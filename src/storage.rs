//! Append-only block storage.
//!
//! Blocks are written as length-prefixed consensus-encoded records. The
//! in-memory hash index makes reads O(1). A durable location index avoids
//! decoding the append-only file on normal restarts; truncated, stale, or
//! corrupt index files fall back to a complete record scan.

use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::{File, OpenOptions, create_dir_all};
use std::io::{ErrorKind, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

#[cfg(unix)]
use std::os::unix::fs::FileExt;
#[cfg(windows)]
use std::os::windows::fs::FileExt;

use anyhow::{Context, Result, bail};
use bitcoin::bip158::FilterHeader;
use bitcoin::consensus::encode::{VarInt, deserialize, deserialize_partial, serialize};
use bitcoin::hashes::{Hash, HashEngine};
use bitcoin::{Block, BlockHash, OutPoint, Transaction, TxOut, Txid};
use parking_lot::Mutex;
use rand::random;
use serde::{Deserialize, Serialize};

const MAX_STORED_BLOCK_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_UNDO_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_FILTER_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_CHAINSTATE_DELTA_SIZE: usize = 64 * 1024 * 1024;
const MAX_STORED_ELECTRUM_BLOCK_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_ELECTRUM_HISTORY_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_UTXO_SIZE: usize = 100 * 1024;
const XOR_KEY_SIZE: usize = 8;
const INDEX_HEADER_SIZE: u64 = 8;
const INDEX_RECORD_SIZE: u64 = 44;
const UTXO_DATA_MAGIC: &[u8] = b"bitcoind-rs-utxo-v1\0";
const UTXO_INDEX_MAGIC: &[u8] = b"bitcoind-rs-utxo-index-v1\0";
const ELECTRUM_HISTORY_DATA_MAGIC: &[u8] = b"bitcoind-rs-electrum-history-v1\0";
const ELECTRUM_HISTORY_INDEX_MAGIC: &[u8] = b"bitcoind-rs-electrum-history-index-v1\0";
const UTXO_PUT: u8 = 1;
const UTXO_DELETE: u8 = 2;
const UTXO_COMMIT: u8 = 3;
const HISTORY_PUT: u8 = 1;
const HISTORY_COMMIT: u8 = 2;

#[derive(Clone, Copy, Debug)]
struct Record {
    offset: u64,
    length: u32,
}

/// The serialized value kept by the durable UTXO store.
///
/// This type deliberately lives in the storage layer so the store does not
/// depend on ChainState.  ChainState converts it to and from its public
/// `UtxoEntry` type at the integration boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StoredUtxo {
    pub output: TxOut,
    pub height: u32,
    pub median_time_past: u32,
    pub coinbase: bool,
}

pub type StoredElectrumHistory = Vec<(Txid, u32)>;

#[derive(Clone, Copy, Debug)]
struct UtxoLocation {
    offset: u64,
    length: u32,
}

type UtxoIndexState = (HashMap<OutPoint, UtxoLocation>, u64, u64);

#[derive(Default)]
struct UtxoReadCache {
    entries: HashMap<OutPoint, (StoredUtxo, usize)>,
    order: VecDeque<OutPoint>,
    bytes: usize,
    limit: usize,
}

impl UtxoReadCache {
    fn configure_limit(&mut self, limit: usize) {
        self.limit = limit;
        self.trim();
    }

    fn get(&mut self, outpoint: &OutPoint) -> Option<StoredUtxo> {
        let entry = self.entries.get(outpoint).map(|(entry, _)| entry.clone());
        if entry.is_some() {
            self.touch(*outpoint);
        }
        entry
    }

    fn insert(&mut self, outpoint: OutPoint, entry: StoredUtxo) {
        let bytes = stored_utxo_cache_bytes(&entry);
        if self.limit == 0 || bytes > self.limit {
            return;
        }
        if let Some((_, old_bytes)) = self.entries.remove(&outpoint) {
            self.bytes = self.bytes.saturating_sub(old_bytes);
            self.order.retain(|cached| *cached != outpoint);
        }
        self.bytes = self.bytes.saturating_add(bytes);
        self.entries.insert(outpoint, (entry, bytes));
        self.order.push_back(outpoint);
        self.trim();
    }

    fn remove(&mut self, outpoint: &OutPoint) {
        if let Some((_, bytes)) = self.entries.remove(outpoint) {
            self.bytes = self.bytes.saturating_sub(bytes);
            self.order.retain(|cached| cached != outpoint);
        }
    }

    fn clear(&mut self) {
        self.entries.clear();
        self.order.clear();
        self.bytes = 0;
    }

    fn touch(&mut self, outpoint: OutPoint) {
        if let Some(position) = self.order.iter().position(|cached| *cached == outpoint) {
            self.order.remove(position);
        }
        self.order.push_back(outpoint);
    }

    fn trim(&mut self) {
        while self.bytes > self.limit {
            let Some(outpoint) = self.order.pop_front() else {
                self.bytes = 0;
                break;
            };
            if let Some((_, bytes)) = self.entries.remove(&outpoint) {
                self.bytes = self.bytes.saturating_sub(bytes);
            }
        }
    }
}

fn stored_utxo_cache_bytes(entry: &StoredUtxo) -> usize {
    64usize.saturating_add(entry.output.script_pubkey.len())
}

#[derive(Clone, Copy, Debug)]
struct HistoryLocation {
    offset: u64,
    length: u32,
}

#[derive(Clone, Copy, Debug)]
struct PendingHistoryOperation {
    script_hash: [u8; 32],
    location: HistoryLocation,
}

type HistoryIndexState = (HashMap<[u8; 32], HistoryLocation>, u64);

#[derive(Clone, Copy, Debug, Default)]
struct XorKey([u8; XOR_KEY_SIZE]);

impl XorKey {
    fn apply(self, bytes: &mut [u8], offset: u64) {
        for (index, byte) in bytes.iter_mut().enumerate() {
            let key_index = ((offset.saturating_add(index as u64)) % XOR_KEY_SIZE as u64) as usize;
            *byte ^= self.0[key_index];
        }
    }
}

fn read_xor_key(path: &Path) -> Result<XorKey> {
    let bytes = std::fs::read(path)
        .with_context(|| format!("reading blocksdir XOR key {}", path.display()))?;
    let bytes: [u8; XOR_KEY_SIZE] = bytes
        .try_into()
        .map_err(|_| anyhow::anyhow!("blocksdir XOR key must be exactly {XOR_KEY_SIZE} bytes"))?;
    Ok(XorKey(bytes))
}

fn init_xor_key(directory: &Path, use_xor: bool) -> Result<XorKey> {
    let path = directory.join("xor.dat");
    let key = if path.exists() {
        read_xor_key(&path)?
    } else {
        let first_run = std::fs::read_dir(directory)?.try_fold(true, |first_run, entry| {
            let entry = entry?;
            let hidden = entry.file_name().to_string_lossy().starts_with('.');
            Ok::<_, std::io::Error>(first_run && hidden)
        })?;
        let key = if use_xor && first_run {
            XorKey(random())
        } else {
            XorKey::default()
        };
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
            .with_context(|| format!("creating blocksdir XOR key {}", path.display()))?;
        file.write_all(&key.0)?;
        file.sync_all()?;
        key
    };
    if !use_xor && key.0.iter().any(|byte| *byte != 0) {
        bail!("the blocksdir XOR key cannot be disabled when a random key is already stored");
    }
    Ok(key)
}

pub struct BlockStore {
    path: PathBuf,
    file: File,
    index_file: File,
    index: HashMap<BlockHash, Record>,
    undo_file: File,
    undo_index_file: File,
    undo_index: HashMap<BlockHash, Record>,
    xor_key: XorKey,
    block_cache: HashMap<BlockHash, (Block, usize)>,
    block_cache_order: VecDeque<BlockHash>,
    block_cache_bytes: usize,
    block_cache_limit: usize,
}

impl BlockStore {
    pub fn open(directory: impl AsRef<Path>) -> Result<Self> {
        Self::open_with_xor(directory, false)
    }

    /// Open the block and undo stores with Core-compatible blocksdir
    /// obfuscation.  The key is persisted in `xor.dat`; a fresh directory gets
    /// a random key when enabled, while an existing clear directory gets a
    /// zero key so upgrading does not rewrite historical data.
    pub fn open_with_xor(directory: impl AsRef<Path>, use_xor: bool) -> Result<Self> {
        let directory = directory.as_ref();
        create_dir_all(directory)
            .with_context(|| format!("creating block directory {}", directory.display()))?;
        let xor_key = init_xor_key(directory, use_xor)?;
        let path = directory.join("blocks.dat");
        let mut file = OpenOptions::new()
            .create(true)
            .read(true)
            .append(true)
            .open(&path)
            .with_context(|| format!("opening block store {}", path.display()))?;
        let index_path = directory.join("blocks.index");
        let mut index_file = OpenOptions::new()
            .create(true)
            .truncate(false)
            .read(true)
            .write(true)
            .open(&index_path)
            .with_context(|| format!("opening block index {}", index_path.display()))?;
        let data_len = file.metadata()?.len();
        let index = match load_index(&mut index_file, data_len)? {
            Some(index) => index,
            None => {
                let index = scan_index(&mut file, xor_key)
                    .with_context(|| format!("scanning {}", path.display()))?;
                rewrite_index(&mut index_file, file.metadata()?.len(), &index)?;
                index
            }
        };
        let undo_path = directory.join("undo.dat");
        let mut undo_file = OpenOptions::new()
            .create(true)
            .read(true)
            .append(true)
            .open(&undo_path)
            .with_context(|| format!("opening undo store {}", undo_path.display()))?;
        let undo_index_path = directory.join("undo.index");
        let mut undo_index_file = OpenOptions::new()
            .create(true)
            .truncate(false)
            .read(true)
            .write(true)
            .open(&undo_index_path)
            .with_context(|| format!("opening undo index {}", undo_index_path.display()))?;
        let undo_data_len = undo_file.metadata()?.len();
        let undo_index = match load_index(&mut undo_index_file, undo_data_len)? {
            Some(index) => index,
            None => {
                let index = scan_undo_index(&mut undo_file, xor_key)
                    .with_context(|| format!("scanning {}", undo_path.display()))?;
                rewrite_index(&mut undo_index_file, undo_file.metadata()?.len(), &index)?;
                index
            }
        };
        Ok(Self {
            path,
            file,
            index_file,
            index,
            undo_file,
            undo_index_file,
            undo_index,
            xor_key,
            block_cache: HashMap::new(),
            block_cache_order: VecDeque::new(),
            block_cache_bytes: 0,
            block_cache_limit: 0,
        })
    }

    /// Open the block and undo records for a reader that must not mutate the
    /// append-only stores.  Background chainstate validation uses a separate
    /// file descriptor so seeks in the validator cannot race the active
    /// chain's reads or writes.
    pub fn open_read_only(directory: impl AsRef<Path>) -> Result<Self> {
        Self::open_read_only_with_xor(directory, false)
    }

    pub fn open_read_only_with_xor(directory: impl AsRef<Path>, use_xor: bool) -> Result<Self> {
        let directory = directory.as_ref();
        let xor_key = if use_xor {
            read_xor_key(&directory.join("xor.dat"))?
        } else {
            XorKey::default()
        };
        let path = directory.join("blocks.dat");
        let mut file = OpenOptions::new()
            .read(true)
            .open(&path)
            .with_context(|| format!("opening block store {}", path.display()))?;
        let index_path = directory.join("blocks.index");
        let mut index_file = OpenOptions::new()
            .read(true)
            .open(&index_path)
            .with_context(|| format!("opening block index {}", index_path.display()))?;
        let data_len = file.metadata()?.len();
        let index = match load_index(&mut index_file, data_len)? {
            Some(index) => index,
            None => scan_index(&mut file, xor_key)
                .with_context(|| format!("scanning {}", path.display()))?,
        };

        let undo_path = directory.join("undo.dat");
        let mut undo_file = OpenOptions::new()
            .read(true)
            .open(&undo_path)
            .with_context(|| format!("opening undo store {}", undo_path.display()))?;
        let undo_index_path = directory.join("undo.index");
        let mut undo_index_file = OpenOptions::new()
            .read(true)
            .open(&undo_index_path)
            .with_context(|| format!("opening undo index {}", undo_index_path.display()))?;
        let undo_data_len = undo_file.metadata()?.len();
        let undo_index = match load_index(&mut undo_index_file, undo_data_len)? {
            Some(index) => index,
            None => scan_undo_index(&mut undo_file, xor_key)
                .with_context(|| format!("scanning {}", undo_path.display()))?,
        };

        Ok(Self {
            path,
            file,
            index_file,
            index,
            undo_file,
            undo_index_file,
            undo_index,
            xor_key,
            block_cache: HashMap::new(),
            block_cache_order: VecDeque::new(),
            block_cache_bytes: 0,
            block_cache_limit: 0,
        })
    }

    /// Configure the in-memory block-record cache used by the custom storage
    /// backend. Core's `-dbcache` is split across several LevelDB caches; this
    /// implementation keeps the UTXO state in memory already, so its useful
    /// equivalent is a bounded cache for decoded historical blocks.
    pub fn configure_cache_size_mib(&mut self, mib: i64) {
        const MIN_CACHE_MIB: u64 = 4;
        const MIB: u64 = 1024 * 1024;
        let mib = u64::try_from(mib.max(0)).unwrap_or(u64::MAX);
        let bytes = mib.max(MIN_CACHE_MIB).saturating_mul(MIB);
        let bytes = usize::try_from(bytes).unwrap_or(usize::MAX);
        self.block_cache_limit = bytes.saturating_mul(3) / 4;
        self.trim_block_cache();
    }

    fn touch_block_cache(&mut self, hash: BlockHash) {
        if let Some(position) = self
            .block_cache_order
            .iter()
            .position(|cached| *cached == hash)
        {
            self.block_cache_order.remove(position);
        }
        self.block_cache_order.push_back(hash);
    }

    fn trim_block_cache(&mut self) {
        while self.block_cache_bytes > self.block_cache_limit {
            let Some(hash) = self.block_cache_order.pop_front() else {
                self.block_cache_bytes = 0;
                break;
            };
            if let Some((_, bytes)) = self.block_cache.remove(&hash) {
                self.block_cache_bytes = self.block_cache_bytes.saturating_sub(bytes);
            }
        }
    }

    fn cache_block(&mut self, hash: BlockHash, block: Block, bytes: usize) {
        if self.block_cache_limit == 0 || bytes > self.block_cache_limit {
            return;
        }
        if let Some((_, old_bytes)) = self.block_cache.remove(&hash) {
            self.block_cache_bytes = self.block_cache_bytes.saturating_sub(old_bytes);
            self.block_cache_order.retain(|cached| *cached != hash);
        }
        self.block_cache_bytes = self.block_cache_bytes.saturating_add(bytes);
        self.block_cache.insert(hash, (block, bytes));
        self.block_cache_order.push_back(hash);
        self.trim_block_cache();
    }

    fn clear_block_cache(&mut self) {
        self.block_cache.clear();
        self.block_cache_order.clear();
        self.block_cache_bytes = 0;
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Return the bytes occupied by block and undo records.
    ///
    /// Core's automatic prune target covers these two files rather than the
    /// small metadata indexes, so keep the accounting aligned with that
    /// behavior.
    pub fn disk_usage(&self) -> Result<u64> {
        self.file
            .metadata()?
            .len()
            .checked_add(self.undo_file.metadata()?.len())
            .context("block store disk usage overflowed")
    }

    pub fn data_size(&self) -> Result<u64> {
        Ok(self.file.metadata()?.len())
    }

    pub fn undo_size(&self) -> Result<u64> {
        Ok(self.undo_file.metadata()?.len())
    }

    pub fn contains(&self, hash: &BlockHash) -> bool {
        self.index.contains_key(hash)
    }

    /// Return the record offset in the implementation's single block data
    /// file. This is exposed for the experimental getblocklocations RPC.
    pub fn block_location(&self, hash: &BlockHash) -> Option<u64> {
        self.index.get(hash).map(|record| record.offset)
    }

    /// Return the record offset in the implementation's single undo data
    /// file, when undo data is available for the block.
    pub fn undo_location(&self, hash: &BlockHash) -> Option<u64> {
        self.undo_index.get(hash).map(|record| record.offset)
    }

    pub fn len(&self) -> usize {
        self.index.len()
    }

    pub fn is_empty(&self) -> bool {
        self.index.is_empty()
    }

    pub fn insert(&mut self, block: &Block) -> Result<BlockHash> {
        let hash = block.block_hash();
        if self.index.contains_key(&hash) {
            return Ok(hash);
        }
        let bytes = serialize(block);
        if bytes.len() > MAX_STORED_BLOCK_SIZE {
            bail!("block is too large: {} bytes", bytes.len());
        }
        let offset = self.file.seek(SeekFrom::End(0))?;
        let length = u32::try_from(bytes.len()).context("block length does not fit u32")?;
        let mut record = Vec::with_capacity(4 + bytes.len());
        record.extend_from_slice(&length.to_le_bytes());
        record.extend_from_slice(&bytes);
        self.xor_key.apply(&mut record, offset);
        self.file.write_all(&record)?;
        self.file.sync_data()?;
        persist_index_entry(
            &mut self.index_file,
            offset + 4 + bytes.len() as u64,
            hash,
            Record { offset, length },
        )?;
        self.index.insert(hash, Record { offset, length });
        self.cache_block(hash, block.clone(), bytes.len());
        Ok(hash)
    }

    pub fn get(&mut self, hash: &BlockHash) -> Result<Option<Block>> {
        if let Some(block) = self.block_cache.get(hash).map(|(block, _)| block.clone()) {
            self.touch_block_cache(*hash);
            return Ok(Some(block));
        }
        let Some(record) = self.index.get(hash).copied() else {
            return Ok(None);
        };
        self.file.seek(SeekFrom::Start(record.offset))?;
        let mut length = [0u8; 4];
        self.file.read_exact(&mut length)?;
        self.xor_key.apply(&mut length, record.offset);
        let actual = u32::from_le_bytes(length);
        if actual != record.length {
            bail!("block store index disagrees with record length");
        }
        let mut bytes = vec![0u8; record.length as usize];
        self.file.read_exact(&mut bytes)?;
        self.xor_key.apply(&mut bytes, record.offset + 4);
        let block: Block = deserialize(&bytes).context("decoding stored block")?;
        if block.block_hash() != *hash {
            bail!("stored block hash does not match block index");
        }
        self.cache_block(*hash, block.clone(), record.length as usize);
        Ok(Some(block))
    }

    pub fn get_undo(&mut self, hash: &BlockHash) -> Result<Option<Vec<Vec<TxOut>>>> {
        let Some(record) = self.undo_index.get(hash).copied() else {
            return Ok(None);
        };
        self.undo_file.seek(SeekFrom::Start(record.offset))?;
        let mut length = [0u8; 4];
        self.undo_file.read_exact(&mut length)?;
        self.xor_key.apply(&mut length, record.offset);
        let actual = u32::from_le_bytes(length);
        if actual != record.length {
            bail!("undo store index disagrees with record length");
        }
        let mut bytes = vec![0u8; record.length as usize];
        self.undo_file.read_exact(&mut bytes)?;
        self.xor_key.apply(&mut bytes, record.offset + 4);
        let (stored_hash, undo) = decode_undo_record(&bytes)?;
        if stored_hash != *hash {
            bail!("stored block undo hash does not match undo index");
        }
        Ok(Some(undo))
    }

    pub fn insert_undo(&mut self, hash: BlockHash, undo: &[Vec<TxOut>]) -> Result<()> {
        if self.undo_index.contains_key(&hash) {
            return Ok(());
        }
        let bytes = encode_undo_record(hash, undo)?;
        if bytes.len() > MAX_STORED_UNDO_SIZE {
            bail!("block undo is too large: {} bytes", bytes.len());
        }
        let offset = self.undo_file.seek(SeekFrom::End(0))?;
        let length = u32::try_from(bytes.len()).context("undo length does not fit u32")?;
        let mut record = Vec::with_capacity(4 + bytes.len());
        record.extend_from_slice(&length.to_le_bytes());
        record.extend_from_slice(&bytes);
        self.xor_key.apply(&mut record, offset);
        self.undo_file.write_all(&record)?;
        self.undo_file.sync_data()?;
        persist_index_entry(
            &mut self.undo_index_file,
            offset + 4 + bytes.len() as u64,
            hash,
            Record { offset, length },
        )?;
        self.undo_index.insert(hash, Record { offset, length });
        Ok(())
    }

    pub fn hashes(&self) -> impl Iterator<Item = &BlockHash> {
        self.index.keys()
    }

    /// Rewrite the append-only files, retaining only the supplied records.
    /// This is used by manual pruning after the chainstate snapshot has made
    /// the retained active tip restartable without old block bodies.
    pub fn prune(
        &mut self,
        retained_blocks: &HashSet<BlockHash>,
        retained_undo: &HashSet<BlockHash>,
    ) -> Result<()> {
        let block_hashes = self
            .index
            .keys()
            .copied()
            .filter(|hash| retained_blocks.contains(hash))
            .collect::<Vec<_>>();
        let mut block_records = Vec::with_capacity(block_hashes.len());
        for hash in block_hashes {
            let block = self
                .get(&hash)?
                .with_context(|| format!("block {hash} disappeared during pruning"))?;
            block_records.push((hash, serialize(&block)));
        }
        let (file, index, data_len) =
            rewrite_record_file(&self.path, &block_records, self.xor_key)?;
        self.file = file;
        self.index = index;
        rewrite_index(&mut self.index_file, data_len, &self.index)?;

        let undo_path = self
            .path
            .parent()
            .context("block store has no parent directory")?
            .join("undo.dat");
        let undo_hashes = self
            .undo_index
            .keys()
            .copied()
            .filter(|hash| retained_undo.contains(hash))
            .collect::<Vec<_>>();
        let mut undo_records = Vec::with_capacity(undo_hashes.len());
        for hash in undo_hashes {
            let undo = self
                .get_undo(&hash)?
                .with_context(|| format!("undo for block {hash} disappeared during pruning"))?;
            undo_records.push((hash, encode_undo_record(hash, &undo)?));
        }
        let (undo_file, undo_index, undo_data_len) =
            rewrite_record_file(&undo_path, &undo_records, self.xor_key)?;
        self.undo_file = undo_file;
        self.undo_index = undo_index;
        rewrite_index(&mut self.undo_index_file, undo_data_len, &self.undo_index)?;
        self.clear_block_cache();
        Ok(())
    }
}

fn rewrite_record_file(
    path: &Path,
    records: &[(BlockHash, Vec<u8>)],
    xor_key: XorKey,
) -> Result<(File, HashMap<BlockHash, Record>, u64)> {
    let temp_path = path.with_file_name(format!(
        "{}.prune.tmp",
        path.file_name().unwrap_or_default().to_string_lossy()
    ));
    let mut temp = OpenOptions::new()
        .create(true)
        .truncate(true)
        .read(true)
        .write(true)
        .open(&temp_path)
        .with_context(|| format!("opening temporary store {}", temp_path.display()))?;
    let mut index = HashMap::with_capacity(records.len());
    for (hash, bytes) in records {
        let offset = temp.seek(SeekFrom::End(0))?;
        let length = u32::try_from(bytes.len()).context("record length does not fit u32")?;
        let mut record = Vec::with_capacity(4 + bytes.len());
        record.extend_from_slice(&length.to_le_bytes());
        record.extend_from_slice(bytes);
        xor_key.apply(&mut record, offset);
        temp.write_all(&record)?;
        index.insert(*hash, Record { offset, length });
    }
    temp.sync_all()?;
    drop(temp);
    std::fs::rename(&temp_path, path)
        .with_context(|| format!("replacing pruned store {}", path.display()))?;
    let data_len = std::fs::metadata(path)?.len();
    let file = OpenOptions::new()
        .read(true)
        .append(true)
        .open(path)
        .with_context(|| format!("reopening pruned store {}", path.display()))?;
    Ok((file, index, data_len))
}

/// Durable BIP158 filter content and filter-header storage.
///
/// Filters are immutable by block hash, so an append-only record file with a
/// compact hash index gives restart-time lookups without replaying block
/// bodies or the UTXO set.
pub struct FilterStore {
    file: File,
    index_file: File,
    index: HashMap<BlockHash, Record>,
}

impl FilterStore {
    pub fn open(directory: impl AsRef<Path>) -> Result<Self> {
        let directory = directory.as_ref();
        create_dir_all(directory)
            .with_context(|| format!("creating filter directory {}", directory.display()))?;
        let path = directory.join("basic-filters.dat");
        let mut file = OpenOptions::new()
            .create(true)
            .read(true)
            .append(true)
            .open(&path)
            .with_context(|| format!("opening filter store {}", path.display()))?;
        let index_path = directory.join("basic-filters.index");
        let mut index_file = OpenOptions::new()
            .create(true)
            .truncate(false)
            .read(true)
            .write(true)
            .open(&index_path)
            .with_context(|| format!("opening filter index {}", index_path.display()))?;
        let data_len = file.metadata()?.len();
        let index = match load_filter_index(&mut index_file, data_len)? {
            Some(index) => index,
            None => {
                let index = scan_filter_index(&mut file)?;
                rewrite_index(&mut index_file, file.metadata()?.len(), &index)?;
                index
            }
        };
        Ok(Self {
            file,
            index_file,
            index,
        })
    }

    pub fn len(&self) -> usize {
        self.index.len()
    }

    pub fn is_empty(&self) -> bool {
        self.index.is_empty()
    }

    pub fn get(&mut self, hash: &BlockHash) -> Result<Option<(Vec<u8>, FilterHeader)>> {
        let Some(record) = self.index.get(hash).copied() else {
            return Ok(None);
        };
        self.file.seek(SeekFrom::Start(record.offset))?;
        let mut length = [0u8; 4];
        self.file.read_exact(&mut length)?;
        let actual = u32::from_le_bytes(length);
        if actual != record.length {
            bail!("filter store index disagrees with record length");
        }
        if actual as usize > MAX_STORED_FILTER_SIZE + 64 {
            bail!("stored filter record is too large");
        }
        let mut bytes = vec![0u8; record.length as usize];
        self.file.read_exact(&mut bytes)?;
        if bytes.len() < 64 {
            bail!("stored filter record is truncated");
        }
        let stored_hash = BlockHash::from_byte_array(
            bytes[..32]
                .try_into()
                .expect("filter block hash has fixed width"),
        );
        if stored_hash != *hash {
            bail!("stored filter hash does not match filter index");
        }
        let header = FilterHeader::from_byte_array(
            bytes[32..64]
                .try_into()
                .expect("filter header has fixed width"),
        );
        Ok(Some((bytes[64..].to_vec(), header)))
    }

    pub fn get_header(&mut self, hash: &BlockHash) -> Result<Option<FilterHeader>> {
        let Some(record) = self.index.get(hash).copied() else {
            return Ok(None);
        };
        if record.length < 64 {
            bail!("stored filter record is truncated");
        }
        if record.length as usize > MAX_STORED_FILTER_SIZE + 64 {
            bail!("stored filter record is too large");
        }
        self.file.seek(SeekFrom::Start(record.offset))?;
        let mut length = [0u8; 4];
        self.file.read_exact(&mut length)?;
        let actual = u32::from_le_bytes(length);
        if actual != record.length {
            bail!("filter store index disagrees with record length");
        }
        let mut prefix = [0u8; 64];
        self.file.read_exact(&mut prefix)?;
        let stored_hash = BlockHash::from_byte_array(
            prefix[..32]
                .try_into()
                .expect("filter block hash has fixed width"),
        );
        if stored_hash != *hash {
            bail!("stored filter hash does not match filter index");
        }
        Ok(Some(FilterHeader::from_byte_array(
            prefix[32..64]
                .try_into()
                .expect("filter header has fixed width"),
        )))
    }

    pub fn insert(&mut self, hash: BlockHash, content: &[u8], header: FilterHeader) -> Result<()> {
        self.insert_batch(&[(hash, content, header)])
    }

    /// Append multiple immutable filters with one data sync and one index
    /// sync.  A crash after the data file is durable but before the index is
    /// durable is recoverable because `open` falls back to scanning the
    /// append-only records when the index length is stale.
    pub fn insert_batch(&mut self, entries: &[(BlockHash, &[u8], FilterHeader)]) -> Result<()> {
        let mut seen = HashSet::new();
        let mut pending = Vec::new();
        let mut data_len = self.file.seek(SeekFrom::End(0))?;

        for (hash, content, header) in entries {
            if self.index.contains_key(hash) || !seen.insert(*hash) {
                continue;
            }
            if content.len() > MAX_STORED_FILTER_SIZE {
                bail!("basic filter is too large: {} bytes", content.len());
            }
            let bytes_len = 64usize
                .checked_add(content.len())
                .context("filter record length overflow")?;
            let length = u32::try_from(bytes_len).context("filter length does not fit u32")?;
            let record_end = data_len
                .checked_add(4)
                .and_then(|offset| offset.checked_add(u64::from(length)))
                .context("filter store size overflow")?;
            pending.push((*hash, *content, *header, data_len, length));
            data_len = record_end;
        }

        if pending.is_empty() {
            return Ok(());
        }

        let mut records = Vec::with_capacity(pending.len());
        for (hash, content, header, offset, length) in pending {
            let mut bytes = Vec::with_capacity(usize::try_from(length).expect("u32 fits usize"));
            bytes.extend_from_slice(&hash.to_byte_array());
            bytes.extend_from_slice(&header.to_byte_array());
            bytes.extend_from_slice(content);
            debug_assert_eq!(
                bytes.len(),
                usize::try_from(length).expect("u32 fits usize")
            );
            self.file.write_all(&length.to_le_bytes())?;
            self.file.write_all(&bytes)?;
            records.push((hash, Record { offset, length }));
        }
        self.file.sync_data()?;

        self.index_file.seek(SeekFrom::Start(0))?;
        self.index_file.write_all(&data_len.to_le_bytes())?;
        self.index_file.seek(SeekFrom::End(0))?;
        for (hash, record) in &records {
            self.index_file.write_all(&hash.to_byte_array())?;
            self.index_file.write_all(&record.offset.to_le_bytes())?;
            self.index_file.write_all(&record.length.to_le_bytes())?;
        }
        self.index_file.sync_data()?;
        for (hash, record) in records {
            self.index.insert(hash, record);
        }
        Ok(())
    }
}

/// Incrementally maintained UTXO statistics for the coinstats index.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct CoinStatsRecord {
    pub block_hash: BlockHash,
    pub height: u32,
    pub transactions: u64,
    pub outputs: u64,
    pub total_amount_sat: u64,
    pub bogo_size: u64,
    pub muhash: String,
    #[serde(default)]
    pub total_subsidy_sat: u64,
    #[serde(default)]
    pub total_prevout_spent_sat: u64,
    #[serde(default)]
    pub total_new_outputs_ex_coinbase_sat: u64,
    #[serde(default)]
    pub total_coinbase_sat: u64,
    #[serde(default)]
    pub total_unspendable_genesis_sat: u64,
    #[serde(default)]
    pub total_unspendable_bip30_sat: u64,
    #[serde(default)]
    pub total_unspendable_scripts_sat: u64,
    #[serde(default)]
    pub total_unspendable_unclaimed_rewards_sat: u64,
}

const MAX_STORED_COINSTATS_SIZE: usize = 4 * 1024;

/// Durable coinstats records keyed by block hash.
pub struct CoinStatsStore {
    path: PathBuf,
    file: File,
    index_file: File,
    index: HashMap<BlockHash, Record>,
}

/// Durable active-chain mutation records.
///
/// The chainstate layer owns the serialized payload; this store only provides
/// the crash-recoverable append-only record and hash index.  A delta is
/// immutable once written because its key is the block hash.  Snapshots can
/// therefore discard old records without changing the recovery semantics for
/// the active suffix.
pub struct ChainstateStore {
    path: PathBuf,
    file: File,
    index_file: File,
    index: HashMap<BlockHash, Record>,
    write_batch_limit: usize,
    pending_write_bytes: usize,
}

impl ChainstateStore {
    pub fn open(directory: impl AsRef<Path>) -> Result<Self> {
        let directory = directory.as_ref();
        create_dir_all(directory)
            .with_context(|| format!("creating chainstate directory {}", directory.display()))?;
        let path = directory.join("deltas.dat");
        let mut file = OpenOptions::new()
            .create(true)
            .read(true)
            .append(true)
            .open(&path)
            .with_context(|| format!("opening chainstate delta store {}", path.display()))?;
        let index_path = directory.join("deltas.index");
        let mut index_file = OpenOptions::new()
            .create(true)
            .truncate(false)
            .read(true)
            .write(true)
            .open(&index_path)
            .with_context(|| format!("opening chainstate delta index {}", index_path.display()))?;
        let data_len = file.metadata()?.len();
        let index = match load_index_with_limit(
            &mut index_file,
            data_len,
            MAX_STORED_CHAINSTATE_DELTA_SIZE + 32,
        )? {
            Some(index) => index,
            None => {
                let index = scan_chainstate_index(&mut file)?;
                rewrite_index(&mut index_file, file.metadata()?.len(), &index)?;
                index
            }
        };
        Ok(Self {
            path,
            file,
            index_file,
            index,
            write_batch_limit: 32 * 1024 * 1024,
            pending_write_bytes: 0,
        })
    }

    /// Set the maximum amount of chainstate data written between data-file
    /// syncs. This is the append-only backend's equivalent of Core's hidden
    /// `-dbbatchsize` debug option.
    pub fn configure_write_batch_size_bytes(&mut self, bytes: i64) {
        self.write_batch_limit = usize::try_from(bytes.max(1)).unwrap_or(usize::MAX);
    }

    fn flush_pending_writes(&mut self) -> Result<()> {
        if self.pending_write_bytes == 0 {
            return Ok(());
        }
        self.file.sync_data()?;
        self.pending_write_bytes = 0;
        Ok(())
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Return the durable size of the chainstate delta data and its index.
    pub fn disk_usage(&self) -> Result<u64> {
        self.file
            .metadata()?
            .len()
            .checked_add(self.index_file.metadata()?.len())
            .context("chainstate store disk usage overflowed")
    }

    pub fn contains(&self, hash: &BlockHash) -> bool {
        self.index.contains_key(hash)
    }

    pub fn get(&mut self, hash: &BlockHash) -> Result<Option<Vec<u8>>> {
        let Some(record) = self.index.get(hash).copied() else {
            return Ok(None);
        };
        if record.length < 32 {
            bail!("stored chainstate delta is truncated");
        }
        if record.length as usize > MAX_STORED_CHAINSTATE_DELTA_SIZE + 32 {
            bail!("stored chainstate delta is too large");
        }
        self.file.seek(SeekFrom::Start(record.offset))?;
        let mut length = [0u8; 4];
        self.file.read_exact(&mut length)?;
        let actual = u32::from_le_bytes(length);
        if actual != record.length {
            bail!("chainstate delta index disagrees with record length");
        }
        let mut bytes = vec![0u8; record.length as usize];
        self.file.read_exact(&mut bytes)?;
        let stored_hash = BlockHash::from_byte_array(
            bytes[..32]
                .try_into()
                .expect("chainstate delta hash has fixed width"),
        );
        if stored_hash != *hash {
            bail!("stored chainstate delta hash does not match its index");
        }
        Ok(Some(bytes[32..].to_vec()))
    }

    pub fn insert(&mut self, hash: BlockHash, payload: &[u8]) -> Result<()> {
        if self.index.contains_key(&hash) {
            return Ok(());
        }
        if payload.len() > MAX_STORED_CHAINSTATE_DELTA_SIZE {
            bail!("chainstate delta is too large: {} bytes", payload.len());
        }
        let length = 32usize
            .checked_add(payload.len())
            .context("chainstate delta length overflow")?;
        let length = u32::try_from(length).context("chainstate delta length does not fit u32")?;
        let offset = self.file.seek(SeekFrom::End(0))?;
        self.file.write_all(&length.to_le_bytes())?;
        self.file.write_all(&hash.to_byte_array())?;
        self.file.write_all(payload)?;
        self.pending_write_bytes = self
            .pending_write_bytes
            .saturating_add(4usize.saturating_add(usize::try_from(length).unwrap_or(usize::MAX)));
        let record = Record { offset, length };
        persist_index_entry(
            &mut self.index_file,
            offset + 4 + u64::from(length),
            hash,
            record,
        )?;
        self.index.insert(hash, record);
        if self.pending_write_bytes >= self.write_batch_limit {
            self.flush_pending_writes()?;
        }
        Ok(())
    }

    /// Discard all records covered by a durable full snapshot.
    pub fn clear(&mut self) -> Result<()> {
        self.flush_pending_writes()?;
        self.file.set_len(0)?;
        self.file.seek(SeekFrom::End(0))?;
        self.file.sync_data()?;
        self.index.clear();
        rewrite_index(&mut self.index_file, 0, &self.index)
    }
}

impl Drop for ChainstateStore {
    fn drop(&mut self) {
        let _ = self.flush_pending_writes();
    }
}

#[derive(Clone, Copy, Debug)]
enum PendingUtxoOperation {
    Put {
        outpoint: OutPoint,
        location: UtxoLocation,
    },
    Delete {
        outpoint: OutPoint,
    },
}

/// Crash-recoverable, batched UTXO storage.
///
/// The value log is append-only and each mutation batch ends with a commit
/// marker.  A torn final record or an uncommitted batch is discarded on the
/// next open.  A separate append-only location index avoids decoding the
/// value log during ordinary restarts; if the index is stale or damaged, the
/// value log is replayed and the index is rebuilt.
pub struct UtxoStore {
    path: PathBuf,
    index_path: PathBuf,
    file: File,
    index_file: File,
    index: HashMap<OutPoint, UtxoLocation>,
    next_batch_id: u64,
    generation: u64,
    pending_write_bytes: usize,
    read_cache: Mutex<UtxoReadCache>,
}

impl UtxoStore {
    pub fn open(directory: impl AsRef<Path>) -> Result<Self> {
        let directory = directory.as_ref();
        create_dir_all(directory)
            .with_context(|| format!("creating UTXO store {}", directory.display()))?;
        let path = directory.join("utxos.dat");
        let mut file = OpenOptions::new()
            .create(true)
            .read(true)
            .append(true)
            .open(&path)
            .with_context(|| format!("opening UTXO store {}", path.display()))?;
        if file.metadata()?.len() == 0 {
            file.write_all(UTXO_DATA_MAGIC)?;
            file.sync_data()?;
        } else {
            let mut magic = vec![0u8; UTXO_DATA_MAGIC.len()];
            file.seek(SeekFrom::Start(0))?;
            file.read_exact(&mut magic)?;
            if magic != UTXO_DATA_MAGIC {
                bail!("UTXO store has an unknown format");
            }
        }

        let index_path = directory.join("utxos.index");
        let mut index_file = OpenOptions::new()
            .create(true)
            .read(true)
            .append(true)
            .open(&index_path)
            .with_context(|| format!("opening UTXO index {}", index_path.display()))?;
        let data_len = file.metadata()?.len();
        let loaded_index = load_utxo_index(&mut index_file, data_len)?;
        let (index, next_batch_id, generation) = if let Some(index) = loaded_index {
            index
        } else {
            let (index, next_batch_id) = scan_utxo_data(&mut file)?;
            // A rebuilt index must not reuse a tip marker from an interrupted
            // replacement, even if the resulting data happens to have the
            // same length as the old value log.
            let generation = random::<u64>().max(1);
            rewrite_utxo_index(
                &mut index_file,
                data_len_after(&file)?,
                next_batch_id,
                generation,
                &index,
            )?;
            (index, next_batch_id, generation)
        };
        Ok(Self {
            path,
            index_path,
            file,
            index_file,
            index,
            next_batch_id,
            generation,
            pending_write_bytes: 0,
            read_cache: Mutex::new(UtxoReadCache::default()),
        })
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn index_path(&self) -> &Path {
        &self.index_path
    }

    pub fn len(&self) -> usize {
        self.index.len()
    }

    pub fn is_empty(&self) -> bool {
        self.index.is_empty()
    }

    pub fn generation(&self) -> u64 {
        self.generation
    }

    /// Allocate one quarter of the configured storage cache to decoded UTXO
    /// values. The remaining three quarters are reserved for block records,
    /// matching the split used by the custom backend's block cache.
    pub fn configure_cache_size_mib(&self, mib: i64) {
        const MIN_CACHE_MIB: u64 = 4;
        const MIB: u64 = 1024 * 1024;
        let mib = u64::try_from(mib.max(0)).unwrap_or(u64::MAX);
        let total_bytes = mib.max(MIN_CACHE_MIB).saturating_mul(MIB);
        let limit = usize::try_from(total_bytes / 4).unwrap_or(usize::MAX);
        self.read_cache.lock().configure_limit(limit);
    }

    pub fn contains(&self, outpoint: &OutPoint) -> bool {
        self.index.contains_key(outpoint)
    }

    pub fn disk_usage(&self) -> Result<u64> {
        self.file
            .metadata()?
            .len()
            .checked_add(self.index_file.metadata()?.len())
            .context("UTXO store disk usage overflowed")
    }

    pub fn get(&self, outpoint: &OutPoint) -> Result<Option<StoredUtxo>> {
        if let Some(entry) = self.read_cache.lock().get(outpoint) {
            return Ok(Some(entry));
        }
        let Some(location) = self.index.get(outpoint).copied() else {
            return Ok(None);
        };
        let body = read_utxo_data_record(&self.file, location)?;
        if body.first().copied() != Some(UTXO_PUT) || body.len() < 1 + 8 + 36 {
            bail!("UTXO location points to a non-value record");
        }
        let stored_outpoint = decode_outpoint(&body[9..45])?;
        if stored_outpoint != *outpoint {
            bail!("UTXO value key does not match its index");
        }
        let entry = decode_stored_utxo(&body[45..])?;
        self.read_cache.lock().insert(*outpoint, entry.clone());
        Ok(Some(entry))
    }

    /// Read all live entries.  This is intentionally explicit: normal block
    /// validation uses point lookups, while snapshot/export code can opt into
    /// the full materialization cost.
    pub fn entries(&self) -> Result<Vec<(OutPoint, StoredUtxo)>> {
        let mut locations = self
            .index
            .iter()
            .map(|(outpoint, location)| (*outpoint, *location))
            .collect::<Vec<_>>();
        locations.sort_unstable_by_key(|(_, location)| location.offset);
        locations
            .into_iter()
            .map(|(outpoint, location)| {
                let body = read_utxo_data_record(&self.file, location)?;
                if body.first().copied() != Some(UTXO_PUT) || body.len() < 1 + 8 + 36 {
                    bail!("UTXO location points to a non-value record");
                }
                let stored_outpoint = decode_outpoint(&body[9..45])?;
                if stored_outpoint != outpoint {
                    bail!("UTXO value key does not match its index");
                }
                Ok((outpoint, decode_stored_utxo(&body[45..])?))
            })
            .collect()
    }

    /// Apply removals and additions as one durable mutation batch.  A caller
    /// may remove and then recreate the same outpoint in one batch, which is
    /// required for historical duplicate-coinbase (BIP30) handling.
    pub fn apply_batch(
        &mut self,
        removals: &[OutPoint],
        additions: &[(OutPoint, StoredUtxo)],
    ) -> Result<()> {
        if removals.is_empty() && additions.is_empty() {
            return Ok(());
        }
        let batch_id = self.next_batch_id;
        let next_batch_id = batch_id
            .checked_add(1)
            .context("UTXO batch identifier exhausted")?;
        let batch_start = data_len_after(&self.file)?;
        let mut data_committed = false;
        let mut operations = Vec::with_capacity(removals.len() + additions.len());
        let write_result = (|| -> Result<()> {
            for outpoint in removals {
                let body = encode_utxo_delete(batch_id, outpoint);
                let location = append_utxo_data_record(&mut self.file, &body)?;
                operations.push(PendingUtxoOperation::Delete {
                    outpoint: *outpoint,
                });
                self.pending_write_bytes = self
                    .pending_write_bytes
                    .saturating_add(4usize.saturating_add(location.length as usize));
            }
            for (outpoint, entry) in additions {
                let body = encode_utxo_put(batch_id, outpoint, entry)?;
                let location = append_utxo_data_record(&mut self.file, &body)?;
                operations.push(PendingUtxoOperation::Put {
                    outpoint: *outpoint,
                    location,
                });
                self.pending_write_bytes = self
                    .pending_write_bytes
                    .saturating_add(4usize.saturating_add(location.length as usize));
            }
            let commit = encode_utxo_commit(batch_id);
            let commit_location = append_utxo_data_record(&mut self.file, &commit)?;
            self.pending_write_bytes = self
                .pending_write_bytes
                .saturating_add(4usize.saturating_add(commit_location.length as usize));
            self.file.sync_data()?;
            data_committed = true;
            append_utxo_index_batch(
                &mut self.index_file,
                batch_id,
                data_len_after(&self.file)?,
                next_batch_id,
                self.generation,
                &operations,
            )?;
            self.index_file.sync_data()?;
            Ok(())
        })();
        if let Err(error) = write_result {
            // If the data commit itself was not durable, remove the partial
            // tail so the live store can continue to accept writes. Once the
            // commit marker has been synced, leave the committed value log
            // intact; a later open can rebuild an index whose append failed.
            if !data_committed {
                let current_len = data_len_after(&self.file)?;
                if current_len > batch_start {
                    let _ = self.file.set_len(batch_start);
                    let _ = self.file.seek(SeekFrom::End(0));
                }
            }
            return Err(error);
        }
        for operation in operations {
            match operation {
                PendingUtxoOperation::Put { outpoint, location } => {
                    self.index.insert(outpoint, location);
                    self.read_cache.lock().remove(&outpoint);
                }
                PendingUtxoOperation::Delete { outpoint } => {
                    self.index.remove(&outpoint);
                    self.read_cache.lock().remove(&outpoint);
                }
            }
        }
        self.next_batch_id = next_batch_id;
        Ok(())
    }

    /// Replace the live set in bounded batches.  This is used when importing
    /// a snapshot or migrating the legacy in-memory chainstate format.
    pub fn replace_all<I>(&mut self, entries: I) -> Result<()>
    where
        I: IntoIterator<Item = (OutPoint, StoredUtxo)>,
    {
        self.clear()?;
        let mut batch = Vec::with_capacity(10_000);
        for entry in entries {
            batch.push(entry);
            if batch.len() == 10_000 {
                self.apply_batch(&[], &batch)?;
                batch.clear();
            }
        }
        if !batch.is_empty() {
            self.apply_batch(&[], &batch)?;
        }
        Ok(())
    }

    pub fn clear(&mut self) -> Result<()> {
        self.file.set_len(0)?;
        self.file.seek(SeekFrom::End(0))?;
        self.file.write_all(UTXO_DATA_MAGIC)?;
        self.file.sync_data()?;
        self.index.clear();
        self.read_cache.lock().clear();
        self.next_batch_id = 1;
        self.generation = self
            .generation
            .checked_add(1)
            .context("UTXO store generation exhausted")?;
        rewrite_utxo_index(
            &mut self.index_file,
            UTXO_DATA_MAGIC.len() as u64,
            self.next_batch_id,
            self.generation,
            &self.index,
        )?;
        self.pending_write_bytes = 0;
        Ok(())
    }

    pub fn flush(&mut self) -> Result<()> {
        self.file.sync_data()?;
        self.index_file.sync_data()?;
        self.pending_write_bytes = 0;
        Ok(())
    }
}

impl Drop for UtxoStore {
    fn drop(&mut self) {
        let _ = self.flush();
    }
}

/// Durable Electrum script history.
///
/// Each value-log record contains the complete history for one script hash;
/// the in-memory index keeps only the latest record location.  Updating a
/// script therefore appends a new value and atomically advances its pointer,
/// while ordinary restarts avoid loading every history vector into memory.
pub struct ElectrumHistoryStore {
    path: PathBuf,
    index_path: PathBuf,
    file: File,
    index_file: File,
    index: HashMap<[u8; 32], HistoryLocation>,
    next_batch_id: u64,
}

impl ElectrumHistoryStore {
    pub fn open(directory: impl AsRef<Path>) -> Result<Self> {
        let directory = directory.as_ref();
        create_dir_all(directory)
            .with_context(|| format!("creating Electrum history store {}", directory.display()))?;
        let path = directory.join("history.dat");
        let mut file = OpenOptions::new()
            .create(true)
            .read(true)
            .append(true)
            .open(&path)
            .with_context(|| format!("opening Electrum history store {}", path.display()))?;
        if file.metadata()?.len() == 0 {
            file.write_all(ELECTRUM_HISTORY_DATA_MAGIC)?;
            file.sync_data()?;
        } else {
            let mut magic = vec![0u8; ELECTRUM_HISTORY_DATA_MAGIC.len()];
            file.seek(SeekFrom::Start(0))?;
            file.read_exact(&mut magic)?;
            if magic != ELECTRUM_HISTORY_DATA_MAGIC {
                bail!("Electrum history store has an unknown format");
            }
        }

        let index_path = directory.join("history.index");
        let mut index_file = OpenOptions::new()
            .create(true)
            .read(true)
            .append(true)
            .open(&index_path)
            .with_context(|| format!("opening Electrum history index {}", index_path.display()))?;
        let data_len = file.metadata()?.len();
        let loaded_index = load_history_index(&mut index_file, data_len)?;
        let (index, next_batch_id) = if let Some(index) = loaded_index {
            index
        } else {
            let (index, next_batch_id) = scan_history_data(&mut file)?;
            rewrite_history_index(
                &mut index_file,
                data_len_after(&file)?,
                next_batch_id,
                &index,
            )?;
            (index, next_batch_id)
        };
        Ok(Self {
            path,
            index_path,
            file,
            index_file,
            index,
            next_batch_id,
        })
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn index_path(&self) -> &Path {
        &self.index_path
    }

    pub fn len(&self) -> usize {
        self.index.len()
    }

    pub fn is_empty(&self) -> bool {
        self.index.is_empty()
    }

    /// Monotonically increasing checkpoint used by chainstate to detect a
    /// history store write that was not followed by metadata publication.
    pub fn generation(&self) -> u64 {
        self.next_batch_id
    }

    pub fn contains(&self, script_hash: &str) -> bool {
        encode_history_script_hash(script_hash)
            .ok()
            .is_some_and(|script_hash| self.index.contains_key(&script_hash))
    }

    pub fn disk_usage(&self) -> Result<u64> {
        self.file
            .metadata()?
            .len()
            .checked_add(self.index_file.metadata()?.len())
            .context("Electrum history store size overflowed")
    }

    pub fn get(&self, script_hash: &str) -> Result<Vec<(Txid, u32)>> {
        let script_hash = encode_history_script_hash(script_hash)?;
        let Some(location) = self.index.get(&script_hash).copied() else {
            return Ok(Vec::new());
        };
        let body = read_history_data_record(&self.file, location)?;
        decode_history_value(&body, script_hash)
    }

    pub fn keys(&self) -> Vec<String> {
        self.index.keys().map(hex::encode).collect()
    }

    pub fn entries(&self) -> Result<Vec<(String, StoredElectrumHistory)>> {
        let mut locations = self
            .index
            .iter()
            .map(|(script_hash, location)| (*script_hash, *location))
            .collect::<Vec<_>>();
        locations.sort_unstable_by_key(|(_, location)| location.offset);
        locations
            .into_iter()
            .map(|(script_hash, location)| {
                let body = read_history_data_record(&self.file, location)?;
                Ok((
                    hex::encode(script_hash),
                    decode_history_value(&body, script_hash)?,
                ))
            })
            .collect()
    }

    /// Apply complete replacement values for the scripts touched by a block.
    /// The caller supplies each script's new chronological history.
    pub fn apply_batch(&mut self, updates: &[(String, Vec<(Txid, u32)>)]) -> Result<()> {
        if updates.is_empty() {
            return Ok(());
        }
        let batch_id = self.next_batch_id;
        let next_batch_id = batch_id
            .checked_add(1)
            .context("Electrum history batch identifier exhausted")?;
        let batch_start = data_len_after(&self.file)?;
        let mut operations = Vec::with_capacity(updates.len());
        let mut data_committed = false;
        let write_result = (|| -> Result<()> {
            for (script_hash, entries) in updates {
                let script_hash_bytes = encode_history_script_hash(script_hash)?;
                let body = encode_history_value(batch_id, script_hash_bytes, entries)?;
                let location = append_history_data_record(&mut self.file, &body)?;
                operations.push(PendingHistoryOperation {
                    script_hash: script_hash_bytes,
                    location,
                });
            }
            let commit = encode_history_commit(batch_id);
            append_history_data_record(&mut self.file, &commit)?;
            self.file.sync_data()?;
            data_committed = true;
            append_history_index_batch(
                &mut self.index_file,
                batch_id,
                data_len_after(&self.file)?,
                next_batch_id,
                &operations,
            )?;
            self.index_file.sync_data()?;
            Ok(())
        })();
        if let Err(error) = write_result {
            if !data_committed {
                let current_len = data_len_after(&self.file)?;
                if current_len > batch_start {
                    let _ = self.file.set_len(batch_start);
                    let _ = self.file.seek(SeekFrom::End(0));
                }
            }
            return Err(error);
        }
        for operation in operations {
            self.index.insert(operation.script_hash, operation.location);
        }
        self.next_batch_id = next_batch_id;
        Ok(())
    }

    pub fn replace_all<I>(&mut self, entries: I) -> Result<()>
    where
        I: IntoIterator<Item = (String, Vec<(Txid, u32)>)>,
    {
        self.clear()?;
        let mut batch = Vec::with_capacity(1_000);
        for entry in entries {
            batch.push(entry);
            if batch.len() == 1_000 {
                self.apply_batch(&batch)?;
                batch.clear();
            }
        }
        if !batch.is_empty() {
            self.apply_batch(&batch)?;
        }
        Ok(())
    }

    pub fn clear(&mut self) -> Result<()> {
        self.file.set_len(0)?;
        self.file.seek(SeekFrom::End(0))?;
        self.file.write_all(ELECTRUM_HISTORY_DATA_MAGIC)?;
        self.file.sync_data()?;
        self.index.clear();
        self.next_batch_id = 1;
        self.index_file.set_len(0)?;
        self.index_file.seek(SeekFrom::End(0))?;
        self.index_file.write_all(ELECTRUM_HISTORY_INDEX_MAGIC)?;
        self.index_file.sync_data()?;
        Ok(())
    }

    pub fn flush(&mut self) -> Result<()> {
        self.file.sync_data()?;
        self.index_file.sync_data()?;
        Ok(())
    }
}

impl Drop for ElectrumHistoryStore {
    fn drop(&mut self) {
        let _ = self.flush();
    }
}

fn data_len_after(file: &File) -> Result<u64> {
    Ok(file.metadata()?.len())
}

fn encode_history_script_hash(script_hash: &str) -> Result<[u8; 32]> {
    let bytes = hex::decode(script_hash).context("decoding Electrum script hash")?;
    bytes
        .try_into()
        .map_err(|_| anyhow::anyhow!("Electrum script hash must be exactly 32 bytes"))
}

fn encode_history_value(
    batch_id: u64,
    script_hash: [u8; 32],
    entries: &[(Txid, u32)],
) -> Result<Vec<u8>> {
    let entry_bytes = entries
        .len()
        .checked_mul(36)
        .context("Electrum history entry count overflowed")?;
    let body_len = 1usize
        .checked_add(8)
        .and_then(|length| length.checked_add(32))
        .and_then(|length| length.checked_add(4))
        .and_then(|length| length.checked_add(entry_bytes))
        .context("Electrum history record length overflowed")?;
    if body_len > MAX_STORED_ELECTRUM_HISTORY_SIZE {
        bail!("Electrum history record is too large: {body_len} bytes");
    }
    let count =
        u32::try_from(entries.len()).context("Electrum history entry count is too large")?;
    let mut body = Vec::with_capacity(body_len);
    body.push(HISTORY_PUT);
    body.extend_from_slice(&batch_id.to_le_bytes());
    body.extend_from_slice(&script_hash);
    body.extend_from_slice(&count.to_le_bytes());
    for (txid, height) in entries {
        body.extend_from_slice(&txid.to_byte_array());
        body.extend_from_slice(&height.to_le_bytes());
    }
    Ok(body)
}

fn encode_history_commit(batch_id: u64) -> Vec<u8> {
    let mut body = Vec::with_capacity(1 + 8);
    body.push(HISTORY_COMMIT);
    body.extend_from_slice(&batch_id.to_le_bytes());
    body
}

fn append_history_data_record(file: &mut File, body: &[u8]) -> Result<HistoryLocation> {
    if body.is_empty() || body.len() > MAX_STORED_ELECTRUM_HISTORY_SIZE {
        bail!("Electrum history log record is too large");
    }
    let offset = data_len_after(file)?;
    let length = u32::try_from(body.len()).context("Electrum history record is too large")?;
    file.write_all(&length.to_le_bytes())?;
    file.write_all(body)?;
    Ok(HistoryLocation { offset, length })
}

fn read_history_data_record(file: &File, location: HistoryLocation) -> Result<Vec<u8>> {
    if location.length as usize > MAX_STORED_ELECTRUM_HISTORY_SIZE {
        bail!("stored Electrum history record is too large");
    }
    let mut length = [0u8; 4];
    read_exact_at(file, &mut length, location.offset)?;
    let actual = u32::from_le_bytes(length);
    if actual != location.length {
        bail!("Electrum history index disagrees with record length");
    }
    let mut body = vec![0u8; location.length as usize];
    read_exact_at(
        file,
        &mut body,
        location
            .offset
            .checked_add(4)
            .context("Electrum history value offset overflowed")?,
    )?;
    Ok(body)
}

fn decode_history_value(body: &[u8], expected_script_hash: [u8; 32]) -> Result<Vec<(Txid, u32)>> {
    if body.len() < 1 + 8 + 32 + 4 || body[0] != HISTORY_PUT {
        bail!("Electrum history value is truncated or has an invalid operation");
    }
    let script_hash: [u8; 32] = body[9..41]
        .try_into()
        .expect("Electrum history script hash has fixed width");
    if script_hash != expected_script_hash {
        bail!("Electrum history value key does not match its index");
    }
    let count = usize::try_from(u32::from_le_bytes(
        body[41..45]
            .try_into()
            .expect("Electrum history count has fixed width"),
    ))
    .context("Electrum history count does not fit usize")?;
    let expected_len = 45usize
        .checked_add(
            count
                .checked_mul(36)
                .context("Electrum history count overflowed")?,
        )
        .context("Electrum history value length overflowed")?;
    if expected_len != body.len() {
        bail!("Electrum history count does not match value length");
    }
    let mut entries = Vec::with_capacity(count);
    let mut offset = 45usize;
    for _ in 0..count {
        let txid = Txid::from_byte_array(
            body[offset..offset + 32]
                .try_into()
                .expect("Electrum history txid has fixed width"),
        );
        let height = u32::from_le_bytes(
            body[offset + 32..offset + 36]
                .try_into()
                .expect("Electrum history height has fixed width"),
        );
        entries.push((txid, height));
        offset += 36;
    }
    Ok(entries)
}

fn scan_history_data(file: &mut File) -> Result<(HashMap<[u8; 32], HistoryLocation>, u64)> {
    let data_len = data_len_after(file)?;
    file.seek(SeekFrom::Start(0))?;
    let mut magic = vec![0u8; ELECTRUM_HISTORY_DATA_MAGIC.len()];
    file.read_exact(&mut magic)?;
    if magic != ELECTRUM_HISTORY_DATA_MAGIC {
        bail!("Electrum history store has an unknown format");
    }
    let mut position = ELECTRUM_HISTORY_DATA_MAGIC.len() as u64;
    let mut committed_end = position;
    let mut pending_batch = None;
    let mut pending = Vec::new();
    let mut index = HashMap::new();
    let mut max_batch = 0u64;
    while position < data_len {
        let record_start = position;
        let mut length_bytes = [0u8; 4];
        if let Err(error) = file.read_exact(&mut length_bytes) {
            if error.kind() == ErrorKind::UnexpectedEof {
                break;
            }
            return Err(error.into());
        }
        let length = u32::from_le_bytes(length_bytes);
        let next = position
            .checked_add(4)
            .and_then(|value| value.checked_add(u64::from(length)))
            .context("Electrum history log position overflowed")?;
        if length == 0
            || usize::try_from(length).unwrap_or(usize::MAX) > MAX_STORED_ELECTRUM_HISTORY_SIZE
        {
            if next > data_len {
                break;
            }
            bail!("Electrum history log record has an invalid length");
        }
        if next > data_len {
            break;
        }
        let mut body = vec![0u8; length as usize];
        file.read_exact(&mut body)?;
        match body.first().copied() {
            Some(HISTORY_PUT) => {
                if body.len() < 1 + 8 + 32 + 4 {
                    bail!("Electrum history value is truncated");
                }
                let batch_id = u64::from_le_bytes(
                    body[1..9]
                        .try_into()
                        .context("Electrum history batch identifier is truncated")?,
                );
                let script_hash: [u8; 32] = body[9..41]
                    .try_into()
                    .context("Electrum history script hash is truncated")?;
                decode_history_value(&body, script_hash)?;
                if pending_batch != Some(batch_id) {
                    if pending_batch.is_some() {
                        bail!("Electrum history log contains interleaved batches");
                    }
                    pending_batch = Some(batch_id);
                }
                pending.push(PendingHistoryOperation {
                    script_hash,
                    location: HistoryLocation {
                        offset: record_start,
                        length,
                    },
                });
                max_batch = max_batch.max(batch_id);
            }
            Some(HISTORY_COMMIT) => {
                if body.len() != 1 + 8 {
                    bail!("Electrum history commit record has an invalid length");
                }
                let batch_id = u64::from_le_bytes(
                    body[1..9]
                        .try_into()
                        .expect("Electrum history batch identifier has fixed width"),
                );
                if pending_batch != Some(batch_id) || pending.is_empty() {
                    bail!("Electrum history commit does not match a pending batch");
                }
                for operation in pending.drain(..) {
                    index.insert(operation.script_hash, operation.location);
                }
                pending_batch = None;
                committed_end = next;
                max_batch = max_batch.max(batch_id);
            }
            _ => bail!("Electrum history log contains an unknown operation"),
        }
        position = next;
    }
    if pending_batch.is_some() || position != committed_end {
        file.set_len(committed_end)?;
        file.seek(SeekFrom::End(0))?;
    }
    Ok((
        index,
        max_batch
            .checked_add(1)
            .context("Electrum history batch identifier exhausted")?,
    ))
}

fn load_history_index(file: &mut File, data_len: u64) -> Result<Option<HistoryIndexState>> {
    let index_len = file.metadata()?.len();
    if index_len < ELECTRUM_HISTORY_INDEX_MAGIC.len() as u64 {
        return Ok(None);
    }
    file.seek(SeekFrom::Start(0))?;
    let mut magic = vec![0u8; ELECTRUM_HISTORY_INDEX_MAGIC.len()];
    file.read_exact(&mut magic)?;
    if magic != ELECTRUM_HISTORY_INDEX_MAGIC {
        return Ok(None);
    }
    let mut position = ELECTRUM_HISTORY_INDEX_MAGIC.len() as u64;
    let mut pending_batch = None;
    let mut pending = Vec::new();
    let mut index = HashMap::new();
    let mut last_data_end = None;
    let mut stored_next_batch_id = None;
    let mut max_batch = 0u64;
    while position < index_len {
        let mut length_bytes = [0u8; 4];
        if file.read_exact(&mut length_bytes).is_err() {
            return Ok(None);
        }
        let length = u32::from_le_bytes(length_bytes);
        let next = position
            .checked_add(4)
            .and_then(|value| value.checked_add(u64::from(length)))
            .context("Electrum history index position overflowed")?;
        if next > index_len || length == 0 || length > 128 {
            return Ok(None);
        }
        let mut body = vec![0u8; length as usize];
        file.read_exact(&mut body)?;
        match body.first().copied() {
            Some(HISTORY_PUT) => {
                if body.len() != 1 + 8 + 8 + 4 + 32 {
                    return Ok(None);
                }
                let batch_id = u64::from_le_bytes(body[1..9].try_into().unwrap());
                let offset = u64::from_le_bytes(body[9..17].try_into().unwrap());
                let value_length = u32::from_le_bytes(body[17..21].try_into().unwrap());
                if value_length == 0
                    || value_length as usize > MAX_STORED_ELECTRUM_HISTORY_SIZE
                    || offset < ELECTRUM_HISTORY_DATA_MAGIC.len() as u64
                    || offset
                        .checked_add(4)
                        .and_then(|end| end.checked_add(u64::from(value_length)))
                        .is_none_or(|end| end > data_len)
                {
                    return Ok(None);
                }
                let script_hash: [u8; 32] = body[21..53].try_into().unwrap();
                if pending_batch != Some(batch_id) {
                    if pending_batch.is_some() {
                        return Ok(None);
                    }
                    pending_batch = Some(batch_id);
                }
                pending.push(PendingHistoryOperation {
                    script_hash,
                    location: HistoryLocation {
                        offset,
                        length: value_length,
                    },
                });
                max_batch = max_batch.max(batch_id);
            }
            Some(HISTORY_COMMIT) => {
                if body.len() != 1 + 8 + 8 + 8 {
                    return Ok(None);
                }
                let batch_id = u64::from_le_bytes(body[1..9].try_into().unwrap());
                let data_end = u64::from_le_bytes(body[9..17].try_into().unwrap());
                let next_batch_id = u64::from_le_bytes(body[17..25].try_into().unwrap());
                if next_batch_id == 0
                    || data_end < ELECTRUM_HISTORY_DATA_MAGIC.len() as u64
                    || data_end > data_len
                    || last_data_end.is_some_and(|previous| data_end < previous)
                    || pending_batch != Some(batch_id)
                    || (pending.is_empty() && batch_id != 0)
                {
                    return Ok(None);
                }
                for operation in pending.drain(..) {
                    index.insert(operation.script_hash, operation.location);
                }
                pending_batch = None;
                last_data_end = Some(data_end);
                stored_next_batch_id = Some(next_batch_id);
                max_batch = max_batch.max(batch_id);
            }
            _ => return Ok(None),
        }
        position = next;
    }
    if pending_batch.is_some() || last_data_end != Some(data_len) {
        return Ok(None);
    }
    Ok(Some((
        index,
        stored_next_batch_id.unwrap_or(
            max_batch
                .checked_add(1)
                .context("Electrum history batch identifier exhausted")?,
        ),
    )))
}

fn append_history_index_batch(
    file: &mut File,
    batch_id: u64,
    data_end: u64,
    next_batch_id: u64,
    operations: &[PendingHistoryOperation],
) -> Result<()> {
    file.seek(SeekFrom::End(0))?;
    for operation in operations {
        let mut body = Vec::with_capacity(64);
        body.push(HISTORY_PUT);
        body.extend_from_slice(&batch_id.to_le_bytes());
        body.extend_from_slice(&operation.location.offset.to_le_bytes());
        body.extend_from_slice(&operation.location.length.to_le_bytes());
        body.extend_from_slice(&operation.script_hash);
        let length =
            u32::try_from(body.len()).context("Electrum history index record too large")?;
        file.write_all(&length.to_le_bytes())?;
        file.write_all(&body)?;
    }
    let mut commit = Vec::with_capacity(25);
    commit.push(HISTORY_COMMIT);
    commit.extend_from_slice(&batch_id.to_le_bytes());
    commit.extend_from_slice(&data_end.to_le_bytes());
    commit.extend_from_slice(&next_batch_id.to_le_bytes());
    file.write_all(&(u32::try_from(commit.len()).unwrap()).to_le_bytes())?;
    file.write_all(&commit)?;
    Ok(())
}

fn rewrite_history_index(
    file: &mut File,
    data_end: u64,
    next_batch_id: u64,
    index: &HashMap<[u8; 32], HistoryLocation>,
) -> Result<()> {
    file.set_len(0)?;
    file.seek(SeekFrom::End(0))?;
    file.write_all(ELECTRUM_HISTORY_INDEX_MAGIC)?;
    let operations = index
        .iter()
        .map(|(script_hash, location)| PendingHistoryOperation {
            script_hash: *script_hash,
            location: *location,
        })
        .collect::<Vec<_>>();
    append_history_index_batch(file, 0, data_end, next_batch_id, &operations)?;
    file.sync_data()?;
    Ok(())
}

fn encode_stored_utxo(entry: &StoredUtxo) -> Result<Vec<u8>> {
    let output = serialize(&entry.output);
    let output_len = u32::try_from(output.len()).context("UTXO output is too large")?;
    let mut bytes = Vec::with_capacity(4 + 4 + 1 + 4 + output.len());
    bytes.extend_from_slice(&entry.height.to_le_bytes());
    bytes.extend_from_slice(&entry.median_time_past.to_le_bytes());
    bytes.push(u8::from(entry.coinbase));
    bytes.extend_from_slice(&output_len.to_le_bytes());
    bytes.extend_from_slice(&output);
    if bytes.len() > MAX_STORED_UTXO_SIZE {
        bail!("UTXO value is too large: {} bytes", bytes.len());
    }
    Ok(bytes)
}

fn decode_stored_utxo(bytes: &[u8]) -> Result<StoredUtxo> {
    if bytes.len() < 13 {
        bail!("stored UTXO value is truncated");
    }
    let height = u32::from_le_bytes(bytes[0..4].try_into().expect("fixed UTXO height"));
    let median_time_past =
        u32::from_le_bytes(bytes[4..8].try_into().expect("fixed UTXO median time"));
    let coinbase = match bytes[8] {
        0 => false,
        1 => true,
        _ => bail!("stored UTXO coinbase flag is invalid"),
    };
    let output_len = usize::try_from(u32::from_le_bytes(
        bytes[9..13].try_into().expect("fixed UTXO output length"),
    ))
    .context("stored UTXO output length does not fit usize")?;
    let output_end = 13usize
        .checked_add(output_len)
        .context("stored UTXO output length overflowed")?;
    if output_end != bytes.len() {
        bail!("stored UTXO output length does not match record length");
    }
    let output = deserialize(&bytes[13..output_end]).context("decoding stored UTXO output")?;
    Ok(StoredUtxo {
        output,
        height,
        median_time_past,
        coinbase,
    })
}

fn encode_outpoint(outpoint: &OutPoint) -> [u8; 36] {
    serialize(outpoint)
        .try_into()
        .expect("Bitcoin outpoints have a fixed 36-byte encoding")
}

fn decode_outpoint(bytes: &[u8]) -> Result<OutPoint> {
    if bytes.len() != 36 {
        bail!("stored UTXO outpoint is not 36 bytes");
    }
    deserialize(bytes).context("decoding stored UTXO outpoint")
}

fn encode_utxo_put(batch_id: u64, outpoint: &OutPoint, entry: &StoredUtxo) -> Result<Vec<u8>> {
    let mut body = Vec::with_capacity(1 + 8 + 36 + MAX_STORED_UTXO_SIZE.min(128));
    body.push(UTXO_PUT);
    body.extend_from_slice(&batch_id.to_le_bytes());
    body.extend_from_slice(&encode_outpoint(outpoint));
    body.extend_from_slice(&encode_stored_utxo(entry)?);
    Ok(body)
}

fn encode_utxo_delete(batch_id: u64, outpoint: &OutPoint) -> Vec<u8> {
    let mut body = Vec::with_capacity(1 + 8 + 36);
    body.push(UTXO_DELETE);
    body.extend_from_slice(&batch_id.to_le_bytes());
    body.extend_from_slice(&encode_outpoint(outpoint));
    body
}

fn encode_utxo_commit(batch_id: u64) -> Vec<u8> {
    let mut body = Vec::with_capacity(1 + 8);
    body.push(UTXO_COMMIT);
    body.extend_from_slice(&batch_id.to_le_bytes());
    body
}

fn append_utxo_data_record(file: &mut File, body: &[u8]) -> Result<UtxoLocation> {
    if body.is_empty() || body.len() > MAX_STORED_UTXO_SIZE + 64 {
        bail!("UTXO log record is too large");
    }
    let offset = data_len_after(file)?;
    let length = u32::try_from(body.len()).context("UTXO log record length does not fit u32")?;
    file.write_all(&length.to_le_bytes())?;
    file.write_all(body)?;
    Ok(UtxoLocation { offset, length })
}

fn read_file_at(file: &File, bytes: &mut [u8], offset: u64) -> std::io::Result<usize> {
    #[cfg(unix)]
    {
        file.read_at(bytes, offset)
    }
    #[cfg(windows)]
    {
        file.seek_read(bytes, offset)
    }
}

fn read_exact_at(file: &File, bytes: &mut [u8], offset: u64) -> Result<()> {
    let mut consumed = 0usize;
    while consumed < bytes.len() {
        let read = read_file_at(
            file,
            &mut bytes[consumed..],
            offset
                .checked_add(consumed as u64)
                .context("UTXO read offset overflowed")?,
        )?;
        if read == 0 {
            bail!("unexpected end of UTXO value log");
        }
        consumed += read;
    }
    Ok(())
}

fn read_utxo_data_record(file: &File, location: UtxoLocation) -> Result<Vec<u8>> {
    if location.length as usize > MAX_STORED_UTXO_SIZE + 64 {
        bail!("stored UTXO log record is too large");
    }
    let mut length = [0u8; 4];
    read_exact_at(file, &mut length, location.offset)?;
    let actual = u32::from_le_bytes(length);
    if actual != location.length {
        bail!("UTXO index disagrees with value record length");
    }
    let mut body = vec![0u8; location.length as usize];
    read_exact_at(
        file,
        &mut body,
        location
            .offset
            .checked_add(4)
            .context("UTXO value offset overflowed")?,
    )?;
    Ok(body)
}

fn scan_utxo_data(file: &mut File) -> Result<(HashMap<OutPoint, UtxoLocation>, u64)> {
    let data_len = data_len_after(file)?;
    file.seek(SeekFrom::Start(0))?;
    let mut magic = vec![0u8; UTXO_DATA_MAGIC.len()];
    file.read_exact(&mut magic)?;
    if magic != UTXO_DATA_MAGIC {
        bail!("UTXO store has an unknown format");
    }
    let mut position = UTXO_DATA_MAGIC.len() as u64;
    let mut committed_end = position;
    let mut pending_batch = None;
    let mut pending = Vec::new();
    let mut index = HashMap::new();
    let mut max_batch = 0u64;
    while position < data_len {
        let record_start = position;
        let mut length_bytes = [0u8; 4];
        if let Err(error) = file.read_exact(&mut length_bytes) {
            if error.kind() == ErrorKind::UnexpectedEof {
                break;
            }
            return Err(error.into());
        }
        let length = u32::from_le_bytes(length_bytes);
        let next = position
            .checked_add(4)
            .and_then(|value| value.checked_add(u64::from(length)))
            .context("UTXO log position overflowed")?;
        if length == 0 || usize::try_from(length).unwrap_or(usize::MAX) > MAX_STORED_UTXO_SIZE + 64
        {
            if next > data_len {
                break;
            }
            bail!("UTXO log record has an invalid length");
        }
        if next > data_len {
            break;
        }
        let mut body = vec![0u8; length as usize];
        file.read_exact(&mut body)?;
        let operation = body.first().copied().context("UTXO log record is empty")?;
        match operation {
            UTXO_PUT => {
                if body.len() < 1 + 8 + 36 + 13 {
                    bail!("UTXO put record is truncated");
                }
                let batch_id =
                    u64::from_le_bytes(body[1..9].try_into().expect("fixed UTXO batch identifier"));
                let outpoint = decode_outpoint(&body[9..45])?;
                decode_stored_utxo(&body[45..])?;
                if pending_batch != Some(batch_id) {
                    if pending_batch.is_some() {
                        bail!("UTXO log contains interleaved mutation batches");
                    }
                    pending_batch = Some(batch_id);
                }
                pending.push(PendingUtxoOperation::Put {
                    outpoint,
                    location: UtxoLocation {
                        offset: record_start,
                        length,
                    },
                });
                max_batch = max_batch.max(batch_id);
            }
            UTXO_DELETE => {
                if body.len() != 1 + 8 + 36 {
                    bail!("UTXO delete record has an invalid length");
                }
                let batch_id =
                    u64::from_le_bytes(body[1..9].try_into().expect("fixed UTXO batch identifier"));
                let outpoint = decode_outpoint(&body[9..45])?;
                if pending_batch != Some(batch_id) {
                    if pending_batch.is_some() {
                        bail!("UTXO log contains interleaved mutation batches");
                    }
                    pending_batch = Some(batch_id);
                }
                pending.push(PendingUtxoOperation::Delete { outpoint });
                max_batch = max_batch.max(batch_id);
            }
            UTXO_COMMIT => {
                if body.len() != 1 + 8 {
                    bail!("UTXO commit record has an invalid length");
                }
                let batch_id =
                    u64::from_le_bytes(body[1..9].try_into().expect("fixed UTXO batch identifier"));
                if pending_batch != Some(batch_id) || pending.is_empty() {
                    bail!("UTXO commit does not match a pending batch");
                }
                for operation in pending.drain(..) {
                    match operation {
                        PendingUtxoOperation::Put { outpoint, location } => {
                            index.insert(outpoint, location);
                        }
                        PendingUtxoOperation::Delete { outpoint } => {
                            index.remove(&outpoint);
                        }
                    }
                }
                pending_batch = None;
                committed_end = next;
                max_batch = max_batch.max(batch_id);
            }
            _ => bail!("UTXO log contains an unknown operation"),
        }
        position = next;
    }
    if pending_batch.is_some() || position != committed_end {
        file.set_len(committed_end)?;
        file.seek(SeekFrom::End(0))?;
    }
    Ok((
        index,
        max_batch
            .checked_add(1)
            .context("UTXO batch identifier exhausted")?,
    ))
}

fn load_utxo_index(file: &mut File, data_len: u64) -> Result<Option<UtxoIndexState>> {
    let index_len = file.metadata()?.len();
    if index_len < UTXO_INDEX_MAGIC.len() as u64 {
        return Ok(None);
    }
    file.seek(SeekFrom::Start(0))?;
    let mut magic = vec![0u8; UTXO_INDEX_MAGIC.len()];
    file.read_exact(&mut magic)?;
    if magic != UTXO_INDEX_MAGIC {
        return Ok(None);
    }
    let mut position = UTXO_INDEX_MAGIC.len() as u64;
    let mut pending_batch = None;
    let mut pending = Vec::new();
    let mut index = HashMap::new();
    let mut last_data_end = None;
    let mut max_batch = 0u64;
    let mut stored_next_batch_id = None;
    let mut stored_generation = None;
    while position < index_len {
        let mut length_bytes = [0u8; 4];
        if file.read_exact(&mut length_bytes).is_err() {
            return Ok(None);
        }
        let length = u32::from_le_bytes(length_bytes);
        let next = position
            .checked_add(4)
            .and_then(|value| value.checked_add(u64::from(length)))
            .context("UTXO index position overflowed")?;
        if next > index_len || length == 0 || length > 128 {
            return Ok(None);
        }
        let mut body = vec![0u8; length as usize];
        file.read_exact(&mut body)?;
        let operation = body
            .first()
            .copied()
            .context("UTXO index record is empty")?;
        match operation {
            UTXO_PUT => {
                if body.len() != 1 + 8 + 8 + 4 + 36 {
                    return Ok(None);
                }
                let batch_id = u64::from_le_bytes(body[1..9].try_into().unwrap());
                let offset = u64::from_le_bytes(body[9..17].try_into().unwrap());
                let value_length = u32::from_le_bytes(body[17..21].try_into().unwrap());
                let outpoint = decode_outpoint(&body[21..57])?;
                if value_length == 0
                    || value_length as usize > MAX_STORED_UTXO_SIZE + 64
                    || offset < UTXO_DATA_MAGIC.len() as u64
                    || offset
                        .checked_add(4)
                        .and_then(|end| end.checked_add(u64::from(value_length)))
                        .is_none_or(|end| end > data_len)
                {
                    return Ok(None);
                }
                if pending_batch != Some(batch_id) {
                    if pending_batch.is_some() {
                        return Ok(None);
                    }
                    pending_batch = Some(batch_id);
                }
                pending.push(PendingUtxoOperation::Put {
                    outpoint,
                    location: UtxoLocation {
                        offset,
                        length: value_length,
                    },
                });
                max_batch = max_batch.max(batch_id);
            }
            UTXO_DELETE => {
                if body.len() != 1 + 8 + 36 {
                    return Ok(None);
                }
                let batch_id = u64::from_le_bytes(body[1..9].try_into().unwrap());
                let outpoint = decode_outpoint(&body[9..45])?;
                if pending_batch != Some(batch_id) {
                    if pending_batch.is_some() {
                        return Ok(None);
                    }
                    pending_batch = Some(batch_id);
                }
                pending.push(PendingUtxoOperation::Delete { outpoint });
                max_batch = max_batch.max(batch_id);
            }
            UTXO_COMMIT => {
                if body.len() != 1 + 8 + 8 + 8 + 8 {
                    return Ok(None);
                }
                let batch_id = u64::from_le_bytes(body[1..9].try_into().unwrap());
                let data_end = u64::from_le_bytes(body[9..17].try_into().unwrap());
                let next_batch_id = u64::from_le_bytes(body[17..25].try_into().unwrap());
                let generation = u64::from_le_bytes(body[25..33].try_into().unwrap());
                if next_batch_id == 0 {
                    return Ok(None);
                }
                if generation == 0
                    || data_end < UTXO_DATA_MAGIC.len() as u64
                    || data_end > data_len
                    || last_data_end.is_some_and(|previous| data_end < previous)
                    || stored_generation.is_some_and(|previous| previous != generation)
                {
                    return Ok(None);
                }
                if pending_batch != Some(batch_id) || (pending.is_empty() && batch_id != 0) {
                    return Ok(None);
                }
                for operation in pending.drain(..) {
                    match operation {
                        PendingUtxoOperation::Put { outpoint, location } => {
                            index.insert(outpoint, location);
                        }
                        PendingUtxoOperation::Delete { outpoint } => {
                            index.remove(&outpoint);
                        }
                    }
                }
                pending_batch = None;
                last_data_end = Some(data_end);
                stored_next_batch_id = Some(next_batch_id);
                stored_generation = Some(generation);
                max_batch = max_batch.max(batch_id);
            }
            _ => return Ok(None),
        }
        position = next;
    }
    if pending_batch.is_some() || last_data_end != Some(data_len) {
        return Ok(None);
    }
    Ok(Some((
        index,
        stored_next_batch_id.unwrap_or(
            max_batch
                .checked_add(1)
                .context("UTXO batch identifier exhausted")?,
        ),
        stored_generation.context("UTXO index has no generation checkpoint")?,
    )))
}

fn append_utxo_index_batch(
    file: &mut File,
    batch_id: u64,
    data_end: u64,
    next_batch_id: u64,
    generation: u64,
    operations: &[PendingUtxoOperation],
) -> Result<()> {
    file.seek(SeekFrom::End(0))?;
    for operation in operations {
        let mut body = Vec::with_capacity(64);
        match operation {
            PendingUtxoOperation::Put { outpoint, location } => {
                body.push(UTXO_PUT);
                body.extend_from_slice(&batch_id.to_le_bytes());
                body.extend_from_slice(&location.offset.to_le_bytes());
                body.extend_from_slice(&location.length.to_le_bytes());
                body.extend_from_slice(&encode_outpoint(outpoint));
            }
            PendingUtxoOperation::Delete { outpoint } => {
                body.push(UTXO_DELETE);
                body.extend_from_slice(&batch_id.to_le_bytes());
                body.extend_from_slice(&encode_outpoint(outpoint));
            }
        }
        let length = u32::try_from(body.len()).context("UTXO index record is too large")?;
        file.write_all(&length.to_le_bytes())?;
        file.write_all(&body)?;
    }
    let mut commit = Vec::with_capacity(33);
    commit.push(UTXO_COMMIT);
    commit.extend_from_slice(&batch_id.to_le_bytes());
    commit.extend_from_slice(&data_end.to_le_bytes());
    commit.extend_from_slice(&next_batch_id.to_le_bytes());
    commit.extend_from_slice(&generation.to_le_bytes());
    file.write_all(&(u32::try_from(commit.len()).unwrap()).to_le_bytes())?;
    file.write_all(&commit)?;
    Ok(())
}

fn rewrite_utxo_index(
    file: &mut File,
    data_end: u64,
    next_batch_id: u64,
    generation: u64,
    index: &HashMap<OutPoint, UtxoLocation>,
) -> Result<()> {
    file.set_len(0)?;
    file.seek(SeekFrom::End(0))?;
    file.write_all(UTXO_INDEX_MAGIC)?;
    let checkpoint_batch = 0u64;
    let operations = index
        .iter()
        .map(|(outpoint, location)| PendingUtxoOperation::Put {
            outpoint: *outpoint,
            location: *location,
        })
        .collect::<Vec<_>>();
    append_utxo_index_batch(
        file,
        checkpoint_batch,
        data_end,
        next_batch_id,
        generation,
        &operations,
    )?;
    file.sync_data()?;
    Ok(())
}

impl CoinStatsStore {
    pub fn open(directory: impl AsRef<Path>) -> Result<Self> {
        let directory = directory.as_ref();
        create_dir_all(directory)
            .with_context(|| format!("creating coinstats directory {}", directory.display()))?;
        let path = directory.join("coinstats.dat");
        let mut file = OpenOptions::new()
            .create(true)
            .read(true)
            .append(true)
            .open(&path)
            .with_context(|| format!("opening coinstats store {}", path.display()))?;
        let index_path = directory.join("coinstats.index");
        let mut index_file = OpenOptions::new()
            .create(true)
            .truncate(false)
            .read(true)
            .write(true)
            .open(&index_path)
            .with_context(|| format!("opening coinstats index {}", index_path.display()))?;
        let data_len = file.metadata()?.len();
        let index = match load_index(&mut index_file, data_len)? {
            Some(index) => index,
            None => {
                let index = scan_coinstats_index(&mut file)?;
                rewrite_index(&mut index_file, file.metadata()?.len(), &index)?;
                index
            }
        };
        Ok(Self {
            path,
            file,
            index_file,
            index,
        })
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn contains(&self, hash: &BlockHash) -> bool {
        self.index.contains_key(hash)
    }

    pub fn insert(&mut self, record: &CoinStatsRecord) -> Result<()> {
        if self.index.contains_key(&record.block_hash) {
            return Ok(());
        }
        let bytes = serde_json::to_vec(record).context("encoding coinstats record")?;
        if bytes.len() > MAX_STORED_COINSTATS_SIZE {
            bail!("coinstats record is too large: {} bytes", bytes.len());
        }
        let offset = self.file.seek(SeekFrom::End(0))?;
        let length = u32::try_from(bytes.len()).context("coinstats length does not fit u32")?;
        self.file.write_all(&length.to_le_bytes())?;
        self.file.write_all(&bytes)?;
        self.file.sync_data()?;
        let record_index = Record { offset, length };
        persist_index_entry(
            &mut self.index_file,
            offset + 4 + bytes.len() as u64,
            record.block_hash,
            record_index,
        )?;
        self.index.insert(record.block_hash, record_index);
        Ok(())
    }

    pub fn get(&mut self, hash: &BlockHash) -> Result<Option<CoinStatsRecord>> {
        let Some(record) = self.index.get(hash).copied() else {
            return Ok(None);
        };
        if record.length as usize > MAX_STORED_COINSTATS_SIZE {
            bail!("stored coinstats record is too large");
        }
        self.file.seek(SeekFrom::Start(record.offset))?;
        let mut length = [0u8; 4];
        self.file.read_exact(&mut length)?;
        let actual = u32::from_le_bytes(length);
        if actual != record.length {
            bail!("coinstats store index disagrees with record length");
        }
        let mut bytes = vec![0u8; record.length as usize];
        self.file.read_exact(&mut bytes)?;
        let decoded: CoinStatsRecord =
            serde_json::from_slice(&bytes).context("decoding stored coinstats record")?;
        if decoded.block_hash != *hash {
            bail!("stored coinstats hash does not match coinstats index");
        }
        Ok(Some(decoded))
    }
}

/// Durable transaction bodies retained for the in-process Electrum service.
///
/// The normal block store may prune old block bodies, but Electrum clients
/// still expect `transaction.get`, merkle proofs, and `id_from_pos` to work
/// for historical active-chain transactions. Records are keyed by block hash
/// so chainstate can validate the active location before reading them, and the
/// index remains compact because it does not duplicate the transaction index.
pub struct ElectrumBlockStore {
    path: PathBuf,
    file: File,
    index_file: File,
    index: HashMap<BlockHash, Record>,
}

impl ElectrumBlockStore {
    pub fn open(directory: impl AsRef<Path>) -> Result<Self> {
        let directory = directory.as_ref();
        create_dir_all(directory).with_context(|| {
            format!(
                "creating Electrum transaction store {}",
                directory.display()
            )
        })?;
        let path = directory.join("txblocks.dat");
        let mut file = OpenOptions::new()
            .create(true)
            .read(true)
            .append(true)
            .open(&path)
            .with_context(|| format!("opening Electrum transaction store {}", path.display()))?;
        let index_path = directory.join("txblocks.index");
        let mut index_file = OpenOptions::new()
            .create(true)
            .truncate(false)
            .read(true)
            .write(true)
            .open(&index_path)
            .with_context(|| {
                format!(
                    "opening Electrum transaction index {}",
                    index_path.display()
                )
            })?;
        let data_len = file.metadata()?.len();
        let index = match load_index_with_limit(
            &mut index_file,
            data_len,
            MAX_STORED_ELECTRUM_BLOCK_SIZE + 32,
        )? {
            Some(index) => index,
            None => {
                let index = scan_electrum_index(&mut file)?;
                rewrite_index(&mut index_file, file.metadata()?.len(), &index)?;
                index
            }
        };
        Ok(Self {
            path,
            file,
            index_file,
            index,
        })
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn contains(&self, hash: &BlockHash) -> bool {
        self.index.contains_key(hash)
    }

    pub fn disk_usage(&self) -> Result<u64> {
        self.file
            .metadata()?
            .len()
            .checked_add(self.index_file.metadata()?.len())
            .context("Electrum transaction store size overflowed")
    }

    pub fn insert(&mut self, block: &Block) -> Result<BlockHash> {
        let hash = block.block_hash();
        if self.index.contains_key(&hash) {
            return Ok(hash);
        }
        let mut bytes = hash.to_byte_array().to_vec();
        bytes.extend_from_slice(&serialize(&block.txdata));
        if bytes.len() > MAX_STORED_ELECTRUM_BLOCK_SIZE + 32 {
            bail!(
                "Electrum transaction record is too large: {} bytes",
                bytes.len()
            );
        }
        let offset = self.file.seek(SeekFrom::End(0))?;
        let length = u32::try_from(bytes.len())
            .context("Electrum transaction record length does not fit u32")?;
        self.file.write_all(&length.to_le_bytes())?;
        self.file.write_all(&bytes)?;
        self.file.sync_data()?;
        let record = Record { offset, length };
        persist_index_entry(
            &mut self.index_file,
            offset + 4 + u64::from(length),
            hash,
            record,
        )?;
        self.index.insert(hash, record);
        Ok(hash)
    }

    pub fn transaction(
        &mut self,
        block_hash: &BlockHash,
        transaction_index: usize,
    ) -> Result<Option<Transaction>> {
        let transactions = self.transactions(block_hash)?;
        Ok(transactions.and_then(|transactions| transactions.into_iter().nth(transaction_index)))
    }

    pub fn merkle_branch(
        &mut self,
        block_hash: &BlockHash,
        transaction_index: usize,
    ) -> Result<Option<Vec<Txid>>> {
        let Some(transactions) = self.transactions(block_hash)? else {
            return Ok(None);
        };
        if transaction_index >= transactions.len() {
            return Ok(None);
        }
        Ok(Some(merkle_branch_for_transactions(
            &transactions,
            transaction_index,
        )))
    }

    fn transactions(&mut self, block_hash: &BlockHash) -> Result<Option<Vec<Transaction>>> {
        let Some(record) = self.index.get(block_hash).copied() else {
            return Ok(None);
        };
        if record.length < 32 || record.length as usize > MAX_STORED_ELECTRUM_BLOCK_SIZE + 32 {
            bail!("stored Electrum transaction record is too large or truncated")
        }
        self.file.seek(SeekFrom::Start(record.offset))?;
        let mut length = [0u8; 4];
        self.file.read_exact(&mut length)?;
        let actual = u32::from_le_bytes(length);
        if actual != record.length {
            bail!("Electrum transaction store index disagrees with record length")
        }
        let mut bytes = vec![0u8; record.length as usize];
        self.file.read_exact(&mut bytes)?;
        let stored_hash = BlockHash::from_byte_array(
            bytes[..32]
                .try_into()
                .expect("Electrum block hash has fixed width"),
        );
        if stored_hash != *block_hash {
            bail!("stored Electrum block hash does not match its index")
        }
        let transactions: Vec<Transaction> =
            deserialize(&bytes[32..]).context("decoding stored Electrum transactions")?;
        Ok(Some(transactions))
    }
}

fn merkle_branch_for_transactions(
    transactions: &[Transaction],
    transaction_index: usize,
) -> Vec<Txid> {
    let mut layer: Vec<Txid> = transactions.iter().map(Transaction::compute_txid).collect();
    let mut index = transaction_index;
    let mut branch = Vec::new();
    while layer.len() > 1 {
        let sibling = if index ^ 1 < layer.len() {
            index ^ 1
        } else {
            index
        };
        branch.push(layer[sibling]);
        let mut next = Vec::with_capacity(layer.len().div_ceil(2));
        for pair in layer.chunks(2) {
            let left = pair[0];
            let right = *pair.get(1).unwrap_or(&left);
            let mut engine = bitcoin::hashes::sha256d::Hash::engine();
            engine.input(&left.to_raw_hash().to_byte_array());
            engine.input(&right.to_raw_hash().to_byte_array());
            next.push(Txid::from_raw_hash(
                bitcoin::hashes::sha256d::Hash::from_engine(engine),
            ));
        }
        layer = next;
        index /= 2;
    }
    branch
}

fn scan_electrum_index(file: &mut File) -> Result<HashMap<BlockHash, Record>> {
    file.seek(SeekFrom::Start(0))?;
    let mut index = HashMap::new();
    let data_len = file.metadata()?.len();
    loop {
        let offset = file.stream_position()?;
        let mut length_bytes = [0u8; 4];
        match file.read_exact(&mut length_bytes) {
            Ok(()) => {}
            Err(error) if error.kind() == ErrorKind::UnexpectedEof => {
                file.set_len(offset)?;
                break;
            }
            Err(error) => return Err(error.into()),
        }
        let length = u32::from_le_bytes(length_bytes);
        let end = offset.saturating_add(4).saturating_add(u64::from(length));
        if end > data_len {
            file.set_len(offset)?;
            break;
        }
        if length < 32 || length as usize > MAX_STORED_ELECTRUM_BLOCK_SIZE + 32 {
            bail!(
                "invalid Electrum transaction record length {} at offset {}",
                length,
                offset
            )
        }
        let mut bytes = vec![0u8; length as usize];
        file.read_exact(&mut bytes).map_err(|error| {
            anyhow::anyhow!(
                "truncated Electrum transaction record at offset {}: {}",
                offset,
                error
            )
        })?;
        let hash = BlockHash::from_byte_array(
            bytes[..32]
                .try_into()
                .expect("Electrum block hash has fixed width"),
        );
        let _: Vec<Transaction> = deserialize(&bytes[32..])
            .with_context(|| format!("decoding Electrum transaction record at offset {offset}"))?;
        if index.insert(hash, Record { offset, length }).is_some() {
            bail!("duplicate block hash in Electrum transaction store")
        }
    }
    file.seek(SeekFrom::End(0))?;
    Ok(index)
}

fn scan_coinstats_index(file: &mut File) -> Result<HashMap<BlockHash, Record>> {
    file.seek(SeekFrom::Start(0))?;
    let mut index = HashMap::new();
    let data_len = file.metadata()?.len();
    loop {
        let offset = file.stream_position()?;
        let mut length_bytes = [0u8; 4];
        match file.read_exact(&mut length_bytes) {
            Ok(()) => {}
            Err(error) if error.kind() == ErrorKind::UnexpectedEof => {
                file.set_len(offset)?;
                break;
            }
            Err(error) => return Err(error.into()),
        }
        let length = u32::from_le_bytes(length_bytes);
        let end = offset.saturating_add(4).saturating_add(u64::from(length));
        if end > data_len {
            file.set_len(offset)?;
            break;
        }
        if length == 0 || length as usize > MAX_STORED_COINSTATS_SIZE {
            bail!(
                "invalid coinstats record length {} at offset {}",
                length,
                offset
            );
        }
        let mut bytes = vec![0u8; length as usize];
        file.read_exact(&mut bytes).map_err(|error| {
            anyhow::anyhow!("truncated coinstats record at offset {}: {}", offset, error)
        })?;
        let record: CoinStatsRecord = serde_json::from_slice(&bytes)
            .with_context(|| format!("decoding coinstats record at offset {offset}"))?;
        if index
            .insert(record.block_hash, Record { offset, length })
            .is_some()
        {
            bail!("duplicate block hash in coinstats store");
        }
    }
    file.seek(SeekFrom::End(0))?;
    Ok(index)
}

fn load_filter_index(file: &mut File, data_len: u64) -> Result<Option<HashMap<BlockHash, Record>>> {
    let index_len = file.metadata()?.len();
    if index_len < INDEX_HEADER_SIZE || (index_len - INDEX_HEADER_SIZE) % INDEX_RECORD_SIZE != 0 {
        return Ok(None);
    }
    file.seek(SeekFrom::Start(0))?;
    let mut expected_data_len = [0u8; 8];
    file.read_exact(&mut expected_data_len)?;
    if u64::from_le_bytes(expected_data_len) != data_len {
        return Ok(None);
    }
    let count = (index_len - INDEX_HEADER_SIZE) / INDEX_RECORD_SIZE;
    let mut index = HashMap::with_capacity(count as usize);
    for _ in 0..count {
        let mut hash_bytes = [0u8; 32];
        file.read_exact(&mut hash_bytes)?;
        let mut offset_bytes = [0u8; 8];
        file.read_exact(&mut offset_bytes)?;
        let mut length_bytes = [0u8; 4];
        file.read_exact(&mut length_bytes)?;
        let record = Record {
            offset: u64::from_le_bytes(offset_bytes),
            length: u32::from_le_bytes(length_bytes),
        };
        if record.length < 64
            || record.length as usize > MAX_STORED_FILTER_SIZE + 64
            || record
                .offset
                .saturating_add(4)
                .saturating_add(record.length as u64)
                > data_len
        {
            return Ok(None);
        }
        let hash = BlockHash::from_byte_array(hash_bytes);
        if index.insert(hash, record).is_some() {
            return Ok(None);
        }
    }
    if !index_layout_is_contiguous(&index, data_len) {
        return Ok(None);
    }
    Ok(Some(index))
}

fn scan_filter_index(file: &mut File) -> Result<HashMap<BlockHash, Record>> {
    file.seek(SeekFrom::Start(0))?;
    let mut index = HashMap::new();
    let data_len = file.metadata()?.len();
    loop {
        let offset = file.stream_position()?;
        let mut length_bytes = [0u8; 4];
        match file.read_exact(&mut length_bytes) {
            Ok(()) => {}
            Err(error) if error.kind() == ErrorKind::UnexpectedEof => {
                file.set_len(offset)?;
                break;
            }
            Err(error) => return Err(error.into()),
        }
        let length = u32::from_le_bytes(length_bytes);
        let end = offset.saturating_add(4).saturating_add(u64::from(length));
        if end > data_len {
            file.set_len(offset)?;
            break;
        }
        if length < 64 || length as usize > MAX_STORED_FILTER_SIZE + 64 {
            bail!(
                "invalid filter record length {} at offset {}",
                length,
                offset
            );
        }
        let mut bytes = vec![0u8; length as usize];
        file.read_exact(&mut bytes).map_err(|error| {
            anyhow::anyhow!("truncated filter record at offset {}: {}", offset, error)
        })?;
        let hash = BlockHash::from_byte_array(
            bytes[..32]
                .try_into()
                .expect("filter block hash has fixed width"),
        );
        if index.insert(hash, Record { offset, length }).is_some() {
            bail!("duplicate block hash in filter store");
        }
    }
    file.seek(SeekFrom::End(0))?;
    Ok(index)
}

fn load_index(file: &mut File, data_len: u64) -> Result<Option<HashMap<BlockHash, Record>>> {
    load_index_with_limit(file, data_len, MAX_STORED_BLOCK_SIZE)
}

fn load_index_with_limit(
    file: &mut File,
    data_len: u64,
    max_record_size: usize,
) -> Result<Option<HashMap<BlockHash, Record>>> {
    let index_len = file.metadata()?.len();
    if index_len < INDEX_HEADER_SIZE || (index_len - INDEX_HEADER_SIZE) % INDEX_RECORD_SIZE != 0 {
        return Ok(None);
    }
    file.seek(SeekFrom::Start(0))?;
    let mut expected_data_len = [0u8; 8];
    file.read_exact(&mut expected_data_len)?;
    if u64::from_le_bytes(expected_data_len) != data_len {
        return Ok(None);
    }
    let count = (index_len - INDEX_HEADER_SIZE) / INDEX_RECORD_SIZE;
    let mut index = HashMap::with_capacity(count as usize);
    for _ in 0..count {
        let mut hash_bytes = [0u8; 32];
        file.read_exact(&mut hash_bytes)?;
        let mut offset_bytes = [0u8; 8];
        file.read_exact(&mut offset_bytes)?;
        let mut length_bytes = [0u8; 4];
        file.read_exact(&mut length_bytes)?;
        let record = Record {
            offset: u64::from_le_bytes(offset_bytes),
            length: u32::from_le_bytes(length_bytes),
        };
        if record.length == 0
            || record.length as usize > max_record_size
            || record
                .offset
                .saturating_add(4)
                .saturating_add(record.length as u64)
                > data_len
        {
            return Ok(None);
        }
        let hash = BlockHash::from_byte_array(hash_bytes);
        if index.insert(hash, record).is_some() {
            return Ok(None);
        }
    }
    if !index_layout_is_contiguous(&index, data_len) {
        return Ok(None);
    }
    Ok(Some(index))
}

fn scan_chainstate_index(file: &mut File) -> Result<HashMap<BlockHash, Record>> {
    file.seek(SeekFrom::Start(0))?;
    let mut index = HashMap::new();
    let data_len = file.metadata()?.len();
    loop {
        let offset = file.stream_position()?;
        let mut length_bytes = [0u8; 4];
        match file.read_exact(&mut length_bytes) {
            Ok(()) => {}
            Err(error) if error.kind() == ErrorKind::UnexpectedEof => {
                file.set_len(offset)?;
                break;
            }
            Err(error) => return Err(error.into()),
        }
        let length = u32::from_le_bytes(length_bytes);
        let end = offset.saturating_add(4).saturating_add(u64::from(length));
        if end > data_len {
            file.set_len(offset)?;
            break;
        }
        if length < 32 || length as usize > MAX_STORED_CHAINSTATE_DELTA_SIZE + 32 {
            bail!(
                "invalid chainstate delta length {} at offset {}",
                length,
                offset
            );
        }
        let mut bytes = vec![0u8; length as usize];
        file.read_exact(&mut bytes).map_err(|error| {
            anyhow::anyhow!("truncated chainstate delta at offset {}: {}", offset, error)
        })?;
        let hash = BlockHash::from_byte_array(
            bytes[..32]
                .try_into()
                .expect("chainstate delta hash has fixed width"),
        );
        if index.insert(hash, Record { offset, length }).is_some() {
            bail!("duplicate block hash in chainstate delta store");
        }
    }
    file.seek(SeekFrom::End(0))?;
    Ok(index)
}

fn rewrite_index(file: &mut File, data_len: u64, index: &HashMap<BlockHash, Record>) -> Result<()> {
    file.set_len(0)?;
    file.seek(SeekFrom::Start(0))?;
    file.write_all(&data_len.to_le_bytes())?;
    let mut entries: Vec<(&BlockHash, &Record)> = index.iter().collect();
    entries.sort_by_key(|(hash, _)| hash.to_string());
    for (hash, record) in entries {
        file.write_all(&hash.to_byte_array())?;
        file.write_all(&record.offset.to_le_bytes())?;
        file.write_all(&record.length.to_le_bytes())?;
    }
    file.sync_data()?;
    Ok(())
}

fn persist_index_entry(
    file: &mut File,
    data_len: u64,
    hash: BlockHash,
    record: Record,
) -> Result<()> {
    file.seek(SeekFrom::Start(0))?;
    file.write_all(&data_len.to_le_bytes())?;
    file.seek(SeekFrom::End(0))?;
    file.write_all(&hash.to_byte_array())?;
    file.write_all(&record.offset.to_le_bytes())?;
    file.write_all(&record.length.to_le_bytes())?;
    file.sync_data()?;
    Ok(())
}

fn index_layout_is_contiguous(index: &HashMap<BlockHash, Record>, data_len: u64) -> bool {
    let mut records = index.values().copied().collect::<Vec<_>>();
    records.sort_unstable_by_key(|record| record.offset);
    let mut expected_offset = 0u64;
    for record in records {
        if record.offset != expected_offset {
            return false;
        }
        let Some(end) = record
            .offset
            .checked_add(4)
            .and_then(|offset| offset.checked_add(u64::from(record.length)))
        else {
            return false;
        };
        expected_offset = end;
    }
    expected_offset == data_len
}

fn scan_index(file: &mut File, xor_key: XorKey) -> Result<HashMap<BlockHash, Record>> {
    file.seek(SeekFrom::Start(0))?;
    let mut index = HashMap::new();
    let data_len = file.metadata()?.len();
    loop {
        let offset = file.stream_position()?;
        let mut length_bytes = [0u8; 4];
        match file.read_exact(&mut length_bytes) {
            Ok(()) => {}
            Err(error) if error.kind() == ErrorKind::UnexpectedEof => {
                file.set_len(offset)?;
                break;
            }
            Err(error) => return Err(error.into()),
        }
        xor_key.apply(&mut length_bytes, offset);
        let length = u32::from_le_bytes(length_bytes);
        let end = offset.saturating_add(4).saturating_add(u64::from(length));
        if end > data_len {
            file.set_len(offset)?;
            break;
        }
        if length == 0 || length as usize > MAX_STORED_BLOCK_SIZE {
            bail!(
                "invalid block record length {} at offset {}",
                length,
                offset
            );
        }
        let mut bytes = vec![0u8; length as usize];
        file.read_exact(&mut bytes).map_err(|error| {
            anyhow::anyhow!("truncated block record at offset {}: {}", offset, error)
        })?;
        xor_key.apply(&mut bytes, offset + 4);
        let block: Block = deserialize(&bytes).context("decoding block record")?;
        if index
            .insert(block.block_hash(), Record { offset, length })
            .is_some()
        {
            bail!("duplicate block hash in block store");
        }
    }
    file.seek(SeekFrom::End(0))?;
    Ok(index)
}

fn scan_undo_index(file: &mut File, xor_key: XorKey) -> Result<HashMap<BlockHash, Record>> {
    file.seek(SeekFrom::Start(0))?;
    let mut index = HashMap::new();
    let mut max_end = 0u64;
    let data_len = file.metadata()?.len();
    loop {
        let offset = file.stream_position()?;
        let mut length_bytes = [0u8; 4];
        match file.read_exact(&mut length_bytes) {
            Ok(()) => {}
            Err(error) if error.kind() == ErrorKind::UnexpectedEof => {
                file.set_len(offset)?;
                break;
            }
            Err(error) => return Err(error.into()),
        }
        xor_key.apply(&mut length_bytes, offset);
        let length = u32::from_le_bytes(length_bytes);
        let end = offset.saturating_add(4).saturating_add(u64::from(length));
        if end > data_len {
            file.set_len(offset)?;
            break;
        }
        if length == 0 || length as usize > MAX_STORED_UNDO_SIZE {
            bail!("invalid undo record length {} at offset {}", length, offset);
        }
        let mut bytes = vec![0u8; length as usize];
        file.read_exact(&mut bytes).map_err(|error| {
            anyhow::anyhow!("truncated undo record at offset {}: {}", offset, error)
        })?;
        xor_key.apply(&mut bytes, offset + 4);
        let (hash, _) = decode_undo_record(&bytes)?;
        if index.insert(hash, Record { offset, length }).is_some() {
            bail!("duplicate block hash in undo store")
        }
        max_end = offset + 4 + u64::from(length);
    }
    if max_end != file.metadata()?.len() && max_end != 0 {
        bail!("undo store contains trailing data")
    }
    Ok(index)
}

fn encode_undo_record(hash: BlockHash, undo: &[Vec<TxOut>]) -> Result<Vec<u8>> {
    let mut bytes = serialize(&hash);
    bytes.extend_from_slice(&serialize(&VarInt(undo.len() as u64)));
    for outputs in undo {
        bytes.extend_from_slice(&serialize(&VarInt(outputs.len() as u64)));
        for output in outputs {
            bytes.extend_from_slice(&serialize(output));
        }
    }
    Ok(bytes)
}

fn decode_undo_record(bytes: &[u8]) -> Result<(BlockHash, Vec<Vec<TxOut>>)> {
    let (hash, mut consumed) =
        deserialize_partial::<BlockHash>(bytes).context("decoding stored block undo hash")?;
    let (transaction_count, count_consumed) = deserialize_partial::<VarInt>(&bytes[consumed..])
        .context("decoding stored block undo transaction count")?;
    consumed = consumed.saturating_add(count_consumed);
    let transaction_count = usize::try_from(transaction_count.0)
        .context("stored block undo transaction count is too large")?;
    if transaction_count > MAX_STORED_UNDO_SIZE {
        bail!("stored block undo transaction count is unreasonable")
    }
    let mut undo = Vec::with_capacity(transaction_count);
    for _ in 0..transaction_count {
        let (output_count, count_consumed) = deserialize_partial::<VarInt>(&bytes[consumed..])
            .context("decoding stored block undo output count")?;
        consumed = consumed.saturating_add(count_consumed);
        let output_count = usize::try_from(output_count.0)
            .context("stored block undo output count is too large")?;
        if output_count > MAX_STORED_UNDO_SIZE {
            bail!("stored block undo output count is unreasonable")
        }
        let mut outputs = Vec::with_capacity(output_count);
        for _ in 0..output_count {
            let (output, output_consumed) = deserialize_partial::<TxOut>(&bytes[consumed..])
                .context("decoding stored block undo output")?;
            consumed = consumed.saturating_add(output_consumed);
            outputs.push(output);
        }
        undo.push(outputs);
    }
    if consumed != bytes.len() {
        bail!("stored block undo contains trailing data")
    }
    Ok((hash, undo))
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::Network;
    use bitcoin::blockdata::constants::genesis_block;
    use bitcoin::hashes::Hash;
    use std::collections::HashSet;

    #[test]
    fn persists_and_reopens_genesis() {
        let directory = tempfile::tempdir().unwrap();
        let block = genesis_block(Network::Regtest);
        let hash = {
            let mut store = BlockStore::open(directory.path()).unwrap();
            let hash = store.insert(&block).unwrap();
            assert_eq!(store.get(&hash).unwrap().unwrap(), block);
            hash
        };
        let index_path = directory.path().join("blocks.index");
        assert!(index_path.exists());
        std::fs::write(&index_path, b"corrupt").unwrap();
        let mut reopened = BlockStore::open(directory.path()).unwrap();
        assert!(reopened.contains(&hash));
        assert_eq!(reopened.get(&hash).unwrap().unwrap(), block);
    }

    #[test]
    fn utxo_batches_reopen_and_recover_an_uncommitted_tail() {
        let directory = tempfile::tempdir().unwrap();
        let first = OutPoint::new(Txid::from_byte_array([1; 32]), 0);
        let second = OutPoint::new(Txid::from_byte_array([2; 32]), 1);
        let first_entry = StoredUtxo {
            output: TxOut {
                value: bitcoin::Amount::from_sat(50_000),
                script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
            },
            height: 12,
            median_time_past: 11,
            coinbase: true,
        };
        let second_entry = StoredUtxo {
            output: TxOut {
                value: bitcoin::Amount::from_sat(40_000),
                script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x52]),
            },
            height: 13,
            median_time_past: 12,
            coinbase: false,
        };
        {
            let mut store = UtxoStore::open(directory.path()).unwrap();
            store
                .apply_batch(&[], &[(first, first_entry.clone())])
                .unwrap();
            assert_eq!(store.get(&first).unwrap(), Some(first_entry.clone()));
            store
                .apply_batch(&[first], &[(second, second_entry.clone())])
                .unwrap();
            assert!(!store.contains(&first));
            assert_eq!(store.get(&second).unwrap(), Some(second_entry.clone()));
        }

        let data_path = directory.path().join("utxos.dat");
        let committed_len = std::fs::metadata(&data_path).unwrap().len();
        {
            let reopened = UtxoStore::open(directory.path()).unwrap();
            assert_eq!(reopened.len(), 1);
            assert_eq!(reopened.get(&second).unwrap(), Some(second_entry.clone()));
        }

        let mut file = OpenOptions::new().append(true).open(&data_path).unwrap();
        let uncommitted = encode_utxo_put(
            99,
            &first,
            &StoredUtxo {
                output: TxOut {
                    value: bitcoin::Amount::from_sat(1),
                    script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x53]),
                },
                height: 14,
                median_time_past: 13,
                coinbase: false,
            },
        )
        .unwrap();
        file.write_all(&(u32::try_from(uncommitted.len()).unwrap()).to_le_bytes())
            .unwrap();
        file.write_all(&uncommitted).unwrap();
        file.sync_data().unwrap();
        drop(file);

        let recovered = UtxoStore::open(directory.path()).unwrap();
        assert_eq!(recovered.get(&first).unwrap(), None);
        assert_eq!(recovered.get(&second).unwrap(), Some(second_entry));
        assert_eq!(std::fs::metadata(data_path).unwrap().len(), committed_len);
    }

    #[test]
    fn utxo_read_cache_is_invalidated_by_replacement_and_clear() {
        let directory = tempfile::tempdir().unwrap();
        let outpoint = OutPoint::new(Txid::from_byte_array([9u8; 32]), 0);
        let first = StoredUtxo {
            output: TxOut {
                value: bitcoin::Amount::from_sat(1_000),
                script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
            },
            height: 1,
            median_time_past: 1,
            coinbase: false,
        };
        let second = StoredUtxo {
            output: TxOut {
                value: bitcoin::Amount::from_sat(2_000),
                script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x52]),
            },
            height: 2,
            median_time_past: 2,
            coinbase: true,
        };
        let mut store = UtxoStore::open(directory.path()).unwrap();
        store.configure_cache_size_mib(4);
        store
            .apply_batch(&[], &[(outpoint, first.clone())])
            .unwrap();
        assert_eq!(store.get(&outpoint).unwrap(), Some(first));
        assert_eq!(store.read_cache.lock().entries.len(), 1);

        store
            .apply_batch(&[outpoint], &[(outpoint, second.clone())])
            .unwrap();
        assert_eq!(store.get(&outpoint).unwrap(), Some(second));
        assert_eq!(store.read_cache.lock().entries.len(), 1);

        store.clear().unwrap();
        assert_eq!(store.get(&outpoint).unwrap(), None);
        assert!(store.read_cache.lock().entries.is_empty());
    }

    #[test]
    fn electrum_history_batches_reopen_and_recover_an_uncommitted_tail() {
        let directory = tempfile::tempdir().unwrap();
        let script_hash = hex::encode([1u8; 32]);
        let first_txid = Txid::from_byte_array([2u8; 32]);
        let second_txid = Txid::from_byte_array([3u8; 32]);
        let first_history = vec![(first_txid, 7)];
        let second_history = vec![(first_txid, 7), (second_txid, 8)];
        {
            let mut store = ElectrumHistoryStore::open(directory.path()).unwrap();
            store
                .apply_batch(&[(script_hash.clone(), first_history.clone())])
                .unwrap();
            assert_eq!(store.get(&script_hash).unwrap(), first_history);
            store
                .apply_batch(&[(script_hash.clone(), second_history.clone())])
                .unwrap();
            assert_eq!(store.get(&script_hash).unwrap(), second_history);
            assert_eq!(store.keys(), vec![script_hash.clone()]);
        }

        let data_path = directory.path().join("history.dat");
        let committed_len = std::fs::metadata(&data_path).unwrap().len();
        let uncommitted =
            encode_history_value(99, [1u8; 32], &[(Txid::from_byte_array([4u8; 32]), 9)]).unwrap();
        let mut file = OpenOptions::new().append(true).open(&data_path).unwrap();
        file.write_all(&(u32::try_from(uncommitted.len()).unwrap()).to_le_bytes())
            .unwrap();
        file.write_all(&uncommitted).unwrap();
        file.sync_data().unwrap();
        drop(file);

        let recovered = ElectrumHistoryStore::open(directory.path()).unwrap();
        assert_eq!(recovered.get(&script_hash).unwrap(), second_history);
        assert_eq!(std::fs::metadata(data_path).unwrap().len(), committed_len);
    }

    #[test]
    fn electrum_history_rebuilds_a_corrupt_index_and_replaces_all_values() {
        let directory = tempfile::tempdir().unwrap();
        let first_script = hex::encode([5u8; 32]);
        let second_script = hex::encode([6u8; 32]);
        let first_txid = Txid::from_byte_array([7u8; 32]);
        let second_txid = Txid::from_byte_array([8u8; 32]);
        let entries = vec![
            (first_script.clone(), vec![(first_txid, 10)]),
            (second_script.clone(), vec![(second_txid, 11)]),
        ];
        {
            let mut store = ElectrumHistoryStore::open(directory.path()).unwrap();
            store.replace_all(entries.clone()).unwrap();
        }
        std::fs::write(directory.path().join("history.index"), b"corrupt").unwrap();

        let mut reopened = ElectrumHistoryStore::open(directory.path()).unwrap();
        assert_eq!(reopened.entries().unwrap().len(), 2);
        assert_eq!(reopened.get(&first_script).unwrap(), entries[0].1);
        assert_eq!(reopened.get(&second_script).unwrap(), entries[1].1);
        reopened
            .replace_all([(first_script.clone(), vec![(second_txid, 12)])])
            .unwrap();
        assert_eq!(
            reopened.get(&first_script).unwrap(),
            vec![(second_txid, 12)]
        );
        assert!(reopened.get(&second_script).unwrap().is_empty());
        drop(reopened);

        let reopened = ElectrumHistoryStore::open(directory.path()).unwrap();
        assert_eq!(reopened.len(), 1);
        assert_eq!(
            reopened.get(&first_script).unwrap(),
            vec![(second_txid, 12)]
        );
    }

    #[test]
    fn persists_and_reopens_electrum_transactions() {
        let directory = tempfile::tempdir().unwrap();
        let block = genesis_block(Network::Regtest);
        let hash = block.block_hash();
        let txid = block.txdata[0].compute_txid();
        {
            let mut store = ElectrumBlockStore::open(directory.path()).unwrap();
            assert_eq!(store.insert(&block).unwrap(), hash);
            assert!(store.contains(&hash));
            assert_eq!(
                store.transaction(&hash, 0).unwrap().unwrap().compute_txid(),
                txid
            );
            assert_eq!(store.merkle_branch(&hash, 0).unwrap(), Some(Vec::new()));
            assert_eq!(store.transaction(&hash, 1).unwrap(), None);
        }

        std::fs::write(directory.path().join("txblocks.index"), b"corrupt").unwrap();
        let mut reopened = ElectrumBlockStore::open(directory.path()).unwrap();
        assert_eq!(
            reopened
                .transaction(&hash, 0)
                .unwrap()
                .unwrap()
                .compute_txid(),
            txid
        );
        assert_eq!(reopened.merkle_branch(&hash, 0).unwrap(), Some(Vec::new()));
    }

    #[test]
    fn decoded_block_cache_is_bounded_and_cleared_after_pruning() {
        let directory = tempfile::tempdir().unwrap();
        let block = genesis_block(Network::Regtest);
        let hash = block.block_hash();
        let mut store = BlockStore::open(directory.path()).unwrap();
        store.configure_cache_size_mib(4);
        store.insert(&block).unwrap();
        assert_eq!(store.block_cache.len(), 1);
        assert_eq!(store.get(&hash).unwrap(), Some(block));
        store
            .prune(&HashSet::from([hash]), &HashSet::new())
            .unwrap();
        assert!(store.block_cache.is_empty());
    }

    #[test]
    fn persists_and_recovers_xored_blocks_and_undo() {
        let directory = tempfile::tempdir().unwrap();
        let block = genesis_block(Network::Regtest);
        let hash = block.block_hash();
        let undo = vec![vec![TxOut {
            value: bitcoin::Amount::from_sat(42),
            script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
        }]];
        {
            let mut store = BlockStore::open_with_xor(directory.path(), true).unwrap();
            store.insert(&block).unwrap();
            store.insert_undo(hash, &undo).unwrap();
            assert_eq!(store.get(&hash).unwrap(), Some(block.clone()));
            assert_eq!(store.get_undo(&hash).unwrap(), Some(undo.clone()));
        }

        let key = read_xor_key(&directory.path().join("xor.dat")).unwrap();
        assert_eq!(
            std::fs::metadata(directory.path().join("xor.dat"))
                .unwrap()
                .len(),
            XOR_KEY_SIZE as u64
        );
        let mut raw = std::fs::read(directory.path().join("blocks.dat")).unwrap();
        key.apply(&mut raw, 0);
        let mut expected = (serialize(&block).len() as u32).to_le_bytes().to_vec();
        expected.extend_from_slice(&serialize(&block));
        assert_eq!(raw, expected);

        std::fs::write(directory.path().join("blocks.index"), b"corrupt").unwrap();
        std::fs::write(directory.path().join("undo.index"), b"corrupt").unwrap();
        let mut reopened = BlockStore::open_with_xor(directory.path(), true).unwrap();
        assert_eq!(reopened.get(&hash).unwrap(), Some(block));
        assert_eq!(reopened.get_undo(&hash).unwrap(), Some(undo));
    }

    #[test]
    fn cannot_disable_a_nonzero_xor_key() {
        let directory = tempfile::tempdir().unwrap();
        let _store = BlockStore::open_with_xor(directory.path(), true).unwrap();
        let key = read_xor_key(&directory.path().join("xor.dat")).unwrap();
        if key.0.iter().any(|byte| *byte != 0) {
            assert!(BlockStore::open_with_xor(directory.path(), false).is_err());
        }
    }

    #[test]
    fn recovers_from_an_overlapping_block_index() {
        let directory = tempfile::tempdir().unwrap();
        let first = genesis_block(Network::Regtest);
        let mut second = first.clone();
        second.header.nonce = 1;
        let first_hash = first.block_hash();
        let second_hash = second.block_hash();
        {
            let mut store = BlockStore::open(directory.path()).unwrap();
            store.insert(&first).unwrap();
            store.insert(&second).unwrap();
        }
        let index_path = directory.path().join("blocks.index");
        let mut index = std::fs::read(&index_path).unwrap();
        let second_offset = (INDEX_HEADER_SIZE + INDEX_RECORD_SIZE + 32) as usize;
        index[second_offset..second_offset + 8].copy_from_slice(&0u64.to_le_bytes());
        std::fs::write(index_path, index).unwrap();

        let mut reopened = BlockStore::open(directory.path()).unwrap();
        assert_eq!(reopened.get(&first_hash).unwrap(), Some(first));
        assert_eq!(reopened.get(&second_hash).unwrap(), Some(second));
    }

    #[test]
    fn recovers_truncated_final_records() {
        let directory = tempfile::tempdir().unwrap();
        let block = genesis_block(Network::Regtest);
        let hash = block.block_hash();
        {
            let mut store = BlockStore::open(directory.path()).unwrap();
            store.insert(&block).unwrap();
            store.insert_undo(hash, &[Vec::new()]).unwrap();
        }
        let block_len = std::fs::metadata(directory.path().join("blocks.dat"))
            .unwrap()
            .len();
        let undo_len = std::fs::metadata(directory.path().join("undo.dat"))
            .unwrap()
            .len();
        for path in ["blocks.dat", "undo.dat"] {
            let mut file = std::fs::OpenOptions::new()
                .append(true)
                .open(directory.path().join(path))
                .unwrap();
            std::io::Write::write_all(&mut file, &128u32.to_le_bytes()).unwrap();
            std::io::Write::write_all(&mut file, &[1, 2, 3]).unwrap();
            std::io::Write::flush(&mut file).unwrap();
        }
        let mut reopened = BlockStore::open(directory.path()).unwrap();
        assert_eq!(reopened.get(&hash).unwrap(), Some(block));
        assert_eq!(reopened.get_undo(&hash).unwrap(), Some(vec![Vec::new()]));
        assert_eq!(
            std::fs::metadata(directory.path().join("blocks.dat"))
                .unwrap()
                .len(),
            block_len
        );
        assert_eq!(
            std::fs::metadata(directory.path().join("undo.dat"))
                .unwrap()
                .len(),
            undo_len
        );

        let filter_directory = tempfile::tempdir().unwrap();
        let filter_hash = BlockHash::from_byte_array([8; 32]);
        let filter_header = FilterHeader::from_byte_array([9; 32]);
        {
            let mut store = FilterStore::open(filter_directory.path()).unwrap();
            store
                .insert(filter_hash, &[1, 2, 3], filter_header)
                .unwrap();
        }
        let filter_len = std::fs::metadata(filter_directory.path().join("basic-filters.dat"))
            .unwrap()
            .len();
        let mut file = std::fs::OpenOptions::new()
            .append(true)
            .open(filter_directory.path().join("basic-filters.dat"))
            .unwrap();
        std::io::Write::write_all(&mut file, &128u32.to_le_bytes()).unwrap();
        std::io::Write::write_all(&mut file, &[1, 2, 3]).unwrap();
        std::io::Write::flush(&mut file).unwrap();
        let mut reopened = FilterStore::open(filter_directory.path()).unwrap();
        assert_eq!(
            reopened.get(&filter_hash).unwrap(),
            Some((vec![1, 2, 3], filter_header))
        );
        assert_eq!(
            std::fs::metadata(filter_directory.path().join("basic-filters.dat"))
                .unwrap()
                .len(),
            filter_len
        );
    }

    #[test]
    fn batches_filter_records_and_reopens() {
        let directory = tempfile::tempdir().unwrap();
        let first_hash = BlockHash::from_byte_array([1; 32]);
        let second_hash = BlockHash::from_byte_array([2; 32]);
        let first_header = FilterHeader::from_byte_array([3; 32]);
        let second_header = FilterHeader::from_byte_array([4; 32]);
        let first_content = [5, 6, 7];
        let second_content = [8, 9];
        {
            let mut store = FilterStore::open(directory.path()).unwrap();
            store
                .insert_batch(&[
                    (first_hash, first_content.as_slice(), first_header),
                    (second_hash, second_content.as_slice(), second_header),
                ])
                .unwrap();
            assert_eq!(store.len(), 2);
            assert_eq!(
                store.get(&first_hash).unwrap(),
                Some((first_content.to_vec(), first_header))
            );
            assert_eq!(
                store.get(&second_hash).unwrap(),
                Some((second_content.to_vec(), second_header))
            );
        }
        let mut reopened = FilterStore::open(directory.path()).unwrap();
        assert_eq!(reopened.len(), 2);
        assert_eq!(
            reopened.get_header(&first_hash).unwrap(),
            Some(first_header)
        );
        assert_eq!(
            reopened.get(&second_hash).unwrap(),
            Some((second_content.to_vec(), second_header))
        );
    }

    #[test]
    fn persists_and_reopens_block_undo() {
        let directory = tempfile::tempdir().unwrap();
        let hash = BlockHash::from_byte_array([7; 32]);
        let undo = vec![
            Vec::new(),
            vec![TxOut {
                value: bitcoin::Amount::from_sat(42),
                script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
            }],
        ];
        {
            let mut store = BlockStore::open(directory.path()).unwrap();
            store.insert_undo(hash, &undo).unwrap();
            assert_eq!(store.get_undo(&hash).unwrap(), Some(undo.clone()));
        }
        let mut reopened = BlockStore::open(directory.path()).unwrap();
        assert_eq!(reopened.get_undo(&hash).unwrap(), Some(undo));
    }

    #[test]
    fn persists_and_reopens_basic_filter() {
        let directory = tempfile::tempdir().unwrap();
        let hash = BlockHash::from_byte_array([8; 32]);
        let header = FilterHeader::from_byte_array([9; 32]);
        {
            let mut store = FilterStore::open(directory.path()).unwrap();
            store.insert(hash, &[1, 2, 3], header).unwrap();
            assert_eq!(store.get(&hash).unwrap(), Some((vec![1, 2, 3], header)));
            assert_eq!(store.get_header(&hash).unwrap(), Some(header));
        }
        let mut reopened = FilterStore::open(directory.path()).unwrap();
        assert_eq!(reopened.get(&hash).unwrap(), Some((vec![1, 2, 3], header)));
        assert_eq!(reopened.get_header(&hash).unwrap(), Some(header));
    }

    #[test]
    fn persists_and_reopens_coinstats_records() {
        let directory = tempfile::tempdir().unwrap();
        let record = CoinStatsRecord {
            block_hash: BlockHash::from_byte_array([4; 32]),
            height: 12,
            transactions: 3,
            outputs: 5,
            total_amount_sat: 42,
            bogo_size: 99,
            muhash: "deadbeef".to_owned(),
            total_subsidy_sat: 50,
            total_prevout_spent_sat: 1,
            total_new_outputs_ex_coinbase_sat: 2,
            total_coinbase_sat: 3,
            total_unspendable_genesis_sat: 4,
            total_unspendable_bip30_sat: 5,
            total_unspendable_scripts_sat: 6,
            total_unspendable_unclaimed_rewards_sat: 7,
        };
        {
            let mut store = CoinStatsStore::open(directory.path()).unwrap();
            store.insert(&record).unwrap();
            assert_eq!(store.get(&record.block_hash).unwrap(), Some(record.clone()));
        }
        let mut reopened = CoinStatsStore::open(directory.path()).unwrap();
        assert_eq!(reopened.get(&record.block_hash).unwrap(), Some(record));
    }

    #[test]
    fn persists_and_recovers_chainstate_deltas() {
        let directory = tempfile::tempdir().unwrap();
        let hash = BlockHash::from_byte_array([6; 32]);
        let payload = vec![1, 2, 3, 4, 5];
        {
            let mut store = ChainstateStore::open(directory.path()).unwrap();
            store.insert(hash, &payload).unwrap();
            assert_eq!(store.get(&hash).unwrap(), Some(payload.clone()));
        }
        let data_path = directory.path().join("deltas.dat");
        let original_len = std::fs::metadata(&data_path).unwrap().len();
        let mut file = std::fs::OpenOptions::new()
            .append(true)
            .open(&data_path)
            .unwrap();
        std::io::Write::write_all(&mut file, &128u32.to_le_bytes()).unwrap();
        std::io::Write::write_all(&mut file, &[1, 2, 3]).unwrap();
        std::io::Write::flush(&mut file).unwrap();

        let mut reopened = ChainstateStore::open(directory.path()).unwrap();
        assert_eq!(reopened.get(&hash).unwrap(), Some(payload));
        assert_eq!(std::fs::metadata(data_path).unwrap().len(), original_len);
        reopened.clear().unwrap();
        assert!(!reopened.contains(&hash));
        assert_eq!(reopened.get(&hash).unwrap(), None);
    }

    #[test]
    fn chainstate_write_batch_flushes_at_the_configured_boundary() {
        let directory = tempfile::tempdir().unwrap();
        let hash = BlockHash::from_byte_array([7; 32]);
        let mut store = ChainstateStore::open(directory.path()).unwrap();
        store.configure_write_batch_size_bytes(1024 * 1024);
        store.insert(hash, &[1, 2, 3]).unwrap();
        assert!(store.pending_write_bytes > 0);
        store.flush_pending_writes().unwrap();
        assert_eq!(store.pending_write_bytes, 0);
        drop(store);
        let mut reopened = ChainstateStore::open(directory.path()).unwrap();
        assert_eq!(reopened.get(&hash).unwrap(), Some(vec![1, 2, 3]));
    }

    #[test]
    fn pruning_rewrites_block_and_undo_records() {
        let directory = tempfile::tempdir().unwrap();
        let first = genesis_block(Network::Regtest);
        let mut second = first.clone();
        second.header.nonce = 1;
        let first_hash = first.block_hash();
        let second_hash = second.block_hash();
        let retained = HashSet::from([second_hash]);
        let mut store = BlockStore::open_with_xor(directory.path(), true).unwrap();
        store.insert(&first).unwrap();
        store.insert(&second).unwrap();
        store.insert_undo(first_hash, &[Vec::new()]).unwrap();
        store.insert_undo(second_hash, &[Vec::new()]).unwrap();
        store.prune(&retained, &retained).unwrap();
        assert!(!store.contains(&first_hash));
        assert_eq!(store.get(&second_hash).unwrap(), Some(second));
        assert!(store.get_undo(&first_hash).unwrap().is_none());
        assert_eq!(
            store.get_undo(&second_hash).unwrap(),
            Some(vec![Vec::new()])
        );
    }
}
