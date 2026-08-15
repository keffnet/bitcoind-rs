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

use anyhow::{Context, Result, bail};
use bitcoin::bip158::FilterHeader;
use bitcoin::consensus::encode::{VarInt, deserialize, deserialize_partial, serialize};
use bitcoin::hashes::Hash;
use bitcoin::{Block, BlockHash, TxOut};
use rand::random;
use serde::{Deserialize, Serialize};

const MAX_STORED_BLOCK_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_UNDO_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_FILTER_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_CHAINSTATE_DELTA_SIZE: usize = 64 * 1024 * 1024;
const XOR_KEY_SIZE: usize = 8;
const INDEX_HEADER_SIZE: u64 = 8;
const INDEX_RECORD_SIZE: u64 = 44;

#[derive(Clone, Copy, Debug)]
struct Record {
    offset: u64,
    length: u32,
}

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
        })
    }

    pub fn path(&self) -> &Path {
        &self.path
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
        self.file.sync_data()?;
        let record = Record { offset, length };
        persist_index_entry(
            &mut self.index_file,
            offset + 4 + u64::from(length),
            hash,
            record,
        )?;
        self.index.insert(hash, record);
        Ok(())
    }

    /// Discard all records covered by a durable full snapshot.
    pub fn clear(&mut self) -> Result<()> {
        self.file.set_len(0)?;
        self.file.seek(SeekFrom::End(0))?;
        self.file.sync_data()?;
        self.index.clear();
        rewrite_index(&mut self.index_file, 0, &self.index)
    }
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
