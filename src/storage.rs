//! Append-only block storage.
//!
//! Blocks are written as length-prefixed consensus-encoded records. The
//! in-memory hash index makes reads O(1). A durable location index avoids
//! decoding the append-only file on normal restarts; truncated, stale, or
//! corrupt index files fall back to a complete record scan.

use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::{File, OpenOptions, create_dir_all, remove_file};
use std::io::{ErrorKind, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;

#[cfg(unix)]
use std::os::unix::fs::FileExt;
#[cfg(windows)]
use std::os::windows::fs::FileExt;

use anyhow::{Context, Result, bail};
use bitcoin::bip158::FilterHeader;
use bitcoin::consensus::encode::{VarInt, deserialize, deserialize_partial, serialize};
use bitcoin::hashes::{Hash, HashEngine};
use bitcoin::{Block, BlockHash, OutPoint, Transaction, TxOut, Txid};
use fjall::{
    CompressionType, Config as FjallConfig, Keyspace, PartitionCreateOptions, PartitionHandle,
    PersistMode,
};
use hashbrown::HashMap as FastHashMap;
use parking_lot::{Mutex, RwLock};
use rand::random;
use serde::{Deserialize, Serialize};

const MAX_STORED_BLOCK_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_UNDO_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_FILTER_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_CHAINSTATE_DELTA_SIZE: usize = 64 * 1024 * 1024;
const MAX_STORED_ELECTRUM_BLOCK_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_TRANSACTION_INDEX_SIZE: usize = 8 * 1024 * 1024;
const MAX_STORED_UTXO_SIZE: usize = 100 * 1024;
const XOR_KEY_SIZE: usize = 8;
const STORAGE_COMPRESSION_MAGIC: &[u8] = b"bitcoind-rs-zstd-v1\0";
const STORAGE_COMPRESSION_HEADER_SIZE: usize = STORAGE_COMPRESSION_MAGIC.len() + 4;
const STORAGE_COMPRESSION_LEVEL: i32 = 6;
const STORAGE_COMPRESSION_MIN_SIZE: usize = 256;
const INDEX_HEADER_SIZE: u64 = 8;
const INDEX_RECORD_SIZE: u64 = 44;

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

/// Complete coin metadata required to restore a spent output during a reorg.
/// Keeping this in undo data avoids consulting a historical transaction
/// index, matching the role of Core's undo coins while retaining the median
/// time field used by this implementation's sequence-lock validation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StoredUndo {
    pub output: TxOut,
    pub height: u32,
    pub median_time_past: u32,
    pub coinbase: bool,
}

pub type StoredElectrumHistory = Vec<(Txid, u32)>;

#[derive(Default)]
struct UtxoReadCache {
    entries: FastHashMap<OutPoint, (StoredUtxo, usize, u64)>,
    order: VecDeque<(OutPoint, u64)>,
    bytes: usize,
    limit: usize,
    next_generation: u64,
}

impl UtxoReadCache {
    fn configure_limit(&mut self, limit: usize) {
        self.limit = limit;
        self.trim();
    }

    fn get(&mut self, outpoint: &OutPoint) -> Option<StoredUtxo> {
        // Outputs are normally read once, immediately before being spent.
        // FIFO retention avoids an O(cache size) LRU-list update in that hot
        // path while still keeping recently created outputs resident.
        self.entries
            .get(outpoint)
            .map(|(entry, _, _)| entry.clone())
    }

    fn insert(&mut self, outpoint: OutPoint, entry: StoredUtxo) {
        let bytes = stored_utxo_cache_bytes(&entry);
        if self.limit == 0 || bytes > self.limit {
            return;
        }
        let generation = self.next_generation;
        self.next_generation = self.next_generation.saturating_add(1);
        if let Some((_, old_bytes, _)) = self.entries.insert(outpoint, (entry, bytes, generation)) {
            self.bytes = self.bytes.saturating_sub(old_bytes);
        }
        self.bytes = self.bytes.saturating_add(bytes);
        self.order.push_back((outpoint, generation));
        self.trim();
    }

    fn remove(&mut self, outpoint: &OutPoint) {
        if let Some((_, bytes, _)) = self.entries.remove(outpoint) {
            self.bytes = self.bytes.saturating_sub(bytes);
        }
        self.compact_order_if_needed();
    }

    fn clear(&mut self) {
        self.entries.clear();
        self.order.clear();
        self.bytes = 0;
    }

    fn trim(&mut self) {
        while self.bytes > self.limit {
            let Some((outpoint, generation)) = self.order.pop_front() else {
                self.bytes = 0;
                break;
            };
            let is_current = self
                .entries
                .get(&outpoint)
                .is_some_and(|(_, _, current)| *current == generation);
            if is_current && let Some((_, bytes, _)) = self.entries.remove(&outpoint) {
                self.bytes = self.bytes.saturating_sub(bytes);
            }
        }
        self.compact_order_if_needed();
    }

    fn compact_order_if_needed(&mut self) {
        let maximum_entries = self.entries.len().saturating_mul(2).saturating_add(1_024);
        if self.order.len() <= maximum_entries {
            return;
        }
        let entries = &self.entries;
        self.order.retain(|(outpoint, generation)| {
            entries
                .get(outpoint)
                .is_some_and(|(_, _, current)| current == generation)
        });
    }
}

fn stored_utxo_cache_bytes(entry: &StoredUtxo) -> usize {
    64usize.saturating_add(entry.output.script_pubkey.len())
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

/// Encode one authoritative append-only payload with the storage codec.
///
/// The outer record framing remains four-byte-length-prefixed so indexes can
/// still address records directly.  Compression is therefore applied before
/// XOR obfuscation and independently for each record, which preserves random
/// reads and makes a torn tail recoverable without a global decompression
/// stream. Small or incompressible values stay raw as part of the current
/// record format.
fn encode_storage_payload(payload: &[u8], max_size: usize) -> Result<Vec<u8>> {
    if payload.len() > max_size {
        bail!("storage payload is too large: {} bytes", payload.len());
    }
    if payload.len() < STORAGE_COMPRESSION_MIN_SIZE {
        return Ok(payload.to_vec());
    }
    let compressed = zstd::bulk::compress(payload, STORAGE_COMPRESSION_LEVEL)
        .context("compressing storage record with zstd")?;
    if compressed
        .len()
        .saturating_add(STORAGE_COMPRESSION_HEADER_SIZE)
        >= payload.len()
    {
        return Ok(payload.to_vec());
    }
    let uncompressed_length = u32::try_from(payload.len())
        .context("uncompressed storage payload length does not fit u32")?;
    let mut encoded = Vec::with_capacity(STORAGE_COMPRESSION_HEADER_SIZE + compressed.len());
    encoded.extend_from_slice(STORAGE_COMPRESSION_MAGIC);
    encoded.extend_from_slice(&uncompressed_length.to_le_bytes());
    encoded.extend_from_slice(&compressed);
    Ok(encoded)
}

fn decode_storage_payload(encoded: &[u8], max_size: usize) -> Result<Vec<u8>> {
    if !encoded.starts_with(STORAGE_COMPRESSION_MAGIC) {
        if encoded.len() > max_size {
            bail!("stored payload is too large: {} bytes", encoded.len());
        }
        return Ok(encoded.to_vec());
    }
    if encoded.len() < STORAGE_COMPRESSION_HEADER_SIZE {
        bail!("truncated zstd storage record header");
    }
    let length_start = STORAGE_COMPRESSION_MAGIC.len();
    let expected_length = u32::from_le_bytes(
        encoded[length_start..STORAGE_COMPRESSION_HEADER_SIZE]
            .try_into()
            .expect("zstd storage length has fixed width"),
    ) as usize;
    if expected_length > max_size {
        bail!(
            "decompressed storage payload is too large: {} bytes",
            expected_length
        );
    }
    let decoded =
        zstd::bulk::decompress(&encoded[STORAGE_COMPRESSION_HEADER_SIZE..], expected_length)
            .context("decompressing storage record with zstd")?;
    if decoded.len() != expected_length {
        bail!(
            "zstd storage record decoded to {} bytes, expected {}",
            decoded.len(),
            expected_length
        );
    }
    Ok(decoded)
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
        let entries = std::fs::read_dir(directory)?
            .map(|entry| entry.map(|entry| entry.file_name().to_string_lossy().into_owned()))
            .collect::<std::result::Result<Vec<_>, _>>()?;
        let first_run = entries.iter().all(|name| {
            name.starts_with('.')
                // Core creates the block-index directory before the block store
                // gets its obfuscation key. It is metadata, not existing block
                // data, and must not turn a first run into an all-zero key.
                || name == "index"
        });
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
        bail!("The blocksdir XOR-key can not be disabled when a random key was already stored!");
    }
    Ok(key)
}

#[derive(Clone)]
pub struct BlockStoreReader {
    file: Arc<RwLock<File>>,
    index: Arc<RwLock<HashMap<BlockHash, Record>>>,
    xor_key: XorKey,
}

impl BlockStoreReader {
    fn new(file: File, index: HashMap<BlockHash, Record>, xor_key: XorKey) -> Self {
        Self {
            file: Arc::new(RwLock::new(file)),
            index: Arc::new(RwLock::new(index)),
            xor_key,
        }
    }

    pub fn get(&self, hash: &BlockHash) -> Result<Option<Block>> {
        let Some(record) = self.index.read().get(hash).copied() else {
            return Ok(None);
        };
        let file = self.file.read();
        let bytes =
            read_storage_record(&file, record, self.xor_key, MAX_STORED_BLOCK_SIZE, "block")?;
        let block: Block = deserialize(&bytes).context("decoding stored block")?;
        if block.block_hash() != *hash {
            bail!("stored block hash does not match block index");
        }
        Ok(Some(block))
    }

    pub fn transaction_count(&self, hash: &BlockHash) -> Result<Option<usize>> {
        let Some(record) = self.index.read().get(hash).copied() else {
            return Ok(None);
        };
        read_block_transaction_count(&self.file.read(), record, self.xor_key).map(Some)
    }

    fn insert(&self, hash: BlockHash, record: Record) {
        self.index.write().insert(hash, record);
    }

    fn replace(&self, file: File, index: HashMap<BlockHash, Record>) {
        *self.file.write() = file;
        *self.index.write() = index;
    }
}

pub struct BlockStore {
    path: PathBuf,
    file: File,
    index_file: File,
    index: HashMap<BlockHash, Record>,
    serving_reader: BlockStoreReader,
    undo_file: File,
    undo_index_file: File,
    undo_index: HashMap<BlockHash, Record>,
    xor_key: XorKey,
    block_file_read_only: bool,
    allow_block_file_reopen: bool,
    block_cache: HashMap<BlockHash, (Block, usize)>,
    block_cache_order: VecDeque<BlockHash>,
    block_cache_bytes: usize,
    block_cache_limit: usize,
}

pub(crate) struct PreparedBlockRecord {
    hash: BlockHash,
    encoded: Vec<u8>,
    raw_length: usize,
}

impl BlockStore {
    pub fn open(directory: impl AsRef<Path>) -> Result<Self> {
        Self::open_with_xor(directory, false)
    }

    /// Open the block and undo stores with optional cyclic XOR obfuscation.
    /// The key is persisted in `xor.dat`; a fresh directory gets a random key
    /// when enabled, while an existing clear directory gets a zero key so
    /// upgrading does not rewrite historical data.
    pub fn open_with_xor(directory: impl AsRef<Path>, use_xor: bool) -> Result<Self> {
        Self::open_with_xor_mode(directory, use_xor, false, false)
    }

    /// Open an existing store for a chainstate reindex without requiring
    /// append permission on the block data. Reindex rebuilds metadata from
    /// durable block records; a later block write can reopen the descriptor.
    pub(crate) fn open_for_reindex_with_xor(
        directory: impl AsRef<Path>,
        use_xor: bool,
    ) -> Result<Self> {
        Self::open_with_xor_mode(directory, use_xor, true, true)
    }

    fn open_with_xor_mode(
        directory: impl AsRef<Path>,
        use_xor: bool,
        prefer_read_only_blocks: bool,
        allow_block_file_reopen: bool,
    ) -> Result<Self> {
        let directory = directory.as_ref();
        create_dir_all(directory)
            .with_context(|| format!("creating block directory {}", directory.display()))?;
        let xor_key = init_xor_key(directory, use_xor)?;
        let path = directory.join("blocks.dat");
        let block_file_read_only = prefer_read_only_blocks && path.is_file();
        let mut file = if block_file_read_only {
            OpenOptions::new().read(true).open(&path)
        } else {
            OpenOptions::new()
                .create(true)
                .read(true)
                .append(true)
                .open(&path)
        }
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
                let index = scan_index(&mut file, xor_key, !block_file_read_only)
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
        let serving_reader = BlockStoreReader::new(file.try_clone()?, index.clone(), xor_key);
        Ok(Self {
            path,
            file,
            index_file,
            index,
            serving_reader,
            undo_file,
            undo_index_file,
            undo_index,
            xor_key,
            block_file_read_only,
            allow_block_file_reopen,
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
            None => scan_index(&mut file, xor_key, false)
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

        let serving_reader = BlockStoreReader::new(file.try_clone()?, index.clone(), xor_key);
        Ok(Self {
            path,
            file,
            index_file,
            index,
            serving_reader,
            undo_file,
            undo_index_file,
            undo_index,
            xor_key,
            block_file_read_only: true,
            allow_block_file_reopen: false,
            block_cache: HashMap::new(),
            block_cache_order: VecDeque::new(),
            block_cache_bytes: 0,
            block_cache_limit: 0,
        })
    }

    /// Configure the in-memory block-record cache used by the custom storage
    /// backend. Keep one quarter of `-dbcache` for decoded historical blocks;
    /// the UTXO value cache receives the other three quarters because random
    /// prevout reads dominate IBD and newly accepted blocks are rarely read
    /// again before they leave this cache.
    pub fn configure_cache_size_mib(&mut self, mib: i64) {
        const MIN_CACHE_MIB: u64 = 4;
        const MIB: u64 = 1024 * 1024;
        let mib = u64::try_from(mib.max(0)).unwrap_or(u64::MAX);
        let bytes = mib.max(MIN_CACHE_MIB).saturating_mul(MIB);
        let bytes = usize::try_from(bytes).unwrap_or(usize::MAX);
        self.block_cache_limit = bytes / 4;
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

    pub fn reader(&self) -> BlockStoreReader {
        self.serving_reader.clone()
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
        self.insert_with_sync(block, true)
    }

    /// Append a block without forcing a filesystem sync for every record.
    /// Headers-first downloads can deliver thousands of tiny side-chain
    /// blocks; the owning chainstate flushes the append-only stores at the
    /// end of the reorg (and on shutdown), while keeping the hot path batched.
    pub fn insert_unsynced(&mut self, block: &Block) -> Result<BlockHash> {
        self.insert_with_sync(block, false)
    }

    fn ensure_block_file_writable(&mut self) -> Result<()> {
        if !self.block_file_read_only {
            return Ok(());
        }
        if !self.allow_block_file_reopen {
            bail!("block store is read-only")
        }
        self.file = OpenOptions::new()
            .read(true)
            .append(true)
            .open(&self.path)
            .with_context(|| {
                format!("reopening block store {} for writing", self.path.display())
            })?;
        self.serving_reader
            .replace(self.file.try_clone()?, self.index.clone());
        self.block_file_read_only = false;
        Ok(())
    }

    fn insert_with_sync(&mut self, block: &Block, sync: bool) -> Result<BlockHash> {
        let hash = block.block_hash();
        if self.index.contains_key(&hash) {
            return Ok(hash);
        }
        let prepared = Self::prepare_record(block)?;
        self.insert_prepared_with_sync(block, prepared, sync)
    }

    pub(crate) fn prepare_record(block: &Block) -> Result<PreparedBlockRecord> {
        let hash = block.block_hash();
        let raw_bytes = serialize(block);
        let encoded = encode_storage_payload(&raw_bytes, MAX_STORED_BLOCK_SIZE)?;
        Ok(PreparedBlockRecord {
            hash,
            encoded,
            raw_length: raw_bytes.len(),
        })
    }

    pub(crate) fn insert_prepared(
        &mut self,
        block: &Block,
        prepared: PreparedBlockRecord,
    ) -> Result<BlockHash> {
        self.insert_prepared_with_sync(block, prepared, true)
    }

    pub(crate) fn insert_prepared_unsynced(
        &mut self,
        block: &Block,
        prepared: PreparedBlockRecord,
    ) -> Result<BlockHash> {
        self.insert_prepared_with_sync(block, prepared, false)
    }

    fn insert_prepared_with_sync(
        &mut self,
        block: &Block,
        prepared: PreparedBlockRecord,
        sync: bool,
    ) -> Result<BlockHash> {
        let hash = block.block_hash();
        if self.index.contains_key(&hash) {
            return Ok(hash);
        }
        if prepared.hash != hash {
            bail!("prepared block record does not match block")
        }
        self.ensure_block_file_writable()?;
        let bytes = prepared.encoded;
        let offset = self.file.seek(SeekFrom::End(0))?;
        let length = u32::try_from(bytes.len()).context("block length does not fit u32")?;
        let mut record = Vec::with_capacity(4 + bytes.len());
        record.extend_from_slice(&length.to_le_bytes());
        record.extend_from_slice(&bytes);
        self.xor_key.apply(&mut record, offset);
        self.file.write_all(&record)?;
        if sync {
            self.file.sync_data()?;
        }
        persist_index_entry_with_sync(
            &mut self.index_file,
            offset + 4 + bytes.len() as u64,
            hash,
            Record { offset, length },
            sync,
        )?;
        self.index.insert(hash, Record { offset, length });
        self.serving_reader.insert(hash, Record { offset, length });
        self.cache_block(hash, block.clone(), prepared.raw_length);
        Ok(hash)
    }

    pub fn flush(&mut self) -> Result<()> {
        self.file.sync_data()?;
        publish_index_data_len(&mut self.index_file, data_len_after(&self.file)?)?;
        self.undo_file.sync_data()?;
        publish_index_data_len(&mut self.undo_index_file, data_len_after(&self.undo_file)?)?;
        Ok(())
    }

    pub fn get(&mut self, hash: &BlockHash) -> Result<Option<Block>> {
        if let Some(block) = self.block_cache.get(hash).map(|(block, _)| block.clone()) {
            self.touch_block_cache(*hash);
            return Ok(Some(block));
        }
        let Some(record) = self.index.get(hash).copied() else {
            return Ok(None);
        };
        let bytes = read_storage_record(
            &self.file,
            record,
            self.xor_key,
            MAX_STORED_BLOCK_SIZE,
            "block",
        )?;
        let block: Block = deserialize(&bytes).context("decoding stored block")?;
        if block.block_hash() != *hash {
            bail!("stored block hash does not match block index");
        }
        self.cache_block(*hash, block.clone(), bytes.len());
        Ok(Some(block))
    }

    pub fn transaction_count(&mut self, hash: &BlockHash) -> Result<Option<usize>> {
        let Some(record) = self.index.get(hash).copied() else {
            return Ok(None);
        };
        read_block_transaction_count(&self.file, record, self.xor_key).map(Some)
    }

    /// Read a block without touching the mutable LRU cache or the seek
    /// cursor owned by the normal chain-state path. Peer uploads can use this
    /// method while holding only a shared ChainState lock, so serving an old
    /// branch cannot delay validation of a competing active candidate.
    pub fn get_readonly(&self, hash: &BlockHash) -> Result<Option<Block>> {
        self.serving_reader.get(hash)
    }

    pub fn get_undo(&mut self, hash: &BlockHash) -> Result<Option<Vec<Vec<StoredUndo>>>> {
        let Some(record) = self.undo_index.get(hash).copied() else {
            return Ok(None);
        };
        let bytes = read_storage_record(
            &self.undo_file,
            record,
            self.xor_key,
            MAX_STORED_UNDO_SIZE,
            "undo",
        )?;
        let (stored_hash, undo) = decode_undo_record(&bytes)?;
        if stored_hash != *hash {
            bail!("stored block undo hash does not match undo index");
        }
        Ok(Some(undo))
    }

    pub fn insert_undo(&mut self, hash: BlockHash, undo: &[Vec<StoredUndo>]) -> Result<()> {
        self.insert_undo_with_sync(hash, undo, true)
    }

    /// Append undo data without forcing a filesystem sync for every record.
    /// Chain activation writes a complete candidate suffix as one batch and
    /// flushes the store after the new active state is durable.
    pub fn insert_undo_unsynced(
        &mut self,
        hash: BlockHash,
        undo: &[Vec<StoredUndo>],
    ) -> Result<()> {
        self.insert_undo_with_sync(hash, undo, false)
    }

    fn insert_undo_with_sync(
        &mut self,
        hash: BlockHash,
        undo: &[Vec<StoredUndo>],
        sync: bool,
    ) -> Result<()> {
        if self.undo_index.contains_key(&hash) {
            return Ok(());
        }
        let raw_bytes = encode_undo_record(hash, undo)?;
        let bytes = encode_storage_payload(&raw_bytes, MAX_STORED_UNDO_SIZE)?;
        let offset = self.undo_file.seek(SeekFrom::End(0))?;
        let length = u32::try_from(bytes.len()).context("undo length does not fit u32")?;
        let mut record = Vec::with_capacity(4 + bytes.len());
        record.extend_from_slice(&length.to_le_bytes());
        record.extend_from_slice(&bytes);
        self.xor_key.apply(&mut record, offset);
        self.undo_file.write_all(&record)?;
        if sync {
            self.undo_file.sync_data()?;
        }
        persist_index_entry_with_sync(
            &mut self.undo_index_file,
            offset + 4 + bytes.len() as u64,
            hash,
            Record { offset, length },
            sync,
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
        self.ensure_block_file_writable()?;
        let block_hashes = self
            .index
            .keys()
            .copied()
            .filter(|hash| retained_blocks.contains(hash))
            .collect::<Vec<_>>();
        let block_path = self.path.clone();
        let xor_key = self.xor_key;
        let (file, index, data_len) = rewrite_record_file(
            &block_path,
            block_hashes.into_iter().map(|hash| {
                let block = self
                    .get(&hash)?
                    .with_context(|| format!("block {hash} disappeared during pruning"))?;
                Ok((hash, serialize(&block)))
            }),
            xor_key,
            MAX_STORED_BLOCK_SIZE,
        )?;
        self.file = file;
        self.index = index;
        rewrite_index(&mut self.index_file, data_len, &self.index)?;
        self.serving_reader
            .replace(self.file.try_clone()?, self.index.clone());

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
        let (undo_file, undo_index, undo_data_len) = rewrite_record_file(
            &undo_path,
            undo_hashes.into_iter().map(|hash| {
                let undo = self
                    .get_undo(&hash)?
                    .with_context(|| format!("undo for block {hash} disappeared during pruning"))?;
                Ok((hash, encode_undo_record(hash, &undo)?))
            }),
            xor_key,
            MAX_STORED_UNDO_SIZE,
        )?;
        self.undo_file = undo_file;
        self.undo_index = undo_index;
        rewrite_index(&mut self.undo_index_file, undo_data_len, &self.undo_index)?;
        self.clear_block_cache();
        Ok(())
    }
}

fn read_storage_record(
    file: &File,
    record: Record,
    xor_key: XorKey,
    max_size: usize,
    kind: &str,
) -> Result<Vec<u8>> {
    let stored_length =
        usize::try_from(record.length).context("record length does not fit usize")?;
    if stored_length == 0 || stored_length > max_size {
        bail!("stored {kind} record is too large: {stored_length} bytes");
    }
    let mut length = [0u8; 4];
    read_block_exact_at(file, &mut length, record.offset)?;
    xor_key.apply(&mut length, record.offset);
    let actual = u32::from_le_bytes(length);
    if actual != record.length {
        bail!("{kind} store index disagrees with record length");
    }
    let mut encoded = vec![0u8; stored_length];
    read_block_exact_at(file, &mut encoded, record.offset + 4)?;
    xor_key.apply(&mut encoded, record.offset + 4);
    decode_storage_payload(&encoded, max_size)
        .with_context(|| format!("decoding stored {kind} record"))
}

fn read_block_transaction_count(file: &File, record: Record, xor_key: XorKey) -> Result<usize> {
    let bytes = read_storage_record(file, record, xor_key, MAX_STORED_BLOCK_SIZE, "block")?;
    let (_, header_bytes) = deserialize_partial::<bitcoin::block::Header>(&bytes)
        .context("decoding stored block header")?;
    let (count, _) = deserialize_partial::<VarInt>(&bytes[header_bytes..])
        .context("decoding stored block transaction count")?;
    usize::try_from(count.0).context("stored block transaction count is too large")
}

fn read_block_exact_at(file: &File, mut bytes: &mut [u8], mut offset: u64) -> std::io::Result<()> {
    while !bytes.is_empty() {
        let read = file.read_at(bytes, offset)?;
        if read == 0 {
            return Err(std::io::Error::new(
                ErrorKind::UnexpectedEof,
                "short positional read",
            ));
        }
        bytes = &mut bytes[read..];
        offset = offset.saturating_add(read as u64);
    }
    Ok(())
}

impl Drop for BlockStore {
    fn drop(&mut self) {
        let _ = self.flush();
    }
}

fn rewrite_record_file(
    path: &Path,
    records: impl IntoIterator<Item = Result<(BlockHash, Vec<u8>)>>,
    xor_key: XorKey,
    max_size: usize,
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
    let records = records.into_iter();
    let (lower_bound, _) = records.size_hint();
    let mut index = HashMap::with_capacity(lower_bound);
    for record in records {
        let (hash, raw_bytes) = record?;
        let bytes = encode_storage_payload(&raw_bytes, max_size)?;
        let offset = temp.seek(SeekFrom::End(0))?;
        let length = u32::try_from(bytes.len()).context("record length does not fit u32")?;
        let mut record = Vec::with_capacity(4 + bytes.len());
        record.extend_from_slice(&length.to_le_bytes());
        record.extend_from_slice(&bytes);
        xor_key.apply(&mut record, offset);
        temp.write_all(&record)?;
        index.insert(hash, Record { offset, length });
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
        let bytes = read_storage_record(
            &self.file,
            record,
            XorKey::default(),
            MAX_STORED_FILTER_SIZE + 64,
            "filter",
        )?;
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
        Ok(self.get(hash)?.map(|(_, header)| header))
    }

    pub fn insert(&mut self, hash: BlockHash, content: &[u8], header: FilterHeader) -> Result<()> {
        self.insert_batch(&[(hash, content, header)])
    }

    /// Append multiple immutable filters with one data sync and one index
    /// sync.  A crash after the data file is durable but before the index is
    /// durable is recoverable because `open` falls back to scanning the
    /// append-only records when the index length is stale.
    pub fn insert_batch(&mut self, entries: &[(BlockHash, &[u8], FilterHeader)]) -> Result<()> {
        self.insert_batch_with_sync(entries, true)
    }

    /// Append immutable filters without forcing a filesystem sync for every
    /// block. The owning chainstate flushes the append-only stores at its
    /// bounded peer-write durability boundary.
    pub fn insert_batch_unsynced(
        &mut self,
        entries: &[(BlockHash, &[u8], FilterHeader)],
    ) -> Result<()> {
        self.insert_batch_with_sync(entries, false)
    }

    fn insert_batch_with_sync(
        &mut self,
        entries: &[(BlockHash, &[u8], FilterHeader)],
        sync: bool,
    ) -> Result<()> {
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
            let mut raw_bytes = Vec::with_capacity(64 + content.len());
            raw_bytes.extend_from_slice(&hash.to_byte_array());
            raw_bytes.extend_from_slice(&header.to_byte_array());
            raw_bytes.extend_from_slice(content);
            let bytes = encode_storage_payload(&raw_bytes, MAX_STORED_FILTER_SIZE + 64)?;
            let length = u32::try_from(bytes.len()).context("filter length does not fit u32")?;
            let record_end = data_len
                .checked_add(4)
                .and_then(|offset| offset.checked_add(u64::from(length)))
                .context("filter store size overflow")?;
            pending.push((*hash, bytes, data_len, length));
            data_len = record_end;
        }

        if pending.is_empty() {
            return Ok(());
        }

        let data_bytes_capacity = pending.iter().fold(0usize, |total, (_, bytes, _, _)| {
            total.saturating_add(4).saturating_add(bytes.len())
        });
        let mut data_bytes = Vec::with_capacity(data_bytes_capacity);
        let mut records = Vec::with_capacity(pending.len());
        for (hash, bytes, offset, length) in pending {
            debug_assert_eq!(
                bytes.len(),
                usize::try_from(length).expect("u32 fits usize")
            );
            data_bytes.extend_from_slice(&length.to_le_bytes());
            data_bytes.extend_from_slice(&bytes);
            records.push((hash, Record { offset, length }));
        }
        self.file.write_all(&data_bytes)?;
        if sync {
            self.file.sync_data()?;
        }

        if sync {
            self.index_file.seek(SeekFrom::Start(0))?;
            self.index_file.write_all(&data_len.to_le_bytes())?;
        }
        self.index_file.seek(SeekFrom::End(0))?;
        let mut index_bytes =
            Vec::with_capacity(records.len().saturating_mul(INDEX_RECORD_SIZE as usize));
        for (hash, record) in &records {
            index_bytes.extend_from_slice(&hash.to_byte_array());
            index_bytes.extend_from_slice(&record.offset.to_le_bytes());
            index_bytes.extend_from_slice(&record.length.to_le_bytes());
        }
        self.index_file.write_all(&index_bytes)?;
        if sync {
            self.index_file.sync_data()?;
        }
        for (hash, record) in records {
            self.index.insert(hash, record);
        }
        Ok(())
    }

    pub fn flush(&mut self) -> Result<()> {
        self.file.sync_data()?;
        publish_index_data_len(&mut self.index_file, data_len_after(&self.file)?)?;
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

const TXINDEX_BLOCKS_PARTITION_NAME: &str = "blocks";
const TXINDEX_ALL_BLOCKS_PARTITION_NAME: &str = "all-indexed-blocks";
const TXINDEX_ALL_PARTITION_NAME: &str = "all-transactions";
const TXINDEX_ACTIVE_PARTITION_NAME: &str = "active-transactions";
const TXINDEX_META_PARTITION_NAME: &str = "metadata";
const META_BLOCK_COUNT: &[u8] = b"block-count";
const META_ACTIVE_TIP: &[u8] = b"active-tip";

/// A transaction's durable location. The block body remains authoritative
/// for transaction bytes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StoredTxLocation {
    pub block_hash: BlockHash,
    pub height: u32,
    pub transaction_index: u32,
}

/// Optional, fully disk-backed transaction index.
///
/// The `all_transactions` partition implements Core-style `-txindex`.
/// `active_transactions` provides best-chain lookups for wallet-free RPC,
/// REST, and Electrum methods. Neither partition is loaded into a
/// process-wide hash map.
pub struct TransactionIndexStore {
    path: PathBuf,
    keyspace: Keyspace,
    blocks: PartitionHandle,
    all_indexed_blocks: PartitionHandle,
    all_transactions: PartitionHandle,
    active_transactions: PartitionHandle,
    metadata: PartitionHandle,
    block_count: usize,
}

impl TransactionIndexStore {
    pub fn open(directory: impl AsRef<Path>) -> Result<Self> {
        Self::open_with_cache(directory, DISK_INDEX_DEFAULT_CACHE_BYTES)
    }

    pub fn open_with_cache(directory: impl AsRef<Path>, cache_bytes: u64) -> Result<Self> {
        let directory = directory.as_ref();
        create_dir_all(directory).with_context(|| {
            format!(
                "creating transaction index directory {}",
                directory.display()
            )
        })?;
        let path = directory.join("database");
        let keyspace = FjallConfig::new(&path)
            .cache_size(cache_bytes.max(1024 * 1024))
            .max_write_buffer_size(DISK_INDEX_DEFAULT_WRITE_BUFFER_BYTES)
            .manual_journal_persist(true)
            .open()
            .with_context(|| format!("opening transaction database {}", path.display()))?;
        let uncompressed = || PartitionCreateOptions::default().compression(CompressionType::None);
        let blocks = keyspace.open_partition(TXINDEX_BLOCKS_PARTITION_NAME, uncompressed())?;
        let all_indexed_blocks =
            keyspace.open_partition(TXINDEX_ALL_BLOCKS_PARTITION_NAME, uncompressed())?;
        let all_transactions =
            keyspace.open_partition(TXINDEX_ALL_PARTITION_NAME, uncompressed())?;
        let active_transactions =
            keyspace.open_partition(TXINDEX_ACTIVE_PARTITION_NAME, uncompressed())?;
        let metadata = keyspace.open_partition(TXINDEX_META_PARTITION_NAME, uncompressed())?;
        let block_count = read_usize_metadata(&metadata, META_BLOCK_COUNT)?.unwrap_or(0);
        if block_count == 0 && !blocks.is_empty()? {
            bail!("transaction database is missing its exact block-count metadata");
        }
        if read_u64_metadata(&metadata, META_BLOCK_COUNT)?.is_none() {
            metadata.insert(META_BLOCK_COUNT, 0u64.to_le_bytes().to_vec())?;
            keyspace.persist(PersistMode::SyncAll)?;
        }
        Ok(Self {
            path,
            keyspace,
            blocks,
            all_indexed_blocks,
            all_transactions,
            active_transactions,
            metadata,
            block_count,
        })
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn len(&self) -> usize {
        self.block_count
    }

    pub fn is_empty(&self) -> bool {
        self.block_count == 0
    }

    pub fn contains(&self, hash: &BlockHash) -> Result<bool> {
        self.blocks
            .contains_key(hash.to_byte_array())
            .context("looking up transaction-index block")
    }

    pub fn hashes(&self) -> Result<Vec<BlockHash>> {
        self.blocks
            .keys()
            .map(|key| {
                let key = key.context("scanning transaction-index block keys")?;
                let bytes: [u8; 32] = key
                    .as_ref()
                    .try_into()
                    .context("transaction-index block key has invalid length")?;
                Ok(BlockHash::from_byte_array(bytes))
            })
            .collect()
    }

    pub fn disk_usage(&self) -> Result<u64> {
        Ok(self
            .blocks
            .disk_space()
            .saturating_add(self.all_indexed_blocks.disk_space())
            .saturating_add(self.all_transactions.disk_space())
            .saturating_add(self.active_transactions.disk_space())
            .saturating_add(self.metadata.disk_space()))
    }

    pub fn get(&self, hash: &BlockHash) -> Result<Option<Vec<Txid>>> {
        self.blocks
            .get(hash.to_byte_array())?
            .map(|bytes| decode_txid_list(&bytes))
            .transpose()
    }

    pub fn all_indexed_hashes(&self) -> Result<Vec<BlockHash>> {
        self.all_indexed_blocks
            .keys()
            .map(|key| {
                let key = key.context("scanning all-transaction-index block keys")?;
                let bytes: [u8; 32] = key
                    .as_ref()
                    .try_into()
                    .context("all-transaction-index block key has invalid length")?;
                Ok(BlockHash::from_byte_array(bytes))
            })
            .collect()
    }

    pub fn transaction(&self, txid: &Txid) -> Result<Option<StoredTxLocation>> {
        self.all_transactions
            .get(txid.to_byte_array())?
            .map(|bytes| decode_stored_tx_location(&bytes))
            .transpose()
    }

    pub fn active_locations(&self, txid: &Txid) -> Result<Vec<StoredTxLocation>> {
        self.active_transactions
            .prefix(txid.to_byte_array())
            .map(|item| {
                let (_, value) = item.context("scanning active transaction locations")?;
                decode_stored_tx_location(&value)
            })
            .collect()
    }

    pub fn active_tip(&self) -> Result<Option<(BlockHash, u32)>> {
        let Some(bytes) = self.metadata.get(META_ACTIVE_TIP)? else {
            return Ok(None);
        };
        if bytes.len() != 36 {
            bail!("transaction database has an invalid active-tip marker");
        }
        Ok(Some((
            BlockHash::from_byte_array(
                bytes[..32]
                    .try_into()
                    .expect("active tip hash has fixed width"),
            ),
            u32::from_le_bytes(
                bytes[32..]
                    .try_into()
                    .expect("active tip height has fixed width"),
            ),
        )))
    }

    pub fn insert(&mut self, hash: BlockHash, txids: &[Txid]) -> Result<()> {
        self.insert_with_sync(hash, txids, true)
    }

    pub fn insert_unsynced(&mut self, hash: BlockHash, txids: &[Txid]) -> Result<()> {
        self.insert_with_sync(hash, txids, false)
    }

    fn insert_with_sync(&mut self, hash: BlockHash, txids: &[Txid], sync: bool) -> Result<()> {
        if self.contains(&hash)? {
            return Ok(());
        }
        let next_count = self.block_count.saturating_add(1);
        let mut batch = self
            .keyspace
            .batch()
            .durability(sync.then_some(PersistMode::SyncData));
        batch.insert(
            &self.blocks,
            hash.to_byte_array().to_vec(),
            encode_txid_list(txids)?,
        );
        batch.insert(
            &self.metadata,
            META_BLOCK_COUNT.to_vec(),
            u64::try_from(next_count)
                .context("transaction-index block count does not fit u64")?
                .to_le_bytes()
                .to_vec(),
        );
        batch.commit()?;
        self.block_count = next_count;
        Ok(())
    }

    pub fn index_all_block(
        &mut self,
        hash: BlockHash,
        height: u32,
        txids: &[Txid],
        sync: bool,
    ) -> Result<()> {
        let block_exists = self.contains(&hash)?;
        let mut batch = self
            .keyspace
            .batch()
            .durability(sync.then_some(PersistMode::SyncData));
        if !block_exists {
            batch.insert(
                &self.blocks,
                hash.to_byte_array().to_vec(),
                encode_txid_list(txids)?,
            );
        }
        for (transaction_index, txid) in txids.iter().enumerate() {
            let candidate = StoredTxLocation {
                block_hash: hash,
                height,
                transaction_index: u32::try_from(transaction_index)
                    .context("transaction index does not fit u32")?,
            };
            let replace = self.transaction(txid)?.is_none_or(|current| {
                (
                    candidate.height,
                    candidate.block_hash.to_byte_array(),
                    candidate.transaction_index,
                ) >= (
                    current.height,
                    current.block_hash.to_byte_array(),
                    current.transaction_index,
                )
            });
            if replace {
                batch.insert(
                    &self.all_transactions,
                    txid.to_byte_array().to_vec(),
                    encode_stored_tx_location(candidate),
                );
            }
        }
        batch.insert(
            &self.all_indexed_blocks,
            hash.to_byte_array().to_vec(),
            vec![1],
        );
        let next_count = self.block_count.saturating_add(usize::from(!block_exists));
        if !block_exists {
            batch.insert(
                &self.metadata,
                META_BLOCK_COUNT.to_vec(),
                u64::try_from(next_count)
                    .context("transaction-index block count does not fit u64")?
                    .to_le_bytes()
                    .to_vec(),
            );
        }
        batch.commit()?;
        self.block_count = next_count;
        Ok(())
    }

    pub fn connect_active_block(
        &mut self,
        hash: BlockHash,
        height: u32,
        txids: &[Txid],
        sync: bool,
    ) -> Result<()> {
        let block_exists = self.contains(&hash)?;
        let next_count = self.block_count.saturating_add(usize::from(!block_exists));
        let mut batch = self
            .keyspace
            .batch()
            .durability(sync.then_some(PersistMode::SyncData));
        if !block_exists {
            batch.insert(
                &self.blocks,
                hash.to_byte_array().to_vec(),
                encode_txid_list(txids)?,
            );
            batch.insert(
                &self.metadata,
                META_BLOCK_COUNT.to_vec(),
                u64::try_from(next_count)
                    .context("transaction-index block count does not fit u64")?
                    .to_le_bytes()
                    .to_vec(),
            );
        }
        for (transaction_index, txid) in txids.iter().enumerate() {
            let location = StoredTxLocation {
                block_hash: hash,
                height,
                transaction_index: u32::try_from(transaction_index)
                    .context("transaction index does not fit u32")?,
            };
            batch.insert(
                &self.active_transactions,
                active_transaction_key(*txid, height, location.transaction_index).to_vec(),
                encode_stored_tx_location(location),
            );
        }
        let mut active_tip = Vec::with_capacity(36);
        active_tip.extend_from_slice(&hash.to_byte_array());
        active_tip.extend_from_slice(&height.to_le_bytes());
        batch.insert(&self.metadata, META_ACTIVE_TIP.to_vec(), active_tip);
        batch.commit()?;
        self.block_count = next_count;
        Ok(())
    }

    pub fn disconnect_active_block(
        &mut self,
        hash: BlockHash,
        txids: &[Txid],
        sync: bool,
    ) -> Result<()> {
        let mut batch = self
            .keyspace
            .batch()
            .durability(sync.then_some(PersistMode::SyncData));
        for txid in txids {
            for location in self.active_locations(txid)? {
                if location.block_hash == hash {
                    batch.remove(
                        &self.active_transactions,
                        active_transaction_key(*txid, location.height, location.transaction_index)
                            .to_vec(),
                    );
                }
            }
        }
        batch.commit()?;
        Ok(())
    }

    pub fn set_active_tip(&mut self, hash: BlockHash, height: u32, sync: bool) -> Result<()> {
        let mut marker = Vec::with_capacity(36);
        marker.extend_from_slice(&hash.to_byte_array());
        marker.extend_from_slice(&height.to_le_bytes());
        self.metadata.insert(META_ACTIVE_TIP, marker)?;
        if sync {
            self.keyspace.persist(PersistMode::SyncData)?;
        }
        Ok(())
    }

    pub fn clear_active(&mut self) -> Result<()> {
        clear_partition(&self.keyspace, &self.active_transactions)?;
        self.metadata.remove(META_ACTIVE_TIP)?;
        Ok(())
    }

    pub fn clear_all_index(&mut self) -> Result<()> {
        clear_partition(&self.keyspace, &self.all_indexed_blocks)?;
        clear_partition(&self.keyspace, &self.all_transactions)?;
        Ok(())
    }

    pub fn clear(&mut self) -> Result<()> {
        clear_partition(&self.keyspace, &self.blocks)?;
        clear_partition(&self.keyspace, &self.all_indexed_blocks)?;
        clear_partition(&self.keyspace, &self.all_transactions)?;
        clear_partition(&self.keyspace, &self.active_transactions)?;
        self.metadata.remove(META_ACTIVE_TIP)?;
        self.block_count = 0;
        self.metadata
            .insert(META_BLOCK_COUNT, 0u64.to_le_bytes().to_vec())?;
        self.flush()
    }

    pub fn flush(&mut self) -> Result<()> {
        self.keyspace.persist(PersistMode::SyncData)?;
        Ok(())
    }
}

impl Drop for TransactionIndexStore {
    fn drop(&mut self) {
        let _ = self.flush();
    }
}

fn encode_txid_list(txids: &[Txid]) -> Result<Vec<u8>> {
    let mut raw = Vec::with_capacity(4usize.saturating_add(txids.len().saturating_mul(32)));
    raw.extend_from_slice(
        &u32::try_from(txids.len())
            .context("transaction-ID list is too large")?
            .to_le_bytes(),
    );
    for txid in txids {
        raw.extend_from_slice(&txid.to_byte_array());
    }
    encode_storage_payload(&raw, MAX_STORED_TRANSACTION_INDEX_SIZE)
}

fn decode_txid_list(bytes: &[u8]) -> Result<Vec<Txid>> {
    let raw = decode_storage_payload(bytes, MAX_STORED_TRANSACTION_INDEX_SIZE)?;
    if raw.len() < 4 {
        bail!("truncated transaction-ID list");
    }
    let count = u32::from_le_bytes(raw[..4].try_into().expect("txid count is fixed")) as usize;
    if raw.len() != 4usize.saturating_add(count.saturating_mul(32)) {
        bail!("transaction-ID list length does not match its count");
    }
    raw[4..]
        .chunks_exact(32)
        .map(|txid| {
            Ok(Txid::from_byte_array(
                txid.try_into().expect("txid length is fixed"),
            ))
        })
        .collect()
}

fn encode_stored_tx_location(location: StoredTxLocation) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(40);
    bytes.extend_from_slice(&location.block_hash.to_byte_array());
    bytes.extend_from_slice(&location.height.to_le_bytes());
    bytes.extend_from_slice(&location.transaction_index.to_le_bytes());
    bytes
}

fn decode_stored_tx_location(bytes: &[u8]) -> Result<StoredTxLocation> {
    if bytes.len() != 40 {
        bail!("invalid stored transaction location length");
    }
    Ok(StoredTxLocation {
        block_hash: BlockHash::from_byte_array(
            bytes[..32].try_into().expect("block hash length is fixed"),
        ),
        height: u32::from_le_bytes(bytes[32..36].try_into().expect("height length is fixed")),
        transaction_index: u32::from_le_bytes(
            bytes[36..]
                .try_into()
                .expect("transaction index length is fixed"),
        ),
    })
}

fn active_transaction_key(txid: Txid, height: u32, transaction_index: u32) -> [u8; 40] {
    let mut key = [0u8; 40];
    key[..32].copy_from_slice(&txid.to_byte_array());
    key[32..36].copy_from_slice(&height.to_be_bytes());
    key[36..].copy_from_slice(&transaction_index.to_be_bytes());
    key
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

pub(crate) struct PreparedChainstateRecord {
    hash: BlockHash,
    encoded_payload: Vec<u8>,
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

    pub fn flush(&mut self) -> Result<()> {
        self.flush_pending_writes()?;
        publish_index_data_len(&mut self.index_file, data_len_after(&self.file)?)?;
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
        let bytes = read_storage_record(
            &self.file,
            record,
            XorKey::default(),
            MAX_STORED_CHAINSTATE_DELTA_SIZE + 32,
            "chainstate delta",
        )?;
        if bytes.len() < 32 {
            bail!("stored chainstate delta is truncated");
        }
        let stored_hash = BlockHash::from_byte_array(
            bytes[..32]
                .try_into()
                .expect("chainstate delta hash has fixed width"),
        );
        if stored_hash != *hash {
            bail!("stored chainstate delta hash does not match its index");
        }
        let payload = decode_storage_payload(&bytes[32..], MAX_STORED_CHAINSTATE_DELTA_SIZE)
            .context("decoding compressed chainstate delta")?;
        Ok(Some(payload))
    }

    pub fn insert(&mut self, hash: BlockHash, payload: &[u8]) -> Result<()> {
        self.insert_with_index_sync(hash, payload, true)
    }

    pub fn insert_unsynced(&mut self, hash: BlockHash, payload: &[u8]) -> Result<()> {
        self.insert_with_index_sync(hash, payload, false)
    }

    fn insert_with_index_sync(
        &mut self,
        hash: BlockHash,
        payload: &[u8],
        sync_index: bool,
    ) -> Result<()> {
        if self.index.contains_key(&hash) {
            return Ok(());
        }
        if payload.len() > MAX_STORED_CHAINSTATE_DELTA_SIZE {
            bail!("chainstate delta is too large: {} bytes", payload.len());
        }
        let prepared = Self::prepare_record(hash, payload)?;
        self.insert_prepared_with_index_sync(prepared, sync_index)
    }

    pub(crate) fn prepare_record(
        hash: BlockHash,
        payload: &[u8],
    ) -> Result<PreparedChainstateRecord> {
        if payload.len() > MAX_STORED_CHAINSTATE_DELTA_SIZE {
            bail!("chainstate delta is too large: {} bytes", payload.len());
        }
        Ok(PreparedChainstateRecord {
            hash,
            encoded_payload: encode_storage_payload(payload, MAX_STORED_CHAINSTATE_DELTA_SIZE)?,
        })
    }

    pub(crate) fn insert_prepared(&mut self, prepared: PreparedChainstateRecord) -> Result<()> {
        self.insert_prepared_with_index_sync(prepared, true)
    }

    pub(crate) fn insert_prepared_unsynced(
        &mut self,
        prepared: PreparedChainstateRecord,
    ) -> Result<()> {
        self.insert_prepared_with_index_sync(prepared, false)
    }

    fn insert_prepared_with_index_sync(
        &mut self,
        prepared: PreparedChainstateRecord,
        sync_index: bool,
    ) -> Result<()> {
        let hash = prepared.hash;
        if self.index.contains_key(&hash) {
            return Ok(());
        }
        let encoded_payload = prepared.encoded_payload;
        let length = 32usize
            .checked_add(encoded_payload.len())
            .context("chainstate delta length overflow")?;
        let length = u32::try_from(length).context("chainstate delta length does not fit u32")?;
        let offset = self.file.seek(SeekFrom::End(0))?;
        let mut record_bytes = Vec::with_capacity(4 + 32 + encoded_payload.len());
        record_bytes.extend_from_slice(&length.to_le_bytes());
        record_bytes.extend_from_slice(&hash.to_byte_array());
        record_bytes.extend_from_slice(&encoded_payload);
        self.file.write_all(&record_bytes)?;
        self.pending_write_bytes = self
            .pending_write_bytes
            .saturating_add(4usize.saturating_add(usize::try_from(length).unwrap_or(usize::MAX)));
        let record = Record { offset, length };
        persist_index_entry_with_sync(
            &mut self.index_file,
            offset + 4 + u64::from(length),
            hash,
            record,
            sync_index,
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

/// Crash-recoverable, batched UTXO storage.
///
/// Coins are keyed directly by outpoint in the LSM database. Fjall's journal
/// and atomic batches provide recovery without a second location index or a
/// startup replay of the complete UTXO set.
const DISK_INDEX_DEFAULT_CACHE_BYTES: u64 = 64 * 1024 * 1024;
const DISK_INDEX_DEFAULT_WRITE_BUFFER_BYTES: u64 = 64 * 1024 * 1024;
const UTXO_PARTITION_NAME: &str = "coins";
const UTXO_META_PARTITION_NAME: &str = "metadata";
const META_ENTRY_COUNT: &[u8] = b"entry-count";
const META_GENERATION: &[u8] = b"generation";

/// Disk-backed UTXO set with a bounded decoded-value cache.
///
/// Outpoints are stored directly in an LSM tree; only the configured database
/// block cache, write buffers, and decoded-value cache remain resident.
pub struct UtxoStore {
    path: PathBuf,
    recovery_marker_path: PathBuf,
    recovery_attempt_path: PathBuf,
    keyspace: Keyspace,
    coins: PartitionHandle,
    metadata: PartitionHandle,
    entry_count: usize,
    generation: u64,
    crash_ratio: Option<u64>,
    read_cache: Mutex<UtxoReadCache>,
}

impl UtxoStore {
    pub fn open(directory: impl AsRef<Path>) -> Result<Self> {
        Self::open_with_cache(directory, DISK_INDEX_DEFAULT_CACHE_BYTES)
    }

    pub fn open_with_cache(directory: impl AsRef<Path>, cache_bytes: u64) -> Result<Self> {
        let directory = directory.as_ref();
        create_dir_all(directory)
            .with_context(|| format!("creating UTXO store {}", directory.display()))?;
        let path = directory.join("coins");
        let keyspace = FjallConfig::new(&path)
            .cache_size(cache_bytes.max(1024 * 1024))
            .max_write_buffer_size(DISK_INDEX_DEFAULT_WRITE_BUFFER_BYTES)
            .manual_journal_persist(true)
            .open()
            .with_context(|| format!("opening disk-backed UTXO database {}", path.display()))?;
        let coins = keyspace
            .open_partition(
                UTXO_PARTITION_NAME,
                PartitionCreateOptions::default().compression(CompressionType::Lz4),
            )
            .context("opening UTXO partition")?;
        let metadata = keyspace
            .open_partition(
                UTXO_META_PARTITION_NAME,
                PartitionCreateOptions::default().compression(CompressionType::None),
            )
            .context("opening UTXO metadata partition")?;
        let entry_count = read_usize_metadata(&metadata, META_ENTRY_COUNT)?.unwrap_or(0);
        if entry_count == 0 && !coins.is_empty()? {
            bail!("UTXO database is missing its exact entry-count metadata");
        }
        let generation = match read_u64_metadata(&metadata, META_GENERATION)? {
            Some(generation) if generation != 0 => generation,
            _ => {
                let generation = random::<u64>().max(1);
                metadata.insert(META_GENERATION, generation.to_le_bytes().to_vec())?;
                metadata.insert(META_ENTRY_COUNT, 0u64.to_le_bytes().to_vec())?;
                keyspace.persist(PersistMode::SyncAll)?;
                generation
            }
        };
        Ok(Self {
            recovery_marker_path: directory.join("utxos.recovery.pending"),
            recovery_attempt_path: directory.join("utxos.recovery.attempted"),
            path,
            keyspace,
            coins,
            metadata,
            entry_count,
            generation,
            crash_ratio: None,
            read_cache: Mutex::new(UtxoReadCache::default()),
        })
    }

    pub fn configure_crash_ratio(&mut self, ratio: Option<u64>) {
        self.crash_ratio = ratio.filter(|ratio| *ratio > 0);
    }

    fn mark_recovery_pending(&self) -> Result<()> {
        let mut marker = OpenOptions::new()
            .create(true)
            .truncate(true)
            .write(true)
            .open(&self.recovery_marker_path)?;
        marker.write_all(b"recovery required\n")?;
        marker.sync_data()?;
        Ok(())
    }

    pub fn maybe_simulate_recovery_crash(&self) -> Result<()> {
        if self.recovery_attempt_path.exists() {
            match remove_file(&self.recovery_attempt_path) {
                Ok(()) => {}
                Err(error) if error.kind() == ErrorKind::NotFound => {}
                Err(error) => return Err(error.into()),
            }
            return Ok(());
        }
        if !self.recovery_marker_path.exists() {
            return Ok(());
        }
        if self.crash_ratio.is_none() {
            let _ = remove_file(&self.recovery_marker_path);
            return Ok(());
        }
        std::fs::rename(&self.recovery_marker_path, &self.recovery_attempt_path)?;
        tracing::error!("Simulating a crash during chainstate recovery. Goodbye.");
        std::process::abort();
    }

    pub fn maybe_simulate_crash(&self) -> Result<()> {
        let Some(ratio) = self.crash_ratio else {
            return Ok(());
        };
        if random::<u64>() % ratio == 0 {
            self.mark_recovery_pending()?;
            tracing::error!("Simulating a crash. Goodbye.");
            std::process::abort();
        }
        Ok(())
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn index_path(&self) -> &Path {
        &self.path
    }

    pub fn len(&self) -> usize {
        self.entry_count
    }

    pub fn is_empty(&self) -> bool {
        self.entry_count == 0
    }

    pub fn generation(&self) -> u64 {
        self.generation
    }

    /// The LSM block cache and write buffers are bounded independently.  Use
    /// the remaining storage allocation for decoded hot UTXOs, with a floor
    /// suitable for tests and very small nodes.
    pub fn configure_cache_size_mib(&self, mib: i64) {
        const MIN_CACHE_MIB: u64 = 4;
        const MIB: u64 = 1024 * 1024;
        let mib = u64::try_from(mib.max(0)).unwrap_or(u64::MAX);
        let total_bytes = mib.max(MIN_CACHE_MIB).saturating_mul(MIB);
        let limit = usize::try_from(total_bytes / 2).unwrap_or(usize::MAX);
        self.read_cache.lock().configure_limit(limit);
    }

    /// New outputs populate the decoded cache as they are connected.  A full
    /// startup scan would defeat the disk-backed design, so this store does
    /// not materialize the UTXO set merely to warm it.
    pub fn warm_cache(&self) -> Result<(usize, usize)> {
        let cache = self.read_cache.lock();
        Ok((cache.entries.len(), cache.bytes))
    }

    pub fn contains(&self, outpoint: &OutPoint) -> Result<bool> {
        self.coins
            .contains_key(encode_outpoint(outpoint))
            .context("looking up UTXO key")
    }

    pub fn disk_usage(&self) -> Result<u64> {
        Ok(self
            .coins
            .disk_space()
            .saturating_add(self.metadata.disk_space()))
    }

    pub fn get(&self, outpoint: &OutPoint) -> Result<Option<StoredUtxo>> {
        if let Some(entry) = self.read_cache.lock().get(outpoint) {
            return Ok(Some(entry));
        }
        let Some(bytes) = self
            .coins
            .get(encode_outpoint(outpoint))
            .context("reading UTXO value")?
        else {
            return Ok(None);
        };
        let entry = decode_stored_utxo(&bytes)?;
        self.read_cache.lock().insert(*outpoint, entry.clone());
        Ok(Some(entry))
    }

    pub fn entries(&self) -> Result<Vec<(OutPoint, StoredUtxo)>> {
        self.coins
            .iter()
            .map(|item| {
                let (key, value) = item.context("scanning UTXO database")?;
                Ok((decode_outpoint(&key)?, decode_stored_utxo(&value)?))
            })
            .collect()
    }

    pub fn apply_batch(
        &mut self,
        removals: &[OutPoint],
        additions: &[(OutPoint, StoredUtxo)],
    ) -> Result<()> {
        self.apply_batch_with_sync(removals, additions, true)
    }

    pub fn apply_batch_unsynced(
        &mut self,
        removals: &[OutPoint],
        additions: &[(OutPoint, StoredUtxo)],
    ) -> Result<()> {
        self.apply_batch_with_sync(removals, additions, false)
    }

    /// Apply a consensus-validated transition whose removals are known to
    /// exist and whose additions are known to be fresh. This avoids one LSM
    /// point lookup per affected output on the normal block-connect path.
    pub fn apply_validated_batch(
        &mut self,
        removals: &[OutPoint],
        additions: &[(OutPoint, StoredUtxo)],
    ) -> Result<()> {
        self.apply_validated_batch_with_sync(removals, additions, true)
    }

    pub fn apply_validated_batch_unsynced(
        &mut self,
        removals: &[OutPoint],
        additions: &[(OutPoint, StoredUtxo)],
    ) -> Result<()> {
        self.apply_validated_batch_with_sync(removals, additions, false)
    }

    fn apply_validated_batch_with_sync(
        &mut self,
        removals: &[OutPoint],
        additions: &[(OutPoint, StoredUtxo)],
        sync: bool,
    ) -> Result<()> {
        let next_count = self
            .entry_count
            .checked_sub(removals.len())
            .and_then(|count| count.checked_add(additions.len()))
            .context("validated UTXO batch entry count overflow")?;
        self.commit_batch_with_count(removals, additions, next_count, sync)
    }

    fn apply_batch_with_sync(
        &mut self,
        removals: &[OutPoint],
        additions: &[(OutPoint, StoredUtxo)],
        sync: bool,
    ) -> Result<()> {
        if removals.is_empty() && additions.is_empty() {
            return Ok(());
        }
        let addition_keys = additions
            .iter()
            .map(|(outpoint, _)| *outpoint)
            .collect::<HashSet<_>>();
        let affected = removals
            .iter()
            .copied()
            .chain(addition_keys.iter().copied())
            .collect::<HashSet<_>>();
        let mut next_count = self.entry_count;
        for outpoint in affected {
            let existed = self.contains(&outpoint)?;
            let exists_after = addition_keys.contains(&outpoint);
            match (existed, exists_after) {
                (false, true) => next_count = next_count.saturating_add(1),
                (true, false) => next_count = next_count.saturating_sub(1),
                _ => {}
            }
        }

        self.commit_batch_with_count(removals, additions, next_count, sync)
    }

    fn commit_batch_with_count(
        &mut self,
        removals: &[OutPoint],
        additions: &[(OutPoint, StoredUtxo)],
        next_count: usize,
        sync: bool,
    ) -> Result<()> {
        if removals.is_empty() && additions.is_empty() {
            return Ok(());
        }

        let mut batch = self
            .keyspace
            .batch()
            .durability(sync.then_some(PersistMode::SyncData));
        for outpoint in removals {
            batch.remove(&self.coins, encode_outpoint(outpoint).to_vec());
        }
        for (outpoint, entry) in additions {
            batch.insert(
                &self.coins,
                encode_outpoint(outpoint).to_vec(),
                encode_stored_utxo(entry)?,
            );
        }
        batch.insert(
            &self.metadata,
            META_ENTRY_COUNT.to_vec(),
            u64::try_from(next_count)
                .context("UTXO entry count does not fit u64")?
                .to_le_bytes()
                .to_vec(),
        );
        batch.commit().context("committing UTXO database batch")?;

        let mut read_cache = self.read_cache.lock();
        for outpoint in removals {
            read_cache.remove(outpoint);
        }
        for (outpoint, entry) in additions {
            read_cache.insert(*outpoint, entry.clone());
        }
        self.entry_count = next_count;
        Ok(())
    }

    pub fn replace_all<I>(&mut self, entries: I) -> Result<()>
    where
        I: IntoIterator<Item = (OutPoint, StoredUtxo)>,
    {
        self.clear()?;
        let mut pending = Vec::with_capacity(10_000);
        for entry in entries {
            pending.push(entry);
            if pending.len() == 10_000 {
                self.apply_batch_unsynced(&[], &pending)?;
                pending.clear();
            }
        }
        if !pending.is_empty() {
            self.apply_batch_unsynced(&[], &pending)?;
        }
        self.flush()
    }

    pub fn compact(&mut self) -> Result<()> {
        self.flush()?;
        self.coins
            .major_compact()
            .context("compacting UTXO database")
    }

    pub fn compact_if_needed(&mut self) -> Result<bool> {
        // Fjall performs leveled background compaction and reclaims
        // tombstoned entries without materializing the keyspace.
        Ok(false)
    }

    pub fn clear(&mut self) -> Result<()> {
        loop {
            let keys = self
                .coins
                .keys()
                .take(10_000)
                .map(|key| key.map(|key| key.to_vec()))
                .collect::<std::result::Result<Vec<_>, _>>()?;
            if keys.is_empty() {
                break;
            }
            let mut batch = self.keyspace.batch();
            for key in keys {
                batch.remove(&self.coins, key);
            }
            batch.commit()?;
        }
        self.entry_count = 0;
        self.generation = self
            .generation
            .checked_add(1)
            .context("UTXO store generation exhausted")?;
        let mut batch = self
            .keyspace
            .batch()
            .durability(Some(PersistMode::SyncData));
        batch.insert(
            &self.metadata,
            META_ENTRY_COUNT.to_vec(),
            0u64.to_le_bytes().to_vec(),
        );
        batch.insert(
            &self.metadata,
            META_GENERATION.to_vec(),
            self.generation.to_le_bytes().to_vec(),
        );
        batch.commit()?;
        self.read_cache.lock().clear();
        Ok(())
    }

    pub fn flush(&mut self) -> Result<()> {
        self.keyspace
            .persist(PersistMode::SyncData)
            .context("flushing UTXO database")
    }
}

impl Drop for UtxoStore {
    fn drop(&mut self) {
        let _ = self.flush();
    }
}

fn read_u64_metadata(partition: &PartitionHandle, key: &[u8]) -> Result<Option<u64>> {
    let Some(bytes) = partition.get(key)? else {
        return Ok(None);
    };
    let bytes: [u8; 8] = bytes
        .as_ref()
        .try_into()
        .context("database metadata value is not a u64")?;
    Ok(Some(u64::from_le_bytes(bytes)))
}

fn read_usize_metadata(partition: &PartitionHandle, key: &[u8]) -> Result<Option<usize>> {
    read_u64_metadata(partition, key)?
        .map(|value| usize::try_from(value).context("database count does not fit usize"))
        .transpose()
}

const HISTORY_EVENTS_PARTITION_NAME: &str = "events";
const HISTORY_META_PARTITION_NAME: &str = "metadata";

/// Disk-backed Electrum history index.
///
/// Every confirmed history item is an immutable event keyed by script hash,
/// height, and its order within that height. Prefix scans answer Electrum
/// queries directly. Normal IBD therefore performs insert-only batches: it
/// never reads a per-script head or rewrites an existing history value.
pub struct ElectrumHistoryStore {
    path: PathBuf,
    keyspace: Keyspace,
    events: PartitionHandle,
    metadata: PartitionHandle,
    entry_count: usize,
    generation: u64,
}

impl ElectrumHistoryStore {
    pub fn open(directory: impl AsRef<Path>) -> Result<Self> {
        Self::open_with_cache(directory, DISK_INDEX_DEFAULT_CACHE_BYTES)
    }

    pub fn open_with_cache(directory: impl AsRef<Path>, cache_bytes: u64) -> Result<Self> {
        let directory = directory.as_ref();
        create_dir_all(directory)
            .with_context(|| format!("creating Electrum history store {}", directory.display()))?;
        // Storage is intentionally versioned by directory. There has been no
        // public release, so the former head/chunk schema is not opened or
        // migrated; a rebuild starts with this event-oriented layout.
        let path = directory.join("history-v2");
        let keyspace = FjallConfig::new(&path)
            .cache_size(cache_bytes.max(1024 * 1024))
            .max_write_buffer_size(DISK_INDEX_DEFAULT_WRITE_BUFFER_BYTES)
            .manual_journal_persist(true)
            .open()
            .with_context(|| format!("opening disk-backed Electrum database {}", path.display()))?;
        let events = keyspace.open_partition(
            HISTORY_EVENTS_PARTITION_NAME,
            // Segment compression exploits the shared 32-byte script prefix
            // while retaining inexpensive decompression for query serving.
            PartitionCreateOptions::default().compression(CompressionType::Lz4),
        )?;
        let metadata = keyspace.open_partition(
            HISTORY_META_PARTITION_NAME,
            PartitionCreateOptions::default().compression(CompressionType::None),
        )?;
        let entry_count = read_usize_metadata(&metadata, META_ENTRY_COUNT)?.unwrap_or(0);
        if entry_count == 0 && !events.is_empty()? {
            bail!("Electrum history database is missing its exact entry-count metadata");
        }
        let generation = match read_u64_metadata(&metadata, META_GENERATION)? {
            Some(generation) if generation != 0 => generation,
            _ => {
                let generation = 1u64;
                metadata.insert(META_GENERATION, generation.to_le_bytes().to_vec())?;
                metadata.insert(META_ENTRY_COUNT, 0u64.to_le_bytes().to_vec())?;
                keyspace.persist(PersistMode::SyncAll)?;
                generation
            }
        };
        Ok(Self {
            path,
            keyspace,
            events,
            metadata,
            entry_count,
            generation,
        })
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn index_path(&self) -> &Path {
        &self.path
    }

    pub fn len(&self) -> usize {
        self.entry_count
    }

    pub fn is_empty(&self) -> bool {
        self.entry_count == 0
    }

    pub fn generation(&self) -> u64 {
        self.generation
    }

    pub fn contains(&self, script_hash: &str) -> bool {
        encode_history_script_hash(script_hash)
            .ok()
            .is_some_and(|key| {
                self.events
                    .prefix(key)
                    .next()
                    .is_some_and(|item| item.is_ok())
            })
    }

    pub fn disk_usage(&self) -> Result<u64> {
        Ok(self
            .events
            .disk_space()
            .saturating_add(self.metadata.disk_space()))
    }

    pub fn get(&self, script_hash: &str) -> Result<StoredElectrumHistory> {
        self.get_limited(script_hash, usize::MAX)
            .map(|history| history.expect("unlimited history limit cannot be exceeded"))
    }

    pub fn get_limited(
        &self,
        script_hash: &str,
        limit: usize,
    ) -> Result<Option<StoredElectrumHistory>> {
        let script_hash = encode_history_script_hash(script_hash)?;
        let mut history = Vec::new();
        for item in self.events.prefix(script_hash) {
            let (key, _) = item.context("scanning Electrum history events")?;
            history.push(decode_history_event_key(&key)?.1);
            if history.len() > limit {
                return Ok(None);
            }
        }
        Ok(Some(history))
    }

    pub fn get_batch(
        &self,
        script_hashes: &[String],
    ) -> Result<HashMap<String, StoredElectrumHistory>> {
        script_hashes
            .iter()
            .map(|script_hash| Ok((script_hash.clone(), self.get(script_hash)?)))
            .collect()
    }

    pub fn keys(&self) -> Vec<String> {
        self.events
            .keys()
            .filter_map(|key| key.ok())
            .filter_map(|key| decode_history_event_key(&key).ok().map(|entry| entry.0))
            .collect::<HashSet<_>>()
            .into_iter()
            .map(hex::encode)
            .collect()
    }

    pub fn entries(&self) -> Result<Vec<(String, StoredElectrumHistory)>> {
        let mut histories: HashMap<[u8; 32], StoredElectrumHistory> = HashMap::new();
        for item in self.events.iter() {
            let (key, _) = item.context("scanning Electrum history database")?;
            let (script_hash, entry) = decode_history_event_key(&key)?;
            histories.entry(script_hash).or_default().push(entry);
        }
        Ok(histories
            .into_iter()
            .map(|(script_hash, history)| (hex::encode(script_hash), history))
            .collect())
    }

    pub fn apply_batch(&mut self, updates: &[(String, StoredElectrumHistory)]) -> Result<()> {
        self.apply_batch_with_sync(updates, true)
    }

    pub fn apply_batch_unsynced(
        &mut self,
        updates: &[(String, StoredElectrumHistory)],
    ) -> Result<()> {
        self.apply_batch_with_sync(updates, false)
    }

    pub fn append_entries(&mut self, updates: &[(String, StoredElectrumHistory)]) -> Result<()> {
        self.append_entries_with_sync(updates, true)
    }

    pub fn append_entries_unsynced(
        &mut self,
        updates: &[(String, StoredElectrumHistory)],
    ) -> Result<()> {
        self.append_entries_with_sync(updates, false)
    }

    pub fn append_entries_owned_unsynced(
        &mut self,
        updates: Vec<(String, StoredElectrumHistory)>,
    ) -> Result<()> {
        let updates = updates
            .into_iter()
            .map(|(script_hash, entries)| Ok((encode_history_script_hash(&script_hash)?, entries)))
            .collect::<Result<Vec<_>>>()?;
        self.append_encoded_entries(&updates, false)
    }

    fn apply_batch_with_sync(
        &mut self,
        updates: &[(String, StoredElectrumHistory)],
        sync: bool,
    ) -> Result<()> {
        let mut encoded = FastHashMap::new();
        for (script_hash, entries) in updates {
            encoded.insert(encode_history_script_hash(script_hash)?, entries.clone());
        }
        let mut encoded = encoded.into_iter().collect::<Vec<_>>();
        encoded.sort_unstable_by_key(|(script_hash, _)| *script_hash);
        self.replace_encoded_entries(&encoded, sync)
    }

    fn append_entries_with_sync(
        &mut self,
        updates: &[(String, StoredElectrumHistory)],
        sync: bool,
    ) -> Result<()> {
        let mut encoded = FastHashMap::new();
        for (script_hash, additions) in updates {
            let history = encoded
                .entry(encode_history_script_hash(script_hash)?)
                .or_insert_with(Vec::new);
            extend_history(history, additions);
        }
        let mut encoded = encoded.into_iter().collect::<Vec<_>>();
        encoded.sort_unstable_by_key(|(script_hash, _)| *script_hash);
        self.append_encoded_entries(&encoded, sync)
    }

    fn replace_encoded_entries(
        &mut self,
        updates: &[([u8; 32], StoredElectrumHistory)],
        sync: bool,
    ) -> Result<()> {
        if updates.is_empty() {
            return Ok(());
        }
        let mut batch = self
            .keyspace
            .batch()
            .durability(sync.then_some(PersistMode::SyncData));
        let mut next_count = self.entry_count;
        for (script_hash, entries) in updates {
            let previous_keys = self
                .events
                .prefix(script_hash)
                .map(|item| item.map(|(key, _)| key.to_vec()))
                .collect::<std::result::Result<Vec<_>, _>>()?;
            for key in &previous_keys {
                batch.remove(&self.events, key.clone());
            }
            let inserted = insert_history_events(&mut batch, &self.events, *script_hash, entries)?;
            next_count = next_count
                .checked_sub(previous_keys.len())
                .and_then(|count| count.checked_add(inserted))
                .context("Electrum history entry count overflow")?;
        }
        self.commit_history_batch(batch, next_count)
    }

    /// Append consensus-validated history events. Active-chain connection
    /// guarantees these `(script, height, transaction)` positions are fresh,
    /// so the IBD path needs no existence probes.
    fn append_encoded_entries(
        &mut self,
        updates: &[([u8; 32], StoredElectrumHistory)],
        sync: bool,
    ) -> Result<()> {
        let additions = updates
            .iter()
            .map(|(_, entries)| deduplicated_history_len(entries))
            .sum::<usize>();
        if additions == 0 {
            return Ok(());
        }
        let next_count = self
            .entry_count
            .checked_add(additions)
            .context("Electrum history entry count overflow")?;
        let mut batch = self
            .keyspace
            .batch()
            .durability(sync.then_some(PersistMode::SyncData));
        for (script_hash, entries) in updates {
            insert_history_events(&mut batch, &self.events, *script_hash, entries)?;
        }
        self.commit_history_batch(batch, next_count)
    }

    fn commit_history_batch(&mut self, mut batch: fjall::Batch, next_count: usize) -> Result<()> {
        let next_generation = self
            .generation
            .checked_add(1)
            .context("Electrum history generation exhausted")?;
        batch.insert(
            &self.metadata,
            META_ENTRY_COUNT.to_vec(),
            u64::try_from(next_count)
                .context("Electrum history count does not fit u64")?
                .to_le_bytes()
                .to_vec(),
        );
        batch.insert(
            &self.metadata,
            META_GENERATION.to_vec(),
            next_generation.to_le_bytes().to_vec(),
        );
        batch
            .commit()
            .context("committing Electrum history batch")?;
        self.entry_count = next_count;
        self.generation = next_generation;
        Ok(())
    }

    pub fn replace_all<I>(&mut self, entries: I) -> Result<()>
    where
        I: IntoIterator<Item = (String, StoredElectrumHistory)>,
    {
        self.clear()?;
        let mut pending = Vec::with_capacity(1000);
        for entry in entries {
            pending.push(entry);
            if pending.len() == 1000 {
                self.apply_batch_with_sync(&pending, false)?;
                pending.clear();
            }
        }
        if !pending.is_empty() {
            self.apply_batch_with_sync(&pending, false)?;
        }
        self.flush()
    }

    pub fn compact(&mut self) -> Result<()> {
        self.flush()?;
        self.events.major_compact()?;
        Ok(())
    }

    pub fn compact_if_needed(&mut self) -> Result<bool> {
        Ok(false)
    }

    pub fn clear(&mut self) -> Result<()> {
        clear_partition(&self.keyspace, &self.events)?;
        self.entry_count = 0;
        self.generation = self
            .generation
            .checked_add(1)
            .context("Electrum history generation exhausted")?;
        let mut batch = self
            .keyspace
            .batch()
            .durability(Some(PersistMode::SyncData));
        batch.insert(
            &self.metadata,
            META_ENTRY_COUNT.to_vec(),
            0u64.to_le_bytes().to_vec(),
        );
        batch.insert(
            &self.metadata,
            META_GENERATION.to_vec(),
            self.generation.to_le_bytes().to_vec(),
        );
        batch.commit()?;
        Ok(())
    }

    pub fn flush(&mut self) -> Result<()> {
        self.keyspace
            .persist(PersistMode::SyncData)
            .context("flushing Electrum history database")
    }
}

impl Drop for ElectrumHistoryStore {
    fn drop(&mut self) {
        let _ = self.flush();
    }
}

const HISTORY_EVENT_KEY_SIZE: usize = 32 + 4 + 4 + 32;

fn history_event_key(
    script_hash: [u8; 32],
    txid: Txid,
    height: u32,
    ordinal: u32,
) -> [u8; HISTORY_EVENT_KEY_SIZE] {
    let mut key = [0u8; HISTORY_EVENT_KEY_SIZE];
    key[..32].copy_from_slice(&script_hash);
    key[32..36].copy_from_slice(&height.to_be_bytes());
    key[36..40].copy_from_slice(&ordinal.to_be_bytes());
    key[40..].copy_from_slice(&txid.to_byte_array());
    key
}

fn decode_history_event_key(bytes: &[u8]) -> Result<([u8; 32], (Txid, u32))> {
    if bytes.len() != HISTORY_EVENT_KEY_SIZE {
        bail!("invalid Electrum history event key length");
    }
    let script_hash = bytes[..32]
        .try_into()
        .expect("history event script hash has a fixed length");
    let height = u32::from_be_bytes(
        bytes[32..36]
            .try_into()
            .expect("history event height has a fixed length"),
    );
    let txid = Txid::from_byte_array(
        bytes[40..]
            .try_into()
            .expect("history event txid has a fixed length"),
    );
    Ok((script_hash, (txid, height)))
}

fn deduplicated_history_len(entries: &StoredElectrumHistory) -> usize {
    usize::from(!entries.is_empty()).saturating_add(
        entries
            .windows(2)
            .filter(|window| window[0] != window[1])
            .count(),
    )
}

fn insert_history_events(
    batch: &mut fjall::Batch,
    events: &PartitionHandle,
    script_hash: [u8; 32],
    entries: &StoredElectrumHistory,
) -> Result<usize> {
    let mut previous_height = None;
    let mut previous_entry = None;
    let mut ordinal = 0u32;
    let mut inserted = 0usize;
    for (txid, height) in entries {
        if previous_entry == Some((*txid, *height)) {
            continue;
        }
        if previous_height == Some(*height) {
            ordinal = ordinal
                .checked_add(1)
                .context("too many Electrum history entries at one height")?;
        } else {
            previous_height = Some(*height);
            ordinal = 0;
        }
        batch.insert(
            events,
            history_event_key(script_hash, *txid, *height, ordinal).to_vec(),
            Vec::new(),
        );
        previous_entry = Some((*txid, *height));
        inserted = inserted.saturating_add(1);
    }
    Ok(inserted)
}

fn clear_partition(keyspace: &Keyspace, partition: &PartitionHandle) -> Result<()> {
    loop {
        let keys = partition
            .keys()
            .take(10_000)
            .map(|key| key.map(|key| key.to_vec()))
            .collect::<std::result::Result<Vec<_>, _>>()?;
        if keys.is_empty() {
            return Ok(());
        }
        let mut batch = keyspace.batch();
        for key in keys {
            batch.remove(partition, key);
        }
        batch.commit()?;
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

fn extend_history(history: &mut StoredElectrumHistory, additions: &[(Txid, u32)]) {
    for entry in additions {
        if history.last() != Some(entry) {
            history.push(*entry);
        }
    }
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
        self.insert_with_sync(record, true)
    }

    pub fn insert_unsynced(&mut self, record: &CoinStatsRecord) -> Result<()> {
        self.insert_with_sync(record, false)
    }

    fn insert_with_sync(&mut self, record: &CoinStatsRecord, sync: bool) -> Result<()> {
        if self.index.contains_key(&record.block_hash) {
            return Ok(());
        }
        let raw_bytes = serde_json::to_vec(record).context("encoding coinstats record")?;
        let bytes = encode_storage_payload(&raw_bytes, MAX_STORED_COINSTATS_SIZE)?;
        let offset = self.file.seek(SeekFrom::End(0))?;
        let length = u32::try_from(bytes.len()).context("coinstats length does not fit u32")?;
        let mut record_bytes = Vec::with_capacity(4 + bytes.len());
        record_bytes.extend_from_slice(&length.to_le_bytes());
        record_bytes.extend_from_slice(&bytes);
        self.file.write_all(&record_bytes)?;
        if sync {
            self.file.sync_data()?;
        }
        let record_index = Record { offset, length };
        persist_index_entry_with_sync(
            &mut self.index_file,
            offset + 4 + bytes.len() as u64,
            record.block_hash,
            record_index,
            sync,
        )?;
        self.index.insert(record.block_hash, record_index);
        Ok(())
    }

    pub fn get(&mut self, hash: &BlockHash) -> Result<Option<CoinStatsRecord>> {
        let Some(record) = self.index.get(hash).copied() else {
            return Ok(None);
        };
        let bytes = read_storage_record(
            &self.file,
            record,
            XorKey::default(),
            MAX_STORED_COINSTATS_SIZE,
            "coinstats",
        )?;
        let decoded: CoinStatsRecord =
            serde_json::from_slice(&bytes).context("decoding stored coinstats record")?;
        if decoded.block_hash != *hash {
            bail!("stored coinstats hash does not match coinstats index");
        }
        Ok(Some(decoded))
    }

    pub fn flush(&mut self) -> Result<()> {
        self.file.sync_data()?;
        publish_index_data_len(&mut self.index_file, data_len_after(&self.file)?)?;
        Ok(())
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
        let index = match load_electrum_index(&mut index_file, &file, data_len)? {
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

    pub fn len(&self) -> usize {
        self.index.len()
    }

    pub fn is_empty(&self) -> bool {
        self.index.is_empty()
    }

    pub fn disk_usage(&self) -> Result<u64> {
        self.file
            .metadata()?
            .len()
            .checked_add(self.index_file.metadata()?.len())
            .context("Electrum transaction store size overflowed")
    }

    pub fn insert(&mut self, block: &Block) -> Result<BlockHash> {
        self.insert_with_sync(block, true)
    }

    pub fn insert_unsynced(&mut self, block: &Block) -> Result<BlockHash> {
        self.insert_with_sync(block, false)
    }

    fn insert_with_sync(&mut self, block: &Block, sync: bool) -> Result<BlockHash> {
        let hash = block.block_hash();
        if self.index.contains_key(&hash) {
            return Ok(hash);
        }
        let raw_bytes = encode_electrum_block_record(hash, &block.txdata)?;
        let bytes = encode_storage_payload(&raw_bytes, MAX_STORED_ELECTRUM_BLOCK_SIZE + 32)?;
        let offset = self.file.seek(SeekFrom::End(0))?;
        let length = u32::try_from(bytes.len())
            .context("Electrum transaction record length does not fit u32")?;
        let mut record_bytes = Vec::with_capacity(4 + bytes.len());
        record_bytes.extend_from_slice(&length.to_le_bytes());
        record_bytes.extend_from_slice(&bytes);
        self.file.write_all(&record_bytes)?;
        if sync {
            self.file.sync_data()?;
        }
        let record = Record { offset, length };
        persist_index_entry_with_sync(
            &mut self.index_file,
            offset + 4 + u64::from(length),
            hash,
            record,
            sync,
        )?;
        self.index.insert(hash, record);
        Ok(hash)
    }

    /// Remove transaction bodies that are no longer needed by the active
    /// pruned chain. The sidecar is intentionally append-only during normal
    /// operation, but a reorg or a node upgraded from the earlier
    /// eager-copying behavior can otherwise retain side-chain and still
    /// unpruned bodies forever.
    pub fn retain_only(&mut self, retained: &HashSet<BlockHash>) -> Result<bool> {
        let hashes = self.index.keys().copied().collect::<Vec<_>>();
        if hashes.iter().all(|hash| retained.contains(hash)) {
            return Ok(false);
        }

        let path = self.path.clone();
        let (file, index, data_len) = rewrite_record_file(
            &path,
            hashes
                .into_iter()
                .filter(|hash| retained.contains(hash))
                .map(|hash| {
                    let transactions = self
                        .transactions(&hash)?
                        .with_context(|| format!("Electrum transaction body {hash} disappeared"))?;
                    Ok((hash, encode_electrum_block_record(hash, &transactions)?))
                }),
            XorKey::default(),
            MAX_STORED_ELECTRUM_BLOCK_SIZE + 32,
        )?;
        self.file = file;
        self.index = index;
        rewrite_index(&mut self.index_file, data_len, &self.index)?;
        Ok(true)
    }

    pub fn flush(&mut self) -> Result<()> {
        self.file.sync_data()?;
        publish_index_data_len(&mut self.index_file, data_len_after(&self.file)?)?;
        Ok(())
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

    /// Read several pruned block transaction lists in append-log order.  The
    /// active chain is normally traversed by height, but compaction and
    /// recovery can leave the index order unrelated to that traversal.  Sort
    /// the requests by record offset so restart-time index rebuilds perform
    /// mostly forward reads from the sidecar.
    pub(crate) fn transactions_for_blocks(
        &mut self,
        block_hashes: &[BlockHash],
    ) -> Result<HashMap<BlockHash, Vec<Transaction>>> {
        let mut records = block_hashes
            .iter()
            .filter_map(|hash| self.index.get(hash).copied().map(|record| (*hash, record)))
            .collect::<Vec<_>>();
        records.sort_unstable_by_key(|(_, record)| record.offset);
        records.dedup_by_key(|(hash, _)| *hash);

        records
            .into_iter()
            .map(|(hash, record)| {
                self.transactions_from_record(hash, record)
                    .map(|transactions| (hash, transactions))
            })
            .collect()
    }

    fn transactions(&mut self, block_hash: &BlockHash) -> Result<Option<Vec<Transaction>>> {
        let Some(record) = self.index.get(block_hash).copied() else {
            return Ok(None);
        };
        self.transactions_from_record(*block_hash, record).map(Some)
    }

    fn transactions_from_record(
        &self,
        block_hash: BlockHash,
        record: Record,
    ) -> Result<Vec<Transaction>> {
        let bytes = read_storage_record(
            &self.file,
            record,
            XorKey::default(),
            MAX_STORED_ELECTRUM_BLOCK_SIZE + 32,
            "Electrum transaction",
        )?;
        if bytes.len() < 32 {
            bail!("stored Electrum transaction record is truncated")
        }
        let stored_hash = BlockHash::from_byte_array(
            bytes[..32]
                .try_into()
                .expect("Electrum block hash has fixed width"),
        );
        if stored_hash != block_hash {
            bail!("stored Electrum block hash does not match its index")
        }
        let transactions: Vec<Transaction> =
            deserialize(&bytes[32..]).context("decoding stored Electrum transactions")?;
        Ok(transactions)
    }
}

fn encode_electrum_block_record(hash: BlockHash, transactions: &[Transaction]) -> Result<Vec<u8>> {
    let mut bytes = hash.to_byte_array().to_vec();
    bytes.extend_from_slice(&serialize(&transactions.to_vec()));
    if bytes.len() > MAX_STORED_ELECTRUM_BLOCK_SIZE + 32 {
        bail!(
            "Electrum transaction record is too large: {} bytes",
            bytes.len()
        );
    }
    Ok(bytes)
}

impl Drop for ElectrumBlockStore {
    fn drop(&mut self) {
        let _ = self.flush();
    }
}

fn load_electrum_index(
    index_file: &mut File,
    data_file: &File,
    data_len: u64,
) -> Result<Option<HashMap<BlockHash, Record>>> {
    let Some(index) =
        load_index_with_limit(index_file, data_len, MAX_STORED_ELECTRUM_BLOCK_SIZE + 32)?
    else {
        return Ok(None);
    };
    for (hash, record) in &index {
        if validate_electrum_data_header(data_file, *record, *hash).is_err() {
            return Ok(None);
        }
    }
    Ok(Some(index))
}

fn validate_electrum_data_header(
    file: &File,
    record: Record,
    expected_hash: BlockHash,
) -> Result<()> {
    let bytes = read_storage_record(
        file,
        record,
        XorKey::default(),
        MAX_STORED_ELECTRUM_BLOCK_SIZE + 32,
        "Electrum transaction",
    )?;
    if bytes.len() < 32 {
        bail!("stored Electrum transaction record is truncated");
    }
    if BlockHash::from_byte_array(bytes[..32].try_into().expect("fixed block hash width"))
        != expected_hash
    {
        bail!("Electrum transaction value key does not match its index");
    }
    Ok(())
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
        if length == 0 || length as usize > MAX_STORED_ELECTRUM_BLOCK_SIZE + 32 {
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
        let bytes = decode_storage_payload(&bytes, MAX_STORED_ELECTRUM_BLOCK_SIZE + 32)
            .context("decoding compressed Electrum transaction record")?;
        if bytes.len() < 32 {
            bail!(
                "Electrum transaction record is truncated at offset {}",
                offset
            );
        }
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
        let bytes = decode_storage_payload(&bytes, MAX_STORED_COINSTATS_SIZE)
            .context("decoding compressed coinstats record")?;
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
        if record.length == 0
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
        if length == 0 || length as usize > MAX_STORED_FILTER_SIZE + 64 {
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
        let bytes = decode_storage_payload(&bytes, MAX_STORED_FILTER_SIZE + 64)
            .context("decoding compressed filter record")?;
        if bytes.len() < 64 {
            bail!("filter record is truncated at offset {}", offset);
        }
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
        if length == 0 || length as usize > MAX_STORED_CHAINSTATE_DELTA_SIZE + 32 {
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
        if bytes.len() < 32 {
            bail!("chainstate delta is truncated at offset {}", offset);
        }
        let hash = BlockHash::from_byte_array(
            bytes[..32]
                .try_into()
                .expect("chainstate delta hash has fixed width"),
        );
        decode_storage_payload(&bytes[32..], MAX_STORED_CHAINSTATE_DELTA_SIZE)
            .context("decoding compressed chainstate delta")?;
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
    // Fixed-width hexadecimal encoding has the same ordering as the raw
    // bytes, so avoid allocating a String for every index key during a
    // rewrite.
    entries.sort_unstable_by_key(|(hash, _)| hash.to_byte_array());
    for (hash, record) in entries {
        file.write_all(&hash.to_byte_array())?;
        file.write_all(&record.offset.to_le_bytes())?;
        file.write_all(&record.length.to_le_bytes())?;
    }
    file.sync_data()?;
    Ok(())
}

fn persist_index_entry_with_sync(
    file: &mut File,
    data_len: u64,
    hash: BlockHash,
    record: Record,
    sync: bool,
) -> Result<()> {
    if sync {
        file.seek(SeekFrom::Start(0))?;
        file.write_all(&data_len.to_le_bytes())?;
    }
    file.seek(SeekFrom::End(0))?;
    let mut bytes = [0u8; INDEX_RECORD_SIZE as usize];
    bytes[..32].copy_from_slice(&hash.to_byte_array());
    bytes[32..40].copy_from_slice(&record.offset.to_le_bytes());
    bytes[40..44].copy_from_slice(&record.length.to_le_bytes());
    file.write_all(&bytes)?;
    if sync {
        file.sync_data()?;
    }
    Ok(())
}

fn publish_index_data_len(file: &mut File, data_len: u64) -> Result<()> {
    file.seek(SeekFrom::Start(0))?;
    file.write_all(&data_len.to_le_bytes())?;
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

fn scan_index(
    file: &mut File,
    xor_key: XorKey,
    repair_truncated_tail: bool,
) -> Result<HashMap<BlockHash, Record>> {
    file.seek(SeekFrom::Start(0))?;
    let mut index = HashMap::new();
    let data_len = file.metadata()?.len();
    loop {
        let offset = file.stream_position()?;
        let mut length_bytes = [0u8; 4];
        match file.read_exact(&mut length_bytes) {
            Ok(()) => {}
            Err(error) if error.kind() == ErrorKind::UnexpectedEof => {
                // An exact EOF is already a clean tail. Reindex may have
                // opened the existing block file read-only, so avoid asking
                // the descriptor to truncate when there is nothing to trim.
                if offset < data_len && repair_truncated_tail {
                    file.set_len(offset)?;
                } else if offset < data_len {
                    bail!("truncated block record at offset {offset}");
                }
                break;
            }
            Err(error) => return Err(error.into()),
        }
        xor_key.apply(&mut length_bytes, offset);
        let length = u32::from_le_bytes(length_bytes);
        let end = offset.saturating_add(4).saturating_add(u64::from(length));
        if end > data_len {
            if repair_truncated_tail {
                file.set_len(offset)?;
            } else {
                bail!("truncated block record at offset {offset}");
            }
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
        let bytes = decode_storage_payload(&bytes, MAX_STORED_BLOCK_SIZE)
            .context("decoding compressed block record")?;
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
        let bytes = decode_storage_payload(&bytes, MAX_STORED_UNDO_SIZE)
            .context("decoding compressed undo record")?;
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

fn encode_undo_record(hash: BlockHash, undo: &[Vec<StoredUndo>]) -> Result<Vec<u8>> {
    let mut bytes = serialize(&hash);
    bytes.extend_from_slice(&serialize(&VarInt(undo.len() as u64)));
    for coins in undo {
        bytes.extend_from_slice(&serialize(&VarInt(coins.len() as u64)));
        for coin in coins {
            bytes.extend_from_slice(&coin.height.to_le_bytes());
            bytes.extend_from_slice(&coin.median_time_past.to_le_bytes());
            bytes.push(u8::from(coin.coinbase));
            bytes.extend_from_slice(&serialize(&coin.output));
        }
    }
    Ok(bytes)
}

fn decode_undo_record(bytes: &[u8]) -> Result<(BlockHash, Vec<Vec<StoredUndo>>)> {
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
            let metadata_end = consumed
                .checked_add(9)
                .context("stored undo coin metadata offset overflowed")?;
            if metadata_end > bytes.len() {
                bail!("stored undo coin metadata is truncated")
            }
            let height = u32::from_le_bytes(
                bytes[consumed..consumed + 4]
                    .try_into()
                    .expect("undo height has fixed width"),
            );
            let median_time_past = u32::from_le_bytes(
                bytes[consumed + 4..consumed + 8]
                    .try_into()
                    .expect("undo median time has fixed width"),
            );
            let coinbase = match bytes[consumed + 8] {
                0 => false,
                1 => true,
                _ => bail!("stored undo coin has an invalid coinbase flag"),
            };
            consumed = metadata_end;
            let (output, output_consumed) = deserialize_partial::<TxOut>(&bytes[consumed..])
                .context("decoding stored block undo output")?;
            consumed = consumed.saturating_add(output_consumed);
            outputs.push(StoredUndo {
                output,
                height,
                median_time_past,
                coinbase,
            });
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
    fn zstd_storage_records_round_trip_and_skip_incompressible_payloads() {
        let payload = vec![0x42; 8 * 1024];
        let encoded = encode_storage_payload(&payload, MAX_STORED_BLOCK_SIZE).unwrap();
        assert!(encoded.starts_with(STORAGE_COMPRESSION_MAGIC));
        assert!(encoded.len() < payload.len());
        assert_eq!(
            decode_storage_payload(&encoded, MAX_STORED_BLOCK_SIZE).unwrap(),
            payload
        );

        let small = vec![0x42; STORAGE_COMPRESSION_MIN_SIZE - 1];
        let raw = encode_storage_payload(&small, MAX_STORED_BLOCK_SIZE).unwrap();
        assert!(!raw.starts_with(STORAGE_COMPRESSION_MAGIC));
        assert_eq!(
            decode_storage_payload(&raw, MAX_STORED_BLOCK_SIZE).unwrap(),
            small
        );
    }

    #[test]
    fn transaction_index_store_round_trips_txids_without_block_bodies() {
        let directory = tempfile::tempdir().unwrap();
        let first_hash = BlockHash::from_byte_array([1u8; 32]);
        let second_hash = BlockHash::from_byte_array([2u8; 32]);
        let first_txids = vec![
            Txid::from_byte_array([3u8; 32]),
            Txid::from_byte_array([4u8; 32]),
        ];
        let second_txids = vec![Txid::from_byte_array([5u8; 32])];
        {
            let mut store = TransactionIndexStore::open(directory.path()).unwrap();
            store.insert(first_hash, &first_txids).unwrap();
            store.insert(second_hash, &second_txids).unwrap();
            assert_eq!(store.len(), 2);
            assert_eq!(store.get(&first_hash).unwrap(), Some(first_txids.clone()));
            assert_eq!(store.get(&second_hash).unwrap(), Some(second_txids.clone()));
        }

        let mut reopened = TransactionIndexStore::open(directory.path()).unwrap();
        assert_eq!(reopened.get(&first_hash).unwrap(), Some(first_txids));
        assert_eq!(reopened.get(&second_hash).unwrap(), Some(second_txids));
        reopened.clear().unwrap();
        assert!(reopened.is_empty());
    }

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
    fn utxo_batches_are_atomic_and_reopen() {
        let directory = tempfile::tempdir().unwrap();
        let first = OutPoint::new(Txid::from_byte_array([1; 32]), 0);
        let second = OutPoint::new(Txid::from_byte_array([2; 32]), 1);
        let entry = |value, height| StoredUtxo {
            output: TxOut {
                value: bitcoin::Amount::from_sat(value),
                script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
            },
            height,
            median_time_past: height.saturating_sub(1),
            coinbase: height == 12,
        };
        let first_entry = entry(50_000, 12);
        let second_entry = entry(40_000, 13);
        let generation = {
            let mut store = UtxoStore::open(directory.path()).unwrap();
            store
                .apply_batch(&[], &[(first, first_entry.clone())])
                .unwrap();
            store
                .apply_batch(&[first], &[(second, second_entry.clone())])
                .unwrap();
            assert!(!store.contains(&first).unwrap());
            assert_eq!(store.get(&second).unwrap(), Some(second_entry.clone()));
            assert_eq!(store.len(), 1);
            store.generation()
        };

        let reopened = UtxoStore::open(directory.path()).unwrap();
        assert_eq!(reopened.generation(), generation);
        assert_eq!(reopened.len(), 1);
        assert_eq!(reopened.get(&first).unwrap(), None);
        assert_eq!(reopened.get(&second).unwrap(), Some(second_entry));
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
        assert!(store.read_cache.lock().entries.contains_key(&outpoint));
        assert_eq!(store.get(&outpoint).unwrap(), Some(first));
        assert_eq!(store.read_cache.lock().entries.len(), 1);

        store
            .apply_batch(&[outpoint], &[(outpoint, second.clone())])
            .unwrap();
        assert!(store.read_cache.lock().entries.contains_key(&outpoint));
        assert_eq!(store.get(&outpoint).unwrap(), Some(second.clone()));
        assert_eq!(store.read_cache.lock().entries.len(), 1);

        store.read_cache.lock().clear();
        assert_eq!(store.warm_cache().unwrap().0, 0);
        assert_eq!(store.get(&outpoint).unwrap(), Some(second));
        assert_eq!(store.warm_cache().unwrap().0, 1);

        store.clear().unwrap();
        assert_eq!(store.get(&outpoint).unwrap(), None);
        assert!(store.read_cache.lock().entries.is_empty());
    }

    #[test]
    fn utxo_compaction_rewrites_live_values_and_reopens() {
        let directory = tempfile::tempdir().unwrap();
        let mut store = UtxoStore::open(directory.path()).unwrap();
        let mut entries = (0..32u32)
            .map(|index| {
                (
                    OutPoint::new(Txid::from_byte_array([index as u8; 32]), index),
                    StoredUtxo {
                        output: TxOut {
                            value: bitcoin::Amount::from_sat(1_000 + u64::from(index)),
                            script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
                        },
                        height: 1,
                        median_time_past: 1,
                        coinbase: false,
                    },
                )
            })
            .collect::<Vec<_>>();
        store.apply_batch(&[], &entries).unwrap();
        for height in 2..=7u32 {
            let removals = entries
                .iter()
                .map(|(outpoint, _)| *outpoint)
                .collect::<Vec<_>>();
            let additions = entries
                .iter()
                .map(|(outpoint, entry)| {
                    (
                        *outpoint,
                        StoredUtxo {
                            height,
                            median_time_past: height,
                            ..entry.clone()
                        },
                    )
                })
                .collect::<Vec<_>>();
            store.apply_batch(&removals, &additions).unwrap();
            entries = additions;
        }
        store.compact().unwrap();
        assert_eq!(store.entries().unwrap(), entries);
        drop(store);

        let reopened = UtxoStore::open(directory.path()).unwrap();
        assert_eq!(reopened.entries().unwrap(), entries);
    }

    #[test]
    fn electrum_history_appends_are_insert_only_and_reopen() {
        let directory = tempfile::tempdir().unwrap();
        let script_hash = hex::encode([31u8; 32]);
        let first = (Txid::from_byte_array([32u8; 32]), 1);
        let second = (Txid::from_byte_array([33u8; 32]), 2);
        let mut store = ElectrumHistoryStore::open(directory.path()).unwrap();
        let initial_size = store.disk_usage().unwrap();

        store
            .append_entries_unsynced(&[(script_hash.clone(), vec![first])])
            .unwrap();
        store
            .append_entries_unsynced(&[(script_hash.clone(), vec![second])])
            .unwrap();
        assert_eq!(store.get(&script_hash).unwrap(), vec![first, second]);
        assert_eq!(store.disk_usage().unwrap(), initial_size);
        assert_eq!(store.len(), 2);

        store.flush().unwrap();
        assert_eq!(store.events.prefix([31u8; 32]).count(), 2);
        drop(store);

        let reopened = ElectrumHistoryStore::open(directory.path()).unwrap();
        assert_eq!(reopened.get(&script_hash).unwrap(), vec![first, second]);
    }

    #[test]
    fn electrum_history_events_append_and_replacements_remove_old_events() {
        let directory = tempfile::tempdir().unwrap();
        let script_hash = hex::encode([41u8; 32]);
        let first = (Txid::from_byte_array([42u8; 32]), 1);
        let second = (Txid::from_byte_array([43u8; 32]), 2);
        let replacement = (Txid::from_byte_array([44u8; 32]), 3);
        let mut store = ElectrumHistoryStore::open(directory.path()).unwrap();

        store
            .append_entries_unsynced(&[(script_hash.clone(), vec![first])])
            .unwrap();
        store.flush().unwrap();
        let after_first = store.disk_usage().unwrap();
        store
            .append_entries_unsynced(&[(script_hash.clone(), vec![second])])
            .unwrap();
        store.flush().unwrap();
        let after_second = store.disk_usage().unwrap();
        assert_eq!(store.get(&script_hash).unwrap(), vec![first, second]);
        assert!(after_second >= after_first);

        store
            .apply_batch(&[(script_hash.clone(), vec![replacement])])
            .unwrap();
        assert_eq!(store.get(&script_hash).unwrap(), vec![replacement]);
        drop(store);

        let reopened = ElectrumHistoryStore::open(directory.path()).unwrap();
        assert_eq!(reopened.get(&script_hash).unwrap(), vec![replacement]);
    }

    #[test]
    fn electrum_history_limited_reads_reject_oversized_values() {
        let directory = tempfile::tempdir().unwrap();
        let script_hash = hex::encode([9u8; 32]);
        let history = (0..128u32)
            .map(|height| (Txid::from_byte_array([height as u8; 32]), height))
            .collect::<Vec<_>>();
        let mut store = ElectrumHistoryStore::open(directory.path()).unwrap();
        store
            .apply_batch(&[(script_hash.clone(), history.clone())])
            .unwrap();

        assert_eq!(
            store.get_limited(&script_hash, history.len()).unwrap(),
            Some(history.clone())
        );
        assert_eq!(
            store.get_limited(&script_hash, history.len() - 1).unwrap(),
            None
        );
        assert_eq!(store.get_limited(&script_hash, 0).unwrap(), None);
    }

    #[test]
    fn electrum_history_batch_reads_existing_and_missing_scripts() {
        let directory = tempfile::tempdir().unwrap();
        let first_script = hex::encode([16u8; 32]);
        let second_script = hex::encode([17u8; 32]);
        let missing_script = hex::encode([18u8; 32]);
        let first_history = vec![(Txid::from_byte_array([19u8; 32]), 20)];
        let second_history = vec![(Txid::from_byte_array([21u8; 32]), 22)];
        let mut store = ElectrumHistoryStore::open(directory.path()).unwrap();
        store
            .apply_batch(&[
                (first_script.clone(), first_history.clone()),
                (second_script.clone(), second_history.clone()),
            ])
            .unwrap();

        let histories = store
            .get_batch(&[
                missing_script.clone(),
                second_script.clone(),
                first_script.clone(),
            ])
            .unwrap();
        assert_eq!(histories.get(&first_script), Some(&first_history));
        assert_eq!(histories.get(&second_script), Some(&second_history));
        assert_eq!(histories.get(&missing_script), Some(&Vec::new()));
    }

    #[test]
    fn electrum_history_replaces_all_values_and_reopens() {
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
    fn electrum_history_compaction_rewrites_live_values_and_reopens() {
        let directory = tempfile::tempdir().unwrap();
        let script_hash = hex::encode([11u8; 32]);
        let mut history = (0..32u32)
            .map(|height| (Txid::from_byte_array([height as u8; 32]), height))
            .collect::<Vec<_>>();
        let mut store = ElectrumHistoryStore::open(directory.path()).unwrap();
        store
            .apply_batch(&[(script_hash.clone(), history.clone())])
            .unwrap();
        for round in 1..=7u32 {
            history = history
                .into_iter()
                .map(|(txid, height)| (txid, height.saturating_add(round)))
                .collect();
            store
                .apply_batch(&[(script_hash.clone(), history.clone())])
                .unwrap();
        }
        store.compact().unwrap();
        assert_eq!(store.get(&script_hash).unwrap(), history);
        drop(store);

        let reopened = ElectrumHistoryStore::open(directory.path()).unwrap();
        assert_eq!(reopened.get(&script_hash).unwrap(), history);
        assert_eq!(reopened.generation(), 9);
    }

    #[test]
    fn electrum_history_compaction_drops_empty_reorg_values() {
        let directory = tempfile::tempdir().unwrap();
        let removed_script = hex::encode([12u8; 32]);
        let live_script = hex::encode([13u8; 32]);
        let removed_txid = Txid::from_byte_array([14u8; 32]);
        let live_txid = Txid::from_byte_array([15u8; 32]);
        let mut store = ElectrumHistoryStore::open(directory.path()).unwrap();
        store
            .apply_batch(&[
                (removed_script.clone(), vec![(removed_txid, 1)]),
                (live_script.clone(), vec![(live_txid, 2)]),
            ])
            .unwrap();
        store
            .apply_batch(&[(removed_script.clone(), Vec::new())])
            .unwrap();
        assert_eq!(store.len(), 1);

        store.compact().unwrap();
        assert_eq!(store.len(), 1);
        assert!(store.get(&removed_script).unwrap().is_empty());
        assert_eq!(store.get(&live_script).unwrap(), vec![(live_txid, 2)]);
        drop(store);

        let reopened = ElectrumHistoryStore::open(directory.path()).unwrap();
        assert_eq!(reopened.len(), 1);
        assert!(!reopened.contains(&removed_script));
        assert_eq!(reopened.get(&live_script).unwrap(), vec![(live_txid, 2)]);
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
    fn batches_electrum_transaction_reads_and_ignores_missing_blocks() {
        let directory = tempfile::tempdir().unwrap();
        let first = genesis_block(Network::Regtest);
        let mut second = first.clone();
        second.header.nonce = 1;
        let first_hash = first.block_hash();
        let second_hash = second.block_hash();
        let missing_hash = BlockHash::from_byte_array([9; 32]);
        let mut store = ElectrumBlockStore::open(directory.path()).unwrap();
        // Insert in the reverse chain order so the batch method has to use
        // record offsets instead of request order.
        store.insert(&second).unwrap();
        store.insert(&first).unwrap();

        let transactions = store
            .transactions_for_blocks(&[first_hash, missing_hash, second_hash, first_hash])
            .unwrap();
        assert_eq!(transactions.len(), 2);
        assert_eq!(
            transactions[&first_hash][0].compute_txid(),
            first.txdata[0].compute_txid()
        );
        assert_eq!(
            transactions[&second_hash][0].compute_txid(),
            second.txdata[0].compute_txid()
        );
        assert!(!transactions.contains_key(&missing_hash));
    }

    #[test]
    fn compacts_electrum_transactions_to_the_pruned_active_set() {
        let directory = tempfile::tempdir().unwrap();
        let first = genesis_block(Network::Regtest);
        let mut second = first.clone();
        second.header.nonce = 1;
        let first_hash = first.block_hash();
        let second_hash = second.block_hash();
        let mut store = ElectrumBlockStore::open(directory.path()).unwrap();
        store.insert(&first).unwrap();
        store.insert(&second).unwrap();
        let before = store.disk_usage().unwrap();

        assert!(store.retain_only(&HashSet::from([first_hash])).unwrap());
        assert!(store.disk_usage().unwrap() < before);
        assert!(store.contains(&first_hash));
        assert!(!store.contains(&second_hash));
        assert!(store.transaction(&first_hash, 0).unwrap().is_some());
        assert!(store.transaction(&second_hash, 0).unwrap().is_none());
    }

    #[test]
    fn recovers_a_stale_electrum_transaction_pointer() {
        let directory = tempfile::tempdir().unwrap();
        let first = genesis_block(Network::Regtest);
        let first_hash = first.block_hash();
        let mut second = first.clone();
        second.header.nonce = 1;
        let second_hash = second.block_hash();
        {
            let mut store = ElectrumBlockStore::open(directory.path()).unwrap();
            store.insert(&first).unwrap();
            store.insert(&second).unwrap();
        }

        let index_path = directory.path().join("txblocks.index");
        let mut index = std::fs::read(&index_path).unwrap();
        let second_offset = (INDEX_HEADER_SIZE + INDEX_RECORD_SIZE + 32) as usize;
        index[second_offset..second_offset + 8].copy_from_slice(&0u64.to_le_bytes());
        std::fs::write(index_path, index).unwrap();

        let mut reopened = ElectrumBlockStore::open(directory.path()).unwrap();
        assert_eq!(
            reopened
                .transaction(&first_hash, 0)
                .unwrap()
                .unwrap()
                .compute_txid(),
            first.txdata[0].compute_txid()
        );
        assert_eq!(
            reopened
                .transaction(&second_hash, 0)
                .unwrap()
                .unwrap()
                .compute_txid(),
            second.txdata[0].compute_txid()
        );
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
    fn native_block_store_does_not_create_core_block_files() {
        let directory = tempfile::tempdir().unwrap();
        let block = genesis_block(Network::Regtest);
        let hash = block.block_hash();

        let mut store = BlockStore::open(directory.path()).unwrap();
        store.insert(&block).unwrap();
        store.insert_undo(hash, &[Vec::new()]).unwrap();
        drop(store);

        for name in ["blk00000.dat", "rev00000.dat"] {
            assert!(
                !directory.path().join(name).exists(),
                "native storage must not create Core file {name}"
            );
        }
        for name in ["blocks.dat", "blocks.index", "undo.dat", "undo.index"] {
            assert!(
                directory.path().join(name).exists(),
                "missing native file {name}"
            );
        }
    }

    #[test]
    fn persists_and_recovers_xored_blocks_and_undo() {
        let directory = tempfile::tempdir().unwrap();
        let block = genesis_block(Network::Regtest);
        let hash = block.block_hash();
        let undo = vec![vec![StoredUndo {
            output: TxOut {
                value: bitcoin::Amount::from_sat(42),
                script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
            },
            height: 7,
            median_time_past: 6,
            coinbase: false,
        }]];
        {
            let mut store = BlockStore::open_with_xor(directory.path(), true).unwrap();
            store.insert(&block).unwrap();
            store.insert_undo(hash, &undo).unwrap();
            assert_eq!(store.get(&hash).unwrap(), Some(block.clone()));
            assert_eq!(store.get_undo(&hash).unwrap(), Some(undo.clone()));
        }
        assert!(!directory.path().join("blk00000.dat").exists());
        assert!(!directory.path().join("rev00000.dat").exists());

        let key = read_xor_key(&directory.path().join("xor.dat")).unwrap();
        assert_eq!(
            std::fs::metadata(directory.path().join("xor.dat"))
                .unwrap()
                .len(),
            XOR_KEY_SIZE as u64
        );
        let mut raw = std::fs::read(directory.path().join("blocks.dat")).unwrap();
        key.apply(&mut raw, 0);
        let payload = encode_storage_payload(&serialize(&block), MAX_STORED_BLOCK_SIZE).unwrap();
        let mut expected = (payload.len() as u32).to_le_bytes().to_vec();
        expected.extend_from_slice(&payload);
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

    #[cfg(unix)]
    #[test]
    fn reindex_reads_read_only_blocks_and_reopens_for_new_writes() {
        use std::os::unix::fs::PermissionsExt;

        let directory = tempfile::tempdir().unwrap();
        let first = genesis_block(Network::Regtest);
        let mut second = first.clone();
        second.header.nonce = 1;
        let mut third = first.clone();
        third.header.nonce = 3;
        assert_ne!(first.block_hash(), second.block_hash());
        assert_ne!(first.block_hash(), third.block_hash());
        assert_ne!(second.block_hash(), third.block_hash());
        {
            let mut store = BlockStore::open(directory.path()).unwrap();
            store.insert(&first).unwrap();
            store.insert(&second).unwrap();
        }

        let block_path = directory.path().join("blocks.dat");
        let mut read_only = std::fs::metadata(&block_path).unwrap().permissions();
        read_only.set_mode(0o444);
        std::fs::set_permissions(&block_path, read_only).unwrap();

        let mut store = BlockStore::open_for_reindex_with_xor(directory.path(), false).unwrap();
        assert!(store.block_file_read_only);
        assert_eq!(store.get(&first.block_hash()).unwrap(), Some(first));
        assert_eq!(store.get(&second.block_hash()).unwrap(), Some(second));

        let writable = std::fs::Permissions::from_mode(0o644);
        std::fs::set_permissions(&block_path, writable).unwrap();
        store.insert(&third).unwrap();
        assert!(!store.block_file_read_only);
        assert_eq!(store.get(&third.block_hash()).unwrap(), Some(third));
    }

    #[cfg(unix)]
    #[test]
    fn reindex_opens_empty_read_only_block_file() {
        use std::os::unix::fs::PermissionsExt;

        let directory = tempfile::tempdir().unwrap();
        let block_path = directory.path().join("blocks.dat");
        std::fs::write(&block_path, []).unwrap();
        let mut read_only = std::fs::metadata(&block_path).unwrap().permissions();
        read_only.set_mode(0o444);
        std::fs::set_permissions(&block_path, read_only).unwrap();

        let mut store = BlockStore::open_for_reindex_with_xor(directory.path(), false).unwrap();
        assert!(store.block_file_read_only);

        std::fs::set_permissions(&block_path, std::fs::Permissions::from_mode(0o644)).unwrap();
        let block = genesis_block(Network::Regtest);
        store.insert(&block).unwrap();
        assert_eq!(store.get(&block.block_hash()).unwrap(), Some(block));
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
            vec![StoredUndo {
                output: TxOut {
                    value: bitcoin::Amount::from_sat(42),
                    script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
                },
                height: 11,
                median_time_past: 10,
                coinbase: true,
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
