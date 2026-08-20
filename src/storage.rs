//! Append-only block storage.
//!
//! Blocks are written as length-prefixed consensus-encoded records. The
//! in-memory hash index makes reads O(1). A durable location index avoids
//! decoding the append-only file on normal restarts; truncated, stale, or
//! corrupt index files fall back to a complete record scan.

use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::{File, OpenOptions, create_dir_all, remove_file, rename};
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
use parking_lot::{Mutex, RwLock};
use rand::random;
use serde::{Deserialize, Serialize};

const MAX_STORED_BLOCK_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_UNDO_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_FILTER_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_CHAINSTATE_DELTA_SIZE: usize = 64 * 1024 * 1024;
const MAX_STORED_ELECTRUM_BLOCK_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_ELECTRUM_HISTORY_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_TRANSACTION_INDEX_SIZE: usize = 8 * 1024 * 1024;
const MAX_STORED_UTXO_SIZE: usize = 100 * 1024;
const MIN_UTXO_COMPACTION_DATA_SIZE: u64 = 16 * 1024 * 1024;
const MIN_UTXO_COMPACTION_STALE_SIZE: u64 = 8 * 1024 * 1024;
const MIN_ELECTRUM_HISTORY_COMPACTION_DATA_SIZE: u64 = 16 * 1024 * 1024;
const MIN_ELECTRUM_HISTORY_COMPACTION_STALE_SIZE: u64 = 8 * 1024 * 1024;
const XOR_KEY_SIZE: usize = 8;
const STORAGE_COMPRESSION_MAGIC: &[u8] = b"bitcoind-rs-zstd-v1\0";
const STORAGE_COMPRESSION_HEADER_SIZE: usize = STORAGE_COMPRESSION_MAGIC.len() + 4;
const STORAGE_COMPRESSION_LEVEL: i32 = 6;
const STORAGE_COMPRESSION_MIN_SIZE: usize = 256;
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

/// Compact in-memory pointer into the append-only UTXO value log.
///
/// A normal UTXO record is below 100 KiB, so 17 bits are sufficient for its
/// encoded length.  The remaining 47 bits address a value log up to 128 TiB.
/// Keeping the pointer in one word matters at mainnet scale: the UTXO index
/// has one entry per live outpoint, and the pointer is present in every hash
/// table value.  The on-disk index format remains the existing u64 offset +
/// u32 length encoding.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct UtxoLocation(u64);

impl UtxoLocation {
    const LENGTH_BITS: u32 = 17;
    const LENGTH_MASK: u64 = (1 << Self::LENGTH_BITS) - 1;
    const MAX_OFFSET: u64 = (1 << (u64::BITS - Self::LENGTH_BITS)) - 1;

    fn new(offset: u64, length: u32) -> Result<Self> {
        if length == 0 || u64::from(length) > Self::LENGTH_MASK {
            bail!("UTXO record length does not fit compact location: {length}");
        }
        if offset > Self::MAX_OFFSET {
            bail!("UTXO record offset does not fit compact location: {offset}");
        }
        Ok(Self((offset << Self::LENGTH_BITS) | u64::from(length)))
    }

    #[inline]
    fn offset(self) -> u64 {
        self.0 >> Self::LENGTH_BITS
    }

    #[inline]
    fn length(self) -> u32 {
        (self.0 & Self::LENGTH_MASK) as u32
    }
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

/// Compact in-memory pointer into the append-only Electrum history log.
///
/// History records are capped at 4 MiB.  Storing `length - 1` in 22 bits
/// represents that full range, leaving 42 bits for a history log up to 4 TiB.
/// The durable history index deliberately keeps its existing u64 offset and
/// u32 length fields, so this optimization only changes resident memory.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct HistoryLocation(u64);

impl HistoryLocation {
    const LENGTH_BITS: u32 = 22;
    const LENGTH_MASK: u64 = (1 << Self::LENGTH_BITS) - 1;
    const MAX_LENGTH: u32 = (Self::LENGTH_MASK + 1) as u32;
    const MAX_OFFSET: u64 = (1 << (u64::BITS - Self::LENGTH_BITS)) - 1;

    fn new(offset: u64, length: u32) -> Result<Self> {
        if length == 0 || length > Self::MAX_LENGTH {
            bail!("Electrum history record length does not fit compact location: {length}");
        }
        if offset > Self::MAX_OFFSET {
            bail!("Electrum history record offset does not fit compact location: {offset}");
        }
        Ok(Self((offset << Self::LENGTH_BITS) | u64::from(length - 1)))
    }

    #[inline]
    fn offset(self) -> u64 {
        self.0 >> Self::LENGTH_BITS
    }

    #[inline]
    fn length(self) -> u32 {
        ((self.0 & Self::LENGTH_MASK) + 1) as u32
    }
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

/// Encode one authoritative append-only payload with the storage codec.
///
/// The outer record framing remains four-byte-length-prefixed so indexes can
/// still address records directly.  Compression is therefore applied before
/// XOR obfuscation and independently for each record, which preserves random
/// reads and makes a torn tail recoverable without a global decompression
/// stream.  Small or incompressible values stay raw; the decoder accepts both
/// forms so existing stores upgrade in place as new records are appended.
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
        self.ensure_block_file_writable()?;
        let raw_bytes = serialize(block);
        let bytes = encode_storage_payload(&raw_bytes, MAX_STORED_BLOCK_SIZE)?;
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
        self.cache_block(hash, block.clone(), raw_bytes.len());
        Ok(hash)
    }

    pub fn flush(&mut self) -> Result<()> {
        self.file.sync_data()?;
        self.index_file.sync_data()?;
        self.undo_file.sync_data()?;
        self.undo_index_file.sync_data()?;
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

    pub fn get_undo(&mut self, hash: &BlockHash) -> Result<Option<Vec<Vec<TxOut>>>> {
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

    pub fn insert_undo(&mut self, hash: BlockHash, undo: &[Vec<TxOut>]) -> Result<()> {
        self.insert_undo_with_sync(hash, undo, true)
    }

    /// Append undo data without forcing a filesystem sync for every record.
    /// Chain activation writes a complete candidate suffix as one batch and
    /// flushes the store after the new active state is durable.
    pub fn insert_undo_unsynced(&mut self, hash: BlockHash, undo: &[Vec<TxOut>]) -> Result<()> {
        self.insert_undo_with_sync(hash, undo, false)
    }

    fn insert_undo_with_sync(
        &mut self,
        hash: BlockHash,
        undo: &[Vec<TxOut>],
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

        let mut records = Vec::with_capacity(pending.len());
        for (hash, bytes, offset, length) in pending {
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

/// Durable transaction-ID lists keyed by block hash.
///
/// The optional Core-style txindex needs a transaction location for every
/// stored block, but it does not need to duplicate transaction bodies. Keeping
/// only the txids in a separate native sidecar lets a normal restart rebuild
/// the in-memory location map without decoding every block record. The block
/// store remains authoritative for the transaction bytes.
pub struct TransactionIndexStore {
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

    pub fn flush(&mut self) -> Result<()> {
        self.flush_pending_writes()?;
        self.index_file.sync_data()?;
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
        if self.index.contains_key(&hash) {
            return Ok(());
        }
        if payload.len() > MAX_STORED_CHAINSTATE_DELTA_SIZE {
            bail!("chainstate delta is too large: {} bytes", payload.len());
        }
        let encoded_payload = encode_storage_payload(payload, MAX_STORED_CHAINSTATE_DELTA_SIZE)?;
        let length = 32usize
            .checked_add(encoded_payload.len())
            .context("chainstate delta length overflow")?;
        let length = u32::try_from(length).context("chainstate delta length does not fit u32")?;
        let offset = self.file.seek(SeekFrom::End(0))?;
        self.file.write_all(&length.to_le_bytes())?;
        self.file.write_all(&hash.to_byte_array())?;
        self.file.write_all(&encoded_payload)?;
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
    recovery_marker_path: PathBuf,
    recovery_attempt_path: PathBuf,
    index_path: PathBuf,
    file: File,
    index_file: File,
    index: HashMap<OutPoint, UtxoLocation>,
    next_batch_id: u64,
    generation: u64,
    pending_write_bytes: usize,
    crash_ratio: Option<u64>,
    read_cache: Mutex<UtxoReadCache>,
}

impl UtxoStore {
    pub fn open(directory: impl AsRef<Path>) -> Result<Self> {
        let directory = directory.as_ref();
        create_dir_all(directory)
            .with_context(|| format!("creating UTXO store {}", directory.display()))?;
        let path = directory.join("utxos.dat");
        let recovery_marker_path = directory.join("utxos.recovery.pending");
        let recovery_attempt_path = directory.join("utxos.recovery.attempted");
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
        let loaded_index = load_utxo_index(&mut index_file, &file, data_len)?;
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
            recovery_marker_path,
            recovery_attempt_path,
            index_path,
            file,
            index_file,
            index,
            next_batch_id,
            generation,
            pending_write_bytes: 0,
            crash_ratio: None,
            read_cache: Mutex::new(UtxoReadCache::default()),
        })
    }

    /// Configure Core's debug-only crash-injection hook.
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

    /// Reproduce the restart-time part of Core's interrupted coins flush.
    /// The first startup after an injected write crash exits once; the next
    /// startup consumes the attempted marker and proceeds with the durable
    /// state.
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
        locations.sort_unstable_by_key(|(_, location)| location.offset());
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
                    .saturating_add(4usize.saturating_add(location.length() as usize));
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
                    .saturating_add(4usize.saturating_add(location.length() as usize));
            }
            let commit = encode_utxo_commit(batch_id);
            let commit_location = append_utxo_data_record(&mut self.file, &commit)?;
            self.pending_write_bytes = self
                .pending_write_bytes
                .saturating_add(4usize.saturating_add(commit_location.length() as usize));
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

    /// Rewrite the live UTXO set into a compact value log and atomically
    /// replace the location index.  The data and index are written and synced
    /// before either rename, so an interrupted compaction is recovered by the
    /// normal index rebuild path on the next open.
    pub fn compact(&mut self) -> Result<()> {
        self.flush()?;
        let mut locations = self
            .index
            .iter()
            .map(|(outpoint, location)| (*outpoint, *location))
            .collect::<Vec<_>>();
        locations.sort_unstable_by_key(|(_, location)| location.offset());
        let compact_data_path = self.path.with_extension("dat.compact");
        let compact_index_path = self.index_path.with_extension("index.compact");
        for path in [&compact_data_path, &compact_index_path] {
            match remove_file(path) {
                Ok(()) => {}
                Err(error) if error.kind() == ErrorKind::NotFound => {}
                Err(error) => return Err(error.into()),
            }
        }

        let result = (|| -> Result<()> {
            let mut compact_data = OpenOptions::new()
                .create_new(true)
                .read(true)
                .write(true)
                .open(&compact_data_path)
                .with_context(|| {
                    format!(
                        "creating compacted UTXO store {}",
                        compact_data_path.display()
                    )
                })?;
            compact_data.write_all(UTXO_DATA_MAGIC)?;
            let batch_id = self.next_batch_id;
            let next_batch_id = batch_id
                .checked_add(1)
                .context("UTXO batch identifier exhausted during compaction")?;
            let entries_empty = locations.is_empty();
            let mut compact_index = HashMap::with_capacity(locations.len());
            if !entries_empty {
                for (outpoint, location) in &locations {
                    let body = read_utxo_data_record(&self.file, *location)?;
                    if body.first().copied() != Some(UTXO_PUT) || body.len() < 1 + 8 + 36 {
                        bail!("UTXO location points to a non-value record");
                    }
                    let stored_outpoint = decode_outpoint(&body[9..45])?;
                    if stored_outpoint != *outpoint {
                        bail!("UTXO value key does not match its index");
                    }
                    let entry = decode_stored_utxo(&body[45..])?;
                    let body = encode_utxo_put(batch_id, outpoint, &entry)?;
                    let location = append_utxo_data_record(&mut compact_data, &body)?;
                    compact_index.insert(*outpoint, location);
                }
                let commit = encode_utxo_commit(batch_id);
                append_utxo_data_record(&mut compact_data, &commit)?;
            }
            compact_data.sync_data()?;
            let data_end = data_len_after(&compact_data)?;

            let mut compact_index_file = OpenOptions::new()
                .create_new(true)
                .read(true)
                .write(true)
                .open(&compact_index_path)
                .with_context(|| {
                    format!(
                        "creating compacted UTXO index {}",
                        compact_index_path.display()
                    )
                })?;
            rewrite_utxo_index(
                &mut compact_index_file,
                data_end,
                if entries_empty {
                    self.next_batch_id
                } else {
                    next_batch_id
                },
                self.generation,
                &compact_index,
            )?;
            drop(compact_index_file);
            drop(compact_data);

            rename(&compact_data_path, &self.path).with_context(|| {
                format!("installing compacted UTXO store {}", self.path.display())
            })?;
            rename(&compact_index_path, &self.index_path).with_context(|| {
                format!(
                    "installing compacted UTXO index {}",
                    self.index_path.display()
                )
            })?;

            self.file = OpenOptions::new()
                .read(true)
                .append(true)
                .open(&self.path)
                .with_context(|| {
                    format!("reopening compacted UTXO store {}", self.path.display())
                })?;
            self.index_file = OpenOptions::new()
                .read(true)
                .append(true)
                .open(&self.index_path)
                .with_context(|| {
                    format!(
                        "reopening compacted UTXO index {}",
                        self.index_path.display()
                    )
                })?;
            self.index = compact_index;
            self.next_batch_id = if entries_empty {
                self.next_batch_id
            } else {
                next_batch_id
            };
            self.pending_write_bytes = 0;
            Ok(())
        })();
        if result.is_err() {
            let _ = remove_file(&compact_data_path);
            let _ = remove_file(&compact_index_path);
        }
        result
    }

    /// Compact only when stale mutation records are large enough to justify a
    /// full live-set rewrite.  Snapshot boundaries call this method so normal
    /// operation gets LevelDB-like reclamation without a rewrite per block.
    pub fn compact_if_needed(&mut self) -> Result<bool> {
        let data_len = data_len_after(&self.file)?;
        if data_len < MIN_UTXO_COMPACTION_DATA_SIZE {
            return Ok(false);
        }
        let live_bytes = UTXO_DATA_MAGIC.len() as u64
            + self
                .index
                .values()
                .map(|location| 4u64.saturating_add(u64::from(location.length())))
                .sum::<u64>()
            + if self.index.is_empty() { 0 } else { 13 };
        let stale_bytes = data_len.saturating_sub(live_bytes);
        if stale_bytes < MIN_UTXO_COMPACTION_STALE_SIZE || stale_bytes < live_bytes / 4 {
            return Ok(false);
        }
        self.compact()?;
        Ok(true)
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
        let loaded_index = load_history_index(&mut index_file, &file, data_len)?;
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

    /// Read one script history while refusing to allocate more than `limit`
    /// entries. The normal full-history reader remains available for chain
    /// rebuilds, but bounded Electrum requests should reject an oversized
    /// history before copying it into a temporary vector.
    pub fn get_limited(&self, script_hash: &str, limit: usize) -> Result<Option<Vec<(Txid, u32)>>> {
        let script_hash = encode_history_script_hash(script_hash)?;
        let Some(location) = self.index.get(&script_hash).copied() else {
            return Ok(Some(Vec::new()));
        };
        let body = read_history_data_record(&self.file, location)?;
        decode_history_value_limited(&body, script_hash, limit)
    }

    /// Read several script histories in data-file order. Reorgs commonly
    /// touch thousands of scripts whose latest values were appended close
    /// together; sorting by record offset turns that workload into a mostly
    /// sequential scan instead of issuing one random seek per script.
    pub fn get_batch(&self, script_hashes: &[String]) -> Result<HashMap<String, Vec<(Txid, u32)>>> {
        let mut requests = script_hashes
            .iter()
            .map(|script_hash| {
                let encoded = encode_history_script_hash(script_hash)?;
                Ok((
                    script_hash.clone(),
                    encoded,
                    self.index.get(&encoded).copied(),
                ))
            })
            .collect::<Result<Vec<_>>>()?;
        requests.sort_unstable_by_key(|(_, _, location)| {
            location.map_or(u64::MAX, HistoryLocation::offset)
        });

        let mut histories = HashMap::with_capacity(requests.len());
        for (script_hash, encoded, location) in requests {
            let entries = match location {
                Some(location) => {
                    let body = read_history_data_record(&self.file, location)?;
                    decode_history_value(&body, encoded)?
                }
                None => Vec::new(),
            };
            histories.insert(script_hash, entries);
        }
        Ok(histories)
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
        locations.sort_unstable_by_key(|(_, location)| location.offset());
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

    /// Rewrite the latest history value for every script into a compact data
    /// log and atomically replace the location index.  Both replacement files
    /// are synced before installation; an interrupted two-file replacement is
    /// detected by the index/data consistency checks during the next open.
    pub fn compact(&mut self) -> Result<()> {
        self.flush()?;
        let mut locations = self
            .index
            .iter()
            .map(|(script_hash, location)| (*script_hash, *location))
            .collect::<Vec<_>>();
        locations.sort_unstable_by_key(|(_, location)| location.offset());
        let compact_data_path = self.path.with_extension("dat.compact");
        let compact_index_path = self.index_path.with_extension("index.compact");
        for path in [&compact_data_path, &compact_index_path] {
            match remove_file(path) {
                Ok(()) => {}
                Err(error) if error.kind() == ErrorKind::NotFound => {}
                Err(error) => return Err(error.into()),
            }
        }

        let result = (|| -> Result<()> {
            let mut compact_data = OpenOptions::new()
                .create_new(true)
                .read(true)
                .write(true)
                .open(&compact_data_path)
                .with_context(|| {
                    format!(
                        "creating compacted Electrum history store {}",
                        compact_data_path.display()
                    )
                })?;
            compact_data.write_all(ELECTRUM_HISTORY_DATA_MAGIC)?;
            let batch_id = self.next_batch_id;
            let next_batch_id = batch_id
                .checked_add(1)
                .context("Electrum history batch identifier exhausted during compaction")?;
            let mut compact_index = HashMap::with_capacity(locations.len());
            let mut copied_entries = 0usize;
            for (script_hash_bytes, location) in &locations {
                let body = read_history_data_record(&self.file, *location)?;
                let history = decode_history_value(&body, *script_hash_bytes)?;
                if history.is_empty() {
                    // Reorg deltas may leave an empty replacement value for a
                    // script that no longer has any active-chain history.
                    // Keep the append-only log readable, but do not carry a
                    // phantom key into the compacted index.
                    continue;
                }
                let body = encode_history_value(batch_id, *script_hash_bytes, &history)?;
                let location = append_history_data_record(&mut compact_data, &body)?;
                compact_index.insert(*script_hash_bytes, location);
                copied_entries = copied_entries.saturating_add(1);
            }
            if copied_entries != 0 {
                let commit = encode_history_commit(batch_id);
                append_history_data_record(&mut compact_data, &commit)?;
            }
            compact_data.sync_data()?;
            let data_end = data_len_after(&compact_data)?;

            let mut compact_index_file = OpenOptions::new()
                .create_new(true)
                .read(true)
                .write(true)
                .open(&compact_index_path)
                .with_context(|| {
                    format!(
                        "creating compacted Electrum history index {}",
                        compact_index_path.display()
                    )
                })?;
            rewrite_history_index(
                &mut compact_index_file,
                data_end,
                if copied_entries == 0 {
                    self.next_batch_id
                } else {
                    next_batch_id
                },
                &compact_index,
            )?;
            drop(compact_index_file);
            drop(compact_data);

            rename(&compact_data_path, &self.path).with_context(|| {
                format!(
                    "installing compacted Electrum history store {}",
                    self.path.display()
                )
            })?;
            rename(&compact_index_path, &self.index_path).with_context(|| {
                format!(
                    "installing compacted Electrum history index {}",
                    self.index_path.display()
                )
            })?;

            self.file = OpenOptions::new()
                .read(true)
                .append(true)
                .open(&self.path)
                .with_context(|| {
                    format!(
                        "reopening compacted Electrum history store {}",
                        self.path.display()
                    )
                })?;
            self.index_file = OpenOptions::new()
                .read(true)
                .append(true)
                .open(&self.index_path)
                .with_context(|| {
                    format!(
                        "reopening compacted Electrum history index {}",
                        self.index_path.display()
                    )
                })?;
            self.index = compact_index;
            self.next_batch_id = if copied_entries == 0 {
                self.next_batch_id
            } else {
                next_batch_id
            };
            Ok(())
        })();
        if result.is_err() {
            let _ = remove_file(&compact_data_path);
            let _ = remove_file(&compact_index_path);
        }
        result
    }

    /// Compact only when enough historical replacement data is dead to make a
    /// full rewrite worthwhile.  Chainstate snapshots invoke this hook so
    /// long-running Electrum nodes reclaim old script-history versions.
    pub fn compact_if_needed(&mut self) -> Result<bool> {
        let data_len = data_len_after(&self.file)?;
        if data_len < MIN_ELECTRUM_HISTORY_COMPACTION_DATA_SIZE {
            return Ok(false);
        }
        let live_bytes = ELECTRUM_HISTORY_DATA_MAGIC.len() as u64
            + self
                .index
                .values()
                .map(|location| 4u64.saturating_add(u64::from(location.length())))
                .sum::<u64>()
            + if self.index.is_empty() { 0 } else { 13 };
        let stale_bytes = data_len.saturating_sub(live_bytes);
        if stale_bytes < MIN_ELECTRUM_HISTORY_COMPACTION_STALE_SIZE || stale_bytes < live_bytes / 4
        {
            return Ok(false);
        }
        self.compact()?;
        Ok(true)
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
    let encoded_body = encode_storage_payload(body, MAX_STORED_ELECTRUM_HISTORY_SIZE)?;
    let offset = data_len_after(file)?;
    let length =
        u32::try_from(encoded_body.len()).context("Electrum history record is too large")?;
    file.write_all(&length.to_le_bytes())?;
    file.write_all(&encoded_body)?;
    HistoryLocation::new(offset, length)
}

fn read_history_data_record(file: &File, location: HistoryLocation) -> Result<Vec<u8>> {
    read_storage_record(
        file,
        Record {
            offset: location.offset(),
            length: location.length(),
        },
        XorKey::default(),
        MAX_STORED_ELECTRUM_HISTORY_SIZE,
        "Electrum history",
    )
}

fn decode_history_value(body: &[u8], expected_script_hash: [u8; 32]) -> Result<Vec<(Txid, u32)>> {
    decode_history_value_limited(body, expected_script_hash, usize::MAX)
        .map(|entries| entries.expect("unlimited history limit cannot be exceeded"))
}

fn decode_history_value_limited(
    body: &[u8],
    expected_script_hash: [u8; 32],
    limit: usize,
) -> Result<Option<Vec<(Txid, u32)>>> {
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
    if count > limit {
        return Ok(None);
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
    Ok(Some(entries))
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
        let body = decode_storage_payload(&body, MAX_STORED_ELECTRUM_HISTORY_SIZE)
            .context("decoding compressed Electrum history record")?;
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
                    location: HistoryLocation::new(record_start, length)?,
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

fn load_history_index(
    file: &mut File,
    data_file: &File,
    data_len: u64,
) -> Result<Option<HistoryIndexState>> {
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
                let Ok(location) = HistoryLocation::new(offset, value_length) else {
                    return Ok(None);
                };
                pending.push(PendingHistoryOperation {
                    script_hash,
                    location,
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
    for (script_hash, location) in &index {
        if validate_history_data_header(data_file, *location, *script_hash).is_err() {
            return Ok(None);
        }
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

fn validate_history_data_header(
    file: &File,
    location: HistoryLocation,
    expected_script_hash: [u8; 32],
) -> Result<()> {
    let body = read_history_data_record(file, location)?;
    if body.len() < 1 + 8 + 32 + 4 || body[0] != HISTORY_PUT {
        bail!("Electrum history index points to a non-value record");
    }
    if body[9..41] != expected_script_hash {
        bail!("Electrum history value key does not match its index");
    }
    let count = usize::try_from(u32::from_le_bytes(
        body[41..45]
            .try_into()
            .expect("Electrum history count has fixed width"),
    ))
    .context("Electrum history count does not fit usize")?;
    let expected_length = 45usize
        .checked_add(
            count
                .checked_mul(36)
                .context("Electrum history count overflowed")?,
        )
        .context("Electrum history value length overflowed")?;
    if expected_length != body.len() {
        bail!("Electrum history count does not match value length");
    }
    Ok(())
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
        append_history_index_operation(file, batch_id, operation)?;
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

fn append_history_index_operation(
    file: &mut File,
    batch_id: u64,
    operation: &PendingHistoryOperation,
) -> Result<()> {
    let mut body = Vec::with_capacity(64);
    body.push(HISTORY_PUT);
    body.extend_from_slice(&batch_id.to_le_bytes());
    body.extend_from_slice(&operation.location.offset().to_le_bytes());
    body.extend_from_slice(&operation.location.length().to_le_bytes());
    body.extend_from_slice(&operation.script_hash);
    let length = u32::try_from(body.len()).context("Electrum history index record too large")?;
    file.write_all(&length.to_le_bytes())?;
    file.write_all(&body)?;
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
    for (script_hash, location) in index {
        append_history_index_operation(
            file,
            0,
            &PendingHistoryOperation {
                script_hash: *script_hash,
                location: *location,
            },
        )?;
    }
    let mut commit = Vec::with_capacity(25);
    commit.push(HISTORY_COMMIT);
    commit.extend_from_slice(&0u64.to_le_bytes());
    commit.extend_from_slice(&data_end.to_le_bytes());
    commit.extend_from_slice(&next_batch_id.to_le_bytes());
    file.write_all(&(u32::try_from(commit.len()).unwrap()).to_le_bytes())?;
    file.write_all(&commit)?;
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
    let encoded_body = encode_storage_payload(body, MAX_STORED_UTXO_SIZE + 64)?;
    let offset = data_len_after(file)?;
    let length =
        u32::try_from(encoded_body.len()).context("UTXO log record length does not fit u32")?;
    let location = UtxoLocation::new(offset, length)?;
    file.write_all(&length.to_le_bytes())?;
    file.write_all(&encoded_body)?;
    Ok(location)
}

fn read_utxo_data_record(file: &File, location: UtxoLocation) -> Result<Vec<u8>> {
    read_storage_record(
        file,
        Record {
            offset: location.offset(),
            length: location.length(),
        },
        XorKey::default(),
        MAX_STORED_UTXO_SIZE + 64,
        "UTXO",
    )
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
        let body = decode_storage_payload(&body, MAX_STORED_UTXO_SIZE + 64)
            .context("decoding compressed UTXO log record")?;
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
                let location = UtxoLocation::new(record_start, length)?;
                if pending_batch != Some(batch_id) {
                    if pending_batch.is_some() {
                        bail!("UTXO log contains interleaved mutation batches");
                    }
                    pending_batch = Some(batch_id);
                }
                pending.push(PendingUtxoOperation::Put { outpoint, location });
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

fn load_utxo_index(
    file: &mut File,
    data_file: &File,
    data_len: u64,
) -> Result<Option<UtxoIndexState>> {
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
                let Ok(location) = UtxoLocation::new(offset, value_length) else {
                    return Ok(None);
                };
                pending.push(PendingUtxoOperation::Put { outpoint, location });
                if validate_utxo_data_header(data_file, location, outpoint).is_err() {
                    return Ok(None);
                }
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

fn validate_utxo_data_header(
    file: &File,
    location: UtxoLocation,
    expected_outpoint: OutPoint,
) -> Result<()> {
    let body = read_utxo_data_record(file, location)?;
    if body.len() < 1 + 8 + 36 + 13 || body[0] != UTXO_PUT {
        bail!("UTXO index points to a non-value record");
    }
    if u64::from_le_bytes(body[1..9].try_into().expect("UTXO batch has fixed width")) == 0 {
        bail!("UTXO value batch identifier is invalid");
    }
    if decode_outpoint(&body[9..45])? != expected_outpoint {
        bail!("UTXO value key does not match its index");
    }
    decode_stored_utxo(&body[45..])?;
    Ok(())
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
        append_utxo_index_operation(file, batch_id, operation)?;
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

fn append_utxo_index_operation(
    file: &mut File,
    batch_id: u64,
    operation: &PendingUtxoOperation,
) -> Result<()> {
    let mut body = Vec::with_capacity(64);
    match operation {
        PendingUtxoOperation::Put { outpoint, location } => {
            body.push(UTXO_PUT);
            body.extend_from_slice(&batch_id.to_le_bytes());
            body.extend_from_slice(&location.offset().to_le_bytes());
            body.extend_from_slice(&location.length().to_le_bytes());
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
    for (outpoint, location) in index {
        append_utxo_index_operation(
            file,
            checkpoint_batch,
            &PendingUtxoOperation::Put {
                outpoint: *outpoint,
                location: *location,
            },
        )?;
    }
    let mut commit = Vec::with_capacity(33);
    commit.push(UTXO_COMMIT);
    commit.extend_from_slice(&checkpoint_batch.to_le_bytes());
    commit.extend_from_slice(&data_end.to_le_bytes());
    commit.extend_from_slice(&next_batch_id.to_le_bytes());
    commit.extend_from_slice(&generation.to_le_bytes());
    file.write_all(&(u32::try_from(commit.len()).unwrap()).to_le_bytes())?;
    file.write_all(&commit)?;
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
        let raw_bytes = serde_json::to_vec(record).context("encoding coinstats record")?;
        let bytes = encode_storage_payload(&raw_bytes, MAX_STORED_COINSTATS_SIZE)?;
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
}

impl TransactionIndexStore {
    pub fn open(directory: impl AsRef<Path>) -> Result<Self> {
        let directory = directory.as_ref();
        create_dir_all(directory).with_context(|| {
            format!(
                "creating transaction index directory {}",
                directory.display()
            )
        })?;
        let path = directory.join("txindex.dat");
        let mut file = OpenOptions::new()
            .create(true)
            .read(true)
            .append(true)
            .open(&path)
            .with_context(|| format!("opening transaction index store {}", path.display()))?;
        let index_path = directory.join("txindex.index");
        let mut index_file = OpenOptions::new()
            .create(true)
            .truncate(false)
            .read(true)
            .write(true)
            .open(&index_path)
            .with_context(|| format!("opening transaction index {}", index_path.display()))?;
        let data_len = file.metadata()?.len();
        let index = match load_index_with_limit(
            &mut index_file,
            data_len,
            MAX_STORED_TRANSACTION_INDEX_SIZE,
        )? {
            Some(index) => index,
            None => {
                let index = scan_transaction_index(&mut file)?;
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

    pub fn len(&self) -> usize {
        self.index.len()
    }

    pub fn is_empty(&self) -> bool {
        self.index.is_empty()
    }

    pub fn contains(&self, hash: &BlockHash) -> bool {
        self.index.contains_key(hash)
    }

    pub fn hashes(&self) -> impl Iterator<Item = &BlockHash> {
        self.index.keys()
    }

    pub fn disk_usage(&self) -> Result<u64> {
        self.file
            .metadata()?
            .len()
            .checked_add(self.index_file.metadata()?.len())
            .context("transaction index store size overflowed")
    }

    pub fn get(&mut self, hash: &BlockHash) -> Result<Option<Vec<Txid>>> {
        let Some(record) = self.index.get(hash).copied() else {
            return Ok(None);
        };
        let bytes = read_storage_record(
            &self.file,
            record,
            XorKey::default(),
            MAX_STORED_TRANSACTION_INDEX_SIZE,
            "transaction index",
        )?;
        let (stored_hash, txids) = decode_transaction_index_value(&bytes)?;
        if stored_hash != *hash {
            bail!("stored transaction index hash does not match its index");
        }
        Ok(Some(txids))
    }

    pub fn insert(&mut self, hash: BlockHash, txids: &[Txid]) -> Result<()> {
        self.insert_with_sync(hash, txids, true)
    }

    /// Append a transaction-ID record without forcing a filesystem sync.
    /// Block relay batches side-chain bodies this way; the owning chainstate
    /// flushes the sidecar when the corresponding block store is flushed.
    pub fn insert_unsynced(&mut self, hash: BlockHash, txids: &[Txid]) -> Result<()> {
        self.insert_with_sync(hash, txids, false)
    }

    fn insert_with_sync(&mut self, hash: BlockHash, txids: &[Txid], sync: bool) -> Result<()> {
        if self.index.contains_key(&hash) {
            return Ok(());
        }
        let count = u32::try_from(txids.len()).context("transaction index count is too large")?;
        let txid_bytes = txids
            .len()
            .checked_mul(32)
            .context("transaction index size overflowed")?;
        let raw_len = 32usize
            .checked_add(4)
            .and_then(|len| len.checked_add(txid_bytes))
            .context("transaction index size overflowed")?;
        let mut raw = Vec::with_capacity(raw_len);
        raw.extend_from_slice(&hash.to_byte_array());
        raw.extend_from_slice(&count.to_le_bytes());
        for txid in txids {
            raw.extend_from_slice(&txid.to_byte_array());
        }
        let bytes = encode_storage_payload(&raw, MAX_STORED_TRANSACTION_INDEX_SIZE)?;
        let offset = self.file.seek(SeekFrom::End(0))?;
        let length = u32::try_from(bytes.len()).context("transaction index record is too large")?;
        self.file.write_all(&length.to_le_bytes())?;
        self.file.write_all(&bytes)?;
        let record = Record { offset, length };
        if sync {
            self.file.sync_data()?;
        }
        persist_index_entry_with_sync(
            &mut self.index_file,
            offset + 4 + bytes.len() as u64,
            hash,
            record,
            sync,
        )?;
        self.index.insert(hash, record);
        Ok(())
    }

    pub fn flush(&mut self) -> Result<()> {
        self.file.sync_data()?;
        self.index_file.sync_data()?;
        Ok(())
    }

    /// Remove all sidecar records before a full txindex rebuild.
    pub fn clear(&mut self) -> Result<()> {
        self.file.set_len(0)?;
        self.file.seek(SeekFrom::End(0))?;
        self.file.sync_data()?;
        self.index.clear();
        rewrite_index(&mut self.index_file, 0, &self.index)
    }
}

impl Drop for TransactionIndexStore {
    fn drop(&mut self) {
        let _ = self.flush();
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
        self.file.write_all(&length.to_le_bytes())?;
        self.file.write_all(&bytes)?;
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
        self.index_file.sync_data()?;
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

    /// Read every transaction for a pruned active-chain block.  Chainstate
    /// uses this compact sidecar not only for Electrum transaction serving,
    /// but also to rebuild the confirmed-spender index after a restart.
    pub(crate) fn transactions_for_block(
        &mut self,
        block_hash: &BlockHash,
    ) -> Result<Option<Vec<Transaction>>> {
        self.transactions(block_hash)
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

fn decode_transaction_index_value(bytes: &[u8]) -> Result<(BlockHash, Vec<Txid>)> {
    if bytes.len() < 32 + 4 {
        bail!("transaction index record is truncated");
    }
    let hash = BlockHash::from_byte_array(
        bytes[..32]
            .try_into()
            .expect("transaction index block hash has fixed width"),
    );
    let count = usize::try_from(u32::from_le_bytes(
        bytes[32..36]
            .try_into()
            .expect("transaction index count has fixed width"),
    ))
    .context("transaction index count does not fit usize")?;
    let txid_bytes = count
        .checked_mul(32)
        .context("transaction index count overflows its record")?;
    let expected_len = 36usize
        .checked_add(txid_bytes)
        .context("transaction index record length overflowed")?;
    if expected_len != bytes.len() {
        bail!("transaction index count does not match record length");
    }
    let mut txids = Vec::with_capacity(count);
    for chunk in bytes[36..].chunks_exact(32) {
        txids.push(Txid::from_byte_array(
            chunk
                .try_into()
                .expect("transaction index txid has fixed width"),
        ));
    }
    Ok((hash, txids))
}

fn scan_transaction_index(file: &mut File) -> Result<HashMap<BlockHash, Record>> {
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
        if length == 0 || length as usize > MAX_STORED_TRANSACTION_INDEX_SIZE {
            bail!(
                "invalid transaction index record length {} at offset {}",
                length,
                offset
            );
        }
        let mut encoded = vec![0u8; length as usize];
        file.read_exact(&mut encoded).map_err(|error| {
            anyhow::anyhow!(
                "truncated transaction index record at offset {}: {}",
                offset,
                error
            )
        })?;
        let bytes = decode_storage_payload(&encoded, MAX_STORED_TRANSACTION_INDEX_SIZE)
            .context("decoding compressed transaction index record")?;
        let (hash, _) = decode_transaction_index_value(&bytes)
            .with_context(|| format!("decoding transaction index record at offset {offset}"))?;
        if index.insert(hash, Record { offset, length }).is_some() {
            bail!("duplicate block hash in transaction index store");
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

fn persist_index_entry(
    file: &mut File,
    data_len: u64,
    hash: BlockHash,
    record: Record,
) -> Result<()> {
    persist_index_entry_with_sync(file, data_len, hash, record, true)
}

fn persist_index_entry_with_sync(
    file: &mut File,
    data_len: u64,
    hash: BlockHash,
    record: Record,
    sync: bool,
) -> Result<()> {
    file.seek(SeekFrom::Start(0))?;
    file.write_all(&data_len.to_le_bytes())?;
    file.seek(SeekFrom::End(0))?;
    file.write_all(&hash.to_byte_array())?;
    file.write_all(&record.offset.to_le_bytes())?;
    file.write_all(&record.length.to_le_bytes())?;
    if sync {
        file.sync_data()?;
    }
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
    fn utxo_locations_use_one_word_without_changing_disk_coordinates() {
        assert_eq!(
            std::mem::size_of::<UtxoLocation>(),
            std::mem::size_of::<u64>()
        );
        let location = UtxoLocation::new(123_456_789, 98_765).unwrap();
        assert_eq!(location.offset(), 123_456_789);
        assert_eq!(location.length(), 98_765);
        assert!(UtxoLocation::new(UtxoLocation::MAX_OFFSET + 1, 1).is_err());
        assert!(UtxoLocation::new(0, (UtxoLocation::LENGTH_MASK + 1) as u32).is_err());
    }

    #[test]
    fn history_locations_use_one_word_without_changing_disk_coordinates() {
        assert_eq!(
            std::mem::size_of::<HistoryLocation>(),
            std::mem::size_of::<u64>()
        );
        let location = HistoryLocation::new(123_456_789, HistoryLocation::MAX_LENGTH).unwrap();
        assert_eq!(location.offset(), 123_456_789);
        assert_eq!(location.length(), HistoryLocation::MAX_LENGTH);
        assert!(HistoryLocation::new(HistoryLocation::MAX_OFFSET + 1, 1).is_err());
        assert!(HistoryLocation::new(0, HistoryLocation::MAX_LENGTH + 1).is_err());
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
        let before = std::fs::metadata(directory.path().join("utxos.dat"))
            .unwrap()
            .len();
        store.compact().unwrap();
        let after = std::fs::metadata(directory.path().join("utxos.dat"))
            .unwrap()
            .len();
        assert!(after < before);
        assert_eq!(store.entries().unwrap(), entries);
        drop(store);

        let reopened = UtxoStore::open(directory.path()).unwrap();
        assert_eq!(reopened.entries().unwrap(), entries);
        assert_eq!(reopened.next_batch_id, 9);

        let index_path = directory.path().join("utxos.index");
        let mut index_bytes = std::fs::read(&index_path).unwrap();
        let offset_start = UTXO_INDEX_MAGIC.len() + 4 + 1 + 8;
        index_bytes[offset_start..offset_start + 8]
            .copy_from_slice(&(UTXO_DATA_MAGIC.len() as u64).to_le_bytes());
        std::fs::write(&index_path, index_bytes).unwrap();
        let repaired = UtxoStore::open(directory.path()).unwrap();
        assert_eq!(repaired.entries().unwrap(), entries);
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
        let index_path = directory.path().join("history.index");
        let mut index_bytes = std::fs::read(&index_path).unwrap();
        let first_put_body = ELECTRUM_HISTORY_INDEX_MAGIC.len() + 4;
        let offset_start = first_put_body + 1 + 8;
        index_bytes[offset_start..offset_start + 8]
            .copy_from_slice(&(ELECTRUM_HISTORY_DATA_MAGIC.len() as u64).to_le_bytes());
        std::fs::write(&index_path, index_bytes).unwrap();

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
        let before = std::fs::metadata(directory.path().join("history.dat"))
            .unwrap()
            .len();
        store.compact().unwrap();
        let after = std::fs::metadata(directory.path().join("history.dat"))
            .unwrap()
            .len();
        assert!(after < before);
        assert_eq!(store.get(&script_hash).unwrap(), history);
        drop(store);

        let reopened = ElectrumHistoryStore::open(directory.path()).unwrap();
        assert_eq!(reopened.get(&script_hash).unwrap(), history);
        assert_eq!(reopened.generation(), 10);
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
        assert_eq!(store.len(), 2);

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
