//! Append-only block storage.
//!
//! Blocks are written as length-prefixed consensus-encoded records. The
//! in-memory hash index makes reads O(1). A durable location index avoids
//! decoding the append-only file on normal restarts; truncated, stale, or
//! corrupt index files fall back to a complete record scan.

use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::{File, OpenOptions, create_dir_all, remove_file};
use std::io::{self, BufReader, Cursor, ErrorKind, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::{
    Arc, OnceLock,
    atomic::{AtomicUsize, Ordering},
};
use std::thread;
use std::time::{Duration, Instant};

#[cfg(target_os = "linux")]
use std::os::fd::AsRawFd;
#[cfg(unix)]
use std::os::unix::fs::FileExt;
#[cfg(windows)]
use std::os::windows::fs::FileExt;

use anyhow::{Context, Result, bail};
use bitcoin::bip158::FilterHeader;
use bitcoin::consensus::encode::{VarInt, deserialize, deserialize_partial, serialize};
use bitcoin::hashes::{Hash, HashEngine};
use bitcoin::{Block, BlockHash, OutPoint, Script, ScriptBuf, Transaction, TxOut, Txid};
use fjall::compaction::{Leveled, SizeTiered, Strategy as CompactionStrategy};
use fjall::{
    CompressionType, Config as FjallConfig, Keyspace, PartitionCreateOptions, PartitionHandle,
    PersistMode, Snapshot,
};
use hashbrown::{HashMap as FastHashMap, HashSet as FastHashSet};
use parking_lot::{Mutex, MutexGuard, RwLock};
use rand::random;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const MAX_STORED_BLOCK_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_UNDO_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_FILTER_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_CHAINSTATE_DELTA_SIZE: usize = 64 * 1024 * 1024;
const MAX_STORED_ELECTRUM_BLOCK_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_TRANSACTION_INDEX_SIZE: usize = 8 * 1024 * 1024;
const MAX_STORED_UTXO_SIZE: usize = 100 * 1024;
const MAX_STORED_UTXO_SCRIPT_SIZE: usize = 10_000;
// The native UTXO value keeps the implementation-specific median-time-past
// field, but otherwise follows Core's compact coin representation.  The
// magic is deliberately longer than the old fixed-width height prefix so an
// old record cannot be mistaken for the new format at any reachable height.
const COMPACT_STORED_UTXO_MAGIC: &[u8] = b"bitcoind-rs-utxo-v2\0";
const XOR_KEY_SIZE: usize = 8;
const STORAGE_COMPRESSION_MAGIC: &[u8] = b"bitcoind-rs-zstd-v1\0";
const STORAGE_COMPRESSION_HEADER_SIZE: usize = STORAGE_COMPRESSION_MAGIC.len() + 4;
// Compression accounting is advisory metadata, not part of the consensus
// store.  Keep it in a separate checksummed sidecar so a restart can reuse
// the counters without walking every block and undo record header.
const STORAGE_COMPRESSION_STATS_MAGIC: &[u8] = b"bitcoind-rs-zstd-stats-v1\0";
const STORAGE_COMPRESSION_STATS_CHECKSUM_SIZE: usize = 32;
pub const STORAGE_COMPRESSION_LEVEL: i32 = 6;
const STORAGE_COMPRESSION_MIN_SIZE: usize = 256;
const INDEX_HEADER_SIZE: u64 = 8;
const INDEX_RECORD_SIZE: u64 = 44;
const APPEND_BUFFER_FLUSH_BYTES: usize = 16 * 1024 * 1024;
const BLOCK_PREALLOCATION_CHUNK_BYTES: u64 = 16 * 1024 * 1024;
const UNDO_PREALLOCATION_CHUNK_BYTES: u64 = 1024 * 1024;
// Core's BufferedFile keeps roughly two maximum block payloads available
// while reindexing. Use the same order of magnitude for the native store so
// sequential replay benefits from filesystem/NFS readahead.
const BLOCK_REPLAY_READ_BUFFER_BYTES: usize = 8 * 1024 * 1024;

#[derive(Clone, Copy, Debug)]
struct Record {
    offset: u64,
    length: u32,
}

fn preallocate_keep_size(file: &File, offset: u64, length: u64) -> io::Result<()> {
    #[cfg(target_os = "linux")]
    {
        let offset = i64::try_from(offset)
            .map_err(|_| io::Error::new(ErrorKind::InvalidInput, "file offset exceeds i64"))?;
        let length = i64::try_from(length)
            .map_err(|_| io::Error::new(ErrorKind::InvalidInput, "file length exceeds i64"))?;
        // SAFETY: the descriptor remains owned by `file` for the duration of
        // the call, and fallocate does not access Rust memory.
        let result =
            unsafe { libc::fallocate(file.as_raw_fd(), libc::FALLOC_FL_KEEP_SIZE, offset, length) };
        if result == 0 {
            Ok(())
        } else {
            Err(io::Error::last_os_error())
        }
    }
    #[cfg(not(target_os = "linux"))]
    {
        let _ = (file, offset, length);
        Err(io::Error::new(
            ErrorKind::Unsupported,
            "keep-size preallocation is unavailable",
        ))
    }
}

fn ensure_file_preallocated(
    file: &File,
    preallocated_through: &mut u64,
    enabled: &mut bool,
    end: u64,
    chunk_bytes: u64,
    path: &Path,
) {
    if !*enabled || end <= *preallocated_through {
        return;
    }
    let target = end.div_ceil(chunk_bytes).saturating_mul(chunk_bytes);
    let length = target.saturating_sub(*preallocated_through);
    if length == 0 {
        return;
    }
    match preallocate_keep_size(file, *preallocated_through, length) {
        Ok(()) => *preallocated_through = target,
        Err(error) => {
            // Preallocation is an optimization and is not supported by every
            // NFS server or filesystem. Disable it for this open descriptor;
            // the normal append still reports real write/space failures.
            *enabled = false;
            tracing::debug!(
                path = %path.display(),
                %error,
                "append-file preallocation is unavailable"
            );
        }
    }
}

/// Exact compression accounting for one native append-only record file.
///
/// `uncompressed_size_bytes` and `stored_size_bytes` both include the
/// unchanged four-byte framing prefix for every record. The payload-specific
/// fields make the small framing overhead explicit for diagnostic tools.
#[derive(Clone, Copy, Debug, Default, PartialEq, Serialize)]
pub struct StorageCompressionInfo {
    pub records: u64,
    pub compressed_records: u64,
    pub uncompressed_records: u64,
    pub original_payload_bytes: u64,
    pub stored_payload_bytes: u64,
    pub framing_bytes: u64,
    pub uncompressed_size_bytes: u64,
    pub stored_size_bytes: u64,
    pub saved_bytes: u64,
    pub space_saved_percent: f64,
    pub compression_ratio: f64,
}

#[derive(Clone, Copy, Debug, Default, Deserialize, Serialize)]
struct StorageCompressionCounts {
    records: u64,
    compressed_records: u64,
    original_payload_bytes: u64,
    stored_payload_bytes: u64,
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
struct PersistedStorageCompression {
    data_len: u64,
    counts: StorageCompressionCounts,
}

#[derive(Clone, Copy, Debug)]
struct PendingCompressionRecord {
    original_length: u64,
    stored_length: u64,
}

#[derive(Debug, Default)]
struct StorageCompressionCache {
    counts: Option<StorageCompressionCounts>,
    tracking_from: Option<u64>,
    tracking_end: u64,
    pending: Vec<PendingCompressionRecord>,
}

impl StorageCompressionCounts {
    fn add_record(&mut self, original_length: u64, stored_length: u64, compressed: bool) {
        self.records = self.records.saturating_add(1);
        self.compressed_records = self
            .compressed_records
            .saturating_add(u64::from(compressed));
        self.original_payload_bytes = self.original_payload_bytes.saturating_add(original_length);
        self.stored_payload_bytes = self.stored_payload_bytes.saturating_add(stored_length);
    }

    fn stored_size_bytes(self) -> u64 {
        self.stored_payload_bytes
            .saturating_add(self.records.saturating_mul(4))
    }

    fn into_info(self) -> StorageCompressionInfo {
        let framing_bytes = self.records.saturating_mul(4);
        let uncompressed_size_bytes = self.original_payload_bytes.saturating_add(framing_bytes);
        let stored_size_bytes = self.stored_payload_bytes.saturating_add(framing_bytes);
        let saved_bytes = uncompressed_size_bytes.saturating_sub(stored_size_bytes);
        let (space_saved_percent, compression_ratio) = if uncompressed_size_bytes == 0 {
            (0.0, 1.0)
        } else {
            (
                saved_bytes as f64 * 100.0 / uncompressed_size_bytes as f64,
                uncompressed_size_bytes as f64 / stored_size_bytes as f64,
            )
        };
        StorageCompressionInfo {
            records: self.records,
            compressed_records: self.compressed_records,
            uncompressed_records: self.records.saturating_sub(self.compressed_records),
            original_payload_bytes: self.original_payload_bytes,
            stored_payload_bytes: self.stored_payload_bytes,
            framing_bytes,
            uncompressed_size_bytes,
            stored_size_bytes,
            saved_bytes,
            space_saved_percent,
            compression_ratio,
        }
    }

    fn combine(self, other: Self) -> Self {
        Self {
            records: self.records.saturating_add(other.records),
            compressed_records: self
                .compressed_records
                .saturating_add(other.compressed_records),
            original_payload_bytes: self
                .original_payload_bytes
                .saturating_add(other.original_payload_bytes),
            stored_payload_bytes: self
                .stored_payload_bytes
                .saturating_add(other.stored_payload_bytes),
        }
    }
}

fn compression_stats_path(data_path: &Path) -> PathBuf {
    data_path.with_extension("compression")
}

fn encode_storage_compression_stats(counts: StorageCompressionCounts) -> Result<Vec<u8>> {
    let persisted = PersistedStorageCompression {
        data_len: counts.stored_size_bytes(),
        counts,
    };
    let payload = bincode::serialize(&persisted).context("encoding compression statistics")?;
    let mut bytes = Vec::with_capacity(
        STORAGE_COMPRESSION_STATS_MAGIC
            .len()
            .saturating_add(payload.len())
            .saturating_add(STORAGE_COMPRESSION_STATS_CHECKSUM_SIZE),
    );
    bytes.extend_from_slice(STORAGE_COMPRESSION_STATS_MAGIC);
    bytes.extend_from_slice(&payload);
    let checksum = Sha256::digest(&bytes);
    bytes.extend_from_slice(checksum.as_slice());
    Ok(bytes)
}

fn load_storage_compression_stats(path: &Path) -> Option<PersistedStorageCompression> {
    let bytes = std::fs::read(path).ok()?;
    let payload_end = bytes
        .len()
        .checked_sub(STORAGE_COMPRESSION_STATS_CHECKSUM_SIZE)?;
    if payload_end < STORAGE_COMPRESSION_STATS_MAGIC.len()
        || !bytes.starts_with(STORAGE_COMPRESSION_STATS_MAGIC)
    {
        return None;
    }
    let checksum = Sha256::digest(&bytes[..payload_end]);
    if checksum.as_slice() != &bytes[payload_end..] {
        return None;
    }
    bincode::deserialize(&bytes[STORAGE_COMPRESSION_STATS_MAGIC.len()..payload_end]).ok()
}

/// Persist a complete counter snapshot atomically.  The temporary filename is
/// unique because compression RPCs may finish concurrently; an older snapshot
/// is still safe if a process stops between the data append and this rename.
fn persist_storage_compression_stats(path: &Path, counts: StorageCompressionCounts) -> Result<()> {
    let bytes = encode_storage_compression_stats(counts)?;
    let temporary = path.with_file_name(format!(
        ".{}.tmp-{:016x}",
        path.file_name().unwrap_or_default().to_string_lossy(),
        random::<u64>()
    ));
    let result = (|| {
        let mut file = OpenOptions::new()
            .create(true)
            .truncate(true)
            .write(true)
            .open(&temporary)
            .with_context(|| format!("opening compression statistics {}", temporary.display()))?;
        file.write_all(&bytes)?;
        file.sync_all()?;
        drop(file);
        std::fs::rename(&temporary, path)
            .with_context(|| format!("publishing compression statistics {}", path.display()))?;
        Ok(())
    })();
    if result.is_err() {
        let _ = remove_file(&temporary);
    }
    result
}

/// Compression accounting for the authoritative block and undo stores.
#[derive(Clone, Copy, Debug, Default, PartialEq, Serialize)]
pub struct BlockStoreCompressionInfo {
    pub blocks: StorageCompressionInfo,
    pub undo: StorageCompressionInfo,
    pub total: StorageCompressionInfo,
}

/// The value kept by the durable UTXO store and the chain validation cache.
///
/// Keeping one representation for both layers is important on the IBD hot
/// path: a cache miss can be decoded once, validated, and then moved into the
/// resident cache without cloning the transaction output just to cross a
/// storage/chain boundary.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct StoredUtxo {
    pub output: TxOut,
    pub height: u32,
    pub median_time_past: u32,
    pub coinbase: bool,
}

#[derive(Clone)]
struct PendingUtxo {
    entry: Option<StoredUtxo>,
    fresh: bool,
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

const UTXO_CACHE_SHARDS: usize = 384;

struct UtxoReadCache {
    // The decoded cache is deliberately sharded so a complete warm can
    // reserve each hash table independently. Do not keep an LRU/FIFO side
    // table here: a second OutPoint for every resident coin is a substantial
    // fraction of process memory at mainnet scale. Eviction rotates through
    // the shards and removes arbitrary entries; this is a cache-only policy
    // and cannot affect consensus or the authoritative LSM view.
    entries: Vec<FastHashMap<OutPoint, StoredUtxo>>,
    eviction_shard: usize,
    entry_count: usize,
    bytes: usize,
    limit: usize,
    complete: bool,
}

impl Default for UtxoReadCache {
    fn default() -> Self {
        Self {
            entries: (0..UTXO_CACHE_SHARDS).map(|_| FastHashMap::new()).collect(),
            eviction_shard: 0,
            entry_count: 0,
            bytes: 0,
            limit: 0,
            complete: false,
        }
    }
}

impl UtxoReadCache {
    fn shard_index(outpoint: &OutPoint) -> usize {
        let txid = outpoint.txid.to_byte_array();
        usize::from(u16::from_le_bytes([txid[0], txid[1]])) % UTXO_CACHE_SHARDS
    }

    fn len(&self) -> usize {
        self.entry_count
    }

    fn contains_key(&self, outpoint: &OutPoint) -> bool {
        self.entries[Self::shard_index(outpoint)].contains_key(outpoint)
    }

    fn reserve(&mut self, entries: usize) {
        let per_shard = entries.div_ceil(UTXO_CACHE_SHARDS);
        for shard in &mut self.entries {
            shard.reserve(per_shard.saturating_sub(shard.len()));
        }
    }

    fn configure_limit(&mut self, limit: usize) {
        self.limit = limit;
        self.trim();
    }

    fn get_ref(&self, outpoint: &OutPoint) -> Option<&StoredUtxo> {
        self.entries[Self::shard_index(outpoint)].get(outpoint)
    }

    fn get(&self, outpoint: &OutPoint) -> Option<StoredUtxo> {
        self.get_ref(outpoint).cloned()
    }

    fn insert(&mut self, outpoint: OutPoint, entry: StoredUtxo) {
        let bytes = read_cache_utxo_bytes(&entry);
        if self.limit == 0 || bytes > self.limit {
            self.complete = false;
            return;
        }
        // This is an incremental cache insertion from a pending mutation or
        // a point-read prefetch, not a proof that the cache covers the whole
        // database. A cache that was complete only because the store was
        // empty must stop claiming completeness as soon as the first coin is
        // added; otherwise query_unresolved can skip a disk read and leave
        // consensus validation with an apparently prefetched miss.
        self.complete = false;
        let shard = Self::shard_index(&outpoint);
        if let Some(old_entry) = self.entries[shard].insert(outpoint, entry) {
            self.bytes = self.bytes.saturating_sub(read_cache_utxo_bytes(&old_entry));
        } else {
            self.entry_count = self.entry_count.saturating_add(1);
        }
        self.bytes = self.bytes.saturating_add(bytes);
        self.trim();
    }

    /// Insert an entry discovered by a complete sequential database scan.
    /// It remains cache-resident until spent or until a later size trim needs
    /// to reclaim it.
    fn insert_stationary(&mut self, outpoint: OutPoint, entry: StoredUtxo) {
        let bytes = read_cache_utxo_bytes(&entry);
        if self.limit == 0 || bytes > self.limit {
            self.complete = false;
            return;
        }
        let shard = Self::shard_index(&outpoint);
        if let Some(old_entry) = self.entries[shard].insert(outpoint, entry) {
            self.bytes = self.bytes.saturating_sub(read_cache_utxo_bytes(&old_entry));
        } else {
            self.entry_count = self.entry_count.saturating_add(1);
        }
        self.bytes = self.bytes.saturating_add(bytes);
    }

    fn remove(&mut self, outpoint: &OutPoint) {
        let shard = Self::shard_index(outpoint);
        if let Some(entry) = self.entries[shard].remove(outpoint) {
            self.bytes = self.bytes.saturating_sub(read_cache_utxo_bytes(&entry));
            self.entry_count = self.entry_count.saturating_sub(1);
        }
    }

    fn clear(&mut self) {
        // Core's large coin-cache flush calls ReallocateCache after clearing
        // the map.  `HashMap::clear` keeps every bucket allocation alive,
        // which is particularly expensive here because the cache is split
        // into shards and can contain millions of outpoints.  Replace the
        // buckets so a checkpoint can actually return the table to the
        // allocator instead of retaining its peak capacity for the rest of
        // IBD.
        self.entries = (0..UTXO_CACHE_SHARDS).map(|_| FastHashMap::new()).collect();
        self.eviction_shard = 0;
        self.entry_count = 0;
        self.bytes = 0;
        self.complete = false;
    }

    /// Reserve the buckets needed by a bulk cache rebuild before inserting
    /// entries. Large IBD checkpoints repopulate millions of recent coins
    /// after replacing the cache; growing 384 hash tables incrementally
    /// repeatedly allocates, copies, and frees bucket arrays while the chain
    /// writer is held. Counting the target shard for each entry is a small
    /// fixed-size pass and avoids that allocator churn without changing the
    /// cache contents or eviction policy.
    fn reserve_for_outpoints<'a, I>(&mut self, outpoints: I)
    where
        I: IntoIterator<Item = &'a OutPoint>,
    {
        let mut counts = [0usize; UTXO_CACHE_SHARDS];
        for outpoint in outpoints {
            let shard = Self::shard_index(outpoint);
            counts[shard] = counts[shard].saturating_add(1);
        }
        for (shard, count) in self.entries.iter_mut().zip(counts) {
            if count != 0 {
                shard.reserve(count);
            }
        }
    }

    fn trim(&mut self) {
        self.trim_to(self.limit);
    }

    /// Trim to a temporary target without changing the configured cache
    /// budget. Large Core-style checkpoints normally clear the decoded coin
    /// cache, but retaining a small newest-output window is useful on the
    /// next IBD blocks and still leaves the normal budget accounting intact.
    fn trim_to(&mut self, limit: usize) {
        if self.bytes <= limit {
            return;
        }
        let target = limit.saturating_mul(7) / 8;
        let shard_count = self.entries.len();
        let mut empty_shards = 0usize;
        while self.bytes > target && self.entry_count != 0 && empty_shards < shard_count {
            let shard_index = self.eviction_shard % shard_count;
            self.eviction_shard = self.eviction_shard.saturating_add(1) % shard_count;
            let outpoint = self.entries[shard_index].keys().next().copied();
            let Some(outpoint) = outpoint else {
                empty_shards = empty_shards.saturating_add(1);
                continue;
            };
            if let Some(entry) = self.entries[shard_index].remove(&outpoint) {
                self.bytes = self.bytes.saturating_sub(read_cache_utxo_bytes(&entry));
                self.entry_count = self.entry_count.saturating_sub(1);
                self.complete = false;
                empty_shards = 0;
            }
        }
        if self.bytes > limit {
            self.complete = false;
        }
    }
}

fn stored_utxo_cache_bytes(entry: &StoredUtxo) -> usize {
    64usize.saturating_add(entry.output.script_pubkey.len())
}

// A resident decoded coin occupies more than its serialized value: the
// sharded hash table stores the outpoint and its bucket/table overhead.
// Core's DynamicMemoryUsage includes that container overhead. Charging it to
// the cache budget prevents the native cache from reaching the byte limit
// only after its allocator footprint has already grown far beyond it.
const UTXO_CACHE_CONTAINER_OVERHEAD: usize = 96;
// A pending coin is stored in a hashbrown table as an OutPoint key plus a
// PendingUtxo value.  The previous 32-byte allowance covered only the map
// bookkeeping and substantially understated the table's bucket/key/value
// footprint once IBD accumulated millions of dirty entries.  Charge a
// conservative per-entry slot allowance so the byte-based checkpoint fires
// before the allocator has to grow a multi-gigabyte table; this follows Core's
// DynamicMemoryUsage accounting more closely and avoids swap-driven stalls.
const UTXO_PENDING_CONTAINER_OVERHEAD: usize = 96;

fn read_cache_utxo_bytes(entry: &StoredUtxo) -> usize {
    stored_utxo_cache_bytes(entry).saturating_add(UTXO_CACHE_CONTAINER_OVERHEAD)
}

fn pending_utxo_bytes(entry: Option<&StoredUtxo>) -> usize {
    // Include the outpoint/hash-map bookkeeping that is not represented by
    // `stored_utxo_cache_bytes`. This is intentionally conservative: the
    // trigger should resemble Core's DynamicMemoryUsage, not just the value
    // payload size.
    48usize
        .saturating_add(UTXO_PENDING_CONTAINER_OVERHEAD)
        .saturating_add(entry.map_or(0, stored_utxo_cache_bytes))
}

/// Return large hash-table allocations released by a UTXO checkpoint to the
/// operating system.  The Core implementation explicitly reallocates its
/// coin cache after a large flush; glibc otherwise keeps these freed pages in
/// the process arena, making each repeated IBD checkpoint look like a memory
/// leak and eventually causing swap-driven stalls.
fn trim_utxo_process_heap() {
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    // SAFETY: `malloc_trim` has no pointer arguments and only releases pages
    // that are no longer owned by a live allocation.
    unsafe {
        libc::malloc_trim(0);
    }
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

/// Inspect one native length-prefixed append-only file without decompressing
/// or reading complete record payloads. If no XOR-key path is supplied, an
/// adjacent `xor.dat` is used when present; otherwise a zero key is assumed.
pub fn inspect_storage_file_compression(
    path: impl AsRef<Path>,
    xor_key_path: Option<&Path>,
) -> Result<StorageCompressionInfo> {
    let path = path.as_ref();
    let file = OpenOptions::new()
        .read(true)
        .open(path)
        .with_context(|| format!("opening native storage file {}", path.display()))?;
    let automatic_xor_path = path.parent().map(|parent| parent.join("xor.dat"));
    let xor_path = xor_key_path
        .map(Path::to_path_buf)
        .or_else(|| automatic_xor_path.filter(|candidate| candidate.is_file()));
    let xor_key = xor_path
        .as_deref()
        .map(read_xor_key)
        .transpose()?
        .unwrap_or_default();
    let data_len = file.metadata()?.len();
    if let Some(persisted) = load_storage_compression_stats(&compression_stats_path(path))
        && persisted.data_len == data_len
        && persisted.counts.stored_size_bytes() == data_len
    {
        return Ok(persisted.counts.into_info());
    }
    let persisted = load_storage_compression_stats(&compression_stats_path(path));
    let counts = match load_storage_compression_index(path, data_len)? {
        Some(records) => {
            if let Some(persisted) = persisted {
                if let Some((base, prefix_records)) =
                    valid_storage_compression_prefix(persisted, data_len, &records)
                {
                    if base.stored_size_bytes() == data_len {
                        base
                    } else {
                        let suffix = scan_indexed_storage_compression(
                            &file,
                            xor_key,
                            &records[prefix_records..],
                        )?;
                        base.combine(suffix)
                    }
                } else {
                    scan_indexed_storage_compression(&file, xor_key, &records)?
                }
            } else {
                scan_indexed_storage_compression(&file, xor_key, &records)?
            }
        }
        None => scan_storage_compression(&file, xor_key, data_len)?,
    };
    // The sidecar is deliberately best-effort: inspection remains useful for
    // read-only directories and removable media where it cannot be updated.
    if counts.stored_size_bytes() == data_len {
        let _ = persist_storage_compression_stats(&compression_stats_path(path), counts);
    }
    Ok(counts.into_info())
}

fn load_storage_compression_index(path: &Path, data_len: u64) -> Result<Option<Vec<Record>>> {
    let index_path = path.with_extension("index");
    if !index_path.is_file() {
        return Ok(None);
    }
    // Indexes are compact (44 bytes per record). One buffered read avoids a
    // syscall per record, which is especially important on network filesystems.
    let index_bytes = std::fs::read(&index_path)
        .with_context(|| format!("reading native storage index {}", index_path.display()))?;
    let index_len = index_bytes.len() as u64;
    if index_len < INDEX_HEADER_SIZE || (index_len - INDEX_HEADER_SIZE) % INDEX_RECORD_SIZE != 0 {
        return Ok(None);
    }
    let record_count = (index_len - INDEX_HEADER_SIZE) / INDEX_RECORD_SIZE;
    let mut records = Vec::with_capacity(
        usize::try_from(record_count).context("native storage index is too large")?,
    );
    for bytes in index_bytes[INDEX_HEADER_SIZE as usize..].chunks_exact(INDEX_RECORD_SIZE as usize)
    {
        let offset = u64::from_le_bytes(
            bytes[32..40]
                .try_into()
                .expect("native index offset has fixed width"),
        );
        let length = u32::from_le_bytes(
            bytes[40..44]
                .try_into()
                .expect("native index length has fixed width"),
        );
        if length == 0 {
            return Ok(None);
        }
        let Some(end) = offset
            .checked_add(4)
            .and_then(|value| value.checked_add(u64::from(length)))
        else {
            return Ok(None);
        };
        if end <= data_len {
            records.push(Record { offset, length });
        } else if offset < data_len {
            return Ok(None);
        }
    }
    records.sort_unstable_by_key(|record| record.offset);
    let mut expected_offset = 0u64;
    for record in &records {
        if record.offset != expected_offset {
            return Ok(None);
        }
        expected_offset = record.offset + 4 + u64::from(record.length);
    }
    if expected_offset != data_len {
        return Ok(None);
    }
    Ok(Some(records))
}

fn record_end(record: Record) -> u64 {
    record
        .offset
        .saturating_add(4)
        .saturating_add(u64::from(record.length))
}

fn valid_storage_compression_prefix(
    persisted: PersistedStorageCompression,
    data_len: u64,
    records: &[Record],
) -> Option<(StorageCompressionCounts, usize)> {
    let cached_len = persisted.counts.stored_size_bytes();
    if persisted.data_len != cached_len || cached_len > data_len {
        return None;
    }
    let prefix_records = records.partition_point(|record| record_end(*record) <= cached_len);
    let valid_boundary = cached_len == 0
        || cached_len == data_len
        || records
            .get(prefix_records)
            .is_some_and(|record| record.offset == cached_len);
    let prefix_records_u64 = u64::try_from(prefix_records).unwrap_or(u64::MAX);
    let index_records = u64::try_from(records.len()).unwrap_or(u64::MAX);
    let valid = persisted.counts.records == prefix_records_u64
        && valid_boundary
        && (cached_len < data_len || persisted.counts.records == index_records);
    valid.then_some((persisted.counts, prefix_records))
}

/// Restore a counters cache when its boundary is represented by the current
/// record index.  A sidecar may lag behind an append-only data file; that is
/// still useful because the inspector can scan only records after this
/// boundary.  Rewritten/pruned files fail the boundary test and fall back to a
/// full authoritative scan instead of trusting stale accounting.
fn load_compression_cache(
    data_path: &Path,
    data_len: u64,
    index: &HashMap<BlockHash, Record>,
) -> StorageCompressionCache {
    let mut cache = StorageCompressionCache::default();
    // An empty append-only store has an unambiguous zero-length prefix. Seed
    // it so ordinary block/undo appends can maintain the counters and publish
    // the sidecar at the next durable flush without requiring an RPC first.
    if data_len == 0 && index.is_empty() {
        cache.counts = Some(StorageCompressionCounts::default());
        return cache;
    }
    let Some(persisted) = load_storage_compression_stats(&compression_stats_path(data_path)) else {
        return cache;
    };
    let cached_len = persisted.counts.stored_size_bytes();
    if persisted.data_len != cached_len || cached_len > data_len {
        return cache;
    }
    let prefix_records = index
        .values()
        .filter(|record| record_end(**record) <= cached_len)
        .count();
    let valid_boundary = cached_len == 0
        || cached_len == data_len
        || index.values().any(|record| record.offset == cached_len);
    let prefix_records = u64::try_from(prefix_records).unwrap_or(u64::MAX);
    let index_records = u64::try_from(index.len()).unwrap_or(u64::MAX);
    let valid = persisted.counts.records == prefix_records
        && valid_boundary
        && (cached_len < data_len || persisted.counts.records == index_records);
    if valid {
        cache.counts = Some(persisted.counts);
    }
    cache
}

fn scan_indexed_storage_compression(
    file: &File,
    xor_key: XorKey,
    records: &[Record],
) -> Result<StorageCompressionCounts> {
    if records.is_empty() {
        return Ok(StorageCompressionCounts::default());
    }
    const MAX_INSPECTION_THREADS: usize = 16;
    let worker_count = thread::available_parallelism()
        .map_or(1, |parallelism| parallelism.get())
        .min(MAX_INSPECTION_THREADS)
        .min(records.len());
    let next_record = AtomicUsize::new(0);
    thread::scope(|scope| {
        let workers = (0..worker_count)
            .map(|_| {
                let next_record = &next_record;
                scope.spawn(move || {
                    let mut counts = StorageCompressionCounts::default();
                    loop {
                        let index = next_record.fetch_add(1, Ordering::Relaxed);
                        let Some(record) = records.get(index) else {
                            break;
                        };
                        let (original_length, compressed) =
                            inspect_storage_record_header(file, xor_key, *record)?;
                        counts.add_record(original_length, u64::from(record.length), compressed);
                    }
                    Ok::<_, anyhow::Error>(counts)
                })
            })
            .collect::<Vec<_>>();
        let mut counts = StorageCompressionCounts::default();
        for worker in workers {
            let partial = worker
                .join()
                .map_err(|_| anyhow::anyhow!("native storage inspection worker panicked"))??;
            counts = counts.combine(partial);
        }
        Ok(counts)
    })
}

fn inspect_storage_record_header(
    file: &File,
    xor_key: XorKey,
    record: Record,
) -> Result<(u64, bool)> {
    let header_length = usize::try_from(record.length)
        .unwrap_or(usize::MAX)
        .min(STORAGE_COMPRESSION_HEADER_SIZE);
    let mut prefix = [0u8; 4 + STORAGE_COMPRESSION_HEADER_SIZE];
    let prefix_length = 4 + header_length;
    read_block_exact_at(file, &mut prefix[..prefix_length], record.offset)
        .with_context(|| format!("reading native storage record at offset {}", record.offset))?;
    xor_key.apply(&mut prefix[..prefix_length], record.offset);
    let actual_length = u32::from_le_bytes(
        prefix[..4]
            .try_into()
            .expect("native storage length has fixed width"),
    );
    if actual_length != record.length {
        bail!(
            "native storage index disagrees with record length at offset {}",
            record.offset
        )
    }
    let header = &prefix[4..prefix_length];
    if header_length < STORAGE_COMPRESSION_HEADER_SIZE
        || !header.starts_with(STORAGE_COMPRESSION_MAGIC)
    {
        return Ok((u64::from(record.length), false));
    }
    let length_start = STORAGE_COMPRESSION_MAGIC.len();
    let original_length = u32::from_le_bytes(
        header[length_start..STORAGE_COMPRESSION_HEADER_SIZE]
            .try_into()
            .expect("zstd storage length has fixed width"),
    );
    if original_length <= record.length {
        bail!(
            "invalid zstd storage lengths at offset {}: original {}, stored {}",
            record.offset,
            original_length,
            record.length
        )
    }
    Ok((u64::from(original_length), true))
}

fn scan_storage_compression(
    file: &File,
    xor_key: XorKey,
    data_len: u64,
) -> Result<StorageCompressionCounts> {
    const PREFIX_SIZE: usize = 4 + STORAGE_COMPRESSION_HEADER_SIZE;
    let mut counts = StorageCompressionCounts::default();
    let mut offset = 0u64;
    while offset < data_len {
        let remaining = data_len.saturating_sub(offset);
        if remaining < 4 {
            bail!("truncated native storage length at offset {offset}")
        }
        let prefix_length = usize::try_from(remaining.min(PREFIX_SIZE as u64))
            .context("native storage prefix length does not fit usize")?;
        let mut prefix = [0u8; PREFIX_SIZE];
        read_block_exact_at(file, &mut prefix[..prefix_length], offset)
            .with_context(|| format!("reading native storage record at offset {offset}"))?;
        xor_key.apply(&mut prefix[..prefix_length], offset);

        let stored_length = u32::from_le_bytes(
            prefix[..4]
                .try_into()
                .expect("native record length has fixed width"),
        );
        if stored_length == 0 {
            bail!("invalid zero-length native storage record at offset {offset}")
        }
        let record_end = offset
            .checked_add(4)
            .and_then(|value| value.checked_add(u64::from(stored_length)))
            .context("native storage record offset overflowed")?;
        if record_end > data_len {
            bail!(
                "truncated native storage record at offset {offset}: expected end {record_end}, file size is {data_len}"
            )
        }

        let stored_length_u64 = u64::from(stored_length);
        let has_compression_header = usize::try_from(stored_length)
            .ok()
            .is_some_and(|length| length >= STORAGE_COMPRESSION_HEADER_SIZE)
            && prefix[4..4 + STORAGE_COMPRESSION_MAGIC.len()]
                .starts_with(STORAGE_COMPRESSION_MAGIC);
        let original_length = if has_compression_header {
            let length_start = 4 + STORAGE_COMPRESSION_MAGIC.len();
            let original_length = u32::from_le_bytes(
                prefix[length_start..length_start + 4]
                    .try_into()
                    .expect("zstd storage length has fixed width"),
            );
            if u64::from(original_length) <= stored_length_u64 {
                bail!(
                    "invalid zstd storage lengths at offset {offset}: original {original_length}, stored {stored_length}"
                )
            }
            u64::from(original_length)
        } else {
            stored_length_u64
        };
        counts.add_record(original_length, stored_length_u64, has_compression_header);
        offset = record_end;
    }
    Ok(counts)
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
    pending_blocks: Arc<RwLock<HashMap<BlockHash, Arc<Block>>>>,
    xor_key: XorKey,
}

impl BlockStoreReader {
    fn new(file: File, index: HashMap<BlockHash, Record>, xor_key: XorKey) -> Self {
        Self {
            file: Arc::new(RwLock::new(file)),
            index: Arc::new(RwLock::new(index)),
            pending_blocks: Arc::new(RwLock::new(HashMap::new())),
            xor_key,
        }
    }

    pub(crate) fn get_shared(&self, hash: &BlockHash) -> Result<Option<Arc<Block>>> {
        if let Some(block) = self.pending_blocks.read().get(hash).map(Arc::clone) {
            return Ok(Some(block));
        }
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
        Ok(Some(Arc::new(block)))
    }

    pub fn get(&self, hash: &BlockHash) -> Result<Option<Block>> {
        self.get_shared(hash)
            .map(|block| block.map(|block| block.as_ref().clone()))
    }

    pub fn transaction_count(&self, hash: &BlockHash) -> Result<Option<usize>> {
        if let Some(block) = self.pending_blocks.read().get(hash) {
            return Ok(Some(block.txdata.len()));
        }
        let Some(record) = self.index.read().get(hash).copied() else {
            return Ok(None);
        };
        read_block_transaction_count(&self.file.read(), record, self.xor_key).map(Some)
    }

    fn insert(&self, hash: BlockHash, record: Record) {
        self.index.write().insert(hash, record);
    }

    fn insert_pending(&self, hash: BlockHash, block: Arc<Block>) {
        self.pending_blocks.write().insert(hash, block);
    }

    fn clear_pending(&self) {
        self.pending_blocks.write().clear();
    }

    fn replace(&self, file: File, index: HashMap<BlockHash, Record>) {
        *self.file.write() = file;
        *self.index.write() = index;
        self.clear_pending();
    }
}

pub struct BlockStore {
    path: PathBuf,
    file: File,
    // Forward chainstate replay normally consumes block records in their
    // append order. Keep a private buffered cursor for that path so IBD does
    // not turn every block body into a separate positional NFS read. The
    // ordinary serving reader and RPC path continue to use independent
    // positional reads.
    replay_reader: Option<BufReader<File>>,
    replay_reader_cursor: u64,
    index_file: File,
    index: HashMap<BlockHash, Record>,
    serving_reader: BlockStoreReader,
    undo_file: File,
    undo_index_file: File,
    undo_index: HashMap<BlockHash, Record>,
    block_data_len: u64,
    undo_data_len: u64,
    block_preallocated_through: u64,
    undo_preallocated_through: u64,
    block_preallocation_enabled: bool,
    undo_preallocation_enabled: bool,
    pending_block_data: Vec<u8>,
    pending_index_data: Vec<u8>,
    pending_undo_data: Vec<u8>,
    pending_undo_index_data: Vec<u8>,
    xor_key: XorKey,
    block_file_read_only: bool,
    allow_block_file_reopen: bool,
    block_cache: HashMap<BlockHash, (Arc<Block>, usize)>,
    block_cache_order: VecDeque<BlockHash>,
    block_cache_bytes: usize,
    block_cache_limit: usize,
    block_cache_metrics: BlockStoreCacheMetrics,
    block_compression_cache: Arc<Mutex<StorageCompressionCache>>,
    undo_compression_cache: Arc<Mutex<StorageCompressionCache>>,
}

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct BlockStoreCacheMetrics {
    pub(crate) lookups: u64,
    pub(crate) hits: u64,
    pub(crate) misses: u64,
    pub(crate) lookup_time: Duration,
    pub(crate) load_time: Duration,
    pub(crate) decode_time: Duration,
}

struct StorageCompressionSnapshot {
    file: File,
    data_len: u64,
    xor_key: XorKey,
    base_counts: Option<StorageCompressionCounts>,
    records: Vec<Record>,
    stats_path: PathBuf,
    cache: Arc<Mutex<StorageCompressionCache>>,
}

/// A consistent pair of append-only file snapshots. Creating this object is
/// quick enough to do under the chain read lock; the potentially longer
/// header scan happens after that lock has been released.
pub struct BlockStoreCompressionInspector {
    blocks: StorageCompressionSnapshot,
    undo: StorageCompressionSnapshot,
}

impl BlockStoreCompressionInspector {
    pub fn inspect(self) -> Result<BlockStoreCompressionInfo> {
        let blocks = inspect_compression_snapshot(self.blocks)?;
        let undo = inspect_compression_snapshot(self.undo)?;
        let total = blocks.combine(undo);
        Ok(BlockStoreCompressionInfo {
            blocks: blocks.into_info(),
            undo: undo.into_info(),
            total: total.into_info(),
        })
    }
}

fn inspect_compression_snapshot(
    mut snapshot: StorageCompressionSnapshot,
) -> Result<StorageCompressionCounts> {
    if let Some(cached) = snapshot.cache.lock().counts
        && cached.stored_size_bytes() == snapshot.data_len
    {
        return Ok(cached);
    }
    let suffix = if snapshot.records.is_empty()
        && snapshot.data_len != 0
        && snapshot.base_counts.is_none()
    {
        scan_storage_compression(&snapshot.file, snapshot.xor_key, snapshot.data_len)?
    } else {
        snapshot
            .records
            .sort_unstable_by_key(|record| record.offset);
        scan_indexed_storage_compression(&snapshot.file, snapshot.xor_key, &snapshot.records)?
    };
    let inspected = snapshot
        .base_counts
        .map_or(suffix, |base| base.combine(suffix));
    // `inspected` describes the exact file length captured before the scan.
    // IBD may append more records while the header scan is in progress; keep
    // this prefix separately so it can still be persisted even when the
    // in-memory result is extended with those concurrent records below.
    let persistable = inspected;
    let mut cache = snapshot.cache.lock();
    let mut current = inspected;
    if cache.tracking_from == Some(snapshot.data_len) {
        for pending in &cache.pending {
            current.add_record(
                pending.original_length,
                pending.stored_length,
                pending.original_length > pending.stored_length,
            );
        }
        cache.counts = Some(current);
        cache.tracking_from = None;
        cache.tracking_end = 0;
        cache.pending.clear();
    } else if let Some(cached) = cache.counts
        && cached.stored_size_bytes() >= snapshot.data_len
    {
        return Ok(cached);
    }
    cache.counts = Some(current);
    // The statistics file is advisory.  Do not make an RPC fail because an
    // NFS rename or a read-only blocks directory prevented the cache update.
    // Only publish a snapshot whose counters describe bytes that are already
    // in the captured file; concurrent appends are picked up by the next
    // flush or by a suffix scan after restart.
    if persistable.stored_size_bytes() == snapshot.data_len {
        let _ = persist_storage_compression_stats(&snapshot.stats_path, persistable);
    }
    Ok(current)
}

fn prepare_compression_scan(
    cache: &Mutex<StorageCompressionCache>,
    data_len: u64,
) -> (bool, Option<StorageCompressionCounts>) {
    let mut cache = cache.lock();
    if cache
        .counts
        .is_some_and(|cached| cached.stored_size_bytes() == data_len)
    {
        return (true, None);
    }
    let base_counts = cache
        .counts
        .filter(|cached| cached.stored_size_bytes() < data_len);
    cache.counts = None;
    cache.tracking_from = Some(data_len);
    cache.tracking_end = data_len;
    cache.pending.clear();
    (false, base_counts)
}

fn note_compressed_record_append(
    cache: &Mutex<StorageCompressionCache>,
    offset: u64,
    original_length: usize,
    stored_length: usize,
) {
    let mut cache = cache.lock();
    let original_length = u64::try_from(original_length).unwrap_or(u64::MAX);
    let stored_length = u64::try_from(stored_length).unwrap_or(u64::MAX);
    if let Some(counts) = cache.counts.as_mut() {
        if counts.stored_size_bytes() == offset {
            counts.add_record(
                original_length,
                stored_length,
                original_length > stored_length,
            );
            return;
        }
        cache.counts = None;
    }
    if cache.tracking_from.is_some() {
        if cache.tracking_end == offset {
            cache.pending.push(PendingCompressionRecord {
                original_length,
                stored_length,
            });
            cache.tracking_end = offset.saturating_add(4).saturating_add(stored_length);
        } else {
            cache.tracking_from = None;
            cache.tracking_end = 0;
            cache.pending.clear();
        }
    }
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
        let mut data_len = file.metadata()?.len();
        if !block_file_read_only
            && let Some(recovered_len) = recover_unpublished_indexed_tail(
                &mut file,
                &mut index_file,
                data_len,
                MAX_STORED_BLOCK_SIZE,
            )?
        {
            data_len = recovered_len;
        }
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
        let mut undo_data_len = undo_file.metadata()?.len();
        if let Some(recovered_len) = recover_unpublished_indexed_tail(
            &mut undo_file,
            &mut undo_index_file,
            undo_data_len,
            MAX_STORED_UNDO_SIZE,
        )? {
            undo_data_len = recovered_len;
        }
        let undo_index = match load_index(&mut undo_index_file, undo_data_len)? {
            Some(index) => index,
            None => {
                let index = scan_undo_index(&mut undo_file, xor_key, true)
                    .with_context(|| format!("scanning {}", undo_path.display()))?;
                rewrite_index(&mut undo_index_file, undo_file.metadata()?.len(), &index)?;
                index
            }
        };
        let serving_reader = BlockStoreReader::new(file.try_clone()?, index.clone(), xor_key);
        let block_compression_cache =
            Arc::new(Mutex::new(load_compression_cache(&path, data_len, &index)));
        let undo_compression_cache = Arc::new(Mutex::new(load_compression_cache(
            &directory.join("undo.dat"),
            undo_data_len,
            &undo_index,
        )));
        Ok(Self {
            path,
            file,
            replay_reader: None,
            replay_reader_cursor: 0,
            index_file,
            index,
            serving_reader,
            undo_file,
            undo_index_file,
            undo_index,
            block_data_len: data_len,
            undo_data_len,
            block_preallocated_through: data_len,
            undo_preallocated_through: undo_data_len,
            block_preallocation_enabled: !block_file_read_only,
            undo_preallocation_enabled: true,
            pending_block_data: Vec::new(),
            pending_index_data: Vec::new(),
            pending_undo_data: Vec::new(),
            pending_undo_index_data: Vec::new(),
            xor_key,
            block_file_read_only,
            allow_block_file_reopen,
            block_cache: HashMap::new(),
            block_cache_order: VecDeque::new(),
            block_cache_bytes: 0,
            block_cache_limit: 0,
            block_cache_metrics: BlockStoreCacheMetrics::default(),
            block_compression_cache,
            undo_compression_cache,
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
            None => scan_undo_index(&mut undo_file, xor_key, false)
                .with_context(|| format!("scanning {}", undo_path.display()))?,
        };

        let serving_reader = BlockStoreReader::new(file.try_clone()?, index.clone(), xor_key);
        let block_compression_cache =
            Arc::new(Mutex::new(load_compression_cache(&path, data_len, &index)));
        let undo_compression_cache = Arc::new(Mutex::new(load_compression_cache(
            &undo_path,
            undo_data_len,
            &undo_index,
        )));
        Ok(Self {
            path,
            file,
            replay_reader: None,
            replay_reader_cursor: 0,
            index_file,
            index,
            serving_reader,
            undo_file,
            undo_index_file,
            undo_index,
            block_data_len: data_len,
            undo_data_len,
            block_preallocated_through: data_len,
            undo_preallocated_through: undo_data_len,
            block_preallocation_enabled: false,
            undo_preallocation_enabled: false,
            pending_block_data: Vec::new(),
            pending_index_data: Vec::new(),
            pending_undo_data: Vec::new(),
            pending_undo_index_data: Vec::new(),
            xor_key,
            block_file_read_only: true,
            allow_block_file_reopen: false,
            block_cache: HashMap::new(),
            block_cache_order: VecDeque::new(),
            block_cache_bytes: 0,
            block_cache_limit: 0,
            block_cache_metrics: BlockStoreCacheMetrics::default(),
            block_compression_cache,
            undo_compression_cache,
        })
    }

    /// Configure the in-memory block-record cache used by the custom storage
    /// backend. Keep one eighth of `-dbcache` for decoded historical blocks;
    /// the UTXO value cache receives the other seven eighths because random
    /// prevout reads dominate IBD and newly accepted blocks are rarely read
    /// again before they leave this cache.
    pub fn configure_cache_size_mib(&mut self, mib: i64) {
        const MIN_CACHE_MIB: u64 = 4;
        const MIB: u64 = 1024 * 1024;
        let mib = u64::try_from(mib.max(0)).unwrap_or(u64::MAX);
        let bytes = mib.max(MIN_CACHE_MIB).saturating_mul(MIB);
        let bytes = usize::try_from(bytes).unwrap_or(usize::MAX);
        self.block_cache_limit = bytes / 8;
        self.trim_block_cache();
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

    fn cache_block(&mut self, hash: BlockHash, block: Arc<Block>, bytes: usize) {
        if self.block_cache_limit == 0 || bytes > self.block_cache_limit {
            return;
        }
        if let Some((cached, old_bytes)) = self.block_cache.get_mut(&hash) {
            self.block_cache_bytes = self
                .block_cache_bytes
                .saturating_sub(*old_bytes)
                .saturating_add(bytes);
            *cached = block;
            *old_bytes = bytes;
            self.trim_block_cache();
            return;
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

    fn reset_replay_reader(&mut self) {
        self.replay_reader = None;
        self.replay_reader_cursor = 0;
    }

    fn flush_pending_block_data(&mut self) -> Result<()> {
        if self.pending_block_data.is_empty() {
            return Ok(());
        }
        self.file.write_all(&self.pending_block_data)?;
        self.pending_block_data.clear();
        // The serving reader uses positional reads, so records become
        // directly readable as soon as this append buffer reaches the file.
        // Retaining decoded clones until the next durability checkpoint made
        // IBD memory grow with tens of thousands of already-written blocks.
        self.serving_reader.clear_pending();
        Ok(())
    }

    fn flush_pending_index_data(&mut self) -> Result<()> {
        if self.pending_index_data.is_empty() {
            return Ok(());
        }
        self.index_file.seek(SeekFrom::End(0))?;
        self.index_file.write_all(&self.pending_index_data)?;
        self.pending_index_data.clear();
        Ok(())
    }

    fn flush_pending_undo_data(&mut self) -> Result<()> {
        if self.pending_undo_data.is_empty() {
            return Ok(());
        }
        self.undo_file.write_all(&self.pending_undo_data)?;
        self.pending_undo_data.clear();
        Ok(())
    }

    fn flush_pending_undo_index_data(&mut self) -> Result<()> {
        if self.pending_undo_index_data.is_empty() {
            return Ok(());
        }
        self.undo_index_file.seek(SeekFrom::End(0))?;
        self.undo_index_file
            .write_all(&self.pending_undo_index_data)?;
        self.pending_undo_index_data.clear();
        Ok(())
    }

    fn flush_pending_io(&mut self) -> Result<()> {
        self.flush_pending_block_data()?;
        self.flush_pending_index_data()?;
        self.flush_pending_undo_data()?;
        self.flush_pending_undo_index_data()?;
        Ok(())
    }

    fn append_unsynced_index_entry(pending: &mut Vec<u8>, hash: BlockHash, record: Record) {
        let mut bytes = [0u8; INDEX_RECORD_SIZE as usize];
        bytes[..32].copy_from_slice(&hash.to_byte_array());
        bytes[32..40].copy_from_slice(&record.offset.to_le_bytes());
        bytes[40..44].copy_from_slice(&record.length.to_le_bytes());
        pending.extend_from_slice(&bytes);
    }

    fn persist_compression_caches(&self) {
        let stats = [
            (
                compression_stats_path(&self.path),
                self.block_data_len,
                Arc::clone(&self.block_compression_cache),
            ),
            (
                compression_stats_path(
                    &self
                        .path
                        .parent()
                        .expect("block store path has a parent")
                        .join("undo.dat"),
                ),
                self.undo_data_len,
                Arc::clone(&self.undo_compression_cache),
            ),
        ];
        for (path, data_len, cache) in stats {
            let Some(counts) = cache.lock().counts else {
                continue;
            };
            if counts.stored_size_bytes() != data_len {
                continue;
            }
            if let Err(error) = persist_storage_compression_stats(&path, counts) {
                tracing::debug!(path = %path.display(), %error, "unable to persist compression statistics");
            }
        }
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
        self.block_data_len
            .checked_add(self.undo_data_len)
            .context("block store disk usage overflowed")
    }

    pub fn data_size(&self) -> Result<u64> {
        Ok(self.block_data_len)
    }

    pub fn undo_size(&self) -> Result<u64> {
        Ok(self.undo_data_len)
    }

    /// Capture block and undo descriptors plus their current lengths for an
    /// exact header-only compression scan. The returned inspector owns cloned
    /// descriptors, allowing callers to release the chain lock before doing
    /// any filesystem work.
    pub fn compression_inspector(&mut self) -> Result<BlockStoreCompressionInspector> {
        self.flush_pending_io()?;
        let block_data_len = self.block_data_len;
        let undo_data_len = self.undo_data_len;
        let (blocks_are_cached, mut block_base_counts) =
            prepare_compression_scan(&self.block_compression_cache, block_data_len);
        let (undo_is_cached, mut undo_base_counts) =
            prepare_compression_scan(&self.undo_compression_cache, undo_data_len);
        let block_records = if blocks_are_cached {
            Vec::new()
        } else {
            let mut records = self.index.values().copied().collect::<Vec<_>>();
            if let Some(base) = block_base_counts {
                let start = base.stored_size_bytes();
                if start == 0 {
                    // Keep the complete index in this case; the empty prefix
                    // is equivalent to an uncached scan.
                } else if records.iter().any(|record| record.offset == start) {
                    records.retain(|record| record.offset >= start);
                } else {
                    // A stale sidecar can only be used at an exact record
                    // boundary.  Falling back to the complete index preserves
                    // correctness after pruning or manual file replacement.
                    block_base_counts = None;
                }
            }
            records
        };
        let undo_records = if undo_is_cached {
            Vec::new()
        } else {
            let mut records = self.undo_index.values().copied().collect::<Vec<_>>();
            if let Some(base) = undo_base_counts {
                let start = base.stored_size_bytes();
                if start == 0 {
                    // Keep the complete index in this case; the empty prefix
                    // is equivalent to an uncached scan.
                } else if records.iter().any(|record| record.offset == start) {
                    records.retain(|record| record.offset >= start);
                } else {
                    undo_base_counts = None;
                }
            }
            records
        };
        Ok(BlockStoreCompressionInspector {
            blocks: StorageCompressionSnapshot {
                file: self.file.try_clone()?,
                data_len: block_data_len,
                xor_key: self.xor_key,
                base_counts: block_base_counts,
                records: block_records,
                stats_path: compression_stats_path(&self.path),
                cache: Arc::clone(&self.block_compression_cache),
            },
            undo: StorageCompressionSnapshot {
                file: self.undo_file.try_clone()?,
                data_len: undo_data_len,
                xor_key: self.xor_key,
                base_counts: undo_base_counts,
                records: undo_records,
                stats_path: compression_stats_path(
                    &self
                        .path
                        .parent()
                        .expect("block store path has a parent")
                        .join("undo.dat"),
                ),
                cache: Arc::clone(&self.undo_compression_cache),
            },
        })
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
        self.reset_replay_reader();
        self.file = OpenOptions::new()
            .read(true)
            .append(true)
            .open(&self.path)
            .with_context(|| {
                format!("reopening block store {} for writing", self.path.display())
            })?;
        self.block_data_len = self.file.metadata()?.len();
        self.block_preallocated_through = self.block_data_len;
        self.block_preallocation_enabled = true;
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
        self.insert_prepared_with_sync(block, prepared, sync, None)
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
        self.insert_prepared_with_sync(block, prepared, true, None)
    }

    pub(crate) fn insert_prepared_unsynced(
        &mut self,
        block: &Block,
        prepared: PreparedBlockRecord,
    ) -> Result<BlockHash> {
        self.insert_prepared_with_sync(block, prepared, false, None)
    }

    pub(crate) fn insert_prepared_unsynced_shared(
        &mut self,
        block: Arc<Block>,
        prepared: PreparedBlockRecord,
    ) -> Result<BlockHash> {
        self.insert_prepared_with_sync(&block, prepared, false, Some(Arc::clone(&block)))
    }

    /// Retain a bounded decoded copy of a peer body that was stored while its
    /// parent was still missing. Headers-first IBD commonly receives a long
    /// suffix before the validation lane can connect it; without this cache,
    /// activating that suffix decodes every body from the NFS-backed append
    /// file a second time. The normal block cache already has the Core-sized
    /// `dbcache / 8` budget, so this does not create a second unbounded body
    /// store and older entries are evicted by the existing FIFO policy.
    pub(crate) fn cache_peer_block(&mut self, block: Arc<Block>) {
        self.cache_block(block.block_hash(), Arc::clone(&block), block.total_size());
    }

    fn insert_prepared_with_sync(
        &mut self,
        block: &Block,
        prepared: PreparedBlockRecord,
        sync: bool,
        shared_block: Option<Arc<Block>>,
    ) -> Result<BlockHash> {
        let hash = block.block_hash();
        if self.index.contains_key(&hash) {
            return Ok(hash);
        }
        if prepared.hash != hash {
            bail!("prepared block record does not match block")
        }
        if sync {
            self.flush_pending_io()?;
        }
        self.ensure_block_file_writable()?;
        let bytes = prepared.encoded;
        let offset = self.block_data_len;
        let length = u32::try_from(bytes.len()).context("block length does not fit u32")?;
        let record_len = u64::from(length) + 4;
        ensure_file_preallocated(
            &self.file,
            &mut self.block_preallocated_through,
            &mut self.block_preallocation_enabled,
            offset.saturating_add(record_len),
            BLOCK_PREALLOCATION_CHUNK_BYTES,
            &self.path,
        );
        if sync {
            let mut record = Vec::with_capacity(4 + bytes.len());
            record.extend_from_slice(&length.to_le_bytes());
            record.extend_from_slice(&bytes);
            self.xor_key.apply(&mut record, offset);
            self.file.write_all(&record)?;
            self.file.sync_data()?;
            persist_index_entry_with_sync(
                &mut self.index_file,
                offset + record_len,
                hash,
                Record { offset, length },
                true,
            )?;
        } else {
            let start = self.pending_block_data.len();
            self.pending_block_data.reserve(4 + bytes.len());
            self.pending_block_data
                .extend_from_slice(&length.to_le_bytes());
            self.pending_block_data.extend_from_slice(&bytes);
            self.xor_key
                .apply(&mut self.pending_block_data[start..], offset);
            Self::append_unsynced_index_entry(
                &mut self.pending_index_data,
                hash,
                Record { offset, length },
            );
            if self.pending_block_data.len() >= APPEND_BUFFER_FLUSH_BYTES {
                self.flush_pending_block_data()?;
            }
            if self.pending_index_data.len() >= APPEND_BUFFER_FLUSH_BYTES {
                self.flush_pending_index_data()?;
            }
        }
        self.block_data_len = self.block_data_len.saturating_add(record_len);
        self.index.insert(hash, Record { offset, length });
        self.serving_reader.insert(hash, Record { offset, length });
        if !sync && !self.pending_block_data.is_empty() {
            let pending = shared_block
                .as_ref()
                .map(Arc::clone)
                .unwrap_or_else(|| Arc::new(block.clone()));
            self.serving_reader.insert_pending(hash, pending);
        }
        // Core does not retain a second decoded copy of every block while
        // importing the chain.  The peer task already owns the parsed block,
        // the serving reader keeps the short append-buffer suffix available
        // to uploaders, and the durable file is the source for later reads.
        // Populating the decoded cache here would clone the complete block once per
        // IBD block and spend the block-cache budget on data that is almost
        // never read again before it is evicted.  Keep the cache for
        // synchronous inserts, where callers may immediately query the block.
        if sync {
            let cached = shared_block.unwrap_or_else(|| Arc::new(block.clone()));
            self.cache_block(hash, cached, prepared.raw_length);
        }
        note_compressed_record_append(
            &self.block_compression_cache,
            offset,
            prepared.raw_length,
            bytes.len(),
        );
        Ok(hash)
    }

    pub fn flush(&mut self) -> Result<()> {
        self.flush_pending_io()?;
        self.file.sync_data()?;
        self.undo_file.sync_data()?;
        publish_index_data_len(&mut self.index_file, self.block_data_len)?;
        publish_index_data_len(&mut self.undo_index_file, self.undo_data_len)?;
        self.persist_compression_caches();
        self.serving_reader.clear_pending();
        Ok(())
    }

    pub(crate) fn get_shared(&mut self, hash: &BlockHash) -> Result<Option<Arc<Block>>> {
        let lookup_started = Instant::now();
        self.block_cache_metrics.lookups = self.block_cache_metrics.lookups.saturating_add(1);
        if let Some(block) = self
            .block_cache
            .get(hash)
            .map(|(block, _)| Arc::clone(block))
        {
            self.block_cache_metrics.hits = self.block_cache_metrics.hits.saturating_add(1);
            self.block_cache_metrics.lookup_time += lookup_started.elapsed();
            return Ok(Some(block));
        }
        self.block_cache_metrics.misses = self.block_cache_metrics.misses.saturating_add(1);
        let Some(record) = self.index.get(hash).copied() else {
            self.block_cache_metrics.lookup_time += lookup_started.elapsed();
            return Ok(None);
        };
        self.flush_pending_io()?;
        let load_started = Instant::now();
        let bytes = read_storage_record(
            &self.file,
            record,
            self.xor_key,
            MAX_STORED_BLOCK_SIZE,
            "block",
        )?;
        self.block_cache_metrics.load_time += load_started.elapsed();
        let decode_started = Instant::now();
        let block: Block = deserialize(&bytes).context("decoding stored block")?;
        self.block_cache_metrics.decode_time += decode_started.elapsed();
        if block.block_hash() != *hash {
            bail!("stored block hash does not match block index");
        }
        let block = Arc::new(block);
        self.cache_block(*hash, Arc::clone(&block), bytes.len());
        self.block_cache_metrics.lookup_time += lookup_started.elapsed();
        Ok(Some(block))
    }

    pub fn get(&mut self, hash: &BlockHash) -> Result<Option<Block>> {
        self.get_shared(hash)
            .map(|block| block.map(|block| block.as_ref().clone()))
    }

    pub(crate) fn take_cache_metrics(&mut self) -> (BlockStoreCacheMetrics, usize, usize) {
        (
            std::mem::take(&mut self.block_cache_metrics),
            self.block_cache.len(),
            self.block_cache_bytes,
        )
    }

    /// Read one block during a forward chainstate replay.
    ///
    /// Unlike [`Self::get`], this deliberately bypasses the decoded block cache
    /// and uses a buffered sequential cursor. Replay callers walk a known
    /// active-chain path, so keeping the file cursor aligned with the next
    /// record lets the kernel/NFS client perform useful readahead instead of
    /// issuing one positional read for every block body. A discontinuity is
    /// still handled correctly by the buffered reader's seek path.
    pub(crate) fn get_for_replay(&mut self, hash: &BlockHash) -> Result<Option<Block>> {
        let Some(record) = self.index.get(hash).copied() else {
            return Ok(None);
        };
        self.flush_pending_io()?;
        if self.replay_reader.is_none() {
            let mut reader = BufReader::with_capacity(
                BLOCK_REPLAY_READ_BUFFER_BYTES,
                self.file.try_clone().context("cloning block replay file")?,
            );
            reader
                .seek(SeekFrom::Start(0))
                .context("seeking to the beginning of the block store")?;
            self.replay_reader = Some(reader);
            self.replay_reader_cursor = 0;
        }
        let bytes = read_storage_record_buffered(
            self.replay_reader
                .as_mut()
                .expect("replay reader initialized above"),
            &mut self.replay_reader_cursor,
            record,
            self.xor_key,
            MAX_STORED_BLOCK_SIZE,
            "block",
        )?;
        let block: Block = deserialize(&bytes).context("decoding stored block")?;
        if block.block_hash() != *hash {
            bail!("stored block hash does not match block index");
        }
        Ok(Some(block))
    }

    pub fn transaction_count(&mut self, hash: &BlockHash) -> Result<Option<usize>> {
        let Some(record) = self.index.get(hash).copied() else {
            return Ok(None);
        };
        self.flush_pending_io()?;
        read_block_transaction_count(&self.file, record, self.xor_key).map(Some)
    }

    /// Read a block without touching the mutable decoded cache or the seek
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
        self.flush_pending_io()?;
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

    pub fn has_undo(&self, hash: &BlockHash) -> bool {
        self.undo_index.contains_key(hash)
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
        if sync {
            self.flush_pending_io()?;
        }
        let offset = self.undo_data_len;
        let length = u32::try_from(bytes.len()).context("undo length does not fit u32")?;
        let mut record = Vec::with_capacity(4 + bytes.len());
        record.extend_from_slice(&length.to_le_bytes());
        record.extend_from_slice(&bytes);
        self.xor_key.apply(&mut record, offset);
        let record_len = u64::try_from(record.len()).context("undo record length overflowed")?;
        let undo_path = self
            .path
            .parent()
            .expect("block store path has a parent")
            .join("undo.dat");
        ensure_file_preallocated(
            &self.undo_file,
            &mut self.undo_preallocated_through,
            &mut self.undo_preallocation_enabled,
            offset.saturating_add(record_len),
            UNDO_PREALLOCATION_CHUNK_BYTES,
            &undo_path,
        );
        if sync {
            self.undo_file.write_all(&record)?;
            self.undo_file.sync_data()?;
            persist_index_entry_with_sync(
                &mut self.undo_index_file,
                offset + record_len,
                hash,
                Record { offset, length },
                true,
            )?;
        } else {
            self.pending_undo_data.extend_from_slice(&record);
            Self::append_unsynced_index_entry(
                &mut self.pending_undo_index_data,
                hash,
                Record { offset, length },
            );
            if self.pending_undo_data.len() >= APPEND_BUFFER_FLUSH_BYTES {
                self.flush_pending_undo_data()?;
            }
            if self.pending_undo_index_data.len() >= APPEND_BUFFER_FLUSH_BYTES {
                self.flush_pending_undo_index_data()?;
            }
        }
        self.undo_data_len = self.undo_data_len.saturating_add(record_len);
        self.undo_index.insert(hash, Record { offset, length });
        note_compressed_record_append(
            &self.undo_compression_cache,
            offset,
            raw_bytes.len(),
            bytes.len(),
        );
        Ok(())
    }

    pub fn hashes(&self) -> impl Iterator<Item = &BlockHash> {
        self.index.keys()
    }

    /// Read block headers in their physical append order.
    ///
    /// A reindex has no reason to walk the hash map and issue one positional
    /// read per block. Core scans its block files sequentially for the same
    /// reason: buffered sequential reads let the kernel and the storage
    /// server readahead instead of turning the reindex into hundreds of
    /// thousands of random reads. Only headers are retained, so this does not
    /// recreate a second in-memory copy of the block store.
    pub(crate) fn headers_in_file_order(&self) -> Result<Vec<(BlockHash, bitcoin::block::Header)>> {
        let mut records = self
            .index
            .iter()
            .map(|(hash, record)| (*hash, *record))
            .collect::<Vec<_>>();
        records.sort_unstable_by_key(|(_, record)| record.offset);

        let mut reader = BufReader::with_capacity(
            BLOCK_REPLAY_READ_BUFFER_BYTES,
            self.file.try_clone().context("cloning block replay file")?,
        );
        reader
            .seek(SeekFrom::Start(0))
            .context("seeking to the beginning of the block store")?;
        let mut cursor = 0u64;
        let mut headers = Vec::with_capacity(records.len());
        for (hash, record) in records {
            let bytes = read_storage_record_buffered(
                &mut reader,
                &mut cursor,
                record,
                self.xor_key,
                MAX_STORED_BLOCK_SIZE,
                "block",
            )?;
            let (header, _) = deserialize_partial::<bitcoin::block::Header>(&bytes)
                .context("decoding block header")?;
            if header.block_hash() != hash {
                bail!("stored block hash does not match block index");
            }
            headers.push((hash, header));
        }
        Ok(headers)
    }

    /// Rewrite the append-only files, retaining only the supplied records.
    /// This is used by manual pruning after the chainstate snapshot has made
    /// the retained active tip restartable without old block bodies.
    pub fn prune(
        &mut self,
        retained_blocks: &HashSet<BlockHash>,
        retained_undo: &HashSet<BlockHash>,
    ) -> Result<()> {
        self.flush_pending_io()?;
        self.ensure_block_file_writable()?;
        let block_hashes = self
            .index
            .keys()
            .copied()
            .filter(|hash| retained_blocks.contains(hash))
            .collect::<Vec<_>>();
        let block_path = self.path.clone();
        // Pruning rewrites physical offsets, so an old sidecar must never be
        // mistaken for a prefix of the replacement file after a crash.
        let _ = remove_file(compression_stats_path(&block_path));
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
        self.reset_replay_reader();
        self.block_data_len = data_len;
        self.block_preallocated_through = data_len;
        self.block_preallocation_enabled = true;
        self.pending_block_data.clear();
        self.pending_index_data.clear();
        self.index = index;
        rewrite_index(&mut self.index_file, data_len, &self.index)?;
        self.serving_reader
            .replace(self.file.try_clone()?, self.index.clone());

        let undo_path = self
            .path
            .parent()
            .context("block store has no parent directory")?
            .join("undo.dat");
        let _ = remove_file(compression_stats_path(&undo_path));
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
        self.undo_data_len = undo_data_len;
        self.undo_preallocated_through = undo_data_len;
        self.undo_preallocation_enabled = true;
        self.pending_undo_data.clear();
        self.pending_undo_index_data.clear();
        self.undo_index = undo_index;
        rewrite_index(&mut self.undo_index_file, undo_data_len, &self.undo_index)?;
        *self.block_compression_cache.lock() = StorageCompressionCache::default();
        *self.undo_compression_cache.lock() = StorageCompressionCache::default();
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

fn read_storage_record_buffered(
    reader: &mut BufReader<File>,
    cursor: &mut u64,
    record: Record,
    xor_key: XorKey,
    max_size: usize,
    kind: &str,
) -> Result<Vec<u8>> {
    if *cursor != record.offset {
        reader
            .seek(SeekFrom::Start(record.offset))
            .with_context(|| format!("seeking to stored {kind} record"))?;
        *cursor = record.offset;
    }

    let mut length_bytes = [0u8; 4];
    reader
        .read_exact(&mut length_bytes)
        .with_context(|| format!("reading stored {kind} length"))?;
    xor_key.apply(&mut length_bytes, record.offset);
    let stored_length = u32::from_le_bytes(length_bytes);
    if stored_length != record.length {
        bail!(
            "stored {kind} index disagrees with record length at offset {}",
            record.offset
        );
    }
    let stored_length =
        usize::try_from(stored_length).context("stored record length does not fit usize")?;
    if stored_length == 0 || stored_length > max_size {
        bail!("stored {kind} record is too large: {stored_length} bytes");
    }
    let mut encoded = vec![0u8; stored_length];
    reader
        .read_exact(&mut encoded)
        .with_context(|| format!("reading stored {kind} payload"))?;
    xor_key.apply(&mut encoded, record.offset.saturating_add(4));
    *cursor = record
        .offset
        .saturating_add(4)
        .saturating_add(u64::from(record.length));
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
    pending_blocks: FastHashMap<BlockHash, Vec<Txid>>,
    pending_active_locations: FastHashMap<Txid, Vec<StoredTxLocation>>,
    pending_active_hashes: HashSet<BlockHash>,
    pending_active_tip: Option<(BlockHash, u32)>,
    pending_item_count: usize,
}

/// Point-in-time active transaction-location lookup. Fjall keeps the
/// snapshot's old versions alive while the query runs; the small pending
/// overlay captures writes that have not entered Fjall yet.
pub struct ActiveTransactionLocationsQuery {
    snapshot: Snapshot,
    txids: Vec<Txid>,
    pending: FastHashMap<Txid, Vec<StoredTxLocation>>,
}

impl ActiveTransactionLocationsQuery {
    pub fn execute(self) -> Result<HashMap<Txid, Vec<StoredTxLocation>>> {
        let mut result = HashMap::with_capacity(self.txids.len());
        for txid in self.txids {
            let mut locations = self
                .snapshot
                .prefix(txid.to_byte_array())
                .map(|item| {
                    let (_, value) = item.context("scanning active transaction locations")?;
                    decode_stored_tx_location(&value)
                })
                .collect::<Result<Vec<_>>>()?;
            if let Some(pending) = self.pending.get(&txid) {
                locations.extend_from_slice(pending);
            }
            locations.sort_unstable_by_key(|location| {
                (
                    location.height,
                    location.transaction_index,
                    location.block_hash.to_byte_array(),
                )
            });
            locations.dedup();
            if !locations.is_empty() {
                result.insert(txid, locations);
            }
        }
        Ok(result)
    }
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
            pending_blocks: FastHashMap::new(),
            pending_active_locations: FastHashMap::new(),
            pending_active_hashes: HashSet::new(),
            pending_active_tip: None,
            pending_item_count: 0,
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
        if self.pending_blocks.contains_key(hash) {
            return Ok(true);
        }
        self.blocks
            .contains_key(hash.to_byte_array())
            .context("looking up transaction-index block")
    }

    pub fn hashes(&self) -> Result<Vec<BlockHash>> {
        let mut hashes = self
            .blocks
            .keys()
            .map(|key| {
                let key = key.context("scanning transaction-index block keys")?;
                let bytes: [u8; 32] = key
                    .as_ref()
                    .try_into()
                    .context("transaction-index block key has invalid length")?;
                Ok(BlockHash::from_byte_array(bytes))
            })
            .collect::<Result<Vec<_>>>()?;
        hashes.extend(self.pending_blocks.keys().copied());
        Ok(hashes)
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
        if let Some(txids) = self.pending_blocks.get(hash) {
            return Ok(Some(txids.clone()));
        }
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
        let mut locations = self
            .active_transactions
            .prefix(txid.to_byte_array())
            .map(|item| {
                let (_, value) = item.context("scanning active transaction locations")?;
                decode_stored_tx_location(&value)
            })
            .collect::<Result<Vec<_>>>()?;
        if let Some(pending) = self.pending_active_locations.get(txid) {
            locations.extend_from_slice(pending);
        }
        Ok(locations)
    }

    pub fn active_locations_query(&self, txids: &[Txid]) -> ActiveTransactionLocationsQuery {
        let mut unique = HashSet::with_capacity(txids.len());
        let txids = txids
            .iter()
            .copied()
            .filter(|txid| unique.insert(*txid))
            .collect::<Vec<_>>();
        let pending = txids
            .iter()
            .filter_map(|txid| {
                self.pending_active_locations
                    .get(txid)
                    .cloned()
                    .map(|locations| (*txid, locations))
            })
            .collect();
        ActiveTransactionLocationsQuery {
            snapshot: self.active_transactions.snapshot(),
            txids,
            pending,
        }
    }

    pub fn active_tip(&self) -> Result<Option<(BlockHash, u32)>> {
        if let Some(tip) = self.pending_active_tip {
            return Ok(Some(tip));
        }
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
        self.flush_pending_active(false)?;
        if self.contains(&hash)? {
            if sync {
                self.keyspace.persist(PersistMode::SyncData)?;
            }
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
        self.flush_pending_active(false)?;
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
        if !block_exists {
            self.pending_blocks.insert(hash, txids.to_vec());
            self.block_count = self.block_count.saturating_add(1);
            self.pending_item_count = self.pending_item_count.saturating_add(1);
        }
        if self.pending_active_hashes.insert(hash) {
            for (transaction_index, txid) in txids.iter().enumerate() {
                let location = StoredTxLocation {
                    block_hash: hash,
                    height,
                    transaction_index: u32::try_from(transaction_index)
                        .context("transaction index does not fit u32")?,
                };
                self.pending_active_locations
                    .entry(*txid)
                    .or_default()
                    .push(location);
            }
            self.pending_item_count = self.pending_item_count.saturating_add(txids.len());
        }
        self.pending_active_tip = Some((hash, height));
        if sync || self.pending_item_count >= DISK_INDEX_MAX_PENDING_ITEMS {
            self.flush_pending_active(sync)?;
        }
        Ok(())
    }

    fn flush_pending_active(&mut self, sync: bool) -> Result<()> {
        if self.pending_active_tip.is_none() && self.pending_blocks.is_empty() {
            if sync {
                self.keyspace
                    .persist(PersistMode::SyncData)
                    .context("flushing transaction index database")?;
            }
            return Ok(());
        }

        let mut batch = fjall::Batch::with_capacity(
            self.keyspace.clone(),
            self.pending_item_count.saturating_add(2),
        )
        .durability(sync.then_some(PersistMode::SyncData));
        for (hash, txids) in &self.pending_blocks {
            batch.insert(
                &self.blocks,
                hash.to_byte_array().to_vec(),
                encode_txid_list(txids)?,
            );
        }
        for (txid, locations) in &self.pending_active_locations {
            for location in locations {
                batch.insert(
                    &self.active_transactions,
                    active_transaction_key(*txid, location.height, location.transaction_index)
                        .to_vec(),
                    encode_stored_tx_location(*location),
                );
            }
        }
        batch.insert(
            &self.metadata,
            META_BLOCK_COUNT.to_vec(),
            u64::try_from(self.block_count)
                .context("transaction-index block count does not fit u64")?
                .to_le_bytes()
                .to_vec(),
        );
        if let Some((hash, height)) = self.pending_active_tip {
            let mut marker = Vec::with_capacity(36);
            marker.extend_from_slice(&hash.to_byte_array());
            marker.extend_from_slice(&height.to_le_bytes());
            batch.insert(&self.metadata, META_ACTIVE_TIP.to_vec(), marker);
        }
        batch
            .commit()
            .context("committing active transaction-index batch")?;
        self.pending_blocks.clear();
        self.pending_active_locations.clear();
        self.pending_active_hashes.clear();
        self.pending_active_tip = None;
        self.pending_item_count = 0;
        Ok(())
    }

    pub fn disconnect_active_block(
        &mut self,
        hash: BlockHash,
        txids: &[Txid],
        sync: bool,
    ) -> Result<()> {
        self.flush_pending_active(false)?;
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
        self.flush_pending_active(false)?;
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
        self.flush_pending_active(false)?;
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
        self.pending_blocks.clear();
        self.pending_active_locations.clear();
        self.pending_active_hashes.clear();
        self.pending_active_tip = None;
        self.pending_item_count = 0;
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
        self.flush_pending_active(true)
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
    // Cache warming is the only caller that reads many deltas concurrently.
    // Keep that pool owned by the store so the startup-only workers and their
    // allocator arenas can be released before steady-state IBD begins.
    read_pool: Option<rayon::ThreadPool>,
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
            read_pool: None,
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
        read_chainstate_delta_record(&self.file, *hash, record).map(Some)
    }

    /// Read a bounded batch of immutable chainstate deltas concurrently.
    /// Startup cache warming walks these records backwards and must still
    /// process them in that order, but the records themselves are independent
    /// positional reads. A small dedicated pool hides NFS latency while the
    /// caller retains control of the batch size and memory bound.
    pub(crate) fn get_many(&mut self, hashes: &[BlockHash]) -> Result<Vec<Option<Vec<u8>>>> {
        if hashes.is_empty() {
            return Ok(Vec::new());
        }
        if self.read_pool.is_none() {
            let threads = thread::available_parallelism()
                .map_or(8, usize::from)
                .saturating_mul(8)
                .clamp(16, 64);
            self.read_pool = Some(
                rayon::ThreadPoolBuilder::new()
                    .num_threads(threads)
                    .thread_name(|index| format!("chainstate-reader-{index}"))
                    .build()
                    .context("building bounded chainstate read pool")?,
            );
        }
        let read_pool = self
            .read_pool
            .as_ref()
            .expect("chainstate read pool initialized above");
        let file = self
            .file
            .try_clone()
            .context("cloning chainstate delta file for parallel read")?;
        read_pool.install(|| {
            hashes
                .par_iter()
                .map(|hash| {
                    self.index
                        .get(hash)
                        .copied()
                        .map(|record| read_chainstate_delta_record(&file, *hash, record))
                        .transpose()
                })
                .collect::<Result<Vec<_>>>()
        })
    }

    /// Release the startup-only parallel read workers after cache warming.
    /// The steady-state IBD path uses the UTXO reader pool instead.
    pub(crate) fn release_read_pool(&mut self) {
        self.read_pool = None;
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

fn read_chainstate_delta_record(file: &File, hash: BlockHash, record: Record) -> Result<Vec<u8>> {
    let bytes = read_storage_record(
        file,
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
    if stored_hash != hash {
        bail!("stored chainstate delta hash does not match its index");
    }
    decode_storage_payload(&bytes[32..], MAX_STORED_CHAINSTATE_DELTA_SIZE)
        .context("decoding compressed chainstate delta")
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
// The UTXO table is the hot random-read/write path during IBD. LZ4 keeps
// decode latency low while reducing NFS write and compaction traffic; the
// immutable block files retain their higher-ratio zstd codec separately.
// The decoded UTXO cache above the storage layer owns the IBD working set.
// Keep the lower-level cache below the combined decoded/dirty coin budget:
// point reads on the NFS-backed LSM revisit many index/value blocks across
// levels, and retaining compressed blocks is cheaper than repeating those
// reads over the network. Core's coins LevelDB cache is capped at 8 MiB, so
// this larger bound is specific to the native backend.
const UTXO_DISK_CACHE_DEFAULT_BYTES: u64 = 128 * 1024 * 1024;
const UTXO_DISK_CACHE_MIN_MIB: u64 = 128;
// Keep the compressed LSM block cache below the decoded coin cache. The
// latter already accounts for the IBD working set, while Fjall also needs
// room for memtables and compaction buffers that are not included in its
// cache-size setting. A roughly 682 MiB cache at `-dbcache=2048` retains more
// of the random-read working set without recreating the multi-gigabyte
// native-cache pressure seen with the earlier 1 GiB setting.
const UTXO_DISK_CACHE_MAX_MIB: u64 = 768;
const DISK_INDEX_DEFAULT_WRITE_BUFFER_BYTES: u64 = 64 * 1024 * 1024;
// Core's dbwrapper gives the coins LevelDB a substantial write buffer, while
// CCoinsViewDB still emits bounded 64 MiB CDBBatch writes. Keep a smaller
// native cap: Fjall may retain several partition memtables while flush and
// compaction workers run, and those allocations are outside the decoded coin
// cache accounting. The smaller service indexes retain the 64 MiB default.
const UTXO_DISK_WRITE_BUFFER_BYTES: u64 = 256 * 1024 * 1024;
// Fjall's default 64 MiB target is too small for the UTXO workload.  With
// that setting, the current lsm-tree compactor can refuse an L1->L2 repair
// once the destination contains more than 50 target-sized segments.  That is
// exactly what happened during late IBD: L1 accumulated 140 overlapping
// segments, so every point read had to probe a large fraction of the level.
// Larger runs keep the same 4 KiB point-read blocks while reducing both the
// number of files and the amount of overlap that a lookup must examine.
const UTXO_PARTITION_MEMTABLE_BYTES: u32 = 128 * 1024 * 1024;
const UTXO_PARTITION_COMPACTION_TARGET_BYTES: u32 = 128 * 1024 * 1024;
// Fresh UTXO databases use high-byte prefix partitions. A point lookup then
// probes only the LSM files for one eighth of the keyspace instead of every
// segment in the monolithic coins tree. Existing single-partition databases
// remain readable; new databases use the sharded layout.
const UTXO_SHARD_COUNT: usize = 8;
// Unsynced IBD writes are not a durability boundary: ChainState publishes its
// store-tip markers only after flushing every store. Core keeps dirty coins in
// the same byte budget as clean coins and normally flushes near 90% of that
// budget. Use an emergency entry cap only for pathological values or a bad
// cache-size setting; the normal trigger below is byte-based.
const UTXO_PENDING_EMERGENCY_ITEMS: usize = 16_777_216;
const UTXO_PENDING_DEFAULT_LIMIT_BYTES: usize = 512 * 1024 * 1024;
// Hashbrown grows a large table by allocating a second table before moving
// the entries. That transient allocation is not represented by the encoded
// coin-size estimate below. Allow the small and medium tables to grow so
// normal checkpoints amortize their writes, but flush before the first truly
// large table reaches its growth boundary; this avoids the multi-gigabyte
// rehash while keeping the early IBD path from producing tiny SST runs.
const UTXO_PENDING_CAPACITY_GUARD_MIN: usize = 8 << 20;
const UTXO_PENDING_CAPACITY_GUARD_NUMERATOR: usize = 7;
const UTXO_PENDING_CAPACITY_GUARD_DENOMINATOR: usize = 8;
// Keep a bounded window of the newest outputs after a large dirty-cache
// checkpoint. Core clears CCoinsViewCache::Flush completely; this native
// cache is an intentional read-performance extension for the common IBD
// pattern where the next blocks spend outputs from the recent suffix. Keep
// as much of the existing clean cache as fits alongside that suffix instead
// of discarding the entire decoded working set and turning the next window
// into random LSM reads over NFS. The decoded cache's normal byte budget is
// still the hard upper bound and remains separate from Fjall's compressed
// block cache. Keep an additional cap below that budget so dirty UTXO state
// can accumulate in larger batches instead of forcing a checkpoint as soon
// as the retained clean cache reaches the full decoded-cache limit.
const UTXO_POST_FLUSH_HOT_CACHE_BYTES: usize = 1_536 * 1024 * 1024;
const UTXO_POST_FLUSH_HOT_CACHE_BLOCKS: u32 = 32_768;
// A major compaction is deliberately kept out of the per-block IBD path: it
// is a blocking rewrite of the live LSM tree. Run it at a durable snapshot
// boundary once accumulated runs would otherwise make random point reads
// probe too many files. The threshold is across all UTXO shards, so a fresh
// mainnet chainstate can accumulate several normal runs per shard first.
const UTXO_MAJOR_COMPACTION_SEGMENT_THRESHOLD: usize = 128;
// Append-only service indexes remain item-batched; their values are small
// and do not share the decoded UTXO coin-cache budget.
const DISK_INDEX_MAX_PENDING_ITEMS: usize = 2_097_152;
// Fjall's atomic batch encodes every pending value before commit. Keep each
// batch bounded; a multi-million-coin shutdown batch can otherwise duplicate
// more than ten GiB of state transiently.
const DISK_INDEX_DIRTY_CHECKPOINT_ITEMS: usize = 256 * 1024 * 1024;
const UTXO_PARTITION_NAME: &str = "coins";
const UTXO_META_PARTITION_NAME: &str = "metadata";
const META_ENTRY_COUNT: &[u8] = b"entry-count";
const META_GENERATION: &[u8] = b"generation";

fn utxo_partition_options() -> PartitionCreateOptions {
    PartitionCreateOptions::default()
        .compression(CompressionType::Lz4)
        .compaction_strategy(CompactionStrategy::Leveled(Leveled {
            l0_threshold: 4,
            target_size: UTXO_PARTITION_COMPACTION_TARGET_BYTES,
            level_ratio: 10,
        }))
        .max_memtable_size(UTXO_PARTITION_MEMTABLE_BYTES)
}

/// The physical UTXO partitions behind one logical coin set. The one-element
/// form is used for pre-sharding databases; fresh stores use eight partitions
/// selected by the first byte of the serialized outpoint key.
#[derive(Clone)]
struct UtxoPartitions {
    partitions: Arc<Vec<PartitionHandle>>,
}

struct UtxoSnapshots {
    snapshots: Vec<Snapshot>,
}

impl UtxoPartitions {
    fn new(partitions: Vec<PartitionHandle>) -> Self {
        debug_assert!(!partitions.is_empty());
        Self {
            partitions: Arc::new(partitions),
        }
    }

    fn iter(&self) -> impl Iterator<Item = &PartitionHandle> {
        self.partitions.iter()
    }

    fn len(&self) -> usize {
        self.partitions.len()
    }

    fn partition_index(&self, key: &[u8]) -> usize {
        if self.partitions.len() == 1 {
            return 0;
        }
        let first = usize::from(key.first().copied().unwrap_or_default());
        first.saturating_mul(self.partitions.len()) / 256
    }

    fn partition_for_key(&self, key: &[u8]) -> &PartitionHandle {
        &self.partitions[self.partition_index(key)]
    }

    fn partition(&self, index: usize) -> &PartitionHandle {
        &self.partitions[index]
    }

    fn get(&self, key: &[u8]) -> fjall::Result<Option<fjall::Slice>> {
        self.partition_for_key(key).get(key)
    }

    fn contains_key(&self, key: &[u8]) -> fjall::Result<bool> {
        self.partition_for_key(key).contains_key(key)
    }

    fn is_empty(&self) -> fjall::Result<bool> {
        for partition in self.iter() {
            if !partition.is_empty()? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn snapshot(&self) -> UtxoSnapshots {
        UtxoSnapshots {
            snapshots: self.iter().map(PartitionHandle::snapshot).collect(),
        }
    }

    fn segment_count(&self) -> usize {
        self.iter().map(PartitionHandle::segment_count).sum()
    }
}

impl UtxoSnapshots {
    fn get(&self, key: &[u8]) -> fjall::Result<Option<fjall::Slice>> {
        if self.snapshots.len() == 1 {
            return self.snapshots[0].get(key).map_err(Into::into);
        }
        let first = usize::from(key.first().copied().unwrap_or_default());
        let index = first.saturating_mul(self.snapshots.len()) / 256;
        self.snapshots[index].get(key).map_err(Into::into)
    }
}

/// Disk-backed UTXO set with a bounded decoded-value cache.
///
/// Outpoints are stored directly in an LSM tree; only the configured database
/// block cache, write buffers, and decoded-value cache remain resident.
pub struct UtxoStore {
    path: PathBuf,
    recovery_marker_path: PathBuf,
    recovery_attempt_path: PathBuf,
    unsynced_marker_path: PathBuf,
    keyspace: Keyspace,
    coins: Arc<UtxoPartitions>,
    metadata: PartitionHandle,
    entry_count: usize,
    generation: u64,
    crash_ratio: Option<u64>,
    read_cache: Mutex<UtxoReadCache>,
    read_tuner: Arc<UtxoReadTuner>,
    pending: FastHashMap<OutPoint, PendingUtxo>,
    pending_bytes: usize,
    pending_limit_bytes: usize,
    pending_item_limit: usize,
    write_batch_limit_bytes: usize,
    dirty_items_since_sync: usize,
    dirty_item_limit: usize,
    durability_checkpoint_needed: bool,
    // True while the durable store is empty and every effective coin is
    // represented by the pending overlay.  In that phase a block can read
    // the overlay directly; a separate prefetch/deduplication pass would
    // only hash every input twice.
    pending_covers_all: bool,
    // Fjall bulk_ingest requires a tree with no active memtable, not merely a
    // tree whose logical iterator is empty.  Establish this capability once
    // when the store is opened and consume it after the first write.  In
    // particular, clear()/replace_all() leave tombstones in the active
    // memtable and must use the normal journaled path afterward.
    bulk_ingest_eligible: bool,
}

/// A lock-held view used by consensus validation. Core's coin cache is
/// protected by the chainstate lock, so repeated `AccessCoin` calls do not
/// acquire a separate mutex for every transaction input. The IBD path creates
/// this view only after all unresolved reads have been prefetched.
pub(crate) struct UtxoValidationView<'a> {
    pending: &'a FastHashMap<OutPoint, PendingUtxo>,
    read_cache: MutexGuard<'a, UtxoReadCache>,
}

impl UtxoValidationView<'_> {
    pub(crate) fn contains(&self, outpoint: &OutPoint) -> Result<bool> {
        if let Some(entry) = self.pending.get(outpoint) {
            return Ok(entry.entry.is_some());
        }
        if self.read_cache.contains_key(outpoint) {
            return Ok(true);
        }
        if self.read_cache.complete {
            return Ok(false);
        }
        bail!("UTXO validation view missed a prefetched outpoint")
    }

    pub(crate) fn with_entry<T>(
        &self,
        outpoint: &OutPoint,
        f: impl FnOnce(Option<&StoredUtxo>) -> Result<T>,
    ) -> Result<T> {
        if let Some(entry) = self.pending.get(outpoint) {
            return f(entry.entry.as_ref());
        }
        if let Some(entry) = self.read_cache.get_ref(outpoint) {
            return f(Some(entry));
        }
        if self.read_cache.complete {
            return f(None);
        }
        bail!("UTXO validation view missed a prefetched outpoint")
    }
}

/// Point-in-time UTXO lookup for a bounded set of outpoints. Entries already
/// present in the decoded cache or the unflushed overlay are copied while the
/// chain lock is held; remaining point reads use either a Fjall snapshot or
/// the current partition, depending on the caller.
enum UtxoQuerySource {
    Snapshot(UtxoSnapshots),
    Latest(Arc<UtxoPartitions>),
}

pub struct UtxoQuery {
    source: UtxoQuerySource,
    known: FastHashMap<OutPoint, Option<StoredUtxo>>,
    unresolved: Vec<OutPoint>,
    read_workers: usize,
    adaptive_tuner: Option<Arc<UtxoReadTuner>>,
}

// Keep each prefetch wave bounded so a pathological block batch cannot turn
// every input into a simultaneously allocated task/result. The result map is
// retained until validation either way; two 262k waves cover the usual large
// IBD block more efficiently than four 131k waves while keeping the decoded
// working set and the reader pool bounded.
const UTXO_PREFETCH_CHUNK: usize = 262_144;

const ADAPTIVE_UTXO_MIN_SAMPLE_LOOKUPS: usize = 16_384;
const ADAPTIVE_UTXO_MIN_SAMPLES: u32 = 4;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum UtxoReadProfile {
    Latency,
    Balanced,
    LowOverhead,
}

impl UtxoReadProfile {
    fn name(self) -> &'static str {
        match self {
            Self::Latency => "latency",
            Self::Balanced => "balanced",
            Self::LowOverhead => "low-overhead",
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct UtxoPrefetchTuning {
    pub(crate) max_blocks: usize,
    pub(crate) max_outpoints: usize,
    pub(crate) read_workers: usize,
    pub(crate) adaptive: bool,
    pub(crate) profile: &'static str,
}

struct UtxoReadTunerState {
    enabled: bool,
    profile: UtxoReadProfile,
    samples: u32,
    lookup_rate_ewma: Option<f64>,
    candidate_profile: Option<UtxoReadProfile>,
    candidate_samples: u32,
}

impl Default for UtxoReadTunerState {
    fn default() -> Self {
        Self {
            enabled: false,
            profile: UtxoReadProfile::Latency,
            samples: 0,
            lookup_rate_ewma: None,
            candidate_profile: None,
            candidate_samples: 0,
        }
    }
}

#[derive(Default)]
struct UtxoReadTuner {
    state: Mutex<UtxoReadTunerState>,
}

impl UtxoReadTuner {
    fn configure(&self, enabled: bool) {
        let mut state = self.state.lock();
        state.enabled = enabled;
        // Start with the least read amplification. Fast local storage stays
        // here, while sustained low lookup throughput promotes concurrency
        // through balanced to latency mode. This avoids issuing 64-way
        // speculative reads before there is evidence the backend needs them.
        state.profile = if enabled {
            UtxoReadProfile::LowOverhead
        } else {
            UtxoReadProfile::Latency
        };
        state.samples = 0;
        state.lookup_rate_ewma = None;
        state.candidate_profile = None;
        state.candidate_samples = 0;
    }

    fn tuning(&self) -> UtxoPrefetchTuning {
        let state = self.state.lock();
        Self::profile_tuning(state.profile, state.enabled)
    }

    fn profile_tuning(profile: UtxoReadProfile, adaptive: bool) -> UtxoPrefetchTuning {
        let latency_workers = thread::available_parallelism()
            .map_or(8, usize::from)
            .saturating_mul(8)
            .clamp(32, 64);
        let (max_blocks, max_outpoints, read_workers) = match profile {
            UtxoReadProfile::Latency => (128, 1_048_576, latency_workers),
            UtxoReadProfile::Balanced => (64, 524_288, latency_workers.saturating_div(2).max(16)),
            UtxoReadProfile::LowOverhead => (32, 262_144, latency_workers.saturating_div(4).max(8)),
        };
        UtxoPrefetchTuning {
            max_blocks,
            max_outpoints,
            read_workers,
            adaptive,
            profile: profile.name(),
        }
    }

    fn record(&self, lookups: usize, elapsed: Duration) {
        if lookups < ADAPTIVE_UTXO_MIN_SAMPLE_LOOKUPS || elapsed.is_zero() {
            return;
        }
        let lookup_rate = lookups as f64 / elapsed.as_secs_f64();
        let mut state = self.state.lock();
        if !state.enabled {
            return;
        }
        let smoothed = state
            .lookup_rate_ewma
            .map_or(lookup_rate, |previous| previous * 0.75 + lookup_rate * 0.25);
        state.lookup_rate_ewma = Some(smoothed);
        state.samples = state.samples.saturating_add(1);
        if state.samples < ADAPTIVE_UTXO_MIN_SAMPLES {
            return;
        }

        // Promote only after a substantial sustained margin, and demote at a
        // lower threshold. The gap prevents a database checkpoint or one hot
        // cache window from making the profile oscillate.
        let next = match state.profile {
            UtxoReadProfile::Latency if smoothed >= 450_000.0 => UtxoReadProfile::LowOverhead,
            UtxoReadProfile::Latency if smoothed >= 125_000.0 => UtxoReadProfile::Balanced,
            UtxoReadProfile::Balanced if smoothed < 75_000.0 => UtxoReadProfile::Latency,
            UtxoReadProfile::Balanced if smoothed >= 350_000.0 => UtxoReadProfile::LowOverhead,
            UtxoReadProfile::LowOverhead if smoothed < 200_000.0 => UtxoReadProfile::Balanced,
            profile => profile,
        };
        if next == state.profile {
            state.candidate_profile = None;
            state.candidate_samples = 0;
            return;
        }
        if state.candidate_profile == Some(next) {
            state.candidate_samples = state.candidate_samples.saturating_add(1);
        } else {
            state.candidate_profile = Some(next);
            state.candidate_samples = 1;
        }
        if state.candidate_samples < ADAPTIVE_UTXO_MIN_SAMPLES {
            return;
        }
        let previous = state.profile;
        state.profile = next;
        state.candidate_profile = None;
        state.candidate_samples = 0;
        let tuning = Self::profile_tuning(next, true);
        tracing::info!(
            previous = previous.name(),
            profile = next.name(),
            lookup_rate = smoothed,
            max_blocks = tuning.max_blocks,
            max_outpoints = tuning.max_outpoints,
            read_workers = tuning.read_workers,
            "Adaptive UTXO prefetch profile changed"
        );
    }
}

fn utxo_read_pool(workers: usize) -> Arc<rayon::ThreadPool> {
    static READ_POOLS: OnceLock<Mutex<HashMap<usize, Arc<rayon::ThreadPool>>>> = OnceLock::new();
    let pools = READ_POOLS.get_or_init(|| Mutex::new(HashMap::new()));
    let mut pools = pools.lock();
    Arc::clone(pools.entry(workers).or_insert_with(|| {
        Arc::new(
            rayon::ThreadPoolBuilder::new()
                .num_threads(workers)
                .thread_name(move |index| format!("utxo-reader-{workers}-{index}"))
                .build()
                .expect("building bounded UTXO read pool"),
        )
    }))
}

impl UtxoQuery {
    pub fn unresolved_len(&self) -> usize {
        self.unresolved.len()
    }

    pub fn execute(self) -> Result<FastHashMap<OutPoint, StoredUtxo>> {
        let UtxoQuery {
            source,
            known,
            unresolved,
            read_workers,
            adaptive_tuner,
        } = self;
        let unresolved_len = unresolved.len();
        let started = Instant::now();
        let mut entries = FastHashMap::with_capacity(known.len() + unresolved.len());
        for (outpoint, entry) in known {
            if let Some(entry) = entry {
                entries.insert(outpoint, entry);
            }
        }
        entries.extend(Self::execute_unresolved_values(
            &source,
            unresolved,
            read_workers,
        )?);
        if let Some(tuner) = adaptive_tuner {
            tuner.record(unresolved_len, started.elapsed());
        }
        Ok(entries)
    }

    /// Load only the values that were absent from the decoded cache when the
    /// query was created. IBD can install these values directly in the
    /// persistent cache before validation; materializing already-cached coins
    /// in a temporary per-block map would otherwise clone every `TxOut` and
    /// retain a second allocation until the block finishes.
    pub fn execute_unresolved(self) -> Result<FastHashMap<OutPoint, StoredUtxo>> {
        let UtxoQuery {
            source,
            unresolved,
            read_workers,
            adaptive_tuner,
            ..
        } = self;
        let unresolved_len = unresolved.len();
        let started = Instant::now();
        let entries = Self::execute_unresolved_values(&source, unresolved, read_workers)?;
        if let Some(tuner) = adaptive_tuner {
            tuner.record(unresolved_len, started.elapsed());
        }
        Ok(entries)
    }

    /// Decode unresolved coins in bounded batches for the current block. The
    /// values are kept in one block-local map because every successful miss
    /// is immediately spent by the block; inserting them into the persistent
    /// cache first only creates a second copy which Core removes again during
    /// `SpendCoin`.
    pub fn seed_unresolved_into(self) -> Result<FastHashMap<OutPoint, Option<StoredUtxo>>> {
        let UtxoQuery {
            source,
            unresolved,
            read_workers,
            adaptive_tuner,
            ..
        } = self;
        // Keep negative reads in the same map as successful reads. A block
        // prefetch can be larger than the decoded cache; retaining this
        // bounded fallback keeps validation independent of later evictions.
        // Core's cache has the same fallback relationship to its DB view.
        let mut prefetched = FastHashMap::with_capacity(unresolved.len());
        let unresolved_len = unresolved.len();
        let started = Instant::now();
        for chunk in unresolved.chunks(UTXO_PREFETCH_CHUNK) {
            let loaded = Self::load_unresolved(&source, chunk, read_workers)?;
            for (outpoint, entry) in loaded {
                prefetched.insert(outpoint, entry);
            }
        }
        if let Some(tuner) = adaptive_tuner {
            tuner.record(unresolved_len, started.elapsed());
        }
        Ok(prefetched)
    }

    fn execute_unresolved_values(
        source: &UtxoQuerySource,
        unresolved: Vec<OutPoint>,
        read_workers: usize,
    ) -> Result<FastHashMap<OutPoint, StoredUtxo>> {
        let entries = FastHashMap::with_capacity(unresolved.len());
        let loaded = Self::load_unresolved(source, &unresolved, read_workers)?;
        Ok(loaded
            .into_iter()
            .fold(entries, |mut entries, (outpoint, entry)| {
                if let Some(entry) = entry {
                    entries.insert(outpoint, entry);
                }
                entries
            }))
    }

    fn load_unresolved(
        source: &UtxoQuerySource,
        unresolved: &[OutPoint],
        read_workers: usize,
    ) -> Result<Vec<(OutPoint, Option<StoredUtxo>)>> {
        // Point reads are independent and storage latency dominates cache
        // misses during IBD. The peer path uses the current partition,
        // matching Core's latest-value LevelDB Get and avoiding Fjall's
        // slower sequence-number lookup. General callers can still request
        // the snapshot variant for a coherent point-in-time view.
        //
        // Keep substantially more outstanding reads than hardware threads:
        // on the NFS chainstate used for IBD, a worker spends most of its time
        // waiting for a bloom/index/value-block read.  Sixty-four workers is
        // enough to keep the remote store busy on the current 8-core host,
        // while avoiding the allocator/thread pressure of larger pools.
        let read_pool = utxo_read_pool(read_workers);
        read_pool.install(|| {
            unresolved
                .par_iter()
                .map(|outpoint| {
                    let key = encode_outpoint(outpoint);
                    let bytes = match source {
                        UtxoQuerySource::Snapshot(snapshot) => {
                            snapshot.get(&key).context("reading UTXO value")?
                        }
                        UtxoQuerySource::Latest(coins) => {
                            coins.get(&key).context("reading UTXO value")?
                        }
                    };
                    let entry = bytes.map(|bytes| decode_stored_utxo(&bytes)).transpose()?;
                    Ok((*outpoint, entry))
                })
                .collect::<Result<Vec<_>>>()
        })
    }
}

impl UtxoStore {
    pub fn open(directory: impl AsRef<Path>) -> Result<Self> {
        Self::open_with_cache(directory, UTXO_DISK_CACHE_DEFAULT_BYTES)
    }

    /// Select the explicit Fjall block-cache budget for the configured
    /// `-dbcache` value. Core's coins LevelDB cache is small because the
    /// operating system page cache supplies the rest of its read locality;
    /// the native store cannot rely on that behavior consistently for the
    /// random point reads produced by an NFS-backed IBD. Keep the decoded
    /// coin cache's Core-style budget separate, but scale this lower-level
    /// cache enough to retain the hot LSM index/value blocks.
    pub(crate) fn recommended_disk_cache_bytes(storage_cache_mib: Option<i64>) -> u64 {
        let cache_mib = storage_cache_mib
            .and_then(|mib| u64::try_from(mib.max(0)).ok())
            .unwrap_or(UTXO_DISK_CACHE_MIN_MIB);
        cache_mib
            .saturating_div(3)
            .clamp(UTXO_DISK_CACHE_MIN_MIB, UTXO_DISK_CACHE_MAX_MIB)
            .saturating_mul(1024 * 1024)
    }

    pub fn open_with_cache(directory: impl AsRef<Path>, cache_bytes: u64) -> Result<Self> {
        let directory = directory.as_ref();
        create_dir_all(directory)
            .with_context(|| format!("creating UTXO store {}", directory.display()))?;
        let path = directory.join("coins");
        let legacy_partition_path = path.join("partitions").join(UTXO_PARTITION_NAME);
        let sharded_partition_exists = (0..UTXO_SHARD_COUNT).any(|index| {
            path.join("partitions")
                .join(format!("{UTXO_PARTITION_NAME}-{index:02}"))
                .exists()
        });
        // A logically empty Fjall partition may still contain active
        // tombstones after a clear or a prior delete cycle.  Only a keyspace
        // that did not exist before this open is eligible for bulk_ingest;
        // this keeps the one-shot path safe across restarts as well. New
        // keyspaces are opened with eight prefix partitions; an existing
        // legacy keyspace stays on its single partition until explicitly
        // rebuilt.
        let keyspace_was_new = !legacy_partition_path.exists() && !sharded_partition_exists;
        let recovery_marker_path = directory.join("utxos.recovery.pending");
        let unsynced_marker_path = directory.join("utxos.unsynced.pending");
        // Unsynced chunk commits are protected by this marker. A process or
        // power failure may leave an arbitrary prefix of those chunks in the
        // journal, so discard that derived index and let ChainState replay
        // the durable block prefix instead of trusting a mixed generation.
        if unsynced_marker_path.exists() {
            match std::fs::remove_dir_all(&path) {
                Ok(()) => {}
                Err(error) if error.kind() == ErrorKind::NotFound => {}
                Err(error) => return Err(error).context("discarding interrupted UTXO database"),
            }
            remove_file(&unsynced_marker_path)
                .context("removing interrupted unsynced UTXO marker")?;
        }
        // Fjall's per-worker flush/compaction buffers are independent of the
        // decoded UTXO cache budget. Cap the worker count so a high-core host
        // cannot multiply the partition memtable footprint into several GiB
        // during IBD; script validation and UTXO reads have their own larger
        // CPU pools.
        let storage_workers = thread::available_parallelism()
            .map_or(2, usize::from)
            .clamp(2, 4);
        let keyspace = FjallConfig::new(&path)
            .cache_size(cache_bytes.max(1024 * 1024))
            .max_write_buffer_size(UTXO_DISK_WRITE_BUFFER_BYTES)
            .flush_workers(storage_workers)
            // Core's LevelDB chainstate runs one background compaction at a
            // time. Multiple concurrent Fjall compactions compete with the
            // random UTXO point reads on NFS and, in a controlled experiment,
            // reduced warm IBD throughput despite shortening one compaction.
            .compaction_workers(1)
            .manual_journal_persist(true)
            .open()
            .with_context(|| format!("opening disk-backed UTXO database {}", path.display()))?;
        let coins = if legacy_partition_path.exists() {
            vec![
                keyspace
                    .open_partition(UTXO_PARTITION_NAME, utxo_partition_options())
                    .context("opening legacy UTXO partition")?,
            ]
        } else {
            (0..UTXO_SHARD_COUNT)
                .map(|index| {
                    let name = format!("{UTXO_PARTITION_NAME}-{index:02}");
                    keyspace
                        .open_partition(&name, utxo_partition_options())
                        .with_context(|| format!("opening UTXO partition {name}"))
                })
                .collect::<Result<Vec<_>>>()?
        };
        let coins = Arc::new(UtxoPartitions::new(coins));
        let metadata = keyspace
            .open_partition(
                UTXO_META_PARTITION_NAME,
                PartitionCreateOptions::default().compression(CompressionType::None),
            )
            .context("opening UTXO metadata partition")?;
        let entry_count = read_usize_metadata(&metadata, META_ENTRY_COUNT)?.unwrap_or(0);
        let partition_empty = entry_count == 0 && coins.is_empty()?;
        if entry_count == 0 && !partition_empty {
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
        let read_cache = UtxoReadCache {
            complete: entry_count == 0,
            ..UtxoReadCache::default()
        };
        // A newly created empty store is already a complete cache. Every
        // subsequent pending mutation is consulted before the cache and is
        // folded into it at flush, so fresh IBD can answer BIP30's many
        // negative existence checks without one LSM lookup per transaction
        // output. Any capacity eviction clears this invariant in `trim`.
        Ok(Self {
            recovery_marker_path,
            recovery_attempt_path: directory.join("utxos.recovery.attempted"),
            unsynced_marker_path,
            path,
            keyspace,
            coins,
            metadata,
            entry_count,
            generation,
            crash_ratio: None,
            read_cache: Mutex::new(read_cache),
            read_tuner: Arc::new(UtxoReadTuner::default()),
            pending: FastHashMap::new(),
            pending_bytes: 0,
            pending_limit_bytes: UTXO_PENDING_DEFAULT_LIMIT_BYTES,
            pending_item_limit: UTXO_PENDING_EMERGENCY_ITEMS,
            write_batch_limit_bytes: DISK_INDEX_DEFAULT_WRITE_BUFFER_BYTES as usize,
            dirty_items_since_sync: 0,
            dirty_item_limit: DISK_INDEX_DIRTY_CHECKPOINT_ITEMS,
            durability_checkpoint_needed: false,
            pending_covers_all: entry_count == 0,
            bulk_ingest_eligible: keyspace_was_new && partition_empty,
        })
    }

    pub fn configure_crash_ratio(&mut self, ratio: Option<u64>) {
        self.crash_ratio = ratio.filter(|ratio| *ratio > 0);
    }

    pub(crate) fn configure_adaptive_prefetch(&self, enabled: bool) {
        self.read_tuner.configure(enabled);
        let tuning = self.read_tuner.tuning();
        tracing::info!(
            enabled,
            profile = tuning.profile,
            max_blocks = tuning.max_blocks,
            max_outpoints = tuning.max_outpoints,
            read_workers = tuning.read_workers,
            "Configured adaptive UTXO prefetch"
        );
    }

    pub(crate) fn prefetch_tuning(&self) -> UtxoPrefetchTuning {
        self.read_tuner.tuning()
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

    fn mark_unsynced_pending(&self) -> Result<()> {
        if self.unsynced_marker_path.exists() {
            return Ok(());
        }
        let mut marker = OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(&self.unsynced_marker_path)?;
        marker.write_all(b"discard UTXO database after unclean shutdown\n")?;
        marker.sync_data()?;
        Ok(())
    }

    fn clear_unsynced_pending(&self) -> Result<()> {
        match remove_file(&self.unsynced_marker_path) {
            Ok(()) => Ok(()),
            Err(error) if error.kind() == ErrorKind::NotFound => Ok(()),
            Err(error) => Err(error.into()),
        }
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

    /// Scale the decoded coin cache and dirty-coin checkpoint to Core's
    /// cache-accounting rules. The two maps mostly hold disjoint outpoints
    /// during IBD: uncommitted creations remain in `pending`, while the read
    /// cache supplies older prevouts. Core reserves only 2 MiB for the block
    /// tree DB and 8 MiB for the coins DB, then permits unused mempool space to
    /// be used by the coin cache. Keeping that space available is important on
    /// high-latency storage because an early flush discards the IBD working
    /// set and turns subsequent spends into random point reads.
    pub fn configure_cache_size_mib(&mut self, mib: i64) {
        self.configure_cache_size_mib_with_mempool(mib, 0);
    }

    pub fn configure_cache_size_mib_with_mempool(&mut self, mib: i64, max_mempool_bytes: usize) {
        const MIN_CACHE_MIB: u64 = 4;
        const MIB: u64 = 1024 * 1024;
        const MAX_BLOCK_DB_CACHE_BYTES: u64 = 2 * MIB;
        const MAX_COINS_DB_CACHE_BYTES: u64 = 8 * MIB;
        let mib = u64::try_from(mib.max(0)).unwrap_or(u64::MAX);
        let total_bytes = mib.max(MIN_CACHE_MIB).saturating_mul(MIB);
        let block_tree_cache = (total_bytes / 8).min(MAX_BLOCK_DB_CACHE_BYTES);
        let after_block_tree = total_bytes.saturating_sub(block_tree_cache);
        let coins_db_cache = (after_block_tree / 2).min(MAX_COINS_DB_CACHE_BYTES);
        let coins_cache = total_bytes
            .saturating_sub(block_tree_cache)
            .saturating_sub(coins_db_cache);
        // Core's GetCoinsCacheSizeState adds unused mempool capacity to the
        // coin budget. The node passes its configured maximum here; the
        // actual mempool usage is charged separately by the node, so only the
        // configured headroom is added for the IBD working-set limit.
        let total_coin_budget =
            coins_cache.saturating_add(u64::try_from(max_mempool_bytes).unwrap_or(u64::MAX));
        let limit = usize::try_from(total_coin_budget).unwrap_or(usize::MAX);
        self.read_cache.lock().configure_limit(limit);
        // Match validation.cpp's `GetCoinsCacheSizeState` large-cache
        // threshold: Core flushes at max(90% of the total coin budget,
        // total budget - 10 MiB), not at a flat 90%.  The latter leaves a
        // sizeable part of dbcache unused and causes avoidable full-cache
        // checkpoints during IBD.
        let ten_mib = usize::try_from(10 * MIB).unwrap_or(usize::MAX);
        self.pending_limit_bytes = limit
            .saturating_mul(9)
            .checked_div(10)
            .unwrap_or(0)
            .max(limit.saturating_sub(ten_mib));
    }

    /// Bound each Fjall batch to the same order of magnitude as Core's
    /// `CCoinsViewDB::BatchWrite` batches.  Keeping the bound on encoded
    /// values avoids building a multi-gigabyte temporary allocation when a
    /// large dirty-coin checkpoint is reached.
    pub fn configure_write_batch_size_bytes(&mut self, bytes: i64) {
        self.write_batch_limit_bytes = usize::try_from(bytes.max(1)).unwrap_or(usize::MAX);
    }

    pub fn needs_durability_checkpoint(&self) -> bool {
        self.durability_checkpoint_needed
    }

    /// New outputs populate the decoded cache as they are connected.  A full
    /// startup scan would defeat the disk-backed design, so this store does
    /// not materialize the UTXO set merely to warm it.
    pub fn warm_cache(&self) -> Result<(usize, usize)> {
        let cache = self.read_cache.lock();
        Ok((cache.len(), cache.bytes))
    }

    pub fn cache_capacity_bytes(&self) -> usize {
        self.read_cache.lock().limit
    }

    pub fn validation_view_is_complete(&self) -> bool {
        self.pending_covers_all || self.read_cache.lock().complete
    }

    pub fn cache_stats(&self) -> (usize, usize) {
        let cache = self.read_cache.lock();
        (cache.len(), cache.bytes)
    }

    pub fn pending_stats(&self) -> (usize, usize, usize, usize) {
        let cache = self.read_cache.lock();
        (
            self.pending.len(),
            self.pending_bytes,
            cache.bytes,
            self.pending_limit_bytes,
        )
    }

    fn set_pending(&mut self, outpoint: OutPoint, entry: Option<StoredUtxo>, fresh: bool) {
        let value = PendingUtxo { entry, fresh };
        let new_bytes = pending_utxo_bytes(value.entry.as_ref());
        match self.pending.entry(outpoint) {
            hashbrown::hash_map::Entry::Occupied(mut occupied) => {
                let previous = std::mem::replace(occupied.get_mut(), value);
                self.pending_bytes = self
                    .pending_bytes
                    .saturating_sub(pending_utxo_bytes(previous.entry.as_ref()))
                    .saturating_add(new_bytes);
            }
            hashbrown::hash_map::Entry::Vacant(vacant) => {
                vacant.insert(value);
                self.pending_bytes = self.pending_bytes.saturating_add(new_bytes);
            }
        }
    }

    fn remove_pending(&mut self, outpoint: &OutPoint) {
        if let Some(previous) = self.pending.remove(outpoint) {
            self.pending_bytes = self
                .pending_bytes
                .saturating_sub(pending_utxo_bytes(previous.entry.as_ref()));
        }
    }

    /// Populate the decoded cache with the complete UTXO set when a
    /// conservative size estimate fits the configured cache. Sequential LSM
    /// iteration is substantially cheaper than rediscovering the same coins
    /// through random prevout reads after a mid-IBD restart.
    pub fn warm_complete_cache_if_fits(&self) -> Result<Option<(usize, usize)>> {
        // The cache's accounting includes fixed outpoint/value/container
        // overhead and script bytes; live mainnet sets average about 160
        // bytes per resident coin in this representation.
        // Leave a small margin while allowing the final trim to enforce the
        // exact byte limit if a particular UTXO set has larger scripts.
        const ESTIMATED_CACHE_BYTES_PER_COIN: usize = 160;
        let mut cache = self.read_cache.lock();
        if self
            .entry_count
            .saturating_mul(ESTIMATED_CACHE_BYTES_PER_COIN)
            > cache.limit
        {
            return Ok(None);
        }
        cache.clear();
        cache.reserve(self.entry_count);
        for partition in self.coins.iter() {
            for item in partition.iter() {
                let (key, value) = item.context("scanning UTXO database for cache warming")?;
                cache.insert_stationary(decode_outpoint(&key)?, decode_stored_utxo(&value)?);
            }
        }
        // Startup recovery can connect a durable block suffix without
        // immediately flushing its UTXO batch. The pending map is the
        // authoritative overlay on the Fjall partition, so fold it into the
        // sequential warm just as `contains` and `get` do. Requiring the
        // overlay to be empty incorrectly made an otherwise complete cache
        // fall through to one random LSM lookup for every negative BIP30
        // output check after a restart.
        for (outpoint, entry) in &self.pending {
            if let Some(entry) = entry.entry.as_ref() {
                cache.insert_stationary(*outpoint, entry.clone());
            } else {
                cache.remove(outpoint);
            }
        }
        cache.trim();
        cache.complete = cache.len() == self.entry_count;
        Ok(Some((cache.len(), cache.bytes)))
    }

    /// Seed consensus-validated current coins into the decoded read cache.
    /// Callers provide oldest-to-newest entries so FIFO eviction retains the
    /// most recently created outputs when the configured byte limit is hit.
    pub fn seed_cache<I>(&self, entries: I) -> (usize, usize)
    where
        I: IntoIterator<Item = (OutPoint, StoredUtxo)>,
    {
        let mut cache = self.read_cache.lock();
        for (outpoint, entry) in entries {
            // A block prefetch contains both disk misses and values already
            // found in the decoded cache. Do not turn every cache hit into a
            // new FIFO generation; Core's coin cache keeps the existing
            // resident entry without manufacturing duplicate eviction work.
            if cache.contains_key(&outpoint) {
                continue;
            }
            cache.insert(outpoint, entry);
        }
        (cache.len(), cache.bytes)
    }

    /// Fill otherwise unused decoded-cache capacity with a sequential sample
    /// of the current UTXO set. Restarted IBD nodes may have outgrown a
    /// complete cache and may not have a recent delta suffix to seed from;
    /// leaving the cache empty in that case turns every prevout into a random
    /// LSM read. Keep one eighth free for newly connected outputs.
    pub fn warm_partial_cache(&self, target_bytes: usize) -> Result<(usize, usize)> {
        let mut cache = self.read_cache.lock();
        let target_bytes = target_bytes.min(cache.limit);
        if cache.bytes >= target_bytes {
            return Ok((cache.len(), cache.bytes));
        }
        for partition in self.coins.iter() {
            for item in partition.iter() {
                if cache.bytes >= target_bytes {
                    break;
                }
                let (key, value) =
                    item.context("scanning UTXO database for partial cache warming")?;
                let outpoint = decode_outpoint(&key)?;
                if self.pending.contains_key(&outpoint) || cache.contains_key(&outpoint) {
                    continue;
                }
                cache.insert_stationary(outpoint, decode_stored_utxo(&value)?);
            }
            if cache.bytes >= target_bytes {
                break;
            }
        }
        cache.complete = false;
        Ok((cache.len(), cache.bytes))
    }

    pub fn contains(&self, outpoint: &OutPoint) -> Result<bool> {
        if let Some(entry) = self.pending.get(outpoint) {
            return Ok(entry.entry.is_some());
        }
        let read_cache = self.read_cache.lock();
        if read_cache.contains_key(outpoint) {
            return Ok(true);
        }
        if read_cache.complete {
            return Ok(false);
        }
        drop(read_cache);
        self.coins
            .contains_key(&encode_outpoint(outpoint))
            .context("looking up UTXO key")
    }

    pub fn disk_usage(&self) -> Result<u64> {
        // Partition sizes exclude Fjall's active journal. Fresh and
        // write-heavy chainstates can therefore have a substantial physical
        // footprint while both partitions still report zero. Core's
        // `disk_size` describes the whole UTXO database, so include the
        // keyspace journal as well as all partition tables.
        Ok(self.keyspace.disk_space())
    }

    pub fn get(&self, outpoint: &OutPoint) -> Result<Option<StoredUtxo>> {
        self.with_entry(outpoint, |entry| Ok(entry.cloned()))
    }

    pub(crate) fn with_validation_view<T>(
        &self,
        f: impl FnOnce(&UtxoValidationView<'_>) -> Result<T>,
    ) -> Result<T> {
        let read_cache = self.read_cache.lock();
        let view = UtxoValidationView {
            pending: &self.pending,
            read_cache,
        };
        f(&view)
    }

    /// Borrow a decoded coin while the cache lock is held. Consensus
    /// validation uses this form to match Core's `CCoinsViewCache::AccessCoin`
    /// semantics and avoid allocating a second `TxOut` for every input.
    pub fn with_entry<T>(
        &self,
        outpoint: &OutPoint,
        f: impl FnOnce(Option<&StoredUtxo>) -> Result<T>,
    ) -> Result<T> {
        if let Some(entry) = self.pending.get(outpoint) {
            return f(entry.entry.as_ref());
        }
        let read_cache = self.read_cache.lock();
        if let Some(entry) = read_cache.get_ref(outpoint) {
            return f(Some(entry));
        }
        if read_cache.complete {
            return f(None);
        }
        drop(read_cache);
        let Some(bytes) = self
            .coins
            .get(&encode_outpoint(outpoint))
            .context("reading UTXO value")?
        else {
            return f(None);
        };
        let entry = decode_stored_utxo(&bytes)?;
        let mut read_cache = self.read_cache.lock();
        if read_cache.limit == 0 || read_cache_utxo_bytes(&entry) > read_cache.limit {
            return f(Some(&entry));
        }
        read_cache.insert(*outpoint, entry);
        f(read_cache.get_ref(outpoint))
    }

    pub fn query(&self, outpoints: &[OutPoint]) -> UtxoQuery {
        let mut unique = FastHashSet::with_capacity(outpoints.len());
        let mut known = FastHashMap::with_capacity(outpoints.len());
        let mut unresolved = Vec::new();
        let read_cache = self.read_cache.lock();
        for outpoint in outpoints {
            if !unique.insert(*outpoint) {
                continue;
            }
            if let Some(entry) = self.pending.get(outpoint) {
                known.insert(*outpoint, entry.entry.clone());
            } else if let Some(entry) = read_cache.get(outpoint) {
                known.insert(*outpoint, Some(entry));
            } else if read_cache.complete {
                known.insert(*outpoint, None);
            } else {
                unresolved.push(*outpoint);
            }
        }
        drop(read_cache);
        UtxoQuery {
            source: UtxoQuerySource::Snapshot(self.coins.snapshot()),
            known,
            unresolved,
            read_workers: UtxoReadTuner::profile_tuning(UtxoReadProfile::Latency, false)
                .read_workers,
            adaptive_tuner: None,
        }
    }

    /// Build the IBD prefetch query without cloning cache hits. The general
    /// `query` API must return owned known values for callers that materialize
    /// the result, but block validation reads those values directly from the
    /// shared cache and only needs the unresolved outpoints.
    pub fn query_unresolved(&self, outpoints: &[OutPoint]) -> UtxoQuery {
        let mut unresolved = Vec::new();
        let read_cache = self.read_cache.lock();
        for outpoint in outpoints {
            if self.pending.contains_key(outpoint)
                || read_cache.contains_key(outpoint)
                || read_cache.complete
            {
                continue;
            }
            unresolved.push(*outpoint);
        }
        drop(read_cache);
        // Fjall's point lookup walks a bloom filter, index block, and value
        // block for each miss. Core's LevelDB path gets much of this locality
        // from its block cache, but the Rust query starts with transaction
        // order, which is effectively random in the UTXO key space. Sorting
        // the unresolved keys once lets adjacent reads reuse those lower
        // layers without changing validation order: callers consume the
        // query as a map keyed by OutPoint. Sort by the bytes Fjall actually
        // indexes (txid followed by little-endian vout), rather than by
        // OutPoint's Rust ordering, so the locality optimization remains
        // correct if the in-memory ordering ever changes.
        unresolved.sort_unstable_by(|left, right| {
            left.txid
                .as_byte_array()
                .cmp(right.txid.as_byte_array())
                .then_with(|| left.vout.to_le_bytes().cmp(&right.vout.to_le_bytes()))
        });
        // Sorting gives us de-duplication without a second hash table. This
        // preserves the invalid-block validation path: repeated inputs still
        // reach consensus validation, while the storage layer performs one
        // point read for the shared outpoint.
        unresolved.dedup();
        let tuning = self.read_tuner.tuning();
        UtxoQuery {
            // Peer IBD owns the chain writer for the whole query/validation
            // sequence, so no other UTXO mutation can race these reads. Use
            // the normal latest-value path just like Core's CCoinsViewDB.
            source: UtxoQuerySource::Latest(self.coins.clone()),
            known: FastHashMap::new(),
            unresolved,
            read_workers: tuning.read_workers,
            adaptive_tuner: tuning.adaptive.then(|| Arc::clone(&self.read_tuner)),
        }
    }

    pub fn entries(&self) -> Result<Vec<(OutPoint, StoredUtxo)>> {
        let mut entries = FastHashMap::new();
        for partition in self.coins.iter() {
            for item in partition.iter() {
                let (key, value) = item.context("scanning UTXO database")?;
                entries.insert(decode_outpoint(&key)?, decode_stored_utxo(&value)?);
            }
        }
        for (outpoint, entry) in &self.pending {
            if let Some(entry) = entry.entry.as_ref() {
                entries.insert(*outpoint, entry.clone());
            } else {
                entries.remove(outpoint);
            }
        }
        let mut entries = entries.into_iter().collect::<Vec<_>>();
        entries.sort_unstable_by_key(|(outpoint, _)| encode_outpoint(outpoint));
        Ok(entries)
    }

    /// Visit the effective UTXO set in serialized outpoint order without
    /// materializing the whole database.  The ordinary `entries` method is
    /// useful to callers that need ownership, but using it for statistics on
    /// mainnet would allocate one decoded value for every live coin before a
    /// second sort allocation.
    pub fn for_each_entry_sorted<F>(&self, mut callback: F) -> Result<()>
    where
        F: FnMut(OutPoint, &StoredUtxo) -> Result<()>,
    {
        // Fjall partitions cover contiguous first-byte ranges of the
        // serialized outpoint key. Sort only the pending overlay, then merge
        // each small overlay shard with its on-disk partition. This preserves
        // the same ordering as `entries` while keeping decoded disk values
        // alive for one callback at a time.
        let mut pending_by_partition = (0..self.coins.len())
            .map(|_| Vec::<OutPoint>::new())
            .collect::<Vec<_>>();
        for outpoint in self.pending.keys().copied() {
            let key = encode_outpoint(&outpoint);
            let partition = self.coins.partition_index(&key);
            pending_by_partition[partition].push(outpoint);
        }
        for pending in &mut pending_by_partition {
            pending.sort_unstable_by_key(encode_outpoint);
        }

        for (partition_index, partition) in self.coins.iter().enumerate() {
            let pending = &pending_by_partition[partition_index];
            let mut pending_index = 0usize;
            let mut disk_iter = partition.iter();
            let mut disk_item = disk_iter
                .next()
                .transpose()
                .context("scanning UTXO database")?;

            loop {
                let Some(pending_outpoint) = pending.get(pending_index).copied() else {
                    let Some((key, value)) = disk_item.take() else {
                        break;
                    };
                    let outpoint = decode_outpoint(&key)?;
                    // An overlay key in this partition would compare equal
                    // above, so a disk-only value can be emitted directly.
                    let entry = decode_stored_utxo(&value)?;
                    callback(outpoint, &entry)?;
                    disk_item = disk_iter
                        .next()
                        .transpose()
                        .context("scanning UTXO database")?;
                    continue;
                };
                let pending_key = encode_outpoint(&pending_outpoint);
                let Some((disk_key, _)) = disk_item.as_ref() else {
                    for outpoint in &pending[pending_index..] {
                        if let Some(entry) = self
                            .pending
                            .get(outpoint)
                            .and_then(|pending| pending.entry.as_ref())
                        {
                            callback(*outpoint, entry)?;
                        }
                    }
                    break;
                };

                match disk_key.as_ref().cmp(pending_key.as_ref()) {
                    std::cmp::Ordering::Less => {
                        let (key, value) = disk_item.take().expect("disk item was present");
                        let outpoint = decode_outpoint(&key)?;
                        let entry = decode_stored_utxo(&value)?;
                        callback(outpoint, &entry)?;
                        disk_item = disk_iter
                            .next()
                            .transpose()
                            .context("scanning UTXO database")?;
                    }
                    std::cmp::Ordering::Equal => {
                        if let Some(entry) = self
                            .pending
                            .get(&pending_outpoint)
                            .and_then(|pending| pending.entry.as_ref())
                        {
                            callback(pending_outpoint, entry)?;
                        }
                        pending_index = pending_index.saturating_add(1);
                        disk_item = disk_iter
                            .next()
                            .transpose()
                            .context("scanning UTXO database")?;
                    }
                    std::cmp::Ordering::Greater => {
                        if let Some(entry) = self
                            .pending
                            .get(&pending_outpoint)
                            .and_then(|pending| pending.entry.as_ref())
                        {
                            callback(pending_outpoint, entry)?;
                        }
                        pending_index = pending_index.saturating_add(1);
                    }
                }
            }
        }
        Ok(())
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

    /// Apply a validated fresh-output batch by taking ownership of its
    /// decoded coins. The chain validator has already built these values, so
    /// cloning every output into the pending overlay only to satisfy a slice
    /// API needlessly doubles large IBD allocations.
    pub fn apply_validated_batch_owned(
        &mut self,
        removals: &[OutPoint],
        additions: Vec<(OutPoint, StoredUtxo)>,
    ) -> Result<()> {
        self.apply_validated_batch_owned_with_sync(removals, additions, true)
    }

    pub fn apply_validated_batch_owned_unsynced(
        &mut self,
        removals: &[OutPoint],
        additions: Vec<(OutPoint, StoredUtxo)>,
    ) -> Result<()> {
        self.apply_validated_batch_owned_with_sync(removals, additions, false)
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
        self.commit_batch_with_count(removals, additions, next_count, sync, true)
    }

    fn apply_validated_batch_owned_with_sync(
        &mut self,
        removals: &[OutPoint],
        additions: Vec<(OutPoint, StoredUtxo)>,
        sync: bool,
    ) -> Result<()> {
        let next_count = self
            .entry_count
            .checked_sub(removals.len())
            .and_then(|count| count.checked_add(additions.len()))
            .context("validated UTXO batch entry count overflow")?;
        self.commit_owned_batch_with_count(removals, additions, next_count, sync, true)
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

        // While the durable partition is empty, the pending overlay contains
        // the complete effective UTXO set.  An overwrite in that phase (the
        // two historical BIP30 duplicate-coinbase blocks are the mainnet
        // example) is still fresh relative to disk: replacing a pending
        // value must not permanently poison the fresh-store bulk-ingest path.
        self.commit_batch_with_count(
            removals,
            additions,
            next_count,
            sync,
            self.bulk_ingest_eligible && self.pending_covers_all,
        )
    }

    fn commit_batch_with_count(
        &mut self,
        removals: &[OutPoint],
        additions: &[(OutPoint, StoredUtxo)],
        next_count: usize,
        sync: bool,
        additions_are_fresh: bool,
    ) -> Result<()> {
        let additions = additions
            .iter()
            .map(|(outpoint, entry)| (*outpoint, entry.clone()))
            .collect();
        self.commit_owned_batch_with_count(
            removals,
            additions,
            next_count,
            sync,
            additions_are_fresh,
        )
    }

    fn commit_owned_batch_with_count(
        &mut self,
        removals: &[OutPoint],
        additions: Vec<(OutPoint, StoredUtxo)>,
        next_count: usize,
        sync: bool,
        additions_are_fresh: bool,
    ) -> Result<()> {
        if removals.is_empty() && additions.is_empty() {
            if sync {
                self.flush_pending(true)?;
            }
            return Ok(());
        }
        // Do not let a large hash-table resize turn a bounded dirty-cache
        // checkpoint into a transient multi-gigabyte allocation.  The
        // current block is still applied after this flush; `entry_count`
        // remains the pre-block value until the complete mutation below is
        // installed, so the durable store and its metadata stay consistent.
        let pending_capacity_limit = self
            .pending
            .capacity()
            .saturating_mul(UTXO_PENDING_CAPACITY_GUARD_NUMERATOR)
            / UTXO_PENDING_CAPACITY_GUARD_DENOMINATOR;
        if !sync
            && self.pending.capacity() >= UTXO_PENDING_CAPACITY_GUARD_MIN
            && self.pending.len().saturating_add(additions.len()) > pending_capacity_limit
        {
            self.mark_unsynced_pending()?;
            self.dirty_items_since_sync = self
                .dirty_items_since_sync
                .saturating_add(self.pending.len());
            self.durability_checkpoint_needed =
                self.dirty_items_since_sync >= self.dirty_item_limit;
            self.flush_pending(false)?;
        }
        for outpoint in removals {
            // Match CCoinsViewCache's FRESH semantics: a coin created and
            // spent before the cache is flushed has no disk mutation at all.
            // Keeping a tombstone for it made raw transaction activity, not
            // effective dirty state, drive IBD checkpoints.
            let fresh = self
                .pending
                .get(outpoint)
                .is_some_and(|pending| pending.fresh);
            if fresh {
                self.remove_pending(outpoint);
            } else {
                self.set_pending(*outpoint, None, false);
            }
        }
        for (outpoint, entry) in additions {
            self.set_pending(outpoint, Some(entry), additions_are_fresh);
        }
        // Prevent a cached pre-batch value from becoming visible after the
        // pending overlay is committed or coalesced into another mutation.
        let mut read_cache = self.read_cache.lock();
        for outpoint in removals {
            read_cache.remove(outpoint);
        }
        drop(read_cache);
        self.entry_count = next_count;
        let (cache_bytes, cache_limit) = {
            let cache = self.read_cache.lock();
            (cache.bytes, cache.limit)
        };
        // Keep a bounded dirty working set even when the decoded cache is
        // already full.  Comparing `cache_bytes + pending_bytes` against the
        // limit makes every following block flush synchronously once the
        // clean cache reaches the ceiling, which turns IBD into a sequence of
        // tiny database writes.  Core keeps dirty cache entries until its
        // batch/flush policy fires; reserve a minimum fraction for them here
        // as well.
        let minimum_pending_budget = cache_limit / 8;
        let pending_budget = self
            .pending_limit_bytes
            .saturating_sub(cache_bytes.min(self.pending_limit_bytes))
            .max(minimum_pending_budget);
        let flush_unsynced = !sync
            && (self.pending.len() >= self.pending_item_limit
                || self.pending_bytes >= pending_budget);
        if flush_unsynced {
            self.mark_unsynced_pending()?;
            self.dirty_items_since_sync = self
                .dirty_items_since_sync
                .saturating_add(self.pending.len());
            self.durability_checkpoint_needed =
                self.dirty_items_since_sync >= self.dirty_item_limit;
        }
        if sync || flush_unsynced {
            self.flush_pending(sync)?;
        }
        Ok(())
    }

    fn flush_pending(&mut self, sync: bool) -> Result<()> {
        if self.pending.is_empty() {
            if self.entry_count == 0 {
                self.pending_covers_all = true;
            }
            if sync {
                self.keyspace
                    .persist(PersistMode::SyncData)
                    .context("flushing UTXO database")?;
                self.dirty_items_since_sync = 0;
                self.durability_checkpoint_needed = false;
                self.clear_unsynced_pending()?;
            }
            return Ok(());
        }

        let flush_started = Instant::now();

        let next_generation = self
            .generation
            .checked_add(1)
            .context("UTXO store generation exhausted")?;
        // A complete pending overlay (fresh replay from an empty store) or a
        // previously complete decoded cache already covers every effective
        // coin. Preserve that invariant across a normal Sync when the
        // resulting cache still contains exactly the authoritative entry
        // count. Core's large-cache path is different: CoinsTip().Flush()
        // clears the decoded cache after BatchWrite. Keeping our old FIFO
        // copy at that boundary retained tens of millions of outpoints and
        // made eviction bookkeeping, rather than validation, the IBD hot
        // path.
        let (cache_was_complete, cache_was_large) = {
            let cache = self.read_cache.lock();
            (
                self.pending_covers_all || cache.complete,
                // The item limit is an emergency guard for allocator and
                // hash-table overhead that the payload estimate cannot see.
                // It is still a full-cache checkpoint, but the decoded cache
                // has an explicit byte budget. Retain a bounded hot portion
                // of it so the next IBD window does not become a cold LSM
                // read storm after every checkpoint.
                cache.bytes.saturating_add(self.pending_bytes) >= self.pending_limit_bytes
                    || self.pending.len() >= self.pending_item_limit,
            )
        };

        // Consensus output serialization and allocation dominate large IBD
        // batch construction. Core's CCoinsViewDB::BatchWrite splits large
        // checkpoints into bounded batches (64 MiB by default). Do the same
        // here so a dirty-coin checkpoint cannot create a multi-gigabyte
        // temporary allocation or one long stop-the-world NFS write.
        let pending_items = self.pending.len();
        let pending_bytes = self.pending_bytes;
        let batch_limit = self.write_batch_limit_bytes.max(1);
        // Core's BatchWrite walks its dirty-coin cursor in key order. The
        // pending overlay is a hash map, so collect only references and sort
        // them once before splitting into bounded batches. Sorting each batch
        // independently still cuts the stream at random key ranges; the
        // resulting overlapping SSTs make later Fjall compactions dominate
        // the checkpoint. A reference is two machine words, so this bounded
        // indexing allocation is much smaller than encoding the values.
        let sort_started = Instant::now();
        let mut ordered_pending: Vec<(&OutPoint, &PendingUtxo)> = self.pending.iter().collect();
        ordered_pending.par_sort_unstable_by(|left, right| {
            // Fjall's bulk-ingest stream is ordered by the serialized key,
            // not by OutPoint's Rust ordering.  The latter compares vout as
            // a native integer, while the on-disk key uses little-endian
            // bytes (so vout 256 sorts before vout 1 on disk).
            left.0
                .txid
                .as_byte_array()
                .cmp(right.0.txid.as_byte_array())
                .then_with(|| left.0.vout.to_le_bytes().cmp(&right.0.vout.to_le_bytes()))
        });
        let sort_elapsed = sort_started.elapsed();

        // Count batches with a first pass, then stream one bounded batch at a
        // time from the globally ordered reference list.
        let batch_count = {
            let mut count = 0usize;
            let mut batch_bytes = 0usize;
            for (_, pending) in &ordered_pending {
                // Include the outpoint/hash-map bookkeeping that is not
                // represented by the stored value. A single unusually large
                // script still gets its own batch rather than being dropped or
                // split.
                let item_bytes = pending_utxo_bytes(pending.entry.as_ref()).saturating_add(64);
                if batch_bytes != 0 && batch_bytes.saturating_add(item_bytes) > batch_limit {
                    count = count.saturating_add(1);
                    batch_bytes = 0;
                }
                batch_bytes = batch_bytes.saturating_add(item_bytes);
            }
            if batch_bytes != 0 {
                count.saturating_add(1)
            } else {
                count
            }
        };

        // Multiple commits are no longer one atomic Fjall batch. The marker
        // makes an interrupted sequence fail closed: startup discards this
        // derived UTXO view and replays the durable block prefix.
        if sync && batch_count > 1 {
            self.mark_unsynced_pending()?;
        }

        let write_buffer_before = self.keyspace.write_buffer_size();
        let flushes_before = self.keyspace.flushes_completed();
        let compacting_before = self.keyspace.time_compacting();
        let mut encode_elapsed = Duration::ZERO;
        let mut ingest_elapsed = Duration::ZERO;
        let mut commit_elapsed = Duration::ZERO;

        // Fjall can bulk-ingest one strictly sorted stream directly into a
        // fresh partition. This is materially cheaper than creating dozens
        // of journaled memtable batches for the first large chainstate
        // checkpoint. It is safe only while the pending overlay is the whole
        // effective UTXO set: no tombstones, overwrites, or pre-existing
        // disk values may be present. The unsynced marker protects the
        // ingest/metadata split if the process stops between those writes.
        let can_bulk_ingest = self.pending_covers_all
            && self.bulk_ingest_eligible
            && self.entry_count == pending_items
            && self
                .coins
                .is_empty()
                .context("checking empty UTXO partition")?
            && ordered_pending
                .iter()
                .all(|(_, pending)| pending.fresh && pending.entry.is_some());

        // The capability is deliberately one-shot.  Once any pending batch
        // is written through either path, the partition may have an active
        // memtable and can no longer be passed to Fjall's empty-tree-only
        // bulk_ingest API.
        self.bulk_ingest_eligible = false;

        let used_bulk_ingest = if can_bulk_ingest {
            for (_, pending) in &ordered_pending {
                let entry = pending
                    .entry
                    .as_ref()
                    .context("bulk UTXO ingest encountered a missing coin")?;
                // These are the only fallible branches in the compact
                // encoder for a consensus-created output. Validate them
                // before starting ingest so an invalid synthetic/test value
                // cannot leave a partially ingested partition behind.
                if entry.output.script_pubkey.len() > MAX_STORED_UTXO_SCRIPT_SIZE {
                    bail!("UTXO script is too large");
                }
            }
            self.mark_unsynced_pending()?;
            let ingest_started = Instant::now();
            let mut pending_by_partition: Vec<Vec<(&OutPoint, &PendingUtxo)>> =
                (0..self.coins.len()).map(|_| Vec::new()).collect();
            for (outpoint, pending) in &ordered_pending {
                let key = encode_outpoint(outpoint);
                let index = self.coins.partition_index(&key);
                pending_by_partition[index].push((outpoint, pending));
            }
            // The prefix shards are independent LSM trees. Ingest them in
            // parallel so a fresh replay spends the available CPU and NFS
            // bandwidth on eight sequential key streams instead of paying
            // the full wall-clock cost of each shard one after another.
            let coins = self.coins.clone();
            let ingest_results = pending_by_partition
                .into_par_iter()
                .enumerate()
                .filter_map(|(index, partition_pending)| {
                    (!partition_pending.is_empty()).then_some((index, partition_pending))
                })
                .map(|(index, partition_pending)| {
                    coins
                        .partition(index)
                        .ingest(partition_pending.into_iter().map(|(outpoint, pending)| {
                            let entry = pending
                                .entry
                                .as_ref()
                                .expect("bulk UTXO ingest preflight guarantees a coin");
                            let value = encode_stored_utxo(entry)
                                .expect("bulk UTXO ingest preflight guarantees encodability");
                            (encode_outpoint(outpoint).to_vec(), value)
                        }))
                        .context("bulk-ingesting initial UTXO database")
                })
                .collect::<Vec<_>>();
            for result in ingest_results {
                result?;
            }
            ingest_elapsed = ingest_started.elapsed();

            let mut batch = self
                .keyspace
                .batch()
                .durability(sync.then_some(PersistMode::SyncData));
            batch.insert(
                &self.metadata,
                META_ENTRY_COUNT.to_vec(),
                u64::try_from(self.entry_count)
                    .context("UTXO entry count does not fit u64")?
                    .to_le_bytes()
                    .to_vec(),
            );
            batch.insert(
                &self.metadata,
                META_GENERATION.to_vec(),
                next_generation.to_le_bytes().to_vec(),
            );
            let commit_started = Instant::now();
            batch
                .commit()
                .context("committing bulk-ingested UTXO metadata")?;
            commit_elapsed += commit_started.elapsed();
            true
        } else {
            let mut commit_pending_batch =
                |batch_items: &[(&OutPoint, &PendingUtxo)], final_batch: bool| -> Result<()> {
                    let encode_started = Instant::now();
                    let encoded = batch_items
                        .par_iter()
                        .map(|item| {
                            let (outpoint, pending) = *item;
                            Ok((
                                encode_outpoint(outpoint).to_vec(),
                                pending.entry.as_ref().map(encode_stored_utxo).transpose()?,
                            ))
                        })
                        .collect::<Result<Vec<_>>>()?;
                    encode_elapsed += encode_started.elapsed();
                    let mut batch = fjall::Batch::with_capacity(
                        self.keyspace.clone(),
                        encoded
                            .len()
                            .saturating_add(if final_batch { 1 } else { 0 }),
                    )
                    .durability((sync && final_batch).then_some(PersistMode::SyncData));
                    for (key, entry) in encoded {
                        let partition = self.coins.partition(self.coins.partition_index(&key));
                        if let Some(entry) = entry {
                            batch.insert(partition, key, entry);
                        } else {
                            batch.remove(partition, key);
                        }
                    }
                    if final_batch {
                        batch.insert(
                            &self.metadata,
                            META_ENTRY_COUNT.to_vec(),
                            u64::try_from(self.entry_count)
                                .context("UTXO entry count does not fit u64")?
                                .to_le_bytes()
                                .to_vec(),
                        );
                        batch.insert(
                            &self.metadata,
                            META_GENERATION.to_vec(),
                            next_generation.to_le_bytes().to_vec(),
                        );
                    }
                    let commit_started = Instant::now();
                    batch.commit().context("committing UTXO database batch")?;
                    commit_elapsed += commit_started.elapsed();
                    Ok(())
                };

            let mut batch_items: Vec<(&OutPoint, &PendingUtxo)> = Vec::new();
            let mut batch_bytes = 0usize;
            let mut batch_index = 0usize;
            for &(outpoint, pending) in &ordered_pending {
                let item_bytes = pending_utxo_bytes(pending.entry.as_ref()).saturating_add(64);
                if !batch_items.is_empty() && batch_bytes.saturating_add(item_bytes) > batch_limit {
                    commit_pending_batch(&batch_items, batch_index + 1 == batch_count)?;
                    batch_index = batch_index.saturating_add(1);
                    batch_items.clear();
                    batch_bytes = 0;
                }
                batch_items.push((outpoint, pending));
                batch_bytes = batch_bytes.saturating_add(item_bytes);
            }
            if !batch_items.is_empty() {
                commit_pending_batch(&batch_items, batch_index + 1 == batch_count)?;
            }
            false
        };
        drop(ordered_pending);
        if sync {
            self.dirty_items_since_sync = 0;
            self.durability_checkpoint_needed = false;
            self.clear_unsynced_pending()?;
        }

        self.generation = next_generation;
        self.pending_covers_all = self.entry_count == 0;
        let pending = std::mem::take(&mut self.pending);
        self.pending_bytes = 0;
        let mut read_cache = self.read_cache.lock();
        if cache_was_large {
            // Match Core's large-checkpoint memory bound while retaining the
            // existing clean working set alongside a bounded hot portion of
            // the newest pending outputs. The pending map is moved below, so
            // evict enough clean entries first to make the final cache fit;
            // this avoids both a cold post-flush read storm and a temporary
            // duplicate decoded cache.
            let hot_cache_limit = UTXO_POST_FLUSH_HOT_CACHE_BYTES.min(read_cache.limit);
            let newest_height = pending
                .values()
                .filter_map(|pending| pending.entry.as_ref().map(|entry| entry.height))
                .max();
            if let Some(newest_height) = newest_height {
                let cutoff = newest_height.saturating_sub(UTXO_POST_FLUSH_HOT_CACHE_BLOCKS);
                let mut recent = pending
                    .into_iter()
                    .filter_map(|(outpoint, pending)| {
                        pending
                            .entry
                            .filter(|entry| entry.height >= cutoff)
                            .map(|entry| (outpoint, entry))
                    })
                    .collect::<Vec<_>>();
                recent.sort_unstable_by_key(|(_, entry)| entry.height);
                let recent_bytes = recent.iter().fold(0usize, |bytes, (_, entry)| {
                    bytes.saturating_add(read_cache_utxo_bytes(entry))
                });
                if recent_bytes >= hot_cache_limit {
                    read_cache.clear();
                } else {
                    read_cache.trim_to(hot_cache_limit.saturating_sub(recent_bytes));
                }
                read_cache.complete = false;
                read_cache.reserve_for_outpoints(recent.iter().map(|(outpoint, _)| outpoint));
                for (outpoint, entry) in recent {
                    // The bulk rebuild trims once after all entries are
                    // installed. Using the incremental insertion path here
                    // would re-check the full cache limit for every coin.
                    read_cache.insert_stationary(outpoint, entry);
                }
                read_cache.trim_to(hot_cache_limit);
            } else {
                read_cache.complete = false;
            }
        } else {
            for (outpoint, pending) in pending {
                if let Some(entry) = pending.entry {
                    read_cache.insert(outpoint, entry);
                } else {
                    read_cache.remove(&outpoint);
                }
            }
            read_cache.complete = cache_was_complete && read_cache.entry_count == self.entry_count;
        }
        let cache_after_entries = read_cache.len();
        let cache_after_bytes = read_cache.bytes;
        drop(read_cache);
        if cache_was_large || batch_count > 4 {
            trim_utxo_process_heap();
        }
        if cache_was_large || batch_count > 4 {
            let compacting_elapsed = self
                .keyspace
                .time_compacting()
                .saturating_sub(compacting_before);
            tracing::info!(
                "UTXO flush phases: entries={} pending_bytes={} batches={} bulk_ingest={} sort={:.2}s encode={:.2}s ingest={:.2}s commit={:.2}s total={:.2}s write_buffer={:.1}->{:.1}MiB memtable_flushes={} compaction={:.2}s active_compactions={} segments={} large_cache={} hot_cache={} entries/{}MiB sync={}",
                pending_items,
                pending_bytes,
                batch_count,
                used_bulk_ingest,
                sort_elapsed.as_secs_f64(),
                encode_elapsed.as_secs_f64(),
                ingest_elapsed.as_secs_f64(),
                commit_elapsed.as_secs_f64(),
                flush_started.elapsed().as_secs_f64(),
                write_buffer_before as f64 / (1024.0 * 1024.0),
                self.keyspace.write_buffer_size() as f64 / (1024.0 * 1024.0),
                self.keyspace
                    .flushes_completed()
                    .saturating_sub(flushes_before),
                compacting_elapsed.as_secs_f64(),
                self.keyspace.active_compactions(),
                self.coins.segment_count(),
                cache_was_large,
                cache_after_entries,
                cache_after_bytes / (1024 * 1024),
                sync,
            );
        }
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
        for partition in self.coins.iter() {
            partition
                .major_compact()
                .context("compacting UTXO database")?;
        }
        Ok(())
    }

    pub fn compact_if_needed(&mut self) -> Result<bool> {
        let segments = self.coins.segment_count();
        if segments < UTXO_MAJOR_COMPACTION_SEGMENT_THRESHOLD {
            return Ok(false);
        }
        let started = Instant::now();
        tracing::info!(
            segments,
            threshold = UTXO_MAJOR_COMPACTION_SEGMENT_THRESHOLD,
            "Starting major UTXO compaction"
        );
        self.compact()?;
        tracing::info!(
            segments_before = segments,
            segments_after = self.coins.segment_count(),
            elapsed = ?started.elapsed(),
            "Completed major UTXO compaction"
        );
        Ok(true)
    }

    pub fn clear(&mut self) -> Result<()> {
        self.pending.clear();
        self.pending_bytes = 0;
        self.dirty_items_since_sync = 0;
        self.durability_checkpoint_needed = false;
        // clear() removes logical values by writing tombstones.  Even when
        // the partition becomes logically empty, Fjall still has those
        // tombstones in its active memtable, so it is not a bulk-ingest
        // target until a future open establishes a truly empty tree.
        self.bulk_ingest_eligible = false;
        for partition in self.coins.iter() {
            loop {
                let keys = partition
                    .keys()
                    .take(10_000)
                    .map(|key| key.map(|key| key.to_vec()))
                    .collect::<std::result::Result<Vec<_>, _>>()?;
                if keys.is_empty() {
                    break;
                }
                let mut batch = self.keyspace.batch();
                for key in keys {
                    batch.remove(partition, key);
                }
                batch.commit()?;
            }
        }
        self.entry_count = 0;
        self.pending_covers_all = true;
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
        self.clear_unsynced_pending()?;
        let mut read_cache = self.read_cache.lock();
        read_cache.clear();
        read_cache.complete = true;
        Ok(())
    }

    pub fn flush(&mut self) -> Result<()> {
        self.flush_pending(true)
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

const HISTORY_EVENTS_PARTITION_PREFIX: &str = "events-";
const HISTORY_META_PARTITION_NAME: &str = "metadata";
const META_EVENT_PARTITION_EPOCH: &[u8] = b"event-partition-epoch";

fn history_events_partition_name(epoch: u64) -> String {
    format!("{HISTORY_EVENTS_PARTITION_PREFIX}{epoch}")
}

fn history_events_partition_options() -> PartitionCreateOptions {
    // History recovery inserts hundreds of millions of immutable, randomly
    // ordered event keys. Leveled compaction repeatedly rewrites overlapping
    // lower levels during that bulk load. Size-tiered compaction trades a
    // small amount of temporary read amplification for much lower write
    // amplification; history prefixes remain efficient after background
    // compaction. Larger data blocks improve LZ4's shared-script-prefix ratio
    // and match the range/prefix-heavy Electrum query workload.
    PartitionCreateOptions::default()
        .compression(CompressionType::Lz4)
        .compaction_strategy(CompactionStrategy::SizeTiered(SizeTiered::default()))
        .max_memtable_size(32 * 1024 * 1024)
        .block_size(64 * 1024)
}

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
    event_partition_epoch: u64,
    pending_events: FastHashMap<[u8; 32], Vec<[u8; HISTORY_EVENT_KEY_SIZE]>>,
    pending_event_count: usize,
}

/// Bounded point-in-time history lookup. Keeping the snapshot request-scoped
/// prevents a large script history scan from holding ChainState's global
/// lock while preserving a coherent view across concurrent IBD flushes.
pub struct ElectrumHistoryQuery {
    snapshot: Snapshot,
    script_hash: [u8; 32],
    pending: Vec<[u8; HISTORY_EVENT_KEY_SIZE]>,
    limit: usize,
}

impl ElectrumHistoryQuery {
    pub fn execute(self) -> Result<Option<StoredElectrumHistory>> {
        let mut history = Vec::new();
        for item in self.snapshot.prefix(self.script_hash) {
            let (key, _) = item.context("scanning Electrum history events")?;
            history.push(decode_history_event_key(&key)?.1);
            if history.len() > self.limit {
                return Ok(None);
            }
        }
        for key in self.pending {
            history.push(decode_history_event_key(&key)?.1);
            if history.len() > self.limit {
                return Ok(None);
            }
        }
        Ok(Some(history))
    }
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
        let path = directory.join("history-v3");
        let keyspace = FjallConfig::new(&path)
            .cache_size(cache_bytes.max(1024 * 1024))
            .max_write_buffer_size(DISK_INDEX_DEFAULT_WRITE_BUFFER_BYTES)
            .manual_journal_persist(true)
            .open()
            .with_context(|| format!("opening disk-backed Electrum database {}", path.display()))?;
        let metadata = keyspace.open_partition(
            HISTORY_META_PARTITION_NAME,
            PartitionCreateOptions::default().compression(CompressionType::None),
        )?;
        let stored_epoch = read_u64_metadata(&metadata, META_EVENT_PARTITION_EPOCH)?;
        let stored_generation = read_u64_metadata(&metadata, META_GENERATION)?;
        let stored_count = read_usize_metadata(&metadata, META_ENTRY_COUNT)?;
        let (event_partition_epoch, generation, entry_count) =
            match (stored_epoch, stored_generation, stored_count) {
                (Some(epoch), Some(generation), Some(entry_count))
                    if epoch != 0 && generation != 0 =>
                {
                    (epoch, generation, entry_count)
                }
                (None, None, None) => {
                    let epoch = 1u64;
                    let generation = 1u64;
                    let mut batch = keyspace.batch().durability(Some(PersistMode::SyncData));
                    batch.insert(
                        &metadata,
                        META_EVENT_PARTITION_EPOCH.to_vec(),
                        epoch.to_le_bytes().to_vec(),
                    );
                    batch.insert(
                        &metadata,
                        META_GENERATION.to_vec(),
                        generation.to_le_bytes().to_vec(),
                    );
                    batch.insert(
                        &metadata,
                        META_ENTRY_COUNT.to_vec(),
                        0u64.to_le_bytes().to_vec(),
                    );
                    batch.commit()?;
                    (epoch, generation, 0)
                }
                _ => bail!("Electrum history database metadata is incomplete"),
            };
        let events = keyspace.open_partition(
            &history_events_partition_name(event_partition_epoch),
            history_events_partition_options(),
        )?;
        if events.len()? != entry_count {
            bail!("Electrum history database entry count does not match its active partition");
        }
        Ok(Self {
            path,
            keyspace,
            events,
            metadata,
            entry_count,
            generation,
            event_partition_epoch,
            pending_events: FastHashMap::new(),
            pending_event_count: 0,
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
            .is_some_and(|script_hash| {
                self.pending_events
                    .get(&script_hash)
                    .is_some_and(|events| !events.is_empty())
                    || self
                        .events
                        .prefix(script_hash)
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
        self.query(script_hash, limit)?.execute()
    }

    pub fn query(&self, script_hash: &str, limit: usize) -> Result<ElectrumHistoryQuery> {
        let script_hash = encode_history_script_hash(script_hash)?;
        Ok(ElectrumHistoryQuery {
            snapshot: self.events.snapshot(),
            script_hash,
            pending: self
                .pending_events
                .get(&script_hash)
                .cloned()
                .unwrap_or_default(),
            limit,
        })
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
        let mut keys = self
            .events
            .keys()
            .filter_map(|key| key.ok())
            .filter_map(|key| decode_history_event_key(&key).ok().map(|entry| entry.0))
            .collect::<HashSet<_>>();
        keys.extend(self.pending_events.keys().copied());
        keys.into_iter().map(hex::encode).collect()
    }

    pub fn entries(&self) -> Result<Vec<(String, StoredElectrumHistory)>> {
        let mut histories: HashMap<[u8; 32], StoredElectrumHistory> = HashMap::new();
        for item in self.events.iter() {
            let (key, _) = item.context("scanning Electrum history database")?;
            let (script_hash, entry) = decode_history_event_key(&key)?;
            histories.entry(script_hash).or_default().push(entry);
        }
        for events in self.pending_events.values() {
            for key in events {
                let (script_hash, entry) = decode_history_event_key(key)?;
                histories.entry(script_hash).or_default().push(entry);
            }
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
        // Replacement batches need a complete prefix view. Make preceding
        // append-only IBD events visible to the LSM before scanning it.
        self.flush_pending_events(false)?;
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
        let mut staged = Vec::new();
        for (script_hash, entries) in updates {
            let keys = history_event_keys(*script_hash, entries)?;
            staged.push((*script_hash, keys));
        }
        let additions = staged.iter().map(|(_, keys)| keys.len()).sum::<usize>();
        if additions == 0 {
            if sync {
                self.flush_pending_events(true)?;
            }
            return Ok(());
        }
        let next_count = self
            .entry_count
            .checked_add(additions)
            .context("Electrum history entry count overflow")?;
        let next_generation = self
            .generation
            .checked_add(1)
            .context("Electrum history generation exhausted")?;
        for (script_hash, keys) in staged {
            self.pending_event_count = self.pending_event_count.saturating_add(keys.len());
            self.pending_events
                .entry(script_hash)
                .or_default()
                .extend(keys);
        }
        self.entry_count = next_count;
        self.generation = next_generation;
        if sync || self.pending_event_count >= DISK_INDEX_MAX_PENDING_ITEMS {
            self.flush_pending_events(sync)?;
        }
        Ok(())
    }

    fn flush_pending_events(&mut self, sync: bool) -> Result<()> {
        if self.pending_event_count == 0 {
            if sync {
                self.keyspace
                    .persist(PersistMode::SyncData)
                    .context("flushing Electrum history database")?;
            }
            return Ok(());
        }

        let mut batch = fjall::Batch::with_capacity(
            self.keyspace.clone(),
            self.pending_event_count.saturating_add(2),
        )
        .durability(sync.then_some(PersistMode::SyncData));
        for events in self.pending_events.values() {
            for key in events {
                batch.insert(&self.events, key.to_vec(), Vec::new());
            }
        }
        batch.insert(
            &self.metadata,
            META_ENTRY_COUNT.to_vec(),
            u64::try_from(self.entry_count)
                .context("Electrum history count does not fit u64")?
                .to_le_bytes()
                .to_vec(),
        );
        batch.insert(
            &self.metadata,
            META_GENERATION.to_vec(),
            self.generation.to_le_bytes().to_vec(),
        );
        batch
            .commit()
            .context("committing Electrum history batch")?;
        self.pending_events.clear();
        self.pending_event_count = 0;
        Ok(())
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
        self.pending_events.clear();
        self.pending_event_count = 0;
        let next_epoch = self
            .event_partition_epoch
            .checked_add(1)
            .context("Electrum history partition epoch exhausted")?;
        let next_generation = self
            .generation
            .checked_add(1)
            .context("Electrum history generation exhausted")?;
        let next_events = self.keyspace.open_partition(
            &history_events_partition_name(next_epoch),
            history_events_partition_options(),
        )?;
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
            next_generation.to_le_bytes().to_vec(),
        );
        batch.insert(
            &self.metadata,
            META_EVENT_PARTITION_EPOCH.to_vec(),
            next_epoch.to_le_bytes().to_vec(),
        );
        batch.commit()?;
        let previous_events = std::mem::replace(&mut self.events, next_events);
        self.entry_count = 0;
        self.generation = next_generation;
        self.event_partition_epoch = next_epoch;
        self.keyspace.delete_partition(previous_events)?;
        Ok(())
    }

    pub fn flush(&mut self) -> Result<()> {
        self.flush_pending_events(true)
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

fn history_event_keys(
    script_hash: [u8; 32],
    entries: &StoredElectrumHistory,
) -> Result<Vec<[u8; HISTORY_EVENT_KEY_SIZE]>> {
    let mut keys = Vec::with_capacity(entries.len());
    let mut previous_height = None;
    let mut previous_entry = None;
    let mut ordinal = 0u32;
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
        keys.push(history_event_key(script_hash, *txid, *height, ordinal));
        previous_entry = Some((*txid, *height));
    }
    Ok(keys)
}

fn insert_history_events(
    batch: &mut fjall::Batch,
    events: &PartitionHandle,
    script_hash: [u8; 32],
    entries: &StoredElectrumHistory,
) -> Result<usize> {
    let keys = history_event_keys(script_hash, entries)?;
    for key in &keys {
        batch.insert(events, key.to_vec(), Vec::new());
    }
    Ok(keys.len())
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
    let code = u64::from(entry.height)
        .checked_mul(2)
        .and_then(|code| code.checked_add(u64::from(entry.coinbase)))
        .context("UTXO height is too large")?;
    let compressed_amount = compress_core_amount(entry.output.value.to_sat());
    let mut bytes = Vec::with_capacity(COMPACT_STORED_UTXO_MAGIC.len() + 48);
    bytes.extend_from_slice(COMPACT_STORED_UTXO_MAGIC);
    // Core does not need this field because it can derive sequence-lock MTP
    // from the active chain.  Keep it after the compact coin metadata for the
    // Rust validator's equivalent sequence-lock checks.
    write_core_varint(&mut bytes, code)?;
    write_core_varint(&mut bytes, compressed_amount)?;
    write_core_script(&mut bytes, &entry.output.script_pubkey)?;
    bytes.extend_from_slice(&entry.median_time_past.to_le_bytes());
    if bytes.len() > MAX_STORED_UTXO_SIZE {
        bail!("UTXO value is too large: {} bytes", bytes.len());
    }
    Ok(bytes)
}

fn decode_stored_utxo(bytes: &[u8]) -> Result<StoredUtxo> {
    if bytes.starts_with(COMPACT_STORED_UTXO_MAGIC) {
        return decode_compact_stored_utxo(bytes);
    }
    decode_legacy_stored_utxo(bytes)
}

fn decode_compact_stored_utxo(bytes: &[u8]) -> Result<StoredUtxo> {
    let mut cursor = Cursor::new(&bytes[COMPACT_STORED_UTXO_MAGIC.len()..]);
    let code = read_core_varint(&mut cursor).context("reading compact UTXO metadata")?;
    let code = u32::try_from(code).context("compact UTXO metadata is too large")?;
    let height = code >> 1;
    let coinbase = code & 1 != 0;
    let value = decompress_core_amount(
        read_core_varint(&mut cursor).context("reading compact UTXO amount")?,
    )?;
    if value > bitcoin::Amount::MAX_MONEY.to_sat() {
        bail!("compact UTXO amount is out of range");
    }
    let script_pubkey = read_core_script(&mut cursor)?;
    let median_time_past = read_fixed_u32(&mut cursor).context("reading UTXO median time")?;
    if cursor.position() as usize != bytes.len() - COMPACT_STORED_UTXO_MAGIC.len() {
        bail!("compact UTXO value has trailing bytes");
    }
    Ok(StoredUtxo {
        output: TxOut {
            value: bitcoin::Amount::from_sat(value),
            script_pubkey,
        },
        height,
        median_time_past,
        coinbase,
    })
}

fn decode_legacy_stored_utxo(bytes: &[u8]) -> Result<StoredUtxo> {
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

/// Core's base-128 VARINT encoding.  Unlike a normal unsigned varint, a
/// continuation digit increments the accumulated value before the next digit
/// is incorporated.  This is the encoding used by `VARINT` in coins.cpp.
fn write_core_varint(bytes: &mut Vec<u8>, mut value: u64) -> Result<()> {
    let mut digits = Vec::with_capacity(10);
    loop {
        let continuation = if digits.is_empty() { 0 } else { 0x80 };
        digits.push((value as u8 & 0x7f) | continuation);
        if value <= 0x7f {
            break;
        }
        value = (value >> 7) - 1;
    }
    for digit in digits.into_iter().rev() {
        bytes.push(digit);
    }
    Ok(())
}

fn read_core_varint(cursor: &mut Cursor<&[u8]>) -> Result<u64> {
    let mut value = 0u64;
    loop {
        let digit = read_fixed_byte(cursor)?;
        if value > (u64::MAX >> 7) {
            bail!("compact UTXO VARINT is too large");
        }
        value = (value << 7) | u64::from(digit & 0x7f);
        if digit & 0x80 != 0 {
            if value == u64::MAX {
                bail!("compact UTXO VARINT is too large");
            }
            value += 1;
        } else {
            return Ok(value);
        }
    }
}

fn write_core_script(bytes: &mut Vec<u8>, script: &Script) -> Result<()> {
    let script = script.as_bytes();
    if script.len() == 25 && script[0..3] == [0x76, 0xa9, 0x14] && script[23..] == [0x88, 0xac] {
        bytes.push(0);
        bytes.extend_from_slice(&script[3..23]);
    } else if script.len() == 23 && script[0..2] == [0xa9, 0x14] && script[22] == 0x87 {
        bytes.push(1);
        bytes.extend_from_slice(&script[2..22]);
    } else if script.len() == 35
        && script[0] == 33
        && matches!(script[1], 0x02 | 0x03)
        && script[34] == 0xac
    {
        bytes.extend_from_slice(&script[1..34]);
    } else if script.len() == 67
        && script[0] == 65
        && script[1] == 0x04
        && script[66] == 0xac
        && bitcoin::secp256k1::PublicKey::from_slice(&script[1..66])
            .is_ok_and(|key| key.serialize_uncompressed().as_slice() == &script[1..66])
    {
        let key = &script[1..66];
        bytes.push(0x04 | (key[64] & 1));
        bytes.extend_from_slice(&key[1..33]);
    } else {
        if script.len() > MAX_STORED_UTXO_SCRIPT_SIZE {
            bail!("UTXO script is too large");
        }
        let size = u64::try_from(script.len())
            .ok()
            .and_then(|size| size.checked_add(6))
            .context("UTXO script size overflowed")?;
        write_core_varint(bytes, size)?;
        bytes.extend_from_slice(script);
    }
    Ok(())
}

fn read_core_script(cursor: &mut Cursor<&[u8]>) -> Result<ScriptBuf> {
    let size = read_core_varint(cursor)?;
    if size < 6 {
        let length = match size {
            0 | 1 => 20,
            2..=5 => 32,
            _ => unreachable!(),
        };
        let data = read_fixed_vec(cursor, length)?;
        let mut script = Vec::with_capacity(length + 5);
        match size {
            0 => {
                script.extend_from_slice(&[0x76, 0xa9, 0x14]);
                script.extend_from_slice(&data);
                script.extend_from_slice(&[0x88, 0xac]);
            }
            1 => {
                script.extend_from_slice(&[0xa9, 0x14]);
                script.extend_from_slice(&data);
                script.push(0x87);
            }
            2 | 3 => {
                script.push(33);
                script.push(size as u8);
                script.extend_from_slice(&data);
                script.push(0xac);
            }
            4 | 5 => {
                let mut compressed = Vec::with_capacity(33);
                compressed.push((size - 2) as u8);
                compressed.extend_from_slice(&data);
                let key = bitcoin::secp256k1::PublicKey::from_slice(&compressed)
                    .context("invalid compressed public key in compact UTXO")?;
                script.push(65);
                script.extend_from_slice(&key.serialize_uncompressed());
                script.push(0xac);
            }
            _ => unreachable!(),
        }
        return Ok(ScriptBuf::from_bytes(script));
    }
    let length = usize::try_from(size - 6).context("compact UTXO script is too large")?;
    if length > MAX_STORED_UTXO_SCRIPT_SIZE {
        bail!("compact UTXO script is too large");
    }
    Ok(ScriptBuf::from_bytes(read_fixed_vec(cursor, length)?))
}

fn read_fixed_byte(cursor: &mut Cursor<&[u8]>) -> Result<u8> {
    let mut byte = [0; 1];
    cursor.read_exact(&mut byte)?;
    Ok(byte[0])
}

fn read_fixed_u32(cursor: &mut Cursor<&[u8]>) -> Result<u32> {
    let mut bytes = [0; 4];
    cursor.read_exact(&mut bytes)?;
    Ok(u32::from_le_bytes(bytes))
}

fn read_fixed_vec(cursor: &mut Cursor<&[u8]>, length: usize) -> Result<Vec<u8>> {
    let mut bytes = vec![0; length];
    cursor.read_exact(&mut bytes)?;
    Ok(bytes)
}

fn compress_core_amount(mut value: u64) -> u64 {
    if value == 0 {
        return 0;
    }
    let mut exponent = 0u64;
    while value % 10 == 0 && exponent < 9 {
        value /= 10;
        exponent += 1;
    }
    if exponent < 9 {
        let digit = value % 10;
        value /= 10;
        1 + (value * 9 + digit - 1) * 10 + exponent
    } else {
        1 + (value - 1) * 10 + 9
    }
}

fn decompress_core_amount(mut value: u64) -> Result<u64> {
    if value == 0 {
        return Ok(0);
    }
    value -= 1;
    let exponent = value % 10;
    value /= 10;
    let mut number = if exponent < 9 {
        let digit = value % 9 + 1;
        value /= 9;
        value
            .checked_mul(10)
            .and_then(|value| value.checked_add(digit))
            .context("compact UTXO amount overflows")?
    } else {
        value
            .checked_add(1)
            .context("compact UTXO amount overflows")?
    };
    for _ in 0..exponent {
        number = number
            .checked_mul(10)
            .context("compact UTXO amount overflows")?;
    }
    Ok(number)
}

#[inline]
fn encode_outpoint(outpoint: &OutPoint) -> [u8; 36] {
    // OutPoint consensus encoding is exactly txid bytes followed by a
    // little-endian u32.  Construct it in place: the generic `serialize`
    // helper allocates a temporary Vec for every UTXO point read, which is a
    // significant allocator cost when a 256-block IBD window has hundreds of
    // thousands of misses.
    let mut encoded = [0u8; 36];
    encoded[..32].copy_from_slice(outpoint.txid.as_byte_array());
    encoded[32..].copy_from_slice(&outpoint.vout.to_le_bytes());
    encoded
}

fn decode_outpoint(bytes: &[u8]) -> Result<OutPoint> {
    if bytes.len() != 36 {
        bail!("stored UTXO outpoint is not 36 bytes");
    }
    let txid = Txid::from_byte_array(
        bytes[..32]
            .try_into()
            .expect("validated 32-byte transaction id"),
    );
    let vout = u32::from_le_bytes(
        bytes[32..]
            .try_into()
            .expect("validated 4-byte output index"),
    );
    Ok(OutPoint::new(txid, vout))
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
#[derive(Clone)]
pub struct ElectrumBlockStoreReader {
    state: Arc<RwLock<ElectrumBlockStoreReaderState>>,
}

struct ElectrumBlockStoreReaderState {
    file: Arc<File>,
    index: HashMap<BlockHash, Record>,
}

impl ElectrumBlockStoreReader {
    fn new(file: File, index: HashMap<BlockHash, Record>) -> Self {
        Self {
            state: Arc::new(RwLock::new(ElectrumBlockStoreReaderState {
                file: Arc::new(file),
                index,
            })),
        }
    }

    pub fn transaction(
        &self,
        block_hash: &BlockHash,
        transaction_index: usize,
    ) -> Result<Option<Transaction>> {
        let transactions = self.transactions(block_hash)?;
        Ok(transactions.and_then(|transactions| transactions.into_iter().nth(transaction_index)))
    }

    pub fn merkle_branch(
        &self,
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

    /// Read several pruned block transaction lists in append-log order. The
    /// file descriptor and records are snapshotted together before doing any
    /// disk I/O, so a concurrent sidecar rewrite cannot mix old offsets with
    /// the replacement file.
    pub(crate) fn transactions_for_blocks(
        &self,
        block_hashes: &[BlockHash],
    ) -> Result<HashMap<BlockHash, Vec<Transaction>>> {
        let (file, mut records) = {
            let state = self.state.read();
            let records = block_hashes
                .iter()
                .filter_map(|hash| state.index.get(hash).copied().map(|record| (*hash, record)))
                .collect::<Vec<_>>();
            (Arc::clone(&state.file), records)
        };
        records.sort_unstable_by_key(|(_, record)| record.offset);
        records.dedup_by_key(|(hash, _)| *hash);

        records
            .into_iter()
            .map(|(hash, record)| {
                read_electrum_transactions_from_record(&file, hash, record)
                    .map(|transactions| (hash, transactions))
            })
            .collect()
    }

    pub(crate) fn transactions(&self, block_hash: &BlockHash) -> Result<Option<Vec<Transaction>>> {
        let (file, record) = {
            let state = self.state.read();
            let Some(record) = state.index.get(block_hash).copied() else {
                return Ok(None);
            };
            (Arc::clone(&state.file), record)
        };
        read_electrum_transactions_from_record(&file, *block_hash, record).map(Some)
    }

    fn insert(&self, hash: BlockHash, record: Record) {
        self.state.write().index.insert(hash, record);
    }

    fn replace(&self, file: File, index: HashMap<BlockHash, Record>) {
        *self.state.write() = ElectrumBlockStoreReaderState {
            file: Arc::new(file),
            index,
        };
    }
}

pub struct ElectrumBlockStore {
    path: PathBuf,
    file: File,
    index_file: File,
    index: HashMap<BlockHash, Record>,
    serving_reader: ElectrumBlockStoreReader,
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
        let serving_reader = ElectrumBlockStoreReader::new(file.try_clone()?, index.clone());
        Ok(Self {
            path,
            file,
            index_file,
            index,
            serving_reader,
        })
    }

    pub fn reader(&self) -> ElectrumBlockStoreReader {
        self.serving_reader.clone()
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
        self.serving_reader.insert(hash, record);
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
        self.serving_reader
            .replace(self.file.try_clone()?, self.index.clone());
        Ok(true)
    }

    pub fn flush(&mut self) -> Result<()> {
        self.file.sync_data()?;
        publish_index_data_len(&mut self.index_file, data_len_after(&self.file)?)?;
        Ok(())
    }

    pub fn transaction(
        &self,
        block_hash: &BlockHash,
        transaction_index: usize,
    ) -> Result<Option<Transaction>> {
        self.serving_reader
            .transaction(block_hash, transaction_index)
    }

    pub fn merkle_branch(
        &self,
        block_hash: &BlockHash,
        transaction_index: usize,
    ) -> Result<Option<Vec<Txid>>> {
        self.serving_reader
            .merkle_branch(block_hash, transaction_index)
    }

    /// Read several pruned block transaction lists in append-log order.  The
    /// active chain is normally traversed by height, but compaction and
    /// recovery can leave the index order unrelated to that traversal.  Sort
    /// the requests by record offset so restart-time index rebuilds perform
    /// mostly forward reads from the sidecar.
    pub(crate) fn transactions_for_blocks(
        &self,
        block_hashes: &[BlockHash],
    ) -> Result<HashMap<BlockHash, Vec<Transaction>>> {
        self.serving_reader.transactions_for_blocks(block_hashes)
    }

    fn transactions(&self, block_hash: &BlockHash) -> Result<Option<Vec<Transaction>>> {
        self.serving_reader.transactions(block_hash)
    }
}

fn read_electrum_transactions_from_record(
    file: &File,
    block_hash: BlockHash,
    record: Record,
) -> Result<Vec<Transaction>> {
    let bytes = read_storage_record(
        file,
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

pub(crate) fn merkle_branch_for_transactions(
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

/// Recover a writable append-only store after an interrupted unsynced batch.
///
/// The first index word is published only after the data file has been synced,
/// so it is the authoritative durable boundary. Appended data and index
/// records beyond that boundary may be complete, but were never committed as
/// a unit and must be discarded. Rebuilding the small index from its durable
/// prefix avoids scanning and decoding the potentially huge data file.
fn recover_unpublished_indexed_tail(
    data_file: &mut File,
    index_file: &mut File,
    actual_data_len: u64,
    max_record_size: usize,
) -> Result<Option<u64>> {
    let index_len = index_file.metadata()?.len();
    if index_len < INDEX_HEADER_SIZE {
        return Ok(None);
    }
    index_file.seek(SeekFrom::Start(0))?;
    let mut published_bytes = [0u8; 8];
    index_file.read_exact(&mut published_bytes)?;
    let published_data_len = u64::from_le_bytes(published_bytes);
    if published_data_len == actual_data_len {
        return Ok(Some(actual_data_len));
    }
    if published_data_len > actual_data_len {
        return Ok(None);
    }

    let complete_records = (index_len - INDEX_HEADER_SIZE) / INDEX_RECORD_SIZE;
    let mut durable_index = HashMap::with_capacity(complete_records as usize);
    for _ in 0..complete_records {
        let mut bytes = [0u8; INDEX_RECORD_SIZE as usize];
        index_file.read_exact(&mut bytes)?;
        let hash = BlockHash::from_byte_array(
            bytes[..32]
                .try_into()
                .expect("block index hash has fixed width"),
        );
        let record = Record {
            offset: u64::from_le_bytes(
                bytes[32..40]
                    .try_into()
                    .expect("block index offset has fixed width"),
            ),
            length: u32::from_le_bytes(
                bytes[40..44]
                    .try_into()
                    .expect("block index length has fixed width"),
            ),
        };
        let end = record
            .offset
            .saturating_add(4)
            .saturating_add(u64::from(record.length));
        if end > published_data_len {
            continue;
        }
        if record.length == 0 || record.length as usize > max_record_size {
            return Ok(None);
        }
        if durable_index.insert(hash, record).is_some() {
            return Ok(None);
        }
    }
    if !index_layout_is_contiguous(&durable_index, published_data_len) {
        return Ok(None);
    }

    data_file.set_len(published_data_len)?;
    data_file.seek(SeekFrom::End(0))?;
    rewrite_index(index_file, published_data_len, &durable_index)?;
    Ok(Some(published_data_len))
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

fn scan_undo_index(
    file: &mut File,
    xor_key: XorKey,
    repair_truncated_tail: bool,
) -> Result<HashMap<BlockHash, Record>> {
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
                if offset < data_len && repair_truncated_tail {
                    file.set_len(offset)?;
                } else if offset < data_len {
                    bail!("truncated undo record at offset {offset}");
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
                bail!("truncated undo record at offset {offset}");
            }
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
    fn utxo_miss_order_matches_serialized_key_order() {
        let txid = Txid::from_byte_array([0; 32]);
        let mut outpoints = vec![OutPoint::new(txid, 1), OutPoint::new(txid, 256)];
        outpoints.sort_unstable_by_key(encode_outpoint);

        // The UTXO partition stores vout as little-endian bytes, so 256
        // precedes 1 even though OutPoint's native integer ordering does not.
        assert_eq!(
            outpoints,
            [OutPoint::new(txid, 256), OutPoint::new(txid, 1)]
        );
        assert!(encode_outpoint(&outpoints[0]) < encode_outpoint(&outpoints[1]));
    }

    #[test]
    fn recommended_utxo_disk_cache_scales_with_dbcache() {
        let mib = |bytes: u64| bytes / (1024 * 1024);
        assert_eq!(mib(UtxoStore::recommended_disk_cache_bytes(None)), 128);
        assert_eq!(mib(UtxoStore::recommended_disk_cache_bytes(Some(4))), 128);
        assert_eq!(
            mib(UtxoStore::recommended_disk_cache_bytes(Some(1_024))),
            341
        );
        assert_eq!(
            mib(UtxoStore::recommended_disk_cache_bytes(Some(2_048))),
            682
        );
        assert_eq!(
            mib(UtxoStore::recommended_disk_cache_bytes(Some(8_192))),
            768
        );
    }

    #[test]
    fn adaptive_utxo_prefetch_uses_sustained_throughput_and_hysteresis() {
        let tuner = UtxoReadTuner::default();
        let fixed = tuner.tuning();
        assert!(!fixed.adaptive);
        assert_eq!(fixed.profile, "latency");

        // Disabled observations must preserve the established fixed profile.
        for _ in 0..8 {
            tuner.record(1_000_000, Duration::from_secs(1));
        }
        assert_eq!(tuner.tuning().profile, "latency");

        tuner.configure(true);
        let initial = tuner.tuning();
        assert!(initial.adaptive);
        assert_eq!(initial.profile, "low-overhead");

        // One slow sample is not enough to increase read concurrency.
        tuner.record(20_000, Duration::from_secs(1));
        assert_eq!(tuner.tuning().profile, "low-overhead");
        for _ in 1..16 {
            tuner.record(20_000, Duration::from_secs(1));
        }
        let latency = tuner.tuning();
        assert_eq!(latency.profile, "latency");
        assert!(latency.max_blocks > initial.max_blocks);
        assert!(latency.max_outpoints > initial.max_outpoints);
        assert!(latency.read_workers > initial.read_workers);

        // Sustained high throughput eventually returns to the lower-overhead
        // profile; hysteresis prevents one hot-cache sample from doing so.
        tuner.record(1_000_000, Duration::from_secs(1));
        assert_eq!(tuner.tuning().profile, "latency");
        for _ in 0..16 {
            tuner.record(1_000_000, Duration::from_secs(1));
        }
        assert_eq!(tuner.tuning().profile, "low-overhead");
    }

    #[test]
    fn utxo_query_deduplicates_sorted_misses() {
        let directory = tempfile::tempdir().unwrap();
        let txid = Txid::from_byte_array([1; 32]);
        let first = OutPoint::new(txid, 1);
        let second = OutPoint::new(txid, 256);
        let entry = StoredUtxo {
            output: TxOut {
                value: bitcoin::Amount::from_sat(1_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            },
            height: 1,
            median_time_past: 1,
            coinbase: false,
        };
        let mut store = UtxoStore::open(directory.path()).unwrap();
        store
            .apply_batch(&[], &[(first, entry.clone()), (second, entry)])
            .unwrap();
        store.read_cache.lock().clear();

        let query = store.query_unresolved(&[first, second, first]);
        assert_eq!(query.unresolved, vec![second, first]);
    }

    #[test]
    fn compact_utxo_values_round_trip_and_decode_legacy_values() {
        let entries = [
            StoredUtxo {
                output: TxOut {
                    value: bitcoin::Amount::from_sat(50_000_000),
                    script_pubkey: ScriptBuf::from_bytes(
                        [
                            [0x76, 0xa9, 0x14].as_slice(),
                            &[0x11; 20],
                            [0x88, 0xac].as_slice(),
                        ]
                        .concat(),
                    ),
                },
                height: 840_000,
                median_time_past: 1_700_000_000,
                coinbase: true,
            },
            StoredUtxo {
                output: TxOut {
                    value: bitcoin::Amount::from_sat(123_456_789),
                    script_pubkey: ScriptBuf::from_bytes(vec![0x51, 0x21, 0x02, 0x02]),
                },
                height: 840_001,
                median_time_past: 1_700_000_001,
                coinbase: false,
            },
        ];

        for entry in entries {
            let encoded = encode_stored_utxo(&entry).unwrap();
            assert!(encoded.starts_with(COMPACT_STORED_UTXO_MAGIC));
            assert_eq!(decode_stored_utxo(&encoded).unwrap(), entry);

            let output = serialize(&entry.output);
            let mut legacy = Vec::with_capacity(13 + output.len());
            legacy.extend_from_slice(&entry.height.to_le_bytes());
            legacy.extend_from_slice(&entry.median_time_past.to_le_bytes());
            legacy.push(u8::from(entry.coinbase));
            legacy.extend_from_slice(&(output.len() as u32).to_le_bytes());
            legacy.extend_from_slice(&output);
            assert_eq!(decode_stored_utxo(&legacy).unwrap(), entry);
        }
    }

    #[test]
    fn compression_inspector_counts_xored_records_without_decompression() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("records.dat");
        let xor_key = XorKey([1, 2, 3, 4, 5, 6, 7, 8]);
        std::fs::write(directory.path().join("xor.dat"), xor_key.0).unwrap();
        let payloads = [
            vec![0x11; STORAGE_COMPRESSION_MIN_SIZE - 1],
            vec![0x42; 16 * 1024],
        ];
        let mut expected_original = 0u64;
        let mut expected_stored = 0u64;
        let mut file = File::create(&path).unwrap();
        let mut offset = 0u64;
        let mut records = Vec::new();
        for payload in &payloads {
            let encoded = encode_storage_payload(payload, MAX_STORED_BLOCK_SIZE).unwrap();
            expected_original += payload.len() as u64;
            expected_stored += encoded.len() as u64;
            let mut record = (encoded.len() as u32).to_le_bytes().to_vec();
            record.extend_from_slice(&encoded);
            xor_key.apply(&mut record, offset);
            file.write_all(&record).unwrap();
            records.push(Record {
                offset,
                length: encoded.len() as u32,
            });
            offset += record.len() as u64;
        }
        drop(file);

        let info = inspect_storage_file_compression(&path, None).unwrap();
        assert_eq!(info.records, 2);
        assert_eq!(info.compressed_records, 1);
        assert_eq!(info.uncompressed_records, 1);
        assert_eq!(info.original_payload_bytes, expected_original);
        assert_eq!(info.stored_payload_bytes, expected_stored);
        assert_eq!(info.framing_bytes, 8);
        assert_eq!(
            info.stored_size_bytes,
            std::fs::metadata(&path).unwrap().len()
        );
        assert!(directory.path().join("records.compression").is_file());
        assert_eq!(
            info.saved_bytes,
            expected_original.saturating_sub(expected_stored)
        );
        assert!(info.space_saved_percent > 0.0);
        assert!(info.compression_ratio > 1.0);

        // Grow the file after the first inspection and publish a matching
        // index. The second inspection must use the sidecar as a prefix and
        // read only this newly appended record.
        let appended_payload = vec![0x55; 8 * 1024];
        let appended = encode_storage_payload(&appended_payload, MAX_STORED_BLOCK_SIZE).unwrap();
        let appended_offset = std::fs::metadata(&path).unwrap().len();
        let mut appended_record = (appended.len() as u32).to_le_bytes().to_vec();
        appended_record.extend_from_slice(&appended);
        xor_key.apply(&mut appended_record, appended_offset);
        OpenOptions::new()
            .append(true)
            .open(&path)
            .unwrap()
            .write_all(&appended_record)
            .unwrap();
        records.push(Record {
            offset: appended_offset,
            length: appended.len() as u32,
        });
        let mut index = HashMap::new();
        for (record_index, record) in records.iter().copied().enumerate() {
            index.insert(BlockHash::from_byte_array([record_index as u8; 32]), record);
        }
        let mut index_file = OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .truncate(true)
            .open(path.with_extension("index"))
            .unwrap();
        rewrite_index(
            &mut index_file,
            std::fs::metadata(&path).unwrap().len(),
            &index,
        )
        .unwrap();
        let grown = inspect_storage_file_compression(&path, None).unwrap();
        assert_eq!(grown.records, 3);
        assert_eq!(
            grown.stored_size_bytes,
            std::fs::metadata(&path).unwrap().len()
        );
    }

    #[test]
    fn block_store_compression_cache_tracks_appended_and_pruned_records() {
        let directory = tempfile::tempdir().unwrap();
        let first = genesis_block(Network::Regtest);
        let first_hash = first.block_hash();
        let mut second = first.clone();
        second.header.nonce = 1;
        let second_hash = second.block_hash();
        let mut store = BlockStore::open_with_xor(directory.path(), true).unwrap();
        let initial_inspector = store.compression_inspector().unwrap();
        store.insert(&first).unwrap();
        store.insert_undo(first_hash, &[Vec::new()]).unwrap();

        // Appends that race a first long-running inspection are folded into
        // its result instead of making the new cache stale immediately.
        let initial = initial_inspector.inspect().unwrap();
        assert_eq!(initial.blocks.records, 1);
        assert_eq!(initial.undo.records, 1);

        store.insert(&second).unwrap();
        store.insert_undo(second_hash, &[Vec::new()]).unwrap();
        let appended = store.compression_inspector().unwrap().inspect().unwrap();
        assert_eq!(appended.blocks.records, 2);
        assert_eq!(appended.undo.records, 2);
        assert_eq!(
            appended.blocks.stored_size_bytes,
            store.data_size().unwrap()
        );
        assert_eq!(appended.undo.stored_size_bytes, store.undo_size().unwrap());

        store
            .prune(&HashSet::from([second_hash]), &HashSet::from([second_hash]))
            .unwrap();
        let pruned = store.compression_inspector().unwrap().inspect().unwrap();
        assert_eq!(pruned.blocks.records, 1);
        assert_eq!(pruned.undo.records, 1);
        assert_eq!(pruned.total.records, 2);
    }

    #[test]
    fn block_store_compression_stats_survive_reopen() {
        let directory = tempfile::tempdir().unwrap();
        let block = genesis_block(Network::Regtest);
        let hash = block.block_hash();
        let expected = {
            let mut store = BlockStore::open_with_xor(directory.path(), true).unwrap();
            store.insert(&block).unwrap();
            store.insert_undo(hash, &[Vec::new()]).unwrap();
            store.flush().unwrap();
            assert!(directory.path().join("blocks.compression").is_file());
            assert!(directory.path().join("undo.compression").is_file());
            store.compression_inspector().unwrap().inspect().unwrap()
        };

        let mut reopened = BlockStore::open_with_xor(directory.path(), true).unwrap();
        assert!(reopened.block_compression_cache.lock().counts.is_some());
        assert!(reopened.undo_compression_cache.lock().counts.is_some());
        assert_eq!(
            reopened.compression_inspector().unwrap().inspect().unwrap(),
            expected
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
    fn transaction_index_batches_active_blocks_and_keeps_pending_writes_visible() {
        let directory = tempfile::tempdir().unwrap();
        let first_hash = BlockHash::from_byte_array([11u8; 32]);
        let second_hash = BlockHash::from_byte_array([12u8; 32]);
        let first_txid = Txid::from_byte_array([13u8; 32]);
        let second_txid = Txid::from_byte_array([14u8; 32]);
        {
            let mut store = TransactionIndexStore::open(directory.path()).unwrap();
            store
                .connect_active_block(first_hash, 1, &[first_txid], false)
                .unwrap();

            assert!(
                store
                    .blocks
                    .get(first_hash.to_byte_array())
                    .unwrap()
                    .is_none()
            );
            assert!(store.contains(&first_hash).unwrap());
            assert_eq!(store.get(&first_hash).unwrap(), Some(vec![first_txid]));
            assert_eq!(store.active_tip().unwrap(), Some((first_hash, 1)));
            assert_eq!(
                store.active_locations(&first_txid).unwrap(),
                vec![StoredTxLocation {
                    block_hash: first_hash,
                    height: 1,
                    transaction_index: 0,
                }]
            );
            let location_query = store.active_locations_query(&[first_txid, second_txid]);

            store
                .connect_active_block(second_hash, 2, &[second_txid], true)
                .unwrap();
            let snapshotted = location_query.execute().unwrap();
            assert_eq!(
                snapshotted[&first_txid],
                vec![StoredTxLocation {
                    block_hash: first_hash,
                    height: 1,
                    transaction_index: 0,
                }]
            );
            assert!(!snapshotted.contains_key(&second_txid));
            assert!(
                store
                    .blocks
                    .get(first_hash.to_byte_array())
                    .unwrap()
                    .is_some()
            );
            assert!(
                store
                    .blocks
                    .get(second_hash.to_byte_array())
                    .unwrap()
                    .is_some()
            );
        }

        let reopened = TransactionIndexStore::open(directory.path()).unwrap();
        assert_eq!(reopened.len(), 2);
        assert_eq!(reopened.active_tip().unwrap(), Some((second_hash, 2)));
        assert_eq!(
            reopened.active_locations(&first_txid).unwrap(),
            vec![StoredTxLocation {
                block_hash: first_hash,
                height: 1,
                transaction_index: 0,
            }]
        );
        assert_eq!(
            reopened.active_locations(&second_txid).unwrap(),
            vec![StoredTxLocation {
                block_hash: second_hash,
                height: 2,
                transaction_index: 0,
            }]
        );
    }

    #[test]
    fn persists_and_reopens_genesis() {
        let directory = tempfile::tempdir().unwrap();
        let block = genesis_block(Network::Regtest);
        let hash = {
            let mut store = BlockStore::open(directory.path()).unwrap();
            let hash = store.insert(&block).unwrap();
            assert_eq!(store.get(&hash).unwrap().unwrap(), block);
            assert_eq!(store.get_for_replay(&hash).unwrap(), Some(block.clone()));
            hash
        };
        let index_path = directory.path().join("blocks.index");
        assert!(index_path.exists());
        std::fs::write(&index_path, b"corrupt").unwrap();
        let mut reopened = BlockStore::open(directory.path()).unwrap();
        assert!(reopened.contains(&hash));
        assert_eq!(reopened.get(&hash).unwrap().unwrap(), block);
        assert_eq!(reopened.get_for_replay(&hash).unwrap(), Some(block));
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
            assert!(store.disk_usage().unwrap() > 0);
            store.generation()
        };

        let reopened = UtxoStore::open(directory.path()).unwrap();
        assert_eq!(reopened.generation(), generation);
        assert_eq!(reopened.len(), 1);
        assert_eq!(reopened.get(&first).unwrap(), None);
        assert_eq!(reopened.get(&second).unwrap(), Some(second_entry));
    }

    #[test]
    fn streaming_utxo_entries_merge_pending_overlay_in_key_order() {
        let directory = tempfile::tempdir().unwrap();
        let first = OutPoint::new(Txid::from_byte_array([1; 32]), 0);
        let second = OutPoint::new(Txid::from_byte_array([1; 32]), 1);
        let third = OutPoint::new(Txid::from_byte_array([128; 32]), 0);
        let replacement = OutPoint::new(Txid::from_byte_array([255; 32]), 0);
        let entry = |value, height| StoredUtxo {
            output: TxOut {
                value: bitcoin::Amount::from_sat(value),
                script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
            },
            height,
            median_time_past: height,
            coinbase: false,
        };
        let first_entry = entry(1_000, 1);
        let second_entry = entry(2_000, 2);
        let third_entry = entry(3_000, 3);
        let replacement_entry = entry(4_000, 4);
        let mut store = UtxoStore::open(directory.path()).unwrap();
        store
            .apply_batch(
                &[],
                &[
                    (first, first_entry.clone()),
                    (second, second_entry),
                    (third, third_entry),
                ],
            )
            .unwrap();
        store
            .apply_batch_unsynced(
                &[first],
                &[
                    (replacement, replacement_entry.clone()),
                    (first, first_entry),
                ],
            )
            .unwrap();

        let expected = store.entries().unwrap();
        let mut streamed = Vec::new();
        store
            .for_each_entry_sorted(|outpoint, entry| {
                streamed.push((outpoint, entry.clone()));
                Ok(())
            })
            .unwrap();
        assert_eq!(streamed, expected);

        store.flush().unwrap();
        let mut reopened_streamed = Vec::new();
        store
            .for_each_entry_sorted(|outpoint, entry| {
                reopened_streamed.push((outpoint, entry.clone()));
                Ok(())
            })
            .unwrap();
        assert_eq!(reopened_streamed, expected);
    }

    #[test]
    fn fresh_utxo_flush_bulk_ingests_and_allows_incremental_updates() {
        let directory = tempfile::tempdir().unwrap();
        let entry = |value, height| StoredUtxo {
            output: TxOut {
                value: bitcoin::Amount::from_sat(value),
                script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
            },
            height,
            median_time_past: height.saturating_sub(1),
            coinbase: false,
        };
        let first = OutPoint::new(Txid::from_byte_array([11; 32]), 0);
        let second = OutPoint::new(Txid::from_byte_array([9; 32]), 1);
        let third = OutPoint::new(Txid::from_byte_array([10; 32]), 2);
        let first_entry = entry(10_000, 1);
        let second_entry = entry(20_000, 2);
        let third_entry = entry(30_000, 3);
        let overwritten = OutPoint::new(Txid::from_byte_array([12; 32]), 0);
        let overwritten_entry = entry(35_000, 3);
        let replacement_entry = entry(36_000, 4);

        {
            let mut store = UtxoStore::open(directory.path()).unwrap();
            store
                .apply_validated_batch_unsynced(
                    &[],
                    &[
                        (first, first_entry.clone()),
                        (second, second_entry.clone()),
                        (third, third_entry.clone()),
                    ],
                )
                .unwrap();
            // A non-validated overwrite while the store is still entirely
            // pending must remain fresh. This mirrors the BIP30 duplicate
            // coinbase transition encountered during mainnet replay.
            store
                .apply_batch_unsynced(&[], &[(overwritten, overwritten_entry)])
                .unwrap();
            store
                .apply_batch_unsynced(&[overwritten], &[(overwritten, replacement_entry.clone())])
                .unwrap();
            assert!(
                store
                    .pending
                    .get(&overwritten)
                    .is_some_and(|pending| pending.fresh)
            );
            store.flush().unwrap();
            // Bulk ingest creates a sorted immutable segment immediately;
            // normal journaled writes have no segment until background flush.
            assert_eq!(store.coins.segment_count(), 1);
            assert_eq!(store.pending.len(), 0);
            assert_eq!(store.len(), 4);
        }

        let replacement = entry(40_000, 4);
        {
            let mut store = UtxoStore::open(directory.path()).unwrap();
            assert_eq!(store.get(&first).unwrap(), Some(first_entry));
            assert_eq!(store.get(&second).unwrap(), Some(second_entry));
            assert_eq!(store.get(&third).unwrap(), Some(third_entry.clone()));
            store
                .apply_validated_batch(&[second], &[(first, replacement.clone())])
                .unwrap();
            assert_eq!(store.get(&second).unwrap(), None);
            assert_eq!(store.get(&first).unwrap(), Some(replacement.clone()));
            store.flush().unwrap();
        }

        let reopened = UtxoStore::open(directory.path()).unwrap();
        assert_eq!(reopened.len(), 4);
        assert_eq!(reopened.get(&first).unwrap(), Some(replacement));
        assert_eq!(reopened.get(&second).unwrap(), None);
        assert_eq!(reopened.get(&third).unwrap(), Some(third_entry));
        assert_eq!(reopened.get(&overwritten).unwrap(), Some(replacement_entry));
    }

    #[test]
    fn bulk_utxo_ingest_orders_little_endian_vouts() {
        let directory = tempfile::tempdir().unwrap();
        let txid = Txid::from_byte_array([42; 32]);
        let first = OutPoint::new(txid, 1);
        let second = OutPoint::new(txid, 256);
        let entry = |height| StoredUtxo {
            output: TxOut {
                value: bitcoin::Amount::from_sat(1_000),
                script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
            },
            height,
            median_time_past: height,
            coinbase: false,
        };
        let first_entry = entry(1);
        let second_entry = entry(2);
        let mut store = UtxoStore::open(directory.path()).unwrap();
        store
            .apply_validated_batch_unsynced(
                &[],
                &[(first, first_entry.clone()), (second, second_entry.clone())],
            )
            .unwrap();
        store.flush().unwrap();
        assert_eq!(store.coins.segment_count(), 1);
        assert_eq!(store.get(&first).unwrap(), Some(first_entry));
        assert_eq!(store.get(&second).unwrap(), Some(second_entry));
    }

    #[test]
    fn fresh_utxo_store_uses_prefix_partitions() {
        let directory = tempfile::tempdir().unwrap();
        let entry = |height| StoredUtxo {
            output: TxOut {
                value: bitcoin::Amount::from_sat(1_000),
                script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
            },
            height,
            median_time_past: height,
            coinbase: false,
        };
        // Pick one key from every high-byte range. This exercises every
        // independent bulk-ingest worker instead of only checking that the
        // first and last shards exist.
        let entries = (0..UTXO_SHARD_COUNT)
            .map(|partition| {
                let first_byte = (partition as u8) * 32;
                (
                    OutPoint::new(Txid::from_byte_array([first_byte; 32]), partition as u32),
                    entry(partition as u32 + 1),
                )
            })
            .collect::<Vec<_>>();

        let mut store = UtxoStore::open(directory.path()).unwrap();
        assert_eq!(store.coins.len(), UTXO_SHARD_COUNT);
        store.apply_validated_batch_unsynced(&[], &entries).unwrap();
        store.flush().unwrap();
        assert_eq!(store.coins.segment_count(), UTXO_SHARD_COUNT);
        for (outpoint, expected) in &entries {
            assert_eq!(store.get(outpoint).unwrap(), Some(expected.clone()));
        }

        let reopened = UtxoStore::open(directory.path()).unwrap();
        assert_eq!(reopened.coins.len(), UTXO_SHARD_COUNT);
        for (outpoint, expected) in entries {
            assert_eq!(reopened.get(&outpoint).unwrap(), Some(expected));
        }
    }

    #[test]
    fn unsynced_utxo_batches_are_visible_and_coalesce_before_flush() {
        let directory = tempfile::tempdir().unwrap();
        let first = OutPoint::new(Txid::from_byte_array([71; 32]), 0);
        let second = OutPoint::new(Txid::from_byte_array([72; 32]), 1);
        let entry = |value, height| StoredUtxo {
            output: TxOut {
                value: bitcoin::Amount::from_sat(value),
                script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
            },
            height,
            median_time_past: height.saturating_sub(1),
            coinbase: false,
        };
        let first_entry = entry(25_000, 20);
        let second_entry = entry(20_000, 21);
        let mut store = UtxoStore::open(directory.path()).unwrap();
        store
            .apply_validated_batch_unsynced(&[], &[(first, first_entry)])
            .unwrap();
        assert!(store.contains(&first).unwrap());
        assert_eq!(store.pending.len(), 1);
        let query = store.query(&[first, second]);

        store
            .apply_validated_batch_unsynced(&[first], &[(second, second_entry.clone())])
            .unwrap();
        assert!(!store.contains(&first).unwrap());
        assert_eq!(store.get(&first).unwrap(), None);
        assert_eq!(store.get(&second).unwrap(), Some(second_entry.clone()));
        assert_eq!(
            store.entries().unwrap(),
            vec![(second, second_entry.clone())]
        );
        assert_eq!(store.len(), 1);
        assert_eq!(store.pending.len(), 1);

        store.flush().unwrap();
        let snapshotted = query.execute().unwrap();
        assert!(snapshotted.contains_key(&first));
        assert!(!snapshotted.contains_key(&second));
        assert!(store.pending.is_empty());
        drop(store);
        let reopened = UtxoStore::open(directory.path()).unwrap();
        assert_eq!(reopened.len(), 1);
        assert_eq!(reopened.get(&first).unwrap(), None);
        assert_eq!(reopened.get(&second).unwrap(), Some(second_entry));
    }

    #[test]
    fn unsynced_utxo_chunks_are_bounded_and_marked_until_durable() {
        let directory = tempfile::tempdir().unwrap();
        let outpoint = OutPoint::new(Txid::from_byte_array([73; 32]), 0);
        let entry = StoredUtxo {
            output: TxOut {
                value: bitcoin::Amount::from_sat(10_000),
                script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
            },
            height: 22,
            median_time_past: 21,
            coinbase: false,
        };
        let mut store = UtxoStore::open(directory.path()).unwrap();
        store.pending_item_limit = 1;
        store
            .apply_validated_batch_unsynced(&[], &[(outpoint, entry.clone())])
            .unwrap();

        assert!(store.pending.is_empty());
        assert_eq!(store.get(&outpoint).unwrap(), Some(entry));
        assert!(store.unsynced_marker_path.exists());
        assert!(!store.needs_durability_checkpoint());

        store.flush().unwrap();
        assert!(!store.unsynced_marker_path.exists());
    }

    #[test]
    fn interrupted_unsynced_utxo_chunks_are_discarded_on_open() {
        let directory = tempfile::tempdir().unwrap();
        let outpoint = OutPoint::new(Txid::from_byte_array([74; 32]), 0);
        {
            let mut store = UtxoStore::open(directory.path()).unwrap();
            store
                .apply_batch(
                    &[],
                    &[(
                        outpoint,
                        StoredUtxo {
                            output: TxOut {
                                value: bitcoin::Amount::from_sat(9_000),
                                script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
                            },
                            height: 23,
                            median_time_past: 22,
                            coinbase: false,
                        },
                    )],
                )
                .unwrap();
        }
        std::fs::write(
            directory.path().join("utxos.unsynced.pending"),
            b"simulate interrupted unsynced chunks\n",
        )
        .unwrap();

        let reopened = UtxoStore::open(directory.path()).unwrap();
        assert!(reopened.is_empty());
        assert_eq!(reopened.get(&outpoint).unwrap(), None);
        assert!(!directory.path().join("utxos.unsynced.pending").exists());
    }

    #[test]
    fn complete_utxo_cache_warm_avoids_fifo_copies_and_can_trim() {
        let mut cache = UtxoReadCache::default();
        cache.configure_limit(400);
        for byte in 1..=10 {
            cache.insert_stationary(
                OutPoint::new(Txid::from_byte_array([byte; 32]), 0),
                StoredUtxo {
                    output: TxOut {
                        value: bitcoin::Amount::from_sat(u64::from(byte)),
                        script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
                    },
                    height: u32::from(byte),
                    median_time_past: 0,
                    coinbase: false,
                },
            );
        }
        assert!(cache.bytes > cache.limit);
        cache.complete = true;

        cache.trim();
        assert!(!cache.complete);
        assert!(cache.bytes <= cache.limit.saturating_mul(7) / 8);
        assert_eq!(
            cache.len(),
            cache.entries.iter().map(FastHashMap::len).sum::<usize>()
        );
        assert_eq!(
            cache.bytes,
            cache
                .entries
                .iter()
                .flat_map(FastHashMap::values)
                .map(read_cache_utxo_bytes)
                .sum::<usize>()
        );
    }

    #[test]
    fn large_utxo_flush_retains_only_recent_hot_entries() {
        let directory = tempfile::tempdir().unwrap();
        let mut store = UtxoStore::open(directory.path()).unwrap();
        {
            let mut cache = store.read_cache.lock();
            cache.limit = 4_096;
        }
        // Force the direct large-checkpoint path without needing a large
        // database fixture. The oldest entries are still durable, but only
        // the newest height window should remain decoded in memory.
        store.pending_limit_bytes = 1;
        let entries = [1u8, 2, 3, 4]
            .into_iter()
            .zip([1u32, 2, 3, 50_000])
            .map(|(byte, height)| {
                (
                    OutPoint::new(Txid::from_byte_array([byte; 32]), 0),
                    StoredUtxo {
                        output: TxOut {
                            value: bitcoin::Amount::from_sat(u64::from(byte)),
                            script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
                        },
                        height,
                        median_time_past: height,
                        coinbase: false,
                    },
                )
            })
            .collect::<Vec<_>>();
        store.entry_count = entries.len();
        for (outpoint, entry) in &entries {
            store.set_pending(*outpoint, Some(entry.clone()), true);
        }
        store.flush_pending(false).unwrap();

        let cache = store.read_cache.lock();
        assert_eq!(cache.len(), 1);
        assert!(cache.contains_key(&entries[3].0));
        assert!(!cache.contains_key(&entries[0].0));
    }

    #[test]
    fn complete_utxo_cache_answers_absence_and_tracks_pending_mutations() {
        let directory = tempfile::tempdir().unwrap();
        let first = OutPoint::new(Txid::from_byte_array([21; 32]), 0);
        let second = OutPoint::new(Txid::from_byte_array([22; 32]), 1);
        let missing = OutPoint::new(Txid::from_byte_array([23; 32]), 0);
        let ephemeral = OutPoint::new(Txid::from_byte_array([24; 32]), 0);
        let entry = |height| StoredUtxo {
            output: TxOut {
                value: bitcoin::Amount::from_sat(1_000),
                script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
            },
            height,
            median_time_past: height,
            coinbase: false,
        };
        let mut store = UtxoStore::open(directory.path()).unwrap();
        store.configure_cache_size_mib(4);
        assert_eq!(store.pending_item_limit, UTXO_PENDING_EMERGENCY_ITEMS);
        store.configure_cache_size_mib(2_048);
        assert_eq!(store.pending_item_limit, UTXO_PENDING_EMERGENCY_ITEMS);
        assert!(store.read_cache.lock().complete);
        assert!(!store.contains(&missing).unwrap());
        store.apply_batch(&[], &[(first, entry(1))]).unwrap();
        store.read_cache.lock().clear();
        assert_eq!(store.warm_complete_cache_if_fits().unwrap().unwrap().0, 1);
        assert!(store.read_cache.lock().complete);
        assert!(store.contains(&first).unwrap());
        assert!(!store.contains(&missing).unwrap());
        assert_eq!(store.get(&missing).unwrap(), None);

        store
            .apply_validated_batch_unsynced(&[first], &[(second, entry(2))])
            .unwrap();
        assert_eq!(store.pending.len(), 2);
        store
            .apply_validated_batch_unsynced(&[], &[(ephemeral, entry(3))])
            .unwrap();
        store
            .apply_validated_batch_unsynced(&[ephemeral], &[])
            .unwrap();
        assert!(!store.pending.contains_key(&ephemeral));
        store.pending_item_limit = 2;
        store.dirty_item_limit = 2;
        store
            .apply_validated_batch_unsynced(&[], &[(missing, entry(3))])
            .unwrap();
        assert!(store.needs_durability_checkpoint());
        assert!(!store.contains(&first).unwrap());
        assert!(store.contains(&second).unwrap());
        assert_eq!(store.get(&second).unwrap(), Some(entry(2)));
        store.read_cache.lock().clear();
        assert_eq!(store.warm_complete_cache_if_fits().unwrap().unwrap().0, 2);
        assert!(store.read_cache.lock().complete);
        assert!(!store.contains(&first).unwrap());
        assert!(store.contains(&second).unwrap());
        store.flush().unwrap();
        assert!(!store.needs_durability_checkpoint());
        assert!(store.read_cache.lock().complete);
        assert!(!store.contains(&first).unwrap());
        assert!(store.contains(&second).unwrap());
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
        assert!(store.read_cache.lock().contains_key(&outpoint));
        assert_eq!(store.get(&outpoint).unwrap(), Some(first));
        assert_eq!(store.read_cache.lock().len(), 1);

        store
            .apply_batch(&[outpoint], &[(outpoint, second.clone())])
            .unwrap();
        assert!(store.read_cache.lock().contains_key(&outpoint));
        assert_eq!(store.get(&outpoint).unwrap(), Some(second.clone()));
        assert_eq!(store.read_cache.lock().len(), 1);

        store.read_cache.lock().clear();
        assert_eq!(store.warm_cache().unwrap().0, 0);
        assert_eq!(store.get(&outpoint).unwrap(), Some(second));
        assert_eq!(store.warm_cache().unwrap().0, 1);

        store.clear().unwrap();
        assert_eq!(store.get(&outpoint).unwrap(), None);
        assert_eq!(store.read_cache.lock().len(), 0);
        drop(store);

        // A reopened logically empty store may still have the clear
        // tombstone in Fjall's active state; it must not regain the fresh
        // keyspace-only bulk-ingest capability.
        let reopened = UtxoStore::open(directory.path()).unwrap();
        assert!(!reopened.bulk_ingest_eligible);
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
    fn unsynced_electrum_events_are_queryable_before_the_batched_commit() {
        let directory = tempfile::tempdir().unwrap();
        let script_hash = hex::encode([73u8; 32]);
        let first = (Txid::from_byte_array([74u8; 32]), 30);
        let second = (Txid::from_byte_array([75u8; 32]), 31);
        let mut store = ElectrumHistoryStore::open(directory.path()).unwrap();
        store
            .append_entries_unsynced(&[(script_hash.clone(), vec![first])])
            .unwrap();
        store
            .append_entries_unsynced(&[(script_hash.clone(), vec![second])])
            .unwrap();

        assert_eq!(store.pending_event_count, 2);
        assert!(store.contains(&script_hash));
        assert_eq!(store.get(&script_hash).unwrap(), vec![first, second]);
        let query = store.query(&script_hash, usize::MAX).unwrap();
        assert_eq!(
            store.get_batch(std::slice::from_ref(&script_hash)).unwrap()[&script_hash],
            vec![first, second]
        );
        assert_eq!(store.entries().unwrap()[0].1, vec![first, second]);

        store.flush().unwrap();
        assert_eq!(query.execute().unwrap().unwrap(), vec![first, second]);
        assert_eq!(store.pending_event_count, 0);
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
    fn electrum_history_clear_switches_partitions_without_scanning_old_events() {
        let directory = tempfile::tempdir().unwrap();
        let first_script = hex::encode([45u8; 32]);
        let second_script = hex::encode([46u8; 32]);
        let first = (Txid::from_byte_array([47u8; 32]), 1);
        let second = (Txid::from_byte_array([48u8; 32]), 2);
        let mut store = ElectrumHistoryStore::open(directory.path()).unwrap();
        store
            .append_entries(&[(first_script.clone(), vec![first])])
            .unwrap();
        let previous_epoch = store.event_partition_epoch;
        let previous_partition = history_events_partition_name(previous_epoch);

        store.clear().unwrap();
        assert_eq!(store.event_partition_epoch, previous_epoch + 1);
        assert_eq!(store.len(), 0);
        assert!(store.get(&first_script).unwrap().is_empty());
        assert!(
            !store
                .keyspace
                .list_partitions()
                .iter()
                .any(|name| name.as_ref() == previous_partition)
        );
        store
            .append_entries(&[(second_script.clone(), vec![second])])
            .unwrap();
        drop(store);

        let reopened = ElectrumHistoryStore::open(directory.path()).unwrap();
        assert_eq!(reopened.len(), 1);
        assert!(reopened.get(&first_script).unwrap().is_empty());
        assert_eq!(reopened.get(&second_script).unwrap(), vec![second]);
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
            let reader = store.reader();
            assert_eq!(store.insert(&block).unwrap(), hash);
            assert!(store.contains(&hash));
            assert_eq!(
                store.transaction(&hash, 0).unwrap().unwrap().compute_txid(),
                txid
            );
            assert_eq!(store.merkle_branch(&hash, 0).unwrap(), Some(Vec::new()));
            assert_eq!(store.transaction(&hash, 1).unwrap(), None);
            assert_eq!(
                reader
                    .transaction(&hash, 0)
                    .unwrap()
                    .unwrap()
                    .compute_txid(),
                txid
            );
        }

        std::fs::write(directory.path().join("txblocks.index"), b"corrupt").unwrap();
        let reopened = ElectrumBlockStore::open(directory.path()).unwrap();
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
        let reader = store.reader();
        let before = store.disk_usage().unwrap();

        assert!(store.retain_only(&HashSet::from([first_hash])).unwrap());
        assert!(store.disk_usage().unwrap() < before);
        assert!(store.contains(&first_hash));
        assert!(!store.contains(&second_hash));
        assert!(store.transaction(&first_hash, 0).unwrap().is_some());
        assert!(store.transaction(&second_hash, 0).unwrap().is_none());
        assert!(reader.transaction(&first_hash, 0).unwrap().is_some());
        assert!(reader.transaction(&second_hash, 0).unwrap().is_none());
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

        let reopened = ElectrumBlockStore::open(directory.path()).unwrap();
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
    fn unsynced_peer_body_can_be_reused_from_decoded_cache() {
        let directory = tempfile::tempdir().unwrap();
        let block = Arc::new(genesis_block(Network::Regtest));
        let hash = block.block_hash();
        let mut store = BlockStore::open(directory.path()).unwrap();
        store.configure_cache_size_mib(4);
        let prepared = BlockStore::prepare_record(&block).unwrap();
        store
            .insert_prepared_unsynced_shared(Arc::clone(&block), prepared)
            .unwrap();
        store.cache_peer_block(Arc::clone(&block));

        assert_eq!(store.block_cache.len(), 1);
        let cached = store.get_shared(&hash).unwrap().unwrap();
        assert!(Arc::ptr_eq(&cached, &block));
        let (metrics, entries, _) = store.take_cache_metrics();
        assert_eq!(metrics.lookups, 1);
        assert_eq!(metrics.hits, 1);
        assert_eq!(metrics.misses, 0);
        assert_eq!(entries, 1);
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
    fn append_preallocation_keeps_logical_record_lengths() {
        let directory = tempfile::tempdir().unwrap();
        let block = genesis_block(Network::Regtest);
        let hash = block.block_hash();
        let mut store = BlockStore::open(directory.path()).unwrap();
        store.insert(&block).unwrap();
        store.insert_undo(hash, &[Vec::new()]).unwrap();

        assert_eq!(store.file.metadata().unwrap().len(), store.block_data_len);
        assert_eq!(
            store.undo_file.metadata().unwrap().len(),
            store.undo_data_len
        );
        if store.block_preallocation_enabled {
            assert!(store.block_preallocated_through >= BLOCK_PREALLOCATION_CHUNK_BYTES);
        }
        if store.undo_preallocation_enabled {
            assert!(store.undo_preallocated_through >= UNDO_PREALLOCATION_CHUNK_BYTES);
        }
    }

    #[test]
    fn read_only_store_scans_a_clean_unpublished_suffix_without_mutating_it() {
        let directory = tempfile::tempdir().unwrap();
        let block = genesis_block(Network::Regtest);
        let hash = block.block_hash();
        {
            let mut store = BlockStore::open(directory.path()).unwrap();
            store.insert_unsynced(&block).unwrap();
            store.insert_undo_unsynced(hash, &[Vec::new()]).unwrap();
        }

        // Unsynced appends deliberately leave the index-header lengths at
        // their previous durability boundary. A read-only consumer may scan
        // a complete suffix, but must not try to truncate either data file.
        let mut reopened = BlockStore::open_read_only(directory.path()).unwrap();
        assert_eq!(reopened.get(&hash).unwrap(), Some(block));
        assert_eq!(reopened.get_undo(&hash).unwrap(), Some(vec![Vec::new()]));
    }

    #[test]
    fn serving_reader_releases_decoded_blocks_after_append_buffer_flush() {
        let directory = tempfile::tempdir().unwrap();
        let block = genesis_block(Network::Regtest);
        let hash = block.block_hash();
        let mut store = BlockStore::open(directory.path()).unwrap();
        let reader = store.reader();

        store.insert_unsynced(&block).unwrap();
        assert_eq!(reader.pending_blocks.read().len(), 1);
        assert_eq!(reader.get(&hash).unwrap(), Some(block.clone()));

        store.flush_pending_block_data().unwrap();
        assert!(reader.pending_blocks.read().is_empty());
        assert_eq!(reader.get(&hash).unwrap(), Some(block));
    }

    #[test]
    fn buffered_block_frames_preserve_xor_offsets_across_mixed_appends() {
        for xor in [false, true] {
            let directory = tempfile::tempdir().unwrap();
            let mut store = BlockStore::open_with_xor(directory.path(), xor).unwrap();
            let mut expected = Vec::new();
            let mut blocks = Vec::new();
            for index in 0..8 {
                let mut block = genesis_block(Network::Regtest);
                block.header.nonce = index;
                block.txdata[0].output[0].script_pubkey =
                    bitcoin::ScriptBuf::from_bytes(vec![0x51; 100 + index as usize]);
                let payload =
                    encode_storage_payload(&serialize(&block), MAX_STORED_BLOCK_SIZE).unwrap();
                expected.extend_from_slice(&(payload.len() as u32).to_le_bytes());
                expected.extend_from_slice(&payload);
                if index % 3 == 2 {
                    store.insert(&block).unwrap();
                } else {
                    store.insert_unsynced(&block).unwrap();
                }
                assert_eq!(
                    store.reader().get(&block.block_hash()).unwrap(),
                    Some(block.clone())
                );
                blocks.push(block);
            }
            store.flush().unwrap();
            let mut actual = std::fs::read(directory.path().join("blocks.dat")).unwrap();
            store.xor_key.apply(&mut actual, 0);
            assert_eq!(actual, expected);
            drop(store);
            let mut reopened = BlockStore::open_with_xor(directory.path(), xor).unwrap();
            for block in blocks {
                assert_eq!(reopened.get(&block.block_hash()).unwrap(), Some(block));
            }
        }
    }

    #[test]
    fn buffered_block_frames_survive_automatic_buffer_rollover() {
        use rand::{RngCore, SeedableRng};
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let mut script = vec![0u8; APPEND_BUFFER_FLUSH_BYTES / 5 + 1];
        rng.fill_bytes(&mut script);
        for xor in [false, true] {
            let directory = tempfile::tempdir().unwrap();
            let mut store = BlockStore::open_with_xor(directory.path(), xor).unwrap();
            let reader = store.reader();
            let mut blocks = Vec::new();
            let mut rolled_over = false;
            for index in 0..7 {
                let mut block = genesis_block(Network::Regtest);
                block.header.nonce = index;
                block.txdata[0].output[0].script_pubkey =
                    bitcoin::ScriptBuf::from_bytes(script.clone());
                store.insert_unsynced(&block).unwrap();
                if store.pending_block_data.is_empty() {
                    rolled_over = true;
                    assert!(store.block_data_len >= APPEND_BUFFER_FLUSH_BYTES as u64);
                }
                assert_eq!(
                    reader.get(&block.block_hash()).unwrap(),
                    Some(block.clone())
                );
                blocks.push(block);
            }
            assert!(rolled_over);
            assert!(!store.pending_block_data.is_empty());
            store.flush().unwrap();
            drop(store);
            let mut reopened = BlockStore::open_with_xor(directory.path(), xor).unwrap();
            for block in blocks {
                assert_eq!(reopened.get(&block.block_hash()).unwrap(), Some(block));
            }
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

    #[test]
    fn writable_store_discards_unpublished_tail_without_scanning_data_file() {
        let directory = tempfile::tempdir().unwrap();
        let first = genesis_block(Network::Regtest);
        let mut second = first.clone();
        second.header.nonce = 1;
        let first_hash = first.block_hash();
        let second_hash = second.block_hash();
        {
            let mut store = BlockStore::open(directory.path()).unwrap();
            store.insert(&first).unwrap();
        }

        let data_path = directory.path().join("blocks.dat");
        let index_path = directory.path().join("blocks.index");
        let durable_data_len = std::fs::metadata(&data_path).unwrap().len();
        let durable_index_len = std::fs::metadata(&index_path).unwrap().len();
        let prepared = BlockStore::prepare_record(&second).unwrap();
        let mut record_bytes = (prepared.encoded.len() as u32).to_le_bytes().to_vec();
        record_bytes.extend_from_slice(&prepared.encoded);
        let mut data_file = std::fs::OpenOptions::new()
            .append(true)
            .open(&data_path)
            .unwrap();
        std::io::Write::write_all(&mut data_file, &record_bytes).unwrap();
        std::io::Write::flush(&mut data_file).unwrap();

        let mut index_bytes = Vec::new();
        BlockStore::append_unsynced_index_entry(
            &mut index_bytes,
            second_hash,
            Record {
                offset: durable_data_len,
                length: prepared.encoded.len() as u32,
            },
        );
        let mut index_file = std::fs::OpenOptions::new()
            .append(true)
            .open(&index_path)
            .unwrap();
        std::io::Write::write_all(&mut index_file, &index_bytes).unwrap();
        std::io::Write::flush(&mut index_file).unwrap();

        let mut reopened = BlockStore::open(directory.path()).unwrap();
        assert_eq!(reopened.get(&first_hash).unwrap(), Some(first));
        assert_eq!(reopened.get(&second_hash).unwrap(), None);
        assert_eq!(
            std::fs::metadata(data_path).unwrap().len(),
            durable_data_len
        );
        assert_eq!(
            std::fs::metadata(index_path).unwrap().len(),
            durable_index_len
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
        let second_hash = BlockHash::from_byte_array([7; 32]);
        let payload = vec![1, 2, 3, 4, 5];
        let second_payload = vec![6, 7, 8];
        {
            let mut store = ChainstateStore::open(directory.path()).unwrap();
            store.insert(hash, &payload).unwrap();
            store.insert(second_hash, &second_payload).unwrap();
            assert_eq!(store.get(&hash).unwrap(), Some(payload.clone()));
            assert_eq!(
                store
                    .get_many(&[hash, second_hash, BlockHash::from_byte_array([8; 32])])
                    .unwrap(),
                vec![Some(payload.clone()), Some(second_payload.clone()), None]
            );
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
