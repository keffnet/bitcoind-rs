#![deny(unsafe_op_in_unsafe_fn)]
#![warn(rust_2018_idioms, clippy::all)]

pub mod address;
pub mod asmap;
pub mod chain;
pub mod config;
pub mod electrum;
pub mod fee_estimator;
pub mod i2p;
mod ipc;
pub mod mempool;
pub mod muhash;
pub mod p2p;
pub mod portmap;
pub mod rpc;
pub(crate) mod script;
pub mod storage;
pub mod time;
pub mod tor;
pub mod validation;
pub mod wire;
pub mod zmq;

// The generated modules use crate-root paths for cross-schema references.
// Keep these private: the wire protocol is a Core compatibility surface, not
// a Rust API exposed by the node library.
#[doc(hidden)]
#[allow(dead_code)]
pub(crate) mod proxy_capnp {
    include!(concat!(env!("OUT_DIR"), "/mp/proxy_capnp.rs"));
}
#[doc(hidden)]
#[allow(dead_code)]
pub(crate) mod common_capnp {
    include!(concat!(env!("OUT_DIR"), "/ipc/common_capnp.rs"));
}
#[doc(hidden)]
#[allow(dead_code)]
pub(crate) mod echo_capnp {
    include!(concat!(env!("OUT_DIR"), "/ipc/echo_capnp.rs"));
}
#[doc(hidden)]
#[allow(dead_code)]
pub(crate) mod init_capnp {
    include!(concat!(env!("OUT_DIR"), "/ipc/init_capnp.rs"));
}
#[doc(hidden)]
#[allow(dead_code)]
pub(crate) mod mining_capnp {
    include!(concat!(env!("OUT_DIR"), "/ipc/mining_capnp.rs"));
}

use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::mem::size_of;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};
use std::path::Path;
use std::process::Command;
use std::sync::{
    Arc,
    atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering},
};
use std::time::{Duration, Instant};

use anyhow::{Context, Result, anyhow, bail};
use bitcoin::consensus::encode::deserialize;
use bitcoin::hashes::{Hash, sha256d};
use bitcoin::{Block, BlockHash, Network, OutPoint, Transaction, Txid, Wtxid};
use fs2::FileExt;
use parking_lot::{Mutex, RwLock};
use rand::{random, seq::SliceRandom};
use serde::de::{self, Deserializer, MapAccess, Visitor};
use serde::{Deserialize, Serialize};
use tokio::sync::{Notify, broadcast, oneshot};
use tracing::{debug, info, warn};

use crate::address::{NetworkEndpoint, is_core_routable_ip};
use crate::asmap::{AsMap, EMBEDDED_ASMAP_PATH};
use crate::chain::ChainState;
use crate::config::{
    Config, PeerPermissions, ProxyEndpoint, RpcCookiePermissions, core_network_blocks_dir,
    network_data_dir_name,
};
use crate::fee_estimator::{FeeEstimator, RawFeeEstimate};
use crate::mempool::{
    Mempool, MempoolChange, MempoolChangeKind, MempoolError, MempoolLoadOptions, MempoolPolicy,
};
use crate::storage::BlockStoreReader;

// Core assigns live peer IDs from zero. Address-manager entries use a
// separate sentinel so peer 0 remains distinguishable from an unconnected
// address.
const UNCONNECTED_PEER_ID: usize = usize::MAX;
const MAX_ORPHAN_TRANSACTION_WEIGHT: u64 = 400_000;
const MAX_ORPHANAGE_LATENCY_SCORE: usize = 3_000;
const RESERVED_ORPHAN_WEIGHT_PER_PEER: u64 = 404_000;
const ORPHAN_TRANSACTION_EXPIRY: Duration = Duration::from_secs(20 * 60);
const MAX_RECENTLY_REJECTED_TRANSACTIONS: usize = 4_096;
const ADDR_RESPONSE_CACHE_MIN_LIFETIME: u64 = 21 * 60 * 60;
const ADDR_RESPONSE_CACHE_RANDOM_LIFETIME: u64 = 6 * 60 * 60;
const ADDR_RELAY_DESTINATIONS: usize = 2;
const ADDR_RELAY_DESTINATION_ROTATION: u64 = 24 * 60 * 60;
// Core's AddrMan stores at most 10,000 entries across its new and tried
// tables. Keep the same bound for both the legacy IP table and BIP155 table.
const MAX_KNOWN_ADDRESSES: usize = 10_000;
const ADDRMAN_TRIED_BUCKET_COUNT: usize = 256;
const ADDRMAN_BUCKET_SIZE: usize = 64;
const ADDRMAN_SECRET_FILE: &str = "addrman.key";
const BLOCK_RELAY_ONLY_ANCHORS_FILE: &str = "anchors.json";
pub(crate) const MAX_BLOCK_RELAY_ONLY_ANCHORS: usize = 2;
const MAX_OUTBOUND_FULL_RELAY_CONNECTIONS: usize = 8;
pub(crate) const EXTRA_PEER_CHECK_INTERVAL: Duration = Duration::from_secs(45);
const STALE_TIP_CHECK_INTERVAL_SECS: u64 = 10 * 60;
const EXTRA_BLOCK_RELAY_ONLY_PEER_INTERVAL_SECS: u64 = 5 * 60;
const MINIMUM_EXTRA_PEER_CONNECT_TIME_SECS: u64 = 30;
const COINSTATS_CLEAN_SHUTDOWN_HEIGHT_FILE: &str = "clean_shutdown_height";
const LARGE_WORK_INVALID_CHAIN_WARNING: &str = "Warning: Found invalid chain more than 6 blocks longer than our best chain. This could be due to database corruption or consensus incompatibility with peers.";

fn addrman_append_compact_size(input: &mut Vec<u8>, value: usize) {
    let value = u64::try_from(value).expect("address-manager vector length fits u64");
    if value <= 252 {
        input.push(value as u8);
    } else if value <= u64::from(u16::MAX) {
        input.push(253);
        input.extend_from_slice(&(value as u16).to_le_bytes());
    } else if value <= u64::from(u32::MAX) {
        input.push(254);
        input.extend_from_slice(&(value as u32).to_le_bytes());
    } else {
        input.push(255);
        input.extend_from_slice(&value.to_le_bytes());
    }
}

fn addrman_hash<F>(key: &[u8; 32], append: F) -> u64
where
    F: FnOnce(&mut Vec<u8>),
{
    let mut input = key.to_vec();
    append(&mut input);
    let digest = sha256d::Hash::hash(&input).to_byte_array();
    u64::from_le_bytes(digest[..8].try_into().expect("hash has eight-byte prefix"))
}

fn addrman_endpoint_key(endpoint: &NetworkEndpoint) -> Vec<u8> {
    let mut key = match endpoint {
        NetworkEndpoint::Ip(address) => match address.ip() {
            IpAddr::V4(address) => {
                let mut key = vec![0; 10];
                key.extend_from_slice(&[0xff, 0xff]);
                key.extend_from_slice(&address.octets());
                key
            }
            IpAddr::V6(address) => address.octets().to_vec(),
        },
        NetworkEndpoint::Dns { host, .. } => host.as_bytes().to_vec(),
        NetworkEndpoint::OnionV2 { address, .. } => address.to_vec(),
        NetworkEndpoint::OnionV3 { address, .. } => address.to_vec(),
        NetworkEndpoint::I2p { address, .. } => address.to_vec(),
        NetworkEndpoint::Cjdns { address, .. } => address.octets().to_vec(),
    };
    key.extend_from_slice(&endpoint.port().to_be_bytes());
    key
}

fn addrman_group(endpoint: &NetworkEndpoint) -> Vec<u8> {
    match endpoint {
        NetworkEndpoint::Ip(address) => match address.ip() {
            IpAddr::V4(address) => vec![1, address.octets()[0], address.octets()[1]],
            IpAddr::V6(address) => {
                let octets = address.octets();
                vec![2, octets[0], octets[1], octets[2], octets[3]]
            }
        },
        NetworkEndpoint::Cjdns { address, .. } => {
            let octets = address.octets();
            vec![5, octets[0], octets[1] | 0x0f]
        }
        NetworkEndpoint::Dns { host, .. } => {
            let digest = bitcoin::hashes::sha256::Hash::hash(host.to_ascii_lowercase().as_bytes());
            let mut group = vec![0];
            group.extend_from_slice(&digest[..4]);
            group
        }
        NetworkEndpoint::OnionV2 { address, .. } => vec![3, address[0] | 0x0f],
        NetworkEndpoint::OnionV3 { address, .. } => vec![3, address[0] | 0x0f],
        NetworkEndpoint::I2p { address, .. } => vec![4, address[0] | 0x0f],
    }
}

fn addrman_tried_slot(key: &[u8; 32], endpoint: &NetworkEndpoint) -> (usize, usize) {
    let endpoint_key = addrman_endpoint_key(endpoint);
    let endpoint_group = addrman_group(endpoint);
    let hash1 = addrman_hash(key, |input| {
        addrman_append_compact_size(input, endpoint_key.len());
        input.extend_from_slice(&endpoint_key);
    });
    let bucket = addrman_hash(key, |input| {
        addrman_append_compact_size(input, endpoint_group.len());
        input.extend_from_slice(&endpoint_group);
        input.extend_from_slice(&(hash1 % 8).to_le_bytes());
    }) as usize
        % ADDRMAN_TRIED_BUCKET_COUNT;
    let position = addrman_hash(key, |input| {
        input.push(b'K');
        input.extend_from_slice(&(bucket as i32).to_le_bytes());
        addrman_append_compact_size(input, endpoint_key.len());
        input.extend_from_slice(&endpoint_key);
    }) as usize
        % ADDRMAN_BUCKET_SIZE;
    (bucket, position)
}
pub(crate) const MAX_BLOCKS_IN_TRANSIT_PER_PEER: usize = 16;
pub(crate) const MAX_CMPCTBLOCKS_INFLIGHT_PER_BLOCK: usize = 3;
const BLOCK_DOWNLOAD_WINDOW: u32 = 1024;
const NODE_NETWORK_LIMITED_MIN_BLOCKS: u32 = 288;
const BLOCK_STALLING_TIMEOUT_DEFAULT: Duration = Duration::from_secs(2);
const BLOCK_STALLING_TIMEOUT_MAX: Duration = Duration::from_secs(64);
const MAX_ADDR_RATE_PER_SECOND: f64 = 0.1;
const MAX_ADDR_PROCESSING_TOKEN_BUCKET: f64 = 1_000.0;
const MEMPOOL_EXPIRY_INTERVAL: Duration = Duration::from_secs(60);
const FEE_ESTIMATOR_FLUSH_INTERVAL: Duration = Duration::from_secs(60 * 60);
const MAX_EXTERNAL_BLOCK_RECORD_SIZE: usize = 4 * 1024 * 1024;
const EXTERNAL_BLOCK_READ_SIZE: usize = 64 * 1024;
// Core's DisconnectedBlockTransactions cap used while processing a reorg.
const MAX_DISCONNECTED_TX_POOL_BYTES: usize = 20_000_000;
const MAX_UPLOAD_TIMEFRAME_SECS: u64 = 24 * 60 * 60;
const MAX_UPLOAD_BLOCK_RESERVE_BYTES: u64 = 4_000_000;
const HISTORICAL_BLOCK_AGE_SECS: u64 = 7 * 24 * 60 * 60;
const MAX_TIME_OFFSET_SAMPLES: usize = 50;
const CLOCK_OUT_OF_SYNC_THRESHOLD_SECS: u64 = 10 * 60;
const P2P_MESSAGE_TYPE_OTHER: &str = "*other*";
// Keep this list aligned with Core's ALL_NET_MESSAGE_TYPES. Unknown received
// commands are aggregated under P2P_MESSAGE_TYPE_OTHER to avoid an unbounded
// per-peer map in getpeerinfo.
const KNOWN_P2P_MESSAGE_TYPES: &[&str] = &[
    "version",
    "verack",
    "addr",
    "addrv2",
    "sendaddrv2",
    "inv",
    "getdata",
    "merkleblock",
    "getblocks",
    "getheaders",
    "tx",
    "headers",
    "block",
    "getaddr",
    "mempool",
    "ping",
    "pong",
    "notfound",
    "filterload",
    "filteradd",
    "filterclear",
    "sendheaders",
    "feefilter",
    "sendcmpct",
    "cmpctblock",
    "getblocktxn",
    "blocktxn",
    "getcfilters",
    "cfilter",
    "getcfheaders",
    "cfheaders",
    "getcfcheckpt",
    "cfcheckpt",
    "wtxidrelay",
    "sendtxrcncl",
];
pub(crate) const PRIVATE_BROADCAST_PEERS_PER_TRANSACTION: usize = 3;
pub(crate) const PRIVATE_BROADCAST_RETRY_SECS: u64 = 60;
pub(crate) const MAX_INITIAL_BROADCAST_DELAY_SECS: u64 = 15 * 60;

/// Match Core's default `SanitizeString` rule for peer user-agent strings.
///
/// Peer subversions are untrusted handshake data. Core removes every byte
/// outside this conservative printable set before retaining the value for
/// diagnostics and RPC output.
fn sanitize_peer_user_agent(user_agent: &str) -> String {
    user_agent
        .chars()
        .filter(|character| {
            character.is_ascii_alphanumeric()
                || matches!(
                    character,
                    ' ' | '.' | ',' | ';' | '-' | '_' | '/' | ':' | '?' | '@' | '(' | ')'
                )
        })
        .collect()
}

fn received_p2p_message_type(command: &str) -> &str {
    if KNOWN_P2P_MESSAGE_TYPES.contains(&command) {
        command
    } else {
        P2P_MESSAGE_TYPE_OTHER
    }
}

fn expand_notify_command(command: &str, argument: Option<&str>) -> String {
    command.replace("%s", argument.unwrap_or_default())
}

async fn wait_for_shutdown_signal() -> Result<()> {
    #[cfg(unix)]
    {
        use tokio::signal::unix::{SignalKind, signal};

        let mut interrupt = signal(SignalKind::interrupt()).context("installing SIGINT handler")?;
        let mut terminate =
            signal(SignalKind::terminate()).context("installing SIGTERM handler")?;
        tokio::select! {
            _ = interrupt.recv() => Ok(()),
            _ = terminate.recv() => Ok(()),
        }
    }
    #[cfg(not(unix))]
    {
        tokio::signal::ctrl_c()
            .await
            .context("waiting for shutdown signal")
    }
}

pub(crate) struct StartupLatch {
    remaining: AtomicUsize,
    sender: parking_lot::Mutex<Option<oneshot::Sender<()>>>,
}

impl StartupLatch {
    pub(crate) fn new(sender: oneshot::Sender<()>, services: usize) -> Arc<Self> {
        Arc::new(Self {
            remaining: AtomicUsize::new(services),
            sender: parking_lot::Mutex::new(Some(sender)),
        })
    }

    pub(crate) fn service_ready(&self) {
        if self.remaining.fetch_sub(1, Ordering::AcqRel) == 1
            && let Some(sender) = self.sender.lock().take()
        {
            let _ = sender.send(());
        }
    }
}

fn run_notify_command(command: Option<&str>, argument: Option<&str>) {
    let Some(command) = command else {
        return;
    };
    let expanded = expand_notify_command(command, argument);
    let result = {
        #[cfg(windows)]
        {
            Command::new("cmd").args(["/C", &expanded]).spawn()
        }
        #[cfg(not(windows))]
        {
            Command::new("sh").args(["-c", &expanded]).spawn()
        }
    };
    if let Err(error) = result {
        warn!(%error, command = %expanded, "notification command could not be started");
    }
}

fn run_alert_notify_command(command: Option<&str>, message: &str) {
    let safe_message = message
        .chars()
        .filter(|character| {
            character.is_ascii_alphanumeric()
                || matches!(
                    character,
                    ' ' | '.' | ',' | ';' | '-' | '_' | '/' | ':' | '?' | '@' | '(' | ')'
                )
        })
        .collect::<String>();
    let shell_argument = format!("'{safe_message}'");
    run_notify_command(command, Some(&shell_argument));
}

struct CompactExtraTransactions {
    limit: usize,
    transactions: VecDeque<Transaction>,
}

/// A bounded cache of transactions rejected by peer admission. Core uses the
/// reject cache to avoid requesting the same low-fee or policy-invalid
/// transaction from every announcing peer, while explicit orphan-parent
/// requests can still bypass it.
struct RecentlyRejectedTransactions {
    hashes: HashSet<BlockHash>,
    non_retryable: HashSet<BlockHash>,
    order: VecDeque<BlockHash>,
}

impl RecentlyRejectedTransactions {
    fn new() -> Self {
        Self {
            hashes: HashSet::new(),
            non_retryable: HashSet::new(),
            order: VecDeque::new(),
        }
    }

    fn insert(&mut self, transaction: &Transaction, include_txid: bool) {
        self.insert_with_kind(transaction, include_txid, false);
    }

    fn insert_non_retryable(&mut self, transaction: &Transaction, include_txid: bool) {
        self.insert_with_kind(transaction, include_txid, true);
    }

    fn insert_with_kind(
        &mut self,
        transaction: &Transaction,
        include_txid: bool,
        non_retryable: bool,
    ) {
        let wtxid = BlockHash::from_raw_hash(transaction.compute_wtxid().to_raw_hash());
        let txid = BlockHash::from_raw_hash(transaction.compute_txid().to_raw_hash());
        let hashes = if include_txid && txid != wtxid {
            vec![txid, wtxid]
        } else {
            vec![wtxid]
        };
        for hash in hashes {
            if self.hashes.insert(hash) {
                self.order.push_back(hash);
            }
            if non_retryable {
                self.non_retryable.insert(hash);
            }
        }
        while self.order.len() > MAX_RECENTLY_REJECTED_TRANSACTIONS.saturating_mul(2) {
            if let Some(hash) = self.order.pop_front() {
                self.hashes.remove(&hash);
                self.non_retryable.remove(&hash);
            }
        }
    }

    fn remove(&mut self, transaction: &Transaction) {
        for hash in [
            BlockHash::from_raw_hash(transaction.compute_txid().to_raw_hash()),
            BlockHash::from_raw_hash(transaction.compute_wtxid().to_raw_hash()),
        ] {
            if self.hashes.remove(&hash) {
                self.order.retain(|queued| *queued != hash);
            }
            self.non_retryable.remove(&hash);
        }
    }

    fn clear(&mut self) {
        self.hashes.clear();
        self.non_retryable.clear();
        self.order.clear();
    }

    fn contains(&self, hash: BlockHash) -> bool {
        self.hashes.contains(&hash)
    }

    fn contains_non_retryable(&self, hash: BlockHash) -> bool {
        self.non_retryable.contains(&hash)
    }
}

/// Transactions disconnected during a normal reorg are queued in Core's
/// order and bounded independently of the mempool size.  The front is the
/// newest transaction; draining from the back restores the oldest first so
/// parent transactions are available before descendants.
#[derive(Default)]
struct DisconnectedTransactionPool {
    transactions: VecDeque<Transaction>,
    txids: HashSet<Txid>,
    memory_usage: usize,
}

impl DisconnectedTransactionPool {
    fn add_block(&mut self, block: &Block) -> Vec<Transaction> {
        self.add_transactions(&block.txdata)
    }

    fn add_transactions(&mut self, transactions: &[Transaction]) -> Vec<Transaction> {
        let mut evicted = Vec::new();
        for transaction in transactions.iter().rev() {
            let txid = transaction.compute_txid();
            if !self.txids.insert(txid) {
                continue;
            }
            self.memory_usage = self
                .memory_usage
                .saturating_add(disconnected_transaction_memory_usage(transaction));
            self.transactions.push_back(transaction.clone());
        }
        while self.memory_usage > MAX_DISCONNECTED_TX_POOL_BYTES {
            let Some(transaction) = self.transactions.pop_front() else {
                break;
            };
            self.txids.remove(&transaction.compute_txid());
            self.memory_usage = self
                .memory_usage
                .saturating_sub(disconnected_transaction_memory_usage(&transaction));
            evicted.push(transaction);
        }
        evicted
    }

    fn remove_for_block(&mut self, block: &Block) {
        for transaction in &block.txdata {
            let txid = transaction.compute_txid();
            if !self.txids.remove(&txid) {
                continue;
            }
            if let Some(position) = self
                .transactions
                .iter()
                .position(|queued| queued.compute_txid() == txid)
            {
                if let Some(removed) = self.transactions.remove(position) {
                    self.memory_usage = self
                        .memory_usage
                        .saturating_sub(disconnected_transaction_memory_usage(&removed));
                }
            }
        }
    }

    fn take_oldest_first(self) -> impl Iterator<Item = Transaction> {
        self.transactions.into_iter().rev()
    }
}

fn disconnected_transaction_memory_usage(transaction: &Transaction) -> usize {
    // Core's RecursiveDynamicUsage counts transaction-owned allocations plus
    // its list/hash-map nodes. Rust's transaction fields use different
    // containers, so use a deterministic conservative estimate covering the
    // same categories and the serialized script/witness payloads.
    let mut usage = size_of::<Transaction>()
        .saturating_add(
            transaction
                .input
                .len()
                .saturating_mul(size_of::<bitcoin::TxIn>()),
        )
        .saturating_add(
            transaction
                .output
                .len()
                .saturating_mul(size_of::<bitcoin::TxOut>()),
        )
        .saturating_add(size_of::<Txid>() + size_of::<usize>() * 4);
    for input in &transaction.input {
        usage = usage.saturating_add(input.script_sig.as_bytes().len());
        let witness = input.witness.to_vec();
        usage = usage.saturating_add(witness.capacity().saturating_mul(size_of::<Vec<u8>>()));
        for item in witness {
            usage = usage.saturating_add(item.capacity());
        }
    }
    for output in &transaction.output {
        usage = usage.saturating_add(output.script_pubkey.as_bytes().len());
    }
    usage
}

impl CompactExtraTransactions {
    fn new(limit: usize) -> Self {
        Self {
            limit,
            transactions: VecDeque::with_capacity(limit.min(1_024)),
        }
    }

    fn insert(&mut self, transaction: Transaction) {
        if self.limit == 0 {
            return;
        }
        if self.transactions.len() == self.limit {
            self.transactions.pop_front();
        }
        self.transactions.push_back(transaction);
    }

    fn snapshot(&self) -> Vec<Transaction> {
        self.transactions.iter().cloned().collect()
    }
}

fn core_block_download_timeout(
    block_interval: Duration,
    other_downloading_peers: usize,
) -> Duration {
    let per_peer = Duration::from_secs(block_interval.as_secs() / 2);
    block_interval.saturating_add(
        per_peer.saturating_mul(u32::try_from(other_downloading_peers).unwrap_or(u32::MAX)),
    )
}

struct ExternalBlockReader {
    file: File,
    path: std::path::PathBuf,
    magic: Vec<u8>,
    buffer: Vec<u8>,
    buffer_start: usize,
    read_buffer: [u8; EXTERNAL_BLOCK_READ_SIZE],
    eof: bool,
}

impl ExternalBlockReader {
    fn new(file: File, path: &Path, magic: Vec<u8>) -> Self {
        Self {
            file,
            path: path.to_owned(),
            magic,
            buffer: Vec::with_capacity(MAX_EXTERNAL_BLOCK_RECORD_SIZE + 8),
            buffer_start: 0,
            read_buffer: [0; EXTERNAL_BLOCK_READ_SIZE],
            eof: false,
        }
    }

    fn available(&self) -> usize {
        self.buffer.len().saturating_sub(self.buffer_start)
    }

    fn compact(&mut self) {
        if self.buffer_start >= EXTERNAL_BLOCK_READ_SIZE
            && self.buffer_start.saturating_mul(2) >= self.buffer.len()
        {
            self.buffer.drain(..self.buffer_start);
            self.buffer_start = 0;
        }
    }

    fn discard(&mut self, bytes: usize) {
        self.buffer_start = self.buffer_start.saturating_add(bytes);
        self.compact();
    }

    fn fill_to(&mut self, required: usize) -> Result<bool> {
        while self.available() < required && !self.eof {
            self.compact();
            let read = self
                .file
                .read(&mut self.read_buffer)
                .with_context(|| format!("reading block file {}", self.path.display()))?;
            if read == 0 {
                self.eof = true;
                break;
            }
            self.buffer.extend_from_slice(&self.read_buffer[..read]);
        }
        Ok(self.available() >= required)
    }

    fn next_block(&mut self) -> Result<Option<Block>> {
        loop {
            if !self.fill_to(self.magic.len())? {
                return Ok(None);
            }
            let candidate = {
                let available = &self.buffer[self.buffer_start..];
                available
                    .windows(self.magic.len())
                    .position(|bytes| bytes == self.magic.as_slice())
            };
            let Some(relative_magic) = candidate else {
                // Preserve enough bytes for a network marker split between
                // two read buffers. The discarded prefix is arbitrary data
                // that Core's importer would scan past.
                self.discard(self.available().saturating_sub(self.magic.len() - 1));
                continue;
            };
            let header_size = relative_magic.saturating_add(8);
            if !self.fill_to(header_size)? {
                // A partial record header at EOF is an incomplete tail.
                return Ok(None);
            }
            let record_offset = self.buffer_start.saturating_add(relative_magic);
            let length = u32::from_le_bytes(
                self.buffer[record_offset + 4..record_offset + 8]
                    .try_into()
                    .expect("record header has four length bytes"),
            ) as usize;
            if !(80..=MAX_EXTERNAL_BLOCK_RECORD_SIZE).contains(&length) {
                // Rewind by one byte so a later occurrence of the magic
                // inside malformed data can still be considered.
                self.discard(relative_magic.saturating_add(1));
                continue;
            }
            let record_size = header_size.saturating_add(length);
            if !self.fill_to(record_size)? {
                // Ignore an incomplete final record while retaining the
                // valid prefix, matching Core's EOF behavior.
                return Ok(None);
            }
            let payload_start = record_offset.saturating_add(8);
            let payload_end = payload_start.saturating_add(length);
            let block = deserialize::<Block>(&self.buffer[payload_start..payload_end]);
            if let Ok(block) = block {
                self.discard(record_size);
                return Ok(Some(block));
            }
            self.discard(relative_magic.saturating_add(1));
        }
    }
}

fn connect_external_pending(
    chain: &mut ChainState,
    pending: &mut Vec<Block>,
    path: &Path,
) -> Result<(usize, bool)> {
    let mut remaining = Vec::with_capacity(pending.len());
    let mut imported = 0usize;
    let mut progress = false;
    for block in pending.drain(..) {
        let hash = block.block_hash();
        if chain.header_by_hash(&hash).is_some() && chain.block(&hash)?.is_some() {
            continue;
        }
        let parent_hash = block.header.prev_blockhash;
        if chain.header_by_hash(&parent_hash).is_none() || chain.block(&parent_hash)?.is_none() {
            remaining.push(block);
            continue;
        }
        chain
            .connect_block(block)
            .with_context(|| format!("connecting block {hash} from {}", path.display()))?;
        imported = imported.saturating_add(1);
        progress = true;
    }
    *pending = remaining;
    Ok((imported, progress))
}

fn import_external_block_file(
    chain: &mut ChainState,
    path: &Path,
    network: Network,
    signet_challenge: Option<&[u8]>,
) -> Result<usize> {
    let file =
        File::open(path).with_context(|| format!("reading block file {}", path.display()))?;
    let magic = wire::network_magic_with_signet_challenge(network, signet_challenge).to_vec();
    let mut reader = ExternalBlockReader::new(file, path, magic);
    let mut pending = Vec::new();
    let mut imported = 0usize;
    while let Some(block) = reader.next_block()? {
        pending.push(block);
        let (count, _) = connect_external_pending(chain, &mut pending, path)?;
        imported = imported.saturating_add(count);
    }
    while !pending.is_empty() {
        let (count, progress) = connect_external_pending(chain, &mut pending, path)?;
        imported = imported.saturating_add(count);
        if !progress {
            let block = &pending[0];
            bail!(
                "block file {} contains block {} with an unknown or unavailable parent {}",
                path.display(),
                block.block_hash(),
                block.header.prev_blockhash
            );
        }
    }
    Ok(imported)
}

#[derive(Clone, Copy, Debug, Default)]
struct OutboundUsage {
    cycle_start: u64,
    bytes: u64,
}

fn outbound_time_left_in_cycle(target: u64, usage: OutboundUsage, now: u64) -> u64 {
    if target == 0 {
        return 0;
    }
    if usage.cycle_start == 0 {
        return MAX_UPLOAD_TIMEFRAME_SECS;
    }
    usage
        .cycle_start
        .saturating_add(MAX_UPLOAD_TIMEFRAME_SECS)
        .saturating_sub(now)
}

fn outbound_target_reached(
    target: u64,
    usage: OutboundUsage,
    now: u64,
    historical_block_serving_limit: bool,
) -> bool {
    if target == 0 {
        return false;
    }
    if historical_block_serving_limit {
        let time_left = outbound_time_left_in_cycle(target, usage, now);
        let buffer = (time_left / (10 * 60)).saturating_mul(MAX_UPLOAD_BLOCK_RESERVE_BYTES);
        buffer >= target || usage.bytes >= target.saturating_sub(buffer)
    } else {
        usage.bytes >= target
    }
}

struct OrphanEntry {
    transaction: Transaction,
    // Core records orphan entry and expiration timestamps against its node
    // clock, including regtest mocktime. Keep the wall-clock Instant out of
    // the authoritative timestamp so getorphantxs and expiration move with
    // setmocktime.
    added_at: u64,
    announcers: HashSet<usize>,
}

#[derive(Default)]
struct OrphanPool {
    entries: HashMap<Wtxid, OrphanEntry>,
    by_prevout: HashMap<OutPoint, HashSet<Wtxid>>,
    insertion_order: VecDeque<Wtxid>,
}

impl OrphanPool {
    fn add(&mut self, transaction: Transaction, peer_id: Option<usize>) -> bool {
        let announcers = peer_id.into_iter().collect();
        self.add_entry(OrphanEntry {
            transaction,
            added_at: crate::time::unix_time(),
            announcers,
        })
    }

    fn add_entry(&mut self, entry: OrphanEntry) -> bool {
        self.prune_expired();
        let wtxid = entry.transaction.compute_wtxid();
        if let Some(existing) = self.entries.get_mut(&wtxid) {
            for peer_id in entry.announcers {
                existing.announcers.insert(peer_id);
            }
            return false;
        }
        if entry.transaction.weight().to_wu() > MAX_ORPHAN_TRANSACTION_WEIGHT
            || entry
                .added_at
                .saturating_add(ORPHAN_TRANSACTION_EXPIRY.as_secs())
                <= crate::time::unix_time()
        {
            return false;
        }
        for input in &entry.transaction.input {
            self.by_prevout
                .entry(input.previous_output)
                .or_default()
                .insert(wtxid);
        }
        self.entries.insert(wtxid, entry);
        self.insertion_order.push_back(wtxid);
        self.limit_orphans();
        true
    }

    fn add_announcers(&mut self, transaction: &Transaction, peer_ids: &[usize]) -> bool {
        self.prune_expired();
        let Some(entry) = self.entries.get_mut(&transaction.compute_wtxid()) else {
            return false;
        };
        let mut added = false;
        for peer_id in peer_ids {
            added |= entry.announcers.insert(*peer_id);
        }
        added
    }

    fn announcers(&mut self, transaction: &Transaction) -> Vec<usize> {
        self.prune_expired();
        let Some(entry) = self.entries.get(&transaction.compute_wtxid()) else {
            return Vec::new();
        };
        let mut peer_ids = entry.announcers.iter().copied().collect::<Vec<_>>();
        peer_ids.sort_unstable();
        peer_ids
    }

    fn add_inventory_announcer(&mut self, hash: BlockHash, witness: bool, peer_id: usize) -> bool {
        self.prune_expired();
        let matching_wtxids = if witness {
            let wtxid = Wtxid::from_byte_array(hash.to_byte_array());
            self.entries
                .contains_key(&wtxid)
                .then_some(wtxid)
                .into_iter()
                .collect::<Vec<_>>()
        } else {
            let txid = Txid::from_byte_array(hash.to_byte_array());
            self.entries
                .iter()
                .filter_map(|(wtxid, entry)| {
                    (entry.transaction.compute_txid() == txid).then_some(*wtxid)
                })
                .collect::<Vec<_>>()
        };
        let mut added = false;
        for wtxid in matching_wtxids {
            if let Some(entry) = self.entries.get_mut(&wtxid) {
                added |= entry.announcers.insert(peer_id);
            }
        }
        added
    }

    fn has_inventory(&mut self, hash: BlockHash, witness: bool) -> bool {
        self.prune_expired();
        if witness {
            return self
                .entries
                .contains_key(&Wtxid::from_byte_array(hash.to_byte_array()));
        }
        let txid = Txid::from_byte_array(hash.to_byte_array());
        self.entries.values().any(|entry| {
            let transaction = &entry.transaction;
            transaction.compute_txid() == txid
                && transaction.compute_txid().to_raw_hash()
                    == transaction.compute_wtxid().to_raw_hash()
        })
    }

    fn transaction_for_inventory(&mut self, hash: BlockHash, witness: bool) -> Option<Transaction> {
        self.prune_expired();
        if witness {
            return self
                .entries
                .get(&Wtxid::from_byte_array(hash.to_byte_array()))
                .map(|entry| entry.transaction.clone());
        }
        let txid = Txid::from_byte_array(hash.to_byte_array());
        self.entries
            .values()
            .find(|entry| entry.transaction.compute_txid() == txid)
            .map(|entry| entry.transaction.clone())
    }

    fn remove(&mut self, wtxid: &Wtxid) -> Option<OrphanEntry> {
        let entry = self.entries.remove(wtxid)?;
        for input in &entry.transaction.input {
            if let Some(children) = self.by_prevout.get_mut(&input.previous_output) {
                children.remove(wtxid);
                if children.is_empty() {
                    self.by_prevout.remove(&input.previous_output);
                }
            }
        }
        self.insertion_order.retain(|queued| queued != wtxid);
        Some(entry)
    }

    fn remove_announcement(&mut self, wtxid: &Wtxid, peer_id: usize) -> bool {
        let remove_transaction = match self.entries.get_mut(wtxid) {
            Some(entry) => {
                entry.announcers.remove(&peer_id);
                entry.announcers.is_empty()
            }
            None => return false,
        };
        if remove_transaction {
            self.remove(wtxid);
        }
        true
    }

    fn take_children(&mut self, parent: &Transaction) -> Vec<OrphanEntry> {
        self.prune_expired();
        let parent_txid = parent.compute_txid();
        let mut wtxids = HashSet::new();
        for vout in 0..parent.output.len() {
            let outpoint = OutPoint::new(parent_txid, vout as u32);
            if let Some(children) = self.by_prevout.get(&outpoint) {
                wtxids.extend(children.iter().copied());
            }
        }
        let mut wtxids: Vec<_> = wtxids.into_iter().collect();
        wtxids.sort_by_key(ToString::to_string);
        wtxids
            .into_iter()
            .filter_map(|wtxid| self.remove(&wtxid))
            .collect()
    }

    fn erase_for_peer(&mut self, peer_id: usize) {
        let wtxids: Vec<_> = self
            .entries
            .iter()
            .filter_map(|(wtxid, entry)| entry.announcers.contains(&peer_id).then_some(*wtxid))
            .collect();
        for wtxid in wtxids {
            self.remove_announcement(&wtxid, peer_id);
        }
        self.limit_orphans();
    }

    fn transactions(&mut self) -> Vec<OrphanTransaction> {
        self.prune_expired();
        let mut transactions = self
            .entries
            .values()
            .map(|entry| {
                let mut peer_ids: Vec<_> = entry.announcers.iter().copied().collect();
                peer_ids.sort_unstable();
                OrphanTransaction {
                    transaction: entry.transaction.clone(),
                    peer_ids,
                    entry_time: entry.added_at,
                    expiration_time: entry
                        .added_at
                        .saturating_add(ORPHAN_TRANSACTION_EXPIRY.as_secs()),
                }
            })
            .collect::<Vec<_>>();
        transactions.sort_by_key(|entry| entry.transaction.compute_txid().to_string());
        transactions
    }

    fn erase_for_block(&mut self, block: &Block) -> usize {
        let mut wtxids = HashSet::new();
        for transaction in &block.txdata {
            let transaction_id = transaction.compute_wtxid();
            if self.entries.contains_key(&transaction_id) {
                wtxids.insert(transaction_id);
            }
            for input in &transaction.input {
                if let Some(children) = self.by_prevout.get(&input.previous_output) {
                    wtxids.extend(children.iter().copied());
                }
            }
        }
        let mut erased = 0;
        for wtxid in wtxids {
            if self.remove(&wtxid).is_some() {
                erased += 1;
            }
        }
        self.limit_orphans();
        erased
    }

    fn len(&mut self) -> usize {
        self.prune_expired();
        self.entries.len()
    }

    fn contains_txid(&mut self, txid: Txid) -> bool {
        self.prune_expired();
        self.entries
            .values()
            .any(|entry| entry.transaction.compute_txid() == txid)
    }

    fn contains_wtxid(&mut self, wtxid: Wtxid) -> bool {
        self.prune_expired();
        self.entries.contains_key(&wtxid)
    }

    fn contains_nonwitness_txid(&mut self, txid: Txid) -> bool {
        self.prune_expired();
        self.entries.values().any(|entry| {
            let transaction = &entry.transaction;
            transaction.compute_txid() == txid
                && transaction.compute_txid().to_raw_hash()
                    == transaction.compute_wtxid().to_raw_hash()
        })
    }

    fn prune_expired(&mut self) {
        let now = crate::time::unix_time();
        while let Some(txid) = self.insertion_order.front().copied() {
            let expired = self.entries.get(&txid).is_none_or(|entry| {
                entry
                    .added_at
                    .saturating_add(ORPHAN_TRANSACTION_EXPIRY.as_secs())
                    <= now
            });
            if !expired {
                break;
            }
            self.insertion_order.pop_front();
            self.remove(&txid);
        }
    }

    fn total_weight(&self) -> u64 {
        self.entries
            .values()
            .map(|entry| entry.transaction.weight().to_wu())
            .sum()
    }

    fn total_latency_score(&self) -> usize {
        self.entries
            .values()
            .map(|entry| 1 + entry.transaction.input.len() / 10)
            .sum()
    }

    fn peer_stats(&self) -> HashMap<usize, (u64, usize)> {
        let mut stats = HashMap::new();
        for entry in self.entries.values() {
            let weight = entry.transaction.weight().to_wu();
            let latency = 1 + entry.transaction.input.len() / 10;
            for peer_id in &entry.announcers {
                let peer = stats.entry(*peer_id).or_insert((0u64, 0usize));
                peer.0 = peer.0.saturating_add(weight);
                peer.1 = peer.1.saturating_add(latency);
            }
        }
        stats
    }

    fn limit_orphans(&mut self) {
        loop {
            let stats = self.peer_stats();
            let peer_count = stats.len().max(1) as u64;
            let max_global_weight = RESERVED_ORPHAN_WEIGHT_PER_PEER.saturating_mul(peer_count);
            if self.total_latency_score() <= MAX_ORPHANAGE_LATENCY_SCORE
                && self.total_weight() <= max_global_weight
            {
                return;
            }

            let max_peer_latency = (MAX_ORPHANAGE_LATENCY_SCORE / stats.len().max(1)).max(1);
            let Some((&worst_peer, _)) =
                stats.iter().max_by(|(left_id, left), (right_id, right)| {
                    let left_score = (left.0 as u128)
                        .saturating_mul(max_peer_latency as u128)
                        .max(
                            (left.1 as u128)
                                .saturating_mul(RESERVED_ORPHAN_WEIGHT_PER_PEER as u128),
                        );
                    let right_score = (right.0 as u128)
                        .saturating_mul(max_peer_latency as u128)
                        .max(
                            (right.1 as u128)
                                .saturating_mul(RESERVED_ORPHAN_WEIGHT_PER_PEER as u128),
                        );
                    left_score
                        .cmp(&right_score)
                        .then_with(|| left_id.cmp(right_id))
                })
            else {
                return;
            };

            let Some(wtxid) = self.insertion_order.iter().copied().find(|wtxid| {
                self.entries
                    .get(wtxid)
                    .is_some_and(|entry| entry.announcers.contains(&worst_peer))
            }) else {
                return;
            };
            self.remove_announcement(&wtxid, worst_peer);
        }
    }
}

pub type ChainEvent = chain::ChainTip;
pub type MempoolEvent = Txid;

#[derive(Clone, Debug)]
pub(crate) struct PeerMempoolEvent {
    pub txid: Txid,
    pub excluded_peers: Vec<usize>,
    pub force_relay: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct PrivateBroadcastPeer {
    pub(crate) address: SocketAddr,
    pub(crate) sent: u64,
    pub(crate) received: Option<u64>,
}

#[derive(Clone, Debug)]
pub(crate) struct PrivateBroadcastInfo {
    pub(crate) transaction: Transaction,
    pub(crate) peers: Vec<PrivateBroadcastPeer>,
}

struct PrivateBroadcastEntry {
    transaction: Transaction,
    peers: Vec<PrivateBroadcastPeer>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum NodeWarningKind {
    UnknownRulesActive,
    ClockOutOfSync,
    LargeWorkInvalidChain,
    FatalInternal,
}

#[derive(Clone, Debug)]
struct NodeWarning {
    kind: NodeWarningKind,
    message: String,
}

#[derive(Clone, Debug)]
pub struct OrphanTransaction {
    pub transaction: Transaction,
    pub peer_ids: Vec<usize>,
    pub entry_time: u64,
    pub expiration_time: u64,
}

#[derive(Clone, Debug)]
pub struct PeerInfo {
    pub id: usize,
    pub address: std::net::SocketAddr,
    pub endpoint: NetworkEndpoint,
    pub local_address: Option<std::net::SocketAddr>,
    pub reported_local_address: Option<std::net::SocketAddr>,
    pub inbound: bool,
    pub version: Option<i32>,
    pub services: u64,
    pub user_agent: String,
    pub start_height: i32,
    pub relay_transactions: bool,
    pub permissions: PeerPermissions,
    pub min_fee_filter: i64,
    pub transport_protocol_type: &'static str,
    pub(crate) session_id: String,
    pub connected_at: u64,
    pub last_send: u64,
    pub last_recv: u64,
    pub bytes_sent: u64,
    pub bytes_received: u64,
    // Bytes observed during transport detection are visible immediately in
    // getpeerinfo, then excluded when the eventual v1 frame is accounted.
    preaccounted_received_bytes: u64,
    unread_detection_bytes: u64,
    pub bytes_sent_per_msg: HashMap<String, u64>,
    pub bytes_received_per_msg: HashMap<String, u64>,
    pub last_inv_sequence: u64,
    pub inv_to_send: usize,
    pub last_transaction: u64,
    pub last_block: u64,
    pub last_block_announcement: u64,
    pub(crate) best_known_block: Option<BlockHash>,
    // Core keeps the latest block announcement that is not in the global
    // index yet.  Once another peer supplies the missing headers, the
    // announcement can be promoted to best_known_block.
    pub(crate) last_unknown_block: Option<BlockHash>,
    pub(crate) last_common_block: Option<BlockHash>,
    pub(crate) presynced_headers: i64,
    pub(crate) bip152_highbandwidth_to: bool,
    pub(crate) bip152_highbandwidth_from: bool,
    inflight_blocks: Vec<InflightBlock>,
    pub time_offset: i64,
    pub addr_processed: u64,
    pub addr_rate_limited: u64,
    pub addr_relay_enabled: bool,
    pub ping_time: Option<f64>,
    pub min_ping: Option<f64>,
    pub connection_type: &'static str,
    pub manual: bool,
    pub forced_inbound: bool,
    addr_token_bucket: f64,
    addr_token_timestamp: u128,
    ping_nonce: Option<u64>,
    ping_sent_at: Option<Instant>,
    ping_sent_mocktime: Option<u128>,
}

pub(crate) struct PeerRegistrationOptions {
    pub(crate) local_address: Option<SocketAddr>,
    pub(crate) permissions: PeerPermissions,
    pub(crate) connection_type: &'static str,
    pub(crate) manual: bool,
    pub(crate) forced_inbound: bool,
}

#[derive(Clone, Copy, Default)]
pub(crate) struct PeerTransportStats {
    pub(crate) last_send: u64,
    pub(crate) last_recv: u64,
    pub(crate) bytes_sent: u64,
    pub(crate) bytes_received: u64,
    pub(crate) preaccounted_received_bytes: u64,
    pub(crate) unread_detection_bytes: u64,
}

/// Address-manager metadata for an endpoint that may not be connected yet.
#[derive(Clone, Debug)]
pub struct KnownNetworkAddress {
    pub endpoint: NetworkEndpoint,
    pub services: u64,
    pub time: u64,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct AddrResponseCacheKey {
    pub(crate) network: &'static str,
    pub(crate) local_address: Option<SocketAddr>,
}

struct CachedAddrResponse {
    addresses: Vec<KnownNetworkAddress>,
    expiration: u64,
}

#[derive(Clone, Debug)]
struct InflightBlock {
    hash: BlockHash,
    height: u32,
    requested_at: Instant,
}

#[derive(Clone, Copy)]
struct BlockStallingMoment {
    wall: Instant,
    unix_time: u64,
}

#[derive(Clone, Copy, Default)]
struct ChainSyncTimeoutState {
    timeout: u64,
    work_hash: Option<BlockHash>,
    sent_getheaders: bool,
    protect: bool,
}

pub(crate) enum OutboundEvictionAction {
    None,
    RequestHeaders(BlockHash),
    Disconnect,
}

pub(crate) struct BlockDownloadSchedule {
    pub(crate) requests: Vec<wire::Inventory>,
    pub(crate) staller: Option<usize>,
}

impl PeerInfo {
    pub(crate) fn ping_wait(&self) -> Option<f64> {
        self.ping_sent_mocktime
            .map(|sent_at| time::unix_time_millis().saturating_sub(sent_at) as f64 / 1_000.0)
            .or_else(|| {
                self.ping_sent_at
                    .map(|sent_at| sent_at.elapsed().as_secs_f64())
            })
    }

    pub(crate) fn inflight_heights(&self) -> Vec<u32> {
        self.inflight_blocks
            .iter()
            .map(|block| block.height)
            .collect()
    }
}

fn is_non_reduced_outbound(peer: &PeerInfo, services: u64) -> bool {
    !peer.inbound
        && !peer.manual
        && matches!(
            peer.connection_type,
            "outbound-full" | "block-relay-only" | "addr-fetch"
        )
        && services & crate::wire::NODE_REDUCED_DATA == 0
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct IpSubnet {
    address: IpAddr,
    prefix: u8,
}

impl IpSubnet {
    pub(crate) fn parse(value: &str) -> Result<Self> {
        let mut parts = value.split('/');
        let address_value = parts
            .next()
            .ok_or_else(|| anyhow::anyhow!("invalid IP/Subnet"))?;
        let address_value = address_value
            .strip_prefix('[')
            .and_then(|value| value.strip_suffix(']'))
            .unwrap_or(address_value);
        let address = address_value
            .parse::<IpAddr>()
            .map_err(|_| anyhow::anyhow!("invalid IP/Subnet"))?;
        let prefix = match parts.next() {
            Some(prefix) => match prefix.parse::<u8>() {
                Ok(prefix) => prefix,
                Err(_) => {
                    let netmask = prefix
                        .parse::<IpAddr>()
                        .map_err(|_| anyhow::anyhow!("invalid IP/Subnet"))?;
                    prefix_from_netmask(address, netmask)?
                }
            },
            None => address_bits(address),
        };
        if parts.next().is_some() {
            bail!("invalid IP/Subnet")
        }
        Self::new(address, prefix)
    }

    pub(crate) fn from_address(address: IpAddr) -> Self {
        Self {
            address,
            prefix: address_bits(address),
        }
    }

    fn new(address: IpAddr, prefix: u8) -> Result<Self> {
        let bits = address_bits(address);
        if prefix > bits {
            bail!("invalid IP/Subnet")
        }
        Ok(Self {
            address: mask_address(address, prefix),
            prefix,
        })
    }

    pub(crate) fn address(self) -> IpAddr {
        self.address
    }

    pub(crate) fn prefix(self) -> u8 {
        self.prefix
    }

    pub(crate) fn contains(self, address: IpAddr) -> bool {
        Self::new(address, self.prefix).is_ok_and(|candidate| candidate.address == self.address)
    }

    pub(crate) fn display(self) -> String {
        format!("{}/{}", self.address, self.prefix)
    }
}

fn address_bits(address: IpAddr) -> u8 {
    match address {
        IpAddr::V4(_) => 32,
        IpAddr::V6(_) => 128,
    }
}

fn prefix_from_netmask(address: IpAddr, netmask: IpAddr) -> Result<u8> {
    let prefix = match (address, netmask) {
        (IpAddr::V4(_), IpAddr::V4(netmask)) => {
            netmask.octets().into_iter().fold(0u8, |prefix, octet| {
                prefix.saturating_add(octet.leading_ones() as u8)
            })
        }
        (IpAddr::V6(_), IpAddr::V6(netmask)) => {
            netmask.segments().into_iter().fold(0u8, |prefix, segment| {
                prefix.saturating_add(segment.leading_ones() as u8)
            })
        }
        _ => bail!("invalid IP/Subnet"),
    };
    let all_ones = match address {
        IpAddr::V4(_) => IpAddr::V4(Ipv4Addr::from(u32::MAX)),
        IpAddr::V6(_) => IpAddr::V6(Ipv6Addr::from(u128::MAX)),
    };
    let expected = mask_address(all_ones, prefix);
    if expected
        != match netmask {
            IpAddr::V4(netmask) => IpAddr::V4(netmask),
            IpAddr::V6(netmask) => IpAddr::V6(netmask),
        }
    {
        bail!("invalid IP/Subnet")
    }
    Ok(prefix)
}

fn mask_address(address: IpAddr, prefix: u8) -> IpAddr {
    match address {
        IpAddr::V4(address) => {
            let mask = if prefix == 0 {
                0
            } else {
                u32::MAX << (32 - u32::from(prefix))
            };
            IpAddr::V4(Ipv4Addr::from(u32::from(address) & mask))
        }
        IpAddr::V6(address) => {
            let mask = if prefix == 0 {
                0
            } else {
                u128::MAX << (128 - u32::from(prefix))
            };
            IpAddr::V6(Ipv6Addr::from(u128::from(address) & mask))
        }
    }
}

#[derive(Clone, Debug)]
pub struct BannedAddress {
    pub address: IpAddr,
    pub prefix: u8,
    pub ban_created: u64,
    pub ban_until: u64,
    pub reason: String,
}

impl BannedAddress {
    pub(crate) fn subnet(&self) -> IpSubnet {
        IpSubnet {
            address: self.address,
            prefix: self.prefix,
        }
    }
}

#[derive(Clone, Debug)]
pub struct BannedNetworkAddress {
    pub endpoint: NetworkEndpoint,
    pub ban_created: u64,
    pub ban_until: u64,
    pub reason: String,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct PersistedBannedAddress {
    #[serde(default = "default_ban_version")]
    version: u32,
    address: String,
    #[serde(default)]
    prefix: Option<u8>,
    #[serde(default)]
    network: Option<String>,
    ban_created: u64,
    ban_until: u64,
    reason: String,
}

fn default_ban_version() -> u32 {
    1
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct PersistedAddress {
    address: String,
    services: u64,
    time: u64,
    #[serde(default)]
    tried: bool,
    #[serde(default)]
    network: Option<String>,
    #[serde(default)]
    port: Option<u16>,
    #[serde(default)]
    source: Option<String>,
    #[serde(default)]
    source_network: Option<String>,
    #[serde(default)]
    source_port: Option<u16>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct PersistedAnchor {
    address: String,
    network: String,
    port: u16,
}

type LoadedAddressState = (
    HashMap<SocketAddr, PeerInfo>,
    HashSet<SocketAddr>,
    HashMap<NetworkEndpoint, KnownNetworkAddress>,
    HashSet<NetworkEndpoint>,
    HashMap<NetworkEndpoint, NetworkEndpoint>,
);

type LoadedBanState = (
    HashMap<IpSubnet, BannedAddress>,
    HashMap<NetworkEndpoint, BannedNetworkAddress>,
);

/// Per-node state shared by the long-running descriptor scans.
pub(crate) struct ScanState {
    pub(crate) in_progress: AtomicBool,
    pub(crate) abort: AtomicBool,
    pub(crate) progress: AtomicUsize,
    pub(crate) current_height: AtomicUsize,
}

impl Default for ScanState {
    fn default() -> Self {
        Self {
            in_progress: AtomicBool::new(false),
            abort: AtomicBool::new(false),
            progress: AtomicUsize::new(0),
            current_height: AtomicUsize::new(0),
        }
    }
}

const MEMPOOL_STATS_SAMPLE_MIN_DELTA_SECS: u64 = 2;
const MEMPOOL_STATS_CLEANUP_THRESHOLD: usize = 100;

/// A single non-interpolated mempool statistics sample, matching Core's
/// `CStatsMempoolSample` layout and JSON representation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MempoolStatsSample {
    pub(crate) time_delta: u32,
    pub(crate) tx_count: i64,
    pub(crate) dynamic_memory_usage: i64,
    pub(crate) min_fee_per_k: i64,
}

#[derive(Debug)]
struct MempoolStats {
    enabled: bool,
    max_memory_target: usize,
    start_time: u64,
    samples: Vec<MempoolStatsSample>,
    cleanup_counter: usize,
}

impl MempoolStats {
    fn new(enabled: bool, max_memory_target: usize) -> Self {
        Self {
            enabled: enabled && max_memory_target > 0,
            max_memory_target,
            start_time: 0,
            samples: Vec::new(),
            cleanup_counter: 0,
        }
    }

    fn add_sample(&mut self, tx_count: usize, dynamic_memory_usage: usize, min_fee_per_k: u64) {
        if !self.enabled {
            return;
        }
        let now = time::unix_time();
        if self.start_time == 0 {
            self.start_time = now;
        }
        if self.samples.last().is_some_and(|sample| {
            self.start_time
                .saturating_add(u64::from(sample.time_delta))
                .saturating_add(MEMPOOL_STATS_SAMPLE_MIN_DELTA_SECS)
                >= now
        }) {
            return;
        }
        self.samples.push(MempoolStatsSample {
            time_delta: now.saturating_sub(self.start_time).min(u64::from(u32::MAX)) as u32,
            tx_count: i64::try_from(tx_count).unwrap_or(i64::MAX),
            dynamic_memory_usage: i64::try_from(dynamic_memory_usage).unwrap_or(i64::MAX),
            min_fee_per_k: i64::try_from(min_fee_per_k).unwrap_or(i64::MAX),
        });
        self.cleanup_counter = self.cleanup_counter.saturating_add(1);
        if self.cleanup_counter >= MEMPOOL_STATS_CLEANUP_THRESHOLD {
            self.samples.shrink_to_fit();
            let sample_bytes = std::mem::size_of::<MempoolStatsSample>();
            let memory_usage = self.samples.capacity().saturating_mul(sample_bytes);
            if memory_usage > self.max_memory_target && self.samples.len() > 1 {
                let items_to_remove = (memory_usage
                    .saturating_sub(self.max_memory_target)
                    .saturating_add(sample_bytes.saturating_sub(1))
                    / sample_bytes)
                    .min(self.samples.len().saturating_sub(1));
                self.samples.drain(..items_to_remove);
            }
            self.samples.shrink_to_fit();
            self.cleanup_counter = 0;
        }
    }

    fn snapshot(&self) -> (u64, u64, Vec<MempoolStatsSample>) {
        let Some(first) = self.samples.first() else {
            return (0, 0, Vec::new());
        };
        let last = self.samples.last().unwrap_or(first);
        (
            self.start_time.saturating_add(u64::from(first.time_delta)),
            self.start_time.saturating_add(u64::from(last.time_delta)),
            self.samples.clone(),
        )
    }
}

/// The wallet-free node facade shared by the network and RPC services.
pub struct Node {
    pub config: Config,
    _data_dir_lock: File,
    _blocks_dir_lock: Option<File>,
    asmap: Option<Arc<AsMap>>,
    pub chain: Arc<RwLock<ChainState>>,
    pub(crate) block_store_reader: BlockStoreReader,
    pub mempool: Arc<RwLock<Mempool>>,
    mempool_stats: Mutex<MempoolStats>,
    pub events: broadcast::Sender<ChainEvent>,
    pub mempool_events: broadcast::Sender<MempoolEvent>,
    peer_mempool_events: broadcast::Sender<PeerMempoolEvent>,
    pub(crate) zmq_events: zmq::EventBus,
    pub(crate) txout_scan: Arc<ScanState>,
    pub(crate) blockfilter_scan: Arc<ScanState>,
    pub rpc_cookie: Option<String>,
    pub(crate) i2p_sam: Option<Arc<i2p::I2pSam>>,
    pub(crate) tor_controller: Option<Arc<tor::TorController>>,
    outbound_tor_ok_at_least_once: AtomicBool,
    mempool_path: std::path::PathBuf,
    block_relay_only_anchors_path: std::path::PathBuf,
    block_relay_only_anchors: parking_lot::RwLock<Vec<NetworkEndpoint>>,
    banlist_recreated: bool,
    /// Serialize RPC mining operations so a block template cannot become
    /// stale between reading the active tip and connecting the mined block.
    pub(crate) mining_lock: Mutex<()>,
    pub peer_count: AtomicUsize,
    /// Number of automatic outbound peers admitted under the optional
    /// NODE_REDUCED_DATA compatibility policy.
    non_reduced_outbound_count: AtomicUsize,
    mempool_check_operations: AtomicUsize,
    block_index_check_operations: AtomicUsize,
    addrman_check_operations: AtomicUsize,
    pub(crate) rpc_logging: parking_lot::RwLock<HashSet<String>>,
    zmq_mempool_sequence: AtomicU64,
    rpc_command_sequence: AtomicUsize,
    rpc_commands: parking_lot::RwLock<HashMap<usize, (String, Instant)>>,
    headers_sync_peers: AtomicUsize,
    headers_sync_started: parking_lot::Mutex<HashSet<usize>>,
    // Core's per-peer fSyncStarted state survives release of the single
    // global initial-sync slot. Keep it separate from the current slot claim
    // so a peer can continue reacting to announcements while another peer
    // temporarily owns the slot.
    headers_sync_active: parking_lot::Mutex<HashSet<usize>>,
    inv_triggered_headers_sync: parking_lot::Mutex<HashSet<usize>>,
    last_block_inv_triggering_headers_sync: parking_lot::Mutex<Option<BlockHash>>,
    total_bytes_sent: AtomicU64,
    total_bytes_received: AtomicU64,
    outbound_usage: parking_lot::Mutex<OutboundUsage>,
    network_active: AtomicBool,
    block_stalling_timeout_secs: AtomicU64,
    mock_scheduler_elapsed_secs: AtomicU64,
    block_stalling_since: parking_lot::RwLock<HashMap<usize, BlockStallingMoment>>,
    chain_sync_states: parking_lot::RwLock<HashMap<usize, ChainSyncTimeoutState>>,
    last_tip_update: AtomicU64,
    stale_tip_check_at: AtomicU64,
    try_new_outbound_peer: AtomicBool,
    extra_block_relay_peers_enabled: AtomicBool,
    next_extra_block_relay_at: AtomicU64,
    rejected_block_bodies: parking_lot::RwLock<HashSet<BlockHash>>,
    shutdown_requested: Arc<AtomicBool>,
    peers: parking_lot::RwLock<HashMap<usize, PeerInfo>>,
    peer_commands:
        parking_lot::RwLock<HashMap<usize, tokio::sync::mpsc::UnboundedSender<p2p::PeerCommand>>>,
    peer_manager_requests:
        parking_lot::RwLock<Option<tokio::sync::mpsc::UnboundedSender<p2p::PeerManagerRequest>>>,
    pub(crate) electrum_peers: parking_lot::Mutex<electrum::ElectrumPeerRegistry>,
    private_broadcasts: parking_lot::Mutex<HashMap<Wtxid, PrivateBroadcastEntry>>,
    compact_extra_transactions: parking_lot::Mutex<CompactExtraTransactions>,
    recently_rejected_transactions: parking_lot::Mutex<RecentlyRejectedTransactions>,
    orphans: parking_lot::Mutex<OrphanPool>,
    addrman_key: [u8; 32],
    known_addresses: parking_lot::RwLock<HashMap<SocketAddr, PeerInfo>>,
    tried_addresses: parking_lot::RwLock<HashSet<SocketAddr>>,
    network_addresses: parking_lot::RwLock<HashMap<NetworkEndpoint, KnownNetworkAddress>>,
    network_tried_addresses: parking_lot::RwLock<HashSet<NetworkEndpoint>>,
    network_address_sources: parking_lot::RwLock<HashMap<NetworkEndpoint, NetworkEndpoint>>,
    addr_response_caches: parking_lot::Mutex<HashMap<AddrResponseCacheKey, CachedAddrResponse>>,
    added_nodes: parking_lot::RwLock<HashMap<NetworkEndpoint, Option<bool>>>,
    added_node_names: parking_lot::RwLock<HashMap<NetworkEndpoint, String>>,
    banned_addresses: parking_lot::RwLock<HashMap<IpSubnet, BannedAddress>>,
    banned_network_addresses: parking_lot::RwLock<HashMap<NetworkEndpoint, BannedNetworkAddress>>,
    electrum_address: parking_lot::RwLock<Option<SocketAddr>>,
    listen_address: parking_lot::RwLock<Option<SocketAddr>>,
    listen_addresses: parking_lot::RwLock<Vec<SocketAddr>>,
    mapped_addresses: parking_lot::RwLock<Vec<SocketAddr>>,
    listen_network_addresses: parking_lot::RwLock<Vec<NetworkEndpoint>>,
    last_mining_block: parking_lot::RwLock<Option<(u64, usize)>>,
    time_offset_samples: parking_lot::RwLock<VecDeque<i64>>,
    warnings: parking_lot::RwLock<Vec<NodeWarning>>,
    versionbits_warning_scanned: AtomicBool,
    fee_estimator: Mutex<FeeEstimator>,
    coinstats_clean_shutdown_height_path: std::path::PathBuf,
    coinstats_unclean_startup_height: Option<u32>,
    pub started_at: Instant,
    pub(crate) network_nonce: u64,
    ipc_wait_cancellation: AtomicBool,
    peer_tasks_changed: Notify,
    shutdown: Notify,
}

impl Node {
    pub fn network_magic(&self) -> [u8; 4] {
        wire::network_magic_with_signet_challenge(
            self.config.network,
            self.config.signet_challenge.as_deref(),
        )
    }

    pub fn open(config: Config) -> Result<Arc<Self>> {
        fs::create_dir_all(&config.datadir)
            .with_context(|| format!("creating data directory {}", config.datadir.display()))?;
        let network_datadir = if network_data_dir_name(config.network).is_empty() {
            config.datadir.clone()
        } else {
            config.datadir.join(network_data_dir_name(config.network))
        };
        fs::create_dir_all(&network_datadir).with_context(|| {
            format!(
                "creating network data directory {}",
                network_datadir.display()
            )
        })?;
        // Core creates network-specific data directories and the wallet
        // placeholder with owner-only permissions.  Wallet functionality is
        // intentionally absent here, but keeping the directory preserves the
        // normal datadir shape without introducing Core's blk*.dat/rev*.dat
        // storage files.
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;

            fs::set_permissions(&network_datadir, fs::Permissions::from_mode(0o700)).with_context(
                || {
                    format!(
                        "setting permissions on network data directory {}",
                        network_datadir.display()
                    )
                },
            )?;
        }
        let wallets_dir = network_datadir.join("wallets");
        fs::create_dir_all(&wallets_dir)
            .with_context(|| format!("creating wallet directory {}", wallets_dir.display()))?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;

            fs::set_permissions(&wallets_dir, fs::Permissions::from_mode(0o700)).with_context(
                || {
                    format!(
                        "setting permissions on wallet directory {}",
                        wallets_dir.display()
                    )
                },
            )?;
        }
        let coinstats_unclean_startup = config.coinstatsindex && config.pid_path.exists();
        let lock_path = network_datadir.join(".lock");
        let data_dir_lock = OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .truncate(false)
            .open(&lock_path)
            .with_context(|| format!("opening data directory lock {}", lock_path.display()))?;
        data_dir_lock.try_lock_exclusive().map_err(|_| {
            anyhow!(
                "Cannot obtain a lock on directory {}. bitcoind-rs is probably already running.",
                network_datadir.display()
            )
        })?;
        let mut addrman_key = load_addrman_key(&config.datadir)?;
        let deterministic_addrman = std::env::args()
            .any(|argument| argument == "-test=addrman" || argument == "--test=addrman");
        if deterministic_addrman {
            addrman_key = [0; 32];
            addrman_key[0] = 1;
        }
        let configured_blocks_dir = config
            .blocks_dir
            .clone()
            .unwrap_or_else(|| config.datadir.join("blocks"));
        let blocks_dir = if config.blocks_dir_explicit {
            core_network_blocks_dir(&configured_blocks_dir, config.network)
                .unwrap_or_else(|| configured_blocks_dir.clone())
        } else {
            configured_blocks_dir.clone()
        };
        let blocks_dir_was_present = blocks_dir.is_dir();
        let snapshot_chainstate = network_datadir.join("chainstate_snapshot");
        let snapshot_base_hash_path = snapshot_chainstate.join("base_blockhash");
        if snapshot_base_hash_path.is_file() {
            let bytes = fs::read(&snapshot_base_hash_path).with_context(|| {
                format!(
                    "reading AssumeUTXO base block hash {}",
                    snapshot_base_hash_path.display()
                )
            })?;
            let base_hash = bytes
                .get(..32)
                .and_then(|bytes| <[u8; 32]>::try_from(bytes).ok())
                .map(BlockHash::from_byte_array)
                .context("invalid AssumeUTXO base block hash")?;
            let message =
                format!("Assumeutxo data not found for the given blockhash '{base_hash}'.");
            if let Some(parent) = config.debug_log_path.parent() {
                fs::create_dir_all(parent)?;
            }
            let mut debug_log = OpenOptions::new()
                .create(true)
                .append(true)
                .open(&config.debug_log_path)
                .with_context(|| {
                    format!("opening debug log {}", config.debug_log_path.display())
                })?;
            writeln!(debug_log, "{message}")?;
            return Err(anyhow!(
                "A fatal internal error occurred, see debug.log for details: {message}"
            ));
        }
        if config.blocks_dir_explicit && !configured_blocks_dir.is_dir() {
            bail!(
                "Specified blocks directory \"{}\" does not exist.",
                configured_blocks_dir.display()
            );
        }
        if !blocks_dir.is_dir() {
            fs::create_dir_all(&blocks_dir)
                .with_context(|| format!("creating blocks directory {}", blocks_dir.display()))?;
        }
        let blocks_dir_lock = if blocks_dir == config.datadir {
            None
        } else {
            let lock_path = blocks_dir.join(".lock");
            let lock = OpenOptions::new()
                .create(true)
                .read(true)
                .write(true)
                .truncate(false)
                .open(&lock_path)
                .with_context(|| {
                    format!("opening blocks directory lock {}", lock_path.display())
                })?;
            lock.try_lock_exclusive().map_err(|_| {
                anyhow!(
                    "Cannot obtain a lock on directory {}. bitcoind-rs is probably already running.",
                    blocks_dir.display()
                )
            })?;
            Some(lock)
        };
        if let Some(settings_path) = config.settings_path.as_deref() {
            initialize_settings_file(settings_path)?;
        }
        let asmap = config
            .asmap
            .as_deref()
            .map(|path| {
                if path == Path::new(EMBEDDED_ASMAP_PATH) {
                    AsMap::embedded()
                } else {
                    AsMap::from_file(path)
                }
            })
            .transpose()?
            .map(Arc::new);
        if let Some(mock_time) = config.mock_time {
            time::set_mock_time(mock_time);
        }
        let network_active = config.network_active;
        let shutdown_requested = Arc::new(AtomicBool::new(false));
        let i2p_sam = config.i2p_sam.map(|address| {
            Arc::new(i2p::I2pSam::new(
                address,
                config.datadir.clone(),
                Duration::from_millis(config.connect_timeout_ms),
                config.i2p_accept_incoming,
            ))
        });
        let tor_controller = config.listen_onion.then(|| {
            Arc::new(tor::TorController::new(
                config.tor_control,
                config.tor_password.clone(),
                config.datadir.clone(),
                Duration::from_millis(config.connect_timeout_ms),
            ))
        });
        let added_nodes = config
            .seed_nodes
            .iter()
            .chain(config.add_nodes.iter())
            .cloned()
            .map(|endpoint| (endpoint, None))
            .collect();
        let added_node_names = config
            .seed_nodes
            .iter()
            .chain(config.add_nodes.iter())
            .cloned()
            .map(|endpoint| {
                let name = endpoint.to_string();
                (endpoint, name)
            })
            .collect();
        let max_mempool_bytes = config
            .max_mempool_mb
            .checked_mul(1_000_000)
            .context("--maxmempool is too large")?;
        let max_mempool_bytes =
            usize::try_from(max_mempool_bytes).context("--maxmempool does not fit usize")?;
        let deployment_parameters = config
            .deployment_parameters
            .unwrap_or_else(|| validation::DeploymentParameters::for_network(config.network));
        let legacy_chain_data_dir = config.datadir.clone();
        let network_chain_data_dir = network_datadir.clone();
        let use_network_chain_data = !network_data_dir_name(config.network).is_empty()
            && (network_chain_data_dir.join("chainstate.bin").exists()
                || (legacy_chain_data_dir.join("chainstate.bin").exists()
                    && !blocks_dir_was_present));
        let chain_data_dir = if use_network_chain_data {
            network_chain_data_dir
        } else {
            legacy_chain_data_dir
        };
        let coinstats_clean_shutdown_height_path = chain_data_dir
            .join("indexes/coinstatsindex")
            .join(COINSTATS_CLEAN_SHUTDOWN_HEIGHT_FILE);
        let coinstats_unclean_startup_height = coinstats_unclean_startup
            .then(|| fs::read_to_string(&coinstats_clean_shutdown_height_path).ok())
            .flatten()
            .and_then(|height| height.trim().parse().ok());
        let mut chain =
            ChainState::open_with_options_and_tx_index_in_dirs_with_minimum_chain_work_and_assume_valid_and_blocks_xor_and_deployment_parameters_and_electrum_index(
                config.network,
                &chain_data_dir,
                blocks_dir,
                config.signet_challenge.as_deref(),
                config.blockfilterindex,
                config.reindex,
                config.reindex_chainstate,
                config.txindex,
                config.minimum_chain_work,
                config.assume_valid,
                config.blocks_xor,
                deployment_parameters,
                config.electrum_bind.is_some(),
            )
            .map_err(core_startup_chain_error)?;
        chain.set_shutdown_interrupt(shutdown_requested.clone());

        fs::create_dir_all(&network_datadir).with_context(|| {
            format!(
                "creating network data directory {}",
                network_datadir.display()
            )
        })?;

        let block_store_reader = chain.block_store_reader();
        chain.configure_max_tip_age(config.max_tip_age_secs);
        chain.configure_script_check_threads(config.script_check_threads);
        chain.configure_script_cache_size_mib(config.max_sig_cache_mib);
        chain.configure_storage_cache_size_mib(config.db_cache_mib);
        chain.configure_storage_batch_size_bytes(config.db_batch_size_bytes);
        #[cfg(not(test))]
        chain.configure_storage_crash_ratio(config.db_crash_ratio);
        #[cfg(not(test))]
        chain.maybe_simulate_storage_recovery_crash()?;
        chain.configure_prune_after_height(config.network, config.fast_prune);
        chain.configure_pruning(config.prune)?;
        if !config.reindex && !config.reindex_chainstate {
            chain
                .validate_persisted_indices_against_pruning(config.coinstatsindex)
                .map_err(|error| {
                    anyhow::anyhow!(
                        "{error}\nError: A fatal internal error occurred, see debug.log for details: Failed to start indexes, shutting down…"
                    )
                })?;
        }
        // Electrum 1.7 outpoint status needs confirmed spender lookups even
        // when the standalone Core-style txospenderindex RPC option is off.
        // Keep this internal index enabled for Electrum without changing the
        // user-facing getindexinfo reporting for that optional index.
        // Configure the Electrum sidecar first: a pruned restart can then
        // rebuild confirmed spenders from its compact transaction records
        // before the index is exposed to RPC clients.
        chain.configure_electrum_index(config.electrum_bind.is_some())?;
        chain
            .configure_txospender_index(config.txospenderindex || config.electrum_bind.is_some())?;
        chain.configure_coinstats_index(config.coinstatsindex)?;
        let signet_challenge = chain.signet_challenge().map(|challenge| challenge.to_vec());
        for path in &config.load_blocks {
            import_external_block_file(
                &mut chain,
                path,
                config.network,
                signet_challenge.as_deref(),
            )?;
        }
        chain.maybe_auto_prune()?;
        if config.check_blocks.is_some() || config.check_level.is_some() {
            let check_blocks = config.check_blocks.unwrap_or(6);
            let check_level = config.check_level.unwrap_or(3);
            chain
                .verify_active_chain_with_level(check_level, check_blocks)
                .context("startup block verification failed")?;
        }
        fs::create_dir_all(&network_datadir).with_context(|| {
            format!(
                "creating network data directory {}",
                network_datadir.display()
            )
        })?;
        let mempool_path = network_datadir.join("mempool.dat");
        let fee_estimator_path = network_datadir.join("fee_estimates.dat");
        let mempool_policy = MempoolPolicy {
            min_relay_fee_sat_per_kvb: config.min_relay_tx_fee_sat_per_kvb,
            incremental_relay_fee_sat_per_kvb: config.incremental_relay_fee_sat_per_kvb,
            dust_relay_fee_sat_per_kvb: config.dust_relay_fee_sat_per_kvb,
            bytes_per_sigop: config.bytes_per_sigop,
            #[cfg(not(test))]
            max_tx_legacy_sigops: config.max_tx_legacy_sigops,
            #[cfg(test)]
            max_tx_legacy_sigops: usize::try_from(crate::config::DEFAULT_MAX_TX_LEGACY_SIGOPS)
                .expect("constant fits usize"),
            max_datacarrier_bytes: config.max_datacarrier_bytes,
            #[cfg(not(test))]
            datacarrier_fullcount: config.datacarrier_fullcount,
            #[cfg(not(test))]
            accept_nonstd_datacarrier: config.accept_nonstd_datacarrier,
            #[cfg(test)]
            datacarrier_fullcount: true,
            #[cfg(test)]
            accept_nonstd_datacarrier: false,
            #[cfg(not(test))]
            permit_bare_datacarrier: config.permit_bare_datacarrier,
            #[cfg(test)]
            permit_bare_datacarrier: true,
            permit_bare_multisig: config.permit_bare_multisig,
            require_standard: !config.accept_nonstd_txn,
            ancestor_count_limit: config.ancestor_count_limit,
            ancestor_size_limit_vbytes: config.ancestor_size_vbytes,
            descendant_count_limit: config.descendant_count_limit,
            descendant_size_limit_vbytes: config.descendant_size_vbytes,
            cluster_count_limit: config.cluster_count,
            cluster_vsize_limit: config.cluster_size_vbytes,
            rbf_policy: config.rbf_policy,
            truc_policy: config.truc_policy,
        };
        let mut mempool =
            Mempool::with_max_bytes_and_policy(config.network, max_mempool_bytes, mempool_policy);
        if config.persist_mempool {
            let expiry = Duration::from_secs(config.mempool_expiry_hours.saturating_mul(60 * 60));
            let legacy_mempool_path = config.datadir.join("mempool.json");
            let load_path = mempool_path
                .exists()
                .then_some(mempool_path.as_path())
                .or_else(|| {
                    legacy_mempool_path
                        .exists()
                        .then_some(legacy_mempool_path.as_path())
                });
            if let Some(load_path) = load_path {
                if let Err(error) = mempool.load_from_file_with_expiry(load_path, &chain, expiry) {
                    // Core treats a failed startup mempool load as non-fatal.  Keep any
                    // entries that were admitted before a malformed record and continue
                    // bringing up the node; importmempool remains strict for RPC callers.
                    warn!(
                        %error,
                        path = %load_path.display(),
                        "failed to load persisted mempool; continuing without it"
                    );
                }
            }
        }
        let _ = mempool.take_changes();
        let mut fee_estimator = FeeEstimator::new(
            fee_estimator_path,
            chain.height(),
            config.accept_stale_fee_estimates,
        );
        for (txid, transaction, fee_sat, vsize, height) in mempool.fee_estimation_entries() {
            if !mempool.has_mempool_parent(&transaction) {
                fee_estimator.track_mempool_entry(txid, &transaction, fee_sat, vsize, height);
            }
        }
        if config.check_mempool != 0 {
            mempool
                .check_consistency()
                .context("startup mempool consistency check failed")?;
        }
        if config.check_block_index != 0 {
            chain
                .check_consistency()
                .context("startup block-index consistency check failed")?;
        }
        let banlist_path = network_datadir.join("banlist.json");
        let banlist_exists = banlist_path.exists();
        let (banned_addresses, banned_network_addresses) = match load_banlist(&network_datadir) {
            Ok(entries) => entries,
            Err(error) => {
                quarantine_persistent_file(&banlist_path, &error);
                (HashMap::new(), HashMap::new())
            }
        };
        if !banlist_exists {
            info!("Recreating the banlist database");
            fs::write(&banlist_path, b"[]")
                .with_context(|| format!("creating {}", banlist_path.display()))?;
        }
        let peers_path = config.datadir.join("peers.json");
        let (
            known_addresses,
            tried_addresses,
            network_addresses,
            network_tried_addresses,
            network_address_sources,
        ) = match load_known_addresses(&config.datadir) {
            Ok(state) => state,
            Err(error) => {
                quarantine_persistent_file(&peers_path, &error);
                (
                    HashMap::new(),
                    HashSet::new(),
                    HashMap::new(),
                    HashSet::new(),
                    HashMap::new(),
                )
            }
        };
        let block_relay_only_anchors_path = network_datadir.join(BLOCK_RELAY_ONLY_ANCHORS_FILE);
        let block_relay_only_anchors = if config.connect_disabled || !config.seed_nodes.is_empty() {
            // Core disables AddrMan-driven outgoing connections, including
            // anchor replay and clean-shutdown anchor snapshots, when
            // -connect/-noconnect is configured. Leave a native snapshot in
            // place so a later restart without that restriction can still
            // consume it.
            Vec::new()
        } else {
            match load_block_relay_only_anchors(&block_relay_only_anchors_path) {
                Ok(anchors) => {
                    if block_relay_only_anchors_path.exists() {
                        // Like Core, consume the startup snapshot. A clean
                        // shutdown will replace it with the peers that are
                        // actually connected at that point; an unclean restart
                        // must not keep retrying stale anchors indefinitely.
                        fs::remove_file(&block_relay_only_anchors_path).with_context(|| {
                            format!(
                                "removing consumed block-relay-only anchors {}",
                                block_relay_only_anchors_path.display()
                            )
                        })?;
                    }
                    anchors
                }
                Err(error) => {
                    quarantine_persistent_file(&block_relay_only_anchors_path, &error);
                    Vec::new()
                }
            }
        };
        let (events, _) = broadcast::channel(256);
        let (mempool_events, _) = broadcast::channel(256);
        let (peer_mempool_events, _) = broadcast::channel(256);
        let zmq_events = zmq::EventBus::new(&config.zmq);
        let zmq_mempool_sequence = mempool.sequence();
        let rpc_cookie = config
            .rpc_cookie_path
            .clone()
            .filter(|_| {
                !config
                    .rpc_auth
                    .iter()
                    .any(|auth| auth.uses_plaintext_password())
            })
            .map(|path| {
                let cookie = load_rpc_cookie(&path, config.rpc_cookie_permissions)?;
                if let Some(compat_path) = rpc_cookie_compat_path(&config, &path) {
                    write_rpc_cookie(&compat_path, &cookie, config.rpc_cookie_permissions)?;
                }
                Ok::<String, anyhow::Error>(cookie)
            })
            .transpose()
            .map_err(|_| {
                anyhow::anyhow!("Unable to start HTTP server. See debug log for details.")
            })?;
        let compact_extra_limit = config.block_reconstruction_extra_txn;
        let rpc_logging = if config.logging.debug_all {
            crate::config::CORE_LOG_CATEGORIES
                .iter()
                .map(|category| (*category).to_owned())
                .collect()
        } else {
            config.logging.debug_categories.iter().cloned().collect()
        };
        let mempool_stats = MempoolStats::new(config.stats_enable, config.stats_max_memory_target);
        let electrum_address = config.electrum_bind;
        let node = Arc::new(Self {
            config,
            _data_dir_lock: data_dir_lock,
            _blocks_dir_lock: blocks_dir_lock,
            asmap,
            chain: Arc::new(RwLock::new(chain)),
            block_store_reader,
            mempool: Arc::new(RwLock::new(mempool)),
            mempool_stats: Mutex::new(mempool_stats),
            events,
            mempool_events,
            peer_mempool_events,
            zmq_events,
            txout_scan: Arc::new(ScanState::default()),
            blockfilter_scan: Arc::new(ScanState::default()),
            rpc_cookie,
            i2p_sam,
            tor_controller,
            outbound_tor_ok_at_least_once: AtomicBool::new(false),
            mempool_path,
            block_relay_only_anchors_path,
            block_relay_only_anchors: parking_lot::RwLock::new(block_relay_only_anchors),
            banlist_recreated: !banlist_exists,
            mining_lock: Mutex::new(()),
            peer_count: AtomicUsize::new(0),
            non_reduced_outbound_count: AtomicUsize::new(0),
            mempool_check_operations: AtomicUsize::new(0),
            block_index_check_operations: AtomicUsize::new(0),
            addrman_check_operations: AtomicUsize::new(0),
            rpc_logging: parking_lot::RwLock::new(rpc_logging),
            zmq_mempool_sequence: AtomicU64::new(zmq_mempool_sequence),
            rpc_command_sequence: AtomicUsize::new(0),
            rpc_commands: parking_lot::RwLock::new(HashMap::new()),
            headers_sync_peers: AtomicUsize::new(0),
            headers_sync_started: parking_lot::Mutex::new(HashSet::new()),
            headers_sync_active: parking_lot::Mutex::new(HashSet::new()),
            inv_triggered_headers_sync: parking_lot::Mutex::new(HashSet::new()),
            last_block_inv_triggering_headers_sync: parking_lot::Mutex::new(None),
            total_bytes_sent: AtomicU64::new(0),
            total_bytes_received: AtomicU64::new(0),
            outbound_usage: parking_lot::Mutex::new(OutboundUsage::default()),
            network_active: AtomicBool::new(network_active),
            block_stalling_timeout_secs: AtomicU64::new(BLOCK_STALLING_TIMEOUT_DEFAULT.as_secs()),
            mock_scheduler_elapsed_secs: AtomicU64::new(0),
            block_stalling_since: parking_lot::RwLock::new(HashMap::new()),
            chain_sync_states: parking_lot::RwLock::new(HashMap::new()),
            last_tip_update: AtomicU64::new(0),
            stale_tip_check_at: AtomicU64::new(0),
            try_new_outbound_peer: AtomicBool::new(false),
            extra_block_relay_peers_enabled: AtomicBool::new(false),
            next_extra_block_relay_at: AtomicU64::new(0),
            rejected_block_bodies: parking_lot::RwLock::new(HashSet::new()),
            shutdown_requested,
            peers: parking_lot::RwLock::new(HashMap::new()),
            peer_commands: parking_lot::RwLock::new(HashMap::new()),
            peer_manager_requests: parking_lot::RwLock::new(None),
            electrum_peers: parking_lot::Mutex::new(electrum::ElectrumPeerRegistry::default()),
            private_broadcasts: parking_lot::Mutex::new(HashMap::new()),
            compact_extra_transactions: parking_lot::Mutex::new(CompactExtraTransactions::new(
                compact_extra_limit,
            )),
            recently_rejected_transactions: parking_lot::Mutex::new(
                RecentlyRejectedTransactions::new(),
            ),
            orphans: parking_lot::Mutex::new(OrphanPool::default()),
            addrman_key,
            known_addresses: parking_lot::RwLock::new(known_addresses),
            tried_addresses: parking_lot::RwLock::new(tried_addresses),
            network_addresses: parking_lot::RwLock::new(network_addresses),
            network_tried_addresses: parking_lot::RwLock::new(network_tried_addresses),
            network_address_sources: parking_lot::RwLock::new(network_address_sources),
            addr_response_caches: parking_lot::Mutex::new(HashMap::new()),
            added_nodes: parking_lot::RwLock::new(added_nodes),
            added_node_names: parking_lot::RwLock::new(added_node_names),
            banned_addresses: parking_lot::RwLock::new(banned_addresses),
            banned_network_addresses: parking_lot::RwLock::new(banned_network_addresses),
            electrum_address: parking_lot::RwLock::new(electrum_address),
            listen_address: parking_lot::RwLock::new(None),
            listen_addresses: parking_lot::RwLock::new(Vec::new()),
            mapped_addresses: parking_lot::RwLock::new(Vec::new()),
            listen_network_addresses: parking_lot::RwLock::new(Vec::new()),
            last_mining_block: parking_lot::RwLock::new(None),
            time_offset_samples: parking_lot::RwLock::new(VecDeque::new()),
            warnings: parking_lot::RwLock::new(Vec::new()),
            versionbits_warning_scanned: AtomicBool::new(false),
            fee_estimator: Mutex::new(fee_estimator),
            coinstats_clean_shutdown_height_path,
            coinstats_unclean_startup_height,
            started_at: Instant::now(),
            network_nonce: random(),
            ipc_wait_cancellation: AtomicBool::new(false),
            peer_tasks_changed: Notify::new(),
            shutdown: Notify::new(),
        });
        if node.config.check_addrman != 0 {
            node.check_addrman_consistency()
                .context("startup address-manager consistency check failed")?;
        }
        node.refresh_versionbits_warning();
        node.log_asmap_health();
        if node.config.stop_after_block_import {
            node.request_shutdown();
        }
        Ok(node)
    }

    pub fn connect_block(&self, block: Block) -> Result<ChainEvent> {
        self.connect_block_with_policy(block, false)
    }

    pub(crate) fn note_ipc_wait_cancellation(&self) {
        self.ipc_wait_cancellation.store(true, Ordering::Release);
    }

    fn log_ipc_wait_cancellation(&self) {
        if self.ipc_wait_cancellation.swap(false, Ordering::AcqRel) {
            debug!(target: "bitcoind_rs::ipc", "interrupted (canceled)");
        }
    }

    pub(crate) fn connect_block_from_peer(&self, block: Block) -> Result<ChainEvent> {
        self.connect_block_with_policy(block, true)
    }

    fn connect_block_with_policy(
        &self,
        block: Block,
        retain_invalid_body: bool,
    ) -> Result<ChainEvent> {
        let previous_tip = self.chain.read().best_hash();
        let (tip, activated_blocks, disconnected_blocks) = {
            let mut chain = self.chain.write();
            let tip = if retain_invalid_body {
                chain.connect_block_from_peer(block)?
            } else {
                chain.connect_block(block)?
            };
            chain.maybe_auto_prune()?;
            let activated_blocks = if tip.hash != previous_tip {
                chain.active_blocks_after(previous_tip)?
            } else {
                Vec::new()
            };
            let disconnected_blocks = if tip.hash != previous_tip {
                chain.disconnected_blocks_after(previous_tip)?
            } else {
                Vec::new()
            };
            (tip, activated_blocks, disconnected_blocks)
        };
        if tip.hash != previous_tip {
            // Core's peer manager records every active-tip change for stale
            // tip detection. Keep the timestamp in node state rather than in
            // the native chain files; it is deliberately runtime-only.
            self.last_tip_update
                .store(time::unix_time(), Ordering::Release);
        }
        for _ in &activated_blocks {
            self.reduce_block_stalling_timeout();
        }
        if !activated_blocks.is_empty() || !disconnected_blocks.is_empty() {
            // Core publishes disconnect notifications before it updates the
            // mempool, while connect notifications follow the mempool
            // removals caused by the newly active blocks.
            self.announce_zmq_block_events(&disconnected_blocks, &[]);
            self.reconcile_mempool_after_chain_change(
                &activated_blocks,
                &disconnected_blocks,
                false,
            );
            self.announce_zmq_block_events(&[], &activated_blocks);
            let _ = self.events.send(tip.clone());

            self.log_ipc_wait_cancellation();

            self.promote_orphans_after_chain_change(&activated_blocks, &disconnected_blocks);
        }
        if self.config.stop_at_height != 0 && tip.height >= self.config.stop_at_height {
            self.request_shutdown();
        }
        if tip.hash != previous_tip {
            let hash = tip.hash.to_string();
            run_notify_command(self.config.block_notify.as_deref(), Some(&hash));
        }
        self.refresh_versionbits_warning();
        self.maybe_check_block_index();
        Ok(tip)
    }

    pub(crate) fn maybe_check_mempool(&self) {
        let interval = self.config.check_mempool;
        if interval == 0 {
            return;
        }
        let operation = self
            .mempool_check_operations
            .fetch_add(1, Ordering::Relaxed)
            .saturating_add(1);
        if operation % interval != 0 {
            return;
        }
        if let Err(error) = self.mempool.read().check_consistency() {
            panic!("mempool consistency check failed: {error:#}");
        }
    }

    /// Record the current mempool state when statistics collection is
    /// enabled. The mempool lock is released before taking the statistics
    /// lock so RPC snapshots cannot create a lock-order cycle.
    pub(crate) fn record_mempool_stats(&self) {
        if !self.config.stats_enable || self.config.stats_max_memory_target == 0 {
            return;
        }
        let (tx_count, dynamic_memory_usage, min_fee_per_k) = {
            let mut mempool = self.mempool.write();
            (
                mempool.len(),
                mempool.dynamic_memory_usage(),
                mempool.mempool_min_fee_sat_per_kvb(),
            )
        };
        self.mempool_stats
            .lock()
            .add_sample(tx_count, dynamic_memory_usage, min_fee_per_k);
    }

    pub(crate) fn mempool_stats_snapshot(&self) -> (u64, u64, Vec<MempoolStatsSample>) {
        self.mempool_stats.lock().snapshot()
    }

    pub(crate) fn update_fee_estimator_for_changes(
        &self,
        changes: &[MempoolChange],
        current_height: u32,
    ) {
        self.update_fee_estimator_for_changes_except(changes, current_height, &HashSet::new());
    }

    pub(crate) fn update_fee_estimator_for_changes_except(
        &self,
        changes: &[MempoolChange],
        current_height: u32,
        excluded: &HashSet<Txid>,
    ) {
        if changes.is_empty() {
            return;
        }
        let mempool = self.mempool.read();
        let mut estimator = self.fee_estimator.lock();
        for change in changes {
            let txid = change.transaction.compute_txid();
            match &change.kind {
                MempoolChangeKind::Added => {
                    if excluded.contains(&txid) {
                        continue;
                    }
                    if let Some(entry) = mempool.get(&txid)
                        && !mempool.has_mempool_parent(&entry.transaction)
                    {
                        estimator.track_mempool_entry(
                            txid,
                            &entry.transaction,
                            entry.fee_sat,
                            entry.vsize,
                            entry.height,
                        );
                    }
                }
                MempoolChangeKind::Removed { notify_zmq: true } => {
                    estimator.remove_from_mempool(&txid)
                }
                MempoolChangeKind::Removed { notify_zmq: false } => {
                    // Confirmed removals are processed with their exact block
                    // height by process_fee_estimator_block.
                    let _ = current_height;
                }
            }
        }
    }

    fn process_fee_estimator_block(&self, height: u32, confirmed: &[Txid]) {
        self.fee_estimator.lock().process_block(height, confirmed);
    }

    pub(crate) fn estimate_smart_fee(
        &self,
        conf_target: u32,
        conservative: bool,
    ) -> (Option<u64>, u32) {
        self.fee_estimator
            .lock()
            .estimate_smart_fee(conf_target, conservative)
    }

    pub(crate) fn raw_fee_estimates(
        &self,
        conf_target: u32,
        threshold: f64,
    ) -> Vec<(&'static str, RawFeeEstimate)> {
        self.fee_estimator
            .lock()
            .raw_fee_estimates(conf_target, threshold)
    }

    fn flush_fee_estimates(&self, include_unconfirmed: bool) -> Result<()> {
        let mut estimator = self.fee_estimator.lock();
        if include_unconfirmed {
            estimator.flush_unconfirmed();
        }
        estimator.flush()
    }

    pub(crate) fn save_fee_estimates(&self) -> Result<()> {
        self.flush_fee_estimates(false)
    }

    fn maybe_check_block_index(&self) {
        let interval = self.config.check_block_index;
        if interval == 0 {
            return;
        }
        let operation = self
            .block_index_check_operations
            .fetch_add(1, Ordering::Relaxed)
            .saturating_add(1);
        if operation % interval != 0 {
            return;
        }
        if let Err(error) = self.chain.read().check_consistency() {
            panic!("block-index consistency check failed: {error:#}");
        }
    }

    fn maybe_check_addrman(&self) {
        let interval = self.config.check_addrman;
        if interval == 0 {
            return;
        }
        let operation = self
            .addrman_check_operations
            .fetch_add(1, Ordering::Relaxed)
            .saturating_add(1);
        if operation % interval != 0 {
            return;
        }
        if let Err(error) = self.check_addrman_consistency() {
            panic!("address-manager consistency check failed: {error:#}");
        }
    }

    /// Verify the relationships between the persisted known/tried endpoint
    /// tables and connected peer records. This is the local equivalent of
    /// Core's AddrMan consistency check for the simplified indexed store.
    pub(crate) fn check_addrman_consistency(&self) -> Result<()> {
        let known_addresses = self
            .known_addresses
            .read()
            .iter()
            .map(|(address, peer)| (*address, peer.id, peer.endpoint.clone()))
            .collect::<Vec<_>>();
        let tried_addresses = self.tried_addresses.read().clone();
        let network_addresses = self
            .network_addresses
            .read()
            .iter()
            .map(|(endpoint, entry)| (endpoint.clone(), entry.endpoint.clone()))
            .collect::<Vec<_>>();
        let network_tried_addresses = self.network_tried_addresses.read().clone();
        let peer_ids = self
            .peers
            .read()
            .iter()
            .map(|(id, peer)| (*id, peer.endpoint.clone()))
            .collect::<HashMap<_, _>>();
        let new_count = known_addresses
            .iter()
            .filter(|(address, _, _)| !tried_addresses.contains(address))
            .count()
            + network_addresses
                .iter()
                .filter(|(endpoint, _)| !network_tried_addresses.contains(endpoint))
                .count();
        let tried_count = tried_addresses.len() + network_tried_addresses.len();
        let total_count = new_count.saturating_add(tried_count);
        info!("CheckAddrman: new {new_count}, tried {tried_count}, total {total_count} started");

        if known_addresses.len() > MAX_KNOWN_ADDRESSES
            || network_addresses.len() > MAX_KNOWN_ADDRESSES
        {
            bail!("address-manager table exceeds its configured capacity");
        }
        for (address, peer_id, endpoint) in &known_addresses {
            if *endpoint != NetworkEndpoint::Ip(*address) {
                bail!("known IPv4/IPv6 address has a mismatched endpoint key: {address}");
            }
            if *peer_id != UNCONNECTED_PEER_ID && peer_ids.get(peer_id) != Some(endpoint) {
                bail!("known address {address} points to a missing or different peer");
            }
        }
        for address in &tried_addresses {
            if !known_addresses.iter().any(|(known, _, _)| known == address) {
                bail!("tried address {address} is absent from the known-address table");
            }
        }
        for (endpoint, stored_endpoint) in &network_addresses {
            if endpoint != stored_endpoint || matches!(endpoint, NetworkEndpoint::Dns { .. }) {
                bail!("network address has an invalid endpoint key: {endpoint}");
            }
            if endpoint.legacy_socket_addr().is_some() {
                bail!("legacy socket endpoint was stored in the network address table: {endpoint}");
            }
        }
        for endpoint in &network_tried_addresses {
            let present = endpoint
                .legacy_socket_addr()
                .is_some_and(|address| tried_addresses.contains(&address))
                || network_addresses.iter().any(|(known, _)| known == endpoint);
            if !present {
                bail!("tried network address {endpoint} is absent from the known tables");
            }
        }
        info!("CheckAddrman: completed");
        Ok(())
    }

    pub(crate) fn mapped_as(&self, endpoint: &NetworkEndpoint) -> Option<u32> {
        self.asmap.as_ref()?.mapped_as(endpoint)
    }

    pub(crate) fn peer_netgroup_key(&self, endpoint: &NetworkEndpoint) -> Vec<u8> {
        if let Some(asn) = self.mapped_as(endpoint) {
            // Core uses NET_IPV6 as the common class prefix for AS-mapped
            // IPv4 and IPv6 addresses so the same ASN shares a group across
            // address families.
            let mut key = Vec::with_capacity(1 + std::mem::size_of::<u32>());
            key.push(2);
            key.extend_from_slice(&asn.to_le_bytes());
            key
        } else {
            endpoint.netgroup_key()
        }
    }

    pub(crate) fn addrman_hash_key(&self) -> &[u8; 32] {
        &self.addrman_key
    }

    fn log_asmap_health(&self) {
        let Some(asmap) = &self.asmap else {
            return;
        };
        let mut clearnet_peers = 0usize;
        let mut mapped_asns = HashSet::new();
        let mut unmapped_peers = 0usize;
        for entry in self.known_network_addresses() {
            if !matches!(entry.endpoint, NetworkEndpoint::Ip(_)) {
                continue;
            }
            clearnet_peers = clearnet_peers.saturating_add(1);
            if let Some(asn) = asmap.mapped_as(&entry.endpoint) {
                mapped_asns.insert(asn);
            } else {
                unmapped_peers = unmapped_peers.saturating_add(1);
            }
        }
        info!(
            "ASMap Health Check: {clearnet_peers} clearnet peers are mapped to {} ASNs with {unmapped_peers} peers being unmapped",
            mapped_asns.len()
        );
    }

    pub fn log_asmap_configuration(&self) {
        if let Some(asmap) = &self.asmap {
            if let Some(path) = self.config.asmap.as_deref() {
                if path == Path::new(EMBEDDED_ASMAP_PATH) {
                    info!(
                        "Opened asmap data ({} bytes) from embedded byte array",
                        AsMap::embedded_len()
                    );
                } else {
                    let size = fs::metadata(path).map_or(0, |metadata| metadata.len());
                    info!(
                        "Opened asmap file \"{}\" ({} bytes) from disk",
                        path.display(),
                        size
                    );
                }
            }
            info!(
                "Using asmap version {} for IP bucketing",
                asmap.version_hex()
            );
        } else {
            info!("Using /16 prefix for IP bucketing");
        }
        self.log_asmap_health();
    }

    fn reconcile_mempool_after_chain_change(
        &self,
        activated_blocks: &[Block],
        disconnected_blocks: &[Block],
        manual_invalidation: bool,
    ) {
        // Core resets both recent-reject filters whenever the active tip
        // changes so transactions rejected under the previous chain state
        // can be requested and reconsidered again.
        self.recently_rejected_transactions.lock().clear();
        let mempool_before = self
            .mempool
            .read()
            .transaction_order()
            .into_iter()
            .collect::<HashSet<_>>();
        let chain = self.chain.read();
        let mut mempool = self.mempool.write();
        let mut fee_block_changes = Vec::with_capacity(activated_blocks.len());
        let mut mempool_changes = Vec::new();
        let mut disconnected_pool =
            (!manual_invalidation).then(DisconnectedTransactionPool::default);
        if let Some(pool) = disconnected_pool.as_mut() {
            // Core receives disconnected blocks from newest to oldest and
            // queues each block's transactions in reverse order. Evicted
            // entries are removed immediately, including their descendants.
            for block in disconnected_blocks.iter().rev() {
                for evicted in pool.add_block(block) {
                    mempool.remove_recursive(&evicted.compute_txid());
                }
            }
        }
        for block in activated_blocks {
            mempool.remove_conflicts(block);
            mempool.remove_confirmed(block);
            if let Some(pool) = disconnected_pool.as_mut() {
                pool.remove_for_block(block);
            }
            let block_changes = mempool.take_changes();
            let confirmed = block_changes
                .iter()
                .filter_map(|change| {
                    matches!(
                        &change.kind,
                        MempoolChangeKind::Removed { notify_zmq: false }
                    )
                    .then_some(change.transaction.compute_txid())
                })
                .collect::<Vec<_>>();
            if let Some(height) = chain.block_height_by_hash(&block.block_hash()) {
                fee_block_changes.push((height, confirmed));
            }
            mempool_changes.extend(block_changes);
        }
        let added_at = time::unix_time();
        let mut fee_estimator_exclusions = HashSet::new();
        // Core's invalidateblock disconnects one block at a time. It
        // attempts to resurrect transactions from the ten most recently
        // disconnected blocks, newest first; deeper invalidations skip
        // resurrection entirely. Ordinary reorgs drain one aggregate
        // disconnect pool oldest first so parents are available before their
        // descendants.
        if let Some(pool) = disconnected_pool {
            for transaction in pool.take_oldest_first() {
                if transaction.is_coinbase() {
                    continue;
                }
                match mempool.accept_reorg(transaction.clone(), &chain, added_at) {
                    Ok(txid) => {
                        fee_estimator_exclusions.insert(txid);
                    }
                    Err(error) => {
                        debug!(
                            txid = %transaction.compute_txid(),
                            %error,
                            "reorg transaction rejected while restoring mempool"
                        );
                    }
                }
            }
        } else {
            // InvalidateBlock disconnects one tip at a time in Core, but the
            // final chain state is passed to this reconciliation hook only
            // after the whole invalidated suffix has been disconnected. Queue
            // the most recent ten blocks in newest-to-oldest order, then
            // replay the aggregate pool oldest-first so parents are available
            // before descendants.
            let mut pool = DisconnectedTransactionPool::default();
            for block in disconnected_blocks.iter().rev().take(10) {
                for evicted in pool.add_block(block) {
                    mempool.remove_recursive(&evicted.compute_txid());
                }
            }
            // A deep invalidation does not resurrect transactions from blocks
            // beyond Core's ten-block window, but it still removes their
            // descendants from the mempool. The aggregate hook receives the
            // whole suffix, so perform that cleanup explicitly here.
            for block in disconnected_blocks.iter().rev().skip(10) {
                for transaction in &block.txdata {
                    mempool.remove_recursive(&transaction.compute_txid());
                }
            }
            for activated in activated_blocks {
                pool.remove_for_block(activated);
            }
            for transaction in pool.take_oldest_first() {
                if transaction.is_coinbase() {
                    continue;
                }
                match mempool.accept_reorg(transaction.clone(), &chain, added_at) {
                    Ok(txid) => {
                        fee_estimator_exclusions.insert(txid);
                    }
                    Err(error) => {
                        debug!(
                            txid = %transaction.compute_txid(),
                            %error,
                            "reorg transaction rejected while restoring mempool"
                        );
                    }
                }
            }
        }
        // Disconnected-block transactions are replayed oldest-first, but
        // their descendants may already have been in the mempool.  Rebuild
        // the reverse graph once after the bulk restoration so those edges
        // are visible to reorg cleanup, descendant accounting, and TRUC/RBF
        // policy checks.
        mempool.rebuild_children_index();
        mempool.remove_for_reorg(&chain);
        mempool.enforce_size_limit();
        let mempool_after = mempool
            .transaction_order()
            .into_iter()
            .collect::<HashSet<_>>();
        mempool_changes.extend(mempool.take_changes());
        let current_height = chain.height();
        drop(mempool);
        drop(chain);
        for (height, confirmed) in fee_block_changes {
            self.process_fee_estimator_block(height, &confirmed);
        }
        self.update_fee_estimator_for_changes_except(
            &mempool_changes,
            current_height,
            &fee_estimator_exclusions,
        );
        self.announce_mempool_diff(mempool_before, mempool_after);
        self.notify_zmq_mempool_changes(mempool_changes);
        self.record_mempool_stats();
    }

    fn promote_orphans_after_chain_change(
        &self,
        activated_blocks: &[Block],
        disconnected_blocks: &[Block],
    ) {
        for block in activated_blocks {
            let erased = self.orphans.lock().erase_for_block(block);
            if erased > 0 {
                info!("Erased {erased} orphan transaction(s) included or conflicted by block");
            }
        }
        for block in activated_blocks {
            for transaction in &block.txdata {
                self.promote_orphans_for_parent(transaction);
            }
        }
        for block in disconnected_blocks {
            for transaction in block.txdata.iter().skip(1) {
                if self
                    .mempool
                    .read()
                    .get(&transaction.compute_txid())
                    .is_some()
                {
                    self.promote_orphans_for_parent(transaction);
                }
            }
        }
    }

    fn chain_change_needs_block_bodies(&self) -> bool {
        !self.mempool.read().is_empty()
            || self.orphan_count() != 0
            || (self.config.zmq.is_enabled() && self.zmq_events.receiver_count() != 0)
    }

    fn reduce_block_stalling_timeout(&self) {
        let current = self.block_stalling_timeout_secs.load(Ordering::Relaxed);
        if current <= BLOCK_STALLING_TIMEOUT_DEFAULT.as_secs() {
            return;
        }
        let reduced =
            (current.saturating_mul(85) / 100).max(BLOCK_STALLING_TIMEOUT_DEFAULT.as_secs());
        if self
            .block_stalling_timeout_secs
            .compare_exchange(current, reduced, Ordering::Relaxed, Ordering::Relaxed)
            .is_ok()
        {
            info!("Decreased stalling timeout to {reduced} seconds");
        }
    }

    pub fn accept_transaction(&self, transaction: Transaction) -> Result<Txid> {
        self.accept_transaction_with_policy(transaction, false)
    }

    pub fn accept_transaction_with_ignored_rejects(
        &self,
        transaction: Transaction,
        ignore_rejects: &HashSet<String>,
    ) -> Result<Txid> {
        let disable_standard_policy = ignore_rejects.iter().any(|reason| {
            matches!(
                reason.as_str(),
                "scriptsig-not-pushonly" | "scriptpubkey" | "bad-txns-input-script-unknown"
            )
        });
        self.accept_transaction_with_policy(transaction, disable_standard_policy)
    }

    fn accept_transaction_with_policy(
        &self,
        transaction: Transaction,
        disable_standard_policy: bool,
    ) -> Result<Txid> {
        self.expire_mempool();
        let txid = transaction.compute_txid();
        if let Some(existing) = self
            .mempool
            .read()
            .get(&txid)
            .map(|entry| entry.transaction.clone())
        {
            // Core treats an already-mempool transaction as a successful
            // rebroadcast. Use the mempool's witness-bearing transaction so
            // a same-txid/different-witness submission cannot relay data that
            // was not admitted.
            self.notify_mempool_transaction(existing);
            return Ok(txid);
        }
        let (txid, _) = self
            .try_accept_transaction_with_policy(transaction.clone(), disable_standard_policy)
            .map_err(|error| {
                let detailed = matches!(
                    &error,
                    MempoolError::NonStandard(reason)
                        if reason == "missing-ephemeral-spends"
                ) || error.to_string() == "transaction is non-standard: missing-ephemeral-spends";
                if detailed {
                    anyhow!(
                        "missing-ephemeral-spends, tx {} (wtxid={}) did not spend parent's ephemeral dust",
                        transaction.compute_txid(),
                        transaction.compute_wtxid()
                    )
                } else {
                    anyhow::Error::new(error)
                }
            })?;
        self.mempool.write().add_unbroadcast(txid);
        self.notify_mempool_transaction(transaction);
        Ok(txid)
    }

    fn validate_private_broadcast_transaction(&self, transaction: Transaction) -> Result<()> {
        let chain = self.chain.read();
        let mut mempool = self.mempool.read().clone();
        mempool
            .accept(transaction, &chain)
            .map(|_| ())
            .map_err(Into::into)
    }

    pub(crate) fn queue_private_broadcast(&self, transaction: Transaction) -> Result<Txid> {
        if !self.config.private_broadcast {
            bail!("private broadcast is disabled")
        }
        let tor_reachable = self.config.onion_enabled
            && (self.config.onion_proxy.is_some()
                || self.config.proxy_for_network("onion").is_some()
                || self
                    .tor_controller
                    .as_ref()
                    .is_some_and(|controller| controller.is_reachable()));
        let i2p_reachable = self.i2p_sam.is_some();
        if !tor_reachable && !i2p_reachable {
            bail!(
                "-privatebroadcast is enabled, but none of the Tor or I2P networks is reachable. Maybe the location of the Tor proxy couldn't be retrieved from the Tor daemon at startup. Check whether the Tor daemon is running and that -torcontrol, -torpassword and -i2psam are configured properly."
            );
        }
        if self.config.proxy_for_network("ipv4").is_none() {
            bail!("--privatebroadcast requires --proxy for IPv4/IPv6 private connections")
        }
        let txid = transaction.compute_txid();
        let wtxid = transaction.compute_wtxid();
        // Core treats a transaction already in the mempool as a successful
        // reannouncement request, without re-running admission for the
        // submitted witness.  This is also how private broadcast switches
        // back to a new private-broadcast attempt after the transaction was
        // received from the network and entered our mempool.
        let already_in_mempool = self.mempool.read().get(&txid).is_some();
        if !already_in_mempool {
            self.validate_private_broadcast_transaction(transaction.clone())?;
        }
        if self.private_broadcasts.lock().contains_key(&wtxid) {
            tracing::debug!(target: "bitcoind_rs::p2p",
                "Ignoring unnecessary request to schedule an already scheduled transaction: txid={txid}, wtxid={wtxid}"
            );
            return Ok(txid);
        }
        self.private_broadcasts.lock().insert(
            wtxid,
            PrivateBroadcastEntry {
                transaction,
                peers: Vec::new(),
            },
        );
        self.schedule_private_broadcasts();
        Ok(txid)
    }

    pub(crate) fn private_broadcast_infos(&self) -> Vec<PrivateBroadcastInfo> {
        let mut infos = self
            .private_broadcasts
            .lock()
            .values()
            .map(|entry| PrivateBroadcastInfo {
                transaction: entry.transaction.clone(),
                peers: entry.peers.clone(),
            })
            .collect::<Vec<_>>();
        infos.sort_by_key(|info| info.transaction.compute_txid().to_string());
        infos
    }

    pub(crate) fn abort_private_broadcast(&self, id: Txid) -> Vec<PrivateBroadcastInfo> {
        let removed = {
            let mut broadcasts = self.private_broadcasts.lock();
            let id_as_wtxid = Wtxid::from_byte_array(id.to_byte_array());
            let keys = broadcasts
                .iter()
                .filter_map(|(entry_wtxid, entry)| {
                    (entry.transaction.compute_txid() == id
                        || entry.transaction.compute_wtxid() == id_as_wtxid)
                        .then_some(*entry_wtxid)
                })
                .collect::<Vec<_>>();
            keys.into_iter()
                .filter_map(|wtxid| broadcasts.remove(&wtxid))
                .map(|entry| PrivateBroadcastInfo {
                    transaction: entry.transaction,
                    peers: entry.peers,
                })
                .collect::<Vec<_>>()
        };
        let addresses = removed
            .iter()
            .flat_map(|info| info.peers.iter().map(|peer| peer.address))
            .collect::<HashSet<_>>();
        for peer in self.peer_infos().into_iter().filter(|peer| {
            peer.connection_type == "private-broadcast" && addresses.contains(&peer.address)
        }) {
            self.disconnect_peer(peer.id);
        }
        removed
    }

    pub(crate) fn private_broadcast_transaction_is_pending(
        &self,
        transaction: &Transaction,
    ) -> bool {
        self.private_broadcasts
            .lock()
            .contains_key(&transaction.compute_wtxid())
    }

    pub(crate) fn mark_private_broadcast_peer_ack(
        &self,
        transaction: &Transaction,
        address: SocketAddr,
    ) {
        let wtxid = transaction.compute_wtxid();
        if let Some(entry) = self.private_broadcasts.lock().get_mut(&wtxid)
            && let Some(peer) = entry.peers.iter_mut().find(|peer| peer.address == address)
        {
            peer.received = Some(time::unix_time());
        }
    }

    pub(crate) fn mark_private_broadcast_received(&self, transaction: &Transaction) -> bool {
        self.private_broadcasts
            .lock()
            .remove(&transaction.compute_wtxid())
            .is_some()
    }

    fn private_broadcast_targets(
        &self,
        entry: &PrivateBroadcastEntry,
        now: u64,
    ) -> Vec<SocketAddr> {
        let mut candidates = self
            .config
            .seed_nodes
            .iter()
            .filter_map(NetworkEndpoint::socket_addr)
            .collect::<Vec<_>>();
        candidates.extend(self.known_addresses.read().keys().copied());
        candidates.sort_unstable();
        candidates.dedup();
        let connected = self
            .peer_infos()
            .into_iter()
            .filter_map(|peer| peer.endpoint.socket_addr())
            .collect::<HashSet<_>>();
        candidates.retain(|address| {
            address.port() != 0
                && !address.ip().is_unspecified()
                && (address.is_ipv4() || address.is_ipv6())
                && !connected.contains(address)
        });
        candidates.retain(|address| {
            self.config.allows_address(*address)
                && !self.is_banned_for_peer(*address, false)
                && !entry.peers.iter().any(|peer| {
                    peer.address == *address
                        && now.saturating_sub(peer.sent) < PRIVATE_BROADCAST_RETRY_SECS
                })
        });
        candidates
    }

    pub(crate) fn schedule_private_broadcasts(&self) {
        self.schedule_private_broadcasts_with_limit(None, None);
    }

    fn schedule_private_broadcasts_with_limit(
        &self,
        per_entry_limit: Option<usize>,
        only_entries: Option<&HashSet<Wtxid>>,
    ) {
        if !self.config.private_broadcast {
            return;
        }
        let Some(sender) = self.peer_manager_requests.read().as_ref().cloned() else {
            return;
        };
        let now = time::unix_time();
        let mut requests = Vec::new();
        {
            let mut broadcasts = self.private_broadcasts.lock();
            for (wtxid, entry) in broadcasts.iter_mut() {
                if only_entries.is_some_and(|entries| !entries.contains(wtxid)) {
                    continue;
                }
                let current = entry
                    .peers
                    .iter()
                    .filter(|peer| {
                        let last_activity = peer.received.unwrap_or(peer.sent);
                        now.saturating_sub(last_activity) < PRIVATE_BROADCAST_RETRY_SECS
                    })
                    .count();
                let needed = PRIVATE_BROADCAST_PEERS_PER_TRANSACTION.saturating_sub(current);
                if needed == 0 {
                    continue;
                }
                let needed = per_entry_limit.map_or(needed, |limit| needed.min(limit));
                for address in self
                    .private_broadcast_targets(entry, now)
                    .into_iter()
                    .take(needed)
                {
                    entry.peers.push(PrivateBroadcastPeer {
                        address,
                        sent: now,
                        received: None,
                    });
                    requests.push((*wtxid, address, entry.transaction.clone()));
                }
            }
        }
        for (wtxid, address, transaction) in requests {
            if sender
                .send(p2p::PeerManagerRequest::PrivateBroadcast {
                    address,
                    transaction,
                })
                .is_err()
            {
                if let Some(entry) = self.private_broadcasts.lock().get_mut(&wtxid) {
                    entry.peers.retain(|peer| peer.address != address);
                }
            }
        }
    }

    /// Reattempt private broadcasts whose recipients have not acknowledged
    /// them recently.  Core opens one additional connection per stale
    /// transaction; the normal scheduler is deliberately not used here
    /// because it would refill all three initial slots at once.
    pub(crate) fn reattempt_stale_private_broadcasts(&self) {
        if !self.config.private_broadcast {
            return;
        }
        let now = time::unix_time();
        let stale = {
            let broadcasts = self.private_broadcasts.lock();
            broadcasts
                .iter()
                .filter_map(|(wtxid, entry)| {
                    let last_confirmed = entry
                        .peers
                        .iter()
                        .filter_map(|peer| peer.received)
                        .max()
                        .unwrap_or(0);
                    (now.saturating_sub(last_confirmed) >= PRIVATE_BROADCAST_RETRY_SECS)
                        .then_some((*wtxid, entry.transaction.clone()))
                })
                .collect::<Vec<_>>()
        };
        if stale.is_empty() {
            return;
        }

        let mut eligible = HashSet::new();
        for (wtxid, transaction) in stale {
            let txid = transaction.compute_txid();
            if self.mempool.read().get(&txid).is_some() {
                self.private_broadcasts.lock().remove(&wtxid);
                continue;
            }
            match self.validate_private_broadcast_transaction(transaction.clone()) {
                Ok(()) => {
                    tracing::debug!(
                        target: "bitcoind_rs::p2p",
                        "Reattempting broadcast of stale txid={txid} wtxid={wtxid}"
                    );
                    eligible.insert(wtxid);
                }
                Err(error) => {
                    tracing::debug!(
                        target: "bitcoind_rs::p2p",
                        "Giving up broadcast attempts for txid={txid} wtxid={wtxid}: {error}"
                    );
                    self.private_broadcasts.lock().remove(&wtxid);
                }
            }
        }
        if !eligible.is_empty() {
            self.schedule_private_broadcasts_with_limit(Some(1), Some(&eligible));
        }
    }

    /// Process a transaction received over the peer network. Missing-input
    /// transactions are retained briefly so they can be retried when a parent
    /// arrives; direct RPC submission remains strict via `accept_transaction`.
    pub fn accept_peer_transaction(&self, transaction: Transaction) -> Result<Txid> {
        self.accept_peer_transaction_from(0, transaction)
    }

    pub fn accept_peer_transaction_from(
        &self,
        peer_id: usize,
        transaction: Transaction,
    ) -> Result<Txid> {
        self.expire_mempool();
        // Repeated announcements of the same orphan are common during relay
        // storms. The first admission already established that its inputs are
        // missing; rerunning full mempool validation for every announcer only
        // serializes the peer workers on the mempool lock. Refresh the
        // announcer set and return the same admission result instead.
        if !transaction.input.is_empty()
            && self.orphan_transaction_by_wtxid(transaction.compute_wtxid())
        {
            self.orphans.lock().add(transaction.clone(), Some(peer_id));
            return Err(MempoolError::MissingInput(transaction.input[0].previous_output).into());
        }
        match self.try_accept_transaction(transaction.clone()) {
            Ok((txid, _)) => {
                self.notify_mempool_transaction_from_peer(transaction, peer_id);
                Ok(txid)
            }
            Err(error @ MempoolError::MissingInput(_)) => {
                self.add_compact_extra_transaction(transaction.clone());
                if self.peer_orphan_has_rejected_parent(&transaction) {
                    // A child of a non-retryable rejected parent inherits the
                    // reject filter entry so descendants cannot be retained
                    // as orphans and repeatedly re-request this child.
                    self.recently_rejected_transactions
                        .lock()
                        .insert_non_retryable(&transaction, true);
                } else {
                    self.orphans.lock().add(transaction, Some(peer_id));
                }
                Err(error.into())
            }
            Err(error) => {
                self.add_compact_extra_transaction(transaction.clone());
                self.cache_peer_rejection(&transaction, &error);
                Err(error.into())
            }
        }
    }

    fn cache_peer_rejection(&self, transaction: &Transaction, error: &MempoolError) {
        // Missing-input results are retryable by definition and are not
        // entries in Core's recent-reject filter. This also matters for a
        // failed package containing an orphan parent: that parent remains
        // reconsiderable from the orphanage.
        if matches!(error, MempoolError::MissingInput(_)) {
            return;
        }
        // A txid is safe to cache only when policy failure is independent of
        // witness data.  Core otherwise caches the wtxid so a different
        // witness can still be downloaded and tried by txid.
        let stripped_witness = matches!(error, MempoolError::Script(_))
            && transaction
                .input
                .iter()
                .all(|input| input.witness.is_empty())
            && transaction
                .input
                .iter()
                .any(|input| self.spends_witness_program(input.previous_output));
        if stripped_witness {
            return;
        }
        let include_txid = transaction.compute_txid().to_raw_hash()
            == transaction.compute_wtxid().to_raw_hash()
            || matches!(
                error,
                MempoolError::NonStandard(reason)
                    if reason == "bad-txns-nonstandard-inputs"
            );
        let retryable = matches!(
            error,
            MempoolError::FeeRate
                | MempoolError::MinRelayFee
                | MempoolError::MinRelayFeeWithContext(_)
                | MempoolError::Full
                | MempoolError::ReplacementFee
                | MempoolError::ReplacementFeeWithContext(_)
                | MempoolError::ReplacementFeerateDiagram
        );
        if retryable {
            self.recently_rejected_transactions
                .lock()
                .insert(transaction, include_txid);
        } else {
            self.recently_rejected_transactions
                .lock()
                .insert_non_retryable(transaction, include_txid);
        }
    }

    fn spends_witness_program(&self, outpoint: OutPoint) -> bool {
        if let Some(is_witness) = self
            .mempool
            .read()
            .get(&outpoint.txid)
            .and_then(|entry| entry.transaction.output.get(outpoint.vout as usize))
            .map(|output| output.script_pubkey.is_witness_program())
        {
            return is_witness;
        }
        self.chain
            .read()
            .utxo(&outpoint)
            .is_some_and(|entry| entry.output.script_pubkey.is_witness_program())
    }

    pub(crate) fn peer_orphan_has_rejected_parent(&self, transaction: &Transaction) -> bool {
        let rejected = self.recently_rejected_transactions.lock();
        transaction.input.iter().any(|input| {
            let parent_txid = input.previous_output.txid;
            if !rejected.contains_non_retryable(BlockHash::from_raw_hash(parent_txid.to_raw_hash()))
            {
                return false;
            }
            let available = self
                .mempool
                .read()
                .get(&parent_txid)
                .and_then(|entry| {
                    entry
                        .transaction
                        .output
                        .get(input.previous_output.vout as usize)
                })
                .is_some()
                || self.chain.read().utxo(&input.previous_output).is_some();
            let in_orphanage = self.orphan_transaction_by_txid(parent_txid);
            !available && !in_orphanage
        })
    }

    /// Accept a package received from a peer and publish the same mempool
    /// notifications as ordinary peer transaction admission.  Core uses this
    /// path when a replacement parent and its child arrive separately over
    /// the wire but only pass policy when evaluated together.
    pub(crate) fn accept_peer_package_from(
        &self,
        peer_id: usize,
        transactions: &[Transaction],
    ) -> Result<Vec<Txid>> {
        self.expire_mempool();
        let (result, changes, current_height) = {
            let chain = self.chain.read();
            let mut mempool = self.mempool.write();
            let result = mempool.accept_package(transactions, &chain);
            let changes = mempool.take_changes();
            (result, changes, chain.height())
        };
        let txids = match result {
            Ok(txids) => txids,
            Err(error) => {
                for transaction in transactions {
                    self.cache_peer_rejection(transaction, &error);
                }
                return Err(error.into());
            }
        };
        self.update_fee_estimator_for_changes(&changes, current_height);
        let removed_ids = changes
            .iter()
            .filter_map(|change| match &change.kind {
                MempoolChangeKind::Removed { .. } => {
                    self.add_compact_extra_transaction(change.transaction.clone());
                    Some(change.transaction.compute_txid())
                }
                MempoolChangeKind::Added => None,
            })
            .collect::<Vec<_>>();
        self.announce_mempool_changes(removed_ids);
        self.notify_zmq_mempool_changes(changes);
        self.maybe_check_mempool();
        self.record_mempool_stats();

        // A child that arrived before its replacement parent may already be
        // in the orphan pool. Remove both package members before publishing
        // the successful parent notification so ordinary orphan promotion
        // cannot race the package result.
        {
            let mut orphans = self.orphans.lock();
            for transaction in transactions {
                orphans.remove(&transaction.compute_wtxid());
            }
        }
        for transaction in transactions {
            self.recently_rejected_transactions
                .lock()
                .remove(transaction);
            self.notify_mempool_transaction_from_peer(transaction.clone(), peer_id);
        }
        Ok(txids)
    }

    fn add_compact_extra_transaction(&self, transaction: Transaction) {
        self.compact_extra_transactions.lock().insert(transaction);
    }

    pub(crate) fn compact_extra_transactions(&self) -> Vec<Transaction> {
        self.compact_extra_transactions.lock().snapshot()
    }

    pub(crate) fn recently_rejected_transaction(&self, hash: BlockHash) -> bool {
        self.recently_rejected_transactions.lock().contains(hash)
    }

    pub(crate) fn recently_confirmed_transaction(&self, txid: Txid) -> bool {
        let chain = self.chain.read();
        chain
            .transaction_location(&txid)
            .is_some_and(|location| location.height >= chain.height().saturating_sub(1))
    }

    pub(crate) fn orphan_transaction_by_txid(&self, txid: Txid) -> bool {
        self.orphans.lock().contains_txid(txid)
    }

    pub(crate) fn orphan_transaction_by_wtxid(&self, wtxid: Wtxid) -> bool {
        self.orphans.lock().contains_wtxid(wtxid)
    }

    pub(crate) fn orphan_nonwitness_transaction_by_txid(&self, txid: Txid) -> bool {
        self.orphans.lock().contains_nonwitness_txid(txid)
    }

    pub(crate) fn add_orphan_announcers(
        &self,
        transaction: &Transaction,
        peer_ids: &[usize],
    ) -> bool {
        self.orphans.lock().add_announcers(transaction, peer_ids)
    }

    pub(crate) fn orphan_announcers(&self, transaction: &Transaction) -> Vec<usize> {
        self.orphans.lock().announcers(transaction)
    }

    pub(crate) fn add_orphan_inventory_announcer(
        &self,
        hash: BlockHash,
        witness: bool,
        peer_id: usize,
    ) -> bool {
        self.orphans
            .lock()
            .add_inventory_announcer(hash, witness, peer_id)
    }

    pub(crate) fn orphan_has_inventory(&self, hash: BlockHash, witness: bool) -> bool {
        self.orphans.lock().has_inventory(hash, witness)
    }

    pub(crate) fn orphan_transaction_for_inventory(
        &self,
        hash: BlockHash,
        witness: bool,
    ) -> Option<Transaction> {
        self.orphans.lock().transaction_for_inventory(hash, witness)
    }

    pub fn orphan_count(&self) -> usize {
        self.orphans.lock().len()
    }

    pub fn orphan_transactions(&self) -> Vec<OrphanTransaction> {
        self.orphans.lock().transactions()
    }

    fn try_accept_transaction(
        &self,
        transaction: Transaction,
    ) -> std::result::Result<(Txid, Vec<MempoolChange>), MempoolError> {
        self.try_accept_transaction_with_policy(transaction, false)
    }

    fn try_accept_transaction_with_policy(
        &self,
        transaction: Transaction,
        disable_standard_policy: bool,
    ) -> std::result::Result<(Txid, Vec<MempoolChange>), MempoolError> {
        let (result, changes, current_height) = {
            let chain = self.chain.read();
            let mut mempool = self.mempool.write();
            let result = if disable_standard_policy {
                mempool.accept_with_standard_policy_disabled(transaction, &chain)
            } else {
                mempool.accept(transaction, &chain)
            };
            let changes = mempool.take_changes();
            (result, changes, chain.height())
        };
        self.update_fee_estimator_for_changes(&changes, current_height);
        let removed_ids = changes
            .iter()
            .filter_map(|change| match &change.kind {
                MempoolChangeKind::Removed { .. } => Some(change.transaction.compute_txid()),
                MempoolChangeKind::Added => None,
            })
            .collect::<Vec<_>>();
        for change in &changes {
            if matches!(&change.kind, MempoolChangeKind::Removed { .. }) {
                self.add_compact_extra_transaction(change.transaction.clone());
            }
        }
        self.announce_mempool_changes(removed_ids);
        self.notify_zmq_mempool_changes(changes.clone());
        self.maybe_check_mempool();
        let accepted = result.map(|txid| (txid, changes));
        if accepted.is_ok() {
            self.record_mempool_stats();
        }
        accepted
    }

    fn announce_mempool_transaction(&self, txid: Txid) {
        let _ = self.mempool_events.send(txid);
    }

    fn announce_peer_mempool_transaction(&self, txid: Txid, excluded_peers: Vec<usize>) {
        self.announce_peer_mempool_transaction_with_force(txid, excluded_peers, false);
    }

    fn announce_peer_mempool_transaction_with_force(
        &self,
        txid: Txid,
        mut excluded_peers: Vec<usize>,
        force_relay: bool,
    ) {
        excluded_peers.sort_unstable();
        excluded_peers.dedup();
        let _ = self.peer_mempool_events.send(PeerMempoolEvent {
            txid,
            excluded_peers,
            force_relay,
        });
    }

    fn announce_mempool_changes(&self, mut removed: Vec<Txid>) {
        removed.sort_by_key(ToString::to_string);
        for txid in removed {
            self.announce_mempool_transaction(txid);
        }
    }

    pub(crate) fn expire_mempool(&self) {
        let changes = {
            let mut mempool = self.mempool.write();
            let expiry =
                Duration::from_secs(self.config.mempool_expiry_hours.saturating_mul(60 * 60));
            mempool.clear_expired(time::unix_time(), expiry);
            mempool.take_changes()
        };
        if changes.is_empty() {
            return;
        }
        let current_height = self.chain.read().height();
        self.update_fee_estimator_for_changes(&changes, current_height);
        let removed = changes
            .iter()
            .filter_map(|change| {
                matches!(change.kind, MempoolChangeKind::Removed { .. })
                    .then_some(change.transaction.compute_txid())
            })
            .collect();
        self.announce_mempool_changes(removed);
        self.notify_zmq_mempool_changes(changes);
        self.maybe_check_mempool();
        self.record_mempool_stats();
    }

    #[cfg(test)]
    fn announce_zmq_mempool_added(&self, transaction: Transaction) {
        if !self.config.zmq.is_enabled() {
            return;
        }
        let mempool_sequence = self.zmq_mempool_sequence.fetch_add(1, Ordering::Relaxed);
        self.zmq_events.send(zmq::Event::TransactionAdded {
            transaction: Arc::new(transaction),
            mempool_sequence,
        });
    }

    #[cfg(test)]
    fn announce_zmq_mempool_removed(&self, transaction: Transaction) {
        if !self.config.zmq.is_enabled() {
            return;
        }
        let mempool_sequence = self.zmq_mempool_sequence.fetch_add(1, Ordering::Relaxed);
        self.zmq_events.send(zmq::Event::TransactionRemoved {
            transaction: Arc::new(transaction),
            mempool_sequence,
        });
    }

    fn announce_zmq_mempool_change(&self, change: MempoolChange) {
        if !self.config.zmq.is_enabled() {
            return;
        }
        let MempoolChange {
            transaction,
            sequence,
            kind,
        } = change;
        let notify_zmq = !matches!(&kind, MempoolChangeKind::Removed { notify_zmq: false });
        self.zmq_mempool_sequence
            .fetch_max(sequence.saturating_add(1), Ordering::Relaxed);
        if !notify_zmq {
            return;
        }
        let event = match kind {
            MempoolChangeKind::Added => zmq::Event::TransactionAdded {
                transaction: Arc::new(transaction),
                mempool_sequence: sequence,
            },
            MempoolChangeKind::Removed { .. } => zmq::Event::TransactionRemoved {
                transaction: Arc::new(transaction),
                mempool_sequence: sequence,
            },
        };
        self.zmq_events.send(event);
    }

    pub(crate) fn notify_zmq_mempool_changes(&self, changes: Vec<MempoolChange>) {
        for change in changes {
            self.announce_zmq_mempool_change(change);
        }
    }

    pub(crate) fn notify_mempool_removals(&self, transactions: Vec<Transaction>) {
        let mut txids = transactions
            .into_iter()
            .map(|transaction| transaction.compute_txid())
            .collect::<Vec<_>>();
        txids.sort_by_key(ToString::to_string);
        for txid in txids {
            self.announce_mempool_transaction(txid);
        }
    }

    fn announce_zmq_block_events(&self, disconnected: &[Block], connected: &[Block]) {
        if !self.config.zmq.is_enabled() || self.zmq_events.receiver_count() == 0 {
            return;
        }
        for block in disconnected.iter().rev() {
            self.zmq_events
                .send(zmq::Event::BlockDisconnected(Arc::new(block.clone())));
        }
        for block in connected {
            self.zmq_events
                .send(zmq::Event::BlockConnected(Arc::new(block.clone())));
        }
        if (!self.config.zmq.pub_hash_block.is_empty() || !self.config.zmq.pub_raw_block.is_empty())
            && let Some(block) = connected.last()
        {
            self.zmq_events
                .send(zmq::Event::BlockTip(Arc::new(block.clone())));
        }
    }

    fn announce_mempool_diff(&self, before: HashSet<Txid>, after: HashSet<Txid>) {
        let mut changed = before
            .symmetric_difference(&after)
            .copied()
            .collect::<Vec<_>>();
        changed.sort_by_key(ToString::to_string);
        for txid in &changed {
            self.announce_mempool_transaction(*txid);
        }
        for txid in changed {
            self.announce_peer_mempool_transaction(txid, Vec::new());
        }
    }

    pub(crate) fn notify_mempool_transaction(&self, transaction: Transaction) {
        self.notify_mempool_transaction_with_exclusions(transaction, Vec::new());
    }

    pub(crate) fn mock_scheduler_forward(&self, delta_secs: u64) -> Result<()> {
        let previous = self
            .mock_scheduler_elapsed_secs
            .fetch_add(delta_secs, Ordering::Relaxed);
        let next = previous.saturating_add(delta_secs);
        if next / MAX_INITIAL_BROADCAST_DELAY_SECS > previous / MAX_INITIAL_BROADCAST_DELAY_SECS {
            self.reannounce_unbroadcast_transactions();
        }
        self.reattempt_stale_private_broadcasts();
        if next / FEE_ESTIMATOR_FLUSH_INTERVAL.as_secs()
            > previous / FEE_ESTIMATOR_FLUSH_INTERVAL.as_secs()
        {
            self.flush_fee_estimates(false)?;
        }
        Ok(())
    }

    fn reannounce_unbroadcast_transactions(&self) {
        let txids = self.mempool.read().unbroadcast_txids();
        for txid in txids {
            self.announce_peer_mempool_transaction(txid, Vec::new());
        }
    }

    pub(crate) fn notify_mempool_transaction_from_peer(
        &self,
        transaction: Transaction,
        peer_id: usize,
    ) {
        self.notify_mempool_transaction_with_exclusions(transaction, vec![peer_id]);
    }

    pub(crate) fn notify_mempool_transaction_force_from_peer(
        &self,
        transaction: Transaction,
        peer_id: usize,
    ) {
        let txid = transaction.compute_txid();
        self.announce_mempool_transaction(txid);
        self.announce_peer_mempool_transaction_with_force(txid, vec![peer_id], true);
    }

    pub(crate) fn notify_mempool_transaction_force(&self, transaction: Transaction) {
        let txid = transaction.compute_txid();
        self.orphans.lock().remove(&transaction.compute_wtxid());
        self.announce_mempool_transaction(txid);
        self.announce_peer_mempool_transaction_with_force(txid, Vec::new(), true);
        self.promote_orphans_for_parent(&transaction);
    }

    fn notify_mempool_transaction_with_exclusions(
        &self,
        transaction: Transaction,
        excluded_peers: Vec<usize>,
    ) {
        let txid = transaction.compute_txid();
        self.orphans.lock().remove(&transaction.compute_wtxid());
        self.announce_mempool_transaction(txid);
        self.announce_peer_mempool_transaction(txid, excluded_peers);
        self.promote_orphans_for_parent(&transaction);
    }

    fn promote_orphans_for_parent(&self, parent: &Transaction) {
        let mut pending = self
            .orphans
            .lock()
            .take_children(parent)
            .into_iter()
            .collect::<VecDeque<_>>();
        while let Some(entry) = pending.pop_front() {
            let transaction = entry.transaction.clone();
            let txid = transaction.compute_txid();
            match self.try_accept_transaction(transaction.clone()) {
                Ok((accepted_txid, _)) => {
                    self.announce_mempool_transaction(accepted_txid);
                    self.announce_peer_mempool_transaction(
                        accepted_txid,
                        entry.announcers.into_iter().collect(),
                    );
                    pending.extend(self.orphans.lock().take_children(&transaction));
                }
                Err(MempoolError::MissingInput(_)) => {
                    self.orphans.lock().add_entry(entry);
                }
                Err(error) => {
                    self.cache_peer_rejection(&transaction, &error);
                    let reject_reason = error.reject_reason();
                    info!(
                        %txid,
                        %error,
                        reject_reason,
                        "rejected orphan transaction"
                    );
                }
            }
        }
    }

    pub fn invalidate_block(&self, hash: bitcoin::BlockHash) -> Result<ChainEvent> {
        let (tip, changed, activated_blocks, disconnected_blocks) = {
            let mut chain = self.chain.write();
            let previous = chain.best_hash();
            let tip = chain.invalidate_block(&hash)?;
            let changed = previous != chain.best_hash();
            let disconnected_has_transactions =
                changed && chain.disconnected_suffix_has_non_coinbase_transactions(previous)?;
            let load_block_bodies = changed
                && (disconnected_has_transactions || self.chain_change_needs_block_bodies());
            let activated_blocks = if load_block_bodies {
                chain.active_blocks_after(previous)?
            } else {
                Vec::new()
            };
            let disconnected_blocks = if load_block_bodies {
                chain.disconnected_blocks_after(previous)?
            } else {
                Vec::new()
            };
            (tip, changed, activated_blocks, disconnected_blocks)
        };
        if changed {
            self.announce_zmq_block_events(&disconnected_blocks, &[]);
            self.reconcile_mempool_after_chain_change(
                &activated_blocks,
                &disconnected_blocks,
                true,
            );
            self.announce_zmq_block_events(&[], &activated_blocks);
            self.promote_orphans_after_chain_change(&activated_blocks, &disconnected_blocks);
            let _ = self.events.send(tip.clone());
        }
        self.refresh_large_work_invalid_chain_warning();
        self.refresh_versionbits_warning();
        self.maybe_check_block_index();
        Ok(tip)
    }

    pub fn reconsider_block(&self, hash: bitcoin::BlockHash) -> Result<ChainEvent> {
        let (tip, changed, activated_blocks, disconnected_blocks) = {
            let mut chain = self.chain.write();
            let previous = chain.best_hash();
            let tip = chain.reconsider_block(&hash)?;
            let changed = previous != chain.best_hash();
            let disconnected_has_transactions =
                changed && chain.disconnected_suffix_has_non_coinbase_transactions(previous)?;
            let load_block_bodies = changed
                && (disconnected_has_transactions || self.chain_change_needs_block_bodies());
            let activated_blocks = if load_block_bodies {
                chain.active_blocks_after(previous)?
            } else {
                Vec::new()
            };
            let disconnected_blocks = if load_block_bodies {
                chain.disconnected_blocks_after(previous)?
            } else {
                Vec::new()
            };
            (tip, changed, activated_blocks, disconnected_blocks)
        };
        if changed {
            self.announce_zmq_block_events(&disconnected_blocks, &[]);
            self.reconcile_mempool_after_chain_change(
                &activated_blocks,
                &disconnected_blocks,
                false,
            );
            self.announce_zmq_block_events(&[], &activated_blocks);
            self.promote_orphans_after_chain_change(&activated_blocks, &disconnected_blocks);
            let _ = self.events.send(tip.clone());
        }
        self.refresh_versionbits_warning();
        self.maybe_check_block_index();
        Ok(tip)
    }

    pub fn precious_block(&self, hash: bitcoin::BlockHash) -> Result<ChainEvent> {
        let (tip, changed, activated_blocks, disconnected_blocks) = {
            let mut chain = self.chain.write();
            let previous = chain.best_hash();
            let tip = chain.precious_block(&hash)?;
            let changed = previous != chain.best_hash();
            let disconnected_has_transactions =
                changed && chain.disconnected_suffix_has_non_coinbase_transactions(previous)?;
            let load_block_bodies = changed
                && (disconnected_has_transactions || self.chain_change_needs_block_bodies());
            let activated_blocks = if load_block_bodies {
                chain.active_blocks_after(previous)?
            } else {
                Vec::new()
            };
            let disconnected_blocks = if load_block_bodies {
                chain.disconnected_blocks_after(previous)?
            } else {
                Vec::new()
            };
            (tip, changed, activated_blocks, disconnected_blocks)
        };
        if changed {
            self.announce_zmq_block_events(&disconnected_blocks, &[]);
            self.reconcile_mempool_after_chain_change(
                &activated_blocks,
                &disconnected_blocks,
                false,
            );
            self.announce_zmq_block_events(&[], &activated_blocks);
            self.promote_orphans_after_chain_change(&activated_blocks, &disconnected_blocks);
            let _ = self.events.send(tip.clone());
        }
        self.refresh_versionbits_warning();
        self.maybe_check_block_index();
        Ok(tip)
    }

    pub fn subscribe_chain(&self) -> broadcast::Receiver<ChainEvent> {
        self.events.subscribe()
    }

    pub fn subscribe_mempool(&self) -> broadcast::Receiver<MempoolEvent> {
        self.mempool_events.subscribe()
    }

    pub(crate) fn subscribe_peer_mempool(&self) -> broadcast::Receiver<PeerMempoolEvent> {
        self.peer_mempool_events.subscribe()
    }

    #[cfg(test)]
    pub(crate) fn subscribe_zmq(&self) -> broadcast::Receiver<zmq::Event> {
        self.zmq_events.subscribe_all()
    }

    pub fn peer_count(&self) -> usize {
        self.peer_count.load(Ordering::Relaxed)
    }

    pub(crate) fn notify_peer_task_finished(&self) {
        self.peer_tasks_changed.notify_waiters();
    }

    pub(crate) async fn wait_for_peer_tasks(&self) {
        loop {
            if self.peer_count.load(Ordering::Acquire) == 0 {
                return;
            }
            let notified = self.peer_tasks_changed.notified();
            tokio::pin!(notified);
            notified.as_mut().enable();
            if self.peer_count.load(Ordering::Acquire) == 0 {
                return;
            }
            notified.await;
        }
    }

    pub(crate) fn non_reduced_outbound_count(&self) -> usize {
        self.non_reduced_outbound_count.load(Ordering::Acquire)
    }

    /// Admit an automatic outbound peer under the optional reduced-data
    /// compatibility policy.
    ///
    /// The peer table write lock covers the counter reservation so a
    /// simultaneous disconnect cannot let two handshakes pass the limit.
    /// Manual connections and inbound/feeler/private-broadcast connections
    /// are deliberately outside this project-specific limit.
    pub(crate) fn admit_non_reduced_outbound(&self, id: usize, services: u64) -> bool {
        let Some(max_stale_outbound) = self.config.max_stale_outbound() else {
            return true;
        };
        let mut peers = self.peers.write();
        let Some(peer) = peers.get_mut(&id) else {
            return false;
        };
        if peer.version.is_some() || !is_non_reduced_outbound(peer, services) {
            return true;
        }
        let count = self.non_reduced_outbound_count.load(Ordering::Acquire);
        if count >= max_stale_outbound {
            return false;
        }
        self.non_reduced_outbound_count
            .fetch_add(1, Ordering::AcqRel);
        true
    }

    pub(crate) fn begin_rpc_command(&self, method: &str) -> usize {
        let id = self.rpc_command_sequence.fetch_add(1, Ordering::Relaxed);
        self.rpc_commands
            .write()
            .insert(id, (method.to_owned(), Instant::now()));
        id
    }

    pub(crate) fn end_rpc_command(&self, id: usize) {
        self.rpc_commands.write().remove(&id);
    }

    pub(crate) fn active_rpc_commands(&self) -> Vec<serde_json::Value> {
        let now = Instant::now();
        self.rpc_commands
            .read()
            .values()
            .map(|(method, started)| {
                serde_json::json!({
                    "method": method,
                    "duration": now.duration_since(*started).as_micros() as u64,
                })
            })
            .collect()
    }

    pub fn total_bytes_sent(&self) -> u64 {
        self.total_bytes_sent.load(Ordering::Relaxed)
    }

    pub fn total_bytes_received(&self) -> u64 {
        self.total_bytes_received.load(Ordering::Relaxed)
    }

    pub(crate) fn max_upload_target(&self) -> u64 {
        self.config.max_upload_target
    }

    pub(crate) fn max_upload_timeframe(&self) -> u64 {
        MAX_UPLOAD_TIMEFRAME_SECS
    }

    pub(crate) fn outbound_target_reached(&self, historical_block_serving_limit: bool) -> bool {
        outbound_target_reached(
            self.config.max_upload_target,
            *self.outbound_usage.lock(),
            unix_time_seconds(),
            historical_block_serving_limit,
        )
    }

    pub(crate) fn outbound_target_bytes_left(&self) -> u64 {
        let usage = *self.outbound_usage.lock();
        self.config.max_upload_target.saturating_sub(usage.bytes)
    }

    pub(crate) fn outbound_time_left_in_cycle(&self) -> u64 {
        outbound_time_left_in_cycle(
            self.config.max_upload_target,
            *self.outbound_usage.lock(),
            unix_time_seconds(),
        )
    }

    pub(crate) fn historical_block_serving_limit_reached(
        &self,
        hash: &BlockHash,
        filtered: bool,
        permissions: PeerPermissions,
    ) -> bool {
        if permissions.contains(PeerPermissions::DOWNLOAD) || !self.outbound_target_reached(true) {
            return false;
        }
        if filtered {
            return true;
        }
        let chain = self.chain.read();
        let Some(header) = chain.header_by_hash(hash) else {
            return false;
        };
        let best_header = chain.best_header_tip();
        let Some(best_header) = chain.header_by_hash(&best_header.hash) else {
            return false;
        };
        u64::from(best_header.time).saturating_sub(u64::from(header.time))
            > HISTORICAL_BLOCK_AGE_SECS
    }

    pub(crate) fn record_bytes_sent(&self, peer_id: usize, bytes: usize, command: &str) {
        let bytes = u64::try_from(bytes).unwrap_or(u64::MAX);
        self.total_bytes_sent.fetch_add(bytes, Ordering::Relaxed);
        let now = unix_time_seconds();
        {
            let mut usage = self.outbound_usage.lock();
            if usage.cycle_start.saturating_add(MAX_UPLOAD_TIMEFRAME_SECS) < now {
                usage.cycle_start = now;
                usage.bytes = 0;
            }
            usage.bytes = usage.bytes.saturating_add(bytes);
        }
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.bytes_sent = peer.bytes_sent.saturating_add(bytes);
            peer.last_send = now;
            let total = peer
                .bytes_sent_per_msg
                .entry(command.to_owned())
                .or_default();
            *total = total.saturating_add(bytes);
        }
    }

    /// Account bytes used by the BIP324 transport handshake. Core includes
    /// these bytes in the peer totals and updates lastsend, but does not put
    /// them in a decoded P2P message bucket.
    pub(crate) fn record_transport_bytes_sent(&self, peer_id: usize, bytes: usize) {
        let bytes = u64::try_from(bytes).unwrap_or(u64::MAX);
        self.total_bytes_sent.fetch_add(bytes, Ordering::Relaxed);
        let now = unix_time_seconds();
        {
            let mut usage = self.outbound_usage.lock();
            if usage.cycle_start.saturating_add(MAX_UPLOAD_TIMEFRAME_SECS) < now {
                usage.cycle_start = now;
                usage.bytes = 0;
            }
            usage.bytes = usage.bytes.saturating_add(bytes);
        }
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.bytes_sent = peer.bytes_sent.saturating_add(bytes);
            peer.last_send = now;
        }
    }

    /// Append a decoded application-layer P2P message in Core's
    /// `-capturemessages` format. The transport envelope is deliberately not
    /// included, so v1 and BIP324 captures have the same record structure.
    pub(crate) fn capture_message(
        &self,
        peer_id: usize,
        incoming: bool,
        message: &wire::Message,
    ) -> Result<()> {
        if !self.config.capture_messages {
            return Ok(());
        }
        let endpoint = self
            .peers
            .read()
            .get(&peer_id)
            .map(|peer| peer.endpoint.clone());
        let Some(endpoint) = endpoint else {
            return Ok(());
        };
        let command = message.command();
        let command_bytes = command.as_bytes();
        if command_bytes.len() > 12 {
            bail!("P2P command exceeds capture header width: {command}");
        }
        let payload = wire::encode_message_payload(message)?;
        let payload_len = u32::try_from(payload.len())
            .context("P2P capture payload exceeds the on-disk length field")?;
        let network_datadir = if network_data_dir_name(self.config.network).is_empty() {
            self.config.datadir.clone()
        } else {
            self.config
                .datadir
                .join(network_data_dir_name(self.config.network))
        };
        let directory = network_datadir
            .join("message_capture")
            .join(endpoint.to_string().replace(':', "_"));
        fs::create_dir_all(&directory)
            .with_context(|| format!("creating P2P capture directory {}", directory.display()))?;
        let path = directory.join(if incoming {
            "msgs_recv.dat"
        } else {
            "msgs_sent.dat"
        });
        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)
            .with_context(|| format!("opening P2P capture file {}", path.display()))?;
        let timestamp =
            u64::try_from(time::unix_time_millis().saturating_mul(1_000)).unwrap_or(u64::MAX);
        file.write_all(&timestamp.to_le_bytes())?;
        let mut command_header = [0u8; 12];
        command_header[..command_bytes.len()].copy_from_slice(command_bytes);
        file.write_all(&command_header)?;
        file.write_all(&payload_len.to_le_bytes())?;
        file.write_all(&payload)?;
        file.flush()?;
        Ok(())
    }

    /// Account bytes as soon as they arrive from a v1 socket. The frame may
    /// still be incomplete, so there is no message bucket to update yet.
    pub(crate) fn record_partial_bytes_received(&self, peer_id: usize, bytes: usize) {
        let bytes = u64::try_from(bytes).unwrap_or(u64::MAX);
        let skipped = self
            .peers
            .write()
            .get_mut(&peer_id)
            .map(|peer| {
                let skipped = peer.unread_detection_bytes.min(bytes);
                peer.unread_detection_bytes -= skipped;
                skipped
            })
            .unwrap_or(0);
        self.total_bytes_received
            .fetch_add(bytes.saturating_sub(skipped), Ordering::Relaxed);
    }

    /// Account bytes observed with MSG_PEEK while an inbound transport is
    /// still being identified. They are exposed immediately in getpeerinfo;
    /// the corresponding consumed bytes are reconciled by the handshake or
    /// completed v1-frame accounting paths.
    pub(crate) fn record_transport_detection_bytes(&self, peer_id: usize, bytes: usize) {
        let bytes = u64::try_from(bytes).unwrap_or(u64::MAX);
        self.total_bytes_received
            .fetch_add(bytes, Ordering::Relaxed);
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.bytes_received = peer.bytes_received.saturating_add(bytes);
            peer.preaccounted_received_bytes =
                peer.preaccounted_received_bytes.saturating_add(bytes);
            peer.unread_detection_bytes = peer.unread_detection_bytes.saturating_add(bytes);
            peer.last_recv = unix_time_seconds();
        }
    }

    /// Account bytes consumed by the BIP324 handshake, excluding any prefix
    /// bytes already counted during transport detection.
    pub(crate) fn record_handshake_bytes_received(&self, peer_id: usize, bytes: usize) {
        let bytes = u64::try_from(bytes).unwrap_or(u64::MAX);
        let fresh = self
            .peers
            .write()
            .get_mut(&peer_id)
            .map(|peer| {
                let skipped = peer.unread_detection_bytes.min(bytes);
                peer.unread_detection_bytes -= skipped;
                peer.preaccounted_received_bytes =
                    peer.preaccounted_received_bytes.saturating_sub(skipped);
                bytes.saturating_sub(skipped)
            })
            .unwrap_or(bytes);
        if fresh != 0 {
            self.record_transport_bytes_received(
                peer_id,
                usize::try_from(fresh).unwrap_or(usize::MAX),
            );
        }
    }

    pub(crate) fn record_transport_bytes_received(&self, peer_id: usize, bytes: usize) {
        let bytes = u64::try_from(bytes).unwrap_or(u64::MAX);
        self.total_bytes_received
            .fetch_add(bytes, Ordering::Relaxed);
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.bytes_received = peer.bytes_received.saturating_add(bytes);
            peer.last_recv = unix_time_seconds();
        }
    }

    /// Update the per-message byte bucket after a complete frame has been
    /// decoded. v1 transport totals were already updated while reading the
    /// socket, including fragmented frames.
    pub(crate) fn record_received_message(&self, peer_id: usize, bytes: usize, command: &str) {
        let bytes = u64::try_from(bytes).unwrap_or(u64::MAX);
        let mut peers = if bytes > 1_000_000 && command == P2P_MESSAGE_TYPE_OTHER {
            let Some(peers) = self.peers.try_write() else {
                return;
            };
            peers
        } else {
            self.peers.write()
        };
        if let Some(peer) = peers.get_mut(&peer_id) {
            let preaccounted = peer.preaccounted_received_bytes.min(bytes);
            peer.preaccounted_received_bytes -= preaccounted;
            peer.bytes_received = peer
                .bytes_received
                .saturating_add(bytes.saturating_sub(preaccounted));
            peer.last_recv = unix_time_seconds();
            let command = received_p2p_message_type(command);
            let total = peer
                .bytes_received_per_msg
                .entry(command.to_owned())
                .or_default();
            *total = total.saturating_add(bytes);
        }
    }

    pub(crate) fn record_bytes_received(&self, peer_id: usize, bytes: usize, command: &str) {
        let bytes = u64::try_from(bytes).unwrap_or(u64::MAX);
        self.total_bytes_received
            .fetch_add(bytes, Ordering::Relaxed);
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            let now = unix_time_seconds();
            peer.bytes_received = peer.bytes_received.saturating_add(bytes);
            peer.last_recv = now;
            let command = received_p2p_message_type(command);
            let total = peer
                .bytes_received_per_msg
                .entry(command.to_owned())
                .or_default();
            *total = total.saturating_add(bytes);
        }
    }

    pub(crate) fn record_peer_inv_sequence(&self, peer_id: usize, sequence: u64) {
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.last_inv_sequence = sequence;
        }
    }

    pub(crate) fn set_peer_inv_to_send(&self, peer_id: usize, count: usize) {
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.inv_to_send = count;
        }
    }

    pub(crate) fn record_peer_transaction(&self, peer_id: usize) {
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.last_transaction = unix_time_seconds();
        }
    }

    pub(crate) fn record_peer_block(&self, peer_id: usize, hash: BlockHash) {
        let current_common = self
            .peers
            .read()
            .get(&peer_id)
            .and_then(|peer| peer.last_common_block);
        let (height, active, common_height) = {
            let chain = self.chain.read();
            (
                chain.block_height_by_hash(&hash),
                chain.is_active_block(&hash),
                current_common.and_then(|common| chain.block_height_by_hash(&common)),
            )
        };
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.last_block = unix_time_seconds();
            if active
                && height
                    .is_some_and(|height| common_height.is_none_or(|current| height >= current))
            {
                peer.last_common_block = Some(hash);
            }
        }
    }

    pub(crate) fn update_peer_best_known_block(&self, peer_id: usize, hash: BlockHash) {
        let chain = self.chain.read();
        let mut peers = self.peers.write();
        let Some(peer) = peers.get_mut(&peer_id) else {
            return;
        };
        let active_work = chain.tip().work;

        let mut update_known = |candidate_hash: BlockHash, candidate_work| {
            let should_update = peer.best_known_block.is_none_or(|current| {
                chain
                    .chain_work_by_hash(&current)
                    .is_none_or(|current_work| candidate_work >= current_work)
            });
            if should_update {
                peer.best_known_block = Some(candidate_hash);
                if candidate_work > active_work {
                    peer.last_block_announcement = unix_time_seconds();
                }
            }
        };

        // Match Core's ProcessBlockAvailability: resolve the previously
        // unknown announcement before handling the new one.
        if let Some(unknown_hash) = peer.last_unknown_block.take() {
            if let Some(unknown_work) = chain.chain_work_by_hash(&unknown_hash) {
                update_known(unknown_hash, unknown_work);
            } else {
                peer.last_unknown_block = Some(unknown_hash);
            }
        }

        if let Some(candidate_work) = chain.chain_work_by_hash(&hash) {
            update_known(hash, candidate_work);
        } else {
            // An unindexed announcement is retained until a later header or
            // block update gives us enough information to compare its work.
            peer.last_unknown_block = Some(hash);
        }
    }

    pub(crate) fn process_peer_block_availability(&self, peer_id: usize) {
        let chain = self.chain.read();
        let mut peers = self.peers.write();
        let Some(peer) = peers.get_mut(&peer_id) else {
            return;
        };
        let Some(unknown_hash) = peer.last_unknown_block.take() else {
            return;
        };
        let Some(unknown_work) = chain.chain_work_by_hash(&unknown_hash) else {
            peer.last_unknown_block = Some(unknown_hash);
            return;
        };
        let active_work = chain.tip().work;
        let should_update = peer.best_known_block.is_none_or(|current| {
            chain
                .chain_work_by_hash(&current)
                .is_none_or(|current_work| unknown_work >= current_work)
        });
        if should_update {
            peer.best_known_block = Some(unknown_hash);
            if unknown_work > active_work {
                peer.last_block_announcement = unix_time_seconds();
            }
        }
    }

    fn headers_sync_peer_is_eligible(peer: &PeerInfo) -> bool {
        peer.version.is_some()
            && !matches!(
                peer.connection_type,
                "addr-fetch" | "feeler" | "private-broadcast"
            )
            && peer.services & (wire::NODE_NETWORK | wire::NODE_NETWORK_LIMITED) != 0
    }

    pub(crate) fn best_header_is_recent(&self) -> bool {
        let chain = self.chain.read();
        let best_header = chain.best_header_tip();
        let Some(header) = chain.header(best_header.height) else {
            return false;
        };
        u64::from(header.time).saturating_add(24 * 60 * 60) >= time::unix_time()
    }

    /// Claim Core's single initial headers-sync slot for a connected peer.
    /// Once the node is within a day of the current time Core allows all
    /// suitable peers to start their own headers requests.
    pub(crate) fn start_initial_headers_sync(&self, peer_id: usize) -> bool {
        let allow_parallel = self.best_header_is_recent();
        let mut started = self.headers_sync_started.lock();
        if started.contains(&peer_id) {
            return false;
        }
        let replaces_limited_peer = if allow_parallel {
            false
        } else {
            let peers = self.peers.read();
            let candidate_is_full = peers
                .get(&peer_id)
                .is_some_and(|peer| peer.services & wire::NODE_NETWORK != 0);
            candidate_is_full
                && started.iter().any(|started_peer_id| {
                    peers.get(started_peer_id).is_some_and(|peer| {
                        peer.services & wire::NODE_NETWORK == 0
                            && peer.services & wire::NODE_NETWORK_LIMITED != 0
                    })
                })
        };
        if !allow_parallel
            && !replaces_limited_peer
            && self.headers_sync_peers.load(Ordering::Relaxed) != 0
        {
            return false;
        }
        if !self
            .peers
            .read()
            .get(&peer_id)
            .is_some_and(Self::headers_sync_peer_is_eligible)
        {
            return false;
        }
        started.insert(peer_id);
        self.headers_sync_active.lock().insert(peer_id);
        self.headers_sync_peers.fetch_add(1, Ordering::Relaxed);
        self.initialize_chain_sync_timeout(peer_id);
        true
    }

    /// Apply Core's one-new-peer-per-announced-block headers-sync policy.
    pub(crate) fn headers_sync_for_block_inventory(
        &self,
        peer_id: usize,
        block_hash: BlockHash,
    ) -> bool {
        if self.headers_sync_active.lock().contains(&peer_id) {
            return true;
        }
        let mut triggered = self.inv_triggered_headers_sync.lock();
        let mut last_block = self.last_block_inv_triggering_headers_sync.lock();
        if triggered.contains(&peer_id) {
            return false;
        }
        if *last_block == Some(block_hash) {
            return false;
        }
        triggered.insert(peer_id);
        *last_block = Some(block_hash);
        true
    }

    pub(crate) fn clear_inv_headers_sync_trigger(&self, peer_id: usize) {
        let mut triggered = self.inv_triggered_headers_sync.lock();
        if !triggered.remove(&peer_id) || !triggered.is_empty() {
            return;
        }
        self.last_block_inv_triggering_headers_sync.lock().take();
    }

    fn initialize_chain_sync_timeout(&self, peer_id: usize) {
        let tip_hash = self.chain.read().tip().hash;
        let mut states = self.chain_sync_states.write();
        let state = states.entry(peer_id).or_default();
        if state.timeout == 0 {
            state.timeout = time::unix_time().saturating_add(20 * 60);
            state.work_hash = Some(tip_hash);
            state.sent_getheaders = false;
        }
    }

    fn assign_headers_sync_replacement(
        &self,
        excluded_peer_id: Option<usize>,
    ) -> Option<tokio::sync::mpsc::UnboundedSender<p2p::PeerCommand>> {
        if self.headers_sync_peers.load(Ordering::Relaxed) != 0 {
            return None;
        }
        let mut started = self.headers_sync_started.lock();
        let candidate = self
            .peers
            .read()
            .values()
            .filter(|peer| Some(peer.id) != excluded_peer_id)
            .filter(|peer| Self::headers_sync_peer_is_eligible(peer))
            .min_by_key(|peer| (!peer.inbound, peer.id))
            .map(|peer| peer.id)?;
        let sender = self.peer_commands.read().get(&candidate).cloned()?;
        started.insert(candidate);
        self.headers_sync_active.lock().insert(candidate);
        self.headers_sync_peers.fetch_add(1, Ordering::Relaxed);
        self.initialize_chain_sync_timeout(candidate);
        Some(sender)
    }

    /// Drop a peer's initial headers-sync claim and, if possible, immediately
    /// hand the slot to another connected peer.
    pub(crate) fn release_headers_sync_peer(
        &self,
        peer_id: usize,
    ) -> Option<tokio::sync::mpsc::UnboundedSender<p2p::PeerCommand>> {
        if !self.clear_headers_sync_peer(peer_id) {
            return None;
        }
        self.assign_headers_sync_replacement(Some(peer_id))
    }

    /// Clear a headers-sync claim without immediately assigning a replacement.
    /// Core uses this path when a `noban` peer times out: the peer remains
    /// connected while its existing sync claim is cleared, allowing the
    /// message loop to retry without disconnecting it.
    pub(crate) fn clear_headers_sync_peer(&self, peer_id: usize) -> bool {
        let removed = self.headers_sync_started.lock().remove(&peer_id);
        if removed {
            self.headers_sync_peers.fetch_sub(1, Ordering::Relaxed);
        }
        removed
    }

    pub(crate) fn reset_initial_headers_sync_peer(&self, peer_id: usize) {
        self.headers_sync_active.lock().remove(&peer_id);
    }

    /// Release body requests that have aged past the short relay race window
    /// when a peer continues making header progress without supplying them.
    /// This only affects missing bodies; requests for bodies already present
    /// in the native store are cleared by the normal completion path.
    pub(crate) fn clear_stale_peer_block_requests_for_missing_bodies(
        &self,
        peer_id: usize,
        minimum_age: Duration,
    ) -> usize {
        // This is a wall-clock relay-race guard.  Functional tests and RPC
        // callers that advance mocktime expect the Core in-flight window to
        // remain exact, so never age those requests using real elapsed time.
        if time::mock_time() != 0 {
            return 0;
        }
        let chain = self.chain.read();
        let mut cleared = 0;
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.inflight_blocks.retain(|inflight| {
                let stale = inflight.requested_at.elapsed() >= minimum_age;
                let keep = !stale || chain.store.contains(&inflight.hash);
                if !keep {
                    cleared += 1;
                }
                keep
            });
        }
        if cleared != 0 {
            self.block_stalling_since.write().remove(&peer_id);
        }
        cleared
    }

    /// Apply Core's chain-sync timeout to outbound peers that started header
    /// synchronization. A peer first gets a full chain-sync grace period. If
    /// it still has not announced a chain with enough work, send one
    /// getheaders request using the chain tip that established the timer and
    /// then give it the shorter response window before disconnecting it.
    pub(crate) fn consider_outbound_eviction(&self, peer_id: usize) -> OutboundEvictionAction {
        let Some(peer) = self.peers.read().get(&peer_id).cloned() else {
            return OutboundEvictionAction::None;
        };
        let eligible_connection = !peer.inbound
            && matches!(
                peer.connection_type,
                "outbound-full" | "outbound-full-relay" | "block-relay-only"
            );
        let sync_active = self.headers_sync_active.lock().contains(&peer_id);
        if !eligible_connection || !sync_active {
            return OutboundEvictionAction::None;
        }

        let state_snapshot = self
            .chain_sync_states
            .read()
            .get(&peer_id)
            .copied()
            .unwrap_or_default();
        let (tip_hash, tip_work, peer_work, benchmark_work, benchmark_parent) = {
            let chain = self.chain.read();
            let tip = chain.tip();
            let peer_work = peer
                .best_known_block
                .and_then(|hash| chain.chain_work_by_hash(&hash));
            let benchmark_work = state_snapshot
                .work_hash
                .and_then(|hash| chain.chain_work_by_hash(&hash));
            let benchmark_parent = state_snapshot.work_hash.and_then(|hash| {
                chain
                    .header_by_hash(&hash)
                    .map(|header| header.prev_blockhash)
            });
            (
                tip.hash,
                tip.work,
                peer_work,
                benchmark_work,
                benchmark_parent,
            )
        };

        let now = time::unix_time();
        let mut states = self.chain_sync_states.write();
        let protected_count = states.values().filter(|state| state.protect).count();
        let state = states.entry(peer_id).or_default();

        // Core protects only full-relay outbound peers, and only while one of
        // the four protection slots is still available. Block-relay peers are
        // deliberately always subject to the timeout below.
        if !state.protect
            && matches!(
                peer.connection_type,
                "outbound-full" | "outbound-full-relay"
            )
            && peer_work.is_some_and(|work| work >= tip_work)
            && protected_count < 4
        {
            state.protect = true;
        }
        if state.protect {
            return OutboundEvictionAction::None;
        }

        if peer_work.is_some_and(|work| work >= tip_work) {
            if state.timeout != 0 {
                state.timeout = 0;
                state.work_hash = None;
                state.sent_getheaders = false;
            }
        } else if state.timeout == 0
            || (state.work_hash.is_some()
                && peer_work
                    .zip(benchmark_work)
                    .is_some_and(|(peer_work, benchmark_work)| peer_work >= benchmark_work))
        {
            state.timeout = now.saturating_add(20 * 60);
            state.work_hash = Some(tip_hash);
            state.sent_getheaders = false;
            debug!(
                "outbound eviction timer started peer={peer_id} timeout={} best_known={:?}",
                state.timeout, peer.best_known_block
            );
        } else if state.timeout > 0 && now > state.timeout {
            if state.sent_getheaders {
                info!(
                    "Outbound peer has old chain, best known block = {}, peer={peer_id}",
                    peer.best_known_block
                        .map_or_else(|| "<none>".to_owned(), |hash| hash.to_string())
                );
                return OutboundEvictionAction::Disconnect;
            }
            state.sent_getheaders = true;
            state.timeout = now.saturating_add(2 * 60);
            debug!(
                "outbound eviction verification getheaders peer={peer_id} timeout={}",
                state.timeout
            );
            if let Some(parent_hash) = benchmark_parent {
                return OutboundEvictionAction::RequestHeaders(parent_hash);
            }
            return OutboundEvictionAction::RequestHeaders(tip_hash);
        }

        OutboundEvictionAction::None
    }

    pub(crate) fn extra_full_outbound_requested(&self) -> bool {
        self.try_new_outbound_peer.load(Ordering::Acquire)
    }

    pub(crate) fn extra_block_relay_attempt_due(&self, now: u64) -> bool {
        self.extra_block_relay_peers_enabled.load(Ordering::Acquire)
            && now >= self.next_extra_block_relay_at.load(Ordering::Acquire)
    }

    pub(crate) fn claim_extra_block_relay_attempt(&self, now: u64) -> bool {
        if !self.extra_block_relay_peers_enabled.load(Ordering::Acquire) {
            return false;
        }
        let next = self.next_extra_block_relay_at.load(Ordering::Acquire);
        if now < next {
            return false;
        }
        self.next_extra_block_relay_at
            .compare_exchange(
                next,
                now.saturating_add(EXTRA_BLOCK_RELAY_ONLY_PEER_INTERVAL_SECS),
                Ordering::AcqRel,
                Ordering::Acquire,
            )
            .is_ok()
    }

    /// Run Core's periodic stale-tip and extra-outbound maintenance. The
    /// connection scheduler consumes the two resulting flags on its next
    /// AddrMan pass; the peer manager itself remains responsible for opening
    /// and closing sockets.
    pub(crate) fn check_for_stale_tip_and_evict_peers(
        &self,
        now: u64,
        max_full_relay: usize,
        max_block_relay: usize,
    ) {
        self.evict_extra_outbound_peers(now, max_full_relay, max_block_relay);

        if !self.uses_addrman_outgoing() || !self.network_active() {
            self.try_new_outbound_peer.store(false, Ordering::Release);
            self.extra_block_relay_peers_enabled
                .store(false, Ordering::Release);
            return;
        }

        if max_block_relay != 0
            && !self.extra_block_relay_peers_enabled.load(Ordering::Acquire)
            && self.can_direct_fetch_tip(now)
        {
            self.extra_block_relay_peers_enabled
                .store(true, Ordering::Release);
            self.next_extra_block_relay_at.store(
                now.saturating_add(EXTRA_BLOCK_RELAY_ONLY_PEER_INTERVAL_SECS),
                Ordering::Release,
            );
            debug!("enabling extra block-relay-only peers");
        }

        let check_at = self.stale_tip_check_at.load(Ordering::Acquire);
        if now < check_at {
            return;
        }
        let stale = self.tip_may_be_stale(now);
        if max_full_relay == MAX_OUTBOUND_FULL_RELAY_CONNECTIONS && stale {
            let age = now.saturating_sub(self.last_tip_update.load(Ordering::Acquire));
            info!(
                "Potential stale tip detected, will try using extra outbound peer (last tip update: {age} seconds ago)"
            );
            self.try_new_outbound_peer.store(true, Ordering::Release);
        } else {
            self.try_new_outbound_peer.store(false, Ordering::Release);
        }
        self.stale_tip_check_at.store(
            now.saturating_add(STALE_TIP_CHECK_INTERVAL_SECS),
            Ordering::Release,
        );
    }

    fn tip_may_be_stale(&self, now: u64) -> bool {
        let last_update = self.last_tip_update.load(Ordering::Acquire);
        if last_update == 0 {
            self.last_tip_update.store(now, Ordering::Release);
            return false;
        }
        if self
            .peer_infos()
            .into_iter()
            .any(|peer| !peer.inflight_heights().is_empty())
        {
            return false;
        }
        let spacing = self.chain.read().network.params().pow_target_spacing;
        now.saturating_sub(last_update) > spacing.saturating_mul(3)
    }

    fn can_direct_fetch_tip(&self, now: u64) -> bool {
        let chain = self.chain.read();
        let Some(header) = chain.header(chain.height()) else {
            return false;
        };
        let now = i64::try_from(now).unwrap_or(i64::MAX);
        let spacing = i64::try_from(chain.network.params().pow_target_spacing).unwrap_or(i64::MAX);
        i64::from(header.time) > now.saturating_sub(spacing.saturating_mul(20))
    }

    pub(crate) fn uses_addrman_outgoing(&self) -> bool {
        !self.config.connect_disabled && self.config.seed_nodes.is_empty()
    }

    fn evict_extra_outbound_peers(&self, now: u64, max_full_relay: usize, max_block_relay: usize) {
        let peers = self
            .peer_infos()
            .into_iter()
            .filter(|peer| !peer.inbound && peer.version.is_some())
            .collect::<Vec<_>>();

        let mut block_relay_peers = peers
            .iter()
            .filter(|peer| peer.connection_type == "block-relay-only")
            .cloned()
            .collect::<Vec<_>>();
        if block_relay_peers.len() > max_block_relay {
            // Core uses monotonically increasing node ids as the connection
            // order for this eviction decision.
            block_relay_peers.sort_by_key(|peer| peer.id);
            let youngest = block_relay_peers.pop();
            let next_youngest = block_relay_peers.pop();
            let candidate = match (youngest, next_youngest) {
                (Some(youngest), Some(next_youngest))
                    if youngest.last_block > next_youngest.last_block =>
                {
                    next_youngest
                }
                (Some(youngest), _) => youngest,
                _ => return,
            };
            if now.saturating_sub(candidate.connected_at) >= MINIMUM_EXTRA_PEER_CONNECT_TIME_SECS
                && candidate.inflight_heights().is_empty()
                && self.disconnect_peer(candidate.id)
            {
                debug!(
                    peer_id = candidate.id,
                    "disconnecting extra block-relay-only peer"
                );
            }
        }

        let mut full_relay_peers = peers
            .iter()
            .filter(|peer| !peer.manual && peer.connection_type == "outbound-full")
            .collect::<Vec<_>>();
        if full_relay_peers.len() <= max_full_relay {
            return;
        }

        let mut network_counts = HashMap::<&'static str, usize>::new();
        for peer in &peers {
            if peer.connection_type != "outbound-full" {
                continue;
            }
            *network_counts
                .entry(peer.endpoint.network_name())
                .or_default() += 1;
        }
        let protected = self.chain_sync_states.read();
        full_relay_peers.retain(|peer| {
            !protected.get(&peer.id).is_some_and(|state| state.protect)
                && network_counts
                    .get(peer.endpoint.network_name())
                    .is_some_and(|count| *count > 1)
        });
        full_relay_peers.sort_by(|left, right| {
            left.last_block
                .cmp(&right.last_block)
                .then_with(|| right.id.cmp(&left.id))
        });
        let Some(candidate) = full_relay_peers.first() else {
            return;
        };
        if now.saturating_sub(candidate.connected_at) > MINIMUM_EXTRA_PEER_CONNECT_TIME_SECS
            && candidate.inflight_heights().is_empty()
            && self.disconnect_peer(candidate.id)
        {
            self.try_new_outbound_peer.store(false, Ordering::Release);
            debug!(
                peer_id = candidate.id,
                "disconnecting extra outbound-full peer"
            );
        }
    }

    pub(crate) fn update_peer_presynced_headers(&self, peer_id: usize, height: Option<i64>) {
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.presynced_headers = height.unwrap_or(-1);
        }
    }

    pub(crate) fn update_peer_bip152_highbandwidth_from(&self, peer_id: usize, enabled: bool) {
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.bip152_highbandwidth_from = enabled;
        }
    }

    /// Select a peer for BIP152 high-bandwidth announcements after it has
    /// supplied a valid active-chain block. Core keeps at most three such
    /// peers and prefers retaining an outbound peer when replacing an
    /// inbound one.
    pub(crate) fn select_peer_bip152_highbandwidth(
        &self,
        peer_id: usize,
        block_hash: BlockHash,
    ) -> Option<Option<usize>> {
        let chain = self.chain.read();
        if self.config.blocksonly
            || chain.is_initial_block_download()
            || !chain.is_active_block(&block_hash)
        {
            return None;
        }
        drop(chain);

        let mut peers = self.peers.write();
        let candidate = peers.get(&peer_id)?;
        let candidate_inbound = candidate.inbound;
        if candidate.bip152_highbandwidth_to {
            return None;
        }

        let high_bandwidth = peers
            .values()
            .filter(|peer| peer.bip152_highbandwidth_to)
            .collect::<Vec<_>>();
        let evicted = if high_bandwidth.len() < 3 {
            None
        } else {
            let outbound_count = high_bandwidth.iter().filter(|peer| !peer.inbound).count();
            high_bandwidth
                .iter()
                .filter(|peer| !(candidate_inbound && outbound_count == 1 && !peer.inbound))
                .min_by_key(|peer| (peer.connected_at, peer.id))
                .map(|peer| peer.id)
        };

        if let Some(evicted_id) = evicted {
            if let Some(peer) = peers.get_mut(&evicted_id) {
                peer.bip152_highbandwidth_to = false;
            }
        }
        if let Some(peer) = peers.get_mut(&peer_id) {
            peer.bip152_highbandwidth_to = true;
        }
        Some(evicted)
    }

    pub(crate) fn peer_bip152_highbandwidth_to(&self, peer_id: usize) -> bool {
        self.peers
            .read()
            .get(&peer_id)
            .is_some_and(|peer| peer.bip152_highbandwidth_to)
    }

    pub(crate) fn update_peer_reported_local_address(
        &self,
        peer_id: usize,
        address: Option<SocketAddr>,
    ) {
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.reported_local_address = address;
        }
    }

    pub(crate) fn track_peer_block_request(&self, peer_id: usize, hash: BlockHash) -> bool {
        self.track_peer_block_request_with_limit(peer_id, hash, true)
    }

    /// Reserve one of Core's parallel compact-block reconstruction attempts.
    /// Unlike a full block download, several peers may be asked for the same
    /// block's missing transactions at once. Keep the reservation in the
    /// normal in-flight set so completion, stalling, and RPC peer metadata
    /// continue to observe the same request lifecycle.
    pub(crate) fn track_peer_compact_block_request(&self, peer_id: usize, hash: BlockHash) -> bool {
        let Some(height) = self.chain.read().block_height_by_hash(&hash) else {
            return false;
        };
        let mut peers = self.peers.write();
        let block_requests = peers
            .values()
            .filter(|peer| {
                peer.inflight_blocks
                    .iter()
                    .any(|inflight| inflight.hash == hash)
            })
            .count();
        if block_requests >= MAX_CMPCTBLOCKS_INFLIGHT_PER_BLOCK {
            return false;
        }
        let Some(peer) = peers.get_mut(&peer_id) else {
            return false;
        };
        if peer
            .inflight_blocks
            .iter()
            .any(|inflight| inflight.hash == hash)
            || peer.inflight_blocks.len() >= MAX_BLOCKS_IN_TRANSIT_PER_PEER
        {
            return false;
        }
        peer.inflight_blocks.push(InflightBlock {
            hash,
            height,
            requested_at: Instant::now(),
        });
        true
    }

    /// Record a request made by the `getblockfrompeer` RPC. Core's manual
    /// fetch path intentionally does not apply the automatic download window
    /// limit; callers may queue a range of previously-pruned blocks from one
    /// peer at once.
    pub(crate) fn track_manual_peer_block_request(&self, peer_id: usize, hash: BlockHash) -> bool {
        self.track_peer_block_request_with_limit(peer_id, hash, false)
    }

    fn track_peer_block_request_with_limit(
        &self,
        peer_id: usize,
        hash: BlockHash,
        enforce_limit: bool,
    ) -> bool {
        let Some(height) = self.chain.read().block_height_by_hash(&hash) else {
            return false;
        };
        let mut peers = self.peers.write();
        if peers.values().any(|peer| {
            peer.inflight_blocks
                .iter()
                .any(|inflight| inflight.hash == hash)
        }) {
            return false;
        }
        if let Some(peer) = peers.get_mut(&peer_id) {
            if enforce_limit && peer.inflight_blocks.len() >= MAX_BLOCKS_IN_TRANSIT_PER_PEER {
                return false;
            }
            peer.inflight_blocks.push(InflightBlock {
                hash,
                height,
                requested_at: Instant::now(),
            });
            return true;
        }
        false
    }

    pub(crate) fn peer_inflight_block_count(&self, peer_id: usize) -> usize {
        self.peers
            .read()
            .get(&peer_id)
            .map_or(0, |peer| peer.inflight_blocks.len())
    }

    pub(crate) fn clear_peer_block_requests_for_stored_blocks(&self, peer_id: usize) {
        let chain = self.chain.read();
        let mut cleared = false;
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            let before = peer.inflight_blocks.len();
            peer.inflight_blocks
                .retain(|inflight| !chain.store.contains(&inflight.hash));
            cleared = peer.inflight_blocks.len() != before;
        }
        if cleared {
            self.block_stalling_since.write().remove(&peer_id);
        }
    }

    pub(crate) fn compact_block_request_state(&self, hash: BlockHash) -> (usize, bool) {
        let peers = self.peers.read();
        let mut count = 0;
        let mut outbound_request = false;
        for peer in peers.values() {
            if peer
                .inflight_blocks
                .iter()
                .any(|inflight| inflight.hash == hash)
            {
                count += 1;
                outbound_request |= !peer.inbound;
            }
        }
        (count, outbound_request)
    }

    pub(crate) fn peer_is_inbound(&self, peer_id: usize) -> bool {
        self.peers
            .read()
            .get(&peer_id)
            .is_some_and(|peer| peer.inbound)
    }

    pub(crate) fn peer_has_inflight_block_request(&self, peer_id: usize, hash: BlockHash) -> bool {
        self.peers.read().get(&peer_id).is_some_and(|peer| {
            peer.inflight_blocks
                .iter()
                .any(|inflight| inflight.hash == hash)
        })
    }

    pub(crate) fn block_request_in_flight(&self, hash: BlockHash) -> bool {
        self.peers.read().values().any(|peer| {
            peer.inflight_blocks
                .iter()
                .any(|inflight| inflight.hash == hash)
        })
    }

    /// Return true when the oldest validated block request for a peer has
    /// exceeded Core's block-interval timeout. The timeout is extended for
    /// each other peer that is actively downloading validated blocks so a
    /// saturated local link is not mistaken for a single stalled peer.
    pub(crate) fn peer_block_download_timed_out(&self, peer_id: usize) -> bool {
        let block_interval = Duration::from_secs(self.config.network.params().pow_target_spacing);
        let peers = self.peers.read();
        let Some(peer) = peers.get(&peer_id) else {
            return false;
        };
        let Some(oldest) = peer.inflight_blocks.first() else {
            return false;
        };
        let other_downloading_peers = peers
            .values()
            .filter(|candidate| candidate.id != peer_id && !candidate.inflight_blocks.is_empty())
            .count();
        let timeout = core_block_download_timeout(block_interval, other_downloading_peers);
        oldest.requested_at.elapsed() > timeout
    }

    /// Return the next contiguous header-chain window whose full blocks are
    /// absent locally. This is used after a peer disconnects or times out;
    /// the headers-first state remains durable, so another connected peer can
    /// resume without needing to re-announce the same headers.
    #[cfg(test)]
    pub(crate) fn next_block_download_requests(
        &self,
        limit: usize,
        peer_services: u64,
    ) -> Vec<wire::Inventory> {
        self.next_block_download_schedule_for(None, limit, peer_services)
            .requests
    }

    pub(crate) fn next_block_download_schedule(
        &self,
        peer_id: usize,
        limit: usize,
        peer_services: u64,
    ) -> BlockDownloadSchedule {
        self.next_block_download_schedule_for(Some(peer_id), limit, peer_services)
    }

    pub(crate) fn remember_rejected_block_body(&self, hash: BlockHash) {
        self.rejected_block_bodies.write().insert(hash);
    }

    pub(crate) fn forget_rejected_block_body(&self, hash: &BlockHash) {
        self.rejected_block_bodies.write().remove(hash);
    }

    pub(crate) fn block_body_was_rejected(&self, hash: &BlockHash) -> bool {
        self.rejected_block_bodies.read().contains(hash)
    }

    fn next_block_download_schedule_for(
        &self,
        peer_id: Option<usize>,
        limit: usize,
        peer_services: u64,
    ) -> BlockDownloadSchedule {
        if limit == 0 || peer_services & (wire::NODE_NETWORK | wire::NODE_NETWORK_LIMITED) == 0 {
            return BlockDownloadSchedule {
                requests: Vec::new(),
                staller: None,
            };
        }
        let max_scan = {
            let peer_count = self.peers.read().len();
            limit.saturating_add(
                MAX_BLOCKS_IN_TRANSIT_PER_PEER.saturating_mul(peer_count.saturating_add(1)),
            )
        };
        let limited_peer = peer_services & wire::NODE_NETWORK == 0;
        let peer_best_known = peer_id.and_then(|id| {
            self.peers
                .read()
                .get(&id)
                .and_then(|peer| peer.best_known_block)
        });
        let peer_has_known_tip = peer_best_known.is_some();
        let (candidates, window_end_height) = {
            let chain = self.chain.read();
            let target_hash = if let Some(peer_best_known) = peer_best_known {
                let Some(peer_work) = chain.chain_work_by_hash(&peer_best_known) else {
                    return BlockDownloadSchedule {
                        requests: Vec::new(),
                        staller: None,
                    };
                };
                let tip = chain.tip();
                if peer_work < tip.work || peer_work < chain.minimum_chain_work() {
                    return BlockDownloadSchedule {
                        requests: Vec::new(),
                        staller: None,
                    };
                }
                peer_best_known
            } else {
                // The live peer loop only calls this scheduler after it has
                // observed block availability. Keep the header-tip fallback
                // for callers that use the queue as a durable resume view
                // (and for the staller accounting path before availability
                // has been materialized).
                chain.best_header_tip().hash
            };
            let peer_best_height = peer_best_known
                .and_then(|hash| chain.block_height_by_hash(&hash))
                .unwrap_or_else(|| chain.height());
            let segwit_height = chain.deployment_parameters().buried.segwit;
            let Some(headers) = chain.headers_to_hash_cow(&target_hash) else {
                return BlockDownloadSchedule {
                    requests: Vec::new(),
                    staller: None,
                };
            };
            let last_common_height = headers
                .iter()
                .enumerate()
                .rev()
                .find_map(|(height, header)| {
                    chain
                        .is_active_block(&header.block_hash())
                        .then_some(u32::try_from(height).unwrap_or(u32::MAX))
                })
                .unwrap_or_default();
            let window_end_height = last_common_height.saturating_add(BLOCK_DOWNLOAD_WINDOW);
            let candidates = headers
                .iter()
                .enumerate()
                .skip(1)
                .map(|(height, header)| {
                    (
                        header.block_hash(),
                        u32::try_from(height).unwrap_or(u32::MAX),
                    )
                })
                .filter(|(hash, _)| !chain.store.contains(hash))
                .filter(|(hash, _)| !self.block_body_was_rejected(hash))
                .filter(|(hash, _)| !chain.is_block_pruned(hash))
                .filter(|(_, height)| {
                    !limited_peer
                        || peer_best_height.saturating_sub(*height)
                            < NODE_NETWORK_LIMITED_MIN_BLOCKS.saturating_sub(2)
                })
                .filter(|(_, height)| {
                    peer_id.is_none()
                        || peer_services & wire::NODE_WITNESS != 0
                        || *height < segwit_height
                })
                // Keep the first missing block beyond the window so the
                // caller can distinguish a true staller from a peer that is
                // merely waiting for an in-window block.
                .take(max_scan.saturating_add(1))
                .collect::<Vec<_>>();
            (candidates, window_end_height)
        };
        if candidates.is_empty() {
            return BlockDownloadSchedule {
                requests: Vec::new(),
                staller: None,
            };
        }

        let peers = self.peers.read();
        let peer_has_inflight = peer_id.is_some_and(|id| {
            peers
                .get(&id)
                .is_some_and(|peer| !peer.inflight_blocks.is_empty())
        });
        let mut requests = Vec::with_capacity(limit);
        let mut waiting_for = None;
        let mut window_exceeded = false;
        for (hash, height) in candidates {
            if height > window_end_height {
                window_exceeded = true;
                break;
            }
            let owner = peers.values().find_map(|peer| {
                peer.inflight_blocks
                    .iter()
                    .any(|inflight| inflight.hash == hash)
                    .then_some(peer.id)
            });
            if let Some(owner) = owner {
                if waiting_for.is_none() && peer_id != Some(owner) {
                    waiting_for = Some(owner);
                }
                continue;
            }
            if requests.len() >= limit {
                break;
            }
            requests.push(wire::Inventory {
                kind: if peer_services & wire::NODE_WITNESS != 0 {
                    wire::InventoryType::WitnessBlock
                } else {
                    wire::InventoryType::Block
                },
                hash,
            });
        }

        let staller =
            (!peer_has_inflight && requests.is_empty() && (window_exceeded || !peer_has_known_tip))
                .then_some(waiting_for)
                .flatten();
        BlockDownloadSchedule { requests, staller }
    }

    pub(crate) fn note_block_staller(&self, peer_id: usize) {
        if self.note_block_staller_at(peer_id, Instant::now()) {
            info!("Stall started peer={peer_id}");
        }
    }

    fn note_block_staller_at(&self, peer_id: usize, since: Instant) -> bool {
        if self.peers.read().contains_key(&peer_id) {
            let mut stalling = self.block_stalling_since.write();
            if stalling.contains_key(&peer_id) {
                return false;
            }
            stalling.insert(
                peer_id,
                BlockStallingMoment {
                    wall: since,
                    unix_time: time::unix_time(),
                },
            );
            return true;
        }
        false
    }

    pub(crate) fn take_stalled_block_peer(&self) -> Option<usize> {
        self.take_stalled_block_peer_at(Instant::now())
    }

    fn take_stalled_block_peer_at(&self, now: Instant) -> Option<usize> {
        let timeout = Duration::from_secs(
            self.block_stalling_timeout_secs
                .load(Ordering::Relaxed)
                .max(BLOCK_STALLING_TIMEOUT_DEFAULT.as_secs()),
        );
        let mut stalled = self.block_stalling_since.write();
        let peer_id = stalled.iter().find_map(|(peer_id, since)| {
            let wall_expired = now.duration_since(since.wall) > timeout;
            let mock_expired = time::mock_time() > 0
                && time::unix_time().saturating_sub(since.unix_time) > timeout.as_secs();
            (wall_expired || mock_expired).then_some(*peer_id)
        })?;
        stalled.remove(&peer_id);
        let current = self.block_stalling_timeout_secs.load(Ordering::Relaxed);
        let increased = current
            .saturating_mul(2)
            .min(BLOCK_STALLING_TIMEOUT_MAX.as_secs());
        self.block_stalling_timeout_secs
            .store(increased, Ordering::Relaxed);
        Some(peer_id)
    }

    pub(crate) fn clear_peer_block_request(&self, peer_id: usize, hash: BlockHash) {
        let mut cleared = false;
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            let before = peer.inflight_blocks.len();
            peer.inflight_blocks
                .retain(|inflight| inflight.hash != hash);
            cleared = peer.inflight_blocks.len() != before;
        }
        if cleared {
            self.block_stalling_since.write().remove(&peer_id);
        }
    }

    pub(crate) fn clear_peer_block_requests_for_hash(&self, hash: BlockHash) {
        let mut cleared_peers = Vec::new();
        {
            let mut peers = self.peers.write();
            for (peer_id, peer) in peers.iter_mut() {
                let before = peer.inflight_blocks.len();
                peer.inflight_blocks
                    .retain(|inflight| inflight.hash != hash);
                if peer.inflight_blocks.len() != before {
                    cleared_peers.push(*peer_id);
                }
            }
        }
        let mut stalling = self.block_stalling_since.write();
        for peer_id in cleared_peers {
            stalling.remove(&peer_id);
        }
    }

    pub(crate) fn clear_other_peer_block_requests(&self, peer_id: usize, hash: BlockHash) {
        let mut cleared_peers = Vec::new();
        {
            let mut peers = self.peers.write();
            for (candidate_id, peer) in peers.iter_mut() {
                if *candidate_id == peer_id {
                    continue;
                }
                let before = peer.inflight_blocks.len();
                peer.inflight_blocks
                    .retain(|inflight| inflight.hash != hash);
                if peer.inflight_blocks.len() != before {
                    cleared_peers.push(*candidate_id);
                }
            }
        }
        let mut stalling = self.block_stalling_since.write();
        for candidate_id in cleared_peers {
            stalling.remove(&candidate_id);
        }
    }

    pub(crate) fn record_pong(&self, peer_id: usize, nonce: u64) -> bool {
        let mut peers = self.peers.write();
        let Some(peer) = peers.get_mut(&peer_id) else {
            return false;
        };
        if peer.ping_nonce != Some(nonce) {
            return false;
        }
        peer.ping_nonce = None;
        let sent_at = peer.ping_sent_at.take();
        let sent_mocktime = peer.ping_sent_mocktime.take();
        if sent_at.is_some() || sent_mocktime.is_some() {
            let ping_time = sent_mocktime
                .map(|sent_at| time::unix_time_millis().saturating_sub(sent_at) as f64 / 1_000.0)
                .unwrap_or_else(|| {
                    sent_at
                        .expect("ping timestamp exists")
                        .elapsed()
                        .as_secs_f64()
                });
            peer.ping_time = Some(ping_time);
            peer.min_ping = Some(
                peer.min_ping
                    .map_or(ping_time, |minimum| minimum.min(ping_time)),
            );
        }
        true
    }

    pub(crate) fn peer_ping_nonce(&self, peer_id: usize) -> Option<u64> {
        self.peers
            .read()
            .get(&peer_id)
            .and_then(|peer| peer.ping_nonce)
    }

    pub(crate) fn cancel_peer_ping(&self, peer_id: usize) {
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.ping_nonce = None;
            peer.ping_sent_at = None;
            peer.ping_sent_mocktime = None;
        }
    }

    pub fn network_active(&self) -> bool {
        self.network_active.load(Ordering::Relaxed)
    }

    pub(crate) fn set_listen_address(&self, address: SocketAddr) {
        *self.listen_address.write() = Some(address);
        *self.listen_addresses.write() = vec![address];
    }

    pub(crate) fn set_electrum_address(&self, address: SocketAddr) {
        *self.electrum_address.write() = Some(address);
    }

    pub(crate) fn electrum_address(&self) -> Option<SocketAddr> {
        *self.electrum_address.read()
    }

    pub(crate) fn add_listen_address(&self, address: SocketAddr) {
        let mut addresses = self.listen_addresses.write();
        if !addresses.contains(&address) {
            addresses.push(address);
        }
    }

    pub(crate) fn listen_addresses(&self) -> Vec<SocketAddr> {
        self.listen_addresses.read().clone()
    }

    pub(crate) fn add_mapped_address(&self, address: SocketAddr) {
        let mut addresses = self.mapped_addresses.write();
        if !addresses.contains(&address) {
            addresses.push(address);
        }
    }

    pub(crate) fn mapped_addresses(&self) -> Vec<SocketAddr> {
        self.mapped_addresses.read().clone()
    }

    pub(crate) fn add_listen_network_address(&self, endpoint: NetworkEndpoint) {
        let mut addresses = self.listen_network_addresses.write();
        if !addresses.contains(&endpoint) {
            addresses.push(endpoint);
        }
    }

    pub(crate) fn remove_listen_network_address(&self, endpoint: &NetworkEndpoint) {
        self.listen_network_addresses
            .write()
            .retain(|address| address != endpoint);
    }

    pub(crate) fn listen_network_addresses(&self) -> Vec<NetworkEndpoint> {
        self.listen_network_addresses.read().clone()
    }

    pub(crate) fn listen_address(&self) -> Option<SocketAddr> {
        *self.listen_address.read()
    }

    pub(crate) async fn wait_for_shutdown(&self) {
        loop {
            let notified = self.shutdown.notified();
            tokio::pin!(notified);
            notified.as_mut().enable();
            if self.shutdown_requested.load(Ordering::Acquire) {
                return;
            }
            notified.await;
        }
    }

    pub(crate) fn shutdown_requested(&self) -> bool {
        self.shutdown_requested.load(Ordering::Acquire)
    }

    pub(crate) fn onion_proxy(&self) -> Option<ProxyEndpoint> {
        if !self.config.onion_enabled {
            return None;
        }
        self.config.onion_proxy.clone().or_else(|| {
            self.config.proxy_for_network("onion").or_else(|| {
                self.tor_controller
                    .as_ref()?
                    .socks_proxy()
                    .map(ProxyEndpoint::Tcp)
            })
        })
    }

    pub(crate) fn mark_outbound_tor_success(&self) {
        self.outbound_tor_ok_at_least_once
            .store(true, Ordering::Relaxed);
    }

    pub(crate) fn private_broadcast_proxy(
        &self,
        endpoint: &NetworkEndpoint,
    ) -> Option<ProxyEndpoint> {
        if matches!(endpoint, NetworkEndpoint::Ip(_))
            && self.outbound_tor_ok_at_least_once.load(Ordering::Relaxed)
        {
            self.onion_proxy()
                .or_else(|| self.config.proxy_for_endpoint(endpoint))
        } else {
            self.config.proxy_for_endpoint(endpoint)
        }
    }

    pub(crate) fn record_mining_block(&self, block: &Block) {
        let transaction_weight = block
            .txdata
            .iter()
            .skip(1)
            .map(|transaction| transaction.weight().to_wu())
            .sum::<u64>();
        *self.last_mining_block.write() = Some((
            self.config
                .block_reserved_weight
                .saturating_add(transaction_weight),
            block.txdata.len().saturating_sub(1),
        ));
    }

    pub(crate) fn last_mining_block(&self) -> Option<(u64, usize)> {
        *self.last_mining_block.read()
    }

    pub fn set_network_active(&self, active: bool) {
        info!("SetNetworkActive: {active}");
        self.network_active.store(active, Ordering::Relaxed);
        if !active {
            self.disconnect_all_peers();
        }
    }

    #[cfg(test)]
    pub(crate) fn register_peer(
        &self,
        id: usize,
        address: SocketAddr,
        inbound: bool,
        commands: tokio::sync::mpsc::UnboundedSender<p2p::PeerCommand>,
    ) {
        self.register_peer_with_endpoint(
            id,
            NetworkEndpoint::from_socket(address),
            inbound,
            commands,
            PeerRegistrationOptions {
                local_address: None,
                permissions: PeerPermissions::empty(),
                connection_type: if inbound { "inbound" } else { "outbound-full" },
                manual: false,
                forced_inbound: false,
            },
        );
        // The production registration path deliberately excludes unroutable
        // sockets from AddrMan. Keep this test-only convenience helper's
        // historical behavior for unit tests that inspect the connected
        // peer's address after disconnecting it.
        if !is_core_routable_ip(address.ip())
            && let Some(peer) = self.peers.read().get(&id).cloned()
        {
            self.known_addresses.write().insert(address, peer);
            self.tried_addresses.write().insert(address);
        }
    }

    pub(crate) fn register_peer_with_endpoint(
        &self,
        id: usize,
        endpoint: NetworkEndpoint,
        inbound: bool,
        commands: tokio::sync::mpsc::UnboundedSender<p2p::PeerCommand>,
        options: PeerRegistrationOptions,
    ) {
        let PeerRegistrationOptions {
            local_address,
            permissions,
            connection_type,
            manual,
            forced_inbound,
        } = options;
        let address = endpoint.peer_socket_addr();
        let connected_at = time::unix_time();
        let addr_relay_enabled = {
            #[cfg(test)]
            {
                // Unit-test registration helpers represent an already
                // negotiated peer; production transport registration starts
                // disabled until the VERSION/VERACK handshake completes.
                !inbound && connection_type != "block-relay-only"
            }
            #[cfg(not(test))]
            {
                false
            }
        };
        let peer = PeerInfo {
            id,
            address,
            endpoint: endpoint.clone(),
            local_address,
            reported_local_address: None,
            inbound,
            version: None,
            services: 0,
            user_agent: String::new(),
            start_height: -1,
            relay_transactions: false,
            permissions,
            min_fee_filter: 0,
            transport_protocol_type: "v1",
            session_id: String::new(),
            connection_type,
            manual,
            forced_inbound,
            connected_at,
            last_send: 0,
            last_recv: 0,
            bytes_sent: 0,
            bytes_received: 0,
            preaccounted_received_bytes: 0,
            unread_detection_bytes: 0,
            bytes_sent_per_msg: HashMap::new(),
            bytes_received_per_msg: HashMap::new(),
            last_inv_sequence: 0,
            inv_to_send: 0,
            last_transaction: 0,
            last_block: 0,
            last_block_announcement: 0,
            best_known_block: None,
            last_unknown_block: None,
            last_common_block: None,
            presynced_headers: -1,
            bip152_highbandwidth_to: false,
            bip152_highbandwidth_from: false,
            inflight_blocks: Vec::new(),
            time_offset: 0,
            addr_processed: 0,
            addr_rate_limited: 0,
            // Core enables address relay for outbound peers during the
            // version handshake, and for inbound peers only after their
            // first address-related message. The `addr` permission bypasses
            // processing limits; it does not enroll an inbound peer in relay.
            addr_relay_enabled,
            ping_time: None,
            min_ping: None,
            ping_nonce: None,
            ping_sent_at: None,
            ping_sent_mocktime: None,
            addr_token_bucket: 1.0,
            addr_token_timestamp: time::unix_time_millis(),
        };
        let (active_connections, replaced_connection) = {
            let mut peers = self.peers.write();
            let replaced_connection = peers.insert(id, peer.clone()).is_some();
            (peers.len(), replaced_connection)
        };
        self.peer_commands.write().insert(id, commands);
        self.chain_sync_states
            .write()
            .insert(id, ChainSyncTimeoutState::default());
        if replaced_connection {
            info!(
                "Updated connection peer_id={id} active_connections={active_connections} connection_type={connection_type}"
            );
        } else {
            info!(
                "Added connection peer_id={id} active_connections={active_connections} connection_type={connection_type}"
            );
        }
        let endpoint_is_addrman_candidate = match &endpoint {
            NetworkEndpoint::Ip(address) => is_core_routable_ip(address.ip()),
            NetworkEndpoint::Dns { .. } => false,
            NetworkEndpoint::OnionV2 { .. }
            | NetworkEndpoint::OnionV3 { .. }
            | NetworkEndpoint::I2p { .. }
            | NetworkEndpoint::Cjdns { .. } => true,
        };
        if connection_type != "private-broadcast" && endpoint_is_addrman_candidate {
            if let Some(address) = endpoint.legacy_socket_addr() {
                let mut known = self.known_addresses.write();
                if self.reserve_known_address(&mut known, address) {
                    known.insert(address, peer);
                    self.tried_addresses.write().insert(address);
                    self.network_address_sources
                        .write()
                        .entry(endpoint.clone())
                        .or_insert(endpoint.clone());
                }
            } else {
                let mut known = self.network_addresses.write();
                if self.reserve_network_address(&mut known, &endpoint) {
                    let entry =
                        known
                            .entry(endpoint.clone())
                            .or_insert_with(|| KnownNetworkAddress {
                                endpoint: endpoint.clone(),
                                services: 0,
                                time: connected_at,
                            });
                    entry.time = entry.time.max(connected_at);
                    self.network_tried_addresses.write().insert(endpoint);
                    self.network_address_sources
                        .write()
                        .entry(peer.endpoint.clone())
                        .or_insert(peer.endpoint.clone());
                }
            }
        }
        self.maybe_check_addrman();
    }

    pub fn update_peer_version(
        &self,
        id: usize,
        version: i32,
        services: u64,
        user_agent: &str,
        start_height: i32,
        relay_transactions: bool,
    ) {
        if let Some(peer) = self.peers.write().get_mut(&id) {
            let user_agent = sanitize_peer_user_agent(user_agent);
            let relay_transactions = relay_transactions
                && !matches!(
                    peer.connection_type,
                    "block-relay-only" | "feeler" | "private-broadcast"
                );
            peer.version = Some(version);
            peer.services = services;
            peer.user_agent.clone_from(&user_agent);
            peer.start_height = start_height;
            peer.relay_transactions = relay_transactions;
            if peer.connection_type != "private-broadcast" {
                if let Some(address) = peer.endpoint.legacy_socket_addr() {
                    if let Some(known) = self.known_addresses.write().get_mut(&address) {
                        known.version = Some(version);
                        known.services = services;
                        known.user_agent = user_agent;
                        known.start_height = start_height;
                        known.relay_transactions = relay_transactions;
                    }
                } else if let Some(known) = self.network_addresses.write().get_mut(&peer.endpoint) {
                    known.services |= services;
                }
            }
        }
    }

    pub(crate) fn update_peer_relay_transactions(&self, id: usize, relay_transactions: bool) {
        if let Some(peer) = self.peers.write().get_mut(&id) {
            let relay_transactions = relay_transactions
                && !matches!(
                    peer.connection_type,
                    "block-relay-only" | "feeler" | "private-broadcast"
                );
            peer.relay_transactions = relay_transactions;
            if peer.connection_type != "private-broadcast"
                && let Some(address) = peer.endpoint.legacy_socket_addr()
                && let Some(known) = self.known_addresses.write().get_mut(&address)
            {
                known.relay_transactions = relay_transactions;
            }
        }
    }

    pub fn update_peer_fee_filter(&self, id: usize, min_fee_filter: i64) {
        let min_fee_filter = min_fee_filter.max(0);
        if let Some(peer) = self.peers.write().get_mut(&id) {
            peer.min_fee_filter = min_fee_filter;
            if peer.connection_type != "private-broadcast"
                && let Some(address) = peer.endpoint.legacy_socket_addr()
                && let Some(known) = self.known_addresses.write().get_mut(&address)
            {
                known.min_fee_filter = min_fee_filter;
            }
        }
    }

    pub(crate) fn update_peer_time_offset(&self, id: usize, time_offset: i64) {
        let outbound = if let Some(peer) = self.peers.write().get_mut(&id) {
            peer.time_offset = time_offset;
            !peer.inbound && peer.version.is_some()
        } else {
            false
        };
        if outbound {
            let mut samples = self.time_offset_samples.write();
            if samples.len() >= MAX_TIME_OFFSET_SAMPLES {
                samples.pop_front();
            }
            samples.push_back(time_offset);
        }
        self.refresh_clock_warning();
    }

    fn refresh_clock_warning(&self) {
        let mut offsets = self
            .time_offset_samples
            .read()
            .iter()
            .copied()
            .collect::<Vec<_>>();
        if offsets.len() < 5 {
            self.unset_warning(NodeWarningKind::ClockOutOfSync);
            return;
        }
        offsets.sort_unstable();
        let median = offsets[offsets.len() / 2];
        if median.unsigned_abs() > CLOCK_OUT_OF_SYNC_THRESHOLD_SECS {
            self.set_warning(
                NodeWarningKind::ClockOutOfSync,
                "Your computer's date and time appear to be more than 10 minutes out of sync with the network, this may lead to consensus failure. After you've confirmed your computer's clock, this message should no longer appear when you restart your node. Without a restart, it should stop showing automatically after you've connected to a sufficient number of new outbound peers, which may take some time. You can inspect the timeoffset field of the getpeerinfo and getnetworkinfo RPC methods to get more info.".to_owned(),
            );
        } else {
            self.unset_warning(NodeWarningKind::ClockOutOfSync);
        }
    }

    fn refresh_versionbits_warning(&self) {
        let unknown_bit = {
            if self
                .warnings
                .read()
                .iter()
                .any(|warning| warning.kind == NodeWarningKind::UnknownRulesActive)
            {
                return;
            }
            let chain = self.chain.read();
            if chain.is_initial_block_download() {
                return;
            }
            let headers = chain.active_headers();
            let deployment_parameters = chain.deployment_parameters();
            let period = usize::try_from(deployment_parameters.bip9[0].period)
                .unwrap_or(1)
                .max(1);
            let first_scan = !self
                .versionbits_warning_scanned
                .swap(true, Ordering::AcqRel);
            if first_scan {
                validation::unknown_versionbits_active_with_params(headers, &deployment_parameters)
            } else if headers.len() % period == 0 {
                validation::unknown_versionbits_active_at_boundary_with_params(
                    headers,
                    &deployment_parameters,
                )
            } else {
                None
            }
        };
        if let Some(bit) = unknown_bit {
            self.set_warning(
                NodeWarningKind::UnknownRulesActive,
                format!("Unknown new rules activated (versionbit {bit})"),
            );
        }
    }

    pub(crate) fn set_warning(&self, kind: NodeWarningKind, message: String) {
        let inserted = {
            let mut warnings = self.warnings.write();
            if warnings.iter().any(|warning| warning.kind == kind) {
                false
            } else {
                warnings.push(NodeWarning {
                    kind,
                    message: message.clone(),
                });
                true
            }
        };
        if inserted {
            run_alert_notify_command(self.config.alert_notify.as_deref(), &message);
        }
    }

    pub(crate) fn refresh_large_work_invalid_chain_warning(&self) {
        if self.chain.read().has_large_work_invalid_chain() {
            self.set_warning(
                NodeWarningKind::LargeWorkInvalidChain,
                LARGE_WORK_INVALID_CHAIN_WARNING.to_owned(),
            );
        }
    }

    pub(crate) fn unset_warning(&self, kind: NodeWarningKind) {
        self.warnings.write().retain(|warning| warning.kind != kind);
    }

    pub(crate) fn warning_messages(&self) -> Vec<String> {
        let mut warnings = self
            .warnings
            .read()
            .iter()
            .map(|warning| (warning.kind, warning.message.clone()))
            .collect::<Vec<_>>();
        warnings.sort_unstable_by_key(|(kind, _)| *kind);
        warnings.into_iter().map(|(_, message)| message).collect()
    }

    pub(crate) fn enable_peer_address_relay(&self, id: usize) {
        if let Some(peer) = self.peers.write().get_mut(&id)
            && peer.inbound
        {
            peer.addr_relay_enabled = true;
        }
    }

    pub(crate) fn peer_address_relay_enabled(&self, id: usize) -> bool {
        self.peers
            .read()
            .get(&id)
            .is_some_and(|peer| peer.addr_relay_enabled)
    }

    pub(crate) fn setup_outbound_address_relay(&self, id: usize) {
        if let Some(peer) = self.peers.write().get_mut(&id)
            && !peer.inbound
            && peer.connection_type != "block-relay-only"
        {
            peer.addr_relay_enabled = true;
        }
    }

    pub(crate) fn allow_peer_address(&self, id: usize) -> bool {
        let mut peers = self.peers.write();
        let Some(peer) = peers.get_mut(&id) else {
            return false;
        };
        if peer.permissions.contains(PeerPermissions::ADDR) {
            peer.addr_processed = peer.addr_processed.saturating_add(1);
            return true;
        }
        let now = time::unix_time_millis();
        if peer.addr_token_bucket < MAX_ADDR_PROCESSING_TOKEN_BUCKET {
            let elapsed = now.saturating_sub(peer.addr_token_timestamp) as f64 / 1_000.0;
            peer.addr_token_bucket = (peer.addr_token_bucket + elapsed * MAX_ADDR_RATE_PER_SECOND)
                .min(MAX_ADDR_PROCESSING_TOKEN_BUCKET);
        }
        peer.addr_token_timestamp = now;
        if peer.addr_token_bucket < 1.0 {
            peer.addr_rate_limited = peer.addr_rate_limited.saturating_add(1);
            return false;
        }
        peer.addr_token_bucket -= 1.0;
        peer.addr_processed = peer.addr_processed.saturating_add(1);
        if peer.inbound {
            peer.addr_relay_enabled = true;
        }
        true
    }

    pub(crate) fn grant_peer_address_tokens(&self, id: usize, count: usize) {
        if let Some(peer) = self.peers.write().get_mut(&id) {
            peer.addr_token_bucket += count as f64;
        }
    }

    pub(crate) fn relay_peer_addresses(
        &self,
        origin_peer_id: usize,
        addresses: Vec<(NetworkEndpoint, u64, u64)>,
    ) {
        if addresses.is_empty() {
            return;
        }
        let now = time::unix_time();
        let peers = self.peers.read();
        let mut selected = HashMap::<usize, Vec<(NetworkEndpoint, u64, u64)>>::new();
        for address in addresses {
            let address_hash = addrman_hash(&self.addrman_key, |input| {
                input.extend_from_slice(&addrman_endpoint_key(&address.0));
            });
            let rotation = now
                .saturating_add(address_hash)
                .saturating_div(ADDR_RELAY_DESTINATION_ROTATION);
            let mut candidates = peers
                .values()
                .filter(|peer| {
                    peer.id != origin_peer_id && peer.version.is_some() && peer.addr_relay_enabled
                })
                .map(|peer| {
                    let score = addrman_hash(&self.addrman_key, |input| {
                        input.extend_from_slice(&address_hash.to_le_bytes());
                        input.extend_from_slice(&rotation.to_le_bytes());
                        input.extend_from_slice(
                            &u64::try_from(peer.id)
                                .expect("peer id fits in the address relay hash")
                                .to_le_bytes(),
                        );
                    });
                    (peer.id, score)
                })
                .collect::<Vec<_>>();
            candidates.sort_unstable_by(|left, right| {
                right.1.cmp(&left.1).then_with(|| left.0.cmp(&right.0))
            });
            for peer_id in candidates
                .into_iter()
                .take(ADDR_RELAY_DESTINATIONS)
                .map(|candidate| candidate.0)
            {
                selected.entry(peer_id).or_default().push(address.clone());
            }
        }
        drop(peers);
        let commands = self.peer_commands.read();
        for (peer_id, addresses) in selected {
            if let Some(sender) = commands.get(&peer_id) {
                let _ = sender.send(p2p::PeerCommand::RelayAddresses { addresses });
            }
        }
    }

    pub(crate) fn set_peer_transport_protocol(&self, id: usize, transport_v2: bool) {
        if let Some(peer) = self.peers.write().get_mut(&id) {
            peer.transport_protocol_type = if transport_v2 { "v2" } else { "v1" };
        }
    }

    pub(crate) fn peer_transport_stats(&self, id: usize) -> Option<PeerTransportStats> {
        self.peers.read().get(&id).map(|peer| PeerTransportStats {
            last_send: peer.last_send,
            last_recv: peer.last_recv,
            bytes_sent: peer.bytes_sent,
            bytes_received: peer.bytes_received,
            preaccounted_received_bytes: peer.preaccounted_received_bytes,
            unread_detection_bytes: peer.unread_detection_bytes,
        })
    }

    pub(crate) fn restore_peer_transport_stats(&self, id: usize, stats: PeerTransportStats) {
        if let Some(peer) = self.peers.write().get_mut(&id) {
            peer.last_send = stats.last_send;
            peer.last_recv = stats.last_recv;
            peer.bytes_sent = stats.bytes_sent;
            peer.bytes_received = stats.bytes_received;
            peer.preaccounted_received_bytes = stats.preaccounted_received_bytes;
            peer.unread_detection_bytes = stats.unread_detection_bytes;
        }
    }

    pub(crate) fn set_peer_transport_detecting(&self, id: usize) {
        if let Some(peer) = self.peers.write().get_mut(&id) {
            peer.transport_protocol_type = "detecting";
        }
    }

    pub(crate) fn set_peer_session_id(&self, id: usize, session_id: Option<String>) {
        if let Some(peer) = self.peers.write().get_mut(&id) {
            peer.session_id = session_id.unwrap_or_default();
        }
    }

    pub(crate) fn set_peer_connection_type(&self, id: usize, connection_type: &'static str) {
        if let Some(peer) = self.peers.write().get_mut(&id) {
            peer.connection_type = connection_type;
            if peer.inbound || connection_type == "block-relay-only" {
                peer.addr_relay_enabled = false;
            }
        }
    }

    pub(crate) fn permissions_for_peer(
        &self,
        address: SocketAddr,
        inbound: bool,
    ) -> PeerPermissions {
        self.config.peer_permissions(address.ip(), inbound)
    }

    pub fn unregister_peer(&self, id: usize) {
        let endpoint = {
            let mut peers = self.peers.write();
            let removed = peers.remove(&id);
            if removed.as_ref().is_some_and(|peer| {
                peer.version.is_some() && is_non_reduced_outbound(peer, peer.services)
            }) {
                self.non_reduced_outbound_count
                    .fetch_sub(1, Ordering::AcqRel);
            }
            removed.map(|peer| peer.endpoint)
        };
        let active_connections = self.peers.read().len();
        debug!("Removed connection peer_id={id} active_connections={active_connections}");
        self.peer_commands.write().remove(&id);
        let replacement = self.release_headers_sync_peer(id);
        self.headers_sync_active.lock().remove(&id);
        self.inv_triggered_headers_sync.lock().remove(&id);
        self.block_stalling_since.write().remove(&id);
        self.chain_sync_states.write().remove(&id);
        if let Some(endpoint) = endpoint {
            if let Some(address) = endpoint.legacy_socket_addr()
                && let Some(known) = self.known_addresses.write().get_mut(&address)
                && known.id == id
            {
                known.id = UNCONNECTED_PEER_ID;
                known.inbound = false;
                known.local_address = None;
                known.ping_nonce = None;
                known.ping_sent_at = None;
                known.ping_sent_mocktime = None;
            }
        }
        if let Some(sender) = replacement {
            let _ = sender.send(p2p::PeerCommand::RequestHeaders);
        }
        self.orphans.lock().erase_for_peer(id);
        self.maybe_check_addrman();
        self.refresh_clock_warning();
    }

    pub fn peer_infos(&self) -> Vec<PeerInfo> {
        let mut peers = self.peers.read().values().cloned().collect::<Vec<_>>();
        // Core exposes getpeerinfo in peer-id order.  Keeping the ordering
        // deterministic also makes the first/second peer distinction used by
        // compatibility clients meaningful when connections are concurrent.
        peers.sort_by_key(|peer| peer.id);
        peers
    }

    /// Select an inbound peer using Core's main eviction protections.
    pub(crate) fn select_inbound_peer_to_evict(&self, force: bool) -> Option<usize> {
        let candidates = self
            .peer_infos()
            .into_iter()
            .filter(|peer| peer.inbound && !peer.permissions.contains(PeerPermissions::NO_BAN))
            .collect::<Vec<_>>();
        if candidates.is_empty() {
            return None;
        }

        let mut protected = HashSet::new();
        // Core protects four peers from each keyed network group before
        // applying the other eviction criteria.
        let mut by_netgroup = HashMap::<Vec<u8>, Vec<&PeerInfo>>::new();
        for peer in &candidates {
            by_netgroup
                .entry(self.peer_netgroup_key(&peer.endpoint))
                .or_default()
                .push(peer);
        }
        for peers in by_netgroup.values_mut() {
            peers.sort_by_key(|peer| (peer.connected_at, peer.id));
            protected.extend(peers.iter().take(4).map(|peer| peer.id));
        }
        let mut by_ping = candidates
            .iter()
            .filter(|peer| !protected.contains(&peer.id))
            .cloned()
            .collect::<Vec<_>>();
        by_ping.sort_by(|left, right| {
            left.min_ping
                .unwrap_or(f64::INFINITY)
                .total_cmp(&right.min_ping.unwrap_or(f64::INFINITY))
                .then_with(|| left.id.cmp(&right.id))
        });
        protected.extend(by_ping.into_iter().take(8).map(|peer| peer.id));

        let mut by_transaction = candidates
            .iter()
            .filter(|peer| peer.last_transaction != 0 && !protected.contains(&peer.id))
            .cloned()
            .collect::<Vec<_>>();
        by_transaction.sort_by(|left, right| {
            right
                .last_transaction
                .cmp(&left.last_transaction)
                .then_with(|| left.id.cmp(&right.id))
        });
        protected.extend(by_transaction.into_iter().take(4).map(|peer| peer.id));

        let mut by_block = candidates
            .iter()
            .filter(|peer| peer.last_block != 0 && !protected.contains(&peer.id))
            .cloned()
            .collect::<Vec<_>>();
        by_block.sort_by(|left, right| {
            right
                .last_block
                .cmp(&left.last_block)
                .then_with(|| left.id.cmp(&right.id))
        });
        protected.extend(by_block.into_iter().take(4).map(|peer| peer.id));

        let mut evictable = candidates
            .into_iter()
            .filter(|peer| !protected.contains(&peer.id))
            .collect::<Vec<_>>();
        if evictable.is_empty() {
            if !force {
                return None;
            }
            // Core uses a random candidate as the force-inbound fallback.
            // The connection id is a stable fallback for this deterministic
            // peer manager.
            evictable = self
                .peer_infos()
                .into_iter()
                .filter(|peer| peer.inbound && !peer.permissions.contains(PeerPermissions::NO_BAN))
                .collect();
        }
        evictable
            .into_iter()
            .min_by_key(|peer| (peer.connected_at, peer.id))
            .map(|peer| peer.id)
    }

    /// Return the median clock offset reported by connected outbound peers.
    ///
    /// Bitcoin Core uses only outbound handshake samples for the node-wide
    /// network time offset; inbound peers must not be able to influence it.
    pub fn median_outbound_time_offset(&self) -> i64 {
        let mut offsets = self
            .peers
            .read()
            .values()
            .filter(|peer| !peer.inbound && peer.version.is_some())
            .map(|peer| peer.time_offset)
            .collect::<Vec<_>>();
        if offsets.is_empty() {
            return 0;
        }
        offsets.sort_unstable();
        offsets[offsets.len() / 2]
    }

    pub fn known_addresses(&self) -> Vec<PeerInfo> {
        self.known_addresses.read().values().cloned().collect()
    }

    pub fn known_network_addresses(&self) -> Vec<KnownNetworkAddress> {
        let mut addresses = self
            .known_addresses
            .read()
            .values()
            .map(|peer| KnownNetworkAddress {
                endpoint: peer.endpoint.clone(),
                services: peer.services,
                time: peer.connected_at,
            })
            .collect::<Vec<_>>();
        addresses.extend(self.network_addresses.read().values().cloned());
        addresses
    }

    /// Return the privacy-preserving address snapshot used for a getaddr
    /// response. Core keeps a separate randomized snapshot for each network
    /// key (network plus local bind) for roughly a day so repeated requests
    /// cannot reveal address-manager churn or correlate listeners.
    pub(crate) fn cached_addr_response(
        &self,
        key: AddrResponseCacheKey,
        max_addresses: usize,
        max_pct: usize,
    ) -> Vec<KnownNetworkAddress> {
        let now = time::unix_time();
        let mut caches = self.addr_response_caches.lock();
        let cache = caches.entry(key).or_insert_with(|| CachedAddrResponse {
            addresses: Vec::new(),
            expiration: 0,
        });
        if cache.expiration < now {
            let mut addresses = self.known_network_addresses();
            let limit = if max_pct == 0 {
                addresses.len()
            } else {
                addresses.len().saturating_mul(max_pct).saturating_div(100)
            }
            .min(max_addresses);
            addresses.shuffle(&mut rand::rng());
            addresses.truncate(limit);
            cache.addresses = addresses;
            cache.expiration = now
                .saturating_add(ADDR_RESPONSE_CACHE_MIN_LIFETIME)
                .saturating_add(rand::random_range(0..ADDR_RESPONSE_CACHE_RANDOM_LIFETIME));
        }
        cache.addresses.clone()
    }

    /// Return the peer or discovery endpoint that introduced an address to
    /// the address manager. Older persisted entries have no source metadata,
    /// so the address itself is the Core-compatible fallback.
    pub(crate) fn network_address_source(&self, endpoint: &NetworkEndpoint) -> NetworkEndpoint {
        self.network_address_sources
            .read()
            .get(endpoint)
            .cloned()
            .unwrap_or_else(|| endpoint.clone())
    }

    fn remember_network_address_source(
        &self,
        endpoint: &NetworkEndpoint,
        source: &NetworkEndpoint,
    ) {
        self.network_address_sources
            .write()
            .entry(endpoint.clone())
            .or_insert_with(|| source.clone());
    }

    pub(crate) fn is_address_tried(&self, address: SocketAddr) -> bool {
        self.tried_addresses.read().contains(&address)
    }

    pub(crate) fn is_network_address_tried(&self, endpoint: &NetworkEndpoint) -> bool {
        match endpoint {
            NetworkEndpoint::Ip(address) => self.is_address_tried(*address),
            NetworkEndpoint::Dns { .. } => false,
            NetworkEndpoint::OnionV2 { .. }
            | NetworkEndpoint::OnionV3 { .. }
            | NetworkEndpoint::I2p { .. } => self.network_tried_addresses.read().contains(endpoint),
            NetworkEndpoint::Cjdns { .. } => {
                self.network_tried_addresses.read().contains(endpoint)
                    || endpoint
                        .socket_addr()
                        .is_some_and(|address| self.is_address_tried(address))
            }
        }
    }

    pub(crate) fn promote_network_address_to_tried(&self, endpoint: &NetworkEndpoint) -> bool {
        let target_slot = addrman_tried_slot(&self.addrman_key, endpoint);
        let occupied = match endpoint.legacy_socket_addr() {
            Some(address) => {
                let tried = self.tried_addresses.read();
                self.known_addresses.read().keys().any(|candidate| {
                    *candidate != address
                        && tried.contains(candidate)
                        && addrman_tried_slot(
                            &self.addrman_key,
                            &NetworkEndpoint::from_socket(*candidate),
                        ) == target_slot
                })
            }
            None => {
                let tried = self.network_tried_addresses.read();
                self.network_addresses.read().keys().any(|candidate| {
                    candidate != endpoint
                        && tried.contains(candidate)
                        && addrman_tried_slot(&self.addrman_key, candidate) == target_slot
                })
            }
        };
        if occupied {
            return false;
        }
        match endpoint.legacy_socket_addr() {
            Some(address) => {
                if !self.known_addresses.read().contains_key(&address) {
                    return false;
                }
                self.tried_addresses.write().insert(address);
            }
            None => {
                if !self.network_addresses.read().contains_key(endpoint) {
                    return false;
                }
                self.network_tried_addresses
                    .write()
                    .insert(endpoint.clone());
            }
        }
        self.maybe_check_addrman();
        true
    }

    pub(crate) fn add_network_address(&self, endpoint: NetworkEndpoint, tried: bool) -> bool {
        if matches!(endpoint, NetworkEndpoint::Dns { .. }) {
            return false;
        }
        if !self.config.allows_network_endpoint(&endpoint) {
            return false;
        }
        let added = if let Some(address) = endpoint.legacy_socket_addr() {
            self.add_peer_address(address, false)
        } else {
            let now = unix_time_seconds();
            let mut known = self.network_addresses.write();
            if known.contains_key(&endpoint) || !self.reserve_network_address(&mut known, &endpoint)
            {
                false
            } else {
                known.insert(
                    endpoint.clone(),
                    KnownNetworkAddress {
                        endpoint: endpoint.clone(),
                        services: crate::wire::NODE_NETWORK | crate::wire::NODE_WITNESS,
                        time: now,
                    },
                );
                drop(known);
                self.remember_network_address_source(&endpoint, &endpoint);
                self.maybe_check_addrman();
                true
            }
        };
        if !added {
            return false;
        }
        !tried || self.promote_network_address_to_tried(&endpoint)
    }

    pub(crate) fn remember_network_address(
        &self,
        endpoint: NetworkEndpoint,
        services: u64,
        time: u64,
    ) -> bool {
        let source = endpoint.clone();
        self.remember_network_address_from(endpoint, services, time, source)
    }

    pub(crate) fn remember_network_address_from(
        &self,
        endpoint: NetworkEndpoint,
        services: u64,
        time: u64,
        source: NetworkEndpoint,
    ) -> bool {
        if !self.config.allows_network_endpoint(&endpoint) {
            return false;
        }
        if let Some(address) = endpoint.legacy_socket_addr() {
            let is_new = self.remember_address(address, services, time);
            if is_new || self.known_addresses.read().contains_key(&address) {
                self.remember_network_address_source(&endpoint, &source);
            }
            return is_new;
        }
        let mut known = self.network_addresses.write();
        if !self.reserve_network_address(&mut known, &endpoint) {
            return false;
        }
        let is_new = !known.contains_key(&endpoint);
        let entry = known
            .entry(endpoint.clone())
            .or_insert_with(|| KnownNetworkAddress {
                endpoint: endpoint.clone(),
                services,
                time,
            });
        entry.services |= services;
        entry.time = entry.time.max(time);
        drop(known);
        self.remember_network_address_source(&endpoint, &source);
        self.maybe_check_addrman();
        is_new
    }

    pub(crate) fn add_peer_address(&self, address: SocketAddr, tried: bool) -> bool {
        let now = unix_time_seconds();
        let mut known = self.known_addresses.write();
        if known.contains_key(&address) {
            return false;
        }
        if !self.reserve_known_address(&mut known, address) {
            return false;
        }
        known.insert(
            address,
            PeerInfo {
                id: UNCONNECTED_PEER_ID,
                address,
                endpoint: NetworkEndpoint::from_socket(address),
                local_address: None,
                reported_local_address: None,
                inbound: false,
                version: None,
                services: crate::wire::NODE_NETWORK | crate::wire::NODE_WITNESS,
                user_agent: String::new(),
                start_height: 0,
                relay_transactions: true,
                permissions: PeerPermissions::empty(),
                min_fee_filter: 0,
                transport_protocol_type: "v1",
                session_id: String::new(),
                connection_type: "outbound-full",
                manual: false,
                forced_inbound: false,
                connected_at: now,
                last_send: now,
                last_recv: now,
                bytes_sent: 0,
                bytes_received: 0,
                preaccounted_received_bytes: 0,
                unread_detection_bytes: 0,
                bytes_sent_per_msg: HashMap::new(),
                bytes_received_per_msg: HashMap::new(),
                last_inv_sequence: 0,
                inv_to_send: 0,
                last_transaction: 0,
                last_block: 0,
                last_block_announcement: 0,
                best_known_block: None,
                last_unknown_block: None,
                last_common_block: None,
                presynced_headers: -1,
                bip152_highbandwidth_to: false,
                bip152_highbandwidth_from: false,
                inflight_blocks: Vec::new(),
                time_offset: 0,
                addr_processed: 0,
                addr_rate_limited: 0,
                addr_relay_enabled: false,
                ping_time: None,
                min_ping: None,
                ping_nonce: None,
                ping_sent_at: None,
                ping_sent_mocktime: None,
                addr_token_bucket: 1.0,
                addr_token_timestamp: time::unix_time_millis(),
            },
        );
        drop(known);
        let endpoint = NetworkEndpoint::from_socket(address);
        self.remember_network_address_source(&endpoint, &endpoint);
        if tried {
            self.tried_addresses.write().insert(address);
            if matches!(endpoint, NetworkEndpoint::Cjdns { .. }) {
                self.network_tried_addresses.write().insert(endpoint);
            }
        }
        self.maybe_check_addrman();
        true
    }

    pub(crate) fn remember_address(&self, address: SocketAddr, services: u64, time: u64) -> bool {
        let mut known = self.known_addresses.write();
        if !self.reserve_known_address(&mut known, address) {
            return false;
        }
        let is_new = !known.contains_key(&address);
        let endpoint = NetworkEndpoint::from_socket(address);
        let entry = known.entry(address).or_insert_with(|| PeerInfo {
            id: UNCONNECTED_PEER_ID,
            address,
            endpoint,
            local_address: None,
            reported_local_address: None,
            inbound: false,
            version: None,
            services,
            user_agent: String::new(),
            start_height: 0,
            relay_transactions: true,
            permissions: PeerPermissions::empty(),
            min_fee_filter: 0,
            transport_protocol_type: "v1",
            session_id: String::new(),
            connection_type: "outbound-full",
            manual: false,
            forced_inbound: false,
            connected_at: time,
            last_send: time,
            last_recv: time,
            bytes_sent: 0,
            bytes_received: 0,
            preaccounted_received_bytes: 0,
            unread_detection_bytes: 0,
            bytes_sent_per_msg: HashMap::new(),
            bytes_received_per_msg: HashMap::new(),
            last_inv_sequence: 0,
            inv_to_send: 0,
            last_transaction: 0,
            last_block: 0,
            last_block_announcement: 0,
            best_known_block: None,
            last_unknown_block: None,
            last_common_block: None,
            presynced_headers: -1,
            bip152_highbandwidth_to: false,
            bip152_highbandwidth_from: false,
            inflight_blocks: Vec::new(),
            time_offset: 0,
            addr_processed: 0,
            addr_rate_limited: 0,
            addr_relay_enabled: false,
            ping_time: None,
            min_ping: None,
            ping_nonce: None,
            ping_sent_at: None,
            ping_sent_mocktime: None,
            addr_token_bucket: 1.0,
            addr_token_timestamp: time::unix_time_millis(),
        });
        if entry.id == UNCONNECTED_PEER_ID {
            entry.services |= services;
            entry.connected_at = entry.connected_at.max(time);
            entry.last_send = entry.last_send.max(time);
            entry.last_recv = entry.last_recv.max(time);
        }
        drop(known);
        self.maybe_check_addrman();
        is_new
    }

    fn reserve_known_address(
        &self,
        known: &mut HashMap<SocketAddr, PeerInfo>,
        address: SocketAddr,
    ) -> bool {
        if known.contains_key(&address) || known.len() < MAX_KNOWN_ADDRESSES {
            return true;
        }
        let tried = self.tried_addresses.read();
        let eviction = known
            .iter()
            .filter(|(candidate, peer)| {
                peer.id == UNCONNECTED_PEER_ID
                    && !tried.contains(*candidate)
                    && **candidate != address
            })
            .min_by_key(|(_, peer)| peer.connected_at)
            .map(|(candidate, _)| *candidate);
        drop(tried);
        if let Some(eviction) = eviction {
            known.remove(&eviction);
            self.network_address_sources
                .write()
                .remove(&NetworkEndpoint::from_socket(eviction));
            true
        } else {
            false
        }
    }

    fn reserve_network_address(
        &self,
        known: &mut HashMap<NetworkEndpoint, KnownNetworkAddress>,
        endpoint: &NetworkEndpoint,
    ) -> bool {
        if known.contains_key(endpoint) || known.len() < MAX_KNOWN_ADDRESSES {
            return true;
        }
        let tried = self.network_tried_addresses.read();
        let eviction = known
            .iter()
            .filter(|(candidate, _)| !tried.contains(*candidate) && *candidate != endpoint)
            .min_by_key(|(_, entry)| entry.time)
            .map(|(candidate, _)| candidate.clone());
        drop(tried);
        if let Some(eviction) = eviction {
            known.remove(&eviction);
            self.network_address_sources.write().remove(&eviction);
            true
        } else {
            false
        }
    }

    pub fn add_node(&self, address: SocketAddr) -> bool {
        self.add_node_with_transport(address, None)
    }

    pub(crate) fn add_node_with_transport(
        &self,
        address: SocketAddr,
        transport_v2: Option<bool>,
    ) -> bool {
        self.add_node_endpoint_with_transport(
            NetworkEndpoint::from_socket(address),
            address.to_string(),
            transport_v2,
        )
    }

    pub(crate) fn add_node_endpoint_with_transport(
        &self,
        endpoint: NetworkEndpoint,
        display_name: String,
        transport_v2: Option<bool>,
    ) -> bool {
        let inserted = match self.added_nodes.write().entry(endpoint.clone()) {
            std::collections::hash_map::Entry::Occupied(_) => false,
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(transport_v2);
                true
            }
        };
        if inserted {
            self.added_node_names
                .write()
                .insert(endpoint.clone(), display_name);
            if let Some(sender) = self.peer_manager_requests.read().as_ref() {
                let _ = sender.send(p2p::PeerManagerRequest::Add(endpoint, transport_v2));
            }
        }
        inserted
    }

    pub(crate) fn request_one_try_endpoint_with_connection_type(
        &self,
        endpoint: NetworkEndpoint,
        transport_v2: Option<bool>,
        connection_type: &'static str,
    ) {
        self.request_one_try_endpoint_with_connection_type_mode(
            endpoint,
            transport_v2,
            connection_type,
            false,
        );
    }

    pub(crate) async fn request_one_try_endpoint_with_connection_type_and_wait(
        &self,
        endpoint: NetworkEndpoint,
        transport_v2: Option<bool>,
        connection_type: &'static str,
    ) {
        let Some(sender) = self.peer_manager_requests.read().as_ref().cloned() else {
            return;
        };
        let (completion_sender, completion_receiver) = oneshot::channel();
        if sender
            .send(p2p::PeerManagerRequest::OneTry(
                endpoint,
                transport_v2,
                connection_type,
                false,
                Some(completion_sender),
            ))
            .is_ok()
        {
            let _ = completion_receiver.await;
        }
    }

    pub(crate) fn request_add_connection_with_type(
        &self,
        address: SocketAddr,
        transport_v2: bool,
        connection_type: &'static str,
    ) {
        self.request_one_try_endpoint_with_connection_type_mode(
            NetworkEndpoint::from_socket(address),
            Some(transport_v2),
            connection_type,
            true,
        );
    }

    fn request_one_try_endpoint_with_connection_type_mode(
        &self,
        endpoint: NetworkEndpoint,
        transport_v2: Option<bool>,
        connection_type: &'static str,
        addconnection: bool,
    ) {
        if let Some(sender) = self.peer_manager_requests.read().as_ref() {
            let _ = sender.send(p2p::PeerManagerRequest::OneTry(
                endpoint,
                transport_v2,
                connection_type,
                addconnection,
                None,
            ));
        }
    }

    pub fn remove_node(&self, address: &SocketAddr) -> bool {
        self.remove_node_endpoint(&NetworkEndpoint::from_socket(*address))
    }

    pub(crate) fn remove_node_endpoint(&self, endpoint: &NetworkEndpoint) -> bool {
        let removed = self.added_nodes.write().remove(endpoint);
        if removed.is_some() {
            self.added_node_names.write().remove(endpoint);
        }
        if let Some(address) = endpoint.socket_addr() {
            self.disconnect_peer_at(address);
        } else {
            let peer_ids = self
                .peer_infos()
                .into_iter()
                .filter(|peer| &peer.endpoint == endpoint)
                .map(|peer| peer.id)
                .collect::<Vec<_>>();
            for peer_id in peer_ids {
                self.disconnect_peer(peer_id);
            }
        }
        removed.is_some()
    }

    pub fn added_nodes(&self) -> Vec<SocketAddr> {
        self.added_nodes
            .read()
            .keys()
            .filter_map(NetworkEndpoint::socket_addr)
            .collect()
    }

    pub(crate) fn added_network_endpoints(&self) -> Vec<NetworkEndpoint> {
        self.added_nodes.read().keys().cloned().collect()
    }

    pub(crate) fn is_node_added_endpoint(&self, endpoint: &NetworkEndpoint) -> bool {
        self.added_nodes.read().contains_key(endpoint)
    }

    pub(crate) fn ensure_node_endpoint_added(&self, endpoint: NetworkEndpoint) {
        if let std::collections::hash_map::Entry::Vacant(entry) =
            self.added_nodes.write().entry(endpoint.clone())
        {
            entry.insert(None);
            self.added_node_names
                .write()
                .insert(endpoint.clone(), endpoint.to_string());
        }
    }

    pub(crate) fn added_node_name(&self, endpoint: &NetworkEndpoint) -> Option<String> {
        self.added_node_names.read().get(endpoint).cloned()
    }

    pub(crate) fn set_peer_manager_sender(
        &self,
        sender: tokio::sync::mpsc::UnboundedSender<p2p::PeerManagerRequest>,
    ) {
        *self.peer_manager_requests.write() = Some(sender);
        self.schedule_private_broadcasts();
    }

    pub fn disconnect_peer(&self, id: usize) -> bool {
        self.peer_commands
            .read()
            .get(&id)
            .is_some_and(|sender| sender.send(p2p::PeerCommand::Disconnect).is_ok())
    }

    pub fn disconnect_peer_at(&self, address: SocketAddr) -> bool {
        self.disconnect_peer_endpoint(&NetworkEndpoint::from_socket(address))
    }

    pub(crate) fn disconnect_peer_endpoint(&self, endpoint: &NetworkEndpoint) -> bool {
        self.peer_infos()
            .into_iter()
            .filter(|peer| &peer.endpoint == endpoint)
            .any(|peer| self.disconnect_peer(peer.id))
    }

    pub fn disconnect_all_peers(&self) {
        let commands: Vec<_> = self.peer_commands.read().values().cloned().collect();
        for sender in commands {
            let _ = sender.send(p2p::PeerCommand::Disconnect);
        }
    }

    pub fn request_block_from_peer(&self, peer_id: usize, hash: bitcoin::BlockHash) -> Result<()> {
        let (header_height, block_downloaded, tip_height, prune_mode) = {
            let chain = self.chain.read();
            let header_height = chain.block_height_by_hash(&hash);
            (
                header_height,
                header_height.is_some_and(|_| chain.store.contains(&hash)),
                chain.height(),
                chain.is_pruned(),
            )
        };
        let Some(header_height) = header_height else {
            bail!("Block header missing");
        };
        if prune_mode && header_height > tip_height {
            bail!(
                "In prune mode, only blocks that the node has already synced previously can be fetched from a peer"
            );
        }
        if block_downloaded {
            bail!("Block already downloaded");
        }
        let sender = self
            .peer_commands
            .read()
            .get(&peer_id)
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("peer {peer_id} is not connected"))?;
        if self
            .peers
            .read()
            .get(&peer_id)
            .is_some_and(|peer| peer.services & wire::NODE_WITNESS == 0)
        {
            bail!("Pre-SegWit peer");
        }
        if self.peer_has_inflight_block_request(peer_id, hash) {
            bail!("Already requested from this peer");
        }
        self.clear_peer_block_requests_for_hash(hash);
        if !self.track_manual_peer_block_request(peer_id, hash) {
            bail!("block request limit reached for peer {peer_id}");
        }
        if sender.send(p2p::PeerCommand::RequestBlock(hash)).is_err() {
            self.clear_peer_block_request(peer_id, hash);
            bail!("peer {peer_id} disconnected");
        }
        Ok(())
    }

    pub fn send_message_to_peer(
        &self,
        peer_id: usize,
        command: String,
        payload: Vec<u8>,
    ) -> Result<()> {
        let sender = self
            .peer_commands
            .read()
            .get(&peer_id)
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("Error: Could not send message to peer"))?;
        sender
            .send(p2p::PeerCommand::SendMessage { command, payload })
            .map_err(|_| anyhow::anyhow!("Error: Could not send message to peer"))
    }

    pub fn ping_peers(&self) {
        let commands: Vec<_> = self
            .peer_commands
            .read()
            .iter()
            .map(|(peer_id, sender)| (*peer_id, sender.clone()))
            .collect();
        for (peer_id, sender) in commands {
            let nonce = random();
            if self.record_ping(peer_id, nonce)
                && sender.send(p2p::PeerCommand::Ping(nonce)).is_err()
            {
                self.cancel_ping(peer_id, nonce);
            }
        }
    }

    pub(crate) fn record_ping(&self, peer_id: usize, nonce: u64) -> bool {
        let mut peers = self.peers.write();
        let Some(peer) = peers.get_mut(&peer_id) else {
            return false;
        };
        if peer
            .version
            .is_none_or(|version| version <= p2p::BIP31_VERSION)
        {
            return false;
        }
        if peer.ping_nonce.is_some() {
            return false;
        }
        peer.ping_nonce = Some(nonce);
        peer.ping_sent_at = Some(Instant::now());
        peer.ping_sent_mocktime = (time::mock_time() > 0).then(time::unix_time_millis);
        true
    }

    pub(crate) fn cancel_ping(&self, peer_id: usize, nonce: u64) {
        if let Some(peer) = self.peers.write().get_mut(&peer_id)
            && peer.ping_nonce == Some(nonce)
        {
            peer.ping_nonce = None;
            peer.ping_sent_at = None;
            peer.ping_sent_mocktime = None;
        }
    }

    pub(crate) fn ping_timed_out(&self, peer_id: usize, timeout: Duration) -> bool {
        self.peers.read().get(&peer_id).is_some_and(|peer| {
            peer.ping_sent_mocktime
                .map(|sent_at| {
                    time::unix_time_millis().saturating_sub(sent_at) >= timeout.as_millis()
                })
                .unwrap_or_else(|| {
                    peer.ping_sent_at
                        .is_some_and(|sent_at| sent_at.elapsed() >= timeout)
                })
        })
    }

    pub fn is_banned(&self, address: IpAddr) -> bool {
        let now = time::unix_time();
        let mut banned = self.banned_addresses.write();
        remove_expired_bans(&mut banned, now);
        banned.keys().any(|subnet| subnet.contains(address))
    }

    pub(crate) fn is_banned_for_peer(&self, address: SocketAddr, inbound: bool) -> bool {
        let permissions = self.permissions_for_peer(address, inbound);
        self.is_banned_for_permissions(address, permissions)
    }

    pub(crate) fn is_banned_for_endpoint(&self, endpoint: &NetworkEndpoint) -> bool {
        if endpoint
            .socket_addr()
            .is_some_and(|address| self.is_banned(address.ip()))
        {
            return true;
        }
        let Some(key) = endpoint.without_port() else {
            return false;
        };
        let now = time::unix_time();
        let mut banned = self.banned_network_addresses.write();
        remove_expired_network_bans(&mut banned, now);
        banned.get(&key).is_some_and(|entry| entry.ban_until > now)
    }

    pub(crate) fn is_banned_for_permissions(
        &self,
        address: SocketAddr,
        permissions: PeerPermissions,
    ) -> bool {
        !permissions.contains(PeerPermissions::NO_BAN) && self.is_banned(address.ip())
    }

    pub fn banned_addresses(&self) -> Vec<BannedAddress> {
        let now = time::unix_time();
        let mut banned = self.banned_addresses.write();
        remove_expired_bans(&mut banned, now);
        let mut addresses = banned.values().cloned().collect::<Vec<_>>();
        addresses.sort_by_key(|entry| entry.subnet().display());
        addresses
    }

    pub fn banned_network_addresses(&self) -> Vec<BannedNetworkAddress> {
        let now = time::unix_time();
        let mut banned = self.banned_network_addresses.write();
        remove_expired_network_bans(&mut banned, now);
        let mut addresses = banned.values().cloned().collect::<Vec<_>>();
        addresses.sort_by_key(|entry| entry.endpoint.host_string());
        addresses
    }

    pub fn ban_address(&self, address: IpAddr, ban_until: u64, reason: String) -> Result<()> {
        self.ban_subnet_with_match(IpSubnet::from_address(address), ban_until, reason, true)
    }

    pub(crate) fn ban_subnet(
        &self,
        subnet: IpSubnet,
        ban_until: u64,
        reason: String,
    ) -> Result<()> {
        self.ban_subnet_with_match(subnet, ban_until, reason, false)
    }

    fn ban_subnet_with_match(
        &self,
        subnet: IpSubnet,
        ban_until: u64,
        reason: String,
        match_containing_subnet: bool,
    ) -> Result<()> {
        let ban_created = time::unix_time();
        let mut banned = self.banned_addresses.write();
        remove_expired_bans(&mut banned, ban_created);
        let already_banned = if match_containing_subnet {
            banned
                .keys()
                .any(|existing| existing.contains(subnet.address()))
        } else {
            banned.contains_key(&subnet)
        };
        if already_banned {
            bail!("IP/Subnet already banned")
        }
        banned.insert(
            subnet,
            BannedAddress {
                address: subnet.address(),
                prefix: subnet.prefix(),
                ban_created,
                ban_until,
                reason,
            },
        );
        drop(banned);
        let peers: Vec<_> = self
            .peer_infos()
            .into_iter()
            .filter(|peer| subnet.contains(peer.address.ip()))
            .map(|peer| peer.id)
            .collect();
        for peer_id in peers {
            self.disconnect_peer(peer_id);
        }
        self.persist_banlist()
    }

    pub(crate) fn ban_network_address(
        &self,
        endpoint: NetworkEndpoint,
        ban_until: u64,
        reason: String,
    ) -> Result<()> {
        let key = endpoint
            .without_port()
            .ok_or_else(|| anyhow::anyhow!("invalid network address"))?;
        let ban_created = time::unix_time();
        let mut banned = self.banned_network_addresses.write();
        remove_expired_network_bans(&mut banned, ban_created);
        if banned.contains_key(&key) {
            bail!("IP/Subnet already banned")
        }
        banned.insert(
            key.clone(),
            BannedNetworkAddress {
                endpoint: key.clone(),
                ban_created,
                ban_until,
                reason,
            },
        );
        drop(banned);
        let peers: Vec<_> = self
            .peer_infos()
            .into_iter()
            .filter(|peer| peer.endpoint.without_port().as_ref() == Some(&key))
            .map(|peer| peer.id)
            .collect();
        for peer_id in peers {
            self.disconnect_peer(peer_id);
        }
        self.persist_banlist()
    }

    pub fn unban_address(&self, address: IpAddr) -> Result<bool> {
        self.unban_subnet(IpSubnet::from_address(address))
    }

    pub(crate) fn unban_subnet(&self, subnet: IpSubnet) -> Result<bool> {
        let removed = self.banned_addresses.write().remove(&subnet).is_some();
        if removed {
            self.persist_banlist()?;
        }
        Ok(removed)
    }

    pub(crate) fn unban_network_address(&self, endpoint: &NetworkEndpoint) -> Result<bool> {
        let Some(key) = endpoint.without_port() else {
            return Ok(false);
        };
        let removed = self.banned_network_addresses.write().remove(&key).is_some();
        if removed {
            self.persist_banlist()?;
        }
        Ok(removed)
    }

    pub fn request_shutdown(&self) {
        self.shutdown_requested.store(true, Ordering::Release);
        self.shutdown.notify_waiters();
        self.disconnect_all_peers();
    }

    pub async fn run(self: Arc<Self>) -> Result<()> {
        self.run_with_startup(None).await
    }

    pub async fn run_with_startup(
        self: Arc<Self>,
        startup_sender: Option<oneshot::Sender<()>>,
    ) -> Result<()> {
        let startup_services = 4 + usize::from(!self.config.ipc_bind.is_empty());
        let startup = startup_sender.map(|sender| StartupLatch::new(sender, startup_services));
        // Preserve Core's initialization trace points for operators and
        // startup tooling. The corresponding native work is completed during
        // Node::open or by the asynchronous services below; these markers do
        // not imply Core's blk/rev database layout.
        info!("scheduler thread start");
        info!("Loading banlist");
        info!("Loading block index");
        info!("Checking all blk files are present");
        let (best_height, best_hash) = {
            let chain = self.chain.read();
            (chain.height(), chain.best_hash())
        };
        info!("Loaded best chain: hash={best_hash} height={best_height}");
        info!("init message: Verifying blocks");
        if let Some(assume_valid) = self.config.assume_valid {
            info!("Assuming ancestors of block {assume_valid} have valid signatures.");
        } else {
            info!("Validating signatures for all blocks.");
        }
        info!("SetNetworkActive: {}", self.network_active());
        if self.banlist_recreated {
            info!("Recreating the banlist database");
        }
        let ipc = ipc::IpcServer::bind(self.clone()).await?;
        if ipc.is_some()
            && let Some(startup) = startup.as_ref()
        {
            startup.service_ready();
        }
        let p2p = p2p::PeerManager::new(self.clone());
        let rpc = rpc::RpcServer::new(self.clone());
        let electrum = electrum::ElectrumServer::new(self.clone());
        let mut ipc_task = ipc.map(|server| tokio::task::spawn_local(server.run()));
        let mut zmq_task = tokio::spawn(zmq::run_with_startup(
            self.config.zmq.clone(),
            self.zmq_events.subscribe_topics(),
            startup.clone(),
        ));

        info!(
            network = ?self.config.network,
            p2p = %self.config.p2p_bind,
            rpc = ?self.config.rpc_bind,
            electrum = ?self.config.electrum_bind,
            ipc = ?self.config.ipc_bind,
            "starting wallet-free Bitcoin node"
        );

        info!("init message: Starting network threads");
        let mut p2p_task = tokio::spawn(p2p.run_with_startup(startup.clone()));
        let mut rpc_task = tokio::spawn(rpc.run_with_startup(startup.clone()));
        let mut electrum_task = tokio::spawn(electrum.run_with_startup(startup));
        run_notify_command(self.config.startup_notify.as_deref(), None);
        let background_node = self.clone();
        let background_validation_task = tokio::spawn(async move {
            let mut ticker = tokio::time::interval(Duration::from_millis(100));
            ticker.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
            loop {
                ticker.tick().await;
                if let Err(error) = background_node.chain.write().poll_background_validation() {
                    warn!(%error, "background AssumeUTXO validation supervisor failed to poll");
                    background_node.set_warning(
                        NodeWarningKind::FatalInternal,
                        format!("background AssumeUTXO validation failed: {error}"),
                    );
                }
            }
        });
        let expiry_node = self.clone();
        let mempool_expiry_task = tokio::spawn(async move {
            let mut ticker = tokio::time::interval(MEMPOOL_EXPIRY_INTERVAL);
            ticker.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
            loop {
                ticker.tick().await;
                expiry_node.expire_mempool();
            }
        });
        let fee_estimator_node = self.clone();
        let fee_estimator_task = tokio::spawn(async move {
            let mut ticker = tokio::time::interval(FEE_ESTIMATOR_FLUSH_INTERVAL);
            ticker.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
            loop {
                ticker.tick().await;
                if let Err(error) = fee_estimator_node.flush_fee_estimates(false) {
                    warn!(%error, "unable to flush fee estimates");
                }
            }
        });
        let unbroadcast_node = self.clone();
        let unbroadcast_retry_task = tokio::spawn(async move {
            let retry_interval = Duration::from_secs(MAX_INITIAL_BROADCAST_DELAY_SECS);
            let first_retry = tokio::time::Instant::now() + retry_interval;
            let mut ticker = tokio::time::interval_at(first_retry, retry_interval);
            ticker.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
            loop {
                tokio::select! {
                    _ = ticker.tick() => unbroadcast_node.reannounce_unbroadcast_transactions(),
                    _ = unbroadcast_node.wait_for_shutdown() => break,
                }
            }
        });

        let current_height = self.chain.read().height();
        if self.config.stop_at_height != 0 && current_height >= self.config.stop_at_height {
            info!(
                target_height = self.config.stop_at_height,
                current_height, "stop height already reached"
            );
            self.request_shutdown();
        }

        let run_result: Result<()> = tokio::select! {
            result = &mut p2p_task => result
                .map_err(anyhow::Error::from)
                .and_then(|result| result),
            result = &mut rpc_task => result
                .map_err(anyhow::Error::from)
                .and_then(|result| result),
            result = &mut electrum_task => result
                .map_err(anyhow::Error::from)
                .and_then(|result| result),
            result = &mut zmq_task => result
                .map_err(anyhow::Error::from)
                .and_then(|result| result),
            result = async {
                match ipc_task.as_mut() {
                    Some(task) => Some(task.await),
                    None => std::future::pending().await,
                }
            } => result
                .expect("IPC task branch only completes when IPC is configured")
                .map_err(anyhow::Error::from)
                .and_then(|result| result),
            result = wait_for_shutdown_signal() => result,
            _ = self.wait_for_shutdown() => Ok(()),
        };

        // Snapshot connected block-relay-only peers before stopping the P2P
        // tasks. This is the native equivalent of Core's clean-shutdown
        // anchors dump; inbound peers and full-relay peers are deliberately
        // excluded.
        let anchors_to_persist = run_result
            .is_ok()
            .then(|| !self.config.connect_disabled && self.config.seed_nodes.is_empty())
            .and_then(|enabled| enabled.then(|| self.current_block_relay_only_anchors()));
        // Every shutdown path, including SIGINT/SIGTERM and an unexpected
        // service exit, must publish the same cancellation signal as RPC
        // `stop`. Peer handlers are spawned below the top-level P2P task;
        // aborting only that parent would otherwise leave a handler capable
        // of mutating chainstate while the final metadata flush is running.
        self.request_shutdown();
        if let Some(task) = ipc_task {
            task.abort();
        }
        if !p2p_task.is_finished() {
            match tokio::time::timeout(Duration::from_secs(10), &mut p2p_task).await {
                Ok(Ok(Ok(()))) => {}
                Ok(Ok(Err(error))) => {
                    warn!(%error, "P2P service ended during shutdown");
                }
                Ok(Err(error)) => {
                    warn!(%error, "P2P service task failed during shutdown");
                }
                Err(_) => {
                    warn!("timed out waiting for P2P service shutdown");
                    p2p_task.abort();
                }
            }
        }
        rpc_task.abort();
        electrum_task.abort();
        zmq_task.abort();
        background_validation_task.abort();
        mempool_expiry_task.abort();
        fee_estimator_task.abort();
        unbroadcast_retry_task.abort();
        tokio::time::timeout(Duration::from_secs(10), self.wait_for_peer_tasks())
            .await
            .map_err(|_| anyhow!("timed out waiting for peer handlers during shutdown"))?;
        self.chain
            .write()
            .flush()
            .context("flushing chainstate during shutdown")?;
        run_notify_command(self.config.shutdown_notify.as_deref(), None);
        if let Err(error) = self.flush_fee_estimates(true) {
            warn!(%error, "unable to flush fee estimates during shutdown");
        }
        if self.config.persist_mempool {
            self.persist_mempool()?;
        }
        if run_result.is_ok() && self.config.coinstatsindex {
            self.persist_coinstats_clean_shutdown_height()?;
        }
        if let Some(anchors) = anchors_to_persist {
            self.persist_block_relay_only_anchors(&anchors)?;
        }
        self.persist_known_addresses()?;
        self.remove_rpc_cookie();
        run_result
    }

    fn remove_rpc_cookie(&self) {
        let Some(path) = self.config.rpc_cookie_path.as_deref() else {
            return;
        };
        if self.rpc_cookie.is_some() {
            let mut paths = vec![path.to_owned()];
            if let Some(compat_path) = rpc_cookie_compat_path(&self.config, path) {
                paths.push(compat_path);
            }
            for path in paths {
                if let Err(error) = fs::remove_file(&path)
                    && error.kind() != std::io::ErrorKind::NotFound
                {
                    warn!(path = %path.display(), %error, "unable to remove RPC authentication cookie");
                }
            }
        }
    }

    pub fn persist_mempool(&self) -> Result<()> {
        self.mempool
            .read()
            .save_to_file_with_format(&self.mempool_path, self.config.persist_mempool_v1)
            .with_context(|| "Unable to dump mempool to disk")
    }

    fn persist_coinstats_clean_shutdown_height(&self) -> Result<()> {
        let height = self.chain.read().height();
        let path = &self.coinstats_clean_shutdown_height_path;
        let temporary_path = std::path::PathBuf::from(format!("{}.tmp", path.display()));
        fs::write(&temporary_path, format!("{height}\n"))
            .with_context(|| format!("writing {}", path.display()))?;
        let file = OpenOptions::new()
            .read(true)
            .open(&temporary_path)
            .with_context(|| format!("opening {} for synchronization", temporary_path.display()))?;
        file.sync_all()
            .with_context(|| format!("flushing {}", temporary_path.display()))?;
        fs::rename(&temporary_path, path)
            .with_context(|| format!("installing {}", path.display()))?;
        Ok(())
    }

    pub(crate) fn take_block_relay_only_anchors(&self, limit: usize) -> Vec<NetworkEndpoint> {
        let mut anchors = self.block_relay_only_anchors.write();
        let count = limit.min(anchors.len());
        anchors.drain(..count).collect()
    }

    fn current_block_relay_only_anchors(&self) -> Vec<NetworkEndpoint> {
        let mut anchors = Vec::with_capacity(MAX_BLOCK_RELAY_ONLY_ANCHORS);
        for peer in self.peer_infos() {
            if peer.inbound
                || peer.connection_type != "block-relay-only"
                || peer.endpoint.to_addr_v2().is_none()
                || anchors.contains(&peer.endpoint)
            {
                continue;
            }
            anchors.push(peer.endpoint);
            if anchors.len() == MAX_BLOCK_RELAY_ONLY_ANCHORS {
                break;
            }
        }
        anchors
    }

    fn persist_block_relay_only_anchors(&self, anchors: &[NetworkEndpoint]) -> Result<()> {
        let mut seen = HashSet::new();
        let entries = anchors
            .iter()
            .filter(|endpoint| endpoint.to_addr_v2().is_some() && seen.insert((*endpoint).clone()))
            .take(MAX_BLOCK_RELAY_ONLY_ANCHORS)
            .map(|endpoint| PersistedAnchor {
                address: endpoint.host_string(),
                network: endpoint.network_name().to_owned(),
                port: endpoint.port(),
            })
            .collect::<Vec<_>>();
        let temporary = self
            .block_relay_only_anchors_path
            .with_file_name(format!(".{BLOCK_RELAY_ONLY_ANCHORS_FILE}.tmp"));
        fs::write(
            &temporary,
            serde_json::to_vec_pretty(&entries).context("serializing block-relay-only anchors")?,
        )
        .with_context(|| {
            format!(
                "writing block-relay-only anchors {}",
                self.block_relay_only_anchors_path.display()
            )
        })?;
        fs::rename(&temporary, &self.block_relay_only_anchors_path).with_context(|| {
            format!(
                "installing block-relay-only anchors {}",
                self.block_relay_only_anchors_path.display()
            )
        })?;
        Ok(())
    }

    pub(crate) fn coinstats_best_block_height(&self) -> u32 {
        self.coinstats_unclean_startup_height
            .unwrap_or_else(|| self.chain.read().height())
    }

    pub(crate) fn mempool_path(&self) -> &Path {
        &self.mempool_path
    }

    pub fn import_mempool(&self, path: impl AsRef<Path>) -> Result<()> {
        self.import_mempool_with_options(
            path,
            MempoolLoadOptions {
                use_current_time: true,
                apply_fee_delta_priority: false,
                apply_unbroadcast_set: false,
            },
        )
    }

    pub fn import_mempool_with_options(
        &self,
        path: impl AsRef<Path>,
        options: MempoolLoadOptions,
    ) -> Result<()> {
        let path = path.as_ref();
        if !path.exists() {
            bail!("mempool file {} does not exist", path.display());
        }
        let chain = self.chain.read();
        let (result, changed, changes) = {
            let mut mempool = self.mempool.write();
            let before = mempool
                .transaction_order()
                .into_iter()
                .collect::<HashSet<_>>();
            let expiry =
                Duration::from_secs(self.config.mempool_expiry_hours.saturating_mul(60 * 60));
            let result =
                mempool.load_from_file_with_expiry_and_options(path, &chain, expiry, options);
            let after = mempool
                .transaction_order()
                .into_iter()
                .collect::<HashSet<_>>();
            let changed = before
                .symmetric_difference(&after)
                .copied()
                .collect::<Vec<_>>();
            let changes = mempool.take_changes();
            (result, changed, changes)
        };
        let current_height = chain.height();
        drop(chain);
        if result.is_ok() {
            self.update_fee_estimator_for_changes(&changes, current_height);
            self.maybe_check_mempool();
            self.notify_zmq_mempool_changes(changes);
            self.record_mempool_stats();
            let mut changed = changed;
            changed.sort_by_key(ToString::to_string);
            for txid in &changed {
                self.announce_mempool_transaction(*txid);
            }
            for txid in changed {
                self.announce_peer_mempool_transaction(txid, Vec::new());
            }
        }
        result
    }

    fn persist_banlist(&self) -> Result<()> {
        let data_dir = self
            .config
            .datadir
            .join(network_data_dir_name(self.config.network));
        let path = data_dir.join("banlist.json");
        let temp = data_dir.join("banlist.json.tmp");
        let mut entries = self
            .banned_addresses
            .read()
            .values()
            .map(|entry| PersistedBannedAddress {
                version: 1,
                address: entry.address.to_string(),
                prefix: Some(entry.prefix),
                network: None,
                ban_created: entry.ban_created,
                ban_until: entry.ban_until,
                reason: entry.reason.clone(),
            })
            .collect::<Vec<_>>();
        entries.extend(self.banned_network_addresses.read().values().map(|entry| {
            PersistedBannedAddress {
                version: 1,
                address: entry.endpoint.host_string(),
                prefix: None,
                network: Some(entry.endpoint.network_name().to_owned()),
                ban_created: entry.ban_created,
                ban_until: entry.ban_until,
                reason: entry.reason.clone(),
            }
        }));
        std::fs::write(&temp, serde_json::to_vec_pretty(&entries)?)?;
        std::fs::rename(temp, path)?;
        Ok(())
    }

    fn persist_known_addresses(&self) -> Result<()> {
        let path = self.config.datadir.join("peers.json");
        let temp = self.config.datadir.join("peers.json.tmp");
        let mut entries = self
            .known_addresses
            .read()
            .values()
            .map(|peer| {
                let source = self.network_address_source(&peer.endpoint);
                PersistedAddress {
                    address: peer.address.to_string(),
                    services: peer.services,
                    time: peer.connected_at,
                    tried: self.is_address_tried(peer.address),
                    network: None,
                    port: None,
                    source: Some(source.host_string()),
                    source_network: Some(source.network_name().to_owned()),
                    source_port: Some(source.port()),
                }
            })
            .collect::<Vec<_>>();
        entries.extend(self.network_addresses.read().values().map(|entry| {
            let source = self.network_address_source(&entry.endpoint);
            PersistedAddress {
                address: entry.endpoint.host_string(),
                services: entry.services,
                time: entry.time,
                tried: self.is_network_address_tried(&entry.endpoint),
                network: Some(entry.endpoint.network_name().to_owned()),
                port: Some(entry.endpoint.port()),
                source: Some(source.host_string()),
                source_network: Some(source.network_name().to_owned()),
                source_port: Some(source.port()),
            }
        }));
        entries.sort_by(|left, right| {
            left.network
                .cmp(&right.network)
                .then_with(|| left.address.cmp(&right.address))
                .then_with(|| left.port.cmp(&right.port))
        });
        std::fs::write(&temp, serde_json::to_vec_pretty(&entries)?)?;
        std::fs::rename(temp, path)?;
        Ok(())
    }
}

fn remove_expired_bans(banned: &mut HashMap<IpSubnet, BannedAddress>, now: u64) {
    banned.retain(|_, entry| entry.ban_until > now);
}

fn remove_expired_network_bans(
    banned: &mut HashMap<NetworkEndpoint, BannedNetworkAddress>,
    now: u64,
) {
    banned.retain(|_, entry| entry.ban_until > now);
}

fn quarantine_persistent_file(path: &Path, error: &anyhow::Error) {
    let Some(file_name) = path.file_name().and_then(|name| name.to_str()) else {
        warn!(path = %path.display(), %error, "discarding invalid persistent state");
        return;
    };
    let mut backup = path.with_file_name(format!("{file_name}.corrupt"));
    let mut suffix = 1u32;
    while backup.exists() {
        backup = path.with_file_name(format!("{file_name}.corrupt.{suffix}"));
        suffix = suffix.saturating_add(1);
    }
    match std::fs::rename(path, &backup) {
        Ok(()) => warn!(
            path = %path.display(),
            backup = %backup.display(),
            %error,
            "quarantined invalid persistent state"
        ),
        Err(rename_error) => warn!(
            path = %path.display(),
            %error,
            %rename_error,
            "failed to quarantine invalid persistent state; continuing with empty state"
        ),
    }
}

struct SettingsObjectVisitor;

const SETTINGS_WARNING: &str = "This file is automatically generated and updated by bitcoind-rs. Please do not edit this file while the node is running, as any changes might be ignored or overwritten.";

impl<'de> Visitor<'de> for SettingsObjectVisitor {
    type Value = serde_json::Value;

    fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("a JSON object")
    }

    fn visit_str<E>(self, value: &str) -> std::result::Result<Self::Value, E>
    where
        E: de::Error,
    {
        Err(E::custom(format!(
            "non-object value {}",
            serde_json::to_string(value).unwrap_or_else(|_| "\"\"".to_owned())
        )))
    }

    fn visit_map<M>(self, mut map: M) -> Result<Self::Value, M::Error>
    where
        M: MapAccess<'de>,
    {
        let mut object = serde_json::Map::new();
        while let Some(key) = map.next_key::<String>()? {
            if object.contains_key(&key) {
                return Err(de::Error::custom(format!("duplicate key {key}")));
            }
            object.insert(key, map.next_value()?);
        }
        Ok(serde_json::Value::Object(object))
    }
}

fn initialize_settings_file(path: &Path) -> Result<()> {
    if path.exists() {
        let contents = fs::read_to_string(path)
            .with_context(|| format!("reading settings file {}", path.display()))?;
        let mut deserializer = serde_json::Deserializer::from_str(&contents);
        let value = deserializer
            .deserialize_any(SettingsObjectVisitor)
            .map_err(|error| {
                let error = error.to_string();
                if let Some(key) = error
                    .strip_prefix("duplicate key ")
                    .map(|key| key.split_once(" at line ").map_or(key, |(key, _)| key))
                {
                    anyhow::anyhow!(
                        "Found duplicate key {key} in settings file {}",
                        path.display()
                    )
                } else if let Some(value) = error
                    .strip_prefix("non-object value ")
                    .map(|value| value.split_once(" at line ").map_or(value, |(value, _)| value))
                {
                    anyhow::anyhow!(
                        "Found non-object value {value} in settings file {}",
                        path.display()
                    )
                } else {
                    anyhow::anyhow!(
                        "Settings file {} does not contain valid JSON. This may be caused by a crash, power loss, full disk, or storage error",
                        path.display()
                    )
                }
            })?;
        deserializer.end().map_err(|_error| {
            anyhow::anyhow!(
                "Settings file {} does not contain valid JSON. This may be caused by a crash, power loss, full disk, or storage error",
                path.display()
            )
        })?;
        let serde_json::Value::Object(object) = value else {
            bail!(
                "settings file {} must contain a JSON object",
                path.display()
            );
        };
        if !object.contains_key("_warning_") {
            let mut settings = serde_json::Map::new();
            settings.insert(
                "_warning_".to_owned(),
                serde_json::Value::String(SETTINGS_WARNING.to_owned()),
            );
            settings.extend(object);
            write_settings_file(path, &serde_json::Value::Object(settings))?;
        }
        return Ok(());
    }

    let warning = serde_json::json!({
        "_warning_": SETTINGS_WARNING
    });
    write_settings_file(path, &warning)?;
    Ok(())
}

fn write_settings_file(path: &Path, settings: &serde_json::Value) -> Result<()> {
    let temporary = path.with_file_name(format!(
        ".{}.tmp",
        path.file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("settings.json")
    ));
    fs::write(&temporary, serde_json::to_vec_pretty(settings)?)
        .with_context(|| format!("writing settings file {}", path.display()))?;
    fs::rename(&temporary, path)
        .with_context(|| format!("installing settings file {}", path.display()))?;
    Ok(())
}

fn load_banlist(data_dir: &Path) -> Result<LoadedBanState> {
    let path = data_dir.join("banlist.json");
    if !path.exists() {
        return Ok((HashMap::new(), HashMap::new()));
    }
    let bytes = std::fs::read(path)?;
    let entries: Vec<PersistedBannedAddress> = serde_json::from_slice(&bytes)?;
    let mut ip_addresses = HashMap::new();
    let mut network_addresses = HashMap::new();
    for entry in entries {
        if entry.version != 1 {
            continue;
        }
        if let Ok(address) = entry.address.parse::<IpAddr>() {
            let prefix = entry.prefix.unwrap_or_else(|| address_bits(address));
            let subnet = IpSubnet::new(address, prefix)?;
            let banned = BannedAddress {
                address: subnet.address(),
                prefix: subnet.prefix(),
                ban_created: entry.ban_created,
                ban_until: entry.ban_until,
                reason: entry.reason,
            };
            ip_addresses.insert(subnet, banned);
        } else {
            let endpoint = match entry.network.as_deref() {
                Some(network) => NetworkEndpoint::parse(Some(network), &entry.address, Some(1))?
                    .without_port()
                    .ok_or_else(|| anyhow::anyhow!("invalid banned network address"))?,
                None => NetworkEndpoint::parse_ban_address(&entry.address)?,
            };
            network_addresses.insert(
                endpoint.clone(),
                BannedNetworkAddress {
                    endpoint,
                    ban_created: entry.ban_created,
                    ban_until: entry.ban_until,
                    reason: entry.reason,
                },
            );
        }
    }
    Ok((ip_addresses, network_addresses))
}

fn load_addrman_key(data_dir: &Path) -> Result<[u8; 32]> {
    let path = data_dir.join(ADDRMAN_SECRET_FILE);
    if path.exists() {
        let bytes = fs::read(&path)
            .with_context(|| format!("reading address-manager secret {}", path.display()))?;
        return bytes.try_into().map_err(|bytes: Vec<u8>| {
            anyhow::anyhow!(
                "address-manager secret {} has invalid length {}; expected 32 bytes",
                path.display(),
                bytes.len()
            )
        });
    }

    let key = random::<[u8; 32]>();
    let temporary = data_dir.join(format!("{ADDRMAN_SECRET_FILE}.tmp"));
    fs::write(&temporary, key)
        .with_context(|| format!("writing address-manager secret {}", path.display()))?;
    fs::rename(&temporary, &path)
        .with_context(|| format!("installing address-manager secret {}", path.display()))?;
    Ok(key)
}

fn load_block_relay_only_anchors(path: &Path) -> Result<Vec<NetworkEndpoint>> {
    if !path.exists() {
        return Ok(Vec::new());
    }
    let bytes = fs::read(path)
        .with_context(|| format!("reading block-relay-only anchors {}", path.display()))?;
    let entries: Vec<PersistedAnchor> = serde_json::from_slice(&bytes)
        .with_context(|| format!("decoding block-relay-only anchors {}", path.display()))?;
    let mut anchors = Vec::with_capacity(entries.len());
    for entry in entries {
        let endpoint =
            NetworkEndpoint::parse(Some(&entry.network), &entry.address, Some(entry.port))
                .with_context(|| {
                    format!(
                        "decoding block-relay-only anchor {}:{}",
                        entry.address, entry.port
                    )
                })?;
        if !anchors.contains(&endpoint) {
            anchors.push(endpoint);
        }
    }
    Ok(anchors)
}

fn load_known_addresses(data_dir: &Path) -> Result<LoadedAddressState> {
    let path = data_dir.join("peers.json");
    if !path.exists() {
        return Ok((
            HashMap::new(),
            HashSet::new(),
            HashMap::new(),
            HashSet::new(),
            HashMap::new(),
        ));
    }
    let bytes = std::fs::read(path)?;
    let entries: Vec<PersistedAddress> = serde_json::from_slice(&bytes)?;
    let mut known = HashMap::with_capacity(entries.len());
    let mut tried = HashSet::new();
    let mut network_addresses = HashMap::new();
    let mut network_tried_addresses = HashSet::new();
    let mut network_address_sources = HashMap::new();
    for entry in entries {
        let endpoint =
            NetworkEndpoint::parse(entry.network.as_deref(), &entry.address, entry.port)?;
        let source = parse_persisted_address_source(&entry, &endpoint)?;
        match endpoint {
            NetworkEndpoint::Ip(address) => {
                if entry.tried {
                    tried.insert(address);
                }
                known.insert(
                    address,
                    PeerInfo {
                        id: UNCONNECTED_PEER_ID,
                        address,
                        endpoint: NetworkEndpoint::Ip(address),
                        local_address: None,
                        reported_local_address: None,
                        inbound: false,
                        version: None,
                        services: entry.services,
                        user_agent: String::new(),
                        start_height: 0,
                        relay_transactions: true,
                        permissions: PeerPermissions::empty(),
                        min_fee_filter: 0,
                        transport_protocol_type: "v1",
                        session_id: String::new(),
                        connection_type: "outbound-full",
                        manual: false,
                        forced_inbound: false,
                        connected_at: entry.time,
                        last_send: entry.time,
                        last_recv: entry.time,
                        bytes_sent: 0,
                        bytes_received: 0,
                        preaccounted_received_bytes: 0,
                        unread_detection_bytes: 0,
                        bytes_sent_per_msg: HashMap::new(),
                        bytes_received_per_msg: HashMap::new(),
                        last_inv_sequence: 0,
                        inv_to_send: 0,
                        last_transaction: 0,
                        last_block: 0,
                        last_block_announcement: 0,
                        best_known_block: None,
                        last_unknown_block: None,
                        last_common_block: None,
                        presynced_headers: -1,
                        bip152_highbandwidth_to: false,
                        bip152_highbandwidth_from: false,
                        inflight_blocks: Vec::new(),
                        time_offset: 0,
                        addr_processed: 0,
                        addr_rate_limited: 0,
                        addr_relay_enabled: false,
                        ping_time: None,
                        min_ping: None,
                        ping_nonce: None,
                        ping_sent_at: None,
                        ping_sent_mocktime: None,
                        addr_token_bucket: 1.0,
                        addr_token_timestamp: time::unix_time_millis(),
                    },
                );
                network_address_sources.insert(NetworkEndpoint::from_socket(address), source);
            }
            endpoint => {
                if entry.tried {
                    network_tried_addresses.insert(endpoint.clone());
                }
                network_addresses.insert(
                    endpoint.clone(),
                    KnownNetworkAddress {
                        endpoint: endpoint.clone(),
                        services: entry.services,
                        time: entry.time,
                    },
                );
                network_address_sources.insert(endpoint, source);
            }
        }
    }
    Ok((
        known,
        tried,
        network_addresses,
        network_tried_addresses,
        network_address_sources,
    ))
}

fn parse_persisted_address_source(
    entry: &PersistedAddress,
    endpoint: &NetworkEndpoint,
) -> Result<NetworkEndpoint> {
    let Some(source) = entry.source.as_deref() else {
        return Ok(endpoint.clone());
    };
    match entry.source_network.as_deref() {
        Some(network) => NetworkEndpoint::parse(Some(network), source, entry.source_port),
        None => NetworkEndpoint::parse(None, source, None),
    }
}

fn unix_time_seconds() -> u64 {
    time::unix_time()
}

fn load_rpc_cookie(path: &Path, permissions: RpcCookiePermissions) -> Result<String> {
    let cookie = format!("__cookie__:{}", hex::encode(random::<[u8; 32]>()));
    write_rpc_cookie(path, &cookie, permissions)?;
    Ok(cookie)
}

fn write_rpc_cookie(path: &Path, cookie: &str, permissions: RpcCookiePermissions) -> Result<()> {
    if let Some(parent) = path.parent()
        && !parent.as_os_str().is_empty()
    {
        std::fs::create_dir_all(parent)?;
    }
    let temp = std::path::PathBuf::from(format!("{}.tmp", path.display()));
    std::fs::write(&temp, cookie)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mode = match permissions {
            RpcCookiePermissions::Owner => 0o600,
            RpcCookiePermissions::Group => 0o640,
            RpcCookiePermissions::All => 0o644,
        };
        std::fs::set_permissions(&temp, std::fs::Permissions::from_mode(mode))?;
    }
    #[cfg(not(unix))]
    let _ = permissions;
    std::fs::rename(temp, path)?;
    Ok(())
}

fn rpc_cookie_compat_path(config: &Config, primary_path: &Path) -> Option<std::path::PathBuf> {
    if config.network == Network::Bitcoin || primary_path != config.datadir.join(".cookie") {
        return None;
    }
    Some(
        config
            .datadir
            .join(network_data_dir_name(config.network))
            .join(".cookie"),
    )
}

#[derive(Debug)]
pub struct CoreStartupError {
    message: String,
}

impl CoreStartupError {
    fn future() -> Self {
        Self {
            message: concat!(
                "The block database contains a block which appears to be from the future. ",
                "This may be due to your computer's date and time being set incorrectly. ",
                "Only rebuild the block database if you are sure that your computer's date ",
                "and time are correct.\nPlease restart with -reindex or ",
                "-reindex-chainstate to recover.",
            )
            .to_owned(),
        }
    }

    pub(crate) fn witness(height: u32) -> Self {
        Self {
            message: format!(
                "Witness data for blocks after height {height} requires validation. Please restart with -reindex..\nPlease restart with -reindex or -reindex-chainstate to recover."
            ),
        }
    }
}

impl std::fmt::Display for CoreStartupError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for CoreStartupError {}

fn core_startup_chain_error(error: anyhow::Error) -> anyhow::Error {
    if error
        .downcast_ref::<validation::ValidationError>()
        .is_some_and(|error| matches!(error, validation::ValidationError::TimeTooNew))
    {
        CoreStartupError::future().into()
    } else {
        error
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::Amount;
    use bitcoin::absolute::LockTime;
    use bitcoin::block::{Header, Version as BlockVersion};
    use bitcoin::blockdata::script::{Builder, ScriptBuf};
    use bitcoin::blockdata::transaction::{OutPoint, TxIn, TxOut, Version};
    use bitcoin::blockdata::witness::Witness;
    use bitcoin::hashes::Hash;
    use clap::Parser;

    #[test]
    fn core_startup_recovery_errors_match_core_messages() {
        assert!(CoreStartupError::future().to_string().starts_with(
            "The block database contains a block which appears to be from the future."
        ));
        assert!(
            CoreStartupError::witness(5)
                .to_string()
                .starts_with("Witness data for blocks after height 5 requires validation.")
        );
    }

    #[test]
    fn mempool_stats_follow_core_sampling_boundaries() {
        let _guard = time::mock_time_test_guard();
        time::set_mock_time(1_000_000);
        let mut stats = MempoolStats::new(true, 10 * 1024 * 1024);

        stats.add_sample(1, 2, 3);
        time::set_mock_time(1_000_001);
        stats.add_sample(4, 5, 6);
        time::set_mock_time(1_000_005);
        stats.add_sample(7, 8, 9);

        let (from, to, samples) = stats.snapshot();
        assert_eq!(from, 1_000_000);
        assert_eq!(to, 1_000_005);
        assert_eq!(
            samples,
            vec![
                MempoolStatsSample {
                    time_delta: 0,
                    tx_count: 1,
                    dynamic_memory_usage: 2,
                    min_fee_per_k: 3,
                },
                MempoolStatsSample {
                    time_delta: 5,
                    tx_count: 7,
                    dynamic_memory_usage: 8,
                    min_fee_per_k: 9,
                },
            ]
        );
    }

    #[test]
    fn notification_commands_expand_tip_hash_placeholders() {
        assert_eq!(
            expand_notify_command("echo %s >> /tmp/tips", Some("abc123")),
            "echo abc123 >> /tmp/tips"
        );
        assert_eq!(expand_notify_command("echo ready", None), "echo ready");
    }

    #[test]
    fn compact_extra_transaction_cache_is_bounded_fifo() {
        let mut cache = CompactExtraTransactions::new(2);
        let transaction = |value| Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: Vec::new(),
            output: vec![TxOut {
                value: Amount::from_sat(value),
                script_pubkey: ScriptBuf::new(),
            }],
        };
        let first = transaction(1);
        let second = transaction(2);
        let third = transaction(3);
        cache.insert(first.clone());
        cache.insert(second.clone());
        cache.insert(third.clone());
        assert_eq!(cache.snapshot(), vec![second, third]);
    }

    #[test]
    fn disconnected_transaction_pool_evicts_newest_entries_at_core_limit() {
        let transactions = (0u8..25)
            .map(|tag| Transaction {
                version: Version::ONE,
                lock_time: LockTime::ZERO,
                input: vec![TxIn {
                    previous_output: OutPoint::new(Txid::from_byte_array([tag; 32]), 0),
                    script_sig: ScriptBuf::from_bytes(vec![tag; 1_000_000]),
                    sequence: bitcoin::Sequence::MAX,
                    witness: Witness::default(),
                }],
                output: vec![TxOut {
                    value: Amount::from_sat(1),
                    script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
                }],
            })
            .collect::<Vec<_>>();
        let mut pool = DisconnectedTransactionPool::default();
        let evicted = pool.add_transactions(&transactions);
        let restored = pool
            .take_oldest_first()
            .map(|transaction| transaction.compute_txid())
            .collect::<Vec<_>>();

        assert!(!evicted.is_empty());
        assert!(restored.len() < transactions.len());
        assert_eq!(restored.first(), Some(&transactions[0].compute_txid()));
        assert!(!restored.contains(&transactions[24].compute_txid()));
    }

    fn test_config(datadir: &Path) -> Config {
        Config {
            network: bitcoin::Network::Regtest,
            datadir: datadir.to_owned(),
            blocks_dir: None,
            blocks_dir_explicit: false,
            ipc_bind: Vec::new(),
            blocks_xor: false,
            capture_messages: false,
            debug_log_path: std::path::PathBuf::from("debug.log"),
            pid_path: std::path::PathBuf::from("bitcoind.pid"),
            logging: Default::default(),
            debug_log_file_enabled: false,
            print_to_console: false,
            shrink_debug_file: false,
            settings_path: None,
            asmap: None,
            minimum_chain_work: None,
            assume_valid: None,
            check_blocks: None,
            check_level: None,
            check_block_index: 0,
            check_mempool: 0,
            check_addrman: 0,
            max_tip_age_secs: 24 * 60 * 60,
            mock_time: None,
            stop_at_height: 0,
            p2p_bind: "127.0.0.1:0".parse().unwrap(),
            p2p_binds: Vec::new(),
            rpc_bind: None,
            rpc_binds: Vec::new(),
            rpc_allow_ips: Vec::new(),
            rpc_auth: Vec::new(),
            rpc_cookie_path: None,
            rpc_cookie_permissions: crate::config::RpcCookiePermissions::Owner,
            rpc_server_timeout_secs: 30,
            rpc_threads: 16,
            rpc_work_queue: 64,
            script_check_threads: 0,
            block_reconstruction_extra_txn: 100,
            user_agent_comments: Vec::new(),
            startup_notify: None,
            block_notify: None,
            shutdown_notify: None,
            alert_notify: None,
            max_sig_cache_mib: 32,
            db_cache_mib: 450,
            db_batch_size_bytes: 32 * 1024 * 1024,
            print_priority: false,
            rpc_doc_check: false,
            accept_stale_fee_estimates: false,
            rpc_whitelist: std::collections::HashMap::new(),
            rpc_whitelist_default: false,
            electrum_bind: None,
            rest: false,
            listen: true,
            dnsseed: true,
            fixed_seeds: false,
            force_dns_seed: false,
            onlynet: Vec::new(),
            proxy: None,
            i2p_sam: None,
            onion_proxy: None,
            listen_onion: false,
            onion_enabled: true,
            tor_control: "127.0.0.1:9051".parse().unwrap(),
            tor_password: None,
            i2p_accept_incoming: false,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            rbf_policy: crate::mempool::RbfPolicy::Always,
            truc_policy: crate::mempool::TrucPolicy::Accept,
            cjdns_reachable: true,
            prune: 0,
            fast_prune: false,
            natpmp: false,
            reindex: false,
            reindex_chainstate: false,
            load_blocks: Vec::new(),
            stop_after_block_import: false,
            txindex: false,
            txospenderindex: false,
            max_mempool_mb: 300,
            cluster_count: 64,
            cluster_size_vbytes: 101_000,
            ancestor_count_limit: 25,
            ancestor_size_vbytes: 101_000,
            descendant_count_limit: 25,
            descendant_size_vbytes: 101_000,
            mempool_expiry_hours: 336,
            coinstatsindex: false,
            stats_enable: false,
            stats_max_memory_target: 10 * 1024 * 1024,
            blockfilterindex: true,
            peer_block_filters: true,
            persist_mempool: true,
            persist_mempool_v1: false,
            seed_nodes: Vec::new(),
            connect_disabled: false,
            v2_transport: true,
            network_active: true,
            discover: true,
            external_addresses: Vec::new(),
            dns_lookup: true,
            add_nodes: Vec::new(),
            seed_nodes_for_address_fetch: Vec::new(),
            signet_challenge: None,
            signet_seed_nodes: Vec::new(),
            deployment_parameters: None,
            max_peers: 1,
            max_receive_buffer: 5_000,
            max_send_buffer: 1_000,
            max_upload_target: 0,
            peer_bloom_filters: false,
            peer_timeout_secs: 60,
            ban_time_secs: 86_400,
            deprecated_rpcs: std::collections::HashSet::new(),
            connect_timeout_ms: 5_000,
            block_max_weight: 4_000_000,
            block_reserved_weight: 8_000,
            block_version: None,
            block_min_tx_fee_sat_per_kvb: 1,
            min_relay_tx_fee_sat_per_kvb: 100,
            incremental_relay_fee_sat_per_kvb: 100,
            dust_relay_fee_sat_per_kvb: 3_000,
            max_datacarrier_bytes: Some(100_000),
            bytes_per_sigop: 20,
            permit_bare_multisig: true,
            zmq: crate::config::ZmqConfig::default(),
        }
    }

    #[test]
    fn data_directory_lock_rejects_concurrent_nodes_and_releases_on_drop() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        assert!(Node::open(test_config(directory.path())).is_err());
        drop(node);
        assert!(Node::open(test_config(directory.path())).is_ok());
    }

    #[test]
    fn limits_automatic_outbound_peers_without_reduced_data_service() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let (sender, _receiver) = tokio::sync::mpsc::unbounded_channel();
        let services = crate::wire::NODE_NETWORK | crate::wire::NODE_WITNESS;

        for id in 1..=8 {
            node.register_peer(
                id,
                format!("192.0.2.{id}:18444").parse().unwrap(),
                false,
                sender.clone(),
            );
            assert!(node.admit_non_reduced_outbound(id, services));
            node.update_peer_version(id, 70016, services, "/stale/", 0, true);
        }
        assert_eq!(node.non_reduced_outbound_count(), 8);

        node.register_peer(9, "192.0.2.9:18444".parse().unwrap(), false, sender.clone());
        assert!(!node.admit_non_reduced_outbound(9, services));

        node.unregister_peer(1);
        assert_eq!(node.non_reduced_outbound_count(), 7);
        assert!(node.admit_non_reduced_outbound(9, services));
        node.update_peer_version(9, 70016, services, "/stale/", 0, true);

        // Manual connections are not counted against Core's automatic stale
        // peer limit.
        node.register_peer_with_endpoint(
            10,
            crate::address::NetworkEndpoint::from_socket("192.0.2.10:18444".parse().unwrap()),
            false,
            sender,
            PeerRegistrationOptions {
                local_address: None,
                permissions: PeerPermissions::empty(),
                connection_type: "outbound-full",
                manual: true,
                forced_inbound: false,
            },
        );
        assert!(node.admit_non_reduced_outbound(10, services));
        assert_eq!(node.non_reduced_outbound_count(), 8);
    }

    #[cfg(unix)]
    #[test]
    fn network_and_wallet_directories_are_private() {
        use std::os::unix::fs::PermissionsExt;

        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let network_directory = directory.path().join("regtest");
        let wallets_directory = network_directory.join("wallets");

        assert!(!network_directory.join("peers.dat").exists());
        assert_eq!(
            fs::metadata(network_directory)
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o700
        );
        assert_eq!(
            fs::metadata(wallets_directory)
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o700
        );
        drop(node);
    }

    #[test]
    fn blocks_directory_lock_rejects_different_data_directories() {
        let data_directory = tempfile::tempdir().unwrap();
        let other_data_directory = tempfile::tempdir().unwrap();
        let blocks_directory = tempfile::tempdir().unwrap();
        let mut config = test_config(data_directory.path());
        config.blocks_dir = Some(blocks_directory.path().to_owned());
        let node = Node::open(config).unwrap();

        let mut conflicting_config = test_config(other_data_directory.path());
        conflicting_config.blocks_dir = Some(blocks_directory.path().to_owned());
        assert!(Node::open(conflicting_config.clone()).is_err());

        drop(node);
        assert!(Node::open(conflicting_config).is_ok());
    }

    #[test]
    fn explicit_missing_blocks_directory_is_rejected() {
        let data_directory = tempfile::tempdir().unwrap();
        let missing_blocks_directory = data_directory.path().join("missing-blocks");
        let mut config = test_config(data_directory.path());
        config.blocks_dir = Some(missing_blocks_directory.clone());
        config.blocks_dir_explicit = true;
        assert!(Node::open(config).is_err());
        assert!(!missing_blocks_directory.exists());
    }

    #[test]
    fn runtime_settings_file_is_created_and_validated() {
        let directory = tempfile::tempdir().unwrap();
        let settings_path = directory.path().join("settings.json");
        let mut config = test_config(directory.path());
        config.settings_path = Some(settings_path.clone());
        drop(Node::open(config).unwrap());

        let settings: serde_json::Value =
            serde_json::from_slice(&fs::read(&settings_path).unwrap()).unwrap();
        assert!(settings.get("_warning_").is_some());

        fs::write(&settings_path, br#"{"key": 1, "key": 2}"#).unwrap();
        let mut config = test_config(directory.path());
        config.settings_path = Some(settings_path);
        assert!(Node::open(config).is_err());
    }

    #[test]
    fn capture_messages_uses_core_record_framing() {
        let directory = tempfile::tempdir().unwrap();
        let mut config = test_config(directory.path());
        config.capture_messages = true;
        let node = Node::open(config).unwrap();
        let (sender, _receiver) = tokio::sync::mpsc::unbounded_channel();
        node.register_peer(1, "192.0.2.1:18444".parse().unwrap(), false, sender);
        let message = wire::Message::Ping(42);
        node.capture_message(1, false, &message).unwrap();

        let path = directory
            .path()
            .join("regtest/message_capture/192.0.2.1_18444/msgs_sent.dat");
        let bytes = fs::read(path).unwrap();
        assert_eq!(bytes.len(), 8 + 12 + 4 + 8);
        assert_ne!(u64::from_le_bytes(bytes[..8].try_into().unwrap()), 0);
        assert_eq!(&bytes[8..12], b"ping");
        assert!(bytes[12..20].iter().all(|byte| *byte == 0));
        assert_eq!(u32::from_le_bytes(bytes[20..24].try_into().unwrap()), 8);
        assert_eq!(u64::from_le_bytes(bytes[24..32].try_into().unwrap()), 42);
    }

    #[test]
    fn max_upload_target_matches_core_reserve_rules() {
        let target = 10_000_000;
        let usage = OutboundUsage {
            cycle_start: 1_000,
            bytes: 6_000_000,
        };
        assert!(!outbound_target_reached(target, usage, 1_000, false));
        assert_eq!(outbound_time_left_in_cycle(target, usage, 1_000), 86_400);
        assert!(outbound_target_reached(target, usage, 1_000 + 85_800, true));
        assert_eq!(
            outbound_time_left_in_cycle(target, usage, 1_000 + 85_800),
            600
        );
        assert!(!outbound_target_reached(
            target,
            usage,
            1_000 + 85_800,
            false
        ));
        assert!(!outbound_target_reached(
            0,
            OutboundUsage::default(),
            1_000,
            false
        ));
        assert_eq!(
            outbound_time_left_in_cycle(0, OutboundUsage::default(), 1_000),
            0
        );
    }

    #[test]
    fn persistent_added_node_keeps_transport_preference() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let address = "192.0.2.10:18444".parse().unwrap();

        assert!(node.add_node_with_transport(address, Some(false)));
        assert_eq!(
            node.added_nodes
                .read()
                .get(&NetworkEndpoint::from_socket(address)),
            Some(&Some(false))
        );
        assert!(!node.add_node_with_transport(address, Some(true)));
        assert_eq!(
            node.added_nodes
                .read()
                .get(&NetworkEndpoint::from_socket(address)),
            Some(&Some(false))
        );
        assert!(node.remove_node(&address));
        assert!(!node.is_node_added_endpoint(&NetworkEndpoint::from_socket(address)));
    }

    #[test]
    fn corrupt_startup_mempool_does_not_abort_node_open() {
        let directory = tempfile::tempdir().unwrap();
        let network_directory = directory.path().join("regtest");
        fs::create_dir_all(&network_directory).unwrap();
        fs::write(network_directory.join("mempool.dat"), b"not a mempool dump").unwrap();

        let node = Node::open(test_config(directory.path())).unwrap();

        assert!(node.mempool.read().is_empty());
    }

    fn private_broadcast_test_transaction(node: &Arc<Node>) -> Transaction {
        for height in 1..=101 {
            let previous = *node.chain.read().header(height - 1).unwrap();
            node.connect_block(mine_test_block(&previous, height, height as u8))
                .unwrap();
        }
        let funding_hash = node.chain.read().block_hash(1).unwrap();
        let funding_block = node.chain.write().block(&funding_hash).unwrap().unwrap();
        Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(funding_block.txdata[0].compute_txid(), 0),
                script_sig: ScriptBuf::from_bytes(vec![0; 8]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(4_999_999_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        }
    }

    #[test]
    fn mock_scheduler_reannounces_unbroadcast_transactions() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let transaction = private_broadcast_test_transaction(&node);
        let txid = transaction.compute_txid();
        let mut events = node.subscribe_peer_mempool();

        assert_eq!(node.accept_transaction(transaction).unwrap(), txid);
        assert_eq!(events.try_recv().unwrap().txid, txid);

        node.mock_scheduler_forward(MAX_INITIAL_BROADCAST_DELAY_SECS - 1)
            .unwrap();
        assert!(events.try_recv().is_err());
        node.mock_scheduler_forward(1).unwrap();
        assert_eq!(events.try_recv().unwrap().txid, txid);

        node.mempool.write().remove_unbroadcast(&txid);
        node.mock_scheduler_forward(MAX_INITIAL_BROADCAST_DELAY_SECS)
            .unwrap();
        assert!(events.try_recv().is_err());
        node.mock_scheduler_forward(FEE_ESTIMATOR_FLUSH_INTERVAL.as_secs())
            .unwrap();
        assert!(
            directory
                .path()
                .join("regtest")
                .join("fee_estimates.dat")
                .exists()
        );
    }

    #[test]
    fn private_broadcast_queue_keeps_transactions_out_of_the_mempool() {
        let directory = tempfile::tempdir().unwrap();
        let mut config = test_config(directory.path());
        config.private_broadcast = true;
        config.proxy = Some("127.0.0.1:9050".parse().unwrap());
        config.seed_nodes = vec![
            NetworkEndpoint::from_socket("192.0.2.1:18444".parse().unwrap()),
            NetworkEndpoint::from_socket("192.0.2.2:18444".parse().unwrap()),
            NetworkEndpoint::from_socket("192.0.2.3:18444".parse().unwrap()),
        ];
        config.max_peers = 3;
        let node = Node::open(config).unwrap();
        let transaction = private_broadcast_test_transaction(&node);
        let txid = transaction.compute_txid();
        let wtxid = transaction.compute_wtxid();
        let (sender, mut receiver) = tokio::sync::mpsc::unbounded_channel();
        node.set_peer_manager_sender(sender);

        assert_eq!(
            node.queue_private_broadcast(transaction.clone()).unwrap(),
            txid
        );
        assert!(node.mempool.read().is_empty());
        let info = node.private_broadcast_infos();
        assert_eq!(info.len(), 1);
        assert_eq!(info[0].transaction.compute_wtxid(), wtxid);
        assert_eq!(info[0].peers.len(), 3);
        for _ in 0..3 {
            assert!(matches!(
                receiver.try_recv().unwrap(),
                p2p::PeerManagerRequest::PrivateBroadcast { .. }
            ));
        }

        let address = info[0].peers[0].address;
        node.mark_private_broadcast_peer_ack(&transaction, address);
        assert!(
            node.private_broadcast_infos()[0].peers[0]
                .received
                .is_some()
        );
        assert!(node.mark_private_broadcast_received(&transaction));
        assert!(node.private_broadcast_infos().is_empty());
        assert!(node.mempool.read().is_empty());
    }

    #[test]
    fn abort_private_broadcast_matches_wtxid_and_disconnects_private_peers() {
        let directory = tempfile::tempdir().unwrap();
        let mut config = test_config(directory.path());
        config.private_broadcast = true;
        config.proxy = Some("127.0.0.1:9050".parse().unwrap());
        config.seed_nodes = vec![NetworkEndpoint::from_socket(
            "192.0.2.1:18444".parse().unwrap(),
        )];
        let node = Node::open(config).unwrap();
        let transaction = private_broadcast_test_transaction(&node);
        let wtxid = transaction.compute_wtxid();
        node.queue_private_broadcast(transaction.clone()).unwrap();

        let removed = node.abort_private_broadcast(wtxid.to_string().parse().unwrap());
        assert_eq!(removed.len(), 1);
        assert_eq!(removed[0].transaction, transaction);
        assert!(node.private_broadcast_infos().is_empty());
    }

    #[test]
    fn subnet_bans_normalize_and_load_legacy_single_addresses() {
        let subnet = IpSubnet::parse("192.0.2.7/24").unwrap();
        assert_eq!(subnet.display(), "192.0.2.0/24");
        assert!(subnet.contains("192.0.2.99".parse().unwrap()));
        assert!(!subnet.contains("192.0.3.1".parse().unwrap()));
        let netmask = IpSubnet::parse("192.0.2.7/255.255.255.0").unwrap();
        assert_eq!(netmask.display(), "192.0.2.0/24");
        assert!(IpSubnet::parse("192.0.2.7/255.0.255.0").is_err());

        let directory = tempfile::tempdir().unwrap();
        let legacy = serde_json::json!([{
            "address": "192.0.2.7",
            "ban_created": 1,
            "ban_until": 2,
            "reason": "manual"
        }, {
            "address": "pg6mmjiyjmcrsslvykfwnntlaru7p5svn6y2ymmju6nubxndf4pscryd.onion",
            "ban_created": 1,
            "ban_until": 2,
            "reason": "manual"
        }]);
        fs::write(
            directory.path().join("banlist.json"),
            serde_json::to_vec(&legacy).unwrap(),
        )
        .unwrap();
        let (loaded, loaded_network) = load_banlist(directory.path()).unwrap();
        let legacy_subnet = IpSubnet::parse("192.0.2.7").unwrap();
        assert_eq!(loaded[&legacy_subnet].prefix, 32);
        assert_eq!(
            loaded[&legacy_subnet].address,
            "192.0.2.7".parse::<IpAddr>().unwrap()
        );
        assert_eq!(loaded_network.len(), 1);
        assert_eq!(
            loaded_network
                .values()
                .next()
                .unwrap()
                .endpoint
                .host_string(),
            "pg6mmjiyjmcrsslvykfwnntlaru7p5svn6y2ymmju6nubxndf4pscryd.onion"
        );
    }

    #[test]
    fn rpc_cookie_rotates_on_each_startup() {
        let directory = tempfile::tempdir().unwrap();
        let cookie_path = directory.path().join(".cookie");
        let first = load_rpc_cookie(&cookie_path, RpcCookiePermissions::Owner).unwrap();
        let second = load_rpc_cookie(&cookie_path, RpcCookiePermissions::Owner).unwrap();
        assert_ne!(first, second);
        assert_eq!(
            fs::read_to_string(directory.path().join(".cookie"))
                .unwrap()
                .trim(),
            second
        );
    }

    #[cfg(unix)]
    #[test]
    fn rpc_cookie_permissions_follow_core_modes() {
        use std::os::unix::fs::PermissionsExt;

        let directory = tempfile::tempdir().unwrap();
        let cookie_path = directory.path().join(".cookie");
        for (permissions, mode) in [
            (RpcCookiePermissions::Owner, 0o600),
            (RpcCookiePermissions::Group, 0o640),
            (RpcCookiePermissions::All, 0o644),
        ] {
            load_rpc_cookie(&cookie_path, permissions).unwrap();
            assert_eq!(
                fs::metadata(&cookie_path).unwrap().permissions().mode() & 0o777,
                mode
            );
        }
    }

    #[test]
    fn generated_rpc_cookie_is_removed_on_shutdown() {
        let directory = tempfile::tempdir().unwrap();
        let args = crate::config::Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--rpccookiefile=auth/rpc.cookie",
        ])
        .unwrap();
        let node = Node::open(Config::from_args(args).unwrap()).unwrap();
        let path = directory.path().join("auth/rpc.cookie");
        assert!(path.exists());
        node.remove_rpc_cookie();
        assert!(!path.exists());
    }

    #[tokio::test]
    async fn shutdown_requested_before_run_is_not_lost() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        node.request_shutdown();
        tokio::time::timeout(Duration::from_secs(2), node.run())
            .await
            .expect("pre-run shutdown should wake the node")
            .unwrap();
    }

    #[tokio::test]
    async fn shutdown_waits_for_peer_handlers_before_flushing_chainstate() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        node.peer_count.fetch_add(1, Ordering::Release);
        node.request_shutdown();

        let run_node = node.clone();
        let mut run_task = tokio::spawn(async move { run_node.run().await });
        assert!(
            tokio::time::timeout(Duration::from_millis(100), &mut run_task)
                .await
                .is_err(),
            "shutdown must not flush while a peer handler is still active"
        );

        node.peer_count.fetch_sub(1, Ordering::Release);
        node.notify_peer_task_finished();
        tokio::time::timeout(Duration::from_secs(2), run_task)
            .await
            .expect("node shutdown should finish after peer handlers exit")
            .unwrap()
            .unwrap();
    }

    #[test]
    fn shutdown_interrupts_peer_block_validation_before_mutation() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let previous = *node.chain.read().header(0).unwrap();
        let block = mine_test_block(&previous, 1, 42);

        node.request_shutdown();
        assert!(node.connect_block_from_peer(block).is_err());
        assert_eq!(node.chain.read().height(), 0);
    }

    #[tokio::test]
    async fn stop_after_block_import_requests_shutdown_before_run() {
        let directory = tempfile::tempdir().unwrap();
        let mut config = test_config(directory.path());
        config.stop_after_block_import = true;
        let node = Node::open(config).unwrap();

        tokio::time::timeout(Duration::from_secs(2), node.run())
            .await
            .expect("stop-after-block-import should wake the node")
            .unwrap();
    }

    #[test]
    fn startup_block_import_persists_only_native_storage() {
        let directory = tempfile::tempdir().unwrap();
        let source_directory = directory.path().join("source");
        let source_chain = ChainState::open(Network::Regtest, &source_directory).unwrap();
        let block = mine_test_block(source_chain.header(0).unwrap(), 1, 77);
        drop(source_chain);

        let payload = bitcoin::consensus::encode::serialize(&block);
        let mut framed = wire::network_magic(Network::Regtest).to_vec();
        framed.extend_from_slice(&(payload.len() as u32).to_le_bytes());
        framed.extend_from_slice(&payload);
        let import_path = directory.path().join("bootstrap.dat");
        fs::write(&import_path, framed).unwrap();

        let mut config = test_config(directory.path());
        config.load_blocks.push(import_path);
        config.stop_after_block_import = true;
        let node = Node::open(config).unwrap();
        assert_eq!(node.chain.read().height(), 1);
        assert_eq!(node.chain.read().best_hash(), block.block_hash());
        drop(node);

        let blocks_directory = directory.path().join("blocks");
        assert!(blocks_directory.join("blocks.dat").is_file());
        assert!(blocks_directory.join("blocks.index").is_file());
        assert!(blocks_directory.join("undo.dat").is_file());
        assert!(blocks_directory.join("undo.index").is_file());
        assert!(!blocks_directory.join("blk00000.dat").exists());
        assert!(!blocks_directory.join("rev00000.dat").exists());

        let reopened = Node::open(test_config(directory.path())).unwrap();
        assert_eq!(reopened.chain.read().height(), 1);
        assert_eq!(reopened.chain.read().best_hash(), block.block_hash());
    }

    #[tokio::test]
    async fn stop_at_height_requests_shutdown_when_tip_reaches_target() {
        let directory = tempfile::tempdir().unwrap();
        let mut config = test_config(directory.path());
        config.stop_at_height = 1;
        let node = Node::open(config).unwrap();
        let previous = *node.chain.read().header(0).unwrap();
        node.connect_block(mine_test_block(&previous, 1, 1))
            .unwrap();

        tokio::time::timeout(Duration::from_secs(2), node.run())
            .await
            .expect("stop height should wake the node")
            .unwrap();
    }

    #[test]
    fn blocks_directory_can_be_separated_from_chainstate() {
        let directory = tempfile::tempdir().unwrap();
        std::fs::create_dir_all(directory.path().join("external-blocks")).unwrap();
        let args = crate::config::Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--network=regtest",
            "--blocksdir=external-blocks",
        ])
        .unwrap();
        let node = Node::open(Config::from_args(args).unwrap()).unwrap();
        let previous = *node.chain.read().header(0).unwrap();
        node.connect_block(mine_test_block(&previous, 1, 1))
            .unwrap();

        let external_blocks = directory.path().join("external-blocks/regtest/blocks");
        assert!(
            external_blocks.join("blocks.dat").exists(),
            "connected blocks must be written to the configured native blocksdir"
        );
        for name in ["blk00000.dat", "rev00000.dat"] {
            assert!(
                !external_blocks.join(name).exists(),
                "native blocksdir must not create Core file {name}"
            );
        }
        assert!(
            external_blocks.join("xor.dat").exists(),
            "configured native blocksdir must retain its XOR key"
        );
        assert!(directory.path().join("chainstate.bin").exists());
        assert!(!directory.path().join("blocks/blocks.dat").exists());
    }

    #[test]
    fn node_uses_native_block_storage_without_core_block_files() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let previous = *node.chain.read().header(0).unwrap();
        node.connect_block(mine_test_block(&previous, 1, 1))
            .unwrap();
        drop(node);

        let blocks_directory = directory.path().join("blocks");
        assert!(blocks_directory.join("blocks.dat").is_file());
        assert!(blocks_directory.join("blocks.index").is_file());
        assert!(blocks_directory.join("undo.dat").is_file());
        assert!(blocks_directory.join("undo.index").is_file());
        for name in ["blk00000.dat", "rev00000.dat"] {
            assert!(
                !blocks_directory.join(name).exists(),
                "native node storage must not create Core file {name}"
            );
        }
        assert!(
            !directory
                .path()
                .join("indexes/electrum/txblocks.dat")
                .exists(),
            "unpruned nodes must not duplicate block transactions in an Electrum sidecar"
        );
    }

    #[test]
    fn native_reindex_rebuilds_chainstate_and_transaction_index() {
        let directory = tempfile::tempdir().unwrap();
        let mut initial_config = test_config(directory.path());
        initial_config.txindex = true;

        let (tip_hash, tip_txid) = {
            let node = Node::open(initial_config).unwrap();
            for height in 1..=3 {
                let previous = *node.chain.read().header(height - 1).unwrap();
                node.connect_block(mine_test_block(&previous, height, height as u8))
                    .unwrap();
            }
            let chain = node.chain.read();
            let tip_hash = chain.best_hash();
            let tip = chain.block_for_serving(&tip_hash).unwrap().unwrap();
            (tip_hash, tip.txdata[0].compute_txid())
        };

        for (reindex, reindex_chainstate) in [(true, false), (false, true)] {
            let mut config = test_config(directory.path());
            config.txindex = true;
            config.reindex = reindex;
            config.reindex_chainstate = reindex_chainstate;
            let node = Node::open(config).unwrap();
            assert_eq!(node.chain.read().height(), 3);
            assert_eq!(node.chain.read().best_hash(), tip_hash);
            assert!(node.chain.write().transaction(&tip_txid).unwrap().is_some());
            assert!(
                node.chain
                    .read()
                    .block_for_serving(&tip_hash)
                    .unwrap()
                    .is_some()
            );
        }
    }

    #[test]
    fn minimum_chain_work_override_reaches_chain_state() {
        let directory = tempfile::tempdir().unwrap();
        let args = crate::config::Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--network=regtest",
            "--minimumchainwork=01",
        ])
        .unwrap();
        let node = Node::open(Config::from_args(args).unwrap()).unwrap();

        assert_eq!(
            node.chain.read().minimum_chain_work(),
            bitcoin::pow::Work::from_unprefixed_hex("01").unwrap()
        );
    }

    #[test]
    fn explicit_startup_block_checks_verify_persisted_chainstate() {
        let directory = tempfile::tempdir().unwrap();
        let args = crate::config::Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--network=regtest",
        ])
        .unwrap();
        let node = Node::open(Config::from_args(args).unwrap()).unwrap();
        let previous = *node.chain.read().header(0).unwrap();
        node.connect_block(mine_test_block(&previous, 1, 1))
            .unwrap();
        drop(node);

        let args = crate::config::Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--network=regtest",
            "--checkblocks=1",
            "--checklevel=4",
        ])
        .unwrap();
        Node::open(Config::from_args(args).unwrap()).unwrap();
    }

    #[test]
    fn whitelisted_noban_peers_bypass_admission_bans() {
        let directory = tempfile::tempdir().unwrap();
        let args = crate::config::Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--whitelist=192.0.2.0/24",
        ])
        .unwrap();
        let node = Node::open(Config::from_args(args).unwrap()).unwrap();
        let until = time::unix_time().saturating_add(600);
        node.ban_address("192.0.2.1".parse().unwrap(), until, "test".to_owned())
            .unwrap();
        node.ban_address("198.51.100.1".parse().unwrap(), until, "test".to_owned())
            .unwrap();

        assert!(!node.is_banned_for_peer("192.0.2.7:18444".parse().unwrap(), true));
        assert!(node.is_banned_for_peer("198.51.100.1:18444".parse().unwrap(), true));
    }

    #[test]
    fn imports_network_framed_external_blocks() {
        let directory = tempfile::tempdir().unwrap();
        let mut chain = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let block = mine_test_block(chain.header(0).unwrap(), 1, 1);
        let payload = bitcoin::consensus::encode::serialize(&block);
        let mut framed = wire::network_magic(Network::Regtest).to_vec();
        framed.extend_from_slice(&(payload.len() as u32).to_le_bytes());
        framed.extend_from_slice(&payload);
        let path = directory.path().join("external.blk");
        fs::write(&path, framed).unwrap();

        assert_eq!(
            import_external_block_file(&mut chain, &path, Network::Regtest, None).unwrap(),
            1
        );
        assert_eq!(chain.height(), 1);
        assert_eq!(chain.best_hash(), block.block_hash());
    }

    #[test]
    fn imports_a_block_body_for_a_persisted_header() {
        let directory = tempfile::tempdir().unwrap();
        let mut chain = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let block = mine_test_block(chain.header(0).unwrap(), 1, 2);
        chain
            .accept_headers(std::slice::from_ref(&block.header))
            .unwrap();
        assert!(chain.block(&block.block_hash()).unwrap().is_none());

        let payload = bitcoin::consensus::encode::serialize(&block);
        let mut framed = wire::network_magic(Network::Regtest).to_vec();
        framed.extend_from_slice(&(payload.len() as u32).to_le_bytes());
        framed.extend_from_slice(&payload);
        let path = directory.path().join("header-body.blk");
        fs::write(&path, framed).unwrap();

        assert_eq!(
            import_external_block_file(&mut chain, &path, Network::Regtest, None).unwrap(),
            1
        );
        assert!(chain.block(&block.block_hash()).unwrap().is_some());
        assert_eq!(chain.best_hash(), block.block_hash());
    }

    #[test]
    fn imports_padded_out_of_order_external_blocks() {
        let directory = tempfile::tempdir().unwrap();
        let mut chain = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let first = mine_test_block(chain.header(0).unwrap(), 1, 3);
        let second = mine_test_block(&first.header, 2, 4);
        let magic = wire::network_magic(Network::Regtest);
        let frame = |block: &Block| {
            let payload = bitcoin::consensus::encode::serialize(block);
            let mut frame = magic.to_vec();
            frame.extend_from_slice(&(payload.len() as u32).to_le_bytes());
            frame.extend_from_slice(&payload);
            frame
        };

        // The external importer must scan around non-record bytes, defer the
        // child until its parent arrives, and ignore an incomplete final
        // record instead of discarding the valid prefix.
        // Put the first magic marker across the streaming reader's buffer
        // boundary so scanning does not depend on record alignment.
        let mut framed = vec![0x11; EXTERNAL_BLOCK_READ_SIZE - 2];
        framed.extend_from_slice(&frame(&second));
        framed.extend_from_slice(&[0x91, 0x92, 0x93]);
        framed.extend_from_slice(&frame(&first));
        framed.extend_from_slice(&magic);
        framed.extend_from_slice(&100u32.to_le_bytes());
        framed.extend_from_slice(&[0xaa; 5]);
        let path = directory.path().join("padded-external.blk");
        fs::write(&path, framed).unwrap();

        assert_eq!(
            import_external_block_file(&mut chain, &path, Network::Regtest, None).unwrap(),
            2
        );
        assert_eq!(chain.height(), 2);
        assert_eq!(chain.best_hash(), second.block_hash());
    }

    #[test]
    fn block_download_timeout_matches_core_parallel_peer_window() {
        let interval = Duration::from_secs(600);
        assert_eq!(core_block_download_timeout(interval, 0), interval);
        assert_eq!(
            core_block_download_timeout(interval, 2),
            Duration::from_secs(1_200)
        );
        assert_eq!(
            core_block_download_timeout(interval, 10),
            Duration::from_secs(3_600)
        );
    }

    #[test]
    fn peer_unknown_block_availability_is_resolved_after_header_arrives() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let (sender, _receiver) = tokio::sync::mpsc::unbounded_channel();
        node.register_peer(1, "192.0.2.1:18444".parse().unwrap(), false, sender);

        let genesis = *node.chain.read().header(0).unwrap();
        let block = mine_test_block(&genesis, 1, 99);
        let hash = block.block_hash();
        node.update_peer_best_known_block(1, hash);
        let before = node
            .peer_infos()
            .into_iter()
            .find(|peer| peer.id == 1)
            .unwrap();
        assert_eq!(before.best_known_block, None);
        assert_eq!(before.last_unknown_block, Some(hash));

        node.chain
            .write()
            .accept_headers(std::slice::from_ref(&block.header))
            .unwrap();
        node.process_peer_block_availability(1);

        let after = node
            .peer_infos()
            .into_iter()
            .find(|peer| peer.id == 1)
            .unwrap();
        assert_eq!(after.best_known_block, Some(hash));
        assert_eq!(after.last_unknown_block, None);
    }

    #[test]
    fn block_download_queue_resumes_from_persisted_headers() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let first = mine_test_block(&node.chain.read().header(0).unwrap().to_owned(), 1, 1);
        let second = mine_test_block(&first.header, 2, 2);
        node.chain
            .write()
            .accept_headers(&[first.header, second.header])
            .unwrap();

        let requests =
            node.next_block_download_requests(16, wire::NODE_NETWORK | wire::NODE_WITNESS);
        assert_eq!(
            requests.iter().map(|item| item.hash).collect::<Vec<_>>(),
            vec![first.block_hash(), second.block_hash()]
        );

        let (sender, _receiver) = tokio::sync::mpsc::unbounded_channel();
        node.register_peer(1, "192.0.2.1:18444".parse().unwrap(), false, sender);
        assert!(node.track_peer_block_request(1, first.block_hash()));
        let remaining =
            node.next_block_download_requests(16, wire::NODE_NETWORK | wire::NODE_WITNESS);
        assert_eq!(remaining.len(), 1);
        assert_eq!(remaining[0].hash, second.block_hash());

        node.unregister_peer(1);
        assert_eq!(
            node.next_block_download_requests(16, wire::NODE_NETWORK)
                .into_iter()
                .map(|item| item.hash)
                .collect::<Vec<_>>(),
            vec![first.block_hash(), second.block_hash()]
        );
    }

    #[test]
    fn block_download_request_reservation_is_global() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let first = mine_test_block(&node.chain.read().header(0).unwrap().to_owned(), 1, 3);
        node.chain
            .write()
            .accept_headers(std::slice::from_ref(&first.header))
            .unwrap();

        let (sender_one, _receiver_one) = tokio::sync::mpsc::unbounded_channel();
        let (sender_two, _receiver_two) = tokio::sync::mpsc::unbounded_channel();
        node.register_peer(1, "192.0.2.1:18444".parse().unwrap(), false, sender_one);
        node.register_peer(2, "192.0.2.2:18444".parse().unwrap(), false, sender_two);

        assert!(node.track_peer_block_request(1, first.block_hash()));
        assert!(!node.track_peer_block_request(2, first.block_hash()));
        node.clear_peer_block_request(1, first.block_hash());
        assert!(node.track_peer_block_request(2, first.block_hash()));
    }

    #[test]
    fn compact_block_request_reservation_allows_three_peers() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let first = mine_test_block(&node.chain.read().header(0).unwrap().to_owned(), 1, 4);
        node.chain
            .write()
            .accept_headers(std::slice::from_ref(&first.header))
            .unwrap();

        let (sender_one, _receiver_one) = tokio::sync::mpsc::unbounded_channel();
        let (sender_two, _receiver_two) = tokio::sync::mpsc::unbounded_channel();
        let (sender_three, _receiver_three) = tokio::sync::mpsc::unbounded_channel();
        let (sender_four, _receiver_four) = tokio::sync::mpsc::unbounded_channel();
        node.register_peer(1, "192.0.2.1:18444".parse().unwrap(), false, sender_one);
        node.register_peer(2, "192.0.2.2:18444".parse().unwrap(), true, sender_two);
        node.register_peer(3, "192.0.2.3:18444".parse().unwrap(), true, sender_three);
        node.register_peer(4, "192.0.2.4:18444".parse().unwrap(), true, sender_four);

        let hash = first.block_hash();
        assert!(node.track_peer_compact_block_request(1, hash));
        assert!(node.track_peer_compact_block_request(2, hash));
        assert!(node.track_peer_compact_block_request(3, hash));
        assert!(!node.track_peer_compact_block_request(4, hash));
        assert!(!node.track_peer_compact_block_request(1, hash));

        node.clear_peer_block_request(1, hash);
        assert!(node.track_peer_compact_block_request(4, hash));
    }

    #[test]
    fn block_download_window_reports_the_peer_stalling_the_next_block() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let first = mine_test_block(&node.chain.read().header(0).unwrap().to_owned(), 1, 1);
        node.chain
            .write()
            .accept_headers(std::slice::from_ref(&first.header))
            .unwrap();

        let (sender, _receiver) = tokio::sync::mpsc::unbounded_channel();
        node.register_peer(1, "192.0.2.1:18444".parse().unwrap(), false, sender.clone());
        node.register_peer(2, "192.0.2.2:18444".parse().unwrap(), false, sender);
        assert!(node.track_peer_block_request(1, first.block_hash()));

        let schedule = node.next_block_download_schedule(
            2,
            MAX_BLOCKS_IN_TRANSIT_PER_PEER,
            wire::NODE_NETWORK | wire::NODE_WITNESS,
        );
        assert!(schedule.requests.is_empty());
        assert_eq!(schedule.staller, Some(1));

        let now = Instant::now();
        node.note_block_staller_at(1, now - BLOCK_STALLING_TIMEOUT_DEFAULT * 2);
        assert_eq!(node.take_stalled_block_peer_at(now), Some(1));
        assert_eq!(
            node.block_stalling_timeout_secs.load(Ordering::Relaxed),
            BLOCK_STALLING_TIMEOUT_DEFAULT.as_secs() * 2
        );
    }

    #[test]
    fn receiving_a_block_clears_the_stalling_timer() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let first = mine_test_block(&node.chain.read().header(0).unwrap().to_owned(), 1, 1);
        node.chain
            .write()
            .accept_headers(std::slice::from_ref(&first.header))
            .unwrap();

        let (sender, _receiver) = tokio::sync::mpsc::unbounded_channel();
        node.register_peer(1, "192.0.2.1:18444".parse().unwrap(), false, sender);
        assert!(node.track_peer_block_request(1, first.block_hash()));
        let now = Instant::now();
        node.note_block_staller_at(1, now - BLOCK_STALLING_TIMEOUT_DEFAULT * 2);
        node.clear_peer_block_request(1, first.block_hash());
        assert_eq!(node.take_stalled_block_peer_at(now), None);
    }

    #[test]
    fn zmq_mempool_sequence_advances_without_subscriber() {
        let directory = tempfile::tempdir().unwrap();
        let mut config = test_config(directory.path());
        config.zmq.pub_sequence = vec!["tcp://127.0.0.1:0".to_owned()];
        let node = Node::open(config).unwrap();
        let initial = node.zmq_mempool_sequence.load(Ordering::Relaxed);

        node.announce_zmq_mempool_added(Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: Vec::new(),
            output: Vec::new(),
        });
        node.announce_zmq_mempool_removed(Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: Vec::new(),
            output: Vec::new(),
        });

        assert_eq!(
            node.zmq_mempool_sequence.load(Ordering::Relaxed),
            initial + 2
        );
    }

    #[test]
    fn median_outbound_time_offset_ignores_inbound_and_unnegotiated_peers() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let (sender, _receiver) = tokio::sync::mpsc::unbounded_channel();
        node.register_peer(1, "192.0.2.1:18444".parse().unwrap(), false, sender.clone());
        node.register_peer(2, "192.0.2.2:18444".parse().unwrap(), false, sender.clone());
        node.register_peer(3, "192.0.2.3:18444".parse().unwrap(), false, sender.clone());
        node.register_peer(4, "192.0.2.4:18444".parse().unwrap(), true, sender);
        let (sender, _receiver) = tokio::sync::mpsc::unbounded_channel();
        node.register_peer(5, "192.0.2.5:18444".parse().unwrap(), false, sender);

        node.update_peer_version(1, 70016, 0, "/one/", 0, true);
        node.update_peer_version(2, 70016, 0, "/two/", 0, true);
        node.update_peer_version(3, 70016, 0, "/three/", 0, true);
        node.update_peer_version(4, 70016, 0, "/inbound/", 0, true);
        node.update_peer_time_offset(1, -10);
        node.update_peer_time_offset(2, 20);
        node.update_peer_time_offset(3, 1);
        node.update_peer_time_offset(4, 500);

        assert_eq!(node.median_outbound_time_offset(), 1);
    }

    #[test]
    fn warning_manager_deduplicates_and_clears_warnings() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();

        node.set_warning(
            NodeWarningKind::FatalInternal,
            "fatal validation error".to_owned(),
        );
        node.set_warning(
            NodeWarningKind::FatalInternal,
            "a newer fatal validation error".to_owned(),
        );
        assert_eq!(node.warning_messages(), vec!["fatal validation error"]);

        node.unset_warning(NodeWarningKind::FatalInternal);
        assert!(node.warning_messages().is_empty());
    }

    #[test]
    fn node_surfaces_an_unknown_versionbits_activation_warning() {
        let directory = tempfile::tempdir().unwrap();
        let mut config = test_config(directory.path());
        config.max_tip_age_secs = u64::MAX;
        let node = Node::open(config).unwrap();

        for height in 1..=431 {
            let previous = *node.chain.read().header(height - 1).unwrap();
            let mut block = mine_test_block(&previous, height, height as u8);
            let mut remine = false;
            let subsidy = validation::block_subsidy_for_network(Network::Regtest, height);
            if block.txdata[0].output[0].value.to_sat() != subsidy {
                block.txdata[0].output[0].value = Amount::from_sat(subsidy);
                block.header.merkle_root = block.compute_merkle_root().unwrap();
                remine = true;
            }
            if (144..=251).contains(&height) {
                block.header.version = BlockVersion::from_consensus(0x2000_0000 | (1 << 27));
                remine = true;
            }
            if remine {
                block.header.nonce = 0;
                while !block.header.target().is_met_by(block.block_hash()) {
                    block.header.nonce = block.header.nonce.wrapping_add(1);
                }
            }
            node.connect_block(block).unwrap();
        }

        assert_eq!(
            node.warning_messages(),
            vec!["Unknown new rules activated (versionbit 27)".to_owned()]
        );
    }

    #[test]
    fn clock_warning_uses_five_outbound_samples_and_recovers() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let (sender, _receiver) = tokio::sync::mpsc::unbounded_channel();

        for id in 1..=5 {
            node.register_peer(
                id,
                format!("192.0.2.{id}:18444").parse().unwrap(),
                false,
                sender.clone(),
            );
            node.update_peer_version(id, 70016, 0, "/test-peer/", 0, true);
            node.update_peer_time_offset(id, 601);
        }
        assert_eq!(node.warning_messages().len(), 1);
        assert!(node.warning_messages()[0].contains("more than 10 minutes"));

        for _ in 0..6 {
            node.update_peer_time_offset(1, 0);
        }
        assert!(node.warning_messages().is_empty());
    }

    #[test]
    fn address_processing_uses_core_style_token_bucket() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let (sender, _receiver) = tokio::sync::mpsc::unbounded_channel();
        node.register_peer(1, "192.0.2.1:18444".parse().unwrap(), true, sender);

        assert!(node.allow_peer_address(1));
        assert!(!node.allow_peer_address(1));
        node.grant_peer_address_tokens(1, 2);
        assert!(node.allow_peer_address(1));
        assert!(node.allow_peer_address(1));

        let peer = node.peer_infos().pop().unwrap();
        assert_eq!(peer.addr_processed, 3);
        assert_eq!(peer.addr_rate_limited, 1);
    }

    #[test]
    fn zmq_mempool_sequence_preserves_confirmed_transaction_gaps() {
        let directory = tempfile::tempdir().unwrap();
        let mut config = test_config(directory.path());
        config.zmq.pub_sequence = vec!["tcp://127.0.0.1:0".to_owned()];
        let node = Node::open(config).unwrap();

        for height in 1..=101 {
            let previous = *node.chain.read().header(height - 1).unwrap();
            node.connect_block(mine_test_block(&previous, height, height as u8))
                .unwrap();
        }
        let mut notifications = node.subscribe_zmq();

        let funding_hash = node.chain.read().block_hash(1).unwrap();
        let funding_block = node.chain.write().block(&funding_hash).unwrap().unwrap();
        let funding = OutPoint::new(funding_block.txdata[0].compute_txid(), 0);
        let first = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: funding,
                script_sig: ScriptBuf::from_bytes(vec![0; 8]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(4_999_999_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        node.accept_transaction(first.clone()).unwrap();
        let first_event = notifications.try_recv().unwrap();
        let zmq::Event::TransactionAdded {
            mempool_sequence, ..
        } = first_event
        else {
            panic!("unexpected first ZMQ event");
        };
        assert!(
            mempool_sequence == 1,
            "first sequence was {mempool_sequence}"
        );

        let previous = *node.chain.read().header(101).unwrap();
        let mut block = mine_test_block(&previous, 102, 102);
        block.txdata.push(first.clone());
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        block.header.nonce = 0;
        while !block.header.target().is_met_by(block.block_hash()) {
            block.header.nonce = block.header.nonce.wrapping_add(1);
        }
        node.connect_block(block).unwrap();
        assert!(matches!(
            notifications.try_recv().unwrap(),
            zmq::Event::BlockConnected(_)
        ));
        assert!(notifications.try_recv().is_err());

        let second = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(first.compute_txid(), 0),
                script_sig: ScriptBuf::from_bytes(vec![0; 8]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(4_999_998_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        node.accept_transaction(second).unwrap();
        assert!(matches!(
            notifications.try_recv().unwrap(),
            zmq::Event::TransactionAdded {
                mempool_sequence: 3,
                ..
            }
        ));
    }

    fn mine_test_block(previous: &Header, height: u32, tag: u8) -> Block {
        let mut block = Block {
            header: Header {
                version: BlockVersion::from_consensus(4),
                prev_blockhash: previous.block_hash(),
                merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                time: previous.time + 1,
                bits: previous.bits,
                nonce: 0,
            },
            txdata: vec![Transaction {
                version: Version::ONE,
                lock_time: LockTime::ZERO,
                input: vec![TxIn {
                    previous_output: OutPoint::null(),
                    script_sig: Builder::new()
                        .push_int(i64::from(height))
                        .push_slice([tag])
                        .push_slice([0u8])
                        .into_script(),
                    sequence: bitcoin::Sequence::MAX,
                    witness: Witness::default(),
                }],
                output: vec![TxOut {
                    value: Amount::from_sat(5_000_000_000),
                    script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
                }],
            }],
        };
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        while !block.header.target().is_met_by(block.block_hash()) {
            block.header.nonce = block.header.nonce.wrapping_add(1);
        }
        block
    }

    #[test]
    fn peer_orphans_are_promoted_recursively_when_the_parent_arrives() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        for height in 1..=101 {
            let previous = *node.chain.read().header(height - 1).unwrap();
            node.connect_block(mine_test_block(&previous, height, height as u8))
                .unwrap();
        }

        let funding_block_hash = node.chain.read().block_hash(1).unwrap();
        let funding_block = node
            .chain
            .write()
            .block(&funding_block_hash)
            .unwrap()
            .unwrap();
        let funding = OutPoint::new(funding_block.txdata[0].compute_txid(), 0);
        let parent = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: funding,
                script_sig: ScriptBuf::from_bytes(vec![0x00; 8]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(4_999_999_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let child = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(parent.compute_txid(), 0),
                script_sig: ScriptBuf::from_bytes(vec![0x00; 8]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(4_999_998_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let grandchild = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(child.compute_txid(), 0),
                script_sig: ScriptBuf::from_bytes(vec![0x00; 8]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(4_999_997_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };

        assert!(node.accept_peer_transaction(grandchild.clone()).is_err());
        assert!(node.accept_peer_transaction(child.clone()).is_err());
        assert_eq!(node.orphan_count(), 2);
        assert!(node.mempool.read().get(&child.compute_txid()).is_none());
        assert!(
            node.mempool
                .read()
                .get(&grandchild.compute_txid())
                .is_none()
        );

        let expected_parent_txid = parent.compute_txid();
        let parent_txid = node.accept_transaction(parent).unwrap();
        let mempool = node.mempool.read();
        assert_eq!(parent_txid, expected_parent_txid);
        assert!(mempool.get(&expected_parent_txid).is_some());
        assert!(mempool.get(&child.compute_txid()).is_some());
        assert!(mempool.get(&grandchild.compute_txid()).is_some());
        assert_eq!(node.orphan_count(), 0);
    }

    #[test]
    fn invalidate_and_reconsider_restore_disconnected_transactions() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let transaction = private_broadcast_test_transaction(&node);
        let txid = transaction.compute_txid();
        node.accept_transaction(transaction.clone()).unwrap();

        let previous = *node.chain.read().header(101).unwrap();
        let mut block = mine_test_block(&previous, 102, 102);
        block.txdata.push(transaction);
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        while !block.header.target().is_met_by(block.block_hash()) {
            block.header.nonce = block.header.nonce.wrapping_add(1);
        }
        let block_hash = block.block_hash();
        node.connect_block(block).unwrap();
        assert!(node.mempool.read().get(&txid).is_none());

        node.invalidate_block(block_hash).unwrap();
        assert_eq!(node.chain.read().height(), 101);
        assert!(node.mempool.read().get(&txid).is_some());

        node.reconsider_block(block_hash).unwrap();
        assert_eq!(node.chain.read().height(), 102);
        assert!(node.mempool.read().get(&txid).is_none());
    }

    #[test]
    fn invalidation_resurrects_transactions_in_core_disconnect_order() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let parent = private_broadcast_test_transaction(&node);
        let parent_txid = parent.compute_txid();
        let child = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(parent_txid, 0),
                script_sig: ScriptBuf::from_bytes(vec![0; 8]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(4_999_998_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let child_txid = child.compute_txid();

        let previous = *node.chain.read().header(101).unwrap();
        let mut parent_block = mine_test_block(&previous, 102, 102);
        parent_block.txdata.push(parent);
        parent_block.header.merkle_root = parent_block.compute_merkle_root().unwrap();
        while !parent_block
            .header
            .target()
            .is_met_by(parent_block.block_hash())
        {
            parent_block.header.nonce = parent_block.header.nonce.wrapping_add(1);
        }
        let parent_block_hash = parent_block.block_hash();
        let parent_block_header = parent_block.header;
        node.connect_block(parent_block).unwrap();

        let mut child_block = mine_test_block(&parent_block_header, 103, 103);
        child_block.txdata.push(child);
        child_block.header.merkle_root = child_block.compute_merkle_root().unwrap();
        while !child_block
            .header
            .target()
            .is_met_by(child_block.block_hash())
        {
            child_block.header.nonce = child_block.header.nonce.wrapping_add(1);
        }
        node.connect_block(child_block).unwrap();

        node.invalidate_block(parent_block_hash).unwrap();
        let mempool = node.mempool.read();
        assert!(mempool.get(&parent_txid).is_some());
        assert!(mempool.get(&child_txid).is_some());
    }

    #[test]
    fn deep_invalidation_skips_transactions_older_than_core_limit() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let transaction = private_broadcast_test_transaction(&node);
        let txid = transaction.compute_txid();

        let previous = *node.chain.read().header(101).unwrap();
        let mut first = mine_test_block(&previous, 102, 102);
        first.txdata.push(transaction);
        first.header.merkle_root = first.compute_merkle_root().unwrap();
        while !first.header.target().is_met_by(first.block_hash()) {
            first.header.nonce = first.header.nonce.wrapping_add(1);
        }
        let first_hash = first.block_hash();
        let mut previous = first.header;
        node.connect_block(first).unwrap();
        for height in 103..=113 {
            let block = mine_test_block(&previous, height, height as u8);
            previous = block.header;
            node.connect_block(block).unwrap();
        }

        node.invalidate_block(first_hash).unwrap();
        assert_eq!(node.chain.read().height(), 101);
        assert!(node.mempool.read().get(&txid).is_none());
    }

    #[test]
    fn precious_block_reorg_emits_a_chain_event() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let main_one = mine_test_block(&node.chain.read().header(0).unwrap().to_owned(), 1, 1);
        node.connect_block(main_one).unwrap();
        let main_two = mine_test_block(&node.chain.read().header(1).unwrap().to_owned(), 2, 2);
        node.connect_block(main_two).unwrap();

        let genesis = node.chain.read().header(0).unwrap().to_owned();
        let side_one = mine_test_block(&genesis, 1, 3);
        let side_one_header = side_one.header;
        node.connect_block(side_one).unwrap();
        let side_two = mine_test_block(&side_one_header, 2, 4);
        let side_two_hash = side_two.block_hash();
        node.connect_block(side_two).unwrap();
        assert_ne!(node.chain.read().best_hash(), side_two_hash);

        let mut events = node.subscribe_chain();
        node.precious_block(side_two_hash).unwrap();
        assert_eq!(node.chain.read().best_hash(), side_two_hash);
        assert_eq!(events.try_recv().unwrap().hash, side_two_hash);
    }

    #[test]
    fn reconsider_block_clears_invalid_ancestors() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let main_one = mine_test_block(&node.chain.read().header(0).unwrap().to_owned(), 1, 1);
        node.connect_block(main_one).unwrap();
        let main_two = mine_test_block(&node.chain.read().header(1).unwrap().to_owned(), 2, 2);
        node.connect_block(main_two).unwrap();

        let genesis = node.chain.read().header(0).unwrap().to_owned();
        let side_one = mine_test_block(&genesis, 1, 3);
        let side_one_hash = side_one.block_hash();
        let side_one_header = side_one.header;
        node.connect_block(side_one).unwrap();
        let side_two = mine_test_block(&side_one_header, 2, 4);
        let side_two_header = side_two.header;
        node.connect_block(side_two).unwrap();
        let side_three = mine_test_block(&side_two_header, 3, 5);
        let side_three_hash = side_three.block_hash();
        node.connect_block(side_three).unwrap();
        assert_eq!(node.chain.read().best_hash(), side_three_hash);

        node.invalidate_block(side_one_hash).unwrap();
        assert_eq!(node.chain.read().height(), 2);

        node.reconsider_block(side_three_hash).unwrap();
        assert_eq!(node.chain.read().best_hash(), side_three_hash);
    }

    #[test]
    fn discovered_addresses_survive_a_restart() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let address = "[2001:db8::42]:18444".parse().unwrap();
        node.remember_address(address, crate::wire::NODE_NETWORK, 123);
        node.persist_known_addresses().unwrap();
        drop(node);

        let reopened = Node::open(test_config(directory.path())).unwrap();
        let peer = reopened
            .known_addresses()
            .into_iter()
            .find(|peer| peer.address == address)
            .expect("persisted address");
        assert_eq!(peer.id, UNCONNECTED_PEER_ID);
        assert_eq!(peer.services, crate::wire::NODE_NETWORK);
        assert_eq!(peer.connected_at, 123);
    }

    #[test]
    fn block_relay_only_anchors_use_native_storage_and_are_consumed_on_restart() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let first = NetworkEndpoint::from_socket("203.0.113.1:18444".parse().unwrap());
        let second = NetworkEndpoint::from_socket("203.0.113.2:18444".parse().unwrap());
        let third = NetworkEndpoint::from_socket("203.0.113.3:18444".parse().unwrap());
        let inbound = NetworkEndpoint::from_socket("203.0.113.4:18444".parse().unwrap());
        let (sender, _receiver) = tokio::sync::mpsc::unbounded_channel();
        for (id, endpoint, connection_type, inbound) in [
            (1, first.clone(), "block-relay-only", false),
            (2, second.clone(), "block-relay-only", false),
            (3, third, "block-relay-only", false),
            (4, inbound, "inbound", true),
        ] {
            node.register_peer_with_endpoint(
                id,
                endpoint,
                inbound,
                sender.clone(),
                PeerRegistrationOptions {
                    local_address: None,
                    permissions: PeerPermissions::empty(),
                    connection_type,
                    manual: false,
                    forced_inbound: false,
                },
            );
        }

        let anchors = node.current_block_relay_only_anchors();
        assert_eq!(anchors, vec![first.clone(), second.clone()]);
        node.persist_block_relay_only_anchors(&anchors).unwrap();
        let anchors_path = directory.path().join("regtest/anchors.json");
        assert!(anchors_path.is_file());
        assert!(!directory.path().join("regtest/anchors.dat").exists());
        drop(node);

        let reopened = Node::open(test_config(directory.path())).unwrap();
        assert_eq!(reopened.take_block_relay_only_anchors(2), anchors);
        assert!(!anchors_path.exists());
    }

    #[test]
    fn stale_tip_maintenance_matches_core_timer_boundaries() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let genesis_time = u64::from(node.chain.read().header(0).unwrap().time);
        let now = genesis_time + 1_000;

        // The first pass initializes the tip timestamp and enables the
        // post-IBD extra block-relay mechanism once direct fetch is possible.
        node.check_for_stale_tip_and_evict_peers(now, 8, 2);
        assert_eq!(node.last_tip_update.load(Ordering::Acquire), now);
        assert!(!node.extra_full_outbound_requested());
        assert!(node.extra_block_relay_peers_enabled.load(Ordering::Acquire));
        assert!(!node.extra_block_relay_attempt_due(now));
        assert!(!node.extra_block_relay_attempt_due(now + 299));
        assert!(node.extra_block_relay_attempt_due(now + 300));
        assert!(node.claim_extra_block_relay_attempt(now + 300));
        assert!(!node.extra_block_relay_attempt_due(now + 300));

        // A regtest tip is stale after three proof-of-work spacings, and the
        // stale check itself is no more frequent than ten minutes.
        node.last_tip_update
            .store(now.saturating_sub(2_000), Ordering::Release);
        node.stale_tip_check_at
            .store(now + STALE_TIP_CHECK_INTERVAL_SECS, Ordering::Release);
        node.check_for_stale_tip_and_evict_peers(now + STALE_TIP_CHECK_INTERVAL_SECS, 8, 2);
        assert!(node.extra_full_outbound_requested());
    }

    #[test]
    fn address_manager_sources_survive_a_restart() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let endpoint = NetworkEndpoint::Ip("192.0.2.42:18444".parse().unwrap());
        let source = NetworkEndpoint::Ip("198.51.100.7:18444".parse().unwrap());

        assert!(node.remember_network_address_from(
            endpoint.clone(),
            crate::wire::NODE_NETWORK,
            123,
            source.clone(),
        ));
        assert_eq!(node.network_address_source(&endpoint), source);
        node.persist_known_addresses().unwrap();
        drop(node);

        let reopened = Node::open(test_config(directory.path())).unwrap();
        assert_eq!(reopened.network_address_source(&endpoint), source);
    }

    #[test]
    fn address_manager_secret_survives_a_restart() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let key = *node.addrman_hash_key();
        assert!(directory.path().join(ADDRMAN_SECRET_FILE).is_file());
        drop(node);

        let reopened = Node::open(test_config(directory.path())).unwrap();
        assert_eq!(*reopened.addrman_hash_key(), key);
    }

    #[test]
    fn private_broadcast_peers_do_not_mutate_addrman() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let address = "192.0.2.42:18444".parse().unwrap();
        node.remember_address(address, 0, 123);
        let (sender, _receiver) = tokio::sync::mpsc::unbounded_channel();
        node.register_peer_with_endpoint(
            7,
            NetworkEndpoint::from_socket(address),
            false,
            sender,
            PeerRegistrationOptions {
                local_address: None,
                permissions: PeerPermissions::empty(),
                connection_type: "private-broadcast",
                manual: false,
                forced_inbound: false,
            },
        );
        node.update_peer_version(7, 70016, crate::wire::NODE_NETWORK, "/peer/", 1, true);

        let known = node
            .known_addresses()
            .into_iter()
            .find(|peer| peer.address == address)
            .expect("known endpoint remains present");
        assert_eq!(known.services, 0);
        assert!(!node.is_address_tried(address));
        node.unregister_peer(7);
    }

    #[test]
    fn addrman_consistency_checks_ip_and_network_tables() {
        let directory = tempfile::tempdir().unwrap();
        let mut config = test_config(directory.path());
        config.check_addrman = 1;
        let node = Node::open(config).unwrap();
        let address = "192.0.2.42:18444".parse().unwrap();
        let onion = NetworkEndpoint::OnionV3 {
            address: [6; 32],
            port: 18444,
        };

        node.remember_address(address, crate::wire::NODE_NETWORK, 123);
        node.remember_network_address(onion.clone(), crate::wire::NODE_NETWORK, 124);
        node.network_tried_addresses.write().insert(onion.clone());
        node.check_addrman_consistency().unwrap();

        node.tried_addresses
            .write()
            .insert("198.51.100.1:18444".parse().unwrap());
        assert!(node.check_addrman_consistency().is_err());
    }

    #[test]
    fn non_ip_addresses_survive_a_restart_with_network_identity() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(test_config(directory.path())).unwrap();
        let onion = NetworkEndpoint::OnionV3 {
            address: [4; 32],
            port: 18444,
        };
        let i2p = NetworkEndpoint::I2p {
            address: [5; 32],
            port: 0,
        };
        let cjdns = NetworkEndpoint::Cjdns {
            address: "fc00::42".parse().unwrap(),
            port: 18446,
        };
        assert!(node.remember_network_address(onion.clone(), 1, 100));
        assert!(node.remember_network_address(i2p.clone(), 2, 101));
        assert!(node.remember_network_address(cjdns.clone(), 4, 102));
        node.network_tried_addresses.write().insert(i2p.clone());
        node.persist_known_addresses().unwrap();
        drop(node);

        let reopened = Node::open(test_config(directory.path())).unwrap();
        let addresses = reopened.known_network_addresses();
        assert!(addresses.iter().any(|entry| entry.endpoint == onion));
        assert!(addresses.iter().any(|entry| entry.endpoint == i2p));
        assert!(addresses.iter().any(|entry| entry.endpoint == cjdns));
        assert!(reopened.is_network_address_tried(&i2p));
    }

    #[test]
    fn disabled_mempool_persistence_skips_loading_the_disk_file() {
        let directory = tempfile::tempdir().unwrap();
        let mempool_path = directory.path().join("mempool.json");
        std::fs::write(&mempool_path, b"not-json").unwrap();
        let mut config = test_config(directory.path());
        config.persist_mempool = false;

        let node = Node::open(config).unwrap();

        assert!(node.mempool.read().is_empty());
        assert_eq!(std::fs::read(&mempool_path).unwrap(), b"not-json");
    }

    #[test]
    fn corrupt_peer_and_ban_state_is_quarantined_on_restart() {
        let directory = tempfile::tempdir().unwrap();
        fs::write(directory.path().join("peers.json"), b"not-json").unwrap();
        let network_directory = directory.path().join("regtest");
        fs::create_dir_all(&network_directory).unwrap();
        fs::write(network_directory.join("banlist.json"), b"not-json").unwrap();
        fs::write(network_directory.join("anchors.json"), b"not-json").unwrap();

        let node = Node::open(test_config(directory.path())).unwrap();

        assert!(node.known_addresses().is_empty());
        assert!(node.banned_addresses().is_empty());
        assert!(!directory.path().join("peers.json").exists());
        assert!(!network_directory.join("banlist.json").exists());
        assert!(!network_directory.join("anchors.json").exists());
        assert!(directory.path().join("peers.json.corrupt").exists());
        assert!(network_directory.join("banlist.json.corrupt").exists());
        assert!(network_directory.join("anchors.json.corrupt").exists());
    }
}
