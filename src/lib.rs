#![forbid(unsafe_code)]
#![warn(rust_2018_idioms, clippy::all)]

pub mod address;
pub mod asmap;
pub mod chain;
pub mod config;
pub mod electrum;
pub mod fee_estimator;
pub mod i2p;
pub mod mempool;
pub mod muhash;
pub mod p2p;
pub mod portmap;
pub mod rpc;
pub mod storage;
pub mod time;
pub mod tor;
pub mod validation;
pub mod wire;
pub mod zmq;

use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::{self, File, OpenOptions};
use std::io::Write;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};
use std::path::Path;
use std::process::Command;
use std::sync::{
    Arc,
    atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering},
};
use std::time::{Duration, Instant};

use anyhow::{Context, Result, bail};
use bitcoin::consensus::encode::deserialize;
use bitcoin::hashes::Hash;
use bitcoin::{Block, BlockHash, Network, OutPoint, Transaction, Txid, Wtxid};
use fs2::FileExt;
use parking_lot::{Mutex, RwLock};
use rand::random;
use serde::de::{self, Deserializer, MapAccess, Visitor};
use serde::{Deserialize, Serialize};
use tokio::sync::{Notify, broadcast, oneshot};
use tracing::{info, warn};

use crate::address::NetworkEndpoint;
use crate::asmap::AsMap;
use crate::chain::ChainState;
use crate::config::{Config, PeerPermissions, RpcCookiePermissions};
use crate::fee_estimator::{FeeEstimator, RawFeeEstimate};
use crate::mempool::{
    Mempool, MempoolChange, MempoolChangeKind, MempoolError, MempoolLoadOptions, MempoolPolicy,
};

const MAX_ORPHAN_TRANSACTIONS: usize = 100;
const MAX_ORPHAN_TRANSACTION_WEIGHT: u64 = 400_000;
const ORPHAN_TRANSACTION_EXPIRY: Duration = Duration::from_secs(20 * 60);
const MAX_KNOWN_ADDRESSES: usize = 256_000;
pub(crate) const MAX_BLOCKS_IN_TRANSIT_PER_PEER: usize = 16;
const BLOCK_STALLING_TIMEOUT_DEFAULT: Duration = Duration::from_secs(2);
const BLOCK_STALLING_TIMEOUT_MAX: Duration = Duration::from_secs(64);
const MAX_ADDR_RATE_PER_SECOND: f64 = 0.1;
const MAX_ADDR_PROCESSING_TOKEN_BUCKET: f64 = 1_000.0;
const MEMPOOL_EXPIRY_INTERVAL: Duration = Duration::from_secs(60);
const FEE_ESTIMATOR_FLUSH_INTERVAL: Duration = Duration::from_secs(60 * 60);
const MAX_EXTERNAL_BLOCK_RECORD_SIZE: usize = 4 * 1024 * 1024;
const MAX_UPLOAD_TIMEFRAME_SECS: u64 = 24 * 60 * 60;
const MAX_UPLOAD_BLOCK_RESERVE_BYTES: u64 = 4_000_000;
const HISTORICAL_BLOCK_AGE_SECS: u64 = 7 * 24 * 60 * 60;
const MAX_TIME_OFFSET_SAMPLES: usize = 50;
const CLOCK_OUT_OF_SYNC_THRESHOLD_SECS: u64 = 10 * 60;
pub(crate) const PRIVATE_BROADCAST_PEERS_PER_TRANSACTION: usize = 3;
pub(crate) const PRIVATE_BROADCAST_RETRY_SECS: u64 = 60;

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

fn import_external_block_file(
    chain: &mut ChainState,
    path: &Path,
    network: Network,
) -> Result<usize> {
    let bytes = fs::read(path).with_context(|| format!("reading block file {}", path.display()))?;
    let magic = wire::network_magic(network);
    let mut offset = 0usize;
    let mut blocks = Vec::new();
    while offset < bytes.len() {
        let remaining = bytes.len().saturating_sub(offset);
        if remaining < 8 {
            bail!(
                "block file {} ends with an incomplete record header",
                path.display()
            );
        }
        if bytes[offset..offset + 4] != magic {
            bail!(
                "block file {} has unexpected network magic at offset {}",
                path.display(),
                offset
            );
        }
        let length = u32::from_le_bytes(
            bytes[offset + 4..offset + 8]
                .try_into()
                .expect("record header has four length bytes"),
        ) as usize;
        if length == 0 || length > MAX_EXTERNAL_BLOCK_RECORD_SIZE {
            bail!(
                "block file {} contains an invalid block length {}",
                path.display(),
                length
            );
        }
        let record_start = offset.saturating_add(8);
        let record_end = record_start.saturating_add(length);
        if record_end > bytes.len() {
            bail!("block file {} ends with a truncated block", path.display());
        }
        let block: Block = deserialize(&bytes[record_start..record_end]).with_context(|| {
            format!("decoding block at offset {} in {}", offset, path.display())
        })?;
        blocks.push(block);
        offset = record_end;
    }

    let mut pending = blocks;
    let mut imported = 0usize;
    while !pending.is_empty() {
        let mut remaining = Vec::new();
        let mut progress = false;
        for block in pending {
            let hash = block.block_hash();
            if chain.header_by_hash(&hash).is_some() && chain.block(&hash)?.is_some() {
                continue;
            }
            let parent_hash = block.header.prev_blockhash;
            if chain.header_by_hash(&parent_hash).is_none() || chain.block(&parent_hash)?.is_none()
            {
                remaining.push(block);
                continue;
            }
            chain
                .connect_block(block)
                .with_context(|| format!("connecting block {hash} from {}", path.display()))?;
            imported = imported.saturating_add(1);
            progress = true;
        }
        if !remaining.is_empty() && !progress {
            let block = &remaining[0];
            bail!(
                "block file {} contains block {} with an unknown or unavailable parent {}",
                path.display(),
                block.block_hash(),
                block.header.prev_blockhash
            );
        }
        pending = remaining;
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
    added_at: Instant,
    announcers: HashSet<usize>,
}

#[derive(Default)]
struct OrphanPool {
    entries: HashMap<Txid, OrphanEntry>,
    by_prevout: HashMap<OutPoint, HashSet<Txid>>,
    insertion_order: VecDeque<Txid>,
}

impl OrphanPool {
    fn add(&mut self, transaction: Transaction, peer_id: Option<usize>) -> bool {
        let announcers = peer_id.into_iter().collect();
        self.add_entry(OrphanEntry {
            transaction,
            added_at: Instant::now(),
            announcers,
        })
    }

    fn add_entry(&mut self, entry: OrphanEntry) -> bool {
        self.prune_expired();
        let txid = entry.transaction.compute_txid();
        if let Some(existing) = self.entries.get_mut(&txid) {
            existing.announcers.extend(entry.announcers);
            return false;
        }
        if entry.transaction.weight().to_wu() > MAX_ORPHAN_TRANSACTION_WEIGHT
            || entry.added_at.elapsed() >= ORPHAN_TRANSACTION_EXPIRY
        {
            return false;
        }
        for input in &entry.transaction.input {
            self.by_prevout
                .entry(input.previous_output)
                .or_default()
                .insert(txid);
        }
        self.entries.insert(txid, entry);
        self.insertion_order.push_back(txid);
        while self.entries.len() > MAX_ORPHAN_TRANSACTIONS {
            let Some(oldest) = self.insertion_order.pop_front() else {
                break;
            };
            self.remove(&oldest);
        }
        true
    }

    fn remove(&mut self, txid: &Txid) -> Option<OrphanEntry> {
        let entry = self.entries.remove(txid)?;
        for input in &entry.transaction.input {
            if let Some(children) = self.by_prevout.get_mut(&input.previous_output) {
                children.remove(txid);
                if children.is_empty() {
                    self.by_prevout.remove(&input.previous_output);
                }
            }
        }
        Some(entry)
    }

    fn take_children(&mut self, parent: &Transaction) -> Vec<OrphanEntry> {
        self.prune_expired();
        let parent_txid = parent.compute_txid();
        let mut txids = HashSet::new();
        for vout in 0..parent.output.len() {
            let outpoint = OutPoint::new(parent_txid, vout as u32);
            if let Some(children) = self.by_prevout.get(&outpoint) {
                txids.extend(children.iter().copied());
            }
        }
        let mut txids: Vec<_> = txids.into_iter().collect();
        txids.sort_by_key(ToString::to_string);
        txids
            .into_iter()
            .filter_map(|txid| self.remove(&txid))
            .collect()
    }

    fn erase_for_peer(&mut self, peer_id: usize) {
        let txids: Vec<_> = self
            .entries
            .iter()
            .filter_map(|(txid, entry)| entry.announcers.contains(&peer_id).then_some(*txid))
            .collect();
        for txid in txids {
            self.remove(&txid);
        }
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
                }
            })
            .collect::<Vec<_>>();
        transactions.sort_by_key(|entry| entry.transaction.compute_txid().to_string());
        transactions
    }

    fn erase_for_block(&mut self, block: &Block) {
        let mut txids = HashSet::new();
        for transaction in &block.txdata {
            let transaction_id = transaction.compute_txid();
            if self.entries.contains_key(&transaction_id) {
                txids.insert(transaction_id);
            }
            for input in &transaction.input {
                if let Some(children) = self.by_prevout.get(&input.previous_output) {
                    txids.extend(children.iter().copied());
                }
            }
        }
        for txid in txids {
            self.remove(&txid);
        }
    }

    fn len(&mut self) -> usize {
        self.prune_expired();
        self.entries.len()
    }

    fn prune_expired(&mut self) {
        let now = Instant::now();
        while let Some(txid) = self.insertion_order.front().copied() {
            let expired = self.entries.get(&txid).is_none_or(|entry| {
                now.duration_since(entry.added_at) >= ORPHAN_TRANSACTION_EXPIRY
            });
            if !expired {
                break;
            }
            self.insertion_order.pop_front();
            self.remove(&txid);
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
    pub bytes_sent_per_msg: HashMap<String, u64>,
    pub bytes_received_per_msg: HashMap<String, u64>,
    pub last_inv_sequence: u64,
    pub inv_to_send: usize,
    pub last_transaction: u64,
    pub last_block: u64,
    pub(crate) best_known_block: Option<BlockHash>,
    pub(crate) last_common_block: Option<BlockHash>,
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
    addr_token_bucket: f64,
    addr_token_timestamp: Instant,
    ping_nonce: Option<u64>,
    ping_sent_at: Option<Instant>,
}

pub(crate) struct PeerRegistrationOptions {
    pub(crate) local_address: Option<SocketAddr>,
    pub(crate) permissions: PeerPermissions,
    pub(crate) connection_type: &'static str,
}

/// Address-manager metadata for an endpoint that may not be connected yet.
#[derive(Clone, Debug)]
pub struct KnownNetworkAddress {
    pub endpoint: NetworkEndpoint,
    pub services: u64,
    pub time: u64,
}

#[derive(Clone, Debug)]
struct InflightBlock {
    hash: BlockHash,
    height: u32,
    requested_at: Instant,
}

pub(crate) struct BlockDownloadSchedule {
    pub(crate) requests: Vec<wire::Inventory>,
    pub(crate) staller: Option<usize>,
}

impl PeerInfo {
    pub(crate) fn ping_wait(&self) -> Option<f64> {
        self.ping_sent_at
            .map(|sent_at| sent_at.elapsed().as_secs_f64())
    }

    pub(crate) fn inflight_heights(&self) -> Vec<u32> {
        self.inflight_blocks
            .iter()
            .map(|block| block.height)
            .collect()
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct IpSubnet {
    address: IpAddr,
    prefix: u8,
}

impl IpSubnet {
    pub(crate) fn parse(value: &str) -> Result<Self> {
        let mut parts = value.split('/');
        let address = parts
            .next()
            .ok_or_else(|| anyhow::anyhow!("invalid IP/Subnet"))?
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

    pub(crate) fn contains_subnet(self, subnet: Self) -> bool {
        self.prefix <= subnet.prefix && self.contains(subnet.address)
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

#[derive(Clone, Debug, Deserialize, Serialize)]
struct PersistedBannedAddress {
    address: IpAddr,
    #[serde(default)]
    prefix: Option<u8>,
    ban_created: u64,
    ban_until: u64,
    reason: String,
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
}

type LoadedAddressState = (
    HashMap<SocketAddr, PeerInfo>,
    HashSet<SocketAddr>,
    HashMap<NetworkEndpoint, KnownNetworkAddress>,
    HashSet<NetworkEndpoint>,
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

/// The wallet-free node facade shared by the network and RPC services.
pub struct Node {
    pub config: Config,
    _data_dir_lock: File,
    _blocks_dir_lock: Option<File>,
    asmap: Option<Arc<AsMap>>,
    pub chain: Arc<RwLock<ChainState>>,
    pub mempool: Arc<RwLock<Mempool>>,
    pub events: broadcast::Sender<ChainEvent>,
    pub mempool_events: broadcast::Sender<MempoolEvent>,
    peer_mempool_events: broadcast::Sender<PeerMempoolEvent>,
    pub(crate) zmq_events: broadcast::Sender<zmq::Event>,
    pub(crate) txout_scan: Arc<ScanState>,
    pub(crate) blockfilter_scan: Arc<ScanState>,
    pub rpc_cookie: Option<String>,
    pub(crate) i2p_sam: Option<Arc<i2p::I2pSam>>,
    pub(crate) tor_controller: Option<Arc<tor::TorController>>,
    mempool_path: std::path::PathBuf,
    pub peer_count: AtomicUsize,
    mempool_check_operations: AtomicUsize,
    block_index_check_operations: AtomicUsize,
    addrman_check_operations: AtomicUsize,
    zmq_mempool_sequence: AtomicU64,
    rpc_command_sequence: AtomicUsize,
    rpc_commands: parking_lot::RwLock<HashMap<usize, (String, Instant)>>,
    total_bytes_sent: AtomicU64,
    total_bytes_received: AtomicU64,
    outbound_usage: parking_lot::Mutex<OutboundUsage>,
    network_active: AtomicBool,
    block_stalling_timeout_secs: AtomicU64,
    block_stalling_since: parking_lot::RwLock<HashMap<usize, Instant>>,
    shutdown_requested: AtomicBool,
    peers: parking_lot::RwLock<HashMap<usize, PeerInfo>>,
    peer_commands:
        parking_lot::RwLock<HashMap<usize, tokio::sync::mpsc::UnboundedSender<p2p::PeerCommand>>>,
    peer_manager_requests:
        parking_lot::RwLock<Option<tokio::sync::mpsc::UnboundedSender<p2p::PeerManagerRequest>>>,
    private_broadcasts: parking_lot::Mutex<HashMap<Wtxid, PrivateBroadcastEntry>>,
    compact_extra_transactions: parking_lot::Mutex<CompactExtraTransactions>,
    orphans: parking_lot::Mutex<OrphanPool>,
    known_addresses: parking_lot::RwLock<HashMap<SocketAddr, PeerInfo>>,
    tried_addresses: parking_lot::RwLock<HashSet<SocketAddr>>,
    network_addresses: parking_lot::RwLock<HashMap<NetworkEndpoint, KnownNetworkAddress>>,
    network_tried_addresses: parking_lot::RwLock<HashSet<NetworkEndpoint>>,
    added_nodes: parking_lot::RwLock<HashMap<NetworkEndpoint, Option<bool>>>,
    added_node_names: parking_lot::RwLock<HashMap<NetworkEndpoint, String>>,
    banned_addresses: parking_lot::RwLock<HashMap<IpSubnet, BannedAddress>>,
    listen_address: parking_lot::RwLock<Option<SocketAddr>>,
    listen_addresses: parking_lot::RwLock<Vec<SocketAddr>>,
    mapped_addresses: parking_lot::RwLock<Vec<SocketAddr>>,
    listen_network_addresses: parking_lot::RwLock<Vec<NetworkEndpoint>>,
    last_mining_block: parking_lot::RwLock<Option<(u64, usize)>>,
    time_offset_samples: parking_lot::RwLock<VecDeque<i64>>,
    warnings: parking_lot::RwLock<Vec<NodeWarning>>,
    versionbits_warning_scanned: AtomicBool,
    fee_estimator: Mutex<FeeEstimator>,
    pub started_at: Instant,
    shutdown: Notify,
}

impl Node {
    pub fn open(config: Config) -> Result<Arc<Self>> {
        fs::create_dir_all(&config.datadir)
            .with_context(|| format!("creating data directory {}", config.datadir.display()))?;
        let lock_path = config.datadir.join(".lock");
        let data_dir_lock = OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .truncate(false)
            .open(&lock_path)
            .with_context(|| format!("opening data directory lock {}", lock_path.display()))?;
        data_dir_lock.try_lock_exclusive().with_context(|| {
            format!(
                "data directory is already in use: {}",
                config.datadir.display()
            )
        })?;
        let blocks_dir = config
            .blocks_dir
            .clone()
            .unwrap_or_else(|| config.datadir.join("blocks"));
        if config.blocks_dir_explicit && !blocks_dir.is_dir() {
            bail!(
                "specified blocks directory does not exist: {}",
                blocks_dir.display()
            );
        }
        if !config.blocks_dir_explicit {
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
            lock.try_lock_exclusive().with_context(|| {
                format!(
                    "blocks directory is already in use: {}",
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
            .map(AsMap::from_file)
            .transpose()?
            .map(Arc::new);
        if let Some(asmap) = &asmap {
            info!(
                version = %asmap.version_hex(),
                "Using ASMap for IP bucketing"
            );
        }
        if let Some(mock_time) = config.mock_time {
            time::set_mock_time(mock_time);
        }
        let network_active = config.network_active;
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
        let mut chain =
            ChainState::open_with_options_and_tx_index_in_dirs_with_minimum_chain_work_and_assume_valid_and_blocks_xor(
                config.network,
                &config.datadir,
                blocks_dir,
                config.signet_challenge.as_deref(),
                config.blockfilterindex,
                config.reindex,
                config.reindex_chainstate,
                config.txindex,
                config.minimum_chain_work,
                config.assume_valid,
                config.blocks_xor,
            )?;
        chain.configure_max_tip_age(config.max_tip_age_secs);
        chain.configure_script_check_threads(config.script_check_threads);
        chain.configure_script_cache_size_mib(config.max_sig_cache_mib);
        chain.configure_prune_after_height(config.network, config.fast_prune);
        chain.configure_pruning(config.prune)?;
        // Electrum 1.7 outpoint status needs confirmed spender lookups even
        // when the standalone Core-style txospenderindex RPC option is off.
        // Keep this internal index enabled for Electrum without changing the
        // user-facing getindexinfo reporting for that optional index.
        chain
            .configure_txospender_index(config.txospenderindex || config.electrum_bind.is_some())?;
        chain.configure_coinstats_index(config.coinstatsindex)?;
        for path in &config.load_blocks {
            import_external_block_file(&mut chain, path, config.network)?;
        }
        chain.maybe_auto_prune()?;
        if config.check_blocks.is_some() || config.check_level.is_some() {
            let check_blocks = config.check_blocks.unwrap_or(6);
            let check_level = config.check_level.unwrap_or(3);
            chain
                .verify_active_chain_with_level(check_level, check_blocks)
                .context("startup block verification failed")?;
        }
        let mempool_path = config.datadir.join("mempool.dat");
        let fee_estimator_path = config.datadir.join("fee_estimates.dat");
        let mempool_policy = MempoolPolicy {
            min_relay_fee_sat_per_kvb: config.min_relay_tx_fee_sat_per_kvb,
            incremental_relay_fee_sat_per_kvb: config.incremental_relay_fee_sat_per_kvb,
            dust_relay_fee_sat_per_kvb: config.dust_relay_fee_sat_per_kvb,
            bytes_per_sigop: config.bytes_per_sigop,
            max_datacarrier_bytes: config.max_datacarrier_bytes,
            permit_bare_multisig: config.permit_bare_multisig,
            require_standard: !config.accept_nonstd_txn,
            cluster_count_limit: config.cluster_count,
            cluster_vsize_limit: config.cluster_size_vbytes,
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
        let banlist_path = config.datadir.join("banlist.json");
        let banned_addresses = match load_banlist(&config.datadir) {
            Ok(entries) => entries,
            Err(error) => {
                quarantine_persistent_file(&banlist_path, &error);
                HashMap::new()
            }
        };
        let peers_path = config.datadir.join("peers.json");
        let (known_addresses, tried_addresses, network_addresses, network_tried_addresses) =
            match load_known_addresses(&config.datadir) {
                Ok(state) => state,
                Err(error) => {
                    quarantine_persistent_file(&peers_path, &error);
                    (
                        HashMap::new(),
                        HashSet::new(),
                        HashMap::new(),
                        HashSet::new(),
                    )
                }
            };
        let (events, _) = broadcast::channel(256);
        let (mempool_events, _) = broadcast::channel(256);
        let (peer_mempool_events, _) = broadcast::channel(256);
        let (zmq_events, _) = broadcast::channel(4_096);
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
            .map(|path| load_rpc_cookie(&path, config.rpc_cookie_permissions))
            .transpose()?;
        let compact_extra_limit = config.block_reconstruction_extra_txn;
        let node = Arc::new(Self {
            config,
            _data_dir_lock: data_dir_lock,
            _blocks_dir_lock: blocks_dir_lock,
            asmap,
            chain: Arc::new(RwLock::new(chain)),
            mempool: Arc::new(RwLock::new(mempool)),
            events,
            mempool_events,
            peer_mempool_events,
            zmq_events,
            txout_scan: Arc::new(ScanState::default()),
            blockfilter_scan: Arc::new(ScanState::default()),
            rpc_cookie,
            i2p_sam,
            tor_controller,
            mempool_path,
            peer_count: AtomicUsize::new(0),
            mempool_check_operations: AtomicUsize::new(0),
            block_index_check_operations: AtomicUsize::new(0),
            addrman_check_operations: AtomicUsize::new(0),
            zmq_mempool_sequence: AtomicU64::new(zmq_mempool_sequence),
            rpc_command_sequence: AtomicUsize::new(0),
            rpc_commands: parking_lot::RwLock::new(HashMap::new()),
            total_bytes_sent: AtomicU64::new(0),
            total_bytes_received: AtomicU64::new(0),
            outbound_usage: parking_lot::Mutex::new(OutboundUsage::default()),
            network_active: AtomicBool::new(network_active),
            block_stalling_timeout_secs: AtomicU64::new(BLOCK_STALLING_TIMEOUT_DEFAULT.as_secs()),
            block_stalling_since: parking_lot::RwLock::new(HashMap::new()),
            shutdown_requested: AtomicBool::new(false),
            peers: parking_lot::RwLock::new(HashMap::new()),
            peer_commands: parking_lot::RwLock::new(HashMap::new()),
            peer_manager_requests: parking_lot::RwLock::new(None),
            private_broadcasts: parking_lot::Mutex::new(HashMap::new()),
            compact_extra_transactions: parking_lot::Mutex::new(CompactExtraTransactions::new(
                compact_extra_limit,
            )),
            orphans: parking_lot::Mutex::new(OrphanPool::default()),
            known_addresses: parking_lot::RwLock::new(known_addresses),
            tried_addresses: parking_lot::RwLock::new(tried_addresses),
            network_addresses: parking_lot::RwLock::new(network_addresses),
            network_tried_addresses: parking_lot::RwLock::new(network_tried_addresses),
            added_nodes: parking_lot::RwLock::new(added_nodes),
            added_node_names: parking_lot::RwLock::new(added_node_names),
            banned_addresses: parking_lot::RwLock::new(banned_addresses),
            listen_address: parking_lot::RwLock::new(None),
            listen_addresses: parking_lot::RwLock::new(Vec::new()),
            mapped_addresses: parking_lot::RwLock::new(Vec::new()),
            listen_network_addresses: parking_lot::RwLock::new(Vec::new()),
            last_mining_block: parking_lot::RwLock::new(None),
            time_offset_samples: parking_lot::RwLock::new(VecDeque::new()),
            warnings: parking_lot::RwLock::new(Vec::new()),
            versionbits_warning_scanned: AtomicBool::new(false),
            fee_estimator: Mutex::new(fee_estimator),
            started_at: Instant::now(),
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
        let previous_tip = self.chain.read().best_hash();
        let (tip, activated_blocks, disconnected_blocks) = {
            let mut chain = self.chain.write();
            let tip = chain.connect_block(block)?;
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
        self.reduce_block_stalling_timeout();
        if !activated_blocks.is_empty() || !disconnected_blocks.is_empty() {
            self.reconcile_mempool_after_chain_change(&activated_blocks, &disconnected_blocks);
            let _ = self.events.send(tip.clone());

            self.announce_zmq_block_events(&disconnected_blocks, &activated_blocks);
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

        if known_addresses.len() > MAX_KNOWN_ADDRESSES
            || network_addresses.len() > MAX_KNOWN_ADDRESSES
        {
            bail!("address-manager table exceeds its configured capacity");
        }
        for (address, peer_id, endpoint) in &known_addresses {
            if *endpoint != NetworkEndpoint::Ip(*address) {
                bail!("known IPv4/IPv6 address has a mismatched endpoint key: {address}");
            }
            if *peer_id != 0 && peer_ids.get(peer_id) != Some(endpoint) {
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
        Ok(())
    }

    pub(crate) fn mapped_as(&self, endpoint: &NetworkEndpoint) -> Option<u32> {
        self.asmap.as_ref()?.mapped_as(endpoint)
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

    fn reconcile_mempool_after_chain_change(
        &self,
        activated_blocks: &[Block],
        disconnected_blocks: &[Block],
    ) {
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
        for block in activated_blocks {
            mempool.remove_confirmed(block);
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
        for block in disconnected_blocks {
            for transaction in block.txdata.iter().skip(1) {
                if let Ok(txid) = mempool.accept_reorg(transaction.clone(), &chain, added_at) {
                    fee_estimator_exclusions.insert(txid);
                }
            }
        }
        mempool.revalidate(&chain);
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
    }

    fn promote_orphans_after_chain_change(
        &self,
        activated_blocks: &[Block],
        disconnected_blocks: &[Block],
    ) {
        for block in activated_blocks {
            self.orphans.lock().erase_for_block(block);
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

    fn reduce_block_stalling_timeout(&self) {
        let current = self.block_stalling_timeout_secs.load(Ordering::Relaxed);
        if current <= BLOCK_STALLING_TIMEOUT_DEFAULT.as_secs() {
            return;
        }
        let reduced =
            (current.saturating_mul(85) / 100).max(BLOCK_STALLING_TIMEOUT_DEFAULT.as_secs());
        let _ = self.block_stalling_timeout_secs.compare_exchange(
            current,
            reduced,
            Ordering::Relaxed,
            Ordering::Relaxed,
        );
    }

    pub fn accept_transaction(&self, transaction: Transaction) -> Result<Txid> {
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
        let (txid, _) = self.try_accept_transaction(transaction.clone())?;
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
        if self.config.proxy.is_none() {
            bail!("--privatebroadcast requires --proxy for IPv4/IPv6 private connections")
        }
        let txid = transaction.compute_txid();
        let wtxid = transaction.compute_wtxid();
        if self.private_broadcasts.lock().contains_key(&wtxid) {
            return Ok(txid);
        }
        self.validate_private_broadcast_transaction(transaction.clone())?;
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
        candidates.retain(|address| {
            address.port() != 0
                && !address.ip().is_unspecified()
                && (address.is_ipv4() || address.is_ipv6())
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
        match self.try_accept_transaction(transaction.clone()) {
            Ok((txid, _)) => {
                self.notify_mempool_transaction_from_peer(transaction, peer_id);
                Ok(txid)
            }
            Err(error @ MempoolError::MissingInput(_)) => {
                self.add_compact_extra_transaction(transaction.clone());
                self.orphans.lock().add(transaction, Some(peer_id));
                Err(error.into())
            }
            Err(error) => {
                self.add_compact_extra_transaction(transaction);
                Err(error.into())
            }
        }
    }

    fn add_compact_extra_transaction(&self, transaction: Transaction) {
        self.compact_extra_transactions.lock().insert(transaction);
    }

    pub(crate) fn compact_extra_transactions(&self) -> Vec<Transaction> {
        self.compact_extra_transactions.lock().snapshot()
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
        let (result, changes, current_height) = {
            let chain = self.chain.read();
            let mut mempool = self.mempool.write();
            let result = mempool.accept(transaction, &chain);
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
        result.map(|txid| (txid, changes))
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

    fn expire_mempool(&self) {
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
    }

    #[cfg(test)]
    fn announce_zmq_mempool_added(&self, transaction: Transaction) {
        if !self.config.zmq.is_enabled() {
            return;
        }
        let mempool_sequence = self.zmq_mempool_sequence.fetch_add(1, Ordering::Relaxed);
        let _ = self.zmq_events.send(zmq::Event::TransactionAdded {
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
        let _ = self.zmq_events.send(zmq::Event::TransactionRemoved {
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
        let _ = self.zmq_events.send(event);
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
        for block in disconnected {
            let _ = self
                .zmq_events
                .send(zmq::Event::BlockDisconnected(Arc::new(block.clone())));
        }
        for block in connected {
            let _ = self
                .zmq_events
                .send(zmq::Event::BlockConnected(Arc::new(block.clone())));
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

    fn notify_mempool_transaction_with_exclusions(
        &self,
        transaction: Transaction,
        excluded_peers: Vec<usize>,
    ) {
        let txid = transaction.compute_txid();
        self.orphans.lock().remove(&txid);
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
            match self.try_accept_transaction(transaction.clone()) {
                Ok((txid, _)) => {
                    self.announce_mempool_transaction(txid);
                    self.announce_peer_mempool_transaction(
                        txid,
                        entry.announcers.into_iter().collect(),
                    );
                    pending.extend(self.orphans.lock().take_children(&transaction));
                }
                Err(MempoolError::MissingInput(_)) => {
                    self.orphans.lock().add_entry(entry);
                }
                Err(_) => {}
            }
        }
    }

    pub fn invalidate_block(&self, hash: bitcoin::BlockHash) -> Result<ChainEvent> {
        let (tip, changed, activated_blocks, disconnected_blocks) = {
            let mut chain = self.chain.write();
            let previous = chain.best_hash();
            let tip = chain.invalidate_block(&hash)?;
            let changed = previous != chain.best_hash();
            let activated_blocks = if changed {
                chain.active_blocks_after(previous)?
            } else {
                Vec::new()
            };
            let disconnected_blocks = if changed {
                chain.disconnected_blocks_after(previous)?
            } else {
                Vec::new()
            };
            (tip, changed, activated_blocks, disconnected_blocks)
        };
        if changed {
            self.reconcile_mempool_after_chain_change(&activated_blocks, &disconnected_blocks);
            self.announce_zmq_block_events(&disconnected_blocks, &activated_blocks);
            self.promote_orphans_after_chain_change(&activated_blocks, &disconnected_blocks);
            let _ = self.events.send(tip.clone());
        }
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
            let activated_blocks = if changed {
                chain.active_blocks_after(previous)?
            } else {
                Vec::new()
            };
            let disconnected_blocks = if changed {
                chain.disconnected_blocks_after(previous)?
            } else {
                Vec::new()
            };
            (tip, changed, activated_blocks, disconnected_blocks)
        };
        if changed {
            self.reconcile_mempool_after_chain_change(&activated_blocks, &disconnected_blocks);
            self.announce_zmq_block_events(&disconnected_blocks, &activated_blocks);
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
            let activated_blocks = if changed {
                chain.active_blocks_after(previous)?
            } else {
                Vec::new()
            };
            let disconnected_blocks = if changed {
                chain.disconnected_blocks_after(previous)?
            } else {
                Vec::new()
            };
            (tip, changed, activated_blocks, disconnected_blocks)
        };
        if changed {
            self.reconcile_mempool_after_chain_change(&activated_blocks, &disconnected_blocks);
            self.announce_zmq_block_events(&disconnected_blocks, &activated_blocks);
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

    pub(crate) fn subscribe_zmq(&self) -> broadcast::Receiver<zmq::Event> {
        self.zmq_events.subscribe()
    }

    pub fn peer_count(&self) -> usize {
        self.peer_count.load(Ordering::Relaxed)
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
        let directory = self
            .config
            .datadir
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

    pub(crate) fn record_bytes_received(&self, peer_id: usize, bytes: usize, command: &str) {
        let bytes = u64::try_from(bytes).unwrap_or(u64::MAX);
        self.total_bytes_received
            .fetch_add(bytes, Ordering::Relaxed);
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            let now = unix_time_seconds();
            peer.bytes_received = peer.bytes_received.saturating_add(bytes);
            peer.last_recv = now;
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
        let Some(candidate_work) = chain.chain_work_by_hash(&hash) else {
            return;
        };
        let mut peers = self.peers.write();
        let Some(peer) = peers.get_mut(&peer_id) else {
            return;
        };
        let should_update = peer.best_known_block.is_none_or(|current| {
            chain
                .chain_work_by_hash(&current)
                .is_none_or(|current_work| candidate_work >= current_work)
        });
        if should_update {
            peer.best_known_block = Some(hash);
        }
    }

    pub(crate) fn update_peer_bip152_highbandwidth_from(&self, peer_id: usize, enabled: bool) {
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.bip152_highbandwidth_from = enabled;
        }
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
        let Some(height) = self.chain.read().block_height_by_hash(&hash) else {
            return false;
        };
        if let Some(peer) = self.peers.write().get_mut(&peer_id)
            && !peer
                .inflight_blocks
                .iter()
                .any(|inflight| inflight.hash == hash)
        {
            if peer.inflight_blocks.len() >= MAX_BLOCKS_IN_TRANSIT_PER_PEER {
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

    pub(crate) fn peer_has_inflight_block_request(&self, peer_id: usize, hash: BlockHash) -> bool {
        self.peers.read().get(&peer_id).is_some_and(|peer| {
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
        let candidates = {
            let chain = self.chain.read();
            let best_header = chain.best_header_tip().hash;
            chain
                .headers_to_hash(&best_header)
                .into_iter()
                .flatten()
                .skip(1)
                .map(|header| header.block_hash())
                .filter(|hash| !chain.store.contains(hash))
                .filter(|hash| {
                    !limited_peer
                        || chain
                            .block_height_by_hash(hash)
                            .is_some_and(|height| height.saturating_add(290) >= chain.height())
                })
                .take(max_scan)
                .collect::<Vec<_>>()
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
        for hash in candidates {
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

        let staller = (!peer_has_inflight && requests.is_empty())
            .then_some(waiting_for)
            .flatten();
        BlockDownloadSchedule { requests, staller }
    }

    pub(crate) fn note_block_staller(&self, peer_id: usize) {
        self.note_block_staller_at(peer_id, Instant::now());
    }

    fn note_block_staller_at(&self, peer_id: usize, since: Instant) {
        if self.peers.read().contains_key(&peer_id) {
            self.block_stalling_since
                .write()
                .entry(peer_id)
                .or_insert(since);
        }
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
            (now.duration_since(*since) > timeout).then_some(*peer_id)
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
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.inflight_blocks
                .retain(|inflight| inflight.hash != hash);
        }
        self.block_stalling_since.write().remove(&peer_id);
    }

    fn clear_peer_block_requests_for_hash(&self, hash: BlockHash) {
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

    pub(crate) fn record_pong(&self, peer_id: usize, nonce: u64) -> bool {
        let mut peers = self.peers.write();
        let Some(peer) = peers.get_mut(&peer_id) else {
            return false;
        };
        if peer.ping_nonce != Some(nonce) {
            return false;
        }
        peer.ping_nonce = None;
        if let Some(sent_at) = peer.ping_sent_at.take() {
            let ping_time = sent_at.elapsed().as_secs_f64();
            peer.ping_time = Some(ping_time);
            peer.min_ping = Some(
                peer.min_ping
                    .map_or(ping_time, |minimum| minimum.min(ping_time)),
            );
        }
        true
    }

    pub fn network_active(&self) -> bool {
        self.network_active.load(Ordering::Relaxed)
    }

    pub(crate) fn set_listen_address(&self, address: SocketAddr) {
        *self.listen_address.write() = Some(address);
        *self.listen_addresses.write() = vec![address];
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

    pub(crate) fn onion_proxy(&self) -> Option<SocketAddr> {
        self.config
            .onion_proxy
            .or_else(|| self.tor_controller.as_ref()?.socks_proxy())
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
            },
        );
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
        } = options;
        let address = endpoint.peer_socket_addr();
        let connected_at = time::unix_time();
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
            connected_at,
            last_send: 0,
            last_recv: 0,
            bytes_sent: 0,
            bytes_received: 0,
            bytes_sent_per_msg: HashMap::new(),
            bytes_received_per_msg: HashMap::new(),
            last_inv_sequence: 0,
            inv_to_send: 0,
            last_transaction: 0,
            last_block: 0,
            best_known_block: None,
            last_common_block: None,
            bip152_highbandwidth_to: false,
            bip152_highbandwidth_from: false,
            inflight_blocks: Vec::new(),
            time_offset: 0,
            addr_processed: 0,
            addr_rate_limited: 0,
            addr_relay_enabled: !inbound || permissions.contains(PeerPermissions::ADDR),
            ping_time: None,
            min_ping: None,
            ping_nonce: None,
            ping_sent_at: None,
            addr_token_bucket: 1.0,
            addr_token_timestamp: Instant::now(),
        };
        self.peers.write().insert(id, peer.clone());
        self.peer_commands.write().insert(id, commands);
        if connection_type != "private-broadcast"
            && !matches!(endpoint, NetworkEndpoint::Dns { .. })
        {
            if let Some(address) = endpoint.legacy_socket_addr() {
                let mut known = self.known_addresses.write();
                if self.reserve_known_address(&mut known, address) {
                    known.insert(address, peer);
                    self.tried_addresses.write().insert(address);
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
            peer.version = Some(version);
            peer.services = services;
            peer.user_agent = user_agent.to_owned();
            peer.start_height = start_height;
            peer.relay_transactions = relay_transactions;
            if peer.connection_type != "private-broadcast" {
                if let Some(address) = peer.endpoint.legacy_socket_addr() {
                    if let Some(known) = self.known_addresses.write().get_mut(&address) {
                        known.version = Some(version);
                        known.services = services;
                        known.user_agent = user_agent.to_owned();
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
            let period =
                usize::try_from(validation::bip9_deployments(self.config.network)[0].period)
                    .unwrap_or(1)
                    .max(1);
            let first_scan = !self
                .versionbits_warning_scanned
                .swap(true, Ordering::AcqRel);
            if first_scan {
                validation::unknown_versionbits_active(headers, self.config.network)
            } else if headers.len() % period == 0 {
                validation::unknown_versionbits_active_at_boundary(headers, self.config.network)
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

    pub(crate) fn allow_peer_address(&self, id: usize) -> bool {
        let mut peers = self.peers.write();
        let Some(peer) = peers.get_mut(&id) else {
            return false;
        };
        if peer.permissions.contains(PeerPermissions::ADDR) {
            peer.addr_processed = peer.addr_processed.saturating_add(1);
            return true;
        }
        let now = Instant::now();
        if peer.addr_token_bucket < MAX_ADDR_PROCESSING_TOKEN_BUCKET {
            let elapsed = now
                .saturating_duration_since(peer.addr_token_timestamp)
                .as_secs_f64();
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
        let recipients = self
            .peers
            .read()
            .values()
            .filter(|peer| {
                peer.id != origin_peer_id && peer.version.is_some() && peer.addr_relay_enabled
            })
            .map(|peer| peer.id)
            .collect::<Vec<_>>();
        let commands = self.peer_commands.read();
        for peer_id in recipients {
            if let Some(sender) = commands.get(&peer_id) {
                let _ = sender.send(p2p::PeerCommand::RelayAddresses {
                    addresses: addresses.clone(),
                });
            }
        }
    }

    pub(crate) fn set_peer_transport_protocol(&self, id: usize, transport_v2: bool) {
        if let Some(peer) = self.peers.write().get_mut(&id) {
            peer.transport_protocol_type = if transport_v2 { "v2" } else { "v1" };
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
            peer.addr_relay_enabled = (!peer.inbound && connection_type != "block-relay-only")
                || peer.permissions.contains(PeerPermissions::ADDR);
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
        let endpoint = self.peers.write().remove(&id).map(|peer| peer.endpoint);
        self.peer_commands.write().remove(&id);
        self.block_stalling_since.write().remove(&id);
        if let Some(endpoint) = endpoint {
            if let Some(address) = endpoint.legacy_socket_addr()
                && let Some(known) = self.known_addresses.write().get_mut(&address)
                && known.id == id
            {
                known.id = 0;
                known.inbound = false;
                known.local_address = None;
                known.ping_nonce = None;
                known.ping_sent_at = None;
            }
        }
        self.orphans.lock().erase_for_peer(id);
        self.maybe_check_addrman();
        self.refresh_clock_warning();
    }

    pub fn peer_infos(&self) -> Vec<PeerInfo> {
        self.peers.read().values().cloned().collect()
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

    pub(crate) fn add_network_address(&self, endpoint: NetworkEndpoint, tried: bool) -> bool {
        if matches!(endpoint, NetworkEndpoint::Dns { .. }) {
            return false;
        }
        if !self.config.allows_network_endpoint(&endpoint) {
            return false;
        }
        if let Some(address) = endpoint.legacy_socket_addr() {
            return self.add_peer_address(address, tried);
        }
        let now = unix_time_seconds();
        let mut known = self.network_addresses.write();
        if known.contains_key(&endpoint) || !self.reserve_network_address(&mut known, &endpoint) {
            return false;
        }
        known.insert(
            endpoint.clone(),
            KnownNetworkAddress {
                endpoint: endpoint.clone(),
                services: crate::wire::NODE_NETWORK | crate::wire::NODE_WITNESS,
                time: now,
            },
        );
        drop(known);
        if tried {
            self.network_tried_addresses.write().insert(endpoint);
        }
        self.maybe_check_addrman();
        true
    }

    pub(crate) fn remember_network_address(
        &self,
        endpoint: NetworkEndpoint,
        services: u64,
        time: u64,
    ) -> bool {
        if !self.config.allows_network_endpoint(&endpoint) {
            return false;
        }
        if let Some(address) = endpoint.legacy_socket_addr() {
            return self.remember_address(address, services, time);
        }
        let mut known = self.network_addresses.write();
        if !self.reserve_network_address(&mut known, &endpoint) {
            return false;
        }
        let is_new = !known.contains_key(&endpoint);
        let entry = known
            .entry(endpoint.clone())
            .or_insert_with(|| KnownNetworkAddress {
                endpoint,
                services,
                time,
            });
        entry.services |= services;
        entry.time = entry.time.max(time);
        drop(known);
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
                id: 0,
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
                connected_at: now,
                last_send: now,
                last_recv: now,
                bytes_sent: 0,
                bytes_received: 0,
                bytes_sent_per_msg: HashMap::new(),
                bytes_received_per_msg: HashMap::new(),
                last_inv_sequence: 0,
                inv_to_send: 0,
                last_transaction: 0,
                last_block: 0,
                best_known_block: None,
                last_common_block: None,
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
                addr_token_bucket: 1.0,
                addr_token_timestamp: Instant::now(),
            },
        );
        drop(known);
        if tried {
            self.tried_addresses.write().insert(address);
            let endpoint = NetworkEndpoint::from_socket(address);
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
            id: 0,
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
            connected_at: time,
            last_send: time,
            last_recv: time,
            bytes_sent: 0,
            bytes_received: 0,
            bytes_sent_per_msg: HashMap::new(),
            bytes_received_per_msg: HashMap::new(),
            last_inv_sequence: 0,
            inv_to_send: 0,
            last_transaction: 0,
            last_block: 0,
            best_known_block: None,
            last_common_block: None,
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
            addr_token_bucket: 1.0,
            addr_token_timestamp: Instant::now(),
        });
        if entry.id == 0 {
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
                peer.id == 0 && !tried.contains(*candidate) && **candidate != address
            })
            .min_by_key(|(_, peer)| peer.connected_at)
            .map(|(candidate, _)| *candidate);
        drop(tried);
        if let Some(eviction) = eviction {
            known.remove(&eviction);
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

    pub(crate) fn request_one_try_with_connection_type(
        &self,
        address: SocketAddr,
        transport_v2: Option<bool>,
        connection_type: &'static str,
    ) {
        self.request_one_try_endpoint_with_connection_type(
            NetworkEndpoint::from_socket(address),
            transport_v2,
            connection_type,
        );
    }

    pub(crate) fn request_one_try_endpoint_with_connection_type(
        &self,
        endpoint: NetworkEndpoint,
        transport_v2: Option<bool>,
        connection_type: &'static str,
    ) {
        if let Some(sender) = self.peer_manager_requests.read().as_ref() {
            let _ = sender.send(p2p::PeerManagerRequest::OneTry(
                endpoint,
                transport_v2,
                connection_type,
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
        {
            let chain = self.chain.read();
            let height = chain
                .block_height_by_hash(&hash)
                .ok_or_else(|| anyhow::anyhow!("Block header missing"))?;
            if chain.is_pruned() && height > chain.height() {
                bail!(
                    "In prune mode, only blocks that the node has already synced previously can be fetched from a peer"
                );
            }
            if chain.store.contains(&hash) {
                bail!("Block already downloaded");
            }
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
        self.clear_peer_block_requests_for_hash(hash);
        if !self.track_peer_block_request(peer_id, hash) {
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
            .ok_or_else(|| anyhow::anyhow!("peer {peer_id} is not connected"))?;
        sender
            .send(p2p::PeerCommand::SendMessage { command, payload })
            .map_err(|_| anyhow::anyhow!("peer {peer_id} disconnected"))
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
        if peer.ping_nonce.is_some() {
            return false;
        }
        peer.ping_nonce = Some(nonce);
        peer.ping_sent_at = Some(Instant::now());
        true
    }

    pub(crate) fn cancel_ping(&self, peer_id: usize, nonce: u64) {
        if let Some(peer) = self.peers.write().get_mut(&peer_id)
            && peer.ping_nonce == Some(nonce)
        {
            peer.ping_nonce = None;
            peer.ping_sent_at = None;
        }
    }

    pub(crate) fn ping_timed_out(&self, peer_id: usize, timeout: Duration) -> bool {
        self.peers
            .read()
            .get(&peer_id)
            .and_then(|peer| peer.ping_sent_at)
            .is_some_and(|sent_at| sent_at.elapsed() >= timeout)
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

    pub fn ban_address(&self, address: IpAddr, ban_until: u64, reason: String) -> Result<()> {
        self.ban_subnet(IpSubnet::from_address(address), ban_until, reason)
    }

    pub(crate) fn ban_subnet(
        &self,
        subnet: IpSubnet,
        ban_until: u64,
        reason: String,
    ) -> Result<()> {
        let ban_created = time::unix_time();
        let mut banned = self.banned_addresses.write();
        remove_expired_bans(&mut banned, ban_created);
        if banned
            .keys()
            .any(|existing| existing.contains_subnet(subnet))
        {
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

    pub fn request_shutdown(&self) {
        self.shutdown_requested.store(true, Ordering::Release);
        self.shutdown.notify_waiters();
    }

    pub async fn run(self: Arc<Self>) -> Result<()> {
        self.run_with_startup(None).await
    }

    pub async fn run_with_startup(
        self: Arc<Self>,
        startup_sender: Option<oneshot::Sender<()>>,
    ) -> Result<()> {
        let startup = startup_sender.map(|sender| StartupLatch::new(sender, 4));
        let p2p = p2p::PeerManager::new(self.clone());
        let rpc = rpc::RpcServer::new(self.clone());
        let electrum = electrum::ElectrumServer::new(self.clone());
        let mut zmq_task = tokio::spawn(zmq::run_with_startup(
            self.config.zmq.clone(),
            self.subscribe_zmq(),
            startup.clone(),
        ));

        info!(
            network = ?self.config.network,
            p2p = %self.config.p2p_bind,
            rpc = ?self.config.rpc_bind,
            electrum = ?self.config.electrum_bind,
            "starting wallet-free Bitcoin node"
        );

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
            result = wait_for_shutdown_signal() => result,
            _ = self.wait_for_shutdown() => Ok(()),
        };

        p2p_task.abort();
        rpc_task.abort();
        electrum_task.abort();
        zmq_task.abort();
        background_validation_task.abort();
        mempool_expiry_task.abort();
        fee_estimator_task.abort();
        run_notify_command(self.config.shutdown_notify.as_deref(), None);
        if let Err(error) = self.flush_fee_estimates(true) {
            warn!(%error, "unable to flush fee estimates during shutdown");
        }
        if self.config.persist_mempool {
            self.persist_mempool()?;
        }
        self.persist_known_addresses()?;
        self.remove_rpc_cookie();
        run_result
    }

    fn remove_rpc_cookie(&self) {
        if self.rpc_cookie.is_none() {
            return;
        }
        let Some(path) = self.config.rpc_cookie_path.as_deref() else {
            return;
        };
        if let Err(error) = fs::remove_file(path)
            && error.kind() != std::io::ErrorKind::NotFound
        {
            warn!(path = %path.display(), %error, "unable to remove RPC authentication cookie");
        }
    }

    pub fn persist_mempool(&self) -> Result<()> {
        self.mempool
            .read()
            .save_to_file_with_format(&self.mempool_path, self.config.persist_mempool_v1)
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
        let path = self.config.datadir.join("banlist.json");
        let temp = self.config.datadir.join("banlist.json.tmp");
        let entries = self
            .banned_addresses
            .read()
            .values()
            .map(|entry| PersistedBannedAddress {
                address: entry.address,
                prefix: Some(entry.prefix),
                ban_created: entry.ban_created,
                ban_until: entry.ban_until,
                reason: entry.reason.clone(),
            })
            .collect::<Vec<_>>();
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
            .map(|peer| PersistedAddress {
                address: peer.address.to_string(),
                services: peer.services,
                time: peer.connected_at,
                tried: self.is_address_tried(peer.address),
                network: None,
                port: None,
            })
            .collect::<Vec<_>>();
        entries.extend(
            self.network_addresses
                .read()
                .values()
                .map(|entry| PersistedAddress {
                    address: entry.endpoint.host_string(),
                    services: entry.services,
                    time: entry.time,
                    tried: self.is_network_address_tried(&entry.endpoint),
                    network: Some(entry.endpoint.network_name().to_owned()),
                    port: Some(entry.endpoint.port()),
                }),
        );
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

impl<'de> Visitor<'de> for SettingsObjectVisitor {
    type Value = serde_json::Value;

    fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("a JSON object")
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
                anyhow::anyhow!("settings file {} is invalid: {error}", path.display())
            })?;
        deserializer.end().map_err(|error| {
            anyhow::anyhow!("settings file {} is invalid: {error}", path.display())
        })?;
        if !value.is_object() {
            bail!(
                "settings file {} must contain a JSON object",
                path.display()
            );
        }
        return Ok(());
    }

    let warning = serde_json::json!({
        "_warning_": "This file is automatically generated and updated by bitcoind-rs. Please do not edit this file while the node is running, as changes might be ignored or overwritten."
    });
    let temporary = path.with_file_name(format!(
        ".{}.tmp",
        path.file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("settings.json")
    ));
    fs::write(&temporary, serde_json::to_vec_pretty(&warning)?)
        .with_context(|| format!("writing settings file {}", path.display()))?;
    fs::rename(&temporary, path)
        .with_context(|| format!("installing settings file {}", path.display()))?;
    Ok(())
}

fn load_banlist(data_dir: &Path) -> Result<HashMap<IpSubnet, BannedAddress>> {
    let path = data_dir.join("banlist.json");
    if !path.exists() {
        return Ok(HashMap::new());
    }
    let bytes = std::fs::read(path)?;
    let entries: Vec<PersistedBannedAddress> = serde_json::from_slice(&bytes)?;
    entries
        .into_iter()
        .map(|entry| {
            let prefix = entry.prefix.unwrap_or_else(|| address_bits(entry.address));
            let subnet = IpSubnet::new(entry.address, prefix)?;
            let banned = BannedAddress {
                address: subnet.address(),
                prefix: subnet.prefix(),
                ban_created: entry.ban_created,
                ban_until: entry.ban_until,
                reason: entry.reason,
            };
            Ok((subnet, banned))
        })
        .collect()
}

fn load_known_addresses(data_dir: &Path) -> Result<LoadedAddressState> {
    let path = data_dir.join("peers.json");
    if !path.exists() {
        return Ok((
            HashMap::new(),
            HashSet::new(),
            HashMap::new(),
            HashSet::new(),
        ));
    }
    let bytes = std::fs::read(path)?;
    let entries: Vec<PersistedAddress> = serde_json::from_slice(&bytes)?;
    let mut known = HashMap::with_capacity(entries.len());
    let mut tried = HashSet::new();
    let mut network_addresses = HashMap::new();
    let mut network_tried_addresses = HashSet::new();
    for entry in entries {
        let endpoint =
            NetworkEndpoint::parse(entry.network.as_deref(), &entry.address, entry.port)?;
        match endpoint {
            NetworkEndpoint::Ip(address) => {
                if entry.tried {
                    tried.insert(address);
                }
                known.insert(
                    address,
                    PeerInfo {
                        id: 0,
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
                        connected_at: entry.time,
                        last_send: entry.time,
                        last_recv: entry.time,
                        bytes_sent: 0,
                        bytes_received: 0,
                        bytes_sent_per_msg: HashMap::new(),
                        bytes_received_per_msg: HashMap::new(),
                        last_inv_sequence: 0,
                        inv_to_send: 0,
                        last_transaction: 0,
                        last_block: 0,
                        best_known_block: None,
                        last_common_block: None,
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
                        addr_token_bucket: 1.0,
                        addr_token_timestamp: Instant::now(),
                    },
                );
            }
            endpoint => {
                if entry.tried {
                    network_tried_addresses.insert(endpoint.clone());
                }
                network_addresses.insert(
                    endpoint.clone(),
                    KnownNetworkAddress {
                        endpoint,
                        services: entry.services,
                        time: entry.time,
                    },
                );
            }
        }
    }
    Ok((known, tried, network_addresses, network_tried_addresses))
}

fn unix_time_seconds() -> u64 {
    time::unix_time()
}

fn load_rpc_cookie(path: &Path, permissions: RpcCookiePermissions) -> Result<String> {
    if let Some(parent) = path.parent()
        && !parent.as_os_str().is_empty()
    {
        std::fs::create_dir_all(parent)?;
    }
    let cookie = format!("__cookie__:{}", hex::encode(random::<[u8; 32]>()));
    let temp = std::path::PathBuf::from(format!("{}.tmp", path.display()));
    std::fs::write(&temp, &cookie)?;
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
    Ok(cookie)
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

    fn test_config(datadir: &Path) -> Config {
        Config {
            network: bitcoin::Network::Regtest,
            datadir: datadir.to_owned(),
            blocks_dir: None,
            blocks_dir_explicit: false,
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
            tor_control: "127.0.0.1:9051".parse().unwrap(),
            tor_password: None,
            i2p_accept_incoming: false,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
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
            mempool_expiry_hours: 336,
            coinstatsindex: false,
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
            .join("message_capture/192.0.2.1_18444/msgs_sent.dat");
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
        fs::write(directory.path().join("mempool.dat"), b"not a mempool dump").unwrap();

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
        }]);
        fs::write(
            directory.path().join("banlist.json"),
            serde_json::to_vec(&legacy).unwrap(),
        )
        .unwrap();
        let loaded = load_banlist(directory.path()).unwrap();
        let legacy_subnet = IpSubnet::parse("192.0.2.7").unwrap();
        assert_eq!(loaded[&legacy_subnet].prefix, 32);
        assert_eq!(
            loaded[&legacy_subnet].address,
            "192.0.2.7".parse::<IpAddr>().unwrap()
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
        let _node = Node::open(Config::from_args(args).unwrap()).unwrap();
        assert!(directory.path().join("external-blocks/blocks.dat").exists());
        assert!(directory.path().join("external-blocks/xor.dat").exists());
        assert!(directory.path().join("chainstate.bin").exists());
        assert!(!directory.path().join("blocks/blocks.dat").exists());
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
            import_external_block_file(&mut chain, &path, Network::Regtest).unwrap(),
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
            import_external_block_file(&mut chain, &path, Network::Regtest).unwrap(),
            1
        );
        assert!(chain.block(&block.block_hash()).unwrap().is_some());
        assert_eq!(chain.best_hash(), block.block_hash());
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
        assert_eq!(peer.id, 0);
        assert_eq!(peer.services, crate::wire::NODE_NETWORK);
        assert_eq!(peer.connected_at, 123);
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
            port: 18445,
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
        fs::write(directory.path().join("banlist.json"), b"not-json").unwrap();

        let node = Node::open(test_config(directory.path())).unwrap();

        assert!(node.known_addresses().is_empty());
        assert!(node.banned_addresses().is_empty());
        assert!(!directory.path().join("peers.json").exists());
        assert!(!directory.path().join("banlist.json").exists());
        assert!(directory.path().join("peers.json.corrupt").exists());
        assert!(directory.path().join("banlist.json.corrupt").exists());
    }
}
