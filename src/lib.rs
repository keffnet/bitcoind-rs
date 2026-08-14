#![forbid(unsafe_code)]
#![warn(rust_2018_idioms, clippy::all)]

pub mod chain;
pub mod config;
pub mod electrum;
pub mod mempool;
pub mod muhash;
pub mod p2p;
pub mod rpc;
pub mod storage;
pub mod time;
pub mod validation;
pub mod wire;
pub mod zmq;

use std::collections::{HashMap, HashSet, VecDeque};
use std::fs;
use std::net::{IpAddr, SocketAddr};
use std::path::Path;
use std::sync::{
    Arc,
    atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering},
};
use std::time::{Duration, Instant};

use anyhow::{Context, Result, bail};
use bitcoin::consensus::encode::deserialize;
use bitcoin::{Block, Network, OutPoint, Transaction, Txid};
use parking_lot::RwLock;
use rand::random;
use serde::{Deserialize, Serialize};
use tokio::sync::{Notify, broadcast};
use tracing::info;

use crate::chain::ChainState;
use crate::config::Config;
use crate::mempool::{
    Mempool, MempoolChange, MempoolChangeKind, MempoolError, MempoolLoadOptions, MempoolPolicy,
};

const MAX_ORPHAN_TRANSACTIONS: usize = 100;
const MAX_ORPHAN_TRANSACTION_WEIGHT: u64 = 400_000;
const ORPHAN_TRANSACTION_EXPIRY: Duration = Duration::from_secs(20 * 60);
const MAX_KNOWN_ADDRESSES: usize = 256_000;
const MEMPOOL_EXPIRY_INTERVAL: Duration = Duration::from_secs(60);
const MAX_EXTERNAL_BLOCK_RECORD_SIZE: usize = 4 * 1024 * 1024;

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
            if chain.header_by_hash(&hash).is_some() {
                continue;
            }
            if chain.header_by_hash(&block.header.prev_blockhash).is_none() {
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
                "block file {} contains block {} with an unknown parent {}",
                path.display(),
                block.block_hash(),
                block.header.prev_blockhash
            );
        }
        pending = remaining;
    }
    Ok(imported)
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
    pub local_address: Option<std::net::SocketAddr>,
    pub inbound: bool,
    pub version: Option<i32>,
    pub services: u64,
    pub user_agent: String,
    pub start_height: i32,
    pub relay_transactions: bool,
    pub min_fee_filter: i64,
    pub transport_protocol_type: &'static str,
    pub connected_at: u64,
    pub last_send: u64,
    pub last_recv: u64,
    pub bytes_sent: u64,
    pub bytes_received: u64,
    pub bytes_sent_per_msg: HashMap<String, u64>,
    pub bytes_received_per_msg: HashMap<String, u64>,
    pub last_inv_sequence: u64,
    pub last_transaction: u64,
    pub last_block: u64,
    pub time_offset: i64,
    pub addr_processed: u64,
    pub addr_relay_enabled: bool,
    pub ping_time: Option<f64>,
    pub min_ping: Option<f64>,
    pub connection_type: &'static str,
    ping_nonce: Option<u64>,
    ping_sent_at: Option<Instant>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct BannedAddress {
    pub address: IpAddr,
    pub ban_created: u64,
    pub ban_until: u64,
    pub reason: String,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct PersistedAddress {
    address: String,
    services: u64,
    time: u64,
    #[serde(default)]
    tried: bool,
}

/// The wallet-free node facade shared by the network and RPC services.
pub struct Node {
    pub config: Config,
    pub chain: Arc<RwLock<ChainState>>,
    pub mempool: Arc<RwLock<Mempool>>,
    pub events: broadcast::Sender<ChainEvent>,
    pub mempool_events: broadcast::Sender<MempoolEvent>,
    peer_mempool_events: broadcast::Sender<PeerMempoolEvent>,
    pub(crate) zmq_events: broadcast::Sender<zmq::Event>,
    pub rpc_cookie: Option<String>,
    mempool_path: std::path::PathBuf,
    pub peer_count: AtomicUsize,
    zmq_mempool_sequence: AtomicU64,
    rpc_command_sequence: AtomicUsize,
    rpc_commands: parking_lot::RwLock<HashMap<usize, (String, Instant)>>,
    total_bytes_sent: AtomicU64,
    total_bytes_received: AtomicU64,
    network_active: AtomicBool,
    peers: parking_lot::RwLock<HashMap<usize, PeerInfo>>,
    peer_commands:
        parking_lot::RwLock<HashMap<usize, tokio::sync::mpsc::UnboundedSender<p2p::PeerCommand>>>,
    peer_manager_requests:
        parking_lot::RwLock<Option<tokio::sync::mpsc::UnboundedSender<p2p::PeerManagerRequest>>>,
    orphans: parking_lot::Mutex<OrphanPool>,
    known_addresses: parking_lot::RwLock<HashMap<SocketAddr, PeerInfo>>,
    tried_addresses: parking_lot::RwLock<HashSet<SocketAddr>>,
    added_nodes: parking_lot::RwLock<HashSet<SocketAddr>>,
    banned_addresses: parking_lot::RwLock<HashMap<IpAddr, BannedAddress>>,
    pub started_at: Instant,
    shutdown: Notify,
}

impl Node {
    pub fn open(config: Config) -> Result<Arc<Self>> {
        let added_nodes = config.seed_nodes.iter().copied().collect();
        let max_mempool_bytes = config
            .max_mempool_mb
            .checked_mul(1_000_000)
            .context("--maxmempool is too large")?;
        let max_mempool_bytes =
            usize::try_from(max_mempool_bytes).context("--maxmempool does not fit usize")?;
        let mut chain = ChainState::open_with_options(
            config.network,
            &config.datadir,
            config.signet_challenge.as_deref(),
            config.blockfilterindex,
            config.reindex,
            config.reindex_chainstate,
        )?;
        chain.configure_pruning(config.prune)?;
        chain.configure_txospender_index(config.txospenderindex)?;
        chain.configure_coinstats_index(config.coinstatsindex)?;
        for path in &config.load_blocks {
            import_external_block_file(&mut chain, path, config.network)?;
        }
        chain.maybe_auto_prune()?;
        let mempool_path = config.datadir.join("mempool.dat");
        let mempool_policy = MempoolPolicy {
            min_relay_fee_sat_per_kvb: config.min_relay_tx_fee_sat_per_kvb,
            incremental_relay_fee_sat_per_kvb: config.incremental_relay_fee_sat_per_kvb,
            dust_relay_fee_sat_per_kvb: config.dust_relay_fee_sat_per_kvb,
            max_datacarrier_bytes: config.max_datacarrier_bytes,
            permit_bare_multisig: config.permit_bare_multisig,
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
                mempool.load_from_file_with_expiry(load_path, &chain, expiry)?;
            }
        }
        let _ = mempool.take_changes();
        let banned_addresses = load_banlist(&config.datadir)?;
        let (known_addresses, tried_addresses) = load_known_addresses(&config.datadir)?;
        let (events, _) = broadcast::channel(256);
        let (mempool_events, _) = broadcast::channel(256);
        let (peer_mempool_events, _) = broadcast::channel(256);
        let (zmq_events, _) = broadcast::channel(4_096);
        let zmq_mempool_sequence = mempool.sequence();
        let rpc_cookie = config
            .rpc_bind
            .map(|_| load_rpc_cookie(&config.datadir))
            .transpose()?;
        Ok(Arc::new(Self {
            config,
            chain: Arc::new(RwLock::new(chain)),
            mempool: Arc::new(RwLock::new(mempool)),
            events,
            mempool_events,
            peer_mempool_events,
            zmq_events,
            rpc_cookie,
            mempool_path,
            peer_count: AtomicUsize::new(0),
            zmq_mempool_sequence: AtomicU64::new(zmq_mempool_sequence),
            rpc_command_sequence: AtomicUsize::new(0),
            rpc_commands: parking_lot::RwLock::new(HashMap::new()),
            total_bytes_sent: AtomicU64::new(0),
            total_bytes_received: AtomicU64::new(0),
            network_active: AtomicBool::new(true),
            peers: parking_lot::RwLock::new(HashMap::new()),
            peer_commands: parking_lot::RwLock::new(HashMap::new()),
            peer_manager_requests: parking_lot::RwLock::new(None),
            orphans: parking_lot::Mutex::new(OrphanPool::default()),
            known_addresses: parking_lot::RwLock::new(known_addresses),
            tried_addresses: parking_lot::RwLock::new(tried_addresses),
            added_nodes: parking_lot::RwLock::new(added_nodes),
            banned_addresses: parking_lot::RwLock::new(banned_addresses),
            started_at: Instant::now(),
            shutdown: Notify::new(),
        }))
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
        if !activated_blocks.is_empty() || !disconnected_blocks.is_empty() {
            let mempool_before = self
                .mempool
                .read()
                .transaction_order()
                .into_iter()
                .collect::<HashSet<_>>();
            let disconnected_transactions = disconnected_blocks
                .iter()
                .flat_map(|block| block.txdata.iter().skip(1).cloned())
                .collect::<Vec<_>>();
            let chain = self.chain.read();
            let mut mempool = self.mempool.write();
            for block in &activated_blocks {
                mempool.remove_confirmed(block);
            }
            for block in &disconnected_blocks {
                for transaction in block.txdata.iter().skip(1) {
                    let _ = mempool.accept_reorg(transaction.clone(), &chain, time::unix_time());
                }
            }
            mempool.revalidate(&chain);
            let mempool_after = mempool
                .transaction_order()
                .into_iter()
                .collect::<HashSet<_>>();
            let mempool_changes = mempool.take_changes();
            let _ = self.events.send(tip.clone());

            drop(mempool);
            drop(chain);
            self.announce_mempool_diff(mempool_before, mempool_after);
            self.notify_zmq_mempool_changes(mempool_changes);
            self.announce_zmq_block_events(&disconnected_blocks, &activated_blocks);
            for block in &activated_blocks {
                self.orphans.lock().erase_for_block(block);
            }
            for block in &activated_blocks {
                for transaction in &block.txdata {
                    self.promote_orphans_for_parent(transaction);
                }
            }
            for transaction in disconnected_transactions {
                if self
                    .mempool
                    .read()
                    .get(&transaction.compute_txid())
                    .is_some()
                {
                    self.promote_orphans_for_parent(&transaction);
                }
            }
        }
        Ok(tip)
    }

    pub fn accept_transaction(&self, transaction: Transaction) -> Result<Txid> {
        let (txid, _) = self.try_accept_transaction(transaction.clone())?;
        self.mempool.write().add_unbroadcast(txid);
        self.notify_mempool_transaction(transaction);
        Ok(txid)
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
                self.orphans.lock().add(transaction, Some(peer_id));
                Err(error.into())
            }
            Err(error) => Err(error.into()),
        }
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
        let chain = self.chain.read();
        let (result, changes) = {
            let mut mempool = self.mempool.write();
            let result = mempool.accept(transaction, &chain);
            let changes = mempool.take_changes();
            (result, changes)
        };
        let removed_ids = changes
            .iter()
            .filter_map(|change| match &change.kind {
                MempoolChangeKind::Removed { .. } => Some(change.transaction.compute_txid()),
                MempoolChangeKind::Added => None,
            })
            .collect::<Vec<_>>();
        self.announce_mempool_changes(removed_ids);
        self.notify_zmq_mempool_changes(changes.clone());
        result.map(|txid| (txid, changes))
    }

    fn announce_mempool_transaction(&self, txid: Txid) {
        let _ = self.mempool_events.send(txid);
    }

    fn announce_peer_mempool_transaction(&self, txid: Txid, mut excluded_peers: Vec<usize>) {
        excluded_peers.sort_unstable();
        excluded_peers.dedup();
        let _ = self.peer_mempool_events.send(PeerMempoolEvent {
            txid,
            excluded_peers,
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
        let removed = changes
            .iter()
            .filter_map(|change| {
                matches!(change.kind, MempoolChangeKind::Removed { .. })
                    .then_some(change.transaction.compute_txid())
            })
            .collect();
        self.announce_mempool_changes(removed);
        self.notify_zmq_mempool_changes(changes);
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

    fn notify_mempool_transaction_from_peer(&self, transaction: Transaction, peer_id: usize) {
        self.notify_mempool_transaction_with_exclusions(transaction, vec![peer_id]);
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
            let before = self
                .mempool
                .read()
                .transaction_order()
                .into_iter()
                .collect::<HashSet<_>>();
            let chain = self.chain.read();
            let mut mempool = self.mempool.write();
            mempool.revalidate(&chain);
            let after = mempool
                .transaction_order()
                .into_iter()
                .collect::<HashSet<_>>();
            let mempool_changes = mempool.take_changes();
            drop(mempool);
            drop(chain);
            self.announce_mempool_diff(before, after);
            self.notify_zmq_mempool_changes(mempool_changes);
            self.announce_zmq_block_events(&disconnected_blocks, &activated_blocks);
            let _ = self.events.send(tip.clone());
        }
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
            let before = self
                .mempool
                .read()
                .transaction_order()
                .into_iter()
                .collect::<HashSet<_>>();
            let chain = self.chain.read();
            let mut mempool = self.mempool.write();
            mempool.revalidate(&chain);
            let after = mempool
                .transaction_order()
                .into_iter()
                .collect::<HashSet<_>>();
            let mempool_changes = mempool.take_changes();
            drop(mempool);
            drop(chain);
            self.announce_mempool_diff(before, after);
            self.notify_zmq_mempool_changes(mempool_changes);
            self.announce_zmq_block_events(&disconnected_blocks, &activated_blocks);
            let _ = self.events.send(tip.clone());
        }
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

    pub(crate) fn record_bytes_sent(&self, peer_id: usize, bytes: usize, command: &str) {
        let bytes = u64::try_from(bytes).unwrap_or(u64::MAX);
        self.total_bytes_sent.fetch_add(bytes, Ordering::Relaxed);
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.bytes_sent = peer.bytes_sent.saturating_add(bytes);
            peer.last_send = unix_time_seconds();
            let total = peer
                .bytes_sent_per_msg
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

    pub(crate) fn record_peer_transaction(&self, peer_id: usize) {
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.last_transaction = unix_time_seconds();
        }
    }

    pub(crate) fn record_peer_block(&self, peer_id: usize) {
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.last_block = unix_time_seconds();
        }
    }

    pub(crate) fn record_pong(&self, peer_id: usize, nonce: u64) {
        if let Some(peer) = self.peers.write().get_mut(&peer_id)
            && peer.ping_nonce == Some(nonce)
        {
            peer.ping_nonce = None;
            if let Some(sent_at) = peer.ping_sent_at.take() {
                let ping_time = sent_at.elapsed().as_secs_f64();
                peer.ping_time = Some(ping_time);
                peer.min_ping = Some(
                    peer.min_ping
                        .map_or(ping_time, |minimum| minimum.min(ping_time)),
                );
            }
        }
    }

    pub fn network_active(&self) -> bool {
        self.network_active.load(Ordering::Relaxed)
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
        self.register_peer_with_local(id, address, inbound, commands, None);
    }

    pub(crate) fn register_peer_with_local(
        &self,
        id: usize,
        address: SocketAddr,
        inbound: bool,
        commands: tokio::sync::mpsc::UnboundedSender<p2p::PeerCommand>,
        local_address: Option<SocketAddr>,
    ) {
        let connected_at = time::unix_time();
        let peer = PeerInfo {
            id,
            address,
            local_address,
            inbound,
            version: None,
            services: 0,
            user_agent: String::new(),
            start_height: -1,
            relay_transactions: false,
            min_fee_filter: 0,
            transport_protocol_type: "v1",
            connection_type: if inbound { "inbound" } else { "outbound-full" },
            connected_at,
            last_send: 0,
            last_recv: 0,
            bytes_sent: 0,
            bytes_received: 0,
            bytes_sent_per_msg: HashMap::new(),
            bytes_received_per_msg: HashMap::new(),
            last_inv_sequence: 0,
            last_transaction: 0,
            last_block: 0,
            time_offset: 0,
            addr_processed: 0,
            addr_relay_enabled: !inbound,
            ping_time: None,
            min_ping: None,
            ping_nonce: None,
            ping_sent_at: None,
        };
        self.peers.write().insert(id, peer.clone());
        self.peer_commands.write().insert(id, commands);
        let mut known = self.known_addresses.write();
        if self.reserve_known_address(&mut known, address) {
            known.insert(address, peer);
            self.tried_addresses.write().insert(address);
        }
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
            if let Some(known) = self.known_addresses.write().get_mut(&peer.address) {
                known.version = Some(version);
                known.services = services;
                known.user_agent = user_agent.to_owned();
                known.start_height = start_height;
                known.relay_transactions = relay_transactions;
            }
        }
    }

    pub fn update_peer_fee_filter(&self, id: usize, min_fee_filter: i64) {
        let min_fee_filter = min_fee_filter.max(0);
        if let Some(peer) = self.peers.write().get_mut(&id) {
            peer.min_fee_filter = min_fee_filter;
            if let Some(known) = self.known_addresses.write().get_mut(&peer.address) {
                known.min_fee_filter = min_fee_filter;
            }
        }
    }

    pub(crate) fn update_peer_time_offset(&self, id: usize, time_offset: i64) {
        if let Some(peer) = self.peers.write().get_mut(&id) {
            peer.time_offset = time_offset;
        }
    }

    pub(crate) fn record_peer_addresses(&self, id: usize, count: usize) {
        let count = u64::try_from(count).unwrap_or(u64::MAX);
        if let Some(peer) = self.peers.write().get_mut(&id) {
            peer.addr_processed = peer.addr_processed.saturating_add(count);
            if peer.inbound {
                peer.addr_relay_enabled = true;
            }
        }
    }

    pub(crate) fn enable_peer_address_relay(&self, id: usize) {
        if let Some(peer) = self.peers.write().get_mut(&id)
            && peer.inbound
        {
            peer.addr_relay_enabled = true;
        }
    }

    pub(crate) fn relay_peer_addresses(
        &self,
        origin_peer_id: usize,
        addresses: Vec<(SocketAddr, u64, u64)>,
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

    pub(crate) fn set_peer_connection_type(&self, id: usize, connection_type: &'static str) {
        if let Some(peer) = self.peers.write().get_mut(&id) {
            peer.connection_type = connection_type;
            peer.addr_relay_enabled = !peer.inbound && connection_type == "outbound-full";
        }
    }

    pub fn unregister_peer(&self, id: usize) {
        let address = self.peers.write().remove(&id).map(|peer| peer.address);
        self.peer_commands.write().remove(&id);
        if let Some(address) = address
            && let Some(known) = self.known_addresses.write().get_mut(&address)
            && known.id == id
        {
            known.id = 0;
            known.inbound = false;
            known.local_address = None;
            known.ping_nonce = None;
            known.ping_sent_at = None;
        }
        self.orphans.lock().erase_for_peer(id);
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

    pub(crate) fn is_address_tried(&self, address: SocketAddr) -> bool {
        self.tried_addresses.read().contains(&address)
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
                local_address: None,
                inbound: false,
                version: None,
                services: crate::wire::NODE_NETWORK | crate::wire::NODE_WITNESS,
                user_agent: String::new(),
                start_height: 0,
                relay_transactions: true,
                min_fee_filter: 0,
                transport_protocol_type: "v1",
                connection_type: "outbound-full",
                connected_at: now,
                last_send: now,
                last_recv: now,
                bytes_sent: 0,
                bytes_received: 0,
                bytes_sent_per_msg: HashMap::new(),
                bytes_received_per_msg: HashMap::new(),
                last_inv_sequence: 0,
                last_transaction: 0,
                last_block: 0,
                time_offset: 0,
                addr_processed: 0,
                addr_relay_enabled: false,
                ping_time: None,
                min_ping: None,
                ping_nonce: None,
                ping_sent_at: None,
            },
        );
        drop(known);
        if tried {
            self.tried_addresses.write().insert(address);
        }
        true
    }

    pub(crate) fn remember_address(&self, address: SocketAddr, services: u64, time: u64) -> bool {
        let mut known = self.known_addresses.write();
        if !self.reserve_known_address(&mut known, address) {
            return false;
        }
        let is_new = !known.contains_key(&address);
        let entry = known.entry(address).or_insert_with(|| PeerInfo {
            id: 0,
            address,
            local_address: None,
            inbound: false,
            version: None,
            services,
            user_agent: String::new(),
            start_height: 0,
            relay_transactions: true,
            min_fee_filter: 0,
            transport_protocol_type: "v1",
            connection_type: "outbound-full",
            connected_at: time,
            last_send: time,
            last_recv: time,
            bytes_sent: 0,
            bytes_received: 0,
            bytes_sent_per_msg: HashMap::new(),
            bytes_received_per_msg: HashMap::new(),
            last_inv_sequence: 0,
            last_transaction: 0,
            last_block: 0,
            time_offset: 0,
            addr_processed: 0,
            addr_relay_enabled: false,
            ping_time: None,
            min_ping: None,
            ping_nonce: None,
            ping_sent_at: None,
        });
        if entry.id == 0 {
            entry.services |= services;
            entry.connected_at = entry.connected_at.max(time);
            entry.last_send = entry.last_send.max(time);
            entry.last_recv = entry.last_recv.max(time);
        }
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

    pub fn add_node(&self, address: SocketAddr) -> bool {
        let inserted = self.added_nodes.write().insert(address);
        if inserted {
            if let Some(sender) = self.peer_manager_requests.read().as_ref() {
                let _ = sender.send(p2p::PeerManagerRequest::Add(address));
            }
        }
        inserted
    }

    pub(crate) fn request_one_try(&self, address: SocketAddr, transport_v2: Option<bool>) {
        self.request_one_try_with_connection_type(address, transport_v2, "outbound-full");
    }

    pub(crate) fn request_one_try_with_connection_type(
        &self,
        address: SocketAddr,
        transport_v2: Option<bool>,
        connection_type: &'static str,
    ) {
        if let Some(sender) = self.peer_manager_requests.read().as_ref() {
            let _ = sender.send(p2p::PeerManagerRequest::OneTry(
                address,
                transport_v2,
                connection_type,
            ));
        }
    }

    pub fn remove_node(&self, address: &SocketAddr) -> bool {
        let removed = self.added_nodes.write().remove(address);
        self.disconnect_peer_at(*address);
        removed
    }

    pub fn added_nodes(&self) -> Vec<SocketAddr> {
        self.added_nodes.read().iter().copied().collect()
    }

    pub(crate) fn is_node_added(&self, address: SocketAddr) -> bool {
        self.added_nodes.read().contains(&address)
    }

    pub(crate) fn ensure_node_added(&self, address: SocketAddr) {
        self.added_nodes.write().insert(address);
    }

    pub(crate) fn set_peer_manager_sender(
        &self,
        sender: tokio::sync::mpsc::UnboundedSender<p2p::PeerManagerRequest>,
    ) {
        *self.peer_manager_requests.write() = Some(sender);
    }

    pub fn disconnect_peer(&self, id: usize) -> bool {
        self.peer_commands
            .read()
            .get(&id)
            .is_some_and(|sender| sender.send(p2p::PeerCommand::Disconnect).is_ok())
    }

    pub fn disconnect_peer_at(&self, address: SocketAddr) -> bool {
        self.peer_infos()
            .into_iter()
            .filter(|peer| peer.address == address)
            .any(|peer| self.disconnect_peer(peer.id))
    }

    pub fn disconnect_all_peers(&self) {
        let commands: Vec<_> = self.peer_commands.read().values().cloned().collect();
        for sender in commands {
            let _ = sender.send(p2p::PeerCommand::Disconnect);
        }
    }

    pub fn request_block_from_peer(&self, peer_id: usize, hash: bitcoin::BlockHash) -> Result<()> {
        let sender = self
            .peer_commands
            .read()
            .get(&peer_id)
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("peer {peer_id} is not connected"))?;
        sender
            .send(p2p::PeerCommand::RequestBlock(hash))
            .map_err(|_| anyhow::anyhow!("peer {peer_id} disconnected"))
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
        if banned
            .get(&address)
            .is_some_and(|entry| entry.ban_until <= now)
        {
            banned.remove(&address);
        }
        banned.contains_key(&address)
    }

    pub fn banned_addresses(&self) -> Vec<BannedAddress> {
        let addresses: Vec<_> = self.banned_addresses.read().values().cloned().collect();
        addresses
            .into_iter()
            .filter(|entry| self.is_banned(entry.address))
            .collect()
    }

    pub fn ban_address(&self, address: IpAddr, ban_until: u64, reason: String) -> Result<()> {
        let ban_created = time::unix_time();
        self.banned_addresses.write().insert(
            address,
            BannedAddress {
                address,
                ban_created,
                ban_until,
                reason,
            },
        );
        let peers: Vec<_> = self
            .peer_infos()
            .into_iter()
            .filter(|peer| peer.address.ip() == address)
            .map(|peer| peer.id)
            .collect();
        for peer_id in peers {
            self.disconnect_peer(peer_id);
        }
        self.persist_banlist()
    }

    pub fn unban_address(&self, address: IpAddr) -> Result<bool> {
        let removed = self.banned_addresses.write().remove(&address).is_some();
        if removed {
            self.persist_banlist()?;
        }
        Ok(removed)
    }

    pub fn request_shutdown(&self) {
        self.shutdown.notify_waiters();
    }

    pub async fn run(self: Arc<Self>) -> Result<()> {
        let p2p = p2p::PeerManager::new(self.clone());
        let rpc = rpc::RpcServer::new(self.clone());
        let electrum = electrum::ElectrumServer::new(self.clone());
        let mut zmq_task = tokio::spawn(zmq::run(self.config.zmq.clone(), self.subscribe_zmq()));

        info!(
            network = ?self.config.network,
            p2p = %self.config.p2p_bind,
            rpc = ?self.config.rpc_bind,
            electrum = ?self.config.electrum_bind,
            "starting wallet-free Bitcoin node"
        );

        let mut p2p_task = tokio::spawn(p2p.run());
        let mut rpc_task = tokio::spawn(rpc.run());
        let mut electrum_task = tokio::spawn(electrum.run());
        let expiry_node = self.clone();
        let mempool_expiry_task = tokio::spawn(async move {
            let mut ticker = tokio::time::interval(MEMPOOL_EXPIRY_INTERVAL);
            ticker.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
            loop {
                ticker.tick().await;
                expiry_node.expire_mempool();
            }
        });

        tokio::select! {
            result = &mut p2p_task => result??,
            result = &mut rpc_task => result??,
            result = &mut electrum_task => result??,
            result = &mut zmq_task => result??,
            result = tokio::signal::ctrl_c() => result?,
            _ = self.shutdown.notified() => (),
        };

        p2p_task.abort();
        rpc_task.abort();
        electrum_task.abort();
        zmq_task.abort();
        mempool_expiry_task.abort();
        if self.config.persist_mempool {
            self.persist_mempool()?;
        }
        self.persist_known_addresses()?;
        Ok(())
    }

    pub fn persist_mempool(&self) -> Result<()> {
        self.mempool.read().save_to_file(&self.mempool_path)
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
        let chain = self.chain.read();
        let (result, changed, changes) = {
            let mut mempool = self.mempool.write();
            let before = mempool
                .transaction_order()
                .into_iter()
                .collect::<HashSet<_>>();
            let expiry =
                Duration::from_secs(self.config.mempool_expiry_hours.saturating_mul(60 * 60));
            let result = mempool.load_from_file_with_expiry_and_options(
                path.as_ref(),
                &chain,
                expiry,
                options,
            );
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
        if result.is_ok() {
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
        let entries: Vec<_> = self.banned_addresses.read().values().cloned().collect();
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
            })
            .collect::<Vec<_>>();
        entries.sort_by(|left, right| left.address.cmp(&right.address));
        std::fs::write(&temp, serde_json::to_vec_pretty(&entries)?)?;
        std::fs::rename(temp, path)?;
        Ok(())
    }
}

fn load_banlist(data_dir: &Path) -> Result<HashMap<IpAddr, BannedAddress>> {
    let path = data_dir.join("banlist.json");
    if !path.exists() {
        return Ok(HashMap::new());
    }
    let bytes = std::fs::read(path)?;
    let entries: Vec<BannedAddress> = serde_json::from_slice(&bytes)?;
    Ok(entries
        .into_iter()
        .map(|entry| (entry.address, entry))
        .collect())
}

fn load_known_addresses(
    data_dir: &Path,
) -> Result<(HashMap<SocketAddr, PeerInfo>, HashSet<SocketAddr>)> {
    let path = data_dir.join("peers.json");
    if !path.exists() {
        return Ok((HashMap::new(), HashSet::new()));
    }
    let bytes = std::fs::read(path)?;
    let entries: Vec<PersistedAddress> = serde_json::from_slice(&bytes)?;
    let mut known = HashMap::with_capacity(entries.len());
    let mut tried = HashSet::new();
    for entry in entries {
        let address = entry.address.parse::<SocketAddr>()?;
        if entry.tried {
            tried.insert(address);
        }
        known.insert(
            address,
            PeerInfo {
                id: 0,
                address,
                local_address: None,
                inbound: false,
                version: None,
                services: entry.services,
                user_agent: String::new(),
                start_height: 0,
                relay_transactions: true,
                min_fee_filter: 0,
                transport_protocol_type: "v1",
                connection_type: "outbound-full",
                connected_at: entry.time,
                last_send: entry.time,
                last_recv: entry.time,
                bytes_sent: 0,
                bytes_received: 0,
                bytes_sent_per_msg: HashMap::new(),
                bytes_received_per_msg: HashMap::new(),
                last_inv_sequence: 0,
                last_transaction: 0,
                last_block: 0,
                time_offset: 0,
                addr_processed: 0,
                addr_relay_enabled: false,
                ping_time: None,
                min_ping: None,
                ping_nonce: None,
                ping_sent_at: None,
            },
        );
    }
    Ok((known, tried))
}

fn unix_time_seconds() -> u64 {
    time::unix_time()
}

fn load_rpc_cookie(data_dir: &Path) -> Result<String> {
    let path = data_dir.join(".cookie");
    if path.exists() {
        return Ok(std::fs::read_to_string(path)?.trim().to_owned());
    }
    let cookie = format!("__cookie__:{}", hex::encode(random::<[u8; 32]>()));
    let temp = data_dir.join(".cookie.tmp");
    std::fs::write(&temp, &cookie)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&temp, std::fs::Permissions::from_mode(0o600))?;
    }
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

    fn test_config(datadir: &Path) -> Config {
        Config {
            network: bitcoin::Network::Regtest,
            datadir: datadir.to_owned(),
            p2p_bind: "127.0.0.1:0".parse().unwrap(),
            rpc_bind: None,
            electrum_bind: None,
            rest: false,
            listen: true,
            dnsseed: true,
            blocksonly: false,
            prune: 0,
            reindex: false,
            reindex_chainstate: false,
            load_blocks: Vec::new(),
            txindex: false,
            txospenderindex: false,
            max_mempool_mb: 300,
            mempool_expiry_hours: 336,
            coinstatsindex: false,
            blockfilterindex: true,
            peer_block_filters: true,
            persist_mempool: true,
            seed_nodes: Vec::new(),
            signet_challenge: None,
            max_peers: 1,
            peer_bloom_filters: false,
            peer_timeout_secs: 60,
            block_max_weight: 4_000_000,
            block_reserved_weight: 8_000,
            block_min_tx_fee_sat_per_kvb: 1,
            min_relay_tx_fee_sat_per_kvb: 100,
            incremental_relay_fee_sat_per_kvb: 100,
            dust_relay_fee_sat_per_kvb: 3_000,
            max_datacarrier_bytes: Some(100_000),
            permit_bare_multisig: true,
            zmq: crate::config::ZmqConfig::default(),
        }
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
            mempool_sequence == 0,
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
                mempool_sequence: 2,
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
}
