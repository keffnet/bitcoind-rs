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

use std::collections::{HashMap, HashSet, VecDeque};
use std::net::{IpAddr, SocketAddr};
use std::path::Path;
use std::sync::{
    Arc,
    atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering},
};
use std::time::{Duration, Instant};

use anyhow::Result;
use bitcoin::Block;
use bitcoin::{OutPoint, Transaction, Txid};
use parking_lot::RwLock;
use rand::random;
use serde::{Deserialize, Serialize};
use tokio::sync::{Notify, broadcast};
use tracing::info;

use crate::chain::ChainState;
use crate::config::Config;
use crate::mempool::{Mempool, MempoolError};

const MAX_ORPHAN_TRANSACTIONS: usize = 100;
const MAX_ORPHAN_TRANSACTION_WEIGHT: u64 = 400_000;
const ORPHAN_TRANSACTION_EXPIRY: Duration = Duration::from_secs(20 * 60);

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
    pub connected_at: u64,
    pub last_send: u64,
    pub last_recv: u64,
    pub bytes_sent: u64,
    pub bytes_received: u64,
    pub ping_time: Option<f64>,
    pub min_ping: Option<f64>,
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
    pub rpc_cookie: Option<String>,
    mempool_path: std::path::PathBuf,
    pub peer_count: AtomicUsize,
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
        let chain = ChainState::open_with_signet_challenge(
            config.network,
            &config.datadir,
            config.signet_challenge.as_deref(),
        )?;
        let mempool_path = config.datadir.join("mempool.json");
        let mut mempool = Mempool::new(config.network);
        mempool.load_from_file(&mempool_path, &chain)?;
        let banned_addresses = load_banlist(&config.datadir)?;
        let (known_addresses, tried_addresses) = load_known_addresses(&config.datadir)?;
        let (events, _) = broadcast::channel(256);
        let (mempool_events, _) = broadcast::channel(256);
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
            rpc_cookie,
            mempool_path,
            peer_count: AtomicUsize::new(0),
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
                    let _ = mempool.accept(transaction.clone(), &chain);
                }
            }
            mempool.revalidate(&chain);
            let _ = self.events.send(tip.clone());

            drop(mempool);
            drop(chain);
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
        let txid = self.try_accept_transaction(transaction.clone())?;
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
            Ok(txid) => {
                self.notify_mempool_transaction(transaction);
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
    ) -> std::result::Result<Txid, MempoolError> {
        let chain = self.chain.read();
        self.mempool.write().accept(transaction, &chain)
    }

    fn announce_mempool_transaction(&self, txid: Txid) {
        let _ = self.mempool_events.send(txid);
    }

    pub(crate) fn notify_mempool_transaction(&self, transaction: Transaction) {
        let txid = transaction.compute_txid();
        self.orphans.lock().remove(&txid);
        self.announce_mempool_transaction(txid);
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
                Ok(txid) => {
                    self.announce_mempool_transaction(txid);
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
        let (tip, changed) = {
            let mut chain = self.chain.write();
            let previous = chain.best_hash();
            let tip = chain.invalidate_block(&hash)?;
            (tip, previous != chain.best_hash())
        };
        if changed {
            self.mempool.write().revalidate(&self.chain.read());
            let _ = self.events.send(tip.clone());
        }
        Ok(tip)
    }

    pub fn reconsider_block(&self, hash: bitcoin::BlockHash) -> Result<ChainEvent> {
        let (tip, changed) = {
            let mut chain = self.chain.write();
            let previous = chain.best_hash();
            let tip = chain.reconsider_block(&hash)?;
            (tip, previous != chain.best_hash())
        };
        if changed {
            self.mempool.write().revalidate(&self.chain.read());
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

    pub(crate) fn record_bytes_sent(&self, peer_id: usize, bytes: usize) {
        let bytes = u64::try_from(bytes).unwrap_or(u64::MAX);
        self.total_bytes_sent.fetch_add(bytes, Ordering::Relaxed);
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.bytes_sent = peer.bytes_sent.saturating_add(bytes);
            peer.last_send = unix_time_seconds();
        }
    }

    pub(crate) fn record_bytes_received(&self, peer_id: usize, bytes: usize) {
        let bytes = u64::try_from(bytes).unwrap_or(u64::MAX);
        self.total_bytes_received
            .fetch_add(bytes, Ordering::Relaxed);
        if let Some(peer) = self.peers.write().get_mut(&peer_id) {
            peer.bytes_received = peer.bytes_received.saturating_add(bytes);
            peer.last_recv = unix_time_seconds();
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
            start_height: 0,
            relay_transactions: true,
            min_fee_filter: 0,
            connected_at,
            last_send: connected_at,
            last_recv: connected_at,
            bytes_sent: 0,
            bytes_received: 0,
            ping_time: None,
            min_ping: None,
            ping_nonce: None,
            ping_sent_at: None,
        };
        self.peers.write().insert(id, peer.clone());
        self.peer_commands.write().insert(id, commands);
        self.known_addresses.write().insert(address, peer);
        self.tried_addresses.write().insert(address);
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

    pub fn unregister_peer(&self, id: usize) {
        self.peers.write().remove(&id);
        self.peer_commands.write().remove(&id);
        self.orphans.lock().erase_for_peer(id);
    }

    pub fn peer_infos(&self) -> Vec<PeerInfo> {
        self.peers.read().values().cloned().collect()
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
                connected_at: now,
                last_send: now,
                last_recv: now,
                bytes_sent: 0,
                bytes_received: 0,
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

    pub(crate) fn remember_address(&self, address: SocketAddr, services: u64, time: u64) {
        let mut known = self.known_addresses.write();
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
            connected_at: time,
            last_send: time,
            last_recv: time,
            bytes_sent: 0,
            bytes_received: 0,
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
        if let Some(sender) = self.peer_manager_requests.read().as_ref() {
            let _ = sender.send(p2p::PeerManagerRequest::OneTry(address, transport_v2));
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
            if sender.send(p2p::PeerCommand::Ping(nonce)).is_ok()
                && let Some(peer) = self.peers.write().get_mut(&peer_id)
            {
                peer.ping_nonce = Some(nonce);
                peer.ping_sent_at = Some(Instant::now());
            }
        }
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

        tokio::select! {
            result = &mut p2p_task => result??,
            result = &mut rpc_task => result??,
            result = &mut electrum_task => result??,
            result = tokio::signal::ctrl_c() => result?,
            _ = self.shutdown.notified() => (),
        };

        p2p_task.abort();
        rpc_task.abort();
        electrum_task.abort();
        self.persist_mempool()?;
        self.persist_known_addresses()?;
        Ok(())
    }

    pub fn persist_mempool(&self) -> Result<()> {
        self.mempool.read().save_to_file(&self.mempool_path)
    }

    pub fn import_mempool(&self, path: impl AsRef<Path>) -> Result<()> {
        let chain = self.chain.read();
        self.mempool.write().load_from_file(path.as_ref(), &chain)
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
                connected_at: entry.time,
                last_send: entry.time,
                last_recv: entry.time,
                bytes_sent: 0,
                bytes_received: 0,
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
            seed_nodes: Vec::new(),
            signet_challenge: None,
            max_peers: 1,
            peer_bloom_filters: false,
        }
    }

    fn mine_test_block(previous: &Header, height: u32, tag: u8) -> Block {
        let mut block = Block {
            header: Header {
                version: BlockVersion::TWO,
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
}
