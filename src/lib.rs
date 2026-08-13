#![forbid(unsafe_code)]
#![warn(rust_2018_idioms, clippy::all)]

pub mod chain;
pub mod config;
pub mod electrum;
pub mod mempool;
pub mod p2p;
pub mod rpc;
pub mod storage;
pub mod validation;
pub mod wire;

use std::collections::{HashMap, HashSet};
use std::net::{IpAddr, SocketAddr};
use std::path::Path;
use std::sync::{
    Arc,
    atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering},
};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use anyhow::Result;
use bitcoin::Block;
use bitcoin::{Transaction, Txid};
use parking_lot::RwLock;
use rand::random;
use serde::{Deserialize, Serialize};
use tokio::sync::{Notify, broadcast};
use tracing::info;

use crate::chain::ChainState;
use crate::config::Config;
use crate::mempool::Mempool;

pub type ChainEvent = chain::ChainTip;
pub type MempoolEvent = Txid;

#[derive(Clone, Debug)]
pub struct PeerInfo {
    pub id: usize,
    pub address: std::net::SocketAddr,
    pub inbound: bool,
    pub version: Option<i32>,
    pub services: u64,
    pub user_agent: String,
    pub start_height: i32,
    pub relay_transactions: bool,
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
    total_bytes_sent: AtomicU64,
    total_bytes_received: AtomicU64,
    network_active: AtomicBool,
    peers: parking_lot::RwLock<HashMap<usize, PeerInfo>>,
    peer_commands:
        parking_lot::RwLock<HashMap<usize, tokio::sync::mpsc::UnboundedSender<p2p::PeerCommand>>>,
    peer_manager_requests:
        parking_lot::RwLock<Option<tokio::sync::mpsc::UnboundedSender<SocketAddr>>>,
    known_addresses: parking_lot::RwLock<HashMap<SocketAddr, PeerInfo>>,
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
            total_bytes_sent: AtomicU64::new(0),
            total_bytes_received: AtomicU64::new(0),
            network_active: AtomicBool::new(true),
            peers: parking_lot::RwLock::new(HashMap::new()),
            peer_commands: parking_lot::RwLock::new(HashMap::new()),
            peer_manager_requests: parking_lot::RwLock::new(None),
            known_addresses: parking_lot::RwLock::new(HashMap::new()),
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
        }
        Ok(tip)
    }

    pub fn accept_transaction(&self, transaction: Transaction) -> Result<Txid> {
        let chain = self.chain.read();
        let txid = self.mempool.write().accept(transaction, &chain)?;
        let _ = self.mempool_events.send(txid);
        Ok(txid)
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

    pub(crate) fn register_peer(
        &self,
        id: usize,
        address: SocketAddr,
        inbound: bool,
        commands: tokio::sync::mpsc::UnboundedSender<p2p::PeerCommand>,
    ) {
        let connected_at = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();
        let peer = PeerInfo {
            id,
            address,
            inbound,
            version: None,
            services: 0,
            user_agent: String::new(),
            start_height: 0,
            relay_transactions: true,
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

    pub fn unregister_peer(&self, id: usize) {
        self.peers.write().remove(&id);
        self.peer_commands.write().remove(&id);
    }

    pub fn peer_infos(&self) -> Vec<PeerInfo> {
        self.peers.read().values().cloned().collect()
    }

    pub fn known_addresses(&self) -> Vec<PeerInfo> {
        self.known_addresses.read().values().cloned().collect()
    }

    pub fn add_node(&self, address: SocketAddr) -> bool {
        let inserted = self.added_nodes.write().insert(address);
        if inserted {
            if let Some(sender) = self.peer_manager_requests.read().as_ref() {
                let _ = sender.send(address);
            }
        }
        inserted
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
        sender: tokio::sync::mpsc::UnboundedSender<SocketAddr>,
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
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();
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
        let ban_created = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();
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
        Ok(())
    }

    pub fn persist_mempool(&self) -> Result<()> {
        self.mempool.read().save_to_file(&self.mempool_path)
    }

    fn persist_banlist(&self) -> Result<()> {
        let path = self.config.datadir.join("banlist.json");
        let temp = self.config.datadir.join("banlist.json.tmp");
        let entries: Vec<_> = self.banned_addresses.read().values().cloned().collect();
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

fn unix_time_seconds() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
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
