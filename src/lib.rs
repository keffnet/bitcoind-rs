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

use std::path::Path;
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use anyhow::Result;
use bitcoin::Block;
use bitcoin::{Transaction, Txid};
use parking_lot::RwLock;
use rand::random;
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
    pub user_agent: String,
    pub start_height: i32,
    pub connected_at: u64,
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
    peers: parking_lot::RwLock<std::collections::HashMap<usize, PeerInfo>>,
    pub started_at: Instant,
    shutdown: Notify,
}

impl Node {
    pub fn open(config: Config) -> Result<Arc<Self>> {
        let chain = ChainState::open_with_signet_challenge(
            config.network,
            &config.datadir,
            config.signet_challenge.as_deref(),
        )?;
        let mempool_path = config.datadir.join("mempool.json");
        let mut mempool = Mempool::new(config.network);
        mempool.load_from_file(&mempool_path, &chain)?;
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
            peers: parking_lot::RwLock::new(std::collections::HashMap::new()),
            started_at: Instant::now(),
            shutdown: Notify::new(),
        }))
    }

    pub fn connect_block(&self, block: Block) -> Result<ChainEvent> {
        let previous_tip = self.chain.read().best_hash();
        let (tip, activated_blocks) = {
            let mut chain = self.chain.write();
            let tip = chain.connect_block(block)?;
            let activated_blocks = if tip.hash != previous_tip {
                chain.active_blocks_after(previous_tip)?
            } else {
                Vec::new()
            };
            (tip, activated_blocks)
        };
        if !activated_blocks.is_empty() {
            let chain = self.chain.read();
            let mut mempool = self.mempool.write();
            for block in &activated_blocks {
                mempool.remove_confirmed(block);
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

    pub fn subscribe_chain(&self) -> broadcast::Receiver<ChainEvent> {
        self.events.subscribe()
    }

    pub fn subscribe_mempool(&self) -> broadcast::Receiver<MempoolEvent> {
        self.mempool_events.subscribe()
    }

    pub fn peer_count(&self) -> usize {
        self.peer_count.load(Ordering::Relaxed)
    }

    pub fn register_peer(&self, id: usize, address: std::net::SocketAddr, inbound: bool) {
        self.peers.write().insert(
            id,
            PeerInfo {
                id,
                address,
                inbound,
                version: None,
                user_agent: String::new(),
                start_height: 0,
                connected_at: SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap_or_default()
                    .as_secs(),
            },
        );
    }

    pub fn update_peer_version(
        &self,
        id: usize,
        version: i32,
        user_agent: &str,
        start_height: i32,
    ) {
        if let Some(peer) = self.peers.write().get_mut(&id) {
            peer.version = Some(version);
            peer.user_agent = user_agent.to_owned();
            peer.start_height = start_height;
        }
    }

    pub fn unregister_peer(&self, id: usize) {
        self.peers.write().remove(&id);
    }

    pub fn peer_infos(&self) -> Vec<PeerInfo> {
        self.peers.read().values().cloned().collect()
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
