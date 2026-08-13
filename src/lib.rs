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
use std::sync::Arc;

use anyhow::Result;
use bitcoin::Block;
use parking_lot::RwLock;
use rand::random;
use tokio::sync::broadcast;
use tracing::info;

use crate::chain::ChainState;
use crate::config::Config;
use crate::mempool::Mempool;

pub type ChainEvent = chain::ChainTip;

/// The wallet-free node facade shared by the network and RPC services.
pub struct Node {
    pub config: Config,
    pub chain: Arc<RwLock<ChainState>>,
    pub mempool: Arc<RwLock<Mempool>>,
    pub events: broadcast::Sender<ChainEvent>,
    pub rpc_cookie: Option<String>,
}

impl Node {
    pub fn open(config: Config) -> Result<Arc<Self>> {
        let chain = ChainState::open(config.network, &config.datadir)?;
        let mempool = Mempool::new(config.network);
        let (events, _) = broadcast::channel(256);
        let rpc_cookie = config
            .rpc_bind
            .map(|_| load_rpc_cookie(&config.datadir))
            .transpose()?;
        Ok(Arc::new(Self {
            config,
            chain: Arc::new(RwLock::new(chain)),
            mempool: Arc::new(RwLock::new(mempool)),
            events,
            rpc_cookie,
        }))
    }

    pub fn connect_block(&self, block: Block) -> Result<ChainEvent> {
        let hash = block.block_hash();
        let previous_tip = self.chain.read().best_hash();
        let tip = self.chain.write().connect_block(block.clone())?;
        if tip.hash != previous_tip && self.chain.read().is_active_block(&hash) {
            self.mempool.write().remove_confirmed(&block);
            let _ = self.events.send(tip.clone());
        }
        Ok(tip)
    }

    pub fn subscribe_chain(&self) -> broadcast::Receiver<ChainEvent> {
        self.events.subscribe()
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

        let p2p_task = tokio::spawn(p2p.run());
        let rpc_task = tokio::spawn(rpc.run());
        let electrum_task = tokio::spawn(electrum.run());

        tokio::select! {
            result = p2p_task => result??,
            result = rpc_task => result??,
            result = electrum_task => result??,
            result = tokio::signal::ctrl_c() => result?,
        }

        Ok(())
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
