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

use std::sync::Arc;

use anyhow::Result;
use parking_lot::RwLock;
use tracing::info;

use crate::chain::ChainState;
use crate::config::Config;
use crate::mempool::Mempool;

/// The wallet-free node facade shared by the network and RPC services.
pub struct Node {
    pub config: Config,
    pub chain: Arc<RwLock<ChainState>>,
    pub mempool: Arc<RwLock<Mempool>>,
}

impl Node {
    pub fn open(config: Config) -> Result<Arc<Self>> {
        let chain = ChainState::open(config.network, &config.datadir)?;
        let mempool = Mempool::new(config.network);
        Ok(Arc::new(Self {
            config,
            chain: Arc::new(RwLock::new(chain)),
            mempool: Arc::new(RwLock::new(mempool)),
        }))
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
