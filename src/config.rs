use std::net::{IpAddr, SocketAddr};
use std::path::PathBuf;

use anyhow::{Context, Result, bail};
use bitcoin::Network;
use clap::{Parser, ValueEnum};

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub enum NetworkName {
    Bitcoin,
    Testnet,
    Signet,
    Regtest,
}

impl From<NetworkName> for Network {
    fn from(value: NetworkName) -> Self {
        match value {
            NetworkName::Bitcoin => Network::Bitcoin,
            NetworkName::Testnet => Network::Testnet,
            NetworkName::Signet => Network::Signet,
            NetworkName::Regtest => Network::Regtest,
        }
    }
}

#[derive(Parser, Debug)]
#[command(
    name = "bitcoind-rs",
    version,
    about = "Wallet-free Bitcoin node and Electrum server"
)]
pub struct Args {
    #[arg(long, value_enum, default_value_t = NetworkName::Bitcoin)]
    pub network: NetworkName,

    #[arg(long, default_value = "./data")]
    pub datadir: PathBuf,

    #[arg(long, default_value = "127.0.0.1:8333")]
    pub p2p: SocketAddr,

    #[arg(long, default_value = "127.0.0.1:8332")]
    pub rpc: SocketAddr,

    #[arg(long, default_value = "127.0.0.1:30001")]
    pub electrum: SocketAddr,

    #[arg(long, value_delimiter = ',')]
    pub connect: Vec<SocketAddr>,

    #[arg(long, default_value_t = 32)]
    pub max_peers: usize,
}

#[derive(Clone, Debug)]
pub struct Config {
    pub network: Network,
    pub datadir: PathBuf,
    pub p2p_bind: SocketAddr,
    pub rpc_bind: Option<SocketAddr>,
    pub electrum_bind: Option<SocketAddr>,
    pub seed_nodes: Vec<SocketAddr>,
    pub max_peers: usize,
}

impl Config {
    pub fn from_args(args: Args) -> Result<Self> {
        if args.max_peers == 0 {
            bail!("--max-peers must be greater than zero");
        }
        if args.p2p.ip() == IpAddr::V4(std::net::Ipv4Addr::UNSPECIFIED) && args.p2p.port() == 0 {
            bail!("--p2p must use a non-zero port when binding all interfaces");
        }
        std::fs::create_dir_all(&args.datadir)
            .with_context(|| format!("creating data directory {}", args.datadir.display()))?;
        Ok(Self {
            network: args.network.into(),
            datadir: args.datadir,
            p2p_bind: args.p2p,
            rpc_bind: Some(args.rpc),
            electrum_bind: Some(args.electrum),
            seed_nodes: args.connect,
            max_peers: args.max_peers,
        })
    }
}
