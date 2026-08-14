use std::net::{IpAddr, SocketAddr};
use std::path::PathBuf;

use anyhow::{Context, Result, bail};
use bitcoin::Network;
use clap::{Parser, ValueEnum};

pub const DEFAULT_ZMQ_HWM: u32 = 1_000;
pub const DEFAULT_MAX_MEMPOOL_MB: u64 = 300;
pub const DEFAULT_MEMPOOL_EXPIRY_HOURS: u64 = 336;
pub const DEFAULT_PEER_TIMEOUT_SECS: u64 = 60;
pub const MIN_AUTO_PRUNE_TARGET_MIB: u64 = 550;
pub const DEFAULT_PERSIST_MEMPOOL: bool = true;
pub const DEFAULT_BLOCKFILTERINDEX: &str = "0";

#[derive(Clone, Debug)]
pub struct ZmqConfig {
    pub tx_reconciliation: bool,
    pub pub_hash_tx: Vec<String>,
    pub pub_hash_block: Vec<String>,
    pub pub_raw_tx: Vec<String>,
    pub pub_raw_block: Vec<String>,
    pub pub_sequence: Vec<String>,
    pub hash_tx_hwm: u32,
    pub hash_block_hwm: u32,
    pub raw_tx_hwm: u32,
    pub raw_block_hwm: u32,
    pub sequence_hwm: u32,
}

impl Default for ZmqConfig {
    fn default() -> Self {
        Self {
            tx_reconciliation: false,
            pub_hash_tx: Vec::new(),
            pub_hash_block: Vec::new(),
            pub_raw_tx: Vec::new(),
            pub_raw_block: Vec::new(),
            pub_sequence: Vec::new(),
            hash_tx_hwm: DEFAULT_ZMQ_HWM,
            hash_block_hwm: DEFAULT_ZMQ_HWM,
            raw_tx_hwm: DEFAULT_ZMQ_HWM,
            raw_block_hwm: DEFAULT_ZMQ_HWM,
            sequence_hwm: DEFAULT_ZMQ_HWM,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZmqNotification {
    pub kind: &'static str,
    pub address: String,
    pub hwm: u32,
}

impl ZmqConfig {
    pub fn is_enabled(&self) -> bool {
        !self.pub_hash_tx.is_empty()
            || !self.pub_hash_block.is_empty()
            || !self.pub_raw_tx.is_empty()
            || !self.pub_raw_block.is_empty()
            || !self.pub_sequence.is_empty()
    }

    pub fn notifications(&self) -> Vec<ZmqNotification> {
        [
            ("pubhashblock", &self.pub_hash_block, self.hash_block_hwm),
            ("pubhashtx", &self.pub_hash_tx, self.hash_tx_hwm),
            ("pubrawblock", &self.pub_raw_block, self.raw_block_hwm),
            ("pubrawtx", &self.pub_raw_tx, self.raw_tx_hwm),
            ("pubsequence", &self.pub_sequence, self.sequence_hwm),
        ]
        .into_iter()
        .flat_map(|(kind, addresses, hwm)| {
            addresses.iter().map(move |address| ZmqNotification {
                kind,
                address: normalize_address(address),
                hwm,
            })
        })
        .collect()
    }
}

fn normalize_address(address: &str) -> String {
    address
        .strip_prefix("unix:")
        .map_or_else(|| address.to_owned(), |path| format!("ipc://{path}"))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub enum NetworkName {
    Bitcoin,
    Testnet,
    Testnet4,
    Signet,
    Regtest,
}

impl From<NetworkName> for Network {
    fn from(value: NetworkName) -> Self {
        match value {
            NetworkName::Bitcoin => Network::Bitcoin,
            NetworkName::Testnet => Network::Testnet,
            NetworkName::Testnet4 => Network::Testnet4,
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

    #[arg(
        long,
        default_value_t = true,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub listen: bool,

    #[arg(
        long,
        default_value_t = true,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub dnsseed: bool,

    #[arg(long, default_value = "127.0.0.1:8332")]
    pub rpc: SocketAddr,

    #[arg(long, default_value = "127.0.0.1:30001")]
    pub electrum: SocketAddr,

    #[arg(long, default_value_t = false)]
    pub rest: bool,

    #[arg(long, value_delimiter = ',')]
    pub connect: Vec<SocketAddr>,

    #[arg(long, value_name = "HEX")]
    pub signet_challenge: Option<String>,

    #[arg(long, visible_alias = "maxconnections", default_value_t = 125)]
    pub max_peers: usize,

    #[arg(long, default_value_t = DEFAULT_PEER_TIMEOUT_SECS)]
    pub peertimeout: u64,

    #[arg(long, default_value_t = false)]
    pub peer_bloom_filters: bool,

    #[arg(
        long,
        default_value_t = false,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub blocksonly: bool,

    #[arg(long, default_value_t = 0)]
    pub prune: u64,

    #[arg(long, default_value_t = false)]
    pub txindex: bool,

    #[arg(long, default_value_t = false)]
    pub txospenderindex: bool,

    #[arg(long, default_value_t = false)]
    pub coinstatsindex: bool,

    #[arg(
        long,
        default_value = DEFAULT_BLOCKFILTERINDEX,
        num_args = 0..=1,
        default_missing_value = "basic"
    )]
    pub blockfilterindex: String,

    #[arg(
        long,
        default_value_t = false,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub peerblockfilters: bool,

    #[arg(long = "maxmempool", default_value_t = DEFAULT_MAX_MEMPOOL_MB)]
    pub max_mempool: u64,

    #[arg(long, default_value_t = DEFAULT_MEMPOOL_EXPIRY_HOURS)]
    pub mempoolexpiry: u64,

    #[arg(
        long,
        default_value_t = DEFAULT_PERSIST_MEMPOOL,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub persistmempool: bool,

    #[arg(long, default_value_t = false, hide = true)]
    pub tx_reconciliation: bool,

    #[arg(long = "zmqpubhashtx", value_name = "ADDRESS")]
    pub zmq_pub_hash_tx: Vec<String>,

    #[arg(long = "zmqpubhashblock", value_name = "ADDRESS")]
    pub zmq_pub_hash_block: Vec<String>,

    #[arg(long = "zmqpubrawtx", value_name = "ADDRESS")]
    pub zmq_pub_raw_tx: Vec<String>,

    #[arg(long = "zmqpubrawblock", value_name = "ADDRESS")]
    pub zmq_pub_raw_block: Vec<String>,

    #[arg(long = "zmqpubsequence", value_name = "ADDRESS")]
    pub zmq_pub_sequence: Vec<String>,

    #[arg(long = "zmqpubhashtxhwm", default_value_t = DEFAULT_ZMQ_HWM)]
    pub zmq_pub_hash_tx_hwm: u32,

    #[arg(long = "zmqpubhashblockhwm", default_value_t = DEFAULT_ZMQ_HWM)]
    pub zmq_pub_hash_block_hwm: u32,

    #[arg(long = "zmqpubrawtxhwm", default_value_t = DEFAULT_ZMQ_HWM)]
    pub zmq_pub_raw_tx_hwm: u32,

    #[arg(long = "zmqpubrawblockhwm", default_value_t = DEFAULT_ZMQ_HWM)]
    pub zmq_pub_raw_block_hwm: u32,

    #[arg(long = "zmqpubsequencehwm", default_value_t = DEFAULT_ZMQ_HWM)]
    pub zmq_pub_sequence_hwm: u32,
}

#[derive(Clone, Debug)]
pub struct Config {
    pub network: Network,
    pub datadir: PathBuf,
    pub p2p_bind: SocketAddr,
    pub listen: bool,
    pub rpc_bind: Option<SocketAddr>,
    pub electrum_bind: Option<SocketAddr>,
    pub rest: bool,
    pub seed_nodes: Vec<SocketAddr>,
    pub dnsseed: bool,
    pub signet_challenge: Option<Vec<u8>>,
    pub max_peers: usize,
    pub peer_timeout_secs: u64,
    pub peer_bloom_filters: bool,
    pub blocksonly: bool,
    /// Pruning mode: 0 disabled, 1 manual, or a target size in MiB.
    pub prune: u64,
    pub txindex: bool,
    pub txospenderindex: bool,
    pub coinstatsindex: bool,
    pub blockfilterindex: bool,
    pub peer_block_filters: bool,
    /// Maximum mempool size in decimal megabytes, matching Core's option.
    pub max_mempool_mb: u64,
    /// Maximum age of a mempool entry in hours.
    pub mempool_expiry_hours: u64,
    /// Load and save the mempool automatically across node restarts.
    pub persist_mempool: bool,
    pub zmq: ZmqConfig,
}

impl Config {
    pub fn from_args(args: Args) -> Result<Self> {
        if args.max_peers == 0 {
            bail!("--max-peers must be greater than zero");
        }
        if args.peertimeout == 0 {
            bail!("--peertimeout must be greater than zero");
        }
        if args.prune != 0 && args.prune != 1 && args.prune < MIN_AUTO_PRUNE_TARGET_MIB {
            bail!("--prune automatic target must be at least {MIN_AUTO_PRUNE_TARGET_MIB} MiB");
        }
        if (args.txindex || args.txospenderindex) && args.prune != 0 {
            bail!("Prune mode is incompatible with transaction indexes.");
        }
        if args.max_mempool == 0 {
            bail!("--maxmempool must be greater than zero");
        }
        if args.mempoolexpiry == 0 {
            bail!("--mempoolexpiry must be greater than zero");
        }
        if [
            args.zmq_pub_hash_tx_hwm,
            args.zmq_pub_hash_block_hwm,
            args.zmq_pub_raw_tx_hwm,
            args.zmq_pub_raw_block_hwm,
            args.zmq_pub_sequence_hwm,
        ]
        .contains(&0)
        {
            bail!("ZMQ high water marks must be greater than zero");
        }
        if args.listen
            && args.p2p.ip() == IpAddr::V4(std::net::Ipv4Addr::UNSPECIFIED)
            && args.p2p.port() == 0
        {
            bail!("--p2p must use a non-zero port when binding all interfaces");
        }
        let signet_challenge = match args.signet_challenge {
            Some(_challenge) if args.network != NetworkName::Signet => {
                bail!("--signet-challenge requires --network signet")
            }
            Some(challenge) => Some(
                hex::decode(&challenge).with_context(|| "decoding --signet-challenge as hex")?,
            ),
            None => None,
        };
        let blockfilterindex = match args.blockfilterindex.as_str() {
            "0" | "false" => false,
            "1" | "true" | "basic" => true,
            value => bail!("unknown --blockfilterindex value {value}"),
        };
        if args.peerblockfilters && !blockfilterindex {
            bail!("--peerblockfilters requires --blockfilterindex");
        }
        std::fs::create_dir_all(&args.datadir)
            .with_context(|| format!("creating data directory {}", args.datadir.display()))?;
        Ok(Self {
            network: args.network.into(),
            datadir: args.datadir,
            p2p_bind: args.p2p,
            listen: args.listen,
            rpc_bind: Some(args.rpc),
            electrum_bind: Some(args.electrum),
            rest: args.rest,
            seed_nodes: args.connect,
            dnsseed: args.dnsseed,
            signet_challenge,
            max_peers: args.max_peers,
            peer_timeout_secs: args.peertimeout,
            peer_bloom_filters: args.peer_bloom_filters,
            blocksonly: args.blocksonly,
            prune: args.prune,
            txindex: args.txindex,
            txospenderindex: args.txospenderindex,
            coinstatsindex: args.coinstatsindex,
            blockfilterindex,
            peer_block_filters: args.peerblockfilters,
            max_mempool_mb: args.max_mempool,
            mempool_expiry_hours: args.mempoolexpiry,
            persist_mempool: args.persistmempool,
            zmq: ZmqConfig {
                tx_reconciliation: args.tx_reconciliation,
                pub_hash_tx: args.zmq_pub_hash_tx,
                pub_hash_block: args.zmq_pub_hash_block,
                pub_raw_tx: args.zmq_pub_raw_tx,
                pub_raw_block: args.zmq_pub_raw_block,
                pub_sequence: args.zmq_pub_sequence,
                hash_tx_hwm: args.zmq_pub_hash_tx_hwm,
                hash_block_hwm: args.zmq_pub_hash_block_hwm,
                raw_tx_hwm: args.zmq_pub_raw_tx_hwm,
                raw_block_hwm: args.zmq_pub_raw_block_hwm,
                sequence_hwm: args.zmq_pub_sequence_hwm,
            },
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_core_style_network_policy_switches() {
        let directory = tempfile::tempdir().unwrap();
        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--p2p",
            "0.0.0.0:0",
            "--listen=false",
            "--dnsseed=0",
            "--blocksonly=1",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert!(!config.listen);
        assert!(!config.dnsseed);
        assert!(config.blocksonly);
        assert_eq!(config.prune, 0);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--peertimeout=15",
        ])
        .unwrap();
        assert_eq!(Config::from_args(args).unwrap().peer_timeout_secs, 15);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--peertimeout=0",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());
    }

    #[test]
    fn parses_and_validates_pruning_modes() {
        let directory = tempfile::tempdir().unwrap();
        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--prune=1",
        ])
        .unwrap();
        assert_eq!(Config::from_args(args).unwrap().prune, 1);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--prune",
            "550",
        ])
        .unwrap();
        assert_eq!(Config::from_args(args).unwrap().prune, 550);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--prune",
            "549",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--blockfilterindex=basic",
            "--peerblockfilters",
        ])
        .unwrap();
        assert!(Config::from_args(args).unwrap().peer_block_filters);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--peerblockfilters",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--coinstatsindex",
        ])
        .unwrap();
        assert!(Config::from_args(args).unwrap().coinstatsindex);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--maxmempool",
            "12",
        ])
        .unwrap();
        assert_eq!(Config::from_args(args).unwrap().max_mempool_mb, 12);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--mempoolexpiry",
            "24",
        ])
        .unwrap();
        assert_eq!(Config::from_args(args).unwrap().mempool_expiry_hours, 24);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--mempoolexpiry=0",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--persistmempool=false",
        ])
        .unwrap();
        assert!(!Config::from_args(args).unwrap().persist_mempool);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--maxmempool=0",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--txindex",
        ])
        .unwrap();
        assert!(Config::from_args(args).unwrap().txindex);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--txospenderindex",
        ])
        .unwrap();
        assert!(Config::from_args(args).unwrap().txospenderindex);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--blockfilterindex=basic",
        ])
        .unwrap();
        assert!(Config::from_args(args).unwrap().blockfilterindex);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--blockfilterindex=unknown",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--prune=1",
            "--txindex",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--prune=1",
            "--txospenderindex",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());
    }
}
