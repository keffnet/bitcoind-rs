use std::net::{IpAddr, SocketAddr};
use std::path::PathBuf;

use anyhow::{Context, Result, bail};
use bitcoin::{Amount, Denomination, Network};
use clap::{Parser, ValueEnum};

use crate::address::NetworkEndpoint;

pub const DEFAULT_ZMQ_HWM: u32 = 1_000;
pub const DEFAULT_MAX_MEMPOOL_MB: u64 = 300;
pub const DEFAULT_BLOCKSONLY_MAX_MEMPOOL_MB: u64 = 5;
pub const DEFAULT_MAX_UPLOAD_TARGET: &str = "0M";
pub const DEFAULT_MEMPOOL_EXPIRY_HOURS: u64 = 336;
pub const DEFAULT_PEER_TIMEOUT_SECS: u64 = 60;
pub const DEFAULT_BLOCK_MAX_WEIGHT: u64 = 4_000_000;
pub const DEFAULT_BLOCK_RESERVED_WEIGHT: u64 = 8_000;
pub const MINIMUM_BLOCK_RESERVED_WEIGHT: u64 = 2_000;
pub const DEFAULT_BLOCK_MIN_TX_FEE_SAT_PER_KVB: u64 = 1;
pub const DEFAULT_MIN_RELAY_TX_FEE_SAT_PER_KVB: u64 = 100;
pub const DEFAULT_INCREMENTAL_RELAY_FEE_SAT_PER_KVB: u64 = 100;
pub const DEFAULT_DUST_RELAY_FEE_SAT_PER_KVB: u64 = 3_000;
pub const DEFAULT_MAX_DATACARRIER_BYTES: u64 = 100_000;
pub const DEFAULT_ACCEPT_DATACARRIER: bool = true;
pub const DEFAULT_PERMIT_BARE_MULTISIG: bool = true;
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

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, ValueEnum)]
pub enum OnlyNet {
    Ipv4,
    Ipv6,
    Onion,
    I2p,
    Cjdns,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PeerPermissions(u32);

impl PeerPermissions {
    pub const BLOOM_FILTER: Self = Self(1 << 0);
    pub const RELAY: Self = Self(1 << 1);
    pub const FORCE_RELAY: Self = Self((1 << 2) | (1 << 1));
    pub const NO_BAN: Self = Self((1 << 3) | (1 << 5));
    pub const MEMPOOL: Self = Self(1 << 4);
    pub const DOWNLOAD: Self = Self(1 << 5);
    pub const ADDR: Self = Self(1 << 6);
    const IMPLICIT: Self = Self(1 << 31);

    const ALL: Self = Self(
        Self::BLOOM_FILTER.0
            | Self::FORCE_RELAY.0
            | Self::NO_BAN.0
            | Self::MEMPOOL.0
            | Self::ADDR.0,
    );

    pub const fn empty() -> Self {
        Self(0)
    }

    pub const fn contains(self, permission: Self) -> bool {
        self.0 & permission.0 == permission.0
    }

    const fn union(self, permission: Self) -> Self {
        Self(self.0 | permission.0)
    }

    const fn without(self, permission: Self) -> Self {
        Self(self.0 & !permission.0)
    }

    pub fn to_strings(self) -> Vec<&'static str> {
        let mut permissions = Vec::new();
        if self.contains(Self::BLOOM_FILTER) {
            permissions.push("bloomfilter");
        }
        if self.contains(Self::NO_BAN) {
            permissions.push("noban");
        }
        if self.contains(Self::FORCE_RELAY) {
            permissions.push("forcerelay");
        }
        if self.contains(Self::RELAY) {
            permissions.push("relay");
        }
        if self.contains(Self::MEMPOOL) {
            permissions.push("mempool");
        }
        if self.contains(Self::DOWNLOAD) {
            permissions.push("download");
        }
        if self.contains(Self::ADDR) {
            permissions.push("addr");
        }
        permissions
    }

    fn parse_flags(value: &str) -> Result<(Self, bool, bool)> {
        let mut flags = Self::empty();
        let mut incoming = false;
        let mut outgoing = false;
        for name in value.split(',') {
            match name {
                "" => {}
                "bloom" | "bloomfilter" => flags = flags.union(Self::BLOOM_FILTER),
                "noban" => flags = flags.union(Self::NO_BAN),
                "forcerelay" => flags = flags.union(Self::FORCE_RELAY),
                "relay" => flags = flags.union(Self::RELAY),
                "mempool" => flags = flags.union(Self::MEMPOOL),
                "download" => flags = flags.union(Self::DOWNLOAD),
                "addr" => flags = flags.union(Self::ADDR),
                "all" => flags = flags.union(Self::ALL),
                "in" => incoming = true,
                "out" => outgoing = true,
                name => bail!("invalid P2P permission: '{name}'"),
            }
        }
        if !incoming && !outgoing {
            incoming = true;
        } else if flags == Self::empty() {
            bail!("only direction was set, no permissions: '{value}'");
        }
        Ok((flags, incoming, outgoing))
    }

    fn implicit() -> Self {
        Self::IMPLICIT
    }

    fn resolve(self, whitelist_relay: bool, whitelist_force_relay: bool) -> Self {
        if !self.contains(Self::IMPLICIT) {
            return self;
        }
        let mut resolved = self.without(Self::IMPLICIT);
        if whitelist_force_relay {
            resolved = resolved.union(Self::FORCE_RELAY);
        }
        if whitelist_relay {
            resolved = resolved.union(Self::RELAY);
        }
        resolved.union(Self::MEMPOOL).union(Self::NO_BAN)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WhitelistSubnet {
    address: IpAddr,
    prefix: u8,
}

impl WhitelistSubnet {
    fn parse(value: &str) -> Result<Self> {
        let mut parts = value.split('/');
        let address = parts
            .next()
            .ok_or_else(|| anyhow::anyhow!("invalid IP/Subnet"))?
            .parse::<IpAddr>()
            .map_err(|_| anyhow::anyhow!("invalid IP/Subnet"))?;
        let prefix = match parts.next() {
            Some(prefix) => prefix
                .parse::<u8>()
                .map_err(|_| anyhow::anyhow!("invalid IP/Subnet"))?,
            None => match address {
                IpAddr::V4(_) => 32,
                IpAddr::V6(_) => 128,
            },
        };
        if parts.next().is_some() {
            bail!("invalid IP/Subnet");
        }
        let bits = match address {
            IpAddr::V4(_) => 32,
            IpAddr::V6(_) => 128,
        };
        if prefix > bits {
            bail!("invalid IP/Subnet");
        }
        Ok(Self {
            address: mask_address(address, prefix),
            prefix,
        })
    }

    fn contains(self, address: IpAddr) -> bool {
        let bits = match address {
            IpAddr::V4(_) => 32,
            IpAddr::V6(_) => 128,
        };
        if bits
            != match self.address {
                IpAddr::V4(_) => 32,
                IpAddr::V6(_) => 128,
            }
        {
            return false;
        }
        mask_address(address, self.prefix) == self.address
    }
}

fn mask_address(address: IpAddr, prefix: u8) -> IpAddr {
    match address {
        IpAddr::V4(address) => {
            let mask = if prefix == 0 {
                0
            } else {
                u32::MAX << (32 - u32::from(prefix))
            };
            IpAddr::V4(std::net::Ipv4Addr::from(u32::from(address) & mask))
        }
        IpAddr::V6(address) => {
            let mask = if prefix == 0 {
                0
            } else {
                u128::MAX << (128 - u32::from(prefix))
            };
            IpAddr::V6(std::net::Ipv6Addr::from(u128::from(address) & mask))
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WhitelistRule {
    pub subnet: WhitelistSubnet,
    pub permissions: PeerPermissions,
    pub incoming: bool,
    pub outgoing: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WhiteBind {
    pub address: SocketAddr,
    pub permissions: PeerPermissions,
}

impl WhiteBind {
    fn parse(value: &str, whitelist_relay: bool, whitelist_force_relay: bool) -> Result<Self> {
        let (permission_text, address_text) = value
            .split_once('@')
            .map_or((None, value), |(permissions, address)| {
                (Some(permissions), address)
            });
        let address = address_text
            .parse::<SocketAddr>()
            .with_context(|| format!("parsing --whitebind address '{address_text}'"))?;
        if address.port() == 0 {
            bail!("--whitebind must use a non-zero port");
        }
        let permissions = match permission_text {
            Some(permissions) => {
                let (permissions, incoming, outgoing) = PeerPermissions::parse_flags(permissions)?;
                if outgoing || !incoming {
                    bail!("--whitebind only supports incoming permissions");
                }
                permissions
            }
            None => PeerPermissions::implicit(),
        }
        .resolve(whitelist_relay, whitelist_force_relay);
        Ok(Self {
            address,
            permissions,
        })
    }
}

impl WhitelistRule {
    fn parse(value: &str) -> Result<Self> {
        let (permission_text, subnet_text) = value
            .split_once('@')
            .map_or((None, value), |(permissions, subnet)| {
                (Some(permissions), subnet)
            });
        let subnet = WhitelistSubnet::parse(subnet_text)
            .with_context(|| format!("parsing --whitelist subnet '{subnet_text}'"))?;
        let (permissions, incoming, outgoing) = match permission_text {
            Some(permissions) => PeerPermissions::parse_flags(permissions)?,
            None => (PeerPermissions::implicit(), true, false),
        };
        Ok(Self {
            subnet,
            permissions,
            incoming,
            outgoing,
        })
    }

    fn applies(&self, address: IpAddr, incoming: bool) -> bool {
        self.subnet.contains(address)
            && if incoming {
                self.incoming
            } else {
                self.outgoing
            }
    }
}

#[derive(Clone, Debug)]
pub struct PeerPermissionConfig {
    pub whitelist: Vec<WhitelistRule>,
    pub whitebind: Vec<WhiteBind>,
    pub whitelist_relay: bool,
    pub whitelist_force_relay: bool,
}

impl Default for PeerPermissionConfig {
    fn default() -> Self {
        Self {
            whitelist: Vec::new(),
            whitebind: Vec::new(),
            whitelist_relay: true,
            whitelist_force_relay: false,
        }
    }
}

impl PeerPermissionConfig {
    fn from_args(
        whitelist: &[String],
        whitebind: &[String],
        whitelist_relay: Option<bool>,
        whitelist_force_relay: bool,
        blocksonly: bool,
    ) -> Result<Self> {
        let whitelist = whitelist
            .iter()
            .map(|value| WhitelistRule::parse(value))
            .collect::<Result<Vec<_>>>()?;
        let whitelist_relay = whitelist_relay.unwrap_or(!blocksonly);
        let whitebind = whitebind
            .iter()
            .map(|value| WhiteBind::parse(value, whitelist_relay, whitelist_force_relay))
            .collect::<Result<Vec<_>>>()?;
        Ok(Self {
            whitelist,
            whitebind,
            whitelist_relay: whitelist_relay || whitelist_force_relay,
            whitelist_force_relay,
        })
    }

    pub fn permissions_for(&self, address: IpAddr, incoming: bool) -> PeerPermissions {
        let flags = self
            .whitelist
            .iter()
            .filter(|rule| rule.applies(address, incoming))
            .fold(PeerPermissions::empty(), |flags, rule| {
                flags.union(rule.permissions)
            });
        flags.resolve(self.whitelist_relay, self.whitelist_force_relay)
    }
}

impl OnlyNet {
    pub fn matches(self, address: SocketAddr) -> bool {
        self.matches_endpoint(&NetworkEndpoint::from_socket(address))
    }

    pub fn matches_endpoint(self, endpoint: &NetworkEndpoint) -> bool {
        match self {
            Self::Ipv4 => endpoint.network_name() == "ipv4",
            Self::Ipv6 => endpoint.network_name() == "ipv6",
            Self::Onion => endpoint.network_name() == "onion",
            Self::I2p => endpoint.network_name() == "i2p",
            Self::Cjdns => endpoint.network_name() == "cjdns",
        }
    }
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
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub listen: Option<bool>,

    #[arg(
        long,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub dnsseed: Option<bool>,

    #[arg(long, default_value = "127.0.0.1:8332")]
    pub rpc: SocketAddr,

    #[arg(long, default_value = "127.0.0.1:30001")]
    pub electrum: SocketAddr,

    #[arg(long, default_value_t = false)]
    pub rest: bool,

    #[arg(long, value_delimiter = ',')]
    pub connect: Vec<SocketAddr>,

    #[arg(long = "onlynet", value_enum, value_delimiter = ',')]
    pub onlynet: Vec<OnlyNet>,

    #[arg(long, value_name = "IP:PORT")]
    pub proxy: Option<SocketAddr>,

    #[arg(
        long = "cjdnsreachable",
        default_value_t = false,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub cjdns_reachable: bool,

    #[arg(long = "whitelist", value_name = "PERMISSIONS@IP[/PREFIX]")]
    pub whitelist: Vec<String>,

    #[arg(long = "whitebind", value_name = "PERMISSIONS@IP:PORT")]
    pub whitebind: Vec<String>,

    #[arg(
        long,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub whitelistrelay: Option<bool>,

    #[arg(
        long,
        default_value_t = false,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub whitelistforcerelay: bool,

    #[arg(long, value_name = "HEX")]
    pub signet_challenge: Option<String>,

    #[arg(long, visible_alias = "maxconnections", default_value_t = 125)]
    pub max_peers: usize,

    /// Maximum outbound bytes per 24-hour cycle. Lowercase units are decimal
    /// and uppercase units are powers of 1024, matching Core.
    #[arg(long = "maxuploadtarget", default_value = DEFAULT_MAX_UPLOAD_TARGET)]
    pub max_upload_target: String,

    #[arg(long, default_value_t = DEFAULT_PEER_TIMEOUT_SECS)]
    pub peertimeout: u64,

    #[arg(long, default_value_t = DEFAULT_BLOCK_MAX_WEIGHT)]
    pub blockmaxweight: u64,

    #[arg(long, default_value_t = DEFAULT_BLOCK_RESERVED_WEIGHT)]
    pub blockreservedweight: u64,

    #[arg(long)]
    pub blockversion: Option<i32>,

    #[arg(long, default_value = "0.00000001")]
    pub blockmintxfee: String,

    #[arg(long)]
    pub minrelaytxfee: Option<String>,

    #[arg(long)]
    pub incrementalrelayfee: Option<String>,

    #[arg(long)]
    pub dustrelayfee: Option<String>,

    #[arg(
        long,
        default_value_t = DEFAULT_ACCEPT_DATACARRIER,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub datacarrier: bool,

    #[arg(long, default_value_t = DEFAULT_MAX_DATACARRIER_BYTES)]
    pub datacarriersize: u64,

    #[arg(
        long,
        default_value_t = DEFAULT_PERMIT_BARE_MULTISIG,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub permitbaremultisig: bool,

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

    /// Send RPC-submitted transactions over dedicated short-lived proxy
    /// connections instead of admitting them to the local mempool first.
    #[arg(
        long,
        default_value_t = false,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub privatebroadcast: bool,

    #[arg(
        long = "acceptnonstdtxn",
        default_value_t = false,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub accept_nonstd_txn: bool,

    #[arg(long, default_value_t = 0)]
    pub prune: u64,

    #[arg(
        long,
        default_value_t = false,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub reindex: bool,

    #[arg(
        long = "reindex-chainstate",
        default_value_t = false,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub reindex_chainstate: bool,

    #[arg(long = "loadblock")]
    pub loadblock: Vec<PathBuf>,

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

    #[arg(long = "maxmempool")]
    pub max_mempool: Option<u64>,

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
    pub persistmempoolv1: bool,

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
    pub onlynet: Vec<OnlyNet>,
    pub proxy: Option<SocketAddr>,
    pub cjdns_reachable: bool,
    pub peer_permissions: PeerPermissionConfig,
    pub signet_challenge: Option<Vec<u8>>,
    pub max_peers: usize,
    pub max_upload_target: u64,
    pub peer_timeout_secs: u64,
    pub block_max_weight: u64,
    pub block_reserved_weight: u64,
    pub block_version: Option<i32>,
    pub block_min_tx_fee_sat_per_kvb: u64,
    pub min_relay_tx_fee_sat_per_kvb: u64,
    pub incremental_relay_fee_sat_per_kvb: u64,
    pub dust_relay_fee_sat_per_kvb: u64,
    pub max_datacarrier_bytes: Option<usize>,
    pub permit_bare_multisig: bool,
    pub peer_bloom_filters: bool,
    pub blocksonly: bool,
    pub private_broadcast: bool,
    /// Permit non-standard transactions on test chains, matching Core's
    /// `-acceptnonstdtxn` option. Mainnet never permits this override.
    pub accept_nonstd_txn: bool,
    /// Pruning mode: 0 disabled, 1 manual, or a target size in MiB.
    pub prune: u64,
    pub reindex: bool,
    pub reindex_chainstate: bool,
    pub load_blocks: Vec<PathBuf>,
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
    /// Write persisted mempool files in Core's legacy v1 format.
    pub persist_mempool_v1: bool,
    pub zmq: ZmqConfig,
}

impl Config {
    pub fn from_args(args: Args) -> Result<Self> {
        if args.peertimeout == 0 {
            bail!("--peertimeout must be greater than zero");
        }
        if args.accept_nonstd_txn && args.network == NetworkName::Bitcoin {
            bail!("--acceptnonstdtxn is not currently supported for main chain");
        }
        if args.proxy.is_some_and(|proxy| proxy.port() == 0) {
            bail!("--proxy must use a non-zero port");
        }
        if args.proxy.is_none()
            && let Some(network) = args.onlynet.iter().find_map(|network| match network {
                OnlyNet::Onion => Some("onion"),
                OnlyNet::I2p => Some("i2p"),
                OnlyNet::Ipv4 | OnlyNet::Ipv6 | OnlyNet::Cjdns => None,
            })
        {
            bail!("--onlynet={network} requires --proxy for outbound connections");
        }
        if args.onlynet.contains(&OnlyNet::Cjdns) && !args.cjdns_reachable {
            bail!(
                "Outbound connections restricted to CJDNS (-onlynet=cjdns) but -cjdnsreachable is not provided"
            );
        }
        let listen = args.listen.unwrap_or(
            !args.whitebind.is_empty()
                || (args.proxy.is_none() && args.connect.is_empty() && args.max_peers > 0),
        );
        if !listen && !args.whitebind.is_empty() {
            bail!("--whitebind cannot be used with --listen=false");
        }
        let clearnet_reachable = args.onlynet.is_empty()
            || args
                .onlynet
                .iter()
                .any(|network| matches!(network, OnlyNet::Ipv4 | OnlyNet::Ipv6));
        let dnsseed = args
            .dnsseed
            .unwrap_or(args.connect.is_empty() && args.max_peers > 0 && clearnet_reachable);
        let peer_permissions = PeerPermissionConfig::from_args(
            &args.whitelist,
            &args.whitebind,
            args.whitelistrelay,
            args.whitelistforcerelay,
            args.blocksonly,
        )?;
        if args.blockmaxweight > DEFAULT_BLOCK_MAX_WEIGHT {
            bail!(
                "--blockmaxweight must not exceed the consensus maximum of {DEFAULT_BLOCK_MAX_WEIGHT}"
            );
        }
        if args.blockreservedweight > DEFAULT_BLOCK_MAX_WEIGHT {
            bail!(
                "--blockreservedweight must not exceed the consensus maximum of {DEFAULT_BLOCK_MAX_WEIGHT}"
            );
        }
        if args.blockreservedweight < MINIMUM_BLOCK_RESERVED_WEIGHT {
            bail!("--blockreservedweight must be at least {MINIMUM_BLOCK_RESERVED_WEIGHT}");
        }
        let block_min_tx_fee_sat_per_kvb =
            Amount::from_str_in(&args.blockmintxfee, Denomination::Bitcoin)
                .with_context(|| {
                    format!(
                        "decoding --blockmintxfee as BTC/kvB: {}",
                        args.blockmintxfee
                    )
                })?
                .to_sat();
        let incremental_relay_fee_sat_per_kvb = parse_fee_rate(
            args.incrementalrelayfee.as_deref(),
            "0.00000100",
            "--incrementalrelayfee",
        )?;
        let min_relay_tx_fee_sat_per_kvb = parse_fee_rate(
            args.minrelaytxfee.as_deref(),
            "0.00000100",
            "--minrelaytxfee",
        )?;
        let min_relay_tx_fee_sat_per_kvb = if args.minrelaytxfee.is_none() {
            min_relay_tx_fee_sat_per_kvb.max(incremental_relay_fee_sat_per_kvb)
        } else {
            min_relay_tx_fee_sat_per_kvb
        };
        let dust_relay_fee_sat_per_kvb =
            parse_fee_rate(args.dustrelayfee.as_deref(), "0.00003000", "--dustrelayfee")?;
        let max_datacarrier_bytes = args.datacarrier.then_some(
            usize::try_from(args.datacarriersize)
                .context("--datacarriersize does not fit usize")?,
        );
        if args.prune != 0 && args.prune != 1 && args.prune < MIN_AUTO_PRUNE_TARGET_MIB {
            bail!("--prune automatic target must be at least {MIN_AUTO_PRUNE_TARGET_MIB} MiB");
        }
        if (args.txindex || args.txospenderindex) && args.prune != 0 {
            bail!("Prune mode is incompatible with transaction indexes.");
        }
        let max_mempool = args.max_mempool.unwrap_or(if args.blocksonly {
            DEFAULT_BLOCKSONLY_MAX_MEMPOOL_MB
        } else {
            DEFAULT_MAX_MEMPOOL_MB
        });
        if max_mempool == 0 {
            bail!("--maxmempool must be greater than zero");
        }
        if args.mempoolexpiry == 0 {
            bail!("--mempoolexpiry must be greater than zero");
        }
        let max_upload_target =
            parse_byte_units(&args.max_upload_target, 1 << 20).with_context(|| {
                format!(
                    "unable to parse --maxuploadtarget: '{}'",
                    args.max_upload_target
                )
            })?;
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
        if listen
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
            listen,
            rpc_bind: Some(args.rpc),
            electrum_bind: Some(args.electrum),
            rest: args.rest,
            seed_nodes: args.connect,
            dnsseed,
            onlynet: args.onlynet,
            proxy: args.proxy,
            cjdns_reachable: args.cjdns_reachable,
            peer_permissions,
            signet_challenge,
            max_peers: args.max_peers,
            max_upload_target,
            peer_timeout_secs: args.peertimeout,
            block_max_weight: args.blockmaxweight.max(args.blockreservedweight),
            block_reserved_weight: args.blockreservedweight,
            block_version: args.blockversion,
            block_min_tx_fee_sat_per_kvb,
            min_relay_tx_fee_sat_per_kvb,
            incremental_relay_fee_sat_per_kvb,
            dust_relay_fee_sat_per_kvb,
            max_datacarrier_bytes,
            permit_bare_multisig: args.permitbaremultisig,
            peer_bloom_filters: args.peer_bloom_filters,
            blocksonly: args.blocksonly,
            private_broadcast: args.privatebroadcast,
            accept_nonstd_txn: args.accept_nonstd_txn,
            prune: args.prune,
            reindex: args.reindex,
            reindex_chainstate: args.reindex_chainstate,
            load_blocks: args.loadblock,
            txindex: args.txindex,
            txospenderindex: args.txospenderindex,
            coinstatsindex: args.coinstatsindex,
            blockfilterindex,
            peer_block_filters: args.peerblockfilters,
            max_mempool_mb: max_mempool,
            mempool_expiry_hours: args.mempoolexpiry,
            persist_mempool: args.persistmempool,
            persist_mempool_v1: args.persistmempoolv1,
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

    pub fn allows_address(&self, address: SocketAddr) -> bool {
        self.allows_network_endpoint(&NetworkEndpoint::from_socket(address))
    }

    pub fn allows_network_endpoint(&self, endpoint: &NetworkEndpoint) -> bool {
        if matches!(endpoint, NetworkEndpoint::Cjdns { .. }) && !self.cjdns_reachable {
            return false;
        }
        self.onlynet.is_empty()
            || self
                .onlynet
                .iter()
                .copied()
                .any(|network| network.matches_endpoint(endpoint))
    }

    pub fn peer_permissions(&self, address: IpAddr, incoming: bool) -> PeerPermissions {
        self.peer_permissions.permissions_for(address, incoming)
    }
}

fn parse_fee_rate(value: Option<&str>, default: &str, name: &str) -> Result<u64> {
    Amount::from_str_in(value.unwrap_or(default), Denomination::Bitcoin)
        .with_context(|| format!("decoding {name} as BTC/kvB"))
        .map(Amount::to_sat)
}

fn parse_byte_units(value: &str, default_multiplier: u64) -> Option<u64> {
    if value.is_empty() {
        return None;
    }

    let (digits, multiplier) = match value.as_bytes().last().copied() {
        Some(b'k') => (&value[..value.len() - 1], 1_000),
        Some(b'K') => (&value[..value.len() - 1], 1 << 10),
        Some(b'm') => (&value[..value.len() - 1], 1_000_000),
        Some(b'M') => (&value[..value.len() - 1], 1 << 20),
        Some(b'g') => (&value[..value.len() - 1], 1_000_000_000),
        Some(b'G') => (&value[..value.len() - 1], 1 << 30),
        Some(b't') => (&value[..value.len() - 1], 1_000_000_000_000),
        Some(b'T') => (&value[..value.len() - 1], 1 << 40),
        Some(_) => (value, default_multiplier),
        None => return None,
    };
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    digits.parse::<u64>().ok()?.checked_mul(multiplier)
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
            "--onlynet=ipv4",
            "--proxy=127.0.0.1:9050",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert!(!config.listen);
        assert!(!config.dnsseed);
        assert!(config.blocksonly);
        assert_eq!(config.max_mempool_mb, DEFAULT_BLOCKSONLY_MAX_MEMPOOL_MB);
        assert_eq!(config.onlynet, vec![OnlyNet::Ipv4]);
        assert_eq!(config.proxy, Some("127.0.0.1:9050".parse().unwrap()));
        assert!(config.allows_address("192.0.2.1:8333".parse().unwrap()));
        assert!(!config.allows_address("[2001:db8::1]:8333".parse().unwrap()));
        assert!(!config.allows_address("[fc00::1]:8333".parse().unwrap()));
        assert!(OnlyNet::Cjdns.matches("[fc00::1]:8333".parse().unwrap()));
        assert!(!OnlyNet::Ipv6.matches("[fc00::1]:8333".parse().unwrap()));
        assert!(!config.cjdns_reachable);
        assert_eq!(config.prune, 0);
        assert_eq!(config.max_upload_target, 0);

        for network in ["onion", "i2p"] {
            let args = Args::try_parse_from([
                "bitcoind-rs",
                "--datadir",
                directory.path().to_str().unwrap(),
                &format!("--onlynet={network}"),
            ])
            .unwrap();
            let error = Config::from_args(args).unwrap_err().to_string();
            assert_eq!(
                error,
                format!("--onlynet={network} requires --proxy for outbound connections")
            );
        }

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--onlynet=cjdns",
        ])
        .unwrap();
        assert_eq!(
            Config::from_args(args).unwrap_err().to_string(),
            "Outbound connections restricted to CJDNS (-onlynet=cjdns) but -cjdnsreachable is not provided"
        );

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--onlynet=cjdns",
            "--cjdnsreachable",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert!(config.cjdns_reachable);
        assert!(config.allows_address("[fc00::1]:8333".parse().unwrap()));

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--maxuploadtarget=2M",
        ])
        .unwrap();
        assert_eq!(Config::from_args(args).unwrap().max_upload_target, 2 << 20);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--proxy=127.0.0.1:9050",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert!(!config.listen);
        assert!(config.dnsseed);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--privatebroadcast",
            "--proxy=127.0.0.1:9050",
        ])
        .unwrap();
        assert!(Config::from_args(args).unwrap().private_broadcast);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--network=regtest",
            "--acceptnonstdtxn",
        ])
        .unwrap();
        assert!(Config::from_args(args).unwrap().accept_nonstd_txn);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--acceptnonstdtxn",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--proxy=127.0.0.1:9050",
            "--listen=true",
        ])
        .unwrap();
        assert!(Config::from_args(args).unwrap().listen);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--connect=192.0.2.1:8333",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert!(!config.listen);
        assert!(!config.dnsseed);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--max-peers=0",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert!(!config.listen);
        assert!(!config.dnsseed);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--proxy=127.0.0.1:9050",
            "--whitebind=127.0.0.1:18444",
        ])
        .unwrap();
        assert!(Config::from_args(args).unwrap().listen);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--reindex",
            "--reindex-chainstate=1",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert!(config.reindex);
        assert!(config.reindex_chainstate);

        let block_file = directory.path().join("bootstrap.blk");
        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--loadblock",
            block_file.to_str().unwrap(),
        ])
        .unwrap();
        assert_eq!(
            Config::from_args(args).unwrap().load_blocks,
            vec![block_file]
        );

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
    fn parses_core_byte_units_for_upload_target() {
        assert_eq!(parse_byte_units("1k", 1 << 20), Some(1_000));
        assert_eq!(parse_byte_units("1K", 1 << 20), Some(1 << 10));
        assert_eq!(parse_byte_units("2m", 1 << 20), Some(2_000_000));
        assert_eq!(parse_byte_units("2M", 1 << 20), Some(2 << 20));
        assert_eq!(parse_byte_units("3g", 1 << 20), Some(3_000_000_000));
        assert_eq!(parse_byte_units("3G", 1 << 20), Some(3 << 30));
        assert_eq!(parse_byte_units("4t", 1 << 20), Some(4_000_000_000_000));
        assert_eq!(parse_byte_units("4T", 1 << 20), Some(4 << 40));
        assert_eq!(parse_byte_units("5", 1 << 20), Some(5 << 20));
        assert_eq!(parse_byte_units("020M", 1 << 20), Some(20 << 20));
        assert_eq!(parse_byte_units("", 1 << 20), None);
        assert_eq!(parse_byte_units("0.5T", 1 << 20), None);
        assert_eq!(parse_byte_units("+1M", 1 << 20), None);
        assert_eq!(parse_byte_units("1x", 1 << 20), None);
        assert_eq!(parse_byte_units("18446744073709551615g", 1 << 20), None);
    }

    #[test]
    fn parses_whitelist_permissions_and_directions() {
        let directory = tempfile::tempdir().unwrap();
        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--blocksonly",
            "--whitelist=192.0.2.0/24",
            "--whitelist=relay@203.0.113.0/24",
            "--whitelist=out,noban@198.51.100.0/24",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();

        let implicit = config.peer_permissions("192.0.2.7".parse().unwrap(), true);
        assert!(implicit.contains(PeerPermissions::NO_BAN));
        assert!(implicit.contains(PeerPermissions::DOWNLOAD));
        assert!(implicit.contains(PeerPermissions::MEMPOOL));
        assert!(!implicit.contains(PeerPermissions::RELAY));

        let explicit = config.peer_permissions("203.0.113.7".parse().unwrap(), true);
        assert_eq!(explicit.to_strings(), vec!["relay"]);
        assert!(
            config
                .peer_permissions("198.51.100.7".parse().unwrap(), false)
                .contains(PeerPermissions::NO_BAN)
        );
        assert_eq!(
            config.peer_permissions("198.51.100.7".parse().unwrap(), true),
            PeerPermissions::empty()
        );
    }

    #[test]
    fn parses_and_validates_whitebind_listeners() {
        let directory = tempfile::tempdir().unwrap();
        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--whitebind=forcerelay@127.0.0.1:18444",
            "--whitebind=127.0.0.1:18445",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert_eq!(config.peer_permissions.whitebind.len(), 2);
        assert_eq!(
            config.peer_permissions.whitebind[0].address,
            "127.0.0.1:18444".parse().unwrap()
        );
        assert_eq!(
            config.peer_permissions.whitebind[0]
                .permissions
                .to_strings(),
            vec!["forcerelay", "relay"]
        );
        assert!(
            config.peer_permissions.whitebind[1]
                .permissions
                .contains(PeerPermissions::RELAY)
        );

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--whitebind=127.0.0.1:0",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--whitebind=out,relay@127.0.0.1:18444",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--listen=false",
            "--whitebind=127.0.0.1:18444",
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
            "--blocksonly",
            "--maxmempool=12",
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
            "--persistmempoolv1",
        ])
        .unwrap();
        assert!(Config::from_args(args).unwrap().persist_mempool_v1);

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
            "--blockmaxweight",
            "2500000",
            "--blockreservedweight",
            "9000",
            "--blockversion",
            "1337",
            "--blockmintxfee",
            "0.00001000",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert_eq!(config.block_max_weight, 2_500_000);
        assert_eq!(config.block_reserved_weight, 9_000);
        assert_eq!(config.block_version, Some(1337));
        assert_eq!(config.block_min_tx_fee_sat_per_kvb, 1_000);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--blockreservedweight",
            "1999",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--blockmintxfee",
            "not-an-amount",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--minrelaytxfee",
            "0.00000200",
            "--incrementalrelayfee",
            "0.00000300",
            "--dustrelayfee",
            "0.00004000",
            "--datacarrier=false",
            "--datacarriersize",
            "42",
            "--permitbaremultisig=false",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert_eq!(config.min_relay_tx_fee_sat_per_kvb, 200);
        assert_eq!(config.incremental_relay_fee_sat_per_kvb, 300);
        assert_eq!(config.dust_relay_fee_sat_per_kvb, 4_000);
        assert_eq!(config.max_datacarrier_bytes, None);
        assert!(!config.permit_bare_multisig);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--incrementalrelayfee",
            "0.00000300",
        ])
        .unwrap();
        assert_eq!(
            Config::from_args(args)
                .unwrap()
                .min_relay_tx_fee_sat_per_kvb,
            300
        );

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
