use std::collections::{HashMap, HashSet};
use std::fmt;
use std::net::{IpAddr, SocketAddr};
use std::path::PathBuf;

use anyhow::{Context, Result, bail};
use bitcoin::pow::Work;
use bitcoin::{Amount, Denomination, Network};
use clap::{Parser, ValueEnum};

use crate::IpSubnet;
use crate::address::NetworkEndpoint;

pub const DEFAULT_ZMQ_HWM: u32 = 1_000;
pub const DEFAULT_MAX_MEMPOOL_MB: u64 = 300;
pub const DEFAULT_BLOCKSONLY_MAX_MEMPOOL_MB: u64 = 5;
pub const DEFAULT_MAX_UPLOAD_TARGET: &str = "0M";
pub const DEFAULT_MEMPOOL_EXPIRY_HOURS: u64 = 336;
pub const DEFAULT_PEER_TIMEOUT_SECS: u64 = 60;
pub const DEFAULT_CONNECT_TIMEOUT_MS: u64 = 5_000;
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
pub const DEFAULT_RPC_THREADS: usize = 16;
pub const DEFAULT_RPC_WORK_QUEUE: usize = 64;
pub const DEFAULT_RPC_SERVER_TIMEOUT_SECS: u64 = 30;

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

#[derive(Clone)]
pub(crate) enum RpcAuth {
    Plain {
        username: String,
        password: String,
    },
    Hmac {
        username: String,
        salt: Vec<u8>,
        hash: [u8; 32],
    },
}

impl RpcAuth {
    pub(crate) fn uses_plaintext_password(&self) -> bool {
        matches!(self, Self::Plain { .. })
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, ValueEnum)]
pub enum RpcCookiePermissions {
    #[default]
    Owner,
    Group,
    All,
}

impl fmt::Debug for RpcAuth {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Plain { username, .. } => formatter
                .debug_struct("Plain")
                .field("username", username)
                .field("password", &"<redacted>")
                .finish(),
            Self::Hmac { username, .. } => formatter
                .debug_struct("Hmac")
                .field("username", username)
                .field("salt", &"<redacted>")
                .field("hash", &"<redacted>")
                .finish(),
        }
    }
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

    #[arg(long = "blocksdir", value_name = "PATH")]
    pub blocks_dir: Option<PathBuf>,

    #[arg(long = "minimumchainwork", value_name = "HEX")]
    pub minimum_chain_work: Option<String>,

    #[arg(long)]
    pub p2p: Option<SocketAddr>,

    #[arg(long, value_name = "PORT")]
    pub port: Option<u16>,

    #[arg(long = "bind", value_name = "IP:PORT", value_delimiter = ',')]
    pub bind: Vec<SocketAddr>,

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

    #[arg(
        long = "forcednsseed",
        default_value_t = false,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub force_dns_seed: bool,

    #[arg(long)]
    pub rpc: Option<SocketAddr>,

    #[arg(long = "rpcport", value_name = "PORT")]
    pub rpc_port: Option<u16>,

    #[arg(
        long,
        default_value_t = true,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub server: bool,

    #[arg(long = "rpcservertimeout", default_value_t = DEFAULT_RPC_SERVER_TIMEOUT_SECS)]
    pub rpc_server_timeout: u64,

    #[arg(long = "rpcthreads", default_value_t = DEFAULT_RPC_THREADS)]
    pub rpc_threads: usize,

    #[arg(long = "rpcworkqueue", default_value_t = DEFAULT_RPC_WORK_QUEUE)]
    pub rpc_work_queue: usize,

    #[arg(long = "rpcbind", value_name = "IP[:PORT]", value_delimiter = ',')]
    pub rpc_binds: Vec<String>,

    #[arg(long = "rpcallowip", value_name = "IP[/PREFIX]")]
    pub rpc_allow_ips: Vec<String>,

    #[arg(long = "rpcuser", value_name = "USER")]
    pub rpc_user: Option<String>,

    #[arg(long = "rpcpassword", value_name = "PASSWORD")]
    pub rpc_password: Option<String>,

    #[arg(long = "rpcauth", value_name = "USER:SALT$HASH")]
    pub rpc_auth: Vec<String>,

    #[arg(long = "rpccookiefile", value_name = "PATH")]
    pub rpc_cookie_file: Option<PathBuf>,

    #[arg(
        long = "rpccookieperms",
        value_enum,
        default_value_t = RpcCookiePermissions::Owner
    )]
    pub rpc_cookie_permissions: RpcCookiePermissions,

    #[arg(long = "norpccookiefile", default_value_t = false)]
    pub no_rpc_cookie_file: bool,

    #[arg(long = "rpcwhitelist", value_name = "USER:METHOD[,METHOD]")]
    pub rpc_whitelist: Vec<String>,

    #[arg(
        long = "rpcwhitelistdefault",
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub rpc_whitelist_default: Option<bool>,

    #[arg(long, default_value = "127.0.0.1:30001")]
    pub electrum: SocketAddr,

    #[arg(long, default_value_t = false)]
    pub rest: bool,

    #[arg(long, value_delimiter = ',')]
    pub connect: Vec<String>,

    #[arg(long = "addnode", value_delimiter = ',')]
    pub addnode: Vec<String>,

    #[arg(long = "seednode", value_delimiter = ',')]
    pub seednode: Vec<String>,

    #[arg(
        long = "noconnect",
        default_value_t = false,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub no_connect: bool,

    #[arg(
        long = "v2transport",
        default_value_t = true,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub v2_transport: bool,

    #[arg(
        long = "networkactive",
        default_value_t = true,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub network_active: bool,

    #[arg(
        long,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub discover: Option<bool>,

    #[arg(long = "externalip", value_name = "IP")]
    pub externalip: Vec<String>,

    #[arg(
        long,
        default_value_t = true,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub dns: bool,

    #[arg(long = "onlynet", value_enum, value_delimiter = ',')]
    pub onlynet: Vec<OnlyNet>,

    #[arg(long, value_name = "IP:PORT")]
    pub proxy: Option<SocketAddr>,

    #[arg(
        long = "proxyrandomize",
        default_value_t = true,
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = clap::builder::BoolishValueParser::new()
    )]
    pub proxy_randomize: bool,

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

    /// Initial TCP connection timeout in milliseconds, matching Core's
    /// `-timeout` option.
    #[arg(long, default_value_t = DEFAULT_CONNECT_TIMEOUT_MS)]
    pub timeout: u64,

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
    pub(crate) blocks_dir: Option<PathBuf>,
    pub(crate) minimum_chain_work: Option<Work>,
    pub p2p_bind: SocketAddr,
    pub p2p_binds: Vec<SocketAddr>,
    pub listen: bool,
    pub rpc_bind: Option<SocketAddr>,
    pub rpc_binds: Vec<SocketAddr>,
    pub(crate) rpc_allow_ips: Vec<IpSubnet>,
    pub(crate) rpc_auth: Vec<RpcAuth>,
    pub(crate) rpc_cookie_path: Option<PathBuf>,
    pub(crate) rpc_cookie_permissions: RpcCookiePermissions,
    pub(crate) rpc_whitelist: HashMap<String, HashSet<String>>,
    pub(crate) rpc_whitelist_default: bool,
    pub rpc_server_timeout_secs: u64,
    pub rpc_threads: usize,
    pub rpc_work_queue: usize,
    pub electrum_bind: Option<SocketAddr>,
    pub rest: bool,
    pub seed_nodes: Vec<NetworkEndpoint>,
    pub connect_disabled: bool,
    pub v2_transport: bool,
    pub network_active: bool,
    pub discover: bool,
    pub external_addresses: Vec<SocketAddr>,
    pub dns_lookup: bool,
    pub add_nodes: Vec<NetworkEndpoint>,
    pub seed_nodes_for_address_fetch: Vec<NetworkEndpoint>,
    pub dnsseed: bool,
    pub force_dns_seed: bool,
    pub onlynet: Vec<OnlyNet>,
    pub proxy: Option<SocketAddr>,
    pub proxy_randomize: bool,
    pub cjdns_reachable: bool,
    pub peer_permissions: PeerPermissionConfig,
    pub signet_challenge: Option<Vec<u8>>,
    pub max_peers: usize,
    pub max_upload_target: u64,
    pub peer_timeout_secs: u64,
    pub connect_timeout_ms: u64,
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
        let network = args.network.into();
        let blocks_dir = args.blocks_dir.as_ref().map_or_else(
            || args.datadir.join("blocks"),
            |path| {
                if path.is_absolute() {
                    path.clone()
                } else {
                    args.datadir.join(path)
                }
            },
        );
        let minimum_chain_work = args
            .minimum_chain_work
            .as_deref()
            .map(|value| {
                if value == "0" {
                    Ok(Work::from_be_bytes([0; 32]))
                } else {
                    Work::from_unprefixed_hex(value)
                        .with_context(|| format!("decoding --minimumchainwork as hex: {value}"))
                }
            })
            .transpose()?;
        let p2p = args.p2p.unwrap_or_else(|| {
            SocketAddr::from((
                [127, 0, 0, 1],
                args.port.unwrap_or_else(|| default_p2p_port(network)),
            ))
        });
        if args.p2p.is_some() && !args.bind.is_empty() {
            bail!("--p2p cannot be combined with --bind");
        }
        let p2p_binds = if args.bind.is_empty() {
            vec![p2p]
        } else {
            args.bind.clone()
        };
        let rpc = args.rpc.unwrap_or_else(|| {
            SocketAddr::from((
                [127, 0, 0, 1],
                args.rpc_port.unwrap_or_else(|| default_rpc_port(network)),
            ))
        });
        if args.rpc.is_some() && args.rpc_port.is_some() {
            bail!("--rpc cannot be combined with --rpcport");
        }
        if args.rpc.is_some() && !args.rpc_binds.is_empty() {
            bail!("--rpc cannot be combined with --rpcbind");
        }
        if args.rpc_port == Some(0) {
            bail!("--rpcport must use a non-zero port");
        }
        let rpc_allow_ips = args
            .rpc_allow_ips
            .iter()
            .map(|value| {
                IpSubnet::parse(value)
                    .with_context(|| format!("parsing --rpcallowip subnet '{value}'"))
            })
            .collect::<Result<Vec<_>>>()?;
        let rpc_binds = if !args.server {
            Vec::new()
        } else if !args.rpc_binds.is_empty() && !rpc_allow_ips.is_empty() {
            parse_rpc_binds(&args.rpc_binds, rpc.port())?
        } else if args.rpc.is_some() {
            vec![rpc]
        } else {
            vec![
                rpc,
                SocketAddr::from(([0, 0, 0, 0, 0, 0, 0, 1], rpc.port())),
            ]
        };
        let rpc_auth = parse_rpc_auth(
            &args.rpc_auth,
            args.rpc_user.as_deref(),
            args.rpc_password.as_deref(),
        )?;
        let rpc_server_timeout_secs = args.rpc_server_timeout.max(1);
        let rpc_threads = args.rpc_threads.max(1);
        let rpc_work_queue = args.rpc_work_queue.max(1);
        if args.no_rpc_cookie_file && args.rpc_cookie_file.is_some() {
            bail!("--norpccookiefile cannot be combined with --rpccookiefile");
        }
        let rpc_cookie_path = if !args.server || args.no_rpc_cookie_file {
            None
        } else {
            let path = args
                .rpc_cookie_file
                .clone()
                .unwrap_or_else(|| PathBuf::from(".cookie"));
            Some(if path.is_absolute() {
                path
            } else {
                args.datadir.join(path)
            })
        };
        let rpc_whitelist_default = args
            .rpc_whitelist_default
            .unwrap_or(!args.rpc_whitelist.is_empty());
        let rpc_whitelist = parse_rpc_whitelist(&args.rpc_whitelist);
        if args.peertimeout == 0 {
            bail!("--peertimeout must be greater than zero");
        }
        if args.timeout == 0 {
            bail!("--timeout must be greater than zero");
        }
        if args.accept_nonstd_txn && args.network == NetworkName::Bitcoin {
            bail!("--acceptnonstdtxn is not currently supported for main chain");
        }
        if args.proxy.is_some_and(|proxy| proxy.port() == 0) {
            bail!("--proxy must use a non-zero port");
        }
        let connect_configured = args.no_connect || !args.connect.is_empty();
        if args.privatebroadcast && args.proxy.is_none() {
            bail!("--privatebroadcast requires --proxy for private connections");
        }
        if args.privatebroadcast && connect_configured {
            bail!(
                "Private broadcast of own transactions requested (--privatebroadcast), but --connect is also configured"
            );
        }
        if args.no_connect && !args.connect.is_empty() {
            bail!("--noconnect cannot be combined with --connect");
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
            !args.bind.is_empty()
                || !args.whitebind.is_empty()
                || (args.proxy.is_none() && !connect_configured && args.max_peers > 0),
        );
        if !listen && (!args.bind.is_empty() || !args.whitebind.is_empty()) {
            bail!("--bind/--whitebind cannot be used with --listen=false");
        }
        let clearnet_reachable = args.onlynet.is_empty()
            || args
                .onlynet
                .iter()
                .any(|network| matches!(network, OnlyNet::Ipv4 | OnlyNet::Ipv6));
        let dnsseed = args
            .dnsseed
            .unwrap_or(!connect_configured && args.max_peers > 0 && clearnet_reachable);
        if args.force_dns_seed && !dnsseed {
            bail!("Cannot set --forcednsseed=true when setting --dnsseed=false");
        }
        let discover = args
            .discover
            .unwrap_or(listen && args.externalip.is_empty() && args.proxy.is_none());
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
        if listen {
            for bind in &p2p_binds {
                if bind.ip() == IpAddr::V4(std::net::Ipv4Addr::UNSPECIFIED) && bind.port() == 0 {
                    bail!("--bind/--p2p must use a non-zero port when binding all interfaces");
                }
            }
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
        let connect_disabled = args.no_connect
            || (args.connect.len() == 1 && args.connect.first().is_some_and(|value| value == "0"));
        let seed_nodes = args
            .connect
            .iter()
            .filter(|value| !connect_disabled || value.as_str() != "0")
            .cloned()
            .collect::<Vec<_>>();
        let seed_nodes = parse_manual_endpoints(&seed_nodes, network, "connect")?;
        let add_nodes = parse_manual_endpoints(&args.addnode, network, "addnode")?;
        let seed_nodes_for_address_fetch =
            parse_manual_endpoints(&args.seednode, network, "seednode")?;
        let primary_p2p_bind = p2p_binds[0];
        let external_port = if primary_p2p_bind.port() == 0 {
            default_p2p_port(network)
        } else {
            primary_p2p_bind.port()
        };
        let external_addresses = parse_external_addresses(&args.externalip, external_port)?;
        std::fs::create_dir_all(&args.datadir)
            .with_context(|| format!("creating data directory {}", args.datadir.display()))?;
        Ok(Self {
            network,
            datadir: args.datadir,
            blocks_dir: Some(blocks_dir),
            minimum_chain_work,
            p2p_bind: primary_p2p_bind,
            p2p_binds,
            listen,
            rpc_bind: rpc_binds.first().copied(),
            rpc_binds,
            rpc_allow_ips,
            rpc_auth,
            rpc_cookie_path,
            rpc_cookie_permissions: args.rpc_cookie_permissions,
            rpc_whitelist,
            rpc_whitelist_default,
            rpc_server_timeout_secs,
            rpc_threads,
            rpc_work_queue,
            electrum_bind: Some(args.electrum),
            rest: args.rest,
            seed_nodes,
            connect_disabled,
            v2_transport: args.v2_transport,
            network_active: args.network_active,
            discover,
            external_addresses,
            dns_lookup: args.dns,
            add_nodes,
            seed_nodes_for_address_fetch,
            dnsseed,
            force_dns_seed: args.force_dns_seed,
            onlynet: args.onlynet,
            proxy: args.proxy,
            proxy_randomize: args.proxy_randomize,
            cjdns_reachable: args.cjdns_reachable,
            peer_permissions,
            signet_challenge,
            max_peers: args.max_peers,
            max_upload_target,
            peer_timeout_secs: args.peertimeout,
            connect_timeout_ms: args.timeout,
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

pub(crate) fn default_p2p_port(network: Network) -> u16 {
    match network {
        Network::Bitcoin => 8333,
        Network::Testnet => 18333,
        Network::Testnet4 => 48333,
        Network::Signet => 38333,
        Network::Regtest => 18444,
    }
}

fn default_rpc_port(network: Network) -> u16 {
    match network {
        Network::Bitcoin => 8332,
        Network::Testnet => 18332,
        Network::Testnet4 => 48332,
        Network::Signet => 38332,
        Network::Regtest => 18443,
    }
}

fn parse_manual_endpoints(
    values: &[String],
    network: Network,
    option: &str,
) -> Result<Vec<NetworkEndpoint>> {
    values
        .iter()
        .map(|value| {
            NetworkEndpoint::parse_manual(value, default_p2p_port(network))
                .with_context(|| format!("parsing --{option} address '{value}'"))
        })
        .collect()
}

fn parse_external_addresses(values: &[String], default_port: u16) -> Result<Vec<SocketAddr>> {
    values
        .iter()
        .map(|value| {
            let endpoint = NetworkEndpoint::parse_manual(value, default_port)
                .with_context(|| format!("parsing --externalip address '{value}'"))?;
            endpoint
                .socket_addr()
                .ok_or_else(|| anyhow::anyhow!("--externalip must resolve to an IP address"))
        })
        .collect()
}

fn parse_rpc_binds(values: &[String], default_port: u16) -> Result<Vec<SocketAddr>> {
    values
        .iter()
        .map(|value| {
            if let Ok(address) = value.parse::<SocketAddr>() {
                return Ok(address);
            }
            if let Ok(ip) = value.parse::<IpAddr>() {
                return Ok(SocketAddr::new(ip, default_port));
            }
            if let Some(host) = value
                .strip_prefix('[')
                .and_then(|value| value.strip_suffix(']'))
                && let Ok(ip) = host.parse::<IpAddr>()
            {
                return Ok(SocketAddr::new(ip, default_port));
            }
            Err(anyhow::anyhow!(
                "invalid --rpcbind address '{value}'; expected IP[:PORT]"
            ))
        })
        .collect()
}

fn parse_rpc_auth(
    values: &[String],
    username: Option<&str>,
    password: Option<&str>,
) -> Result<Vec<RpcAuth>> {
    let mut credentials = Vec::with_capacity(values.len() + usize::from(password.is_some()));
    if let Some(password) = password {
        credentials.push(RpcAuth::Plain {
            username: username.unwrap_or_default().to_owned(),
            password: password.to_owned(),
        });
    }
    for value in values {
        let (username, salt_and_hash) = value
            .split_once(':')
            .ok_or_else(|| anyhow::anyhow!("invalid --rpcauth value; expected USER:SALT$HASH"))?;
        let (salt, encoded_hash) = salt_and_hash
            .split_once('$')
            .ok_or_else(|| anyhow::anyhow!("invalid --rpcauth value; expected USER:SALT$HASH"))?;
        if username.is_empty() || salt.is_empty() || encoded_hash.is_empty() {
            bail!("invalid --rpcauth value; expected USER:SALT$HASH");
        }
        let hash =
            hex::decode(encoded_hash).with_context(|| "decoding --rpcauth hash as hexadecimal")?;
        let hash: [u8; 32] = hash
            .try_into()
            .map_err(|_| anyhow::anyhow!("--rpcauth hash must contain 32 bytes"))?;
        credentials.push(RpcAuth::Hmac {
            username: username.to_owned(),
            salt: salt.as_bytes().to_vec(),
            hash,
        });
    }
    Ok(credentials)
}

fn parse_rpc_whitelist(values: &[String]) -> HashMap<String, HashSet<String>> {
    let mut whitelist: HashMap<String, HashSet<String>> = HashMap::new();
    for value in values {
        let (username, methods) = value.split_once(':').unwrap_or((value, ""));
        let methods = methods
            .split([',', ' '])
            .filter(|method| !method.is_empty())
            .map(str::to_owned)
            .collect::<HashSet<_>>();
        if let Some(existing) = whitelist.get_mut(username) {
            existing.retain(|method| methods.contains(method));
        } else {
            whitelist.insert(username.to_owned(), methods);
        }
    }
    whitelist
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
        assert!(config.proxy_randomize);
        assert!(config.v2_transport);
        assert!(config.allows_address("192.0.2.1:8333".parse().unwrap()));
        assert!(!config.allows_address("[2001:db8::1]:8333".parse().unwrap()));
        assert!(!config.allows_address("[fc00::1]:8333".parse().unwrap()));
        assert!(OnlyNet::Cjdns.matches("[fc00::1]:8333".parse().unwrap()));
        assert!(!OnlyNet::Ipv6.matches("[fc00::1]:8333".parse().unwrap()));
        assert!(!config.cjdns_reachable);
        assert_eq!(config.prune, 0);
        assert_eq!(config.max_upload_target, 0);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--blocksdir=storage/blocks",
        ])
        .unwrap();
        assert_eq!(
            Config::from_args(args).unwrap().blocks_dir,
            Some(directory.path().join("storage/blocks"))
        );

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--minimumchainwork=0",
        ])
        .unwrap();
        assert_eq!(
            Config::from_args(args).unwrap().minimum_chain_work,
            Some(Work::from_be_bytes([0; 32]))
        );

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--minimumchainwork=not-hex",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

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
            "--forcednsseed",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert!(config.force_dns_seed);
        assert!(config.dnsseed);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--dnsseed=false",
            "--forcednsseed",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--network=regtest",
            "--rpcbind=127.0.0.1:18446,127.0.0.1:18447",
            "--rpcallowip=192.0.2.0/24",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert_eq!(
            config.rpc_binds,
            vec![
                "127.0.0.1:18446".parse().unwrap(),
                "127.0.0.1:18447".parse().unwrap(),
            ]
        );
        assert_eq!(config.rpc_bind, Some("127.0.0.1:18446".parse().unwrap()));

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--network=regtest",
            "--rpcport=18446",
            "--rpcbind=127.0.0.1,[::1]",
            "--rpcallowip=192.0.2.0/24",
        ])
        .unwrap();
        assert_eq!(
            Config::from_args(args).unwrap().rpc_binds,
            vec![
                "127.0.0.1:18446".parse().unwrap(),
                "[::1]:18446".parse().unwrap(),
            ]
        );

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--network=regtest",
            "--rpcbind=0.0.0.0:18446",
        ])
        .unwrap();
        assert_eq!(
            Config::from_args(args).unwrap().rpc_binds,
            vec![
                "127.0.0.1:18443".parse().unwrap(),
                "[::1]:18443".parse().unwrap(),
            ]
        );

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--proxy=127.0.0.1:9050",
            "--proxyrandomize=false",
        ])
        .unwrap();
        assert!(!Config::from_args(args).unwrap().proxy_randomize);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--v2transport=false",
            "--networkactive=false",
            "--dns=false",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert!(!config.v2_transport);
        assert!(!config.network_active);
        assert!(!config.dns_lookup);

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
            "--privatebroadcast",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--privatebroadcast",
            "--proxy=127.0.0.1:9050",
            "--noconnect",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--privatebroadcast",
            "--proxy=127.0.0.1:9050",
            "--connect=192.0.2.1:8333",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

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
            "--connect=192.0.2.1:8333",
            "--bind=127.0.0.1:8333",
        ])
        .unwrap();
        assert!(Config::from_args(args).unwrap().listen);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--bind=127.0.0.1:8333",
            "--listen=false",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--network=regtest",
            "--connect=example.invalid,192.0.2.1",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert_eq!(
            config.seed_nodes,
            vec![
                NetworkEndpoint::dns("example.invalid".to_owned(), 18444).unwrap(),
                NetworkEndpoint::from_socket("192.0.2.1:18444".parse().unwrap()),
            ]
        );

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--network=regtest",
            "--addnode=example.invalid,192.0.2.2",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert_eq!(
            config.add_nodes,
            vec![
                NetworkEndpoint::dns("example.invalid".to_owned(), 18444).unwrap(),
                NetworkEndpoint::from_socket("192.0.2.2:18444".parse().unwrap()),
            ]
        );
        assert_eq!(config.p2p_bind, "127.0.0.1:18444".parse().unwrap());
        assert_eq!(config.rpc_bind, Some("127.0.0.1:18443".parse().unwrap()));
        assert!(config.listen);
        assert!(config.dnsseed);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--network=regtest",
            "--port=18445",
        ])
        .unwrap();
        assert_eq!(
            Config::from_args(args).unwrap().p2p_bind,
            "127.0.0.1:18445".parse().unwrap()
        );

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--network=regtest",
            "--rpcport=18446",
        ])
        .unwrap();
        assert_eq!(
            Config::from_args(args).unwrap().rpc_bind,
            Some("127.0.0.1:18446".parse().unwrap())
        );
        assert_eq!(
            Config::from_args(
                Args::try_parse_from([
                    "bitcoind-rs",
                    "--datadir",
                    directory.path().to_str().unwrap(),
                    "--network=regtest",
                    "--rpcport=18446",
                ])
                .unwrap(),
            )
            .unwrap()
            .rpc_binds,
            vec![
                "127.0.0.1:18446".parse().unwrap(),
                "[::1]:18446".parse().unwrap(),
            ]
        );

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--server=false",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert!(config.rpc_bind.is_none());
        assert!(config.rpc_binds.is_empty());
        assert!(config.rpc_cookie_path.is_none());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--rpcservertimeout=0",
            "--rpcthreads=0",
            "--rpcworkqueue=0",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert_eq!(config.rpc_server_timeout_secs, 1);
        assert_eq!(config.rpc_threads, 1);
        assert_eq!(config.rpc_work_queue, 1);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--rpcallowip=192.0.2.0/255.255.255.0",
            "--rpcallowip=2001:db8::/32",
            "--rpcuser=rpc-user",
            "--rpcpassword=rpc-password",
            "--rpcauth=hashed:salt$84ec44c7d6fc41917953a1dafca3c7d7856f7a9d0328b991b76f0d36be1224b9",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert!(config.rpc_allow_ips[0].contains("192.0.2.77".parse().unwrap()));
        assert!(config.rpc_allow_ips[1].contains("2001:db8::7".parse().unwrap()));
        assert_eq!(config.rpc_auth.len(), 2);
        assert!(matches!(
            config.rpc_auth[0],
            RpcAuth::Plain { ref username, ref password }
                if username == "rpc-user" && password == "rpc-password"
        ));
        assert!(matches!(config.rpc_auth[1], RpcAuth::Hmac { .. }));

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--rpcwhitelist=alice:getblock,getblockchaininfo",
            "--rpcwhitelist=alice:getblock,getrawtransaction",
            "--rpcwhitelistdefault=false",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert_eq!(
            config.rpc_whitelist["alice"],
            ["getblock".to_owned()].into_iter().collect()
        );
        assert!(!config.rpc_whitelist_default);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--rpccookiefile=auth/rpc.cookie",
            "--rpccookieperms=group",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert_eq!(
            config.rpc_cookie_path,
            Some(directory.path().join("auth/rpc.cookie"))
        );
        assert_eq!(config.rpc_cookie_permissions, RpcCookiePermissions::Group);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--norpccookiefile",
        ])
        .unwrap();
        assert!(Config::from_args(args).unwrap().rpc_cookie_path.is_none());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--rpcallowip=192.0.2.0/255.0.255.0",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--rpcport=0",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--network=regtest",
            "--bind=127.0.0.1:18446,127.0.0.1:18447",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert_eq!(
            config.p2p_binds,
            vec![
                "127.0.0.1:18446".parse().unwrap(),
                "127.0.0.1:18447".parse().unwrap(),
            ]
        );
        assert_eq!(config.p2p_bind, "127.0.0.1:18446".parse().unwrap());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--network=regtest",
            "--seednode=seed.example",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert_eq!(
            config.seed_nodes_for_address_fetch,
            vec![NetworkEndpoint::dns("seed.example".to_owned(), 18444).unwrap()]
        );
        assert!(config.listen);
        assert!(config.dnsseed);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--connect=0",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert!(config.connect_disabled);
        assert!(config.seed_nodes.is_empty());
        assert!(!config.listen);
        assert!(!config.dnsseed);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--network=regtest",
            "--externalip=198.51.100.9",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert_eq!(
            config.external_addresses,
            vec!["198.51.100.9:18444".parse().unwrap()]
        );
        assert!(!config.discover);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--noconnect",
        ])
        .unwrap();
        let config = Config::from_args(args).unwrap();
        assert!(config.connect_disabled);
        assert!(config.seed_nodes.is_empty());
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
            "--timeout=1250",
        ])
        .unwrap();
        assert_eq!(Config::from_args(args).unwrap().connect_timeout_ms, 1_250);

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--peertimeout=0",
        ])
        .unwrap();
        assert!(Config::from_args(args).is_err());

        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--timeout=0",
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
