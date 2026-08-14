//! Bitcoin peer networking and block/transaction relay.

use std::collections::{HashMap, HashSet};
use std::net::SocketAddr;
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};
use std::time::Duration;

use anyhow::{Context, Result};
use bip324::futures::{Protocol, ProtocolReader, ProtocolWriter};
use bip324::io::Payload;
use bip324::{PacketType, Role};
use bitcoin::bip152::{BlockTransactions, BlockTransactionsRequest, HeaderAndShortIds, ShortId};
use bitcoin::bip158::FilterHash;
use bitcoin::blockdata::script::Instruction;
use bitcoin::consensus::encode::serialize;
use bitcoin::hashes::Hash;
use bitcoin::p2p::message_bloom::{BloomFlags, FilterAdd, FilterLoad};
use bitcoin::p2p::message_filter::{CFCheckpt, CFHeaders, CFilter};
use bitcoin::{Block, BlockHash, MerkleBlock, Network, Transaction, Txid, Wtxid};
use rand::random;
use tokio::io::BufReader;
use tokio::net::{
    TcpListener, TcpStream,
    tcp::{OwnedReadHalf, OwnedWriteHalf},
};
use tokio::sync::{Mutex, Semaphore, mpsc};
use tracing::{debug, info, warn};

use crate::chain::BasicFilterRange;
use crate::wire::{
    self, GetHeadersMessage, Inventory, InventoryType, Message, SendTxRcnclMessage, VersionMessage,
};
use crate::{Node, unix_time_seconds};

enum PeerReader {
    V1(OwnedReadHalf),
    V2(ProtocolReader<BufReader<OwnedReadHalf>>),
}

enum PeerWriterKind {
    V1(OwnedWriteHalf),
    V2(ProtocolWriter<OwnedWriteHalf>),
}

type PeerWriter = Arc<Mutex<PeerWriterKind>>;

const MAX_BLOOM_FILTER_SIZE: usize = 36_000;
const MAX_BLOOM_HASH_FUNCS: u32 = 50;
const MAX_BLOOM_ELEMENT_SIZE: usize = 520;
const SENDHEADERS_VERSION: i32 = 70_012;
const FEEFILTER_VERSION: i32 = 70_013;
const SHORT_IDS_BLOCKS_VERSION: i32 = 70_014;
const WTXID_RELAY_VERSION: i32 = 70_016;
const TX_RECONCILIATION_VERSION: u32 = 1;
const KNOWN_TX_FILTER_BITS: usize = 1 << 20;
const KNOWN_TX_FILTER_HASHES: u32 = 4;
const KNOWN_TX_FILTER_GENERATION: usize = 25_000;
pub(crate) const PING_TIMEOUT: Duration = Duration::from_secs(20 * 60);

struct PeerState {
    writer: PeerWriter,
    bloom_filter: parking_lot::Mutex<Option<BloomFilter>>,
    known_tx_inventory: parking_lot::Mutex<KnownTxInventory>,
    fee_filter: parking_lot::Mutex<i64>,
    relay_transactions: parking_lot::Mutex<bool>,
    wtxid_relay: parking_lot::Mutex<bool>,
    send_headers: parking_lot::Mutex<bool>,
    compact_block_version: parking_lot::Mutex<Option<u64>>,
    compact_block_announce: parking_lot::Mutex<bool>,
    tx_reconciliation_salt: parking_lot::Mutex<Option<u64>>,
    tx_reconciliation_registered: parking_lot::Mutex<bool>,
}

/// A bounded rolling filter of transaction inventory already known by a peer.
/// Core uses the same two-generation shape to avoid repeatedly announcing the
/// same transaction while keeping per-peer memory bounded.
struct KnownTxInventory {
    generations: [Vec<u8>; 2],
    active_generation: usize,
    inserted_in_generation: usize,
}

impl KnownTxInventory {
    fn new() -> Self {
        let bytes = KNOWN_TX_FILTER_BITS / 8;
        Self {
            generations: [vec![0; bytes], vec![0; bytes]],
            active_generation: 0,
            inserted_in_generation: 0,
        }
    }

    fn contains(&self, hash: &BlockHash) -> bool {
        self.generations
            .iter()
            .any(|generation| self.generation_contains(generation, hash))
    }

    fn insert(&mut self, hash: &BlockHash) {
        if self.contains(hash) {
            return;
        }
        if self.inserted_in_generation >= KNOWN_TX_FILTER_GENERATION {
            self.active_generation ^= 1;
            self.generations[self.active_generation].fill(0);
            self.inserted_in_generation = 0;
        }
        let generation = &mut self.generations[self.active_generation];
        let bytes = hash.to_byte_array();
        for index in 0..KNOWN_TX_FILTER_HASHES {
            let bit = (murmur_hash3(index.wrapping_mul(0xfba4_c795), &bytes) as usize)
                & (KNOWN_TX_FILTER_BITS - 1);
            generation[bit / 8] |= 1 << (bit % 8);
        }
        self.inserted_in_generation += 1;
    }

    fn generation_contains(&self, generation: &[u8], hash: &BlockHash) -> bool {
        let bytes = hash.to_byte_array();
        (0..KNOWN_TX_FILTER_HASHES).all(|index| {
            let bit = (murmur_hash3(index.wrapping_mul(0xfba4_c795), &bytes) as usize)
                & (KNOWN_TX_FILTER_BITS - 1);
            generation[bit / 8] & (1 << (bit % 8)) != 0
        })
    }
}

type PeerRegistry = Arc<parking_lot::Mutex<HashMap<usize, Arc<PeerState>>>>;
type OutboundAttempts = Arc<parking_lot::Mutex<HashSet<SocketAddr>>>;

#[derive(Clone)]
struct OutboundContext {
    slots: Arc<Semaphore>,
    peers: PeerRegistry,
    next_peer_id: Arc<AtomicUsize>,
    attempts: OutboundAttempts,
}

#[derive(Clone, Debug)]
struct BloomFilter {
    data: Vec<u8>,
    hash_funcs: u32,
    tweak: u32,
    flags: BloomFlags,
}

impl BloomFilter {
    fn from_message(message: FilterLoad) -> Result<Self> {
        if message.filter.len() > MAX_BLOOM_FILTER_SIZE {
            anyhow::bail!("bloom filter exceeds the 36000-byte limit");
        }
        if message.hash_funcs > MAX_BLOOM_HASH_FUNCS {
            anyhow::bail!("bloom filter has too many hash functions");
        }
        Ok(Self {
            data: message.filter,
            hash_funcs: message.hash_funcs,
            tweak: message.tweak,
            flags: message.flags,
        })
    }

    fn insert(&mut self, value: &[u8]) {
        if self.data.is_empty() {
            return;
        }
        let bit_count = self.data.len().saturating_mul(8);
        for index in 0..self.hash_funcs {
            let seed = index.wrapping_mul(0xfba4_c795).wrapping_add(self.tweak);
            let bit = (murmur_hash3(seed, value) as usize) % bit_count;
            self.data[bit / 8] |= 1 << (bit % 8);
        }
    }

    fn contains(&self, value: &[u8]) -> bool {
        if self.data.is_empty() {
            return true;
        }
        let bit_count = self.data.len().saturating_mul(8);
        (0..self.hash_funcs).all(|index| {
            let seed = index.wrapping_mul(0xfba4_c795).wrapping_add(self.tweak);
            let bit = (murmur_hash3(seed, value) as usize) % bit_count;
            self.data[bit / 8] & (1 << (bit % 8)) != 0
        })
    }

    fn contains_script_data(&self, script: &bitcoin::Script) -> bool {
        for instruction in script.instructions() {
            match instruction {
                Ok(Instruction::PushBytes(data))
                    if !data.is_empty() && self.contains(data.as_bytes()) =>
                {
                    return true;
                }
                Ok(_) => {}
                Err(_) => break,
            }
        }
        false
    }

    fn is_relevant_and_update(&mut self, transaction: &Transaction) -> bool {
        if self.data.is_empty() {
            return true;
        }
        let txid = transaction.compute_txid();
        if self.contains(&serialize(&txid)) {
            return true;
        }
        let mut matched = false;
        for (index, output) in transaction.output.iter().enumerate() {
            if !self.contains_script_data(&output.script_pubkey) {
                continue;
            }
            matched = true;
            let should_update = match self.flags {
                BloomFlags::All => true,
                BloomFlags::PubkeyOnly => {
                    output.script_pubkey.is_p2pk() || output.script_pubkey.is_multisig()
                }
                BloomFlags::None => false,
            };
            if should_update {
                let outpoint = bitcoin::OutPoint::new(txid, index as u32);
                self.insert(&serialize(&outpoint));
            }
            break;
        }
        if matched {
            return true;
        }
        for input in &transaction.input {
            if self.contains(&serialize(&input.previous_output))
                || self.contains_script_data(&input.script_sig)
            {
                return true;
            }
        }
        false
    }

    fn matched_transaction_ids(&mut self, block: &Block) -> Vec<Txid> {
        block
            .txdata
            .iter()
            .filter_map(|transaction| {
                self.is_relevant_and_update(transaction)
                    .then_some(transaction.compute_txid())
            })
            .collect()
    }
}

fn murmur_hash3(seed: u32, data: &[u8]) -> u32 {
    let mut hash = seed;
    const C1: u32 = 0xcc9e_2d51;
    const C2: u32 = 0x1b87_3593;
    for chunk in data.chunks_exact(4) {
        let mut value = u32::from_le_bytes(chunk.try_into().expect("four-byte chunk"));
        value = value.wrapping_mul(C1).rotate_left(15).wrapping_mul(C2);
        hash ^= value;
        hash = hash
            .rotate_left(13)
            .wrapping_mul(5)
            .wrapping_add(0xe654_6b64);
    }
    let tail = data.chunks_exact(4).remainder();
    let mut value = 0u32;
    for (index, byte) in tail.iter().enumerate() {
        value |= u32::from(*byte) << (index * 8);
    }
    if !tail.is_empty() {
        hash ^= value.wrapping_mul(C1).rotate_left(15).wrapping_mul(C2);
    }
    hash ^= data.len() as u32;
    hash ^= hash >> 16;
    hash = hash.wrapping_mul(0x85eb_ca6b);
    hash ^= hash >> 13;
    hash = hash.wrapping_mul(0xc2b2_ae35);
    hash ^ (hash >> 16)
}

impl PeerReader {
    async fn read_message(&mut self, network: Network) -> Result<(Message, usize)> {
        match self {
            Self::V1(reader) => wire::read_message_with_size(reader, network).await,
            Self::V2(reader) => loop {
                let payload = reader.read().await?;
                if payload.packet_type() == PacketType::Decoy {
                    continue;
                }
                let contents = payload.contents();
                let bytes = contents.len().saturating_add(20);
                let message = wire::decode_v2_message(contents)?;
                break Ok((message, bytes));
            },
        }
    }
}

#[derive(Debug)]
pub(crate) enum PeerCommand {
    Disconnect,
    RequestBlock(BlockHash),
    Ping(u64),
    SendMessage { command: String, payload: Vec<u8> },
}

#[derive(Debug)]
pub(crate) enum PeerManagerRequest {
    Add(SocketAddr),
    OneTry(SocketAddr, Option<bool>),
}

struct PendingCompactBlock {
    compact: HeaderAndShortIds,
    transactions: Vec<Option<Transaction>>,
    requested_indexes: Vec<u64>,
}

pub struct PeerManager {
    node: Arc<Node>,
}

impl PeerManager {
    pub fn new(node: Arc<Node>) -> Self {
        Self { node }
    }

    pub async fn run(self) -> Result<()> {
        let listener = if self.node.config.listen {
            Some(
                TcpListener::bind(self.node.config.p2p_bind)
                    .await
                    .with_context(|| {
                        format!("binding P2P listener {}", self.node.config.p2p_bind)
                    })?,
            )
        } else {
            None
        };
        let slots = Arc::new(Semaphore::new(self.node.config.max_peers));
        let peers: PeerRegistry = Arc::new(parking_lot::Mutex::new(HashMap::new()));
        let next_peer_id = Arc::new(AtomicUsize::new(1));
        let outbound = OutboundContext {
            slots: slots.clone(),
            peers: peers.clone(),
            next_peer_id: next_peer_id.clone(),
            attempts: Arc::new(parking_lot::Mutex::new(HashSet::new())),
        };
        let (add_node_sender, mut add_node_receiver) = mpsc::unbounded_channel();
        self.node.set_peer_manager_sender(add_node_sender);
        let mut chain_events = self.node.subscribe_chain();
        let mut mempool_events = self.node.subscribe_peer_mempool();
        let block_relay_node = self.node.clone();
        let block_relay_peers = peers.clone();
        let block_relay_network = self.node.config.network;
        tokio::spawn(async move {
            loop {
                let tip = match chain_events.recv().await {
                    Ok(tip) => tip,
                    Err(tokio::sync::broadcast::error::RecvError::Lagged(_)) => continue,
                    Err(tokio::sync::broadcast::error::RecvError::Closed) => break,
                };
                let block = block_relay_node
                    .chain
                    .write()
                    .block(&tip.hash)
                    .ok()
                    .flatten();
                if block.is_some() {
                    broadcast_inventory(
                        &block_relay_node,
                        &block_relay_peers,
                        0,
                        block_relay_network,
                        Inventory {
                            kind: InventoryType::WitnessBlock,
                            hash: tip.hash,
                        },
                    )
                    .await;
                }
            }
        });
        let relay_peers = peers.clone();
        let relay_node = self.node.clone();
        let relay_network = self.node.config.network;
        tokio::spawn(async move {
            loop {
                let event = match mempool_events.recv().await {
                    Ok(event) => event,
                    Err(tokio::sync::broadcast::error::RecvError::Lagged(_)) => continue,
                    Err(tokio::sync::broadcast::error::RecvError::Closed) => break,
                };
                if relay_node.config.blocksonly {
                    continue;
                }
                let Some(hash) = relay_node
                    .mempool
                    .read()
                    .get(&event.txid)
                    .map(|entry| entry.transaction.compute_wtxid())
                else {
                    // Removal notifications share the public mempool event
                    // stream, but a removed transaction must never be
                    // announced as if it were still relayable.
                    continue;
                };
                broadcast_inventory_excluding(
                    &relay_node,
                    &relay_peers,
                    &event.excluded_peers,
                    relay_network,
                    Inventory {
                        kind: InventoryType::WitnessTransaction,
                        hash: BlockHash::from_raw_hash(hash.to_raw_hash()),
                    },
                )
                .await;
            }
        });
        let configured_seed_nodes = !self.node.config.seed_nodes.is_empty();
        let seed_nodes = if !configured_seed_nodes && self.node.config.dnsseed {
            let addresses = discover_dns_seeds(self.node.config.network).await;
            for address in &addresses {
                self.node.remember_address(
                    *address,
                    wire::NODE_NETWORK | wire::NODE_WITNESS,
                    unix_time_seconds(),
                );
            }
            Vec::new()
        } else {
            self.node.config.seed_nodes.clone()
        };
        for address in seed_nodes {
            self.node.ensure_node_added(address);
            spawn_outbound_loop(self.node.clone(), address, outbound.clone(), true, None);
        }
        let discovery_node = self.node.clone();
        let discovery_outbound = outbound.clone();
        if !configured_seed_nodes {
            tokio::spawn(async move {
                let mut ticker = tokio::time::interval(Duration::from_secs(30));
                ticker.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
                loop {
                    ticker.tick().await;
                    if !discovery_node.network_active() {
                        continue;
                    }
                    let available = discovery_outbound.slots.available_permits().min(8);
                    if available == 0 {
                        continue;
                    }
                    for address in select_discovery_addresses(
                        &discovery_node,
                        available,
                        &discovery_outbound.attempts,
                    ) {
                        spawn_outbound_loop(
                            discovery_node.clone(),
                            address,
                            discovery_outbound.clone(),
                            false,
                            None,
                        );
                    }
                }
            });
        }
        let dynamic_node = self.node.clone();
        let dynamic_outbound = outbound.clone();
        tokio::spawn(async move {
            while let Some(request) = add_node_receiver.recv().await {
                let (address, persistent, transport_v2) = match request {
                    PeerManagerRequest::Add(address) => (address, true, None),
                    PeerManagerRequest::OneTry(address, transport_v2) => {
                        (address, false, transport_v2)
                    }
                };
                spawn_outbound_loop(
                    dynamic_node.clone(),
                    address,
                    dynamic_outbound.clone(),
                    persistent,
                    transport_v2,
                );
            }
        });

        let Some(listener) = listener else {
            return std::future::pending::<Result<()>>().await;
        };
        loop {
            let (stream, address) = listener.accept().await?;
            if !self.node.network_active() || self.node.is_banned(address.ip()) {
                continue;
            }
            let node = self.node.clone();
            let slots = slots.clone();
            let peers = peers.clone();
            let peer_id = next_peer_id.fetch_add(1, Ordering::Relaxed);
            tokio::spawn(async move {
                let Ok(permit) = slots.try_acquire_owned() else {
                    debug!(%address, "rejecting peer because peer limit is reached");
                    return;
                };
                if let Err(error) =
                    serve_peer(node, stream, address, false, None, peers, peer_id).await
                {
                    debug!(%address, %error, "inbound peer ended");
                }
                drop(permit);
            });
        }
    }
}

fn spawn_outbound_loop(
    node: Arc<Node>,
    address: std::net::SocketAddr,
    outbound: OutboundContext,
    persistent: bool,
    transport_v2: Option<bool>,
) {
    {
        let mut attempts = outbound.attempts.lock();
        if !attempts.insert(address) {
            return;
        }
    }
    let peer_id = outbound.next_peer_id.fetch_add(1, Ordering::Relaxed);
    let OutboundContext {
        slots,
        peers,
        attempts: outbound_attempts,
        ..
    } = outbound;
    tokio::spawn(async move {
        struct AttemptGuard {
            address: SocketAddr,
            attempts: OutboundAttempts,
        }

        impl Drop for AttemptGuard {
            fn drop(&mut self) {
                self.attempts.lock().remove(&self.address);
            }
        }

        let _attempt = AttemptGuard {
            address,
            attempts: outbound_attempts,
        };
        let Ok(_permit) = slots.acquire_owned().await else {
            return;
        };
        loop {
            if persistent && !node.is_node_added(address) {
                return;
            }
            if !node.network_active() || node.is_banned(address.ip()) {
                tokio::time::sleep(Duration::from_secs(1)).await;
                continue;
            }
            if node
                .peer_infos()
                .into_iter()
                .any(|peer| peer.address == address)
            {
                if !persistent {
                    return;
                }
                tokio::time::sleep(Duration::from_secs(5)).await;
                continue;
            }
            match TcpStream::connect(address).await {
                Ok(stream) => {
                    info!(%address, "connected to configured peer");
                    if let Err(error) = serve_peer(
                        node.clone(),
                        stream,
                        address,
                        true,
                        transport_v2,
                        peers.clone(),
                        peer_id,
                    )
                    .await
                    {
                        debug!(%address, %error, "outbound peer ended");
                    }
                    if !persistent {
                        return;
                    }
                }
                Err(error) => {
                    if !persistent {
                        debug!(%address, %error, "one-shot peer connection failed");
                        return;
                    }
                    warn!(%address, %error, "unable to connect to configured peer");
                }
            }
            tokio::time::sleep(Duration::from_secs(5)).await;
        }
    });
}

fn select_discovery_addresses(
    node: &Arc<Node>,
    limit: usize,
    outbound_attempts: &OutboundAttempts,
) -> Vec<SocketAddr> {
    if limit == 0 {
        return Vec::new();
    }
    let connected: HashSet<_> = node
        .peer_infos()
        .into_iter()
        .map(|peer| peer.address)
        .collect();
    let added: HashSet<_> = node.added_nodes().into_iter().collect();
    let attempts = outbound_attempts.lock();
    let mut candidates = node
        .known_addresses()
        .into_iter()
        .filter(|peer| {
            peer.address.port() != 0
                && !peer.address.ip().is_unspecified()
                && !connected.contains(&peer.address)
                && !added.contains(&peer.address)
                && !attempts.contains(&peer.address)
                && !node.is_banned(peer.address.ip())
        })
        .collect::<Vec<_>>();
    drop(attempts);
    candidates.sort_by(|left, right| {
        node.is_address_tried(right.address)
            .cmp(&node.is_address_tried(left.address))
            .then_with(|| right.connected_at.cmp(&left.connected_at))
            .then_with(|| left.address.cmp(&right.address))
    });
    candidates
        .into_iter()
        .take(limit)
        .map(|peer| peer.address)
        .collect()
}

async fn discover_dns_seeds(network: Network) -> Vec<std::net::SocketAddr> {
    let hosts: &[&str] = match network {
        Network::Bitcoin => &[
            "seed.bitcoin.sipa.be",
            "dnsseed.bluematt.me",
            "seed.bitcoinstats.com",
            "seed.bitcoin.jonasschnelli.ch",
            "seed.btc.petertodd.org",
            "seed.bitcoin.sprovoost.nl",
            "dnsseed.emzy.de",
            "seed.bitcoin.wiz.biz",
        ],
        Network::Testnet => &[
            "testnet-seed.bitcoin.jonasschnelli.ch",
            "seed.tbtc.petertodd.org",
            "seed.testnet.bitcoin.sprovoost.nl",
            "testnet-seed.bluematt.me",
        ],
        Network::Signet => &[
            "seed.signet.bitcoin.sprovoost.nl",
            "xarb1.signet.seed.bluematt.me",
        ],
        Network::Testnet4 | Network::Regtest => &[],
    };
    let port = match network {
        Network::Bitcoin => 8333,
        Network::Testnet => 18333,
        Network::Testnet4 => 48333,
        Network::Signet => 38333,
        Network::Regtest => return Vec::new(),
    };
    let mut addresses = Vec::new();
    for host in hosts {
        if let Ok(resolved) = tokio::net::lookup_host((*host, port)).await {
            addresses.extend(resolved.take(16));
        }
        if addresses.len() >= 64 {
            break;
        }
    }
    addresses
}

async fn establish_transport(
    stream: TcpStream,
    address: SocketAddr,
    outbound: bool,
    network: Network,
    transport_v2: Option<bool>,
) -> Result<(PeerReader, PeerWriterKind, Option<SocketAddr>)> {
    if outbound {
        if transport_v2 == Some(false) {
            return establish_v1(stream);
        }
        if transport_v2 == Some(true) {
            return establish_v2(stream, network, Role::Initiator).await;
        }
        match establish_v2(stream, network, Role::Initiator).await {
            Ok((reader, writer, local_address)) => {
                return Ok((reader, writer, local_address));
            }
            Err(error) => {
                debug!(%address, %error, "BIP324 handshake failed; retrying with v1");
                let fallback = TcpStream::connect(address)
                    .await
                    .with_context(|| format!("reconnecting to {address} with v1 transport"))?;
                fallback.set_nodelay(true)?;
                return establish_v1(fallback);
            }
        }
    }

    let mut prefix = [0u8; 16];
    let mut received = 0;
    while received < prefix.len() {
        let count = stream.peek(&mut prefix[received..]).await?;
        if count == 0 {
            anyhow::bail!("peer closed before transport negotiation");
        }
        received += count;
    }

    let mut v1_prefix = [0u8; 16];
    v1_prefix[..4].copy_from_slice(&wire::network_magic(network));
    v1_prefix[4..11].copy_from_slice(b"version");
    if prefix == v1_prefix {
        establish_v1(stream)
    } else {
        establish_v2(stream, network, Role::Responder).await
    }
}

async fn establish_v2(
    stream: TcpStream,
    network: Network,
    role: Role,
) -> Result<(PeerReader, PeerWriterKind, Option<SocketAddr>)> {
    let local_address = stream.local_addr().ok();
    let (reader, writer) = stream.into_split();
    let protocol = Protocol::new(
        wire::network_magic(network),
        role,
        None,
        None,
        BufReader::new(reader),
        writer,
    )
    .await?;
    let (reader, writer) = protocol.into_split();
    Ok((
        PeerReader::V2(reader),
        PeerWriterKind::V2(writer),
        local_address,
    ))
}

fn establish_v1(stream: TcpStream) -> Result<(PeerReader, PeerWriterKind, Option<SocketAddr>)> {
    let local_address = stream.local_addr().ok();
    let (reader, writer) = stream.into_split();
    Ok((
        PeerReader::V1(reader),
        PeerWriterKind::V1(writer),
        local_address,
    ))
}

async fn serve_peer(
    node: Arc<Node>,
    stream: TcpStream,
    address: std::net::SocketAddr,
    outbound: bool,
    transport_v2: Option<bool>,
    peers: PeerRegistry,
    peer_id: usize,
) -> Result<()> {
    let _peer_count = PeerCountGuard::new(&node);
    stream.set_nodelay(true)?;
    let (mut reader, writer_half, local_address) =
        establish_transport(stream, address, outbound, node.config.network, transport_v2).await?;
    let (commands, command_receiver) = mpsc::unbounded_channel();
    node.register_peer_with_local(peer_id, address, !outbound, commands, local_address);
    let peer_state = Arc::new(PeerState {
        writer: Arc::new(Mutex::new(writer_half)),
        bloom_filter: parking_lot::Mutex::new(None),
        known_tx_inventory: parking_lot::Mutex::new(KnownTxInventory::new()),
        fee_filter: parking_lot::Mutex::new(0),
        relay_transactions: parking_lot::Mutex::new(true),
        wtxid_relay: parking_lot::Mutex::new(false),
        send_headers: parking_lot::Mutex::new(false),
        compact_block_version: parking_lot::Mutex::new(None),
        compact_block_announce: parking_lot::Mutex::new(false),
        tx_reconciliation_salt: parking_lot::Mutex::new(None),
        tx_reconciliation_registered: parking_lot::Mutex::new(false),
    });
    peers.lock().insert(peer_id, peer_state.clone());
    let result = serve_peer_loop(
        &node,
        &mut reader,
        &peer_state,
        outbound,
        &peers,
        peer_id,
        command_receiver,
    )
    .await;
    peers.lock().remove(&peer_id);
    node.unregister_peer(peer_id);
    result
}

struct PeerCountGuard<'a> {
    count: &'a AtomicUsize,
}

impl<'a> PeerCountGuard<'a> {
    fn new(node: &'a Arc<Node>) -> Self {
        node.peer_count.fetch_add(1, Ordering::Relaxed);
        Self {
            count: &node.peer_count,
        }
    }
}

impl Drop for PeerCountGuard<'_> {
    fn drop(&mut self) {
        self.count.fetch_sub(1, Ordering::Relaxed);
    }
}

async fn serve_peer_loop(
    node: &Arc<Node>,
    reader: &mut PeerReader,
    peer_state: &PeerState,
    outbound: bool,
    peers: &PeerRegistry,
    peer_id: usize,
    mut commands: mpsc::UnboundedReceiver<PeerCommand>,
) -> Result<()> {
    let writer = &peer_state.writer;
    let bloom_filter = &peer_state.bloom_filter;
    let fee_filter = &peer_state.fee_filter;
    let relay_transactions = &peer_state.relay_transactions;
    let height = node.chain.read().height() as i32;
    let local_nonce = random();
    let mut version =
        VersionMessage::with_bloom(height, local_nonce, node.config.peer_bloom_filters);
    if !(node.config.blockfilterindex && node.config.peer_block_filters) {
        version.services &= !wire::NODE_COMPACT_FILTERS;
        version.receiver_services &= !wire::NODE_COMPACT_FILTERS;
        version.sender_services &= !wire::NODE_COMPACT_FILTERS;
    }
    version.relay = !node.config.blocksonly;
    send_message(
        node,
        peer_id,
        writer,
        node.config.network,
        &Message::Version(version),
    )
    .await?;
    let mut version_received = false;
    let mut verack_received = false;
    let mut verack_sent = false;
    let mut extensions_sent = false;
    let mut addrv2_received = false;
    let mut peer_version = 0i32;
    let mut compact_block_version = 2u64;
    let mut pending_compact = None;
    let mut ping_interval = tokio::time::interval(Duration::from_secs(120));
    ping_interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
    loop {
        if !node.network_active() {
            anyhow::bail!("networking is disabled");
        }
        let message = tokio::select! {
            command = commands.recv() => {
                match command {
                    Some(PeerCommand::Disconnect) | None => anyhow::bail!("peer disconnected by node"),
                    Some(PeerCommand::RequestBlock(hash)) => {
                        send_message(
                            node,
                            peer_id,
                            writer,
                            node.config.network,
                            &Message::GetData(vec![Inventory {
                                kind: InventoryType::WitnessBlock,
                                hash,
                            }]),
                        ).await?;
                        continue;
                    }
                    Some(PeerCommand::Ping(nonce)) => {
                        send_message(
                            node,
                            peer_id,
                            writer,
                            node.config.network,
                            &Message::Ping(nonce),
                        ).await?;
                        continue;
                    }
                    Some(PeerCommand::SendMessage { command, payload }) => {
                        send_message(
                            node,
                            peer_id,
                            writer,
                            node.config.network,
                            &Message::Unknown { command, payload },
                        ).await?;
                        continue;
                    }
                }
            }
            message = reader.read_message(node.config.network) => {
                let (message, bytes) = message?;
                node.record_bytes_received(peer_id, bytes);
                message
            },
            _ = ping_interval.tick(), if version_received && verack_received => {
                if node.ping_timed_out(peer_id, PING_TIMEOUT) {
                    anyhow::bail!("peer ping timed out");
                }
                let nonce = random();
                if node.record_ping(peer_id, nonce) {
                    send_message(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &Message::Ping(nonce),
                    )
                    .await?;
                }
                continue;
            }
        };
        if !version_received && !matches!(&message, Message::Version(_)) {
            // Core ignores application messages until VERSION has been
            // received. In particular, a VERACK received first must not
            // complete the handshake state prematurely.
            continue;
        }
        match message {
            Message::Version(version) => {
                if version_received {
                    anyhow::bail!("duplicate version message");
                }
                version_received = true;
                if version.version < 70001 {
                    anyhow::bail!("peer protocol version is too old");
                }
                if version.nonce == local_nonce {
                    anyhow::bail!("peer connected to itself");
                }
                peer_version = version.version;
                node.update_peer_version(
                    peer_id,
                    version.version,
                    version.services,
                    &version.user_agent,
                    version.start_height,
                    version.relay,
                );
                *relay_transactions.lock() = version.relay;
                if !verack_sent {
                    send_peer_extensions(
                        node,
                        peer_id,
                        writer,
                        peer_state,
                        node.config.network,
                        &mut extensions_sent,
                        peer_version,
                    )
                    .await?;
                    send_message(node, peer_id, writer, node.config.network, &Message::Verack)
                        .await?;
                    verack_sent = true;
                }
                if outbound {
                    debug!(user_agent = %version.user_agent, height = version.start_height, "completed outbound version exchange");
                }
            }
            Message::Verack => {
                verack_received = true;
                if !version_received {
                    continue;
                }
                send_peer_extensions(
                    node,
                    peer_id,
                    writer,
                    peer_state,
                    node.config.network,
                    &mut extensions_sent,
                    peer_version,
                )
                .await?;
                request_headers(node, peer_id, writer).await?;
                send_message(
                    node,
                    peer_id,
                    writer,
                    node.config.network,
                    &Message::GetAddr,
                )
                .await?;
            }
            Message::SendAddrV2 => {
                if verack_received {
                    anyhow::bail!("sendaddrv2 received after verack");
                }
                if peer_version >= WTXID_RELAY_VERSION {
                    addrv2_received = true;
                }
            }
            Message::WtxidRelay => {
                if verack_received {
                    anyhow::bail!("wtxidrelay received after verack");
                }
                if peer_version >= WTXID_RELAY_VERSION && !node.config.blocksonly {
                    *peer_state.wtxid_relay.lock() = true;
                }
            }
            Message::SendTxRcncl(message) => {
                if !node.config.zmq.tx_reconciliation {
                    // Core ignores the offer when reconciliation support is
                    // disabled, preserving compatibility with default nodes.
                    continue;
                }
                if verack_received {
                    anyhow::bail!("sendtxrcncl received after verack");
                }
                if peer_version < WTXID_RELAY_VERSION
                    || peer_state.tx_reconciliation_salt.lock().is_none()
                {
                    continue;
                }
                if !*relay_transactions.lock() {
                    anyhow::bail!("sendtxrcncl received from a non-relaying peer");
                }
                if message.version < TX_RECONCILIATION_VERSION {
                    anyhow::bail!("unsupported transaction reconciliation version");
                }
                let mut registered = peer_state.tx_reconciliation_registered.lock();
                if *registered {
                    anyhow::bail!("duplicate sendtxrcncl message");
                }
                *registered = true;
            }
            Message::Ping(nonce) => {
                send_message(
                    node,
                    peer_id,
                    writer,
                    node.config.network,
                    &Message::Pong(nonce),
                )
                .await?;
            }
            Message::Pong(nonce) => node.record_pong(peer_id, nonce),
            Message::GetHeaders(request) => {
                let headers = node
                    .chain
                    .read()
                    .headers_after_locator(&request.locator_hashes, request.stop_hash);
                send_message(
                    node,
                    peer_id,
                    writer,
                    node.config.network,
                    &Message::Headers(headers),
                )
                .await?;
            }
            Message::GetBlocks(request) => {
                let hashes = node
                    .chain
                    .read()
                    .headers_after_locator(&request.locator_hashes, request.stop_hash)
                    .into_iter()
                    .take(500)
                    .map(|header| Inventory {
                        kind: InventoryType::Block,
                        hash: header.block_hash(),
                    })
                    .collect::<Vec<_>>();
                send_message(
                    node,
                    peer_id,
                    writer,
                    node.config.network,
                    &Message::Inv(hashes),
                )
                .await?;
            }
            Message::Headers(headers) => {
                if headers.is_empty() {
                    continue;
                }
                let hashes = node.chain.write().accept_headers(&headers)?;
                let requests = {
                    let chain = node.chain.read();
                    hashes
                        .into_iter()
                        .filter(|hash| !chain.store.contains(hash))
                        .map(|hash| Inventory {
                            kind: InventoryType::Block,
                            hash,
                        })
                        .collect::<Vec<_>>()
                };
                if !requests.is_empty() {
                    send_message(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &Message::GetData(requests),
                    )
                    .await?;
                } else {
                    request_headers(node, peer_id, writer).await?;
                }
            }
            Message::Inv(items) => {
                let wtxid_relay = *peer_state.wtxid_relay.lock();
                {
                    let mut known = peer_state.known_tx_inventory.lock();
                    for item in &items {
                        let matching_kind = (wtxid_relay
                            && item.kind == InventoryType::WitnessTransaction)
                            || (!wtxid_relay && item.kind == InventoryType::Transaction);
                        if matching_kind {
                            known.insert(&item.hash);
                        }
                    }
                }
                let requests = {
                    let chain = node.chain.read();
                    let mempool = node.mempool.read();
                    items
                        .into_iter()
                        .filter(|item| match item.kind {
                            InventoryType::Block | InventoryType::WitnessBlock => {
                                !chain.store.contains(&item.hash)
                            }
                            InventoryType::CompactBlock => !chain.store.contains(&item.hash),
                            InventoryType::Transaction | InventoryType::WitnessTransaction => {
                                if node.config.blocksonly {
                                    return false;
                                }
                                if (wtxid_relay && item.kind == InventoryType::Transaction)
                                    || (!wtxid_relay
                                        && item.kind == InventoryType::WitnessTransaction)
                                {
                                    return false;
                                }
                                if item.kind == InventoryType::WitnessTransaction {
                                    mempool
                                        .get_by_wtxid(&Wtxid::from_byte_array(
                                            item.hash.to_byte_array(),
                                        ))
                                        .is_none()
                                } else {
                                    mempool
                                        .get(&Txid::from_byte_array(item.hash.to_byte_array()))
                                        .is_none()
                                }
                            }
                            _ => false,
                        })
                        .take(50_000)
                        .collect::<Vec<_>>()
                };
                if !requests.is_empty() {
                    send_message(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &Message::GetData(requests),
                    )
                    .await?;
                }
            }
            Message::GetData(items) => {
                let mut missing = Vec::new();
                for item in items {
                    match item.kind {
                        InventoryType::Block | InventoryType::WitnessBlock => {
                            let block = node.chain.write().block(&item.hash)?;
                            if let Some(block) = block {
                                send_message(
                                    node,
                                    peer_id,
                                    writer,
                                    node.config.network,
                                    &Message::Block(block),
                                )
                                .await?;
                            } else {
                                missing.push(item);
                            }
                        }
                        InventoryType::CompactBlock => {
                            let block = node.chain.write().block(&item.hash)?;
                            let Some(block) = block else {
                                missing.push(item);
                                continue;
                            };
                            let compact = HeaderAndShortIds::from_block(
                                &block,
                                random(),
                                compact_block_version as u32,
                                &[],
                            )?;
                            send_message(
                                node,
                                peer_id,
                                writer,
                                node.config.network,
                                &Message::CompactBlock(compact),
                            )
                            .await?;
                        }
                        InventoryType::FilteredBlock => {
                            let block = node.chain.write().block(&item.hash)?;
                            let Some(block) = block else {
                                missing.push(item);
                                continue;
                            };
                            let matching = {
                                let mut filter = bloom_filter.lock();
                                filter
                                    .as_mut()
                                    .map(|filter| filter.matched_transaction_ids(&block))
                                    .unwrap_or_default()
                            };
                            let matching: HashSet<Txid> = matching.into_iter().collect();
                            let merkle = MerkleBlock::from_block_with_predicate(&block, |txid| {
                                matching.contains(txid)
                            });
                            send_message(
                                node,
                                peer_id,
                                writer,
                                node.config.network,
                                &Message::MerkleBlock(merkle),
                            )
                            .await?;
                            for transaction in block.txdata.iter().filter(|transaction| {
                                matching.contains(&transaction.compute_txid())
                            }) {
                                send_message(
                                    node,
                                    peer_id,
                                    writer,
                                    node.config.network,
                                    &Message::Transaction(transaction.clone()),
                                )
                                .await?;
                            }
                        }
                        InventoryType::Transaction | InventoryType::WitnessTransaction => {
                            if node.config.blocksonly {
                                missing.push(item);
                                continue;
                            }
                            let transaction = {
                                let mempool = node.mempool.read();
                                if item.kind == InventoryType::WitnessTransaction {
                                    mempool
                                        .get_by_wtxid(&Wtxid::from_byte_array(
                                            item.hash.to_byte_array(),
                                        ))
                                        .map(|entry| entry.transaction.clone())
                                } else {
                                    mempool
                                        .get(&Txid::from_byte_array(item.hash.to_byte_array()))
                                        .map(|entry| entry.transaction.clone())
                                }
                            };
                            let transaction = if transaction.is_some() {
                                transaction
                            } else if item.kind == InventoryType::Transaction {
                                node.chain
                                    .write()
                                    .transaction(&Txid::from_byte_array(item.hash.to_byte_array()))?
                                    .map(|(transaction, _)| transaction)
                            } else {
                                None
                            };
                            if let Some(transaction) = transaction {
                                send_message(
                                    node,
                                    peer_id,
                                    writer,
                                    node.config.network,
                                    &Message::Transaction(transaction),
                                )
                                .await?;
                            } else {
                                missing.push(item);
                            }
                        }
                        _ => missing.push(item),
                    }
                }
                if !missing.is_empty() {
                    send_message(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &Message::NotFound(missing),
                    )
                    .await?;
                }
            }
            Message::Block(block) => {
                handle_received_block(node, peers, peer_id, block).await;
                request_headers(node, peer_id, writer).await?;
            }
            Message::CompactBlock(compact) => {
                let hash = compact.header.block_hash();
                match reconstruct_compact_block(&compact, node, compact_block_version) {
                    Ok((transactions, missing)) if missing.is_empty() => {
                        match complete_compact_block(&compact, transactions) {
                            Ok(block) => {
                                handle_received_block(node, peers, peer_id, block).await;
                                request_headers(node, peer_id, writer).await?;
                            }
                            Err(error) => {
                                debug!(%hash, %error, "invalid compact block reconstruction");
                                request_full_block(
                                    node,
                                    peer_id,
                                    writer,
                                    node.config.network,
                                    hash,
                                )
                                .await?;
                            }
                        }
                    }
                    Ok((transactions, missing)) => {
                        let request = BlockTransactionsRequest {
                            block_hash: hash,
                            indexes: missing.clone(),
                        };
                        pending_compact = Some(PendingCompactBlock {
                            compact,
                            transactions,
                            requested_indexes: missing,
                        });
                        send_message(
                            node,
                            peer_id,
                            writer,
                            node.config.network,
                            &Message::GetBlockTxn(request),
                        )
                        .await?;
                    }
                    Err(error) => {
                        debug!(%hash, %error, "unable to reconstruct compact block");
                        request_full_block(node, peer_id, writer, node.config.network, hash)
                            .await?;
                    }
                }
            }
            Message::GetBlockTxn(request) => {
                if request.indexes.len() > 100_000 {
                    debug!("compact block transaction request is too large");
                    continue;
                }
                let block = node.chain.write().block(&request.block_hash)?;
                let Some(block) = block else {
                    continue;
                };
                let mut transactions = Vec::with_capacity(request.indexes.len());
                let mut valid = true;
                for index in &request.indexes {
                    let Ok(index) = usize::try_from(*index) else {
                        valid = false;
                        break;
                    };
                    let Some(transaction) = block.txdata.get(index) else {
                        valid = false;
                        break;
                    };
                    transactions.push(transaction.clone());
                }
                if valid {
                    send_message(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &Message::BlockTxn(BlockTransactions {
                            block_hash: request.block_hash,
                            transactions,
                        }),
                    )
                    .await?;
                }
            }
            Message::BlockTxn(response) => {
                let Some(mut pending) = pending_compact.take() else {
                    continue;
                };
                if response.block_hash != pending.compact.header.block_hash()
                    || response.transactions.len() != pending.requested_indexes.len()
                {
                    request_full_block(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        pending.compact.header.block_hash(),
                    )
                    .await?;
                    continue;
                }
                let mut valid = true;
                for (index, transaction) in pending
                    .requested_indexes
                    .iter()
                    .copied()
                    .zip(response.transactions)
                {
                    let Ok(index) = usize::try_from(index) else {
                        valid = false;
                        break;
                    };
                    let Some(slot) = pending.transactions.get_mut(index) else {
                        valid = false;
                        break;
                    };
                    if slot.is_some() {
                        valid = false;
                        break;
                    }
                    *slot = Some(transaction);
                }
                if !valid || pending.transactions.iter().any(Option::is_none) {
                    request_full_block(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        pending.compact.header.block_hash(),
                    )
                    .await?;
                    continue;
                }
                match complete_compact_block(&pending.compact, pending.transactions) {
                    Ok(block) => {
                        handle_received_block(node, peers, peer_id, block).await;
                        request_headers(node, peer_id, writer).await?;
                    }
                    Err(error) => {
                        let hash = pending.compact.header.block_hash();
                        debug!(%hash, %error, "invalid compact block completion");
                        request_full_block(node, peer_id, writer, node.config.network, hash)
                            .await?;
                    }
                }
            }
            Message::GetCFilters(request) => {
                if !(node.config.blockfilterindex && node.config.peer_block_filters) {
                    continue;
                }
                if request.filter_type != 0 {
                    continue;
                }
                let Some(range) =
                    basic_filter_range(node, request.start_height, request.stop_hash, 1_000)?
                else {
                    continue;
                };
                for (block_hash, filter, _) in range.filters {
                    send_message(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &Message::CFilter(CFilter {
                            filter_type: 0,
                            block_hash,
                            filter,
                        }),
                    )
                    .await?;
                }
            }
            Message::GetCFHeaders(request) => {
                if !(node.config.blockfilterindex && node.config.peer_block_filters) {
                    continue;
                }
                if request.filter_type != 0 {
                    continue;
                }
                let Some(range) =
                    basic_filter_range(node, request.start_height, request.stop_hash, 2_000)?
                else {
                    continue;
                };
                let filter_hashes = range
                    .filters
                    .iter()
                    .map(|(_, filter, _)| FilterHash::hash(filter))
                    .collect();
                let stop_hash = range
                    .filters
                    .last()
                    .map(|(hash, _, _)| *hash)
                    .unwrap_or(range.stop_hash);
                send_message(
                    node,
                    peer_id,
                    writer,
                    node.config.network,
                    &Message::CFHeaders(CFHeaders {
                        filter_type: 0,
                        stop_hash,
                        previous_filter_header: range.previous_filter_header,
                        filter_hashes,
                    }),
                )
                .await?;
            }
            Message::GetCFCheckpt(request) => {
                if !(node.config.blockfilterindex && node.config.peer_block_filters) {
                    continue;
                }
                if request.filter_type != 0 {
                    continue;
                }
                let (stop_hash, filter_headers) = {
                    let mut chain = node.chain.write();
                    let stop_hash = if request.stop_hash == BlockHash::all_zeros() {
                        chain.best_hash()
                    } else {
                        request.stop_hash
                    };
                    let Some(stop_height) = chain.block_height_by_hash(&stop_hash) else {
                        continue;
                    };
                    if !chain.is_active_block(&stop_hash) {
                        continue;
                    }
                    let filter_headers = (999..=stop_height)
                        .step_by(1_000)
                        .map(|height| {
                            let block_hash = chain.block_hash(height).ok_or_else(|| {
                                anyhow::anyhow!("compact filter height is out of range")
                            })?;
                            chain
                                .basic_filter_header_for_block(&block_hash)?
                                .ok_or_else(|| anyhow::anyhow!("compact filter is missing"))
                        })
                        .collect::<Result<Vec<_>>>()?;
                    (stop_hash, filter_headers)
                };
                send_message(
                    node,
                    peer_id,
                    writer,
                    node.config.network,
                    &Message::CFCheckpt(CFCheckpt {
                        filter_type: 0,
                        stop_hash,
                        filter_headers,
                    }),
                )
                .await?;
            }
            Message::Transaction(transaction) => {
                if node.config.blocksonly {
                    continue;
                }
                let known_hash = if *peer_state.wtxid_relay.lock() {
                    BlockHash::from_raw_hash(transaction.compute_wtxid().to_raw_hash())
                } else {
                    BlockHash::from_raw_hash(transaction.compute_txid().to_raw_hash())
                };
                peer_state.known_tx_inventory.lock().insert(&known_hash);
                let txid = transaction.compute_txid();
                let accepted = node
                    .accept_peer_transaction_from(peer_id, transaction)
                    .is_ok();
                if accepted {
                    debug!(%txid, "accepted peer transaction");
                } else {
                    debug!(%txid, "rejected peer transaction");
                }
            }
            Message::FilterLoad(filter) => {
                *bloom_filter.lock() = Some(BloomFilter::from_message(filter)?);
            }
            Message::FilterAdd(FilterAdd { data }) => {
                if data.len() > MAX_BLOOM_ELEMENT_SIZE {
                    anyhow::bail!("bloom filter element exceeds the 520-byte limit");
                }
                let mut filter = bloom_filter.lock();
                let Some(filter) = filter.as_mut() else {
                    anyhow::bail!("filteradd received before filterload");
                };
                filter.insert(&data);
            }
            Message::FilterClear => {
                *bloom_filter.lock() = None;
            }
            Message::MerkleBlock(_) => {}
            Message::Addr(addresses) => {
                for entry in addresses {
                    if let Some(address) = socket_address_from_legacy(&entry) {
                        node.remember_address(address, entry.services, u64::from(entry.time));
                    }
                }
            }
            Message::AddrV2(addresses) => {
                for address in addresses {
                    if let Some(socket) = socket_address_from_v2(&address) {
                        node.remember_address(socket, address.services, u64::from(address.time));
                    }
                }
            }
            Message::SendHeaders => {
                *peer_state.send_headers.lock() = true;
            }
            Message::CFilter(_)
            | Message::CFHeaders(_)
            | Message::CFCheckpt(_)
            | Message::NotFound(_)
            | Message::Unknown { .. } => {}
            Message::FeeFilter(rate) => {
                let rate = rate.max(0);
                *fee_filter.lock() = rate;
                node.update_peer_fee_filter(peer_id, rate);
            }
            Message::SendCmpct { announce, version } => {
                if version == 1 || version == 2 {
                    compact_block_version = version;
                    *peer_state.compact_block_version.lock() = Some(version);
                    *peer_state.compact_block_announce.lock() = announce;
                }
            }
            Message::GetAddr => {
                let peer_infos = node
                    .known_addresses()
                    .into_iter()
                    .take(1_000)
                    .collect::<Vec<_>>();
                if addrv2_received {
                    let addresses = peer_infos
                        .into_iter()
                        .map(|peer| {
                            network_address_v2(peer.address, peer.connected_at, peer.services)
                        })
                        .collect::<Vec<_>>();
                    send_message(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &Message::AddrV2(addresses),
                    )
                    .await?;
                } else {
                    let addresses = peer_infos
                        .into_iter()
                        .map(|peer| wire::NetworkAddress {
                            time: u32::try_from(peer.connected_at).unwrap_or(u32::MAX),
                            services: peer.services,
                            address: socket_address_bytes(peer.address),
                            port: peer.address.port(),
                        })
                        .collect::<Vec<_>>();
                    send_message(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &Message::Addr(addresses),
                    )
                    .await?;
                }
            }
            Message::Mempool => {
                if node.config.blocksonly || !*relay_transactions.lock() {
                    send_message(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &Message::Inv(Vec::new()),
                    )
                    .await?;
                    continue;
                }
                let transactions = {
                    let mempool = node.mempool.read();
                    let minimum_fee = *fee_filter.lock();
                    mempool
                        .transaction_order()
                        .into_iter()
                        .filter_map(|txid| {
                            mempool.get(&txid).and_then(|entry| {
                                let fee_rate = fee_rate_sat_per_kvb(entry.fee_sat, entry.vsize);
                                (fee_rate >= minimum_fee).then(|| entry.transaction.clone())
                            })
                        })
                        .take(50_000)
                        .collect::<Vec<_>>()
                };
                let inventory = {
                    let mut filter = bloom_filter.lock();
                    let wtxid_relay = *peer_state.wtxid_relay.lock();
                    let mut known = peer_state.known_tx_inventory.lock();
                    transactions
                        .into_iter()
                        .filter_map(|transaction| {
                            if let Some(filter) = filter.as_mut()
                                && !filter.is_relevant_and_update(&transaction)
                            {
                                return None;
                            }
                            let item = transaction_inventory(&transaction, wtxid_relay);
                            if known.contains(&item.hash) {
                                return None;
                            }
                            known.insert(&item.hash);
                            Some(item)
                        })
                        .collect::<Vec<_>>()
                };
                send_message(
                    node,
                    peer_id,
                    writer,
                    node.config.network,
                    &Message::Inv(inventory),
                )
                .await?;
            }
        }
        if version_received && verack_received && !verack_sent {
            send_message(node, peer_id, writer, node.config.network, &Message::Verack).await?;
            verack_sent = true;
        }
    }
}

fn basic_filter_range(
    node: &Arc<Node>,
    start_height: u32,
    requested_stop_hash: BlockHash,
    limit: usize,
) -> Result<Option<BasicFilterRange>> {
    let mut chain = node.chain.write();
    let stop_hash = if requested_stop_hash == BlockHash::all_zeros() {
        chain.best_hash()
    } else {
        requested_stop_hash
    };
    let Some(stop_height) = chain.block_height_by_hash(&stop_hash) else {
        return Ok(None);
    };
    if !chain.is_active_block(&stop_hash) || start_height > stop_height {
        return Ok(None);
    }
    let Some(range) = chain.basic_filter_range(start_height, stop_hash, limit)? else {
        return Ok(None);
    };
    Ok(Some(range))
}

async fn handle_received_block(
    node: &Arc<Node>,
    peers: &PeerRegistry,
    peer_id: usize,
    block: Block,
) {
    let hash = block.block_hash();
    let (was_stored, previous_tip) = {
        let chain = node.chain.read();
        (chain.store.contains(&hash), chain.best_hash())
    };
    match node.connect_block(block) {
        Ok(tip) => {
            info!(%hash, height = tip.height, "accepted peer block");
            // Active-tip updates are announced by the chain-event relay. A
            // side-chain block has no tip event, so relay a newly accepted
            // side-chain block here. Avoid announcing duplicate blocks.
            if !was_stored && tip.hash == previous_tip && hash != previous_tip {
                broadcast_inventory(
                    node,
                    peers,
                    peer_id,
                    node.config.network,
                    Inventory {
                        kind: InventoryType::WitnessBlock,
                        hash,
                    },
                )
                .await;
            }
        }
        Err(error) => debug!(%hash, %error, "rejected peer block"),
    }
}

async fn request_full_block(
    node: &Arc<Node>,
    peer_id: usize,
    writer: &PeerWriter,
    network: Network,
    hash: BlockHash,
) -> Result<()> {
    send_message(
        node,
        peer_id,
        writer,
        network,
        &Message::GetData(vec![Inventory {
            kind: InventoryType::WitnessBlock,
            hash,
        }]),
    )
    .await
}

fn reconstruct_compact_block(
    compact: &HeaderAndShortIds,
    node: &Arc<Node>,
    version: u64,
) -> Result<(Vec<Option<Transaction>>, Vec<u64>)> {
    if version != 1 && version != 2 {
        anyhow::bail!("unsupported compact block version {version}");
    }
    let transaction_count = compact
        .short_ids
        .len()
        .checked_add(compact.prefilled_txs.len())
        .ok_or_else(|| anyhow::anyhow!("compact block transaction count overflow"))?;
    if transaction_count == 0 || transaction_count > 1_000_000 {
        anyhow::bail!("invalid compact block transaction count");
    }
    let mut transactions = vec![None; transaction_count];
    let mut last_prefilled = 0usize;
    for prefilled in &compact.prefilled_txs {
        let index = last_prefilled
            .checked_add(prefilled.idx as usize)
            .ok_or_else(|| anyhow::anyhow!("compact block prefilled index overflow"))?;
        if index >= transaction_count || transactions[index].is_some() {
            anyhow::bail!("invalid compact block prefilled index");
        }
        transactions[index] = Some(prefilled.tx.clone());
        last_prefilled = index.saturating_add(1);
    }

    let siphash_keys = ShortId::calculate_siphash_keys(&compact.header, compact.nonce);
    let mut candidates: HashMap<ShortId, Option<Transaction>> = HashMap::new();
    let mempool = node.mempool.read();
    for transaction in mempool.transactions() {
        let short_id = compact_short_id(transaction, version, siphash_keys);
        match candidates.entry(short_id) {
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(Some(transaction.clone()));
            }
            std::collections::hash_map::Entry::Occupied(mut entry) => {
                entry.insert(None);
            }
        }
    }

    let mut missing = Vec::new();
    let mut short_ids = compact.short_ids.iter();
    for (index, transaction) in transactions.iter_mut().enumerate() {
        if transaction.is_some() {
            continue;
        }
        let Some(short_id) = short_ids.next() else {
            anyhow::bail!("compact block short-id count is inconsistent");
        };
        match candidates.get(short_id) {
            Some(Some(candidate)) => *transaction = Some(candidate.clone()),
            _ => missing.push(index as u64),
        }
    }
    if short_ids.next().is_some() {
        anyhow::bail!("compact block has too many short ids");
    }
    Ok((transactions, missing))
}

fn compact_short_id(transaction: &Transaction, version: u64, siphash_keys: (u64, u64)) -> ShortId {
    match version {
        1 => ShortId::with_siphash_keys(&transaction.compute_txid().to_raw_hash(), siphash_keys),
        2 => ShortId::with_siphash_keys(&transaction.compute_wtxid().to_raw_hash(), siphash_keys),
        _ => unreachable!("compact block version validated by caller"),
    }
}

fn complete_compact_block(
    compact: &HeaderAndShortIds,
    transactions: Vec<Option<Transaction>>,
) -> Result<Block> {
    let txdata = transactions
        .into_iter()
        .collect::<Option<Vec<Transaction>>>()
        .ok_or_else(|| anyhow::anyhow!("compact block still has missing transactions"))?;
    let block = Block {
        header: compact.header,
        txdata,
    };
    if block.block_hash() != compact.header.block_hash() {
        anyhow::bail!("compact block header hash changed during reconstruction");
    }
    Ok(block)
}

fn socket_address_bytes(address: std::net::SocketAddr) -> [u8; 16] {
    match address.ip() {
        std::net::IpAddr::V4(ip) => {
            let mut bytes = [0u8; 16];
            bytes[10..12].copy_from_slice(&[0xff, 0xff]);
            bytes[12..].copy_from_slice(&ip.octets());
            bytes
        }
        std::net::IpAddr::V6(ip) => ip.octets(),
    }
}

fn socket_address_from_legacy(address: &wire::NetworkAddress) -> Option<std::net::SocketAddr> {
    let ip = if address.address[..10] == [0; 10] && address.address[10..12] == [0xff, 0xff] {
        std::net::IpAddr::V4(std::net::Ipv4Addr::new(
            address.address[12],
            address.address[13],
            address.address[14],
            address.address[15],
        ))
    } else {
        std::net::IpAddr::V6(std::net::Ipv6Addr::from(address.address))
    };
    (address.port != 0).then(|| std::net::SocketAddr::new(ip, address.port))
}

fn socket_address_from_v2(address: &wire::NetworkAddressV2) -> Option<std::net::SocketAddr> {
    let ip = match address.network {
        1 => std::net::IpAddr::V4(std::net::Ipv4Addr::from(
            <[u8; 4]>::try_from(address.address.as_slice()).ok()?,
        )),
        2 => std::net::IpAddr::V6(std::net::Ipv6Addr::from(
            <[u8; 16]>::try_from(address.address.as_slice()).ok()?,
        )),
        _ => return None,
    };
    (address.port != 0).then(|| std::net::SocketAddr::new(ip, address.port))
}

fn network_address_v2(
    address: std::net::SocketAddr,
    connected_at: u64,
    services: u64,
) -> wire::NetworkAddressV2 {
    let port = address.port();
    let (network, address) = match address.ip() {
        std::net::IpAddr::V4(ip) => (1, ip.octets().to_vec()),
        std::net::IpAddr::V6(ip) => (2, ip.octets().to_vec()),
    };
    wire::NetworkAddressV2 {
        time: u32::try_from(connected_at).unwrap_or(u32::MAX),
        services,
        network,
        address,
        port,
    }
}

async fn send_peer_extensions(
    node: &Arc<Node>,
    peer_id: usize,
    writer: &PeerWriter,
    peer_state: &PeerState,
    network: Network,
    sent: &mut bool,
    peer_version: i32,
) -> Result<()> {
    if *sent {
        return Ok(());
    }
    if peer_version >= SENDHEADERS_VERSION {
        send_message(node, peer_id, writer, network, &Message::SendHeaders).await?;
    }
    if peer_version >= WTXID_RELAY_VERSION {
        if !node.config.blocksonly {
            send_message(node, peer_id, writer, network, &Message::WtxidRelay).await?;
        }
        send_message(node, peer_id, writer, network, &Message::SendAddrV2).await?;
        if node.config.zmq.tx_reconciliation
            && *peer_state.relay_transactions.lock()
            && !node.config.blocksonly
        {
            let salt = random::<u64>();
            send_message(
                node,
                peer_id,
                writer,
                network,
                &Message::SendTxRcncl(SendTxRcnclMessage {
                    version: TX_RECONCILIATION_VERSION,
                    salt,
                }),
            )
            .await?;
            *peer_state.tx_reconciliation_salt.lock() = Some(salt);
        }
    }
    if peer_version >= SHORT_IDS_BLOCKS_VERSION {
        send_message(
            node,
            peer_id,
            writer,
            network,
            &Message::SendCmpct {
                announce: false,
                version: 2,
            },
        )
        .await?;
    }
    if peer_version >= FEEFILTER_VERSION {
        send_message(node, peer_id, writer, network, &Message::FeeFilter(1_000)).await?;
    }
    *sent = true;
    Ok(())
}

async fn request_headers(node: &Arc<Node>, peer_id: usize, writer: &PeerWriter) -> Result<()> {
    let locator = node.chain.read().block_locator_hashes();
    send_message(
        node,
        peer_id,
        writer,
        node.config.network,
        &Message::GetHeaders(GetHeadersMessage {
            version: VersionMessage::PROTOCOL_VERSION,
            locator_hashes: locator,
            stop_hash: BlockHash::all_zeros(),
        }),
    )
    .await
}

async fn send_message(
    node: &Arc<Node>,
    peer_id: usize,
    writer: &PeerWriter,
    network: Network,
    message: &Message,
) -> Result<()> {
    let mut writer = writer.lock().await;
    let bytes = match &mut *writer {
        PeerWriterKind::V1(writer) => {
            wire::write_message_with_size(writer, network, message).await?
        }
        PeerWriterKind::V2(writer) => {
            let contents = wire::encode_v2_message(message)?;
            let bytes = contents.len().saturating_add(20);
            writer.write(&Payload::genuine(contents)).await?;
            bytes
        }
    };
    node.record_bytes_sent(peer_id, bytes);
    Ok(())
}

async fn broadcast_inventory(
    node: &Arc<Node>,
    peers: &PeerRegistry,
    excluded_peer: usize,
    network: Network,
    item: Inventory,
) {
    broadcast_inventory_excluding(node, peers, &[excluded_peer], network, item).await;
}

async fn broadcast_inventory_excluding(
    node: &Arc<Node>,
    peers: &PeerRegistry,
    excluded_peers: &[usize],
    network: Network,
    item: Inventory,
) {
    if node.config.blocksonly
        && matches!(
            item.kind,
            InventoryType::Transaction | InventoryType::WitnessTransaction
        )
    {
        return;
    }
    let transaction = if matches!(
        item.kind,
        InventoryType::Transaction | InventoryType::WitnessTransaction
    ) {
        transaction_for_inventory(node, &item)
    } else {
        None
    };
    if matches!(
        item.kind,
        InventoryType::Transaction | InventoryType::WitnessTransaction
    ) && transaction.is_none()
    {
        return;
    }
    let recipients: Vec<(usize, Arc<PeerState>)> = peers
        .lock()
        .iter()
        .filter(|(peer_id, _)| {
            excluded_peers
                .iter()
                .all(|excluded_peer| **peer_id != *excluded_peer)
        })
        .map(|(peer_id, state)| (*peer_id, state.clone()))
        .collect();
    for (peer_id, state) in recipients {
        let item = transaction
            .as_ref()
            .map(|transaction| transaction_inventory(transaction, *state.wtxid_relay.lock()))
            .unwrap_or_else(|| item.clone());
        if matches!(
            item.kind,
            InventoryType::Block | InventoryType::WitnessBlock | InventoryType::CompactBlock
        ) {
            let compact_version = *state.compact_block_version.lock();
            let announce_compact = *state.compact_block_announce.lock();
            if announce_compact
                && let Some(version) = compact_version
                && let Some(compact) = compact_block_for_inventory(node, &item, version)
                    .ok()
                    .flatten()
            {
                let message = Message::CompactBlock(compact);
                let _ = send_message(node, peer_id, &state.writer, network, &message).await;
                continue;
            }
            if matches!(
                item.kind,
                InventoryType::Block | InventoryType::WitnessBlock
            ) && *state.send_headers.lock()
            {
                let header = node
                    .chain
                    .write()
                    .block(&item.hash)
                    .ok()
                    .flatten()
                    .map(|block| block.header);
                if let Some(header) = header {
                    let _ = send_message(
                        node,
                        peer_id,
                        &state.writer,
                        network,
                        &Message::Headers(vec![header]),
                    )
                    .await;
                    continue;
                }
            }
        }
        if matches!(
            item.kind,
            InventoryType::Transaction | InventoryType::WitnessTransaction
        ) {
            if !*state.relay_transactions.lock() {
                continue;
            }
            let minimum_fee = *state.fee_filter.lock();
            if let Some((fee_sat, vsize)) = transaction_fee_for_inventory(node, &item)
                && fee_rate_sat_per_kvb(fee_sat, vsize) < minimum_fee
            {
                continue;
            }
        }
        let current_transaction = if matches!(
            item.kind,
            InventoryType::Transaction | InventoryType::WitnessTransaction
        ) {
            transaction_for_inventory(node, &item)
        } else {
            None
        };
        if matches!(
            item.kind,
            InventoryType::Transaction | InventoryType::WitnessTransaction
        ) && current_transaction.is_none()
        {
            continue;
        }
        if let Some(transaction) = current_transaction {
            let mut filter = state.bloom_filter.lock();
            if let Some(filter) = filter.as_mut()
                && !filter.is_relevant_and_update(&transaction)
            {
                continue;
            }
        }
        if matches!(
            item.kind,
            InventoryType::Transaction | InventoryType::WitnessTransaction
        ) {
            let mut known = state.known_tx_inventory.lock();
            if known.contains(&item.hash) {
                continue;
            }
            known.insert(&item.hash);
        }
        let message = Message::Inv(vec![item.clone()]);
        let _ = send_message(node, peer_id, &state.writer, network, &message).await;
    }
}

fn compact_block_for_inventory(
    node: &Arc<Node>,
    item: &Inventory,
    version: u64,
) -> Result<Option<HeaderAndShortIds>> {
    if !matches!(
        item.kind,
        InventoryType::Block | InventoryType::WitnessBlock | InventoryType::CompactBlock
    ) {
        return Ok(None);
    }
    let block = node.chain.write().block(&item.hash)?;
    block
        .map(|block| {
            HeaderAndShortIds::from_block(&block, random(), version as u32, &[]).map_err(Into::into)
        })
        .transpose()
}

fn transaction_fee_for_inventory(node: &Arc<Node>, item: &Inventory) -> Option<(u64, u64)> {
    let mempool = node.mempool.read();
    match item.kind {
        InventoryType::WitnessTransaction => mempool
            .get_by_wtxid(&Wtxid::from_byte_array(item.hash.to_byte_array()))
            .map(|entry| (entry.fee_sat, entry.vsize)),
        InventoryType::Transaction => mempool
            .get(&Txid::from_byte_array(item.hash.to_byte_array()))
            .map(|entry| (entry.fee_sat, entry.vsize)),
        _ => None,
    }
}

fn transaction_inventory(transaction: &Transaction, wtxid_relay: bool) -> Inventory {
    if wtxid_relay {
        Inventory {
            kind: InventoryType::WitnessTransaction,
            hash: BlockHash::from_raw_hash(transaction.compute_wtxid().to_raw_hash()),
        }
    } else {
        Inventory {
            kind: InventoryType::Transaction,
            hash: BlockHash::from_raw_hash(transaction.compute_txid().to_raw_hash()),
        }
    }
}

fn fee_rate_sat_per_kvb(fee_sat: u64, vsize: u64) -> i64 {
    if vsize == 0 {
        return i64::MAX;
    }
    i64::try_from(fee_sat.saturating_mul(1_000).saturating_div(vsize)).unwrap_or(i64::MAX)
}

fn transaction_for_inventory(node: &Arc<Node>, item: &Inventory) -> Option<Transaction> {
    let mempool = node.mempool.read();
    match item.kind {
        InventoryType::WitnessTransaction => mempool
            .get_by_wtxid(&Wtxid::from_byte_array(item.hash.to_byte_array()))
            .map(|entry| entry.transaction.clone()),
        InventoryType::Transaction => mempool
            .get(&Txid::from_byte_array(item.hash.to_byte_array()))
            .map(|entry| entry.transaction.clone()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::Network;
    use bitcoin::bip158::FilterHeader;

    use crate::{Config, Node};

    #[test]
    fn builds_a_bounded_basic_filter_range() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            p2p_bind: "127.0.0.1:0".parse().unwrap(),
            rpc_bind: None,
            electrum_bind: None,
            rest: false,
            listen: true,
            dnsseed: true,
            blocksonly: false,
            prune: 0,
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
            zmq: crate::config::ZmqConfig::default(),
        })
        .unwrap();
        let stop_hash = node.chain.read().best_hash();
        let range = basic_filter_range(&node, 0, stop_hash, 1).unwrap().unwrap();
        assert_eq!(range.stop_hash, stop_hash);
        assert_eq!(range.filters.len(), 1);
        assert_eq!(range.previous_filter_header, FilterHeader::all_zeros());
        assert!(!range.filters[0].1.is_empty());
        assert!(
            basic_filter_range(&node, 1, stop_hash, 1)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn bloom_filter_matches_core_murmur_and_bit_order() {
        let mut filter = BloomFilter::from_message(FilterLoad {
            filter: vec![0; 3],
            hash_funcs: 5,
            tweak: 0,
            flags: BloomFlags::All,
        })
        .unwrap();
        for value in [
            "99108ad8ed9bb6274d3980bab5a85c048f0950c8",
            "b5a2c786d9ef4658287ced5914b37a1b4aa32eee",
            "b9300670b4c5366e95b2699e8b18bc75e5f729c5",
        ] {
            filter.insert(&hex::decode(value).unwrap());
        }
        assert_eq!(filter.data, hex::decode("614e9b").unwrap());
        assert!(
            !filter.contains(&hex::decode("19108ad8ed9bb6274d3980bab5a85c048f0950c8").unwrap())
        );
    }

    #[test]
    fn known_transaction_inventory_is_bounded_and_deduplicated() {
        let first = BlockHash::from_byte_array([1; 32]);
        let second = BlockHash::from_byte_array([2; 32]);
        let mut known = KnownTxInventory::new();
        assert!(!known.contains(&first));
        known.insert(&first);
        assert!(known.contains(&first));
        assert_eq!(known.inserted_in_generation, 1);
        known.insert(&first);
        assert_eq!(known.inserted_in_generation, 1);
        known.insert(&second);
        assert!(known.contains(&second));
        assert!(
            known
                .generations
                .iter()
                .all(|generation| { generation.len() == KNOWN_TX_FILTER_BITS / 8 })
        );
    }

    #[test]
    fn fee_filter_rates_are_measured_in_sat_per_kilobyte() {
        assert_eq!(fee_rate_sat_per_kvb(1_000, 250), 4_000);
        assert_eq!(fee_rate_sat_per_kvb(1, 0), i64::MAX);
    }

    #[test]
    fn compact_block_announcements_prefill_the_coinbase() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            p2p_bind: "127.0.0.1:0".parse().unwrap(),
            rpc_bind: None,
            electrum_bind: None,
            rest: false,
            listen: true,
            dnsseed: true,
            blocksonly: false,
            prune: 0,
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
            zmq: crate::config::ZmqConfig::default(),
        })
        .unwrap();
        let hash = node.chain.read().best_hash();
        let compact = compact_block_for_inventory(
            &node,
            &Inventory {
                kind: InventoryType::WitnessBlock,
                hash,
            },
            2,
        )
        .unwrap()
        .unwrap();
        assert_eq!(compact.header.block_hash(), hash);
        assert_eq!(compact.prefilled_txs.len(), 1);
        assert_eq!(compact.prefilled_txs[0].idx, 0);
        assert!(
            compact_block_for_inventory(
                &node,
                &Inventory {
                    kind: InventoryType::WitnessTransaction,
                    hash,
                },
                2,
            )
            .unwrap()
            .is_none()
        );
    }

    #[test]
    fn bloom_filter_matches_script_elements_and_updates_spends() {
        use bitcoin::Amount;
        use bitcoin::absolute::LockTime;
        use bitcoin::blockdata::script::ScriptBuf;
        use bitcoin::blockdata::transaction::{OutPoint, TxIn, TxOut, Version};
        use bitcoin::blockdata::witness::Witness;

        let transaction = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::null(),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(1),
                script_pubkey: ScriptBuf::from_bytes(vec![1, 0x42]),
            }],
        };
        let mut filter = BloomFilter::from_message(FilterLoad {
            filter: vec![0; 32],
            hash_funcs: 5,
            tweak: 0,
            flags: BloomFlags::All,
        })
        .unwrap();
        filter.insert(&[0x42]);
        assert!(filter.is_relevant_and_update(&transaction));

        let spending = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(transaction.compute_txid(), 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(1),
                script_pubkey: ScriptBuf::new(),
            }],
        };
        assert!(filter.is_relevant_and_update(&spending));
    }

    #[test]
    fn peer_counters_track_wire_traffic_and_pings() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            p2p_bind: "127.0.0.1:0".parse().unwrap(),
            rpc_bind: None,
            electrum_bind: None,
            rest: false,
            listen: true,
            dnsseed: true,
            blocksonly: false,
            prune: 0,
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
            zmq: crate::config::ZmqConfig::default(),
        })
        .unwrap();
        let (sender, mut receiver) = mpsc::unbounded_channel();
        node.register_peer(7, "127.0.0.1:18444".parse().unwrap(), false, sender);
        node.record_bytes_sent(7, 42);
        node.record_bytes_received(7, 19);
        node.update_peer_version(7, 70016, 0, "/peer/", 0, false);
        node.update_peer_fee_filter(7, 4_000);
        assert_eq!(node.total_bytes_sent(), 42);
        assert_eq!(node.total_bytes_received(), 19);
        let peer = node.peer_infos().pop().expect("registered peer");
        assert_eq!(peer.bytes_sent, 42);
        assert_eq!(peer.bytes_received, 19);
        assert!(!peer.relay_transactions);
        assert_eq!(peer.min_fee_filter, 4_000);

        node.ping_peers();
        let PeerCommand::Ping(nonce) = receiver.try_recv().unwrap() else {
            panic!("expected a ping command");
        };
        assert!(node.ping_timed_out(7, Duration::ZERO));
        node.ping_peers();
        assert!(receiver.try_recv().is_err());
        node.record_pong(7, nonce);
        assert!(node.peer_infos()[0].ping_time.is_some());
        assert!(node.peer_infos()[0].min_ping.is_some());
        node.unregister_peer(7);
        assert_eq!(
            node.known_addresses()
                .into_iter()
                .find(|known| known.address == "127.0.0.1:18444".parse().unwrap())
                .expect("disconnected peer remains in address table")
                .id,
            0
        );
    }

    #[test]
    fn address_messages_round_trip_into_the_known_address_table() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            p2p_bind: "127.0.0.1:0".parse().unwrap(),
            rpc_bind: None,
            electrum_bind: None,
            rest: false,
            listen: true,
            dnsseed: true,
            blocksonly: false,
            prune: 0,
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
            zmq: crate::config::ZmqConfig::default(),
        })
        .unwrap();
        let legacy = wire::NetworkAddress {
            time: 123,
            services: wire::NODE_NETWORK,
            address: socket_address_bytes("192.0.2.10:18444".parse().unwrap()),
            port: 18444,
        };
        let legacy_socket = socket_address_from_legacy(&legacy).unwrap();
        node.remember_address(legacy_socket, legacy.services, u64::from(legacy.time));
        let v2 = network_address_v2(
            "[2001:db8::10]:18444".parse().unwrap(),
            456,
            wire::NODE_NETWORK | wire::NODE_WITNESS,
        );
        let v2_socket = socket_address_from_v2(&v2).unwrap();
        node.remember_address(v2_socket, v2.services, u64::from(v2.time));

        let addresses = node.known_addresses();
        assert!(addresses.iter().any(|peer| peer.address == legacy_socket));
        assert!(addresses.iter().any(|peer| peer.address == v2_socket));
        assert_eq!(addresses.iter().filter(|peer| peer.id == 0).count(), 2);
    }

    #[test]
    fn discovery_candidates_skip_connected_added_and_in_flight_addresses() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            p2p_bind: "127.0.0.1:0".parse().unwrap(),
            rpc_bind: None,
            electrum_bind: None,
            rest: false,
            listen: true,
            dnsseed: true,
            blocksonly: false,
            prune: 0,
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
            max_peers: 4,
            peer_bloom_filters: false,
            zmq: crate::config::ZmqConfig::default(),
        })
        .unwrap();
        let added = "192.0.2.10:18444".parse().unwrap();
        let connected = "192.0.2.11:18444".parse().unwrap();
        let in_flight = "192.0.2.12:18444".parse().unwrap();
        let eligible = "192.0.2.13:18444".parse().unwrap();
        for address in [added, connected, in_flight, eligible] {
            assert!(node.add_peer_address(address, false));
        }
        assert!(node.add_node(added));
        let (sender, _receiver) = mpsc::unbounded_channel();
        node.register_peer(7, connected, false, sender);
        let attempts = Arc::new(parking_lot::Mutex::new(HashSet::from([in_flight])));

        assert_eq!(
            select_discovery_addresses(&node, 4, &attempts),
            vec![eligible]
        );
    }

    #[tokio::test]
    async fn bip324_transport_round_trips_encrypted_application_messages() {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let address = listener.local_addr().unwrap();
        let client = TcpStream::connect(address);
        let server = listener.accept();
        let (client, server) = tokio::join!(client, server);
        let client = client.unwrap();
        let (server, _) = server.unwrap();

        let (client_result, server_result) = tokio::join!(
            establish_v2(client, Network::Regtest, Role::Initiator),
            establish_v2(server, Network::Regtest, Role::Responder),
        );
        let (client_reader, client_writer, _) = client_result.unwrap();
        let (server_reader, server_writer, _) = server_result.unwrap();
        let mut client_reader = match client_reader {
            PeerReader::V2(reader) => reader,
            PeerReader::V1(_) => panic!("expected encrypted client reader"),
        };
        let mut client_writer = match client_writer {
            PeerWriterKind::V2(writer) => writer,
            PeerWriterKind::V1(_) => panic!("expected encrypted client writer"),
        };
        let mut server_reader = match server_reader {
            PeerReader::V2(reader) => reader,
            PeerReader::V1(_) => panic!("expected encrypted server reader"),
        };
        let mut server_writer = match server_writer {
            PeerWriterKind::V2(writer) => writer,
            PeerWriterKind::V1(_) => panic!("expected encrypted server writer"),
        };

        let client_message = Message::Ping(123);
        client_writer
            .write(&Payload::genuine(
                wire::encode_v2_message(&client_message).unwrap(),
            ))
            .await
            .unwrap();
        let payload = server_reader.read().await.unwrap();
        assert_eq!(
            wire::decode_v2_message(payload.contents()).unwrap(),
            client_message
        );

        let server_message = Message::Pong(456);
        server_writer
            .write(&Payload::genuine(
                wire::encode_v2_message(&server_message).unwrap(),
            ))
            .await
            .unwrap();
        let payload = client_reader.read().await.unwrap();
        assert_eq!(
            wire::decode_v2_message(payload.contents()).unwrap(),
            server_message
        );
    }

    #[tokio::test]
    async fn tx_reconciliation_extensions_precede_verack_and_use_core_ordering() {
        let directory = tempfile::tempdir().unwrap();
        let zmq = crate::config::ZmqConfig {
            tx_reconciliation: true,
            ..Default::default()
        };
        let node = Node::open(Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            p2p_bind: "127.0.0.1:0".parse().unwrap(),
            rpc_bind: None,
            electrum_bind: None,
            rest: false,
            listen: true,
            dnsseed: true,
            blocksonly: false,
            prune: 0,
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
            zmq,
        })
        .unwrap();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let address = listener.local_addr().unwrap();
        let client = TcpStream::connect(address);
        let server = listener.accept();
        let (client, server) = tokio::join!(client, server);
        let client = client.unwrap();
        let (server, _) = server.unwrap();
        let (_, client_writer) = client.into_split();
        let (mut server_reader, _) = server.into_split();
        let writer = Arc::new(Mutex::new(PeerWriterKind::V1(client_writer)));
        let peer_state = PeerState {
            writer: writer.clone(),
            bloom_filter: parking_lot::Mutex::new(None),
            known_tx_inventory: parking_lot::Mutex::new(KnownTxInventory::new()),
            fee_filter: parking_lot::Mutex::new(0),
            relay_transactions: parking_lot::Mutex::new(true),
            wtxid_relay: parking_lot::Mutex::new(false),
            send_headers: parking_lot::Mutex::new(false),
            compact_block_version: parking_lot::Mutex::new(None),
            compact_block_announce: parking_lot::Mutex::new(false),
            tx_reconciliation_salt: parking_lot::Mutex::new(None),
            tx_reconciliation_registered: parking_lot::Mutex::new(false),
        };
        let mut sent = false;
        send_peer_extensions(
            &node,
            1,
            &writer,
            &peer_state,
            Network::Regtest,
            &mut sent,
            WTXID_RELAY_VERSION,
        )
        .await
        .unwrap();

        assert_eq!(
            wire::read_message(&mut server_reader, Network::Regtest)
                .await
                .unwrap(),
            Message::SendHeaders
        );
        assert_eq!(
            wire::read_message(&mut server_reader, Network::Regtest)
                .await
                .unwrap(),
            Message::WtxidRelay
        );
        assert_eq!(
            wire::read_message(&mut server_reader, Network::Regtest)
                .await
                .unwrap(),
            Message::SendAddrV2
        );
        let Message::SendTxRcncl(reconciliation) =
            wire::read_message(&mut server_reader, Network::Regtest)
                .await
                .unwrap()
        else {
            panic!("expected sendtxrcncl extension");
        };
        assert_eq!(reconciliation.version, TX_RECONCILIATION_VERSION);
        assert_eq!(
            *peer_state.tx_reconciliation_salt.lock(),
            Some(reconciliation.salt)
        );
        assert_eq!(
            wire::read_message(&mut server_reader, Network::Regtest)
                .await
                .unwrap(),
            Message::SendCmpct {
                announce: false,
                version: 2,
            }
        );
        assert_eq!(
            wire::read_message(&mut server_reader, Network::Regtest)
                .await
                .unwrap(),
            Message::FeeFilter(1_000)
        );
        send_message(&node, 1, &writer, Network::Regtest, &Message::Verack)
            .await
            .unwrap();
        assert_eq!(
            wire::read_message(&mut server_reader, Network::Regtest)
                .await
                .unwrap(),
            Message::Verack
        );
        assert!(sent);
    }
}
