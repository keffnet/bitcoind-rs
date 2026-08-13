//! Bitcoin peer networking and block/transaction relay.

use std::collections::HashMap;
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};
use std::time::Duration;

use anyhow::{Context, Result};
use bitcoin::bip152::{BlockTransactions, BlockTransactionsRequest, HeaderAndShortIds, ShortId};
use bitcoin::bip158::{FilterHash, FilterHeader};
use bitcoin::hashes::Hash;
use bitcoin::p2p::message_filter::{CFCheckpt, CFHeaders, CFilter};
use bitcoin::{Block, BlockHash, Network, Transaction, Txid, Wtxid};
use rand::random;
use tokio::net::{TcpListener, TcpStream, tcp::OwnedReadHalf};
use tokio::sync::{Mutex, Semaphore, mpsc};
use tracing::{debug, info, warn};

use crate::Node;
use crate::wire::{self, GetHeadersMessage, Inventory, InventoryType, Message, VersionMessage};

type PeerWriter = Arc<Mutex<tokio::net::tcp::OwnedWriteHalf>>;
type PeerRegistry = Arc<parking_lot::Mutex<HashMap<usize, PeerWriter>>>;

#[derive(Debug)]
pub(crate) enum PeerCommand {
    Disconnect,
    RequestBlock(BlockHash),
    Ping(u64),
}

struct PendingCompactBlock {
    compact: HeaderAndShortIds,
    transactions: Vec<Option<Transaction>>,
    requested_indexes: Vec<u64>,
}

struct BasicFilterRange {
    stop_hash: BlockHash,
    previous_filter_header: FilterHeader,
    filters: Vec<(BlockHash, Vec<u8>, FilterHeader)>,
}

pub struct PeerManager {
    node: Arc<Node>,
}

impl PeerManager {
    pub fn new(node: Arc<Node>) -> Self {
        Self { node }
    }

    pub async fn run(self) -> Result<()> {
        let listener = TcpListener::bind(self.node.config.p2p_bind)
            .await
            .with_context(|| format!("binding P2P listener {}", self.node.config.p2p_bind))?;
        let slots = Arc::new(Semaphore::new(self.node.config.max_peers));
        let peers: PeerRegistry = Arc::new(parking_lot::Mutex::new(HashMap::new()));
        let next_peer_id = Arc::new(AtomicUsize::new(1));
        let (add_node_sender, mut add_node_receiver) = mpsc::unbounded_channel();
        self.node.set_peer_manager_sender(add_node_sender);
        let mut mempool_events = self.node.subscribe_mempool();
        let relay_peers = peers.clone();
        let relay_node = self.node.clone();
        let relay_network = self.node.config.network;
        tokio::spawn(async move {
            loop {
                let txid = match mempool_events.recv().await {
                    Ok(txid) => txid,
                    Err(tokio::sync::broadcast::error::RecvError::Lagged(_)) => continue,
                    Err(tokio::sync::broadcast::error::RecvError::Closed) => break,
                };
                let hash = relay_node
                    .mempool
                    .read()
                    .get(&txid)
                    .map(|entry| entry.transaction.compute_wtxid())
                    .unwrap_or_else(|| Wtxid::from_raw_hash(txid.to_raw_hash()));
                broadcast_inventory(
                    &relay_node,
                    &relay_peers,
                    0,
                    relay_network,
                    Inventory {
                        kind: InventoryType::WitnessTransaction,
                        hash: BlockHash::from_raw_hash(hash.to_raw_hash()),
                    },
                )
                .await;
            }
        });
        let seed_nodes = if self.node.config.seed_nodes.is_empty() {
            discover_dns_seeds(self.node.config.network).await
        } else {
            self.node.config.seed_nodes.clone()
        };
        for address in seed_nodes {
            self.node.ensure_node_added(address);
            spawn_outbound_loop(
                self.node.clone(),
                address,
                slots.clone(),
                peers.clone(),
                next_peer_id.clone(),
            );
        }
        let dynamic_node = self.node.clone();
        let dynamic_slots = slots.clone();
        let dynamic_peers = peers.clone();
        let dynamic_ids = next_peer_id.clone();
        tokio::spawn(async move {
            while let Some(address) = add_node_receiver.recv().await {
                spawn_outbound_loop(
                    dynamic_node.clone(),
                    address,
                    dynamic_slots.clone(),
                    dynamic_peers.clone(),
                    dynamic_ids.clone(),
                );
            }
        });

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
                if let Err(error) = serve_peer(node, stream, address, false, peers, peer_id).await {
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
    slots: Arc<Semaphore>,
    peers: PeerRegistry,
    next_peer_id: Arc<AtomicUsize>,
) {
    let peer_id = next_peer_id.fetch_add(1, Ordering::Relaxed);
    tokio::spawn(async move {
        let Ok(_permit) = slots.acquire_owned().await else {
            return;
        };
        loop {
            if !node.is_node_added(address) {
                return;
            }
            if !node.network_active() || node.is_banned(address.ip()) {
                tokio::time::sleep(Duration::from_secs(1)).await;
                continue;
            }
            match TcpStream::connect(address).await {
                Ok(stream) => {
                    info!(%address, "connected to configured peer");
                    if let Err(error) =
                        serve_peer(node.clone(), stream, address, true, peers.clone(), peer_id)
                            .await
                    {
                        debug!(%address, %error, "outbound peer ended");
                    }
                }
                Err(error) => warn!(%address, %error, "unable to connect to configured peer"),
            }
            tokio::time::sleep(Duration::from_secs(5)).await;
        }
    });
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

async fn serve_peer(
    node: Arc<Node>,
    stream: TcpStream,
    address: std::net::SocketAddr,
    outbound: bool,
    peers: PeerRegistry,
    peer_id: usize,
) -> Result<()> {
    let _peer_count = PeerCountGuard::new(&node);
    stream.set_nodelay(true)?;
    let (commands, command_receiver) = mpsc::unbounded_channel();
    let local_address = stream.local_addr().ok();
    node.register_peer_with_local(peer_id, address, !outbound, commands, local_address);
    let (mut reader, writer_half) = stream.into_split();
    let writer = Arc::new(Mutex::new(writer_half));
    peers.lock().insert(peer_id, writer.clone());
    let result = serve_peer_loop(
        &node,
        &mut reader,
        &writer,
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
    reader: &mut OwnedReadHalf,
    writer: &PeerWriter,
    outbound: bool,
    peers: &PeerRegistry,
    peer_id: usize,
    mut commands: mpsc::UnboundedReceiver<PeerCommand>,
) -> Result<()> {
    let height = node.chain.read().height() as i32;
    send_message(
        node,
        peer_id,
        writer,
        node.config.network,
        &Message::Version(VersionMessage::new(height, random())),
    )
    .await?;
    let mut version_received = false;
    let mut verack_received = false;
    let mut verack_sent = false;
    let mut extensions_sent = false;
    let mut addrv2_received = false;
    let mut compact_block_version = 2u64;
    let mut pending_compact = None;
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
                }
            }
            message = wire::read_message_with_size(reader, node.config.network) => {
                let (message, bytes) = message?;
                node.record_bytes_received(peer_id, bytes);
                message
            },
        };
        match message {
            Message::Version(version) => {
                if version_received {
                    anyhow::bail!("duplicate version message");
                }
                version_received = true;
                if version.version < 70001 {
                    anyhow::bail!("peer protocol version is too old");
                }
                node.update_peer_version(
                    peer_id,
                    version.version,
                    version.services,
                    &version.user_agent,
                    version.start_height,
                    version.relay,
                );
                if !verack_sent {
                    send_message(node, peer_id, writer, node.config.network, &Message::Verack)
                        .await?;
                    verack_sent = true;
                }
                send_peer_extensions(
                    node,
                    peer_id,
                    writer,
                    node.config.network,
                    &mut extensions_sent,
                )
                .await?;
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
                    node.config.network,
                    &mut extensions_sent,
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
                addrv2_received = true;
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
                let requests = {
                    let chain = node.chain.read();
                    let mempool = node.mempool.read();
                    items
                        .into_iter()
                        .filter(|item| match item.kind {
                            InventoryType::Block | InventoryType::WitnessBlock => {
                                !chain.store.contains(&item.hash)
                            }
                            InventoryType::Transaction | InventoryType::WitnessTransaction => {
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
                        InventoryType::Transaction | InventoryType::WitnessTransaction => {
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
                if request.filter_type != 0 {
                    continue;
                }
                let Some(range) = basic_filter_range(node, 0, request.stop_hash, usize::MAX)?
                else {
                    continue;
                };
                let filter_headers = range
                    .filters
                    .into_iter()
                    .enumerate()
                    .filter_map(|(height, (_, _, header))| {
                        ((height + 1) % 1_000 == 0).then_some(header)
                    })
                    .collect();
                send_message(
                    node,
                    peer_id,
                    writer,
                    node.config.network,
                    &Message::CFCheckpt(CFCheckpt {
                        filter_type: 0,
                        stop_hash: range.stop_hash,
                        filter_headers,
                    }),
                )
                .await?;
            }
            Message::Transaction(transaction) => {
                let txid = transaction.compute_txid();
                let wtxid = transaction.compute_wtxid();
                let accepted = node
                    .accept_peer_transaction_from(peer_id, transaction)
                    .is_ok();
                if accepted {
                    debug!(%txid, "accepted peer transaction");
                    broadcast_inventory(
                        node,
                        peers,
                        peer_id,
                        node.config.network,
                        Inventory {
                            kind: InventoryType::WitnessTransaction,
                            hash: BlockHash::from_raw_hash(wtxid.to_raw_hash()),
                        },
                    )
                    .await;
                } else {
                    debug!(%txid, "rejected peer transaction");
                }
            }
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
            Message::CFilter(_)
            | Message::CFHeaders(_)
            | Message::CFCheckpt(_)
            | Message::SendHeaders
            | Message::WtxidRelay
            | Message::FeeFilter(_)
            | Message::NotFound(_)
            | Message::Unknown { .. } => {}
            Message::SendCmpct {
                announce: _,
                version,
            } => {
                if version == 1 || version == 2 {
                    compact_block_version = version;
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
                        .map(|peer| network_address_v2(peer.address, peer.connected_at))
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
                            services: wire::NODE_NETWORK | wire::NODE_WITNESS,
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
                let inventory = {
                    let mempool = node.mempool.read();
                    mempool
                        .transaction_order()
                        .into_iter()
                        .filter_map(|txid| {
                            mempool.get(&txid).map(|entry| Inventory {
                                kind: InventoryType::WitnessTransaction,
                                hash: BlockHash::from_raw_hash(
                                    entry.transaction.compute_wtxid().to_raw_hash(),
                                ),
                            })
                        })
                        .take(50_000)
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
    let end_height = start_height
        .saturating_add(u32::try_from(limit.saturating_sub(1)).unwrap_or(u32::MAX))
        .min(stop_height);
    let end_hash = chain
        .block_hash(end_height)
        .ok_or_else(|| anyhow::anyhow!("compact filter height is out of range"))?;
    let all_filters = chain
        .basic_filter_chain(&end_hash)?
        .ok_or_else(|| anyhow::anyhow!("compact filters are not available"))?;
    let previous_filter_header = if start_height == 0 {
        FilterHeader::all_zeros()
    } else {
        all_filters
            .get(start_height as usize - 1)
            .map(|(_, _, header)| *header)
            .ok_or_else(|| anyhow::anyhow!("compact filter predecessor is unavailable"))?
    };
    let filters = all_filters
        .into_iter()
        .skip(start_height as usize)
        .take(limit)
        .map(|(hash, filter, header)| (hash, filter.content, header))
        .collect();
    Ok(Some(BasicFilterRange {
        stop_hash: end_hash,
        previous_filter_header,
        filters,
    }))
}

async fn handle_received_block(
    node: &Arc<Node>,
    peers: &PeerRegistry,
    peer_id: usize,
    block: Block,
) {
    let hash = block.block_hash();
    match node.connect_block(block) {
        Ok(tip) => {
            info!(%hash, height = tip.height, "accepted peer block");
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

fn network_address_v2(address: std::net::SocketAddr, connected_at: u64) -> wire::NetworkAddressV2 {
    let port = address.port();
    let (network, address) = match address.ip() {
        std::net::IpAddr::V4(ip) => (1, ip.octets().to_vec()),
        std::net::IpAddr::V6(ip) => (2, ip.octets().to_vec()),
    };
    wire::NetworkAddressV2 {
        time: u32::try_from(connected_at).unwrap_or(u32::MAX),
        services: wire::NODE_NETWORK | wire::NODE_WITNESS,
        network,
        address,
        port,
    }
}

async fn send_peer_extensions(
    node: &Arc<Node>,
    peer_id: usize,
    writer: &PeerWriter,
    network: Network,
    sent: &mut bool,
) -> Result<()> {
    if *sent {
        return Ok(());
    }
    send_message(node, peer_id, writer, network, &Message::SendHeaders).await?;
    send_message(node, peer_id, writer, network, &Message::SendAddrV2).await?;
    send_message(node, peer_id, writer, network, &Message::WtxidRelay).await?;
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
    send_message(node, peer_id, writer, network, &Message::FeeFilter(1_000)).await?;
    *sent = true;
    Ok(())
}

async fn request_headers(node: &Arc<Node>, peer_id: usize, writer: &PeerWriter) -> Result<()> {
    let locator = vec![node.chain.read().best_hash()];
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
    let bytes = wire::write_message_with_size(&mut *writer, network, message).await?;
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
    let recipients: Vec<(usize, PeerWriter)> = peers
        .lock()
        .iter()
        .filter(|(peer_id, _)| **peer_id != excluded_peer)
        .map(|(peer_id, writer)| (*peer_id, writer.clone()))
        .collect();
    let message = Message::Inv(vec![item]);
    for (peer_id, writer) in recipients {
        let _ = send_message(node, peer_id, &writer, network, &message).await;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::Network;

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
            seed_nodes: Vec::new(),
            signet_challenge: None,
            max_peers: 1,
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
    fn peer_counters_track_wire_traffic_and_pings() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            p2p_bind: "127.0.0.1:0".parse().unwrap(),
            rpc_bind: None,
            electrum_bind: None,
            rest: false,
            seed_nodes: Vec::new(),
            signet_challenge: None,
            max_peers: 1,
        })
        .unwrap();
        let (sender, mut receiver) = mpsc::unbounded_channel();
        node.register_peer(7, "127.0.0.1:18444".parse().unwrap(), false, sender);
        node.record_bytes_sent(7, 42);
        node.record_bytes_received(7, 19);
        assert_eq!(node.total_bytes_sent(), 42);
        assert_eq!(node.total_bytes_received(), 19);
        let peer = node.peer_infos().pop().expect("registered peer");
        assert_eq!(peer.bytes_sent, 42);
        assert_eq!(peer.bytes_received, 19);

        node.ping_peers();
        let PeerCommand::Ping(nonce) = receiver.try_recv().unwrap() else {
            panic!("expected a ping command");
        };
        node.record_pong(7, nonce);
        assert!(node.peer_infos()[0].ping_time.is_some());
        assert!(node.peer_infos()[0].min_ping.is_some());
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
            seed_nodes: Vec::new(),
            signet_challenge: None,
            max_peers: 1,
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
        let v2 = network_address_v2("[2001:db8::10]:18444".parse().unwrap(), 456);
        let v2_socket = socket_address_from_v2(&v2).unwrap();
        node.remember_address(v2_socket, v2.services, u64::from(v2.time));

        let addresses = node.known_addresses();
        assert!(addresses.iter().any(|peer| peer.address == legacy_socket));
        assert!(addresses.iter().any(|peer| peer.address == v2_socket));
        assert_eq!(addresses.iter().filter(|peer| peer.id == 0).count(), 2);
    }
}
