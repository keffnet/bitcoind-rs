//! Bitcoin peer networking and block/transaction relay.

use std::collections::HashMap;
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};
use std::time::Duration;

use anyhow::{Context, Result};
use bitcoin::hashes::Hash;
use bitcoin::{BlockHash, Network, Txid, Wtxid};
use rand::random;
use tokio::net::{TcpListener, TcpStream, tcp::OwnedReadHalf};
use tokio::sync::{Mutex, Semaphore};
use tracing::{debug, info, warn};

use crate::Node;
use crate::wire::{self, GetHeadersMessage, Inventory, InventoryType, Message, VersionMessage};

type PeerWriter = Arc<Mutex<tokio::net::tcp::OwnedWriteHalf>>;
type PeerRegistry = Arc<parking_lot::Mutex<HashMap<usize, PeerWriter>>>;

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
            let node = self.node.clone();
            let slots = slots.clone();
            let peers = peers.clone();
            let peer_id = next_peer_id.fetch_add(1, Ordering::Relaxed);
            tokio::spawn(async move {
                let Ok(_permit) = slots.acquire_owned().await else {
                    return;
                };
                loop {
                    match TcpStream::connect(address).await {
                        Ok(stream) => {
                            info!(%address, "connected to configured peer");
                            if let Err(error) = serve_peer(
                                node.clone(),
                                stream,
                                address,
                                true,
                                peers.clone(),
                                peer_id,
                            )
                            .await
                            {
                                debug!(%address, %error, "outbound peer ended");
                            }
                        }
                        Err(error) => {
                            warn!(%address, %error, "unable to connect to configured peer")
                        }
                    }
                    tokio::time::sleep(Duration::from_secs(5)).await;
                }
            });
        }

        loop {
            let (stream, address) = listener.accept().await?;
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
    node.register_peer(peer_id, address, !outbound);
    let (mut reader, writer_half) = stream.into_split();
    let writer = Arc::new(Mutex::new(writer_half));
    peers.lock().insert(peer_id, writer.clone());
    let result = serve_peer_loop(&node, &mut reader, &writer, outbound, &peers, peer_id).await;
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
) -> Result<()> {
    let height = node.chain.read().height() as i32;
    send_message(
        writer,
        node.config.network,
        &Message::Version(VersionMessage::new(height, random())),
    )
    .await?;
    let mut version_received = false;
    let mut verack_received = false;
    let mut verack_sent = false;
    let mut extensions_sent = false;
    loop {
        let message = wire::read_message(reader, node.config.network).await?;
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
                    send_message(writer, node.config.network, &Message::Verack).await?;
                    verack_sent = true;
                }
                send_peer_extensions(writer, node.config.network, &mut extensions_sent).await?;
                if outbound {
                    debug!(user_agent = %version.user_agent, height = version.start_height, "completed outbound version exchange");
                }
            }
            Message::Verack => {
                verack_received = true;
                if !version_received {
                    continue;
                }
                send_peer_extensions(writer, node.config.network, &mut extensions_sent).await?;
                request_headers(node, writer).await?;
            }
            Message::Ping(nonce) => {
                send_message(writer, node.config.network, &Message::Pong(nonce)).await?;
            }
            Message::Pong(_) => {}
            Message::GetHeaders(request) => {
                let headers = node
                    .chain
                    .read()
                    .headers_after_locator(&request.locator_hashes, request.stop_hash);
                send_message(writer, node.config.network, &Message::Headers(headers)).await?;
            }
            Message::GetBlocks(request) => {
                let hashes = node
                    .chain
                    .read()
                    .headers_after_locator(&request.locator_hashes, request.stop_hash)
                    .into_iter()
                    .take(500)
                    .map(|header| Inventory {
                        kind: InventoryType::WitnessBlock,
                        hash: header.block_hash(),
                    })
                    .collect::<Vec<_>>();
                send_message(writer, node.config.network, &Message::Inv(hashes)).await?;
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
                    send_message(writer, node.config.network, &Message::GetData(requests)).await?;
                } else {
                    request_headers(node, writer).await?;
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
                    send_message(writer, node.config.network, &Message::GetData(requests)).await?;
                }
            }
            Message::GetData(items) => {
                let mut missing = Vec::new();
                for item in items {
                    match item.kind {
                        InventoryType::Block | InventoryType::WitnessBlock => {
                            let block = node.chain.write().block(&item.hash)?;
                            if let Some(block) = block {
                                send_message(writer, node.config.network, &Message::Block(block))
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
                    send_message(writer, node.config.network, &Message::NotFound(missing)).await?;
                }
            }
            Message::Block(block) => {
                let hash = block.block_hash();
                match node.connect_block(block) {
                    Ok(tip) => {
                        info!(%hash, height = tip.height, "accepted peer block");
                        broadcast_inventory(
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
                request_headers(node, writer).await?;
            }
            Message::Transaction(transaction) => {
                let txid = transaction.compute_txid();
                let wtxid = transaction.compute_wtxid();
                let accepted = node.accept_transaction(transaction).is_ok();
                if accepted {
                    debug!(%txid, "accepted peer transaction");
                    broadcast_inventory(
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
            Message::Addr(_)
            | Message::SendHeaders
            | Message::WtxidRelay
            | Message::FeeFilter(_)
            | Message::SendCmpct { .. }
            | Message::NotFound(_)
            | Message::Unknown { .. } => {}
            Message::GetAddr => {
                let addresses = node
                    .peer_infos()
                    .into_iter()
                    .take(1_000)
                    .map(|peer| wire::NetworkAddress {
                        time: u32::try_from(peer.connected_at).unwrap_or(u32::MAX),
                        services: wire::NODE_NETWORK | wire::NODE_WITNESS,
                        address: socket_address_bytes(peer.address),
                        port: peer.address.port(),
                    })
                    .collect::<Vec<_>>();
                send_message(writer, node.config.network, &Message::Addr(addresses)).await?;
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
                send_message(writer, node.config.network, &Message::Inv(inventory)).await?;
            }
        }
        if version_received && verack_received && !verack_sent {
            send_message(writer, node.config.network, &Message::Verack).await?;
            verack_sent = true;
        }
    }
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

async fn send_peer_extensions(
    writer: &PeerWriter,
    network: Network,
    sent: &mut bool,
) -> Result<()> {
    if *sent {
        return Ok(());
    }
    send_message(writer, network, &Message::SendHeaders).await?;
    send_message(writer, network, &Message::WtxidRelay).await?;
    send_message(writer, network, &Message::FeeFilter(1_000)).await?;
    *sent = true;
    Ok(())
}

async fn request_headers(node: &Arc<Node>, writer: &PeerWriter) -> Result<()> {
    let locator = vec![node.chain.read().best_hash()];
    send_message(
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

async fn send_message(writer: &PeerWriter, network: Network, message: &Message) -> Result<()> {
    let mut writer = writer.lock().await;
    wire::write_message(&mut *writer, network, message).await
}

async fn broadcast_inventory(
    peers: &PeerRegistry,
    excluded_peer: usize,
    network: Network,
    item: Inventory,
) {
    let recipients: Vec<PeerWriter> = peers
        .lock()
        .iter()
        .filter(|(peer_id, _)| **peer_id != excluded_peer)
        .map(|(_, writer)| writer.clone())
        .collect();
    let message = Message::Inv(vec![item]);
    for writer in recipients {
        let _ = send_message(&writer, network, &message).await;
    }
}
