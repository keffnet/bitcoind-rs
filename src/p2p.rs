//! Bitcoin peer networking and block/transaction relay.

use std::collections::HashMap;
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};
use std::time::Duration;

use anyhow::{Context, Result};
use bitcoin::hashes::Hash;
use bitcoin::{BlockHash, Network, Txid};
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
                            if let Err(error) =
                                serve_peer(node.clone(), stream, true, peers.clone(), peer_id).await
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
                if let Err(error) = serve_peer(node, stream, false, peers, peer_id).await {
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
    outbound: bool,
    peers: PeerRegistry,
    peer_id: usize,
) -> Result<()> {
    stream.set_nodelay(true)?;
    let (mut reader, writer_half) = stream.into_split();
    let writer = Arc::new(Mutex::new(writer_half));
    peers.lock().insert(peer_id, writer.clone());
    let result = serve_peer_loop(&node, &mut reader, &writer, outbound, &peers, peer_id).await;
    peers.lock().remove(&peer_id);
    result
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
                if !verack_sent {
                    send_message(writer, node.config.network, &Message::Verack).await?;
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
                request_headers(node, writer).await?;
            }
            Message::Ping(nonce) => {
                send_message(writer, node.config.network, &Message::Pong(nonce)).await?;
            }
            Message::Pong(_) => {}
            Message::GetHeaders(request) | Message::GetBlocks(request) => {
                let headers = node
                    .chain
                    .read()
                    .headers_after_locator(&request.locator_hashes, request.stop_hash);
                send_message(writer, node.config.network, &Message::Headers(headers)).await?;
            }
            Message::Headers(headers) => {
                if headers.is_empty() {
                    continue;
                }
                let mut requests = Vec::new();
                {
                    let chain = node.chain.read();
                    for header in headers {
                        let hash = header.block_hash();
                        if !chain.store.contains(&hash) {
                            requests.push(Inventory {
                                kind: InventoryType::Block,
                                hash,
                            });
                        }
                    }
                }
                if !requests.is_empty() {
                    send_message(writer, node.config.network, &Message::GetData(requests)).await?;
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
                                mempool
                                    .get(&Txid::from_byte_array(item.hash.to_byte_array()))
                                    .is_none()
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
                            let txid = Txid::from_byte_array(item.hash.to_byte_array());
                            let transaction = node
                                .mempool
                                .read()
                                .get(&txid)
                                .map(|entry| entry.transaction.clone());
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
            }
            Message::Transaction(transaction) => {
                let txid = transaction.compute_txid();
                let accepted = {
                    let chain = node.chain.read();
                    node.mempool.write().accept(transaction, &chain).is_ok()
                };
                if accepted {
                    debug!(%txid, "accepted peer transaction");
                    broadcast_inventory(
                        peers,
                        peer_id,
                        node.config.network,
                        Inventory {
                            kind: InventoryType::WitnessTransaction,
                            hash: BlockHash::from_raw_hash(txid.to_raw_hash()),
                        },
                    )
                    .await;
                } else {
                    debug!(%txid, "rejected peer transaction");
                }
            }
            Message::Addr(_)
            | Message::GetAddr
            | Message::SendHeaders
            | Message::WtxidRelay
            | Message::Mempool
            | Message::FeeFilter(_)
            | Message::SendCmpct { .. }
            | Message::NotFound(_)
            | Message::Unknown { .. } => {}
        }
        if version_received && verack_received && !verack_sent {
            send_message(writer, node.config.network, &Message::Verack).await?;
            verack_sent = true;
        }
    }
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
