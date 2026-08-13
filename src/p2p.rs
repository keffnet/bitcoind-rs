//! Bitcoin peer networking and block/transaction relay.

use std::sync::Arc;

use anyhow::{Context, Result};
use bitcoin::hashes::Hash;
use bitcoin::{BlockHash, Network, Txid};
use rand::random;
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::Semaphore;
use tracing::{debug, info, warn};

use crate::Node;
use crate::wire::{self, GetHeadersMessage, Inventory, InventoryType, Message, VersionMessage};

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
        let seed_nodes = if self.node.config.seed_nodes.is_empty() {
            discover_dns_seeds(self.node.config.network).await
        } else {
            self.node.config.seed_nodes.clone()
        };
        for address in seed_nodes {
            let node = self.node.clone();
            let slots = slots.clone();
            tokio::spawn(async move {
                let Ok(permit) = slots.acquire_owned().await else {
                    return;
                };
                match TcpStream::connect(address).await {
                    Ok(stream) => {
                        info!(%address, "connected to configured peer");
                        if let Err(error) = serve_peer(node, stream, true).await {
                            debug!(%address, %error, "outbound peer ended");
                        }
                    }
                    Err(error) => warn!(%address, %error, "unable to connect to configured peer"),
                }
                drop(permit);
            });
        }

        loop {
            let (stream, address) = listener.accept().await?;
            let node = self.node.clone();
            let slots = slots.clone();
            tokio::spawn(async move {
                let Ok(permit) = slots.try_acquire_owned() else {
                    debug!(%address, "rejecting peer because peer limit is reached");
                    return;
                };
                if let Err(error) = serve_peer(node, stream, false).await {
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
        Network::Testnet | Network::Testnet4 => 18333,
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

async fn serve_peer(node: Arc<Node>, mut stream: TcpStream, outbound: bool) -> Result<()> {
    stream.set_nodelay(true)?;
    let height = node.chain.read().height() as i32;
    wire::write_message(
        &mut stream,
        node.config.network,
        &Message::Version(VersionMessage::new(height, random())),
    )
    .await?;
    let mut version_received = false;
    let mut verack_received = false;
    let mut verack_sent = false;
    loop {
        let message = wire::read_message(&mut stream, node.config.network).await?;
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
                    wire::write_message(&mut stream, node.config.network, &Message::Verack).await?;
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
                request_headers(&node, &mut stream).await?;
            }
            Message::Ping(nonce) => {
                wire::write_message(&mut stream, node.config.network, &Message::Pong(nonce))
                    .await?;
            }
            Message::Pong(_) => {}
            Message::GetHeaders(request) | Message::GetBlocks(request) => {
                let headers = node
                    .chain
                    .read()
                    .headers_after_locator(&request.locator_hashes, request.stop_hash);
                wire::write_message(&mut stream, node.config.network, &Message::Headers(headers))
                    .await?;
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
                    wire::write_message(
                        &mut stream,
                        node.config.network,
                        &Message::GetData(requests),
                    )
                    .await?;
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
                                !mempool
                                    .get(&Txid::from_byte_array(item.hash.to_byte_array()))
                                    .is_some()
                            }
                            _ => false,
                        })
                        .take(50_000)
                        .collect::<Vec<_>>()
                };
                if !requests.is_empty() {
                    wire::write_message(
                        &mut stream,
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
                                wire::write_message(
                                    &mut stream,
                                    node.config.network,
                                    &Message::Block(block),
                                )
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
                                wire::write_message(
                                    &mut stream,
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
                    wire::write_message(
                        &mut stream,
                        node.config.network,
                        &Message::NotFound(missing),
                    )
                    .await?;
                }
            }
            Message::Block(block) => {
                let hash = block.block_hash();
                match node.connect_block(block) {
                    Ok(tip) => {
                        info!(%hash, height = tip.height, "accepted peer block");
                    }
                    Err(error) => debug!(%hash, %error, "rejected peer block"),
                }
            }
            Message::Transaction(transaction) => {
                let txid = transaction.compute_txid();
                match node.mempool.write().accept(transaction, &node.chain.read()) {
                    Ok(_) => debug!(%txid, "accepted peer transaction"),
                    Err(error) => debug!(%txid, %error, "rejected peer transaction"),
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
            wire::write_message(&mut stream, node.config.network, &Message::Verack).await?;
            verack_sent = true;
        }
    }
}

async fn request_headers(node: &Arc<Node>, stream: &mut TcpStream) -> Result<()> {
    let locator = vec![node.chain.read().best_hash()];
    wire::write_message(
        stream,
        node.config.network,
        &Message::GetHeaders(GetHeadersMessage {
            version: VersionMessage::PROTOCOL_VERSION,
            locator_hashes: locator,
            stop_hash: BlockHash::all_zeros(),
        }),
    )
    .await
}
