//! Electrum protocol server.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use anyhow::{Context, Result, anyhow, bail};
use bitcoin::consensus::encode::{deserialize, serialize};
use bitcoin::hashes::{Hash, sha256d};
use bitcoin::{Address, BlockHash, OutPoint, ScriptBuf, Transaction, TxOut, Txid};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::net::{TcpListener, TcpStream};
use tracing::debug;

use crate::Node;
use crate::chain;

const MAX_LINE_SIZE: usize = 1024 * 1024;
const SERVER_NAME: &str = "bitcoind-rs 0.1.0";

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProtocolVersion {
    major: u8,
    minor: u8,
    patch: u8,
}

const MIN_PROTOCOL_VERSION: ProtocolVersion = ProtocolVersion {
    major: 1,
    minor: 4,
    patch: 0,
};
const MAX_PROTOCOL_VERSION: ProtocolVersion = ProtocolVersion {
    major: 1,
    minor: 7,
    patch: 0,
};
const PROTOCOL_1_6: ProtocolVersion = ProtocolVersion {
    major: 1,
    minor: 6,
    patch: 0,
};
const PROTOCOL_1_7: ProtocolVersion = ProtocolVersion {
    major: 1,
    minor: 7,
    patch: 0,
};

#[derive(Clone, Copy, Debug)]
struct ElectrumSession {
    protocol_version: ProtocolVersion,
    version_negotiated: bool,
    request_seen: bool,
}

impl Default for ElectrumSession {
    fn default() -> Self {
        Self {
            protocol_version: MIN_PROTOCOL_VERSION,
            version_negotiated: false,
            request_seen: false,
        }
    }
}

#[derive(Clone, Debug)]
enum Subscription {
    Address {
        address: String,
        script_hash: String,
        status: Value,
    },
    Scripthash {
        script_hash: String,
        status: Value,
    },
    Scriptpubkey {
        script_hash: String,
        status: Value,
    },
    Outpoint {
        outpoint: OutPoint,
        status: Value,
    },
}

pub struct ElectrumServer {
    node: Arc<Node>,
}

impl ElectrumServer {
    pub fn new(node: Arc<Node>) -> Self {
        Self { node }
    }

    pub async fn run(self) -> Result<()> {
        let Some(address) = self.node.config.electrum_bind else {
            return std::future::pending::<Result<()>>().await;
        };
        let listener = TcpListener::bind(address)
            .await
            .with_context(|| format!("binding Electrum listener {address}"))?;
        loop {
            let (stream, peer) = listener.accept().await?;
            let node = self.node.clone();
            tokio::spawn(async move {
                if let Err(error) = handle_client(node, stream).await {
                    debug!(%peer, %error, "Electrum connection ended");
                }
            });
        }
    }
}

async fn handle_client(node: Arc<Node>, stream: TcpStream) -> Result<()> {
    let (read_half, mut write_half) = stream.into_split();
    let mut reader = BufReader::new(read_half);
    let mut events = node.subscribe_chain();
    let mut mempool_events = node.subscribe_mempool();
    let mut line = Vec::new();
    let mut subscriptions: HashMap<String, Subscription> = HashMap::new();
    let mut session = ElectrumSession::default();
    let mut headers_subscribed = false;
    let mut numblocks_subscribed = false;
    let mut last_chain_tip = node.chain.read().best_hash();
    loop {
        line.clear();
        tokio::select! {
            event = events.recv() => {
                let tip = match event {
                    Ok(tip) => tip,
                    Err(tokio::sync::broadcast::error::RecvError::Lagged(_)) => continue,
                    Err(tokio::sync::broadcast::error::RecvError::Closed) => continue,
                };
                let reorg = {
                    let chain = node.chain.read();
                    !chain.is_active_block(&last_chain_tip)
                };
                last_chain_tip = tip.hash;
                if headers_subscribed {
                    let header = {
                        let chain = node.chain.read();
                        chain.header(tip.height).map(|header| json!({
                            "jsonrpc": "2.0",
                            "method": "blockchain.headers.subscribe",
                            "params": [{"height": tip.height, "hex": hex::encode(serialize(header))}],
                        }))
                    };
                    if let Some(header) = header {
                        let mut encoded = serde_json::to_vec(&header)?;
                        encoded.push(b'\n');
                        write_half.write_all(&encoded).await?;
                    }
                }
                if numblocks_subscribed {
                    let mut encoded = serde_json::to_vec(&json!({
                        "jsonrpc": "2.0",
                        "method": "blockchain.numblocks.subscribe",
                        "params": [tip.height],
                    }))?;
                    encoded.push(b'\n');
                    write_half.write_all(&encoded).await?;
                }
                send_status_notifications(
                    &node,
                    &mut subscriptions,
                    &mut write_half,
                    reorg,
                )
                    .await?;
            }
            event = mempool_events.recv() => {
                match event {
                    Ok(_) | Err(tokio::sync::broadcast::error::RecvError::Lagged(_)) => {
                        send_status_notifications(
                            &node,
                            &mut subscriptions,
                            &mut write_half,
                            false,
                        )
                            .await?;
                    }
                    Err(tokio::sync::broadcast::error::RecvError::Closed) => return Ok(()),
                }
            }
            read = reader.read_until(b'\n', &mut line) => {
                let bytes = read?;
                if bytes == 0 { return Ok(()); }
                if line.len() > MAX_LINE_SIZE { bail!("Electrum request exceeds limit"); }
                let request: Value = serde_json::from_slice(&line)
                    .map_err(|error| anyhow!("invalid Electrum JSON: {error}"))?;
                let id = request.get("id").cloned().unwrap_or(Value::Null);
                let method = request.get("method").and_then(Value::as_str).unwrap_or("");
                let params = request.get("params").cloned().unwrap_or_else(|| Value::Array(Vec::new()));
                let is_notification = request.get("id").is_none();
                if !session.request_seen && method != "server.version" {
                    bail!("server.version must be the first Electrum request");
                }
                session.request_seen = true;
                let result = dispatch_with_session(
                    &node,
                    method,
                    &params,
                    &mut subscriptions,
                    &mut session,
                );
                if method == "blockchain.headers.subscribe" && result.is_ok() {
                    headers_subscribed = true;
                }
                if method == "blockchain.numblocks.subscribe" && result.is_ok() {
                    numblocks_subscribed = true;
                }
                if is_notification {
                    continue;
                }
                let response = match result {
                    Ok(result) => json!({"jsonrpc": "2.0", "id": id, "result": result}),
                    Err(error) => json!({"jsonrpc": "2.0", "id": id, "error": {"code": -1, "message": error.to_string()}}),
                };
                let mut encoded = serde_json::to_vec(&response)?;
                encoded.push(b'\n');
                write_half.write_all(&encoded).await?;
            }
        }
    }
}

#[cfg(test)]
fn dispatch(
    node: &Arc<Node>,
    method: &str,
    params: &Value,
    subscriptions: &mut HashMap<String, Subscription>,
) -> Result<Value> {
    let mut session = ElectrumSession::default();
    dispatch_with_session(node, method, params, subscriptions, &mut session)
}

fn dispatch_with_session(
    node: &Arc<Node>,
    method: &str,
    params: &Value,
    subscriptions: &mut HashMap<String, Subscription>,
    session: &mut ElectrumSession,
) -> Result<Value> {
    match method {
        "server.version" => negotiate_version(params, session),
        "server.ping" => server_ping(params, session.protocol_version),
        "server.banner" => Ok(json!("bitcoind-rs wallet-free Bitcoin node")),
        "server.add_peer" => server_add_peer(node, params),
        "server.donation_address" => Ok(json!("")),
        "server.features" => Ok(server_features_for_protocol(node, session.protocol_version)),
        "blockchain.headers.subscribe" => {
            let chain = node.chain.read();
            let height = chain.height();
            let header = chain.header(height).expect("tip header exists");
            Ok(json!({"height": height, "hex": hex::encode(serialize(header))}))
        }
        "blockchain.numblocks.subscribe" => Ok(json!(node.chain.read().height())),
        "blockchain.block.header" | "blockchain.block.get_header" => block_header(node, params),
        "blockchain.block.headers" => {
            block_headers_for_protocol(node, params, session.protocol_version)
        }
        "blockchain.block.get_chunk" => block_chunk(node, params),
        "blockchain.scripthash.get_history" => {
            let script_hash = script_hash_param(params, 0)?;
            Ok(json!(history_for_script(node, &script_hash)))
        }
        "blockchain.scripthash.get_balance" => {
            let script_hash = script_hash_param(params, 0)?;
            let (confirmed, unconfirmed) = balance_for_script(node, &script_hash);
            Ok(json!({"confirmed": confirmed, "unconfirmed": unconfirmed}))
        }
        "blockchain.scripthash.listunspent" => {
            let script_hash = script_hash_param(params, 0)?;
            Ok(json!(unspent_for_script(node, &script_hash)))
        }
        "blockchain.scripthash.get_mempool" => {
            let script_hash = script_hash_param(params, 0)?;
            Ok(json!(mempool_for_script(node, &script_hash)))
        }
        "blockchain.scripthash.subscribe" => {
            let script_hash = script_hash_param(params, 0)?;
            let status = history_status_for_script(node, &script_hash)
                .map(Value::String)
                .unwrap_or(Value::Null);
            subscriptions.insert(
                format!("scripthash:{script_hash}"),
                Subscription::Scripthash {
                    script_hash,
                    status: status.clone(),
                },
            );
            Ok(status)
        }
        "blockchain.scripthash.unsubscribe" => {
            let script_hash = script_hash_param(params, 0)?;
            Ok(Value::Bool(
                subscriptions
                    .remove(&format!("scripthash:{script_hash}"))
                    .is_some(),
            ))
        }
        "blockchain.address.get_history" => {
            let (_, script_hash) = address_param(node, params, 0)?;
            Ok(json!(history_for_script(node, &script_hash)))
        }
        "blockchain.address.get_balance" => {
            let (_, script_hash) = address_param(node, params, 0)?;
            let (confirmed, unconfirmed) = balance_for_script(node, &script_hash);
            Ok(json!({"confirmed": confirmed, "unconfirmed": unconfirmed}))
        }
        "blockchain.address.listunspent" => {
            let (_, script_hash) = address_param(node, params, 0)?;
            Ok(json!(unspent_for_script(node, &script_hash)))
        }
        "blockchain.address.get_mempool" => {
            let (_, script_hash) = address_param(node, params, 0)?;
            Ok(json!(mempool_for_script(node, &script_hash)))
        }
        "blockchain.address.subscribe" => {
            let (address, script_hash) = address_param(node, params, 0)?;
            let status = history_status_for_script(node, &script_hash)
                .map(Value::String)
                .unwrap_or(Value::Null);
            subscriptions.insert(
                format!("address:{address}"),
                Subscription::Address {
                    address,
                    script_hash,
                    status: status.clone(),
                },
            );
            Ok(status)
        }
        "blockchain.address.unsubscribe" => {
            let (address, _) = address_param(node, params, 0)?;
            Ok(Value::Bool(
                subscriptions
                    .remove(&format!("address:{address}"))
                    .is_some(),
            ))
        }
        "blockchain.scriptpubkey.get_history" => {
            let script_hash = scriptpubkey_hash_param(params, 0)?;
            Ok(json!({"history": history_for_script(node, &script_hash)}))
        }
        "blockchain.scriptpubkey.get_balance" => {
            let script_hash = scriptpubkey_hash_param(params, 0)?;
            let (confirmed, unconfirmed) = balance_for_script(node, &script_hash);
            Ok(json!({"confirmed": confirmed, "unconfirmed": unconfirmed}))
        }
        "blockchain.scriptpubkey.listunspent" => {
            let script_hash = scriptpubkey_hash_param(params, 0)?;
            Ok(json!({"utxos": unspent_for_script(node, &script_hash)}))
        }
        "blockchain.scriptpubkey.get_mempool" => {
            let script_hash = scriptpubkey_hash_param(params, 0)?;
            Ok(json!({"history": mempool_for_script(node, &script_hash)}))
        }
        "blockchain.scriptpubkey.subscribe" => {
            let script_hash = scriptpubkey_hash_param(params, 0)?;
            let status = history_status_for_script(node, &script_hash)
                .map(Value::String)
                .unwrap_or(Value::Null);
            subscriptions.insert(
                format!("scriptpubkey:{script_hash}"),
                Subscription::Scriptpubkey {
                    script_hash,
                    status: status.clone(),
                },
            );
            Ok(status)
        }
        "blockchain.scriptpubkey.unsubscribe" => {
            let script_hash = scriptpubkey_hash_param(params, 0)?;
            Ok(Value::Bool(
                subscriptions
                    .remove(&format!("scriptpubkey:{script_hash}"))
                    .is_some(),
            ))
        }
        "blockchain.transaction.get" => transaction_get(node, params),
        "blockchain.transaction.get_batch" => transaction_get_batch(node, params),
        "blockchain.transaction.get_merkle" => transaction_merkle(node, params),
        "blockchain.transaction.id_from_pos" => transaction_id_from_pos(node, params),
        "blockchain.transaction.broadcast" => transaction_broadcast(node, params),
        "blockchain.transaction.broadcast_package" => transaction_broadcast_package(node, params),
        "blockchain.transaction.testmempoolaccept" => transaction_test_mempool_accept(node, params),
        "blockchain.outpoint.subscribe" => {
            let outpoint = outpoint_param(params)?;
            let _ = scriptpubkey_param(params, 2)?;
            let status = outpoint_status(node, &outpoint)?;
            subscriptions.insert(
                outpoint_subscription_key(&outpoint),
                Subscription::Outpoint {
                    outpoint,
                    status: status.clone(),
                },
            );
            Ok(status)
        }
        "blockchain.outpoint.get_status" => {
            let outpoint = outpoint_param(params)?;
            let _ = scriptpubkey_param(params, 2)?;
            outpoint_status(node, &outpoint)
        }
        "blockchain.outpoint.unsubscribe" => {
            let outpoint = outpoint_param(params)?;
            Ok(Value::Bool(
                subscriptions
                    .remove(&outpoint_subscription_key(&outpoint))
                    .is_some(),
            ))
        }
        "blockchain.estimatefee" => {
            let conf_target = param::<u32>(params, 0)?;
            let mode = crate::rpc::optional_str(params, 1, "UNSET", "mode")?;
            let conservative = match mode.to_ascii_uppercase().as_str() {
                "UNSET" | "ECONOMICAL" => false,
                "CONSERVATIVE" => true,
                _ => bail!("mode must be UNSET, ECONOMICAL, or CONSERVATIVE"),
            };
            let rate = node
                .chain
                .write()
                .estimate_fee_rate_sat_per_kvb(conf_target, conservative)?
                .map_or(-1.0, |rate| rate as f64 / 100_000_000.0);
            Ok(json!(rate))
        }
        "blockchain.relayfee" => {
            let mempool = node.mempool.read();
            Ok(json!(
                mempool.min_relay_fee_sat_per_kvb() as f64 / 100_000_000.0
            ))
        }
        "mempool.get_fee_histogram" => {
            let mempool = node.mempool.read();
            Ok(fee_histogram(&mempool))
        }
        "mempool.get_info" => Ok(mempool_info(node)),
        "mempool.recent" => Ok(mempool_recent(node)),
        "server.peers.subscribe" => Ok(server_peers_for_protocol(node, session.protocol_version)),
        _ => bail!("unsupported Electrum method {method}"),
    }
}

#[cfg(test)]
fn server_features(node: &Arc<Node>) -> Value {
    server_features_for_protocol(node, MIN_PROTOCOL_VERSION)
}

fn server_features_for_protocol(node: &Arc<Node>, protocol_version: ProtocolVersion) -> Value {
    let mut hosts = serde_json::Map::new();
    if let Some(address) = node.config.electrum_bind {
        let host = if address.ip().is_unspecified() {
            "localhost".to_owned()
        } else {
            address.ip().to_string()
        };
        hosts.insert(host, json!({"tcp_port": address.port(), "ssl_port": null}));
    }
    let chain = node.chain.read();
    let mut features = json!({
        "hosts": Value::Object(hosts),
        "server_version": SERVER_NAME,
        "protocol_min": "1.4",
        "protocol_max": "1.7",
        "genesis_hash": chain.block_hash(0).expect("genesis exists").to_string(),
        // Electrum's pruning feature describes retained address-history
        // entries, not Bitcoin Core-style block-body pruning. This node
        // retains its address history even when old block bodies are pruned.
        "pruning": null,
    });
    if protocol_version < PROTOCOL_1_7 {
        features["hash_function"] = json!("sha256");
    }
    features
}

fn server_peers_for_protocol(_node: &Arc<Node>, _protocol_version: ProtocolVersion) -> Value {
    // Bitcoin P2P peers are not Electrum peers. Without a configured
    // directory of Electrum servers, advertising the node's P2P addresses
    // would make clients attempt Electrum connections to the wrong ports.
    json!([])
}

fn parse_protocol_version(value: &str) -> Result<ProtocolVersion> {
    let mut components = value.split('.');
    let major = components
        .next()
        .ok_or_else(|| anyhow!("invalid protocol version"))?
        .parse::<u8>()?;
    let minor = components
        .next()
        .ok_or_else(|| anyhow!("invalid protocol version"))?
        .parse::<u8>()?;
    let patch = components.next().unwrap_or("0").parse::<u8>()?;
    if components.next().is_some() {
        bail!("invalid protocol version {value}")
    }
    Ok(ProtocolVersion {
        major,
        minor,
        patch,
    })
}

fn protocol_version_string(version: ProtocolVersion) -> String {
    if version.patch == 0 {
        format!("{}.{}", version.major, version.minor)
    } else {
        format!("{}.{}.{}", version.major, version.minor, version.patch)
    }
}

fn client_protocol_range(params: &Value) -> Result<(ProtocolVersion, ProtocolVersion)> {
    let default_version = Value::String("1.4".to_owned());
    let requested = params.get(1).unwrap_or(&default_version);
    match requested {
        Value::String(version) => {
            let version = parse_protocol_version(version)?;
            Ok((version, version))
        }
        Value::Array(versions) if versions.len() >= 2 => Ok((
            parse_protocol_version(
                versions[0]
                    .as_str()
                    .ok_or_else(|| anyhow!("protocol minimum must be a string"))?,
            )?,
            parse_protocol_version(
                versions[1]
                    .as_str()
                    .ok_or_else(|| anyhow!("protocol maximum must be a string"))?,
            )?,
        )),
        Value::Array(versions) if versions.len() == 1 => {
            let version = parse_protocol_version(
                versions[0]
                    .as_str()
                    .ok_or_else(|| anyhow!("protocol version must be a string"))?,
            )?;
            Ok((version, version))
        }
        _ => bail!("protocol version must be a string or a two-element array"),
    }
}

fn negotiate_version(params: &Value, session: &mut ElectrumSession) -> Result<Value> {
    if session.version_negotiated {
        bail!("server.version may only be called once")
    }
    let (client_min, client_max) = client_protocol_range(params)?;
    if client_min > client_max {
        bail!("client protocol minimum exceeds maximum")
    }
    let lower = MIN_PROTOCOL_VERSION.max(client_min);
    let selected = MAX_PROTOCOL_VERSION.min(client_max);
    if selected < lower {
        bail!("no mutually supported protocol version")
    }
    session.protocol_version = selected;
    session.version_negotiated = true;
    Ok(json!([SERVER_NAME, protocol_version_string(selected)]))
}

fn server_ping(params: &Value, protocol_version: ProtocolVersion) -> Result<Value> {
    if protocol_version < PROTOCOL_1_7 {
        return Ok(Value::Null);
    }
    let Some(value) = params.get(0) else {
        return Ok(json!({"data": ""}));
    };
    let length = match value {
        Value::Number(number) => number
            .as_u64()
            .ok_or_else(|| anyhow!("pong_len must be a non-negative integer"))?,
        Value::String(_) => 0,
        _ => bail!("pong_len must be a non-negative integer"),
    };
    let length = usize::try_from(length).map_err(|_| anyhow!("pong_len is too large"))?;
    if length > MAX_LINE_SIZE {
        bail!("pong_len exceeds the server limit")
    }
    Ok(json!({"data": "0".repeat(length)}))
}

fn server_add_peer(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let features = params
        .get(0)
        .and_then(Value::as_object)
        .ok_or_else(|| anyhow!("server.add_peer expects a features object"))?;
    let hosts = features
        .get("hosts")
        .and_then(Value::as_object)
        .ok_or_else(|| anyhow!("server.add_peer features must contain hosts"))?;
    let mut accepted = false;
    for (host, details) in hosts {
        let Some(port) = details.get("tcp_port").and_then(Value::as_u64) else {
            continue;
        };
        let Ok(port) = u16::try_from(port) else {
            continue;
        };
        let host = host.trim_start_matches('[').trim_end_matches(']');
        let Ok(address) = host.parse() else {
            continue;
        };
        accepted |= node.add_peer_address(std::net::SocketAddr::new(address, port), false);
    }
    Ok(json!(accepted))
}

fn fee_histogram(mempool: &crate::mempool::Mempool) -> Value {
    let mut entries = mempool
        .transaction_order()
        .into_iter()
        .filter_map(|txid| mempool.get(&txid))
        .filter_map(|entry| (entry.vsize > 0).then_some((entry.fee_sat / entry.vsize, entry.vsize)))
        .collect::<Vec<_>>();
    entries.sort_by_key(|entry| std::cmp::Reverse(entry.0));
    let mut histogram: Vec<(u64, u64)> = Vec::new();
    let mut cumulative_vsize = 0u64;
    for (fee_rate, vsize) in entries {
        cumulative_vsize = cumulative_vsize.saturating_add(vsize);
        if let Some((last_fee_rate, total_vsize)) = histogram.last_mut()
            && *last_fee_rate == fee_rate
        {
            *total_vsize = cumulative_vsize;
        } else {
            histogram.push((fee_rate, cumulative_vsize));
        }
    }
    json!(histogram)
}

fn mempool_for_script(node: &Arc<Node>, script_hash: &str) -> Vec<Value> {
    let chain = node.chain.read();
    let mempool = node.mempool.read();
    mempool_records_for_script(&chain, &mempool, script_hash)
        .into_iter()
        .filter_map(|(txid, height)| {
            let entry = mempool.get(&txid)?;
            Some(json!({
                "tx_hash": txid.to_string(),
                "height": height,
                "fee": entry.fee_sat,
            }))
        })
        .collect()
}

fn mempool_transaction_height(transaction: &Transaction, mempool: &crate::mempool::Mempool) -> i64 {
    if transaction.input.iter().any(|input| {
        !input.previous_output.is_null() && mempool.get(&input.previous_output.txid).is_some()
    }) {
        -1
    } else {
        0
    }
}

fn outpoint_status(node: &Arc<Node>, outpoint: &OutPoint) -> Result<Value> {
    let mut chain = node.chain.write();
    let mempool = node.mempool.read();
    let mut status = serde_json::Map::new();

    let active_funder = chain
        .transaction(&outpoint.txid)?
        .filter(|(_, location)| chain.is_active_block(&location.block_hash))
        .and_then(|(transaction, location)| {
            transaction
                .output
                .get(outpoint.vout as usize)
                .is_some()
                .then_some(location.height)
        });
    if let Some(height) = active_funder {
        status.insert("funder_height".to_owned(), json!(height));
    } else if let Some(entry) = mempool.get(&outpoint.txid)
        && entry
            .transaction
            .output
            .get(outpoint.vout as usize)
            .is_some()
    {
        status.insert(
            "funder_height".to_owned(),
            json!(mempool_transaction_height(&entry.transaction, &mempool)),
        );
    }

    if let Some((txid, _, _, height)) = chain.spending_transaction(outpoint) {
        status.insert("spender_txhash".to_owned(), json!(txid.to_string()));
        status.insert("spender_height".to_owned(), json!(height));
    } else if let Some(txid) = mempool.spender(outpoint)
        && let Some(entry) = mempool.get(&txid)
    {
        status.insert("spender_txhash".to_owned(), json!(txid.to_string()));
        status.insert(
            "spender_height".to_owned(),
            json!(mempool_transaction_height(&entry.transaction, &mempool)),
        );
    }
    Ok(Value::Object(status))
}

fn block_header(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let height = param::<u32>(params, 0)?;
    let checkpoint = optional_checkpoint(params, 1)?;
    let chain = node.chain.read();
    let header = chain
        .header(height)
        .ok_or_else(|| anyhow!("block height out of range"))?;
    let Some(checkpoint) = checkpoint else {
        return Ok(json!(hex::encode(serialize(header))));
    };
    if height > checkpoint {
        bail!("checkpoint height must not precede requested height")
    }
    let (branch, root) = header_merkle_proof(&chain, height, checkpoint)?;
    Ok(json!({
        "header": hex::encode(serialize(header)),
        "branch": branch.iter().map(ToString::to_string).collect::<Vec<_>>(),
        "root": root.to_string(),
    }))
}

fn block_headers_for_protocol(
    node: &Arc<Node>,
    params: &Value,
    protocol_version: ProtocolVersion,
) -> Result<Value> {
    let start = param::<u32>(params, 0)?;
    let count = param::<u32>(params, 1)?.min(2_016);
    let checkpoint = optional_checkpoint(params, 2)?;
    if checkpoint.is_some()
        && count != 0
        && start.saturating_add(count.saturating_sub(1)) > checkpoint.unwrap_or_default()
    {
        bail!("checkpoint height is below the requested header range")
    }
    let chain = node.chain.read();
    let mut bytes = Vec::with_capacity(count as usize * 80);
    let mut headers = Vec::with_capacity(count as usize);
    let mut actual = 0u32;
    for height in start..start.saturating_add(count) {
        let Some(header) = chain.header(height) else {
            break;
        };
        let encoded = serialize(header);
        bytes.extend_from_slice(&encoded);
        headers.push(hex::encode(encoded));
        actual += 1;
    }
    let mut result = if protocol_version >= PROTOCOL_1_6 {
        json!({"count": actual, "headers": headers, "max": 2_016})
    } else {
        json!({"count": actual, "hex": hex::encode(bytes), "max": 2_016})
    };
    if let Some(checkpoint) = checkpoint
        && actual != 0
    {
        let last_height = start + actual - 1;
        let (branch, root) = header_merkle_proof(&chain, last_height, checkpoint)?;
        result["branch"] = json!(branch.iter().map(ToString::to_string).collect::<Vec<_>>());
        result["root"] = json!(root.to_string());
    }
    Ok(result)
}

fn optional_checkpoint(params: &Value, index: usize) -> Result<Option<u32>> {
    let Some(value) = params.get(index).filter(|value| !value.is_null()) else {
        return Ok(None);
    };
    let checkpoint = value
        .as_u64()
        .ok_or_else(|| anyhow!("cp_height must be a non-negative integer"))?;
    Ok(Some(
        u32::try_from(checkpoint).map_err(|_| anyhow!("checkpoint is too large"))?,
    ))
}

fn mempool_info(node: &Arc<Node>) -> Value {
    let mut mempool = node.mempool.write();
    json!({
        "mempoolminfee": mempool.mempool_min_fee_sat_per_kvb() as f64 / 100_000_000.0,
        "minrelaytxfee": mempool.min_relay_fee_sat_per_kvb() as f64 / 100_000_000.0,
        "incrementalrelayfee": mempool.incremental_relay_fee_sat_per_kvb() as f64 / 100_000_000.0,
    })
}

fn mempool_recent(node: &Arc<Node>) -> Value {
    let mempool = node.mempool.read();
    let mut entries = mempool
        .transaction_order()
        .into_iter()
        .filter_map(|txid| mempool.get(&txid).map(|entry| (txid, entry)))
        .collect::<Vec<_>>();
    entries.sort_by(|(left_txid, left), (right_txid, right)| {
        right
            .added_at
            .cmp(&left.added_at)
            .then_with(|| left_txid.to_string().cmp(&right_txid.to_string()))
    });
    json!(
        entries
            .into_iter()
            .take(10)
            .map(|(txid, entry)| json!({
                "txid": txid.to_string(),
                "fee": entry.fee_sat,
                "vsize": entry.vsize,
            }))
            .collect::<Vec<_>>()
    )
}

fn header_merkle_proof(
    chain: &crate::chain::ChainState,
    height: u32,
    checkpoint: u32,
) -> Result<(Vec<BlockHash>, BlockHash)> {
    if height > checkpoint {
        bail!("header height exceeds checkpoint")
    }
    let hashes = (0..=checkpoint)
        .map(|height| {
            chain
                .header(height)
                .map(|header| header.block_hash())
                .ok_or_else(|| anyhow!("checkpoint height out of range"))
        })
        .collect::<Result<Vec<_>>>()?;
    header_merkle_proof_from_hashes(&hashes, height)
}

fn header_merkle_proof_from_hashes(
    hashes: &[BlockHash],
    height: u32,
) -> Result<(Vec<BlockHash>, BlockHash)> {
    if hashes.is_empty() {
        bail!("cannot build an empty header proof")
    }
    let mut layer = hashes.to_vec();
    let mut index = usize::try_from(height).map_err(|_| anyhow!("header height is too large"))?;
    if index >= layer.len() {
        bail!("header height exceeds checkpoint")
    }
    let mut branch = Vec::new();
    while layer.len() > 1 {
        let sibling = if index ^ 1 < layer.len() {
            index ^ 1
        } else {
            index
        };
        branch.push(layer[sibling]);
        let mut next = Vec::with_capacity(layer.len().div_ceil(2));
        for pair in layer.chunks(2) {
            let right = *pair.get(1).unwrap_or(&pair[0]);
            next.push(combine_header_hashes(pair[0], right));
        }
        layer = next;
        index /= 2;
    }
    Ok((branch, layer[0]))
}

fn combine_header_hashes(left: BlockHash, right: BlockHash) -> BlockHash {
    let mut bytes = [0u8; 64];
    bytes[..32].copy_from_slice(&left.to_byte_array());
    bytes[32..].copy_from_slice(&right.to_byte_array());
    BlockHash::from_raw_hash(sha256d::Hash::hash(&bytes))
}

fn block_chunk(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let index = param::<u32>(params, 0)?;
    let start = index
        .checked_mul(2_016)
        .ok_or_else(|| anyhow!("header chunk index is too large"))?;
    let chain = node.chain.read();
    let mut bytes = Vec::with_capacity(2_016 * 80);
    for height in start..start.saturating_add(2_016) {
        let Some(header) = chain.header(height) else {
            break;
        };
        bytes.extend_from_slice(&serialize(header));
    }
    Ok(json!(hex::encode(bytes)))
}

fn transaction_get(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let txid: Txid = param::<String>(params, 0)?.parse()?;
    let verbose = crate::rpc::optional_bool(params, 1, false, "verbose")?;
    let chain_transaction = { node.chain.write().transaction(&txid)? };
    if let Some((transaction, location)) = chain_transaction {
        if verbose {
            let chain = node.chain.read();
            let active = chain.is_active_block(&location.block_hash);
            let confirmations = Some(if active {
                chain.height().saturating_sub(location.height) + 1
            } else {
                0
            });
            let time = active
                .then(|| {
                    chain
                        .header_by_hash(&location.block_hash)
                        .map(|header| header.time)
                })
                .flatten();
            return Ok(electrum_transaction_json(
                &transaction,
                Some(&location),
                confirmations,
                time,
            ));
        }
        return Ok(json!(chain::transaction_hex(&transaction)));
    }
    if let Some(entry) = node.mempool.read().get(&txid) {
        if verbose {
            return Ok(electrum_transaction_json(
                &entry.transaction,
                None,
                None,
                None,
            ));
        }
        return Ok(json!(chain::transaction_hex(&entry.transaction)));
    }
    bail!("transaction not found")
}

fn transaction_get_batch(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let txids = params
        .get(0)
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("transaction.get_batch expects an array of txids"))?;
    let verbose = crate::rpc::optional_bool(params, 1, false, "verbose")?;
    txids
        .iter()
        .map(|txid| {
            let txid = txid
                .as_str()
                .ok_or_else(|| anyhow!("transaction ids must be strings"))?;
            transaction_get(node, &json!([txid, verbose]))
        })
        .collect::<Result<Vec<_>>>()
        .map(Value::Array)
}

fn electrum_transaction_json(
    transaction: &Transaction,
    location: Option<&chain::TxLocation>,
    confirmations: Option<u32>,
    time: Option<u32>,
) -> Value {
    let vin = transaction
        .input
        .iter()
        .map(|input| {
            if input.previous_output.is_null() {
                json!({
                    "coinbase": hex::encode(input.script_sig.as_bytes()),
                    "sequence": input.sequence.to_consensus_u32(),
                })
            } else {
                json!({
                    "txid": input.previous_output.txid.to_string(),
                    "vout": input.previous_output.vout,
                    "scriptSig": {
                        "hex": hex::encode(input.script_sig.as_bytes()),
                        "asm": input.script_sig.to_asm_string(),
                    },
                    "txinwitness": input.witness.to_vec().into_iter().map(hex::encode).collect::<Vec<_>>(),
                    "sequence": input.sequence.to_consensus_u32(),
                })
            }
        })
        .collect::<Vec<_>>();
    let vout = transaction
        .output
        .iter()
        .enumerate()
        .map(|(index, output)| {
            json!({
                "value": output.value.to_btc(),
                "n": index,
                "scriptPubKey": {
                    "hex": hex::encode(output.script_pubkey.as_bytes()),
                    "asm": output.script_pubkey.to_asm_string(),
                },
            })
        })
        .collect::<Vec<_>>();
    let mut result = json!({
        "txid": transaction.compute_txid().to_string(),
        "hash": transaction.compute_wtxid().to_string(),
        "version": transaction.version.0,
        "hex": chain::transaction_hex(transaction),
        "size": serialize(transaction).len(),
        "vsize": transaction.vsize(),
        "weight": transaction.weight().to_wu(),
        "locktime": transaction.lock_time.to_consensus_u32(),
        "vin": vin,
        "vout": vout,
    });
    if let Some(location) = location {
        result["blockhash"] = json!(location.block_hash.to_string());
        result["height"] = json!(location.height);
    }
    if let Some(confirmations) = confirmations {
        result["confirmations"] = json!(confirmations);
    }
    if let Some(time) = time {
        result["time"] = json!(time);
        result["blocktime"] = json!(time);
    }
    result
}

fn transaction_merkle(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let txid: Txid = param::<String>(params, 0)?.parse()?;
    let requested_height = param::<u32>(params, 1)?;
    let Some((branch, position, height)) = node.chain.write().merkle_branch(&txid)? else {
        bail!("transaction not found")
    };
    if height != requested_height {
        bail!("transaction is not in the requested block")
    }
    Ok(json!({
        "block_height": height,
        "pos": position,
        "merkle": branch.iter().map(ToString::to_string).collect::<Vec<_>>(),
    }))
}

fn transaction_id_from_pos(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let height = param::<u32>(params, 0)?;
    let position = param::<u32>(params, 1)?;
    let include_merkle = crate::rpc::optional_bool(params, 2, false, "include_merkle")?;
    let mut chain = node.chain.write();
    let hash = chain
        .block_hash(height)
        .ok_or_else(|| anyhow!("block height out of range"))?;
    let block = chain
        .block(&hash)?
        .ok_or_else(|| anyhow!("block not found"))?;
    let transaction = block
        .txdata
        .get(position as usize)
        .ok_or_else(|| anyhow!("transaction position out of range"))?;
    let txid = transaction.compute_txid();
    if !include_merkle {
        return Ok(json!(txid.to_string()));
    }
    let (branch, _, _) = chain
        .merkle_branch(&txid)?
        .ok_or_else(|| anyhow!("transaction not found"))?;
    Ok(json!({
        "tx_hash": txid.to_string(),
        "merkle": branch.iter().map(ToString::to_string).collect::<Vec<_>>(),
        "pos": position,
    }))
}

fn transaction_broadcast(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let raw = param::<String>(params, 0)?;
    let transaction: Transaction = deserialize(&hex::decode(raw)?)?;
    let txid = node.accept_transaction(transaction)?;
    Ok(json!(txid.to_string()))
}

fn transaction_broadcast_package(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let raw_transactions = params
        .get(0)
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("broadcast_package expects an array of transactions"))?;
    if raw_transactions.is_empty() {
        bail!("broadcast_package requires at least one transaction")
    }
    let verbose = crate::rpc::optional_bool(params, 1, false, "verbose")?;
    let result = crate::rpc::submit_package(node, &json!([raw_transactions]))?;
    if verbose {
        return Ok(result);
    }
    let success = result["package_msg"].as_str() == Some("success");
    if success {
        return Ok(json!({"success": true}));
    }
    let errors = result["tx-results"]
        .as_object()
        .into_iter()
        .flat_map(|results| results.values())
        .filter(|entry| entry["allowed"] == json!(false) || entry.get("error").is_some())
        .map(|entry| {
            json!({
                "txid": entry["txid"].clone(),
                "error": entry
                    .get("error")
                    .or_else(|| entry.get("reject-reason"))
                    .cloned()
                    .unwrap_or_else(|| result["package_msg"].clone()),
            })
        })
        .collect::<Vec<_>>();
    Ok(json!({"success": false, "errors": errors}))
}

fn transaction_test_mempool_accept(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let raw_transactions = params
        .get(0)
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("testmempoolaccept expects an array of transactions"))?;
    if raw_transactions.is_empty() {
        bail!("testmempoolaccept requires at least one transaction")
    }
    crate::rpc::test_mempool_accept(node, &json!([raw_transactions]))
}

async fn send_status_notifications(
    node: &Arc<Node>,
    subscriptions: &mut HashMap<String, Subscription>,
    writer: &mut tokio::net::tcp::OwnedWriteHalf,
    force_scriptpubkey_notification: bool,
) -> Result<()> {
    for subscription in subscriptions.values_mut() {
        let notification = match subscription {
            Subscription::Address {
                address,
                script_hash,
                status,
            } => {
                let current = history_status_for_script(node, script_hash)
                    .map(Value::String)
                    .unwrap_or(Value::Null);
                if status_notification_needed(status, &current, false) {
                    *status = current.clone();
                    json!({
                        "jsonrpc": "2.0",
                        "method": "blockchain.address.subscribe",
                        "params": [address, current],
                    })
                } else {
                    continue;
                }
            }
            Subscription::Scripthash {
                script_hash,
                status,
            } => {
                let current = history_status_for_script(node, script_hash)
                    .map(Value::String)
                    .unwrap_or(Value::Null);
                if status_notification_needed(status, &current, false) {
                    *status = current.clone();
                    json!({
                        "jsonrpc": "2.0",
                        "method": "blockchain.scripthash.subscribe",
                        "params": [script_hash, current],
                    })
                } else {
                    continue;
                }
            }
            Subscription::Scriptpubkey {
                script_hash,
                status,
            } => {
                let current = history_status_for_script(node, script_hash)
                    .map(Value::String)
                    .unwrap_or(Value::Null);
                if status_notification_needed(status, &current, force_scriptpubkey_notification) {
                    *status = current.clone();
                    json!({
                        "jsonrpc": "2.0",
                        "method": "blockchain.scriptpubkey.subscribe",
                        "params": [script_hash, current],
                    })
                } else {
                    continue;
                }
            }
            Subscription::Outpoint { outpoint, status } => {
                let current = outpoint_status(node, outpoint)?;
                if *status == current {
                    continue;
                }
                *status = current.clone();
                json!({
                    "jsonrpc": "2.0",
                    "method": "blockchain.outpoint.subscribe",
                    "params": [outpoint.txid.to_string(), outpoint.vout, current],
                })
            }
        };
        let mut encoded = serde_json::to_vec(&notification)?;
        encoded.push(b'\n');
        writer.write_all(&encoded).await?;
    }
    Ok(())
}

fn status_notification_needed(previous: &Value, current: &Value, force: bool) -> bool {
    force || previous != current
}

fn history_for_script(node: &Arc<Node>, script_hash: &str) -> Vec<Value> {
    let records = history_records_for_script(node, script_hash);
    let mempool = node.mempool.read();
    records
        .into_iter()
        .map(|(txid, height)| {
            let mut result = json!({"tx_hash": txid.to_string(), "height": height});
            if let Some(entry) = mempool.get(&txid) {
                result["fee"] = json!(entry.fee_sat);
            }
            result
        })
        .collect()
}

fn history_status_for_script(node: &Arc<Node>, script_hash: &str) -> Option<String> {
    let records = history_records_for_script(node, script_hash);
    if records.is_empty() {
        return None;
    }
    Some(history_status(&records))
}

fn history_status(records: &[(Txid, i64)]) -> String {
    let mut input = String::new();
    for (txid, height) in records {
        input.push_str(&txid.to_string());
        input.push(':');
        input.push_str(&height.to_string());
        input.push(':');
    }
    hex::encode(Sha256::digest(input.as_bytes()))
}

fn history_records_for_script(node: &Arc<Node>, script_hash: &str) -> Vec<(Txid, i64)> {
    let chain = node.chain.read();
    let mempool = node.mempool.read();
    let mut records = Vec::new();
    let mut seen = HashSet::new();
    for entry in chain.get_history(script_hash) {
        if seen.insert(entry.txid) {
            records.push((entry.txid, i64::from(entry.height)));
        }
    }
    for (txid, height) in mempool_records_for_script(&chain, &mempool, script_hash) {
        if seen.insert(txid) {
            records.push((txid, height));
        }
    }
    records
}

fn mempool_records_for_script(
    chain: &crate::chain::ChainState,
    mempool: &crate::mempool::Mempool,
    script_hash: &str,
) -> Vec<(Txid, i64)> {
    let mut records = mempool
        .transaction_order()
        .into_iter()
        .filter_map(|txid| {
            let entry = mempool.get(&txid)?;
            transaction_affects_script(&entry.transaction, chain, mempool, script_hash).then_some((
                txid,
                mempool_transaction_height(&entry.transaction, mempool),
            ))
        })
        .collect::<Vec<_>>();
    sort_mempool_records(&mut records);
    records
}

fn sort_mempool_records(records: &mut [(Txid, i64)]) {
    records.sort_by(|(left_txid, left_height), (right_txid, right_height)| {
        right_height
            .cmp(left_height)
            .then_with(|| left_txid.to_string().cmp(&right_txid.to_string()))
    });
}

fn balance_for_script(node: &Arc<Node>, script_hash: &str) -> (u64, i64) {
    let chain = node.chain.read();
    let mempool = node.mempool.read();
    let confirmed = chain
        .get_utxos(script_hash)
        .into_iter()
        .map(|(_, entry)| entry.output.value.to_sat())
        .sum();
    let mut unconfirmed = 0i64;
    for txid in mempool.transaction_order() {
        let Some(entry) = mempool.get(&txid) else {
            continue;
        };
        for input in &entry.transaction.input {
            if let Some(output) = output_for_outpoint(&chain, &mempool, input.previous_output)
                && chain::electrum_script_hash(&output.script_pubkey) == script_hash
            {
                unconfirmed -= output.value.to_sat() as i64;
            }
        }
        for output in &entry.transaction.output {
            if chain::electrum_script_hash(&output.script_pubkey) == script_hash {
                unconfirmed += output.value.to_sat() as i64;
            }
        }
    }
    (confirmed, unconfirmed)
}

fn unspent_for_script(node: &Arc<Node>, script_hash: &str) -> Vec<Value> {
    let chain = node.chain.read();
    let mempool = node.mempool.read();
    let mut spent = HashSet::new();
    for txid in mempool.transaction_order() {
        if let Some(entry) = mempool.get(&txid) {
            spent.extend(
                entry
                    .transaction
                    .input
                    .iter()
                    .map(|input| input.previous_output),
            );
        }
    }
    let mut confirmed: Vec<(OutPoint, i64, u64)> = chain
        .get_utxos(script_hash)
        .into_iter()
        .filter(|(outpoint, _)| !spent.contains(outpoint))
        .map(|(outpoint, entry)| {
            (
                outpoint,
                i64::from(entry.height),
                entry.output.value.to_sat(),
            )
        })
        .collect();
    confirmed.sort_by(|left, right| {
        left.1
            .cmp(&right.1)
            .then_with(|| left.0.txid.to_string().cmp(&right.0.txid.to_string()))
            .then_with(|| left.0.vout.cmp(&right.0.vout))
    });
    let mut unconfirmed = Vec::new();
    for txid in mempool.transaction_order() {
        let Some(entry) = mempool.get(&txid) else {
            continue;
        };
        for (vout, output) in entry.transaction.output.iter().enumerate() {
            if chain::electrum_script_hash(&output.script_pubkey) == script_hash {
                let outpoint = OutPoint::new(txid, vout as u32);
                if !spent.contains(&outpoint) {
                    unconfirmed.push((outpoint, 0, output.value.to_sat()));
                }
            }
        }
    }
    confirmed.extend(unconfirmed);
    let results = confirmed;
    results
        .into_iter()
        .map(|(outpoint, height, value)| {
            json!({
                "tx_hash": outpoint.txid.to_string(),
                "tx_pos": outpoint.vout,
                "height": height,
                "value": value,
            })
        })
        .collect()
}

fn transaction_affects_script(
    transaction: &Transaction,
    chain: &crate::chain::ChainState,
    mempool: &crate::mempool::Mempool,
    script_hash: &str,
) -> bool {
    transaction
        .output
        .iter()
        .any(|output| chain::electrum_script_hash(&output.script_pubkey) == script_hash)
        || transaction.input.iter().any(|input| {
            output_for_outpoint(chain, mempool, input.previous_output).is_some_and(|output| {
                chain::electrum_script_hash(&output.script_pubkey) == script_hash
            })
        })
}

fn output_for_outpoint(
    chain: &crate::chain::ChainState,
    mempool: &crate::mempool::Mempool,
    outpoint: OutPoint,
) -> Option<TxOut> {
    chain
        .utxo(&outpoint)
        .map(|entry| entry.output.clone())
        .or_else(|| {
            mempool
                .get(&outpoint.txid)
                .and_then(|entry| entry.transaction.output.get(outpoint.vout as usize))
                .cloned()
        })
}

fn script_hash_param(params: &Value, index: usize) -> Result<String> {
    let value = param::<String>(params, index)?;
    if value.len() != 64 || !value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        bail!("invalid Electrum scripthash");
    }
    Ok(value.to_ascii_lowercase())
}

fn scriptpubkey_param(params: &Value, index: usize) -> Result<ScriptBuf> {
    let value = param::<String>(params, index)?;
    Ok(ScriptBuf::from_bytes(hex::decode(value)?))
}

fn scriptpubkey_hash_param(params: &Value, index: usize) -> Result<String> {
    let script = scriptpubkey_param(params, index)?;
    Ok(chain::electrum_script_hash(&script))
}

fn address_param(node: &Arc<Node>, params: &Value, index: usize) -> Result<(String, String)> {
    let value = param::<String>(params, index)?;
    let address = value
        .parse::<Address<bitcoin::address::NetworkUnchecked>>()?
        .require_network(node.config.network)?;
    let script_hash = chain::electrum_script_hash(&address.script_pubkey());
    Ok((address.to_string(), script_hash))
}

fn outpoint_param(params: &Value) -> Result<OutPoint> {
    let txid: Txid = param::<String>(params, 0)?.parse()?;
    let vout = param::<u32>(params, 1)?;
    Ok(OutPoint::new(txid, vout))
}

fn outpoint_subscription_key(outpoint: &OutPoint) -> String {
    format!("outpoint:{}:{}", outpoint.txid, outpoint.vout)
}

fn param<T: serde::de::DeserializeOwned>(params: &Value, index: usize) -> Result<T> {
    let value = params
        .as_array()
        .and_then(|values| values.get(index))
        .ok_or_else(|| anyhow!("missing parameter {index}"))?;
    Ok(serde_json::from_value(value.clone())?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Config, Node};
    use bitcoin::Amount;
    use bitcoin::Block;
    use bitcoin::Network;
    use bitcoin::absolute::LockTime;
    use bitcoin::block::{Header, Version as BlockVersion};
    use bitcoin::blockdata::script::Builder;
    use bitcoin::blockdata::transaction::{TxIn, TxOut, Version};
    use bitcoin::blockdata::witness::Witness;
    use bitcoin::hashes::Hash;

    fn mine_test_block(previous: &Header, height: u32, tag: u8) -> Block {
        let mut block = Block {
            header: Header {
                version: BlockVersion::from_consensus(4),
                prev_blockhash: previous.block_hash(),
                merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                time: previous.time + 1,
                bits: previous.bits,
                nonce: 0,
            },
            txdata: vec![Transaction {
                version: Version::ONE,
                lock_time: LockTime::ZERO,
                input: vec![TxIn {
                    previous_output: OutPoint::null(),
                    script_sig: Builder::new()
                        .push_int(i64::from(height))
                        .push_slice([tag])
                        .push_slice([0u8])
                        .into_script(),
                    sequence: bitcoin::Sequence::MAX,
                    witness: Witness::default(),
                }],
                output: vec![TxOut {
                    value: Amount::from_sat(5_000_000_000),
                    script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
                }],
            }],
        };
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        while !block.header.target().is_met_by(block.block_hash()) {
            block.header.nonce = block.header.nonce.wrapping_add(1);
        }
        block
    }

    #[test]
    fn empty_fee_histogram_is_a_valid_electrum_result() {
        let mempool = crate::mempool::Mempool::new(Network::Regtest);
        assert_eq!(fee_histogram(&mempool), json!([]));
    }

    #[test]
    fn script_hash_validation_is_case_insensitive_but_length_strict() {
        let params = json!(["AA".repeat(32)]);
        assert_eq!(script_hash_param(&params, 0).unwrap(), "aa".repeat(32));
        assert!(script_hash_param(&json!(["00"]), 0).is_err());
    }

    #[test]
    fn history_status_uses_electrum_digest_order() {
        let txid = Txid::from_byte_array([1; 32]);
        assert_eq!(
            history_status(&[(txid, 1)]),
            "549540a6810df8dc5008757fa694172b0f7a3e32facfd9f39eab228286543cde"
        );
    }

    #[test]
    fn mempool_records_use_electrum_height_then_txid_order() {
        let low_txid = Txid::from_byte_array([1; 32]);
        let high_txid = Txid::from_byte_array([2; 32]);
        let child_txid = Txid::from_byte_array([3; 32]);
        let mut records = vec![(child_txid, -1), (high_txid, 0), (low_txid, 0)];

        sort_mempool_records(&mut records);

        assert_eq!(records[0].1, 0);
        assert_eq!(records[1].1, 0);
        assert_eq!(records[2], (child_txid, -1));
        assert!(records[0].0.to_string() < records[1].0.to_string());
    }

    #[test]
    fn scriptpubkey_reorg_notifications_can_repeat_an_unchanged_status() {
        let status = json!("same-status");
        assert!(!status_notification_needed(&status, &status, false));
        assert!(status_notification_needed(&status, &status, true));
        assert!(status_notification_needed(
            &status,
            &json!("new-status"),
            false
        ));
    }

    #[tokio::test]
    async fn history_notifications_refresh_after_mempool_activity() -> Result<()> {
        let directory = tempfile::tempdir()?;
        let node = Node::open(Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            p2p_bind: "127.0.0.1:0".parse().unwrap(),
            p2p_binds: Vec::new(),
            rpc_bind: None,
            rpc_binds: Vec::new(),
            rpc_allow_ips: Vec::new(),
            rpc_auth: Vec::new(),
            rpc_cookie_path: None,
            rpc_cookie_permissions: crate::config::RpcCookiePermissions::Owner,
            rpc_server_timeout_secs: 30,
            rpc_threads: 16,
            rpc_work_queue: 64,
            rpc_whitelist: std::collections::HashMap::new(),
            rpc_whitelist_default: false,
            electrum_bind: None,
            rest: false,
            listen: true,
            dnsseed: true,
            force_dns_seed: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            prune: 0,
            reindex: false,
            reindex_chainstate: false,
            load_blocks: Vec::new(),
            txindex: false,
            txospenderindex: false,
            max_mempool_mb: 300,
            mempool_expiry_hours: 336,
            coinstatsindex: false,
            blockfilterindex: true,
            peer_block_filters: true,
            persist_mempool: true,
            persist_mempool_v1: false,
            seed_nodes: Vec::new(),
            connect_disabled: false,
            v2_transport: true,
            network_active: true,
            discover: true,
            external_addresses: Vec::new(),
            dns_lookup: true,
            add_nodes: Vec::new(),
            seed_nodes_for_address_fetch: Vec::new(),
            signet_challenge: None,
            max_peers: 1,
            max_upload_target: 0,
            peer_bloom_filters: false,
            peer_timeout_secs: 60,
            connect_timeout_ms: 5_000,
            block_max_weight: 4_000_000,
            block_reserved_weight: 8_000,
            block_version: None,
            block_min_tx_fee_sat_per_kvb: 1,
            min_relay_tx_fee_sat_per_kvb: 100,
            incremental_relay_fee_sat_per_kvb: 100,
            dust_relay_fee_sat_per_kvb: 3_000,
            max_datacarrier_bytes: Some(100_000),
            permit_bare_multisig: true,
            zmq: crate::config::ZmqConfig::default(),
        })?;
        let genesis = *node.chain.read().header(0).expect("genesis header exists");
        let mut funding_outpoint = None;
        let mut previous = genesis;
        for height in 1..=101 {
            let block = mine_test_block(&previous, height, height as u8);
            if height == 1 {
                funding_outpoint = Some(OutPoint::new(block.txdata[0].compute_txid(), 0));
            }
            previous = block.header;
            node.connect_block(block)?;
        }
        let funding_outpoint = funding_outpoint.expect("funding output exists");
        let transaction = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: funding_outpoint,
                script_sig: ScriptBuf::from_bytes(vec![0x00; 100]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(4_999_999_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let script_hash = chain::electrum_script_hash(&transaction.output[0].script_pubkey);
        let key = format!("scripthash:{script_hash}");
        let mut subscriptions = HashMap::new();
        subscriptions.insert(
            key.clone(),
            Subscription::Scripthash {
                script_hash: script_hash.clone(),
                status: Value::Null,
            },
        );
        node.accept_transaction(transaction)?;

        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await?;
        let address = listener.local_addr()?;
        let (client, accepted) =
            tokio::join!(tokio::net::TcpStream::connect(address), listener.accept());
        let _client = client?;
        let (server, _) = accepted?;
        let (_, mut writer) = server.into_split();
        send_status_notifications(&node, &mut subscriptions, &mut writer, false).await?;

        let Subscription::Scripthash { status, .. } = subscriptions.get(&key).unwrap() else {
            panic!("expected scripthash subscription")
        };
        assert!(status.is_string());
        Ok(())
    }

    #[test]
    fn outpoint_status_ignores_side_chain_funders() {
        let directory = tempfile::tempdir().unwrap();
        let node = Arc::new(
            Node::open(Config {
                network: Network::Regtest,
                datadir: directory.path().to_owned(),
                p2p_bind: "127.0.0.1:0".parse().unwrap(),
                p2p_binds: Vec::new(),
                rpc_bind: None,
                rpc_binds: Vec::new(),
                rpc_allow_ips: Vec::new(),
                rpc_auth: Vec::new(),
                rpc_cookie_path: None,
                rpc_cookie_permissions: crate::config::RpcCookiePermissions::Owner,
                rpc_server_timeout_secs: 30,
                rpc_threads: 16,
                rpc_work_queue: 64,
                rpc_whitelist: std::collections::HashMap::new(),
                rpc_whitelist_default: false,
                electrum_bind: Some("127.0.0.1:30001".parse().unwrap()),
                rest: false,
                listen: true,
                dnsseed: true,
                force_dns_seed: false,
                onlynet: Vec::new(),
                proxy: None,
                proxy_randomize: false,
                peer_permissions: crate::config::PeerPermissionConfig::default(),
                blocksonly: false,
                private_broadcast: false,
                accept_nonstd_txn: true,
                cjdns_reachable: false,
                prune: 0,
                reindex: false,
                reindex_chainstate: false,
                load_blocks: Vec::new(),
                txindex: false,
                txospenderindex: false,
                max_mempool_mb: 300,
                mempool_expiry_hours: 336,
                coinstatsindex: false,
                blockfilterindex: true,
                peer_block_filters: true,
                persist_mempool: true,
                persist_mempool_v1: false,
                seed_nodes: Vec::new(),
                connect_disabled: false,
                v2_transport: true,
                network_active: true,
                discover: true,
                external_addresses: Vec::new(),
                dns_lookup: true,
                add_nodes: Vec::new(),
                seed_nodes_for_address_fetch: Vec::new(),
                signet_challenge: None,
                max_peers: 1,
                max_upload_target: 0,
                peer_bloom_filters: false,
                peer_timeout_secs: 60,
                connect_timeout_ms: 5_000,
                block_max_weight: 4_000_000,
                block_reserved_weight: 8_000,
                block_version: None,
                block_min_tx_fee_sat_per_kvb: 1,
                min_relay_tx_fee_sat_per_kvb: 100,
                incremental_relay_fee_sat_per_kvb: 100,
                dust_relay_fee_sat_per_kvb: 3_000,
                max_datacarrier_bytes: Some(100_000),
                permit_bare_multisig: true,
                zmq: crate::config::ZmqConfig::default(),
            })
            .unwrap(),
        );
        let genesis = *node.chain.read().header(0).unwrap();
        let main_one = mine_test_block(&genesis, 1, 1);
        let main_outpoint = OutPoint::new(main_one.txdata[0].compute_txid(), 0);
        node.connect_block(main_one).unwrap();
        let main_tip = *node.chain.read().header(1).unwrap();
        node.connect_block(mine_test_block(&main_tip, 2, 2))
            .unwrap();

        let side = mine_test_block(&genesis, 1, 3);
        let outpoint = OutPoint::new(side.txdata[0].compute_txid(), 0);
        let side_hash = side.block_hash();
        node.connect_block(side).unwrap();

        assert_eq!(node.chain.read().height(), 2);
        assert!(!node.chain.read().is_active_block(&side_hash));
        assert_eq!(
            outpoint_status(&node, &main_outpoint).unwrap(),
            json!({"funder_height": 1})
        );
        assert_eq!(outpoint_status(&node, &outpoint).unwrap(), json!({}));
    }

    #[test]
    fn header_checkpoint_proofs_return_a_branch_and_root() {
        let hashes = vec![
            BlockHash::from_byte_array([1; 32]),
            BlockHash::from_byte_array([2; 32]),
            BlockHash::from_byte_array([3; 32]),
        ];
        let (branch, root) = header_merkle_proof_from_hashes(&hashes, 2).unwrap();
        assert_eq!(branch.len(), 2);
        assert_eq!(branch[0], hashes[2]);
        assert_eq!(
            root,
            combine_header_hashes(
                combine_header_hashes(hashes[0], hashes[1]),
                combine_header_hashes(hashes[2], hashes[2]),
            )
        );
        assert!(header_merkle_proof_from_hashes(&hashes, 3).is_err());
    }

    #[test]
    fn negotiates_modern_protocol_shapes_and_methods() {
        let directory = tempfile::tempdir().unwrap();
        let node = Arc::new(
            Node::open(Config {
                network: Network::Regtest,
                datadir: directory.path().to_owned(),
                p2p_bind: "127.0.0.1:0".parse().unwrap(),
                p2p_binds: Vec::new(),
                rpc_bind: None,
                rpc_binds: Vec::new(),
                rpc_allow_ips: Vec::new(),
                rpc_auth: Vec::new(),
                rpc_cookie_path: None,
                rpc_cookie_permissions: crate::config::RpcCookiePermissions::Owner,
                rpc_server_timeout_secs: 30,
                rpc_threads: 16,
                rpc_work_queue: 64,
                rpc_whitelist: std::collections::HashMap::new(),
                rpc_whitelist_default: false,
                electrum_bind: Some("127.0.0.1:30001".parse().unwrap()),
                rest: false,
                listen: true,
                dnsseed: true,
                force_dns_seed: false,
                onlynet: Vec::new(),
                proxy: None,
                proxy_randomize: false,
                peer_permissions: crate::config::PeerPermissionConfig::default(),
                blocksonly: false,
                private_broadcast: false,
                accept_nonstd_txn: true,
                cjdns_reachable: false,
                // Block pruning must not be advertised as Electrum history
                // pruning in server.features.
                prune: 1,
                reindex: false,
                reindex_chainstate: false,
                load_blocks: Vec::new(),
                txindex: false,
                txospenderindex: false,
                max_mempool_mb: 300,
                mempool_expiry_hours: 336,
                coinstatsindex: false,
                blockfilterindex: true,
                peer_block_filters: true,
                persist_mempool: true,
                persist_mempool_v1: false,
                seed_nodes: Vec::new(),
                connect_disabled: false,
                v2_transport: true,
                network_active: true,
                discover: true,
                external_addresses: Vec::new(),
                dns_lookup: true,
                add_nodes: Vec::new(),
                seed_nodes_for_address_fetch: Vec::new(),
                signet_challenge: None,
                max_peers: 1,
                max_upload_target: 0,
                peer_bloom_filters: false,
                peer_timeout_secs: 60,
                connect_timeout_ms: 5_000,
                block_max_weight: 4_000_000,
                block_reserved_weight: 8_000,
                block_version: None,
                block_min_tx_fee_sat_per_kvb: 1,
                min_relay_tx_fee_sat_per_kvb: 100,
                incremental_relay_fee_sat_per_kvb: 100,
                dust_relay_fee_sat_per_kvb: 3_000,
                max_datacarrier_bytes: Some(100_000),
                permit_bare_multisig: true,
                zmq: crate::config::ZmqConfig::default(),
            })
            .unwrap(),
        );
        let mut session = ElectrumSession::default();
        let mut subscriptions = HashMap::new();
        assert_eq!(
            dispatch_with_session(
                &node,
                "server.version",
                &json!(["test-client", ["1.4", "1.7"]]),
                &mut subscriptions,
                &mut session,
            )
            .unwrap(),
            json!([SERVER_NAME, "1.7"])
        );
        let features = dispatch_with_session(
            &node,
            "server.features",
            &json!([]),
            &mut subscriptions,
            &mut session,
        )
        .unwrap();
        assert_eq!(features["protocol_max"], json!("1.7"));
        assert!(node.chain.read().is_pruned());
        assert!(node.chain.read().txospender_index_enabled());
        assert_eq!(features["pruning"], Value::Null);
        assert!(features.get("hash_function").is_none());
        assert_eq!(
            dispatch_with_session(
                &node,
                "blockchain.numblocks.subscribe",
                &json!([]),
                &mut subscriptions,
                &mut session,
            )
            .unwrap(),
            json!(0)
        );
        let address = "bcrt1q2nfxmhd4n3c8834pj72xagvyr9gl57n5r94fsl";
        let address_balance = dispatch_with_session(
            &node,
            "blockchain.address.get_balance",
            &json!([address]),
            &mut subscriptions,
            &mut session,
        )
        .unwrap();
        let checked_address = address
            .parse::<Address<bitcoin::address::NetworkUnchecked>>()
            .unwrap()
            .require_network(Network::Regtest)
            .unwrap();
        let script_hash = chain::electrum_script_hash(&checked_address.script_pubkey());
        assert_eq!(
            address_balance,
            dispatch_with_session(
                &node,
                "blockchain.scripthash.get_balance",
                &json!([script_hash]),
                &mut subscriptions,
                &mut session,
            )
            .unwrap()
        );
        assert_eq!(
            dispatch_with_session(
                &node,
                "blockchain.address.get_history",
                &json!([address]),
                &mut subscriptions,
                &mut session,
            )
            .unwrap(),
            json!([])
        );
        assert_eq!(
            dispatch_with_session(
                &node,
                "blockchain.address.subscribe",
                &json!([address]),
                &mut subscriptions,
                &mut session,
            )
            .unwrap(),
            Value::Null
        );
        assert!(subscriptions.contains_key(&format!("address:{address}")));
        assert_eq!(
            dispatch_with_session(
                &node,
                "blockchain.address.unsubscribe",
                &json!([address]),
                &mut subscriptions,
                &mut session,
            )
            .unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            dispatch_with_session(
                &node,
                "server.add_peer",
                &json!([{"hosts": {"192.0.2.55": {"tcp_port": 50002}}}]),
                &mut subscriptions,
                &mut session,
            )
            .unwrap(),
            json!(true)
        );
        assert_eq!(
            dispatch_with_session(
                &node,
                "server.donation_address",
                &json!([]),
                &mut subscriptions,
                &mut session,
            )
            .unwrap(),
            json!("")
        );
        let headers = dispatch_with_session(
            &node,
            "blockchain.block.headers",
            &json!([0, 1]),
            &mut subscriptions,
            &mut session,
        )
        .unwrap();
        assert!(headers.get("headers").is_some());
        assert!(headers.get("hex").is_none());
        let genesis_header = dispatch_with_session(
            &node,
            "blockchain.block.header",
            &json!([0, 0]),
            &mut subscriptions,
            &mut session,
        )
        .unwrap();
        assert_eq!(genesis_header["branch"], json!([]));
        assert_eq!(
            genesis_header["root"],
            json!(node.chain.read().block_hash(0).unwrap().to_string())
        );
        let genesis_headers = dispatch_with_session(
            &node,
            "blockchain.block.headers",
            &json!([0, 1, 0]),
            &mut subscriptions,
            &mut session,
        )
        .unwrap();
        assert_eq!(genesis_headers["count"], json!(1));
        assert_eq!(genesis_headers["branch"], json!([]));
        assert_eq!(
            genesis_headers["root"],
            json!(node.chain.read().block_hash(0).unwrap().to_string())
        );
        assert_eq!(
            dispatch_with_session(
                &node,
                "server.ping",
                &json!([3]),
                &mut subscriptions,
                &mut session,
            )
            .unwrap(),
            json!({"data": "000"})
        );
        assert_eq!(
            dispatch_with_session(
                &node,
                "mempool.get_info",
                &json!([]),
                &mut subscriptions,
                &mut session,
            )
            .unwrap()["minrelaytxfee"],
            json!(0.000001)
        );
        assert_eq!(
            dispatch_with_session(
                &node,
                "mempool.recent",
                &json!([]),
                &mut subscriptions,
                &mut session,
            )
            .unwrap(),
            json!([])
        );
        assert_eq!(
            dispatch_with_session(
                &node,
                "blockchain.estimatefee",
                &json!([6]),
                &mut subscriptions,
                &mut session,
            )
            .unwrap(),
            json!(-1.0)
        );
        assert_eq!(
            dispatch_with_session(
                &node,
                "blockchain.estimatefee",
                &json!([6, "conservative"]),
                &mut subscriptions,
                &mut session,
            )
            .unwrap(),
            json!(-1.0)
        );
        assert!(
            dispatch_with_session(
                &node,
                "blockchain.estimatefee",
                &json!([6, "invalid"]),
                &mut subscriptions,
                &mut session,
            )
            .is_err()
        );
        assert_eq!(
            dispatch_with_session(
                &node,
                "blockchain.relayfee",
                &json!([]),
                &mut subscriptions,
                &mut session,
            )
            .unwrap(),
            json!(0.000001)
        );
        assert!(
            dispatch_with_session(
                &node,
                "server.version",
                &json!(["again", "1.7"]),
                &mut subscriptions,
                &mut session,
            )
            .is_err()
        );
    }

    #[test]
    fn transaction_get_batch_returns_each_requested_transaction() {
        let directory = tempfile::tempdir().unwrap();
        let node = Arc::new(
            Node::open(Config {
                network: Network::Regtest,
                datadir: directory.path().to_owned(),
                p2p_bind: "127.0.0.1:0".parse().unwrap(),
                p2p_binds: Vec::new(),
                rpc_bind: None,
                rpc_binds: Vec::new(),
                rpc_allow_ips: Vec::new(),
                rpc_auth: Vec::new(),
                rpc_cookie_path: None,
                rpc_cookie_permissions: crate::config::RpcCookiePermissions::Owner,
                rpc_server_timeout_secs: 30,
                rpc_threads: 16,
                rpc_work_queue: 64,
                rpc_whitelist: std::collections::HashMap::new(),
                rpc_whitelist_default: false,
                electrum_bind: Some("127.0.0.1:30001".parse().unwrap()),
                rest: false,
                listen: true,
                dnsseed: true,
                force_dns_seed: false,
                onlynet: Vec::new(),
                proxy: None,
                proxy_randomize: false,
                peer_permissions: crate::config::PeerPermissionConfig::default(),
                blocksonly: false,
                private_broadcast: false,
                accept_nonstd_txn: true,
                cjdns_reachable: false,
                prune: 0,
                reindex: false,
                reindex_chainstate: false,
                load_blocks: Vec::new(),
                txindex: false,
                txospenderindex: false,
                max_mempool_mb: 300,
                mempool_expiry_hours: 336,
                coinstatsindex: false,
                blockfilterindex: true,
                peer_block_filters: true,
                persist_mempool: true,
                persist_mempool_v1: false,
                seed_nodes: Vec::new(),
                connect_disabled: false,
                v2_transport: true,
                network_active: true,
                discover: true,
                external_addresses: Vec::new(),
                dns_lookup: true,
                add_nodes: Vec::new(),
                seed_nodes_for_address_fetch: Vec::new(),
                signet_challenge: None,
                max_peers: 1,
                max_upload_target: 0,
                peer_bloom_filters: false,
                peer_timeout_secs: 60,
                connect_timeout_ms: 5_000,
                block_max_weight: 4_000_000,
                block_reserved_weight: 8_000,
                block_version: None,
                block_min_tx_fee_sat_per_kvb: 1,
                min_relay_tx_fee_sat_per_kvb: 100,
                incremental_relay_fee_sat_per_kvb: 100,
                dust_relay_fee_sat_per_kvb: 3_000,
                max_datacarrier_bytes: Some(100_000),
                permit_bare_multisig: true,
                zmq: crate::config::ZmqConfig::default(),
            })
            .unwrap(),
        );
        let hash = node.chain.read().best_hash();
        let block = node.chain.write().block(&hash).unwrap().unwrap();
        let txid = block.txdata[0].compute_txid();
        let features = server_features(&node);
        assert_eq!(features["hosts"]["127.0.0.1"]["tcp_port"], 30001);
        assert_eq!(
            dispatch(
                &node,
                "server.peers.subscribe",
                &json!([]),
                &mut HashMap::new()
            )
            .unwrap(),
            json!([])
        );
        assert!(node.add_peer_address("192.0.2.10:50001".parse().unwrap(), false));
        assert_eq!(
            dispatch(
                &node,
                "server.peers.subscribe",
                &json!([]),
                &mut HashMap::new()
            )
            .unwrap(),
            json!([])
        );
        let result = transaction_get_batch(&node, &json!([[txid.to_string()]])).unwrap();
        assert_eq!(result.as_array().unwrap().len(), 1);
        assert_eq!(
            result[0].as_str().unwrap(),
            chain::transaction_hex(&block.txdata[0])
        );
        let verbose = transaction_get(&node, &json!([txid.to_string(), true])).unwrap();
        assert_eq!(verbose["blockhash"], json!(hash.to_string()));
        assert_eq!(verbose["height"], json!(0));
        assert_eq!(verbose["confirmations"], json!(1));
        assert_eq!(verbose["time"], json!(block.header.time));
        assert_eq!(verbose["blocktime"], json!(block.header.time));
        let side_location = chain::TxLocation {
            block_hash: BlockHash::from_byte_array([1; 32]),
            height: 0,
            transaction_index: 0,
        };
        let side_verbose =
            electrum_transaction_json(&block.txdata[0], Some(&side_location), Some(0), None);
        assert_eq!(side_verbose["confirmations"], json!(0));
        assert!(side_verbose.get("time").is_none());
        assert!(side_verbose.get("blocktime").is_none());
        let merkle = transaction_merkle(&node, &json!([txid.to_string(), 0])).unwrap();
        assert_eq!(merkle["block_height"], 0);
        assert!(transaction_merkle(&node, &json!([txid.to_string(), 1])).is_err());

        let script_hash = "00".repeat(32);
        let mut subscriptions = HashMap::new();
        assert_eq!(
            dispatch(
                &node,
                "blockchain.scripthash.subscribe",
                &json!([script_hash]),
                &mut subscriptions,
            )
            .unwrap(),
            Value::Null
        );
        assert_eq!(
            dispatch(
                &node,
                "blockchain.scripthash.unsubscribe",
                &json!([script_hash]),
                &mut subscriptions,
            )
            .unwrap(),
            Value::Bool(true)
        );

        let script = ScriptBuf::from_bytes(vec![0x51]);
        let script_hex = hex::encode(script.as_bytes());
        assert_eq!(
            dispatch(
                &node,
                "blockchain.scriptpubkey.get_history",
                &json!([script_hex]),
                &mut HashMap::new(),
            )
            .unwrap(),
            json!({"history": []})
        );
        assert_eq!(
            dispatch(
                &node,
                "blockchain.scriptpubkey.get_balance",
                &json!([hex::encode(script.as_bytes())]),
                &mut HashMap::new(),
            )
            .unwrap(),
            json!({"confirmed": 0, "unconfirmed": 0})
        );
        assert_eq!(
            dispatch(
                &node,
                "blockchain.scriptpubkey.listunspent",
                &json!([hex::encode(script.as_bytes())]),
                &mut HashMap::new(),
            )
            .unwrap(),
            json!({"utxos": []})
        );
        assert!(
            dispatch(
                &node,
                "blockchain.transaction.testmempoolaccept",
                &json!([[]]),
                &mut HashMap::new(),
            )
            .is_err()
        );
        assert!(
            dispatch(
                &node,
                "blockchain.transaction.broadcast_package",
                &json!([[]]),
                &mut HashMap::new(),
            )
            .is_err()
        );

        let mut modern_subscriptions = HashMap::new();
        assert_eq!(
            dispatch(
                &node,
                "blockchain.scriptpubkey.subscribe",
                &json!([hex::encode(script.as_bytes())]),
                &mut modern_subscriptions,
            )
            .unwrap(),
            Value::Null
        );
        assert_eq!(
            dispatch(
                &node,
                "blockchain.scriptpubkey.unsubscribe",
                &json!([hex::encode(script.as_bytes())]),
                &mut modern_subscriptions,
            )
            .unwrap(),
            Value::Bool(true)
        );

        let zero_txid = Txid::all_zeros().to_string();
        assert_eq!(
            dispatch(
                &node,
                "blockchain.outpoint.get_status",
                &json!([zero_txid.clone(), 0, "51"]),
                &mut HashMap::new(),
            )
            .unwrap(),
            json!({})
        );
        let mut outpoint_subscriptions = HashMap::new();
        assert_eq!(
            dispatch(
                &node,
                "blockchain.outpoint.subscribe",
                &json!([zero_txid.clone(), 0, "51"]),
                &mut outpoint_subscriptions,
            )
            .unwrap(),
            json!({})
        );
        assert_eq!(
            dispatch(
                &node,
                "blockchain.outpoint.unsubscribe",
                &json!([zero_txid, 0]),
                &mut outpoint_subscriptions,
            )
            .unwrap(),
            Value::Bool(true)
        );
    }

    #[tokio::test]
    async fn electrum_tcp_session_negotiates_and_serves_features() -> Result<()> {
        let directory = tempfile::tempdir()?;
        let node = Node::open(Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            p2p_bind: "127.0.0.1:0".parse().unwrap(),
            p2p_binds: Vec::new(),
            rpc_bind: None,
            rpc_binds: Vec::new(),
            rpc_allow_ips: Vec::new(),
            rpc_auth: Vec::new(),
            rpc_cookie_path: None,
            rpc_cookie_permissions: crate::config::RpcCookiePermissions::Owner,
            rpc_server_timeout_secs: 30,
            rpc_threads: 16,
            rpc_work_queue: 64,
            rpc_whitelist: std::collections::HashMap::new(),
            rpc_whitelist_default: false,
            electrum_bind: None,
            rest: false,
            listen: false,
            dnsseed: false,
            force_dns_seed: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            prune: 0,
            reindex: false,
            reindex_chainstate: false,
            load_blocks: Vec::new(),
            txindex: false,
            txospenderindex: false,
            max_mempool_mb: 300,
            mempool_expiry_hours: 336,
            coinstatsindex: false,
            blockfilterindex: false,
            peer_block_filters: false,
            persist_mempool: false,
            persist_mempool_v1: false,
            seed_nodes: Vec::new(),
            connect_disabled: false,
            v2_transport: true,
            network_active: true,
            discover: true,
            external_addresses: Vec::new(),
            dns_lookup: true,
            add_nodes: Vec::new(),
            seed_nodes_for_address_fetch: Vec::new(),
            signet_challenge: None,
            max_peers: 1,
            max_upload_target: 0,
            peer_bloom_filters: false,
            peer_timeout_secs: 60,
            connect_timeout_ms: 5_000,
            block_max_weight: 4_000_000,
            block_reserved_weight: 8_000,
            block_version: None,
            block_min_tx_fee_sat_per_kvb: 1,
            min_relay_tx_fee_sat_per_kvb: 100,
            incremental_relay_fee_sat_per_kvb: 100,
            dust_relay_fee_sat_per_kvb: 3_000,
            max_datacarrier_bytes: Some(100_000),
            permit_bare_multisig: true,
            zmq: crate::config::ZmqConfig::default(),
        })?;
        let listener = TcpListener::bind("127.0.0.1:0").await?;
        let address = listener.local_addr()?;
        let server_node = node.clone();
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await?;
            handle_client(server_node, stream).await
        });

        let mut client = TcpStream::connect(address).await?;
        client
            .write_all(
                br#"{"jsonrpc":"2.0","id":1,"method":"server.version","params":["test-client","1.4"]}
"#,
            )
            .await?;
        let mut reader = BufReader::new(client);
        let mut line = Vec::new();
        reader.read_until(b'\n', &mut line).await?;
        let response: Value = serde_json::from_slice(&line)?;
        assert_eq!(response["result"], json!([SERVER_NAME, "1.4"]));

        line.clear();
        reader
            .get_mut()
            .write_all(
                br#"{"jsonrpc":"2.0","id":2,"method":"server.features","params":[]}
"#,
            )
            .await?;
        reader.read_until(b'\n', &mut line).await?;
        let response: Value = serde_json::from_slice(&line)?;
        assert_eq!(response["result"]["protocol_min"], json!("1.4"));
        assert_eq!(response["result"]["protocol_max"], json!("1.7"));
        drop(reader);
        server.await??;
        Ok(())
    }
}
