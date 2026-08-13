//! Electrum protocol server.

use std::collections::HashSet;
use std::sync::Arc;

use anyhow::{Context, Result, anyhow, bail};
use bitcoin::consensus::encode::{deserialize, serialize};
use bitcoin::{Transaction, Txid};
use serde_json::{Value, json};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::net::{TcpListener, TcpStream};
use tracing::debug;

use crate::Node;
use crate::chain;

const MAX_LINE_SIZE: usize = 1024 * 1024;

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
    let mut line = Vec::new();
    let mut subscriptions: HashSet<String> = HashSet::new();
    let mut headers_subscribed = false;
    loop {
        line.clear();
        tokio::select! {
            event = events.recv() => {
                let tip = match event {
                    Ok(tip) => tip,
                    Err(tokio::sync::broadcast::error::RecvError::Lagged(_)) => continue,
                    Err(tokio::sync::broadcast::error::RecvError::Closed) => continue,
                };
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
                let statuses = {
                    let chain = node.chain.read();
                    subscriptions
                        .iter()
                        .map(|script_hash| {
                            json!({
                                "jsonrpc": "2.0",
                                "method": "blockchain.scripthash.subscribe",
                                "params": [script_hash, chain.history_status(script_hash)],
                            })
                        })
                        .collect::<Vec<_>>()
                };
                for notification in statuses {
                    let mut encoded = serde_json::to_vec(&notification)?;
                    encoded.push(b'\n');
                    write_half.write_all(&encoded).await?;
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
                let result = dispatch(&node, method, &params, &mut subscriptions);
                if method == "blockchain.headers.subscribe" && result.is_ok() {
                    headers_subscribed = true;
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

fn dispatch(
    node: &Arc<Node>,
    method: &str,
    params: &Value,
    subscriptions: &mut HashSet<String>,
) -> Result<Value> {
    match method {
        "server.version" => Ok(json!(["bitcoind-rs 0.1.0", "1.4"])),
        "server.ping" => Ok(Value::Null),
        "server.banner" => Ok(json!("bitcoind-rs wallet-free Bitcoin node")),
        "server.features" => Ok(json!({
            "server_version": "bitcoind-rs 0.1.0",
            "protocol_min": "1.4",
            "protocol_max": "1.4",
            "genesis_hash": node.chain.read().block_hash(0).expect("genesis exists").to_string(),
            "hash_function": "sha256",
            "pruning": null,
        })),
        "blockchain.headers.subscribe" => {
            let chain = node.chain.read();
            let height = chain.height();
            let header = chain.header(height).expect("tip header exists");
            Ok(json!({"height": height, "hex": hex::encode(serialize(header))}))
        }
        "blockchain.block.header" => block_header(node, params),
        "blockchain.block.headers" => block_headers(node, params),
        "blockchain.scripthash.get_history" => {
            let script_hash = script_hash_param(params, 0)?;
            Ok(json!(
                node.chain
                    .read()
                    .get_history(&script_hash)
                    .into_iter()
                    .map(|entry| json!({"tx_hash": entry.txid.to_string(), "height": entry.height}))
                    .collect::<Vec<_>>()
            ))
        }
        "blockchain.scripthash.get_balance" => {
            let script_hash = script_hash_param(params, 0)?;
            let confirmed = node
                .chain
                .read()
                .get_utxos(&script_hash)
                .into_iter()
                .map(|(_, entry)| entry.output.value.to_sat())
                .sum::<u64>();
            Ok(json!({"confirmed": confirmed, "unconfirmed": 0}))
        }
        "blockchain.scripthash.listunspent" => {
            let script_hash = script_hash_param(params, 0)?;
            Ok(json!(
                node.chain
                    .read()
                    .get_utxos(&script_hash)
                    .into_iter()
                    .map(|(outpoint, entry)| json!({
                        "tx_hash": outpoint.txid.to_string(),
                        "tx_pos": outpoint.vout,
                        "height": entry.height,
                        "value": entry.output.value.to_sat(),
                    }))
                    .collect::<Vec<_>>()
            ))
        }
        "blockchain.scripthash.get_mempool" => {
            let script_hash = script_hash_param(params, 0)?;
            let chain = node.chain.read();
            let mempool = node.mempool.read();
            let mut result = Vec::new();
            for transaction in mempool.transactions() {
                let affects_outputs = transaction.output.iter().any(|output| {
                    chain::electrum_script_hash(&output.script_pubkey) == script_hash
                });
                let affects_inputs = transaction.input.iter().any(|input| {
                    chain.utxo(&input.previous_output).map_or_else(
                        || {
                            mempool
                                .get(&input.previous_output.txid)
                                .and_then(|entry| {
                                    entry
                                        .transaction
                                        .output
                                        .get(input.previous_output.vout as usize)
                                })
                                .is_some_and(|output| {
                                    chain::electrum_script_hash(&output.script_pubkey)
                                        == script_hash
                                })
                        },
                        |entry| {
                            chain::electrum_script_hash(&entry.output.script_pubkey) == script_hash
                        },
                    )
                });
                if affects_outputs || affects_inputs {
                    let txid = transaction.compute_txid();
                    let entry = mempool.get(&txid).expect("mempool iterator is consistent");
                    result.push(
                        json!({"tx_hash": txid.to_string(), "height": 0, "fee": entry.fee_sat}),
                    );
                }
            }
            Ok(json!(result))
        }
        "blockchain.scripthash.subscribe" => {
            let script_hash = script_hash_param(params, 0)?;
            subscriptions.insert(script_hash.clone());
            Ok(node
                .chain
                .read()
                .history_status(&script_hash)
                .map(Value::String)
                .unwrap_or(Value::Null))
        }
        "blockchain.transaction.get" => transaction_get(node, params),
        "blockchain.transaction.get_merkle" => transaction_merkle(node, params),
        "blockchain.transaction.broadcast" => transaction_broadcast(node, params),
        "blockchain.estimatefee" | "blockchain.relayfee" => Ok(json!(0.00001000)),
        "mempool.get_fee_histogram" => Ok(json!([])),
        "server.peers.subscribe" => Ok(json!([])),
        _ => bail!("unsupported Electrum method {method}"),
    }
}

fn block_header(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let height = param::<u32>(params, 0)?;
    let chain = node.chain.read();
    let header = chain
        .header(height)
        .ok_or_else(|| anyhow!("block height out of range"))?;
    Ok(json!(hex::encode(serialize(header))))
}

fn block_headers(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let start = param::<u32>(params, 0)?;
    let count = param::<u32>(params, 1)?.min(2_000);
    let chain = node.chain.read();
    let mut bytes = Vec::with_capacity(count as usize * 80);
    let mut actual = 0u32;
    for height in start..start.saturating_add(count) {
        let Some(header) = chain.header(height) else {
            break;
        };
        bytes.extend_from_slice(&serialize(header));
        actual += 1;
    }
    Ok(json!({"count": actual, "hex": hex::encode(bytes), "max": 2_000}))
}

fn transaction_get(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let txid: Txid = param::<String>(params, 0)?.parse()?;
    let verbose = params.get(1).and_then(Value::as_bool).unwrap_or(false);
    if let Some((transaction, location)) = node.chain.write().transaction(&txid)? {
        if verbose {
            return Ok(json!({
                "txid": txid.to_string(),
                "hash": transaction.compute_wtxid().to_string(),
                "hex": chain::transaction_hex(&transaction),
                "blockhash": location.block_hash.to_string(),
                "height": location.height,
            }));
        }
        return Ok(json!(chain::transaction_hex(&transaction)));
    }
    if let Some(entry) = node.mempool.read().get(&txid) {
        return Ok(json!(chain::transaction_hex(&entry.transaction)));
    }
    bail!("transaction not found")
}

fn transaction_merkle(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let txid: Txid = param::<String>(params, 0)?.parse()?;
    let Some((branch, position, height)) = node.chain.write().merkle_branch(&txid)? else {
        bail!("transaction not found")
    };
    Ok(json!({
        "block_height": height,
        "pos": position,
        "merkle": branch.iter().map(ToString::to_string).collect::<Vec<_>>(),
    }))
}

fn transaction_broadcast(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let raw = param::<String>(params, 0)?;
    let transaction: Transaction = deserialize(&hex::decode(raw)?)?;
    let txid = node.accept_transaction(transaction)?;
    Ok(json!(txid.to_string()))
}

fn script_hash_param(params: &Value, index: usize) -> Result<String> {
    let value = param::<String>(params, index)?;
    if value.len() != 64 || !value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        bail!("invalid Electrum scripthash");
    }
    Ok(value.to_ascii_lowercase())
}

fn param<T: serde::de::DeserializeOwned>(params: &Value, index: usize) -> Result<T> {
    let value = params
        .as_array()
        .and_then(|values| values.get(index))
        .ok_or_else(|| anyhow!("missing parameter {index}"))?;
    Ok(serde_json::from_value(value.clone())?)
}
