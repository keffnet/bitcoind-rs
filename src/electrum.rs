//! Electrum protocol server.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use anyhow::{Context, Result, anyhow, bail};
use bitcoin::consensus::encode::{deserialize, serialize};
use bitcoin::hashes::{Hash, sha256d};
use bitcoin::{BlockHash, OutPoint, ScriptBuf, Transaction, TxOut, Txid};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::net::{TcpListener, TcpStream};
use tracing::debug;

use crate::Node;
use crate::chain;

const MAX_LINE_SIZE: usize = 1024 * 1024;

#[derive(Clone, Debug)]
enum Subscription {
    Scripthash(String),
    Scriptpubkey(String),
    Outpoint(OutPoint),
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
                send_status_notifications(&node, &subscriptions, &mut write_half).await?;
            }
            event = mempool_events.recv() => {
                match event {
                    Ok(_) | Err(tokio::sync::broadcast::error::RecvError::Lagged(_)) => {
                        send_status_notifications(&node, &subscriptions, &mut write_half).await?;
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
    subscriptions: &mut HashMap<String, Subscription>,
) -> Result<Value> {
    match method {
        "server.version" => Ok(json!(["bitcoind-rs 0.1.0", "1.4"])),
        "server.ping" => Ok(Value::Null),
        "server.banner" => Ok(json!("bitcoind-rs wallet-free Bitcoin node")),
        "server.features" => Ok(server_features(node)),
        "blockchain.headers.subscribe" => {
            let chain = node.chain.read();
            let height = chain.height();
            let header = chain.header(height).expect("tip header exists");
            Ok(json!({"height": height, "hex": hex::encode(serialize(header))}))
        }
        "blockchain.block.header" | "blockchain.block.get_header" => block_header(node, params),
        "blockchain.block.headers" => block_headers(node, params),
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
            subscriptions.insert(
                format!("scripthash:{script_hash}"),
                Subscription::Scripthash(script_hash.clone()),
            );
            Ok(history_status_for_script(node, &script_hash)
                .map(Value::String)
                .unwrap_or(Value::Null))
        }
        "blockchain.scripthash.unsubscribe" => {
            let script_hash = script_hash_param(params, 0)?;
            Ok(Value::Bool(
                subscriptions
                    .remove(&format!("scripthash:{script_hash}"))
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
            subscriptions.insert(
                format!("scriptpubkey:{script_hash}"),
                Subscription::Scriptpubkey(script_hash.clone()),
            );
            Ok(history_status_for_script(node, &script_hash)
                .map(Value::String)
                .unwrap_or(Value::Null))
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
        "blockchain.outpoint.subscribe" => {
            let outpoint = outpoint_param(params)?;
            let _ = scriptpubkey_param(params, 2)?;
            subscriptions.insert(
                outpoint_subscription_key(&outpoint),
                Subscription::Outpoint(outpoint),
            );
            outpoint_status(node, &outpoint)
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
        "blockchain.estimatefee" | "blockchain.relayfee" => Ok(json!(0.00001000)),
        "mempool.get_fee_histogram" => {
            let mempool = node.mempool.read();
            Ok(fee_histogram(&mempool))
        }
        "server.peers.subscribe" => Ok(server_peers(node)),
        _ => bail!("unsupported Electrum method {method}"),
    }
}

fn server_features(node: &Arc<Node>) -> Value {
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
    json!({
        "hosts": Value::Object(hosts),
        "server_version": "bitcoind-rs 0.1.0",
        "protocol_min": "1.4",
        "protocol_max": "1.4",
        "genesis_hash": chain.block_hash(0).expect("genesis exists").to_string(),
        "hash_function": "sha256",
        "pruning": null,
    })
}

fn server_peers(node: &Arc<Node>) -> Value {
    let mut peers = node.known_addresses();
    peers.sort_by_key(|peer| peer.address);
    json!(
        peers
            .into_iter()
            .map(|peer| {
                let ip = peer.address.ip().to_string();
                json!([
                    ip,
                    peer.address.ip().to_string(),
                    ["v1.4", format!("t{}", peer.address.port())]
                ])
            })
            .collect::<Vec<_>>()
    )
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
    let mut result = Vec::new();
    for txid in mempool.transaction_order() {
        let Some(entry) = mempool.get(&txid) else {
            continue;
        };
        let transaction = &entry.transaction;
        let affects_outputs = transaction
            .output
            .iter()
            .any(|output| chain::electrum_script_hash(&output.script_pubkey) == script_hash);
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
                            chain::electrum_script_hash(&output.script_pubkey) == script_hash
                        })
                },
                |entry| chain::electrum_script_hash(&entry.output.script_pubkey) == script_hash,
            )
        });
        if affects_outputs || affects_inputs {
            result.push(json!({
                "tx_hash": txid.to_string(),
                "height": mempool_transaction_height(transaction, &mempool),
                "fee": entry.fee_sat,
            }));
        }
    }
    result
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

    if let Some((transaction, location)) = chain.transaction(&outpoint.txid)? {
        if transaction.output.get(outpoint.vout as usize).is_some() {
            status.insert("funder_height".to_owned(), json!(location.height));
        }
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
    let checkpoint = params.get(1).and_then(Value::as_u64).unwrap_or(0);
    let checkpoint = u32::try_from(checkpoint).map_err(|_| anyhow!("checkpoint is too large"))?;
    let chain = node.chain.read();
    let header = chain
        .header(height)
        .ok_or_else(|| anyhow!("block height out of range"))?;
    if checkpoint == 0 {
        return Ok(json!(hex::encode(serialize(header))));
    }
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

fn block_headers(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let start = param::<u32>(params, 0)?;
    let count = param::<u32>(params, 1)?.min(2_000);
    let checkpoint = params.get(2).and_then(Value::as_u64).unwrap_or(0);
    let checkpoint = u32::try_from(checkpoint).map_err(|_| anyhow!("checkpoint is too large"))?;
    if checkpoint != 0 && count != 0 && start.saturating_add(count.saturating_sub(1)) > checkpoint {
        bail!("checkpoint height is below the requested header range")
    }
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
    let mut result = json!({"count": actual, "hex": hex::encode(bytes), "max": 2_000});
    if checkpoint != 0 && actual != 0 {
        let last_height = start + actual - 1;
        let (branch, root) = header_merkle_proof(&chain, last_height, checkpoint)?;
        result["branch"] = json!(branch.iter().map(ToString::to_string).collect::<Vec<_>>());
        result["root"] = json!(root.to_string());
    }
    Ok(result)
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
    let verbose = params.get(1).and_then(Value::as_bool).unwrap_or(false);
    if let Some((transaction, location)) = node.chain.write().transaction(&txid)? {
        if verbose {
            let chain = node.chain.read();
            let time = chain
                .header_by_hash(&location.block_hash)
                .map(|header| header.time);
            let confirmations = chain
                .is_active_block(&location.block_hash)
                .then(|| chain.height().saturating_sub(location.height) + 1);
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
    let verbose = params.get(1).and_then(Value::as_bool).unwrap_or(false);
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
    let include_merkle = params.get(2).and_then(Value::as_bool).unwrap_or(false);
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

async fn send_status_notifications(
    node: &Arc<Node>,
    subscriptions: &HashMap<String, Subscription>,
    writer: &mut tokio::net::tcp::OwnedWriteHalf,
) -> Result<()> {
    for subscription in subscriptions.values() {
        let notification = match subscription {
            Subscription::Scripthash(script_hash) => json!({
                "jsonrpc": "2.0",
                "method": "blockchain.scripthash.subscribe",
                "params": [script_hash, history_status_for_script(node, script_hash)],
            }),
            Subscription::Scriptpubkey(script_hash) => json!({
                "jsonrpc": "2.0",
                "method": "blockchain.scriptpubkey.subscribe",
                "params": [script_hash, history_status_for_script(node, script_hash)],
            }),
            Subscription::Outpoint(outpoint) => json!({
                "jsonrpc": "2.0",
                "method": "blockchain.outpoint.subscribe",
                "params": [
                    outpoint.txid.to_string(),
                    outpoint.vout,
                    outpoint_status(node, outpoint)?,
                ],
            }),
        };
        let mut encoded = serde_json::to_vec(&notification)?;
        encoded.push(b'\n');
        writer.write_all(&encoded).await?;
    }
    Ok(())
}

fn history_for_script(node: &Arc<Node>, script_hash: &str) -> Vec<Value> {
    let records = history_records_for_script(node, script_hash);
    let mempool = node.mempool.read();
    records
        .into_iter()
        .map(|(txid, height)| {
            let mut result = json!({"tx_hash": txid.to_string(), "height": height});
            if height == 0
                && let Some(entry) = mempool.get(&txid)
            {
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
    for txid in mempool.transaction_order() {
        let Some(entry) = mempool.get(&txid) else {
            continue;
        };
        if transaction_affects_script(&entry.transaction, &chain, &mempool, script_hash)
            && seen.insert(txid)
        {
            records.push((txid, 0));
        }
    }
    records
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
    use bitcoin::Network;
    use bitcoin::hashes::Hash;

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
    fn transaction_get_batch_returns_each_requested_transaction() {
        let directory = tempfile::tempdir().unwrap();
        let node = Arc::new(
            Node::open(Config {
                network: Network::Regtest,
                datadir: directory.path().to_owned(),
                p2p_bind: "127.0.0.1:0".parse().unwrap(),
                rpc_bind: None,
                electrum_bind: Some("127.0.0.1:30001".parse().unwrap()),
                rest: false,
                seed_nodes: Vec::new(),
                signet_challenge: None,
                max_peers: 1,
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
            json!([["192.0.2.10", "192.0.2.10", ["v1.4", "t50001"]]])
        );
        let result = transaction_get_batch(&node, &json!([[txid.to_string()]])).unwrap();
        assert_eq!(result.as_array().unwrap().len(), 1);
        assert_eq!(
            result[0].as_str().unwrap(),
            chain::transaction_hex(&block.txdata[0])
        );
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
}
