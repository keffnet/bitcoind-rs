//! Wallet-free Bitcoin Core-style JSON-RPC over HTTP/1.1.

use std::collections::HashMap;
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use anyhow::{Context, Result, anyhow, bail};
use base64::Engine;
use bitcoin::consensus::encode::{deserialize, serialize};
use bitcoin::hashes::Hash;
use bitcoin::{BlockHash, Network, OutPoint, Transaction, Txid};
use serde_json::{Value, json};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};
use tracing::debug;

use crate::Node;
use crate::chain;
use crate::validation;

const MAX_HTTP_REQUEST: usize = 8 * 1024 * 1024;

pub struct RpcServer {
    node: Arc<Node>,
}

impl RpcServer {
    pub fn new(node: Arc<Node>) -> Self {
        Self { node }
    }

    pub async fn run(self) -> Result<()> {
        let Some(address) = self.node.config.rpc_bind else {
            return std::future::pending::<Result<()>>().await;
        };
        let listener = TcpListener::bind(address)
            .await
            .with_context(|| format!("binding RPC listener {address}"))?;
        loop {
            let (stream, peer) = listener.accept().await?;
            let node = self.node.clone();
            tokio::spawn(async move {
                if let Err(error) = handle_connection(node, stream).await {
                    debug!(%peer, %error, "RPC connection ended");
                }
            });
        }
    }
}

async fn handle_connection(node: Arc<Node>, mut stream: TcpStream) -> Result<()> {
    stream.set_nodelay(true)?;
    let request = read_http_request(&mut stream).await?;
    let response = match request {
        Some(request) => {
            if !authorized(&node, &request.headers) {
                stream
                    .write_all(b"HTTP/1.1 401 Unauthorized\r\nContent-Length: 0\r\nConnection: close\r\n\r\n")
                    .await?;
                stream.shutdown().await?;
                return Ok(());
            }
            dispatch_json_rpc(&node, &request.body)
        }
        None => {
            json!({"result": null, "error": {"code": -32700, "message": "empty request"}, "id": null})
        }
    };
    let body = serde_json::to_vec(&response)?;
    let header = format!(
        "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        body.len()
    );
    stream.write_all(header.as_bytes()).await?;
    stream.write_all(&body).await?;
    stream.shutdown().await?;
    Ok(())
}

struct HttpRequest {
    headers: String,
    body: Vec<u8>,
}

async fn read_http_request(stream: &mut TcpStream) -> Result<Option<HttpRequest>> {
    let mut bytes = Vec::new();
    let mut chunk = [0u8; 4096];
    let header_end;
    loop {
        let read = stream.read(&mut chunk).await?;
        if read == 0 {
            return Ok(None);
        }
        bytes.extend_from_slice(&chunk[..read]);
        if bytes.len() > MAX_HTTP_REQUEST {
            bail!("HTTP request exceeds limit");
        }
        if let Some(position) = bytes.windows(4).position(|window| window == b"\r\n\r\n") {
            header_end = position + 4;
            break;
        }
    }
    let headers = std::str::from_utf8(&bytes[..header_end])?.to_owned();
    let content_length = headers
        .lines()
        .find_map(|line| {
            line.strip_prefix("Content-Length:")
                .or_else(|| line.strip_prefix("content-length:"))
                .and_then(|value| value.trim().parse::<usize>().ok())
        })
        .unwrap_or(0);
    if header_end.saturating_add(content_length) > MAX_HTTP_REQUEST {
        bail!("HTTP request body exceeds limit");
    }
    while bytes.len() < header_end + content_length {
        let read = stream.read(&mut chunk).await?;
        if read == 0 {
            bail!("truncated HTTP request body");
        }
        bytes.extend_from_slice(&chunk[..read]);
    }
    Ok(Some(HttpRequest {
        headers,
        body: bytes[header_end..header_end + content_length].to_vec(),
    }))
}

fn authorized(node: &Arc<Node>, headers: &str) -> bool {
    let Some(cookie) = node.rpc_cookie.as_deref() else {
        return true;
    };
    let expected = format!(
        "Basic {}",
        base64::engine::general_purpose::STANDARD.encode(cookie.as_bytes())
    );
    headers.lines().any(|line| {
        line.strip_prefix("Authorization:")
            .or_else(|| line.strip_prefix("authorization:"))
            .map(|value| value.trim() == expected)
            .unwrap_or(false)
    })
}

fn dispatch_json_rpc(node: &Arc<Node>, body: &[u8]) -> Value {
    let request: Value = match serde_json::from_slice(body) {
        Ok(value) => value,
        Err(error) => {
            return json!({"result": null, "error": {"code": -32700, "message": error.to_string()}, "id": null});
        }
    };
    let id = request.get("id").cloned().unwrap_or(Value::Null);
    let method = request.get("method").and_then(Value::as_str).unwrap_or("");
    let params = request
        .get("params")
        .cloned()
        .unwrap_or_else(|| Value::Array(Vec::new()));
    match dispatch_method(node, method, &params) {
        Ok(result) => json!({"result": result, "error": null, "id": id}),
        Err(error) => json!({"result": null, "error": rpc_error(&error), "id": id}),
    }
}

fn dispatch_method(node: &Arc<Node>, method: &str, params: &Value) -> Result<Value> {
    match method {
        "getblockchaininfo" => get_blockchain_info(node),
        "getblockcount" => Ok(json!(node.chain.read().height())),
        "getbestblockhash" => Ok(json!(node.chain.read().best_hash().to_string())),
        "getblockhash" => {
            let height = param::<u32>(params, 0)?;
            node.chain
                .read()
                .block_hash(height)
                .map(|hash| json!(hash.to_string()))
                .ok_or_else(|| anyhow!("Block height out of range"))
        }
        "getblockheader" => get_block_header(node, params),
        "getblock" => get_block(node, params),
        "getblockstats" => get_block_stats(node, params),
        "getrawtransaction" => get_raw_transaction(node, params),
        "decoderawtransaction" => decode_raw_transaction(params),
        "sendrawtransaction" => send_raw_transaction(node, params),
        "submitblock" => submit_block(node, params),
        "getblocktemplate" => get_block_template(node),
        "testmempoolaccept" => test_mempool_accept(node, params),
        "verifychain" => Ok(Value::Bool(true)),
        "getmemoryinfo" => {
            let mempool = node.mempool.read();
            Ok(json!({
                "used": mempool.bytes(),
                "free": 0,
                "total": mempool.max_bytes(),
                "locked": {"used": 0, "free": 0, "total": 0, "locked": 0},
            }))
        }
        "gettxout" => get_txout(node, params),
        "getmempoolinfo" => {
            let mempool = node.mempool.read();
            Ok(json!({
                "loaded": true,
                "size": mempool.len(),
                "bytes": mempool.bytes(),
                "usage": mempool.bytes(),
                "maxmempool": mempool.max_bytes(),
                "mempoolminfee": 0.00001000,
                "minrelaytxfee": 0.00001000,
            }))
        }
        "getrawmempool" => {
            let verbose = params.get(0).and_then(Value::as_bool).unwrap_or(false);
            let height = node.chain.read().height();
            let mempool = node.mempool.read();
            let order = mempool.transaction_order();
            if verbose {
                Ok(Value::Object(
                    order
                        .iter()
                        .filter_map(|txid| mempool.get(txid).map(|entry| (txid, entry)))
                        .map(|(txid, entry)| {
                            let depends = entry
                                .transaction
                                .input
                                .iter()
                                .filter_map(|input| {
                                    mempool
                                        .get(&input.previous_output.txid)
                                        .map(|_| input.previous_output.txid.to_string())
                                })
                                .collect::<Vec<_>>();
                            (
                                txid.to_string(),
                                json!({
                                    "vsize": entry.vsize,
                                    "weight": entry.transaction.weight().to_wu(),
                                    "fee": sat_to_btc(entry.fee_sat),
                                    "time": entry.added_at,
                                    "height": height,
                                    "depends": depends,
                                }),
                            )
                        })
                        .collect(),
                ))
            } else {
                Ok(json!(
                    order
                        .into_iter()
                        .map(|txid| txid.to_string())
                        .collect::<Vec<_>>()
                ))
            }
        }
        "getmempoolentry" => {
            let txid: Txid = param::<String>(params, 0)?.parse()?;
            let height = node.chain.read().height();
            let mempool = node.mempool.read();
            let entry = mempool
                .get(&txid)
                .ok_or_else(|| anyhow!("Transaction not in mempool"))?;
            Ok(json!({
                "vsize": entry.vsize,
                "weight": entry.transaction.weight().to_wu(),
                "fee": sat_to_btc(entry.fee_sat),
                "time": entry.added_at,
                "height": height,
                "descendantcount": 1,
                "ancestorcount": 1,
            }))
        }
        "gettxoutsetinfo" => {
            let chain = node.chain.read();
            let (transactions, outputs, total) = chain.utxo_stats();
            Ok(json!({
                "height": chain.height(),
                "bestblock": chain.best_hash().to_string(),
                "transactions": transactions,
                "txouts": outputs,
                "total_amount": sat_to_btc(total),
            }))
        }
        "getchaintips" => {
            let chain = node.chain.read();
            Ok(json!(
                chain
                    .chain_tips()
                    .into_iter()
                    .map(|tip| json!({
                        "height": tip.height,
                        "hash": tip.hash.to_string(),
                        "branchlen": tip.branch_len,
                        "status": tip.status,
                    }))
                    .collect::<Vec<_>>()
            ))
        }
        "getnetworkinfo" => Ok(json!({
            "version": 310100,
            "subversion": "/bitcoind-rs:0.1.0/",
            "protocolversion": 70016,
            "connections": node.peer_count(),
            "networkactive": true,
            "networks": [{
                "name": network_name(node.config.network),
                "limited": false,
                "reachable": true,
                "proxy": "",
                "proxy_randomize_credentials": false,
            }],
            "relayfee": 0.00001000,
            "incrementalfee": 0.00001000,
        })),
        "estimatesmartfee" => Ok(
            json!({"feerate": 0.00001000, "blocks": params.get(0).and_then(Value::as_u64).unwrap_or(6)}),
        ),
        "getdifficulty" => Ok(json!(
            node.chain
                .read()
                .header(node.chain.read().height())
                .map(|header| header.difficulty_float())
                .unwrap_or(1.0)
        )),
        "getconnectioncount" => Ok(json!(node.peer_count())),
        "uptime" => Ok(json!(node.started_at.elapsed().as_secs())),
        _ => bail!("Method not found"),
    }
}

fn get_blockchain_info(node: &Arc<Node>) -> Result<Value> {
    let chain = node.chain.read();
    let tip = chain.tip();
    let header_tip = chain.best_header_tip();
    let header = chain.header(tip.height).expect("tip header exists");
    Ok(json!({
        "chain": network_name(chain.network),
        "blocks": tip.height,
        "headers": header_tip.height,
        "bestblockhash": tip.hash.to_string(),
        "chainwork": format!("{:064x}", tip.work),
        "difficulty": header.difficulty_float(),
        "time": header.time,
        "mediantime": chain.median_time_past_value(),
        "verificationprogress": if header_tip.height == 0 { 1.0 } else { tip.height as f64 / header_tip.height as f64 },
        "initialblockdownload": tip.height < header_tip.height,
        "pruned": false,
        "size_on_disk": std::fs::metadata(chain.store.path()).map(|m| m.len()).unwrap_or(0),
    }))
}

fn get_block_header(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let hash: BlockHash = param::<String>(params, 0)?.parse()?;
    let verbose = params.get(1).and_then(Value::as_bool).unwrap_or(true);
    let chain = node.chain.read();
    let height = chain
        .block_height_by_hash(&hash)
        .ok_or_else(|| anyhow!("Block not found"))?;
    let header = chain
        .header_by_hash(&hash)
        .expect("header index is consistent");
    if !verbose {
        return Ok(json!(hex::encode(serialize(&header))));
    }
    let confirmations = if chain.is_active_block(&hash) {
        chain.height().saturating_sub(height) as i64 + 1
    } else {
        -1
    };
    Ok(json!({
        "hash": hash.to_string(),
        "confirmations": confirmations,
        "height": height,
        "version": header.version.to_consensus(),
        "merkleroot": header.merkle_root.to_string(),
        "time": header.time,
        "mediantime": header.time,
        "nonce": header.nonce,
        "bits": format!("{:08x}", header.bits.to_consensus()),
        "difficulty": header.difficulty_float(),
        "chainwork": format!(
            "{:064x}",
            chain
                .chain_work_by_hash(&hash)
                .unwrap_or_else(|| chain.tip().work)
        ),
        "nTx": 0,
        "previousblockhash": (height > 0).then(|| header.prev_blockhash.to_string()),
    }))
}

fn get_block(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let hash: BlockHash = param::<String>(params, 0)?.parse()?;
    let verbosity = params.get(1).and_then(Value::as_u64).unwrap_or(1);
    let mut chain = node.chain.write();
    let block = chain
        .block(&hash)?
        .ok_or_else(|| anyhow!("Block not found"))?;
    if verbosity == 0 {
        return Ok(json!(hex::encode(serialize(&block))));
    }
    let height = chain.block_height_by_hash(&hash).unwrap_or(0);
    let confirmations = if chain.is_active_block(&hash) {
        chain.height().saturating_sub(height) as i64 + 1
    } else {
        -1
    };
    let txs = if verbosity >= 2 {
        block
            .txdata
            .iter()
            .map(|tx| rpc_transaction(tx, None, None))
            .collect::<Vec<_>>()
    } else {
        block
            .txdata
            .iter()
            .map(Transaction::compute_txid)
            .map(|txid| json!(txid.to_string()))
            .collect()
    };
    Ok(json!({
        "hash": hash.to_string(),
        "confirmations": confirmations,
        "height": height,
        "version": block.header.version.to_consensus(),
        "merkleroot": block.header.merkle_root.to_string(),
        "time": block.header.time,
        "nonce": block.header.nonce,
        "bits": format!("{:08x}", block.header.bits.to_consensus()),
        "difficulty": block.header.difficulty_float(),
        "chainwork": format!(
            "{:064x}",
            chain
                .chain_work_by_hash(&hash)
                .unwrap_or_else(|| chain.tip().work)
        ),
        "nTx": block.txdata.len(),
        "size": serialize(&block).len(),
        "weight": block.weight().to_wu(),
        "tx": txs,
        "previousblockhash": (height > 0).then(|| block.header.prev_blockhash.to_string()),
    }))
}

fn get_block_stats(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let selector = params
        .as_array()
        .and_then(|values| values.first())
        .ok_or_else(|| anyhow!("missing block selector"))?;
    let hash = if let Some(hash) = selector.as_str() {
        hash.parse::<BlockHash>()?
    } else {
        let height = selector
            .as_u64()
            .ok_or_else(|| anyhow!("block selector must be a hash or height"))?
            as u32;
        node.chain
            .read()
            .block_hash(height)
            .ok_or_else(|| anyhow!("block height out of range"))?
    };
    let mut chain = node.chain.write();
    let block = chain
        .block(&hash)?
        .ok_or_else(|| anyhow!("Block not found"))?;
    let height = (0..=chain.height()).find(|height| chain.block_hash(*height) == Some(hash));
    let mut total_out = 0u64;
    for transaction in &block.txdata {
        total_out = total_out.saturating_add(
            transaction
                .output
                .iter()
                .map(|output| output.value.to_sat())
                .sum::<u64>(),
        );
    }
    Ok(json!({
        "blockhash": hash.to_string(),
        "height": height,
        "txs": block.txdata.len(),
        "time": block.header.time,
        "mediantime": chain.median_time_past_value(),
        "size": serialize(&block).len(),
        "total_size": serialize(&block).len(),
        "weight": block.weight().to_wu(),
        "total_out": sat_to_btc(total_out),
        "subsidy": height.map(|height| sat_to_btc(validation::block_subsidy(height))),
        "total_fee": null,
    }))
}

fn get_raw_transaction(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let txid: Txid = param::<String>(params, 0)?.parse()?;
    let verbose = params.get(1).and_then(Value::as_bool).unwrap_or(false);
    let mut chain = node.chain.write();
    let found = chain.transaction(&txid)?;
    let (transaction, location) = if let Some(found) = found {
        found
    } else if let Some(entry) = node.mempool.read().get(&txid) {
        (
            entry.transaction.clone(),
            chain::TxLocation {
                block_hash: BlockHash::all_zeros(),
                height: 0,
                transaction_index: 0,
            },
        )
    } else {
        bail!("No such mempool or blockchain transaction");
    };
    if !verbose {
        return Ok(json!(chain::transaction_hex(&transaction)));
    }
    let blockhash =
        (location.block_hash != BlockHash::all_zeros()).then(|| location.block_hash.to_string());
    let confirmations = blockhash.as_ref().map(|_| {
        if chain.is_active_block(&location.block_hash) {
            chain.height().saturating_sub(location.height) + 1
        } else {
            0
        }
    });
    Ok(rpc_transaction(
        &transaction,
        blockhash.as_deref(),
        confirmations,
    ))
}

fn decode_raw_transaction(params: &Value) -> Result<Value> {
    let bytes = hex::decode(param::<String>(params, 0)?)?;
    let transaction: Transaction = deserialize(&bytes)?;
    Ok(rpc_transaction(&transaction, None, None))
}

fn send_raw_transaction(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let bytes = hex::decode(param::<String>(params, 0)?)?;
    let transaction: Transaction = deserialize(&bytes)?;
    let txid = node.accept_transaction(transaction)?;
    Ok(json!(txid.to_string()))
}

fn submit_block(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let bytes = hex::decode(param::<String>(params, 0)?)?;
    let block: bitcoin::Block = deserialize(&bytes)?;
    let hash = block.block_hash();
    let result = node.connect_block(block);
    match result {
        Ok(_) => Ok(Value::Null),
        Err(error) => {
            debug!(%hash, %error, "submitblock rejected");
            Ok(json!(error.to_string()))
        }
    }
}

fn get_block_template(node: &Arc<Node>) -> Result<Value> {
    let chain = node.chain.read();
    let tip = chain.tip();
    let parent = chain.header(tip.height).expect("tip header exists");
    let height = tip.height + 1;
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs() as u32;
    let curtime = now.max(parent.time.saturating_add(1));
    let bits = chain.next_bits(curtime);
    let mempool = node.mempool.read();
    let mut fees = 0u64;
    let mut weight = 0u64;
    let order = mempool.transaction_order();
    let positions: HashMap<Txid, usize> = order
        .iter()
        .enumerate()
        .map(|(index, txid)| (*txid, index + 1))
        .collect();
    let transactions = order
        .iter()
        .filter_map(|txid| mempool.get(txid).map(|entry| (txid, entry)))
        .map(|(txid, entry)| {
            let transaction = &entry.transaction;
            let wtxid = transaction.compute_wtxid();
            fees = fees.saturating_add(entry.fee_sat);
            weight = weight.saturating_add(transaction.weight().to_wu());
            let depends = transaction
                .input
                .iter()
                .filter_map(|input| positions.get(&input.previous_output.txid))
                .copied()
                .collect::<Vec<_>>();
            json!({
                "data": hex::encode(serialize(transaction)),
                "txid": txid.to_string(),
                "hash": wtxid.to_string(),
                "depends": depends,
                "fee": entry.fee_sat,
                "sigops": transaction.total_sigop_cost(|outpoint| {
                    chain
                        .utxo(outpoint)
                        .map(|entry| entry.output.clone())
                        .or_else(|| {
                            mempool
                                .get(&outpoint.txid)
                                .and_then(|entry| entry.transaction.output.get(outpoint.vout as usize))
                                .cloned()
                        })
                }),
                "weight": transaction.weight().to_wu(),
            })
        })
        .collect::<Vec<_>>();
    let coinbase_value = validation::block_subsidy(height).saturating_add(fees);
    Ok(json!({
        "capabilities": ["proposal", "longpoll", "coinbasetxn", "coinbasevalue"],
        "version": 0x20000000u32,
        "rules": ["csv", "segwit", "taproot"],
        "vbavailable": {},
        "vbrequired": 0,
        "previousblockhash": tip.hash.to_string(),
        "transactions": transactions,
        "coinbaseaux": {"flags": ""},
        "coinbasevalue": coinbase_value,
        "target": format!("{:064x}", bitcoin::pow::Target::from_compact(bitcoin::pow::CompactTarget::from_consensus(bits))),
        "mintime": parent.time.saturating_add(1),
        "curtime": curtime,
        "mutable": ["time", "transactions", "prevblock"],
        "noncerange": "00000000ffffffff",
        "sigoplimit": 80_000,
        "sizelimit": 4_000_000,
        "weightlimit": 4_000_000,
        "longpollid": format!("{}:{}", tip.hash, weight),
        "height": height,
        "bits": format!("{:08x}", bits),
    }))
}

fn test_mempool_accept(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let transactions = params
        .as_array()
        .and_then(|values| values.first())
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("testmempoolaccept expects an array of hex transactions"))?;
    let chain = node.chain.read();
    let mut candidate = node.mempool.read().clone();
    let mut result = Vec::with_capacity(transactions.len());
    for raw in transactions {
        let raw = raw
            .as_str()
            .ok_or_else(|| anyhow!("transaction must be hex"))?;
        let transaction: Transaction = match hex::decode(raw)
            .ok()
            .and_then(|bytes| deserialize(&bytes).ok())
        {
            Some(transaction) => transaction,
            None => {
                result.push(json!({"txid": Value::Null, "allowed": false, "reject-reason": "decode failed"}));
                continue;
            }
        };
        let txid = transaction.compute_txid();
        match candidate.accept(transaction.clone(), &chain) {
            Ok(_) => result.push(json!({
                "txid": txid.to_string(),
                "wtxid": transaction.compute_wtxid().to_string(),
                "allowed": true,
                "vsize": transaction.vsize(),
                "fees": {"base": 0.0},
            })),
            Err(error) => result.push(json!({
                "txid": txid.to_string(),
                "wtxid": transaction.compute_wtxid().to_string(),
                "allowed": false,
                "reject-reason": error.to_string(),
            })),
        }
    }
    Ok(json!(result))
}

fn get_txout(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let txid: Txid = param::<String>(params, 0)?.parse()?;
    let vout = param::<u32>(params, 1)?;
    let include_mempool = params.get(2).and_then(Value::as_bool).unwrap_or(true);
    let chain = node.chain.read();
    let outpoint = OutPoint::new(txid, vout);
    let mempool = include_mempool.then(|| node.mempool.read());
    if let Some(entry) = chain.utxo(&outpoint) {
        if mempool
            .as_ref()
            .is_some_and(|pool| pool.is_spent(&outpoint))
        {
            return Ok(Value::Null);
        }
        return Ok(json!({
            "bestblock": chain.best_hash().to_string(),
            "confirmations": chain.height().saturating_sub(entry.height) + 1,
            "value": sat_to_btc(entry.output.value.to_sat()),
            "scriptPubKey": script_json(&entry.output.script_pubkey),
            "coinbase": entry.coinbase,
        }));
    }
    if let Some(mempool) = mempool {
        if mempool.is_spent(&outpoint) {
            return Ok(Value::Null);
        }
        if let Some(entry) = mempool.get(&txid)
            && let Some(output) = entry.transaction.output.get(vout as usize)
        {
            return Ok(json!({
                "bestblock": chain.best_hash().to_string(),
                "confirmations": 0,
                "value": sat_to_btc(output.value.to_sat()),
                "scriptPubKey": script_json(&output.script_pubkey),
                "coinbase": false,
            }));
        }
    }
    drop(chain);
    Ok(Value::Null)
}

fn rpc_transaction(
    transaction: &Transaction,
    blockhash: Option<&str>,
    confirmations: Option<u32>,
) -> Value {
    let vin = transaction
        .input
        .iter()
        .map(|input| {
            if input.previous_output.is_null() {
                json!({"coinbase": hex::encode(input.script_sig.as_bytes()), "sequence": input.sequence.to_consensus_u32()})
            } else {
                json!({
                    "txid": input.previous_output.txid.to_string(),
                    "vout": input.previous_output.vout,
                    "scriptSig": {"asm": input.script_sig.to_asm_string(), "hex": hex::encode(input.script_sig.as_bytes())},
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
                "value": sat_to_btc(output.value.to_sat()),
                "n": index,
                "scriptPubKey": script_json(&output.script_pubkey),
            })
        })
        .collect::<Vec<_>>();
    let mut value = json!({
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
    if let Some(blockhash) = blockhash {
        value["blockhash"] = json!(blockhash);
    }
    if let Some(confirmations) = confirmations {
        value["confirmations"] = json!(confirmations);
    }
    value
}

fn script_json(script: &bitcoin::Script) -> Value {
    json!({"asm": script.to_asm_string(), "hex": hex::encode(script.as_bytes())})
}

fn param<T: serde::de::DeserializeOwned>(params: &Value, index: usize) -> Result<T> {
    let value = params
        .as_array()
        .and_then(|values| values.get(index))
        .ok_or_else(|| anyhow!("missing parameter {index}"))?;
    Ok(serde_json::from_value(value.clone())?)
}

fn rpc_error(error: &anyhow::Error) -> Value {
    json!({"code": -1, "message": error.to_string()})
}

fn sat_to_btc(satoshis: u64) -> f64 {
    satoshis as f64 / 100_000_000.0
}

fn network_name(network: Network) -> &'static str {
    match network {
        Network::Bitcoin => "main",
        Network::Testnet => "test",
        Network::Signet => "signet",
        Network::Regtest => "regtest",
        Network::Testnet4 => "testnet4",
    }
}
