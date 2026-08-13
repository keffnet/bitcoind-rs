//! Wallet-free Bitcoin Core-style JSON-RPC over HTTP/1.1.

use std::collections::HashMap;
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use anyhow::{Context, Result, anyhow, bail};
use base64::Engine;
use bitcoin::consensus::encode::{deserialize, serialize};
use bitcoin::hashes::Hash;
use bitcoin::{BlockHash, Network, OutPoint, Transaction, TxOut, Txid};
use serde_json::{Value, json};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};
use tracing::debug;

use crate::Node;
use crate::chain;
use crate::mempool::Mempool;
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
    if let Some(batch) = request.as_array() {
        if batch.is_empty() {
            return json!({"result": null, "error": {"code": -32600, "message": "empty batch"}, "id": null});
        }
        return Value::Array(
            batch
                .iter()
                .map(|request| dispatch_request(node, request))
                .collect(),
        );
    }
    dispatch_request(node, &request)
}

fn dispatch_request(node: &Arc<Node>, request: &Value) -> Value {
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
        "stop" => {
            node.request_shutdown();
            Ok(json!("bitcoind stopping"))
        }
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
        "getchaintxstats" => get_chain_tx_stats(node, params),
        "getnetworkhashps" => get_network_hash_ps(node, params),
        "gettxoutproof" => get_txout_proof(node, params),
        "verifytxoutproof" => verify_txout_proof(params),
        "submitheader" => submit_header(node, params),
        "getrawtransaction" => get_raw_transaction(node, params),
        "decoderawtransaction" => decode_raw_transaction(params),
        "sendrawtransaction" => send_raw_transaction(node, params),
        "submitblock" => submit_block(node, params),
        "getblocktemplate" => get_block_template(node),
        "getmininginfo" => get_mining_info(node),
        "testmempoolaccept" => test_mempool_accept(node, params),
        "verifychain" => {
            let depth = params.get(1).and_then(Value::as_u64).unwrap_or(0) as u32;
            node.chain.write().verify_active_chain(depth)?;
            Ok(Value::Bool(true))
        }
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
        "gettxspendingprevout" => get_tx_spending_prevout(node, params),
        "getmempoolinfo" => {
            let mempool = node.mempool.read();
            let total_fee = mempool
                .transaction_order()
                .into_iter()
                .filter_map(|txid| mempool.get(&txid))
                .map(|entry| entry.fee_sat)
                .sum::<u64>();
            Ok(json!({
                "loaded": true,
                "size": mempool.len(),
                "bytes": mempool.bytes(),
                "usage": mempool.bytes(),
                "maxmempool": mempool.max_bytes(),
                "mempoolminfee": 0.00001000,
                "minrelaytxfee": 0.00001000,
                "unbroadcastcount": 0,
                "incrementalrelayfee": 0.00001000,
                "total_fee": sat_to_btc(total_fee),
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
                        .map(|txid| {
                            Ok((
                                txid.to_string(),
                                mempool_entry_json(&mempool, txid, height)?,
                            ))
                        })
                        .collect::<Result<Vec<(String, Value)>>>()?
                        .into_iter()
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
            mempool_entry_json(&mempool, &txid, height)
        }
        "getmempoolancestors" => get_mempool_relationship(node, params, true),
        "getmempooldescendants" => get_mempool_relationship(node, params, false),
        "savemempool" => {
            node.persist_mempool()?;
            Ok(json!(
                node.config.datadir.join("mempool.json").to_string_lossy()
            ))
        }
        "gettxoutsetinfo" => {
            let chain = node.chain.read();
            let (transactions, outputs, total) = chain.utxo_stats();
            let disk_size = std::fs::metadata(chain.store.path())
                .map(|metadata| metadata.len())
                .unwrap_or(0);
            Ok(json!({
                "height": chain.height(),
                "bestblock": chain.best_hash().to_string(),
                "transactions": transactions,
                "txouts": outputs,
                "bogosize": outputs.saturating_mul(32 + 4 + 4 + 1 + 8 + 8),
                "hash_serialized_2": chain.utxo_serialized_hash(),
                "disk_size": disk_size,
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
            "localservices": "0000000000000009",
            "localrelay": true,
            "connections": node.peer_count(),
            "connections_in": node.peer_infos().iter().filter(|peer| peer.inbound).count(),
            "connections_out": node.peer_infos().iter().filter(|peer| !peer.inbound).count(),
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
        "getpeerinfo" => Ok(json!(
            node.peer_infos()
                .into_iter()
                .map(|peer| json!({
                    "id": peer.id,
                    "addr": peer.address.to_string(),
                    "addrbind": "",
                    "addrlocal": "",
                    "network": "ipv4",
                    "services": format!("{:016x}", peer.services),
                    "relaytxes": peer.relay_transactions,
                    "lastsend": 0,
                    "lastrecv": 0,
                    "bytessent": 0,
                    "bytesrecv": 0,
                    "conntime": peer.connected_at,
                    "pingtime": null,
                    "minping": null,
                    "version": peer.version.unwrap_or_default(),
                    "subver": peer.user_agent,
                    "inbound": peer.inbound,
                    "startingheight": peer.start_height,
                    "synced_headers": node.chain.read().best_header_tip().height,
                    "synced_blocks": node.chain.read().height(),
                    "inflight": [],
                }))
                .collect::<Vec<_>>()
        )),
        "getrpcinfo" => Ok(json!({
            "active_commands": [],
            "logpath": node.config.datadir.join("debug.log").to_string_lossy(),
        })),
        "help" => Ok(json!(rpc_help(method_params_string(params)))),
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
    let mut chain = node.chain.write();
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
        "versionHex": format!("{:08x}", header.version.to_consensus()),
        "merkleroot": header.merkle_root.to_string(),
        "time": header.time,
        "mediantime": chain.median_time_past_for_hash(&hash).unwrap_or(header.time),
        "nonce": header.nonce,
        "bits": format!("{:08x}", header.bits.to_consensus()),
        "target": format!("{:064x}", header.target()),
        "difficulty": header.difficulty_float(),
        "chainwork": format!(
            "{:064x}",
            chain
                .chain_work_by_hash(&hash)
                .unwrap_or_else(|| chain.tip().work)
        ),
        "nTx": chain.block_transaction_count(&hash)?.unwrap_or(0),
        "previousblockhash": (height > 0).then(|| header.prev_blockhash.to_string()),
        "nextblockhash": chain.next_block_hash(&hash).map(|next| next.to_string()),
    }))
}

fn get_chain_tx_stats(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let explicit_window = params.get(0).is_some_and(|value| !value.is_null());
    let requested_window = if explicit_window {
        params
            .get(0)
            .and_then(Value::as_i64)
            .ok_or_else(|| anyhow!("window must be an integer"))?
    } else {
        30
    };
    if requested_window < 0 {
        bail!("window must not be negative");
    }
    let requested_hash = params
        .get(1)
        .and_then(Value::as_str)
        .map(str::parse::<BlockHash>)
        .transpose()?;
    let mut chain = node.chain.write();
    let end_height = if let Some(hash) = requested_hash {
        if !chain.is_active_block(&hash) {
            bail!("block is not on the active chain");
        }
        chain
            .block_height_by_hash(&hash)
            .ok_or_else(|| anyhow!("block not found"))?
    } else {
        chain.height()
    };
    let window = if explicit_window {
        let window = u32::try_from(requested_window).unwrap_or(u32::MAX);
        if window > 0 && window >= end_height {
            bail!("window must be between 0 and the block height - 1");
        }
        window
    } else {
        u32::try_from(requested_window)
            .unwrap_or(u32::MAX)
            .min(end_height.saturating_sub(1))
    };
    let start_height = end_height.saturating_sub(window);
    let end_hash = chain
        .block_hash(end_height)
        .ok_or_else(|| anyhow!("block height out of range"))?;
    let start_hash = chain
        .block_hash(start_height)
        .ok_or_else(|| anyhow!("block height out of range"))?;
    let mut txcount = 0u64;
    let mut window_tx_count = 0u64;
    for height in 0..=end_height {
        let hash = chain
            .block_hash(height)
            .ok_or_else(|| anyhow!("block height out of range"))?;
        let count = chain
            .block_transaction_count(&hash)?
            .ok_or_else(|| anyhow!("active block is missing from block store"))?
            as u64;
        txcount = txcount.saturating_add(count);
        if height > start_height {
            window_tx_count = window_tx_count.saturating_add(count);
        }
    }
    let start_time = chain
        .header(start_height)
        .map(|header| header.time)
        .ok_or_else(|| anyhow!("block height out of range"))?;
    let end_time = chain
        .header(end_height)
        .map(|header| header.time)
        .ok_or_else(|| anyhow!("block height out of range"))?;
    let interval = chain
        .median_time_past_for_hash(&end_hash)
        .unwrap_or(end_time)
        .saturating_sub(
            chain
                .median_time_past_for_hash(&start_hash)
                .unwrap_or(start_time),
        );
    let mut result = json!({
        "time": end_time,
        "txcount": txcount,
        "window_final_block_hash": end_hash.to_string(),
        "window_final_block_height": end_height,
        "window_block_count": window,
    });
    if window > 0 {
        result["window_tx_count"] = json!(window_tx_count);
        result["window_interval"] = json!(interval);
        if interval > 0 {
            result["txrate"] = json!(window_tx_count as f64 / interval as f64);
        }
    }
    Ok(result)
}

fn get_network_hash_ps(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let nblocks = params.get(0).and_then(Value::as_u64).unwrap_or(120);
    let requested_height = params.get(1).and_then(Value::as_i64).unwrap_or(-1);
    let chain = node.chain.read();
    let end_height = if requested_height < 0 {
        chain.height()
    } else {
        u32::try_from(requested_height)
            .map_err(|_| anyhow!("height is out of range"))?
            .min(chain.height())
    };
    let window = u32::try_from(nblocks)
        .unwrap_or(u32::MAX)
        .min(end_height.saturating_add(1));
    if window == 0 {
        return Ok(json!(0.0));
    }
    let start_height = end_height.saturating_sub(window.saturating_sub(1));
    let start = chain
        .header(start_height)
        .ok_or_else(|| anyhow!("block height out of range"))?;
    let end = chain
        .header(end_height)
        .ok_or_else(|| anyhow!("block height out of range"))?;
    let interval = end.time.saturating_sub(start.time);
    if interval == 0 {
        return Ok(json!(0.0));
    }
    let expected_hashes = end.difficulty_float() * 4_294_967_296.0 * f64::from(window);
    Ok(json!(expected_hashes / f64::from(interval)))
}

fn get_mining_info(node: &Arc<Node>) -> Result<Value> {
    let chain = node.chain.read();
    let tip = chain.tip();
    let header = chain.header(tip.height).expect("tip header exists");
    let window = 120u32.min(tip.height.saturating_add(1));
    let start_height = tip.height.saturating_sub(window.saturating_sub(1));
    let start = chain.header(start_height).expect("start header exists");
    let interval = header.time.saturating_sub(start.time);
    let network_hashps = if interval == 0 {
        0.0
    } else {
        header.difficulty_float() * 4_294_967_296.0 * f64::from(window) / f64::from(interval)
    };
    let mempool = node.mempool.read();
    Ok(json!({
        "blocks": tip.height,
        "difficulty": header.difficulty_float(),
        "networkhashps": network_hashps,
        "pooledtx": mempool.len(),
        "chain": network_name(chain.network),
        "warnings": "",
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
    let hash_string = hash.to_string();
    let txs = if verbosity >= 2 {
        block
            .txdata
            .iter()
            .map(|tx| {
                rpc_transaction(
                    tx,
                    Some(&hash_string),
                    Some(confirmations),
                    Some(block.header.time),
                    Some(block.header.time),
                )
            })
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
        "versionHex": format!("{:08x}", block.header.version.to_consensus()),
        "merkleroot": block.header.merkle_root.to_string(),
        "time": block.header.time,
        "mediantime": chain
            .median_time_past_for_hash(&hash)
            .unwrap_or(block.header.time),
        "nonce": block.header.nonce,
        "bits": format!("{:08x}", block.header.bits.to_consensus()),
        "target": format!("{:064x}", block.header.target()),
        "difficulty": block.header.difficulty_float(),
        "chainwork": format!(
            "{:064x}",
            chain
                .chain_work_by_hash(&hash)
                .unwrap_or_else(|| chain.tip().work)
        ),
        "nTx": block.txdata.len(),
        "strippedsize": stripped_block_size(&block),
        "size": serialize(&block).len(),
        "weight": block.weight().to_wu(),
        "tx": txs,
        "previousblockhash": (height > 0).then(|| block.header.prev_blockhash.to_string()),
        "nextblockhash": chain.next_block_hash(&hash).map(|next| next.to_string()),
        "coinbase_tx": coinbase_transaction_json(&block.txdata[0]),
    }))
}

fn submit_header(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let bytes = hex::decode(param::<String>(params, 0)?)?;
    let header: bitcoin::block::Header = deserialize(&bytes)?;
    node.chain.write().accept_headers(&[header])?;
    Ok(Value::Null)
}

fn get_txout_proof(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let txids = params
        .get(0)
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("gettxoutproof expects an array of transaction ids"))?
        .iter()
        .map(|value| {
            value
                .as_str()
                .ok_or_else(|| anyhow!("transaction id must be a string"))?
                .parse::<Txid>()
                .map_err(Into::into)
        })
        .collect::<Result<Vec<Txid>>>()?;
    if txids.is_empty() {
        bail!("transaction id array must not be empty");
    }
    let requested_hash = params
        .get(1)
        .and_then(Value::as_str)
        .map(str::parse::<BlockHash>)
        .transpose()?;
    let mut chain = node.chain.write();
    let block_hash = if let Some(hash) = requested_hash {
        hash
    } else {
        chain
            .transaction(&txids[0])?
            .map(|(_, location)| location.block_hash)
            .ok_or_else(|| anyhow!("transaction not found"))?
    };
    let block = chain
        .block(&block_hash)?
        .ok_or_else(|| anyhow!("block not found"))?;
    let block_txids: HashMap<Txid, usize> = block
        .txdata
        .iter()
        .enumerate()
        .map(|(index, transaction)| (transaction.compute_txid(), index))
        .collect();
    if txids.iter().any(|txid| !block_txids.contains_key(txid)) {
        bail!("transaction is not in the specified block");
    }
    let proof = serialize_merkle_proof(&block, &txids)?;
    Ok(json!(hex::encode(proof)))
}

fn verify_txout_proof(params: &Value) -> Result<Value> {
    let bytes = hex::decode(param::<String>(params, 0)?)?;
    if bytes.len() < 84 {
        bail!("invalid merkle proof");
    }
    let header: bitcoin::block::Header = deserialize(&bytes[..80])?;
    let mut reader = ProofReader::new(&bytes[80..]);
    let total = reader.u32()? as usize;
    if total == 0 || total > 1_000_000 {
        bail!("invalid merkle proof transaction count");
    }
    let hash_count = reader.compact_size()?;
    if hash_count == 0 || hash_count > total {
        bail!("invalid merkle proof hash count");
    }
    let mut hashes = Vec::with_capacity(hash_count);
    for _ in 0..hash_count {
        hashes.push(Txid::from_byte_array(reader.array::<32>()?));
    }
    let flag_count = reader.compact_size()?;
    if flag_count == 0 || flag_count > 1_000_000 {
        bail!("invalid merkle proof flag count");
    }
    let flags = reader.bytes(flag_count)?.to_vec();
    let mut cursor = MerkleCursor {
        hashes: &hashes,
        hash_index: 0,
        flags: &flags,
        flag_index: 0,
    };
    let height = merkle_tree_height(total);
    let (root, matches) = extract_merkle_node(height, 0, total, &mut cursor)?;
    if root.to_raw_hash() != header.merkle_root.to_raw_hash() || cursor.hash_index != hashes.len() {
        bail!("invalid merkle proof");
    }
    Ok(json!(
        matches
            .into_iter()
            .map(|txid| txid.to_string())
            .collect::<Vec<_>>()
    ))
}

fn serialize_merkle_proof(block: &bitcoin::Block, requested: &[Txid]) -> Result<Vec<u8>> {
    let txids: Vec<Txid> = block.txdata.iter().map(Transaction::compute_txid).collect();
    if txids.is_empty() {
        bail!("block contains no transactions");
    }
    let matches: Vec<bool> = txids.iter().map(|txid| requested.contains(txid)).collect();
    let height = merkle_tree_height(txids.len());
    let mut levels = vec![txids.clone()];
    while levels.last().expect("level exists").len() > 1 {
        let previous = levels.last().expect("level exists");
        let mut next = Vec::with_capacity(previous.len().div_ceil(2));
        for pair in previous.chunks(2) {
            let right = *pair.get(1).unwrap_or(&pair[0]);
            next.push(combine_merkle_hashes(pair[0], right));
        }
        levels.push(next);
    }
    let mut bits = Vec::new();
    let mut hashes = Vec::new();
    collect_merkle_nodes(
        height,
        0,
        txids.len(),
        &levels,
        &matches,
        &mut bits,
        &mut hashes,
    );
    let mut proof = serialize(&block.header);
    proof.extend_from_slice(&(txids.len() as u32).to_le_bytes());
    put_compact_size(hashes.len(), &mut proof);
    for hash in hashes {
        proof.extend_from_slice(&hash.to_byte_array());
    }
    let flag_bytes = bits
        .chunks(8)
        .map(|chunk| {
            chunk
                .iter()
                .enumerate()
                .fold(0u8, |value, (index, bit)| value | (u8::from(*bit) << index))
        })
        .collect::<Vec<_>>();
    put_compact_size(flag_bytes.len(), &mut proof);
    proof.extend_from_slice(&flag_bytes);
    Ok(proof)
}

fn collect_merkle_nodes(
    height: usize,
    position: usize,
    total: usize,
    levels: &[Vec<Txid>],
    matches: &[bool],
    bits: &mut Vec<bool>,
    hashes: &mut Vec<Txid>,
) {
    let start = position << height;
    let end = start.saturating_add(1usize << height).min(total);
    let parent_match = matches[start..end].iter().any(|matched| *matched);
    bits.push(parent_match);
    if height == 0 || !parent_match {
        hashes.push(levels[height][position]);
        return;
    }
    collect_merkle_nodes(
        height - 1,
        position * 2,
        total,
        levels,
        matches,
        bits,
        hashes,
    );
    if position * 2 + 1 < merkle_tree_width(total, height - 1) {
        collect_merkle_nodes(
            height - 1,
            position * 2 + 1,
            total,
            levels,
            matches,
            bits,
            hashes,
        );
    }
}

fn merkle_tree_height(total: usize) -> usize {
    let mut height = 0;
    while merkle_tree_width(total, height) > 1 {
        height += 1;
    }
    height
}

fn merkle_tree_width(total: usize, height: usize) -> usize {
    (total + (1usize << height) - 1) >> height
}

fn combine_merkle_hashes(left: Txid, right: Txid) -> Txid {
    let mut bytes = [0u8; 64];
    bytes[..32].copy_from_slice(&left.to_byte_array());
    bytes[32..].copy_from_slice(&right.to_byte_array());
    Txid::from_raw_hash(bitcoin::hashes::sha256d::Hash::hash(&bytes))
}

struct MerkleCursor<'a> {
    hashes: &'a [Txid],
    hash_index: usize,
    flags: &'a [u8],
    flag_index: usize,
}

fn extract_merkle_node(
    height: usize,
    position: usize,
    total: usize,
    cursor: &mut MerkleCursor<'_>,
) -> Result<(Txid, Vec<Txid>)> {
    let bit = cursor
        .flags
        .get(cursor.flag_index / 8)
        .map(|byte| byte & (1 << (cursor.flag_index % 8)) != 0)
        .ok_or_else(|| anyhow!("merkle proof has too few flag bits"))?;
    cursor.flag_index += 1;
    if height == 0 || !bit {
        let hash = *cursor
            .hashes
            .get(cursor.hash_index)
            .ok_or_else(|| anyhow!("merkle proof has too few hashes"))?;
        cursor.hash_index += 1;
        return Ok((
            hash,
            (height == 0 && bit)
                .then_some(vec![hash])
                .unwrap_or_default(),
        ));
    }
    let (left, mut matches) = extract_merkle_node(height - 1, position * 2, total, cursor)?;
    let (right, right_matches) = if position * 2 + 1 < merkle_tree_width(total, height - 1) {
        extract_merkle_node(height - 1, position * 2 + 1, total, cursor)?
    } else {
        (left, Vec::new())
    };
    matches.extend(right_matches);
    Ok((combine_merkle_hashes(left, right), matches))
}

fn put_compact_size(value: usize, output: &mut Vec<u8>) {
    if value < 0xfd {
        output.push(value as u8);
    } else if value <= u16::MAX as usize {
        output.push(0xfd);
        output.extend_from_slice(&(value as u16).to_le_bytes());
    } else if value <= u32::MAX as usize {
        output.push(0xfe);
        output.extend_from_slice(&(value as u32).to_le_bytes());
    } else {
        output.push(0xff);
        output.extend_from_slice(&(value as u64).to_le_bytes());
    }
}

fn stripped_block_size(block: &bitcoin::Block) -> usize {
    80 + compact_size_len(block.txdata.len())
        + block
            .txdata
            .iter()
            .map(Transaction::base_size)
            .sum::<usize>()
}

fn compact_size_len(value: usize) -> usize {
    match value {
        0..=0xfc => 1,
        0xfd..=0xffff => 3,
        0x1_0000..=0xffff_ffff => 5,
        _ => 9,
    }
}

struct ProofReader<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl<'a> ProofReader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }

    fn bytes(&mut self, length: usize) -> Result<&'a [u8]> {
        let end = self
            .position
            .checked_add(length)
            .ok_or_else(|| anyhow!("merkle proof length overflow"))?;
        let bytes = self
            .bytes
            .get(self.position..end)
            .ok_or_else(|| anyhow!("merkle proof is truncated"))?;
        self.position = end;
        Ok(bytes)
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N]> {
        self.bytes(N)?
            .try_into()
            .map_err(|_| anyhow!("invalid merkle proof field"))
    }

    fn u32(&mut self) -> Result<u32> {
        Ok(u32::from_le_bytes(self.array()?))
    }

    fn compact_size(&mut self) -> Result<usize> {
        let prefix = self.bytes(1)?[0];
        let value = match prefix {
            0..=0xfc => u64::from(prefix),
            0xfd => {
                let value = u16::from_le_bytes(self.array()?);
                if value < 0xfd {
                    return Err(anyhow!("non-canonical merkle proof count"));
                }
                u64::from(value)
            }
            0xfe => {
                let value = u32::from_le_bytes(self.array()?);
                if value <= u16::MAX as u32 {
                    return Err(anyhow!("non-canonical merkle proof count"));
                }
                u64::from(value)
            }
            0xff => {
                let value = u64::from_le_bytes(self.array()?);
                if value <= u32::MAX as u64 {
                    return Err(anyhow!("non-canonical merkle proof count"));
                }
                value
            }
        };
        usize::try_from(value).map_err(|_| anyhow!("merkle proof count overflows usize"))
    }
}

fn coinbase_transaction_json(transaction: &Transaction) -> Value {
    let input = &transaction.input[0];
    let witness = input.witness.to_vec();
    let mut value = json!({
        "version": transaction.version.0,
        "locktime": transaction.lock_time.to_consensus_u32(),
        "sequence": input.sequence.to_consensus_u32(),
        "coinbase": hex::encode(input.script_sig.as_bytes()),
    });
    if let Some(first) = witness.first() {
        value["witness"] = json!(hex::encode(first));
    }
    value
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
    let height = chain.block_height_by_hash(&hash);
    let fee_stats = chain
        .block_fee_stats(&hash)?
        .ok_or_else(|| anyhow!("Block not found"))?;
    let transaction_fees = fee_stats.transaction_fees_sat;
    let mut total_out = 0u64;
    let mut inputs = 0usize;
    let mut outputs = 0usize;
    let mut total_size = 0usize;
    let mut total_weight = 0u64;
    let mut segwit_transactions = 0usize;
    let mut segwit_size = 0usize;
    let mut segwit_weight = 0u64;
    let mut fees = Vec::with_capacity(transaction_fees.len());
    let mut fee_rates = Vec::with_capacity(transaction_fees.len());
    let mut transaction_sizes = Vec::with_capacity(transaction_fees.len());
    let mut utxo_size_inc = 0i64;
    let mut utxo_size_inc_actual = 0i64;
    let mut utxo_count_actual = 0i64;
    let mut spent_output_index = 0usize;
    let mut transaction_index = 0usize;
    for transaction in &block.txdata {
        outputs = outputs.saturating_add(transaction.output.len());
        for output in &transaction.output {
            let size = utxo_stat_size(output);
            utxo_size_inc = utxo_size_inc.saturating_add(size);
            if !output.script_pubkey.is_op_return() {
                utxo_count_actual = utxo_count_actual.saturating_add(1);
                utxo_size_inc_actual = utxo_size_inc_actual.saturating_add(size);
            }
        }
        if transaction.is_coinbase() {
            continue;
        }
        inputs = inputs.saturating_add(transaction.input.len());
        let fee = *transaction_fees
            .get(transaction_index)
            .ok_or_else(|| anyhow!("block fee statistics are incomplete"))?;
        transaction_index += 1;
        total_out = total_out.saturating_add(
            transaction
                .output
                .iter()
                .map(|output| output.value.to_sat())
                .sum::<u64>(),
        );
        total_size = total_size.saturating_add(serialize(transaction).len());
        let size = serialize(transaction).len();
        let weight = transaction.weight().to_wu();
        total_weight = total_weight.saturating_add(weight);
        transaction_sizes.push(size as u64);
        fees.push(fee);
        fee_rates.push((
            fee.saturating_mul(4).checked_div(weight).unwrap_or(0),
            weight,
        ));
        if transaction
            .input
            .iter()
            .any(|input| !input.witness.is_empty())
        {
            segwit_transactions = segwit_transactions.saturating_add(1);
            segwit_size = segwit_size.saturating_add(size);
            segwit_weight = segwit_weight.saturating_add(weight);
        }
        for _ in &transaction.input {
            let previous_output = fee_stats
                .spent_outputs
                .get(spent_output_index)
                .ok_or_else(|| anyhow!("block fee statistics are incomplete"))?;
            spent_output_index += 1;
            let size = utxo_stat_size(previous_output);
            utxo_size_inc = utxo_size_inc.saturating_sub(size);
            if !previous_output.script_pubkey.is_op_return() {
                utxo_count_actual = utxo_count_actual.saturating_sub(1);
                utxo_size_inc_actual = utxo_size_inc_actual.saturating_sub(size);
            }
        }
    }
    let non_coinbase = block.txdata.len().saturating_sub(1);
    let total_fee = fee_stats.total_fee_sat;
    let mut sorted_fees = fees.clone();
    let mut sorted_sizes = transaction_sizes.clone();
    let mut sorted_fee_rates = fee_rates.clone();
    let percentiles = weighted_fee_percentiles(&mut sorted_fee_rates, total_weight);
    let result = json!({
        "blockhash": hash.to_string(),
        "height": height,
        "txs": block.txdata.len(),
        "time": block.header.time,
        "mediantime": chain.median_time_past_for_hash(&hash).unwrap_or(block.header.time),
        "size": serialize(&block).len(),
        "total_size": total_size,
        "total_weight": total_weight,
        "total_out": total_out,
        "subsidy": height.map(validation::block_subsidy).unwrap_or_default(),
        "totalfee": total_fee,
        "ins": inputs,
        "outs": outputs,
        "swtxs": segwit_transactions,
        "avgfee": if non_coinbase == 0 { 0 } else { total_fee / non_coinbase as u64 },
        "avgfeerate": total_fee.saturating_mul(4).checked_div(total_weight).unwrap_or(0),
        "avgtxsize": total_size.checked_div(non_coinbase).unwrap_or(0),
        "feerate_percentiles": percentiles,
        "maxfee": sorted_fees.iter().copied().max().unwrap_or(0),
        "maxfeerate": fee_rates.iter().map(|(rate, _)| *rate).max().unwrap_or(0),
        "maxtxsize": sorted_sizes.iter().copied().max().unwrap_or(0),
        "medianfee": truncated_median(&mut sorted_fees),
        "mediantime": chain.median_time_past_for_hash(&hash).unwrap_or(block.header.time),
        "mediantxsize": truncated_median(&mut sorted_sizes),
        "minfee": sorted_fees.iter().copied().min().unwrap_or(0),
        "minfeerate": fee_rates.iter().map(|(rate, _)| *rate).min().unwrap_or(0),
        "mintxsize": sorted_sizes.iter().copied().min().unwrap_or(0),
        "swtotal_size": segwit_size,
        "swtotal_weight": segwit_weight,
        "utxo_increase": outputs as i64 - inputs as i64,
        "utxo_size_inc": utxo_size_inc,
        "utxo_increase_actual": utxo_count_actual - inputs as i64,
        "utxo_size_inc_actual": utxo_size_inc_actual,
    });
    let Some(selected) = params.get(1).and_then(Value::as_array) else {
        return Ok(result);
    };
    if selected.is_empty() {
        return Ok(result);
    }
    let mut filtered = serde_json::Map::new();
    for statistic in selected {
        let statistic = statistic
            .as_str()
            .ok_or_else(|| anyhow!("block statistics must be strings"))?;
        let value = result
            .get(statistic)
            .cloned()
            .ok_or_else(|| anyhow!("unknown block statistic: {statistic}"))?;
        filtered.insert(statistic.to_owned(), value);
    }
    Ok(Value::Object(filtered))
}

fn utxo_stat_size(output: &TxOut) -> i64 {
    i64::try_from(serialize(output).len().saturating_add(40)).unwrap_or(i64::MAX)
}

fn truncated_median(values: &mut [u64]) -> u64 {
    if values.is_empty() {
        return 0;
    }
    values.sort_unstable();
    let middle = values.len() / 2;
    if values.len() % 2 == 1 {
        values[middle]
    } else {
        values[middle - 1].saturating_add(values[middle]) / 2
    }
}

fn weighted_fee_percentiles(values: &mut [(u64, u64)], total_weight: u64) -> [u64; 5] {
    if values.is_empty() || total_weight == 0 {
        return [0; 5];
    }
    values.sort_unstable_by_key(|(rate, _)| *rate);
    let mut result = [0; 5];
    let mut cumulative = 0u64;
    let targets =
        [10u64, 25, 50, 75, 90].map(|percentile| total_weight.saturating_mul(percentile) / 100);
    let mut target_index = 0usize;
    for (rate, weight) in values.iter().copied() {
        cumulative = cumulative.saturating_add(weight);
        while target_index < targets.len() && cumulative >= targets[target_index] {
            result[target_index] = rate;
            target_index += 1;
        }
    }
    result
}

fn get_raw_transaction(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let txid: Txid = param::<String>(params, 0)?.parse()?;
    let verbose = params.get(1).and_then(Value::as_bool).unwrap_or(false);
    let requested_block = params
        .get(2)
        .and_then(Value::as_str)
        .map(str::parse::<BlockHash>)
        .transpose()?;
    let mut chain = node.chain.write();
    let found = if let Some(block_hash) = requested_block {
        let block = chain
            .block(&block_hash)?
            .ok_or_else(|| anyhow!("Block not found"))?;
        let Some(transaction_index) = block
            .txdata
            .iter()
            .position(|transaction| transaction.compute_txid() == txid)
        else {
            bail!("No such transaction in specified block");
        };
        Some((
            block.txdata[transaction_index].clone(),
            chain::TxLocation {
                block_hash,
                height: chain.block_height_by_hash(&block_hash).unwrap_or(0),
                transaction_index,
            },
        ))
    } else {
        chain.transaction(&txid)?
    };
    let (transaction, location) = if let Some(found) = found {
        found
    } else if requested_block.is_none()
        && let Some(entry) = node.mempool.read().get(&txid)
    {
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
            (chain.height().saturating_sub(location.height) + 1) as i64
        } else {
            0
        }
    });
    let block_time = (location.block_hash != BlockHash::all_zeros())
        .then(|| {
            chain
                .header_by_hash(&location.block_hash)
                .map(|header| header.time)
        })
        .flatten();
    Ok(rpc_transaction(
        &transaction,
        blockhash.as_deref(),
        confirmations,
        block_time,
        block_time,
    ))
}

fn decode_raw_transaction(params: &Value) -> Result<Value> {
    let bytes = hex::decode(param::<String>(params, 0)?)?;
    let transaction: Transaction = deserialize(&bytes)?;
    Ok(rpc_transaction(&transaction, None, None, None, None))
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

fn get_mempool_relationship(node: &Arc<Node>, params: &Value, ancestors: bool) -> Result<Value> {
    let txid: Txid = param::<String>(params, 0)?.parse()?;
    let verbose = params.get(1).and_then(Value::as_bool).unwrap_or(false);
    let height = node.chain.read().height();
    let mempool = node.mempool.read();
    let related = if ancestors {
        mempool.ancestors(&txid)
    } else {
        mempool.descendants(&txid)
    };
    if verbose {
        let mut result = serde_json::Map::new();
        for related_txid in related {
            result.insert(
                related_txid.to_string(),
                mempool_entry_json(&mempool, &related_txid, height)?,
            );
        }
        Ok(Value::Object(result))
    } else {
        Ok(json!(
            related
                .into_iter()
                .map(|related_txid| related_txid.to_string())
                .collect::<Vec<_>>()
        ))
    }
}

fn mempool_entry_json(mempool: &Mempool, txid: &Txid, height: u32) -> Result<Value> {
    let entry = mempool
        .get(txid)
        .ok_or_else(|| anyhow!("Transaction not in mempool"))?;
    let ancestors = mempool.ancestors(txid);
    let descendants = mempool.descendants(txid);
    let ancestor_ids = std::iter::once(*txid)
        .chain(ancestors.iter().copied())
        .collect::<Vec<_>>();
    let descendant_ids = std::iter::once(*txid)
        .chain(descendants.iter().copied())
        .collect::<Vec<_>>();
    let aggregate = |ids: &[Txid]| {
        ids.iter()
            .filter_map(|candidate| mempool.get(candidate))
            .fold((0u64, 0u64), |(fee, size), candidate| {
                (
                    fee.saturating_add(candidate.fee_sat),
                    size.saturating_add(candidate.vsize),
                )
            })
    };
    let (ancestor_fee, ancestor_size) = aggregate(&ancestor_ids);
    let (descendant_fee, descendant_size) = aggregate(&descendant_ids);
    let parents = mempool
        .parents(txid)
        .into_iter()
        .map(|parent| parent.to_string())
        .collect::<Vec<_>>();
    let children = mempool
        .children(txid)
        .into_iter()
        .map(|child| child.to_string())
        .collect::<Vec<_>>();
    Ok(json!({
        "vsize": entry.vsize,
        "weight": entry.transaction.weight().to_wu(),
        "time": entry.added_at,
        "height": height,
        "descendantcount": descendant_ids.len(),
        "descendantsize": descendant_size,
        "ancestorcount": ancestor_ids.len(),
        "ancestorsize": ancestor_size,
        "wtxid": entry.transaction.compute_wtxid().to_string(),
        "fee": sat_to_btc(entry.fee_sat),
        "fees": {
            "base": sat_to_btc(entry.fee_sat),
            "modified": sat_to_btc(entry.fee_sat),
            "ancestor": sat_to_btc(ancestor_fee),
            "descendant": sat_to_btc(descendant_fee),
        },
        "depends": parents,
        "spentby": children,
        "bip125-replaceable": false,
        "unbroadcast": false,
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

fn get_tx_spending_prevout(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let outpoints = params
        .get(0)
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("gettxspendingprevout expects an array"))?
        .iter()
        .map(|value| {
            let txid: Txid = value
                .get("txid")
                .and_then(Value::as_str)
                .ok_or_else(|| anyhow!("outpoint txid must be a string"))?
                .parse()?;
            let vout = value
                .get("vout")
                .and_then(Value::as_u64)
                .ok_or_else(|| anyhow!("outpoint vout must be an integer"))?;
            let vout = u32::try_from(vout).map_err(|_| anyhow!("outpoint vout is too large"))?;
            Ok(OutPoint::new(txid, vout))
        })
        .collect::<Result<Vec<OutPoint>>>()?;
    let height = node.chain.read().height();
    let mempool = node.mempool.read();
    Ok(json!(
        outpoints
            .into_iter()
            .map(|outpoint| {
                let Some(spender_txid) = mempool.spender(&outpoint) else {
                    return Value::Null;
                };
                let Some(entry) = mempool.get(&spender_txid) else {
                    return Value::Null;
                };
                let Some(vin) = entry
                    .transaction
                    .input
                    .iter()
                    .position(|input| input.previous_output == outpoint)
                else {
                    return Value::Null;
                };
                json!({
                "txid": spender_txid.to_string(),
                "vin": vin,
                "fees": {"base": sat_to_btc(entry.fee_sat)},
                "time": entry.added_at,
                "height": height,
                })
            })
            .collect::<Vec<_>>()
    ))
}

fn rpc_transaction(
    transaction: &Transaction,
    blockhash: Option<&str>,
    confirmations: Option<i64>,
    time: Option<u32>,
    blocktime: Option<u32>,
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
    if let Some(time) = time {
        value["time"] = json!(time);
    }
    if let Some(blocktime) = blocktime {
        value["blocktime"] = json!(blocktime);
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

fn method_params_string(params: &Value) -> &str {
    params.get(0).and_then(Value::as_str).unwrap_or("")
}

fn rpc_help(method: &str) -> String {
    const METHODS: &[&str] = &[
        "getblockchaininfo",
        "getblockcount",
        "getbestblockhash",
        "getblockhash",
        "getblockheader",
        "getblock",
        "getblockstats",
        "getchaintxstats",
        "getnetworkhashps",
        "gettxoutproof",
        "verifytxoutproof",
        "submitheader",
        "getrawtransaction",
        "decoderawtransaction",
        "sendrawtransaction",
        "submitblock",
        "getblocktemplate",
        "getmininginfo",
        "testmempoolaccept",
        "verifychain",
        "gettxout",
        "gettxspendingprevout",
        "getmempoolinfo",
        "getrawmempool",
        "getmempoolentry",
        "getmempoolancestors",
        "getmempooldescendants",
        "savemempool",
        "gettxoutsetinfo",
        "getchaintips",
        "getnetworkinfo",
        "getpeerinfo",
        "getrpcinfo",
        "estimatesmartfee",
        "getdifficulty",
        "getconnectioncount",
        "uptime",
    ];
    if method.is_empty() {
        METHODS.join("\n")
    } else if METHODS.contains(&method) {
        format!("{method}: wallet-free Bitcoin Core-compatible RPC")
    } else {
        format!("unknown command: {method}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Node;
    use crate::config::Config;
    use bitcoin::Network;
    use bitcoin::absolute::LockTime;
    use bitcoin::block::{Header, Version as BlockVersion};
    use bitcoin::blockdata::script::ScriptBuf;
    use bitcoin::blockdata::transaction::{OutPoint, TxIn, TxOut, Version};
    use bitcoin::blockdata::witness::Witness;
    use bitcoin::hashes::Hash;

    fn proof_transaction(tag: u8) -> Transaction {
        Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(Txid::from_byte_array([tag; 32]), 0),
                script_sig: ScriptBuf::from_bytes(vec![tag]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: bitcoin::Amount::from_sat(u64::from(tag)),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        }
    }

    #[test]
    fn merkle_proof_round_trip_for_multiple_transactions() {
        let mut block = bitcoin::Block {
            header: Header {
                version: BlockVersion::TWO,
                prev_blockhash: BlockHash::all_zeros(),
                merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                time: 1,
                bits: bitcoin::pow::CompactTarget::from_consensus(0x207f_ffff),
                nonce: 0,
            },
            txdata: vec![
                proof_transaction(1),
                proof_transaction(2),
                proof_transaction(3),
            ],
        };
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        let requested = vec![
            block.txdata[0].compute_txid(),
            block.txdata[2].compute_txid(),
        ];
        let proof = serialize_merkle_proof(&block, &requested).unwrap();
        let result = verify_txout_proof(&json!([hex::encode(proof)])).unwrap();
        assert_eq!(
            result,
            json!(
                requested
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
            )
        );
    }

    #[test]
    fn merkle_proof_rejects_a_modified_header() {
        let mut block = bitcoin::Block {
            header: Header {
                version: BlockVersion::TWO,
                prev_blockhash: BlockHash::all_zeros(),
                merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                time: 1,
                bits: bitcoin::pow::CompactTarget::from_consensus(0x207f_ffff),
                nonce: 0,
            },
            txdata: vec![proof_transaction(4), proof_transaction(5)],
        };
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        let txid = block.txdata[1].compute_txid();
        let mut proof = serialize_merkle_proof(&block, &[txid]).unwrap();
        proof[36] ^= 1;
        assert!(verify_txout_proof(&json!([hex::encode(proof)])).is_err());
    }

    #[test]
    fn merkle_proof_can_validly_contain_no_matches() {
        let mut block = bitcoin::Block {
            header: Header {
                version: BlockVersion::TWO,
                prev_blockhash: BlockHash::all_zeros(),
                merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                time: 1,
                bits: bitcoin::pow::CompactTarget::from_consensus(0x207f_ffff),
                nonce: 0,
            },
            txdata: vec![proof_transaction(6), proof_transaction(7)],
        };
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        let proof = serialize_merkle_proof(&block, &[]).unwrap();
        assert_eq!(
            verify_txout_proof(&json!([hex::encode(proof)])).unwrap(),
            json!([])
        );
    }

    #[test]
    fn block_stats_report_satoshi_amounts() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            p2p_bind: "127.0.0.1:0".parse().unwrap(),
            rpc_bind: None,
            electrum_bind: None,
            seed_nodes: Vec::new(),
            signet_challenge: None,
            max_peers: 1,
        })
        .unwrap();
        let hash = node.chain.read().best_hash();
        let stats = get_block_stats(&node, &json!([hash.to_string()])).unwrap();
        assert_eq!(stats["total_out"], json!(0));
        assert_eq!(stats["subsidy"], json!(5_000_000_000u64));
        assert_eq!(stats["totalfee"], json!(0));
        assert_eq!(
            get_block_stats(
                &node,
                &json!([hash.to_string(), ["txs", "totalfee", "feerate_percentiles"]]),
            )
            .unwrap(),
            json!({
                "txs": 1,
                "totalfee": 0,
                "feerate_percentiles": [0, 0, 0, 0, 0],
            })
        );
    }
}
