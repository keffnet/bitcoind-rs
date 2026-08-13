//! Wallet-free Bitcoin Core-style JSON-RPC over HTTP/1.1.

use std::sync::Arc;

use anyhow::{Context, Result, anyhow, bail};
use bitcoin::consensus::encode::{deserialize, serialize};
use bitcoin::hashes::Hash;
use bitcoin::{BlockHash, Network, OutPoint, Transaction, Txid};
use serde_json::{Value, json};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};
use tracing::debug;

use crate::Node;
use crate::chain;

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
        Some(body) => dispatch_json_rpc(&node, &body),
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

async fn read_http_request(stream: &mut TcpStream) -> Result<Option<Vec<u8>>> {
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
    let headers = std::str::from_utf8(&bytes[..header_end])?;
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
    Ok(Some(
        bytes[header_end..header_end + content_length].to_vec(),
    ))
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
        "getrawtransaction" => get_raw_transaction(node, params),
        "decoderawtransaction" => decode_raw_transaction(params),
        "sendrawtransaction" => send_raw_transaction(node, params),
        "submitblock" => submit_block(node, params),
        "gettxout" => get_txout(node, params),
        "getmempoolinfo" => {
            let mempool = node.mempool.read();
            Ok(json!({
                "loaded": true,
                "size": mempool.len(),
                "bytes": mempool.bytes(),
                "usage": mempool.bytes(),
                "maxmempool": 300 * 1024 * 1024,
                "mempoolminfee": 0.00001000,
                "minrelaytxfee": 0.00001000,
            }))
        }
        "getrawmempool" => {
            let verbose = params.get(0).and_then(Value::as_bool).unwrap_or(false);
            let mempool = node.mempool.read();
            if verbose {
                Ok(Value::Object(
                    mempool
                        .transactions()
                        .map(|tx| {
                            let txid = tx.compute_txid();
                            let entry = mempool.get(&txid).expect("mempool iterator is consistent");
                            (
                                txid.to_string(),
                                json!({
                                    "vsize": entry.vsize,
                                    "weight": tx.weight().to_wu(),
                                    "fee": sat_to_btc(entry.fee_sat),
                                    "time": entry.added_at,
                                    "height": 0,
                                    "depends": [],
                                }),
                            )
                        })
                        .collect(),
                ))
            } else {
                Ok(json!(
                    mempool
                        .transactions()
                        .map(Transaction::compute_txid)
                        .map(|txid| txid.to_string())
                        .collect::<Vec<_>>()
                ))
            }
        }
        "getmempoolentry" => {
            let txid: Txid = param::<String>(params, 0)?.parse()?;
            let mempool = node.mempool.read();
            let entry = mempool
                .get(&txid)
                .ok_or_else(|| anyhow!("Transaction not in mempool"))?;
            Ok(json!({
                "vsize": entry.vsize,
                "weight": entry.transaction.weight().to_wu(),
                "fee": sat_to_btc(entry.fee_sat),
                "time": entry.added_at,
                "height": 0,
                "descendantcount": 1,
                "ancestorcount": 1,
            }))
        }
        "gettxoutsetinfo" => {
            let chain = node.chain.read();
            let mut total = 0u64;
            let mut transactions = std::collections::HashSet::new();
            let mut outputs = 0u64;
            // The complete UTXO set is intentionally exposed through the
            // chain helper; this method remains cheap for normal RPC calls.
            for script_hash in chain.script_hashes() {
                for (outpoint, entry) in chain.get_utxos(&script_hash) {
                    total = total.saturating_add(entry.output.value.to_sat());
                    outputs += 1;
                    transactions.insert(outpoint.txid);
                }
            }
            Ok(json!({
                "height": chain.height(),
                "bestblock": chain.best_hash().to_string(),
                "transactions": transactions.len(),
                "txouts": outputs,
                "total_amount": sat_to_btc(total),
            }))
        }
        "getnetworkinfo" => Ok(json!({
            "version": 310100,
            "subversion": "/bitcoind-rs:0.1.0/",
            "protocolversion": 70016,
            "connections": 0,
            "networkactive": true,
            "networks": [],
            "relayfee": 0.00001000,
            "incrementalfee": 0.00001000,
        })),
        "getchaintips" => Ok(json!([{
            "height": node.chain.read().height(),
            "hash": node.chain.read().best_hash().to_string(),
            "branchlen": 0,
            "status": "active",
        }])),
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
        "getconnectioncount" => Ok(json!(0)),
        "uptime" => Ok(json!(0)),
        _ => bail!("Method not found"),
    }
}

fn get_blockchain_info(node: &Arc<Node>) -> Result<Value> {
    let chain = node.chain.read();
    let tip = chain.tip();
    let header = chain.header(tip.height).expect("tip header exists");
    Ok(json!({
        "chain": network_name(chain.network),
        "blocks": tip.height,
        "headers": tip.height,
        "bestblockhash": tip.hash.to_string(),
        "chainwork": format!("{:064x}", tip.work),
        "difficulty": header.difficulty_float(),
        "time": header.time,
        "mediantime": header.time,
        "verificationprogress": 1.0,
        "initialblockdownload": false,
        "pruned": false,
        "size_on_disk": std::fs::metadata(chain.store.path()).map(|m| m.len()).unwrap_or(0),
    }))
}

fn get_block_header(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let hash: BlockHash = param::<String>(params, 0)?.parse()?;
    let verbose = params.get(1).and_then(Value::as_bool).unwrap_or(true);
    let chain = node.chain.read();
    let height = (0..=chain.height()).find(|height| chain.block_hash(*height) == Some(hash));
    let Some(height) = height else {
        bail!("Block not found");
    };
    let header = chain.header(height).expect("header index is consistent");
    if !verbose {
        return Ok(json!(hex::encode(serialize(header))));
    }
    Ok(json!({
        "hash": hash.to_string(),
        "confirmations": chain.height().saturating_sub(height) + 1,
        "height": height,
        "version": header.version.to_consensus(),
        "merkleroot": header.merkle_root.to_string(),
        "time": header.time,
        "mediantime": header.time,
        "nonce": header.nonce,
        "bits": format!("{:08x}", header.bits.to_consensus()),
        "difficulty": header.difficulty_float(),
        "chainwork": format!("{:064x}", chain.tip().work),
        "nTx": 0,
        "previousblockhash": (height > 0).then(|| chain.block_hash(height - 1).expect("previous header").to_string()),
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
    let height = (0..=chain.height()).find(|height| chain.block_hash(*height) == Some(hash));
    let height = height.unwrap_or(0);
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
        "confirmations": chain.height().saturating_sub(height) + 1,
        "height": height,
        "version": block.header.version.to_consensus(),
        "merkleroot": block.header.merkle_root.to_string(),
        "time": block.header.time,
        "nonce": block.header.nonce,
        "bits": format!("{:08x}", block.header.bits.to_consensus()),
        "difficulty": block.header.difficulty_float(),
        "chainwork": format!("{:064x}", chain.tip().work),
        "nTx": block.txdata.len(),
        "size": serialize(&block).len(),
        "weight": block.weight().to_wu(),
        "tx": txs,
        "previousblockhash": (height > 0).then(|| chain.block_hash(height - 1).expect("previous block").to_string()),
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
    let confirmations = blockhash
        .as_ref()
        .map(|_| chain.height().saturating_sub(location.height) + 1);
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
    let txid = node
        .mempool
        .write()
        .accept(transaction, &node.chain.read())?;
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

fn get_txout(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let txid: Txid = param::<String>(params, 0)?.parse()?;
    let vout = param::<u32>(params, 1)?;
    let chain = node.chain.read();
    let outpoint = OutPoint::new(txid, vout);
    let Some(entry) = chain.utxo(&outpoint) else {
        return Ok(Value::Null);
    };
    Ok(json!({
        "bestblock": chain.best_hash().to_string(),
        "confirmations": chain.height().saturating_sub(entry.height) + 1,
        "value": sat_to_btc(entry.output.value.to_sat()),
        "scriptPubKey": script_json(&entry.output.script_pubkey),
        "coinbase": entry.coinbase,
    }))
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
