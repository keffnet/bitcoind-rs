//! Wallet-free Bitcoin Core-style JSON-RPC over HTTP/1.1.

use std::collections::{HashMap, HashSet};
use std::net::{IpAddr, SocketAddr};
use std::str::FromStr;
use std::sync::{Arc, OnceLock, atomic::Ordering};
use std::time::Duration;

use anyhow::{Context, Result, anyhow, bail};
use base64::Engine;
use bitcoin::absolute::LockTime;
use bitcoin::address::AddressType;
use bitcoin::bip158::BlockFilter;
use bitcoin::block::{Header, Version as BlockVersion};
use bitcoin::blockdata::opcodes::all::OP_RETURN;
use bitcoin::blockdata::script::{Builder, Instruction, PushBytesBuf};
use bitcoin::blockdata::transaction::{TxIn, Version};
use bitcoin::blockdata::witness::Witness;
use bitcoin::consensus::encode::{VarInt, deserialize, deserialize_partial, serialize};
use bitcoin::ecdsa::Signature as EcdsaSignature;
use bitcoin::hashes::Hash;
use bitcoin::key::TapTweak;
use bitcoin::psbt::{GetKey, Input as PsbtInput, KeyRequest, Psbt};
use bitcoin::secp256k1::{Message, Secp256k1};
use bitcoin::sighash::{EcdsaSighashType, Prevouts, SighashCache, TapSighashType};
use bitcoin::sign_message::{MessageSignature, signed_msg_hash};
use bitcoin::{
    Address, Amount, Block, BlockHash, Denomination, Network, OutPoint, ScriptBuf, Transaction,
    TxOut, Txid,
};
use miniscript::descriptor::DescriptorType as MiniscriptDescriptorType;
use miniscript::psbt::PsbtExt;
use miniscript::{
    Descriptor as MiniscriptDescriptor, DescriptorPublicKey as MiniscriptPublicKey, Legacy,
    Miniscript, Segwitv0, Tap,
};
use rand::random;
use rand::seq::SliceRandom;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::{OwnedSemaphorePermit, Semaphore, broadcast};
use tokio::task::JoinSet;
use tracing::{debug, warn};

use crate::address::NetworkEndpoint;
use crate::chain;
use crate::config::{OnlyNet, RpcAuth, default_p2p_port};
use crate::mempool::{
    MAX_CLUSTER_COUNT, MAX_CLUSTER_VSIZE, MAX_PACKAGE_COUNT, MAX_PACKAGE_WEIGHT, Mempool,
    MempoolError, MempoolLoadOptions, package_is_child_with_parents_tree,
    package_is_topologically_sorted, package_weight,
};
use crate::validation;
use crate::wire;
use crate::{Node, ScanState};

const MAX_HTTP_REQUEST: usize = 8 * 1024 * 1024;
const DEFAULT_MAX_RAW_TX_FEE_RATE_SAT_PER_KVB: u64 = 10_000_000;
const MAX_SCRIPT_SIZE: usize = 10_000;
const MAX_SCRIPT_ELEMENT_SIZE: usize = 520;
const MAX_OPCODE: u8 = 0xb9;
const MIN_MERKLE_TRANSACTION_WEIGHT: usize = 4 * 60;
const MAX_MERKLE_PROOF_TRANSACTIONS: usize =
    validation::MAX_BLOCK_WEIGHT / MIN_MERKLE_TRANSACTION_WEIGHT;
const SCAN_BLOCKFILTER_BATCH_SIZE: usize = 10_000;
const MEMORY_STATS_ARENA_SIZE: usize = 256 * 1024;

/// Wallet-free replacement for Core's locked allocator bookkeeping. The
/// daemon does not retain private keys and forbids unsafe OS page-locking, so
/// the managed arena is intentionally reported with `locked: 0` rather than
/// claiming that heap pages are non-swappable.
struct MemoryStatsArena {
    bytes: Vec<u8>,
}

impl MemoryStatsArena {
    fn new() -> Self {
        let mut bytes = Vec::with_capacity(MEMORY_STATS_ARENA_SIZE);
        // Keep one byte allocated so Core-compatible stats have a used chunk,
        // while the remaining arena remains available to the manager.
        bytes.push(0);
        Self { bytes }
    }

    fn stats(&self) -> Value {
        let total = self.bytes.capacity();
        let used = self.bytes.len().min(total);
        let free = total.saturating_sub(used);
        json!({
            "used": used,
            "free": free,
            "total": total,
            "locked": 0,
            "chunks_used": usize::from(used > 0),
            "chunks_free": usize::from(free > 0),
        })
    }
}

fn rpc_locked_memory_info() -> Value {
    static ARENA: OnceLock<parking_lot::Mutex<MemoryStatsArena>> = OnceLock::new();
    ARENA
        .get_or_init(|| parking_lot::Mutex::new(MemoryStatsArena::new()))
        .lock()
        .stats()
}

pub struct RpcServer {
    node: Arc<Node>,
}

struct RpcWorkQueue {
    pending: Arc<Semaphore>,
    workers: Arc<Semaphore>,
}

impl RpcWorkQueue {
    fn new(threads: usize, queue_depth: usize) -> Self {
        Self {
            pending: Arc::new(Semaphore::new(threads.saturating_add(queue_depth).max(1))),
            workers: Arc::new(Semaphore::new(threads.max(1))),
        }
    }

    async fn acquire(&self) -> Option<(OwnedSemaphorePermit, OwnedSemaphorePermit)> {
        let pending = self.pending.clone().try_acquire_owned().ok()?;
        let worker = self.workers.clone().acquire_owned().await.ok()?;
        Some((pending, worker))
    }
}

impl RpcServer {
    pub fn new(node: Arc<Node>) -> Self {
        Self { node }
    }

    pub async fn run(self) -> Result<()> {
        let binds = if self.node.config.rpc_binds.is_empty() {
            self.node.config.rpc_bind.into_iter().collect::<Vec<_>>()
        } else {
            self.node.config.rpc_binds.clone()
        };
        if binds.is_empty() {
            return std::future::pending::<Result<()>>().await;
        }
        let work_queue = Arc::new(RpcWorkQueue::new(
            self.node.config.rpc_threads,
            self.node.config.rpc_work_queue,
        ));
        let request_timeout = Duration::from_secs(self.node.config.rpc_server_timeout_secs);
        let mut listeners = JoinSet::new();
        let mut bound = 0usize;
        for address in binds {
            let listener = match TcpListener::bind(address).await {
                Ok(listener) => listener,
                Err(error) => {
                    warn!(%address, %error, "unable to bind RPC listener; continuing");
                    continue;
                }
            };
            bound += 1;
            let node = self.node.clone();
            let work_queue = work_queue.clone();
            listeners.spawn(async move {
                loop {
                    let (stream, peer) = listener.accept().await?;
                    let node = node.clone();
                    let work_queue = work_queue.clone();
                    tokio::spawn(async move {
                        if let Err(error) =
                            handle_connection(node, stream, peer, work_queue, request_timeout).await
                        {
                            debug!(%peer, %error, "RPC connection ended");
                        }
                    });
                }
                #[allow(unreachable_code)]
                Ok::<(), anyhow::Error>(())
            });
        }
        if bound == 0 {
            bail!("unable to bind any RPC listener");
        }
        while let Some(result) = listeners.join_next().await {
            result??;
        }
        Ok(())
    }
}

async fn handle_connection(
    node: Arc<Node>,
    stream: TcpStream,
    peer: SocketAddr,
    work_queue: Arc<RpcWorkQueue>,
    request_timeout: Duration,
) -> Result<()> {
    stream.set_nodelay(true)?;
    let mut connection = HttpConnection::new(stream);
    if !rpc_client_allowed(&node, peer.ip()) {
        connection
            .write_response(
                "403 Forbidden",
                "text/plain",
                b"RPC client address is not allowed\r\n",
                false,
            )
            .await?;
        return Ok(());
    }
    loop {
        let request = match tokio::time::timeout(request_timeout, connection.read_request()).await {
            Ok(request) => request?,
            Err(_) => return Ok(()),
        };
        let Some(request) = request else {
            return Ok(());
        };
        let keep_alive = request.keep_alive;
        let (status, content_type, body) = if node.config.rest
            && (request.method.eq_ignore_ascii_case("GET")
                || request.method.eq_ignore_ascii_case("POST"))
            && request.target.starts_with("/rest/")
        {
            let Some((_pending, _worker)) = work_queue.acquire().await else {
                connection
                    .write_response(
                        "503 Service Unavailable",
                        "text/plain",
                        b"RPC work queue depth exceeded\r\n",
                        false,
                    )
                    .await?;
                return Ok(());
            };
            match tokio::time::timeout(request_timeout, async {
                dispatch_rest_with_body(&node, &request.target, &request.body)
            })
            .await
            {
                Ok(Ok((content_type, body))) => ("200 OK", content_type, body),
                Ok(Err(error)) => (
                    rest_error_status(&error),
                    "text/plain",
                    format!("{error}\r\n").into_bytes(),
                ),
                Err(_) => (
                    "500 Internal Server Error",
                    "text/plain",
                    b"RPC request timed out\r\n".to_vec(),
                ),
            }
        } else {
            if !request.method.eq_ignore_ascii_case("POST") {
                connection
                    .write_response(
                        "405 Method Not Allowed",
                        "text/plain",
                        b"JSON-RPC server handles only POST requests\r\n",
                        false,
                    )
                    .await?;
                return Ok(());
            }
            let Some(username) = authorized_user(&node, &request.headers) else {
                connection
                    .write_response("401 Unauthorized", "text/plain", &[], false)
                    .await?;
                return Ok(());
            };
            if !rpc_request_allowed(&node, &username, &request.body) {
                connection
                    .write_response("403 Forbidden", "text/plain", &[], false)
                    .await?;
                return Ok(());
            }
            let Some((_pending, _worker)) = work_queue.acquire().await else {
                connection
                    .write_response(
                        "503 Service Unavailable",
                        "text/plain",
                        b"RPC work queue depth exceeded\r\n",
                        false,
                    )
                    .await?;
                return Ok(());
            };
            match tokio::time::timeout(
                request_timeout,
                dispatch_json_rpc_http(&node, &request.body),
            )
            .await
            {
                Ok(response) => {
                    let body = response
                        .body
                        .map(|value| {
                            let mut body = serde_json::to_vec(&value)?;
                            body.push(b'\n');
                            Ok::<_, serde_json::Error>(body)
                        })
                        .transpose()?;
                    (
                        response.status,
                        "application/json",
                        body.unwrap_or_default(),
                    )
                }
                Err(_) => (
                    "500 Internal Server Error",
                    "text/plain",
                    b"RPC request timed out\r\n".to_vec(),
                ),
            }
        };
        connection
            .write_response(status, content_type, &body, keep_alive)
            .await?;
        if !keep_alive {
            return Ok(());
        }
    }
}

struct HttpConnection {
    stream: TcpStream,
    buffered: Vec<u8>,
}

impl HttpConnection {
    fn new(stream: TcpStream) -> Self {
        Self {
            stream,
            buffered: Vec::new(),
        }
    }

    async fn read_request(&mut self) -> Result<Option<HttpRequest>> {
        let header_end = loop {
            if let Some(position) = self
                .buffered
                .windows(4)
                .position(|window| window == b"\r\n\r\n")
            {
                break position + 4;
            }
            if self.buffered.len() > MAX_HTTP_REQUEST {
                bail!("HTTP request exceeds limit");
            }
            let mut chunk = [0u8; 4096];
            let read = self.stream.read(&mut chunk).await?;
            if read == 0 {
                if self.buffered.is_empty() {
                    return Ok(None);
                }
                bail!("truncated HTTP request headers");
            }
            self.buffered.extend_from_slice(&chunk[..read]);
        };

        let headers = std::str::from_utf8(&self.buffered[..header_end])?.to_owned();
        let mut request_line = headers
            .lines()
            .next()
            .unwrap_or_default()
            .split_whitespace();
        let method = request_line.next().unwrap_or_default().to_owned();
        let target = request_line.next().unwrap_or_default().to_owned();
        let version = request_line.next().unwrap_or_default();
        let content_length = headers
            .lines()
            .find_map(|line| {
                let (name, value) = line.split_once(':')?;
                name.eq_ignore_ascii_case("Content-Length")
                    .then(|| value.trim().parse::<usize>().ok())
                    .flatten()
            })
            .unwrap_or(0);
        if header_end.saturating_add(content_length) > MAX_HTTP_REQUEST {
            bail!("HTTP request body exceeds limit");
        }
        while self.buffered.len() < header_end + content_length {
            let mut chunk = [0u8; 4096];
            let read = self.stream.read(&mut chunk).await?;
            if read == 0 {
                bail!("truncated HTTP request body");
            }
            self.buffered.extend_from_slice(&chunk[..read]);
            if self.buffered.len() > MAX_HTTP_REQUEST {
                bail!("HTTP request exceeds limit");
            }
        }

        let body_end = header_end + content_length;
        let body = self.buffered[header_end..body_end].to_vec();
        self.buffered.drain(..body_end);
        let keep_alive = if version.eq_ignore_ascii_case("HTTP/1.1") {
            !header_has_token(&headers, "Connection", "close")
        } else {
            header_has_token(&headers, "Connection", "keep-alive")
        };
        Ok(Some(HttpRequest {
            method,
            target,
            headers,
            body,
            keep_alive,
        }))
    }

    async fn write_response(
        &mut self,
        status: &str,
        content_type: &str,
        body: &[u8],
        keep_alive: bool,
    ) -> Result<()> {
        let connection = if keep_alive { "keep-alive" } else { "close" };
        let header = format!(
            "HTTP/1.1 {status}\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\nConnection: {connection}\r\n\r\n",
            body.len()
        );
        self.stream.write_all(header.as_bytes()).await?;
        self.stream.write_all(body).await?;
        self.stream.flush().await?;
        if !keep_alive {
            self.stream.shutdown().await?;
        }
        Ok(())
    }
}

struct HttpRequest {
    method: String,
    target: String,
    headers: String,
    body: Vec<u8>,
    keep_alive: bool,
}

fn header_has_token(headers: &str, wanted_name: &str, wanted_value: &str) -> bool {
    headers.lines().any(|line| {
        let Some((name, value)) = line.split_once(':') else {
            return false;
        };
        name.eq_ignore_ascii_case(wanted_name)
            && value
                .split(',')
                .any(|token| token.trim().eq_ignore_ascii_case(wanted_value))
    })
}

#[cfg(test)]
fn authorized(node: &Arc<Node>, headers: &str) -> bool {
    authorized_user(node, headers).is_some()
}

fn authorized_user(node: &Arc<Node>, headers: &str) -> Option<String> {
    let Some(value) = header_value(headers, "Authorization") else {
        return (node.config.rpc_bind.is_none()
            && node.rpc_cookie.is_none()
            && node.config.rpc_auth.is_empty())
        .then(String::new);
    };
    let encoded = value.trim().strip_prefix("Basic ")?;
    let Ok(decoded) = base64::engine::general_purpose::STANDARD.decode(encoded.trim()) else {
        return None;
    };
    if let Some(cookie) = node.rpc_cookie.as_deref()
        && constant_time_eq(&decoded, cookie.as_bytes())
    {
        return Some("__cookie__".to_owned());
    }
    let Ok(decoded) = String::from_utf8(decoded) else {
        return None;
    };
    let (username, password) = decoded.split_once(':')?;
    node.config
        .rpc_auth
        .iter()
        .any(|auth| match auth {
            RpcAuth::Plain {
                username: expected_username,
                password: expected_password,
            } => {
                constant_time_eq(username.as_bytes(), expected_username.as_bytes())
                    && constant_time_eq(password.as_bytes(), expected_password.as_bytes())
            }
            RpcAuth::Hmac {
                username: expected_username,
                salt,
                hash,
            } => {
                constant_time_eq(username.as_bytes(), expected_username.as_bytes())
                    && constant_time_eq(&hmac_sha256(salt, password.as_bytes()), hash)
            }
        })
        .then(|| username.to_owned())
}

fn rpc_request_allowed(node: &Arc<Node>, username: &str, body: &[u8]) -> bool {
    let user_whitelist = node.config.rpc_whitelist.get(username);
    if user_whitelist.is_none() && node.config.rpc_whitelist_default {
        return false;
    }
    let Some(user_whitelist) = user_whitelist else {
        return true;
    };
    let Ok(request) = serde_json::from_slice::<Value>(body) else {
        return true;
    };
    let method_allowed = |request: &Value| {
        request
            .get("method")
            .and_then(Value::as_str)
            .is_none_or(|method| user_whitelist.contains(method))
    };
    match request {
        Value::Array(requests) => requests.iter().all(method_allowed),
        request => method_allowed(&request),
    }
}

fn rpc_client_allowed(node: &Arc<Node>, address: IpAddr) -> bool {
    address.is_loopback()
        || node
            .config
            .rpc_allow_ips
            .iter()
            .any(|subnet| subnet.contains(address))
}

fn header_value<'a>(headers: &'a str, wanted_name: &str) -> Option<&'a str> {
    headers.lines().find_map(|line| {
        let (name, value) = line.split_once(':')?;
        name.eq_ignore_ascii_case(wanted_name)
            .then_some(value.trim())
    })
}

fn hmac_sha256(key: &[u8], message: &[u8]) -> [u8; 32] {
    const BLOCK_SIZE: usize = 64;
    let mut key_block = [0u8; BLOCK_SIZE];
    if key.len() > BLOCK_SIZE {
        key_block[..32].copy_from_slice(&Sha256::digest(key));
    } else {
        key_block[..key.len()].copy_from_slice(key);
    }
    let mut inner_pad = [0u8; BLOCK_SIZE];
    let mut outer_pad = [0u8; BLOCK_SIZE];
    for index in 0..BLOCK_SIZE {
        inner_pad[index] = key_block[index] ^ 0x36;
        outer_pad[index] = key_block[index] ^ 0x5c;
    }
    let mut inner = Sha256::new();
    inner.update(inner_pad);
    inner.update(message);
    let inner_hash = inner.finalize();
    let mut outer = Sha256::new();
    outer.update(outer_pad);
    outer.update(inner_hash);
    outer.finalize().into()
}

fn constant_time_eq(left: &[u8], right: &[u8]) -> bool {
    let mut difference = (left.len() ^ right.len()) as u8;
    for index in 0..left.len().max(right.len()) {
        difference |= left.get(index).copied().unwrap_or_default()
            ^ right.get(index).copied().unwrap_or_default();
    }
    difference == 0
}

#[cfg(test)]
fn authorization_matches(headers: &str, expected: &str) -> bool {
    headers.lines().any(|line| {
        let Some((name, value)) = line.split_once(':') else {
            return false;
        };
        name.eq_ignore_ascii_case("Authorization") && value.trim() == expected
    })
}

#[cfg(test)]
fn dispatch_rest(node: &Arc<Node>, target: &str) -> Result<(&'static str, Vec<u8>)> {
    dispatch_rest_with_body(node, target, &[])
}

fn dispatch_rest_with_body(
    node: &Arc<Node>,
    target: &str,
    body: &[u8],
) -> Result<(&'static str, Vec<u8>)> {
    let (path, query) = target.split_once('?').unwrap_or((target, ""));
    let route = path
        .strip_prefix("/rest/")
        .ok_or_else(|| anyhow!("invalid REST path"))?;
    let (route, format) = route
        .rsplit_once('.')
        .ok_or_else(|| anyhow!("REST output format is required"))?;
    match route {
        "chaininfo" if format == "json" => rest_json(get_blockchain_info(node)?),
        "mempool/info" if format == "json" => rest_json(dispatch_method(
            node,
            "getmempoolinfo",
            &Value::Array(Vec::new()),
        )?),
        "mempool/contents" if format == "json" => {
            let verbose = rest_query_bool(query, "verbose", true)?;
            let sequence = rest_query_bool(query, "mempool_sequence", false)?;
            rest_json(dispatch_method(
                node,
                "getrawmempool",
                &json!([verbose, sequence]),
            )?)
        }
        route if route.starts_with("blockhashbyheight/") => {
            rest_blockhash_by_height(node, route, format)
        }
        route if route.starts_with("headers/") => rest_headers(node, route, format, query),
        route if route.starts_with("blockpart/") => rest_block_part(node, route, format, query),
        route if route.starts_with("blockfilterheaders/") => {
            rest_block_filter_headers(node, route, format, query)
        }
        route if route.starts_with("blockfilter/") => rest_block_filter(node, route, format),
        route if route.starts_with("block/notxdetails/") => rest_block(node, route, format, false),
        route if route.starts_with("block/") => rest_block(node, route, format, true),
        route if route.starts_with("tx/") => rest_transaction(node, route, format),
        "deploymentinfo" => rest_deployment_info(node, route, format),
        route if route.starts_with("deploymentinfo/") => rest_deployment_info(node, route, format),
        route if route.starts_with("spenttxouts/") => rest_spent_txouts(node, route, format),
        "getutxos" => rest_get_utxos(node, route, format, body),
        route if route.starts_with("getutxos/") => rest_get_utxos(node, route, format, body),
        _ => bail!("unsupported REST endpoint"),
    }
}

fn rest_error_status(error: &anyhow::Error) -> &'static str {
    let message = error.to_string().to_ascii_lowercase();
    if message.contains("internal")
        || message.contains("i/o")
        || message.contains("io error")
        || message.contains("failed to read")
    {
        return "500 Internal Server Error";
    }
    if message.contains("not found")
        || message.contains("not available")
        || message.contains("out of range")
        || message.contains("disabled")
        || message.contains("unsupported rest endpoint")
        || message.contains("unsupported rest output format")
        || message.contains("only the basic rest block filter is available")
        || message.contains("rest blockpart supports binary and hex output only")
        || message.contains("rest deploymentinfo supports json output only")
    {
        return "404 Not Found";
    }
    "400 Bad Request"
}

fn rest_json(value: Value) -> Result<(&'static str, Vec<u8>)> {
    let mut body = serde_json::to_vec(&value)?;
    body.push(b'\n');
    Ok(("application/json", body))
}

fn rest_query_bool(query: &str, name: &str, default: bool) -> Result<bool> {
    let value = query
        .split('&')
        .filter_map(|part| part.split_once('='))
        .find_map(|(key, value)| (key == name).then_some(value))
        .unwrap_or(if default { "true" } else { "false" });
    match value {
        "true" => Ok(true),
        "false" => Ok(false),
        _ => bail!("REST query parameter {name} must be true or false"),
    }
}

fn rest_format_bytes(bytes: Vec<u8>, format: &str) -> Result<(&'static str, Vec<u8>)> {
    match format {
        "bin" => Ok(("application/octet-stream", bytes)),
        "hex" => Ok((
            "text/plain",
            format!("{}\n", hex::encode(bytes)).into_bytes(),
        )),
        _ => bail!("unsupported REST output format"),
    }
}

fn rest_blockhash_by_height(
    node: &Arc<Node>,
    route: &str,
    format: &str,
) -> Result<(&'static str, Vec<u8>)> {
    let height = route
        .strip_prefix("blockhashbyheight/")
        .ok_or_else(|| anyhow!("invalid blockhashbyheight path"))?
        .parse::<u32>()?;
    let hash = node
        .chain
        .read()
        .block_hash(height)
        .ok_or_else(|| anyhow!("block height out of range"))?;
    match format {
        "json" => rest_json(json!({"blockhash": hash.to_string()})),
        "bin" => Ok(("application/octet-stream", hash.to_byte_array().to_vec())),
        "hex" => Ok(("text/plain", format!("{}\n", hash).into_bytes())),
        _ => bail!("unsupported REST output format"),
    }
}

fn rest_headers(
    node: &Arc<Node>,
    route: &str,
    format: &str,
    query: &str,
) -> Result<(&'static str, Vec<u8>)> {
    let suffix = route
        .strip_prefix("headers/")
        .ok_or_else(|| anyhow!("invalid headers path"))?;
    let parts = suffix.split('/').collect::<Vec<_>>();
    let (count, hash_text) = if parts.len() == 2 {
        (parts[0].parse::<u32>()?, parts[1])
    } else if parts.len() == 1 {
        (
            query
                .split('&')
                .filter_map(|part| part.split_once('='))
                .find_map(|(key, value)| (key == "count").then_some(value))
                .unwrap_or("5")
                .parse::<u32>()?,
            parts[0],
        )
    } else {
        bail!("invalid headers path")
    };
    if !(1..=2_000).contains(&count) {
        bail!("header count must be between 1 and 2000")
    }
    let hash: BlockHash = hash_text.parse()?;
    let heights = {
        let chain = node.chain.read();
        let Some(start) = chain.block_height_by_hash(&hash) else {
            return if format == "json" {
                rest_json(json!([]))
            } else {
                rest_format_bytes(Vec::new(), format)
            };
        };
        if !chain.is_active_block(&hash) {
            return if format == "json" {
                rest_json(json!([]))
            } else {
                rest_format_bytes(Vec::new(), format)
            };
        }
        (start..start.saturating_add(count))
            .filter_map(|height| chain.block_hash(height))
            .collect::<Vec<_>>()
    };
    let mut headers = Vec::with_capacity(heights.len());
    for hash in heights {
        let header = node
            .chain
            .read()
            .header_by_hash(&hash)
            .ok_or_else(|| anyhow!("header not found"))?;
        headers.push(header);
    }
    match format {
        "bin" => Ok((
            "application/octet-stream",
            headers.iter().flat_map(serialize).collect(),
        )),
        "hex" => Ok((
            "text/plain",
            format!(
                "{}\n",
                hex::encode(headers.iter().flat_map(serialize).collect::<Vec<_>>())
            )
            .into_bytes(),
        )),
        "json" => {
            let values = headers
                .iter()
                .map(|header| {
                    get_block_header(node, &json!([header.block_hash().to_string(), true]))
                })
                .collect::<Result<Vec<_>>>()?;
            rest_json(json!(values))
        }
        _ => bail!("unsupported REST output format"),
    }
}

fn rest_block(
    node: &Arc<Node>,
    route: &str,
    format: &str,
    details: bool,
) -> Result<(&'static str, Vec<u8>)> {
    let prefix = if details {
        "block/"
    } else {
        "block/notxdetails/"
    };
    let hash_text = route
        .strip_prefix(prefix)
        .ok_or_else(|| anyhow!("invalid block path"))?;
    let hash: BlockHash = hash_text.parse()?;
    let block = node
        .chain
        .write()
        .block(&hash)?
        .ok_or_else(|| anyhow!("block not found"))?;
    match format {
        "json" => rest_json(get_block(
            node,
            // Core's /rest/block endpoint uses SHOW_DETAILS_AND_PREVOUT for
            // the extended JSON form, which is RPC verbosity 3 here.
            &json!([hash.to_string(), if details { 3 } else { 1 }]),
        )?),
        "bin" => Ok(("application/octet-stream", serialize(&block))),
        "hex" => rest_format_bytes(serialize(&block), format),
        _ => bail!("unsupported REST output format"),
    }
}

fn rest_query_usize(query: &str, name: &str) -> Result<usize> {
    query
        .split('&')
        .filter_map(|part| part.split_once('='))
        .find_map(|(key, value)| (key == name).then_some(value))
        .ok_or_else(|| anyhow!("REST query parameter {name} is required"))?
        .parse::<usize>()
        .map_err(|_| anyhow!("REST query parameter {name} must be a non-negative integer"))
}

fn rest_block_part(
    node: &Arc<Node>,
    route: &str,
    format: &str,
    query: &str,
) -> Result<(&'static str, Vec<u8>)> {
    if !matches!(format, "bin" | "hex") {
        bail!("REST blockpart supports binary and hex output only")
    }
    let hash: BlockHash = route
        .strip_prefix("blockpart/")
        .ok_or_else(|| anyhow!("invalid blockpart path"))?
        .parse()?;
    let offset = rest_query_usize(query, "offset")?;
    let size = rest_query_usize(query, "size")?;
    let bytes = node
        .chain
        .write()
        .block(&hash)?
        .ok_or_else(|| anyhow!("block not found"))?;
    let bytes = serialize(&bytes);
    let end = offset
        .checked_add(size)
        .ok_or_else(|| anyhow!("block part range overflows"))?;
    if end > bytes.len() {
        bail!("block part offset/size is outside the block")
    }
    rest_format_bytes(bytes[offset..end].to_vec(), format)
}

fn rest_block_filter(
    node: &Arc<Node>,
    route: &str,
    format: &str,
) -> Result<(&'static str, Vec<u8>)> {
    if !node.config.blockfilterindex {
        bail!("blockfilterindex is not enabled")
    }
    let suffix = route
        .strip_prefix("blockfilter/")
        .ok_or_else(|| anyhow!("invalid blockfilter path"))?;
    let mut parts = suffix.split('/');
    let filter_type = parts.next().unwrap_or_default();
    let hash_text = parts.next().unwrap_or_default();
    if filter_type != "basic" || parts.next().is_some() {
        bail!("only the basic REST block filter is available")
    }
    let hash: BlockHash = hash_text.parse()?;
    let (content, _header) = node
        .chain
        .write()
        .basic_filter_for_block(&hash)?
        .ok_or_else(|| anyhow!("block filter not found"))?;
    match format {
        "bin" | "hex" => rest_format_bytes(serialize_block_filter(&content), format),
        "json" => rest_json(json!({"filter": hex::encode(content)})),
        _ => bail!("unsupported REST output format"),
    }
}

fn serialize_block_filter(content: &[u8]) -> Vec<u8> {
    let mut bytes = serialize(&VarInt::from(content.len() as u64));
    bytes.extend_from_slice(content);
    bytes
}

fn rest_block_filter_headers(
    node: &Arc<Node>,
    route: &str,
    format: &str,
    query: &str,
) -> Result<(&'static str, Vec<u8>)> {
    if !node.config.blockfilterindex {
        bail!("blockfilterindex is not enabled")
    }
    let suffix = route
        .strip_prefix("blockfilterheaders/")
        .ok_or_else(|| anyhow!("invalid blockfilterheaders path"))?;
    let parts = suffix.split('/').collect::<Vec<_>>();
    let (filter_type, count, hash_text) = match parts.as_slice() {
        [filter_type, hash_text] => (
            *filter_type,
            query
                .split('&')
                .filter_map(|part| part.split_once('='))
                .find_map(|(key, value)| (key == "count").then_some(value))
                .unwrap_or("5")
                .parse::<usize>()?,
            *hash_text,
        ),
        [filter_type, count, hash_text] => (*filter_type, count.parse::<usize>()?, *hash_text),
        _ => bail!("invalid blockfilterheaders path"),
    };
    if filter_type != "basic" {
        bail!("only the basic REST block filter is available")
    }
    if !(1..=2_000).contains(&count) {
        bail!("filter header count must be between 1 and 2000")
    }
    let hash: BlockHash = hash_text.parse()?;
    let filter_headers = {
        let mut chain = node.chain.write();
        match chain.block_height_by_hash(&hash) {
            Some(start_height) if chain.is_active_block(&hash) => {
                let end_height = start_height
                    .saturating_add(u32::try_from(count.saturating_sub(1)).unwrap_or(u32::MAX))
                    .min(chain.height());
                (start_height..=end_height)
                    .map(|height| {
                        let block_hash = chain
                            .block_hash(height)
                            .ok_or_else(|| anyhow!("block height out of range"))?;
                        chain
                            .basic_filter_header_for_block(&block_hash)?
                            .ok_or_else(|| anyhow!("block filter headers are not available"))
                    })
                    .collect::<Result<Vec<_>>>()?
            }
            _ => Vec::new(),
        }
    };
    match format {
        "bin" => Ok((
            "application/octet-stream",
            filter_headers.iter().flat_map(serialize).collect(),
        )),
        "hex" => Ok((
            "text/plain",
            format!(
                "{}\n",
                hex::encode(
                    filter_headers
                        .iter()
                        .flat_map(serialize)
                        .collect::<Vec<_>>()
                )
            )
            .into_bytes(),
        )),
        "json" => rest_json(json!(
            filter_headers
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
        )),
        _ => bail!("unsupported REST output format"),
    }
}

fn rest_deployment_info(
    node: &Arc<Node>,
    route: &str,
    format: &str,
) -> Result<(&'static str, Vec<u8>)> {
    if format != "json" {
        bail!("REST deploymentinfo supports JSON output only")
    }
    let params = if route == "deploymentinfo" {
        json!([])
    } else {
        let hash = route
            .strip_prefix("deploymentinfo/")
            .ok_or_else(|| anyhow!("invalid deploymentinfo path"))?;
        if hash.is_empty() || hash.contains('/') {
            bail!("invalid deploymentinfo path")
        }
        json!([hash])
    };
    rest_json(get_deployment_info(node, &params)?)
}

fn serialize_block_undo(undo: &[Vec<TxOut>]) -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend(serialize(&VarInt::from(undo.len() as u64)));
    for outputs in undo {
        bytes.extend(serialize(&VarInt::from(outputs.len() as u64)));
        for output in outputs {
            bytes.extend(serialize(output));
        }
    }
    bytes
}

fn rest_spent_txouts(
    node: &Arc<Node>,
    route: &str,
    format: &str,
) -> Result<(&'static str, Vec<u8>)> {
    let hash: BlockHash = route
        .strip_prefix("spenttxouts/")
        .ok_or_else(|| anyhow!("invalid spenttxouts path"))?
        .parse()?;
    let undo = node
        .chain
        .write()
        .spent_outputs_by_transaction(&hash)?
        .ok_or_else(|| anyhow!("block undo not found"))?;
    match format {
        "bin" | "hex" => rest_format_bytes(serialize_block_undo(&undo), format),
        "json" => rest_json(json!(
            undo.iter()
                .map(|outputs| {
                    outputs
                        .iter()
                        .map(|output| {
                            json!({
                                "value": output.value.to_btc(),
                                "scriptPubKey": script_json_with_network(
                                    &output.script_pubkey,
                                    Some(node.config.network),
                                ),
                            })
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        )),
        _ => bail!("unsupported REST output format"),
    }
}

fn rest_transaction(
    node: &Arc<Node>,
    route: &str,
    format: &str,
) -> Result<(&'static str, Vec<u8>)> {
    let txid = route
        .strip_prefix("tx/")
        .ok_or_else(|| anyhow!("invalid transaction path"))?;
    let raw = get_raw_transaction(node, &json!([txid, false]))?;
    let raw = raw
        .as_str()
        .ok_or_else(|| anyhow!("raw transaction response is not hex"))?;
    match format {
        "json" => {
            let mut transaction = get_raw_transaction(node, &json!([txid, true]))?;
            if let Some(object) = transaction.as_object_mut() {
                object.remove("confirmations");
                object.remove("time");
                object.remove("blocktime");
            }
            rest_json(transaction)
        }
        "bin" => Ok(("application/octet-stream", hex::decode(raw)?)),
        "hex" => Ok(("text/plain", format!("{raw}\n").into_bytes())),
        _ => bail!("unsupported REST output format"),
    }
}

fn rest_get_utxos(
    node: &Arc<Node>,
    route: &str,
    format: &str,
    body: &[u8],
) -> Result<(&'static str, Vec<u8>)> {
    let suffix = route
        .strip_prefix("getutxos")
        .ok_or_else(|| anyhow!("invalid getutxos path"))?
        .strip_prefix('/')
        .unwrap_or_default();
    let (uri_check_mempool, uri_outpoints) =
        if let Some(outpoints) = suffix.strip_prefix("checkmempool/") {
            (true, outpoints)
        } else {
            (false, suffix)
        };
    let uri_outpoints = if uri_outpoints.is_empty() {
        Vec::new()
    } else {
        uri_outpoints
            .split('/')
            .map(|value| {
                let (txid, vout) = value
                    .rsplit_once('-')
                    .ok_or_else(|| anyhow!("invalid getutxos outpoint"))?;
                Ok(OutPoint::new(txid.parse()?, vout.parse()?))
            })
            .collect::<Result<Vec<_>>>()?
    };

    let (check_mempool, outpoints) = match format {
        "json" => {
            if body.is_empty() {
                if uri_outpoints.is_empty() {
                    bail!("getutxos request is empty")
                }
                (uri_check_mempool, uri_outpoints)
            } else {
                bail!("JSON getutxos requests must use URI outpoints")
            }
        }
        "bin" | "hex" => {
            if !body.is_empty() && !uri_outpoints.is_empty() {
                bail!("getutxos cannot combine URI outpoints with a request body")
            }
            if body.is_empty() {
                if uri_outpoints.is_empty() {
                    bail!("getutxos request is empty")
                }
                (uri_check_mempool, uri_outpoints)
            } else {
                let request_body = if format == "hex" {
                    hex::decode(body).context("invalid getutxos hexadecimal request")?
                } else {
                    body.to_vec()
                };
                let (check_mempool, outpoints) = deserialize_get_utxos_request(&request_body)?;
                (check_mempool, outpoints)
            }
        }
        _ => bail!("unsupported REST output format"),
    };
    if outpoints.len() > 15 {
        bail!("getutxos accepts at most 15 outpoints")
    }
    let chain = node.chain.read();
    let mempool = check_mempool.then(|| node.mempool.read());
    let mut bitmap = vec![0u8; outpoints.len().div_ceil(8)];
    let mut bitmap_string = String::with_capacity(outpoints.len());
    let mut utxos = Vec::new();
    for (index, outpoint) in outpoints.iter().enumerate() {
        let mut value = chain.utxo(outpoint).map(|entry| {
            (
                entry.height | if entry.coinbase { 1 << 31 } else { 0 },
                entry.output.clone(),
            )
        });
        if let Some(pool) = mempool.as_ref()
            && pool.is_spent(outpoint)
        {
            value = None;
        }
        if value.is_none()
            && let Some(pool) = mempool.as_ref()
            && let Some(entry) = pool.get(&outpoint.txid)
            && let Some(output) = entry.transaction.output.get(outpoint.vout as usize)
            && !pool.is_spent(outpoint)
        {
            value = Some((0, output.clone()));
        }
        if let Some((height, output)) = value {
            bitmap[index / 8] |= 1 << (index % 8);
            bitmap_string.push('1');
            utxos.push((height, output));
        } else {
            bitmap_string.push('0');
        }
    }
    let chain_height = chain.height();
    let chain_tip = chain.best_hash();
    if format == "json" {
        return rest_json(json!({
            "chainHeight": chain_height,
            "chaintipHash": chain_tip.to_string(),
            "bitmap": bitmap_string,
            "utxos": utxos
                .iter()
                .map(|(height, output)| json!({
                    "height": height,
                    "value": output.value.to_btc(),
                    "scriptPubKey": script_json_with_network(
                        &output.script_pubkey,
                        Some(node.config.network),
                    ),
                }))
                .collect::<Vec<_>>(),
        }));
    }

    // BIP64's binary response is: active height, active tip hash, bitmap,
    // and a vector of CCoin records.  Each CCoin starts with a reserved
    // transaction-version field for compatibility with Core's serializer.
    let mut response = serialize(&(chain_height, chain_tip, bitmap));
    response.extend(serialize(&VarInt::from(utxos.len() as u64)));
    for (height, output) in &utxos {
        response.extend(serialize(&(0u32, *height, output)));
    }
    rest_format_bytes(response, format)
}

fn deserialize_get_utxos_request(bytes: &[u8]) -> Result<(bool, Vec<OutPoint>)> {
    let (check_mempool, mut consumed) =
        deserialize_partial::<bool>(bytes).context("invalid getutxos request")?;
    let (count, count_consumed) =
        deserialize_partial::<VarInt>(&bytes[consumed..]).context("invalid getutxos request")?;
    consumed = consumed.saturating_add(count_consumed);
    let count = usize::try_from(count.0).context("getutxos request has too many outpoints")?;
    if count > 15 {
        bail!("getutxos accepts at most 15 outpoints")
    }
    let mut outpoints = Vec::with_capacity(count);
    for _ in 0..count {
        let (outpoint, outpoint_consumed) = deserialize_partial::<OutPoint>(&bytes[consumed..])
            .context("invalid getutxos request")?;
        consumed = consumed.saturating_add(outpoint_consumed);
        outpoints.push(outpoint);
    }
    if consumed != bytes.len() {
        bail!("invalid getutxos request: trailing data")
    }
    Ok((check_mempool, outpoints))
}

struct JsonRpcHttpResponse {
    status: &'static str,
    body: Option<Value>,
}

#[cfg(test)]
async fn dispatch_json_rpc(node: &Arc<Node>, body: &[u8]) -> Option<Value> {
    dispatch_json_rpc_http(node, body).await.body
}

async fn dispatch_json_rpc_http(node: &Arc<Node>, body: &[u8]) -> JsonRpcHttpResponse {
    let request: Value = match serde_json::from_slice(body) {
        Ok(value) => value,
        Err(error) => {
            return JsonRpcHttpResponse {
                status: "500 Internal Server Error",
                body: Some(
                    json!({"result": null, "error": {"code": -32700, "message": error.to_string()}, "id": null}),
                ),
            };
        }
    };
    if let Some(batch) = request.as_array() {
        if batch.is_empty() {
            return JsonRpcHttpResponse {
                status: "200 OK",
                body: Some(Value::Array(Vec::new())),
            };
        }
        let mut responses = Vec::with_capacity(batch.len());
        for request in batch {
            if let Some(response) = dispatch_request(node, request).await {
                responses.push(response);
            }
        }
        return if responses.is_empty() {
            JsonRpcHttpResponse {
                status: "204 No Content",
                body: None,
            }
        } else {
            JsonRpcHttpResponse {
                status: "200 OK",
                body: Some(Value::Array(responses)),
            }
        };
    }
    let body = dispatch_request(node, &request).await;
    let status = match body.as_ref() {
        Some(response) => {
            let is_json_rpc_2 = request.get("jsonrpc").and_then(Value::as_str) == Some("2.0");
            let is_invalid_request = response
                .get("error")
                .and_then(|error| error.get("code"))
                .and_then(Value::as_i64)
                == Some(-32600);
            if is_json_rpc_2 && !is_invalid_request {
                "200 OK"
            } else {
                json_rpc_error_status(response)
            }
        }
        None => "204 No Content",
    };
    JsonRpcHttpResponse { status, body }
}

async fn dispatch_request(node: &Arc<Node>, request: &Value) -> Option<Value> {
    let Some(request_object) = request.as_object() else {
        return Some(json_rpc_invalid_request(
            Value::Null,
            false,
            "Invalid Request object",
        ));
    };
    let id = request.get("id").cloned().unwrap_or(Value::Null);
    let json_rpc_2 = match request.get("jsonrpc") {
        None | Some(Value::Null) => false,
        Some(Value::String(value)) if value == "1.0" => false,
        Some(Value::String(value)) if value == "2.0" => true,
        Some(_) => {
            return Some(json_rpc_invalid_request(
                id,
                false,
                "JSON-RPC version not supported",
            ));
        }
    };
    let is_notification = json_rpc_2 && !request_object.contains_key("id");
    let Some(method) = request_object.get("method").and_then(Value::as_str) else {
        return Some(json_rpc_invalid_request(id, json_rpc_2, "Missing method"));
    };
    let params = match request_object.get("params") {
        None | Some(Value::Null) => Value::Array(Vec::new()),
        Some(Value::Array(values)) => Value::Array(values.clone()),
        Some(Value::Object(values)) => Value::Object(values.clone()),
        Some(_) => {
            return Some(json_rpc_invalid_request(
                id,
                json_rpc_2,
                "Params must be an array or object",
            ));
        }
    };
    let response = match dispatch_method_async(node, method, &params).await {
        Ok(result) if json_rpc_2 => json!({
            "jsonrpc": "2.0",
            "result": result,
            "id": id,
        }),
        Err(error) if json_rpc_2 => json!({
            "jsonrpc": "2.0",
            "error": rpc_error(&error),
            "id": id,
        }),
        Ok(result) => json!({"result": result, "error": null, "id": id}),
        Err(error) => json!({"result": null, "error": rpc_error(&error), "id": id}),
    };
    (!is_notification).then_some(response)
}

fn json_rpc_invalid_request(id: Value, json_rpc_2: bool, message: &str) -> Value {
    if json_rpc_2 {
        json!({
            "jsonrpc": "2.0",
            "error": {"code": -32600, "message": message},
            "id": id,
        })
    } else {
        json!({
            "result": null,
            "error": {"code": -32600, "message": message},
            "id": id,
        })
    }
}

fn json_rpc_error_status(response: &Value) -> &'static str {
    match response
        .get("error")
        .and_then(Value::as_object)
        .and_then(|error| error.get("code"))
        .and_then(Value::as_i64)
    {
        Some(-32600) => "400 Bad Request",
        Some(-32601) => "404 Not Found",
        Some(_) => "500 Internal Server Error",
        None => "200 OK",
    }
}

async fn dispatch_method_async(node: &Arc<Node>, method: &str, params: &Value) -> Result<Value> {
    let normalized_params = normalize_rpc_params(method, params)?;
    let command_id = node.begin_rpc_command(method);
    let result = match method {
        "stop" => match stop_wait(&normalized_params) {
            Ok(wait) => {
                node.request_shutdown();
                if let Some(wait) = wait {
                    tokio::time::sleep(wait).await;
                }
                Ok(json!("bitcoind stopping"))
            }
            Err(error) => Err(error),
        },
        "waitfornewblock" => wait_for_new_block(node, &normalized_params).await,
        "waitforblock" => wait_for_block(node, &normalized_params).await,
        "waitforblockheight" => wait_for_block_height(node, &normalized_params).await,
        "getblocktemplate" => get_block_template_async(node, &normalized_params).await,
        "scantxoutset" | "scanblocks" => {
            let node = node.clone();
            let method = method.to_owned();
            let params = normalized_params.clone();
            match tokio::task::spawn_blocking(move || dispatch_method(&node, &method, &params))
                .await
            {
                Ok(result) => result,
                Err(error) => Err(anyhow!("scan RPC task failed: {error}")),
            }
        }
        _ => dispatch_method(node, method, &normalized_params),
    };
    node.end_rpc_command(command_id);
    result
}

fn stop_wait(params: &Value) -> Result<Option<std::time::Duration>> {
    let Some(value) = params.get(0).filter(|value| !value.is_null()) else {
        return Ok(None);
    };
    let milliseconds = value
        .as_i64()
        .ok_or_else(|| anyhow!("wait must be a non-negative integer"))?;
    let milliseconds =
        u64::try_from(milliseconds).map_err(|_| anyhow!("wait must be a non-negative integer"))?;
    Ok(Some(std::time::Duration::from_millis(milliseconds)))
}

fn normalize_rpc_params(method: &str, params: &Value) -> Result<Value> {
    if params.is_array() {
        if let Some(names) = rpc_parameter_names(method)
            && params
                .as_array()
                .is_some_and(|values| values.len() > names.len())
        {
            bail!("too many positional arguments for {method}")
        }
        return Ok(params.clone());
    }
    let Some(object) = params.as_object() else {
        bail!("RPC params must be an array or object")
    };
    if matches!(method, "echo" | "echojson") {
        let mut values = object
            .get("args")
            .map(|args| {
                args.as_array()
                    .cloned()
                    .ok_or_else(|| anyhow!("RPC args must be an array"))
            })
            .transpose()?
            .unwrap_or_default();
        if values.len() > 10 {
            bail!("too many positional arguments for {method}")
        }
        let mut specified = vec![true; values.len()];
        for (name, value) in object {
            if name == "args" {
                continue;
            }
            let Some(index) = name
                .strip_prefix("arg")
                .and_then(|index| index.parse::<usize>().ok())
                .filter(|index| *index < 10)
            else {
                bail!("unknown named parameter {name} for {method}")
            };
            if specified.get(index).copied().unwrap_or(false) {
                bail!("parameter {name} specified more than once")
            }
            values.resize(index.saturating_add(1), Value::Null);
            specified.resize(index.saturating_add(1), false);
            values[index] = value.clone();
            specified[index] = true;
        }
        return Ok(Value::Array(values));
    }
    let Some(names) = rpc_parameter_names(method) else {
        bail!("named parameters are not supported for {method}")
    };
    let mut values = vec![Value::Null; names.len()];
    let mut specified = vec![false; names.len()];
    if let Some(args) = object.get("args") {
        let args = args
            .as_array()
            .ok_or_else(|| anyhow!("RPC args must be an array"))?;
        if args.len() > names.len() {
            bail!("too many positional arguments for {method}")
        }
        for (index, value) in args.iter().enumerate() {
            values[index] = value.clone();
            specified[index] = true;
        }
    }
    for (name, value) in object {
        if name == "args" {
            continue;
        }
        let lookup_name = rpc_parameter_alias(method, name).unwrap_or(name);
        let Some(index) = names.iter().position(|candidate| *candidate == lookup_name) else {
            bail!("unknown named parameter {name} for {method}")
        };
        if specified[index] {
            bail!("parameter {name} specified more than once")
        }
        values[index] = if method == "dumptxoutset" && name == "rollback" {
            json!({"rollback": value})
        } else if method == "gettxspendingprevout"
            && matches!(name.as_str(), "mempool_only" | "return_spending_tx")
        {
            json!({name: value})
        } else if method == "scanblocks" && name == "filter_false_positives" {
            json!({"filter_false_positives": value})
        } else {
            value.clone()
        };
        specified[index] = true;
    }
    Ok(Value::Array(values))
}

fn rpc_parameter_alias(method: &str, name: &str) -> Option<&'static str> {
    match (method, name) {
        ("getblock" | "getrawtransaction", "verbose") => Some("verbosity"),
        ("dumptxoutset", "rollback") => Some("options"),
        ("gettxspendingprevout", "mempool_only" | "return_spending_tx") => Some("options"),
        ("scanblocks", "filter_false_positives") => Some("options"),
        _ => None,
    }
}

fn rpc_parameter_names(method: &str) -> Option<&'static [&'static str]> {
    match method {
        "stop" => Some(&["wait"]),
        "help" => Some(&["command"]),
        "getdeploymentinfo" => Some(&["blockhash"]),
        "getblockhash" => Some(&["height"]),
        "getblockheader" => Some(&["blockhash", "verbose"]),
        "getblock" => Some(&["blockhash", "verbosity"]),
        "getblockfilter" => Some(&["blockhash", "filtertype"]),
        "getblockstats" => Some(&["hash_or_height", "stats"]),
        "getchaintxstats" => Some(&["nblocks", "blockhash"]),
        "getnetworkhashps" => Some(&["nblocks", "height"]),
        "gettxoutproof" => Some(&["txids", "blockhash"]),
        "verifytxoutproof" => Some(&["proof"]),
        "submitheader" => Some(&["hexdata"]),
        "getblockfrompeer" => Some(&["blockhash", "peer_id"]),
        "invalidateblock" | "reconsiderblock" | "preciousblock" => Some(&["blockhash"]),
        "getrawtransaction" => Some(&["txid", "verbosity", "blockhash"]),
        "decoderawtransaction" => Some(&["hexstring", "iswitness"]),
        "createrawtransaction" => {
            Some(&["inputs", "outputs", "locktime", "replaceable", "version"])
        }
        "decodescript" => Some(&["hexstring"]),
        "combinerawtransaction" => Some(&["txs"]),
        "createpsbt" => Some(&["inputs", "outputs", "locktime", "replaceable", "version"]),
        "decodepsbt" | "analyzepsbt" => Some(&["psbt"]),
        "finalizepsbt" => Some(&["psbt", "extract"]),
        "converttopsbt" => Some(&["hexstring", "permitsigdata", "iswitness"]),
        "combinepsbt" | "joinpsbts" => Some(&["txs"]),
        "utxoupdatepsbt" => Some(&["psbt", "descriptors"]),
        "descriptorprocesspsbt" => Some(&[
            "psbt",
            "descriptors",
            "sighashtype",
            "bip32derivs",
            "finalize",
        ]),
        "signmessagewithprivkey" => Some(&["privkey", "message"]),
        "verifymessage" => Some(&["address", "signature", "message"]),
        "createmultisig" => Some(&["nrequired", "keys", "address_type"]),
        "sendrawtransaction" => Some(&["hexstring", "maxfeerate", "maxburnamount"]),
        "abortprivatebroadcast" => Some(&["txid"]),
        "signrawtransactionwithkey" => Some(&["hexstring", "privkeys", "prevtxs", "sighashtype"]),
        "submitblock" => Some(&["hexdata", "dummy"]),
        "getblocktemplate" => Some(&["template_request"]),
        "prioritisetransaction" => Some(&["txid", "dummy", "fee_delta"]),
        "generatetoaddress" => Some(&["nblocks", "address", "maxtries"]),
        "generatetodescriptor" => Some(&["num_blocks", "descriptor", "maxtries"]),
        "generateblock" => Some(&["output", "transactions", "submit"]),
        "generate" => Some(&[]),
        "submitpackage" => Some(&["package", "maxfeerate", "maxburnamount"]),
        "testmempoolaccept" => Some(&["rawtxs", "maxfeerate"]),
        "setmocktime" => Some(&["timestamp"]),
        "mockscheduler" => Some(&["delta_time"]),
        "echoipc" => Some(&["arg"]),
        "verifychain" => Some(&["checklevel", "nblocks"]),
        "getmemoryinfo" => Some(&["mode"]),
        "gettxout" => Some(&["txid", "n", "include_mempool"]),
        "gettxspendingprevout" => Some(&["outputs", "options"]),
        "getrawmempool" => Some(&["verbose", "mempool_sequence"]),
        "getmempoolentry" => Some(&["txid"]),
        "getmempoolancestors" | "getmempooldescendants" => Some(&["txid", "verbose"]),
        "getorphantxs" => Some(&["verbosity"]),
        "getmempoolcluster" => Some(&["txid"]),
        "importmempool" => Some(&["filepath", "options"]),
        "gettxoutsetinfo" => Some(&["hash_type", "hash_or_height", "use_index"]),
        "dumptxoutset" => Some(&["path", "type", "options"]),
        "loadtxoutset" => Some(&["path"]),
        "pruneblockchain" => Some(&["height"]),
        "waitfornewblock" => Some(&["timeout", "current_tip"]),
        "waitforblock" => Some(&["blockhash", "timeout"]),
        "waitforblockheight" => Some(&["height", "timeout"]),
        "scantxoutset" => Some(&["action", "scanobjects"]),
        "scanblocks" => Some(&[
            "action",
            "scanobjects",
            "start_height",
            "stop_height",
            "filtertype",
            "options",
        ]),
        "getdescriptoractivity" => Some(&["blockhashes", "scanobjects", "include_mempool"]),
        "getnodeaddresses" => Some(&["count", "network"]),
        "addpeeraddress" => Some(&["address", "port", "tried"]),
        "sendmsgtopeer" => Some(&["peer_id", "msg_type", "msg"]),
        "addconnection" => Some(&["address", "connection_type", "v2transport"]),
        "addnode" => Some(&["node", "command", "v2transport"]),
        "disconnectnode" => Some(&["address", "nodeid"]),
        "getaddednodeinfo" => Some(&["node"]),
        "setban" => Some(&["subnet", "command", "bantime", "absolute"]),
        "setnetworkactive" => Some(&["state"]),
        "estimatesmartfee" => Some(&["conf_target", "estimate_mode"]),
        "estimaterawfee" => Some(&["conf_target", "threshold"]),
        "logging" => Some(&["include", "exclude"]),
        "validateaddress" => Some(&["address"]),
        "deriveaddresses" => Some(&["descriptor", "range"]),
        "getdescriptorinfo" => Some(&["descriptor"]),
        "getblockchaininfo"
        | "getblockcount"
        | "getbestblockhash"
        | "getmininginfo"
        | "getprioritisedtransactions"
        | "getmempoolinfo"
        | "getmempoolfeeratediagram"
        | "savemempool"
        | "getchainstates"
        | "getchaintips"
        | "getnetworkinfo"
        | "getpeerinfo"
        | "getnettotals"
        | "getaddrmaninfo"
        | "getrawaddrman"
        | "listbanned"
        | "clearbanned"
        | "ping"
        | "getrpcinfo"
        | "getdifficulty"
        | "getconnectioncount"
        | "uptime"
        | "getzmqnotifications"
        | "syncwithvalidationinterfacequeue"
        | "getprivatebroadcastinfo" => Some(&[]),
        "getindexinfo" => Some(&["index_name"]),
        _ => None,
    }
}

fn dispatch_method(node: &Arc<Node>, method: &str, params: &Value) -> Result<Value> {
    match method {
        "stop" => {
            let wait = stop_wait(params)?;
            node.request_shutdown();
            if let Some(wait) = wait {
                std::thread::sleep(wait);
            }
            Ok(json!("bitcoind stopping"))
        }
        "getblockchaininfo" => get_blockchain_info(node),
        "getdeploymentinfo" => get_deployment_info(node, params),
        "getblockcount" => Ok(json!(node.chain.read().height())),
        "getbestblockhash" => Ok(json!(node.chain.read().best_hash().to_string())),
        "getblockhash" => {
            let height = params
                .get(0)
                .and_then(Value::as_i64)
                .or_else(|| {
                    params
                        .get(0)
                        .and_then(Value::as_u64)
                        .and_then(|height| i64::try_from(height).ok())
                })
                .ok_or_else(|| anyhow!("height must be an integer"))?;
            if height < 0 {
                bail!("Block height out of range")
            }
            let height = u32::try_from(height).map_err(|_| anyhow!("Block height out of range"))?;
            node.chain
                .read()
                .block_hash(height)
                .map(|hash| json!(hash.to_string()))
                .ok_or_else(|| anyhow!("Block height out of range"))
        }
        "getblockheader" => get_block_header(node, params),
        "getblock" => get_block(node, params),
        "getblockfilter" => get_block_filter(node, params),
        "getblockstats" => get_block_stats(node, params),
        "getchaintxstats" => get_chain_tx_stats(node, params),
        "getnetworkhashps" => get_network_hash_ps(node, params),
        "gettxoutproof" => get_txout_proof(node, params),
        "verifytxoutproof" => verify_txout_proof(node, params),
        "submitheader" => submit_header(node, params),
        "getblockfrompeer" => get_block_from_peer(node, params),
        "invalidateblock" => invalidate_block(node, params),
        "reconsiderblock" => reconsider_block(node, params),
        "preciousblock" => precious_block(node, params),
        "getrawtransaction" => get_raw_transaction(node, params),
        "decoderawtransaction" => decode_raw_transaction(node, params),
        "createrawtransaction" => create_raw_transaction(node, params),
        "decodescript" => decode_script(node, params),
        "combinerawtransaction" => combine_raw_transaction(node, params),
        "createpsbt" => create_psbt(node, params),
        "decodepsbt" => decode_psbt(node, params),
        "converttopsbt" => convert_to_psbt(params),
        "analyzepsbt" => analyze_psbt(params),
        "combinepsbt" => combine_psbt(params),
        "joinpsbts" => join_psbts(params),
        "finalizepsbt" => finalize_psbt(params),
        "utxoupdatepsbt" => update_psbt_utxos(node, params),
        "descriptorprocesspsbt" => descriptor_process_psbt(node, params),
        "signmessagewithprivkey" => sign_message_with_private_key(params),
        "verifymessage" => verify_message(node, params),
        "createmultisig" => create_multisig(node, params),
        "sendrawtransaction" => send_raw_transaction(node, params),
        "getprivatebroadcastinfo" => Ok(private_broadcast_info(node)),
        "abortprivatebroadcast" => abort_private_broadcast(node, params),
        "signrawtransactionwithkey" => sign_raw_transaction_with_key(node, params),
        "submitblock" => submit_block(node, params),
        "getblocktemplate" => get_block_template(node, params),
        "getmininginfo" => get_mining_info(node),
        "prioritisetransaction" => prioritise_transaction(node, params),
        "getprioritisedtransactions" => get_prioritised_transactions(node),
        "generatetoaddress" => generate_to_address(node, params),
        "generatetodescriptor" => generate_to_descriptor(node, params),
        "generateblock" => generate_block(node, params),
        "generate" => bail!(
            "generate\n\nhas been replaced by the -generate cli option. Refer to -help for more information."
        ),
        "submitpackage" => submit_package(node, params),
        "testmempoolaccept" => test_mempool_accept(node, params),
        "setmocktime" => set_mock_time(node, params),
        "mockscheduler" => mock_scheduler(node, params),
        "echo" | "echojson" => Ok(params.clone()),
        "echoipc" => Ok(json!(param::<String>(params, 0)?)),
        "verifychain" => {
            let checklevel = params
                .get(0)
                .filter(|value| !value.is_null())
                .map(|value| {
                    value
                        .as_i64()
                        .ok_or_else(|| anyhow!("checklevel must be an integer"))
                })
                .transpose()?
                .unwrap_or(3);
            if !(0..=4).contains(&checklevel) {
                bail!("checklevel must be between 0 and 4")
            }
            let checkblocks = params
                .get(1)
                .filter(|value| !value.is_null())
                .map(|value| {
                    value
                        .as_i64()
                        .ok_or_else(|| anyhow!("nblocks must be an integer"))
                })
                .transpose()?
                .unwrap_or(6);
            if checkblocks < 0 {
                bail!("nblocks must not be negative")
            }
            let depth = u32::try_from(checkblocks).map_err(|_| anyhow!("nblocks is too large"))?;
            let verified = node
                .chain
                .write()
                .verify_active_chain_with_level(checklevel as u8, depth)
                .is_ok();
            Ok(Value::Bool(verified))
        }
        "getmemoryinfo" => get_memory_info(params),
        "gettxout" => get_txout(node, params),
        "gettxspendingprevout" => get_tx_spending_prevout(node, params),
        "getmempoolinfo" => {
            let mut mempool = node.mempool.write();
            let total_fee = mempool
                .transaction_order()
                .into_iter()
                .filter_map(|txid| mempool.get(&txid))
                .map(|entry| entry.fee_sat)
                .sum::<u64>();
            Ok(json!({
                "loaded": true,
                "size": mempool.len(),
                "bytes": mempool.vbytes(),
                "usage": mempool.dynamic_memory_usage(),
                "maxmempool": mempool.max_bytes(),
                "mempoolminfee": sat_to_btc(mempool.mempool_min_fee_sat_per_kvb()),
                "minrelaytxfee": sat_to_btc(mempool.min_relay_fee_sat_per_kvb()),
                "unbroadcastcount": mempool.unbroadcast_txids().len(),
                "incrementalrelayfee": sat_to_btc(mempool.incremental_relay_fee_sat_per_kvb()),
                "total_fee": sat_to_btc(total_fee),
                "fullrbf": true,
                "permitbaremultisig": mempool.permit_bare_multisig(),
                "maxdatacarriersize": mempool.max_datacarrier_bytes().unwrap_or_default(),
                "limitclustercount": MAX_CLUSTER_COUNT,
                "limitclustersize": MAX_CLUSTER_VSIZE,
                "optimal": true,
            }))
        }
        "getrawmempool" => {
            let verbose = optional_bool(params, 0, false, "verbose")?;
            let include_sequence = optional_bool(params, 1, false, "mempool_sequence")?;
            if verbose && include_sequence {
                bail!("Verbose results cannot contain mempool sequence values.")
            }
            let mempool = node.mempool.read();
            let order = mempool.main_order();
            if verbose {
                Ok(Value::Object(
                    order
                        .iter()
                        .map(|txid| Ok((txid.to_string(), mempool_entry_json(&mempool, txid)?)))
                        .collect::<Result<Vec<(String, Value)>>>()?
                        .into_iter()
                        .collect(),
                ))
            } else {
                let txids = order
                    .into_iter()
                    .map(|txid| txid.to_string())
                    .collect::<Vec<_>>();
                if include_sequence {
                    Ok(json!({
                        "txids": txids,
                        "mempool_sequence": mempool.sequence(),
                    }))
                } else {
                    Ok(json!(txids))
                }
            }
        }
        "getorphantxs" => get_orphan_transactions(node, params),
        "getmempoolentry" => {
            let txid: Txid = param::<String>(params, 0)?.parse()?;
            let mempool = node.mempool.read();
            mempool_entry_json(&mempool, &txid)
        }
        "getmempoolancestors" => get_mempool_relationship(node, params, true),
        "getmempooldescendants" => get_mempool_relationship(node, params, false),
        "getmempoolcluster" => get_mempool_cluster(node, params),
        "getmempoolfeeratediagram" => get_mempool_fee_rate_diagram(node),
        "savemempool" => {
            node.persist_mempool()?;
            Ok(json!({
                "filename": node.config.datadir.join("mempool.dat").to_string_lossy(),
            }))
        }
        "importmempool" => {
            if node.chain.read().is_initial_block_download() {
                bail!("Can only import the mempool after the block download and sync is done.");
            }
            let path = param::<String>(params, 0)?;
            let options = params
                .get(1)
                .filter(|value| !value.is_null())
                .map(|value| {
                    value
                        .as_object()
                        .ok_or_else(|| anyhow!("options must be an object"))
                })
                .transpose()?;
            let use_current_time = options
                .and_then(|options| options.get("use_current_time"))
                .filter(|value| !value.is_null())
                .map(|value| {
                    value
                        .as_bool()
                        .ok_or_else(|| anyhow!("use_current_time must be a boolean"))
                })
                .transpose()?
                .unwrap_or(true);
            let apply_fee_delta_priority = options
                .and_then(|options| options.get("apply_fee_delta_priority"))
                .filter(|value| !value.is_null())
                .map(|value| {
                    value
                        .as_bool()
                        .ok_or_else(|| anyhow!("apply_fee_delta_priority must be a boolean"))
                })
                .transpose()?
                .unwrap_or(false);
            let apply_unbroadcast_set = options
                .and_then(|options| options.get("apply_unbroadcast_set"))
                .filter(|value| !value.is_null())
                .map(|value| {
                    value
                        .as_bool()
                        .ok_or_else(|| anyhow!("apply_unbroadcast_set must be a boolean"))
                })
                .transpose()?
                .unwrap_or(false);
            node.import_mempool_with_options(
                path,
                MempoolLoadOptions {
                    use_current_time,
                    apply_fee_delta_priority,
                    apply_unbroadcast_set,
                },
            )
            .map_err(|error| {
                anyhow!("Unable to import mempool file, see debug.log for details: {error}")
            })?;
            Ok(json!({}))
        }
        "gettxoutsetinfo" => get_txout_set_info(node, params),
        "dumptxoutset" => dump_txoutset(node, params),
        "loadtxoutset" => load_txoutset(node, params),
        "pruneblockchain" => prune_blockchain(node, params),
        "scantxoutset" => scan_txout_set(node, params),
        "scanblocks" => scan_blocks(node, params),
        "getdescriptoractivity" => get_descriptor_activity(node, params),
        "getchainstates" => get_chain_states(node),
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
        "getnetworkinfo" => {
            let network_service = if node.chain.read().is_pruned() {
                wire::NODE_NETWORK_LIMITED
            } else {
                wire::NODE_NETWORK
            };
            let local_services = network_service
                | wire::NODE_WITNESS
                | if node.config.v2_transport {
                    wire::NODE_P2P_V2
                } else {
                    0
                }
                | if node.config.blockfilterindex && node.config.peer_block_filters {
                    wire::NODE_COMPACT_FILTERS
                } else {
                    0
                }
                | if node.config.peer_bloom_filters {
                    wire::NODE_BLOOM
                } else {
                    0
                };
            let mempool = node.mempool.read();
            Ok(json!({
            "version": 310100,
            "subversion": "/bitcoind-rs:0.1.0/",
            "protocolversion": 70016,
            "localservices": format!("{local_services:016x}"),
            "localservicesnames": peer_services_names(local_services),
            "timeoffset": node.median_outbound_time_offset(),
            "localrelay": !node.config.blocksonly,
            "connections": node.peer_count(),
            "connections_in": node.peer_infos().iter().filter(|peer| peer.inbound).count(),
            "connections_out": node.peer_infos().iter().filter(|peer| !peer.inbound).count(),
            "networkactive": node.network_active(),
            "networks": network_info(node),
            "localaddresses": local_addresses(node),
            "relayfee": sat_to_btc(mempool.min_relay_fee_sat_per_kvb()),
            "incrementalfee": sat_to_btc(mempool.incremental_relay_fee_sat_per_kvb()),
            "warnings": [],
            }))
        }
        "getpeerinfo" => Ok(json!(
            node.peer_infos()
                .into_iter()
                .map(|peer| {
                    let (synced_headers, synced_blocks) = {
                        let chain = node.chain.read();
                        let synced_headers = peer
                            .best_known_block
                            .and_then(|hash| chain.block_height_by_hash(&hash))
                            .map_or(-1, i64::from);
                        let synced_blocks = peer
                            .last_common_block
                            .and_then(|hash| chain.block_height_by_hash(&hash))
                            .map_or(-1, i64::from);
                        (synced_headers, synced_blocks)
                    };
                    let mut info = json!({
                        "id": peer.id,
                        "addr": peer.endpoint.to_string(),
                        "network": peer_network_name(&peer.endpoint),
                        "services": format!("{:016x}", peer.services),
                        "servicesnames": peer_services_names(peer.services),
                        "relaytxes": peer.relay_transactions,
                        "last_inv_sequence": peer.last_inv_sequence,
                        "inv_to_send": peer.inv_to_send,
                        "lastsend": peer.last_send,
                        "lastrecv": peer.last_recv,
                        "last_transaction": peer.last_transaction,
                        "last_block": peer.last_block,
                        "bytessent": peer.bytes_sent,
                        "bytesrecv": peer.bytes_received,
                        "conntime": peer.connected_at,
                        "timeoffset": peer.time_offset,
                        "version": peer.version.unwrap_or_default(),
                        "subver": peer.user_agent,
                        "inbound": peer.inbound,
                        "bip152_hb_to": peer.bip152_highbandwidth_to,
                        "bip152_hb_from": peer.bip152_highbandwidth_from,
                        "presynced_headers": -1,
                        "synced_headers": synced_headers,
                        "synced_blocks": synced_blocks,
                        "inflight": peer.inflight_heights(),
                        "addr_relay_enabled": peer.addr_relay_enabled,
                        "addr_processed": peer.addr_processed,
                        "addr_rate_limited": peer.addr_rate_limited,
                        "permissions": peer.permissions.to_strings(),
                        "minfeefilter": sat_to_btc_signed(peer.min_fee_filter),
                        "bytessent_per_msg": peer.bytes_sent_per_msg,
                        "bytesrecv_per_msg": peer.bytes_received_per_msg,
                        "connection_type": rpc_connection_type(peer.connection_type),
                        "transport_protocol_type": peer.transport_protocol_type,
                        "session_id": peer.session_id,
                    });
                    if let Some(address) = peer.local_address {
                        info["addrbind"] = json!(address.to_string());
                    }
                    if let Some(address) = peer.reported_local_address {
                        info["addrlocal"] = json!(address.to_string());
                    }
                    if let Some(ping_time) = peer.ping_time {
                        info["pingtime"] = json!(ping_time);
                    }
                    if let Some(min_ping) = peer.min_ping {
                        info["minping"] = json!(min_ping);
                    }
                    if let Some(ping_wait) = peer.ping_wait().filter(|wait| *wait > 0.0) {
                        info["pingwait"] = json!(ping_wait);
                    }
                    info
                })
                .collect::<Vec<_>>()
        )),
        "getnettotals" => get_net_totals(node),
        "getnodeaddresses" => get_node_addresses(node, params),
        "getaddrmaninfo" => get_addrman_info(node),
        "addpeeraddress" => add_peer_address(node, params),
        "getrawaddrman" => get_raw_addrman(node),
        "sendmsgtopeer" => send_message_to_peer(node, params),
        "addconnection" => add_connection(node, params),
        "addnode" => add_node(node, params),
        "disconnectnode" => disconnect_node(node, params),
        "getaddednodeinfo" => get_added_node_info(node, params),
        "setban" => set_ban(node, params),
        "listbanned" => list_banned(node),
        "clearbanned" => clear_banned(node),
        "ping" => {
            node.ping_peers();
            Ok(Value::Null)
        }
        "setnetworkactive" => {
            let active = param::<bool>(params, 0)?;
            node.set_network_active(active);
            Ok(Value::Bool(true))
        }
        "getrpcinfo" => Ok(json!({
            "active_commands": node.active_rpc_commands(),
            "logpath": node.config.datadir.join("debug.log").to_string_lossy(),
        })),
        "help" => Ok(json!(rpc_help(method_params_string(params)))),
        "estimatesmartfee" => estimate_smart_fee(node, params),
        "estimaterawfee" => estimate_raw_fee(node, params),
        "getdifficulty" => Ok(json!(
            node.chain
                .read()
                .header(node.chain.read().height())
                .map(|header| header.difficulty_float())
                .unwrap_or(1.0)
        )),
        "getconnectioncount" => Ok(json!(node.peer_count())),
        "uptime" => Ok(json!(node.started_at.elapsed().as_secs())),
        "getindexinfo" => get_index_info(node, params),
        "getzmqnotifications" => Ok(json!(
            node.config
                .zmq
                .notifications()
                .into_iter()
                .map(|notification| {
                    json!({
                        "type": notification.kind,
                        "address": notification.address,
                        "hwm": notification.hwm,
                    })
                })
                .collect::<Vec<_>>()
        )),
        "logging" => configure_logging(params),
        "syncwithvalidationinterfacequeue" => Ok(Value::Null),
        "validateaddress" => validate_address(node, params),
        "deriveaddresses" => derive_addresses(node, params),
        "getdescriptorinfo" => get_descriptor_info(node, params),
        _ => bail!("Method not found"),
    }
}

fn set_mock_time(node: &Arc<Node>, params: &Value) -> Result<Value> {
    if node.config.network != Network::Regtest {
        bail!("setmocktime is for regression testing (-regtest mode) only")
    }
    let timestamp = param::<i64>(params, 0)?;
    if timestamp < 0 {
        bail!("Mocktime must be in the range [0, 9223372036854775807]")
    }
    crate::time::set_mock_time(timestamp);
    Ok(Value::Null)
}

fn mock_scheduler(node: &Arc<Node>, params: &Value) -> Result<Value> {
    if node.config.network != Network::Regtest {
        bail!("mockscheduler is for regression testing (-regtest mode) only")
    }
    let delta = param::<i64>(params, 0)?;
    if !(1..=3_600).contains(&delta) {
        bail!("delta_time must be between 1 and 3600 seconds (1 hr)")
    }
    // Tokio's scheduler is real-time in this implementation. The RPC still
    // validates and accepts the same testing range; validation notifications
    // are synchronous, so no scheduler wake-up is needed here.
    Ok(Value::Null)
}

fn get_memory_info(params: &Value) -> Result<Value> {
    let mode = params
        .get(0)
        .filter(|value| !value.is_null())
        .map(|value| {
            value
                .as_str()
                .ok_or_else(|| anyhow!("mode must be a string"))
        })
        .transpose()?
        .unwrap_or("stats");
    match mode {
        "stats" => Ok(json!({"locked": rpc_locked_memory_info()})),
        "mallocinfo" => bail!("mallocinfo mode not available"),
        _ => bail!("unknown mode {mode}"),
    }
}

fn get_index_info(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let requested = params
        .get(0)
        .filter(|value| !value.is_null())
        .map(|value| {
            value
                .as_str()
                .ok_or_else(|| anyhow!("index_name must be a string"))
        })
        .transpose()?;
    const BASIC_FILTER_INDEX: &str = "basic block filter index";
    const TX_INDEX: &str = "txindex";
    const TX_SPENDER_INDEX: &str = "txospenderindex";
    const COIN_STATS_INDEX: &str = "coinstatsindex";
    if requested.is_some_and(|name| {
        name != BASIC_FILTER_INDEX
            && name != TX_INDEX
            && name != TX_SPENDER_INDEX
            && name != COIN_STATS_INDEX
    }) {
        return Ok(json!({}));
    }
    let height = node.chain.read().height();
    let mut result = json!({});
    if node.config.txindex && requested.is_none_or(|name| name == TX_INDEX) {
        result[TX_INDEX] = json!({
            "synced": true,
            "best_block_height": height,
        });
    }
    if node.config.txospenderindex && requested.is_none_or(|name| name == TX_SPENDER_INDEX) {
        result[TX_SPENDER_INDEX] = json!({
            "synced": true,
            "best_block_height": height,
        });
    }
    if node.config.coinstatsindex && requested.is_none_or(|name| name == COIN_STATS_INDEX) {
        result[COIN_STATS_INDEX] = json!({
            "synced": true,
            "best_block_height": height,
        });
    }
    if node.config.blockfilterindex && requested.is_none_or(|name| name == BASIC_FILTER_INDEX) {
        result[BASIC_FILTER_INDEX] = json!({
            "synced": true,
            "best_block_height": height,
        });
    }
    Ok(result)
}

fn estimate_smart_fee(node: &Arc<Node>, params: &Value) -> Result<Value> {
    if node.config.blocksonly {
        bail!("Fee estimation disabled")
    }
    let conf_target = params
        .get(0)
        .and_then(Value::as_u64)
        .ok_or_else(|| anyhow!("conf_target must be a positive integer"))?;
    let conf_target = u32::try_from(conf_target)
        .map_err(|_| anyhow!("conf_target must be between 1 and 1008"))?;
    if !(1..=1_008).contains(&conf_target) {
        bail!("conf_target must be between 1 and 1008")
    }
    // Core cannot produce a meaningful one-block estimate and internally
    // evaluates that request as a two-block target.
    let conf_target = conf_target.max(2);
    let conservative = match params
        .get(1)
        .filter(|value| !value.is_null())
        .map(|value| {
            value
                .as_str()
                .ok_or_else(|| anyhow!("estimate_mode must be a string"))
        })
        .transpose()?
        .unwrap_or("UNSET")
        .to_ascii_uppercase()
        .as_str()
    {
        "UNSET" | "ECONOMICAL" => false,
        "CONSERVATIVE" => true,
        _ => bail!("estimate_mode must be UNSET, ECONOMICAL, or CONSERVATIVE"),
    };
    let estimate = node
        .chain
        .write()
        .estimate_fee_rate_sat_per_kvb(conf_target, conservative)?;
    let estimate = estimate.map(|rate| {
        let mut mempool = node.mempool.write();
        let floor = mempool
            .mempool_min_fee_sat_per_kvb()
            .max(mempool.min_relay_fee_sat_per_kvb());
        rate.max(floor)
    });
    let mut result = json!({"blocks": conf_target});
    if let Some(rate) = estimate {
        result["feerate"] = json!(sat_to_btc(rate));
    } else {
        result["errors"] = json!(["Insufficient data or no feerate found"]);
    }
    Ok(result)
}

fn raw_fee_bucket(
    start: u64,
    end: u64,
    within_target: u64,
    total_confirmed: u64,
    in_mempool: u64,
    left_mempool: u64,
) -> Value {
    json!({
        "startrange": start,
        "endrange": end,
        "withintarget": within_target,
        "totalconfirmed": total_confirmed,
        "inmempool": in_mempool,
        "leftmempool": left_mempool,
    })
}

fn raw_fee_horizon(mut samples: Vec<(u64, u64)>, threshold: f64, decay: f64, scale: u32) -> Value {
    samples.retain(|(rate, _)| *rate > 0);
    let mut result = json!({"decay": decay, "scale": scale});
    if samples.is_empty() {
        result["fail"] = json!({
            "startrange": -1,
            "endrange": -1,
            "withintarget": 0,
            "totalconfirmed": 0,
            "inmempool": 0,
            "leftmempool": 0,
        });
        result["errors"] = json!(["Insufficient data or no feerate found which meets threshold"]);
        return result;
    }

    samples.sort_unstable_by_key(|(rate, _)| *rate);
    let index = ((samples.len().saturating_sub(1) as f64) * threshold).ceil() as usize;
    let estimate = samples[index.min(samples.len() - 1)].0;
    let total = samples.len() as u64;
    let passing = samples.iter().filter(|(rate, _)| *rate >= estimate).count() as u64;
    result["feerate"] = json!(sat_to_btc(estimate));
    result["pass"] = raw_fee_bucket(
        estimate,
        samples.last().map_or(estimate, |(rate, _)| *rate),
        passing,
        passing,
        0,
        0,
    );
    if passing < total {
        result["fail"] = raw_fee_bucket(0, estimate, total - passing, total - passing, 0, 0);
    }
    result
}

fn estimate_raw_fee(node: &Arc<Node>, params: &Value) -> Result<Value> {
    if node.config.blocksonly {
        bail!("Fee estimation disabled")
    }
    let conf_target = params
        .get(0)
        .and_then(Value::as_u64)
        .ok_or_else(|| anyhow!("conf_target must be a positive integer"))?;
    let conf_target = u32::try_from(conf_target)
        .map_err(|_| anyhow!("Invalid conf_target, must be between 1 and 1008"))?;
    if !(1..=1_008).contains(&conf_target) {
        bail!("Invalid conf_target, must be between 1 and 1008")
    }
    let threshold = params
        .get(1)
        .filter(|value| !value.is_null())
        .map(|value| {
            value
                .as_f64()
                .ok_or_else(|| anyhow!("threshold must be a number"))
        })
        .transpose()?
        .unwrap_or(0.95);
    if !threshold.is_finite() || !(0.0..=1.0).contains(&threshold) {
        bail!("Invalid threshold")
    }

    // Core tracks three moving-average horizons. This implementation does not
    // retain mempool admission/eviction history, so use confirmed transaction
    // samples from the longest available window and expose the same stable
    // result shape for each horizon.
    let samples = node.chain.write().recent_fee_rate_samples(1_008)?;
    let mut result = serde_json::Map::new();
    for (name, max_target, decay, scale) in [
        ("short", 12_u32, 0.962_f64, 1_u32),
        ("medium", 48_u32, 0.9952_f64, 2_u32),
        ("long", 1_008_u32, 0.99931_f64, 24_u32),
    ] {
        if conf_target <= max_target {
            result.insert(
                name.to_owned(),
                raw_fee_horizon(samples.clone(), threshold, decay, scale),
            );
        }
    }
    Ok(Value::Object(result))
}

const LOG_CATEGORIES: &[&str] = &[
    "addrman",
    "bench",
    "blockstorage",
    "cmpctblock",
    "coindb",
    "estimatefee",
    "http",
    "i2p",
    "ipc",
    "kernel",
    "leveldb",
    "libevent",
    "mempool",
    "mempoolrej",
    "net",
    "privatebroadcast",
    "prune",
    "proxy",
    "qt",
    "rand",
    "reindex",
    "rpc",
    "scan",
    "selectcoins",
    "tor",
    "txpackages",
    "txreconciliation",
    "validation",
    "walletdb",
    "zmq",
];

fn logging_state() -> &'static parking_lot::RwLock<HashSet<String>> {
    static STATE: OnceLock<parking_lot::RwLock<HashSet<String>>> = OnceLock::new();
    STATE.get_or_init(|| parking_lot::RwLock::new(HashSet::new()))
}

fn configure_logging(params: &Value) -> Result<Value> {
    let mut enabled = logging_state().write();
    for (index, should_enable) in [(0usize, true), (1usize, false)] {
        let Some(value) = params.get(index).filter(|value| !value.is_null()) else {
            continue;
        };
        let categories = value
            .as_array()
            .ok_or_else(|| anyhow!("logging categories must be an array"))?;
        for category in categories {
            let category = category
                .as_str()
                .ok_or_else(|| anyhow!("logging category must be a string"))?;
            if category == "all" || category == "1" {
                if should_enable {
                    enabled.extend(LOG_CATEGORIES.iter().map(|category| (*category).to_owned()));
                } else {
                    enabled.clear();
                }
                continue;
            }
            if !LOG_CATEGORIES.contains(&category) {
                bail!("unknown logging category {category}")
            }
            if should_enable {
                enabled.insert(category.to_owned());
            } else {
                enabled.remove(category);
            }
        }
    }
    Ok(json!(
        LOG_CATEGORIES
            .iter()
            .map(|category| ((*category).to_owned(), enabled.contains(*category)))
            .collect::<HashMap<_, _>>()
    ))
}

fn get_net_totals(node: &Arc<Node>) -> Result<Value> {
    let total_bytes_sent = node.total_bytes_sent();
    let total_bytes_recv = node.total_bytes_received();
    Ok(json!({
        "totalbytesrecv": total_bytes_recv,
        "totalbytessent": total_bytes_sent,
        "timemillis": crate::time::unix_time_millis(),
        "uploadtarget": {
            "timeframe": node.max_upload_timeframe(),
            "target": node.max_upload_target(),
            "target_reached": node.outbound_target_reached(false),
            "serve_historical_blocks": !node.outbound_target_reached(true),
            "bytes_left_in_cycle": node.outbound_target_bytes_left(),
            "time_left_in_cycle": node.outbound_time_left_in_cycle(),
        },
    }))
}

fn local_addresses(node: &Arc<Node>) -> Value {
    let mut addresses = Vec::new();
    for address in &node.config.external_addresses {
        if is_routable_ip(address.ip()) && node.config.allows_address(*address) {
            addresses.push((*address, 4));
        }
    }
    if node.config.discover && node.config.proxy.is_none() {
        for address in node
            .listen_addresses()
            .into_iter()
            .filter(|address| is_routable_ip(address.ip()) && node.config.allows_address(*address))
        {
            if !addresses.iter().any(|(known, _)| known == &address) {
                addresses.push((address, 2));
            }
        }
    }
    json!(
        addresses
            .into_iter()
            .map(|(address, score)| json!({
                "address": address.ip().to_string(),
                "port": address.port(),
                "score": score,
            }))
            .collect::<Vec<_>>()
    )
}

fn network_info(node: &Arc<Node>) -> Value {
    let proxy = node
        .config
        .proxy
        .map_or_else(String::new, |proxy| proxy.to_string());
    let networks = [
        ("ipv4", OnlyNet::Ipv4, true),
        ("ipv6", OnlyNet::Ipv6, true),
        ("onion", OnlyNet::Onion, node.config.proxy.is_some()),
        ("i2p", OnlyNet::I2p, node.config.proxy.is_some()),
        ("cjdns", OnlyNet::Cjdns, node.config.cjdns_reachable),
    ]
    .into_iter()
    .map(|(name, network, transport_available)| {
        let limited = !node.config.onlynet.is_empty() && !node.config.onlynet.contains(&network);
        let reachable = !limited && transport_available;
        json!({
            "name": name,
            "limited": limited,
            "reachable": reachable,
            "proxy": if node.config.proxy.is_some() { proxy.as_str() } else { "" },
            "proxy_randomize_credentials": node.config.proxy.is_some()
                && node.config.proxy_randomize,
        })
    })
    .collect::<Vec<_>>();
    json!(networks)
}

fn is_routable_ip(address: std::net::IpAddr) -> bool {
    match address {
        std::net::IpAddr::V4(address) => {
            let octets = address.octets();
            let shared = octets[0] == 100 && (64..=127).contains(&octets[1]);
            let documentation = (octets[0] == 192 && octets[1] == 0 && octets[2] == 2)
                || (octets[0] == 198 && octets[1] == 51 && octets[2] == 100)
                || (octets[0] == 203 && octets[1] == 0 && octets[2] == 113);
            let benchmark = octets[0] == 198 && (18..=19).contains(&octets[1]);
            !address.is_unspecified()
                && !address.is_loopback()
                && !address.is_private()
                && !address.is_link_local()
                && !address.is_broadcast()
                && !shared
                && !documentation
                && !benchmark
                && !address.is_multicast()
        }
        std::net::IpAddr::V6(address) => {
            let segments = address.segments();
            let documentation = segments[0] == 0x2001 && segments[1] == 0x0db8;
            !address.is_unspecified()
                && !address.is_loopback()
                && !address.is_unique_local()
                && !address.is_unicast_link_local()
                && !address.is_multicast()
                && !documentation
        }
    }
}

fn get_txout_set_info(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let hash_type = match params.get(0) {
        None | Some(Value::Null) => "hash_serialized_3",
        Some(value) => value
            .as_str()
            .ok_or_else(|| anyhow!("hash_type must be a string"))?,
    };
    if !matches!(hash_type, "hash_serialized_3" | "muhash" | "none") {
        bail!("unknown hash_type: {hash_type}")
    }
    let use_index = params
        .get(2)
        .filter(|value| !value.is_null())
        .map(|value| {
            value
                .as_bool()
                .ok_or_else(|| anyhow!("use_index must be a boolean"))
        })
        .transpose()?
        .unwrap_or(true);
    let target = params.get(1).filter(|value| !value.is_null());
    if target.is_some() && hash_type == "hash_serialized_3" {
        bail!("hash_serialized_3 hash type cannot be queried for a specific block")
    }
    if target.is_some() && !node.config.coinstatsindex {
        bail!("Querying specific block heights requires coinstatsindex")
    }
    if target.is_some() && !use_index {
        bail!("Cannot set use_index to false when querying for a specific block")
    }
    let use_coinstats_index =
        node.config.coinstatsindex && use_index && matches!(hash_type, "muhash" | "none");

    let mut chain = node.chain.write();
    let include_serialized_hash = hash_type == "hash_serialized_3";
    let include_muhash = hash_type == "muhash";
    let (height, bestblock, stats, disk_size) = if let Some(value) = target {
        let target_hash = if let Some(height) = value.as_u64() {
            let height = u32::try_from(height).context("hash_or_height is too large")?;
            chain
                .block_hash(height)
                .ok_or_else(|| anyhow!("block height out of range"))?
        } else if let Some(text) = value.as_str() {
            if let Ok(hash) = text.parse::<BlockHash>() {
                hash
            } else {
                let height = text
                    .parse::<u32>()
                    .context("hash_or_height must be a block hash or height")?;
                chain
                    .block_hash(height)
                    .ok_or_else(|| anyhow!("block height out of range"))?
            }
        } else {
            bail!("hash_or_height must be a block hash or height")
        };
        if !chain.is_active_block(&target_hash) {
            bail!("hash_or_height is not on the active chain")
        }
        let (height, stats) = chain
            .coinstats_at(&target_hash, include_muhash)?
            .ok_or_else(|| anyhow!("block is not available"))?;
        (height, target_hash, stats, 0)
    } else {
        let stats = if use_coinstats_index {
            chain.utxo_statistics(include_serialized_hash, include_muhash)
        } else {
            chain.utxo_statistics_without_index(include_serialized_hash, include_muhash)
        };
        let disk_size = std::fs::metadata(chain.store.path())
            .map(|metadata| metadata.len())
            .unwrap_or(0);
        (chain.height(), chain.best_hash(), stats, disk_size)
    };
    let mut result = json!({
        "height": height,
        "bestblock": bestblock.to_string(),
        "txouts": stats.outputs,
        "bogosize": stats.bogo_size,
        "total_amount": sat_to_btc(stats.total_amount_sat),
    });
    if !use_coinstats_index {
        result["transactions"] = json!(stats.transactions);
        result["disk_size"] = json!(disk_size);
    }
    match hash_type {
        "hash_serialized_3" => {
            result["hash_serialized_3"] = json!(
                stats
                    .serialized_hash
                    .expect("serialized hash was requested")
            );
        }
        "muhash" => {
            result["muhash"] = json!(stats.muhash.expect("MuHash was requested"));
        }
        "none" => {}
        _ => unreachable!("hash_type was validated above"),
    }
    if use_coinstats_index {
        let previous = if height == 0 {
            crate::chain::UtxoSetStats::default()
        } else {
            let previous_hash = chain
                .block_hash(height.saturating_sub(1))
                .context("previous block is unavailable")?;
            chain
                .coinstats_at(&previous_hash, false)?
                .map(|(_, stats)| stats)
                .context("previous coinstats record is unavailable")?
        };
        let unspendable = stats
            .total_unspendable_genesis_sat
            .saturating_add(stats.total_unspendable_bip30_sat)
            .saturating_add(stats.total_unspendable_scripts_sat)
            .saturating_add(stats.total_unspendable_unclaimed_rewards_sat);
        let previous_unspendable = previous
            .total_unspendable_genesis_sat
            .saturating_add(previous.total_unspendable_bip30_sat)
            .saturating_add(previous.total_unspendable_scripts_sat)
            .saturating_add(previous.total_unspendable_unclaimed_rewards_sat);
        result["total_unspendable_amount"] = json!(sat_to_btc(unspendable));
        result["block_info"] = json!({
            "prevout_spent": sat_to_btc(
                stats
                    .total_prevout_spent_sat
                    .saturating_sub(previous.total_prevout_spent_sat)
            ),
            "coinbase": sat_to_btc(
                stats
                    .total_coinbase_sat
                    .saturating_sub(previous.total_coinbase_sat)
            ),
            "new_outputs_ex_coinbase": sat_to_btc(
                stats
                    .total_new_outputs_ex_coinbase_sat
                    .saturating_sub(previous.total_new_outputs_ex_coinbase_sat)
            ),
            "unspendable": sat_to_btc(unspendable.saturating_sub(previous_unspendable)),
            "unspendables": {
                "genesis_block": sat_to_btc(
                    stats
                        .total_unspendable_genesis_sat
                        .saturating_sub(previous.total_unspendable_genesis_sat)
                ),
                "bip30": sat_to_btc(
                    stats
                        .total_unspendable_bip30_sat
                        .saturating_sub(previous.total_unspendable_bip30_sat)
                ),
                "scripts": sat_to_btc(
                    stats
                        .total_unspendable_scripts_sat
                        .saturating_sub(previous.total_unspendable_scripts_sat)
                ),
                "unclaimed_rewards": sat_to_btc(
                    stats
                        .total_unspendable_unclaimed_rewards_sat
                        .saturating_sub(previous.total_unspendable_unclaimed_rewards_sat)
                ),
            },
        });
    }
    Ok(result)
}

fn peer_services_names(services: u64) -> Vec<String> {
    (0..64)
        .filter(|bit| services & (1u64 << bit) != 0)
        .map(|bit| match bit {
            0 => "NETWORK".to_owned(),
            2 => "BLOOM".to_owned(),
            3 => "WITNESS".to_owned(),
            6 => "COMPACT_FILTERS".to_owned(),
            10 => "NETWORK_LIMITED".to_owned(),
            11 => "P2P_V2".to_owned(),
            bit => format!("UNKNOWN[2^{bit}]"),
        })
        .collect()
}

fn peer_network_name(endpoint: &NetworkEndpoint) -> &'static str {
    match endpoint {
        NetworkEndpoint::Ip(address) => {
            let ip = address.ip();
            if is_publicly_routable(ip) {
                if ip.is_ipv4() { "ipv4" } else { "ipv6" }
            } else {
                "not_publicly_routable"
            }
        }
        _ => endpoint.network_name(),
    }
}

fn is_publicly_routable(ip: IpAddr) -> bool {
    match ip {
        IpAddr::V4(ip) => {
            let [first, second, third, _] = ip.octets();
            !(ip.is_broadcast()
                || first == 0
                || first == 127
                || first == 10
                || (first == 172 && (16..=31).contains(&second))
                || (first == 192 && second == 168)
                || (first == 169 && second == 254)
                || (first == 100 && (64..=127).contains(&second))
                || (first == 198 && (second == 18 || second == 19))
                || (first == 192 && second == 0 && third == 2)
                || (first == 198 && second == 51 && third == 100)
                || (first == 203 && second == 0 && third == 113))
        }
        IpAddr::V6(ip) => {
            let octets = ip.octets();
            !(ip.is_unspecified()
                || ip.is_loopback()
                || (octets[0] & 0xfe == 0xfc)
                || (octets[0] == 0xfe && octets[1] & 0xc0 == 0x80)
                || (octets[0], octets[1], octets[2], octets[3]) == (0x20, 0x01, 0x0d, 0xb8)
                || (octets[0], octets[1], octets[2]) == (0x20, 0x01, 0x00)
                    && (octets[3] & 0xf0 == 0x10 || octets[3] & 0xf0 == 0x20))
        }
    }
}

fn validate_address(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let value = param::<String>(params, 0)?;
    let unchecked = match value.parse::<Address<bitcoin::address::NetworkUnchecked>>() {
        Ok(address) => address,
        Err(error) => {
            return Ok(json!({
                "isvalid": false,
                "error_locations": [],
                "error": error.to_string(),
            }));
        }
    };
    let address = match unchecked.require_network(node.config.network) {
        Ok(address) => address,
        Err(error) => {
            return Ok(json!({
                "isvalid": false,
                "error_locations": [],
                "error": error.to_string(),
            }));
        }
    };
    let witness_program = address.witness_program();
    let mut result = json!({
        "isvalid": true,
        "address": address.to_string(),
        "scriptPubKey": hex::encode(address.script_pubkey().as_bytes()),
    });
    match address.address_type() {
        Some(AddressType::P2pkh) => {
            result["isscript"] = json!(false);
            result["iswitness"] = json!(false);
        }
        Some(AddressType::P2sh) => {
            result["isscript"] = json!(true);
            result["iswitness"] = json!(false);
        }
        Some(AddressType::P2wpkh) => {
            result["isscript"] = json!(false);
            result["iswitness"] = json!(true);
        }
        Some(AddressType::P2wsh | AddressType::P2tr | AddressType::P2a) => {
            result["isscript"] = json!(true);
            result["iswitness"] = json!(true);
        }
        Some(_) => {
            if witness_program.is_some() {
                result["iswitness"] = json!(true);
            }
        }
        None => {
            // Future witness versions are valid addresses but do not have a
            // known script classification yet, matching Core's optional
            // `isscript` field for WitnessUnknown destinations.
            if witness_program.is_some() {
                result["iswitness"] = json!(true);
            }
        }
    }
    if !matches!(address.address_type(), Some(AddressType::P2a))
        && let Some(program) = witness_program
    {
        result["witness_version"] = json!(program.version().to_num());
        result["witness_program"] = json!(hex::encode(program.program().as_bytes()));
    }
    Ok(result)
}

fn derive_addresses(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let descriptor = param::<String>(params, 0)?;
    let range = params
        .get(1)
        .filter(|value| !value.is_null())
        .map(parse_descriptor_range)
        .transpose()?;
    let descriptor_body = if descriptor.contains('#') {
        descriptor_payload(&descriptor)?.0
    } else {
        descriptor.as_str()
    };
    let multipath_payloads = expand_descriptor_multipath(descriptor_body)?;
    if multipath_payloads.len() > 1 {
        let addresses = multipath_payloads
            .iter()
            .map(|payload| derive_addresses_for_descriptor(node, payload, range))
            .collect::<Result<Vec<_>>>()?;
        return Ok(json!(addresses));
    }
    let addresses = derive_addresses_for_descriptor(node, descriptor_body, range)?;
    Ok(json!(addresses))
}

fn derive_addresses_for_descriptor(
    node: &Arc<Node>,
    descriptor: &str,
    range: Option<(u32, u32)>,
) -> Result<Vec<String>> {
    let scripts = expand_descriptor_scripts(node, descriptor, range)?;
    let multipath_or_combo = scripts.len() > 1;
    let addresses = scripts
        .into_iter()
        .filter_map(|script| {
            if multipath_or_combo && script.is_p2pk() {
                return None;
            }
            Some(
                Address::from_script(&script, node.config.network)
                    .map(|address| address.to_string())
                    .map_err(|_| anyhow!("descriptor does not encode a standard address")),
            )
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(addresses)
}

fn descriptor_checksum(descriptor: &str) -> Option<String> {
    const INPUT_CHARSET: &str = "0123456789()[],'/*abcdefgh@:$%{}IJKLMNOPQRSTUVWXYZ&+-.;<=>?!^_|~ijklmnopqrstuvwxyzABCDEFGH`#\"\\ ";
    const CHECKSUM_CHARSET: &[u8] = b"qpzry9x8gf2tvdw0s3jn54khce6mua7l";
    const GENERATOR: [u64; 5] = [
        0xf5dee51989,
        0xa9fdca3312,
        0x1bab10e32d,
        0x3706b1677a,
        0x644d626ffd,
    ];
    let polymod = |value: u64, symbol: u64| {
        let top = (value >> 35) as u8;
        let mut value = ((value & 0x0007_ffff_ffff) << 5) ^ symbol;
        for (index, generator) in GENERATOR.iter().enumerate() {
            if top & (1 << index) != 0 {
                value ^= generator;
            }
        }
        value
    };
    let mut checksum = 1u64;
    let mut class = 0u64;
    let mut class_count = 0u8;
    for character in descriptor.chars() {
        let position = INPUT_CHARSET.find(character)?;
        checksum = polymod(checksum, (position & 31) as u64);
        class = class * 3 + (position >> 5) as u64;
        class_count += 1;
        if class_count == 3 {
            checksum = polymod(checksum, class);
            class = 0;
            class_count = 0;
        }
    }
    if class_count > 0 {
        checksum = polymod(checksum, class);
    }
    for _ in 0..8 {
        checksum = polymod(checksum, 0);
    }
    checksum ^= 1;
    Some(
        (0..8)
            .map(|index| CHECKSUM_CHARSET[((checksum >> (5 * (7 - index))) & 31) as usize] as char)
            .collect(),
    )
}

fn descriptor_payload(descriptor: &str) -> Result<(&str, String)> {
    let mut parts = descriptor.split('#');
    let payload = parts.next().ok_or_else(|| anyhow!("descriptor is empty"))?;
    let supplied = parts.next();
    if parts.next().is_some() {
        bail!("descriptor contains multiple checksum separators")
    }
    let checksum = descriptor_checksum(payload)
        .ok_or_else(|| anyhow!("descriptor contains invalid characters"))?;
    if let Some(supplied) = supplied {
        if supplied.len() != 8 || supplied != checksum {
            bail!("descriptor checksum does not match")
        }
    }
    Ok((payload, checksum))
}

fn expand_descriptor_multipath(payload: &str) -> Result<Vec<String>> {
    const MAX_EXPANSIONS: usize = 64;
    let Some(start) = payload.find('<') else {
        return Ok(vec![payload.to_owned()]);
    };
    let end = payload[start + 1..]
        .find('>')
        .map(|offset| start + 1 + offset)
        .ok_or_else(|| anyhow!("descriptor multipath specifier is missing a closing bracket"))?;
    let values = &payload[start + 1..end];
    let values = values.split(';').collect::<Vec<_>>();
    if values.len() < 2 || values.iter().any(|value| value.is_empty()) {
        bail!("descriptor multipath specifier must contain at least two values")
    }
    let mut seen = HashSet::new();
    if values.iter().any(|value| !seen.insert(*value)) {
        bail!("descriptor multipath specifier contains duplicate values")
    }
    let mut expansions = Vec::new();
    for value in values {
        let replacement = format!("{}{}{}", &payload[..start], value, &payload[end + 1..]);
        for expansion in expand_descriptor_multipath(&replacement)? {
            expansions.push(expansion);
            if expansions.len() > MAX_EXPANSIONS {
                bail!("descriptor multipath expansion is too large")
            }
        }
    }
    Ok(expansions)
}

fn canonicalize_descriptor_private_keys(payload: &str) -> Result<String> {
    let mut canonical = String::with_capacity(payload.len());
    let mut index = 0;
    while index < payload.len() {
        let remaining = &payload[index..];
        if remaining.starts_with("xprv") || remaining.starts_with("tprv") {
            let end = remaining
                .char_indices()
                .skip(1)
                .find_map(|(offset, character)| {
                    (!character.is_ascii_alphanumeric()).then_some(index + offset)
                })
                .unwrap_or(payload.len());
            let private_key = remaining[..end - index]
                .parse::<bitcoin::bip32::Xpriv>()
                .map_err(|error| anyhow!("invalid private descriptor key: {error}"))?;
            canonical.push_str(
                &bitcoin::bip32::Xpub::from_priv(&Secp256k1::new(), &private_key).to_string(),
            );
            index = end;
        } else {
            let character = remaining
                .chars()
                .next()
                .expect("remaining descriptor payload is non-empty");
            canonical.push(character);
            index += character.len_utf8();
        }
    }
    Ok(canonical)
}

fn get_descriptor_info(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let descriptor = param::<String>(params, 0)?;
    let (payload, checksum) = descriptor_payload(&descriptor)?;
    let multipath_payloads = expand_descriptor_multipath(payload)?;
    let canonical_payloads = multipath_payloads
        .iter()
        .map(|payload| canonicalize_descriptor_private_keys(payload))
        .collect::<Result<Vec<_>>>()?;
    let canonical_payload = &canonical_payloads[0];
    let canonical_checksum = descriptor_checksum(canonical_payload)
        .ok_or_else(|| anyhow!("descriptor contains invalid characters"))?;
    let isrange = payload.contains('*');
    let range = isrange.then_some((0, 0));
    let has_private_keys = [
        "xprv", "tprv", "yprv", "zprv", "Yprv", "Zprv", "uprv", "vprv",
    ]
    .iter()
    .any(|prefix| payload.contains(prefix));
    let issolvable = expand_descriptor_scripts(node, &multipath_payloads[0], range).is_ok();
    let mut result = json!({
        "descriptor": format!("{canonical_payload}#{canonical_checksum}"),
        "checksum": checksum,
        "isrange": isrange,
        "issolvable": issolvable,
        "hasprivatekeys": has_private_keys,
    });
    if canonical_payloads.len() > 1 {
        result["multipath_expansion"] = json!(
            canonical_payloads
                .iter()
                .map(|payload| {
                    let checksum = descriptor_checksum(payload)
                        .expect("canonical descriptor payload has valid characters");
                    format!("{payload}#{checksum}")
                })
                .collect::<Vec<_>>()
        );
    }
    Ok(result)
}

fn parse_descriptor_range(value: &Value) -> Result<(u32, u32)> {
    let values = value
        .as_array()
        .ok_or_else(|| anyhow!("descriptor range must be [begin,end]"))?;
    if values.len() != 2 {
        bail!("descriptor range must contain begin and end")
    }
    let begin = values[0]
        .as_u64()
        .ok_or_else(|| anyhow!("descriptor range begin must be an integer"))?;
    let end = values[1]
        .as_u64()
        .ok_or_else(|| anyhow!("descriptor range end must be an integer"))?;
    let begin = u32::try_from(begin).map_err(|_| anyhow!("descriptor range is too large"))?;
    let end = u32::try_from(end).map_err(|_| anyhow!("descriptor range is too large"))?;
    if end < begin {
        bail!("descriptor range end precedes begin")
    }
    Ok((begin, end))
}

fn get_node_addresses(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let count = match params.get(0) {
        None | Some(Value::Null) => Some(1usize),
        Some(value) => {
            let count = value
                .as_i64()
                .ok_or_else(|| anyhow!("address count must be an integer"))?;
            if count < 0 {
                bail!("Address count out of range")
            }
            (count != 0).then(|| usize::try_from(count).unwrap_or(usize::MAX))
        }
    };
    let network = match params.get(1) {
        None | Some(Value::Null) => None,
        Some(value) => Some(
            value
                .as_str()
                .ok_or_else(|| anyhow!("network must be a string"))?
                .to_owned(),
        ),
    };
    if let Some(network) = &network
        && !matches!(
            network.as_str(),
            "ipv4" | "ipv6" | "onion" | "i2p" | "cjdns"
        )
    {
        bail!("Network not recognized: {network}")
    }
    let mut peers = node
        .known_network_addresses()
        .into_iter()
        .filter(|peer| match network.as_deref() {
            None => true,
            Some(network) => peer.endpoint.network_name() == network,
        })
        .filter(|peer| {
            peer.endpoint
                .socket_addr()
                .is_none_or(|address| !node.is_banned_for_peer(address, false))
        })
        .collect::<Vec<_>>();
    peers.shuffle(&mut rand::rng());
    Ok(json!(
        peers
            .into_iter()
            .take(count.unwrap_or(usize::MAX))
            .map(|peer| json!({
                "address": peer.endpoint.host_string(),
                "port": peer.endpoint.port(),
                "services": peer.services,
                "time": peer.time,
                "network": peer.endpoint.network_name(),
            }))
            .collect::<Vec<_>>()
    ))
}

fn get_addrman_info(node: &Arc<Node>) -> Result<Value> {
    let mut counts = [
        ("ipv4", (0usize, 0usize)),
        ("ipv6", (0usize, 0usize)),
        ("onion", (0usize, 0usize)),
        ("i2p", (0usize, 0usize)),
        ("cjdns", (0usize, 0usize)),
    ]
    .into_iter()
    .collect::<HashMap<_, _>>();
    for peer in node.known_network_addresses() {
        let network = peer.endpoint.network_name();
        let Some((new, tried)) = counts.get_mut(network) else {
            continue;
        };
        if !node.is_network_address_tried(&peer.endpoint) {
            *new = new.saturating_add(1);
        } else {
            *tried = tried.saturating_add(1);
        }
    }
    let mut result = serde_json::Map::new();
    let mut all_new = 0usize;
    let mut all_tried = 0usize;
    for network in ["ipv4", "ipv6", "onion", "i2p", "cjdns"] {
        let (new, tried) = counts[network];
        all_new = all_new.saturating_add(new);
        all_tried = all_tried.saturating_add(tried);
        result.insert(
            network.to_owned(),
            json!({"new": new, "tried": tried, "total": new.saturating_add(tried)}),
        );
    }
    result.insert(
        "all_networks".to_owned(),
        json!({
            "new": all_new,
            "tried": all_tried,
            "total": all_new.saturating_add(all_tried),
        }),
    );
    Ok(Value::Object(result))
}

fn add_peer_address(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let address = param::<String>(params, 0)?;
    let port = param::<u16>(params, 1)?;
    let tried = match params.get(2) {
        None | Some(Value::Null) => false,
        Some(value) => value
            .as_bool()
            .ok_or_else(|| anyhow!("tried must be a boolean"))?,
    };
    let endpoint = if let Ok(address) = parse_ip_address(&address) {
        NetworkEndpoint::from_socket(SocketAddr::new(address, port))
    } else if address.ends_with(".onion") {
        NetworkEndpoint::parse(Some("onion"), &address, Some(port))?
    } else if address.ends_with(".b32.i2p") {
        NetworkEndpoint::parse(Some("i2p"), &address, Some(port))?
    } else {
        bail!("address must be an IP, onion, or I2P endpoint")
    };
    if node.add_network_address(endpoint, tried) {
        Ok(json!({"success": true}))
    } else {
        Ok(json!({"success": false, "error": "failed-adding-to-new"}))
    }
}

fn get_raw_addrman(node: &Arc<Node>) -> Result<Value> {
    let mut peers = node.known_network_addresses();
    peers.sort_by(|left, right| left.endpoint.cmp(&right.endpoint));
    let mut new_table = serde_json::Map::new();
    let mut tried_table = serde_json::Map::new();
    for (position, peer) in peers.into_iter().enumerate() {
        let network = peer.endpoint.network_name();
        let host = peer.endpoint.host_string();
        let entry = json!({
            "address": host,
            "port": peer.endpoint.port(),
            "services": peer.services,
            "time": peer.time,
            "network": network,
            "source": host,
            "source_network": network,
        });
        let table = if node.is_network_address_tried(&peer.endpoint) {
            &mut tried_table
        } else {
            &mut new_table
        };
        table.insert(format!("0/{position}"), entry);
    }
    Ok(json!({"new": new_table, "tried": tried_table}))
}

fn send_message_to_peer(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let peer_id = param::<u64>(params, 0)?;
    let peer_id = usize::try_from(peer_id).map_err(|_| anyhow!("peer id is out of range"))?;
    let command = param::<String>(params, 1)?;
    if command.is_empty()
        || command.len() > 12
        || !command.is_ascii()
        || command.as_bytes().contains(&0)
    {
        bail!("msg_type must be a non-empty ASCII command of at most 12 bytes")
    }
    let payload = hex::decode(param::<String>(params, 2)?)
        .map_err(|_| anyhow!("Error parsing input for msg"))?;
    node.send_message_to_peer(peer_id, command, payload)?;
    Ok(json!({}))
}

fn add_connection(node: &Arc<Node>, params: &Value) -> Result<Value> {
    if node.config.network != Network::Regtest {
        bail!("addconnection is only available on regtest")
    }
    let address_string = param::<String>(params, 0)?;
    let address = parse_socket_address(&address_string)?;
    let requested_connection_type = param::<String>(params, 1)?;
    if !matches!(
        requested_connection_type.as_str(),
        "outbound-full-relay" | "block-relay-only" | "addr-fetch" | "feeler"
    ) {
        bail!("invalid connection type")
    }
    let transport_v2 = param::<bool>(params, 2)?;
    if transport_v2 && !node.config.v2_transport {
        bail!("v2transport requested but not enabled (see --v2transport)");
    }
    let connection_type = match requested_connection_type.as_str() {
        "outbound-full-relay" => "outbound-full",
        "block-relay-only" => "block-relay-only",
        "addr-fetch" => "addr-fetch",
        "feeler" => "feeler",
        _ => unreachable!("connection type was validated above"),
    };
    node.request_one_try_with_connection_type(address, Some(transport_v2), connection_type);
    Ok(json!({
        "address": address_string,
        "connection_type": requested_connection_type,
    }))
}

fn get_block_from_peer(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let hash: BlockHash = param::<String>(params, 0)?.parse()?;
    let peer_id = param::<u64>(params, 1)?;
    let peer_id = usize::try_from(peer_id).map_err(|_| anyhow!("peer id is out of range"))?;
    node.request_block_from_peer(peer_id, hash)?;
    Ok(json!({}))
}

fn add_node(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let display_name = param::<String>(params, 0)?;
    let endpoint = parse_node_endpoint(node, &display_name)?;
    let command = param::<String>(params, 1)?;
    let transport_v2 = params
        .get(2)
        .filter(|value| !value.is_null())
        .map(|value| {
            value
                .as_bool()
                .ok_or_else(|| anyhow!("v2transport must be a boolean"))
        })
        .transpose()?;
    if transport_v2 == Some(true) && !node.config.v2_transport {
        bail!("v2transport requested but not enabled (see --v2transport)");
    }
    match command.as_str() {
        "add" => {
            if !node.add_node_endpoint_with_transport(endpoint, display_name, transport_v2) {
                bail!("node has already been added")
            }
            Ok(Value::Null)
        }
        "onetry" => {
            node.request_one_try_endpoint_with_connection_type(
                endpoint,
                transport_v2,
                "outbound-full",
            );
            Ok(Value::Null)
        }
        "remove" => {
            if node.remove_node_endpoint(&endpoint) {
                Ok(Value::Null)
            } else {
                bail!("Node has not been added")
            }
        }
        _ => bail!("addnode command must be add, remove, or onetry"),
    }
}

fn disconnect_node(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let address = match params.get(0) {
        None | Some(Value::Null) => None,
        Some(value) => Some(
            value
                .as_str()
                .ok_or_else(|| anyhow!("address must be a string"))?,
        ),
    };
    let peer_id = params
        .get(1)
        .filter(|value| !value.is_null())
        .map(|value| {
            let peer_id = value
                .as_i64()
                .ok_or_else(|| anyhow!("nodeid must be an integer"))?;
            usize::try_from(peer_id).map_err(|_| anyhow!("nodeid is out of range"))
        })
        .transpose()?;
    let disconnected = match (address, peer_id) {
        (Some(address), None) if !address.is_empty() => {
            node.disconnect_peer_endpoint(&parse_node_endpoint(node, address)?)
        }
        (Some(""), Some(peer_id)) => node.disconnect_peer(peer_id),
        (None, Some(peer_id)) => node.disconnect_peer(peer_id),
        _ => bail!("only one of address and nodeid should be provided"),
    };
    if !disconnected {
        bail!("node is not connected")
    }
    Ok(Value::Null)
}

fn get_added_node_info(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let requested = match params.get(0) {
        None | Some(Value::Null) => None,
        Some(value) => Some(parse_node_endpoint(
            node,
            value
                .as_str()
                .ok_or_else(|| anyhow!("node must be a string"))?,
        )?),
    };
    let peers = node.peer_infos();
    let mut result = Vec::new();
    let mut added_nodes = node.added_network_endpoints();
    added_nodes.sort_unstable();
    for endpoint in added_nodes {
        if requested
            .as_ref()
            .is_some_and(|requested| requested != &endpoint)
        {
            continue;
        }
        let matching = peers.iter().find(|peer| peer.endpoint == endpoint);
        result.push(json!({
            "addednode": node
                .added_node_name(&endpoint)
                .unwrap_or_else(|| endpoint.to_string()),
            "connected": matching.is_some(),
            "addresses": matching.into_iter().map(|peer| json!({
                "address": peer.endpoint.to_string(),
                "connected": if peer.inbound { "inbound" } else { "outbound" },
            })).collect::<Vec<_>>(),
        }));
    }
    if requested.is_some() && result.is_empty() {
        bail!("node has not been added")
    }
    Ok(Value::Array(result))
}

fn set_ban(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let address = param::<String>(params, 0)?;
    let command = param::<String>(params, 1)?;
    let subnet = crate::IpSubnet::parse(&address)?;
    match command.as_str() {
        "add" => {
            let requested_duration = optional_u64(params, 2, 86_400, "bantime")?;
            let absolute = optional_bool(params, 3, false, "absolute")?;
            let (requested_duration, absolute) = if requested_duration == 0 {
                (86_400, false)
            } else {
                (requested_duration, absolute)
            };
            let now = unix_time();
            let ban_until = if absolute {
                requested_duration
            } else {
                now.saturating_add(requested_duration)
            };
            if ban_until <= now {
                bail!("ban time must be in the future")
            }
            node.ban_subnet(subnet, ban_until, "manually banned".to_owned())?;
            Ok(Value::Null)
        }
        "remove" => {
            if node.unban_subnet(subnet)? {
                Ok(Value::Null)
            } else {
                bail!("unban failed: address is not banned")
            }
        }
        _ => bail!("setban command must be add or remove"),
    }
}

fn list_banned(node: &Arc<Node>) -> Result<Value> {
    let now = unix_time();
    Ok(json!(
        node.banned_addresses()
            .into_iter()
            .map(|entry| json!({
                "address": entry.subnet().display(),
                "ban_created": entry.ban_created,
                "banned_until": entry.ban_until,
                "ban_duration": entry.ban_until.saturating_sub(entry.ban_created),
                "time_remaining": entry.ban_until.saturating_sub(now),
            }))
            .collect::<Vec<_>>()
    ))
}

fn clear_banned(node: &Arc<Node>) -> Result<Value> {
    for entry in node.banned_addresses() {
        node.unban_subnet(entry.subnet())?;
    }
    Ok(Value::Null)
}

fn parse_socket_address(value: &str) -> Result<SocketAddr> {
    value
        .parse()
        .map_err(|error| anyhow!("invalid network address {value}: {error}"))
}

fn parse_node_endpoint(node: &Arc<Node>, value: &str) -> Result<NetworkEndpoint> {
    NetworkEndpoint::parse_manual(value, default_p2p_port(node.config.network))
}

fn parse_ip_address(value: &str) -> Result<IpAddr> {
    if value.contains('/') {
        bail!("network ranges are not supported; use a single IP address")
    }
    value
        .parse()
        .map_err(|error| anyhow!("invalid IP address {value}: {error}"))
}

fn unix_time() -> u64 {
    crate::time::unix_time()
}

fn get_blockchain_info(node: &Arc<Node>) -> Result<Value> {
    let chain = node.chain.read();
    let tip = chain.tip();
    let header_tip = chain.best_header_tip();
    let header = chain.header(tip.height).expect("tip header exists");
    let minimum_chain_work = chain.minimum_chain_work();
    let initial_block_download = chain.is_initial_block_download();
    let verification_progress = if !initial_block_download {
        1.0
    } else {
        let work_progress = if minimum_chain_work == bitcoin::pow::Work::from_be_bytes([0; 32]) {
            0.0
        } else {
            (work_to_f64(tip.work) / work_to_f64(minimum_chain_work)).min(1.0)
        };
        let height_progress = if header_tip.height == 0 {
            0.0
        } else {
            f64::from(tip.height) / f64::from(header_tip.height)
        };
        work_progress.min(height_progress).clamp(0.0, 1.0)
    };
    let mut result = json!({
        "chain": network_name(chain.network),
        "blocks": tip.height,
        "headers": header_tip.height,
        "bestblockhash": tip.hash.to_string(),
        "chainwork": format!("{:064x}", tip.work),
        "bits": format!("{:08x}", header.bits.to_consensus()),
        "target": format!("{:064x}", header.target()),
        "difficulty": header.difficulty_float(),
        "time": header.time,
        "mediantime": chain.median_time_past_value(),
        "verificationprogress": verification_progress,
        "initialblockdownload": initial_block_download,
        "pruned": chain.is_pruned(),
        "size_on_disk": chain.store.disk_usage().unwrap_or(0),
        "warnings": [],
    });
    if chain.is_pruned() {
        // ChainState stores the first retained block height. Core exposes
        // the same boundary as getblockchaininfo.pruneheight (last pruned
        // height plus one).
        result["pruneheight"] = json!(chain.prune_height().unwrap_or_default());
        result["automatic_pruning"] = json!(chain.prune_target_size().is_some());
        if let Some(target_size) = chain.prune_target_size() {
            result["prune_target_size"] = json!(target_size);
        }
    }
    if let Some(challenge) = chain.signet_challenge() {
        result["signet_challenge"] = json!(hex::encode(challenge));
    }
    Ok(result)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Bip9State {
    Defined,
    Started,
    LockedIn,
    Active,
    Failed,
}

impl Bip9State {
    fn as_str(self) -> &'static str {
        match self {
            Self::Defined => "defined",
            Self::Started => "started",
            Self::LockedIn => "locked_in",
            Self::Active => "active",
            Self::Failed => "failed",
        }
    }
}

fn median_header_time(headers: &[bitcoin::block::Header], end: usize) -> u32 {
    let start = end.saturating_sub(10);
    let mut times = headers[start..=end]
        .iter()
        .map(|header| header.time)
        .collect::<Vec<_>>();
    times.sort_unstable();
    times[times.len() / 2]
}

fn version_signals(header: &bitcoin::block::Header, bit: u8) -> bool {
    let version = header.version.to_consensus() as u32;
    version & 0xe000_0000 == 0x2000_0000 && version & (1u32 << bit) != 0
}

fn bip9_state_at_height(
    headers: &[bitcoin::block::Header],
    deployment: validation::Bip9Deployment,
    next_height: u32,
) -> (Bip9State, u32) {
    if deployment.start_time == validation::Bip9Deployment::ALWAYS_ACTIVE_TIME {
        return (Bip9State::Active, 0);
    }
    if deployment.start_time == validation::Bip9Deployment::NEVER_ACTIVE_TIME {
        return (Bip9State::Failed, 0);
    }
    let period = deployment.period.max(1);
    let mut state = Bip9State::Defined;
    let mut since = 0;
    let mut boundary = period;
    while boundary <= next_height {
        let previous_end = usize::try_from(boundary - 1)
            .unwrap_or(usize::MAX)
            .min(headers.len().saturating_sub(1));
        let previous_start = usize::try_from(boundary.saturating_sub(period))
            .unwrap_or(usize::MAX)
            .min(previous_end);
        let median_time = median_header_time(headers, previous_end);
        let signal_count = headers[previous_start..=previous_end]
            .iter()
            .filter(|header| version_signals(header, deployment.bit))
            .count() as u32;
        let next_state = match state {
            Bip9State::Defined if i64::from(median_time) >= deployment.start_time => {
                Bip9State::Started
            }
            Bip9State::Started if i64::from(median_time) >= deployment.timeout => Bip9State::Failed,
            Bip9State::Started if signal_count >= deployment.threshold => Bip9State::LockedIn,
            Bip9State::LockedIn if boundary >= deployment.min_activation_height => {
                Bip9State::Active
            }
            _ => state,
        };
        if next_state != state {
            state = next_state;
            since = boundary;
        }
        let Some(next_boundary) = boundary.checked_add(period) else {
            break;
        };
        boundary = next_boundary;
    }
    (state, since)
}

fn bip9_deployment_json(
    headers: &[bitcoin::block::Header],
    selected_height: u32,
    deployment: validation::Bip9Deployment,
) -> Value {
    let next_height = selected_height.saturating_add(1);
    let (state, since) = bip9_state_at_height(headers, deployment, next_height);
    let (next_state, _) = bip9_state_at_height(headers, deployment, next_height.saturating_add(1));
    let mut bip9 = json!({
        "start_time": deployment.start_time,
        "timeout": deployment.timeout,
        "min_activation_height": deployment.min_activation_height,
        "status": state.as_str(),
        "since": since,
        "status_next": next_state.as_str(),
    });
    if matches!(state, Bip9State::Started | Bip9State::LockedIn) {
        let period = deployment.period.max(1);
        let period_start = (selected_height / period) * period;
        let start = usize::try_from(period_start).unwrap_or(usize::MAX);
        let end = usize::try_from(selected_height)
            .unwrap_or(usize::MAX)
            .min(headers.len().saturating_sub(1));
        let (count, signalling) = if start <= end {
            let mut signalling = String::with_capacity(end - start + 1);
            let mut count = 0u32;
            for header in &headers[start..=end] {
                if version_signals(header, deployment.bit) {
                    count = count.saturating_add(1);
                    signalling.push('#');
                } else {
                    signalling.push('-');
                }
            }
            (count, signalling)
        } else {
            (0, String::new())
        };
        let elapsed = if start <= end {
            u32::try_from(end - start + 1).unwrap_or(period)
        } else {
            0
        };
        bip9["bit"] = json!(deployment.bit);
        bip9["statistics"] = json!({
            "period": period,
            "elapsed": elapsed,
            "count": count,
            "threshold": deployment.threshold,
            "possible": count.saturating_add(period.saturating_sub(elapsed)) >= deployment.threshold,
        });
        bip9["signalling"] = json!(signalling);
    }
    let mut result = json!({
        "type": "bip9",
        "active": state == Bip9State::Active,
        "bip9": bip9,
    });
    if state == Bip9State::Active {
        result["height"] = json!(since);
    }
    result
}

fn script_flag_names(flags: u32) -> Vec<&'static str> {
    [
        (
            bitcoinconsensus::VERIFY_CHECKLOCKTIMEVERIFY,
            "CHECKLOCKTIMEVERIFY",
        ),
        (
            bitcoinconsensus::VERIFY_CHECKSEQUENCEVERIFY,
            "CHECKSEQUENCEVERIFY",
        ),
        (bitcoinconsensus::VERIFY_DERSIG, "DERSIG"),
        (bitcoinconsensus::VERIFY_NULLDUMMY, "NULLDUMMY"),
        (bitcoinconsensus::VERIFY_P2SH, "P2SH"),
        (bitcoinconsensus::VERIFY_TAPROOT, "TAPROOT"),
        (bitcoinconsensus::VERIFY_WITNESS, "WITNESS"),
    ]
    .into_iter()
    .filter_map(|(flag, name)| (flags & flag != 0).then_some(name))
    .collect()
}

fn get_deployment_info(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let chain = node.chain.read();
    let hash = match params.get(0).filter(|value| !value.is_null()) {
        Some(value) => value
            .as_str()
            .ok_or_else(|| anyhow!("blockhash must be a string"))?
            .parse::<BlockHash>()?,
        None => chain.best_hash(),
    };
    let height = chain
        .block_height_by_hash(&hash)
        .ok_or_else(|| anyhow!("Block not found"))?;
    let headers = chain
        .headers_to_hash(&hash)
        .ok_or_else(|| anyhow!("Block header chain is unavailable"))?;
    let heights = validation::buried_deployment_heights(chain.network);
    let mut deployments = serde_json::Map::new();
    for (name, activation_height) in [
        ("bip34", heights.bip34),
        ("dersig", heights.bip66),
        ("cltv", heights.bip65),
        ("csv", heights.csv),
        ("segwit", heights.segwit),
    ] {
        deployments.insert(
            name.to_owned(),
            json!({
                "type": "buried",
                "active": height.saturating_add(1) >= activation_height,
                "height": activation_height,
            }),
        );
    }
    let [testdummy, taproot] = validation::bip9_deployments(chain.network);
    // Core does not register NEVER_ACTIVE deployments in getdeploymentinfo.
    // Regtest intentionally keeps testdummy enabled for versionbits tests.
    if testdummy.is_enabled() {
        deployments.insert(
            "testdummy".to_owned(),
            bip9_deployment_json(&headers, height, testdummy),
        );
    }
    deployments.insert(
        "taproot".to_owned(),
        bip9_deployment_json(&headers, height, taproot),
    );
    let flags = validation::script_flags_for_block_with_hash(chain.network, height, Some(hash));
    Ok(json!({
        "hash": hash.to_string(),
        "height": height,
        "script_flags": script_flag_names(flags),
        "deployments": Value::Object(deployments),
    }))
}

fn get_block_header(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let hash: BlockHash = param::<String>(params, 0)?.parse()?;
    let verbose = optional_bool(params, 1, true, "verbose")?;
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
    let mut result = json!({
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
    });
    if height > 0 {
        result["previousblockhash"] = json!(header.prev_blockhash.to_string());
    }
    if let Some(next) = chain.next_block_hash(&hash) {
        result["nextblockhash"] = json!(next.to_string());
    }
    Ok(result)
}

fn get_chain_tx_stats(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let explicit_window = params.get(0).is_some_and(|value| !value.is_null());
    let default_window = {
        let spacing = node.config.network.params().pow_target_spacing;
        i64::try_from((30 * 24 * 60 * 60) / spacing).unwrap_or(i64::MAX)
    };
    let requested_window = optional_i64(params, 0, default_window, "nblocks")?;
    let requested_hash = params
        .get(1)
        .filter(|value| !value.is_null())
        .map(|value| {
            value
                .as_str()
                .ok_or_else(|| anyhow!("blockhash must be a string"))?
                .parse::<BlockHash>()
                .map_err(|error| anyhow!("invalid blockhash: {error}"))
        })
        .transpose()?;
    let chain = node.chain.write();
    let end_height = if let Some(hash) = requested_hash {
        let height = chain
            .block_height_by_hash(&hash)
            .ok_or_else(|| anyhow!("Block not found"))?;
        if !chain.is_active_block(&hash) {
            bail!("Block is not in main chain");
        }
        height
    } else {
        chain.height()
    };
    let window = if explicit_window {
        if requested_window < 0
            || (requested_window > 0 && requested_window >= i64::from(end_height))
        {
            bail!("Invalid block count: should be between 0 and the block's height - 1");
        }
        u32::try_from(requested_window).context("block count is out of range")?
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
    let txcount = chain.chain_transaction_count(end_height);
    let window_tx_count = if window > 0 {
        chain
            .chain_transaction_count(end_height)
            .zip(chain.chain_transaction_count(start_height))
            .map(|(end, start)| end.saturating_sub(start))
    } else {
        None
    };
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
        "window_final_block_hash": end_hash.to_string(),
        "window_final_block_height": end_height,
        "window_block_count": window,
    });
    if let Some(txcount) = txcount {
        result["txcount"] = json!(txcount);
    }
    if window > 0 {
        result["window_interval"] = json!(interval);
        if let Some(window_tx_count) = window_tx_count {
            result["window_tx_count"] = json!(window_tx_count);
            if interval > 0 {
                result["txrate"] = json!(window_tx_count as f64 / interval as f64);
            }
        }
    }
    Ok(result)
}

fn get_network_hash_ps(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let nblocks = optional_i64(params, 0, 120, "nblocks")?;
    if nblocks < -1 || nblocks == 0 {
        bail!("Invalid nblocks. Must be a positive number or -1.");
    }
    let requested_height = optional_i64(params, 1, -1, "height")?;
    if requested_height < -1 {
        bail!("Block does not exist at specified height");
    }
    let chain = node.chain.read();
    if requested_height > i64::from(chain.height()) {
        bail!("Block does not exist at specified height");
    }
    let end_height = if requested_height == -1 {
        chain.height()
    } else {
        u32::try_from(requested_height).map_err(|_| anyhow!("height is out of range"))?
    };
    if end_height == 0 {
        return Ok(json!(0.0));
    }
    let mut lookup = if nblocks == -1 {
        let interval = node
            .config
            .network
            .params()
            .difficulty_adjustment_interval();
        u64::from(end_height) % interval + 1
    } else {
        u64::try_from(nblocks).map_err(|_| anyhow!("nblocks is out of range"))?
    };
    lookup = lookup.min(u64::from(end_height));
    let start_height = end_height
        .checked_sub(u32::try_from(lookup).map_err(|_| anyhow!("nblocks is out of range"))?)
        .ok_or_else(|| anyhow!("nblocks is out of range"))?;
    let first_time = chain
        .header(start_height)
        .ok_or_else(|| anyhow!("block height out of range"))?
        .time;
    let mut min_time = first_time;
    let mut max_time = first_time;
    for height in start_height..=end_height {
        let header = chain
            .header(height)
            .ok_or_else(|| anyhow!("block height out of range"))?;
        min_time = min_time.min(header.time);
        max_time = max_time.max(header.time);
    }
    if min_time == max_time {
        return Ok(json!(0.0));
    }
    let start_hash = chain
        .block_hash(start_height)
        .ok_or_else(|| anyhow!("block height out of range"))?;
    let end_hash = chain
        .block_hash(end_height)
        .ok_or_else(|| anyhow!("block height out of range"))?;
    let work = chain
        .chain_work_by_hash(&end_hash)
        .zip(chain.chain_work_by_hash(&start_hash))
        .map(|(end_work, start_work)| work_to_f64(end_work - start_work))
        .unwrap_or(0.0);
    Ok(json!(work / f64::from(max_time.saturating_sub(min_time))))
}

fn get_mining_info(node: &Arc<Node>) -> Result<Value> {
    let network_hashps = get_network_hash_ps(node, &json!([]))?;
    let chain = node.chain.read();
    let tip = chain.tip();
    let header = chain.header(tip.height).expect("tip header exists");
    let now = u32::try_from(crate::time::unix_time()).unwrap_or(u32::MAX);
    let next_time = now.max(header.time.saturating_add(1));
    let next_bits = chain.next_bits(next_time);
    let mempool = node.mempool.read();
    let mut result = json!({
        "blocks": tip.height,
        "bits": format!("{:08x}", header.bits.to_consensus()),
        "difficulty": header.difficulty_float(),
        "networkhashps": network_hashps,
        "pooledtx": mempool.len(),
        "blockmintxfee": sat_to_btc(node.config.block_min_tx_fee_sat_per_kvb),
        "chain": network_name(chain.network),
        "next": {
            "height": tip.height.saturating_add(1),
            "bits": format!("{:08x}", next_bits),
            "difficulty": bitcoin::pow::Target::from_compact(
                bitcoin::pow::CompactTarget::from_consensus(next_bits),
            )
            .difficulty_float(),
            "target": format!(
                "{:064x}",
                bitcoin::pow::Target::from_compact(
                    bitcoin::pow::CompactTarget::from_consensus(next_bits)
                )
            ),
        },
        "target": format!("{:064x}", header.target()),
        "warnings": [],
    });
    if let Some((weight, transactions)) = node.last_mining_block() {
        result["currentblockweight"] = json!(weight);
        result["currentblocktx"] = json!(transactions);
    }
    if let Some(challenge) = chain.signet_challenge() {
        result["signet_challenge"] = json!(hex::encode(challenge));
    }
    Ok(result)
}

fn get_block(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let hash: BlockHash = param::<String>(params, 0)?.parse()?;
    let verbosity = parse_verbosity(params.get(1), 1)?;
    let mut chain = node.chain.write();
    let height = chain
        .block_height_by_hash(&hash)
        .ok_or_else(|| anyhow!("Block not found"))?;
    let block = chain
        .block(&hash)?
        .ok_or_else(|| anyhow!("Block not available"))?;
    if verbosity <= 0 {
        return Ok(json!(hex::encode(serialize(&block))));
    }
    let confirmations = if chain.is_active_block(&hash) {
        chain.height().saturating_sub(height) as i64 + 1
    } else {
        -1
    };
    let undo = if verbosity >= 2 {
        chain.spent_outputs_by_transaction(&hash)?
    } else {
        None
    };
    let txs = if verbosity >= 2 {
        block
            .txdata
            .iter()
            .enumerate()
            .map(|(transaction_index, tx)| {
                let mut transaction_json =
                    rpc_transaction(tx, None, None, None, None, chain.network);
                if let Some(undo) = undo.as_ref() {
                    let spent_outputs = undo.get(transaction_index).ok_or_else(|| {
                        anyhow!("Block undo is missing transaction {transaction_index}")
                    })?;
                    if verbosity >= 3 {
                        add_prevout_details(
                            &mut transaction_json,
                            tx,
                            spent_outputs,
                            &mut chain,
                            node.config.network,
                        )?;
                    } else {
                        add_transaction_fee(&mut transaction_json, tx, spent_outputs)?;
                    }
                }
                Ok(transaction_json)
            })
            .collect::<Result<Vec<_>>>()?
    } else {
        block
            .txdata
            .iter()
            .map(Transaction::compute_txid)
            .map(|txid| json!(txid.to_string()))
            .collect()
    };
    let mut result = json!({
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
        "coinbase_tx": coinbase_transaction_json(&block.txdata[0]),
    });
    if height > 0 {
        result["previousblockhash"] = json!(block.header.prev_blockhash.to_string());
    }
    if let Some(next) = chain.next_block_hash(&hash) {
        result["nextblockhash"] = json!(next.to_string());
    }
    Ok(result)
}

fn get_block_filter(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let hash: BlockHash = param::<String>(params, 0)?.parse()?;
    let filter_type = optional_str(params, 1, "basic", "filtertype")?;
    if filter_type != "basic" {
        bail!("Unknown filtertype")
    }
    if !node.config.blockfilterindex {
        bail!("Index is not enabled for filtertype {filter_type}")
    }
    let mut chain = node.chain.write();
    if chain.block_height_by_hash(&hash).is_none() {
        bail!("Block not found")
    }
    let block_was_connected = chain.is_active_block(&hash) || chain.store.contains(&hash);
    let Some((content, header)) = chain.basic_filter_for_block(&hash)? else {
        if !block_was_connected {
            bail!("Filter not found. Block was not connected to active chain.")
        }
        bail!("Filter not found. This error is unexpected and indicates index corruption.")
    };
    Ok(json!({
        "filter": hex::encode(content),
        "header": header.to_string(),
    }))
}

fn submit_header(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let bytes = hex::decode(param::<String>(params, 0)?)?;
    let header: bitcoin::block::Header = deserialize(&bytes)?;
    node.chain.write().accept_headers(&[header])?;
    Ok(Value::Null)
}

fn invalidate_block(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let hash: BlockHash = param::<String>(params, 0)?.parse()?;
    node.invalidate_block(hash)?;
    Ok(Value::Null)
}

fn reconsider_block(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let hash: BlockHash = param::<String>(params, 0)?.parse()?;
    node.reconsider_block(hash)?;
    Ok(Value::Null)
}

fn precious_block(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let hash: BlockHash = param::<String>(params, 0)?.parse()?;
    node.precious_block(hash)?;
    Ok(Value::Null)
}

fn dump_txoutset(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let path = snapshot_path(node, &param::<String>(params, 0)?);
    let dump_type = optional_str(params, 1, "", "type")?;
    let rollback = match params.get(2).filter(|value| !value.is_null()) {
        Some(options) => {
            let Some(options) = options.as_object() else {
                bail!("dumptxoutset options must be an object")
            };
            for name in options.keys() {
                if name != "rollback" {
                    bail!("unknown dumptxoutset option {name}")
                }
            }
            options.get("rollback")
        }
        None => None,
    };
    if rollback.is_some() && !dump_type.is_empty() && dump_type != "rollback" {
        bail!("Invalid snapshot type \"{dump_type}\" specified with rollback option")
    }
    if dump_type.is_empty() && rollback.is_none() {
        bail!("Invalid snapshot type \"\" specified. Please specify \"rollback\" or \"latest\"")
    }
    if !dump_type.is_empty() && dump_type != "latest" && dump_type != "rollback" {
        bail!(
            "Invalid snapshot type \"{dump_type}\" specified. Please specify \"rollback\" or \"latest\""
        )
    }
    if path.exists() {
        bail!(
            "{} already exists; move it out of the way before creating a snapshot",
            path.display()
        )
    }
    let target = {
        let chain = node.chain.read();
        match rollback {
            Some(value) => Some(parse_rollback_target(&chain, value)?),
            None if dump_type == "rollback" => Some(chain.latest_snapshot_hash()),
            None => None,
        }
    };
    if let Some(target) = target {
        let (coins_written, base_hash, base_height, txoutset_hash, nchaintx) =
            node.chain.write().dump_utxo_set_at(&path, target)?;
        return Ok(json!({
            "coins_written": coins_written,
            "base_hash": base_hash.to_string(),
            "base_height": base_height,
            "path": path.to_string_lossy(),
            "txoutset_hash": txoutset_hash,
            "nchaintx": nchaintx,
        }));
    }
    let chain = node.chain.read();
    let (coins_written, base_hash, base_height) = chain.dump_utxo_set(&path)?;
    Ok(json!({
        "coins_written": coins_written,
        "base_hash": base_hash.to_string(),
        "base_height": base_height,
        "path": path.to_string_lossy(),
        "txoutset_hash": chain.utxo_serialized_hash(),
        "nchaintx": chain.active_transaction_count(),
    }))
}

fn parse_rollback_target(chain: &chain::ChainState, value: &Value) -> Result<BlockHash> {
    let height = if let Some(value) = value.as_u64() {
        u32::try_from(value).context("rollback height is too large")?
    } else if let Some(value) = value.as_str() {
        if let Ok(hash) = value.parse::<BlockHash>() {
            if chain.is_active_block(&hash) {
                return Ok(hash);
            }
            bail!("Could not roll back to requested height.")
        }
        value
            .parse::<u32>()
            .context("rollback must be a block height or hash")?
    } else {
        bail!("rollback must be a block height or hash")
    };
    chain
        .block_hash(height)
        .context("Could not roll back to requested height.")
}

fn load_txoutset(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let path = snapshot_path(node, &param::<String>(params, 0)?);
    let (coins_loaded, tip_hash, base_height) = node.chain.write().load_assumeutxo_set(&path)?;
    Ok(json!({
        "coins_loaded": coins_loaded,
        "tip_hash": tip_hash.to_string(),
        "base_height": base_height,
        "path": path.to_string_lossy(),
    }))
}

fn snapshot_path(node: &Arc<Node>, path: &str) -> std::path::PathBuf {
    let path = std::path::PathBuf::from(path);
    if path.is_absolute() {
        path
    } else {
        node.config.datadir.join(path)
    }
}

fn prune_blockchain(node: &Arc<Node>, params: &Value) -> Result<Value> {
    if node.config.prune == 0 {
        bail!("Cannot prune blocks because node is not in prune mode.");
    }
    let requested = param::<i64>(params, 0)?;
    if requested < 0 {
        bail!("Negative block height.");
    }
    let first_retained = node.chain.write().prune(requested as u64)?;
    // ChainState keeps the first retained block as its pruning boundary;
    // Core's RPC returns the last block actually pruned, or -1 when none
    // has been pruned yet.
    Ok(json!(
        first_retained.checked_sub(1).map(i64::from).unwrap_or(-1)
    ))
}

async fn wait_for_new_block(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let timeout = rpc_timeout(params, 0)?;
    let current_tip = params
        .get(1)
        .filter(|value| !value.is_null())
        .map(|value| {
            value
                .as_str()
                .ok_or_else(|| anyhow!("current_tip must be a block hash"))?
                .parse::<BlockHash>()
                .map_err(|error| anyhow!("invalid current_tip: {error}"))
        })
        .transpose()?;
    let mut events = node.subscribe_chain();
    let current_tip = current_tip.unwrap_or_else(|| node.chain.read().best_hash());
    loop {
        let tip = node.chain.read().tip();
        if tip.hash != current_tip {
            return Ok(json!({"hash": tip.hash.to_string(), "height": tip.height}));
        }
        let Some(tip) = receive_chain_event(&mut events, timeout).await? else {
            return current_tip_json(node);
        };
        if tip.hash != current_tip {
            return Ok(json!({"hash": tip.hash.to_string(), "height": tip.height}));
        }
    }
}

async fn wait_for_block(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let hash: BlockHash = param::<String>(params, 0)?.parse()?;
    let timeout = rpc_timeout(params, 1)?;
    let mut events = node.subscribe_chain();
    let mut current_tip = node.chain.read().tip();
    if current_tip.hash == hash {
        return Ok(json!({"hash": current_tip.hash.to_string(), "height": current_tip.height}));
    }
    loop {
        let Some(tip) = receive_chain_event(&mut events, timeout).await? else {
            return Ok(json!({
                "hash": current_tip.hash.to_string(),
                "height": current_tip.height,
            }));
        };
        current_tip = tip.clone();
        if tip.hash == hash {
            return Ok(json!({"hash": tip.hash.to_string(), "height": tip.height}));
        }
    }
}

async fn wait_for_block_height(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let height = param::<u64>(params, 0)?;
    let height = u32::try_from(height).map_err(|_| anyhow!("height is out of range"))?;
    let timeout = rpc_timeout(params, 1)?;
    let mut events = node.subscribe_chain();
    let mut current_tip = node.chain.read().tip();
    if current_tip.height >= height {
        return Ok(json!({
            "hash": current_tip.hash.to_string(),
            "height": current_tip.height,
        }));
    }
    loop {
        let Some(tip) = receive_chain_event(&mut events, timeout).await? else {
            return Ok(json!({
                "hash": current_tip.hash.to_string(),
                "height": current_tip.height,
            }));
        };
        current_tip = tip.clone();
        if tip.height >= height {
            return Ok(json!({
                "hash": tip.hash.to_string(),
                "height": tip.height,
            }));
        }
    }
}

fn rpc_timeout(params: &Value, index: usize) -> Result<Option<tokio::time::Instant>> {
    let timeout = params
        .get(index)
        .filter(|value| !value.is_null())
        .map(|value| {
            value
                .as_u64()
                .ok_or_else(|| anyhow!("timeout must be a non-negative integer"))
        })
        .transpose()?;
    Ok(timeout
        .filter(|milliseconds| *milliseconds != 0)
        .map(|milliseconds| {
            tokio::time::Instant::now() + std::time::Duration::from_millis(milliseconds)
        }))
}

async fn receive_chain_event(
    events: &mut broadcast::Receiver<chain::ChainTip>,
    deadline: Option<tokio::time::Instant>,
) -> Result<Option<chain::ChainTip>> {
    loop {
        let received = if let Some(deadline) = deadline {
            match tokio::time::timeout_at(deadline, events.recv()).await {
                Ok(received) => received,
                Err(_) => return Ok(None),
            }
        } else {
            events.recv().await
        };
        match received {
            Ok(tip) => return Ok(Some(tip)),
            Err(broadcast::error::RecvError::Lagged(_)) => continue,
            Err(broadcast::error::RecvError::Closed) => {
                bail!("chain event stream is closed")
            }
        }
    }
}

fn current_tip_json(node: &Arc<Node>) -> Result<Value> {
    let tip = node.chain.read().tip();
    Ok(json!({"hash": tip.hash.to_string(), "height": tip.height}))
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
    let mut unique_txids = HashSet::with_capacity(txids.len());
    for txid in &txids {
        if !unique_txids.insert(*txid) {
            bail!("invalid parameter, duplicated txid: {txid}");
        }
    }
    let requested_hash = params
        .get(1)
        .filter(|value| !value.is_null())
        .map(|value| {
            value
                .as_str()
                .ok_or_else(|| anyhow!("blockhash must be a string"))?
                .parse::<BlockHash>()
                .map_err(|error| anyhow!("invalid blockhash: {error}"))
        })
        .transpose()?;
    let mut chain = node.chain.write();
    let block_hash = if let Some(hash) = requested_hash {
        hash
    } else {
        // Core can locate a block without -txindex only when one of the
        // requested transactions still has an output in the active UTXO set.
        // The internal active-chain index is also used by Electrum, but must
        // not silently expand this RPC's Core-visible lookup semantics.
        let requested_txids: HashSet<Txid> = txids.iter().copied().collect();
        let mut utxo_blocks = HashMap::new();
        for (outpoint, entry) in chain.all_utxos() {
            if requested_txids.contains(&outpoint.txid)
                && let Some(block_hash) = chain.block_hash(entry.height)
            {
                utxo_blocks.entry(outpoint.txid).or_insert(block_hash);
            }
        }
        let mut sorted_txids = txids.clone();
        sorted_txids.sort_unstable();
        let utxo_block = sorted_txids
            .iter()
            .find_map(|txid| utxo_blocks.get(txid).copied());
        let txindex_block = if node.config.txindex {
            chain
                .transaction(txids.iter().min().expect("non-empty txid set"))?
                .map(|(_, location)| location.block_hash)
        } else {
            None
        };
        utxo_block
            .or(txindex_block)
            .ok_or_else(|| anyhow!("Transaction not yet in block"))?
    };
    if chain.block_height_by_hash(&block_hash).is_none() {
        bail!("Block not found");
    }
    let block = chain
        .block(&block_hash)?
        .ok_or_else(|| anyhow!("Block not available"))?;
    let block_txids: HashMap<Txid, usize> = block
        .txdata
        .iter()
        .enumerate()
        .map(|(index, transaction)| (transaction.compute_txid(), index))
        .collect();
    if txids.iter().any(|txid| !block_txids.contains_key(txid)) {
        bail!("Not all transactions found in specified or retrieved block");
    }
    let proof = serialize_merkle_proof(&block, &txids)?;
    Ok(json!(hex::encode(proof)))
}

fn verify_txout_proof(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let Some((header, matches, total)) = parse_merkle_proof(params)? else {
        return Ok(json!([]));
    };
    let block_hash = header.block_hash();
    let mut chain = node.chain.write();
    if !chain.is_active_block(&block_hash) {
        bail!("Block not found in chain");
    }
    let transaction_count = chain
        .block_transaction_count(&block_hash)?
        .ok_or_else(|| anyhow!("Block not found in chain"))?;
    if transaction_count != total {
        return Ok(json!([]));
    }
    Ok(json!(
        matches
            .into_iter()
            .map(|txid| txid.to_string())
            .collect::<Vec<_>>()
    ))
}

fn parse_merkle_proof(params: &Value) -> Result<Option<(Header, Vec<Txid>, usize)>> {
    let bytes = hex::decode(param::<String>(params, 0)?)?;
    if bytes.len() < 84 {
        bail!("invalid merkle proof");
    }
    let header: bitcoin::block::Header = deserialize(&bytes[..80])?;
    let mut reader = ProofReader::new(&bytes[80..]);
    let total = reader.u32()? as usize;
    if total == 0 || total > MAX_MERKLE_PROOF_TRANSACTIONS {
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
    if cursor.flag_index.div_ceil(8) != flags.len() || cursor.hash_index != hashes.len() {
        bail!("invalid merkle proof");
    }
    if root.to_raw_hash() != header.merkle_root.to_raw_hash() {
        return Ok(None);
    }
    Ok(Some((header, matches, total)))
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
        let (right, right_matches) =
            extract_merkle_node(height - 1, position * 2 + 1, total, cursor)?;
        if right == left {
            bail!("invalid merkle proof");
        }
        (right, right_matches)
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
            .ok_or_else(|| anyhow!("block selector must be a hash or height"))?;
        let height =
            u32::try_from(height).map_err(|_| anyhow!("block selector height is out of range"))?;
        node.chain
            .read()
            .block_hash(height)
            .ok_or_else(|| anyhow!("block height out of range"))?
    };
    let mut chain = node.chain.write();
    let height = chain
        .block_height_by_hash(&hash)
        .ok_or_else(|| anyhow!("Block not found"))?;
    let block = chain
        .block(&hash)?
        .ok_or_else(|| anyhow!("Block not available"))?;
    let fee_stats = chain
        .block_fee_stats(&hash)?
        .ok_or_else(|| anyhow!("Undo data not available"))?;
    let height = Some(height);
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
    let is_bip30_repeat =
        height.is_some_and(|height| chain::is_bip30_repeat(chain.network, height, hash));
    for transaction in &block.txdata {
        outputs = outputs.saturating_add(transaction.output.len());
        for output in &transaction.output {
            let size = utxo_stat_size(output);
            utxo_size_inc = utxo_size_inc.saturating_add(size);
            let excluded_from_utxo = height == Some(0)
                || (is_bip30_repeat && transaction.is_coinbase())
                || output.script_pubkey.is_op_return()
                || output.script_pubkey.len() > MAX_SCRIPT_SIZE;
            if !excluded_from_utxo {
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
            utxo_size_inc_actual = utxo_size_inc_actual.saturating_sub(size);
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
        "total_size": total_size,
        "total_weight": total_weight,
        "total_out": total_out,
        "subsidy": height
            .map(|height| validation::block_subsidy_for_network(chain.network, height))
            .unwrap_or_default(),
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
    let Some(selected_value) = params.get(1) else {
        return Ok(result);
    };
    if selected_value.is_null() {
        return Ok(result);
    }
    let selected = selected_value
        .as_array()
        .ok_or_else(|| anyhow!("block statistics must be an array"))?;
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
            .ok_or_else(|| anyhow!("Invalid selected statistic '{statistic}'"))?;
        filtered.insert(statistic.to_owned(), value);
    }
    Ok(Value::Object(filtered))
}

fn utxo_stat_size(output: &TxOut) -> i64 {
    i64::try_from(serialize(output).len().saturating_add(41)).unwrap_or(i64::MAX)
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
    let targets = [10u64, 25, 50, 75, 90]
        .map(|percentile| (u128::from(total_weight) * u128::from(percentile)).div_ceil(100));
    let mut target_index = 0usize;
    for (rate, weight) in values.iter().copied() {
        cumulative = cumulative.saturating_add(weight);
        while target_index < targets.len() && u128::from(cumulative) >= targets[target_index] {
            result[target_index] = rate;
            target_index += 1;
        }
    }
    result
}

fn get_raw_transaction(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let txid: Txid = param::<String>(params, 0)?.parse()?;
    let verbosity = parse_transaction_verbosity(params.get(1))?;
    let requested_block = params
        .get(2)
        .filter(|value| !value.is_null())
        .map(|value| {
            value
                .as_str()
                .ok_or_else(|| anyhow!("blockhash must be a string"))?
                .parse::<BlockHash>()
                .map_err(|error| anyhow!("invalid blockhash: {error}"))
        })
        .transpose()?;
    let mut chain = node.chain.write();
    if let Some(genesis_hash) = chain.block_hash(0)
        && let Some(genesis) = chain.block(&genesis_hash)?
        && genesis
            .txdata
            .first()
            .is_some_and(|transaction| transaction.compute_txid() == txid)
    {
        bail!(
            "The genesis block coinbase is not considered an ordinary transaction and cannot be retrieved"
        )
    }
    let found = if let Some(block_hash) = requested_block {
        let height = chain
            .block_height_by_hash(&block_hash)
            .ok_or_else(|| anyhow!("Block hash not found"))?;
        let block = chain
            .block(&block_hash)?
            .ok_or_else(|| anyhow!("Block not available"))?;
        let Some(transaction_index) = block
            .txdata
            .iter()
            .position(|transaction| transaction.compute_txid() == txid)
        else {
            bail!(
                "No such transaction found in the provided block. Use gettransaction for wallet transactions."
            );
        };
        Some((
            block.txdata[transaction_index].clone(),
            chain::TxLocation {
                block_hash,
                height,
                transaction_index,
            },
        ))
    } else if node.config.txindex {
        chain.transaction(&txid)?
    } else {
        None
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
        let message = if requested_block.is_some() {
            "No such transaction found in the provided block. Use gettransaction for wallet transactions."
        } else if !node.config.txindex {
            "No such mempool transaction. Use -txindex or provide a block hash to enable blockchain transaction queries. Use gettransaction for wallet transactions."
        } else {
            "No such mempool or blockchain transaction. Use gettransaction for wallet transactions."
        };
        bail!(message);
    };
    if verbosity <= 0 {
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
    let block_time = (location.block_hash != BlockHash::all_zeros()
        && chain.is_active_block(&location.block_hash))
    .then(|| {
        chain
            .header_by_hash(&location.block_hash)
            .map(|header| header.time)
    })
    .flatten();
    let mut result = rpc_transaction(
        &transaction,
        blockhash.as_deref(),
        confirmations,
        block_time,
        block_time,
        node.config.network,
    );
    if let Some(block_hash) = requested_block {
        result["in_active_chain"] = json!(chain.is_active_block(&block_hash));
    }
    if verbosity >= 2 {
        if location.block_hash != BlockHash::all_zeros() {
            if let Some(undo) = chain
                .spent_outputs_by_transaction(&location.block_hash)?
                .and_then(|entries| entries.get(location.transaction_index).cloned())
                && undo.len() == transaction.input.len()
            {
                add_prevout_details(
                    &mut result,
                    &transaction,
                    &undo,
                    &mut chain,
                    node.config.network,
                )?;
                let input_total = undo
                    .iter()
                    .map(|output| output.value.to_sat())
                    .try_fold(0u64, u64::checked_add)
                    .ok_or_else(|| anyhow!("transaction input total overflowed"))?;
                let output_total = transaction
                    .output
                    .iter()
                    .map(|output| output.value.to_sat())
                    .try_fold(0u64, u64::checked_add)
                    .ok_or_else(|| anyhow!("transaction output total overflowed"))?;
                if input_total >= output_total {
                    result["fee"] = json!(sat_to_btc(input_total - output_total));
                }
            }
        } else if let Some(entry) = node.mempool.read().get(&txid) {
            result["fee"] = json!(sat_to_btc(entry.fee_sat));
        }
    }
    Ok(result)
}

fn parse_verbosity(value: Option<&Value>, default: i64) -> Result<i64> {
    match value {
        None | Some(Value::Null) => Ok(default),
        Some(Value::Bool(verbose)) => Ok(i64::from(*verbose)),
        Some(Value::Number(number)) => number
            .as_i64()
            .ok_or_else(|| anyhow!("verbosity must be an integer")),
        Some(_) => bail!("verbosity must be an integer or boolean"),
    }
}

fn parse_transaction_verbosity(value: Option<&Value>) -> Result<i64> {
    parse_verbosity(value, 0)
}

fn decoded_transaction_json(transaction: &Transaction, network: Network) -> Value {
    let mut result = rpc_transaction(transaction, None, None, None, None, network);
    result
        .as_object_mut()
        .expect("rpc transaction is an object")
        .remove("hex");
    result
}

fn transaction_has_witness_serialization(bytes: &[u8]) -> bool {
    bytes.get(4).copied() == Some(0) && bytes.get(5).is_some_and(|flag| *flag != 0)
}

fn decode_transaction_from_params(
    params: &Value,
    hex_index: usize,
    witness_index: usize,
) -> Result<Transaction> {
    let bytes = hex::decode(param::<String>(params, hex_index)?).context("TX decode failed")?;
    if let Some(iswitness) = params
        .get(witness_index)
        .filter(|value| !value.is_null())
        .map(|value| {
            value
                .as_bool()
                .ok_or_else(|| anyhow!("iswitness must be a boolean"))
        })
        .transpose()?
        && iswitness != transaction_has_witness_serialization(&bytes)
    {
        bail!("TX decode failed")
    }
    let transaction: Transaction = deserialize(&bytes).context("TX decode failed")?;
    Ok(transaction)
}

fn decode_raw_transaction(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let transaction = decode_transaction_from_params(params, 0, 1)?;
    Ok(decoded_transaction_json(&transaction, node.config.network))
}

fn combine_raw_transaction(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let transactions = decode_raw_transaction_variants(params)?;
    let mut combined = combine_transaction_variants(&transactions)?;
    let chain = node.chain.read();
    let mempool = node.mempool.read();
    for input_index in 0..combined.input.len() {
        let previous_output = combined.input[input_index].previous_output;
        let available = !mempool.is_spent(&previous_output)
            && (chain.utxo(&previous_output).is_some()
                || mempool
                    .get(&previous_output.txid)
                    .and_then(|entry| entry.transaction.output.get(previous_output.vout as usize))
                    .is_some());
        if !available {
            bail!("Input not found or already spent")
        }
        let previous_output = output_for_outpoint(&chain, &mempool, previous_output)
            .expect("available combiner input has an output");
        combine_multisig_input(&mut combined, input_index, &transactions, &previous_output)?;
    }
    Ok(json!(hex::encode(serialize(&combined))))
}

fn decode_raw_transaction_variants(params: &Value) -> Result<Vec<Transaction>> {
    let raw_transactions = params
        .get(0)
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("combinerawtransaction expects an array of transactions"))?;
    if raw_transactions.is_empty() {
        bail!("Missing transactions")
    }
    raw_transactions
        .iter()
        .enumerate()
        .map(|(index, raw)| {
            let raw = raw
                .as_str()
                .ok_or_else(|| anyhow!("transaction {index} must be hexadecimal"))?;
            let bytes = hex::decode(raw)
                .with_context(|| format!("TX decode failed for transaction {index}"))?;
            deserialize::<Transaction>(&bytes)
                .with_context(|| format!("TX decode failed for transaction {index}"))
        })
        .collect()
}

fn combine_transaction_variants(transactions: &[Transaction]) -> Result<Transaction> {
    let first = transactions
        .first()
        .cloned()
        .ok_or_else(|| anyhow!("Missing transactions"))?;
    if transactions
        .iter()
        .skip(1)
        .any(|transaction| !raw_transactions_match(&first, transaction))
    {
        bail!("TXs are not compatible")
    }
    let mut combined = first;
    for transaction in transactions.iter().skip(1) {
        for (combined_input, input) in combined.input.iter_mut().zip(&transaction.input) {
            combined_input.script_sig =
                choose_script_sig(&combined_input.script_sig, &input.script_sig);
            combined_input.witness = choose_witness(&combined_input.witness, &input.witness);
        }
    }
    Ok(combined)
}

fn raw_transactions_match(left: &Transaction, right: &Transaction) -> bool {
    left.version == right.version
        && left.lock_time == right.lock_time
        && left.output == right.output
        && left.input.len() == right.input.len()
        && left.input.iter().zip(&right.input).all(|(left, right)| {
            left.previous_output == right.previous_output && left.sequence == right.sequence
        })
}

#[derive(Clone)]
struct MultisigCombinationContext {
    script: ScriptBuf,
    segwit: bool,
    redeem_script: Option<ScriptBuf>,
}

fn combine_multisig_input(
    transaction: &mut Transaction,
    input_index: usize,
    variants: &[Transaction],
    previous_output: &TxOut,
) -> Result<()> {
    let Some(context) = variants
        .iter()
        .filter_map(|variant| variant.input.get(input_index))
        .find_map(|input| multisig_combination_context(previous_output, input))
    else {
        return Ok(());
    };
    let Some((required, public_keys)) = multisig_script_keys(context.script.as_script()) else {
        return Ok(());
    };

    let mut candidates = Vec::<Vec<u8>>::new();
    for input in variants
        .iter()
        .filter_map(|variant| variant.input.get(input_index))
    {
        for signature in multisig_signature_items(input, &context) {
            if !signature.is_empty() && !candidates.contains(&signature) {
                candidates.push(signature);
            }
        }
    }

    let secp = Secp256k1::verification_only();
    let mut ordered = Vec::new();
    for public_key in public_keys {
        if let Some(signature) = candidates.iter().find(|signature| {
            verify_multisig_signature(
                transaction,
                input_index,
                previous_output,
                &context,
                public_key,
                signature,
                &secp,
            )
        }) {
            ordered.push(signature.clone());
        }
        if ordered.len() == required {
            break;
        }
    }
    if ordered.is_empty() {
        return Ok(());
    }

    if context.segwit {
        let mut stack = Vec::with_capacity(ordered.len().saturating_add(2));
        stack.push(Vec::new());
        stack.extend(ordered);
        stack.push(context.script.to_bytes());
        transaction.input[input_index].witness = Witness::from_slice(&stack);
        transaction.input[input_index].script_sig = context
            .redeem_script
            .as_ref()
            .map(|script| push_script_items(&[script.to_bytes()]))
            .transpose()?
            .unwrap_or_default();
    } else {
        let mut stack = Vec::with_capacity(ordered.len().saturating_add(2));
        stack.push(Vec::new());
        stack.extend(ordered);
        if let Some(redeem_script) = &context.redeem_script {
            stack.push(redeem_script.to_bytes());
        }
        transaction.input[input_index].script_sig = push_script_items(&stack)?;
    }
    Ok(())
}

fn multisig_combination_context(
    previous_output: &TxOut,
    input: &TxIn,
) -> Option<MultisigCombinationContext> {
    if previous_output.script_pubkey.is_p2sh() {
        let redeem_script = last_pushed_script(&input.script_sig)?;
        if ScriptBuf::new_p2sh(&redeem_script.script_hash()) != previous_output.script_pubkey {
            return None;
        }
        if redeem_script.is_p2wsh() {
            let witness = input.witness.to_vec();
            let witness_script = ScriptBuf::from_bytes(witness.last()?.clone());
            if ScriptBuf::new_p2wsh(&witness_script.wscript_hash()) != redeem_script {
                return None;
            }
            return Some(MultisigCombinationContext {
                script: witness_script,
                segwit: true,
                redeem_script: Some(redeem_script),
            });
        }
        return Some(MultisigCombinationContext {
            script: redeem_script.clone(),
            segwit: false,
            redeem_script: Some(redeem_script),
        });
    }
    if previous_output.script_pubkey.is_p2wsh() {
        let witness = input.witness.to_vec();
        let witness_script = ScriptBuf::from_bytes(witness.last()?.clone());
        if ScriptBuf::new_p2wsh(&witness_script.wscript_hash()) != previous_output.script_pubkey {
            return None;
        }
        return Some(MultisigCombinationContext {
            script: witness_script,
            segwit: true,
            redeem_script: None,
        });
    }
    Some(MultisigCombinationContext {
        script: previous_output.script_pubkey.clone(),
        segwit: false,
        redeem_script: None,
    })
}

fn last_pushed_script(script: &bitcoin::Script) -> Option<ScriptBuf> {
    script
        .instructions()
        .filter_map(|instruction| match instruction {
            Ok(Instruction::PushBytes(bytes)) => Some(bytes.as_bytes().to_vec()),
            _ => None,
        })
        .last()
        .map(ScriptBuf::from_bytes)
}

fn multisig_signature_items(input: &TxIn, context: &MultisigCombinationContext) -> Vec<Vec<u8>> {
    if context.segwit {
        let witness = input.witness.to_vec();
        if witness.len() < 2 {
            return Vec::new();
        }
        return witness[1..witness.len() - 1].to_vec();
    }
    let mut items = input
        .script_sig
        .instructions()
        .filter_map(|instruction| {
            instruction
                .ok()?
                .push_bytes()
                .map(|bytes| bytes.as_bytes().to_vec())
        })
        .collect::<Vec<_>>();
    if context.redeem_script.is_some() {
        items.pop();
    }
    items
}

fn verify_multisig_signature(
    transaction: &Transaction,
    input_index: usize,
    previous_output: &TxOut,
    context: &MultisigCombinationContext,
    public_key: bitcoin::PublicKey,
    signature_bytes: &[u8],
    secp: &Secp256k1<bitcoin::secp256k1::VerifyOnly>,
) -> bool {
    let Ok(signature) = EcdsaSignature::from_slice(signature_bytes) else {
        return false;
    };
    let message = if context.segwit {
        let sighash = SighashCache::new(transaction).p2wsh_signature_hash(
            input_index,
            &context.script,
            previous_output.value,
            signature.sighash_type,
        );
        let Ok(sighash) = sighash else {
            return false;
        };
        Message::from(sighash)
    } else {
        let sighash = SighashCache::new(transaction).legacy_signature_hash(
            input_index,
            &context.script,
            signature.sighash_type.to_u32(),
        );
        let Ok(sighash) = sighash else {
            return false;
        };
        Message::from(sighash)
    };
    secp.verify_ecdsa(&message, &signature.signature, &public_key.inner)
        .is_ok()
}

fn choose_script_sig(left: &ScriptBuf, right: &ScriptBuf) -> ScriptBuf {
    if left.is_empty() {
        return right.to_owned();
    }
    if right.is_empty() {
        return left.to_owned();
    }
    if let Some(merged) = merge_multisig_script_sigs(left, right) {
        return merged;
    }
    if script_signature_score(right) > script_signature_score(left) {
        right.to_owned()
    } else {
        left.to_owned()
    }
}

fn merge_multisig_script_sigs(left: &ScriptBuf, right: &ScriptBuf) -> Option<ScriptBuf> {
    let left = multisig_script_items(left)?;
    let right = multisig_script_items(right)?;
    if left.1 != right.1 {
        return None;
    }
    let mut signatures = left.0.into_iter().chain(right.0).collect::<Vec<_>>();
    signatures.dedup();
    let mut builder = Builder::new().push_opcode(bitcoin::opcodes::OP_0);
    for signature in signatures {
        builder = builder.push_slice(PushBytesBuf::try_from(signature).ok()?);
    }
    builder = builder.push_slice(PushBytesBuf::try_from(left.1).ok()?);
    Some(builder.into_script())
}

fn multisig_script_items(script: &bitcoin::Script) -> Option<(Vec<Vec<u8>>, Vec<u8>)> {
    let mut instructions = script.instructions();
    match instructions.next()? {
        Ok(Instruction::Op(opcode)) if opcode.to_u8() == 0 => {}
        _ => return None,
    }
    let mut items = instructions
        .map(|instruction| match instruction {
            Ok(Instruction::PushBytes(bytes)) => Some(bytes.as_bytes().to_vec()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    let redeem_script = items.pop()?;
    if items.is_empty() {
        return None;
    }
    Some((items, redeem_script))
}

fn script_signature_score(script: &bitcoin::Script) -> (usize, usize) {
    let pushes = script
        .instructions()
        .filter(|instruction| match instruction {
            Ok(Instruction::PushBytes(_)) => true,
            Ok(Instruction::Op(opcode)) => opcode.to_u8() == 0,
            Err(_) => false,
        })
        .count();
    (pushes, script.len())
}

fn choose_witness(left: &Witness, right: &Witness) -> Witness {
    if let Some(merged) = merge_multisig_witnesses(left, right) {
        return merged;
    }
    let left_score = (left.len(), serialize(left).len());
    let right_score = (right.len(), serialize(right).len());
    if right_score > left_score {
        right.to_owned()
    } else {
        left.to_owned()
    }
}

fn merge_multisig_witnesses(left: &Witness, right: &Witness) -> Option<Witness> {
    let left = left.iter().collect::<Vec<_>>();
    let right = right.iter().collect::<Vec<_>>();
    if left.len() < 3
        || right.len() < 3
        || !left[0].is_empty()
        || !right[0].is_empty()
        || left.last() != right.last()
    {
        return None;
    }
    let mut stack = vec![Vec::new()];
    stack.extend(
        left[1..left.len() - 1]
            .iter()
            .chain(&right[1..right.len() - 1])
            .map(|item| item.to_vec())
            .collect::<Vec<_>>(),
    );
    stack.dedup();
    stack.push(left.last()?.to_vec());
    Some(Witness::from_slice(&stack))
}

fn create_raw_transaction(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let inputs = match params.get(0) {
        Some(Value::Null) => &[][..],
        Some(value) => value
            .as_array()
            .ok_or_else(|| anyhow!("createrawtransaction inputs must be an array"))?,
        None => bail!("createrawtransaction inputs must be an array"),
    };
    let outputs = params
        .get(1)
        .ok_or_else(|| anyhow!("createrawtransaction outputs are missing"))?;
    let lock_time = u32::try_from(optional_u64(params, 2, 0, "locktime")?)
        .map(LockTime::from_consensus)
        .map_err(|_| anyhow!("locktime is out of range"))?;
    let replaceable = params
        .get(3)
        .filter(|value| !value.is_null())
        .map(|value| {
            value
                .as_bool()
                .ok_or_else(|| anyhow!("replaceable must be a boolean"))
        })
        .transpose()?
        .unwrap_or(true);
    let version = match params.get(4).filter(|value| !value.is_null()) {
        Some(value) => {
            let version = value
                .as_u64()
                .ok_or_else(|| anyhow!("transaction version must be an unsigned integer"))?;
            if !(1..=3).contains(&version) {
                bail!("transaction version is out of range (1~3)")
            }
            Version::non_standard(i32::try_from(version).expect("version is at most three"))
        }
        None => Version::TWO,
    };
    let default_sequence = if replaceable {
        0xffff_fffd
    } else if lock_time != LockTime::ZERO {
        0xffff_fffe
    } else {
        u32::MAX
    };
    let transaction_inputs = inputs
        .iter()
        .map(|value| {
            let txid: Txid = value
                .get("txid")
                .and_then(Value::as_str)
                .ok_or_else(|| anyhow!("transaction input txid is missing"))?
                .parse()?;
            let vout_value = value
                .get("vout")
                .ok_or_else(|| anyhow!("transaction input vout is missing"))?;
            if vout_value.as_i64().is_some_and(|vout| vout < 0) {
                bail!("Invalid parameter, vout cannot be negative")
            }
            let vout = vout_value
                .as_u64()
                .ok_or_else(|| anyhow!("transaction input vout is missing"))?;
            let vout = u32::try_from(vout)
                .map_err(|_| anyhow!("transaction input vout is out of range"))?;
            let sequence = match value.get("sequence").filter(|value| !value.is_null()) {
                Some(value) => {
                    if value.as_i64().is_some_and(|sequence| sequence < 0) {
                        bail!("Invalid parameter, sequence number is out of range")
                    }
                    let sequence = value
                        .as_u64()
                        .ok_or_else(|| anyhow!("transaction input sequence must be an integer"))?;
                    u32::try_from(sequence)
                        .map_err(|_| anyhow!("transaction input sequence is out of range"))?
                }
                None => default_sequence,
            };
            Ok(TxIn {
                previous_output: OutPoint::new(txid, vout),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::from_consensus(sequence),
                witness: Witness::default(),
            })
        })
        .collect::<Result<Vec<_>>>()?;
    if replaceable
        && !transaction_inputs.is_empty()
        && transaction_inputs
            .iter()
            .all(|input| input.sequence.to_consensus_u32() > 0xffff_fffd)
    {
        bail!("Invalid parameter combination: Sequence number(s) contradict replaceable option")
    }
    let transaction_outputs = create_transaction_outputs(node, outputs)?;
    let transaction = Transaction {
        version,
        lock_time,
        input: transaction_inputs,
        output: transaction_outputs,
    };
    Ok(json!(hex::encode(serialize(&transaction))))
}

fn create_transaction_outputs(node: &Arc<Node>, outputs: &Value) -> Result<Vec<TxOut>> {
    let entries = if let Some(object) = outputs.as_object() {
        object.iter().collect::<Vec<_>>()
    } else if let Some(array) = outputs.as_array() {
        array
            .iter()
            .map(|value| {
                let object = value
                    .as_object()
                    .ok_or_else(|| anyhow!("transaction output must be an object"))?;
                if object.len() != 1 {
                    bail!("transaction output object must contain one entry")
                }
                Ok(object.iter().next().expect("one output entry"))
            })
            .collect::<Result<Vec<_>>>()?
    } else {
        bail!("transaction outputs must be an object or array")
    };
    let mut seen_scripts = HashSet::new();
    let mut seen_data = false;
    entries
        .into_iter()
        .map(|(destination, value)| {
            if destination == "data" {
                if seen_data {
                    bail!("Invalid parameter, duplicate key: data")
                }
                seen_data = true;
                let data = value
                    .as_str()
                    .ok_or_else(|| anyhow!("data output must be hexadecimal"))?;
                let data = hex::decode(data)?;
                let data = PushBytesBuf::try_from(data)
                    .map_err(|_| anyhow!("data output is too large"))?;
                return Ok(TxOut {
                    value: Amount::ZERO,
                    script_pubkey: Builder::new()
                        .push_opcode(OP_RETURN)
                        .push_slice(data)
                        .into_script(),
                });
            }
            let address = destination
                .parse::<Address<bitcoin::address::NetworkUnchecked>>()?
                .require_network(node.config.network)?;
            let amount = parse_btc_amount(value, "transaction output amount")?;
            if amount > Amount::MAX_MONEY {
                bail!("transaction output amount exceeds MAX_MONEY")
            }
            let script_pubkey = address.script_pubkey();
            if !seen_scripts.insert(script_pubkey.as_bytes().to_vec()) {
                bail!("Invalid parameter, duplicated address: {destination}")
            }
            Ok(TxOut {
                value: amount,
                script_pubkey,
            })
        })
        .collect()
}

fn parse_btc_amount(value: &Value, field: &str) -> Result<Amount> {
    let text = match value {
        Value::Number(number) => number.to_string(),
        Value::String(string) => string.clone(),
        _ => bail!("{field} must be a number or string"),
    };
    let text =
        expand_decimal_exponent(&text).map_err(|error| anyhow!("invalid {field}: {error}"))?;
    Amount::from_str_in(&text, Denomination::Bitcoin)
        .map_err(|error| anyhow!("invalid {field}: {error}"))
}

fn expand_decimal_exponent(value: &str) -> Result<String> {
    if value.len() > 64 {
        bail!("amount is out of range")
    }
    let Some(exponent_offset) = value.find(['e', 'E']) else {
        return Ok(value.to_owned());
    };
    let (mantissa, exponent) = value.split_at(exponent_offset);
    let exponent = exponent[1..]
        .parse::<i64>()
        .map_err(|_| anyhow!("invalid exponent"))?;
    let (negative, mantissa) = mantissa
        .strip_prefix('-')
        .map_or((false, mantissa), |mantissa| (true, mantissa));
    let (whole, fraction) = mantissa
        .split_once('.')
        .map_or((mantissa, ""), |(whole, fraction)| (whole, fraction));
    if whole.is_empty()
        || !whole.bytes().all(|byte| byte.is_ascii_digit())
        || !fraction.bytes().all(|byte| byte.is_ascii_digit())
        || (mantissa.contains('.') && fraction.is_empty())
    {
        bail!("invalid decimal number")
    }
    let digits = format!("{whole}{fraction}");
    let decimal_position = i64::try_from(whole.len())
        .ok()
        .and_then(|position| position.checked_add(exponent))
        .ok_or_else(|| anyhow!("exponent is out of range"))?;
    let expanded = if decimal_position <= 0 {
        let leading_zeroes = usize::try_from(decimal_position.unsigned_abs())
            .map_err(|_| anyhow!("exponent is out of range"))?;
        if leading_zeroes > 64 {
            bail!("amount is out of range")
        }
        format!("0.{}{}", "0".repeat(leading_zeroes), digits)
    } else if decimal_position >= i64::try_from(digits.len()).unwrap_or(i64::MAX) {
        let trailing_zeroes =
            usize::try_from(decimal_position - i64::try_from(digits.len()).unwrap_or(i64::MAX))
                .map_err(|_| anyhow!("exponent is out of range"))?;
        if trailing_zeroes > 64 {
            bail!("amount is out of range")
        }
        format!("{}{}", digits, "0".repeat(trailing_zeroes))
    } else {
        let split =
            usize::try_from(decimal_position).map_err(|_| anyhow!("exponent is out of range"))?;
        format!("{}.{}", &digits[..split], &digits[split..])
    };
    Ok(if negative {
        format!("-{expanded}")
    } else {
        expanded
    })
}

fn script_push_num(opcode: u8) -> Option<u8> {
    match opcode {
        0x00 => Some(0),
        0x51..=0x60 => Some(opcode - 0x50),
        _ => None,
    }
}

fn multisig_descriptor_body(script: &bitcoin::Script) -> Option<String> {
    if !script.is_multisig() {
        return None;
    }
    let mut instructions = script.instructions();
    let required = match instructions.next()? {
        Ok(Instruction::Op(op)) => script_push_num(op.to_u8())?,
        _ => return None,
    };
    if required == 0 {
        return None;
    }
    let mut keys = Vec::new();
    loop {
        match instructions.next()? {
            Ok(Instruction::PushBytes(bytes)) => {
                let public_key = bitcoin::PublicKey::from_slice(bytes.as_bytes()).ok()?;
                keys.push(public_key.to_string());
            }
            Ok(Instruction::Op(op)) => {
                let key_count = script_push_num(op.to_u8())?;
                let parsed_key_count = u8::try_from(keys.len()).ok()?;
                if key_count != parsed_key_count || required > key_count {
                    return None;
                }
                match instructions.next()? {
                    Ok(Instruction::Op(check))
                        if check == bitcoin::blockdata::opcodes::all::OP_CHECKMULTISIG => {}
                    _ => return None,
                }
                if instructions.next().is_some() {
                    return None;
                }
                return Some(format!("multi({required},{})", keys.join(",")));
            }
            Err(_) => return None,
        }
    }
}

fn is_core_nulldata(script: &bitcoin::Script) -> bool {
    script.as_bytes().first() == Some(&OP_RETURN.to_u8())
        && bitcoin::Script::from_bytes(&script.as_bytes()[1..]).is_push_only()
}

fn script_has_op_success_or_checksigadd(script: &bitcoin::Script) -> bool {
    script.instructions().any(|instruction| {
        let Ok(Instruction::Op(op)) = instruction else {
            return false;
        };
        let opcode = op.to_u8();
        opcode == 0xba
            || matches!(
                opcode,
                0x50
                    | 0x62
                    | 0x7e..=0x81
                    | 0x83..=0x86
                    | 0x89..=0x8a
                    | 0x8d..=0x8e
                    | 0x95..=0x99
                    | 0xbb..=0xfe
            )
    })
}

fn is_p2a_script(script: &bitcoin::Script) -> bool {
    script.as_bytes() == [0x51, 0x02, 0x4e, 0x73]
}

fn script_type_for_decode(script: &bitcoin::Script) -> &'static str {
    if script.is_p2pkh() {
        "pubkeyhash"
    } else if script.is_p2sh() {
        "scripthash"
    } else if script.is_p2wpkh() {
        "witness_v0_keyhash"
    } else if script.is_p2wsh() {
        "witness_v0_scripthash"
    } else if script.is_p2tr() {
        "witness_v1_taproot"
    } else if is_p2a_script(script) {
        "anchor"
    } else if script
        .witness_version()
        .is_some_and(|version| version.to_num() != 0)
    {
        "witness_unknown"
    } else if is_core_nulldata(script) {
        "nulldata"
    } else if script.is_p2pk() {
        "pubkey"
    } else if script.is_multisig() {
        "multisig"
    } else {
        "nonstandard"
    }
}

fn descriptor_with_checksum(body: &str) -> String {
    format!("{body}#{}", descriptor_checksum(body).unwrap_or_default())
}

fn inferred_script_descriptor_for_network(network: Network, script: &bitcoin::Script) -> String {
    let body = if script.is_p2tr() {
        script
            .as_bytes()
            .get(2..)
            .and_then(|bytes| bitcoin::XOnlyPublicKey::from_slice(bytes).ok())
            .map(|key| format!("rawtr({key})"))
            .unwrap_or_else(|| format!("raw({})", hex::encode(script.as_bytes())))
    } else if let Some(public_key) = script.p2pk_public_key() {
        format!("pk({public_key})")
    } else if let Some(multisig) = multisig_descriptor_body(script) {
        multisig
    } else if let Ok(address) = Address::from_script(script, network) {
        format!("addr({address})")
    } else {
        format!("raw({})", hex::encode(script.as_bytes()))
    };
    descriptor_with_checksum(&body)
}

fn inferred_script_descriptor(node: &Arc<Node>, script: &bitcoin::Script) -> String {
    inferred_script_descriptor_for_network(node.config.network, script)
}

fn decoded_script_json(node: &Arc<Node>, script: &bitcoin::Script, include_hex: bool) -> Value {
    let script_type = script_type_for_decode(script);
    let mut result = json!({
        "asm": script.to_asm_string(),
        "desc": inferred_script_descriptor(node, script),
        "type": script_type,
    });
    if include_hex {
        result["hex"] = json!(hex::encode(script.as_bytes()));
    }
    if script_type != "pubkey"
        && let Ok(address) = Address::from_script(script, node.config.network)
    {
        result["address"] = json!(address.to_string());
    }
    result
}

fn segwit_wrapper_script(script: &bitcoin::Script, script_type: &str) -> Option<ScriptBuf> {
    match script_type {
        "pubkey" => {
            let public_key = script.p2pk_public_key()?;
            let compressed = bitcoin::CompressedPublicKey::try_from(public_key).ok()?;
            Some(Address::p2wpkh(&compressed, Network::Bitcoin).script_pubkey())
        }
        "pubkeyhash" => {
            let hash = script.as_bytes().get(3..23)?;
            let mut bytes = Vec::with_capacity(22);
            bytes.extend_from_slice(&[0x00, 0x14]);
            bytes.extend_from_slice(hash);
            Some(ScriptBuf::from_bytes(bytes))
        }
        _ => Some(script.to_p2wsh()),
    }
}

fn decode_script(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let bytes = hex::decode(param::<String>(params, 0)?)?;
    let script = ScriptBuf::from_bytes(bytes);
    let script_ref = script.as_script();
    let script_type = script_type_for_decode(script_ref);
    let mut result = decoded_script_json(node, script_ref, false);
    let can_wrap = matches!(
        script_type,
        "multisig"
            | "nonstandard"
            | "pubkey"
            | "pubkeyhash"
            | "witness_v0_keyhash"
            | "witness_v0_scripthash"
    ) && script_has_valid_ops(script_ref)
        && !script_is_unspendable(script_ref)
        && !script_has_op_success_or_checksigadd(script_ref);
    if can_wrap {
        result["p2sh"] = json!(Address::p2sh(script_ref, node.config.network)?.to_string());
        let can_wrap_p2wsh = matches!(script_type, "multisig" | "nonstandard" | "pubkeyhash")
            || (script_type == "pubkey"
                && script_ref
                    .p2pk_public_key()
                    .is_some_and(|public_key| public_key.compressed));
        if can_wrap_p2wsh
            && let Some(segwit_script) = segwit_wrapper_script(script_ref, script_type)
        {
            let segwit_ref = segwit_script.as_script();
            let mut segwit = decoded_script_json(node, segwit_ref, true);
            segwit["p2sh-segwit"] =
                json!(Address::p2sh(segwit_ref, node.config.network)?.to_string());
            result["segwit"] = segwit;
        }
    }
    Ok(result)
}

fn parse_psbt(params: &Value, index: usize) -> Result<Psbt> {
    let encoded = param::<String>(params, index)?;
    let bytes = base64::engine::general_purpose::STANDARD.decode(encoded)?;
    Ok(Psbt::deserialize(&bytes)?)
}

fn encode_psbt(psbt: &Psbt) -> String {
    base64::engine::general_purpose::STANDARD.encode(psbt.serialize())
}

fn create_psbt(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let raw = create_raw_transaction(node, params)?;
    let transaction: Transaction =
        deserialize(&hex::decode(raw.as_str().ok_or_else(|| {
            anyhow!("createrawtransaction did not return hexadecimal data")
        })?)?)?;
    Ok(json!(encode_psbt(&Psbt::from_unsigned_tx(transaction)?)))
}

fn convert_to_psbt(params: &Value) -> Result<Value> {
    let transaction = decode_transaction_from_params(params, 0, 2)?;
    let permitsigdata = params
        .get(1)
        .filter(|value| !value.is_null())
        .map(|value| {
            value
                .as_bool()
                .ok_or_else(|| anyhow!("permitsigdata must be a boolean"))
        })
        .transpose()?
        .unwrap_or(false);
    let has_signature_data = transaction
        .input
        .iter()
        .any(|input| !input.script_sig.is_empty() || !input.witness.is_empty());
    if has_signature_data && !permitsigdata {
        bail!("transaction contains signature data; set permitsigdata to true")
    }
    let mut unsigned = transaction.clone();
    for input in &mut unsigned.input {
        input.script_sig = ScriptBuf::new();
        input.witness = Witness::default();
    }
    let psbt = Psbt::from_unsigned_tx(unsigned)?;
    Ok(json!(encode_psbt(&psbt)))
}

fn psbt_script_json(node: &Arc<Node>, script: &bitcoin::Script) -> Value {
    script_json_with_network(script, Some(node.config.network))
}

fn psbt_inner_script_json(script: &bitcoin::Script) -> Value {
    script_json_with_network(script, None)
}

fn psbt_unknown_json(
    values: &std::collections::BTreeMap<bitcoin::psbt::raw::Key, Vec<u8>>,
) -> Value {
    Value::Object(
        values
            .iter()
            .map(|(key, value)| {
                (
                    format!("{:02x}{}", key.type_value, hex::encode(&key.key)),
                    json!(hex::encode(value)),
                )
            })
            .collect(),
    )
}

fn psbt_proprietary_json(
    values: &std::collections::BTreeMap<bitcoin::psbt::raw::ProprietaryKey, Vec<u8>>,
) -> Value {
    Value::Array(
        values
            .iter()
            .map(|(key, value)| {
                json!({
                    "identifier": hex::encode(&key.prefix),
                    "subtype": key.subtype,
                    "key": hex::encode(&key.key),
                    "value": hex::encode(value),
                })
            })
            .collect(),
    )
}

fn psbt_path(path: &bitcoin::bip32::DerivationPath) -> String {
    let path = path.to_string();
    if path.is_empty() {
        "m".to_owned()
    } else {
        format!("m/{path}")
    }
}

fn psbt_taproot_derivs_json(
    values: &std::collections::BTreeMap<
        bitcoin::XOnlyPublicKey,
        (Vec<bitcoin::TapLeafHash>, bitcoin::bip32::KeySource),
    >,
) -> Value {
    Value::Array(
        values
            .iter()
            .map(|(public_key, (leaf_hashes, source))| {
                json!({
                    "pubkey": public_key.to_string(),
                    "master_fingerprint": source.0.to_string(),
                    "path": psbt_path(&source.1),
                    "leaf_hashes": leaf_hashes.iter().map(ToString::to_string).collect::<Vec<_>>(),
                })
            })
            .collect(),
    )
}

fn psbt_taproot_tree_json(tree: &bitcoin::taproot::TapTree) -> Value {
    Value::Array(
        tree.script_leaves()
            .map(|leaf| {
                json!({
                    "depth": leaf.merkle_branch().len(),
                    "leaf_ver": leaf.version().to_consensus(),
                    "script": hex::encode(leaf.script().as_bytes()),
                })
            })
            .collect(),
    )
}

fn psbt_taproot_scripts_json(
    values: &std::collections::BTreeMap<
        bitcoin::taproot::ControlBlock,
        (ScriptBuf, bitcoin::taproot::LeafVersion),
    >,
) -> Value {
    let mut grouped = std::collections::BTreeMap::<(Vec<u8>, u8), Vec<String>>::new();
    for (control_block, (script, leaf_version)) in values {
        grouped
            .entry((script.as_bytes().to_vec(), leaf_version.to_consensus()))
            .or_default()
            .push(hex::encode(control_block.serialize()));
    }
    Value::Array(
        grouped
            .into_iter()
            .map(|((script, leaf_version), control_blocks)| {
                json!({
                    "script": hex::encode(script),
                    "leaf_ver": leaf_version,
                    "control_blocks": control_blocks,
                })
            })
            .collect(),
    )
}

fn decode_psbt_input(node: &Arc<Node>, input: &PsbtInput) -> Value {
    let mut result = json!({});
    if let Some(transaction) = &input.non_witness_utxo {
        result["non_witness_utxo"] = decoded_transaction_json(transaction, node.config.network);
    }
    if let Some(output) = &input.witness_utxo {
        result["witness_utxo"] = json!({
            "amount": sat_to_btc(output.value.to_sat()),
            "scriptPubKey": psbt_script_json(node, &output.script_pubkey),
        });
    }
    if !input.partial_sigs.is_empty() {
        result["partial_signatures"] = Value::Object(
            input
                .partial_sigs
                .iter()
                .map(|(public_key, signature)| {
                    (
                        public_key.to_string(),
                        json!(hex::encode(signature.to_vec())),
                    )
                })
                .collect(),
        );
    }
    if let Some(sighash_type) = input.sighash_type {
        result["sighash"] = json!(sighash_type.to_string());
    }
    if let Some(script) = &input.redeem_script {
        result["redeem_script"] = psbt_inner_script_json(script.as_script());
    }
    if let Some(script) = &input.witness_script {
        result["witness_script"] = psbt_inner_script_json(script.as_script());
    }
    if !input.bip32_derivation.is_empty() {
        result["bip32_derivs"] = json!(
            input
                .bip32_derivation
                .iter()
                .map(|(public_key, source)| {
                    json!({
                        "pubkey": public_key.to_string(),
                        "master_fingerprint": source.0.to_string(),
                        "path": psbt_path(&source.1),
                    })
                })
                .collect::<Vec<_>>()
        );
    }
    if let Some(script) = &input.final_script_sig {
        result["final_scriptSig"] = json!({
            "asm": script.to_asm_string(),
            "hex": hex::encode(script.as_bytes()),
        });
    }
    if let Some(witness) = &input.final_script_witness {
        result["final_scriptwitness"] = json!(
            witness
                .to_vec()
                .into_iter()
                .map(hex::encode)
                .collect::<Vec<_>>()
        );
    }
    if !input.ripemd160_preimages.is_empty() {
        result["ripemd160_preimages"] = Value::Object(
            input
                .ripemd160_preimages
                .iter()
                .map(|(hash, preimage)| (hash.to_string(), json!(hex::encode(preimage))))
                .collect(),
        );
    }
    if !input.sha256_preimages.is_empty() {
        result["sha256_preimages"] = Value::Object(
            input
                .sha256_preimages
                .iter()
                .map(|(hash, preimage)| (hash.to_string(), json!(hex::encode(preimage))))
                .collect(),
        );
    }
    if !input.hash160_preimages.is_empty() {
        result["hash160_preimages"] = Value::Object(
            input
                .hash160_preimages
                .iter()
                .map(|(hash, preimage)| (hash.to_string(), json!(hex::encode(preimage))))
                .collect(),
        );
    }
    if !input.hash256_preimages.is_empty() {
        result["hash256_preimages"] = Value::Object(
            input
                .hash256_preimages
                .iter()
                .map(|(hash, preimage)| (hash.to_string(), json!(hex::encode(preimage))))
                .collect(),
        );
    }
    if let Some(signature) = &input.tap_key_sig {
        result["taproot_key_path_sig"] = json!(hex::encode(signature.to_vec()));
    }
    if !input.tap_script_sigs.is_empty() {
        result["taproot_script_path_sigs"] = Value::Array(
            input
                .tap_script_sigs
                .iter()
                .map(|((public_key, leaf_hash), signature)| {
                    json!({
                        "pubkey": public_key.to_string(),
                        "leaf_hash": leaf_hash.to_string(),
                        "sig": hex::encode(signature.to_vec()),
                    })
                })
                .collect(),
        );
    }
    if !input.tap_scripts.is_empty() {
        result["taproot_scripts"] = psbt_taproot_scripts_json(&input.tap_scripts);
    }
    if !input.tap_key_origins.is_empty() {
        result["taproot_bip32_derivs"] = psbt_taproot_derivs_json(&input.tap_key_origins);
    }
    if input.tap_internal_key.is_some() {
        result["taproot_internal_key"] = json!(input.tap_internal_key.map(|key| key.to_string()));
    }
    if input.tap_merkle_root.is_some() {
        result["taproot_merkle_root"] = json!(input.tap_merkle_root.map(|root| root.to_string()));
    }
    if !input.proprietary.is_empty() {
        result["proprietary"] = psbt_proprietary_json(&input.proprietary);
    }
    if !input.unknown.is_empty() {
        result["unknown"] = psbt_unknown_json(&input.unknown);
    }
    result
}

fn decode_psbt_output(_node: &Arc<Node>, output: &bitcoin::psbt::Output) -> Value {
    let mut result = json!({});
    if let Some(script) = &output.redeem_script {
        result["redeem_script"] = psbt_inner_script_json(script.as_script());
    }
    if let Some(script) = &output.witness_script {
        result["witness_script"] = psbt_inner_script_json(script.as_script());
    }
    if !output.bip32_derivation.is_empty() {
        result["bip32_derivs"] = json!(
            output
                .bip32_derivation
                .iter()
                .map(|(public_key, source)| {
                    json!({
                        "pubkey": public_key.to_string(),
                        "master_fingerprint": source.0.to_string(),
                        "path": psbt_path(&source.1),
                    })
                })
                .collect::<Vec<_>>()
        );
    }
    if output.tap_internal_key.is_some() {
        result["taproot_internal_key"] = json!(output.tap_internal_key.map(|key| key.to_string()));
    }
    if let Some(tree) = &output.tap_tree {
        result["taproot_tree"] = psbt_taproot_tree_json(tree);
    }
    if !output.tap_key_origins.is_empty() {
        result["taproot_bip32_derivs"] = psbt_taproot_derivs_json(&output.tap_key_origins);
    }
    if !output.proprietary.is_empty() {
        result["proprietary"] = psbt_proprietary_json(&output.proprietary);
    }
    if !output.unknown.is_empty() {
        result["unknown"] = psbt_unknown_json(&output.unknown);
    }
    result
}

fn decode_psbt(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let psbt = parse_psbt(params, 0)?;
    let mut result = json!({
        "tx": decoded_transaction_json(&psbt.unsigned_tx, node.config.network),
        "global_xpubs": psbt.xpub.iter().map(|(xpub, source)| json!({
            "xpub": xpub.to_string(),
            "master_fingerprint": source.0.to_string(),
            "path": psbt_path(&source.1),
        })).collect::<Vec<_>>(),
        "psbt_version": psbt.version,
        "proprietary": psbt_proprietary_json(&psbt.proprietary),
        "unknown": psbt_unknown_json(&psbt.unknown),
        "inputs": psbt.inputs.iter().map(|input| decode_psbt_input(node, input)).collect::<Vec<_>>(),
        "outputs": psbt.outputs.iter().map(|output| decode_psbt_output(node, output)).collect::<Vec<_>>(),
    });
    let mut total_in = 0u64;
    let mut have_all_utxos = true;
    for input_index in 0..psbt.inputs.len() {
        let Some(prevout) = psbt_prevout(&psbt, input_index) else {
            have_all_utxos = false;
            continue;
        };
        let Some(next_total) = total_in.checked_add(prevout.value.to_sat()) else {
            have_all_utxos = false;
            continue;
        };
        total_in = next_total;
    }
    let total_out = psbt
        .unsigned_tx
        .output
        .iter()
        .map(|output| output.value.to_sat())
        .try_fold(0u64, u64::checked_add);
    if have_all_utxos
        && let Some(total_out) = total_out
        && let (Ok(total_in), Ok(total_out)) = (i64::try_from(total_in), i64::try_from(total_out))
    {
        result["fee"] = json!(sat_to_btc_signed(total_in - total_out));
    }
    Ok(result)
}

fn combine_psbt(params: &Value) -> Result<Value> {
    let values = params
        .get(0)
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("combinepsbt expects an array of PSBTs"))?;
    let mut iter = values.iter();
    let first = iter
        .next()
        .ok_or_else(|| anyhow!("combinepsbt requires at least one PSBT"))?;
    let first = first
        .as_str()
        .ok_or_else(|| anyhow!("PSBT values must be base64 strings"))?;
    let mut combined =
        Psbt::deserialize(&base64::engine::general_purpose::STANDARD.decode(first)?)?;
    for value in iter {
        let encoded = value
            .as_str()
            .ok_or_else(|| anyhow!("PSBT values must be base64 strings"))?;
        let other = Psbt::deserialize(&base64::engine::general_purpose::STANDARD.decode(encoded)?)?;
        combined.combine(other)?;
    }
    Ok(json!(encode_psbt(&combined)))
}

fn join_psbts(params: &Value) -> Result<Value> {
    let values = params
        .get(0)
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("joinpsbts expects an array of PSBTs"))?;
    if values.is_empty() {
        bail!("joinpsbts requires at least one PSBT")
    }
    let psbts = values
        .iter()
        .map(|value| {
            let encoded = value
                .as_str()
                .ok_or_else(|| anyhow!("PSBT values must be base64 strings"))?;
            Ok(Psbt::deserialize(
                &base64::engine::general_purpose::STANDARD.decode(encoded)?,
            )?)
        })
        .collect::<Result<Vec<_>>>()?;
    let version = psbts[0].unsigned_tx.version;
    let lock_time = psbts[0].unsigned_tx.lock_time;
    let mut input_outpoints = HashSet::new();
    let mut output_bytes = HashSet::new();
    let mut inputs = Vec::new();
    let mut outputs = Vec::new();
    for psbt in &psbts {
        if psbt.unsigned_tx.version != version || psbt.unsigned_tx.lock_time != lock_time {
            bail!("PSBTs must use the same transaction version and locktime")
        }
        for (index, input) in psbt.unsigned_tx.input.iter().enumerate() {
            if !input_outpoints.insert(input.previous_output) {
                bail!("PSBTs contain duplicate inputs")
            }
            inputs.push((input.clone(), psbt.inputs[index].clone()));
        }
        for (index, output) in psbt.unsigned_tx.output.iter().enumerate() {
            if !output_bytes.insert(serialize(output)) {
                bail!("PSBTs contain duplicate outputs")
            }
            outputs.push((output.clone(), psbt.outputs[index].clone()));
        }
    }
    let transaction = Transaction {
        version,
        lock_time,
        input: inputs.iter().map(|(input, _)| input.clone()).collect(),
        output: outputs.iter().map(|(output, _)| output.clone()).collect(),
    };
    let mut joined = Psbt::from_unsigned_tx(transaction)?;
    for psbt in psbts {
        joined.version = joined.version.max(psbt.version);
        joined.xpub.extend(psbt.xpub);
        joined.proprietary.extend(psbt.proprietary);
        joined.unknown.extend(psbt.unknown);
    }
    joined.inputs = inputs.into_iter().map(|(_, input)| input).collect();
    joined.outputs = outputs.into_iter().map(|(_, output)| output).collect();
    Ok(json!(encode_psbt(&joined)))
}

fn analyze_psbt(params: &Value) -> Result<Value> {
    let psbt = parse_psbt(params, 0)?;
    let mut all_final = true;
    let mut missing_utxo = false;
    let mut needs_updater = false;
    let mut needs_signer = false;
    let mut needs_finalizer = false;
    let mut inputs = Vec::with_capacity(psbt.inputs.len());
    for (index, input) in psbt.inputs.iter().enumerate() {
        let has_utxo = psbt_prevout(&psbt, index).is_some();
        let is_final = input.final_script_sig.is_some() || input.final_script_witness.is_some();
        all_final &= is_final;
        missing_utxo |= !has_utxo;

        let missing = if let Some(prevout) = psbt_prevout(&psbt, index) {
            psbt_missing_info(input, &prevout)
        } else {
            PsbtMissingInfo::default()
        };
        let next = if !has_utxo || !is_final && (!missing.recognized || missing.needs_updater()) {
            needs_updater = true;
            "updater"
        } else if !is_final && !missing.missing_sigs.is_empty() {
            needs_signer = true;
            "signer"
        } else if !is_final {
            needs_finalizer = true;
            "finalizer"
        } else {
            "extractor"
        };

        let mut input_result = json!({
            "has_utxo": has_utxo,
            "is_final": is_final,
            "next": next,
        });
        if let Some(missing_json) = missing.as_json() {
            input_result["missing"] = missing_json;
        }
        inputs.push(input_result);
    }
    let estimated_vsize = if all_final {
        psbt.clone().extract_tx_unchecked_fee_rate().vsize()
    } else {
        psbt.unsigned_tx.vsize()
    };
    let mut result = json!({
        "inputs": inputs,
        "estimated_vsize": estimated_vsize,
        "next": if missing_utxo || needs_updater {
            "updater"
        } else if needs_signer {
            "signer"
        } else if needs_finalizer {
            "finalizer"
        } else if all_final {
            "extractor"
        } else {
            "updater"
        },
    });
    if let Ok(fee) = psbt.fee() {
        result["fee"] = json!(sat_to_btc(fee.to_sat()));
        if estimated_vsize > 0 {
            result["estimated_feerate"] = json!(sat_to_btc(
                fee.to_sat().saturating_mul(1000) / estimated_vsize as u64
            ));
        }
    }
    Ok(result)
}

#[derive(Default)]
struct PsbtMissingInfo {
    recognized: bool,
    missing_pubkeys: Vec<String>,
    missing_sigs: Vec<String>,
    missing_redeem_script: Option<String>,
    missing_witness_script: Option<String>,
}

impl PsbtMissingInfo {
    fn needs_updater(&self) -> bool {
        !self.missing_pubkeys.is_empty()
            || self.missing_redeem_script.is_some()
            || self.missing_witness_script.is_some()
    }

    fn as_json(&self) -> Option<Value> {
        let mut missing = serde_json::Map::new();
        if !self.missing_pubkeys.is_empty() {
            missing.insert("pubkeys".to_owned(), json!(self.missing_pubkeys));
        }
        if !self.missing_sigs.is_empty() {
            missing.insert("signatures".to_owned(), json!(self.missing_sigs));
        }
        if let Some(redeem_script) = &self.missing_redeem_script {
            missing.insert("redeemscript".to_owned(), json!(redeem_script));
        }
        if let Some(witness_script) = &self.missing_witness_script {
            missing.insert("witnessscript".to_owned(), json!(witness_script));
        }
        (!missing.is_empty()).then_some(Value::Object(missing))
    }
}

fn public_key_id_hex(public_key: &bitcoin::PublicKey) -> String {
    hex::encode(public_key.pubkey_hash().to_byte_array())
}

fn p2pkh_script_from_hash(hash: &[u8]) -> Option<ScriptBuf> {
    (hash.len() == 20).then(|| {
        let mut bytes = Vec::with_capacity(25);
        bytes.extend_from_slice(&[0x76, 0xa9, 0x14]);
        bytes.extend_from_slice(hash);
        bytes.extend_from_slice(&[0x88, 0xac]);
        ScriptBuf::from_bytes(bytes)
    })
}

fn psbt_missing_info(input: &PsbtInput, prevout: &TxOut) -> PsbtMissingInfo {
    let mut missing = PsbtMissingInfo::default();
    let mut script = prevout.script_pubkey.clone();

    if script.is_p2sh() {
        let Some(redeem_script) = input.redeem_script.as_ref() else {
            if let Some(hash) = script.as_bytes().get(2..22) {
                missing.missing_redeem_script = Some(hex::encode(hash));
            }
            return missing;
        };
        script = redeem_script.clone();
    }

    if script.is_p2wsh() {
        let Some(witness_script) = input.witness_script.as_ref() else {
            if let Some(hash) = script.as_bytes().get(2..34) {
                missing.missing_witness_script = Some(hex::encode(hash));
            }
            return missing;
        };
        script = witness_script.clone();
    } else if script.is_p2wpkh() {
        if let Some(hash) = script.as_bytes().get(2..22) {
            let Some(inner) = p2pkh_script_from_hash(hash) else {
                return missing;
            };
            script = inner;
        }
    }

    if script.is_p2pkh() {
        missing.recognized = true;
        let Some(hash) = script.as_bytes().get(3..23) else {
            return missing;
        };
        if !input
            .partial_sigs
            .keys()
            .any(|public_key| public_key.pubkey_hash().to_byte_array() == hash)
        {
            missing.missing_pubkeys.push(hex::encode(hash));
        }
    } else if let Some(public_key) = script.p2pk_public_key() {
        missing.recognized = true;
        if !input.partial_sigs.contains_key(&public_key) {
            missing.missing_sigs.push(public_key_id_hex(&public_key));
        }
    } else if let Some((_, public_keys)) = multisig_script_keys(script.as_script()) {
        missing.recognized = true;
        for public_key in public_keys {
            if !input.partial_sigs.contains_key(&public_key) {
                missing.missing_sigs.push(public_key_id_hex(&public_key));
            }
        }
    }
    missing
}

fn psbt_prevout(psbt: &Psbt, input_index: usize) -> Option<TxOut> {
    let input = psbt.inputs.get(input_index)?;
    if let Some(output) = &input.witness_utxo {
        return Some(output.clone());
    }
    let transaction_input = psbt.unsigned_tx.input.get(input_index)?;
    input
        .non_witness_utxo
        .as_ref()?
        .output
        .get(transaction_input.previous_output.vout as usize)
        .cloned()
}

fn push_script_items(items: &[Vec<u8>]) -> Result<ScriptBuf> {
    let mut builder = Builder::new();
    for item in items {
        let item = PushBytesBuf::try_from(item.clone())
            .map_err(|_| anyhow!("script item is too large"))?;
        builder = builder.push_slice(item);
    }
    Ok(builder.into_script())
}

fn public_key_matches_script(public_key: &bitcoin::PublicKey, script: &bitcoin::Script) -> bool {
    if script.is_p2pkh() {
        Address::p2pkh(*public_key, Network::Bitcoin)
            .script_pubkey()
            .as_script()
            == script
            || Address::p2pkh(*public_key, Network::Testnet)
                .script_pubkey()
                .as_script()
                == script
    } else if script.is_p2wpkh() {
        bitcoin::CompressedPublicKey::try_from(*public_key).is_ok_and(|public_key| {
            Address::p2wpkh(&public_key, Network::Bitcoin)
                .script_pubkey()
                .as_script()
                == script
                || Address::p2wpkh(&public_key, Network::Testnet)
                    .script_pubkey()
                    .as_script()
                    == script
        })
    } else if script.is_p2pk() {
        Builder::new()
            .push_key(public_key)
            .push_opcode(bitcoin::blockdata::opcodes::all::OP_CHECKSIG)
            .into_script()
            .as_script()
            == script
    } else {
        false
    }
}

fn multisig_script_keys(script: &bitcoin::Script) -> Option<(usize, Vec<bitcoin::PublicKey>)> {
    let instructions = script
        .instructions()
        .collect::<std::result::Result<Vec<_>, _>>()
        .ok()?;
    if instructions.len() < 4
        || instructions.last().and_then(Instruction::opcode)
            != Some(bitcoin::blockdata::opcodes::all::OP_CHECKMULTISIG)
    {
        return None;
    }
    let required = usize::try_from(instructions[0].script_num()?).ok()?;
    let key_count = instructions
        .get(instructions.len().saturating_sub(2))
        .and_then(Instruction::script_num)
        .and_then(|count| usize::try_from(count).ok())?;
    if instructions.len() != key_count.saturating_add(3) || required == 0 || required > key_count {
        return None;
    }
    let public_keys = instructions[1..=key_count]
        .iter()
        .map(|instruction| {
            let bytes = instruction.push_bytes()?.as_bytes();
            bitcoin::PublicKey::from_slice(bytes).ok()
        })
        .collect::<Option<Vec<_>>>()?;
    Some((required, public_keys))
}

fn finalize_psbt_input(psbt: &mut Psbt, input_index: usize) -> bool {
    if let Some(input) = psbt.inputs.get(input_index)
        && (input.witness_script.is_some()
            || input.redeem_script.is_some()
            || !input.tap_scripts.is_empty())
        && psbt
            .finalize_inp_mut(&Secp256k1::verification_only(), input_index)
            .is_ok()
    {
        return true;
    }
    let Some(input) = psbt.inputs.get(input_index) else {
        return false;
    };
    if input.final_script_sig.is_some() || input.final_script_witness.is_some() {
        return true;
    }
    if let Some(signature) = input.tap_key_sig {
        psbt.inputs[input_index].final_script_witness =
            Some(Witness::from_slice(&[signature.to_vec()]));
        return true;
    }
    let Some(prevout) = psbt_prevout(psbt, input_index) else {
        return false;
    };
    let nested = prevout.script_pubkey.is_p2sh();
    let redeem_script = input.redeem_script.clone();
    let witness_script = input.witness_script.clone();
    let (spending_script, segwit) = if nested {
        let Some(redeem_script) = redeem_script.as_ref() else {
            return false;
        };
        if redeem_script.is_p2wsh() {
            let Some(witness_script) = witness_script.as_ref() else {
                return false;
            };
            (witness_script.clone(), true)
        } else {
            (redeem_script.clone(), false)
        }
    } else if prevout.script_pubkey.is_p2wsh() {
        let Some(witness_script) = witness_script else {
            return false;
        };
        (witness_script, true)
    } else {
        (prevout.script_pubkey.clone(), false)
    };
    if let Some((required, public_keys)) = multisig_script_keys(spending_script.as_script()) {
        let signatures = public_keys
            .iter()
            .filter_map(|public_key| input.partial_sigs.get(public_key))
            .take(required)
            .map(|signature| signature.to_vec())
            .collect::<Vec<_>>();
        if signatures.len() < required {
            return false;
        }
        let mut stack = vec![Vec::new()];
        stack.extend(signatures);
        if segwit {
            stack.push(spending_script.to_bytes());
            psbt.inputs[input_index].final_script_witness = Some(Witness::from_slice(&stack));
            if nested {
                psbt.inputs[input_index].final_script_sig = Some(
                    push_script_items(&[redeem_script
                        .as_ref()
                        .expect("nested redeem script was checked")
                        .to_bytes()])
                    .expect("redeem script is bounded"),
                );
            }
        } else {
            if nested {
                stack.push(
                    redeem_script
                        .as_ref()
                        .expect("nested redeem script was checked")
                        .to_bytes(),
                );
            }
            if let Ok(script_sig) = push_script_items(&stack) {
                psbt.inputs[input_index].final_script_sig = Some(script_sig);
            } else {
                return false;
            }
        }
        return true;
    }
    let Some((public_key, signature)) = input
        .partial_sigs
        .iter()
        .find(|(public_key, _)| public_key_matches_script(public_key, spending_script.as_script()))
        .map(|(public_key, signature)| (*public_key, *signature))
    else {
        return false;
    };
    if spending_script.is_p2wpkh() {
        let witness = Witness::from_slice(&[signature.to_vec(), public_key.to_bytes()]);
        psbt.inputs[input_index].final_script_witness = Some(witness);
        if nested {
            psbt.inputs[input_index].final_script_sig = Some(
                push_script_items(&[redeem_script
                    .as_ref()
                    .expect("nested redeem script was checked")
                    .to_bytes()])
                .expect("redeem script is bounded"),
            );
        }
        return true;
    }
    if segwit && (spending_script.is_p2pkh() || spending_script.is_p2pk()) {
        let mut witness_items = vec![signature.to_vec()];
        if spending_script.is_p2pkh() {
            witness_items.push(public_key.to_bytes());
        }
        witness_items.push(spending_script.to_bytes());
        psbt.inputs[input_index].final_script_witness = Some(Witness::from_slice(&witness_items));
        if nested {
            psbt.inputs[input_index].final_script_sig = Some(
                push_script_items(&[redeem_script
                    .as_ref()
                    .expect("nested redeem script was checked")
                    .to_bytes()])
                .expect("redeem script is bounded"),
            );
        }
        return true;
    }
    if spending_script.is_p2pkh() {
        let script_sig = if nested {
            push_script_items(&[
                signature.to_vec(),
                public_key.to_bytes(),
                redeem_script
                    .as_ref()
                    .expect("nested redeem script was checked")
                    .to_bytes(),
            ])
        } else {
            push_script_items(&[signature.to_vec(), public_key.to_bytes()])
        };
        if let Ok(script_sig) = script_sig {
            psbt.inputs[input_index].final_script_sig = Some(script_sig);
            return true;
        }
    } else if spending_script.is_p2pk() {
        let mut items = vec![signature.to_vec()];
        if nested {
            items.push(
                redeem_script
                    .as_ref()
                    .expect("nested redeem script was checked")
                    .to_bytes(),
            );
        }
        if let Ok(script_sig) = push_script_items(&items) {
            psbt.inputs[input_index].final_script_sig = Some(script_sig);
            return true;
        }
    }
    false
}

fn finalize_psbt(params: &Value) -> Result<Value> {
    let mut psbt = parse_psbt(params, 0)?;
    let extract = optional_bool(params, 1, true, "extract")?;
    let complete = (0..psbt.inputs.len()).all(|index| finalize_psbt_input(&mut psbt, index));
    let mut result = json!({
        "psbt": encode_psbt(&psbt),
        "complete": complete,
    });
    if complete && extract {
        let transaction = psbt.clone().extract_tx_unchecked_fee_rate();
        result["hex"] = json!(hex::encode(serialize(&transaction)));
    }
    Ok(result)
}

#[derive(Clone)]
struct DescriptorDerivedKey {
    public_key: Option<bitcoin::PublicKey>,
    private_key: Option<bitcoin::PrivateKey>,
    origin: Option<(bitcoin::bip32::Fingerprint, bitcoin::bip32::DerivationPath)>,
}

#[derive(Clone)]
struct DescriptorCandidate {
    script_pubkey: ScriptBuf,
    redeem_script: Option<ScriptBuf>,
    witness_script: Option<ScriptBuf>,
    tap_internal_key: Option<bitcoin::XOnlyPublicKey>,
    tap_merkle_root: Option<bitcoin::taproot::TapNodeHash>,
    tap_tree: Option<bitcoin::taproot::TapTree>,
    tap_scripts: Vec<(
        bitcoin::taproot::ControlBlock,
        ScriptBuf,
        bitcoin::taproot::LeafVersion,
    )>,
    keys: Vec<DescriptorDerivedKey>,
}

fn update_taproot_psbt_origins(
    origins: &mut std::collections::BTreeMap<
        bitcoin::XOnlyPublicKey,
        (Vec<bitcoin::TapLeafHash>, bitcoin::bip32::KeySource),
    >,
    candidate: &DescriptorCandidate,
) {
    for key in &candidate.keys {
        if let (Some(public_key), Some(origin)) = (key.public_key, &key.origin) {
            origins
                .entry(bitcoin::XOnlyPublicKey::from(public_key))
                .or_insert_with(|| (Vec::new(), (origin.0, origin.1.clone())));
        }
    }
    for (_, script, leaf_version) in &candidate.tap_scripts {
        let Ok(miniscript) = Miniscript::<bitcoin::XOnlyPublicKey, Tap>::decode_consensus(script)
        else {
            continue;
        };
        let leaf_hash = bitcoin::TapLeafHash::from_script(script, *leaf_version);
        for public_key in miniscript.iter_pk() {
            let xonly = public_key;
            if let Some((leaf_hashes, _)) = origins.get_mut(&xonly)
                && !leaf_hashes.contains(&leaf_hash)
            {
                leaf_hashes.push(leaf_hash);
            }
        }
    }
}

#[derive(Clone, Copy)]
struct DescriptorSighashType {
    ecdsa: EcdsaSighashType,
    taproot: TapSighashType,
}

fn descriptor_process_psbt(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let mut psbt = parse_psbt(params, 0)?;
    let descriptors = params
        .get(1)
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("descriptorprocesspsbt expects an array of descriptors"))?;
    if descriptors.is_empty() {
        bail!("descriptorprocesspsbt requires at least one descriptor")
    }
    let mut candidates = Vec::new();
    for descriptor in descriptors {
        let (descriptor, range) = parse_descriptor_spec(descriptor)?;
        candidates.extend(descriptor_candidates(node, &descriptor, range)?);
    }
    let sighash_name = params
        .get(2)
        .filter(|value| !value.is_null())
        .map(|value| {
            value
                .as_str()
                .ok_or_else(|| anyhow!("sighashtype must be a string"))
        })
        .transpose()?
        .unwrap_or("DEFAULT");
    let sighash_type = parse_descriptor_sighash_type(sighash_name)?;
    let include_bip32_derivations = params
        .get(3)
        .filter(|value| !value.is_null())
        .map(|value| {
            value
                .as_bool()
                .ok_or_else(|| anyhow!("bip32derivs must be a boolean"))
        })
        .transpose()?
        .unwrap_or(true);
    let finalize = params
        .get(4)
        .filter(|value| !value.is_null())
        .map(|value| {
            value
                .as_bool()
                .ok_or_else(|| anyhow!("finalize must be a boolean"))
        })
        .transpose()?
        .unwrap_or(true);

    for input_index in 0..psbt.inputs.len() {
        if psbt.inputs[input_index].witness_utxo.is_none()
            && psbt.inputs[input_index].non_witness_utxo.is_none()
            && let Some(outpoint) = psbt
                .unsigned_tx
                .input
                .get(input_index)
                .map(|input| input.previous_output)
            && let Some((output, transaction)) = lookup_psbt_prevout(node, &outpoint)?
        {
            if output.script_pubkey.is_witness_program() {
                psbt.inputs[input_index].witness_utxo = Some(output);
            } else if let Some(transaction) = transaction {
                psbt.inputs[input_index].non_witness_utxo = Some(transaction);
            }
        }
        let Some(prevout) = psbt_prevout(&psbt, input_index) else {
            continue;
        };
        let Some(candidate) = candidates
            .iter()
            .find(|candidate| candidate.script_pubkey == prevout.script_pubkey)
        else {
            continue;
        };
        if let Some(redeem_script) = &candidate.redeem_script {
            psbt.inputs[input_index].redeem_script = Some(redeem_script.clone());
        }
        if let Some(witness_script) = &candidate.witness_script {
            psbt.inputs[input_index].witness_script = Some(witness_script.clone());
        }
        if let Some(tap_internal_key) = candidate.tap_internal_key {
            psbt.inputs[input_index].tap_internal_key = Some(tap_internal_key);
        }
        if let Some(tap_merkle_root) = candidate.tap_merkle_root {
            psbt.inputs[input_index].tap_merkle_root = Some(tap_merkle_root);
        }
        for (control_block, script, leaf_version) in &candidate.tap_scripts {
            psbt.inputs[input_index]
                .tap_scripts
                .insert(control_block.clone(), (script.clone(), *leaf_version));
        }
        if include_bip32_derivations {
            for key in &candidate.keys {
                if let (Some(public_key), Some(origin)) = (key.public_key, &key.origin) {
                    psbt.inputs[input_index]
                        .bip32_derivation
                        .entry(public_key.inner)
                        .or_insert_with(|| (origin.0, origin.1.clone()));
                }
            }
            update_taproot_psbt_origins(&mut psbt.inputs[input_index].tap_key_origins, candidate);
        }
        sign_descriptor_psbt_input(&mut psbt, input_index, &prevout, candidate, sighash_type)?;
        if finalize {
            let _ = finalize_psbt_input(&mut psbt, input_index);
        }
    }

    for output_index in 0..psbt.outputs.len() {
        let script_pubkey = &psbt.unsigned_tx.output[output_index].script_pubkey;
        let Some(candidate) = candidates
            .iter()
            .find(|candidate| &candidate.script_pubkey == script_pubkey)
        else {
            continue;
        };
        if let Some(redeem_script) = &candidate.redeem_script {
            psbt.outputs[output_index].redeem_script = Some(redeem_script.clone());
        }
        if let Some(witness_script) = &candidate.witness_script {
            psbt.outputs[output_index].witness_script = Some(witness_script.clone());
        }
        if let Some(tap_internal_key) = candidate.tap_internal_key {
            psbt.outputs[output_index].tap_internal_key = Some(tap_internal_key);
        }
        if let Some(tap_tree) = &candidate.tap_tree {
            psbt.outputs[output_index].tap_tree = Some(tap_tree.clone());
        }
        if include_bip32_derivations {
            for key in &candidate.keys {
                if let (Some(public_key), Some(origin)) = (key.public_key, &key.origin) {
                    psbt.outputs[output_index]
                        .bip32_derivation
                        .entry(public_key.inner)
                        .or_insert_with(|| (origin.0, origin.1.clone()));
                }
            }
            update_taproot_psbt_origins(&mut psbt.outputs[output_index].tap_key_origins, candidate);
        }
    }

    let complete = (0..psbt.inputs.len()).all(|index| {
        psbt.inputs[index].final_script_sig.is_some()
            || psbt.inputs[index].final_script_witness.is_some()
    });
    let mut result = json!({
        "psbt": encode_psbt(&psbt),
        "complete": complete,
    });
    if complete {
        result["hex"] = json!(hex::encode(serialize(
            &psbt.clone().extract_tx_unchecked_fee_rate()
        )));
    }
    Ok(result)
}

fn parse_descriptor_sighash_type(value: &str) -> Result<DescriptorSighashType> {
    let uppercase = value.to_ascii_uppercase();
    let (ecdsa, taproot) = match uppercase.as_str() {
        "DEFAULT" | "SIGHASH_DEFAULT" => (EcdsaSighashType::All, TapSighashType::Default),
        "ALL" | "SIGHASH_ALL" => (EcdsaSighashType::All, TapSighashType::All),
        "NONE" | "SIGHASH_NONE" => (EcdsaSighashType::None, TapSighashType::None),
        "SINGLE" | "SIGHASH_SINGLE" => (EcdsaSighashType::Single, TapSighashType::Single),
        "ALL|ANYONECANPAY" | "SIGHASH_ALL|SIGHASH_ANYONECANPAY" => (
            EcdsaSighashType::AllPlusAnyoneCanPay,
            TapSighashType::AllPlusAnyoneCanPay,
        ),
        "NONE|ANYONECANPAY" | "SIGHASH_NONE|SIGHASH_ANYONECANPAY" => (
            EcdsaSighashType::NonePlusAnyoneCanPay,
            TapSighashType::NonePlusAnyoneCanPay,
        ),
        "SINGLE|ANYONECANPAY" | "SIGHASH_SINGLE|SIGHASH_ANYONECANPAY" => (
            EcdsaSighashType::SinglePlusAnyoneCanPay,
            TapSighashType::SinglePlusAnyoneCanPay,
        ),
        _ => bail!("invalid sighash type: {value}"),
    };
    Ok(DescriptorSighashType { ecdsa, taproot })
}

fn parse_descriptor_spec(value: &Value) -> Result<(String, Option<(u32, u32)>)> {
    if let Some(descriptor) = value.as_str() {
        return Ok((
            descriptor.to_owned(),
            descriptor
                .split('#')
                .next()
                .is_some_and(|payload| payload.contains('*'))
                .then_some((0, 1_000)),
        ));
    }
    let descriptor = value
        .get("desc")
        .and_then(Value::as_str)
        .ok_or_else(|| anyhow!("descriptor entries must be strings or objects with desc"))?;
    let range = value
        .get("range")
        .filter(|value| !value.is_null())
        .map(parse_descriptor_process_range)
        .transpose()?;
    Ok((
        descriptor.to_owned(),
        range.or_else(|| {
            descriptor
                .split('#')
                .next()
                .is_some_and(|payload| payload.contains('*'))
                .then_some((0, 1_000))
        }),
    ))
}

fn parse_descriptor_process_range(value: &Value) -> Result<(u32, u32)> {
    if let Some(end) = value.as_u64() {
        let end = u32::try_from(end).map_err(|_| anyhow!("descriptor range is too large"))?;
        return Ok((0, end));
    }
    parse_descriptor_range(value)
}

fn descriptor_candidates(
    node: &Arc<Node>,
    descriptor: &str,
    range: Option<(u32, u32)>,
) -> Result<Vec<DescriptorCandidate>> {
    let descriptor = if descriptor.contains('#') {
        descriptor_payload(descriptor)?.0
    } else {
        descriptor
    };
    descriptor_candidates_inner(node, descriptor, range)
}

fn miniscript_taproot_candidates(
    descriptor: &str,
    range: Option<(u32, u32)>,
) -> Result<Option<Vec<DescriptorCandidate>>> {
    if !descriptor.starts_with("tr(") || !descriptor.contains(',') {
        return Ok(None);
    }
    let secp = Secp256k1::new();
    let Ok((parsed, keymap)) =
        MiniscriptDescriptor::<MiniscriptPublicKey>::parse_descriptor(&secp, descriptor)
    else {
        return Ok(None);
    };
    if !matches!(&parsed, MiniscriptDescriptor::Tr(_)) {
        return Ok(None);
    }
    let indices = descriptor_indices(parsed.has_wildcard(), range)?;
    let verification = Secp256k1::verification_only();
    let signing = Secp256k1::new();
    let candidates = indices
        .into_iter()
        .map(|index| {
            let definite = parsed.at_derivation_index(index.unwrap_or(0))?;
            let derived = definite.derived_descriptor(&verification);
            let descriptor_keys = definite.iter_pk().collect::<Vec<_>>();
            let public_keys = derived.iter_pk().collect::<Vec<_>>();
            if descriptor_keys.len() != public_keys.len() {
                bail!("miniscript descriptor key derivation is inconsistent")
            }
            let keys = descriptor_keys
                .into_iter()
                .zip(public_keys)
                .map(|(descriptor_key, public_key)| {
                    let origin = descriptor_key
                        .full_derivation_path()
                        .map(|path| (descriptor_key.master_fingerprint(), path));
                    let private_key = origin
                        .as_ref()
                        .and_then(|(_, path)| {
                            keymap
                                .get_key(
                                    KeyRequest::Bip32((
                                        descriptor_key.master_fingerprint(),
                                        path.clone(),
                                    )),
                                    &signing,
                                )
                                .ok()
                                .flatten()
                        })
                        .or_else(|| {
                            keymap
                                .get_key(KeyRequest::Pubkey(public_key), &signing)
                                .ok()
                                .flatten()
                        });
                    DescriptorDerivedKey {
                        public_key: Some(public_key),
                        private_key,
                        origin,
                    }
                })
                .collect();
            let (tap_internal_key, tap_merkle_root, tap_tree, tap_scripts) = match &derived {
                MiniscriptDescriptor::Tr(tr) => {
                    let spend_info = tr.spend_info();
                    let scripts = spend_info
                        .leaves()
                        .map(|leaf| {
                            (
                                leaf.control_block().clone(),
                                ScriptBuf::from_bytes(leaf.script().as_bytes().to_vec()),
                                leaf.leaf_version(),
                            )
                        })
                        .collect();
                    (
                        Some(bitcoin::XOnlyPublicKey::from(*tr.internal_key())),
                        spend_info.merkle_root(),
                        spend_info.to_tap_tree(),
                        scripts,
                    )
                }
                _ => (None, None, None, Vec::new()),
            };
            Ok(DescriptorCandidate {
                script_pubkey: derived.script_pubkey(),
                redeem_script: None,
                witness_script: None,
                tap_internal_key,
                tap_merkle_root,
                tap_tree,
                tap_scripts,
                keys,
            })
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(Some(candidates))
}

fn miniscript_v0_candidates(
    descriptor: &str,
    range: Option<(u32, u32)>,
) -> Result<Option<Vec<DescriptorCandidate>>> {
    let secp = Secp256k1::new();
    let Ok((parsed, keymap)) =
        MiniscriptDescriptor::<MiniscriptPublicKey>::parse_descriptor(&secp, descriptor)
    else {
        return Ok(None);
    };
    if !matches!(
        &parsed,
        MiniscriptDescriptor::Sh(_) | MiniscriptDescriptor::Wsh(_)
    ) {
        return Ok(None);
    }

    let indices = descriptor_indices(parsed.has_wildcard(), range)?;
    let verification = Secp256k1::verification_only();
    let signing = Secp256k1::new();
    let candidates = indices
        .into_iter()
        .map(|index| {
            let definite = parsed.at_derivation_index(index.unwrap_or(0))?;
            let derived = definite.derived_descriptor(&verification);
            let descriptor_keys = definite.iter_pk().collect::<Vec<_>>();
            let public_keys = derived.iter_pk().collect::<Vec<_>>();
            if descriptor_keys.len() != public_keys.len() {
                bail!("miniscript descriptor key derivation is inconsistent")
            }
            let keys = descriptor_keys
                .into_iter()
                .zip(public_keys)
                .map(|(descriptor_key, public_key)| {
                    let origin = descriptor_key
                        .full_derivation_path()
                        .map(|path| (descriptor_key.master_fingerprint(), path));
                    let private_key = origin
                        .as_ref()
                        .and_then(|(_, path)| {
                            keymap
                                .get_key(
                                    KeyRequest::Bip32((
                                        descriptor_key.master_fingerprint(),
                                        path.clone(),
                                    )),
                                    &signing,
                                )
                                .ok()
                                .flatten()
                        })
                        .or_else(|| {
                            keymap
                                .get_key(KeyRequest::Pubkey(public_key), &signing)
                                .ok()
                                .flatten()
                        });
                    DescriptorDerivedKey {
                        public_key: Some(public_key),
                        private_key,
                        origin,
                    }
                })
                .collect::<Vec<_>>();
            let explicit = derived.explicit_script()?;
            let (redeem_script, witness_script) = match derived.desc_type() {
                MiniscriptDescriptorType::Wsh | MiniscriptDescriptorType::WshSortedMulti => {
                    (None, Some(explicit))
                }
                MiniscriptDescriptorType::ShWsh | MiniscriptDescriptorType::ShWshSortedMulti => {
                    (Some(explicit.to_p2wsh()), Some(explicit))
                }
                MiniscriptDescriptorType::Sh
                | MiniscriptDescriptorType::ShSortedMulti
                | MiniscriptDescriptorType::ShWpkh => (Some(explicit), None),
                _ => bail!("unsupported Miniscript v0 descriptor type"),
            };
            Ok(DescriptorCandidate {
                script_pubkey: derived.script_pubkey(),
                redeem_script,
                witness_script,
                tap_internal_key: None,
                tap_merkle_root: None,
                tap_tree: None,
                tap_scripts: Vec::new(),
                keys,
            })
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(Some(candidates))
}

fn raw_taproot_script_pubkey(xonly: bitcoin::XOnlyPublicKey) -> ScriptBuf {
    let mut bytes = Vec::with_capacity(34);
    bytes.extend_from_slice(&[0x51, 0x20]);
    bytes.extend_from_slice(&xonly.serialize());
    ScriptBuf::from_bytes(bytes)
}

fn descriptor_candidates_inner(
    node: &Arc<Node>,
    descriptor: &str,
    range: Option<(u32, u32)>,
) -> Result<Vec<DescriptorCandidate>> {
    if let Some(address) = descriptor
        .strip_prefix("addr(")
        .and_then(|value| value.strip_suffix(')'))
    {
        if range.is_some() {
            bail!("addr descriptors do not accept a range")
        }
        return Ok(vec![DescriptorCandidate {
            script_pubkey: address
                .parse::<Address<bitcoin::address::NetworkUnchecked>>()?
                .require_network(node.config.network)?
                .script_pubkey(),
            redeem_script: None,
            witness_script: None,
            tap_internal_key: None,
            tap_merkle_root: None,
            tap_tree: None,
            tap_scripts: Vec::new(),
            keys: Vec::new(),
        }]);
    }
    if let Some(script) = descriptor
        .strip_prefix("raw(")
        .and_then(|value| value.strip_suffix(')'))
    {
        if range.is_some() {
            bail!("raw descriptors do not accept a range")
        }
        return Ok(vec![DescriptorCandidate {
            script_pubkey: ScriptBuf::from_bytes(hex::decode(script)?),
            redeem_script: None,
            witness_script: None,
            tap_internal_key: None,
            tap_merkle_root: None,
            tap_tree: None,
            tap_scripts: Vec::new(),
            keys: Vec::new(),
        }]);
    }
    if let Some(candidates) = miniscript_v0_candidates(descriptor, range)? {
        return Ok(candidates);
    }
    if let Some(key_expression) = descriptor
        .strip_prefix("rawtr(")
        .and_then(|value| value.strip_suffix(')'))
    {
        let origin = descriptor_key_origin(key_expression)?;
        let (key, path, wildcard) = parse_descriptor_key(key_expression)?;
        let indices = descriptor_indices(wildcard, range)?;
        let secp = bitcoin::secp256k1::Secp256k1::verification_only();
        let mut candidates = Vec::with_capacity(indices.len());
        for index in indices {
            let xonly = match &key {
                DescriptorKey::PublicKey(public_key) => bitcoin::XOnlyPublicKey::from(*public_key),
                DescriptorKey::XOnlyPublicKey(public_key) => *public_key,
                DescriptorKey::Xpriv(_) | DescriptorKey::Xpub(_) => {
                    bitcoin::XOnlyPublicKey::from(descriptor_public_key(&key, &path, index, &secp)?)
                }
            };
            let derived_key = match &key {
                DescriptorKey::XOnlyPublicKey(_) => DescriptorDerivedKey {
                    public_key: None,
                    private_key: None,
                    origin: origin.clone(),
                },
                _ => descriptor_derived_key(
                    node,
                    &key,
                    &path,
                    index,
                    descriptor_public_key(&key, &path, index, &secp)?,
                    origin.clone(),
                )?,
            };
            candidates.push(DescriptorCandidate {
                script_pubkey: raw_taproot_script_pubkey(xonly),
                redeem_script: None,
                witness_script: None,
                tap_internal_key: None,
                tap_merkle_root: None,
                tap_tree: None,
                tap_scripts: Vec::new(),
                keys: vec![derived_key],
            });
        }
        return Ok(candidates);
    }
    for kind in ["sh", "wsh"] {
        if let Some(inner) = descriptor
            .strip_prefix(&format!("{kind}("))
            .and_then(|value| value.strip_suffix(')'))
        {
            let children = descriptor_candidates_inner(node, inner, range)?;
            return children
                .into_iter()
                .map(|child| {
                    if kind == "sh" {
                        let redeem_script = child.script_pubkey.clone();
                        Ok(DescriptorCandidate {
                            script_pubkey: Address::p2sh(&redeem_script, node.config.network)?
                                .script_pubkey(),
                            redeem_script: Some(redeem_script),
                            witness_script: child.witness_script,
                            tap_internal_key: None,
                            tap_merkle_root: None,
                            tap_tree: None,
                            tap_scripts: Vec::new(),
                            keys: child.keys,
                        })
                    } else {
                        let witness_script = child.script_pubkey.clone();
                        Ok(DescriptorCandidate {
                            script_pubkey: Address::p2wsh(&witness_script, node.config.network)
                                .script_pubkey(),
                            redeem_script: None,
                            witness_script: Some(witness_script),
                            tap_internal_key: None,
                            tap_merkle_root: None,
                            tap_tree: None,
                            tap_scripts: Vec::new(),
                            keys: child.keys,
                        })
                    }
                })
                .collect();
        }
    }
    if let Some(arguments) = descriptor
        .strip_prefix("multi(")
        .and_then(|value| value.strip_suffix(')'))
    {
        return multisig_descriptor_candidates(node, arguments, range, false);
    }
    if let Some(arguments) = descriptor
        .strip_prefix("sortedmulti(")
        .and_then(|value| value.strip_suffix(')'))
    {
        return multisig_descriptor_candidates(node, arguments, range, true);
    }
    if let Some(key_expression) = descriptor
        .strip_prefix("pk(")
        .and_then(|value| value.strip_suffix(')'))
    {
        return single_key_descriptor_candidates(node, key_expression, range, |public_key| {
            Ok(Builder::new()
                .push_key(&public_key)
                .push_opcode(bitcoin::blockdata::opcodes::all::OP_CHECKSIG)
                .into_script())
        });
    }
    if let Some(key_expression) = descriptor
        .strip_prefix("combo(")
        .and_then(|value| value.strip_suffix(')'))
    {
        let origin = descriptor_key_origin(key_expression)?;
        let (key, path, wildcard) = parse_descriptor_key(key_expression)?;
        let indices = descriptor_indices(wildcard, range)?;
        let secp = bitcoin::secp256k1::Secp256k1::verification_only();
        let mut candidates = Vec::new();
        for index in indices {
            let public_key = descriptor_public_key(&key, &path, index, &secp)?;
            let derived_key =
                descriptor_derived_key(node, &key, &path, index, public_key, origin.clone())?;
            candidates.push(DescriptorCandidate {
                script_pubkey: Builder::new()
                    .push_key(&public_key)
                    .push_opcode(bitcoin::blockdata::opcodes::all::OP_CHECKSIG)
                    .into_script(),
                redeem_script: None,
                witness_script: None,
                tap_internal_key: None,
                tap_merkle_root: None,
                tap_tree: None,
                tap_scripts: Vec::new(),
                keys: vec![derived_key.clone()],
            });
            candidates.push(DescriptorCandidate {
                script_pubkey: Address::p2pkh(public_key, node.config.network).script_pubkey(),
                redeem_script: None,
                witness_script: None,
                tap_internal_key: None,
                tap_merkle_root: None,
                tap_tree: None,
                tap_scripts: Vec::new(),
                keys: vec![derived_key.clone()],
            });
            if let Ok(compressed) = bitcoin::CompressedPublicKey::try_from(public_key) {
                candidates.push(DescriptorCandidate {
                    script_pubkey: Address::p2wpkh(&compressed, node.config.network)
                        .script_pubkey(),
                    redeem_script: None,
                    witness_script: None,
                    tap_internal_key: None,
                    tap_merkle_root: None,
                    tap_tree: None,
                    tap_scripts: Vec::new(),
                    keys: vec![derived_key.clone()],
                });
                candidates.push(DescriptorCandidate {
                    script_pubkey: Address::p2shwpkh(&compressed, node.config.network)
                        .script_pubkey(),
                    redeem_script: Some(
                        Address::p2wpkh(&compressed, node.config.network).script_pubkey(),
                    ),
                    witness_script: None,
                    tap_internal_key: None,
                    tap_merkle_root: None,
                    tap_tree: None,
                    tap_scripts: Vec::new(),
                    keys: vec![derived_key],
                });
            }
        }
        return Ok(candidates);
    }
    if let Some(candidates) = miniscript_taproot_candidates(descriptor, range)? {
        return Ok(candidates);
    }
    if let Some(key_expression) = descriptor
        .strip_prefix("tr(")
        .and_then(|value| value.strip_suffix(')'))
    {
        let origin = descriptor_key_origin(key_expression)?;
        let (key, path, wildcard) = parse_descriptor_key(key_expression)?;
        let indices = descriptor_indices(wildcard, range)?;
        let secp = bitcoin::secp256k1::Secp256k1::verification_only();
        let mut candidates = Vec::new();
        for index in indices {
            let xonly = match &key {
                DescriptorKey::PublicKey(public_key) => bitcoin::XOnlyPublicKey::from(*public_key),
                DescriptorKey::XOnlyPublicKey(public_key) => *public_key,
                DescriptorKey::Xpriv(_) | DescriptorKey::Xpub(_) => {
                    bitcoin::XOnlyPublicKey::from(descriptor_public_key(&key, &path, index, &secp)?)
                }
            };
            let derived_key = match &key {
                DescriptorKey::XOnlyPublicKey(_) => DescriptorDerivedKey {
                    public_key: None,
                    private_key: None,
                    origin: origin.clone(),
                },
                _ => descriptor_derived_key(
                    node,
                    &key,
                    &path,
                    index,
                    descriptor_public_key(&key, &path, index, &secp)?,
                    origin.clone(),
                )?,
            };
            candidates.push(DescriptorCandidate {
                script_pubkey: Address::p2tr(&secp, xonly, None, node.config.network)
                    .script_pubkey(),
                redeem_script: None,
                witness_script: None,
                tap_internal_key: Some(xonly),
                tap_merkle_root: None,
                tap_tree: None,
                tap_scripts: Vec::new(),
                keys: vec![derived_key],
            });
        }
        return Ok(candidates);
    }
    let Some((kind, key_expression)) = descriptor
        .strip_suffix(')')
        .and_then(|value| value.split_once('('))
        .filter(|(kind, _)| matches!(*kind, "pkh" | "wpkh"))
    else {
        bail!(
            "unsupported descriptor; use addr(...), raw(...), pk(...), pkh(...), wpkh(...), combo(...), multi(...), sortedmulti(...), sh(...), wsh(...), tr(...), or rawtr(...)"
        )
    };
    single_key_descriptor_candidates(node, key_expression, range, |public_key| {
        if kind == "pkh" {
            Ok(Address::p2pkh(public_key, node.config.network).script_pubkey())
        } else {
            let compressed = bitcoin::CompressedPublicKey::try_from(public_key)
                .map_err(|_| anyhow!("wpkh requires a compressed public key"))?;
            Ok(Address::p2wpkh(&compressed, node.config.network).script_pubkey())
        }
    })
}

fn single_key_descriptor_candidates<F>(
    node: &Arc<Node>,
    key_expression: &str,
    range: Option<(u32, u32)>,
    script: F,
) -> Result<Vec<DescriptorCandidate>>
where
    F: Fn(bitcoin::PublicKey) -> Result<ScriptBuf>,
{
    let origin = descriptor_key_origin(key_expression)?;
    let (key, path, wildcard) = parse_descriptor_key(key_expression)?;
    let indices = descriptor_indices(wildcard, range)?;
    let secp = bitcoin::secp256k1::Secp256k1::verification_only();
    indices
        .into_iter()
        .map(|index| {
            let public_key = descriptor_public_key(&key, &path, index, &secp)?;
            Ok(DescriptorCandidate {
                script_pubkey: script(public_key)?,
                redeem_script: None,
                witness_script: None,
                tap_internal_key: None,
                tap_merkle_root: None,
                tap_tree: None,
                tap_scripts: Vec::new(),
                keys: vec![descriptor_derived_key(
                    node,
                    &key,
                    &path,
                    index,
                    public_key,
                    origin.clone(),
                )?],
            })
        })
        .collect()
}

fn multisig_descriptor_candidates(
    node: &Arc<Node>,
    arguments: &str,
    range: Option<(u32, u32)>,
    sorted: bool,
) -> Result<Vec<DescriptorCandidate>> {
    let arguments = arguments.split(',').collect::<Vec<_>>();
    if arguments.len() < 2 {
        bail!("multisig descriptor requires a threshold and keys")
    }
    let required = arguments[0]
        .parse::<u64>()
        .map_err(|_| anyhow!("multisig threshold must be an integer"))?;
    let keys = arguments[1..]
        .iter()
        .map(|key| parse_descriptor_key(key))
        .collect::<Result<Vec<_>>>()?;
    let origins = arguments[1..]
        .iter()
        .map(|key| descriptor_key_origin(key))
        .collect::<Result<Vec<_>>>()?;
    let key_count = u64::try_from(keys.len()).map_err(|_| anyhow!("too many multisig keys"))?;
    if required == 0 || required > key_count || key_count > 16 {
        bail!("multisig threshold must be between 1 and the number of keys (maximum 16)")
    }
    let wildcard = keys.iter().any(|(_, _, wildcard)| *wildcard);
    if keys
        .iter()
        .any(|(_, _, key_wildcard)| *key_wildcard != wildcard)
    {
        bail!("all multisig keys must use the same wildcard form")
    }
    let indices = descriptor_indices(wildcard, range)?;
    let secp = bitcoin::secp256k1::Secp256k1::verification_only();
    indices
        .into_iter()
        .map(|index| {
            let mut derived = keys
                .iter()
                .enumerate()
                .map(|(key_index, (key, path, _))| {
                    let public_key = descriptor_public_key(key, path, index, &secp)?;
                    Ok((
                        public_key,
                        descriptor_derived_key(
                            node,
                            key,
                            path,
                            index,
                            public_key,
                            origins[key_index].clone(),
                        )?,
                    ))
                })
                .collect::<Result<Vec<_>>>()?;
            let mut public_keys = derived
                .iter()
                .map(|(public_key, _)| *public_key)
                .collect::<Vec<_>>();
            if sorted {
                derived.sort_by_key(|(public_key, _)| *public_key);
                public_keys = derived.iter().map(|(public_key, _)| *public_key).collect();
            }
            let mut builder = Builder::new().push_int(required as i64);
            for public_key in &public_keys {
                builder = builder.push_key(public_key);
            }
            Ok(DescriptorCandidate {
                script_pubkey: builder
                    .push_int(key_count as i64)
                    .push_opcode(bitcoin::blockdata::opcodes::all::OP_CHECKMULTISIG)
                    .into_script(),
                redeem_script: None,
                witness_script: None,
                tap_internal_key: None,
                tap_merkle_root: None,
                tap_tree: None,
                tap_scripts: Vec::new(),
                keys: derived.into_iter().map(|(_, key)| key).collect(),
            })
        })
        .collect()
}

fn descriptor_derived_key(
    node: &Arc<Node>,
    key: &DescriptorKey,
    path: &bitcoin::bip32::DerivationPath,
    index: Option<u32>,
    public_key: bitcoin::PublicKey,
    origin: Option<(bitcoin::bip32::Fingerprint, bitcoin::bip32::DerivationPath)>,
) -> Result<DescriptorDerivedKey> {
    let private_key = if let DescriptorKey::Xpriv(xpriv) = key {
        let mut derivation = path.clone();
        if let Some(index) = index {
            derivation = derivation.child(index.into());
        }
        Some(bitcoin::PrivateKey::new(
            xpriv
                .derive_priv(&bitcoin::secp256k1::Secp256k1::new(), &derivation)?
                .private_key,
            node.config.network,
        ))
    } else {
        None
    };
    Ok(DescriptorDerivedKey {
        public_key: Some(public_key),
        private_key,
        origin: origin.map(|(fingerprint, origin_path)| {
            let mut derivation = Vec::from(origin_path);
            derivation.extend(path.as_ref().iter().copied());
            if let Some(index) = index {
                derivation.push(index.into());
            }
            (fingerprint, derivation.into())
        }),
    })
}

fn sign_descriptor_psbt_input(
    psbt: &mut Psbt,
    input_index: usize,
    prevout: &TxOut,
    candidate: &DescriptorCandidate,
    sighash_type: DescriptorSighashType,
) -> Result<()> {
    if let Some(tap_internal_key) = candidate.tap_internal_key {
        if let Some(private_key) = candidate.keys.iter().find_map(|key| {
            let private_key = key.private_key.as_ref()?;
            let public_key = key.public_key?;
            (bitcoin::XOnlyPublicKey::from(public_key) == tap_internal_key).then_some(private_key)
        }) {
            let prevouts = (0..psbt.inputs.len())
                .map(|index| psbt_prevout(psbt, index))
                .collect::<Option<Vec<_>>>();
            let Some(prevouts) = prevouts else {
                return Ok(());
            };
            let sighash = SighashCache::new(&psbt.unsigned_tx).taproot_key_spend_signature_hash(
                input_index,
                &Prevouts::All(&prevouts),
                sighash_type.taproot,
            )?;
            let keypair =
                bitcoin::secp256k1::Keypair::from_secret_key(&Secp256k1::new(), &private_key.inner)
                    .tap_tweak(&Secp256k1::new(), psbt.inputs[input_index].tap_merkle_root)
                    .to_keypair();
            let secp = Secp256k1::new();
            psbt.inputs[input_index].tap_key_sig = Some(bitcoin::taproot::Signature {
                signature: secp.sign_schnorr_no_aux_rand(&Message::from(sighash), &keypair),
                sighash_type: sighash_type.taproot,
            });
            return Ok(());
        }
        if !candidate.tap_scripts.is_empty() {
            sign_taproot_script_path(psbt, input_index, candidate, sighash_type.taproot)?;
            return Ok(());
        }
    }

    let sighash_type = sighash_type.ecdsa;
    let signing_script = candidate
        .witness_script
        .as_ref()
        .or(candidate.redeem_script.as_ref())
        .unwrap_or(&prevout.script_pubkey);
    let miniscript_keys = candidate
        .witness_script
        .as_ref()
        .and_then(|script| {
            Miniscript::<bitcoin::PublicKey, Segwitv0>::decode_consensus(script)
                .ok()
                .map(|miniscript| miniscript.iter_pk().collect::<Vec<_>>())
        })
        .or_else(|| {
            candidate
                .redeem_script
                .as_ref()
                .filter(|script| !script.is_p2wsh())
                .and_then(|script| {
                    Miniscript::<bitcoin::PublicKey, Legacy>::decode_consensus(script)
                        .ok()
                        .map(|miniscript| miniscript.iter_pk().collect::<Vec<_>>())
                })
        });
    let keys = candidate
        .keys
        .iter()
        .filter_map(|key| key.private_key.as_ref().map(|private| (key, private)))
        .filter_map(|(key, private)| key.public_key.map(|public| (public, private)))
        .filter(|(public_key, _)| {
            miniscript_keys.as_ref().map_or_else(
                || descriptor_public_key_matches_script(public_key, signing_script),
                |keys| keys.contains(public_key),
            )
        })
        .collect::<Vec<_>>();
    if keys.is_empty()
        || !(miniscript_keys.is_some()
            || signing_script.is_p2pk()
            || signing_script.is_p2pkh()
            || signing_script.is_p2wpkh()
            || multisig_script_keys(signing_script).is_some())
    {
        return Ok(());
    }
    let message = if signing_script.is_p2wpkh() {
        Message::from(SighashCache::new(&psbt.unsigned_tx).p2wpkh_signature_hash(
            input_index,
            signing_script,
            prevout.value,
            sighash_type,
        )?)
    } else if candidate.witness_script.is_some() {
        Message::from(SighashCache::new(&psbt.unsigned_tx).p2wsh_signature_hash(
            input_index,
            signing_script,
            prevout.value,
            sighash_type,
        )?)
    } else {
        Message::from(SighashCache::new(&psbt.unsigned_tx).legacy_signature_hash(
            input_index,
            signing_script,
            sighash_type.to_u32(),
        )?)
    };
    let secp = Secp256k1::new();
    for (public_key, private_key) in keys {
        if psbt.inputs[input_index]
            .partial_sigs
            .contains_key(&public_key)
        {
            continue;
        }
        let signature = secp.sign_ecdsa(&message, &private_key.inner);
        psbt.inputs[input_index].partial_sigs.insert(
            public_key,
            EcdsaSignature {
                signature,
                sighash_type,
            },
        );
    }
    Ok(())
}

fn sign_taproot_script_path(
    psbt: &mut Psbt,
    input_index: usize,
    candidate: &DescriptorCandidate,
    sighash_type: TapSighashType,
) -> Result<()> {
    let prevouts = (0..psbt.inputs.len())
        .map(|index| psbt_prevout(psbt, index))
        .collect::<Option<Vec<_>>>();
    let Some(prevouts) = prevouts else {
        return Ok(());
    };
    let secp = Secp256k1::new();
    for (_, script, leaf_version) in &candidate.tap_scripts {
        if *leaf_version != bitcoin::taproot::LeafVersion::TapScript {
            continue;
        }
        let Ok(miniscript) = Miniscript::<bitcoin::XOnlyPublicKey, Tap>::decode_consensus(script)
        else {
            continue;
        };
        let leaf_keys = miniscript.iter_pk().collect::<Vec<_>>();
        let leaf_hash = bitcoin::TapLeafHash::from_script(script, *leaf_version);
        for key in &candidate.keys {
            let Some(public_key) = key.public_key else {
                continue;
            };
            let Some(private_key) = key.private_key.as_ref() else {
                continue;
            };
            let xonly = bitcoin::XOnlyPublicKey::from(public_key);
            if !leaf_keys.contains(&xonly)
                || psbt.inputs[input_index]
                    .tap_script_sigs
                    .contains_key(&(xonly, leaf_hash))
            {
                continue;
            }
            let sighash = SighashCache::new(&psbt.unsigned_tx)
                .taproot_script_spend_signature_hash(
                    input_index,
                    &Prevouts::All(&prevouts),
                    leaf_hash,
                    sighash_type,
                )?;
            let keypair = bitcoin::secp256k1::Keypair::from_secret_key(&secp, &private_key.inner);
            psbt.inputs[input_index].tap_script_sigs.insert(
                (xonly, leaf_hash),
                bitcoin::taproot::Signature {
                    signature: secp.sign_schnorr_no_aux_rand(&Message::from(sighash), &keypair),
                    sighash_type,
                },
            );
        }
    }
    Ok(())
}

fn descriptor_public_key_matches_script(
    public_key: &bitcoin::PublicKey,
    script: &bitcoin::Script,
) -> bool {
    public_key_matches_script(public_key, script)
        || multisig_script_keys(script).is_some_and(|(_, keys)| keys.contains(public_key))
}

fn lookup_psbt_prevout(
    node: &Arc<Node>,
    outpoint: &OutPoint,
) -> Result<Option<(TxOut, Option<Transaction>)>> {
    if let Some(entry) = node.mempool.read().get(&outpoint.txid)
        && let Some(output) = entry.transaction.output.get(outpoint.vout as usize)
    {
        return Ok(Some((output.clone(), Some(entry.transaction.clone()))));
    }
    let mut chain = node.chain.write();
    let transaction = chain
        .transaction(&outpoint.txid)?
        .map(|(transaction, _)| transaction);
    let output = transaction
        .as_ref()
        .and_then(|transaction| transaction.output.get(outpoint.vout as usize))
        .cloned()
        .or_else(|| chain.utxo(outpoint).map(|entry| entry.output.clone()));
    Ok(output.map(|output| (output, transaction)))
}

fn update_psbt_utxos(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let mut psbt = parse_psbt(params, 0)?;
    for index in 0..psbt.inputs.len() {
        if psbt.inputs[index].witness_utxo.is_some()
            || psbt.inputs[index].non_witness_utxo.is_some()
        {
            continue;
        }
        let Some(outpoint) = psbt
            .unsigned_tx
            .input
            .get(index)
            .map(|input| input.previous_output)
        else {
            continue;
        };
        let Some((output, transaction)) = lookup_psbt_prevout(node, &outpoint)? else {
            continue;
        };
        if output.script_pubkey.is_witness_program() {
            psbt.inputs[index].witness_utxo = Some(output);
        } else if let Some(transaction) = transaction {
            psbt.inputs[index].non_witness_utxo = Some(transaction);
        }
    }
    Ok(json!(encode_psbt(&psbt)))
}

fn sign_message_with_private_key(params: &Value) -> Result<Value> {
    let private_key = bitcoin::PrivateKey::from_wif(&param::<String>(params, 0)?)?;
    let message = param::<String>(params, 1)?;
    let secp = Secp256k1::new();
    let message_hash = signed_msg_hash(&message);
    let signature = secp.sign_ecdsa_recoverable(
        &Message::from_digest(message_hash.to_byte_array()),
        &private_key.inner,
    );
    Ok(json!(base64::engine::general_purpose::STANDARD.encode(
        MessageSignature::new(signature, private_key.compressed).serialize()
    )))
}

fn verify_message(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let address = param::<String>(params, 0)?
        .parse::<Address<bitcoin::address::NetworkUnchecked>>()?
        .require_network(node.config.network)?;
    let signature = MessageSignature::from_slice(
        &base64::engine::general_purpose::STANDARD.decode(param::<String>(params, 1)?)?,
    )?;
    let message = param::<String>(params, 2)?;
    let verified =
        signature.is_signed_by_address(&Secp256k1::new(), &address, signed_msg_hash(&message))?;
    Ok(json!(verified))
}

fn create_multisig(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let required = param::<u64>(params, 0)?;
    let key_values = params
        .get(1)
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("createmultisig keys must be an array"))?;
    let key_count = u64::try_from(key_values.len()).map_err(|_| anyhow!("too many keys"))?;
    if required == 0 || required > key_count || key_count > 16 {
        bail!("required signatures must be between 1 and the number of keys (maximum 16)")
    }
    let public_keys = key_values
        .iter()
        .map(|value| {
            let key = value
                .as_str()
                .ok_or_else(|| anyhow!("multisig keys must be public key strings"))?;
            key.parse::<bitcoin::PublicKey>()
                .map_err(|error| anyhow!("invalid public key: {error}"))
        })
        .collect::<Result<Vec<_>>>()?;
    let mut builder = Builder::new().push_int(required as i64);
    for public_key in &public_keys {
        builder = builder.push_key(public_key);
    }
    let redeem_script = builder
        .push_int(key_count as i64)
        .push_opcode(bitcoin::blockdata::opcodes::all::OP_CHECKMULTISIG)
        .into_script();
    let requested_address_type = optional_str(params, 2, "legacy", "address_type")?;
    if requested_address_type == "bech32m" {
        bail!("createmultisig cannot create bech32m multisig addresses")
    }
    let address_type = if public_keys.iter().any(|key| !key.compressed) {
        "legacy"
    } else {
        requested_address_type
    };
    let key_list = public_keys
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(",");
    let descriptor_body = match address_type {
        "legacy" => format!("sh(multi({required},{key_list}))"),
        "p2sh-segwit" => format!("sh(wsh(multi({required},{key_list})))"),
        "bech32" => format!("wsh(multi({required},{key_list}))"),
        _ => bail!("unsupported multisig address type: {address_type}"),
    };
    let descriptor = format!(
        "{descriptor_body}#{}",
        descriptor_checksum(&descriptor_body).context("creating multisig descriptor checksum")?
    );
    let address = match address_type {
        "legacy" => Address::p2sh(&redeem_script, node.config.network)?,
        "p2sh-segwit" => Address::p2shwsh(&redeem_script, node.config.network),
        "bech32" => Address::p2wsh(&redeem_script, node.config.network),
        _ => bail!("unsupported multisig address type: {address_type}"),
    };
    let mut result = json!({
        "address": address.to_string(),
        "redeemScript": hex::encode(redeem_script.as_bytes()),
        "descriptor": descriptor,
    });
    if address_type != requested_address_type {
        result["warnings"] = json!([
            "Unable to make chosen address type, please ensure no uncompressed public keys are present."
        ]);
    }
    Ok(result)
}

fn send_raw_transaction(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let bytes = hex::decode(param::<String>(params, 0)?).context("TX decode failed")?;
    let transaction: Transaction = deserialize(&bytes)
        .context("TX decode failed. Make sure the tx has at least one input.")?;
    let max_fee_rate = parse_max_fee_rate(params.get(1))?;
    let max_burn_amount = parse_max_burn_amount(params.get(2))?;
    validate_burn_amount(&transaction, max_burn_amount)?;
    enforce_max_fee_rate(node, &transaction, max_fee_rate)?;
    let txid = if node.config.private_broadcast {
        node.queue_private_broadcast(transaction)?
    } else {
        node.accept_transaction(transaction)?
    };
    Ok(json!(txid.to_string()))
}

fn private_broadcast_info(node: &Arc<Node>) -> Value {
    let transactions = node
        .private_broadcast_infos()
        .into_iter()
        .map(|info| {
            let peers = info
                .peers
                .into_iter()
                .map(|peer| {
                    let mut value = json!({
                        "address": peer.address.to_string(),
                        "sent": peer.sent,
                    });
                    if let Some(received) = peer.received {
                        value["received"] = json!(received);
                    }
                    value
                })
                .collect::<Vec<_>>();
            json!({
                "txid": info.transaction.compute_txid().to_string(),
                "wtxid": info.transaction.compute_wtxid().to_string(),
                "hex": hex::encode(serialize(&info.transaction)),
                "peers": peers,
            })
        })
        .collect::<Vec<_>>();
    json!({"transactions": transactions})
}

fn abort_private_broadcast(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let id = param::<String>(params, 0)?;
    let id = id
        .parse::<Txid>()
        .map_err(|error| anyhow!("invalid private broadcast transaction id: {error}"))?;
    let removed = node.abort_private_broadcast(id);
    if removed.is_empty() {
        bail!("Transaction not in private broadcast queue. Check getprivatebroadcastinfo.")
    }
    Ok(json!({
        "removed_transactions": removed
            .into_iter()
            .map(|info| {
                json!({
                    "txid": info.transaction.compute_txid().to_string(),
                    "wtxid": info.transaction.compute_wtxid().to_string(),
                    "hex": hex::encode(serialize(&info.transaction)),
                })
            })
            .collect::<Vec<_>>(),
    }))
}

fn parse_max_fee_rate(value: Option<&Value>) -> Result<Option<u64>> {
    let max_fee_rate = value
        .filter(|value| !value.is_null())
        .map(|value| parse_btc_amount(value, "maxfeerate").map(|amount| amount.to_sat()))
        .transpose()?
        .unwrap_or(DEFAULT_MAX_RAW_TX_FEE_RATE_SAT_PER_KVB);
    if max_fee_rate >= 100_000_000 {
        bail!("Fee rates larger than or equal to 1BTC/kvB are not accepted")
    }
    Ok((max_fee_rate > 0).then_some(max_fee_rate))
}

fn parse_max_burn_amount(value: Option<&Value>) -> Result<u64> {
    Ok(value
        .filter(|value| !value.is_null())
        .map(|value| parse_btc_amount(value, "maxburnamount"))
        .transpose()?
        .unwrap_or(Amount::ZERO)
        .to_sat())
}

fn script_has_valid_ops(script: &bitcoin::Script) -> bool {
    script.instructions().all(|instruction| match instruction {
        Ok(Instruction::Op(opcode)) => opcode.to_u8() <= MAX_OPCODE,
        Ok(Instruction::PushBytes(bytes)) => bytes.len() <= MAX_SCRIPT_ELEMENT_SIZE,
        Err(_) => false,
    })
}

fn script_is_unspendable(script: &bitcoin::Script) -> bool {
    script.is_op_return() || script.len() > MAX_SCRIPT_SIZE
}

fn validate_burn_amount(transaction: &Transaction, max_burn_amount: u64) -> Result<()> {
    if transaction.output.iter().any(|output| {
        (script_is_unspendable(&output.script_pubkey)
            || !script_has_valid_ops(&output.script_pubkey))
            && output.value.to_sat() > max_burn_amount
    }) {
        bail!("Unspendable output exceeds maximum configured by user (maxburnamount)")
    }
    Ok(())
}

fn enforce_max_fee_rate(
    node: &Arc<Node>,
    transaction: &Transaction,
    max_fee_rate: Option<u64>,
) -> Result<()> {
    let Some(max_fee_rate) = max_fee_rate else {
        return Ok(());
    };
    if node
        .mempool
        .read()
        .get(&transaction.compute_txid())
        .is_some()
    {
        // BroadcastTransaction reannounces an existing mempool transaction
        // before applying the caller's maxfeerate sanity check.
        return Ok(());
    }
    let chain = node.chain.read();
    let mut candidate = node.mempool.read().clone();
    let txid = candidate.accept(transaction.clone(), &chain)?;
    let entry = candidate
        .get(&txid)
        .ok_or_else(|| anyhow!("accepted transaction disappeared"))?;
    if exceeds_max_fee(entry.fee_sat, entry.vsize, Some(max_fee_rate)) {
        bail!("Fee exceeds maximum configured by user (e.g. maxfeerate)")
    }
    Ok(())
}

struct SigningPrevout {
    output: TxOut,
    amount_provided: bool,
    redeem_script: Option<ScriptBuf>,
    witness_script: Option<ScriptBuf>,
}

fn sign_raw_transaction_with_key(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let bytes = hex::decode(param::<String>(params, 0)?).context("TX decode failed")?;
    let mut transaction: Transaction = deserialize(&bytes)
        .context("TX decode failed. Make sure the tx has at least one input.")?;
    let private_keys = params
        .get(1)
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("private keys must be an array"))?
        .iter()
        .map(|value| {
            let wif = value
                .as_str()
                .ok_or_else(|| anyhow!("private keys must be WIF strings"))?;
            bitcoin::PrivateKey::from_wif(wif)
                .map_err(|error| anyhow!("private key decode failed: {error}"))
        })
        .collect::<Result<Vec<_>>>()?;
    let prevouts = parse_signing_prevouts(params.get(2))?;
    let sighash_name = optional_str(params, 3, "DEFAULT", "sighashtype")?;
    let sighash_type = parse_raw_sighash_type(sighash_name)?;
    let mut prevouts = prevouts;
    for prevout in prevouts.values() {
        signing_script_context(prevout)?;
    }
    {
        let chain = node.chain.read();
        let mempool = node.mempool.read();
        for (outpoint, prevout) in &prevouts {
            if let Some(actual) = output_for_outpoint(&chain, &mempool, *outpoint)
                && actual.script_pubkey != prevout.output.script_pubkey
            {
                bail!("Previous output scriptPubKey mismatch")
            }
        }
        for input in &transaction.input {
            if prevouts.contains_key(&input.previous_output) {
                continue;
            }
            if let Some(output) = output_for_outpoint(&chain, &mempool, input.previous_output) {
                prevouts.insert(
                    input.previous_output,
                    SigningPrevout {
                        output,
                        amount_provided: true,
                        redeem_script: None,
                        witness_script: None,
                    },
                );
            }
        }
    }
    let previous_outputs = transaction
        .input
        .iter()
        .map(|input| {
            prevouts
                .get(&input.previous_output)
                .map(|prevout| prevout.output.clone())
        })
        .collect::<Option<Vec<_>>>();
    let secp = Secp256k1::new();
    let mut errors = Vec::new();
    for input_index in 0..transaction.input.len() {
        let input = &transaction.input[input_index];
        let Some(prevout) = prevouts.get(&input.previous_output) else {
            errors.push(signing_error(
                &transaction,
                input_index,
                "missing prevtx metadata",
            ));
            continue;
        };
        if !prevout.amount_provided
            && (prevout.output.script_pubkey.is_witness_program()
                || prevout.witness_script.is_some()
                || prevout
                    .redeem_script
                    .as_ref()
                    .is_some_and(|script| script.is_witness_program()))
            && !is_p2a_script(&prevout.output.script_pubkey)
        {
            bail!("Missing amount")
        }
        if let Err(error) = sign_transaction_input(
            &mut transaction,
            input_index,
            prevout,
            &private_keys,
            &secp,
            sighash_type,
            previous_outputs.as_deref(),
        ) {
            errors.push(signing_error(&transaction, input_index, &error.to_string()));
        }
    }
    let complete = errors.is_empty()
        && previous_outputs
            .as_ref()
            .is_some_and(|outputs| outputs.len() == transaction.input.len())
        && validation::validate_transaction_scripts(
            node.config.network,
            node.chain.read().height().saturating_add(1),
            &transaction,
            previous_outputs.as_deref().unwrap_or_default(),
        )
        .is_ok();
    let mut result = json!({
        "hex": hex::encode(serialize(&transaction)),
        "complete": complete,
    });
    if !errors.is_empty() {
        result["errors"] = json!(errors);
    }
    Ok(result)
}

fn parse_raw_sighash_type(value: &str) -> Result<DescriptorSighashType> {
    let (ecdsa, taproot) = match value {
        "DEFAULT" => (EcdsaSighashType::All, TapSighashType::Default),
        "ALL" => (EcdsaSighashType::All, TapSighashType::All),
        "NONE" => (EcdsaSighashType::None, TapSighashType::None),
        "SINGLE" => (EcdsaSighashType::Single, TapSighashType::Single),
        "ALL|ANYONECANPAY" => (
            EcdsaSighashType::AllPlusAnyoneCanPay,
            TapSighashType::AllPlusAnyoneCanPay,
        ),
        "NONE|ANYONECANPAY" => (
            EcdsaSighashType::NonePlusAnyoneCanPay,
            TapSighashType::NonePlusAnyoneCanPay,
        ),
        "SINGLE|ANYONECANPAY" => (
            EcdsaSighashType::SinglePlusAnyoneCanPay,
            TapSighashType::SinglePlusAnyoneCanPay,
        ),
        _ => bail!("'{value}' is not a valid sighash parameter."),
    };
    Ok(DescriptorSighashType { ecdsa, taproot })
}

fn parse_signing_prevouts(value: Option<&Value>) -> Result<HashMap<OutPoint, SigningPrevout>> {
    let Some(value) = value.filter(|value| !value.is_null()) else {
        return Ok(HashMap::new());
    };
    let entries = value
        .as_array()
        .ok_or_else(|| anyhow!("prevtxs must be an array"))?;
    entries
        .iter()
        .map(|entry| {
            let txid: Txid = entry
                .get("txid")
                .and_then(Value::as_str)
                .ok_or_else(|| anyhow!("prevtx txid is missing"))?
                .parse()?;
            let vout_value = entry
                .get("vout")
                .ok_or_else(|| anyhow!("prevtx vout is missing"))?;
            if vout_value.as_i64().is_some_and(|vout| vout < 0) {
                bail!("vout cannot be negative")
            }
            let vout = vout_value
                .as_u64()
                .ok_or_else(|| anyhow!("prevtx vout is missing"))?;
            let vout = u32::try_from(vout).map_err(|_| anyhow!("prevtx vout is out of range"))?;
            let script = entry
                .get("scriptPubKey")
                .and_then(Value::as_str)
                .ok_or_else(|| anyhow!("prevtx scriptPubKey is missing"))?;
            let amount = entry
                .get("amount")
                .filter(|value| !value.is_null())
                .map(|value| parse_btc_amount(value, "prevtx amount"))
                .transpose()?
                .unwrap_or(Amount::ZERO);
            if amount > Amount::MAX_MONEY {
                bail!("Amount out of range")
            }
            let redeem_script = entry
                .get("redeemScript")
                .filter(|value| !value.is_null())
                .map(|value| -> Result<ScriptBuf> {
                    let script = value
                        .as_str()
                        .ok_or_else(|| anyhow!("prevtx redeemScript must be a string"))?;
                    Ok(ScriptBuf::from_bytes(hex::decode(script)?))
                })
                .transpose()?;
            let witness_script = entry
                .get("witnessScript")
                .filter(|value| !value.is_null())
                .map(|value| -> Result<ScriptBuf> {
                    let script = value
                        .as_str()
                        .ok_or_else(|| anyhow!("prevtx witnessScript must be a string"))?;
                    Ok(ScriptBuf::from_bytes(hex::decode(script)?))
                })
                .transpose()?;
            Ok((
                OutPoint::new(txid, vout),
                SigningPrevout {
                    output: TxOut {
                        value: amount,
                        script_pubkey: ScriptBuf::from_bytes(hex::decode(script)?),
                    },
                    amount_provided: entry.get("amount").is_some_and(|value| !value.is_null()),
                    redeem_script,
                    witness_script,
                },
            ))
        })
        .collect()
}

struct SigningScriptContext {
    script: ScriptBuf,
    segwit: bool,
    redeem_script: Option<ScriptBuf>,
}

fn signing_script_context(prevout: &SigningPrevout) -> Result<SigningScriptContext> {
    let output = &prevout.output.script_pubkey;
    if output.is_p2sh() {
        let script = prevout
            .witness_script
            .as_ref()
            .or(prevout.redeem_script.as_ref())
            .ok_or_else(|| anyhow!("Missing redeemScript/witnessScript"))?;
        let witness_output_script = ScriptBuf::new_p2wsh(&script.wscript_hash());

        if let (Some(redeem_script), Some(witness_script)) =
            (&prevout.redeem_script, &prevout.witness_script)
            && redeem_script != witness_script
            && *redeem_script != witness_output_script
        {
            bail!("redeemScript does not correspond to witnessScript")
        }

        let traditional_output = ScriptBuf::new_p2sh(&script.script_hash());
        if *output == traditional_output {
            return Ok(SigningScriptContext {
                script: script.clone(),
                segwit: script.is_witness_program(),
                redeem_script: Some(script.clone()),
            });
        }

        let nested_output = ScriptBuf::new_p2sh(&witness_output_script.script_hash());
        if *output == nested_output {
            return Ok(SigningScriptContext {
                script: script.clone(),
                segwit: true,
                redeem_script: Some(witness_output_script),
            });
        }

        bail!("redeemScript/witnessScript does not match scriptPubKey")
    }

    if output.is_p2wsh() {
        let script = prevout
            .witness_script
            .as_ref()
            .or(prevout.redeem_script.as_ref())
            .ok_or_else(|| anyhow!("Missing redeemScript/witnessScript"))?;
        if let (Some(redeem_script), Some(witness_script)) =
            (&prevout.redeem_script, &prevout.witness_script)
            && redeem_script != witness_script
            && *redeem_script != ScriptBuf::new_p2wsh(&witness_script.wscript_hash())
        {
            bail!("redeemScript does not correspond to witnessScript")
        }
        if ScriptBuf::new_p2wsh(&script.wscript_hash()) != *output {
            bail!("redeemScript/witnessScript does not match scriptPubKey")
        }
        return Ok(SigningScriptContext {
            script: script.clone(),
            segwit: true,
            redeem_script: None,
        });
    }

    Ok(SigningScriptContext {
        script: output.clone(),
        segwit: output.is_witness_program(),
        redeem_script: None,
    })
}

fn sign_transaction_input(
    transaction: &mut Transaction,
    input_index: usize,
    prevout: &SigningPrevout,
    private_keys: &[bitcoin::PrivateKey],
    secp: &Secp256k1<bitcoin::secp256k1::All>,
    sighash_type: DescriptorSighashType,
    previous_outputs: Option<&[TxOut]>,
) -> Result<()> {
    let context = signing_script_context(prevout)?;
    let signing_script = &context.script;
    let segwit = context.segwit;
    let nested = context.redeem_script.is_some();

    if is_p2a_script(signing_script) {
        return Ok(());
    }

    if signing_script.is_p2tr() {
        let previous_outputs = previous_outputs
            .filter(|outputs| outputs.len() == transaction.input.len())
            .ok_or_else(|| anyhow!("missing prevtx metadata"))?;
        let key = private_keys
            .iter()
            .find(|key| key_matches_script(key, signing_script, secp))
            .ok_or_else(|| anyhow!("no private key matches the prevout script"))?;
        let sighash = SighashCache::new(&*transaction).taproot_key_spend_signature_hash(
            input_index,
            &Prevouts::All(previous_outputs),
            sighash_type.taproot,
        )?;
        let keypair = bitcoin::secp256k1::Keypair::from_secret_key(secp, &key.inner);
        let signature = secp.sign_schnorr_no_aux_rand(&Message::from(sighash), &keypair);
        let signature = bitcoin::taproot::Signature {
            signature,
            sighash_type: sighash_type.taproot,
        };
        transaction.input[input_index].witness = Witness::p2tr_key_spend(&signature);
        if nested {
            let redeem_script = context
                .redeem_script
                .as_ref()
                .expect("nested signing context has a redeem script");
            transaction.input[input_index].script_sig =
                push_script_items(&[redeem_script.to_bytes()])?;
        }
        return Ok(());
    }

    let sighash_type = sighash_type.ecdsa;
    let message = if signing_script.is_p2wpkh() {
        Message::from(SighashCache::new(&*transaction).p2wpkh_signature_hash(
            input_index,
            signing_script,
            prevout.output.value,
            sighash_type,
        )?)
    } else if segwit {
        Message::from(SighashCache::new(&*transaction).p2wsh_signature_hash(
            input_index,
            signing_script,
            prevout.output.value,
            sighash_type,
        )?)
    } else {
        Message::from(SighashCache::new(&*transaction).legacy_signature_hash(
            input_index,
            signing_script,
            sighash_type.to_u32(),
        )?)
    };

    let signature_for_key = |key: &bitcoin::PrivateKey| {
        let signature = secp.sign_ecdsa(&message, &key.inner);
        let mut bytes = signature.serialize_der().to_vec();
        bytes.push(sighash_type.to_u32() as u8);
        Ok::<_, anyhow::Error>(bytes)
    };

    if let Some((required, public_keys)) = multisig_script_keys(signing_script) {
        let mut signatures = Vec::new();
        for public_key in public_keys {
            let Some(key) = private_keys
                .iter()
                .find(|key| key.public_key(secp) == public_key)
            else {
                continue;
            };
            signatures.push(signature_for_key(key)?);
            if signatures.len() == required {
                break;
            }
        }
        if signatures.is_empty() {
            bail!("no private key matches the multisig script")
        }
        let mut items = vec![Vec::new()];
        items.extend(signatures);
        if segwit {
            items.push(signing_script.to_bytes());
            transaction.input[input_index].witness = Witness::from_slice(&items);
            if nested {
                let redeem_script = context
                    .redeem_script
                    .as_ref()
                    .expect("nested signing context has a redeem script");
                transaction.input[input_index].script_sig =
                    push_script_items(&[redeem_script.to_bytes()])?;
            }
        } else {
            if nested {
                items.push(signing_script.to_bytes());
            }
            transaction.input[input_index].script_sig = push_script_items(&items)?;
        }
        return Ok(());
    }

    let key = private_keys
        .iter()
        .find(|key| key_matches_script(key, signing_script, secp))
        .ok_or_else(|| anyhow!("no private key matches the prevout script"))?;
    let signature = signature_for_key(key)?;
    if signing_script.is_p2wpkh() {
        let public_key = key.public_key(secp);
        transaction.input[input_index].witness =
            Witness::from_slice(&[signature, public_key.to_bytes()]);
        if nested {
            let redeem_script = context
                .redeem_script
                .as_ref()
                .expect("nested signing context has a redeem script");
            transaction.input[input_index].script_sig =
                push_script_items(&[redeem_script.to_bytes()])?;
        }
    } else if segwit {
        let mut items = vec![signature];
        if signing_script.is_p2pkh() {
            items.push(key.public_key(secp).to_bytes());
        } else if !signing_script.is_p2pk() {
            bail!("unsupported witnessScript template")
        }
        items.push(signing_script.to_bytes());
        transaction.input[input_index].witness = Witness::from_slice(&items);
        if nested {
            let redeem_script = context
                .redeem_script
                .as_ref()
                .expect("nested signing context has a redeem script");
            transaction.input[input_index].script_sig =
                push_script_items(&[redeem_script.to_bytes()])?;
        }
    } else if signing_script.is_p2pkh() || signing_script.is_p2pk() {
        let mut items = vec![signature];
        if !signing_script.is_p2pk() {
            items.push(key.public_key(secp).to_bytes());
        }
        if nested {
            items.push(
                context
                    .redeem_script
                    .as_ref()
                    .expect("nested signing context has a redeem script")
                    .to_bytes(),
            );
        }
        transaction.input[input_index].script_sig = push_script_items(&items)?;
    } else {
        bail!("unsupported signing script template")
    }
    Ok(())
}

fn key_matches_script(
    key: &bitcoin::PrivateKey,
    script: &bitcoin::Script,
    secp: &Secp256k1<bitcoin::secp256k1::All>,
) -> bool {
    let public_key = key.public_key(secp);
    if script.is_p2pkh() {
        Address::p2pkh(public_key, Network::Bitcoin)
            .script_pubkey()
            .as_script()
            == script
            || Address::p2pkh(public_key, Network::Testnet)
                .script_pubkey()
                .as_script()
                == script
    } else if script.is_p2wpkh() {
        bitcoin::CompressedPublicKey::try_from(public_key).is_ok_and(|public_key| {
            Address::p2wpkh(&public_key, Network::Bitcoin)
                .script_pubkey()
                .as_script()
                == script
                || Address::p2wpkh(&public_key, Network::Testnet)
                    .script_pubkey()
                    .as_script()
                    == script
        })
    } else if script.is_p2pk() {
        Builder::new()
            .push_key(&public_key)
            .push_opcode(bitcoin::blockdata::opcodes::all::OP_CHECKSIG)
            .into_script()
            .as_script()
            == script
    } else if script.is_p2tr() {
        key.compressed
            && script
                .as_bytes()
                .get(2..)
                .and_then(|bytes| bitcoin::XOnlyPublicKey::from_slice(bytes).ok())
                .is_some_and(|output_key| bitcoin::XOnlyPublicKey::from(public_key) == output_key)
    } else {
        false
    }
}

fn signing_error(transaction: &Transaction, input_index: usize, error: &str) -> Value {
    let input = &transaction.input[input_index];
    json!({
        "txid": transaction.compute_txid().to_string(),
        "vout": input.previous_output.vout,
        "witness": input
            .witness
            .to_vec()
            .into_iter()
            .map(hex::encode)
            .collect::<Vec<_>>(),
        "scriptSig": hex::encode(input.script_sig.as_bytes()),
        "sequence": input.sequence.to_consensus_u32(),
        "error": error,
    })
}

fn submit_block(node: &Arc<Node>, params: &Value) -> Result<Value> {
    if let Some(dummy) = params.get(1).filter(|value| !value.is_null())
        && !dummy.is_string()
    {
        bail!("dummy must be a string")
    }
    let bytes = hex::decode(param::<String>(params, 0)?)?;
    let mut block: bitcoin::Block = deserialize(&bytes)?;
    node.chain
        .read()
        .update_uncommitted_block_structures(&mut block);
    let hash = block.block_hash();
    if let Some(status) = node.chain.read().proposal_duplicate_status(&hash)
        && status != "duplicate-inconclusive"
    {
        return Ok(json!(status));
    }
    let result = node.connect_block(block);
    match result {
        Ok(_) => Ok(Value::Null),
        Err(error) => {
            debug!(%hash, %error, "submitblock rejected");
            let message = error.to_string();
            if message.contains("unknown parent")
                || message.contains("parent whose full body is unavailable")
            {
                Ok(json!("inconclusive"))
            } else if message.contains("invalidated branch") {
                Ok(json!("duplicate-invalid"))
            } else if let Some(reason) = bip22_validation_result(&error) {
                Ok(reason)
            } else {
                Ok(json!(message))
            }
        }
    }
}

fn bip22_validation_result(error: &anyhow::Error) -> Option<Value> {
    error
        .downcast_ref::<validation::ValidationError>()
        .map(|error| json!(error.bip22_reject_reason()))
}

fn generate_to_address(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let count = param::<i64>(params, 0)?;
    if count < 0 {
        bail!("nblocks must not be negative");
    }
    let address = param::<String>(params, 1)?
        .parse::<Address<bitcoin::address::NetworkUnchecked>>()?
        .require_network(node.config.network)?;
    let max_tries = optional_i64(params, 2, 1_000_000, "maxtries")?;
    if max_tries < 0 {
        bail!("maxtries must not be negative");
    }
    let max_tries = u64::try_from(max_tries).map_err(|_| anyhow!("maxtries is out of range"))?;
    generate_blocks_to_script(node, address.script_pubkey(), count, max_tries)
}

fn generate_to_descriptor(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let count = param::<i64>(params, 0)?;
    if count < 0 {
        bail!("nblocks must not be negative");
    }
    let descriptor = param::<String>(params, 1)?;
    let script = mining_descriptor_script(node, &descriptor)?;
    let max_tries = optional_i64(params, 2, 1_000_000, "maxtries")?;
    if max_tries < 0 {
        bail!("maxtries must not be negative");
    }
    let max_tries = u64::try_from(max_tries).map_err(|_| anyhow!("maxtries is out of range"))?;
    generate_blocks_to_script(node, script, count, max_tries)
}

fn generate_blocks_to_script(
    node: &Arc<Node>,
    script_pubkey: ScriptBuf,
    count: i64,
    max_tries: u64,
) -> Result<Value> {
    let mut hashes = Vec::with_capacity(usize::try_from(count).unwrap_or_default());
    for _ in 0..count {
        let block = build_mining_block(node, script_pubkey.clone())?;
        let Some(block) = mine_block(block, max_tries) else {
            break;
        };
        let hash = block.block_hash();
        node.connect_block(block)?;
        hashes.push(hash.to_string());
    }
    Ok(json!(hashes))
}

fn generate_block(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let output = param::<String>(params, 0)?;
    let output_script = mining_descriptor_script(node, &output).or_else(|_| {
        output
            .parse::<Address<bitcoin::address::NetworkUnchecked>>()?
            .require_network(node.config.network)
            .map(|address| address.script_pubkey())
            .map_err(anyhow::Error::from)
    })?;
    let requested = params
        .get(1)
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("transactions must be an array"))?;
    let submit = optional_bool(params, 2, true, "submit")?;
    let mempool = node.mempool.read();
    let transactions = requested
        .iter()
        .map(|value| {
            let text = value
                .as_str()
                .ok_or_else(|| anyhow!("transactions must contain hex strings or txids"))?;
            if let Ok(txid) = text.parse::<Txid>() {
                return mempool
                    .get(&txid)
                    .map(|entry| entry.transaction.clone())
                    .ok_or_else(|| anyhow!("Transaction {txid} not in mempool"));
            }
            let bytes = hex::decode(text)
                .with_context(|| format!("transaction decode failed for {text}"))?;
            deserialize(&bytes).context("transaction decode failed")
        })
        .collect::<Result<Vec<Transaction>>>()?;
    drop(mempool);

    let block = build_mining_block_with_transactions(node, output_script, transactions)?;
    let Some(block) = mine_block(block, 1_000_000) else {
        bail!("failed to make block")
    };
    node.chain.read().validate_candidate_block(&block)?;
    let hash = block.block_hash();
    let serialized = (!submit).then(|| hex::encode(serialize(&block)));
    if submit {
        node.connect_block(block)?;
    }
    let mut result = json!({"hash": hash.to_string()});
    if let Some(serialized) = serialized {
        result["hex"] = json!(serialized);
    }
    Ok(result)
}

fn build_mining_block(node: &Arc<Node>, script_pubkey: ScriptBuf) -> Result<Block> {
    let mempool = node.mempool.read();
    let mut transactions = Vec::new();
    let mut transaction_weight = 0u64;
    for txid in mempool.mining_order_with_min_fee(
        node.config.block_max_weight,
        node.config.block_reserved_weight,
        node.config.block_min_tx_fee_sat_per_kvb,
    ) {
        let Some(entry) = mempool.get(&txid) else {
            continue;
        };
        let next_weight = transaction_weight.saturating_add(entry.transaction.weight().to_wu());
        if next_weight.saturating_add(node.config.block_reserved_weight)
            > node.config.block_max_weight
        {
            break;
        }
        transaction_weight = next_weight;
        transactions.push(entry.transaction.clone());
    }
    drop(mempool);
    build_mining_block_with_transactions(node, script_pubkey, transactions)
}

fn build_mining_block_with_transactions(
    node: &Arc<Node>,
    script_pubkey: ScriptBuf,
    transactions: Vec<Transaction>,
) -> Result<Block> {
    let chain = node.chain.read();
    let tip = chain.tip();
    let parent = chain
        .header(tip.height)
        .copied()
        .ok_or_else(|| anyhow!("active tip header is unavailable"))?;
    let height = tip.height.saturating_add(1);
    let now = u32::try_from(crate::time::unix_time()).unwrap_or(u32::MAX);
    let time = now
        .max(parent.time.saturating_add(1))
        .max(chain.median_time_past_value().saturating_add(1));
    let bits = chain.next_bits(time);
    let network = chain.network;
    let version = mining_block_version(
        network,
        chain.active_headers(),
        tip.height,
        node.config.block_version,
    );
    let mempool = node.mempool.read();
    let mut created = HashMap::new();
    let mut fees = 0u64;
    for transaction in &transactions {
        if transaction.is_coinbase() {
            bail!("coinbase transactions are not allowed in generateblock")
        }
        let mut input_total = 0u64;
        for input in &transaction.input {
            let output = created
                .get(&input.previous_output)
                .cloned()
                .or_else(|| {
                    chain
                        .utxo(&input.previous_output)
                        .map(|entry| entry.output.clone())
                })
                .or_else(|| {
                    mempool
                        .get(&input.previous_output.txid)
                        .and_then(|entry| {
                            entry
                                .transaction
                                .output
                                .get(input.previous_output.vout as usize)
                        })
                        .cloned()
                })
                .ok_or_else(|| anyhow!("transaction input {} is missing", input.previous_output))?;
            input_total = input_total
                .checked_add(output.value.to_sat())
                .ok_or_else(|| anyhow!("transaction input total overflow"))?;
        }
        let output_total = transaction
            .output
            .iter()
            .try_fold(0u64, |total, output| {
                total.checked_add(output.value.to_sat())
            })
            .ok_or_else(|| anyhow!("transaction output total overflow"))?;
        if output_total > input_total {
            bail!("transaction spends more than its inputs")
        }
        fees = fees
            .checked_add(input_total - output_total)
            .ok_or_else(|| anyhow!("block fee total overflow"))?;
        let txid = transaction.compute_txid();
        for (vout, output) in transaction.output.iter().enumerate() {
            created.insert(OutPoint::new(txid, vout as u32), output.clone());
        }
    }
    drop(mempool);
    let block = mining_block(MiningBlockTemplate {
        network,
        parent,
        height,
        time,
        bits,
        script_pubkey,
        transactions,
        fees,
        extra_nonce: random(),
        version: Some(version),
    })?;
    if block.weight().to_wu() > node.config.block_max_weight {
        bail!("generated block exceeds the block weight limit")
    }
    node.record_mining_block(&block);
    Ok(block)
}

struct MiningBlockTemplate {
    network: Network,
    parent: Header,
    height: u32,
    time: u32,
    bits: u32,
    script_pubkey: ScriptBuf,
    transactions: Vec<Transaction>,
    fees: u64,
    extra_nonce: u32,
    version: Option<i32>,
}

fn mining_block(template: MiningBlockTemplate) -> Result<Block> {
    let MiningBlockTemplate {
        network,
        parent,
        height,
        time,
        bits,
        script_pubkey,
        transactions,
        fees,
        extra_nonce,
        version,
    } = template;
    let segwit_active = height >= validation::buried_deployment_heights(network).segwit;
    let mut coinbase = Transaction {
        version: Version::ONE,
        lock_time: LockTime::from_consensus(height.saturating_sub(1)),
        input: vec![TxIn {
            previous_output: OutPoint::null(),
            script_sig: Builder::new()
                .push_int(i64::from(height))
                .push_slice(extra_nonce.to_le_bytes())
                .into_script(),
            sequence: bitcoin::Sequence::MAX,
            witness: Witness::default(),
        }],
        output: vec![TxOut {
            value: Amount::from_sat(
                validation::block_subsidy_for_network(network, height).saturating_add(fees),
            ),
            script_pubkey,
        }],
    };
    if segwit_active {
        coinbase.input[0].witness = Witness::from_slice(&[vec![0u8; 32]]);
    }
    let mut block = Block {
        header: Header {
            version: BlockVersion::from_consensus(version.unwrap_or(0x2000_0000)),
            prev_blockhash: parent.block_hash(),
            merkle_root: bitcoin::TxMerkleNode::all_zeros(),
            time,
            bits: bitcoin::pow::CompactTarget::from_consensus(bits),
            nonce: 0,
        },
        txdata: std::iter::once(coinbase).chain(transactions).collect(),
    };
    if segwit_active {
        let witness_root = block
            .witness_root()
            .ok_or_else(|| anyhow!("cannot calculate witness merkle root"))?;
        let commitment = Block::compute_witness_commitment(&witness_root, &[0u8; 32]);
        let mut script = vec![0x6a, 0x24, 0xaa, 0x21, 0xa9, 0xed];
        script.extend_from_slice(&commitment.to_byte_array());
        block.txdata[0].output.push(TxOut {
            value: Amount::ZERO,
            script_pubkey: ScriptBuf::from_bytes(script),
        });
    }
    block.header.merkle_root = block
        .compute_merkle_root()
        .ok_or_else(|| anyhow!("cannot calculate transaction merkle root"))?;
    Ok(block)
}

fn mining_block_version(
    network: Network,
    headers: &[Header],
    tip_height: u32,
    custom_version: Option<i32>,
) -> i32 {
    // Core only applies -blockversion on regtest, where it is a deliberate
    // fork-testing hook. Other networks retain the versionbits-computed
    // default even if the option was supplied.
    let custom_version = (network == Network::Regtest)
        .then_some(custom_version)
        .flatten();
    let mut version = custom_version.unwrap_or(0x2000_0000);
    if custom_version.is_none() {
        for deployment in validation::bip9_deployments(network) {
            let (state, _) = bip9_state_at_height(headers, deployment, tip_height);
            if matches!(state, Bip9State::Started | Bip9State::LockedIn) {
                version |= 1i32 << deployment.bit;
            }
        }
    }
    version
}

fn mine_block(mut block: Block, max_tries: u64) -> Option<Block> {
    let mut tries = 0u64;
    while tries < max_tries {
        if block.header.target().is_met_by(block.block_hash()) {
            return Some(block);
        }
        if block.header.nonce == u32::MAX {
            return None;
        }
        block.header.nonce = block.header.nonce.saturating_add(1);
        tries = tries.saturating_add(1);
    }
    None
}

fn ensure_get_block_template_ready(node: &Arc<Node>) -> Result<()> {
    if node.config.network != Network::Bitcoin {
        return Ok(());
    }
    if node.peer_count() == 0 {
        bail!("Bitcoin Core is not connected!")
    }
    let initial_block_download = {
        let chain = node.chain.read();
        chain.is_initial_block_download()
    };
    if initial_block_download {
        bail!("Bitcoin Core is in initial sync and waiting for blocks...")
    }
    Ok(())
}

fn get_block_template(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let request = params
        .get(0)
        .filter(|value| !value.is_null())
        .cloned()
        .unwrap_or_else(|| json!({}));
    let request = request
        .as_object()
        .ok_or_else(|| anyhow!("getblocktemplate request must be an object"))?;
    let mode = request
        .get("mode")
        .filter(|value| !value.is_null())
        .map(|value| {
            value
                .as_str()
                .ok_or_else(|| anyhow!("getblocktemplate mode must be a string"))
        })
        .transpose()?
        .unwrap_or("template");
    if mode == "proposal" {
        let data = request
            .get("data")
            .and_then(Value::as_str)
            .ok_or_else(|| anyhow!("proposal mode requires a data string"))?;
        let bytes = hex::decode(data).context("block decode failed")?;
        let block: Block = deserialize(&bytes).context("block decode failed")?;
        let chain = node.chain.read();
        if let Some(status) = chain.proposal_duplicate_status(&block.block_hash()) {
            return Ok(json!(status));
        }
        if let Err(error) = chain.validate_candidate_block_without_pow(&block) {
            if let Some(reason) = bip22_validation_result(&error) {
                return Ok(reason);
            }
            return Err(error);
        }
        return Ok(Value::Null);
    }
    if mode != "template" {
        bail!("invalid getblocktemplate mode")
    }
    ensure_get_block_template_ready(node)?;
    let requested_rules = match request.get("rules").filter(|value| !value.is_null()) {
        None => Vec::new(),
        Some(value) => value
            .as_array()
            .ok_or_else(|| anyhow!("getblocktemplate rules must be an array"))?
            .iter()
            .map(|rule| {
                rule.as_str()
                    .ok_or_else(|| anyhow!("getblocktemplate rules must contain strings"))
            })
            .collect::<Result<Vec<_>>>()?,
    };
    if !requested_rules.contains(&"segwit") {
        bail!(
            "{}",
            "getblocktemplate must be called with the segwit rule set (call with {\"rules\": [\"segwit\"]})"
        )
    }
    if node.config.network == Network::Signet && !requested_rules.contains(&"signet") {
        bail!(
            "{}",
            "getblocktemplate must be called with the signet rule set (call with {\"rules\": [\"segwit\", \"signet\"]})"
        )
    }
    let chain = node.chain.read();
    let tip = chain.tip();
    let parent = chain.header(tip.height).expect("tip header exists");
    let height = tip.height + 1;
    let segwit_active = height >= validation::buried_deployment_heights(chain.network).segwit;
    let now = crate::time::unix_time() as u32;
    let mintime = minimum_block_time(
        chain.network,
        parent,
        height,
        chain.median_time_past_value(),
    );
    let curtime = now.max(mintime);
    let bits = chain.next_bits(curtime);
    let mempool = node.mempool.read();
    let mut fees = 0u64;
    let selected = mempool.mining_order_with_min_fee(
        node.config.block_max_weight,
        node.config.block_reserved_weight,
        node.config.block_min_tx_fee_sat_per_kvb,
    );
    let positions = selected
        .iter()
        .enumerate()
        .map(|(index, txid)| (*txid, index + 1))
        .collect::<HashMap<_, _>>();
    let transactions = selected
        .iter()
        .filter_map(|txid| mempool.get(txid).map(|entry| (txid, entry)))
        .map(|(txid, entry)| {
            let transaction = &entry.transaction;
            let wtxid = transaction.compute_wtxid();
            fees = fees.saturating_add(entry.fee_sat);
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
                }) / if segwit_active { 1 } else { 4 },
                "weight": transaction.weight().to_wu(),
            })
        })
        .collect::<Vec<_>>();
    let selected_transactions = selected
        .iter()
        .filter_map(|txid| mempool.get(txid).map(|entry| entry.transaction.clone()))
        .collect::<Vec<_>>();
    let headers = chain.active_headers();
    let version = mining_block_version(
        chain.network,
        headers,
        tip.height,
        node.config.block_version,
    );
    let template_block = mining_block(MiningBlockTemplate {
        network: chain.network,
        parent: *parent,
        height,
        time: curtime,
        bits,
        script_pubkey: ScriptBuf::new(),
        transactions: selected_transactions,
        fees,
        extra_nonce: 0,
        version: Some(version),
    })?;
    node.record_mining_block(&template_block);
    let default_witness_commitment = segwit_active.then(|| {
        template_block
            .txdata
            .first()
            .and_then(|coinbase| coinbase.output.last())
            .map(|output| hex::encode(output.script_pubkey.as_bytes()))
            .unwrap_or_default()
    });
    let coinbase_value =
        validation::block_subsidy_for_network(chain.network, height).saturating_add(fees);
    let mut rules = vec!["csv"];
    if segwit_active {
        rules.push("!segwit");
    }
    if chain.network == Network::Signet {
        rules.push("!signet");
    }
    let [testdummy, taproot] = validation::bip9_deployments(chain.network);
    let mut vbavailable = serde_json::Map::new();
    for (name, deployment) in [("testdummy", testdummy), ("taproot", taproot)] {
        let (state, _) = bip9_state_at_height(headers, deployment, tip.height);
        match state {
            Bip9State::Started | Bip9State::LockedIn => {
                vbavailable.insert(name.to_owned(), json!(deployment.bit));
            }
            Bip9State::Active => rules.push(name),
            Bip9State::Defined | Bip9State::Failed => {}
        }
    }
    let mut result = json!({
        "capabilities": ["proposal"],
        "version": version,
        "rules": rules,
        "vbavailable": vbavailable,
        "vbrequired": 0,
        "previousblockhash": tip.hash.to_string(),
        "transactions": transactions,
        "coinbaseaux": {},
        "coinbasevalue": coinbase_value,
        "target": format!("{:064x}", bitcoin::pow::Target::from_compact(bitcoin::pow::CompactTarget::from_consensus(bits))),
        "mintime": mintime,
        "curtime": curtime,
        "mutable": ["time", "transactions", "prevblock"],
        "noncerange": "00000000ffffffff",
        "sigoplimit": if segwit_active {
            validation::MAX_BLOCK_SIGOP_COST
        } else {
            validation::MAX_BLOCK_SIGOP_COST / 4
        },
        "sizelimit": if segwit_active {
            validation::MAX_BLOCK_SERIALIZED_SIZE
        } else {
            validation::MAX_BLOCK_SERIALIZED_SIZE / 4
        },
        "curtime": curtime,
        "longpollid": format!("{}{}", tip.hash, mempool.sequence()),
        "height": height,
        "bits": format!("{:08x}", bits),
    });
    if let Some(default_witness_commitment) = default_witness_commitment {
        result["default_witness_commitment"] = json!(default_witness_commitment);
    }
    if let Some(challenge) = chain.signet_challenge() {
        result["signet_challenge"] = json!(hex::encode(challenge));
    }
    if segwit_active {
        result["weightlimit"] = json!(validation::MAX_BLOCK_WEIGHT);
    }
    Ok(result)
}

async fn get_block_template_async(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let request = params
        .get(0)
        .filter(|value| !value.is_null())
        .and_then(Value::as_object);
    let longpoll_id = request
        .filter(|request| request.get("mode").and_then(Value::as_str) != Some("proposal"))
        .and_then(|request| request.get("longpollid"))
        .and_then(Value::as_str);
    if request
        .and_then(|request| request.get("mode"))
        .and_then(Value::as_str)
        != Some("proposal")
    {
        ensure_get_block_template_ready(node)?;
    }
    if let Some(longpoll_id) = longpoll_id {
        let mut chain_events = node.subscribe_chain();
        let mut mempool_events = node.subscribe_mempool();
        loop {
            if current_block_template_longpoll_id(node) != longpoll_id {
                break;
            }
            tokio::select! {
                event = chain_events.recv() => match event {
                    Ok(_) | Err(broadcast::error::RecvError::Lagged(_)) => {}
                    Err(broadcast::error::RecvError::Closed) => break,
                },
                event = mempool_events.recv() => match event {
                    Ok(_) | Err(broadcast::error::RecvError::Lagged(_)) => {}
                    Err(broadcast::error::RecvError::Closed) => break,
                },
            }
        }
    }
    get_block_template(node, params)
}

fn current_block_template_longpoll_id(node: &Arc<Node>) -> String {
    let tip = node.chain.read().tip();
    let sequence = node.mempool.read().sequence();
    format!("{}{}", tip.hash, sequence)
}

fn minimum_block_time(
    network: Network,
    parent: &Header,
    height: u32,
    median_time_past: u32,
) -> u32 {
    let mut minimum = median_time_past.saturating_add(1);
    let interval = network.params().difficulty_adjustment_interval();
    if u64::from(height) % interval == 0 {
        minimum = minimum.max(parent.time.saturating_sub(600));
    }
    minimum
}

fn prioritise_transaction(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let txid: Txid = param::<String>(params, 0)?.parse()?;
    if let Some(dummy) = params.get(1).filter(|value| !value.is_null()) {
        let dummy = dummy
            .as_f64()
            .ok_or_else(|| anyhow!("dummy priority argument must be numeric"))?;
        if dummy != 0.0 {
            bail!("priority is no longer supported; dummy argument must be 0")
        }
    }
    let fee_delta = param::<i64>(params, 2)?;
    node.mempool.write().prioritise(txid, fee_delta);
    Ok(Value::Bool(true))
}

fn get_prioritised_transactions(node: &Arc<Node>) -> Result<Value> {
    let mempool = node.mempool.read();
    let mut result = serde_json::Map::new();
    for (txid, fee_delta, in_mempool, modified_fee) in mempool.prioritised_transactions() {
        let mut entry = json!({
            "fee_delta": fee_delta,
            "in_mempool": in_mempool,
        });
        if let Some(modified_fee) = modified_fee {
            entry["modified_fee"] = json!(modified_fee);
        }
        result.insert(txid.to_string(), entry);
    }
    Ok(Value::Object(result))
}

fn get_mempool_relationship(node: &Arc<Node>, params: &Value, ancestors: bool) -> Result<Value> {
    let txid: Txid = param::<String>(params, 0)?.parse()?;
    let verbose = optional_bool(params, 1, false, "verbose")?;
    let mempool = node.mempool.read();
    if mempool.get(&txid).is_none() {
        bail!("Transaction not in mempool");
    }
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
                mempool_entry_json(&mempool, &related_txid)?,
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

fn get_orphan_transactions(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let verbosity = match params.get(0) {
        None | Some(Value::Null) => 0,
        Some(value) => value
            .as_u64()
            .ok_or_else(|| anyhow!("verbosity must be a number"))?,
    };
    if verbosity > 2 {
        bail!("Invalid verbosity value {verbosity}");
    }
    let orphans = node.orphan_transactions();
    if verbosity == 0 {
        return Ok(json!(
            orphans
                .iter()
                .map(|orphan| orphan.transaction.compute_txid().to_string())
                .collect::<Vec<_>>()
        ));
    }
    Ok(json!(
        orphans
            .into_iter()
            .map(|orphan| {
                let transaction = orphan.transaction;
                let mut value = json!({
                    "txid": transaction.compute_txid().to_string(),
                    "wtxid": transaction.compute_wtxid().to_string(),
                    "bytes": serialize(&transaction).len(),
                    "vsize": transaction.vsize(),
                    "weight": transaction.weight().to_wu(),
                    "from": orphan.peer_ids,
                });
                if verbosity == 2 {
                    value["hex"] = json!(hex::encode(serialize(&transaction)));
                }
                value
            })
            .collect::<Vec<_>>()
    ))
}

#[derive(Clone, Debug)]
struct MempoolChunk {
    txids: Vec<Txid>,
    weight: u64,
    fee: i64,
}

fn append_mempool_chunk(chunks: &mut Vec<MempoolChunk>, txid: Txid, weight: u64, fee: i64) {
    chunks.push(MempoolChunk {
        txids: vec![txid],
        weight,
        fee,
    });
    while chunks.len() >= 2 {
        let right_index = chunks.len() - 1;
        let left_index = right_index - 1;
        let (left, right) = (&chunks[left_index], &chunks[right_index]);
        let should_merge = i128::from(left.fee) * i128::from(right.weight)
            < i128::from(right.fee) * i128::from(left.weight);
        if !should_merge {
            break;
        }
        let right = chunks.pop().expect("right chunk exists");
        let left = chunks.last_mut().expect("left chunk exists");
        left.weight = left.weight.saturating_add(right.weight);
        left.fee = left.fee.saturating_add(right.fee);
        left.txids.extend(right.txids);
    }
}

fn mempool_cluster_transaction_ids(mempool: &Mempool, txid: &Txid) -> Option<Vec<Txid>> {
    mempool.get(txid)?;
    let mut cluster = HashSet::new();
    let mut pending = vec![*txid];
    while let Some(current) = pending.pop() {
        if !cluster.insert(current) {
            continue;
        }
        pending.extend(mempool.parents(&current));
        pending.extend(mempool.children(&current));
    }
    Some(
        mempool
            .main_order()
            .into_iter()
            .filter(|candidate| cluster.contains(candidate))
            .collect(),
    )
}

fn modified_mempool_fee_sat(mempool: &Mempool, txid: &Txid) -> i64 {
    let Some(entry) = mempool.get(txid) else {
        return 0;
    };
    i64::try_from(entry.fee_sat)
        .unwrap_or(i64::MAX)
        .saturating_add(mempool.fee_delta(txid))
}

fn mempool_cluster_chunks(mempool: &Mempool, txid: &Txid) -> Option<(u64, Vec<MempoolChunk>)> {
    let transaction_ids = mempool_cluster_transaction_ids(mempool, txid)?;
    let cluster = transaction_ids.iter().copied().collect::<HashSet<_>>();
    let mut chunks = Vec::new();
    for candidate in mempool.mining_order(u64::MAX, 0) {
        if !cluster.contains(&candidate) {
            continue;
        }
        if mempool.get(&candidate).is_none() {
            continue;
        }
        append_mempool_chunk(
            &mut chunks,
            candidate,
            mempool.adjusted_weight(&candidate),
            modified_mempool_fee_sat(mempool, &candidate),
        );
    }
    let weight = chunks
        .iter()
        .map(|chunk| chunk.weight)
        .fold(0u64, u64::saturating_add);
    Some((weight, chunks))
}

fn get_mempool_cluster(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let txid: Txid = param::<String>(params, 0)?.parse()?;
    let mempool = node.mempool.read();
    let (weight, chunks) = mempool_cluster_chunks(&mempool, &txid)
        .ok_or_else(|| anyhow!("Transaction not in mempool"))?;
    let txcount = chunks.iter().map(|chunk| chunk.txids.len()).sum::<usize>();
    Ok(json!({
        "clusterweight": weight,
        "txcount": txcount,
        "chunks": chunks
            .into_iter()
            .map(|chunk| {
                json!({
                    "chunkfee": sat_to_btc_signed(chunk.fee),
                    "chunkweight": chunk.weight,
                    "txs": chunk
                        .txids
                        .into_iter()
                        .map(|txid| txid.to_string())
                        .collect::<Vec<_>>(),
                })
            })
            .collect::<Vec<_>>(),
    }))
}

fn get_mempool_fee_rate_diagram(node: &Arc<Node>) -> Result<Value> {
    let mempool = node.mempool.read();
    let mut chunks = Vec::new();
    for txid in mempool.mining_order(u64::MAX, 0) {
        if mempool.get(&txid).is_none() {
            continue;
        }
        append_mempool_chunk(
            &mut chunks,
            txid,
            mempool.adjusted_weight(&txid),
            modified_mempool_fee_sat(&mempool, &txid),
        );
    }
    let mut weight = 0u64;
    let mut fee = 0i64;
    let mut diagram = vec![json!({"weight": 0, "fee": 0.0})];
    for chunk in chunks {
        weight = weight.saturating_add(chunk.weight);
        fee = fee.saturating_add(chunk.fee);
        diagram.push(json!({
            "weight": weight,
            "fee": sat_to_btc_signed(fee),
        }));
    }
    Ok(Value::Array(diagram))
}

fn mempool_entry_json(mempool: &Mempool, txid: &Txid) -> Result<Value> {
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
            .fold((0u64, 0i64), |(size, modified), candidate| {
                (
                    size.saturating_add(candidate.vsize),
                    modified
                        .saturating_add(i64::try_from(candidate.fee_sat).unwrap_or(i64::MAX))
                        .saturating_add(mempool.fee_delta(&candidate.transaction.compute_txid())),
                )
            })
    };
    let (ancestor_size, ancestor_modified_fee) = aggregate(&ancestor_ids);
    let (descendant_size, descendant_modified_fee) = aggregate(&descendant_ids);
    let modified_fee = modified_mempool_fee_sat(mempool, txid);
    let (_, chunks) =
        mempool_cluster_chunks(mempool, txid).expect("mempool entry must have a cluster");
    let chunk = chunks
        .iter()
        .find(|chunk| chunk.txids.contains(txid))
        .expect("mempool entry must have a chunk");
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
        "height": entry.height,
        "descendantcount": descendant_ids.len(),
        "descendantsize": descendant_size,
        "ancestorcount": ancestor_ids.len(),
        "ancestorsize": ancestor_size,
        "chunkweight": chunk.weight,
        "wtxid": entry.transaction.compute_wtxid().to_string(),
        "fees": {
            "base": sat_to_btc(entry.fee_sat),
            "modified": sat_to_btc_signed(modified_fee),
            "ancestor": sat_to_btc_signed(ancestor_modified_fee),
            "descendant": sat_to_btc_signed(descendant_modified_fee),
            "chunk": sat_to_btc_signed(chunk.fee),
        },
        "depends": parents,
        "spentby": children,
        "bip125-replaceable": mempool.is_replaceable(txid),
        "unbroadcast": mempool.is_unbroadcast(txid),
    }))
}

fn package_policy_error(transactions: &[Transaction]) -> Option<&'static str> {
    if transactions.len() > MAX_PACKAGE_COUNT
        || (transactions.len() > 1 && package_weight(transactions) > MAX_PACKAGE_WEIGHT)
    {
        return Some("package-too-large");
    }
    let mut txids = HashSet::with_capacity(transactions.len());
    if transactions
        .iter()
        .any(|transaction| !txids.insert(transaction.compute_txid()))
    {
        return Some("package-contains-duplicates");
    }
    if !package_is_topologically_sorted(transactions) {
        return Some("package-not-sorted");
    }
    let mut spent = HashMap::new();
    for transaction in transactions {
        let txid = transaction.compute_txid();
        for input in &transaction.input {
            if let Some(previous) = spent.insert(input.previous_output, txid)
                && previous != txid
            {
                return Some("conflict-in-package");
            }
        }
    }
    None
}

fn mempool_reject_reason(error: &MempoolError) -> String {
    match error {
        MempoolError::AlreadyPresent => "txn-already-in-mempool".to_owned(),
        MempoolError::AlreadyInChain => "txn-already-known".to_owned(),
        MempoolError::Conflict(_) => "txn-mempool-conflict".to_owned(),
        MempoolError::TooManyReplacementCandidates { .. } => {
            "too many potential replacements".to_owned()
        }
        MempoolError::ReplacementFeerateDiagram => {
            "insufficient feerate: does not improve feerate diagram".to_owned()
        }
        MempoolError::MissingInput(_) => "missing-inputs".to_owned(),
        MempoolError::FeeRate => "mempool min fee not met".to_owned(),
        MempoolError::NonStandard(reason) => reason.clone(),
        MempoolError::ClusterLimit => "too-long-mempool-chain".to_owned(),
        MempoolError::Truc(reason) => format!("TRUC-violation, {reason}"),
        MempoolError::Script(reason) => reason.clone(),
        _ => error.to_string(),
    }
}

fn package_fee_calculation(
    transaction: &Transaction,
    package: &[Transaction],
    mempool: &Mempool,
) -> (i64, u64, Vec<String>) {
    let by_txid = package
        .iter()
        .map(|candidate| (candidate.compute_txid(), candidate))
        .collect::<HashMap<_, _>>();
    let mut seen = HashSet::new();
    let mut ordered = Vec::new();

    fn visit(
        txid: Txid,
        by_txid: &HashMap<Txid, &Transaction>,
        seen: &mut HashSet<Txid>,
        ordered: &mut Vec<Txid>,
    ) {
        if !seen.insert(txid) {
            return;
        }
        if let Some(transaction) = by_txid.get(&txid) {
            for input in &transaction.input {
                if by_txid.contains_key(&input.previous_output.txid) {
                    visit(input.previous_output.txid, by_txid, seen, ordered);
                }
            }
        }
        ordered.push(txid);
    }

    visit(
        transaction.compute_txid(),
        &by_txid,
        &mut seen,
        &mut ordered,
    );
    let mut fee = 0i64;
    let mut vsize = 0u64;
    let mut includes = Vec::with_capacity(ordered.len());
    for txid in ordered {
        if let Some(entry) = mempool.get(&txid) {
            fee = fee
                .saturating_add(i64::try_from(entry.fee_sat).unwrap_or(i64::MAX))
                .saturating_add(mempool.fee_delta(&txid));
            vsize = vsize.saturating_add(entry.vsize);
            includes.push(entry.transaction.compute_wtxid().to_string());
        }
    }
    (fee, vsize, includes)
}

fn accepted_transaction_json(
    transaction: &Transaction,
    package: &[Transaction],
    mempool: &Mempool,
    include_allowed: bool,
    include_wtxid: bool,
    include_effective_fee: bool,
) -> Result<Value> {
    let txid = transaction.compute_txid();
    let entry = mempool
        .get(&txid)
        .ok_or_else(|| anyhow!("accepted transaction disappeared"))?;
    let (effective_fee, effective_vsize, effective_includes) =
        package_fee_calculation(transaction, package, mempool);
    let effective_rate = if effective_vsize == 0 {
        0
    } else {
        effective_fee
            .saturating_mul(1_000)
            .checked_div(i64::try_from(effective_vsize).unwrap_or(i64::MAX))
            .unwrap_or_default()
    };
    let mut result = serde_json::Map::new();
    result.insert("txid".to_owned(), json!(txid.to_string()));
    if include_wtxid {
        result.insert(
            "wtxid".to_owned(),
            json!(transaction.compute_wtxid().to_string()),
        );
    }
    if include_allowed {
        result.insert("allowed".to_owned(), Value::Bool(true));
    }
    result.insert("vsize".to_owned(), json!(entry.vsize));
    let mut fees = json!({"base": sat_to_btc(entry.fee_sat)});
    if include_effective_fee {
        fees["effective-feerate"] = json!(sat_to_btc_signed(effective_rate));
        fees["effective-includes"] = json!(effective_includes);
    }
    result.insert("fees".to_owned(), fees);
    Ok(Value::Object(result))
}

fn rejected_transaction_json(transaction: &Transaction, error: &MempoolError) -> Value {
    let mut result = json!({
        "txid": transaction.compute_txid().to_string(),
        "wtxid": transaction.compute_wtxid().to_string(),
        "allowed": false,
        "reject-reason": mempool_reject_reason(error),
    });
    if !matches!(error, MempoolError::MissingInput(_)) {
        result["reject-details"] = json!(error.to_string());
    }
    result
}

fn exceeds_max_fee(fee_sat: u64, vsize: u64, max_fee_rate: Option<u64>) -> bool {
    max_fee_rate.is_some_and(|max_fee_rate| fee_sat > max_fee_for_vsize(max_fee_rate, vsize))
}

fn max_fee_for_vsize(max_fee_rate_sat_per_kvb: u64, vsize: u64) -> u64 {
    u64::try_from((u128::from(max_fee_rate_sat_per_kvb) * u128::from(vsize)).div_ceil(1_000))
        .unwrap_or(u64::MAX)
}

fn first_max_fee_failure_index(
    transactions: &[Transaction],
    mempool: &Mempool,
    preexisting: &HashSet<Txid>,
    max_fee_rate: Option<u64>,
) -> Option<usize> {
    max_fee_rate.and_then(|_| {
        transactions
            .iter()
            .enumerate()
            .find_map(|(index, transaction)| {
                let txid = transaction.compute_txid();
                (!preexisting.contains(&txid))
                    .then(|| mempool.get(&txid))
                    .flatten()
                    .filter(|entry| exceeds_max_fee(entry.fee_sat, entry.vsize, max_fee_rate))
                    .map(|_| index)
            })
    })
}

fn discard_unaccepted_package_transactions(
    candidate: &mut Mempool,
    transactions: &[Transaction],
    preexisting: &HashSet<Txid>,
    accepted: &[Transaction],
) {
    let accepted_ids = accepted
        .iter()
        .map(Transaction::compute_txid)
        .collect::<HashSet<_>>();
    for transaction in transactions.iter().rev() {
        let txid = transaction.compute_txid();
        if !preexisting.contains(&txid) && !accepted_ids.contains(&txid) {
            candidate.remove(&txid);
        }
    }
}

pub(crate) fn test_mempool_accept(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let raw_transactions = params
        .as_array()
        .and_then(|values| values.first())
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("testmempoolaccept expects an array of hex transactions"))?;
    if raw_transactions.is_empty() || raw_transactions.len() > MAX_PACKAGE_COUNT {
        bail!("Array must contain between 1 and {MAX_PACKAGE_COUNT} transactions.");
    }
    let max_fee_rate = parse_max_fee_rate(params.get(1))?;
    let transactions = raw_transactions
        .iter()
        .map(|raw| {
            let raw = raw
                .as_str()
                .ok_or_else(|| anyhow!("TX decode failed: transaction must be hex"))?;
            let bytes = hex::decode(raw).context("TX decode failed")?;
            deserialize(&bytes).context("TX decode failed")
        })
        .collect::<Result<Vec<Transaction>>>()?;
    if let Some(error) = package_policy_error(&transactions) {
        return Ok(json!(
            transactions
                .iter()
                .map(|transaction| json!({
                    "txid": transaction.compute_txid().to_string(),
                    "wtxid": transaction.compute_wtxid().to_string(),
                    "package-error": error,
                }))
                .collect::<Vec<_>>()
        ));
    }

    let chain = node.chain.read();
    let mut candidate = node.mempool.read().clone();
    if transactions.len() > 1 {
        if let Err(error) = candidate.accept_package_for_test(&transactions, &chain) {
            return Ok(json!(
                transactions
                    .iter()
                    .map(|transaction| rejected_transaction_json(transaction, &error))
                    .collect::<Vec<_>>()
            ));
        }
        let mut result = Vec::with_capacity(transactions.len());
        let mut exit_early = false;
        for transaction in &transactions {
            if exit_early {
                result.push(json!({
                    "txid": transaction.compute_txid().to_string(),
                    "wtxid": transaction.compute_wtxid().to_string(),
                }));
                continue;
            }
            let entry = candidate
                .get(&transaction.compute_txid())
                .ok_or_else(|| anyhow!("accepted package transaction disappeared"))?;
            if exceeds_max_fee(entry.fee_sat, entry.vsize, max_fee_rate) {
                result.push(json!({
                    "txid": transaction.compute_txid().to_string(),
                    "wtxid": transaction.compute_wtxid().to_string(),
                    "allowed": false,
                    "reject-reason": "max-fee-exceeded",
                }));
                exit_early = true;
            } else {
                result.push(accepted_transaction_json(
                    transaction,
                    &transactions,
                    &candidate,
                    true,
                    true,
                    true,
                )?);
            }
        }
        return Ok(Value::Array(result));
    }

    match candidate.accept_for_test(transactions[0].clone(), &chain) {
        Ok(txid) => {
            let entry = candidate
                .get(&txid)
                .ok_or_else(|| anyhow!("accepted transaction disappeared"))?;
            if exceeds_max_fee(entry.fee_sat, entry.vsize, max_fee_rate) {
                Ok(json!([{
                    "txid": txid.to_string(),
                    "wtxid": transactions[0].compute_wtxid().to_string(),
                    "allowed": false,
                    "reject-reason": "max-fee-exceeded",
                }]))
            } else {
                Ok(json!([accepted_transaction_json(
                    &transactions[0],
                    &transactions,
                    &candidate,
                    true,
                    true,
                    true,
                )?]))
            }
        }
        Err(error) => Ok(json!([rejected_transaction_json(&transactions[0], &error)])),
    }
}

pub(crate) fn submit_package(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let raw_transactions = params
        .get(0)
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("submitpackage expects an array of transactions"))?;
    if raw_transactions.is_empty() || raw_transactions.len() > MAX_PACKAGE_COUNT {
        bail!("Array must contain between 1 and {MAX_PACKAGE_COUNT} transactions.");
    }
    let max_fee_rate = parse_max_fee_rate(params.get(1))?;
    let max_burn_amount = parse_max_burn_amount(params.get(2))?;
    let mut transactions = Vec::with_capacity(raw_transactions.len());
    let mut transaction_ids = HashSet::new();
    for raw in raw_transactions {
        let raw = raw
            .as_str()
            .ok_or_else(|| anyhow!("TX decode failed: package transaction must be hex"))?;
        let transaction: Transaction = deserialize(&hex::decode(raw).context("TX decode failed")?)
            .context("TX decode failed")?;
        validate_burn_amount(&transaction, max_burn_amount)?;
        let txid = transaction.compute_txid();
        if !transaction_ids.insert(txid) {
            bail!("package contains duplicate transaction {txid}")
        }
        transactions.push(transaction);
    }
    if let Some(error) = package_policy_error(&transactions)
        && error != "package-not-sorted"
        && error != "package-contains-duplicates"
    {
        bail!("{error}");
    }
    if transactions.len() > 1 && !package_is_child_with_parents_tree(&transactions) {
        bail!(
            "package topology disallowed. not child-with-parents or parents depend on each other."
        );
    }

    let chain = node.chain.read();
    let original_mempool = node.mempool.read();
    let before_transactions = original_mempool
        .transactions()
        .map(|transaction| (transaction.compute_txid(), transaction.clone()))
        .collect::<HashMap<_, _>>();
    let preexisting = transactions
        .iter()
        .filter_map(|transaction| {
            original_mempool
                .get(&transaction.compute_txid())
                .map(|_| transaction.compute_txid())
        })
        .collect::<HashSet<_>>();
    let (mut candidate, package_result, package_rbf) =
        original_mempool.accept_package_with_state(&transactions, &chain);
    drop(original_mempool);
    let max_fee_failure =
        first_max_fee_failure_index(&transactions, &candidate, &preexisting, max_fee_rate);
    let mut results = serde_json::Map::new();
    if let Err(error) = package_result {
        // submitpackage exposes the detailed validation error in each
        // per-transaction result. testmempoolaccept uses the shorter
        // reject-reason classification instead.
        let reason = error.to_string();
        let first_missing = transactions
            .iter()
            .position(|transaction| candidate.get(&transaction.compute_txid()).is_none());
        let failure_index = if package_rbf {
            None
        } else {
            match (max_fee_failure, first_missing) {
                (Some(max_fee_index), Some(missing_index)) if max_fee_index < missing_index => {
                    Some(max_fee_index)
                }
                (_, Some(missing_index)) => Some(missing_index),
                (Some(max_fee_index), None) => Some(max_fee_index),
                (None, None) => None,
            }
        };
        if let Some(failure_index) = failure_index {
            let accepted = transactions
                .iter()
                .take(failure_index)
                .filter(|transaction| {
                    !preexisting.contains(&transaction.compute_txid())
                        && candidate.get(&transaction.compute_txid()).is_some()
                })
                .cloned()
                .collect::<Vec<_>>();
            for (index, transaction) in transactions.iter().enumerate() {
                let txid = transaction.compute_txid();
                if index < failure_index {
                    results.insert(
                        transaction.compute_wtxid().to_string(),
                        accepted_transaction_json(
                            transaction,
                            &transactions,
                            &candidate,
                            false,
                            false,
                            !preexisting.contains(&txid),
                        )?,
                    );
                    continue;
                }
                let transaction_error = if index == failure_index {
                    max_fee_failure
                        .filter(|max_fee_index| *max_fee_index == failure_index)
                        .map_or_else(|| reason.clone(), |_| "max feerate exceeded".to_owned())
                } else {
                    "package-not-validated".to_owned()
                };
                results.insert(
                    transaction.compute_wtxid().to_string(),
                    json!({
                        "txid": txid.to_string(),
                        "error": transaction_error,
                    }),
                );
            }
            drop(chain);
            let replaced_transactions = if accepted.is_empty() {
                Vec::new()
            } else {
                discard_unaccepted_package_transactions(
                    &mut candidate,
                    &transactions,
                    &preexisting,
                    &accepted,
                );
                commit_submitted_package(node, candidate, before_transactions, accepted)
            };
            return Ok(json!({
                "package_msg": "transaction failed",
                "tx-results": results,
                "replaced-transactions": replaced_transactions,
            }));
        }
        for transaction in &transactions {
            results.insert(
                transaction.compute_wtxid().to_string(),
                json!({
                    "txid": transaction.compute_txid().to_string(),
                    "error": reason,
                }),
            );
        }
        return Ok(json!({
            "package_msg": submit_package_failure_message(&error, package_rbf),
            "tx-results": results,
            "replaced-transactions": [],
        }));
    }

    if !package_rbf {
        if let Some(failure_index) = max_fee_failure {
            let accepted = transactions
                .iter()
                .take(failure_index)
                .filter(|transaction| !preexisting.contains(&transaction.compute_txid()))
                .cloned()
                .collect::<Vec<_>>();
            for (index, transaction) in transactions.iter().enumerate() {
                if index < failure_index {
                    results.insert(
                        transaction.compute_wtxid().to_string(),
                        accepted_transaction_json(
                            transaction,
                            &transactions,
                            &candidate,
                            false,
                            false,
                            !preexisting.contains(&transaction.compute_txid()),
                        )?,
                    );
                } else if index == failure_index {
                    results.insert(
                        transaction.compute_wtxid().to_string(),
                        json!({
                            "txid": transaction.compute_txid().to_string(),
                            "error": "max feerate exceeded",
                        }),
                    );
                } else {
                    results.insert(
                        transaction.compute_wtxid().to_string(),
                        json!({
                            "txid": transaction.compute_txid().to_string(),
                            "error": "package-not-validated",
                        }),
                    );
                }
            }
            drop(chain);
            let replaced_transactions = if accepted.is_empty() {
                Vec::new()
            } else {
                discard_unaccepted_package_transactions(
                    &mut candidate,
                    &transactions,
                    &preexisting,
                    &accepted,
                );
                commit_submitted_package(node, candidate, before_transactions, accepted)
            };
            return Ok(json!({
                "package_msg": "transaction failed",
                "tx-results": results,
                "replaced-transactions": replaced_transactions,
            }));
        }
    }

    let mut max_fee_exceeded = false;
    for transaction in &transactions {
        let entry = candidate
            .get(&transaction.compute_txid())
            .ok_or_else(|| anyhow!("accepted package transaction disappeared"))?;
        if exceeds_max_fee(entry.fee_sat, entry.vsize, max_fee_rate) {
            max_fee_exceeded = true;
            results.insert(
                transaction.compute_wtxid().to_string(),
                json!({
                    "txid": transaction.compute_txid().to_string(),
                    "error": "max feerate exceeded",
                }),
            );
        } else {
            results.insert(
                transaction.compute_wtxid().to_string(),
                accepted_transaction_json(
                    transaction,
                    &transactions,
                    &candidate,
                    false,
                    false,
                    !preexisting.contains(&transaction.compute_txid()),
                )?,
            );
        }
    }
    if max_fee_exceeded {
        return Ok(json!({
            "package_msg": "transaction failed",
            "tx-results": results,
            "replaced-transactions": [],
        }));
    }

    let accepted = transactions
        .iter()
        .filter(|transaction| !preexisting.contains(&transaction.compute_txid()))
        .cloned()
        .collect::<Vec<_>>();
    drop(chain);
    let replaced_transactions =
        commit_submitted_package(node, candidate, before_transactions, accepted);
    Ok(json!({
        "package_msg": "success",
        "tx-results": results,
        "replaced-transactions": replaced_transactions,
    }))
}

fn commit_submitted_package(
    node: &Arc<Node>,
    mut candidate: Mempool,
    before_transactions: HashMap<Txid, Transaction>,
    accepted: Vec<Transaction>,
) -> Vec<String> {
    for transaction in &accepted {
        candidate.add_unbroadcast(transaction.compute_txid());
    }
    let changes = candidate.take_changes();
    let removed = before_transactions
        .into_iter()
        .filter_map(|(txid, transaction)| candidate.get(&txid).is_none().then_some(transaction))
        .collect::<Vec<_>>();
    let replaced_transactions = removed
        .iter()
        .map(|transaction| transaction.compute_txid().to_string())
        .collect::<Vec<_>>();
    *node.mempool.write() = candidate;
    node.notify_zmq_mempool_changes(changes);
    node.notify_mempool_removals(removed);
    for transaction in accepted {
        node.notify_mempool_transaction(transaction);
    }
    replaced_transactions
}

fn submit_package_failure_message(error: &MempoolError, package_rbf: bool) -> &'static str {
    if !package_rbf {
        return "transaction failed";
    }
    match error {
        MempoolError::ReplacementFeerateDiagram => {
            "package RBF failed: insufficient feerate: does not improve feerate diagram"
        }
        MempoolError::ReplacementUnconfirmedInput => {
            "package RBF failed: new transaction cannot have mempool ancestors"
        }
        _ => "transaction failed",
    }
}

fn get_txout(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let txid: Txid = param::<String>(params, 0)?.parse()?;
    let vout = param::<u32>(params, 1)?;
    let include_mempool = optional_bool(params, 2, true, "include_mempool")?;
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
            "scriptPubKey": script_json_with_network(
                &entry.output.script_pubkey,
                Some(node.config.network),
            ),
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
                "scriptPubKey": script_json_with_network(
                    &output.script_pubkey,
                    Some(node.config.network),
                ),
                "coinbase": false,
            }));
        }
    }
    drop(chain);
    Ok(Value::Null)
}

struct ScanReservation(Arc<ScanState>);

impl Drop for ScanReservation {
    fn drop(&mut self) {
        self.0.in_progress.store(false, Ordering::Release);
        self.0.abort.store(false, Ordering::Release);
    }
}

fn reserve_scan(state: &Arc<ScanState>) -> Result<ScanReservation> {
    if state
        .in_progress
        .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
        .is_err()
    {
        bail!("Scan already in progress, use action \"abort\" or \"status\"")
    }
    state.abort.store(false, Ordering::Release);
    state.progress.store(0, Ordering::Release);
    Ok(ScanReservation(state.clone()))
}

fn scan_txout_set(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let action = param::<String>(params, 0)?;
    match action.as_str() {
        "start" => {
            let _reservation = reserve_scan(&node.txout_scan)?;
            let scan_objects = params
                .get(1)
                .and_then(Value::as_array)
                .ok_or_else(|| anyhow!("scantxoutset start expects an array of descriptors"))?;
            if scan_objects.is_empty() {
                bail!("scantxoutset requires at least one descriptor")
            }
            let mut descriptors = Vec::with_capacity(scan_objects.len());
            for object in scan_objects {
                let descriptor = if let Some(descriptor) = object.as_str() {
                    descriptor.to_owned()
                } else {
                    object
                        .get("desc")
                        .and_then(Value::as_str)
                        .ok_or_else(|| anyhow!("scan descriptor object requires desc"))?
                        .to_owned()
                };
                let range = scan_descriptor_range(object, &descriptor)?;
                for script in expand_descriptor_scripts(node, &descriptor, range)? {
                    descriptors.push((descriptor.clone(), script));
                }
            }
            let chain = node.chain.read();
            let mut unspents = Vec::new();
            let mut total = 0u64;
            let mut scanned_txouts = 0usize;
            let total_txouts = chain.all_utxos().count();
            let mut completed = true;
            for (outpoint, entry) in chain.all_utxos() {
                if node.txout_scan.abort.load(Ordering::Acquire) {
                    completed = false;
                    break;
                }
                scanned_txouts = scanned_txouts.saturating_add(1);
                let progress = if total_txouts == 0 {
                    100
                } else {
                    scanned_txouts
                        .saturating_mul(100)
                        .checked_div(total_txouts)
                        .unwrap_or(100)
                        .min(100)
                };
                node.txout_scan.progress.store(progress, Ordering::Release);
                let Some((_, _)) = descriptors
                    .iter()
                    .find(|(_, script)| *script == entry.output.script_pubkey)
                else {
                    continue;
                };
                total = total.saturating_add(entry.output.value.to_sat());
                unspents.push(json!({
                    "txid": outpoint.txid.to_string(),
                    "vout": outpoint.vout,
                    "scriptPubKey": hex::encode(entry.output.script_pubkey.as_bytes()),
                    "desc": inferred_script_descriptor(node, &entry.output.script_pubkey),
                    "amount": sat_to_btc(entry.output.value.to_sat()),
                    "coinbase": entry.coinbase,
                    "height": entry.height,
                    "blockhash": chain
                        .block_hash(entry.height)
                        .map(|hash| hash.to_string())
                        .unwrap_or_default(),
                    "confirmations": chain.height().saturating_sub(entry.height) + 1,
                }));
            }
            if completed {
                node.txout_scan.progress.store(100, Ordering::Release);
            }
            unspents.sort_by(|left, right| {
                left["txid"]
                    .as_str()
                    .cmp(&right["txid"].as_str())
                    .then_with(|| left["vout"].as_u64().cmp(&right["vout"].as_u64()))
            });
            Ok(json!({
                "success": completed,
                "txouts": scanned_txouts,
                "height": chain.height(),
                "bestblock": chain.best_hash().to_string(),
                "unspents": unspents,
                "total_amount": sat_to_btc(total),
            }))
        }
        "status" => {
            if !node.txout_scan.in_progress.load(Ordering::Acquire) {
                Ok(Value::Null)
            } else {
                Ok(json!({
                    "progress": node.txout_scan.progress.load(Ordering::Acquire),
                }))
            }
        }
        "abort" => {
            if !node.txout_scan.in_progress.load(Ordering::Acquire) {
                Ok(Value::Bool(false))
            } else {
                node.txout_scan.abort.store(true, Ordering::Release);
                Ok(Value::Bool(true))
            }
        }
        _ => bail!("scantxoutset action must be start, status, or abort"),
    }
}

fn scan_blocks(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let action = param::<String>(params, 0)?;
    match action.as_str() {
        "status" => {
            if !node.blockfilter_scan.in_progress.load(Ordering::Acquire) {
                Ok(Value::Null)
            } else {
                Ok(json!({
                    "progress": node.blockfilter_scan.progress.load(Ordering::Acquire),
                    "current_height": node.blockfilter_scan.current_height.load(Ordering::Acquire),
                }))
            }
        }
        "abort" => {
            if !node.blockfilter_scan.in_progress.load(Ordering::Acquire) {
                Ok(Value::Bool(false))
            } else {
                node.blockfilter_scan.abort.store(true, Ordering::Release);
                Ok(Value::Bool(true))
            }
        }
        "start" => {
            let _reservation = reserve_scan(&node.blockfilter_scan)?;
            let filter_type = optional_str(params, 4, "basic", "filtertype")?;
            if filter_type != "basic" {
                bail!("Unknown filtertype")
            }
            if !node.config.blockfilterindex {
                bail!("Index is not enabled for filtertype {filter_type}")
            }
            let scan_objects = params
                .get(1)
                .and_then(Value::as_array)
                .ok_or_else(|| anyhow!("scanblocks start expects descriptors"))?;
            let scripts = scan_object_scripts(node, scan_objects)?;
            if scripts.is_empty() {
                bail!("scanblocks requires at least one descriptor")
            }
            let chain_height = node.chain.read().height();
            let start_height = optional_i64(params, 2, 0, "start_height")?;
            if start_height < 0 {
                bail!("start_height must not be negative")
            }
            let start_height =
                u32::try_from(start_height).map_err(|_| anyhow!("start_height is out of range"))?;
            let stop_height = optional_i64(params, 3, i64::from(chain_height), "stop_height")?;
            if stop_height < 0 {
                bail!("stop_height must not be negative")
            }
            let stop_height =
                u32::try_from(stop_height).map_err(|_| anyhow!("stop_height is out of range"))?;
            let filter_false_positives = match params.get(5).filter(|value| !value.is_null()) {
                None => false,
                Some(options) => {
                    let options = options
                        .as_object()
                        .ok_or_else(|| anyhow!("scanblocks options must be an object"))?;
                    options
                        .get("filter_false_positives")
                        .filter(|value| !value.is_null())
                        .map(|value| {
                            value.as_bool().ok_or_else(|| {
                                anyhow!(
                                    "scanblocks options.filter_false_positives must be a boolean"
                                )
                            })
                        })
                        .transpose()?
                        .unwrap_or(false)
                }
            };
            if start_height > stop_height || stop_height > chain_height {
                bail!("invalid scan height range")
            }
            node.blockfilter_scan
                .current_height
                .store(start_height as usize, Ordering::Release);
            let mut chain = node.chain.write();
            let mut relevant_blocks = Vec::new();
            let progress_denominator = stop_height.saturating_sub(start_height).max(1);
            let mut completed = true;
            let mut last_height = start_height;
            let stop_hash = chain
                .block_hash(stop_height)
                .ok_or_else(|| anyhow!("scan height is out of range"))?;
            let mut height = start_height;
            while height <= stop_height {
                if node.blockfilter_scan.abort.load(Ordering::Acquire) {
                    completed = false;
                    break;
                }
                let range = chain
                    .basic_filter_range(height, stop_hash, SCAN_BLOCKFILTER_BATCH_SIZE)?
                    .ok_or_else(|| anyhow!("block filter is missing"))?;
                if range.filters.is_empty() {
                    bail!("block filter is missing")
                }
                for (offset, (hash, content, _)) in range.filters.into_iter().enumerate() {
                    if node.blockfilter_scan.abort.load(Ordering::Acquire) {
                        completed = false;
                        break;
                    }
                    let height = height.saturating_add(u32::try_from(offset).unwrap_or(u32::MAX));
                    node.blockfilter_scan
                        .current_height
                        .store(height as usize, Ordering::Release);
                    let filter = BlockFilter::new(&content);
                    if filter.match_any(&hash, scripts.iter().map(|script| script.as_bytes()))?
                        && (!filter_false_positives
                            || block_matches_scripts(&mut chain, &hash, &scripts)?)
                    {
                        relevant_blocks.push(hash.to_string());
                    }
                    last_height = height;
                    let progress = height
                        .saturating_sub(start_height)
                        .saturating_mul(100)
                        .checked_div(progress_denominator)
                        .unwrap_or(100);
                    node.blockfilter_scan
                        .progress
                        .store(progress as usize, Ordering::Release);
                }
                if !completed || last_height >= stop_height {
                    break;
                }
                height = last_height
                    .checked_add(1)
                    .ok_or_else(|| anyhow!("scan height is out of range"))?;
            }
            if completed {
                node.blockfilter_scan.progress.store(100, Ordering::Release);
            }
            Ok(json!({
                "from_height": start_height,
                "to_height": last_height,
                "relevant_blocks": relevant_blocks,
                "completed": completed,
            }))
        }
        _ => bail!("scanblocks action must be start, status, or abort"),
    }
}

fn block_matches_scripts(
    chain: &mut chain::ChainState,
    hash: &BlockHash,
    scripts: &[ScriptBuf],
) -> Result<bool> {
    let block = chain
        .block(hash)?
        .ok_or_else(|| anyhow!("block not found while verifying filter match"))?;
    for transaction in &block.txdata {
        if transaction
            .output
            .iter()
            .any(|output| scripts.iter().any(|script| script == &output.script_pubkey))
        {
            return Ok(true);
        }
        for input in &transaction.input {
            if input.previous_output.is_null() {
                continue;
            }
            let Some((previous, _)) = chain.transaction(&input.previous_output.txid)? else {
                continue;
            };
            let Some(output) = previous.output.get(input.previous_output.vout as usize) else {
                continue;
            };
            if scripts.iter().any(|script| script == &output.script_pubkey) {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn get_descriptor_activity(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let requested_hashes = params
        .get(0)
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("getdescriptoractivity expects block hashes"))?;
    let scan_objects = params
        .get(1)
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("getdescriptoractivity expects descriptors"))?;
    let scripts = scan_object_scripts(node, scan_objects)?;
    let include_mempool = optional_bool(params, 2, true, "include_mempool")?;
    let mut chain = node.chain.write();
    let mut blocks = requested_hashes
        .iter()
        .map(|value| {
            let hash: BlockHash = value
                .as_str()
                .ok_or_else(|| anyhow!("block hash must be a string"))?
                .parse()?;
            if !chain.is_active_block(&hash) {
                bail!("block is not in the active chain")
            }
            let height = chain
                .block_height_by_hash(&hash)
                .ok_or_else(|| anyhow!("block not found"))?;
            let block = chain
                .block(&hash)?
                .ok_or_else(|| anyhow!("block not found"))?;
            Ok((height, hash, block))
        })
        .collect::<Result<Vec<_>>>()?;
    blocks.sort_by_key(|(height, _, _)| *height);
    blocks.dedup_by_key(|(_, hash, _)| *hash);

    let mut activity = Vec::new();
    for (height, hash, block) in blocks {
        for transaction in &block.txdata {
            let txid = transaction.compute_txid();
            for (vin, input) in transaction.input.iter().enumerate() {
                if input.previous_output.is_null() {
                    continue;
                }
                let Some((previous, _)) = chain.transaction(&input.previous_output.txid)? else {
                    continue;
                };
                let Some(output) = previous.output.get(input.previous_output.vout as usize) else {
                    continue;
                };
                if scripts.iter().any(|script| script == &output.script_pubkey) {
                    activity.push(json!({
                        "type": "spend",
                        "amount": sat_to_btc(output.value.to_sat()),
                        "blockhash": hash.to_string(),
                        "height": height,
                        "spend_txid": txid.to_string(),
                        "spend_vin": vin,
                        "prevout_txid": input.previous_output.txid.to_string(),
                        "prevout_vout": input.previous_output.vout,
                        "prevout_spk": script_json_with_network(
                            &output.script_pubkey,
                            Some(node.config.network),
                        ),
                    }));
                }
            }
            for (vout, output) in transaction.output.iter().enumerate() {
                if scripts.iter().any(|script| script == &output.script_pubkey) {
                    activity.push(json!({
                        "type": "receive",
                        "amount": sat_to_btc(output.value.to_sat()),
                        "blockhash": hash.to_string(),
                        "height": height,
                        "txid": txid.to_string(),
                        "vout": vout,
                        "output_spk": script_json_with_network(
                            &output.script_pubkey,
                            Some(node.config.network),
                        ),
                    }));
                }
            }
        }
    }

    if include_mempool {
        let mempool = node.mempool.read();
        for txid in mempool.transaction_order() {
            let Some(entry) = mempool.get(&txid) else {
                continue;
            };
            for (vin, input) in entry.transaction.input.iter().enumerate() {
                let Some(output) = output_for_outpoint(&chain, &mempool, input.previous_output)
                else {
                    continue;
                };
                if scripts.iter().any(|script| script == &output.script_pubkey) {
                    activity.push(json!({
                        "type": "spend",
                        "amount": sat_to_btc(output.value.to_sat()),
                        "spend_txid": txid.to_string(),
                        "spend_vin": vin,
                        "prevout_txid": input.previous_output.txid.to_string(),
                        "prevout_vout": input.previous_output.vout,
                        "prevout_spk": script_json_with_network(
                            &output.script_pubkey,
                            Some(node.config.network),
                        ),
                    }));
                }
            }
            for (vout, output) in entry.transaction.output.iter().enumerate() {
                if scripts.iter().any(|script| script == &output.script_pubkey) {
                    activity.push(json!({
                        "type": "receive",
                        "amount": sat_to_btc(output.value.to_sat()),
                        "txid": txid.to_string(),
                        "vout": vout,
                        "output_spk": script_json_with_network(
                            &output.script_pubkey,
                            Some(node.config.network),
                        ),
                    }));
                }
            }
        }
    }
    Ok(json!({"activity": activity}))
}

fn get_chain_states(node: &Arc<Node>) -> Result<Value> {
    let mut chain = node.chain.write();
    chain.poll_background_validation()?;
    let tip = chain.tip();
    let header_tip = chain.best_header_tip();
    let mut chainstates = Vec::with_capacity(2);
    let make_chainstate = |height: u32,
                           hash: BlockHash,
                           verificationprogress: f64,
                           coins_tip_cache_bytes: u64,
                           validated: bool,
                           snapshot_base: Option<BlockHash>|
     -> Result<Value> {
        let header = chain
            .header(height)
            .ok_or_else(|| anyhow!("chainstate header is unavailable"))?;
        let mut chainstate = json!({
            "blocks": height,
            "bestblockhash": hash.to_string(),
            "bits": format!("{:08x}", header.bits.to_consensus()),
            "target": format!("{:064x}", header.target()),
            "difficulty": header.difficulty_float(),
            "verificationprogress": verificationprogress,
            "coins_db_cache_bytes": 0,
            "coins_tip_cache_bytes": coins_tip_cache_bytes,
            "validated": validated,
        });
        if let Some(snapshot_base) = snapshot_base {
            chainstate["snapshot_blockhash"] = json!(snapshot_base.to_string());
        }
        Ok(chainstate)
    };

    if let Some((progress_height, progress_hash, snapshot_base, _)) = chain.background_chainstate()
    {
        let progress = if tip.height == 0 {
            0.0
        } else {
            f64::from(progress_height) / f64::from(tip.height)
        };
        chainstates.push(make_chainstate(
            progress_height,
            progress_hash,
            progress.min(1.0),
            0,
            false,
            None,
        )?);
        chainstates.push(make_chainstate(
            tip.height,
            tip.hash,
            1.0,
            chain.utxo_bogo_size(),
            false,
            Some(snapshot_base),
        )?);
    } else {
        let (snapshot_base, validated) = chain
            .snapshot_provenance()
            .map_or((None, true), |(base, validated)| (Some(base), validated));
        chainstates.push(make_chainstate(
            tip.height,
            tip.hash,
            1.0,
            chain.utxo_bogo_size(),
            validated,
            snapshot_base,
        )?);
    }
    Ok(json!({
        "headers": header_tip.height,
        "chainstates": chainstates,
    }))
}

fn scan_object_scripts(node: &Arc<Node>, objects: &[Value]) -> Result<Vec<ScriptBuf>> {
    let mut scripts = Vec::new();
    for object in objects {
        let descriptor = if let Some(descriptor) = object.as_str() {
            descriptor.to_owned()
        } else {
            object
                .get("desc")
                .and_then(Value::as_str)
                .ok_or_else(|| anyhow!("scan descriptor object requires desc"))?
                .to_owned()
        };
        let range = scan_descriptor_range(object, &descriptor)?;
        scripts.extend(expand_descriptor_scripts(node, &descriptor, range)?);
    }
    Ok(scripts)
}

fn scan_descriptor_range(object: &Value, descriptor: &str) -> Result<Option<(u32, u32)>> {
    let range = object
        .get("range")
        .filter(|value| !value.is_null())
        .map(parse_descriptor_process_range)
        .transpose()?;
    Ok(range.or_else(|| {
        descriptor
            .split('#')
            .next()
            .is_some_and(|payload| payload.contains('*'))
            .then_some((0, 1_000))
    }))
}

fn output_for_outpoint(
    chain: &chain::ChainState,
    mempool: &Mempool,
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

fn mining_descriptor_script(node: &Arc<Node>, descriptor: &str) -> Result<ScriptBuf> {
    let mut scripts = expand_descriptor_scripts(node, descriptor, None)?;
    match scripts.len() {
        0 => bail!("descriptor did not produce a script"),
        1 => Ok(scripts.remove(0)),
        4 => Ok(scripts.remove(2)),
        _ => Ok(scripts.remove(1)),
    }
}

fn expand_descriptor_scripts(
    node: &Arc<Node>,
    descriptor: &str,
    range: Option<(u32, u32)>,
) -> Result<Vec<ScriptBuf>> {
    let descriptor = if descriptor.contains('#') {
        descriptor_payload(descriptor)?.0
    } else {
        descriptor
    };
    let multipath_payloads = expand_descriptor_multipath(descriptor)?;
    if multipath_payloads.len() > 1 {
        return multipath_payloads
            .iter()
            .map(|payload| expand_descriptor_scripts(node, payload, range))
            .collect::<Result<Vec<Vec<ScriptBuf>>>>()
            .map(|scripts| scripts.into_iter().flatten().collect());
    }
    if let Some(address) = descriptor
        .strip_prefix("addr(")
        .and_then(|value| value.strip_suffix(')'))
    {
        if range.is_some() {
            bail!("addr descriptors do not accept a range")
        }
        return Ok(vec![
            address
                .parse::<Address<bitcoin::address::NetworkUnchecked>>()?
                .require_network(node.config.network)?
                .script_pubkey(),
        ]);
    }
    if let Some(script) = descriptor
        .strip_prefix("raw(")
        .and_then(|value| value.strip_suffix(')'))
    {
        if range.is_some() {
            bail!("raw descriptors do not accept a range")
        }
        return Ok(vec![ScriptBuf::from_bytes(hex::decode(script)?)]);
    }
    if let Some(candidates) = miniscript_v0_candidates(descriptor, range)? {
        return Ok(candidates
            .into_iter()
            .map(|candidate| candidate.script_pubkey)
            .collect());
    }
    if let Some(key_expression) = descriptor
        .strip_prefix("rawtr(")
        .and_then(|value| value.strip_suffix(')'))
    {
        let (key, path, wildcard) = parse_descriptor_key(key_expression)?;
        let indices = descriptor_indices(wildcard, range)?;
        let secp = bitcoin::secp256k1::Secp256k1::verification_only();
        return indices
            .into_iter()
            .map(|index| {
                let xonly = match &key {
                    DescriptorKey::PublicKey(public_key) => {
                        bitcoin::XOnlyPublicKey::from(*public_key)
                    }
                    DescriptorKey::XOnlyPublicKey(public_key) => *public_key,
                    DescriptorKey::Xpriv(_) | DescriptorKey::Xpub(_) => {
                        bitcoin::XOnlyPublicKey::from(descriptor_public_key(
                            &key, &path, index, &secp,
                        )?)
                    }
                };
                Ok(raw_taproot_script_pubkey(xonly))
            })
            .collect();
    }
    for kind in ["multi", "sortedmulti"] {
        if let Some(arguments) = descriptor
            .strip_prefix(&format!("{kind}("))
            .and_then(|value| value.strip_suffix(')'))
        {
            return expand_multisig_descriptor(node, arguments, range, kind == "sortedmulti");
        }
    }
    if let Some(key_expression) = descriptor
        .strip_prefix("pk(")
        .and_then(|value| value.strip_suffix(')'))
    {
        let (key, path, wildcard) = parse_descriptor_key(key_expression)?;
        let indices = descriptor_indices(wildcard, range)?;
        let secp = bitcoin::secp256k1::Secp256k1::verification_only();
        return indices
            .into_iter()
            .map(|index| {
                let public_key = descriptor_public_key(&key, &path, index, &secp)?;
                Ok(Builder::new()
                    .push_key(&public_key)
                    .push_opcode(bitcoin::blockdata::opcodes::all::OP_CHECKSIG)
                    .into_script())
            })
            .collect();
    }
    if let Some(key_expression) = descriptor
        .strip_prefix("combo(")
        .and_then(|value| value.strip_suffix(')'))
    {
        let (key, path, wildcard) = parse_descriptor_key(key_expression)?;
        let indices = descriptor_indices(wildcard, range)?;
        let secp = bitcoin::secp256k1::Secp256k1::verification_only();
        let mut scripts = Vec::new();
        for index in indices {
            let public_key = descriptor_public_key(&key, &path, index, &secp)?;
            scripts.push(
                Builder::new()
                    .push_key(&public_key)
                    .push_opcode(bitcoin::blockdata::opcodes::all::OP_CHECKSIG)
                    .into_script(),
            );
            scripts.push(Address::p2pkh(public_key, node.config.network).script_pubkey());
            if let Ok(compressed) = bitcoin::CompressedPublicKey::try_from(public_key) {
                scripts.push(Address::p2wpkh(&compressed, node.config.network).script_pubkey());
                scripts.push(Address::p2shwpkh(&compressed, node.config.network).script_pubkey());
            }
        }
        return Ok(scripts);
    }
    if let Some(candidates) = miniscript_taproot_candidates(descriptor, range)? {
        return Ok(candidates
            .into_iter()
            .map(|candidate| candidate.script_pubkey)
            .collect());
    }
    for wrapper in ["sh", "wsh"] {
        if let Some(inner) = descriptor
            .strip_prefix(&format!("{wrapper}("))
            .and_then(|value| value.strip_suffix(')'))
        {
            let scripts = expand_descriptor_scripts(node, inner, range)?;
            return scripts
                .into_iter()
                .map(|script| {
                    let address = if wrapper == "sh" {
                        Address::p2sh(&script, node.config.network)?
                    } else {
                        Address::p2wsh(&script, node.config.network)
                    };
                    Ok(address.script_pubkey())
                })
                .collect();
        }
    }
    if let Some(key_expression) = descriptor
        .strip_prefix("tr(")
        .and_then(|value| value.strip_suffix(')'))
    {
        let (base_key, path, wildcard) = parse_descriptor_key(key_expression)?;
        let indices = descriptor_indices(wildcard, range)?;
        let secp = bitcoin::secp256k1::Secp256k1::verification_only();
        let mut scripts = Vec::with_capacity(indices.len());
        for index in indices {
            let xonly = match &base_key {
                DescriptorKey::PublicKey(public_key) => bitcoin::XOnlyPublicKey::from(*public_key),
                DescriptorKey::XOnlyPublicKey(public_key) => *public_key,
                DescriptorKey::Xpriv(xpriv) => {
                    let mut derivation = path.clone();
                    if let Some(index) = index {
                        derivation = derivation.child(index.into());
                    }
                    xpriv
                        .derive_priv(&bitcoin::secp256k1::Secp256k1::new(), &derivation)?
                        .private_key
                        .public_key(&bitcoin::secp256k1::Secp256k1::new())
                        .x_only_public_key()
                        .0
                }
                DescriptorKey::Xpub(xpub) => {
                    let mut derivation = path.clone();
                    if let Some(index) = index {
                        derivation = derivation.child(index.into());
                    }
                    xpub.derive_pub(&secp, &derivation)?.to_x_only_pub()
                }
            };
            scripts.push(Address::p2tr(&secp, xonly, None, node.config.network).script_pubkey());
        }
        return Ok(scripts);
    }
    let Some((kind, key_expression)) = descriptor
        .strip_suffix(')')
        .and_then(|value| value.split_once('('))
        .filter(|(kind, _)| matches!(*kind, "pkh" | "wpkh"))
    else {
        bail!(
            "unsupported descriptor; use addr(...), raw(...), pk(...), pkh(...), wpkh(...), combo(...), multi(...), sortedmulti(...), sh(...), wsh(...), tr(...), or rawtr(...)"
        )
    };
    let (base_key, path, wildcard) = parse_descriptor_key(key_expression)?;
    let indices = descriptor_indices(wildcard, range)?;
    let secp = bitcoin::secp256k1::Secp256k1::verification_only();
    let mut scripts = Vec::with_capacity(indices.len());
    for index in indices {
        let public_key = match &base_key {
            DescriptorKey::PublicKey(public_key) => *public_key,
            DescriptorKey::XOnlyPublicKey(_) => {
                bail!("x-only public keys are only supported by tr descriptors")
            }
            DescriptorKey::Xpriv(xpriv) => {
                let mut derivation = path.clone();
                if let Some(index) = index {
                    derivation = derivation.child(index.into());
                }
                xpriv
                    .derive_priv(&bitcoin::secp256k1::Secp256k1::new(), &derivation)?
                    .private_key
                    .public_key(&bitcoin::secp256k1::Secp256k1::new())
                    .into()
            }
            DescriptorKey::Xpub(xpub) => {
                let mut derivation = path.clone();
                if let Some(index) = index {
                    derivation = derivation.child(index.into());
                }
                xpub.derive_pub(&secp, &derivation)?.public_key.into()
            }
        };
        let script = if kind == "pkh" {
            Address::p2pkh(public_key, node.config.network).script_pubkey()
        } else {
            let compressed = bitcoin::CompressedPublicKey::try_from(public_key)
                .map_err(|_| anyhow!("wpkh requires a compressed public key"))?;
            Address::p2wpkh(&compressed, node.config.network).script_pubkey()
        };
        scripts.push(script);
    }
    Ok(scripts)
}

enum DescriptorKey {
    PublicKey(bitcoin::PublicKey),
    XOnlyPublicKey(bitcoin::XOnlyPublicKey),
    Xpriv(bitcoin::bip32::Xpriv),
    Xpub(bitcoin::bip32::Xpub),
}

fn expand_multisig_descriptor(
    _node: &Arc<Node>,
    arguments: &str,
    range: Option<(u32, u32)>,
    sorted: bool,
) -> Result<Vec<ScriptBuf>> {
    let arguments = arguments.split(',').collect::<Vec<_>>();
    if arguments.len() < 2 {
        bail!("multisig descriptor requires a threshold and keys")
    }
    let required = arguments[0]
        .parse::<u64>()
        .map_err(|_| anyhow!("multisig threshold must be an integer"))?;
    let keys = arguments[1..]
        .iter()
        .map(|key| parse_descriptor_key(key))
        .collect::<Result<Vec<_>>>()?;
    let key_count = u64::try_from(keys.len()).map_err(|_| anyhow!("too many multisig keys"))?;
    if required == 0 || required > key_count || key_count > 16 {
        bail!("multisig threshold must be between 1 and the number of keys (maximum 16)")
    }
    let wildcard = keys.iter().any(|(_, _, wildcard)| *wildcard);
    if keys
        .iter()
        .any(|(_, _, key_wildcard)| *key_wildcard != wildcard)
    {
        bail!("all multisig keys must use the same wildcard form")
    }
    let indices = descriptor_indices(wildcard, range)?;
    let secp = bitcoin::secp256k1::Secp256k1::verification_only();
    let mut scripts = Vec::with_capacity(indices.len());
    for index in indices {
        let mut public_keys = keys
            .iter()
            .map(|(key, path, _)| descriptor_public_key(key, path, index, &secp))
            .collect::<Result<Vec<_>>>()?;
        if sorted {
            public_keys.sort_unstable();
        }
        let mut builder = Builder::new().push_int(required as i64);
        for public_key in &public_keys {
            builder = builder.push_key(public_key);
        }
        scripts.push(
            builder
                .push_int(key_count as i64)
                .push_opcode(bitcoin::blockdata::opcodes::all::OP_CHECKMULTISIG)
                .into_script(),
        );
    }
    Ok(scripts)
}

fn descriptor_public_key(
    key: &DescriptorKey,
    path: &bitcoin::bip32::DerivationPath,
    index: Option<u32>,
    secp: &bitcoin::secp256k1::Secp256k1<bitcoin::secp256k1::VerifyOnly>,
) -> Result<bitcoin::PublicKey> {
    match key {
        DescriptorKey::PublicKey(public_key) => Ok(*public_key),
        DescriptorKey::XOnlyPublicKey(_) => {
            bail!("x-only public keys are only supported by tr descriptors")
        }
        DescriptorKey::Xpriv(xpriv) => {
            let mut derivation = path.clone();
            if let Some(index) = index {
                derivation = derivation.child(index.into());
            }
            Ok(xpriv
                .derive_priv(&bitcoin::secp256k1::Secp256k1::new(), &derivation)?
                .private_key
                .public_key(&bitcoin::secp256k1::Secp256k1::new())
                .into())
        }
        DescriptorKey::Xpub(xpub) => {
            let mut derivation = path.clone();
            if let Some(index) = index {
                derivation = derivation.child(index.into());
            }
            Ok(xpub.derive_pub(secp, &derivation)?.public_key.into())
        }
    }
}

fn descriptor_indices(wildcard: bool, range: Option<(u32, u32)>) -> Result<Vec<Option<u32>>> {
    if wildcard {
        let (start, end) = range.ok_or_else(|| anyhow!("ranged descriptor requires a range"))?;
        if end.saturating_sub(start) >= 10_000 {
            bail!("descriptor range is too large")
        }
        Ok((start..=end).map(Some).collect())
    } else {
        if range.is_some_and(|(start, end)| start != 0 || end != 0) {
            bail!("non-ranged descriptor cannot use a non-zero range")
        }
        Ok(vec![None])
    }
}

fn parse_descriptor_key(
    expression: &str,
) -> Result<(DescriptorKey, bitcoin::bip32::DerivationPath, bool)> {
    let expression = if expression.starts_with('[') {
        let end = expression
            .find(']')
            .ok_or_else(|| anyhow!("descriptor key origin is missing a closing bracket"))?;
        &expression[end + 1..]
    } else {
        expression
    };
    let mut parts = expression.split('/');
    let base = parts
        .next()
        .ok_or_else(|| anyhow!("descriptor key is empty"))?;
    let mut path = Vec::new();
    let mut wildcard = false;
    for part in parts {
        if part == "*" {
            if wildcard {
                bail!("descriptor key contains multiple wildcards")
            }
            wildcard = true;
        } else {
            if wildcard {
                bail!("descriptor key path follows wildcard")
            }
            path.push(part.parse::<bitcoin::bip32::ChildNumber>()?);
        }
    }
    let key = if let Ok(public_key) = bitcoin::PublicKey::from_str(base) {
        if !path.is_empty() || wildcard {
            bail!("raw public keys cannot be derived")
        }
        DescriptorKey::PublicKey(public_key)
    } else if let Ok(public_key) = bitcoin::XOnlyPublicKey::from_str(base) {
        if !path.is_empty() || wildcard {
            bail!("raw public keys cannot be derived")
        }
        DescriptorKey::XOnlyPublicKey(public_key)
    } else if let Ok(private_key) = base.parse::<bitcoin::bip32::Xpriv>() {
        DescriptorKey::Xpriv(private_key)
    } else {
        DescriptorKey::Xpub(base.parse::<bitcoin::bip32::Xpub>()?)
    };
    Ok((key, path.into(), wildcard))
}

fn descriptor_key_origin(
    expression: &str,
) -> Result<Option<(bitcoin::bip32::Fingerprint, bitcoin::bip32::DerivationPath)>> {
    let Some(expression) = expression.strip_prefix('[') else {
        return Ok(None);
    };
    let end = expression
        .find(']')
        .ok_or_else(|| anyhow!("descriptor key origin is missing a closing bracket"))?;
    let origin = &expression[..end];
    let mut parts = origin.split('/');
    let fingerprint = parts
        .next()
        .ok_or_else(|| anyhow!("descriptor key origin is empty"))?
        .parse::<bitcoin::bip32::Fingerprint>()?;
    let path = parts
        .map(str::parse::<bitcoin::bip32::ChildNumber>)
        .collect::<std::result::Result<Vec<_>, _>>()?
        .into();
    Ok(Some((fingerprint, path)))
}

fn get_tx_spending_prevout(node: &Arc<Node>, params: &Value) -> Result<Value> {
    let outpoints = params
        .get(0)
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("gettxspendingprevout expects an array"))?
        .iter()
        .map(|value| {
            let value = value
                .as_object()
                .ok_or_else(|| anyhow!("outpoint must be an object"))?;
            if let Some(key) = value
                .keys()
                .find(|key| !matches!(key.as_str(), "txid" | "vout"))
            {
                bail!("Unexpected key {key}")
            }
            let txid: Txid = value
                .get("txid")
                .and_then(Value::as_str)
                .ok_or_else(|| anyhow!("outpoint txid must be a string"))?
                .parse()?;
            let vout = value.get("vout").ok_or_else(|| anyhow!("Missing vout"))?;
            if vout.as_i64().is_some_and(|vout| vout < 0) {
                bail!("Invalid parameter, vout cannot be negative")
            }
            let vout = vout
                .as_u64()
                .ok_or_else(|| anyhow!("outpoint vout must be an integer"))?;
            let vout = u32::try_from(vout).map_err(|_| anyhow!("outpoint vout is too large"))?;
            Ok(OutPoint::new(txid, vout))
        })
        .collect::<Result<Vec<OutPoint>>>()?;
    if outpoints.is_empty() {
        bail!("gettxspendingprevout expects at least one output")
    }
    let options = params
        .get(1)
        .filter(|value| !value.is_null())
        .cloned()
        .unwrap_or_else(|| json!({}));
    let options = options
        .as_object()
        .ok_or_else(|| anyhow!("gettxspendingprevout options must be an object"))?;
    if options
        .keys()
        .any(|key| key != "mempool_only" && key != "return_spending_tx")
    {
        let key = options
            .keys()
            .find(|key| *key != "mempool_only" && *key != "return_spending_tx")
            .expect("unknown option exists");
        bail!("Unexpected key {key}")
    }
    let mempool_only = options
        .get("mempool_only")
        .map(|value| {
            value
                .as_bool()
                .ok_or_else(|| anyhow!("mempool_only must be a boolean"))
        })
        .transpose()?
        .unwrap_or(!node.config.txospenderindex);
    let return_spending_tx = options
        .get("return_spending_tx")
        .map(|value| {
            value
                .as_bool()
                .ok_or_else(|| anyhow!("return_spending_tx must be a boolean"))
        })
        .transpose()?
        .unwrap_or(false);
    let mut result = outpoints
        .iter()
        .map(|outpoint| json!({"txid": outpoint.txid.to_string(), "vout": outpoint.vout}))
        .collect::<Vec<_>>();
    let mempool = node.mempool.read();
    for (index, outpoint) in outpoints.iter().enumerate() {
        let Some(spender_txid) = mempool.spender(outpoint) else {
            continue;
        };
        let Some(entry) = mempool.get(&spender_txid) else {
            continue;
        };
        result[index]["spendingtxid"] = json!(spender_txid.to_string());
        if return_spending_tx {
            result[index]["spendingtx"] = json!(hex::encode(serialize(&entry.transaction)));
        }
    }
    drop(mempool);
    if !mempool_only {
        if !node.config.txospenderindex {
            if let Some(outpoint) = outpoints.iter().enumerate().find_map(|(index, outpoint)| {
                result[index]
                    .get("spendingtxid")
                    .is_none()
                    .then_some(outpoint)
            }) {
                bail!(
                    "No spending transaction for the outpoint {}:{} in mempool, and txospenderindex is unavailable.",
                    outpoint.txid,
                    outpoint.vout
                );
            }
        }
        let mut chain = node.chain.write();
        for (index, outpoint) in outpoints.iter().enumerate() {
            if result[index].get("spendingtxid").is_some() {
                continue;
            }
            let Some((spender_txid, _, blockhash, _)) = chain.spending_transaction(outpoint) else {
                continue;
            };
            result[index]["spendingtxid"] = json!(spender_txid.to_string());
            result[index]["blockhash"] = json!(blockhash.to_string());
            if return_spending_tx && let Some(transaction) = chain.transaction(&spender_txid)? {
                result[index]["spendingtx"] = json!(hex::encode(serialize(&transaction.0)));
            }
        }
    }
    Ok(Value::Array(result))
}

fn rpc_transaction(
    transaction: &Transaction,
    blockhash: Option<&str>,
    confirmations: Option<i64>,
    time: Option<u32>,
    blocktime: Option<u32>,
    network: Network,
) -> Value {
    let vin = transaction
        .input
        .iter()
        .map(|input| {
            let mut result = if input.previous_output.is_null() {
                json!({
                    "coinbase": hex::encode(input.script_sig.as_bytes()),
                    "sequence": input.sequence.to_consensus_u32()
                })
            } else {
                json!({
                    "txid": input.previous_output.txid.to_string(),
                    "vout": input.previous_output.vout,
                    "scriptSig": {"asm": input.script_sig.to_asm_string(), "hex": hex::encode(input.script_sig.as_bytes())},
                    "sequence": input.sequence.to_consensus_u32(),
                })
            };
            if !input.witness.is_empty() {
                result["txinwitness"] = json!(
                    input
                        .witness
                        .to_vec()
                        .into_iter()
                        .map(hex::encode)
                        .collect::<Vec<_>>()
                );
            }
            result
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
                "scriptPubKey": script_json_with_network(&output.script_pubkey, Some(network)),
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

fn add_prevout_details(
    transaction_json: &mut Value,
    transaction: &Transaction,
    spent_outputs: &[bitcoin::TxOut],
    chain: &mut chain::ChainState,
    network: Network,
) -> Result<()> {
    let vin = transaction_json
        .get_mut("vin")
        .and_then(Value::as_array_mut)
        .ok_or_else(|| anyhow!("transaction JSON has no vin array"))?;
    for (input_index, input) in transaction.input.iter().enumerate() {
        if input.previous_output.is_null() {
            continue;
        }
        let output = spent_outputs
            .get(input_index)
            .ok_or_else(|| anyhow!("transaction undo is missing input {input_index}"))?;
        let (previous_transaction, location) = chain
            .transaction(&input.previous_output.txid)?
            .ok_or_else(|| anyhow!("previous transaction is unavailable"))?;
        let prevout = json!({
            "generated": previous_transaction.is_coinbase(),
            "height": location.height,
            "value": sat_to_btc(output.value.to_sat()),
            "scriptPubKey": script_json_with_network(&output.script_pubkey, Some(network)),
        });
        let input_json = vin
            .get_mut(input_index)
            .ok_or_else(|| anyhow!("transaction JSON input index is inconsistent"))?;
        input_json["prevout"] = prevout;
    }
    add_transaction_fee(transaction_json, transaction, spent_outputs)
}

fn add_transaction_fee(
    transaction_json: &mut Value,
    transaction: &Transaction,
    spent_outputs: &[bitcoin::TxOut],
) -> Result<()> {
    let input_total = spent_outputs
        .iter()
        .map(|output| output.value.to_sat())
        .try_fold(0u64, u64::checked_add)
        .ok_or_else(|| anyhow!("transaction input total overflowed"))?;
    let output_total = transaction
        .output
        .iter()
        .map(|output| output.value.to_sat())
        .try_fold(0u64, u64::checked_add)
        .ok_or_else(|| anyhow!("transaction output total overflowed"))?;
    if input_total >= output_total {
        transaction_json["fee"] = json!(sat_to_btc(input_total - output_total));
    }
    Ok(())
}

fn script_json_with_network(script: &bitcoin::Script, network: Option<Network>) -> Value {
    let script_type = script_type_for_decode(script);
    let mut result = json!({
        "asm": script.to_asm_string(),
        "hex": hex::encode(script.as_bytes()),
        "type": script_type,
    });
    if let Some(network) = network {
        result["desc"] = json!(inferred_script_descriptor_for_network(network, script));
        if script_type != "pubkey"
            && let Ok(address) = Address::from_script(script, network)
        {
            result["address"] = json!(address.to_string());
        }
    }
    result
}

fn param<T: serde::de::DeserializeOwned>(params: &Value, index: usize) -> Result<T> {
    let value = params
        .as_array()
        .and_then(|values| values.get(index))
        .ok_or_else(|| anyhow!("missing parameter {index}"))?;
    Ok(serde_json::from_value(value.clone())?)
}

pub(crate) fn optional_bool(
    params: &Value,
    index: usize,
    default: bool,
    name: &str,
) -> Result<bool> {
    let Some(value) = params.get(index).filter(|value| !value.is_null()) else {
        return Ok(default);
    };
    value
        .as_bool()
        .ok_or_else(|| anyhow!("{name} must be a boolean"))
}

pub(crate) fn optional_str<'a>(
    params: &'a Value,
    index: usize,
    default: &'a str,
    name: &str,
) -> Result<&'a str> {
    let Some(value) = params.get(index).filter(|value| !value.is_null()) else {
        return Ok(default);
    };
    value
        .as_str()
        .ok_or_else(|| anyhow!("{name} must be a string"))
}

fn optional_i64(params: &Value, index: usize, default: i64, name: &str) -> Result<i64> {
    let Some(value) = params.get(index).filter(|value| !value.is_null()) else {
        return Ok(default);
    };
    value
        .as_i64()
        .ok_or_else(|| anyhow!("{name} must be an integer"))
}

pub(crate) fn optional_u64(params: &Value, index: usize, default: u64, name: &str) -> Result<u64> {
    let Some(value) = params.get(index).filter(|value| !value.is_null()) else {
        return Ok(default);
    };
    value
        .as_u64()
        .ok_or_else(|| anyhow!("{name} must be a non-negative integer"))
}

fn rpc_error(error: &anyhow::Error) -> Value {
    let message = error.to_string();
    let code = rpc_error_code(&message);
    json!({"code": code, "message": message})
}

fn rpc_error_code(message: &str) -> i32 {
    let lower = message.to_ascii_lowercase();
    if message == "Method not found" {
        return -32601;
    }
    if lower == "can only import the mempool after the block download and sync is done." {
        return -28;
    }
    if lower == "transaction outputs already in utxo set" {
        return -27;
    }
    if lower.contains("tx decode failed")
        || lower.contains("transaction decode failed")
        || lower.contains("block decode failed")
    {
        return -22;
    }
    if lower == "input not found or already spent" {
        return -25;
    }
    if lower == "previous output scriptpubkey mismatch" {
        return -22;
    }
    if lower == "amount out of range" || lower == "missing amount" {
        return -3;
    }
    if lower == "unknown filtertype"
        || lower == "block not found"
        || lower == "block hash not found"
        || lower == "block not found in chain"
        || lower == "filter not found. block was not connected to active chain."
        || lower == "transaction not found"
        || lower == "transaction not yet in block"
        || lower == "transaction not in mempool"
        || lower == "not all transactions found in specified or retrieved block"
        || lower.starts_with("no such transaction found in the provided block.")
        || lower.starts_with("no such mempool transaction.")
        || lower.starts_with("no such mempool or blockchain transaction.")
        || lower.contains("not in private broadcast queue")
        || lower.starts_with("the genesis block coinbase is not considered")
    {
        return -5;
    }
    if lower == "filter not found. this error is unexpected and indicates index corruption." {
        return -32603;
    }
    if lower == "mallocinfo mode not available"
        || lower.starts_with("unknown mode ")
        || lower.starts_with("missing parameter ")
        || lower.starts_with("too many positional arguments ")
        || lower.starts_with("unknown named parameter ")
        || lower == "block is not in main chain"
        || lower == "block height out of range"
        || lower == "block does not exist at specified height"
        || lower.starts_with("invalid block count:")
        || lower.starts_with("invalid blockhash:")
        || lower.starts_with("invalid nblocks.")
        || lower.starts_with("invalid selected statistic ")
        || lower.contains("specified more than once")
        || lower.contains("must be between ")
        || lower.contains("must not be negative")
        || lower.contains("cannot be negative")
        || lower.contains("is out of range")
        || lower == "missing redeemscript/witnessscript"
        || lower == "redeemscript does not correspond to witnessscript"
        || lower == "redeemscript/witnessscript does not match scriptpubkey"
    {
        return -8;
    }
    if lower.contains(" must be a ")
        || lower.contains(" must be an ")
        || lower.starts_with("params must be ")
        || lower.contains(" expects an array")
    {
        return -3;
    }
    -1
}

fn sat_to_btc(satoshis: u64) -> f64 {
    satoshis as f64 / 100_000_000.0
}

fn sat_to_btc_signed(satoshis: i64) -> f64 {
    satoshis as f64 / 100_000_000.0
}

fn work_to_f64(work: bitcoin::pow::Work) -> f64 {
    let bytes = work.to_be_bytes();
    let Some(first) = bytes.iter().position(|byte| *byte != 0) else {
        return 0.0;
    };
    let end = (first + 8).min(bytes.len());
    let mut significand = 0u64;
    for byte in &bytes[first..end] {
        significand = (significand << 8) | u64::from(*byte);
    }
    let exponent = i32::try_from((bytes.len() - end) * 8).unwrap_or(i32::MAX);
    (significand as f64) * 2f64.powi(exponent)
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

fn rpc_connection_type(connection_type: &str) -> &str {
    match connection_type {
        "outbound-full" => "outbound-full-relay",
        other => other,
    }
}

fn method_params_string(params: &Value) -> &str {
    params.get(0).and_then(Value::as_str).unwrap_or("")
}

fn rpc_help(method: &str) -> String {
    const METHODS: &[&str] = &[
        "getblockchaininfo",
        "getdeploymentinfo",
        "getblockcount",
        "getbestblockhash",
        "getblockhash",
        "getblockheader",
        "getblock",
        "getblockfilter",
        "getblockstats",
        "getchaintxstats",
        "getnetworkhashps",
        "getmemoryinfo",
        "gettxoutproof",
        "verifytxoutproof",
        "submitheader",
        "getblockfrompeer",
        "invalidateblock",
        "reconsiderblock",
        "preciousblock",
        "getrawtransaction",
        "decoderawtransaction",
        "createrawtransaction",
        "decodescript",
        "combinerawtransaction",
        "createpsbt",
        "decodepsbt",
        "converttopsbt",
        "analyzepsbt",
        "combinepsbt",
        "joinpsbts",
        "finalizepsbt",
        "utxoupdatepsbt",
        "descriptorprocesspsbt",
        "signmessagewithprivkey",
        "verifymessage",
        "createmultisig",
        "sendrawtransaction",
        "getprivatebroadcastinfo",
        "abortprivatebroadcast",
        "signrawtransactionwithkey",
        "submitblock",
        "getblocktemplate",
        "getmininginfo",
        "prioritisetransaction",
        "getprioritisedtransactions",
        "generatetoaddress",
        "generatetodescriptor",
        "generateblock",
        "generate",
        "submitpackage",
        "testmempoolaccept",
        "verifychain",
        "gettxout",
        "gettxspendingprevout",
        "getmempoolinfo",
        "getrawmempool",
        "getorphantxs",
        "getmempoolentry",
        "getmempoolancestors",
        "getmempooldescendants",
        "getmempoolcluster",
        "getmempoolfeeratediagram",
        "savemempool",
        "importmempool",
        "gettxoutsetinfo",
        "dumptxoutset",
        "loadtxoutset",
        "pruneblockchain",
        "waitfornewblock",
        "waitforblock",
        "waitforblockheight",
        "scantxoutset",
        "scanblocks",
        "getdescriptoractivity",
        "getchainstates",
        "getchaintips",
        "getnetworkinfo",
        "getpeerinfo",
        "getnettotals",
        "getnodeaddresses",
        "getaddrmaninfo",
        "addpeeraddress",
        "getrawaddrman",
        "sendmsgtopeer",
        "addconnection",
        "addnode",
        "disconnectnode",
        "getaddednodeinfo",
        "setban",
        "listbanned",
        "clearbanned",
        "ping",
        "setnetworkactive",
        "getrpcinfo",
        "stop",
        "estimatesmartfee",
        "estimaterawfee",
        "getdifficulty",
        "getconnectioncount",
        "uptime",
        "getindexinfo",
        "getzmqnotifications",
        "logging",
        "validateaddress",
        "deriveaddresses",
        "getdescriptorinfo",
    ];
    if method.is_empty() {
        METHODS.join("\n")
    } else if method == "logging" {
        format!(
            "logging: Gets and sets the logging configuration.\nvalid logging categories are: {}",
            LOG_CATEGORIES.join(", ")
        )
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
    use crate::config::{Args, Config};
    use bitcoin::Network;
    use bitcoin::absolute::LockTime;
    use bitcoin::block::{Header, Version as BlockVersion};
    use bitcoin::blockdata::script::ScriptBuf;
    use bitcoin::blockdata::transaction::{OutPoint, TxIn, TxOut, Version};
    use bitcoin::blockdata::witness::Witness;
    use bitcoin::hashes::Hash;
    use clap::Parser;

    #[test]
    fn http_connection_token_matching_is_case_insensitive() {
        let headers = "Connection: keep-alive, Upgrade\r\nX-Test: yes\r\n";
        assert!(header_has_token(headers, "connection", "KEEP-ALIVE"));
        assert!(!header_has_token(headers, "connection", "close"));
    }

    #[test]
    fn http_authorization_header_name_is_case_insensitive() {
        assert!(authorization_matches(
            "aUtHoRiZaTiOn: Basic secret\r\n",
            "Basic secret"
        ));
        assert!(!authorization_matches(
            "X-Authorization: Basic secret\r\n",
            "Basic secret"
        ));
    }

    #[tokio::test]
    async fn rpc_work_queue_caps_pending_requests() {
        let queue = RpcWorkQueue::new(1, 1);
        let first = queue.acquire().await.expect("first request permit");
        let pending = queue
            .pending
            .clone()
            .try_acquire_owned()
            .expect("configured queue slot");
        assert!(queue.pending.clone().try_acquire_owned().is_err());
        assert_eq!(queue.workers.available_permits(), 0);
        drop(pending);
        drop(first);
        assert!(queue.acquire().await.is_some());
    }

    fn basic_auth_header(username: &str, password: &str) -> String {
        let credentials = format!("{username}:{password}");
        format!(
            "Authorization: Basic {}\r\n",
            base64::engine::general_purpose::STANDARD.encode(credentials)
        )
    }

    #[test]
    fn rpc_acl_and_configured_authentication_match_core_modes() {
        let directory = tempfile::tempdir().unwrap();
        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--rpcallowip=192.0.2.0/24",
            "--rpcuser=rpc-user",
            "--rpcpassword=rpc-password",
        ])
        .unwrap();
        let node = Node::open(Config::from_args(args).unwrap()).unwrap();
        assert!(node.rpc_cookie.is_none());
        assert!(rpc_client_allowed(&node, "127.0.0.1".parse().unwrap()));
        assert!(rpc_client_allowed(&node, "192.0.2.7".parse().unwrap()));
        assert!(!rpc_client_allowed(&node, "198.51.100.7".parse().unwrap()));
        assert!(authorized(
            &node,
            &basic_auth_header("rpc-user", "rpc-password")
        ));
        assert!(!authorized(
            &node,
            &basic_auth_header("rpc-user", "wrong-password")
        ));

        let directory = tempfile::tempdir().unwrap();
        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--rpcauth=hashed:salt$84ec44c7d6fc41917953a1dafca3c7d7856f7a9d0328b991b76f0d36be1224b9",
        ])
        .unwrap();
        let node = Node::open(Config::from_args(args).unwrap()).unwrap();
        assert!(node.rpc_cookie.is_some());
        assert!(authorized(&node, &basic_auth_header("hashed", "password")));
        assert!(!authorized(
            &node,
            &basic_auth_header("hashed", "incorrect")
        ));
        assert!(authorized(
            &node,
            &basic_auth_header("__cookie__", &node.rpc_cookie.as_deref().unwrap()[11..])
        ));

        let directory = tempfile::tempdir().unwrap();
        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--norpccookiefile",
        ])
        .unwrap();
        let node = Node::open(Config::from_args(args).unwrap()).unwrap();
        assert!(node.rpc_cookie.is_none());
        assert!(authorized_user(&node, "").is_none());
    }

    #[test]
    fn rpc_hmac_matches_sha256_hmac_vector() {
        assert_eq!(
            hex::encode(hmac_sha256(b"salt", b"password")),
            "84ec44c7d6fc41917953a1dafca3c7d7856f7a9d0328b991b76f0d36be1224b9"
        );
    }

    #[test]
    fn rpc_method_whitelists_cover_single_and_batch_requests() {
        let directory = tempfile::tempdir().unwrap();
        let args = Args::try_parse_from([
            "bitcoind-rs",
            "--datadir",
            directory.path().to_str().unwrap(),
            "--rpcuser=alice",
            "--rpcpassword=rpc-password",
            "--rpcwhitelist=alice:getblock,getblockchaininfo",
        ])
        .unwrap();
        let node = Node::open(Config::from_args(args).unwrap()).unwrap();
        let headers = basic_auth_header("alice", "rpc-password");
        let username = authorized_user(&node, &headers).unwrap();
        assert_eq!(username, "alice");
        assert!(rpc_request_allowed(
            &node,
            &username,
            br#"{"jsonrpc":"1.0","method":"getblock","params":[],"id":1}"#
        ));
        assert!(!rpc_request_allowed(
            &node,
            &username,
            br#"{"jsonrpc":"1.0","method":"getrawmempool","params":[],"id":1}"#
        ));
        assert!(!rpc_request_allowed(
            &node,
            &username,
            br#"[{"method":"getblock","id":1},{"method":"getrawmempool","id":2}]"#
        ));
    }

    #[test]
    fn http_statuses_match_core_json_rpc_error_classes() {
        assert_eq!(
            json_rpc_error_status(&json!({"error": {"code": -32600}})),
            "400 Bad Request"
        );
        assert_eq!(
            json_rpc_error_status(&json!({"error": {"code": -32601}})),
            "404 Not Found"
        );
        assert_eq!(
            json_rpc_error_status(&json!({"error": {"code": -1}})),
            "500 Internal Server Error"
        );
        assert_eq!(
            json_rpc_error_status(&json!({"result": 1, "error": null})),
            "200 OK"
        );
        assert_eq!(
            rpc_error(&anyhow!("Method not found"))["code"],
            json!(-32601)
        );
        assert_eq!(
            rpc_error_code(
                "Can only import the mempool after the block download and sync is done."
            ),
            -28
        );
        assert_eq!(rpc_error_code("unknown mode foobar"), -8);
        assert_eq!(rpc_error_code("mode must be a string"), -3);
        assert_eq!(rpc_error_code("TX decode failed"), -22);
        assert_eq!(rpc_error_code("TX decode failed: invalid hex"), -22);
        assert_eq!(rpc_error_code("Input not found or already spent"), -25);
        assert_eq!(rpc_error_code("Block not found"), -5);
        assert_eq!(rpc_error_code("Transaction not yet in block"), -5);
        assert_eq!(
            rpc_error_code("Not all transactions found in specified or retrieved block"),
            -5
        );
        assert_eq!(rpc_error_code("Block height out of range"), -8);
        assert_eq!(
            rpc_error_code("Block does not exist at specified height"),
            -8
        );
        assert_eq!(
            rpc_error_code("Invalid nblocks. Must be a positive number or -1."),
            -8
        );
        assert_eq!(rpc_error_code("Unknown filtertype"), -5);
        assert_eq!(
            rpc_error_code("Index is not enabled for filtertype basic"),
            -1
        );
        assert_eq!(
            rpc_error_code("Filter not found. Block was not connected to active chain."),
            -5
        );
        assert_eq!(
            rpc_error_code(
                "Filter not found. This error is unexpected and indicates index corruption."
            ),
            -32603
        );
    }

    #[test]
    fn rest_error_status_distinguishes_bad_requests_and_missing_resources() {
        assert_eq!(
            rest_error_status(&anyhow!("invalid hash")),
            "400 Bad Request"
        );
        assert_eq!(
            rest_error_status(&anyhow!("block not found")),
            "404 Not Found"
        );
        assert_eq!(
            rest_error_status(&anyhow!("I/O error reading block")),
            "500 Internal Server Error"
        );
    }

    #[tokio::test]
    async fn http_reader_preserves_pipelined_requests() -> Result<()> {
        let listener = TcpListener::bind("127.0.0.1:0").await?;
        let address = listener.local_addr()?;
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await?;
            let mut connection = HttpConnection::new(stream);
            let first = connection
                .read_request()
                .await?
                .ok_or_else(|| anyhow!("first request missing"))?;
            let second = connection
                .read_request()
                .await?
                .ok_or_else(|| anyhow!("second request missing"))?;
            Ok::<_, anyhow::Error>((first, second))
        });
        let mut client = TcpStream::connect(address).await?;
        client
            .write_all(
                b"POST / HTTP/1.1\r\nHost: localhost\r\nContent-Length: 3\r\nConnection: keep-alive\r\n\r\nabcGET /rest/chaininfo.json HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n",
            )
            .await?;
        let (first, second) = server.await??;
        assert_eq!(first.method, "POST");
        assert_eq!(first.target, "/");
        assert_eq!(first.body, b"abc");
        assert!(first.keep_alive);
        assert_eq!(second.method, "GET");
        assert_eq!(second.target, "/rest/chaininfo.json");
        assert!(second.body.is_empty());
        assert!(!second.keep_alive);
        Ok(())
    }

    fn proof_transaction(tag: u8) -> Transaction {
        Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(Txid::from_byte_array([tag; 32]), 0),
                script_sig: ScriptBuf::from_bytes(vec![0x00; 8]),
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
    fn getorphantxs_reports_peer_orphans_at_each_verbosity() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let transaction = proof_transaction(7);
        let txid = transaction.compute_txid().to_string();
        let raw = hex::encode(serialize(&transaction));
        assert!(node.accept_peer_transaction_from(42, transaction).is_err());

        assert_eq!(
            dispatch_method(&node, "getorphantxs", &json!([])).unwrap(),
            json!([txid])
        );
        let verbose = dispatch_method(&node, "getorphantxs", &json!([1])).unwrap();
        assert_eq!(verbose[0]["txid"], txid);
        assert_eq!(verbose[0]["from"], json!([42]));
        assert!(verbose[0]["bytes"].as_u64().unwrap() > 0);
        assert!(verbose[0]["vsize"].as_u64().unwrap() > 0);
        assert!(verbose[0]["weight"].as_u64().unwrap() > 0);
        let detailed = dispatch_method(&node, "getorphantxs", &json!([2])).unwrap();
        assert_eq!(detailed[0]["hex"], raw);
        assert!(dispatch_method(&node, "getorphantxs", &json!([3])).is_err());
    }

    #[test]
    fn raw_transaction_fee_and_burn_limits_validate_rpc_arguments() {
        assert_eq!(parse_max_fee_rate(None).unwrap(), Some(10_000_000));
        assert_eq!(
            parse_max_fee_rate(Some(&json!("0.1"))).unwrap(),
            Some(10_000_000)
        );
        assert_eq!(parse_max_fee_rate(Some(&json!(0))).unwrap(), None);
        assert!(parse_max_fee_rate(Some(&json!(-1))).is_err());
        assert!(parse_max_fee_rate(Some(&json!(1.1))).is_err());
        assert!(parse_max_fee_rate(Some(&json!("1"))).is_err());
        assert_eq!(max_fee_for_vsize(1, 101), 1);
        assert!(!exceeds_max_fee(1, 101, Some(1)));
        assert!(exceeds_max_fee(2, 101, Some(1)));
        assert_eq!(parse_max_burn_amount(None).unwrap(), 0);
        assert_eq!(parse_max_burn_amount(Some(&json!(0.00000001))).unwrap(), 1);
        assert_eq!(
            parse_max_burn_amount(Some(&json!("0.00000001"))).unwrap(),
            1
        );

        let mut transaction = proof_transaction(8);
        transaction.output.push(TxOut {
            value: Amount::from_sat(1),
            script_pubkey: Builder::new()
                .push_opcode(OP_RETURN)
                .push_slice([1u8])
                .into_script(),
        });
        assert!(validate_burn_amount(&transaction, 0).is_err());
        assert!(validate_burn_amount(&transaction, 1).is_ok());

        transaction.output.push(TxOut {
            value: Amount::from_sat(1),
            script_pubkey: ScriptBuf::from_bytes(vec![0x4c]),
        });
        assert!(validate_burn_amount(&transaction, 0).is_err());

        transaction.output.push(TxOut {
            value: Amount::from_sat(1),
            script_pubkey: ScriptBuf::from_bytes(vec![0x51; MAX_SCRIPT_SIZE + 1]),
        });
        assert!(validate_burn_amount(&transaction, 0).is_err());

        let rejected = rejected_transaction_json(&transaction, &MempoolError::FeeRate);
        assert_eq!(rejected["reject-reason"], "mempool min fee not met");
        assert_eq!(
            rejected["reject-details"],
            "transaction fee rate is below the relay minimum"
        );
        let missing =
            rejected_transaction_json(&transaction, &MempoolError::MissingInput(OutPoint::null()));
        assert!(missing.get("reject-details").is_none());
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
        let (_, matches, total) = parse_merkle_proof(&json!([hex::encode(proof)]))
            .unwrap()
            .unwrap();
        assert_eq!(total, block.txdata.len());
        assert_eq!(matches, requested,);
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
        assert!(
            parse_merkle_proof(&json!([hex::encode(proof)]))
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn merkle_proof_rejects_core_excessive_transaction_counts() {
        let mut block = bitcoin::Block {
            header: Header {
                version: BlockVersion::TWO,
                prev_blockhash: BlockHash::all_zeros(),
                merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                time: 1,
                bits: bitcoin::pow::CompactTarget::from_consensus(0x207f_ffff),
                nonce: 0,
            },
            txdata: vec![proof_transaction(9)],
        };
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        let txid = block.txdata[0].compute_txid();
        let mut proof = serialize_merkle_proof(&block, &[txid]).unwrap();
        proof[80..84].copy_from_slice(
            &u32::try_from(MAX_MERKLE_PROOF_TRANSACTIONS + 1)
                .unwrap()
                .to_le_bytes(),
        );
        assert!(parse_merkle_proof(&json!([hex::encode(proof)])).is_err());
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
        let (_, matches, _) = parse_merkle_proof(&json!([hex::encode(proof)]))
            .unwrap()
            .unwrap();
        assert!(matches.is_empty());
    }

    #[test]
    fn verify_merkle_proof_requires_an_active_chain_block() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let genesis = {
            let hash = node.chain.read().best_hash();
            node.chain.write().block(&hash).unwrap().unwrap()
        };
        let txid = genesis.txdata[0].compute_txid();
        let proof = serialize_merkle_proof(&genesis, &[txid]).unwrap();
        assert_eq!(
            dispatch_method(&node, "verifytxoutproof", &json!([hex::encode(proof)]),).unwrap(),
            json!([txid.to_string()])
        );
        let no_index_lookup = get_txout_proof(&node, &json!([[txid.to_string()]])).unwrap_err();
        assert_eq!(no_index_lookup.to_string(), "Transaction not yet in block");
        assert!(
            get_txout_proof(
                &node,
                &json!([
                    [txid.to_string(), txid.to_string()],
                    genesis.block_hash().to_string()
                ]),
            )
            .is_err()
        );

        let mut off_chain = bitcoin::Block {
            header: Header {
                version: BlockVersion::TWO,
                prev_blockhash: BlockHash::all_zeros(),
                merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                time: 1,
                bits: bitcoin::pow::CompactTarget::from_consensus(0x207f_ffff),
                nonce: 0,
            },
            txdata: vec![proof_transaction(8)],
        };
        off_chain.header.merkle_root = off_chain.compute_merkle_root().unwrap();
        let off_chain_proof =
            serialize_merkle_proof(&off_chain, &[off_chain.txdata[0].compute_txid()]).unwrap();
        assert!(
            dispatch_method(
                &node,
                "verifytxoutproof",
                &json!([hex::encode(off_chain_proof)]),
            )
            .is_err()
        );
    }

    #[test]
    fn block_stats_report_satoshi_amounts() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let hash = node.chain.read().best_hash();
        let stats = get_block_stats(&node, &json!([hash.to_string()])).unwrap();
        assert!(stats.get("size").is_none());
        assert_eq!(stats["total_out"], json!(0));
        assert_eq!(stats["subsidy"], json!(5_000_000_000u64));
        assert_eq!(stats["totalfee"], json!(0));
        assert_eq!(stats["utxo_increase_actual"], json!(0));
        assert_eq!(stats["utxo_size_inc_actual"], json!(0));
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
        let invalid_statistic =
            get_block_stats(&node, &json!([hash.to_string(), ["not_a_block_statistic"]]))
                .unwrap_err();
        assert_eq!(
            invalid_statistic.to_string(),
            "Invalid selected statistic 'not_a_block_statistic'"
        );
        assert_eq!(rpc_error(&invalid_statistic)["code"], json!(-8));
        let header = get_block_header(&node, &json!([hash.to_string()])).unwrap();
        assert!(header.get("previousblockhash").is_none());
        assert!(header.get("nextblockhash").is_none());
        let block = get_block(&node, &json!([hash.to_string(), 1])).unwrap();
        assert!(block.get("previousblockhash").is_none());
        assert!(block.get("nextblockhash").is_none());

        let mined = generate_to_descriptor(&node, &json!([101, "raw(51)"])).unwrap();
        let funding_hash: BlockHash = mined[0].as_str().unwrap().parse().unwrap();
        let funding = node.chain.write().block(&funding_hash).unwrap().unwrap();
        let funding_outpoint = OutPoint::new(funding.txdata[0].compute_txid(), 0);
        let spend = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: funding_outpoint,
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(funding.txdata[0].output[0].value.to_sat() - 1_000),
                script_pubkey: Builder::new().push_int(1).into_script(),
            }],
        };
        let block = generate_block(
            &node,
            &json!(["raw(51)", [hex::encode(serialize(&spend))], true]),
        )
        .unwrap();
        let stats = get_block_stats(&node, &json!([block["hash"].clone()])).unwrap();
        assert_eq!(stats["totalfee"], json!(1_000));
        assert_eq!(stats["utxo_increase_actual"], json!(1));
    }

    #[test]
    fn block_stats_fee_percentiles_follow_core_fractional_boundaries() {
        let mut values = [(10, 1), (20, 1), (30, 1), (40, 1), (50, 1)];
        assert_eq!(
            weighted_fee_percentiles(&mut values, 5),
            [10, 20, 30, 40, 50]
        );
    }

    #[test]
    fn smart_fee_estimate_reports_available_history() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let result = dispatch_method(&node, "estimatesmartfee", &json!([6])).unwrap();
        assert_eq!(result["blocks"], json!(6));
        assert!(result.get("feerate").is_none());
        let one_block = dispatch_method(&node, "estimatesmartfee", &json!([1])).unwrap();
        assert_eq!(one_block["blocks"], json!(2));
        assert!(dispatch_method(&node, "estimatesmartfee", &json!([0])).is_err());
        assert!(dispatch_method(&node, "estimatesmartfee", &json!([6, "invalid"])).is_err());
    }

    #[test]
    fn raw_fee_estimate_reports_core_horizon_shape() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let result = dispatch_method(&node, "estimaterawfee", &json!([6])).unwrap();
        for horizon in ["short", "medium", "long"] {
            assert!(result[horizon]["decay"].is_number());
            assert!(result[horizon]["scale"].is_number());
            assert!(result[horizon]["errors"].is_array());
            assert!(result[horizon]["feerate"].is_null());
        }
        assert!(dispatch_method(&node, "estimaterawfee", &json!([0])).is_err());
        assert!(dispatch_method(&node, "estimaterawfee", &json!([6, -0.1])).is_err());
        assert!(dispatch_method(&node, "estimaterawfee", &json!([6, "invalid"])).is_err());
    }

    #[test]
    fn txoutset_info_honors_core_hash_options() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
            prune: 0,
            reindex: false,
            reindex_chainstate: false,
            load_blocks: Vec::new(),
            txindex: false,
            txospenderindex: false,
            max_mempool_mb: 300,
            mempool_expiry_hours: 336,
            coinstatsindex: true,
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
        .unwrap();

        let default = dispatch_method(&node, "gettxoutsetinfo", &json!([])).unwrap();
        assert!(default["hash_serialized_3"].is_string());
        let without_hash =
            dispatch_method(&node, "gettxoutsetinfo", &json!(["none", null, false])).unwrap();
        assert!(without_hash.get("hash_serialized_3").is_none());
        assert_eq!(without_hash["height"], json!(0));
        assert!(dispatch_method(&node, "gettxoutsetinfo", &json!(["invalid"])).is_err());
        let muhash = dispatch_method(&node, "gettxoutsetinfo", &json!(["muhash"])).unwrap();
        assert!(muhash["muhash"].is_string());
        assert!(muhash.get("hash_serialized_3").is_none());
        let at_genesis = dispatch_method(&node, "gettxoutsetinfo", &json!(["none", 0])).unwrap();
        assert_eq!(at_genesis["height"], json!(0));
        let genesis_hash = node.chain.read().block_hash(0).unwrap();
        assert_eq!(at_genesis["bestblock"], genesis_hash.to_string());
        let best_hash = node.chain.read().best_hash();
        let by_hash = dispatch_method(
            &node,
            "gettxoutsetinfo",
            &json!(["muhash", best_hash.to_string()]),
        )
        .unwrap();
        assert!(by_hash["muhash"].is_string());
        assert!(
            dispatch_method(&node, "gettxoutsetinfo", &json!(["hash_serialized_3", 0]),).is_err()
        );
        assert!(dispatch_method(&node, "gettxoutsetinfo", &json!(["none", 0, false])).is_err());
        assert_eq!(
            dispatch_method(&node, "getzmqnotifications", &json!([])).unwrap(),
            json!([])
        );
        assert_eq!(
            dispatch_method(&node, "syncwithvalidationinterfacequeue", &json!([])).unwrap(),
            Value::Null
        );
        let help = dispatch_method(&node, "help", &json!([])).unwrap();
        let help = help.as_str().expect("help returns text");
        assert!(help.lines().any(|line| line == "getmemoryinfo"));
        assert!(help.lines().any(|line| line == "stop"));
        let generate_error = dispatch_method(&node, "generate", &json!([])).unwrap_err();
        assert!(
            generate_error
                .to_string()
                .contains("replaced by the -generate cli option")
        );
    }

    #[test]
    fn txoutset_info_replays_requested_active_height() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
            prune: 0,
            reindex: false,
            reindex_chainstate: false,
            load_blocks: Vec::new(),
            txindex: false,
            txospenderindex: false,
            max_mempool_mb: 300,
            mempool_expiry_hours: 336,
            coinstatsindex: true,
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
        .unwrap();
        assert_eq!(
            dispatch_method(&node, "getindexinfo", &json!(["coinstatsindex"])).unwrap()["coinstatsindex"]
                ["synced"],
            true
        );
        let mined = generate_to_address(
            &node,
            &json!([1, "bcrt1q2nfxmhd4n3c8834pj72xagvyr9gl57n5r94fsl"]),
        )
        .unwrap();
        let tip_hash = mined[0].as_str().unwrap();

        let genesis = dispatch_method(&node, "gettxoutsetinfo", &json!(["none", 0])).unwrap();
        assert_eq!(genesis["height"], json!(0));
        assert_eq!(genesis["txouts"], json!(0));
        assert_eq!(genesis["total_unspendable_amount"], json!(50.0));
        assert_eq!(genesis["block_info"]["prevout_spent"], json!(0.0));
        assert_eq!(genesis["block_info"]["coinbase"], json!(0.0));
        assert_eq!(genesis["block_info"]["new_outputs_ex_coinbase"], json!(0.0));
        assert_eq!(genesis["block_info"]["unspendable"], json!(50.0));
        assert_eq!(
            genesis["block_info"]["unspendables"]["genesis_block"],
            json!(50.0)
        );

        let tip = dispatch_method(&node, "gettxoutsetinfo", &json!(["none", tip_hash])).unwrap();
        assert_eq!(tip["height"], json!(1));
        assert_eq!(tip["txouts"], json!(1));
        assert_eq!(tip["total_amount"], json!(50.0));
        assert_eq!(tip["total_unspendable_amount"], json!(50.0));
        assert_eq!(tip["block_info"]["prevout_spent"], json!(0.0));
        assert_eq!(tip["block_info"]["coinbase"], json!(50.0));
        assert_eq!(tip["block_info"]["new_outputs_ex_coinbase"], json!(0.0));
        assert_eq!(tip["block_info"]["unspendable"], json!(0.0));
    }

    #[test]
    fn logging_categories_match_core_v31() {
        assert_eq!(
            LOG_CATEGORIES,
            &[
                "addrman",
                "bench",
                "blockstorage",
                "cmpctblock",
                "coindb",
                "estimatefee",
                "http",
                "i2p",
                "ipc",
                "kernel",
                "leveldb",
                "libevent",
                "mempool",
                "mempoolrej",
                "net",
                "privatebroadcast",
                "prune",
                "proxy",
                "qt",
                "rand",
                "reindex",
                "rpc",
                "scan",
                "selectcoins",
                "tor",
                "txpackages",
                "txreconciliation",
                "validation",
                "walletdb",
                "zmq",
            ]
        );
        assert!(
            rpc_help("logging")
                .contains("valid logging categories are: addrman, bench, blockstorage, cmpctblock")
        );
    }

    #[test]
    fn node_control_rpcs_return_core_shapes() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();

        assert_eq!(
            dispatch_method(&node, "echo", &json!([1, {"two": 2}])).unwrap(),
            json!([1, {"two": 2}])
        );
        assert_eq!(
            dispatch_method(&node, "echoipc", &json!(["hello"])).unwrap(),
            json!("hello")
        );
        assert!(
            dispatch_method(&node, "verifychain", &json!([]))
                .unwrap()
                .as_bool()
                .unwrap()
        );
        assert!(dispatch_method(&node, "verifychain", &json!([5])).is_err());
        assert!(dispatch_method(&node, "verifychain", &json!([3, -1])).is_err());
        assert_eq!(
            dispatch_method(&node, "getblockhash", &json!([0])).unwrap(),
            json!(node.chain.read().block_hash(0).unwrap().to_string())
        );
        let negative_height = dispatch_method(&node, "getblockhash", &json!([-1])).unwrap_err();
        assert_eq!(negative_height.to_string(), "Block height out of range");
        assert_eq!(rpc_error(&negative_height)["code"], json!(-8));
        let memory = dispatch_method(&node, "getmemoryinfo", &json!([])).unwrap();
        assert!(
            memory["locked"]["used"]
                .as_u64()
                .is_some_and(|value| value > 0)
        );
        assert!(
            memory["locked"]["free"]
                .as_u64()
                .is_some_and(|value| value > 0)
        );
        assert!(
            memory["locked"]["total"]
                .as_u64()
                .is_some_and(|value| value > 0)
        );
        assert_eq!(
            memory["locked"]["used"].as_u64().unwrap() + memory["locked"]["free"].as_u64().unwrap(),
            memory["locked"]["total"].as_u64().unwrap()
        );
        assert!(dispatch_method(&node, "getmemoryinfo", &json!(["mallocinfo"])).is_err());
        assert!(dispatch_method(&node, "getmemoryinfo", &json!([1])).is_err());
        let net_totals = dispatch_method(&node, "getnettotals", &json!([])).unwrap();
        assert!(net_totals["uploadtarget"]["bytes_left_in_cycle"].is_number());
        assert!(net_totals["uploadtarget"]["time_left_in_cycle"].is_number());
        assert!(net_totals["uploadtarget"].get("bytes_left").is_none());
        assert!(net_totals.get("connections").is_none());
        assert!(
            dispatch_method(&node, "getindexinfo", &json!([])).unwrap()["basic block filter index"]
                ["synced"]
                .as_bool()
                .unwrap()
        );
        assert_eq!(
            dispatch_method(&node, "getprivatebroadcastinfo", &json!([])).unwrap(),
            json!({"transactions": []})
        );
        assert!(
            dispatch_method(
                &node,
                "abortprivatebroadcast",
                &json!([Txid::all_zeros().to_string()]),
            )
            .unwrap_err()
            .to_string()
            .contains("not in private broadcast queue")
        );
        let logging = dispatch_method(&node, "logging", &json!([["rpc"], []])).unwrap();
        assert_eq!(logging["rpc"], json!(true));
        let logging = dispatch_method(&node, "logging", &json!([[], ["rpc"]])).unwrap();
        assert_eq!(logging["rpc"], json!(false));
        let command_id = node.begin_rpc_command("testcommand");
        let rpcinfo = dispatch_method(&node, "getrpcinfo", &json!([])).unwrap();
        assert_eq!(
            rpcinfo["active_commands"][0]["method"],
            json!("testcommand")
        );
        assert!(rpcinfo["active_commands"][0]["duration"].is_u64());
        node.end_rpc_command(command_id);
        assert!(
            dispatch_method(&node, "getrpcinfo", &json!([])).unwrap()["active_commands"]
                .as_array()
                .unwrap()
                .is_empty()
        );
        assert!(dispatch_method(&node, "mockscheduler", &json!([0])).is_err());
        assert!(dispatch_method(&node, "setmocktime", &json!([-1])).is_err());
    }

    #[test]
    fn named_rpc_parameters_are_normalized_with_holes_and_strict_names() {
        let normalized = normalize_rpc_params("stop", &json!({"wait": 250})).unwrap();
        assert_eq!(normalized, json!([250]));
        let normalized = normalize_rpc_params(
            "getblockheader",
            &json!({"verbose": false, "blockhash": "00"}),
        )
        .unwrap();
        assert_eq!(normalized, json!(["00", false]));
        let normalized = normalize_rpc_params("getblock", &json!({"verbose": false})).unwrap();
        assert_eq!(normalized, json!([null, false]));
        let normalized = normalize_rpc_params(
            "gettxspendingprevout",
            &json!({"outputs": [], "options": {"return_spending_tx": true}}),
        )
        .unwrap();
        assert_eq!(normalized, json!([[], {"return_spending_tx": true}]));
        let normalized =
            normalize_rpc_params("setnetworkactive", &json!({"state": false})).unwrap();
        assert_eq!(normalized, json!([false]));
        let normalized = normalize_rpc_params("echo", &json!({"arg0": 0, "arg9": 9})).unwrap();
        assert_eq!(
            normalized,
            json!([0, null, null, null, null, null, null, null, null, 9])
        );
        let normalized =
            normalize_rpc_params("echojson", &json!({"args": [0, 1], "arg3": 3, "arg5": 5}))
                .unwrap();
        assert_eq!(normalized, json!([0, 1, null, 3, null, 5]));
        let normalized = normalize_rpc_params("echoipc", &json!({"arg": "hello"})).unwrap();
        assert_eq!(normalized, json!(["hello"]));

        let normalized = normalize_rpc_params("gettxout", &json!({"txid": "00", "n": 1})).unwrap();
        assert_eq!(normalized, json!(["00", 1, null]));
        let normalized = normalize_rpc_params("getorphantxs", &json!({"verbosity": 2})).unwrap();
        assert_eq!(normalized, json!([2]));
        let normalized =
            normalize_rpc_params("generatetodescriptor", &json!({"num_blocks": 1})).unwrap();
        assert_eq!(normalized, json!([1, null, null]));
        let normalized = normalize_rpc_params(
            "gettxspendingprevout",
            &json!({"outputs": [], "mempool_only": true}),
        )
        .unwrap();
        assert_eq!(normalized, json!([[], {"mempool_only": true}]));
        let normalized = normalize_rpc_params(
            "scanblocks",
            &json!({"action": "status", "filter_false_positives": true}),
        )
        .unwrap();
        assert_eq!(
            normalized,
            json!(["status", null, null, null, null, {"filter_false_positives": true}])
        );
        let normalized = normalize_rpc_params(
            "dumptxoutset",
            &json!({"path": "utxo.dat", "type": "latest", "options": {}}),
        )
        .unwrap();
        assert_eq!(normalized, json!(["utxo.dat", "latest", {}]));
        let normalized = normalize_rpc_params(
            "createpsbt",
            &json!({"inputs": [], "outputs": [], "version": 3}),
        )
        .unwrap();
        assert_eq!(normalized, json!([[], [], null, null, 3]));
        let normalized = normalize_rpc_params(
            "addnode",
            &json!({"node": "127.0.0.1:18444", "command": "onetry", "v2transport": false}),
        )
        .unwrap();
        assert_eq!(normalized, json!(["127.0.0.1:18444", "onetry", false]));
        assert!(normalize_rpc_params("getblockhash", &json!({"height": 0, "extra": 1})).is_err());
        assert!(normalize_rpc_params("getblockhash", &json!([0, 1])).is_err());
        assert!(normalize_rpc_params("getblockcount", &json!([1])).is_err());
        assert!(normalize_rpc_params("getmempoolentry", &json!(["00", false])).is_err());
        assert!(
            normalize_rpc_params("getmempoolentry", &json!({"txid": "00", "verbose": true}),)
                .is_err()
        );
        assert!(
            normalize_rpc_params(
                "signrawtransactionwithkey",
                &json!(["00", [], null, "ALL", 0])
            )
            .is_err()
        );
        assert!(
            normalize_rpc_params(
                "signrawtransactionwithkey",
                &json!({"hexstring": "00", "privkeys": [], "maxfeerate": 0}),
            )
            .is_err()
        );
        assert!(normalize_rpc_params("echo", &json!([1, 2, 3])).is_ok());
    }

    #[test]
    fn stop_wait_accepts_non_negative_integer_milliseconds() {
        assert_eq!(stop_wait(&json!([])).unwrap(), None);
        assert_eq!(
            stop_wait(&json!([250])).unwrap(),
            Some(std::time::Duration::from_millis(250))
        );
        assert!(stop_wait(&json!([-1])).is_err());
        assert!(stop_wait(&json!(["250"])).is_err());
    }

    #[test]
    fn optional_rpc_booleans_preserve_defaults_and_reject_wrong_types() {
        assert!(optional_bool(&json!([]), 0, true, "flag").unwrap());
        assert!(optional_bool(&json!([null]), 0, true, "flag").unwrap());
        assert!(!optional_bool(&json!([false]), 0, true, "flag").unwrap());
        assert!(optional_bool(&json!([true]), 0, false, "flag").unwrap());
        assert!(optional_bool(&json!([1]), 0, true, "flag").is_err());
        assert!(optional_bool(&json!(["true"]), 0, true, "flag").is_err());
        assert_eq!(
            optional_str(&json!([]), 0, "default", "field").unwrap(),
            "default"
        );
        assert_eq!(
            optional_str(&json!([null]), 0, "default", "field").unwrap(),
            "default"
        );
        assert_eq!(
            optional_str(&json!(["value"]), 0, "default", "field").unwrap(),
            "value"
        );
        assert!(optional_str(&json!([1]), 0, "default", "field").is_err());
        assert_eq!(optional_i64(&json!([]), 0, 7, "number").unwrap(), 7);
        assert_eq!(optional_i64(&json!([null]), 0, 7, "number").unwrap(), 7);
        assert_eq!(optional_i64(&json!([-2]), 0, 7, "number").unwrap(), -2);
        assert!(optional_i64(&json!(["7"]), 0, 7, "number").is_err());
        assert_eq!(optional_u64(&json!([]), 0, 7, "number").unwrap(), 7);
        assert_eq!(optional_u64(&json!([null]), 0, 7, "number").unwrap(), 7);
        assert_eq!(optional_u64(&json!([2]), 0, 7, "number").unwrap(), 2);
        assert!(optional_u64(&json!([-2]), 0, 7, "number").is_err());
        assert!(optional_u64(&json!(["7"]), 0, 7, "number").is_err());
    }

    #[test]
    fn rpc_connection_types_use_core_names() {
        assert_eq!(rpc_connection_type("outbound-full"), "outbound-full-relay");
        assert_eq!(rpc_connection_type("block-relay-only"), "block-relay-only");
        assert_eq!(rpc_connection_type("addr-fetch"), "addr-fetch");
    }

    #[test]
    fn wait_rpc_zero_timeout_means_no_deadline() {
        assert!(rpc_timeout(&json!([0]), 0).unwrap().is_none());
        assert!(rpc_timeout(&json!([null]), 0).unwrap().is_none());
        assert!(rpc_timeout(&json!([1]), 0).unwrap().is_some());
    }

    #[tokio::test]
    async fn json_rpc_two_notifications_have_no_response() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();

        assert!(
            dispatch_method_async(&node, "stop", &json!([-1]))
                .await
                .is_err()
        );
        assert!(
            dispatch_method(&node, "getrpcinfo", &json!([])).unwrap()["active_commands"]
                .as_array()
                .unwrap()
                .is_empty()
        );
        assert!(
            dispatch_json_rpc(&node, br#"{"jsonrpc":"2.0","method":"getblockcount"}"#)
                .await
                .is_none()
        );
        assert!(dispatch_json_rpc(
            &node,
            br#"[{"jsonrpc":"2.0","method":"getblockcount"},{"jsonrpc":"2.0","method":"getdifficulty"}]"#,
        )
        .await
        .is_none());

        let response = dispatch_json_rpc(
            &node,
            br#"[{"jsonrpc":"2.0","method":"getblockcount"},{"jsonrpc":"2.0","id":7,"method":"getblockcount"}]"#,
        )
        .await
        .unwrap();
        assert_eq!(response.as_array().unwrap().len(), 1);
        assert_eq!(response[0]["id"], json!(7));
        assert_eq!(response[0]["result"], json!(0));

        let legacy = dispatch_json_rpc(&node, br#"{"method":"getblockcount"}"#)
            .await
            .unwrap();
        assert_eq!(legacy["result"], json!(0));
        assert_eq!(legacy["id"], Value::Null);
    }

    #[test]
    fn network_hash_rate_rejects_invalid_windows() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        assert!(get_network_hash_ps(&node, &json!([0])).is_err());
        assert!(get_network_hash_ps(&node, &json!([-2])).is_err());
        assert!(get_network_hash_ps(&node, &json!(["120"])).is_err());
        assert!(get_chain_tx_stats(&node, &json!([null, 1])).is_err());
        let stats = get_chain_tx_stats(&node, &json!([])).unwrap();
        assert_eq!(stats["txcount"], json!(1));
        assert_eq!(stats["window_block_count"], json!(0));
        let unknown_hash = BlockHash::from_byte_array([0xff; 32]);
        let block_not_found =
            get_chain_tx_stats(&node, &json!([null, unknown_hash.to_string()])).unwrap_err();
        assert_eq!(block_not_found.to_string(), "Block not found");
        assert_eq!(rpc_error(&block_not_found)["code"], json!(-5));
        let invalid_window = get_chain_tx_stats(&node, &json!([-1])).unwrap_err();
        assert_eq!(
            invalid_window.to_string(),
            "Invalid block count: should be between 0 and the block's height - 1"
        );
        assert_eq!(rpc_error(&invalid_window)["code"], json!(-8));
        assert_eq!(
            get_network_hash_ps(&node, &json!([-1])).unwrap(),
            json!(0.0)
        );
    }

    #[test]
    fn mining_info_reports_current_and_next_block_targets() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();

        let info = get_mining_info(&node).unwrap();
        assert_eq!(info["blocks"], json!(0));
        assert_eq!(info["next"]["height"], json!(1));
        assert_eq!(info["pooledtx"], json!(0));
        assert_eq!(info["blockmintxfee"], json!(0.00000001));
        assert!(info["warnings"].is_array());
        assert!(info["bits"].as_str().is_some());
        assert!(info["target"].as_str().is_some());
        assert!(info.get("currentblockweight").is_none());
        assert!(info.get("currentblocktx").is_none());
        get_block_template(&node, &json!([{"rules": ["segwit"]}])).unwrap();
        let info = get_mining_info(&node).unwrap();
        assert_eq!(info["currentblockweight"], json!(8_000));
        assert_eq!(info["currentblocktx"], json!(0));
    }

    #[test]
    fn deployment_info_reports_buried_and_bip9_state() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();

        let info = get_deployment_info(&node, &json!([])).unwrap();
        assert_eq!(info["height"], json!(0));
        assert_eq!(info["deployments"]["bip34"]["height"], json!(1));
        assert_eq!(info["deployments"]["bip34"]["active"], json!(true));
        assert_eq!(info["deployments"]["segwit"]["height"], json!(0));
        assert_eq!(info["deployments"]["taproot"]["active"], json!(true));
        assert_eq!(
            info["deployments"]["testdummy"]["bip9"]["status"],
            json!("defined")
        );
        assert!(
            info["script_flags"]
                .as_array()
                .unwrap()
                .iter()
                .any(|flag| { flag == "TAPROOT" })
        );
    }

    #[test]
    fn blockchain_info_omits_removed_softfork_field() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();

        let info = get_blockchain_info(&node).unwrap();
        assert_eq!(info["initialblockdownload"], json!(true));
        assert_eq!(info["verificationprogress"], json!(0.0));
        assert!(info.get("softforks").is_none());
    }

    #[test]
    fn block_filter_rpc_returns_the_basic_filter_and_header() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let hash = node.chain.read().best_hash();
        let filter = get_block_filter(&node, &json!([hash.to_string()])).unwrap();
        assert!(filter["filter"].as_str().is_some());
        assert_eq!(filter["header"].as_str().unwrap().len(), 64);
        let unknown_filter_type =
            get_block_filter(&node, &json!([hash.to_string(), "extended"])).unwrap_err();
        assert_eq!(unknown_filter_type.to_string(), "Unknown filtertype");
        assert_eq!(rpc_error(&unknown_filter_type)["code"], json!(-5));
        assert!(get_block_filter(&node, &json!([hash.to_string(), 1])).is_err());
        let unknown_hash = BlockHash::from_byte_array([0xff; 32]);
        let block_not_found =
            get_block_filter(&node, &json!([unknown_hash.to_string()])).unwrap_err();
        assert_eq!(block_not_found.to_string(), "Block not found");
        assert_eq!(rpc_error(&block_not_found)["code"], json!(-5));
    }

    #[test]
    fn block_stats_reject_a_non_array_statistic_selector() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let hash = node.chain.read().best_hash();
        assert!(get_block_stats(&node, &json!([hash.to_string(), "txs"])).is_err());
        assert!(get_block_stats(&node, &json!([hash.to_string(), ["size"]])).is_err());
    }

    #[test]
    fn rest_endpoints_render_chain_data() {
        let directory = tempfile::tempdir().unwrap();
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
            rest: true,
            listen: true,
            dnsseed: true,
            force_dns_seed: false,
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let (_, chaininfo) = dispatch_rest(&node, "/rest/chaininfo.json").unwrap();
        assert_eq!(
            serde_json::from_slice::<Value>(&chaininfo).unwrap()["chain"],
            "regtest"
        );
        let (_, hash) = dispatch_rest(&node, "/rest/blockhashbyheight/0.hex").unwrap();
        assert_eq!(hash.len(), 65);
        let (_, hash_json) = dispatch_rest(&node, "/rest/blockhashbyheight/0.json").unwrap();
        assert_eq!(
            serde_json::from_slice::<Value>(&hash_json).unwrap(),
            json!({"blockhash": node.chain.read().block_hash(0).unwrap().to_string()})
        );
        let (_, headers) = dispatch_rest(
            &node,
            &format!(
                "/rest/headers/{}.json?count=1",
                node.chain.read().best_hash()
            ),
        )
        .unwrap();
        assert_eq!(
            serde_json::from_slice::<Value>(&headers)
                .unwrap()
                .as_array()
                .unwrap()
                .len(),
            1
        );
        let genesis_hash = node.chain.read().best_hash();
        let (_, block_part) = dispatch_rest(
            &node,
            &format!("/rest/blockpart/{genesis_hash}.hex?offset=0&size=4"),
        )
        .unwrap();
        assert_eq!(std::str::from_utf8(&block_part).unwrap(), "01000000\n");
        let (_, filter) = dispatch_rest(
            &node,
            &format!("/rest/blockfilter/basic/{genesis_hash}.json"),
        )
        .unwrap();
        let filter = serde_json::from_slice::<Value>(&filter).unwrap();
        assert!(filter["filter"].as_str().is_some());
        let (_, filter_hex) = dispatch_rest(
            &node,
            &format!("/rest/blockfilter/basic/{genesis_hash}.hex"),
        )
        .unwrap();
        let filter_bytes = hex::decode(std::str::from_utf8(&filter_hex).unwrap().trim()).unwrap();
        let raw_filter = hex::decode(filter["filter"].as_str().unwrap()).unwrap();
        assert_eq!(filter_bytes, serialize_block_filter(&raw_filter));
        let (_, filter_headers) = dispatch_rest(
            &node,
            &format!("/rest/blockfilterheaders/basic/{genesis_hash}.json?count=1"),
        )
        .unwrap();
        assert_eq!(
            serde_json::from_slice::<Value>(&filter_headers)
                .unwrap()
                .as_array()
                .unwrap()
                .len(),
            1
        );
        let (_, deployment) = dispatch_rest(&node, "/rest/deploymentinfo.json").unwrap();
        assert_eq!(
            serde_json::from_slice::<Value>(&deployment).unwrap()["height"],
            0
        );
        let (_, spent) =
            dispatch_rest(&node, &format!("/rest/spenttxouts/{genesis_hash}.json")).unwrap();
        assert_eq!(
            serde_json::from_slice::<Value>(&spent).unwrap(),
            json!([[]])
        );
        let (_, spent_hex) =
            dispatch_rest(&node, &format!("/rest/spenttxouts/{genesis_hash}.hex")).unwrap();
        assert_eq!(std::str::from_utf8(&spent_hex).unwrap(), "0100\n");
        let (_, empty_utxos) =
            dispatch_rest_with_body(&node, "/rest/getutxos.bin", &[0, 0]).unwrap();
        assert_eq!(empty_utxos.len(), 38);
    }

    #[test]
    fn mempool_sequence_is_available_for_non_verbose_results() {
        let directory = tempfile::tempdir().unwrap();
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
            rest: true,
            listen: true,
            dnsseed: true,
            force_dns_seed: false,
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();

        let result = dispatch_method(&node, "getrawmempool", &json!([false, true])).unwrap();
        assert_eq!(result["txids"], json!([]));
        assert_eq!(result["mempool_sequence"], json!(1));
        assert!(dispatch_method(&node, "getrawmempool", &json!([true, true])).is_err());
        let info = dispatch_method(&node, "getmempoolinfo", &json!([])).unwrap();
        assert_eq!(info["fullrbf"], json!(true));
        assert_eq!(info["limitclustercount"], json!(64));
        assert_eq!(info["minrelaytxfee"], json!(0.000001));
        assert_eq!(info["incrementalrelayfee"], json!(0.000001));
        assert_eq!(info["maxdatacarriersize"], json!(100_000));
        assert_eq!(info["permitbaremultisig"], json!(true));

        let (_, body) = dispatch_rest(
            &node,
            "/rest/mempool/contents.json?verbose=false&mempool_sequence=true",
        )
        .unwrap();
        let result = serde_json::from_slice::<Value>(&body).unwrap();
        assert_eq!(result["txids"], json!([]));
        assert_eq!(result["mempool_sequence"], json!(1));
        assert!(
            dispatch_rest(
                &node,
                "/rest/mempool/contents.json?verbose=true&mempool_sequence=true"
            )
            .is_err()
        );
    }

    #[test]
    fn mempool_relationships_reject_missing_transactions() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let missing = Txid::from_byte_array([7; 32]).to_string();

        assert!(dispatch_method(&node, "getmempoolancestors", &json!([missing])).is_err());
        assert!(dispatch_method(&node, "getmempooldescendants", &json!([missing])).is_err());
    }

    #[test]
    fn mempool_chunks_merge_when_a_later_fee_rate_is_higher() {
        let first = Txid::from_byte_array([1; 32]);
        let second = Txid::from_byte_array([2; 32]);
        let third = Txid::from_byte_array([3; 32]);
        let mut chunks = Vec::new();

        append_mempool_chunk(&mut chunks, first, 100, 100);
        append_mempool_chunk(&mut chunks, second, 100, 10);
        append_mempool_chunk(&mut chunks, third, 100, 90);

        assert_eq!(chunks.len(), 2);
        assert_eq!(chunks[0].txids, vec![first]);
        assert_eq!(chunks[1].txids, vec![second, third]);
        assert_eq!(chunks[1].fee, 100);
        assert_eq!(chunks[1].weight, 200);
    }

    #[test]
    fn mempool_cluster_and_fee_diagram_report_a_transaction() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();

        let script = ScriptBuf::from_bytes(vec![0x51]);
        let mined = generate_blocks_to_script(&node, script.clone(), 101, 1_000).unwrap();
        assert_eq!(mined.as_array().unwrap().len(), 101);
        let block_hash = node.chain.read().block_hash(1).unwrap();
        let coinbase = node
            .chain
            .write()
            .block(&block_hash)
            .unwrap()
            .unwrap()
            .txdata[0]
            .clone();
        let previous_output = OutPoint::new(coinbase.compute_txid(), 0);
        let transaction = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output,
                script_sig: ScriptBuf::from_bytes(vec![0x00; 8]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: coinbase.output[0].value - bitcoin::Amount::from_sat(1_000),
                script_pubkey: script,
            }],
        };
        let txid = node.accept_transaction(transaction.clone()).unwrap();
        assert_eq!(
            dispatch_method(
                &node,
                "sendrawtransaction",
                &json!([hex::encode(serialize(&transaction)), 0])
            )
            .unwrap(),
            json!(txid.to_string())
        );

        let entry = dispatch_method(&node, "getmempoolentry", &json!([txid.to_string()])).unwrap();
        assert_eq!(entry["height"], json!(node.chain.read().height()));
        assert_eq!(entry["chunkweight"], entry["weight"]);
        assert_eq!(entry["fees"]["chunk"], entry["fees"]["modified"]);
        let mempool_info = dispatch_method(&node, "getmempoolinfo", &json!([])).unwrap();
        assert_eq!(mempool_info["bytes"], entry["vsize"]);

        let cluster =
            dispatch_method(&node, "getmempoolcluster", &json!([txid.to_string()])).unwrap();
        assert_eq!(
            cluster["clusterweight"],
            cluster["chunks"][0]["chunkweight"]
        );
        assert_eq!(cluster["txcount"], json!(1));
        assert_eq!(cluster["chunks"][0]["txs"], json!([txid.to_string()]));

        let diagram = dispatch_method(&node, "getmempoolfeeratediagram", &json!([])).unwrap();
        assert_eq!(diagram.as_array().unwrap().len(), 2);
        assert_eq!(diagram[0], json!({"weight": 0, "fee": 0.0}));
        assert!(diagram[1]["weight"].as_u64().unwrap() > 0);
        assert!(diagram[1]["fee"].as_f64().unwrap() > 0.0);
    }

    #[test]
    fn generate_to_address_mines_and_connects_a_block() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();

        assert!(
            generate_to_address(
                &node,
                &json!([0, "bcrt1q2nfxmhd4n3c8834pj72xagvyr9gl57n5r94fsl", "100"])
            )
            .is_err()
        );
        let result = generate_to_address(
            &node,
            &json!([1, "bcrt1q2nfxmhd4n3c8834pj72xagvyr9gl57n5r94fsl"]),
        )
        .unwrap();
        let hash = result[0].as_str().unwrap().parse::<BlockHash>().unwrap();
        let mut chain = node.chain.write();
        assert_eq!(chain.tip().height, 1);
        assert_eq!(chain.best_hash(), hash);
        let block = chain.block(&hash).unwrap().unwrap();
        assert_eq!(block.txdata.len(), 1);
        assert_eq!(
            block.txdata[0].lock_time,
            LockTime::from_consensus(chain.height().saturating_sub(1))
        );
        assert_eq!(block.txdata[0].output[0].value.to_sat(), 5_000_000_000);
    }

    #[test]
    fn generate_block_can_return_an_unsent_mined_block() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let result = generate_block(
            &node,
            &json!(["bcrt1q2nfxmhd4n3c8834pj72xagvyr9gl57n5r94fsl", [], false]),
        )
        .unwrap();
        assert!(result["hash"].as_str().is_some());
        let block: Block =
            deserialize(&hex::decode(result["hex"].as_str().unwrap()).unwrap()).unwrap();
        assert_eq!(block.block_hash().to_string(), result["hash"]);
        assert_eq!(node.chain.read().height(), 0);

        generate_block(
            &node,
            &json!(["bcrt1q2nfxmhd4n3c8834pj72xagvyr9gl57n5r94fsl", [], true]),
        )
        .unwrap();
        assert_eq!(node.chain.read().height(), 1);

        let descriptor_block = generate_block(&node, &json!(["raw(51)", [], false])).unwrap();
        assert!(descriptor_block["hex"].as_str().is_some());
        let block_hex = descriptor_block["hex"].as_str().unwrap();
        assert!(submit_block(&node, &json!([block_hex, 1])).is_err());
        let mut uncommitted: Block = deserialize(&hex::decode(block_hex).unwrap()).unwrap();
        uncommitted.txdata[0].input[0].witness = Witness::default();
        assert_eq!(
            submit_block(&node, &json!([hex::encode(serialize(&uncommitted))])).unwrap(),
            Value::Null
        );
        assert_eq!(
            submit_block(&node, &json!([block_hex])).unwrap(),
            json!("duplicate")
        );
        let header_first = generate_block(&node, &json!(["raw(51)", [], false])).unwrap();
        let header_first_block: Block =
            deserialize(&hex::decode(header_first["hex"].as_str().unwrap()).unwrap()).unwrap();
        submit_header(
            &node,
            &json!([hex::encode(serialize(&header_first_block.header))]),
        )
        .unwrap();
        assert_eq!(
            submit_block(&node, &json!([header_first["hex"].clone()])).unwrap(),
            Value::Null
        );
        assert_eq!(node.chain.read().height(), 3);
        let combo_block = generate_block(
            &node,
            &json!([
                "combo(0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798)",
                [],
                false
            ]),
        )
        .unwrap();
        assert!(combo_block["hex"].as_str().is_some());
    }

    #[test]
    fn getblock_verbosity_three_includes_prevout_details() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
            prune: 0,
            reindex: false,
            reindex_chainstate: false,
            load_blocks: Vec::new(),
            txindex: false,
            txospenderindex: true,
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
        .unwrap();
        let mined = generate_to_descriptor(&node, &json!([102, "raw(51)"])).unwrap();
        let funding_hash: BlockHash = mined[0].as_str().unwrap().parse().unwrap();
        let funding = node.chain.write().block(&funding_hash).unwrap().unwrap();
        let funding_txid = funding.txdata[0].compute_txid();
        let spend = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(funding_txid, 0),
                script_sig: ScriptBuf::from_bytes(vec![0x00; 8]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: bitcoin::Amount::from_sat(4_999_999_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let spend_txid = node.accept_transaction(spend).unwrap();
        let block_hash: BlockHash = generate_to_descriptor(&node, &json!([1, "raw(51)"])).unwrap()
            [0]
        .as_str()
        .unwrap()
        .parse()
        .unwrap();
        let block = get_block(&node, &json!([block_hash.to_string(), 3])).unwrap();
        let transaction = block["tx"]
            .as_array()
            .unwrap()
            .iter()
            .find(|transaction| transaction["txid"] == spend_txid.to_string())
            .expect("mined transaction is present");
        assert!(transaction.get("blockhash").is_none());
        assert!(transaction.get("confirmations").is_none());
        assert!(transaction.get("time").is_none());
        assert!(transaction.get("blocktime").is_none());
        assert_eq!(transaction["vin"][0]["prevout"]["generated"], true);
        assert_eq!(transaction["vin"][0]["prevout"]["height"], 1);
        assert_eq!(transaction["vin"][0]["prevout"]["value"], 50.0);
        assert_eq!(transaction["fee"], 0.00001);
        assert_eq!(
            transaction["vin"][0]["prevout"]["scriptPubKey"]["hex"],
            "51"
        );
        let details = get_block(&node, &json!([block_hash.to_string(), 2])).unwrap();
        let details_transaction = details["tx"]
            .as_array()
            .unwrap()
            .iter()
            .find(|transaction| transaction["txid"] == spend_txid.to_string())
            .expect("mined transaction is present");
        assert_eq!(details_transaction["fee"], 0.00001);
        assert!(details_transaction["vin"][0].get("prevout").is_none());
        let high_verbosity = get_block(&node, &json!([block_hash.to_string(), 4])).unwrap();
        assert_eq!(
            high_verbosity["tx"]
                .as_array()
                .unwrap()
                .iter()
                .find(|transaction| transaction["txid"] == spend_txid.to_string())
                .unwrap()["fee"],
            0.00001
        );
        assert!(
            get_block(&node, &json!([block_hash.to_string(), -1]))
                .unwrap()
                .as_str()
                .is_some()
        );
        let raw_high = get_raw_transaction(
            &node,
            &json!([spend_txid.to_string(), 4, block_hash.to_string()]),
        )
        .unwrap();
        assert_eq!(raw_high["fee"], 0.00001);
        assert!(raw_high["vin"][0].get("prevout").is_some());
        assert!(
            get_raw_transaction(
                &node,
                &json!([spend_txid.to_string(), -1, block_hash.to_string()]),
            )
            .unwrap()
            .as_str()
            .is_some()
        );
        let raw = get_block(&node, &json!([block_hash.to_string(), false])).unwrap();
        assert!(raw.as_str().is_some_and(|raw| !raw.is_empty()));
        assert_eq!(
            get_block(&node, &json!([block_hash.to_string(), true])).unwrap()["hash"],
            json!(block_hash.to_string())
        );
        let unknown_hash = BlockHash::from_byte_array([0xff; 32]);
        let unknown_block = get_block(&node, &json!([unknown_hash.to_string()])).unwrap_err();
        assert_eq!(unknown_block.to_string(), "Block not found");
        assert_eq!(rpc_error(&unknown_block)["code"], json!(-5));
        let spending = get_tx_spending_prevout(
            &node,
            &json!([[{"txid": funding_txid.to_string(), "vout": 0}], {"return_spending_tx": true}]),
        )
        .unwrap();
        assert_eq!(spending[0]["spendingtxid"], json!(spend_txid.to_string()));
        assert_eq!(spending[0]["blockhash"], json!(block_hash.to_string()));
        assert!(spending[0]["spendingtx"].as_str().is_some());
        let mempool_only = get_tx_spending_prevout(
            &node,
            &json!([[{"txid": funding_txid.to_string(), "vout": 0}], {"mempool_only": true}]),
        )
        .unwrap();
        assert!(mempool_only[0].get("spendingtxid").is_none());
        let negative_vout = get_tx_spending_prevout(
            &node,
            &json!([[{"txid": funding_txid.to_string(), "vout": -1}]]),
        )
        .unwrap_err();
        assert_eq!(
            negative_vout.to_string(),
            "Invalid parameter, vout cannot be negative"
        );
        let unexpected_outpoint_key = get_tx_spending_prevout(
            &node,
            &json!([[{
                "txid": funding_txid.to_string(),
                "vout": 0,
                "unknown": true
            }]]),
        )
        .unwrap_err();
        assert_eq!(
            unexpected_outpoint_key.to_string(),
            "Unexpected key unknown"
        );
        let unexpected_option_key = get_tx_spending_prevout(
            &node,
            &json!([[{"txid": funding_txid.to_string(), "vout": 0}], {"unknown": true}]),
        )
        .unwrap_err();
        assert_eq!(unexpected_option_key.to_string(), "Unexpected key unknown");
    }

    #[test]
    fn getblocktemplate_reports_a_witness_commitment() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
            block_max_weight: 120_000,
            block_reserved_weight: 8_000,
            block_version: Some(1337),
            block_min_tx_fee_sat_per_kvb: 1_000,
            min_relay_tx_fee_sat_per_kvb: 100,
            incremental_relay_fee_sat_per_kvb: 100,
            dust_relay_fee_sat_per_kvb: 3_000,
            max_datacarrier_bytes: Some(100_000),
            permit_bare_multisig: true,
            zmq: crate::config::ZmqConfig::default(),
        })
        .unwrap();
        let template = get_block_template(&node, &json!([{"rules": ["segwit"]}])).unwrap();
        assert_eq!(template["height"], 1);
        assert_eq!(template["sigoplimit"], 80_000);
        assert_eq!(template["sizelimit"], 4_000_000);
        assert_eq!(template["weightlimit"], 4_000_000);
        assert!(template["curtime"].as_u64().is_some());
        assert_eq!(template["rules"], json!(["csv", "!segwit", "taproot"]));
        assert_eq!(
            template["longpollid"],
            current_block_template_longpoll_id(&node)
        );
        let longpollid = template["longpollid"].as_str().unwrap();
        assert_eq!(&longpollid[..64], node.chain.read().best_hash().to_string());
        assert!(longpollid[64..].parse::<u64>().is_ok());
        assert!(template.get("signet_challenge").is_none());
        assert!(
            template["default_witness_commitment"]
                .as_str()
                .is_some_and(|value| value.starts_with("6a24aa21a9ed"))
        );
        assert_eq!(template["version"], json!(1337));
        assert_eq!(
            mining_block_version(Network::Bitcoin, &[], 0, Some(1337)),
            0x2000_0000
        );
        assert!(get_block_template(&node, &json!([{"mode": 1, "rules": ["segwit"]}])).is_err());
        assert!(get_block_template(&node, &json!([{"rules": 1}])).is_err());
        assert!(get_block_template(&node, &json!([{"rules": [1]}])).is_err());

        let bitcoin_genesis = bitcoin::blockdata::constants::genesis_block(Network::Bitcoin);
        let pre_segwit_block = mining_block(MiningBlockTemplate {
            network: Network::Bitcoin,
            parent: bitcoin_genesis.header,
            height: 1,
            time: bitcoin_genesis.header.time.saturating_add(1),
            bits: bitcoin_genesis.header.bits.to_consensus(),
            script_pubkey: ScriptBuf::new(),
            transactions: Vec::new(),
            fees: 0,
            extra_nonce: 0,
            version: None,
        })
        .unwrap();
        assert!(pre_segwit_block.txdata[0].input[0].witness.is_empty());
        assert_eq!(pre_segwit_block.txdata[0].output.len(), 1);
        assert!(get_block_template(&node, &json!([{}])).is_err());

        let (parent, bits) = {
            let chain = node.chain.read();
            let parent = *chain.header(0).unwrap();
            (parent, chain.next_bits(parent.time.saturating_add(1)))
        };
        let mut proposal = mining_block(MiningBlockTemplate {
            network: Network::Regtest,
            parent,
            height: 1,
            time: parent.time.saturating_add(1),
            bits,
            script_pubkey: Builder::new().push_int(1).into_script(),
            transactions: Vec::new(),
            fees: 0,
            extra_nonce: 0,
            version: None,
        })
        .unwrap();
        while proposal.header.target().is_met_by(proposal.block_hash()) {
            proposal.header.nonce = proposal.header.nonce.saturating_add(1);
        }
        assert_eq!(
            get_block_template(
                &node,
                &json!([{"mode": "proposal", "data": hex::encode(serialize(&proposal))}]),
            )
            .unwrap(),
            Value::Null
        );

        proposal.header.prev_blockhash = BlockHash::all_zeros();
        assert_eq!(
            get_block_template(
                &node,
                &json!([{"mode": "proposal", "data": hex::encode(serialize(&proposal))}]),
            )
            .unwrap(),
            json!("inconclusive-not-best-prevblk")
        );
        proposal.header.prev_blockhash = parent.block_hash();
        proposal.header.time = parent.time;
        let invalid_proposal = hex::encode(serialize(&proposal));
        assert_eq!(
            get_block_template(
                &node,
                &json!([{"mode": "proposal", "data": invalid_proposal}]),
            )
            .unwrap(),
            json!("time-too-old")
        );
        assert_eq!(
            submit_block(&node, &json!([hex::encode(serialize(&proposal))])).unwrap(),
            json!("time-too-old")
        );

        let mined_hash = generate_to_address(
            &node,
            &json!([1, "bcrt1q2nfxmhd4n3c8834pj72xagvyr9gl57n5r94fsl"]),
        )
        .unwrap()[0]
            .as_str()
            .unwrap()
            .parse::<BlockHash>()
            .unwrap();
        let mined = node.chain.write().block(&mined_hash).unwrap().unwrap();
        assert_eq!(
            get_block_template(
                &node,
                &json!([{"mode": "proposal", "data": hex::encode(serialize(&mined))}]),
            )
            .unwrap(),
            json!("duplicate")
        );
    }

    #[test]
    fn getblocktemplate_requires_mainnet_connection() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(Config {
            network: Network::Bitcoin,
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let error = get_block_template(&node, &json!([{"rules": ["segwit"]}]))
            .unwrap_err()
            .to_string();
        assert_eq!(error, "Bitcoin Core is not connected!");
    }

    #[tokio::test]
    async fn getblocktemplate_longpoll_returns_after_a_stale_id() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let stale = format!("{}:999", node.chain.read().best_hash());
        let template =
            get_block_template_async(&node, &json!([{"longpollid": stale, "rules": ["segwit"]}]))
                .await
                .unwrap();
        assert_eq!(template["height"], 1);
    }

    #[tokio::test]
    async fn waitfornewblock_honors_current_tip_hash() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let old_tip = node.chain.read().best_hash();
        generate_to_address(
            &node,
            &json!([1, "bcrt1q2nfxmhd4n3c8834pj72xagvyr9gl57n5r94fsl"]),
        )
        .unwrap();
        let result = wait_for_new_block(&node, &json!([0, old_tip.to_string()]))
            .await
            .unwrap();
        assert_eq!(result["height"], 1);
        assert_ne!(result["hash"], old_tip.to_string());
    }

    #[tokio::test]
    async fn waitforblock_rpcs_return_the_current_tip() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        generate_to_address(
            &node,
            &json!([2, "bcrt1q2nfxmhd4n3c8834pj72xagvyr9gl57n5r94fsl"]),
        )
        .unwrap();
        let tip = node.chain.read().tip();
        let first_block = node.chain.read().block_hash(1).unwrap();

        let by_hash = wait_for_block(&node, &json!([first_block.to_string(), 1]))
            .await
            .unwrap();
        assert_eq!(by_hash["hash"], tip.hash.to_string());
        assert_eq!(by_hash["height"], tip.height);

        let by_height = wait_for_block_height(&node, &json!([1, 0])).await.unwrap();
        assert_eq!(by_height["hash"], tip.hash.to_string());
        assert_eq!(by_height["height"], tip.height);
    }

    #[test]
    fn rest_getutxos_supports_bip64_binary_and_hex_requests() {
        let directory = tempfile::tempdir().unwrap();
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
            rest: true,
            listen: true,
            dnsseed: true,
            force_dns_seed: false,
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let outpoint = OutPoint::new(Txid::from_byte_array([0x42; 32]), 0);
        let mut request = serialize(&true);
        request.extend(serialize(&VarInt::from(1u64)));
        request.extend(serialize(&outpoint));
        let (_, binary) = dispatch_rest_with_body(&node, "/rest/getutxos.bin", &request).unwrap();
        let ((height, tip, bitmap), consumed) =
            deserialize_partial::<(u32, BlockHash, Vec<u8>)>(&binary).unwrap();
        assert_eq!(height, 0);
        assert_eq!(tip, node.chain.read().best_hash());
        assert_eq!(bitmap, vec![0]);
        let (count, count_bytes) = deserialize_partial::<VarInt>(&binary[consumed..]).unwrap();
        assert_eq!(count.0, 0);
        assert_eq!(consumed + count_bytes, binary.len());

        let (_, hex_response) = dispatch_rest_with_body(
            &node,
            "/rest/getutxos.hex",
            hex::encode(&request).as_bytes(),
        )
        .unwrap();
        assert_eq!(
            hex::decode(hex_response.strip_suffix(b"\n").unwrap()).unwrap(),
            binary
        );
    }

    #[test]
    fn invalidate_and_reconsider_reselect_a_valid_chain() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let hash = generate_to_address(
            &node,
            &json!([1, "bcrt1q2nfxmhd4n3c8834pj72xagvyr9gl57n5r94fsl"]),
        )
        .unwrap()[0]
            .as_str()
            .unwrap()
            .parse::<BlockHash>()
            .unwrap();
        invalidate_block(&node, &json!([hash.to_string()])).unwrap();
        assert_eq!(node.chain.read().height(), 0);
        let invalid_tip = node
            .chain
            .read()
            .chain_tips()
            .into_iter()
            .find(|tip| tip.status == "invalid")
            .expect("invalid tip is reported");
        assert_eq!(invalid_tip.branch_len, 1);
        reconsider_block(&node, &json!([hash.to_string()])).unwrap();
        assert_eq!(node.chain.read().height(), 1);
        assert_eq!(node.chain.read().best_hash(), hash);
    }

    #[test]
    fn scantxoutset_matches_wallet_free_address_descriptors() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let address = "bcrt1q2nfxmhd4n3c8834pj72xagvyr9gl57n5r94fsl";
        assert_eq!(
            scan_txout_set(&node, &json!(["status"])).unwrap(),
            Value::Null
        );
        assert_eq!(
            scan_txout_set(&node, &json!(["abort"])).unwrap(),
            Value::Bool(false)
        );
        generate_to_address(&node, &json!([1, address])).unwrap();
        let result =
            scan_txout_set(&node, &json!(["start", [format!("addr({address})")]])).unwrap();
        assert_eq!(result["success"], true);
        assert_eq!(result["txouts"], 1);
        assert_eq!(result["unspents"][0]["height"], 1);
        assert_eq!(result["unspents"][0]["coinbase"], true);
        assert_eq!(
            result["unspents"][0]["blockhash"],
            node.chain.read().block_hash(1).unwrap().to_string()
        );
        assert_eq!(result["unspents"][0]["confirmations"], 1);
        assert!(result["unspents"][0]["scriptPubKey"].is_string());
        assert_eq!(result["total_amount"], 50.0);

        let xpub = "xpub661MyMwAqRbcFtXgS5sYJABqqG9YLmC4Q1Rdap9gSE8NqtwybGhePY2gZ29ESFjqJoCu1Rupje8YtGqsefD265TMg7usUDFdp6W1EGMcet8";
        let ranged_descriptor = format!("wpkh({xpub}/0/*)");
        let ranged_address = derive_addresses(&node, &json!([ranged_descriptor.clone(), [0, 0]]))
            .unwrap()[0]
            .as_str()
            .unwrap()
            .to_owned();
        generate_to_address(&node, &json!([1, ranged_address])).unwrap();
        let ranged_result = scan_txout_set(&node, &json!(["start", [ranged_descriptor]])).unwrap();
        assert_eq!(ranged_result["success"], true);
        assert_eq!(ranged_result["txouts"], 2);
        assert_eq!(ranged_result["unspents"][0]["height"], 2);
    }

    #[test]
    fn service_names_match_core_for_known_and_unknown_bits() {
        assert_eq!(
            peer_services_names(
                wire::NODE_NETWORK
                    | wire::NODE_NETWORK_LIMITED
                    | wire::NODE_BLOOM
                    | wire::NODE_WITNESS
                    | wire::NODE_COMPACT_FILTERS
                    | wire::NODE_P2P_V2
                    | (1u64 << 4)
                    | (1u64 << 63)
            ),
            vec![
                "NETWORK",
                "BLOOM",
                "WITNESS",
                "UNKNOWN[2^4]",
                "COMPACT_FILTERS",
                "NETWORK_LIMITED",
                "P2P_V2",
                "UNKNOWN[2^63]",
            ]
        );
    }

    #[test]
    fn publicly_routable_classification_matches_core_reserved_ranges() {
        assert!(is_publicly_routable("8.8.8.8".parse().unwrap()));
        assert!(!is_publicly_routable("255.255.255.255".parse().unwrap()));
        assert!(!is_publicly_routable("192.0.2.1".parse().unwrap()));
        assert!(!is_publicly_routable("2001:db8::1".parse().unwrap()));
    }

    #[test]
    fn network_active_rpc_controls_peer_admission_state() {
        let directory = tempfile::tempdir().unwrap();
        let mut node = Node::open(Config {
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: vec![OnlyNet::Ipv4],
            proxy: Some("127.0.0.1:9050".parse().unwrap()),
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
            v2_transport: false,
            network_active: false,
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
        .unwrap();
        assert!(!node.network_active());
        let localservices = dispatch_method(&node, "getnetworkinfo", &json!([])).unwrap();
        assert_eq!(
            localservices["localservicesnames"],
            json!(["NETWORK", "WITNESS", "COMPACT_FILTERS"])
        );
        Arc::get_mut(&mut node)
            .unwrap()
            .config
            .external_addresses
            .push("8.8.8.8:18444".parse().unwrap());
        assert_eq!(
            dispatch_method(&node, "getnetworkinfo", &json!([])).unwrap()["localaddresses"],
            json!([{"address": "8.8.8.8", "port": 18444, "score": 4}])
        );
        Arc::get_mut(&mut node)
            .unwrap()
            .config
            .external_addresses
            .clear();
        Arc::get_mut(&mut node).unwrap().config.proxy = None;
        node.set_listen_address("8.8.8.8:18444".parse().unwrap());
        node.add_listen_address("9.9.9.9:18445".parse().unwrap());
        assert_eq!(
            dispatch_method(&node, "getnetworkinfo", &json!([])).unwrap()["localaddresses"],
            json!([
                {"address": "8.8.8.8", "port": 18444, "score": 2},
                {"address": "9.9.9.9", "port": 18445, "score": 2}
            ])
        );
        Arc::get_mut(&mut node).unwrap().config.proxy = Some("127.0.0.1:9050".parse().unwrap());
        dispatch_method(&node, "setnetworkactive", &json!([false])).unwrap();
        assert_eq!(
            dispatch_method(&node, "getnetworkinfo", &json!([])).unwrap()["networkactive"],
            false
        );
        assert_eq!(
            dispatch_method(&node, "getnetworkinfo", &json!([])).unwrap()["networks"]
                .as_array()
                .unwrap()
                .iter()
                .map(|network| network["name"].as_str().unwrap())
                .collect::<Vec<_>>(),
            vec!["ipv4", "ipv6", "onion", "i2p", "cjdns"]
        );
        let networks = dispatch_method(&node, "getnetworkinfo", &json!([])).unwrap();
        let ipv4 = networks["networks"]
            .as_array()
            .unwrap()
            .iter()
            .find(|network| network["name"] == "ipv4")
            .unwrap();
        assert_eq!(ipv4["limited"], json!(false));
        assert_eq!(ipv4["reachable"], json!(true));
        assert_eq!(ipv4["proxy"], json!("127.0.0.1:9050"));
        let ipv6 = networks["networks"]
            .as_array()
            .unwrap()
            .iter()
            .find(|network| network["name"] == "ipv6")
            .unwrap();
        assert_eq!(ipv6["limited"], json!(true));
        assert_eq!(ipv6["reachable"], json!(false));
        assert_eq!(ipv6["proxy"], json!("127.0.0.1:9050"));
        for name in ["onion", "i2p"] {
            let network = networks["networks"]
                .as_array()
                .unwrap()
                .iter()
                .find(|network| network["name"] == name)
                .unwrap();
            assert_eq!(network["limited"], json!(true));
            assert_eq!(network["reachable"], json!(false));
            assert_eq!(network["proxy"], json!("127.0.0.1:9050"));
        }
        let cjdns = networks["networks"]
            .as_array()
            .unwrap()
            .iter()
            .find(|network| network["name"] == "cjdns")
            .unwrap();
        assert_eq!(cjdns["limited"], json!(true));
        assert_eq!(cjdns["reachable"], json!(false));
        assert_eq!(cjdns["proxy"], json!("127.0.0.1:9050"));
        dispatch_method(&node, "setnetworkactive", &json!([true])).unwrap();
        assert!(node.network_active());
        node.set_listen_address("8.8.8.8:18444".parse().unwrap());
        assert_eq!(
            dispatch_method(&node, "getnetworkinfo", &json!([])).unwrap()["localaddresses"],
            json!([])
        );
        node.set_listen_address("[2001:4860:4860::8888]:18444".parse().unwrap());
        assert_eq!(
            dispatch_method(&node, "getnetworkinfo", &json!([])).unwrap()["localaddresses"],
            json!([])
        );
        node.set_listen_address("127.0.0.1:18444".parse().unwrap());
        assert_eq!(
            dispatch_method(&node, "getnetworkinfo", &json!([])).unwrap()["localaddresses"],
            json!([])
        );
    }

    #[test]
    fn addrman_info_reports_all_network_buckets() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
            signet_challenge: None,
        })
        .unwrap();
        let result = get_addrman_info(&node).unwrap();
        for network in ["ipv4", "ipv6", "onion", "i2p", "cjdns", "all_networks"] {
            assert_eq!(result[network]["new"], json!(0));
            assert_eq!(result[network]["tried"], json!(0));
            assert_eq!(result[network]["total"], json!(0));
        }
    }

    #[test]
    fn hidden_addrman_and_peer_message_rpcs_use_real_node_state() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: true,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();

        assert_eq!(
            dispatch_method(&node, "addpeeraddress", &json!(["192.0.2.10", 18444]),).unwrap(),
            json!({"success": true})
        );
        assert_eq!(
            dispatch_method(
                &node,
                "addpeeraddress",
                &json!(["2001:db8::10", 18444, true]),
            )
            .unwrap(),
            json!({"success": true})
        );
        assert_eq!(
            dispatch_method(&node, "addpeeraddress", &json!(["fc00::10", 18444, true]),).unwrap(),
            json!({"success": true})
        );
        assert_eq!(
            dispatch_method(&node, "addpeeraddress", &json!(["192.0.2.10", 18444]),).unwrap()["success"],
            false
        );
        let info = dispatch_method(&node, "getaddrmaninfo", &json!([])).unwrap();
        assert_eq!(info["ipv4"], json!({"new": 1, "tried": 0, "total": 1}));
        assert_eq!(info["ipv6"], json!({"new": 0, "tried": 1, "total": 1}));
        assert_eq!(info["cjdns"], json!({"new": 0, "tried": 1, "total": 1}));
        let raw = dispatch_method(&node, "getrawaddrman", &json!([])).unwrap();
        assert_eq!(raw["new"].as_object().unwrap().len(), 1);
        assert_eq!(raw["tried"].as_object().unwrap().len(), 2);

        let (sender, mut receiver) = tokio::sync::mpsc::unbounded_channel();
        node.register_peer_with_endpoint(
            7,
            crate::address::NetworkEndpoint::Ip("127.0.0.1:18444".parse().unwrap()),
            false,
            sender,
            crate::PeerRegistrationOptions {
                local_address: None,
                permissions: crate::config::PeerPermissions::FORCE_RELAY,
                connection_type: "outbound-full",
            },
        );
        let genesis = node.chain.read().best_hash();
        let header_only = generate_block(&node, &json!(["raw(51)", [], false])).unwrap();
        let header_only_block: bitcoin::Block =
            deserialize(&hex::decode(header_only["hex"].as_str().unwrap()).unwrap()).unwrap();
        let requested_hash = header_only_block.block_hash();
        submit_header(
            &node,
            &json!([hex::encode(serialize(&header_only_block.header))]),
        )
        .unwrap();
        let unversioned_peer_info = dispatch_method(&node, "getpeerinfo", &json!([])).unwrap();
        assert_eq!(unversioned_peer_info[0]["relaytxes"], json!(false));
        assert_eq!(
            unversioned_peer_info[0]["permissions"],
            json!(["forcerelay", "relay"])
        );
        assert_eq!(
            unversioned_peer_info[0]["network"],
            json!("not_publicly_routable")
        );
        assert_eq!(unversioned_peer_info[0]["synced_headers"], json!(-1));
        assert_eq!(unversioned_peer_info[0]["synced_blocks"], json!(-1));
        assert_eq!(unversioned_peer_info[0]["addr_relay_enabled"], json!(true));
        node.update_peer_version(
            7,
            70016,
            crate::wire::NODE_NETWORK | crate::wire::NODE_WITNESS,
            "/test-peer/",
            0,
            true,
        );
        node.update_peer_time_offset(7, 42);
        node.update_peer_bip152_highbandwidth_from(7, true);
        node.update_peer_reported_local_address(7, Some("198.51.100.2:18444".parse().unwrap()));
        node.set_peer_transport_protocol(7, true);
        node.set_peer_session_id(7, Some("ab".repeat(32)));
        node.set_peer_inv_to_send(7, 3);
        let peer_info = dispatch_method(&node, "getpeerinfo", &json!([])).unwrap();
        assert_eq!(peer_info[0]["id"], json!(7));
        assert_eq!(
            peer_info[0]["connection_type"],
            json!("outbound-full-relay")
        );
        assert_eq!(peer_info[0]["presynced_headers"], json!(-1));
        assert_eq!(peer_info[0]["bip152_hb_to"], json!(false));
        assert_eq!(peer_info[0]["bip152_hb_from"], json!(true));
        assert_eq!(peer_info[0]["inflight"], json!([]));
        assert_eq!(peer_info[0]["addrlocal"], json!("198.51.100.2:18444"));
        assert_eq!(peer_info[0]["transport_protocol_type"], json!("v2"));
        assert_eq!(peer_info[0]["session_id"], json!("ab".repeat(32)));
        assert_eq!(peer_info[0]["inv_to_send"], json!(3));
        assert!(peer_info[0].get("startingheight").is_none());
        assert!(peer_info[0].get("pingtime").is_none());
        assert_eq!(peer_info[0]["synced_headers"], json!(-1));
        assert_eq!(peer_info[0]["synced_blocks"], json!(-1));
        node.update_peer_best_known_block(7, genesis);
        let announced = dispatch_method(&node, "getpeerinfo", &json!([])).unwrap();
        assert_eq!(announced[0]["synced_headers"], json!(0));
        assert_eq!(announced[0]["synced_blocks"], json!(-1));
        node.record_peer_block(7, genesis);
        let received = dispatch_method(&node, "getpeerinfo", &json!([])).unwrap();
        assert_eq!(received[0]["synced_headers"], json!(0));
        assert_eq!(received[0]["synced_blocks"], json!(0));
        node.set_peer_connection_type(7, "block-relay-only");
        assert_eq!(
            dispatch_method(&node, "getpeerinfo", &json!([])).unwrap()[0]["connection_type"],
            json!("block-relay-only")
        );
        assert_eq!(
            dispatch_method(&node, "getnetworkinfo", &json!([])).unwrap()["timeoffset"],
            json!(42)
        );
        node.ping_peers();
        let pinging = dispatch_method(&node, "getpeerinfo", &json!([])).unwrap();
        assert!(
            pinging[0]["pingwait"]
                .as_f64()
                .is_some_and(|wait| wait > 0.0)
        );
        let crate::p2p::PeerCommand::Ping(nonce) = receiver.try_recv().unwrap() else {
            panic!("expected ping command");
        };
        node.record_pong(7, nonce);
        assert!(
            dispatch_method(&node, "getpeerinfo", &json!([])).unwrap()[0]
                .get("pingwait")
                .is_none()
        );
        assert_eq!(
            dispatch_method(&node, "sendmsgtopeer", &json!([7, "test", "0102"]),).unwrap(),
            json!({})
        );
        let crate::p2p::PeerCommand::SendMessage { command, payload } =
            receiver.try_recv().unwrap()
        else {
            panic!("expected raw peer message command");
        };
        assert_eq!(command, "test");
        assert_eq!(payload, vec![1, 2]);

        assert_eq!(
            dispatch_method(
                &node,
                "getblockfrompeer",
                &json!([requested_hash.to_string(), 7]),
            )
            .unwrap(),
            json!({})
        );
        let crate::p2p::PeerCommand::RequestBlock(hash) = receiver.try_recv().unwrap() else {
            panic!("expected block request command");
        };
        assert_eq!(hash, requested_hash);
        assert_eq!(
            dispatch_method(&node, "getpeerinfo", &json!([])).unwrap()[0]["inflight"],
            json!([1])
        );
        node.clear_peer_block_request(7, requested_hash);
        assert_eq!(
            dispatch_method(&node, "getpeerinfo", &json!([])).unwrap()[0]["inflight"],
            json!([])
        );
        assert!(
            dispatch_method(&node, "getblockfrompeer", &json!([genesis.to_string(), 7]),).is_err()
        );
        assert!(
            dispatch_method(
                &node,
                "getblockfrompeer",
                &json!([BlockHash::all_zeros().to_string(), 7]),
            )
            .is_err()
        );
    }

    #[test]
    fn network_control_rpcs_manage_added_nodes_and_bans() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        assert_eq!(
            dispatch_method(
                &node,
                "addconnection",
                &json!(["127.0.0.1:18446", "feeler", false]),
            )
            .unwrap(),
            json!({
                "address": "127.0.0.1:18446",
                "connection_type": "feeler"
            })
        );
        assert!(
            dispatch_method(
                &node,
                "addconnection",
                &json!(["127.0.0.1:18446", "feeler", true]),
            )
            .is_ok()
        );
        add_node(&node, &json!(["127.0.0.1:18445", "onetry"])).unwrap();
        assert_eq!(get_added_node_info(&node, &json!([])).unwrap(), json!([]));
        add_node(&node, &json!(["127.0.0.1:18444", "add"])).unwrap();
        assert!(add_node(&node, &json!(["127.0.0.1:18444", "add"])).is_err());
        let added = get_added_node_info(&node, &json!([])).unwrap();
        assert_eq!(added[0]["addednode"], "127.0.0.1:18444");
        assert!(set_ban(&node, &json!(["192.0.2.2", "add", "60"])).is_err());
        set_ban(&node, &json!(["192.0.2.1", "add", 60])).unwrap();
        let banned = list_banned(&node).unwrap();
        assert_eq!(banned.as_array().unwrap().len(), 1);
        assert_eq!(banned[0]["ban_duration"], json!(60));
        assert!(
            banned[0]["time_remaining"]
                .as_u64()
                .is_some_and(|remaining| (1..=60).contains(&remaining))
        );
        assert!(banned[0].get("ban_reason").is_none());
        set_ban(&node, &json!(["192.0.2.3", "add", 0])).unwrap();
        let default_duration = list_banned(&node)
            .unwrap()
            .as_array()
            .unwrap()
            .iter()
            .find(|entry| entry["address"] == "192.0.2.3/32")
            .and_then(|entry| entry["ban_duration"].as_u64());
        assert_eq!(default_duration, Some(86_400));
        set_ban(&node, &json!(["192.0.2.0/24", "add", 60])).unwrap();
        assert!(node.is_banned("192.0.2.99".parse().unwrap()));
        assert!(set_ban(&node, &json!(["192.0.2.2", "add", 60])).is_err());
        let subnet_entry = list_banned(&node)
            .unwrap()
            .as_array()
            .unwrap()
            .iter()
            .find(|entry| entry["address"] == "192.0.2.0/24")
            .cloned()
            .unwrap();
        assert_eq!(subnet_entry["ban_duration"], json!(60));
        set_ban(&node, &json!(["192.0.2.0/24", "remove"])).unwrap();
        assert!(!node.is_banned("192.0.2.99".parse().unwrap()));
        let normalized = normalize_rpc_params(
            "setban",
            &json!({"subnet": "192.0.2.4", "command": "add", "bantime": 60}),
        )
        .unwrap();
        assert_eq!(normalized, json!(["192.0.2.4", "add", 60, null]));
        clear_banned(&node).unwrap();
        assert_eq!(list_banned(&node).unwrap(), json!([]));
        add_node(&node, &json!(["127.0.0.1:18444", "remove"])).unwrap();
        assert_eq!(get_added_node_info(&node, &json!([])).unwrap(), json!([]));
    }

    #[test]
    fn network_address_rpcs_honor_filters_and_node_ids() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        node.remember_address("192.0.2.20:18444".parse().unwrap(), 1, 10);
        node.remember_address("[2001:db8::20]:18444".parse().unwrap(), 8, 20);
        set_ban(&node, &json!(["192.0.2.20", "add", 3600, false])).unwrap();

        let default = get_node_addresses(&node, &json!([])).unwrap();
        assert_eq!(default.as_array().unwrap().len(), 1);
        let all = get_node_addresses(&node, &json!([0])).unwrap();
        assert_eq!(all.as_array().unwrap().len(), 1);
        let ipv6 = get_node_addresses(&node, &json!([10, "ipv6"])).unwrap();
        assert_eq!(ipv6[0]["address"], "2001:db8::20");
        assert_eq!(ipv6[0]["services"], 8);
        assert_eq!(
            get_node_addresses(&node, &json!([1, "onion"])).unwrap(),
            json!([])
        );
        assert!(get_node_addresses(&node, &json!([1, "unknown"])).is_err());

        add_node(&node, &json!(["127.0.0.1:18444", "add"])).unwrap();
        let selected = get_added_node_info(&node, &json!(["127.0.0.1:18444"])).unwrap();
        assert_eq!(selected[0]["addednode"], "127.0.0.1:18444");
        assert!(get_added_node_info(&node, &json!(["127.0.0.1:18445"])).is_err());

        add_node(&node, &json!(["127.0.0.2", "add"])).unwrap();
        let bare = get_added_node_info(&node, &json!(["127.0.0.2"])).unwrap();
        assert_eq!(bare[0]["addednode"], "127.0.0.2");
        assert!(node.is_node_added_endpoint(&NetworkEndpoint::from_socket(
            "127.0.0.2:18444".parse().unwrap(),
        )));
        add_node(&node, &json!(["127.0.0.2", "remove"])).unwrap();
        assert!(!node.is_node_added_endpoint(&NetworkEndpoint::from_socket(
            "127.0.0.2:18444".parse().unwrap(),
        )));

        add_node(&node, &json!(["example.invalid:18444", "add"])).unwrap();
        let hostname = get_added_node_info(&node, &json!(["example.invalid:18444"])).unwrap();
        assert_eq!(hostname[0]["addednode"], "example.invalid:18444");

        let (host_sender, mut host_receiver) = tokio::sync::mpsc::unbounded_channel();
        node.register_peer_with_endpoint(
            12,
            NetworkEndpoint::dns("example.invalid".to_owned(), 18444).unwrap(),
            false,
            host_sender,
            crate::PeerRegistrationOptions {
                local_address: None,
                permissions: crate::config::PeerPermissions::empty(),
                connection_type: "outbound-full",
            },
        );
        disconnect_node(&node, &json!(["example.invalid:18444"])).unwrap();
        assert!(matches!(
            host_receiver.try_recv().unwrap(),
            crate::p2p::PeerCommand::Disconnect
        ));
        node.unregister_peer(12);
        add_node(&node, &json!(["example.invalid:18444", "remove"])).unwrap();

        let (sender, mut receiver) = tokio::sync::mpsc::unbounded_channel();
        node.register_peer(11, "127.0.0.1:18444".parse().unwrap(), false, sender);
        let connected = get_added_node_info(&node, &json!(["127.0.0.1:18444"])).unwrap();
        assert_eq!(connected[0]["addresses"][0]["connected"], "outbound");
        disconnect_node(&node, &json!(["", 11])).unwrap();
        assert!(matches!(
            receiver.try_recv().unwrap(),
            crate::p2p::PeerCommand::Disconnect
        ));
    }

    #[test]
    fn address_and_key_descriptors_are_wallet_free() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let address = "bcrt1q2nfxmhd4n3c8834pj72xagvyr9gl57n5r94fsl";
        let validated = validate_address(&node, &json!([address])).unwrap();
        assert_eq!(validated["isvalid"], true);
        assert_eq!(validated["iswitness"], true);
        let invalid = validate_address(&node, &json!(["not-an-address"])).unwrap();
        assert_eq!(invalid["isvalid"], false);
        assert!(invalid["error"].as_str().is_some());
        assert!(invalid["error_locations"].is_array());
        let witness_script = ScriptBuf::from_bytes(vec![0x51]);
        let p2wsh = Address::p2wsh(&witness_script, Network::Regtest);
        let validated_p2wsh = validate_address(&node, &json!([p2wsh.to_string()])).unwrap();
        assert_eq!(validated_p2wsh["isscript"], true);
        let public_key = "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798";
        let p2tr = Address::p2tr(
            &Secp256k1::new(),
            bitcoin::XOnlyPublicKey::from(
                public_key
                    .parse::<bitcoin::PublicKey>()
                    .expect("test public key is valid"),
            ),
            None,
            Network::Regtest,
        );
        let validated_p2tr = validate_address(&node, &json!([p2tr.to_string()])).unwrap();
        assert_eq!(validated_p2tr["isscript"], true);
        let derived = derive_addresses(&node, &json!([format!("pkh({public_key})")])).unwrap();
        assert_eq!(derived.as_array().unwrap().len(), 1);
        let scripts =
            expand_descriptor_scripts(&node, &format!("wpkh({public_key})"), None).unwrap();
        assert_eq!(scripts.len(), 1);
        let xpub = "xpub661MyMwAqRbcFtXgS5sYJABqqG9YLmC4Q1Rdap9gSE8NqtwybGhePY2gZ29ESFjqJoCu1Rupje8YtGqsefD265TMg7usUDFdp6W1EGMcet8";
        let ranged =
            derive_addresses(&node, &json!([format!("wpkh({xpub}/0/*)"), [0, 1]])).unwrap();
        assert_eq!(ranged.as_array().unwrap().len(), 2);
        let ranged_with_origin = derive_addresses(
            &node,
            &json!([format!("wpkh([d34db33f/84'/0'/0']{xpub}/0/*)"), [0, 1]]),
        )
        .unwrap();
        assert_eq!(ranged_with_origin.as_array().unwrap().len(), 2);
        let descriptor_info =
            get_descriptor_info(&node, &json!([format!("wpkh({public_key})")])).unwrap();
        assert_eq!(descriptor_info["isrange"], false);
        assert_eq!(descriptor_info["issolvable"], true);
        assert_eq!(descriptor_info["hasprivatekeys"], false);
        assert_eq!(descriptor_info["checksum"].as_str().unwrap().len(), 8);
        assert!(
            get_descriptor_info(&node, &json!([format!("wpkh({public_key})#qqqqqqqq")])).is_err()
        );
        let ranged_info =
            get_descriptor_info(&node, &json!([format!("wpkh({xpub}/0/*)")])).unwrap();
        assert_eq!(ranged_info["isrange"], true);
        let multipath_descriptor = format!("wpkh({xpub}/<0;1>/*)");
        let multipath_info =
            get_descriptor_info(&node, &json!([multipath_descriptor.clone()])).unwrap();
        assert_eq!(
            multipath_info["multipath_expansion"]
                .as_array()
                .unwrap()
                .len(),
            2
        );
        assert!(!multipath_info["descriptor"].as_str().unwrap().contains('<'));
        let multipath_addresses =
            derive_addresses(&node, &json!([multipath_descriptor, [0, 1]])).unwrap();
        assert_eq!(multipath_addresses.as_array().unwrap().len(), 2);
        assert!(multipath_addresses[0].as_array().unwrap().len() == 2);
        assert!(multipath_addresses[1].as_array().unwrap().len() == 2);
        let xpriv = bitcoin::bip32::Xpriv::new_master(Network::Regtest, &[6; 32]).unwrap();
        let private_info = get_descriptor_info(&node, &json!([format!("wpkh({xpriv})")])).unwrap();
        assert_eq!(private_info["hasprivatekeys"], true);
        let canonical_private = private_info["descriptor"].as_str().unwrap();
        assert!(!canonical_private.contains("tprv"));
        assert!(canonical_private.contains("tpub"));
        let second_public_key = bitcoin::PrivateKey::new(
            bitcoin::secp256k1::SecretKey::from_slice(&[5; 32]).unwrap(),
            Network::Regtest,
        )
        .public_key(&Secp256k1::new())
        .to_string();
        let multisig = format!("multi(1,{public_key},{second_public_key})");
        let multisig_script = expand_descriptor_scripts(&node, &multisig, None).unwrap();
        assert_eq!(multisig_script.len(), 1);
        assert!(multisig_script[0].is_multisig());
        let public_key_script =
            expand_descriptor_scripts(&node, &format!("pk({public_key})"), None).unwrap();
        assert!(public_key_script[0].is_p2pk());
        let combo_scripts =
            expand_descriptor_scripts(&node, &format!("combo({public_key})"), None).unwrap();
        assert_eq!(combo_scripts.len(), 4);
        let wrapped_multisig =
            expand_descriptor_scripts(&node, &format!("wsh({multisig})"), None).unwrap();
        assert!(wrapped_multisig[0].is_p2wsh());
        let miniscript = format!("wsh(and_v(v:pk({public_key}),older(1)))");
        let miniscript_script = expand_descriptor_scripts(&node, &miniscript, None)
            .unwrap()
            .remove(0);
        assert!(miniscript_script.is_p2wsh());
        let miniscript_candidate = descriptor_candidates(&node, &miniscript, None)
            .unwrap()
            .remove(0);
        assert_eq!(
            miniscript_candidate
                .witness_script
                .as_ref()
                .unwrap()
                .to_p2wsh(),
            miniscript_script
        );
        let nested_miniscript = format!("sh({miniscript})");
        let nested_miniscript_candidate = descriptor_candidates(&node, &nested_miniscript, None)
            .unwrap()
            .remove(0);
        assert!(nested_miniscript_candidate.script_pubkey.is_p2sh());
        assert!(
            nested_miniscript_candidate
                .redeem_script
                .as_ref()
                .is_some_and(|script| script.is_p2wsh())
        );
        assert!(nested_miniscript_candidate.witness_script.is_some());
        let wrapped = derive_addresses(&node, &json!([format!("sh(wpkh({public_key}))")])).unwrap();
        assert_eq!(wrapped.as_array().unwrap().len(), 1);
        let taproot_key = "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798";
        let taproot = derive_addresses(&node, &json!([format!("tr({taproot_key})")])).unwrap();
        assert_eq!(taproot.as_array().unwrap().len(), 1);
        let rawtr = derive_addresses(&node, &json!([format!("rawtr({taproot_key})")])).unwrap();
        assert_eq!(rawtr.as_array().unwrap().len(), 1);
        assert_ne!(rawtr[0], taproot[0]);
        let taproot_tree = derive_addresses(
            &node,
            &json!([format!("tr({taproot_key},pk({public_key}))")]),
        )
        .unwrap();
        assert_eq!(taproot_tree.as_array().unwrap().len(), 1);
        assert_ne!(taproot_tree[0], taproot[0]);
    }

    #[test]
    fn raw_transaction_helpers_are_wallet_free() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let genesis_hash = node.chain.read().best_hash();
        let genesis_txid = node
            .chain
            .write()
            .block(&genesis_hash)
            .unwrap()
            .unwrap()
            .txdata[0]
            .compute_txid();
        let genesis_error =
            get_raw_transaction(&node, &json!([genesis_txid.to_string(), 1])).unwrap_err();
        assert_eq!(
            genesis_error.to_string(),
            "The genesis block coinbase is not considered an ordinary transaction and cannot be retrieved"
        );
        assert_eq!(rpc_error(&genesis_error)["code"], json!(-5));
        let unknown_hash = BlockHash::from_byte_array([0xff; 32]);
        let block_hash_error = get_raw_transaction(
            &node,
            &json!([
                Txid::from_byte_array([8; 32]).to_string(),
                0,
                unknown_hash.to_string()
            ]),
        )
        .unwrap_err();
        assert_eq!(block_hash_error.to_string(), "Block hash not found");
        assert_eq!(rpc_error(&block_hash_error)["code"], json!(-5));
        let missing_transaction = get_raw_transaction(
            &node,
            &json!([
                Txid::from_byte_array([8; 32]).to_string(),
                0,
                genesis_hash.to_string()
            ]),
        )
        .unwrap_err();
        assert_eq!(
            missing_transaction.to_string(),
            "No such transaction found in the provided block. Use gettransaction for wallet transactions."
        );
        assert_eq!(rpc_error(&missing_transaction)["code"], json!(-5));
        let missing_without_txindex = get_raw_transaction(
            &node,
            &json!([Txid::from_byte_array([9; 32]).to_string(), 0]),
        )
        .unwrap_err();
        assert!(
            missing_without_txindex
                .to_string()
                .starts_with("No such mempool transaction. Use -txindex")
        );
        assert_eq!(rpc_error(&missing_without_txindex)["code"], json!(-5));
        let raw = create_raw_transaction(
            &node,
            &json!([
                [{
                    "txid": Txid::from_byte_array([7; 32]).to_string(),
                    "vout": 1,
                }],
                {
                    "bcrt1q2nfxmhd4n3c8834pj72xagvyr9gl57n5r94fsl": "0.25",
                    "data": "deadbeef",
                },
                42,
                true,
                3,
            ]),
        )
        .unwrap();
        let transaction: Transaction =
            deserialize(&hex::decode(raw.as_str().expect("raw transaction hex")).unwrap()).unwrap();
        assert_eq!(transaction.version, Version::non_standard(3));
        assert_eq!(transaction.lock_time, LockTime::from_consensus(42));
        assert_eq!(
            transaction.input[0].sequence.to_consensus_u32(),
            0xffff_fffd
        );
        assert_eq!(transaction.output.len(), 2);
        assert!(transaction.output[1].script_pubkey.is_op_return());
        let decoded = decode_script(
            &node,
            &json!([hex::encode(transaction.output[0].script_pubkey.as_bytes())]),
        )
        .unwrap();
        assert_eq!(decoded["type"], "witness_v0_keyhash");
        assert_eq!(
            decoded["address"],
            "bcrt1q2nfxmhd4n3c8834pj72xagvyr9gl57n5r94fsl"
        );
        assert!(decoded["p2sh"].as_str().is_some());
        assert!(decoded.get("segwit").is_none());
        assert!(decoded.get("hex").is_none());
        let decoded_nulldata = decode_script(
            &node,
            &json!([hex::encode(transaction.output[1].script_pubkey.as_bytes())]),
        )
        .unwrap();
        assert_eq!(decoded_nulldata["type"], "nulldata");
        assert!(decoded_nulldata.get("address").is_none());
        assert!(decoded_nulldata.get("p2sh").is_none());
        assert!(decoded_nulldata.get("segwit").is_none());
        let taproot_script = {
            let mut bytes = vec![0x51, 0x20];
            bytes.extend_from_slice(
                &hex::decode("79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")
                    .unwrap(),
            );
            ScriptBuf::from_bytes(bytes)
        };
        let decoded_taproot =
            decode_script(&node, &json!([hex::encode(taproot_script.as_bytes())])).unwrap();
        assert_eq!(decoded_taproot["type"], "witness_v1_taproot");
        assert!(decoded_taproot.get("p2sh").is_none());
        assert!(decoded_taproot.get("segwit").is_none());
        let decoded_transaction = decode_raw_transaction(&node, &json!([raw])).unwrap();
        assert!(decoded_transaction["vin"][0].get("txinwitness").is_none());
        assert_eq!(
            decoded_transaction["vout"][0]["scriptPubKey"]["type"],
            "witness_v0_keyhash"
        );
        assert_eq!(
            decoded_transaction["vout"][0]["scriptPubKey"]["address"],
            "bcrt1q2nfxmhd4n3c8834pj72xagvyr9gl57n5r94fsl"
        );
        assert!(decode_raw_transaction(&node, &json!([raw, false])).is_ok());
        assert!(decode_raw_transaction(&node, &json!([raw, true])).is_err());

        let mut witness_transaction = transaction.clone();
        witness_transaction.input[0].witness = Witness::from_slice(&[vec![0x01]]);
        let witness_raw = hex::encode(serialize(&witness_transaction));
        assert!(transaction_has_witness_serialization(
            &hex::decode(&witness_raw).unwrap()
        ));
        assert!(decode_raw_transaction(&node, &json!([witness_raw])).is_ok());
        let decoded_witness = decode_raw_transaction(&node, &json!([witness_raw, true])).unwrap();
        assert!(decoded_witness["vin"][0]["txinwitness"].is_array());
        assert!(decode_raw_transaction(&node, &json!([witness_raw, false])).is_err());
        assert!(
            parse_signing_prevouts(Some(&json!([{
                "txid": Txid::from_byte_array([7; 32]).to_string(),
                "vout": 0,
                "scriptPubKey": "51",
                "redeemScript": 1,
            }])))
            .is_err()
        );
        let amount_error = match parse_signing_prevouts(Some(&json!([{
            "txid": Txid::from_byte_array([7; 32]).to_string(),
            "vout": 0,
            "scriptPubKey": "51",
            "amount": "21000000.00000001",
        }]))) {
            Ok(_) => panic!("out-of-range amount was accepted"),
            Err(error) => error,
        };
        assert_eq!(amount_error.to_string(), "Amount out of range");

        let default_raw = create_raw_transaction(
            &node,
            &json!([
                [{
                    "txid": Txid::from_byte_array([7; 32]).to_string(),
                    "vout": 1,
                }],
                {"data": "00"},
            ]),
        )
        .unwrap();
        let default_transaction: Transaction = deserialize(
            &hex::decode(default_raw.as_str().expect("default raw transaction hex")).unwrap(),
        )
        .unwrap();
        assert_eq!(default_transaction.version, Version::TWO);
        assert_eq!(
            default_transaction.input[0].sequence.to_consensus_u32(),
            0xffff_fffd
        );
        let null_inputs = create_raw_transaction(&node, &json!([null, {"data": "00"}])).unwrap();
        let null_input_transaction: Transaction = deserialize(
            &hex::decode(
                null_inputs
                    .as_str()
                    .expect("null-input raw transaction hex"),
            )
            .unwrap(),
        )
        .unwrap();
        assert!(null_input_transaction.input.is_empty());
        assert!(create_raw_transaction(&node, &json!([[], {"data": "00"}, null, "yes"])).is_err());
        assert!(
            create_raw_transaction(&node, &json!([[], {"data": "00"}, null, true, 4])).is_err()
        );
        assert!(create_raw_transaction(&node, &json!([[], {"data": "00"}, "42"])).is_err());
        assert!(
            create_raw_transaction(
                &node,
                &json!([[
                {"txid": Txid::from_byte_array([7; 32]).to_string(), "vout": -1}
            ], {"data": "00"}])
            )
            .is_err()
        );
        assert!(
            create_raw_transaction(
                &node,
                &json!([[
                {"txid": Txid::from_byte_array([7; 32]).to_string(), "vout": 1, "sequence": -1}
            ], {"data": "00"}])
            )
            .is_err()
        );
        assert!(create_raw_transaction(
            &node,
            &json!([[
                {"txid": Txid::from_byte_array([7; 32]).to_string(), "vout": 1, "sequence": u32::MAX}
            ], {"data": "00"}, null, true])
        )
        .is_err());
        assert!(
            create_raw_transaction(
                &node,
                &json!([[
                {"txid": Txid::from_byte_array([7; 32]).to_string(), "vout": 1, "sequence": "1"}
            ], {"data": "00"}])
            )
            .is_err()
        );
        assert!(
            create_raw_transaction(
                &node,
                &json!([[], [
                    {"bcrt1q2nfxmhd4n3c8834pj72xagvyr9gl57n5r94fsl": 0.1},
                    {"bcrt1q2nfxmhd4n3c8834pj72xagvyr9gl57n5r94fsl": 0.2}
                ]])
            )
            .is_err()
        );
        assert!(
            create_raw_transaction(&node, &json!([[], [{"data": "00"}, {"data": "01"}]])).is_err()
        );
        assert_eq!(parse_transaction_verbosity(Some(&json!(1))).unwrap(), 1);
        assert_eq!(parse_transaction_verbosity(Some(&json!(true))).unwrap(), 1);
        assert_eq!(parse_transaction_verbosity(Some(&json!(3))).unwrap(), 3);
        assert_eq!(parse_transaction_verbosity(Some(&json!(-1))).unwrap(), -1);
    }

    #[test]
    fn enabled_txindex_serves_confirmed_raw_transactions_without_a_block_hash() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
            prune: 0,
            reindex: false,
            reindex_chainstate: false,
            load_blocks: Vec::new(),
            txindex: true,
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
        .unwrap();
        let mined = generate_to_descriptor(&node, &json!([1, "raw(51)"])).unwrap();
        let block_hash: BlockHash = mined[0].as_str().unwrap().parse().unwrap();
        let block = node.chain.write().block(&block_hash).unwrap().unwrap();
        let txid = block.txdata[0].compute_txid();

        assert_eq!(
            get_index_info(&node, &json!(["txindex"])).unwrap()["txindex"]["synced"],
            true
        );
        assert!(get_raw_transaction(&node, &json!([txid.to_string(), 1])).is_ok());
        assert!(
            get_raw_transaction(&node, &json!([txid.to_string(), 1, block_hash.to_string()]))
                .is_ok()
        );
        assert!(get_raw_transaction(&node, &json!([txid.to_string(), 1, 1])).is_err());
    }

    #[test]
    fn disabled_txindex_is_not_reported_by_getindexinfo() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let mined = generate_to_descriptor(&node, &json!([1, "raw(51)"])).unwrap();
        let block_hash: BlockHash = mined[0].as_str().unwrap().parse().unwrap();
        let block = node.chain.write().block(&block_hash).unwrap().unwrap();
        let txid = block.txdata[0].compute_txid();
        assert!(get_raw_transaction(&node, &json!([txid.to_string(), 1])).is_err());
        assert!(
            get_raw_transaction(&node, &json!([txid.to_string(), 1, block_hash.to_string()]))
                .is_ok()
        );
        assert_eq!(
            get_index_info(&node, &json!(["txindex"])).unwrap(),
            json!({})
        );
    }

    #[test]
    fn combine_raw_transaction_merges_partial_inputs() {
        let previous_a = OutPoint::new(Txid::from_byte_array([8; 32]), 0);
        let previous_b = OutPoint::new(Txid::from_byte_array([9; 32]), 1);
        let output = TxOut {
            value: bitcoin::Amount::from_sat(1_000),
            script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
        };
        let mut first = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![
                TxIn {
                    previous_output: previous_a,
                    script_sig: ScriptBuf::from_bytes(vec![0x51]),
                    sequence: bitcoin::Sequence::MAX,
                    witness: Witness::default(),
                },
                TxIn {
                    previous_output: previous_b,
                    script_sig: ScriptBuf::new(),
                    sequence: bitcoin::Sequence::MAX,
                    witness: Witness::default(),
                },
            ],
            output: vec![output.clone()],
        };
        let mut second = first.clone();
        second.input[0].script_sig = ScriptBuf::new();
        second.input[1].script_sig = ScriptBuf::from_bytes(vec![0x52]);
        let combined = combine_transaction_variants(&[first.clone(), second.clone()]).unwrap();
        assert_eq!(combined.input[0].script_sig, first.input[0].script_sig);
        assert_eq!(combined.input[1].script_sig, second.input[1].script_sig);
        assert_eq!(combined.output, vec![output]);

        first.output[0].value = bitcoin::Amount::from_sat(999);
        assert!(combine_transaction_variants(&[first, second]).is_err());
    }

    #[test]
    fn combine_raw_transaction_orders_verified_multisig_signatures() {
        let secp = Secp256k1::new();
        let private_keys = [1u8, 2, 3].map(|seed| {
            bitcoin::PrivateKey::new(
                bitcoin::secp256k1::SecretKey::from_slice(&[seed; 32]).unwrap(),
                Network::Regtest,
            )
        });
        let public_keys = private_keys.map(|key| key.public_key(&secp));
        let witness_script = Builder::new()
            .push_int(2)
            .push_key(&public_keys[0])
            .push_key(&public_keys[1])
            .push_key(&public_keys[2])
            .push_int(3)
            .push_opcode(bitcoin::blockdata::opcodes::all::OP_CHECKMULTISIG)
            .into_script();
        let previous_output = TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: Address::p2wsh(&witness_script, Network::Regtest).script_pubkey(),
        };
        let unsigned = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(Txid::from_byte_array([7; 32]), 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(99_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let signing_prevout = SigningPrevout {
            output: previous_output.clone(),
            amount_provided: true,
            redeem_script: None,
            witness_script: Some(witness_script.clone()),
        };
        let sighash_type = DescriptorSighashType {
            ecdsa: EcdsaSighashType::All,
            taproot: TapSighashType::Default,
        };
        let previous_outputs = [previous_output.clone()];
        let mut first = unsigned.clone();
        sign_transaction_input(
            &mut first,
            0,
            &signing_prevout,
            &[private_keys[0]],
            &secp,
            sighash_type,
            Some(&previous_outputs),
        )
        .unwrap();
        let mut second = unsigned;
        sign_transaction_input(
            &mut second,
            0,
            &signing_prevout,
            &[private_keys[2]],
            &secp,
            sighash_type,
            Some(&previous_outputs),
        )
        .unwrap();

        let mut combined = combine_transaction_variants(&[second.clone(), first.clone()]).unwrap();
        let unordered = combined.input[0].witness.to_vec();
        assert_eq!(unordered[1], second.input[0].witness.to_vec()[1]);
        assert_eq!(unordered[2], first.input[0].witness.to_vec()[1]);
        combine_multisig_input(
            &mut combined,
            0,
            &[second.clone(), first.clone()],
            &previous_output,
        )
        .unwrap();
        let ordered = combined.input[0].witness.to_vec();
        assert_eq!(ordered[1], first.input[0].witness.to_vec()[1]);
        assert_eq!(ordered[2], second.input[0].witness.to_vec()[1]);
        validation::validate_transaction_scripts(Network::Regtest, 1, &combined, &previous_outputs)
            .unwrap();
    }

    #[test]
    fn combine_raw_transaction_rejects_missing_inputs() {
        let directory = tempfile::tempdir().unwrap();
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
            dnsseed: false,
            force_dns_seed: false,
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
            max_peers: 0,
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
        .unwrap();
        let transaction = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(Txid::from_byte_array([0xaa; 32]), 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: bitcoin::Amount::from_sat(1),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let error =
            combine_raw_transaction(&node, &json!([[hex::encode(serialize(&transaction))]]))
                .unwrap_err();
        assert_eq!(error.to_string(), "Input not found or already spent");
        assert_eq!(rpc_error(&error)["code"], json!(-25));
    }

    #[test]
    fn signrawtransactionwithkey_signs_a_wallet_free_wpkh_spend() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let secret = bitcoin::secp256k1::SecretKey::from_slice(&[1; 32]).unwrap();
        let private = bitcoin::PrivateKey::new(secret, Network::Regtest);
        let secp = Secp256k1::new();
        let public_key = private.public_key(&secp);
        let compressed = bitcoin::CompressedPublicKey::try_from(public_key).unwrap();
        let previous_script = Address::p2wpkh(&compressed, Network::Regtest).script_pubkey();
        let previous_txid = Txid::from_byte_array([8; 32]);
        let unsigned = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(previous_txid, 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(99_000_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let result = sign_raw_transaction_with_key(
            &node,
            &json!([
                hex::encode(serialize(&unsigned)),
                [private.to_wif()],
                [{
                    "txid": previous_txid.to_string(),
                    "vout": 0,
                    "scriptPubKey": hex::encode(previous_script.as_bytes()),
                    "amount": 1.0,
                }],
            ]),
        )
        .unwrap();
        assert_eq!(result["complete"], true);
        assert!(result.get("errors").is_none());
        let signed: Transaction =
            deserialize(&hex::decode(result["hex"].as_str().unwrap()).unwrap()).unwrap();
        assert_eq!(signed.input[0].script_sig, ScriptBuf::new());
        assert_eq!(signed.input[0].witness.len(), 2);

        let taproot_internal_secret = bitcoin::secp256k1::SecretKey::from_slice(&[3; 32]).unwrap();
        let taproot_keypair =
            bitcoin::secp256k1::Keypair::from_secret_key(&secp, &taproot_internal_secret)
                .tap_tweak(&secp, None);
        let taproot_output_key = taproot_keypair.public_parts().0.to_x_only_public_key();
        let taproot_private =
            bitcoin::PrivateKey::new(taproot_keypair.to_keypair().secret_key(), Network::Regtest);
        let taproot_previous_txid = Txid::from_byte_array([10; 32]);
        let taproot_previous_script = raw_taproot_script_pubkey(taproot_output_key);
        let taproot_unsigned = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(taproot_previous_txid, 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(99_000_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let taproot_prevtx = json!([{
            "txid": taproot_previous_txid.to_string(),
            "vout": 0,
            "scriptPubKey": hex::encode(taproot_previous_script.as_bytes()),
            "amount": "1.00000000",
        }]);
        let taproot_result = sign_raw_transaction_with_key(
            &node,
            &json!([
                hex::encode(serialize(&taproot_unsigned)),
                [taproot_private.to_wif()],
                taproot_prevtx,
            ]),
        )
        .unwrap();
        assert_eq!(taproot_result["complete"], true);
        let taproot_signed: Transaction =
            deserialize(&hex::decode(taproot_result["hex"].as_str().unwrap()).unwrap()).unwrap();
        assert!(taproot_signed.input[0].script_sig.is_empty());
        assert_eq!(taproot_signed.input[0].witness.len(), 1);
        assert_eq!(taproot_signed.input[0].witness.to_vec()[0].len(), 64);

        let taproot_explicit_result = sign_raw_transaction_with_key(
            &node,
            &json!([
                hex::encode(serialize(&taproot_unsigned)),
                [taproot_private.to_wif()],
                [{
                    "txid": taproot_previous_txid.to_string(),
                    "vout": 0,
                    "scriptPubKey": hex::encode(taproot_previous_script.as_bytes()),
                    "amount": "1.00000000",
                }],
                "ALL",
            ]),
        )
        .unwrap();
        let taproot_explicit_signed: Transaction =
            deserialize(&hex::decode(taproot_explicit_result["hex"].as_str().unwrap()).unwrap())
                .unwrap();
        assert_eq!(taproot_explicit_result["complete"], true);
        assert_eq!(
            taproot_explicit_signed.input[0].witness.to_vec()[0].len(),
            65
        );

        let anchor_previous_txid = Txid::from_byte_array([11; 32]);
        let anchor_previous_script = ScriptBuf::new_p2a();
        let anchor_unsigned = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(anchor_previous_txid, 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(99_000_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let anchor_raw = hex::encode(serialize(&anchor_unsigned));
        let anchor_result = sign_raw_transaction_with_key(
            &node,
            &json!([
                anchor_raw,
                [],
                [{
                    "txid": anchor_previous_txid.to_string(),
                    "vout": 0,
                    "scriptPubKey": hex::encode(anchor_previous_script.as_bytes()),
                }],
            ]),
        )
        .unwrap();
        assert_eq!(anchor_result["complete"], true);
        assert_eq!(
            anchor_result["hex"],
            hex::encode(serialize(&anchor_unsigned))
        );

        let second_secret = bitcoin::secp256k1::SecretKey::from_slice(&[2; 32]).unwrap();
        let second_public =
            bitcoin::PrivateKey::new(second_secret, Network::Regtest).public_key(&secp);
        let witness_script = Builder::new()
            .push_int(1)
            .push_key(&public_key)
            .push_key(&second_public)
            .push_int(2)
            .push_opcode(bitcoin::blockdata::opcodes::all::OP_CHECKMULTISIG)
            .into_script();
        let witness_prevout_script = witness_script.to_p2wsh();
        let witness_previous_txid = Txid::from_byte_array([9; 32]);
        let witness_unsigned = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(witness_previous_txid, 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(99_000_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let multisig_result = sign_raw_transaction_with_key(
            &node,
            &json!([
                hex::encode(serialize(&witness_unsigned)),
                [private.to_wif()],
                [{
                    "txid": witness_previous_txid.to_string(),
                    "vout": 0,
                    "scriptPubKey": hex::encode(witness_prevout_script.as_bytes()),
                    "witnessScript": hex::encode(witness_script.as_bytes()),
                    "amount": "1.00000000",
                }],
            ]),
        )
        .unwrap();
        assert_eq!(multisig_result["complete"], true);
        let multisig_signed: Transaction =
            deserialize(&hex::decode(multisig_result["hex"].as_str().unwrap()).unwrap()).unwrap();
        assert!(multisig_signed.input[0].script_sig.is_empty());
        assert_eq!(multisig_signed.input[0].witness.len(), 3);

        let native_redeem_only = sign_raw_transaction_with_key(
            &node,
            &json!([
                hex::encode(serialize(&witness_unsigned)),
                [private.to_wif()],
                [{
                    "txid": witness_previous_txid.to_string(),
                    "vout": 0,
                    "scriptPubKey": hex::encode(witness_prevout_script.as_bytes()),
                    "redeemScript": hex::encode(witness_script.as_bytes()),
                    "amount": "1.00000000",
                }],
            ]),
        )
        .unwrap();
        assert_eq!(native_redeem_only["complete"], true);

        let nested_prevout_script = Address::p2sh(&witness_prevout_script, Network::Regtest)
            .unwrap()
            .script_pubkey();
        let nested_previous_txid = Txid::from_byte_array([12; 32]);
        let nested_unsigned = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(nested_previous_txid, 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(99_000_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let nested_prevtx = json!([{
            "txid": nested_previous_txid.to_string(),
            "vout": 0,
            "scriptPubKey": hex::encode(nested_prevout_script.as_bytes()),
            "redeemScript": hex::encode(witness_script.as_bytes()),
            "witnessScript": hex::encode(witness_script.as_bytes()),
            "amount": "1.00000000",
        }]);
        let nested_result = sign_raw_transaction_with_key(
            &node,
            &json!([
                hex::encode(serialize(&nested_unsigned)),
                [private.to_wif()],
                nested_prevtx,
            ]),
        )
        .unwrap();
        assert_eq!(nested_result["complete"], true);
        assert!(nested_result.get("errors").is_none());
        let nested_signed: Transaction =
            deserialize(&hex::decode(nested_result["hex"].as_str().unwrap()).unwrap()).unwrap();
        assert_eq!(
            nested_signed.input[0].script_sig,
            push_script_items(&[witness_prevout_script.to_bytes()]).unwrap()
        );
        assert_eq!(nested_signed.input[0].witness.len(), 3);

        let missing_nested = sign_raw_transaction_with_key(
            &node,
            &json!([
                hex::encode(serialize(&nested_unsigned)),
                [],
                [{
                    "txid": nested_previous_txid.to_string(),
                    "vout": 0,
                    "scriptPubKey": hex::encode(nested_prevout_script.as_bytes()),
                    "amount": "1.00000000",
                }],
            ]),
        )
        .unwrap_err();
        assert_eq!(
            missing_nested.to_string(),
            "Missing redeemScript/witnessScript"
        );

        let correspondence_mismatch = sign_raw_transaction_with_key(
            &node,
            &json!([
                hex::encode(serialize(&nested_unsigned)),
                [],
                [{
                    "txid": nested_previous_txid.to_string(),
                    "vout": 0,
                    "scriptPubKey": hex::encode(nested_prevout_script.as_bytes()),
                    "redeemScript": "6a",
                    "witnessScript": hex::encode(witness_script.as_bytes()),
                    "amount": "1.00000000",
                }],
            ]),
        )
        .unwrap_err();
        assert_eq!(
            correspondence_mismatch.to_string(),
            "redeemScript does not correspond to witnessScript"
        );

        let script_pubkey_mismatch = sign_raw_transaction_with_key(
            &node,
            &json!([
                hex::encode(serialize(&nested_unsigned)),
                [],
                [{
                    "txid": nested_previous_txid.to_string(),
                    "vout": 0,
                    "scriptPubKey": hex::encode(nested_prevout_script.as_bytes()),
                    "redeemScript": "6a",
                    "amount": "1.00000000",
                }],
            ]),
        )
        .unwrap_err();
        assert_eq!(
            script_pubkey_mismatch.to_string(),
            "redeemScript/witnessScript does not match scriptPubKey"
        );

        let mined = generate_to_descriptor(&node, &json!([1, "raw(51)"])).unwrap();
        let funding_hash: BlockHash = mined[0].as_str().unwrap().parse().unwrap();
        let funding = node.chain.write().block(&funding_hash).unwrap().unwrap();
        let funding_txid = funding.txdata[0].compute_txid();
        let mismatch_transaction = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(funding_txid, 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(1),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let mismatch = sign_raw_transaction_with_key(
            &node,
            &json!([
                hex::encode(serialize(&mismatch_transaction)),
                [],
                [{
                    "txid": funding_txid.to_string(),
                    "vout": 0,
                    "scriptPubKey": "52",
                }],
            ]),
        )
        .unwrap_err();
        assert_eq!(
            mismatch.to_string(),
            "Previous output scriptPubKey mismatch"
        );
    }

    #[test]
    fn message_signing_rpcs_round_trip_without_a_wallet() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let secret = bitcoin::secp256k1::SecretKey::from_slice(&[2; 32]).unwrap();
        let private = bitcoin::PrivateKey::new(secret, Network::Regtest);
        let public_key = private.public_key(&Secp256k1::new());
        let address = Address::p2pkh(public_key, Network::Regtest);
        let message = "wallet-free message";
        let signature = sign_message_with_private_key(&json!([private.to_wif(), message])).unwrap();
        assert_eq!(
            verify_message(&node, &json!([address.to_string(), signature, message]),).unwrap(),
            true
        );
        assert_eq!(
            verify_message(&node, &json!([address.to_string(), signature, "tampered"]),).unwrap(),
            false
        );
    }

    #[test]
    fn createmultisig_supports_legacy_and_segwit_address_types() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let secp = Secp256k1::new();
        let first = bitcoin::PrivateKey::new(
            bitcoin::secp256k1::SecretKey::from_slice(&[3; 32]).unwrap(),
            Network::Regtest,
        );
        let second = bitcoin::PrivateKey::new(
            bitcoin::secp256k1::SecretKey::from_slice(&[4; 32]).unwrap(),
            Network::Regtest,
        );
        let keys = json!([
            first.public_key(&secp).to_string(),
            second.public_key(&secp).to_string(),
        ]);
        assert!(create_multisig(&node, &json!([1, keys, 1])).is_err());
        let legacy = create_multisig(&node, &json!([1, keys])).unwrap();
        let redeem_script =
            ScriptBuf::from_bytes(hex::decode(legacy["redeemScript"].as_str().unwrap()).unwrap());
        assert!(redeem_script.is_multisig());
        assert!(legacy["address"].as_str().unwrap().starts_with('2'));
        let legacy_descriptor = legacy["descriptor"].as_str().unwrap();
        assert!(legacy_descriptor.starts_with("sh(multi(1,"));
        assert_eq!(legacy_descriptor.matches('#').count(), 1);
        let segwit = create_multisig(&node, &json!([1, keys, "bech32"])).unwrap();
        assert!(segwit["address"].as_str().unwrap().starts_with("bcrt1q"));
        assert!(
            segwit["descriptor"]
                .as_str()
                .unwrap()
                .starts_with("wsh(multi(1,")
        );

        let uncompressed = bitcoin::PrivateKey::new_uncompressed(
            bitcoin::secp256k1::SecretKey::from_slice(&[5; 32]).unwrap(),
            Network::Regtest,
        );
        let fallback = create_multisig(
            &node,
            &json!([1, [uncompressed.public_key(&secp).to_string()], "bech32"]),
        )
        .unwrap();
        assert!(fallback["address"].as_str().unwrap().starts_with('2'));
        assert!(
            fallback["descriptor"]
                .as_str()
                .unwrap()
                .starts_with("sh(multi(1,")
        );
        assert_eq!(
            fallback["warnings"][0],
            json!(
                "Unable to make chosen address type, please ensure no uncompressed public keys are present."
            )
        );
    }

    #[test]
    fn psbt_rpcs_cover_wallet_free_lifecycle() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let address = "bcrt1q2nfxmhd4n3c8834pj72xagvyr9gl57n5r94fsl";
        let created = create_psbt(&node, &json!([[], {address: 0.5}])).unwrap();
        let created_psbt = parse_psbt(&json!([created.clone()]), 0).unwrap();
        assert!(created_psbt.unsigned_tx.input.is_empty());
        let decoded_created = decode_psbt(&node, &json!([created.clone()])).unwrap();
        assert_eq!(decoded_created["psbt_version"], 0);
        assert!(decoded_created["global_xpubs"].is_array());
        assert!(decoded_created.get("global_xpub").is_none());
        assert!(decoded_created["tx"].get("hex").is_none());
        assert_eq!(
            combine_psbt(&json!([[created.clone(), created]])).unwrap(),
            json!(encode_psbt(&created_psbt))
        );
        let joined_first = create_psbt(
            &node,
            &json!([[{"txid": Txid::from_byte_array([11; 32]), "vout": 0}], {"data": "01"}]),
        )
        .unwrap();
        let joined_second = create_psbt(
            &node,
            &json!([[{"txid": Txid::from_byte_array([12; 32]), "vout": 0}], {"data": "02"}]),
        )
        .unwrap();
        let joined = parse_psbt(
            &json!([join_psbts(&json!([[joined_first, joined_second]])).unwrap()]),
            0,
        )
        .unwrap();
        assert_eq!(joined.unsigned_tx.input.len(), 2);
        assert_eq!(joined.unsigned_tx.output.len(), 2);

        let mined = generate_to_descriptor(&node, &json!([1, "raw(51)"])).unwrap();
        let funding_hash: BlockHash = mined[0].as_str().unwrap().parse().unwrap();
        let funding = node.chain.write().block(&funding_hash).unwrap().unwrap();
        let funding_txid = funding.txdata[0].compute_txid();
        let unsigned = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(funding_txid, 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(4_999_999_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let psbt = Psbt::from_unsigned_tx(unsigned.clone()).unwrap();
        let updated = update_psbt_utxos(&node, &json!([encode_psbt(&psbt)])).unwrap();
        let updated_psbt = parse_psbt(&json!([updated]), 0).unwrap();
        assert!(updated_psbt.inputs[0].non_witness_utxo.is_some());
        let decoded_updated = decode_psbt(&node, &json!([encode_psbt(&updated_psbt)])).unwrap();
        assert!(decoded_updated["inputs"][0]["non_witness_utxo"].is_object());
        assert!(
            decoded_updated["inputs"][0]["non_witness_utxo"]
                .get("hex")
                .is_none()
        );
        assert!(decoded_updated["fee"].is_number());
        assert_eq!(
            analyze_psbt(&json!([encode_psbt(&updated_psbt)])).unwrap()["next"],
            "updater"
        );

        let secret = bitcoin::secp256k1::SecretKey::from_slice(&[1; 32]).unwrap();
        let private = bitcoin::PrivateKey::new(secret, Network::Regtest);
        let secp = Secp256k1::new();
        let public_key = private.public_key(&secp);
        let compressed = bitcoin::CompressedPublicKey::try_from(public_key).unwrap();
        let previous_script = Address::p2wpkh(&compressed, Network::Regtest).script_pubkey();
        let previous_output = TxOut {
            value: Amount::from_sat(100_000_000),
            script_pubkey: previous_script.clone(),
        };
        let signed_unsigned = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(Txid::from_byte_array([9; 32]), 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(99_000_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let mut partial = Psbt::from_unsigned_tx(signed_unsigned).unwrap();
        partial.inputs[0].witness_utxo = Some(previous_output);
        let missing_analysis = analyze_psbt(&json!([encode_psbt(&partial)])).unwrap();
        assert_eq!(missing_analysis["next"], "updater");
        assert_eq!(
            missing_analysis["inputs"][0]["missing"]["pubkeys"][0],
            hex::encode(compressed.wpubkey_hash().to_byte_array())
        );
        let sighash = SighashCache::new(&partial.unsigned_tx)
            .p2wpkh_signature_hash(
                0,
                &previous_script,
                Amount::from_sat(100_000_000),
                EcdsaSighashType::All,
            )
            .unwrap();
        let signature = secp.sign_ecdsa(&Message::from(sighash), &private.inner);
        partial.inputs[0].partial_sigs.insert(
            public_key,
            EcdsaSignature {
                signature,
                sighash_type: EcdsaSighashType::All,
            },
        );
        let analyzed = analyze_psbt(&json!([encode_psbt(&partial)])).unwrap();
        assert_eq!(analyzed["next"], "finalizer");
        let finalized = finalize_psbt(&json!([encode_psbt(&partial), false])).unwrap();
        assert_eq!(finalized["complete"], true);
        assert!(finalized.get("hex").is_none());
        let extracted = finalize_psbt(&json!([finalized["psbt"].clone()])).unwrap();
        assert_eq!(extracted["complete"], true);
        assert!(extracted["hex"].as_str().is_some());
        let converted = convert_to_psbt(&json!([extracted["hex"].clone(), true])).unwrap();
        let converted_psbt = parse_psbt(&json!([converted]), 0).unwrap();
        assert!(converted_psbt.inputs[0].final_script_witness.is_none());
        let decoded_converted = decode_psbt(&node, &json!([encode_psbt(&converted_psbt)])).unwrap();
        assert!(
            decoded_converted["inputs"][0]
                .get("final_scriptwitness")
                .is_none()
        );
        assert!(
            decoded_converted["inputs"][0]
                .get("final_scriptWitness")
                .is_none()
        );
        assert!(convert_to_psbt(&json!([extracted["hex"].clone(), true, false])).is_err());
        assert!(convert_to_psbt(&json!([extracted["hex"].clone(), false, true])).is_err());

        let multisig_script = Builder::new()
            .push_int(1)
            .push_key(&public_key)
            .push_int(1)
            .push_opcode(bitcoin::blockdata::opcodes::all::OP_CHECKMULTISIG)
            .into_script();
        let mut multisig = Psbt::from_unsigned_tx(Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(Txid::from_byte_array([10; 32]), 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(99_000_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        })
        .unwrap();
        multisig.inputs[0].witness_utxo = Some(TxOut {
            value: Amount::from_sat(100_000_000),
            script_pubkey: multisig_script.to_p2wsh(),
        });
        multisig.inputs[0].witness_script = Some(multisig_script);
        multisig.inputs[0].partial_sigs.insert(
            public_key,
            EcdsaSignature {
                signature,
                sighash_type: EcdsaSighashType::All,
            },
        );
        let finalized_multisig = finalize_psbt(&json!([encode_psbt(&multisig), false])).unwrap();
        assert_eq!(finalized_multisig["complete"], true);
        let finalized_multisig =
            parse_psbt(&json!([finalized_multisig["psbt"].clone()]), 0).unwrap();
        assert_eq!(
            finalized_multisig.inputs[0]
                .final_script_witness
                .as_ref()
                .unwrap()
                .len(),
            3
        );
    }

    #[test]
    fn descriptorprocesspsbt_updates_wrappers_and_signs_transient_xprivs() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let xpriv = bitcoin::bip32::Xpriv::new_master(Network::Regtest, &[7; 32]).unwrap();
        let descriptor = format!("wpkh([d34db33f/84'/0'/0']{xpriv})");
        let secp = Secp256k1::new();
        let private = bitcoin::PrivateKey::new(xpriv.private_key, Network::Regtest);
        let public_key = private.public_key(&secp);
        let compressed = bitcoin::CompressedPublicKey::try_from(public_key).unwrap();
        let previous_script = Address::p2wpkh(&compressed, Network::Regtest).script_pubkey();
        let unsigned = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(Txid::from_byte_array([21; 32]), 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(99_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let mut psbt = Psbt::from_unsigned_tx(unsigned).unwrap();
        psbt.inputs[0].witness_utxo = Some(TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: previous_script,
        });
        assert!(
            descriptor_process_psbt(
                &node,
                &json!([
                    encode_psbt(&psbt),
                    [format!("wpkh({public_key})")],
                    1,
                    true,
                    true
                ]),
            )
            .is_err()
        );
        assert!(
            descriptor_process_psbt(
                &node,
                &json!([
                    encode_psbt(&psbt),
                    [format!("wpkh({public_key})")],
                    "SIGHASH_ALL",
                    1,
                    true
                ]),
            )
            .is_err()
        );
        assert!(
            descriptor_process_psbt(
                &node,
                &json!([
                    encode_psbt(&psbt),
                    [format!("wpkh({public_key})")],
                    "SIGHASH_ALL",
                    true,
                    1
                ]),
            )
            .is_err()
        );
        let processed = descriptor_process_psbt(
            &node,
            &json!([encode_psbt(&psbt), [descriptor], "SIGHASH_ALL", true, true]),
        )
        .unwrap();
        assert_eq!(processed["complete"], true);
        assert!(processed["hex"].as_str().is_some());
        let processed_psbt = parse_psbt(&json!([processed["psbt"].clone()]), 0).unwrap();
        assert!(processed_psbt.inputs[0].final_script_witness.is_some());
        assert_eq!(
            processed_psbt.inputs[0]
                .bip32_derivation
                .get(&public_key.inner)
                .unwrap()
                .1
                .to_string(),
            "84'/0'/0'"
        );

        let nested_descriptor = format!("sh(wpkh({public_key}))");
        let nested_script = Address::p2sh(
            &Address::p2wpkh(&compressed, Network::Regtest).script_pubkey(),
            Network::Regtest,
        )
        .unwrap()
        .script_pubkey();
        let mut nested = processed_psbt.clone();
        nested.inputs[0].final_script_sig = None;
        nested.inputs[0].final_script_witness = None;
        nested.inputs[0].partial_sigs.clear();
        nested.inputs[0].witness_utxo = Some(TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: nested_script,
        });
        let nested_processed = descriptor_process_psbt(
            &node,
            &json!([
                encode_psbt(&nested),
                [nested_descriptor],
                "SIGHASH_ALL",
                true,
                false
            ]),
        )
        .unwrap();
        let nested_psbt = parse_psbt(&json!([nested_processed["psbt"].clone()]), 0).unwrap();
        assert_eq!(
            nested_psbt.inputs[0].redeem_script.as_ref().unwrap(),
            &Address::p2wpkh(&compressed, Network::Regtest).script_pubkey()
        );
        assert_eq!(nested_processed["complete"], false);

        let miniscript_descriptor = format!("wsh(and_v(v:pk({xpriv}),older(1)))");
        let miniscript_script = expand_descriptor_scripts(&node, &miniscript_descriptor, None)
            .unwrap()
            .remove(0);
        let miniscript_unsigned = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(Txid::from_byte_array([24; 32]), 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::from_consensus(1),
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(99_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let mut miniscript_psbt = Psbt::from_unsigned_tx(miniscript_unsigned).unwrap();
        miniscript_psbt.inputs[0].witness_utxo = Some(TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: miniscript_script,
        });
        let miniscript_processed = descriptor_process_psbt(
            &node,
            &json!([
                encode_psbt(&miniscript_psbt),
                [miniscript_descriptor],
                "SIGHASH_ALL",
                true,
                true
            ]),
        )
        .unwrap();
        assert_eq!(miniscript_processed["complete"], true);
        let miniscript_processed =
            parse_psbt(&json!([miniscript_processed["psbt"].clone()]), 0).unwrap();
        assert_eq!(
            miniscript_processed.inputs[0]
                .final_script_witness
                .as_ref()
                .unwrap()
                .len(),
            2
        );

        let nested_miniscript_descriptor = format!("sh({miniscript_descriptor})");
        let nested_miniscript_script =
            expand_descriptor_scripts(&node, &nested_miniscript_descriptor, None)
                .unwrap()
                .remove(0);
        let mut nested_miniscript_psbt = miniscript_psbt.clone();
        nested_miniscript_psbt.inputs[0].witness_utxo = Some(TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: nested_miniscript_script,
        });
        let nested_miniscript_processed = descriptor_process_psbt(
            &node,
            &json!([
                encode_psbt(&nested_miniscript_psbt),
                [nested_miniscript_descriptor],
                "SIGHASH_ALL",
                true,
                true
            ]),
        )
        .unwrap();
        assert_eq!(nested_miniscript_processed["complete"], true);
        let nested_miniscript_processed =
            parse_psbt(&json!([nested_miniscript_processed["psbt"].clone()]), 0).unwrap();
        assert!(
            nested_miniscript_processed.inputs[0]
                .final_script_sig
                .is_some()
        );
        assert_eq!(
            nested_miniscript_processed.inputs[0]
                .final_script_witness
                .as_ref()
                .unwrap()
                .len(),
            2
        );

        let taproot_descriptor = format!("tr([d34db33f/86'/0'/0']{xpriv})");
        let internal_key = bitcoin::XOnlyPublicKey::from(public_key);
        let taproot_script =
            Address::p2tr(&secp, internal_key, None, Network::Regtest).script_pubkey();
        let taproot_unsigned = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(Txid::from_byte_array([22; 32]), 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(99_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let mut taproot_psbt = Psbt::from_unsigned_tx(taproot_unsigned).unwrap();
        taproot_psbt.inputs[0].witness_utxo = Some(TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: taproot_script,
        });
        let taproot_processed = descriptor_process_psbt(
            &node,
            &json!([
                encode_psbt(&taproot_psbt),
                [taproot_descriptor],
                "SIGHASH_DEFAULT",
                true,
                true
            ]),
        )
        .unwrap();
        assert_eq!(taproot_processed["complete"], true);
        let taproot_processed_psbt =
            parse_psbt(&json!([taproot_processed["psbt"].clone()]), 0).unwrap();
        assert_eq!(
            taproot_processed_psbt.inputs[0].tap_internal_key,
            Some(internal_key)
        );
        assert!(taproot_processed_psbt.inputs[0].tap_key_sig.is_some());
        assert_eq!(
            taproot_processed_psbt.inputs[0]
                .final_script_witness
                .as_ref()
                .unwrap()
                .len(),
            1
        );
        assert!(
            taproot_processed_psbt.inputs[0]
                .tap_key_origins
                .contains_key(&internal_key)
        );
        let decoded_taproot =
            decode_psbt(&node, &json!([encode_psbt(&taproot_processed_psbt)])).unwrap();
        assert!(decoded_taproot["inputs"][0]["taproot_key_path_sig"].is_string());
        assert!(decoded_taproot["inputs"][0]["taproot_internal_key"].is_string());
        assert!(decoded_taproot["inputs"][0]["taproot_bip32_derivs"].is_array());
        assert!(decoded_taproot["inputs"][0]["final_scriptwitness"].is_array());
        assert!(decoded_taproot["inputs"][0].get("tap_key_sig").is_none());

        let taproot_tree_descriptor = format!("tr([d34db33f/86'/0'/0']{xpriv},pk({public_key}))");
        let taproot_tree_script = expand_descriptor_scripts(&node, &taproot_tree_descriptor, None)
            .unwrap()
            .remove(0);
        let tree_unsigned = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(Txid::from_byte_array([23; 32]), 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(99_000),
                script_pubkey: taproot_tree_script.clone(),
            }],
        };
        let mut tree_psbt = Psbt::from_unsigned_tx(tree_unsigned).unwrap();
        tree_psbt.inputs[0].witness_utxo = Some(TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: taproot_tree_script,
        });
        let tree_processed = descriptor_process_psbt(
            &node,
            &json!([
                encode_psbt(&tree_psbt),
                [taproot_tree_descriptor],
                "SIGHASH_DEFAULT",
                true,
                false
            ]),
        )
        .unwrap();
        let tree_processed_psbt = parse_psbt(&json!([tree_processed["psbt"].clone()]), 0).unwrap();
        assert_eq!(
            tree_processed_psbt.inputs[0].tap_internal_key,
            Some(internal_key)
        );
        assert_eq!(tree_processed_psbt.inputs[0].tap_scripts.len(), 1);
        assert!(tree_processed_psbt.outputs[0].tap_tree.is_some());

        let leaf_xpriv = bitcoin::bip32::Xpriv::new_master(Network::Regtest, &[8; 32]).unwrap();
        let leaf_private = bitcoin::PrivateKey::new(leaf_xpriv.private_key, Network::Regtest);
        let leaf_public = leaf_private.public_key(&secp);
        let script_path_descriptor =
            format!("tr({internal_key},pk([d34db33f/86'/0'/0']{leaf_xpriv}))");
        let script_path_script = expand_descriptor_scripts(&node, &script_path_descriptor, None)
            .unwrap()
            .remove(0);
        let mut script_path_psbt = tree_psbt;
        script_path_psbt.unsigned_tx.output[0].script_pubkey = script_path_script.clone();
        script_path_psbt.inputs[0].witness_utxo = Some(TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: script_path_script,
        });
        let script_path_processed = descriptor_process_psbt(
            &node,
            &json!([
                encode_psbt(&script_path_psbt),
                [script_path_descriptor],
                "SIGHASH_DEFAULT",
                true,
                false
            ]),
        )
        .unwrap();
        assert_eq!(script_path_processed["complete"], false);
        let script_path_psbt =
            parse_psbt(&json!([script_path_processed["psbt"].clone()]), 0).unwrap();
        assert_eq!(script_path_psbt.inputs[0].tap_script_sigs.len(), 1);
        assert_eq!(
            script_path_psbt.inputs[0]
                .tap_script_sigs
                .keys()
                .next()
                .unwrap()
                .0,
            bitcoin::XOnlyPublicKey::from(leaf_public)
        );
        let finalized_script_path =
            finalize_psbt(&json!([encode_psbt(&script_path_psbt), true])).unwrap();
        assert_eq!(finalized_script_path["complete"], true);
        let finalized_script_path =
            parse_psbt(&json!([finalized_script_path["psbt"].clone()]), 0).unwrap();
        assert_eq!(
            finalized_script_path.inputs[0]
                .final_script_witness
                .as_ref()
                .unwrap()
                .len(),
            3
        );
    }

    #[test]
    fn importmempool_round_trips_a_wallet_free_pool() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let initial_download_error = dispatch_method(
            &node,
            "importmempool",
            &json!([directory.path().join("missing.dat").to_string_lossy()]),
        )
        .unwrap_err();
        assert!(
            initial_download_error
                .to_string()
                .contains("Can only import the mempool after the block download and sync is done.")
        );
        let hashes = generate_to_descriptor(&node, &json!([101, "raw(51)"])).unwrap();
        let funding_hash: BlockHash = hashes[0].as_str().unwrap().parse().unwrap();
        let funding = node.chain.write().block(&funding_hash).unwrap().unwrap();
        let transaction = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(funding.txdata[0].compute_txid(), 0),
                script_sig: ScriptBuf::from_bytes(vec![0x00; 8]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(4_999_999_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let txid = node.accept_transaction(transaction).unwrap();
        let path = directory.path().join("mempool-import.json");
        node.mempool.read().save_to_file(&path).unwrap();
        node.mempool.write().remove(&txid);
        assert!(node.mempool.read().get(&txid).is_none());
        assert!(
            dispatch_method(
                &node,
                "importmempool",
                &json!([path.to_string_lossy().to_string(), 1]),
            )
            .unwrap_err()
            .to_string()
            .contains("options must be an object")
        );
        assert!(
            dispatch_method(
                &node,
                "importmempool",
                &json!([
                    path.to_string_lossy().to_string(),
                    {"use_current_time": 1}
                ]),
            )
            .unwrap_err()
            .to_string()
            .contains("use_current_time must be a boolean")
        );
        assert_eq!(
            dispatch_method(
                &node,
                "importmempool",
                &json!([path.to_string_lossy().to_string()]),
            )
            .unwrap(),
            json!({})
        );
        assert!(node.mempool.read().get(&txid).is_some());

        let missing_error = dispatch_method(
            &node,
            "importmempool",
            &json!([directory.path().join("missing.dat").to_string_lossy()]),
        )
        .unwrap_err();
        assert!(
            missing_error
                .to_string()
                .contains("Unable to import mempool file")
        );
    }

    #[test]
    fn mempool_full_rbf_requires_replacement_fees() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let hashes = generate_to_descriptor(&node, &json!([101, "raw(51)"])).unwrap();
        let funding_hash: BlockHash = hashes[0].as_str().unwrap().parse().unwrap();
        let funding = node.chain.write().block(&funding_hash).unwrap().unwrap();
        let outpoint = OutPoint::new(funding.txdata[0].compute_txid(), 0);
        let mut mempool_events = node.subscribe_mempool();
        let old = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: outpoint,
                script_sig: ScriptBuf::from_bytes(vec![0x00; 8]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(4_999_999_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let old_txid = node.accept_transaction(old).unwrap();
        assert_eq!(mempool_events.try_recv().unwrap(), old_txid);
        assert!(!node.mempool.read().is_replaceable(&old_txid));
        let replacement = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: outpoint,
                script_sig: ScriptBuf::from_bytes(vec![0x00; 8]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(4_999_998_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let dry_run = dispatch_method(
            &node,
            "testmempoolaccept",
            &json!([[hex::encode(serialize(&replacement))]]),
        )
        .unwrap();
        assert_eq!(dry_run[0]["allowed"], false);
        assert_eq!(dry_run[0]["reject-reason"], "bip125-replacement-disallowed");
        assert!(node.mempool.read().get(&old_txid).is_some());
        let replacement_txid = replacement.compute_txid();
        let package_result =
            submit_package(&node, &json!([[hex::encode(serialize(&replacement))]])).unwrap();
        assert_eq!(package_result["package_msg"], "success");
        assert_eq!(
            package_result["replaced-transactions"],
            json!([old_txid.to_string()])
        );
        assert_eq!(mempool_events.try_recv().unwrap(), old_txid);
        assert_eq!(mempool_events.try_recv().unwrap(), replacement_txid);
        let mempool = node.mempool.read();
        assert!(mempool.get(&old_txid).is_none());
        assert!(mempool.get(&replacement_txid).is_some());
        drop(mempool);

        let package_parent = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: outpoint,
                script_sig: ScriptBuf::from_bytes(vec![0x00; 8]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(4_999_999_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let package_child = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(package_parent.compute_txid(), 0),
                script_sig: ScriptBuf::from_bytes(vec![0x00; 8]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(4_999_995_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let package_parent_txid = package_parent.compute_txid();
        let package_child_txid = package_child.compute_txid();
        let package_result = submit_package(
            &node,
            &json!([[
                hex::encode(serialize(&package_parent)),
                hex::encode(serialize(&package_child)),
            ]]),
        )
        .unwrap();
        assert_eq!(package_result["package_msg"], "success");
        assert_eq!(
            package_result["replaced-transactions"],
            json!([replacement_txid.to_string()])
        );
        assert!(node.mempool.read().get(&package_parent_txid).is_some());
        assert!(node.mempool.read().get(&package_child_txid).is_some());
    }

    #[test]
    fn submit_package_requires_topologically_sorted_parent_and_child() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let mined = generate_to_descriptor(&node, &json!([102, "raw(51)"])).unwrap();
        let funding_hash: BlockHash = mined[0].as_str().unwrap().parse().unwrap();
        let funding = node.chain.write().block(&funding_hash).unwrap().unwrap();
        let funding_outpoint = OutPoint::new(funding.txdata[0].compute_txid(), 0);
        let parent = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: funding_outpoint,
                script_sig: ScriptBuf::from_bytes(vec![0x00; 8]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: bitcoin::Amount::from_sat(5_000_000_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let parent_outpoint = OutPoint::new(parent.compute_txid(), 0);
        let child = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: parent_outpoint,
                script_sig: ScriptBuf::from_bytes(vec![0x00; 8]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: bitcoin::Amount::from_sat(4_999_998_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let result = submit_package(
            &node,
            &json!([[
                hex::encode(serialize(&parent)),
                hex::encode(serialize(&child)),
            ]]),
        )
        .unwrap();
        assert_eq!(result["package_msg"], "success");
        assert_eq!(
            result["tx-results"][parent.compute_wtxid().to_string()]["txid"],
            parent.compute_txid().to_string()
        );
        assert_eq!(
            result["tx-results"][child.compute_wtxid().to_string()]["txid"],
            child.compute_txid().to_string()
        );
        let mempool = node.mempool.read();
        assert!(mempool.get(&parent.compute_txid()).is_some());
        assert!(mempool.get(&child.compute_txid()).is_some());
        drop(mempool);
        let template = get_block_template(&node, &json!([{"rules": ["segwit"]}])).unwrap();
        let template_transactions = template["transactions"].as_array().unwrap();
        let parent_position = template_transactions
            .iter()
            .position(|entry| entry["txid"] == parent.compute_txid().to_string())
            .expect("package parent is in the template");
        let child_position = template_transactions
            .iter()
            .position(|entry| entry["txid"] == child.compute_txid().to_string())
            .expect("package child is in the template");
        assert!(parent_position < child_position);

        let partial_mined = generate_to_descriptor(&node, &json!([1, "raw(51)"])).unwrap();
        let partial_hash: BlockHash = partial_mined[0].as_str().unwrap().parse().unwrap();
        let partial_block = node.chain.write().block(&partial_hash).unwrap().unwrap();
        let partial_source = partial_block
            .txdata
            .iter()
            .find(|transaction| transaction.compute_txid() == child.compute_txid())
            .expect("earlier package child was mined");
        let partial_outpoint = OutPoint::new(partial_source.compute_txid(), 0);
        let partial_source_value = partial_source.output[0].value.to_sat();
        let partial_parent = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: partial_outpoint,
                script_sig: ScriptBuf::from_bytes(vec![0x00; 8]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: bitcoin::Amount::from_sat(partial_source_value - 1_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let partial_child = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(partial_parent.compute_txid(), 0),
                script_sig: ScriptBuf::from_bytes(vec![0x00; 8]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: bitcoin::Amount::from_sat(partial_source_value),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let max_fee_result = submit_package(
            &node,
            &json!([
                [
                    hex::encode(serialize(&partial_parent)),
                    hex::encode(serialize(&partial_child)),
                ],
                0.000001
            ]),
        )
        .unwrap();
        assert_eq!(max_fee_result["package_msg"], "transaction failed");
        assert!(
            max_fee_result["tx-results"][partial_parent.compute_wtxid().to_string()]["error"]
                == "max feerate exceeded"
        );
        assert_eq!(
            max_fee_result["tx-results"][partial_child.compute_wtxid().to_string()]["error"],
            "package-not-validated"
        );
        assert!(
            node.mempool
                .read()
                .get(&partial_parent.compute_txid())
                .is_none()
        );

        let partial_result = submit_package(
            &node,
            &json!([[
                hex::encode(serialize(&partial_parent)),
                hex::encode(serialize(&partial_child)),
            ]]),
        )
        .unwrap();
        assert_eq!(partial_result["package_msg"], "transaction failed");
        assert!(
            partial_result["tx-results"][partial_parent.compute_wtxid().to_string()]
                .get("error")
                .is_none()
        );
        assert_eq!(
            partial_result["tx-results"][partial_child.compute_wtxid().to_string()]["error"],
            "transaction spends more than its inputs"
        );
        let partial_mempool = node.mempool.read();
        assert!(
            partial_mempool
                .get(&partial_parent.compute_txid())
                .is_some()
        );
        assert!(partial_mempool.get(&partial_child.compute_txid()).is_none());
        drop(partial_mempool);
        let existing_parent_result = submit_package(
            &node,
            &json!([[
                hex::encode(serialize(&partial_parent)),
                hex::encode(serialize(&partial_child)),
            ]]),
        )
        .unwrap();
        assert_eq!(existing_parent_result["package_msg"], "transaction failed");
        assert!(
            existing_parent_result["tx-results"][partial_parent.compute_wtxid().to_string()]
                .get("error")
                .is_none()
        );
        assert_eq!(
            existing_parent_result["tx-results"][partial_child.compute_wtxid().to_string()]["error"],
            "transaction spends more than its inputs"
        );
    }

    #[test]
    fn single_oversized_transaction_is_not_rejected_as_a_package() {
        let transaction = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::null(),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::ZERO,
                script_pubkey: ScriptBuf::from_bytes(vec![0u8; 405_000]),
            }],
        };
        assert!(package_weight(std::slice::from_ref(&transaction)) > MAX_PACKAGE_WEIGHT);
        assert_eq!(package_policy_error(&[transaction]), None);
    }

    #[test]
    fn submit_package_preserves_core_rbf_failure_messages() {
        assert_eq!(
            submit_package_failure_message(&MempoolError::ReplacementFeerateDiagram, true),
            "package RBF failed: insufficient feerate: does not improve feerate diagram"
        );
        assert_eq!(
            submit_package_failure_message(&MempoolError::ReplacementUnconfirmedInput, true),
            "package RBF failed: new transaction cannot have mempool ancestors"
        );
        assert_eq!(
            submit_package_failure_message(&MempoolError::ReplacementFeerateDiagram, false),
            "transaction failed"
        );
    }

    #[test]
    fn utxo_snapshot_rpcs_round_trip_the_active_chainstate() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let path = directory.path().join("utxos.snapshot");
        assert!(dump_txoutset(&node, &json!([path.to_string_lossy(), 1])).is_err());
        assert!(dump_txoutset(&node, &json!([path.to_string_lossy()])).is_err());
        let dumped = dump_txoutset(&node, &json!([path.to_string_lossy(), "latest"])).unwrap();
        assert_eq!(dumped["base_height"], 0);
        assert_eq!(dumped["coins_written"], 0);
        assert_eq!(dumped["nchaintx"], 1);
        assert!(
            dumped["txoutset_hash"]
                .as_str()
                .is_some_and(|hash| !hash.is_empty())
        );
        assert_eq!(dumped["path"], path.to_string_lossy().as_ref());
        let error = load_txoutset(&node, &json!([path.to_string_lossy()]))
            .unwrap_err()
            .to_string();
        assert!(error.contains("not supported by this network's AssumeUTXO commitments"));
    }

    #[test]
    fn dumptxoutset_can_dump_an_active_historical_height_without_rollback() {
        let directory = tempfile::tempdir().unwrap();
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
            dnsseed: false,
            force_dns_seed: false,
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        })
        .unwrap();
        generate_to_descriptor(&node, &json!([3, "raw(51)"])).unwrap();
        let live_height = node.chain.read().height();
        let target_hash = node.chain.read().block_hash(1).unwrap();
        let path = directory.path().join("historical-utxos.snapshot");
        let dumped = dump_txoutset(
            &node,
            &json!([
                path.to_string_lossy(),
                "rollback",
                {"rollback": 1}
            ]),
        )
        .unwrap();
        assert_eq!(dumped["base_height"], 1);
        assert_eq!(dumped["base_hash"], target_hash.to_string());
        assert_eq!(dumped["coins_written"], 1);
        assert_eq!(dumped["nchaintx"], 2);
        assert_eq!(node.chain.read().height(), live_height);
        assert!(path.exists());
        let error = load_txoutset(&node, &json!([path.to_string_lossy()]))
            .unwrap_err()
            .to_string();
        assert!(error.contains("not supported by this network's AssumeUTXO commitments"));
        assert_eq!(node.chain.read().height(), live_height);

        let named_path = directory.path().join("historical-utxos-named.snapshot");
        let named = normalize_rpc_params(
            "dumptxoutset",
            &json!({
                "path": named_path.to_string_lossy(),
                "rollback": target_hash.to_string(),
            }),
        )
        .unwrap();
        let named_dump = dump_txoutset(&node, &named).unwrap();
        assert_eq!(named_dump["base_height"], 1);
        assert_eq!(named_dump["base_hash"], target_hash.to_string());
        assert_eq!(node.chain.read().height(), live_height);
    }

    #[test]
    fn scanblocks_and_descriptor_activity_find_mined_outputs() {
        let directory = tempfile::tempdir().unwrap();
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
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            cjdns_reachable: false,
            onlynet: Vec::new(),
            proxy: None,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
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
        .unwrap();
        let address = "bcrt1q2nfxmhd4n3c8834pj72xagvyr9gl57n5r94fsl";
        assert_eq!(scan_blocks(&node, &json!(["status"])).unwrap(), Value::Null);
        assert_eq!(
            scan_blocks(&node, &json!(["abort"])).unwrap(),
            Value::Bool(false)
        );
        let hash = generate_to_descriptor(&node, &json!([1, format!("addr({address})")])).unwrap()
            [0]
        .as_str()
        .unwrap()
        .to_owned();
        let descriptor = format!("addr({address})");
        assert!(
            scan_blocks(
                &node,
                &json!(["start", [descriptor.clone()], -1, 1, "basic"])
            )
            .is_err()
        );
        assert!(
            scan_blocks(
                &node,
                &json!(["start", [descriptor.clone()], "0", 1, "basic"])
            )
            .is_err()
        );
        let unknown_filter_type = scan_blocks(
            &node,
            &json!(["start", [descriptor.clone()], 0, 1, "extended"]),
        )
        .unwrap_err();
        assert_eq!(unknown_filter_type.to_string(), "Unknown filtertype");
        assert_eq!(rpc_error(&unknown_filter_type)["code"], json!(-5));
        assert!(
            scan_blocks(
                &node,
                &json!(["start", [descriptor.clone()], 0, 1, "basic", 1])
            )
            .is_err()
        );
        let scan = scan_blocks(
            &node,
            &json!(["start", [descriptor.clone()], 0, 1, "basic"]),
        )
        .unwrap();
        assert_eq!(scan["relevant_blocks"][0], hash);
        let exact_scan = scan_blocks(
            &node,
            &json!([
                "start",
                [descriptor.clone()],
                0,
                1,
                "basic",
                {"filter_false_positives": true}
            ]),
        )
        .unwrap();
        assert_eq!(exact_scan["relevant_blocks"][0], hash);
        let activity =
            get_descriptor_activity(&node, &json!([[hash], [descriptor], false])).unwrap();
        assert_eq!(activity["activity"][0]["type"], "receive");
        let duplicate_activity = get_descriptor_activity(
            &node,
            &json!([[hash, hash], [format!("addr({address})")], false]),
        )
        .unwrap();
        assert_eq!(duplicate_activity["activity"].as_array().unwrap().len(), 1);
        assert_eq!(
            get_chain_states(&node).unwrap()["chainstates"][0]["blocks"],
            1
        );
        let chainstate = &get_chain_states(&node).unwrap()["chainstates"][0];
        assert_eq!(chainstate["validated"], true);
        assert!(chainstate.get("snapshot_blockhash").is_none());
    }
}
