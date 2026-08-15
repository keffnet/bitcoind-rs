//! Bitcoin peer networking and block/transaction relay.

use std::collections::{HashMap, HashSet, VecDeque};
use std::net::SocketAddr;
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};
use std::time::{Duration, Instant};

use anyhow::{Context, Result, bail};
use bip324::io::Payload;
use bip324::{
    GarbageResult, Handshake, InboundCipher, NUM_LENGTH_BYTES, OutboundCipher, PacketType, Role,
    VersionResult,
};
use bitcoin::bip152::{BlockTransactions, BlockTransactionsRequest, HeaderAndShortIds, ShortId};
use bitcoin::bip158::FilterHash;
use bitcoin::block::Header as BlockHeader;
use bitcoin::blockdata::script::Instruction;
use bitcoin::consensus::encode::serialize;
use bitcoin::hashes::Hash;
use bitcoin::p2p::message_bloom::{BloomFlags, FilterAdd, FilterLoad};
use bitcoin::p2p::message_filter::{CFCheckpt, CFHeaders, CFilter};
use bitcoin::pow::{CompactTarget, Target, Work};
use bitcoin::{Block, BlockHash, MerkleBlock, Network, Transaction, Txid, Witness, Wtxid};
use rand::random;
use rand::seq::SliceRandom;
use sha2::{Digest, Sha256};
use socket2::SockRef;
use tokio::io::{AsyncReadExt, AsyncWriteExt, BufReader};
use tokio::net::{
    TcpListener, TcpStream,
    tcp::{OwnedReadHalf, OwnedWriteHalf},
};
use tokio::sync::{Mutex, Semaphore, mpsc};
use tokio::task::JoinSet;
use tracing::{debug, info, warn};

use crate::address::{NetworkEndpoint, is_core_routable_ip};
use crate::chain::BasicFilterRange;
#[cfg(test)]
use crate::config::DEFAULT_CONNECT_TIMEOUT_MS;
use crate::config::{PeerPermissions, default_p2p_port};
use crate::mempool::MempoolError;
use crate::wire::{
    self, GetHeadersMessage, Inventory, InventoryType, Message, SendTxRcnclMessage, VersionMessage,
};
use crate::{
    MAX_BLOCKS_IN_TRANSIT_PER_PEER, Node, PRIVATE_BROADCAST_RETRY_SECS, PeerRegistrationOptions,
    StartupLatch, unix_time_seconds,
};

enum PeerReader {
    V1(OwnedReadHalf),
    V2(Box<V2Reader>),
}

enum PeerWriterKind {
    V1(OwnedWriteHalf),
    V2(V2Writer),
}

type PeerWriter = Arc<Mutex<PeerWriterKind>>;

const BIP324_ELLIGATOR_SWIFT_BYTES: usize = 64;
const BIP324_GARBAGE_TERMINATOR_BYTES: usize = 16;
const BIP324_MAX_PACKET_SIZE_FOR_ALLOCATION: usize = 4_000_014;

struct V2BufferedReader {
    reader: BufReader<OwnedReadHalf>,
    leftover: Vec<u8>,
    leftover_offset: usize,
}

impl V2BufferedReader {
    fn new(reader: BufReader<OwnedReadHalf>, leftover: Vec<u8>) -> Self {
        Self {
            reader,
            leftover,
            leftover_offset: 0,
        }
    }

    async fn read_some(&mut self, buffer: &mut [u8]) -> std::io::Result<usize> {
        let available = self.leftover.len().saturating_sub(self.leftover_offset);
        if available != 0 {
            let count = available.min(buffer.len());
            buffer[..count].copy_from_slice(
                &self.leftover[self.leftover_offset..self.leftover_offset + count],
            );
            self.leftover_offset += count;
            return Ok(count);
        }
        self.reader.read(buffer).await
    }

    async fn read_exact(&mut self, buffer: &mut [u8]) -> std::io::Result<()> {
        let mut offset = 0;
        while offset < buffer.len() {
            let count = self.read_some(&mut buffer[offset..]).await?;
            if count == 0 {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::UnexpectedEof,
                    "peer closed during BIP324 transport handshake",
                ));
            }
            offset += count;
        }
        Ok(())
    }
}

struct V2Reader {
    cipher: InboundCipher,
    reader: V2BufferedReader,
    length_bytes: [u8; NUM_LENGTH_BYTES],
    length_read: usize,
    packet_bytes: Vec<u8>,
    packet_read: usize,
}

struct V2Payload {
    packet_type: PacketType,
    contents: Vec<u8>,
}

impl V2Payload {
    fn packet_type(&self) -> PacketType {
        self.packet_type
    }

    fn contents(&self) -> &[u8] {
        &self.contents
    }
}

impl V2Reader {
    fn new(cipher: InboundCipher, reader: V2BufferedReader) -> Self {
        Self {
            cipher,
            reader,
            length_bytes: [0; NUM_LENGTH_BYTES],
            length_read: 0,
            packet_bytes: Vec::new(),
            packet_read: 0,
        }
    }

    async fn read(&mut self) -> Result<V2Payload> {
        while self.length_read < NUM_LENGTH_BYTES {
            let count = self
                .reader
                .read_some(&mut self.length_bytes[self.length_read..])
                .await?;
            if count == 0 {
                bail!("peer closed the BIP324 transport");
            }
            self.length_read += count;
        }

        let packet_len = self.cipher.decrypt_packet_len(self.length_bytes);
        if packet_len > BIP324_MAX_PACKET_SIZE_FOR_ALLOCATION {
            bail!("BIP324 packet exceeds the allocation limit");
        }
        self.packet_bytes.resize(packet_len, 0);
        while self.packet_read < packet_len {
            let count = self
                .reader
                .read_some(&mut self.packet_bytes[self.packet_read..])
                .await?;
            if count == 0 {
                bail!("peer closed the BIP324 transport");
            }
            self.packet_read += count;
        }

        let packet_bytes = std::mem::take(&mut self.packet_bytes);
        self.packet_read = 0;
        self.length_read = 0;
        let mut plaintext = vec![0; InboundCipher::decryption_buffer_len(packet_len)];
        let packet_type = self
            .cipher
            .decrypt(&packet_bytes, &mut plaintext, None)
            .map_err(|error| anyhow::anyhow!(error.to_string()))?;
        Ok(V2Payload {
            packet_type,
            contents: plaintext[1..].to_vec(),
        })
    }
}

struct V2Writer {
    cipher: OutboundCipher,
    writer: OwnedWriteHalf,
}

impl V2Writer {
    async fn write(&mut self, payload: &Payload) -> Result<()> {
        let packet_len = OutboundCipher::encryption_buffer_len(payload.contents().len());
        let mut packet = vec![0; packet_len];
        self.cipher
            .encrypt(payload.contents(), &mut packet, payload.packet_type(), None)
            .map_err(|error| anyhow::anyhow!(error.to_string()))?;
        self.writer.write_all(&packet).await?;
        self.writer.flush().await?;
        Ok(())
    }
}

const MAX_BLOOM_FILTER_SIZE: usize = 36_000;
const MAX_BLOOM_HASH_FUNCS: u32 = 50;
const MAX_BLOOM_ELEMENT_SIZE: usize = 520;
const MAX_ADDR_TO_SEND: usize = 1_000;
const MAX_CMPCTBLOCK_DEPTH: u32 = 5;
const MAX_BLOCKTXN_DEPTH: u32 = 10;
const STALE_RELAY_AGE_LIMIT_SECS: u64 = 30 * 24 * 60 * 60;
const SENDHEADERS_VERSION: i32 = 70_012;
const FEEFILTER_VERSION: i32 = 70_013;
const SHORT_IDS_BLOCKS_VERSION: i32 = 70_014;
const WTXID_RELAY_VERSION: i32 = 70_016;
const TX_RECONCILIATION_VERSION: u32 = 1;
const KNOWN_TX_FILTER_BITS: usize = 1 << 20;
const KNOWN_TX_FILTER_HASHES: u32 = 4;
const KNOWN_TX_FILTER_GENERATION: usize = 25_000;
const ADDR_FETCH_TIMEOUT_SECS: u64 = 10 * 30;
const HEADERS_RESPONSE_TIME: Duration = Duration::from_secs(2 * 60);
const HEADERS_DOWNLOAD_TIMEOUT: Duration = Duration::from_secs(15 * 60);
const MAX_FUTURE_BLOCK_TIME_SECS: u64 = 2 * 60 * 60;
const MAX_TX_INVENTORY_BATCH: usize = 50_000;
const MAX_PEER_TX_ANNOUNCEMENTS: usize = 5_000;
const MAX_PEER_TX_REQUEST_IN_FLIGHT: usize = 100;
const TXID_RELAY_DELAY: Duration = Duration::from_secs(2);
const NONPREF_PEER_TX_DELAY: Duration = Duration::from_secs(2);
const OVERLOADED_PEER_TX_DELAY: Duration = Duration::from_secs(2);
const GETDATA_TX_INTERVAL: Duration = Duration::from_secs(60);
const MAX_GETDATA_BATCH: usize = 1_000;
const MAX_BLOCKS_TO_ANNOUNCE: usize = 8;
const DNS_SEED_OUTBOUND_THRESHOLD: usize = 2;
const DNS_SEED_FALLBACK_DELAY: Duration = Duration::from_secs(11);
const FIXED_SEED_FALLBACK_DELAY: Duration = Duration::from_secs(60);
/// Core keeps manually added connections in a separate, bounded pool rather
/// than consuming automatic `-maxconnections` slots.
const MAX_ADDNODE_CONNECTIONS: usize = 8;
/// Private broadcast connections are short-lived and have their own limit in
/// Core, independent of ordinary peer slots.
const MAX_PRIVATE_BROADCAST_CONNECTIONS: usize = 64;
const INVENTORY_BROADCAST_TARGET: usize = 70;
const INVENTORY_BROADCAST_MAX: usize = 1_000;

fn local_transaction_relay_enabled(
    connection_type: &str,
    blocksonly: bool,
    permissions: PeerPermissions,
) -> bool {
    if matches!(connection_type, "block-relay-only" | "feeler") {
        return false;
    }
    (!blocksonly && matches!(connection_type, "outbound-full" | "inbound" | "addr-fetch"))
        || permissions.contains(PeerPermissions::RELAY)
}

fn connection_requests_headers(connection_type: &str) -> bool {
    !matches!(connection_type, "addr-fetch" | "feeler")
}

fn connection_fetches_addresses(outbound: bool, connection_type: &str) -> bool {
    outbound && connection_type != "block-relay-only" && connection_type != "feeler"
}

fn getdata_batches(requests: &[Inventory]) -> impl Iterator<Item = &[Inventory]> {
    requests.chunks(MAX_GETDATA_BATCH)
}

fn inventory_broadcast_limit(pending: usize) -> usize {
    INVENTORY_BROADCAST_TARGET
        .saturating_add((pending / 1_000).saturating_mul(5))
        .min(INVENTORY_BROADCAST_MAX)
}

fn queue_block_requests(
    pending: &mut Vec<Inventory>,
    requests: impl IntoIterator<Item = Inventory>,
) {
    for request in requests {
        if !matches!(
            request.kind,
            InventoryType::Block | InventoryType::WitnessBlock | InventoryType::CompactBlock
        ) {
            continue;
        }
        if !pending.iter().any(|queued| queued.hash == request.hash) {
            pending.push(request);
        }
    }
}

fn block_request_inventory_type(peer_services: u64) -> InventoryType {
    if peer_services & wire::NODE_WITNESS != 0 {
        InventoryType::WitnessBlock
    } else {
        InventoryType::Block
    }
}

fn addr_fetch_timed_out(connected_at: u64, now: u64) -> bool {
    now.saturating_sub(connected_at) > ADDR_FETCH_TIMEOUT_SECS
}

fn headers_request_is_due(last_request: Option<Instant>) -> bool {
    last_request.is_none_or(|sent| sent.elapsed() >= HEADERS_RESPONSE_TIME)
}

fn headers_download_timed_out(last_request: Option<Instant>) -> bool {
    last_request.is_some_and(|sent| sent.elapsed() > HEADERS_DOWNLOAD_TIMEOUT)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LowWorkHeadersPhase {
    Presync,
    Redownload,
}

#[derive(Debug)]
struct HeadersSyncResult {
    success: bool,
    request_more: bool,
    ready: Vec<BlockHeader>,
    finished: bool,
}

#[derive(Debug, Default)]
struct CommitmentBits {
    words: VecDeque<u64>,
    front_offset: u8,
    len: usize,
}

impl CommitmentBits {
    fn push_back(&mut self, bit: bool) {
        let position = usize::from(self.front_offset) + self.len;
        let word = position / 64;
        if word == self.words.len() {
            self.words.push_back(0);
        }
        if bit {
            *self.words.get_mut(word).expect("commitment word exists") |= 1 << (position % 64);
        }
        self.len += 1;
    }

    fn pop_front(&mut self) -> Option<bool> {
        if self.len == 0 {
            return None;
        }
        let bit = (self.words.front().copied().unwrap_or_default() & (1 << self.front_offset)) != 0;
        self.front_offset += 1;
        self.len -= 1;
        if self.front_offset == 64 {
            self.words.pop_front();
            self.front_offset = 0;
        }
        if self.len == 0 {
            self.words.clear();
            self.front_offset = 0;
        }
        Some(bit)
    }

    fn len(&self) -> usize {
        self.len
    }

    #[cfg(test)]
    fn front(&self) -> Option<bool> {
        (self.len != 0).then(|| {
            (self.words.front().copied().unwrap_or_default() & (1 << self.front_offset)) != 0
        })
    }
}

/// Per-peer implementation of Core's low-work headers synchronization.
///
/// Headers in the presync phase are deliberately kept out of ChainState. A
/// peer must first demonstrate sufficient cumulative work, then provide the
/// same chain again while the salted commitments are checked. Only headers
/// released from the bounded redownload buffer reach the global index.
struct LowWorkHeadersSync {
    network: Network,
    minimum_work: Work,
    commitment_period: u32,
    redownload_buffer_size: usize,
    commit_offset: u32,
    salt: [u8; 32],
    commitments: CommitmentBits,
    max_commitments: u64,
    phase: LowWorkHeadersPhase,
    chain_start_hash: BlockHash,
    chain_start_height: u32,
    chain_start_work: Work,
    last_header: BlockHeader,
    current_height: u32,
    current_work: Work,
    redownload_headers: VecDeque<BlockHeader>,
    redownload_last_hash: BlockHash,
    redownload_last_bits: CompactTarget,
    redownload_height: u32,
    redownload_work: Work,
    process_all_remaining_headers: bool,
}

impl LowWorkHeadersSync {
    fn params(network: Network) -> (u32, usize) {
        match network {
            Network::Bitcoin => (641, 15_218),
            Network::Testnet => (673, 14_460),
            Network::Testnet4 => (606, 16_092),
            Network::Signet => (620, 15_724),
            Network::Regtest => (275, 7_017),
        }
    }

    fn new(
        network: Network,
        minimum_work: Work,
        chain_start_hash: BlockHash,
        chain_start_height: u32,
        chain_start_work: Work,
        chain_start_header: BlockHeader,
        chain_start_median_time_past: u32,
    ) -> Self {
        let (commitment_period, redownload_buffer_size) = Self::params(network);
        let now = unix_time_seconds();
        let elapsed = now
            .saturating_sub(u64::from(chain_start_median_time_past))
            .saturating_add(MAX_FUTURE_BLOCK_TIME_SECS);
        let max_commitments = elapsed
            .saturating_mul(6)
            .checked_div(u64::from(commitment_period))
            .unwrap_or(0);
        let commit_offset = (random::<u64>() % u64::from(commitment_period)) as u32;
        Self {
            network,
            minimum_work,
            commitment_period,
            redownload_buffer_size,
            commit_offset,
            salt: random(),
            commitments: CommitmentBits::default(),
            max_commitments,
            phase: LowWorkHeadersPhase::Presync,
            chain_start_hash,
            chain_start_height,
            chain_start_work,
            last_header: chain_start_header,
            current_height: chain_start_height,
            current_work: chain_start_work,
            redownload_headers: VecDeque::new(),
            redownload_last_hash: chain_start_hash,
            redownload_last_bits: chain_start_header.bits,
            redownload_height: chain_start_height,
            redownload_work: chain_start_work,
            process_all_remaining_headers: false,
        }
    }

    fn commitment(&self, header: &BlockHeader) -> bool {
        let mut hasher = Sha256::new();
        hasher.update(self.salt);
        hasher.update(header.block_hash().to_byte_array());
        (hasher.finalize()[0] & 1) != 0
    }

    fn process(
        &mut self,
        headers: &[BlockHeader],
        full_headers_message: bool,
    ) -> HeadersSyncResult {
        if headers.is_empty() {
            return HeadersSyncResult {
                success: false,
                request_more: false,
                ready: Vec::new(),
                finished: true,
            };
        }
        match self.phase {
            LowWorkHeadersPhase::Presync => self.process_presync(headers, full_headers_message),
            LowWorkHeadersPhase::Redownload => {
                self.process_redownload(headers, full_headers_message)
            }
        }
    }

    fn process_presync(
        &mut self,
        headers: &[BlockHeader],
        full_headers_message: bool,
    ) -> HeadersSyncResult {
        let mut previous = self.last_header;
        for header in headers {
            let next_height = self.current_height.saturating_add(1);
            if header.prev_blockhash != previous.block_hash()
                || !permitted_difficulty_transition(
                    self.network,
                    next_height,
                    previous.bits.to_consensus(),
                    header.bits.to_consensus(),
                )
                || !valid_header_pow(self.network, header)
            {
                return self.failed_result();
            }
            if next_height % self.commitment_period == self.commit_offset {
                self.commitments.push_back(self.commitment(header));
                if self.commitments.len() as u64 > self.max_commitments {
                    return self.failed_result();
                }
            }
            self.current_work = add_work_saturating(self.current_work, header.work());
            self.current_height = next_height;
            previous = *header;
        }
        self.last_header = previous;

        if self.current_work >= self.minimum_work {
            self.phase = LowWorkHeadersPhase::Redownload;
            self.redownload_headers.clear();
            self.redownload_last_hash = self.chain_start_hash;
            self.redownload_height = self.chain_start_height;
            self.redownload_work = self.chain_start_work;
            self.process_all_remaining_headers = false;
            HeadersSyncResult {
                success: true,
                // The second phase starts over from the common chain start.
                request_more: true,
                ready: Vec::new(),
                finished: false,
            }
        } else if full_headers_message {
            HeadersSyncResult {
                success: true,
                request_more: true,
                ready: Vec::new(),
                finished: false,
            }
        } else {
            // A short low-work response proves that this peer has no useful
            // chain to continue with, so discard the presync state.
            HeadersSyncResult {
                success: true,
                request_more: false,
                ready: Vec::new(),
                finished: true,
            }
        }
    }

    fn process_redownload(
        &mut self,
        headers: &[BlockHeader],
        full_headers_message: bool,
    ) -> HeadersSyncResult {
        for header in headers {
            let next_height = self.redownload_height.saturating_add(1);
            if header.prev_blockhash != self.redownload_last_hash
                || !permitted_difficulty_transition(
                    self.network,
                    next_height,
                    self.redownload_last_bits.to_consensus(),
                    header.bits.to_consensus(),
                )
                || !valid_header_pow(self.network, header)
            {
                return self.failed_result();
            }

            self.redownload_work = add_work_saturating(self.redownload_work, header.work());
            if self.redownload_work >= self.minimum_work {
                self.process_all_remaining_headers = true;
            }

            if !self.process_all_remaining_headers
                && next_height % self.commitment_period == self.commit_offset
            {
                let Some(expected) = self.commitments.pop_front() else {
                    return self.failed_result();
                };
                if self.commitment(header) != expected {
                    return self.failed_result();
                }
            }

            self.redownload_headers.push_back(*header);
            self.redownload_last_hash = header.block_hash();
            self.redownload_last_bits = header.bits;
            self.redownload_height = next_height;
        }

        let ready = self.pop_ready_headers();
        let finished = self.redownload_headers.is_empty() && self.process_all_remaining_headers;
        let request_more = !finished && full_headers_message;
        HeadersSyncResult {
            success: true,
            request_more,
            ready,
            finished: finished || !full_headers_message,
        }
    }

    fn pop_ready_headers(&mut self) -> Vec<BlockHeader> {
        let mut ready = Vec::new();
        while self.redownload_headers.len() > self.redownload_buffer_size
            || (self.process_all_remaining_headers && !self.redownload_headers.is_empty())
        {
            let header = self
                .redownload_headers
                .pop_front()
                .expect("redownload queue is non-empty");
            ready.push(header);
        }
        ready
    }

    fn failed_result(&self) -> HeadersSyncResult {
        HeadersSyncResult {
            success: false,
            request_more: false,
            ready: Vec::new(),
            finished: true,
        }
    }

    fn next_locator(&self, chain: &crate::chain::ChainState) -> Vec<BlockHash> {
        let last_hash = match self.phase {
            LowWorkHeadersPhase::Presync => self.last_header.block_hash(),
            LowWorkHeadersPhase::Redownload => self.redownload_last_hash,
        };
        let mut locator = vec![last_hash];
        for hash in chain.block_locator_hashes_from(self.chain_start_hash) {
            if !locator.contains(&hash) {
                locator.push(hash);
            }
        }
        locator
    }

    #[cfg(test)]
    fn phase(&self) -> LowWorkHeadersPhase {
        self.phase
    }

    #[cfg(test)]
    fn commitment_count(&self) -> usize {
        self.commitments.len()
    }
}

fn valid_header_pow(network: Network, header: &BlockHeader) -> bool {
    let compact = header.bits.to_consensus();
    let target = header.target();
    let mantissa = compact & 0x007f_ffff;
    mantissa != 0
        && compact & 0x0080_0000 == 0
        && target != Target::ZERO
        && target <= network.params().max_attainable_target
        && target.to_compact_lossy().to_consensus() == compact
        && target.is_met_by(header.block_hash())
}

fn add_work_saturating(left: Work, right: Work) -> Work {
    let maximum = Work::from_be_bytes([0xff; 32]);
    if left > maximum - right {
        maximum
    } else {
        left + right
    }
}

fn permitted_difficulty_transition(
    network: Network,
    height: u32,
    old_bits: u32,
    new_bits: u32,
) -> bool {
    let params = network.params();
    if params.allow_min_difficulty_blocks {
        return true;
    }
    let interval = params.difficulty_adjustment_interval() as u32;
    if height % interval != 0 {
        return old_bits == new_bits;
    }
    let old_target = Target::from_compact(CompactTarget::from_consensus(old_bits));
    let new_target = Target::from_compact(CompactTarget::from_consensus(new_bits));
    let maximum = Target::from_compact(
        old_target
            .max_transition_threshold(params)
            .to_compact_lossy(),
    );
    let minimum = Target::from_compact(old_target.min_transition_threshold().to_compact_lossy());
    new_target >= minimum && new_target <= maximum
}

fn headers_sync_work_threshold(chain: &crate::chain::ChainState) -> Work {
    let minimum = chain.minimum_chain_work();
    let tip = chain.tip();
    let tip_header = chain
        .header(tip.height)
        .expect("active tip header is always indexed");
    let mut recent_work = Work::from_be_bytes([0; 32]);
    for _ in 0..144 {
        recent_work = add_work_saturating(recent_work, tip_header.work());
    }
    let recent_work = recent_work.min(tip.work);
    let near_tip = tip.work - recent_work;
    near_tip.max(minimum)
}

struct PeerState {
    endpoint: NetworkEndpoint,
    local_address: Option<SocketAddr>,
    writer: PeerWriter,
    connection_type: &'static str,
    permissions: PeerPermissions,
    private_broadcast_transaction: Option<Transaction>,
    private_broadcast_peer: parking_lot::Mutex<bool>,
    local_relay_transactions: bool,
    bloom_filter: parking_lot::Mutex<Option<BloomFilter>>,
    known_tx_inventory: parking_lot::Mutex<KnownTxInventory>,
    pending_tx_inventory: parking_lot::Mutex<Vec<Inventory>>,
    tx_requests: parking_lot::Mutex<TxRequestState>,
    fee_filter: parking_lot::Mutex<i64>,
    relay_transactions: parking_lot::Mutex<bool>,
    wtxid_relay: parking_lot::Mutex<bool>,
    send_headers: parking_lot::Mutex<bool>,
    last_headers_request: parking_lot::Mutex<Option<Instant>>,
    compact_block_version: parking_lot::Mutex<Option<u64>>,
    compact_block_announce: parking_lot::Mutex<bool>,
    tx_reconciliation_salt: parking_lot::Mutex<Option<u64>>,
    tx_reconciliation_registered: parking_lot::Mutex<bool>,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct TxRequestKey {
    witness: bool,
    hash: BlockHash,
}

impl TxRequestKey {
    fn from_inventory(item: &Inventory) -> Option<Self> {
        item.kind.is_transaction().then_some(Self {
            witness: item.kind.is_witness_transaction(),
            hash: item.hash,
        })
    }
}

struct PendingTxRequest {
    key: TxRequestKey,
    item: Inventory,
    ready_at: Instant,
}

/// The transaction-request half of Core's TxRequestTracker. Announcements are
/// kept separate from requests already sent so a peer cannot force an
/// unbounded getdata queue, and the in-flight map allows stale requests to be
/// retried after the Core timeout.
#[derive(Default)]
struct TxRequestState {
    pending: VecDeque<PendingTxRequest>,
    pending_keys: HashSet<TxRequestKey>,
    in_flight: HashMap<TxRequestKey, Instant>,
}

impl TxRequestState {
    fn queue(&mut self, item: Inventory, ready_at: Instant) -> bool {
        let Some(key) = TxRequestKey::from_inventory(&item) else {
            return false;
        };
        if self.pending_keys.contains(&key) || self.in_flight.contains_key(&key) {
            return false;
        }
        if self.pending.len().saturating_add(self.in_flight.len()) >= MAX_PEER_TX_ANNOUNCEMENTS {
            return false;
        }
        self.pending.push_back(PendingTxRequest {
            key,
            item,
            ready_at,
        });
        self.pending_keys.insert(key);
        true
    }

    fn expire(&mut self, now: Instant) {
        self.in_flight
            .retain(|_, requested_at| now.duration_since(*requested_at) < GETDATA_TX_INTERVAL);
    }

    fn in_flight_count(&self) -> usize {
        self.in_flight.len()
    }

    fn has_live_in_flight(&self, key: TxRequestKey, now: Instant) -> bool {
        self.in_flight
            .get(&key)
            .is_some_and(|requested_at| now.duration_since(*requested_at) < GETDATA_TX_INTERVAL)
    }

    fn take_ready(&mut self, now: Instant, limit: usize) -> Vec<PendingTxRequest> {
        self.expire(now);
        let mut ready = Vec::with_capacity(limit);
        let pending_count = self.pending.len();
        for _ in 0..pending_count {
            let Some(request) = self.pending.pop_front() else {
                break;
            };
            if request.ready_at <= now && ready.len() < limit {
                self.pending_keys.remove(&request.key);
                ready.push(request);
            } else {
                self.pending.push_back(request);
            }
        }
        ready
    }

    fn mark_sent(&mut self, request: &PendingTxRequest, now: Instant) {
        self.in_flight.insert(request.key, now);
    }

    fn requeue(&mut self, request: PendingTxRequest, ready_at: Instant) {
        if self.pending_keys.contains(&request.key) || self.in_flight.contains_key(&request.key) {
            return;
        }
        self.pending.push_back(PendingTxRequest {
            key: request.key,
            item: request.item,
            ready_at,
        });
        self.pending_keys.insert(request.key);
    }

    fn remove(&mut self, key: TxRequestKey) {
        self.pending.retain(|request| request.key != key);
        self.pending_keys.remove(&key);
        self.in_flight.remove(&key);
    }

    fn remove_transaction(&mut self, transaction: &Transaction) {
        self.remove(TxRequestKey {
            witness: false,
            hash: BlockHash::from_raw_hash(transaction.compute_txid().to_raw_hash()),
        });
        self.remove(TxRequestKey {
            witness: true,
            hash: BlockHash::from_raw_hash(transaction.compute_wtxid().to_raw_hash()),
        });
    }

    fn remove_inventory(&mut self, item: &Inventory) {
        if let Some(key) = TxRequestKey::from_inventory(item) {
            self.remove(key);
        }
    }
}

/// A bounded rolling filter of transaction inventory already known by a peer.
/// Core uses the same two-generation shape to avoid repeatedly announcing the
/// same transaction while keeping per-peer memory bounded.
struct KnownTxInventory {
    generations: [Vec<u8>; 2],
    active_generation: usize,
    inserted_in_generation: usize,
}

impl KnownTxInventory {
    fn new() -> Self {
        let bytes = KNOWN_TX_FILTER_BITS / 8;
        Self {
            generations: [vec![0; bytes], vec![0; bytes]],
            active_generation: 0,
            inserted_in_generation: 0,
        }
    }

    fn contains(&self, hash: &BlockHash) -> bool {
        self.generations
            .iter()
            .any(|generation| self.generation_contains(generation, hash))
    }

    fn insert(&mut self, hash: &BlockHash) {
        if self.contains(hash) {
            return;
        }
        if self.inserted_in_generation >= KNOWN_TX_FILTER_GENERATION {
            self.active_generation ^= 1;
            self.generations[self.active_generation].fill(0);
            self.inserted_in_generation = 0;
        }
        let generation = &mut self.generations[self.active_generation];
        let bytes = hash.to_byte_array();
        for index in 0..KNOWN_TX_FILTER_HASHES {
            let bit = (murmur_hash3(index.wrapping_mul(0xfba4_c795), &bytes) as usize)
                & (KNOWN_TX_FILTER_BITS - 1);
            generation[bit / 8] |= 1 << (bit % 8);
        }
        self.inserted_in_generation += 1;
    }

    fn generation_contains(&self, generation: &[u8], hash: &BlockHash) -> bool {
        let bytes = hash.to_byte_array();
        (0..KNOWN_TX_FILTER_HASHES).all(|index| {
            let bit = (murmur_hash3(index.wrapping_mul(0xfba4_c795), &bytes) as usize)
                & (KNOWN_TX_FILTER_BITS - 1);
            generation[bit / 8] & (1 << (bit % 8)) != 0
        })
    }
}

type PeerRegistry = Arc<parking_lot::Mutex<HashMap<usize, Arc<PeerState>>>>;
type OutboundAttempts = Arc<parking_lot::Mutex<HashSet<NetworkEndpoint>>>;

#[derive(Clone)]
struct OutboundContext {
    slots: Arc<Semaphore>,
    manual_slots: Arc<Semaphore>,
    private_slots: Arc<Semaphore>,
    peers: PeerRegistry,
    next_peer_id: Arc<AtomicUsize>,
    attempts: OutboundAttempts,
}

#[derive(Clone, Debug)]
struct BloomFilter {
    data: Vec<u8>,
    hash_funcs: u32,
    tweak: u32,
    flags: BloomFlags,
}

impl BloomFilter {
    fn from_message(message: FilterLoad) -> Result<Self> {
        if message.filter.len() > MAX_BLOOM_FILTER_SIZE {
            anyhow::bail!("bloom filter exceeds the 36000-byte limit");
        }
        if message.hash_funcs > MAX_BLOOM_HASH_FUNCS {
            anyhow::bail!("bloom filter has too many hash functions");
        }
        Ok(Self {
            data: message.filter,
            hash_funcs: message.hash_funcs,
            tweak: message.tweak,
            flags: message.flags,
        })
    }

    fn insert(&mut self, value: &[u8]) {
        if self.data.is_empty() {
            return;
        }
        let bit_count = self.data.len().saturating_mul(8);
        for index in 0..self.hash_funcs {
            let seed = index.wrapping_mul(0xfba4_c795).wrapping_add(self.tweak);
            let bit = (murmur_hash3(seed, value) as usize) % bit_count;
            self.data[bit / 8] |= 1 << (bit % 8);
        }
    }

    fn contains(&self, value: &[u8]) -> bool {
        if self.data.is_empty() {
            return true;
        }
        let bit_count = self.data.len().saturating_mul(8);
        (0..self.hash_funcs).all(|index| {
            let seed = index.wrapping_mul(0xfba4_c795).wrapping_add(self.tweak);
            let bit = (murmur_hash3(seed, value) as usize) % bit_count;
            self.data[bit / 8] & (1 << (bit % 8)) != 0
        })
    }

    fn contains_script_data(&self, script: &bitcoin::Script) -> bool {
        for instruction in script.instructions() {
            match instruction {
                Ok(Instruction::PushBytes(data))
                    if !data.is_empty() && self.contains(data.as_bytes()) =>
                {
                    return true;
                }
                Ok(_) => {}
                Err(_) => break,
            }
        }
        false
    }

    fn is_relevant_and_update(&mut self, transaction: &Transaction) -> bool {
        if self.data.is_empty() {
            return true;
        }
        let txid = transaction.compute_txid();
        let mut matched = self.contains(&serialize(&txid));
        for (index, output) in transaction.output.iter().enumerate() {
            if !self.contains_script_data(&output.script_pubkey) {
                continue;
            }
            matched = true;
            let should_update = match self.flags {
                BloomFlags::All => true,
                BloomFlags::PubkeyOnly => {
                    output.script_pubkey.is_p2pk() || output.script_pubkey.is_multisig()
                }
                BloomFlags::None => false,
            };
            if should_update {
                let outpoint = bitcoin::OutPoint::new(txid, index as u32);
                self.insert(&serialize(&outpoint));
            }
        }
        if matched {
            return true;
        }
        for input in &transaction.input {
            if self.contains(&serialize(&input.previous_output))
                || self.contains_script_data(&input.script_sig)
            {
                return true;
            }
        }
        false
    }

    fn matched_transaction_ids(&mut self, block: &Block) -> Vec<Txid> {
        block
            .txdata
            .iter()
            .filter_map(|transaction| {
                self.is_relevant_and_update(transaction)
                    .then_some(transaction.compute_txid())
            })
            .collect()
    }
}

fn murmur_hash3(seed: u32, data: &[u8]) -> u32 {
    let mut hash = seed;
    const C1: u32 = 0xcc9e_2d51;
    const C2: u32 = 0x1b87_3593;
    for chunk in data.chunks_exact(4) {
        let mut value = u32::from_le_bytes(chunk.try_into().expect("four-byte chunk"));
        value = value.wrapping_mul(C1).rotate_left(15).wrapping_mul(C2);
        hash ^= value;
        hash = hash
            .rotate_left(13)
            .wrapping_mul(5)
            .wrapping_add(0xe654_6b64);
    }
    let tail = data.chunks_exact(4).remainder();
    let mut value = 0u32;
    for (index, byte) in tail.iter().enumerate() {
        value |= u32::from(*byte) << (index * 8);
    }
    if !tail.is_empty() {
        hash ^= value.wrapping_mul(C1).rotate_left(15).wrapping_mul(C2);
    }
    hash ^= data.len() as u32;
    hash ^= hash >> 16;
    hash = hash.wrapping_mul(0x85eb_ca6b);
    hash ^= hash >> 13;
    hash = hash.wrapping_mul(0xc2b2_ae35);
    hash ^ (hash >> 16)
}

impl PeerReader {
    async fn read_message(&mut self, network: Network) -> Result<(Message, usize)> {
        match self {
            Self::V1(reader) => wire::read_message_with_size(reader, network).await,
            Self::V2(reader) => loop {
                let payload = reader.read().await?;
                if payload.packet_type() == PacketType::Decoy {
                    continue;
                }
                let contents = payload.contents();
                let bytes = contents.len().saturating_add(20);
                let message = wire::decode_v2_message(contents)?;
                break Ok((message, bytes));
            },
        }
    }
}

#[derive(Debug)]
pub(crate) enum PeerCommand {
    Disconnect,
    RequestBlock(BlockHash),
    Ping(u64),
    SendMessage {
        command: String,
        payload: Vec<u8>,
    },
    RelayAddresses {
        addresses: Vec<(NetworkEndpoint, u64, u64)>,
    },
}

#[derive(Debug)]
pub(crate) enum PeerManagerRequest {
    Add(NetworkEndpoint, Option<bool>),
    OneTry(NetworkEndpoint, Option<bool>, &'static str),
    PrivateBroadcast {
        address: SocketAddr,
        transaction: Transaction,
    },
}

struct PendingCompactBlock {
    compact: HeaderAndShortIds,
    transactions: Vec<Option<Transaction>>,
    requested_indexes: Vec<u64>,
}

pub struct PeerManager {
    node: Arc<Node>,
}

impl PeerManager {
    pub fn new(node: Arc<Node>) -> Self {
        Self { node }
    }

    pub async fn run(self) -> Result<()> {
        self.run_with_startup(None).await
    }

    pub(crate) async fn run_with_startup(self, startup: Option<Arc<StartupLatch>>) -> Result<()> {
        let listeners = if self.node.config.listen {
            let binds = if self.node.config.p2p_binds.is_empty() {
                vec![self.node.config.p2p_bind]
            } else {
                self.node.config.p2p_binds.clone()
            };
            let mut listeners = Vec::with_capacity(binds.len());
            for bind in binds {
                let listener = TcpListener::bind(bind)
                    .await
                    .with_context(|| format!("binding P2P listener {bind}"))?;
                let local_address = listener.local_addr()?;
                if self.node.listen_address().is_none() {
                    self.node.set_listen_address(local_address);
                } else {
                    self.node.add_listen_address(local_address);
                }
                listeners.push(listener);
            }
            listeners
        } else {
            Vec::new()
        };
        let tor_target = listeners
            .first()
            .and_then(|listener| listener.local_addr().ok())
            .map(tor_service_target);
        let whitebind_listeners = if self.node.config.listen {
            let mut listeners = Vec::new();
            for whitebind in &self.node.config.peer_permissions.whitebind {
                let listener = TcpListener::bind(whitebind.address)
                    .await
                    .with_context(|| format!("binding whitebind listener {}", whitebind.address))?;
                listeners.push((listener, whitebind.permissions));
            }
            listeners
        } else {
            Vec::new()
        };
        if let Some(startup) = startup.as_deref() {
            startup.service_ready();
        }
        if self.node.config.natpmp
            && let Some(address) = listeners
                .iter()
                .filter_map(|listener| listener.local_addr().ok())
                .find(|address| !address.ip().is_loopback() && address.port() != 0)
        {
            tokio::spawn(crate::portmap::run(self.node.clone(), address.port()));
        }
        let slots = Arc::new(Semaphore::new(self.node.config.max_peers));
        let manual_slots = Arc::new(Semaphore::new(MAX_ADDNODE_CONNECTIONS));
        let private_slots = Arc::new(Semaphore::new(MAX_PRIVATE_BROADCAST_CONNECTIONS));
        let peers: PeerRegistry = Arc::new(parking_lot::Mutex::new(HashMap::new()));
        let next_peer_id = Arc::new(AtomicUsize::new(1));
        let outbound = OutboundContext {
            slots: slots.clone(),
            manual_slots,
            private_slots,
            peers: peers.clone(),
            next_peer_id: next_peer_id.clone(),
            attempts: Arc::new(parking_lot::Mutex::new(HashSet::new())),
        };
        let (add_node_sender, mut add_node_receiver) = mpsc::unbounded_channel();
        self.node.set_peer_manager_sender(add_node_sender);
        let mut chain_events = self.node.subscribe_chain();
        let mut mempool_events = self.node.subscribe_peer_mempool();
        let block_relay_node = self.node.clone();
        let block_relay_peers = peers.clone();
        let block_relay_network = self.node.config.network;
        tokio::spawn(async move {
            let mut last_announced_tip = block_relay_node.chain.read().best_hash();
            loop {
                let tip = match chain_events.recv().await {
                    Ok(tip) => tip,
                    Err(tokio::sync::broadcast::error::RecvError::Lagged(_)) => continue,
                    Err(tokio::sync::broadcast::error::RecvError::Closed) => break,
                };
                if block_relay_node.chain.read().is_initial_block_download() {
                    // Core does not announce blocks while IBD is active. Move
                    // the relay boundary forward so leaving IBD does not
                    // replay every historical tip as a fresh announcement.
                    last_announced_tip = tip.hash;
                    continue;
                }
                let hashes = {
                    let mut chain = block_relay_node.chain.write();
                    let hashes = chain
                        .active_blocks_after(last_announced_tip)
                        .map(|blocks| {
                            blocks
                                .into_iter()
                                .take(MAX_BLOCKS_TO_ANNOUNCE)
                                .map(|block| block.block_hash())
                                .collect::<Vec<_>>()
                        })
                        .unwrap_or_else(|_| vec![tip.hash]);
                    last_announced_tip = tip.hash;
                    hashes
                };
                for hash in hashes {
                    let available = block_relay_node.chain.read().store.contains(&hash);
                    if !available {
                        continue;
                    }
                    broadcast_inventory(
                        &block_relay_node,
                        &block_relay_peers,
                        0,
                        block_relay_network,
                        Inventory {
                            kind: InventoryType::WitnessBlock,
                            hash,
                        },
                    )
                    .await;
                }
            }
        });
        let relay_peers = peers.clone();
        let relay_node = self.node.clone();
        let relay_network = self.node.config.network;
        tokio::spawn(async move {
            loop {
                let event = match mempool_events.recv().await {
                    Ok(event) => event,
                    Err(tokio::sync::broadcast::error::RecvError::Lagged(_)) => continue,
                    Err(tokio::sync::broadcast::error::RecvError::Closed) => break,
                };
                if relay_node.chain.read().is_initial_block_download() {
                    continue;
                }
                let Some(hash) = relay_node
                    .mempool
                    .read()
                    .get(&event.txid)
                    .map(|entry| entry.transaction.compute_wtxid())
                else {
                    // Removal notifications share the public mempool event
                    // stream, but a removed transaction must never be
                    // announced as if it were still relayable.
                    continue;
                };
                broadcast_inventory_excluding(
                    &relay_node,
                    &relay_peers,
                    &event.excluded_peers,
                    relay_network,
                    event.force_relay,
                    Inventory {
                        kind: InventoryType::WitnessTransaction,
                        hash: BlockHash::from_raw_hash(hash.to_raw_hash()),
                    },
                )
                .await;
            }
        });
        let configured_connect_nodes =
            self.node.config.connect_disabled || !self.node.config.seed_nodes.is_empty();
        let has_seed_nodes = !self.node.config.seed_nodes_for_address_fetch.is_empty();
        let has_add_nodes = !self.node.config.add_nodes.is_empty();
        if !configured_connect_nodes {
            for endpoint in self
                .node
                .config
                .seed_nodes_for_address_fetch
                .iter()
                .cloned()
            {
                spawn_outbound_loop(
                    self.node.clone(),
                    endpoint,
                    outbound.clone(),
                    false,
                    None,
                    "addr-fetch",
                    true,
                );
            }
        }
        let has_known_network_addresses = !self.node.known_network_addresses().is_empty();
        let should_query_dns = !configured_connect_nodes
            && self.node.config.dnsseed
            && (self.node.config.force_dns_seed || !has_known_network_addresses);
        let delayed_dns_seed_fallback = !configured_connect_nodes
            && self.node.config.dnsseed
            && !self.node.config.force_dns_seed
            && has_known_network_addresses;
        let fixed_seed_fallback_started_at = unix_time_seconds();
        let mut fixed_seeds_added = false;
        let connect_nodes = if should_query_dns {
            let addresses = discover_dns_seeds(
                self.node.config.network,
                &self.node.config.signet_seed_nodes,
            )
            .await;
            let mut remembered = 0usize;
            for address in &addresses {
                if self.node.config.allows_address(*address) {
                    remembered += usize::from(self.node.remember_network_address(
                        NetworkEndpoint::from_socket(*address),
                        wire::NODE_NETWORK | wire::NODE_WITNESS,
                        unix_time_seconds(),
                    ));
                }
            }
            let elapsed = Duration::from_secs(
                unix_time_seconds().saturating_sub(fixed_seed_fallback_started_at),
            );
            if remembered == 0
                && should_add_fixed_seed_fallback(
                    self.node.config.fixed_seeds,
                    self.node.config.dnsseed,
                    has_seed_nodes,
                    has_add_nodes,
                    elapsed,
                )
                && has_empty_fixed_seed_network(&self.node)
            {
                remembered = add_fixed_seed_addresses(&self.node);
                fixed_seeds_added = true;
            }
            if remembered != 0 {
                info!(remembered, "added bootstrap peer addresses");
            }
            Vec::new()
        } else {
            let elapsed = Duration::from_secs(
                unix_time_seconds().saturating_sub(fixed_seed_fallback_started_at),
            );
            if !configured_connect_nodes
                && !has_known_network_addresses
                && should_add_fixed_seed_fallback(
                    self.node.config.fixed_seeds,
                    self.node.config.dnsseed,
                    has_seed_nodes,
                    has_add_nodes,
                    elapsed,
                )
                && has_empty_fixed_seed_network(&self.node)
            {
                let remembered = add_fixed_seed_addresses(&self.node);
                fixed_seeds_added = true;
                if remembered != 0 {
                    info!(remembered, "added fixed seed peer addresses");
                }
            }
            self.node.config.seed_nodes.clone()
        };
        let manual_nodes = self
            .node
            .config
            .add_nodes
            .iter()
            .cloned()
            .chain(connect_nodes)
            .collect::<Vec<_>>();
        for endpoint in manual_nodes {
            self.node.ensure_node_endpoint_added(endpoint.clone());
            spawn_outbound_loop(
                self.node.clone(),
                endpoint,
                outbound.clone(),
                true,
                None,
                "outbound-full",
                true,
            );
        }
        let discovery_node = self.node.clone();
        let discovery_outbound = outbound.clone();
        if !configured_connect_nodes {
            tokio::spawn(async move {
                let mut ticker = tokio::time::interval(Duration::from_secs(30));
                ticker.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
                let discovery_started = Instant::now();
                let mut queried_delayed_dns_seed = false;
                loop {
                    ticker.tick().await;
                    if !discovery_node.network_active() {
                        continue;
                    }
                    let outbound_peer_count = discovery_node
                        .peer_infos()
                        .into_iter()
                        .filter(|peer| !peer.inbound)
                        .count();
                    if !queried_delayed_dns_seed
                        && should_query_dns_seed_fallback(
                            delayed_dns_seed_fallback,
                            discovery_started.elapsed(),
                            outbound_peer_count,
                        )
                    {
                        queried_delayed_dns_seed = true;
                        for address in discover_dns_seeds(
                            discovery_node.config.network,
                            &discovery_node.config.signet_seed_nodes,
                        )
                        .await
                        {
                            if discovery_node.config.allows_address(address) {
                                discovery_node.remember_network_address(
                                    NetworkEndpoint::from_socket(address),
                                    wire::NODE_NETWORK | wire::NODE_WITNESS,
                                    unix_time_seconds(),
                                );
                            }
                        }
                    }
                    if !fixed_seeds_added
                        && should_add_fixed_seed_fallback(
                            discovery_node.config.fixed_seeds,
                            discovery_node.config.dnsseed,
                            has_seed_nodes,
                            has_add_nodes,
                            Duration::from_secs(
                                unix_time_seconds().saturating_sub(fixed_seed_fallback_started_at),
                            ),
                        )
                        && has_empty_fixed_seed_network(&discovery_node)
                    {
                        let remembered = add_fixed_seed_addresses(&discovery_node);
                        fixed_seeds_added = true;
                        if remembered != 0 {
                            info!(remembered, "added fixed seed peer addresses");
                        }
                    }
                    let available = discovery_outbound.slots.available_permits().min(8);
                    if available == 0 {
                        continue;
                    }
                    for endpoint in select_discovery_endpoints(
                        &discovery_node,
                        available,
                        &discovery_outbound.attempts,
                    ) {
                        spawn_outbound_loop(
                            discovery_node.clone(),
                            endpoint,
                            discovery_outbound.clone(),
                            false,
                            None,
                            "outbound-full",
                            false,
                        );
                    }
                }
            });
        }
        let dynamic_node = self.node.clone();
        let dynamic_outbound = outbound.clone();
        tokio::spawn(async move {
            let mut private_retry_interval =
                tokio::time::interval(Duration::from_secs(PRIVATE_BROADCAST_RETRY_SECS));
            loop {
                tokio::select! {
                    request = add_node_receiver.recv() => {
                        let Some(request) = request else {
                            break;
                        };
                        let (endpoint, persistent, transport_v2, connection_type, manual) = match request {
                            PeerManagerRequest::Add(endpoint, transport_v2) => (endpoint, true, transport_v2, "outbound-full", true),
                            PeerManagerRequest::OneTry(endpoint, transport_v2, connection_type) => {
                                (endpoint, false, transport_v2, connection_type, true)
                            }
                            PeerManagerRequest::PrivateBroadcast { address, transaction } => {
                                spawn_private_broadcast_loop(
                                    dynamic_node.clone(),
                                    address,
                                    dynamic_outbound.clone(),
                                    transaction,
                                );
                                continue;
                            }
                        };
                        spawn_outbound_loop(
                            dynamic_node.clone(),
                            endpoint,
                            dynamic_outbound.clone(),
                            persistent,
                            transport_v2,
                            connection_type,
                            manual,
                        );
                    }
                    _ = private_retry_interval.tick() => {
                        dynamic_node.schedule_private_broadcasts();
                    }
                }
            }
        });

        let mut inbound_listeners = JoinSet::new();
        for listener in listeners {
            inbound_listeners.spawn(run_inbound_listener(
                self.node.clone(),
                listener,
                slots.clone(),
                peers.clone(),
                next_peer_id.clone(),
                None,
            ));
        }
        for (listener, permissions) in whitebind_listeners {
            inbound_listeners.spawn(run_inbound_listener(
                self.node.clone(),
                listener,
                slots.clone(),
                peers.clone(),
                next_peer_id.clone(),
                Some(permissions),
            ));
        }
        if self.node.config.listen && self.node.config.i2p_accept_incoming {
            if let Some(i2p_sam) = self.node.i2p_sam.clone() {
                inbound_listeners.spawn(run_i2p_listener(
                    self.node.clone(),
                    i2p_sam,
                    slots.clone(),
                    peers.clone(),
                    next_peer_id.clone(),
                ));
            }
        }
        if let (Some(tor_controller), Some(target)) = (self.node.tor_controller.clone(), tor_target)
        {
            inbound_listeners.spawn(run_tor_service(
                self.node.clone(),
                tor_controller,
                target,
                default_p2p_port(self.node.config.network),
            ));
        }
        if inbound_listeners.is_empty() {
            return std::future::pending::<Result<()>>().await;
        }
        while let Some(result) = inbound_listeners.join_next().await {
            result??;
        }
        Ok(())
    }
}

async fn run_i2p_listener(
    node: Arc<Node>,
    i2p_sam: Arc<crate::i2p::I2pSam>,
    slots: Arc<Semaphore>,
    peers: PeerRegistry,
    next_peer_id: Arc<AtomicUsize>,
) -> Result<()> {
    let mut advertised = false;
    loop {
        if let Ok(endpoint) = i2p_sam.local_endpoint().await {
            if !advertised {
                node.add_listen_network_address(endpoint);
                advertised = true;
            }
        } else if !advertised {
            // SAM startup is independent of the Bitcoin listener. Retry in
            // the background so a temporarily unavailable I2P router does
            // not prevent clearnet operation from starting.
            tokio::time::sleep(Duration::from_secs(5)).await;
            continue;
        }

        match i2p_sam.accept().await {
            Ok((stream, endpoint)) => {
                if !node.network_active() {
                    continue;
                }
                let node = node.clone();
                let slots = slots.clone();
                let peers = peers.clone();
                let peer_id = next_peer_id.fetch_add(1, Ordering::Relaxed);
                tokio::spawn(async move {
                    let Ok(_permit) = slots.try_acquire_owned() else {
                        debug!(%endpoint, "rejecting I2P peer because peer limit is reached");
                        return;
                    };
                    let transport_v2 = (!node.config.v2_transport).then_some(false);
                    if let Err(error) = serve_peer(
                        node,
                        stream,
                        endpoint.clone(),
                        PeerConnectionOptions {
                            outbound: false,
                            transport_v2,
                            connection_type: "inbound",
                            permissions: None,
                            private_broadcast_transaction: None,
                        },
                        peers,
                        peer_id,
                    )
                    .await
                    {
                        debug!(%endpoint, %error, "I2P peer ended");
                    }
                });
            }
            Err(error) => {
                debug!(%error, "I2P SAM accept failed; recreating session");
                i2p_sam.reset().await;
                advertised = false;
                tokio::time::sleep(Duration::from_secs(1)).await;
            }
        }
    }
}

fn tor_service_target(address: SocketAddr) -> SocketAddr {
    match address {
        SocketAddr::V4(address) if address.ip().is_unspecified() => {
            SocketAddr::from(([127, 0, 0, 1], address.port()))
        }
        SocketAddr::V6(address) if address.ip().is_unspecified() => {
            SocketAddr::from(([0, 0, 0, 0, 0, 0, 0, 1], address.port()))
        }
        address => address,
    }
}

async fn run_tor_service(
    node: Arc<Node>,
    tor_controller: Arc<crate::tor::TorController>,
    target: SocketAddr,
    virtual_port: u16,
) -> Result<()> {
    let mut retry_delay = Duration::from_secs(1);
    loop {
        match tor_controller.publish(target, virtual_port).await {
            Ok((endpoint, mut control)) => {
                node.add_listen_network_address(endpoint.clone());
                retry_delay = Duration::from_secs(1);
                if let Err(error) = tor_controller.wait_for_disconnect(&mut control).await {
                    debug!(%error, "Tor onion service control connection ended");
                }
                node.remove_listen_network_address(&endpoint);
                tor_controller.clear();
            }
            Err(error) => {
                tor_controller.clear();
                debug!(%error, "Tor onion service setup failed; retrying");
                tokio::time::sleep(retry_delay).await;
                retry_delay = (retry_delay * 3 / 2).min(Duration::from_secs(600));
            }
        }
    }
}

async fn run_inbound_listener(
    node: Arc<Node>,
    listener: TcpListener,
    slots: Arc<Semaphore>,
    peers: PeerRegistry,
    next_peer_id: Arc<AtomicUsize>,
    permissions: Option<PeerPermissions>,
) -> Result<()> {
    loop {
        let (stream, address) = listener.accept().await?;
        let banned = match permissions {
            Some(permissions) => node.is_banned_for_permissions(address, permissions),
            None => node.is_banned_for_peer(address, true),
        };
        if !node.network_active() || banned {
            continue;
        }
        let node = node.clone();
        let slots = slots.clone();
        let peers = peers.clone();
        let transport_v2 = (!node.config.v2_transport).then_some(false);
        let peer_id = next_peer_id.fetch_add(1, Ordering::Relaxed);
        tokio::spawn(async move {
            let Ok(permit) = slots.try_acquire_owned() else {
                debug!(%address, "rejecting peer because peer limit is reached");
                return;
            };
            if let Err(error) = serve_peer(
                node,
                stream,
                NetworkEndpoint::from_socket(address),
                PeerConnectionOptions {
                    outbound: false,
                    transport_v2,
                    connection_type: "inbound",
                    permissions,
                    private_broadcast_transaction: None,
                },
                peers,
                peer_id,
            )
            .await
            {
                debug!(%address, %error, "inbound peer ended");
            }
            drop(permit);
        });
    }
}

fn spawn_outbound_loop(
    node: Arc<Node>,
    endpoint: NetworkEndpoint,
    outbound: OutboundContext,
    persistent: bool,
    transport_v2: Option<bool>,
    connection_type: &'static str,
    manual: bool,
) {
    {
        let mut attempts = outbound.attempts.lock();
        if !attempts.insert(endpoint.clone()) {
            return;
        }
    }
    let transport_v2 = transport_v2.or_else(|| (!node.config.v2_transport).then_some(false));
    let peer_id = outbound.next_peer_id.fetch_add(1, Ordering::Relaxed);
    let OutboundContext {
        slots,
        manual_slots,
        peers,
        attempts: outbound_attempts,
        ..
    } = outbound;
    tokio::spawn(async move {
        struct AttemptGuard {
            endpoint: NetworkEndpoint,
            attempts: OutboundAttempts,
        }

        impl Drop for AttemptGuard {
            fn drop(&mut self) {
                self.attempts.lock().remove(&self.endpoint);
            }
        }

        let _attempt = AttemptGuard {
            endpoint: endpoint.clone(),
            attempts: outbound_attempts,
        };
        let permit = if manual {
            manual_slots.acquire_owned().await
        } else {
            slots.acquire_owned().await
        };
        let Ok(_permit) = permit else {
            return;
        };
        if !manual && !node.config.allows_network_endpoint(&endpoint) {
            debug!(endpoint = %endpoint, "skipping outbound peer outside onlynet policy");
            return;
        }
        loop {
            if persistent && !node.is_node_added_endpoint(&endpoint) {
                return;
            }
            if !node.network_active()
                || endpoint
                    .socket_addr()
                    .is_some_and(|address| node.is_banned_for_peer(address, false))
            {
                tokio::time::sleep(Duration::from_secs(1)).await;
                continue;
            }
            if node
                .peer_infos()
                .into_iter()
                .any(|peer| peer.endpoint == endpoint)
            {
                if !persistent {
                    return;
                }
                tokio::time::sleep(Duration::from_secs(5)).await;
                continue;
            }
            match connect_peer_endpoint_with_options_and_dns_with_i2p(
                &endpoint,
                node.config.proxy,
                node.onion_proxy(),
                false,
                node.config.proxy_randomize,
                node.config.dns_lookup,
                Duration::from_millis(node.config.connect_timeout_ms),
                node.i2p_sam.clone(),
            )
            .await
            {
                Ok(stream) => {
                    info!(endpoint = %endpoint, "connected to configured peer");
                    if let Err(error) = serve_peer(
                        node.clone(),
                        stream,
                        endpoint.clone(),
                        PeerConnectionOptions {
                            outbound: true,
                            transport_v2,
                            connection_type,
                            permissions: None,
                            private_broadcast_transaction: None,
                        },
                        peers.clone(),
                        peer_id,
                    )
                    .await
                    {
                        debug!(endpoint = %endpoint, %error, "outbound peer ended");
                    }
                    if !persistent {
                        return;
                    }
                }
                Err(error) => {
                    if !persistent {
                        debug!(endpoint = %endpoint, %error, "one-shot peer connection failed");
                        return;
                    }
                    warn!(endpoint = %endpoint, %error, "unable to connect to configured peer");
                }
            }
            tokio::time::sleep(Duration::from_secs(5)).await;
        }
    });
}

fn spawn_private_broadcast_loop(
    node: Arc<Node>,
    address: SocketAddr,
    outbound: OutboundContext,
    transaction: Transaction,
) {
    let endpoint = NetworkEndpoint::Ip(address);
    {
        let mut attempts = outbound.attempts.lock();
        if !attempts.insert(endpoint.clone()) {
            return;
        }
    }
    let peer_id = outbound.next_peer_id.fetch_add(1, Ordering::Relaxed);
    let OutboundContext {
        private_slots,
        peers,
        attempts: outbound_attempts,
        ..
    } = outbound;
    tokio::spawn(async move {
        struct AttemptGuard {
            endpoint: NetworkEndpoint,
            attempts: OutboundAttempts,
        }

        impl Drop for AttemptGuard {
            fn drop(&mut self) {
                self.attempts.lock().remove(&self.endpoint);
            }
        }

        let _attempt = AttemptGuard {
            endpoint: endpoint.clone(),
            attempts: outbound_attempts,
        };
        let Ok(_permit) = private_slots.acquire_owned().await else {
            return;
        };
        if !node.config.allows_address(address)
            || !node.network_active()
            || node.is_banned_for_peer(address, false)
        {
            return;
        }
        match connect_peer_endpoint_for_private_broadcast(
            &endpoint,
            node.config.proxy,
            node.config.proxy_randomize,
            Duration::from_millis(node.config.connect_timeout_ms),
        )
        .await
        {
            Ok(stream) => {
                info!(%address, "connected to private-broadcast peer");
                if let Err(error) = serve_peer(
                    node.clone(),
                    stream,
                    endpoint.clone(),
                    PeerConnectionOptions {
                        outbound: true,
                        transport_v2: (!node.config.v2_transport).then_some(false),
                        connection_type: "private-broadcast",
                        permissions: None,
                        private_broadcast_transaction: Some(transaction),
                    },
                    peers,
                    peer_id,
                )
                .await
                {
                    debug!(%address, %error, "private-broadcast peer ended");
                }
            }
            Err(error) => {
                debug!(%address, %error, "private-broadcast connection failed");
            }
        }
    });
}

fn select_discovery_endpoints(
    node: &Arc<Node>,
    limit: usize,
    outbound_attempts: &OutboundAttempts,
) -> Vec<NetworkEndpoint> {
    if limit == 0 {
        return Vec::new();
    }
    let connected: HashSet<_> = node
        .peer_infos()
        .into_iter()
        .map(|peer| peer.endpoint)
        .collect();
    let connected_asns: HashSet<_> = node
        .peer_infos()
        .into_iter()
        .filter_map(|peer| node.mapped_as(&peer.endpoint))
        .collect();
    let added: HashSet<_> = node.added_network_endpoints().into_iter().collect();
    let attempts = outbound_attempts.lock();
    let mut candidates = node
        .known_network_addresses()
        .into_iter()
        .filter(|entry| {
            endpoint_can_be_discovered(node, &entry.endpoint)
                && !connected.contains(&entry.endpoint)
                && !entry.endpoint.legacy_socket_addr().is_some_and(|address| {
                    address.ip().is_unspecified() || node.is_banned_for_peer(address, false)
                })
                && !added.contains(&entry.endpoint)
                && !attempts.contains(&entry.endpoint)
        })
        .collect::<Vec<_>>();
    drop(attempts);
    candidates.sort_by(|left, right| {
        node.is_network_address_tried(&right.endpoint)
            .cmp(&node.is_network_address_tried(&left.endpoint))
            .then_with(|| right.time.cmp(&left.time))
            .then_with(|| left.endpoint.cmp(&right.endpoint))
    });
    let mut selected = Vec::with_capacity(limit);
    let mut selected_asns = connected_asns;
    for entry in candidates {
        if let Some(asn) = node.mapped_as(&entry.endpoint)
            && !selected_asns.insert(asn)
        {
            continue;
        }
        selected.push(entry.endpoint);
        if selected.len() == limit {
            break;
        }
    }
    selected
}

fn should_query_dns_seed_fallback(
    enabled: bool,
    elapsed: Duration,
    outbound_peer_count: usize,
) -> bool {
    enabled
        && elapsed >= DNS_SEED_FALLBACK_DELAY
        && outbound_peer_count < DNS_SEED_OUTBOUND_THRESHOLD
}

fn should_add_fixed_seed_fallback(
    enabled: bool,
    dnsseed: bool,
    has_seed_nodes: bool,
    has_add_nodes: bool,
    elapsed: Duration,
) -> bool {
    enabled
        && ((!dnsseed && !has_seed_nodes && !has_add_nodes) || elapsed >= FIXED_SEED_FALLBACK_DELAY)
}

#[cfg(test)]
fn select_discovery_addresses(
    node: &Arc<Node>,
    limit: usize,
    outbound_attempts: &OutboundAttempts,
) -> Vec<SocketAddr> {
    select_discovery_endpoints(node, limit, outbound_attempts)
        .into_iter()
        .filter_map(|endpoint| endpoint.legacy_socket_addr())
        .collect()
}

#[cfg(test)]
async fn connect_peer_endpoint(
    endpoint: &NetworkEndpoint,
    proxy: Option<SocketAddr>,
) -> Result<TcpStream> {
    connect_peer_endpoint_with_options_and_dns(endpoint, proxy, false, false, true).await
}

async fn connect_peer_endpoint_for_private_broadcast(
    endpoint: &NetworkEndpoint,
    proxy: Option<SocketAddr>,
    proxy_randomize: bool,
    connect_timeout: Duration,
) -> Result<TcpStream> {
    connect_peer_endpoint_with_options_and_dns_with_timeout(
        endpoint,
        proxy,
        true,
        proxy_randomize,
        true,
        connect_timeout,
    )
    .await
}

#[cfg(test)]
async fn connect_peer_endpoint_with_options(
    endpoint: &NetworkEndpoint,
    proxy: Option<SocketAddr>,
    force_proxy: bool,
    proxy_randomize: bool,
) -> Result<TcpStream> {
    connect_peer_endpoint_with_options_and_dns(endpoint, proxy, force_proxy, proxy_randomize, true)
        .await
}

#[cfg(test)]
async fn connect_peer_endpoint_with_options_and_dns(
    endpoint: &NetworkEndpoint,
    proxy: Option<SocketAddr>,
    force_proxy: bool,
    proxy_randomize: bool,
    allow_dns_lookup: bool,
) -> Result<TcpStream> {
    connect_peer_endpoint_with_options_and_dns_with_timeout(
        endpoint,
        proxy,
        force_proxy,
        proxy_randomize,
        allow_dns_lookup,
        Duration::from_millis(DEFAULT_CONNECT_TIMEOUT_MS),
    )
    .await
}

async fn connect_peer_endpoint_with_options_and_dns_with_timeout(
    endpoint: &NetworkEndpoint,
    proxy: Option<SocketAddr>,
    force_proxy: bool,
    proxy_randomize: bool,
    allow_dns_lookup: bool,
    connect_timeout: Duration,
) -> Result<TcpStream> {
    connect_peer_endpoint_with_options_and_dns_with_i2p(
        endpoint,
        proxy,
        None,
        force_proxy,
        proxy_randomize,
        allow_dns_lookup,
        connect_timeout,
        None,
    )
    .await
}

#[allow(clippy::too_many_arguments)]
async fn connect_peer_endpoint_with_options_and_dns_with_i2p(
    endpoint: &NetworkEndpoint,
    proxy: Option<SocketAddr>,
    onion_proxy: Option<SocketAddr>,
    force_proxy: bool,
    proxy_randomize: bool,
    allow_dns_lookup: bool,
    connect_timeout: Duration,
    i2p_sam: Option<Arc<crate::i2p::I2pSam>>,
) -> Result<TcpStream> {
    if let Some(i2p_sam) = i2p_sam
        && matches!(endpoint, NetworkEndpoint::I2p { .. })
    {
        return i2p_sam.connect(endpoint).await;
    }
    let proxy = if endpoint.is_onion() {
        onion_proxy.or(proxy)
    } else {
        proxy
    };
    let proxy = proxy.filter(|_| force_proxy || endpoint.uses_proxy_by_default());
    if proxy.is_none() && endpoint.requires_proxy() {
        bail!("endpoint {endpoint} requires a SOCKS5 proxy");
    }
    let mut stream = if let Some(proxy) = proxy {
        connect_tcp_with_timeout(
            proxy,
            connect_timeout,
            format!("connecting to {endpoint} through proxy {proxy}"),
        )
        .await?
    } else if let Some(target) = endpoint.socket_addr() {
        connect_tcp_with_timeout(target, connect_timeout, format!("connecting to {endpoint}"))
            .await?
    } else {
        if !allow_dns_lookup {
            bail!("DNS lookup is disabled for hostname endpoint {endpoint}");
        }
        let host = endpoint.host_string();
        connect_tcp_with_timeout(
            (host.as_str(), endpoint.port()),
            connect_timeout,
            format!("resolving and connecting to {host}:{}", endpoint.port()),
        )
        .await?
    };
    stream.set_nodelay(true)?;
    if proxy.is_some() {
        socks5_connect_endpoint_with_options(&mut stream, endpoint, proxy_randomize).await?;
    }
    Ok(stream)
}

async fn connect_tcp_with_timeout<A>(
    address: A,
    timeout: Duration,
    context: String,
) -> Result<TcpStream>
where
    A: tokio::net::ToSocketAddrs,
{
    let timeout_context = context.clone();
    match tokio::time::timeout(timeout, TcpStream::connect(address)).await {
        Ok(result) => result.with_context(|| context),
        Err(_) => bail!(
            "{timeout_context}; timed out after {} ms",
            timeout.as_millis()
        ),
    }
}

#[cfg(test)]
async fn socks5_connect(stream: &mut TcpStream, address: SocketAddr) -> Result<()> {
    socks5_connect_endpoint(stream, &NetworkEndpoint::Ip(address)).await
}

#[cfg(test)]
async fn socks5_connect_endpoint(stream: &mut TcpStream, endpoint: &NetworkEndpoint) -> Result<()> {
    socks5_connect_endpoint_with_options(stream, endpoint, false).await
}

fn proxy_credentials() -> String {
    use std::sync::atomic::AtomicU64;

    static PREFIX: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let prefix = PREFIX.get_or_init(|| format!("{}-", hex::encode(random::<[u8; 8]>())));
    format!("{prefix}{}", COUNTER.fetch_add(1, Ordering::Relaxed))
}

async fn socks5_connect_endpoint_with_options(
    stream: &mut TcpStream,
    endpoint: &NetworkEndpoint,
    proxy_randomize: bool,
) -> Result<()> {
    if proxy_randomize {
        stream.write_all(&[5, 2, 0, 2]).await?;
    } else {
        stream.write_all(&[5, 1, 0]).await?;
    }
    let mut greeting = [0; 2];
    stream.read_exact(&mut greeting).await?;
    if greeting[0] != 5 {
        bail!("SOCKS5 proxy returned an invalid greeting version")
    }
    match greeting[1] {
        0 if !proxy_randomize => {}
        0 if proxy_randomize => {}
        2 if proxy_randomize => {
            let credential = proxy_credentials();
            let credential_length =
                u8::try_from(credential.len()).context("SOCKS5 proxy credential is too long")?;
            let mut authentication = Vec::with_capacity(3 + credential.len() * 2);
            authentication.extend_from_slice(&[1, credential_length]);
            authentication.extend_from_slice(credential.as_bytes());
            authentication.push(credential_length);
            authentication.extend_from_slice(credential.as_bytes());
            stream.write_all(&authentication).await?;
            let mut response = [0; 2];
            stream.read_exact(&mut response).await?;
            if response != [1, 0] {
                bail!("SOCKS5 proxy authentication failed")
            }
        }
        _ => bail!("SOCKS5 proxy does not support the requested authentication methods"),
    }

    let host = endpoint.host_string();
    let host = host.as_bytes();
    let length = u8::try_from(host.len()).context("SOCKS5 domain name is too long")?;
    let mut request = Vec::with_capacity(7 + host.len());
    request.extend_from_slice(&[5, 1, 0]);
    // Core deliberately uses the domain-name form for every destination,
    // including numeric IPv4/IPv6 addresses. This keeps proxy behavior
    // consistent across address families and matches Tor's SOCKS5 handling.
    request.push(3);
    request.push(length);
    request.extend_from_slice(host);
    request.extend_from_slice(&endpoint.port().to_be_bytes());
    stream.write_all(&request).await?;

    let mut response = [0; 4];
    stream.read_exact(&mut response).await?;
    if response[0] != 5 {
        bail!("SOCKS5 proxy returned an invalid response version")
    }
    if response[1] != 0 {
        bail!(
            "SOCKS5 proxy rejected the connection with code {}",
            response[1]
        )
    }
    match response[3] {
        1 => {
            let mut address = [0; 4];
            stream.read_exact(&mut address).await?;
        }
        3 => {
            let mut length = [0; 1];
            stream.read_exact(&mut length).await?;
            let mut address = vec![0; usize::from(length[0])];
            stream.read_exact(&mut address).await?;
        }
        4 => {
            let mut address = [0; 16];
            stream.read_exact(&mut address).await?;
        }
        value => bail!("SOCKS5 proxy returned an invalid address type {value}"),
    }
    let mut port = [0; 2];
    stream.read_exact(&mut port).await?;
    Ok(())
}

async fn discover_dns_seeds(
    network: Network,
    signet_seed_nodes: &[String],
) -> Vec<std::net::SocketAddr> {
    let hosts = dns_seed_hosts(network, signet_seed_nodes);
    let default_port = match network {
        Network::Bitcoin => 8333,
        Network::Testnet => 18333,
        Network::Testnet4 => 48333,
        Network::Signet => 38333,
        Network::Regtest => return Vec::new(),
    };
    let mut addresses = Vec::new();
    for host in hosts {
        let (host, port) = dns_seed_target(&host, default_port);
        if let Ok(resolved) = tokio::net::lookup_host((host, port)).await {
            addresses.extend(resolved.take(16));
        }
        if addresses.len() >= 64 {
            break;
        }
    }
    addresses
}

fn dns_seed_target(value: &str, default_port: u16) -> (&str, u16) {
    if let Some(value) = value.strip_prefix('[')
        && let Some((host, port)) = value.split_once("]:")
        && let Ok(port) = port.parse::<u16>()
    {
        return (host, port);
    }
    if let Some((host, port)) = value.rsplit_once(':')
        && !host.is_empty()
        && let Ok(port) = port.parse::<u16>()
    {
        return (host, port);
    }
    (value, default_port)
}

fn dns_seed_hosts(network: Network, signet_seed_nodes: &[String]) -> Vec<String> {
    if network == Network::Signet && !signet_seed_nodes.is_empty() {
        return signet_seed_nodes.to_vec();
    }
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
            "seed.signet.achownodes.xyz",
        ],
        Network::Testnet4 | Network::Regtest => &[],
    };
    hosts.iter().map(|host| (*host).to_owned()).collect()
}

fn fixed_seed_data(network: Network) -> &'static [u8] {
    match network {
        Network::Bitcoin => include_bytes!("fixed_seeds/main.bin"),
        Network::Testnet => include_bytes!("fixed_seeds/test.bin"),
        Network::Testnet4 => include_bytes!("fixed_seeds/testnet4.bin"),
        Network::Signet => include_bytes!("fixed_seeds/signet.bin"),
        Network::Regtest => &[],
    }
}

fn fixed_seed_endpoints(network: Network) -> Vec<NetworkEndpoint> {
    // These assets are the generated chainparamsseeds.h records from Core
    // v31.1. Each record is a BIP155 network id, a length-prefixed address,
    // and a big-endian port. Keeping the records typed is important for
    // onlynet filtering and proxy-backed Tor/I2P/CJDNS connections.
    let bytes = fixed_seed_data(network);
    let mut endpoints = Vec::new();
    let mut cursor = 0;
    while cursor + 2 <= bytes.len() {
        let network_id = bytes[cursor];
        let address_len = usize::from(bytes[cursor + 1]);
        cursor += 2;
        if cursor + address_len + 2 > bytes.len() {
            break;
        }
        let address = &bytes[cursor..cursor + address_len];
        cursor += address_len;
        let port = u16::from_be_bytes([bytes[cursor], bytes[cursor + 1]]);
        cursor += 2;
        if let Some(endpoint) = NetworkEndpoint::from_addr_v2(network_id, address, port) {
            endpoints.push(endpoint);
        }
    }
    endpoints
}

#[cfg(test)]
fn fixed_seed_addresses(network: Network) -> Vec<SocketAddr> {
    fixed_seed_endpoints(network)
        .into_iter()
        .filter_map(|endpoint| endpoint.socket_addr())
        .collect()
}

fn add_fixed_seed_addresses(node: &Arc<Node>) -> usize {
    let known_networks = known_discovered_networks(node);
    fixed_seed_endpoints(node.config.network)
        .into_iter()
        .filter(|endpoint| {
            endpoint_can_be_discovered(node, endpoint)
                && !known_networks.contains(endpoint.network_name())
        })
        .filter(|endpoint| {
            node.remember_network_address(
                endpoint.clone(),
                wire::NODE_NETWORK | wire::NODE_WITNESS,
                unix_time_seconds(),
            )
        })
        .count()
}

fn endpoint_can_be_discovered(node: &Node, endpoint: &NetworkEndpoint) -> bool {
    if !node.config.allows_network_endpoint(endpoint) {
        return false;
    }
    if endpoint.port() == 0 && !matches!(endpoint, NetworkEndpoint::I2p { .. }) {
        return false;
    }
    match endpoint {
        NetworkEndpoint::Ip(_) | NetworkEndpoint::Cjdns { .. } => true,
        NetworkEndpoint::OnionV2 { .. } | NetworkEndpoint::OnionV3 { .. } => {
            node.config.proxy.is_some() || node.onion_proxy().is_some()
        }
        NetworkEndpoint::I2p { .. } => node.config.proxy.is_some() || node.i2p_sam.is_some(),
        NetworkEndpoint::Dns { .. } => false,
    }
}

fn known_discovered_networks(node: &Node) -> HashSet<&'static str> {
    node.known_network_addresses()
        .into_iter()
        .filter(|entry| endpoint_can_be_discovered(node, &entry.endpoint))
        .map(|entry| entry.endpoint.network_name())
        .collect()
}

fn has_empty_fixed_seed_network(node: &Node) -> bool {
    let known_networks = known_discovered_networks(node);
    fixed_seed_endpoints(node.config.network)
        .into_iter()
        .filter(|endpoint| endpoint_can_be_discovered(node, endpoint))
        .any(|endpoint| !known_networks.contains(endpoint.network_name()))
}

#[derive(Clone)]
struct ProxyRoutingOptions {
    proxy: Option<SocketAddr>,
    onion_proxy: Option<SocketAddr>,
    force_proxy: bool,
    randomize_credentials: bool,
    allow_dns_lookup: bool,
    connect_timeout: Duration,
    i2p_sam: Option<Arc<crate::i2p::I2pSam>>,
}

async fn establish_transport(
    stream: TcpStream,
    endpoint: &NetworkEndpoint,
    outbound: bool,
    network: Network,
    transport_v2: Option<bool>,
    proxy_options: ProxyRoutingOptions,
) -> Result<(
    PeerReader,
    PeerWriterKind,
    Option<SocketAddr>,
    Option<String>,
)> {
    if outbound {
        if transport_v2 == Some(false) {
            return establish_v1(stream);
        }
        if transport_v2 == Some(true) {
            return establish_v2(stream, network, Role::Initiator).await;
        }
        match establish_v2(stream, network, Role::Initiator).await {
            Ok((reader, writer, local_address, session_id)) => {
                return Ok((reader, writer, local_address, session_id));
            }
            Err(error) => {
                debug!(%endpoint, %error, "BIP324 handshake failed; retrying with v1");
                let fallback = connect_peer_endpoint_with_options_and_dns_with_i2p(
                    endpoint,
                    proxy_options.proxy,
                    proxy_options.onion_proxy,
                    proxy_options.force_proxy,
                    proxy_options.randomize_credentials,
                    proxy_options.allow_dns_lookup,
                    proxy_options.connect_timeout,
                    proxy_options.i2p_sam,
                )
                .await
                .with_context(|| format!("reconnecting to {endpoint} with v1 transport"))?;
                return establish_v1(fallback);
            }
        }
    }

    let mut prefix = [0u8; 16];
    let mut received = 0;
    while received < prefix.len() {
        let count = stream.peek(&mut prefix[received..]).await?;
        if count == 0 {
            anyhow::bail!("peer closed before transport negotiation");
        }
        received += count;
    }

    let mut v1_prefix = [0u8; 16];
    v1_prefix[..4].copy_from_slice(&wire::network_magic(network));
    v1_prefix[4..11].copy_from_slice(b"version");
    if prefix == v1_prefix {
        establish_v1(stream)
    } else {
        establish_v2(stream, network, Role::Responder).await
    }
}

async fn establish_v2(
    stream: TcpStream,
    network: Network,
    role: Role,
) -> Result<(
    PeerReader,
    PeerWriterKind,
    Option<SocketAddr>,
    Option<String>,
)> {
    let local_address = stream.local_addr().ok();
    let (reader, mut writer) = stream.into_split();
    let mut reader = BufReader::new(reader);

    let handshake = Handshake::new(wire::network_magic(network), role)?;
    let mut key_buffer = vec![0; Handshake::<bip324::Initialized>::send_key_len(None)];
    let handshake = handshake.send_key(None, &mut key_buffer)?;
    writer.write_all(&key_buffer).await?;
    writer.flush().await?;

    let mut remote_key = [0; BIP324_ELLIGATOR_SWIFT_BYTES];
    reader.read_exact(&mut remote_key).await?;
    let handshake = handshake.receive_key(remote_key)?;

    let mut version_buffer = vec![0; Handshake::<bip324::ReceivedKey<'_>>::send_version_len(None)];
    let handshake = handshake.send_version(&mut version_buffer, None)?;
    writer.write_all(&version_buffer).await?;
    writer.flush().await?;

    let mut garbage_buffer = vec![0; BIP324_GARBAGE_TERMINATOR_BYTES];
    reader.read_exact(&mut garbage_buffer).await?;
    let mut garbage_handshake = handshake;
    let (mut handshake, garbage_bytes) = loop {
        match garbage_handshake.receive_garbage(&garbage_buffer)? {
            GarbageResult::FoundGarbage {
                handshake,
                consumed_bytes,
            } => break (handshake, consumed_bytes),
            GarbageResult::NeedMoreData(next_handshake) => {
                let mut temp = vec![0; 256];
                let count = reader.read(&mut temp).await?;
                if count == 0 {
                    bail!("peer closed during BIP324 garbage negotiation");
                }
                garbage_buffer.extend_from_slice(&temp[..count]);
                garbage_handshake = next_handshake;
            }
        }
    };

    let mut session_reader =
        V2BufferedReader::new(reader, garbage_buffer[garbage_bytes..].to_vec());
    let mut length_bytes = [0; NUM_LENGTH_BYTES];
    let cipher = loop {
        session_reader.read_exact(&mut length_bytes).await?;
        let packet_len = handshake.decrypt_packet_len(length_bytes)?;
        if packet_len > BIP324_MAX_PACKET_SIZE_FOR_ALLOCATION {
            bail!("BIP324 packet exceeds the allocation limit");
        }
        let mut packet_bytes = vec![0; packet_len];
        session_reader.read_exact(&mut packet_bytes).await?;
        match handshake.receive_version(&mut packet_bytes)? {
            VersionResult::Complete { cipher } => break cipher,
            VersionResult::Decoy(next_handshake) => handshake = next_handshake,
        }
    };
    let session_id = Some(hex::encode(cipher.id()));
    let (inbound_cipher, outbound_cipher) = cipher.into_split();
    Ok((
        PeerReader::V2(Box::new(V2Reader::new(inbound_cipher, session_reader))),
        PeerWriterKind::V2(V2Writer {
            cipher: outbound_cipher,
            writer,
        }),
        local_address,
        session_id,
    ))
}

fn establish_v1(
    stream: TcpStream,
) -> Result<(
    PeerReader,
    PeerWriterKind,
    Option<SocketAddr>,
    Option<String>,
)> {
    let local_address = stream.local_addr().ok();
    let (reader, writer) = stream.into_split();
    Ok((
        PeerReader::V1(reader),
        PeerWriterKind::V1(writer),
        local_address,
        None,
    ))
}

struct PeerConnectionOptions {
    outbound: bool,
    transport_v2: Option<bool>,
    connection_type: &'static str,
    permissions: Option<PeerPermissions>,
    private_broadcast_transaction: Option<Transaction>,
}

async fn serve_peer(
    node: Arc<Node>,
    stream: TcpStream,
    endpoint: NetworkEndpoint,
    options: PeerConnectionOptions,
    peers: PeerRegistry,
    peer_id: usize,
) -> Result<()> {
    let _peer_count = PeerCountGuard::new(&node);
    stream.set_nodelay(true)?;
    let socket = SockRef::from(&stream);
    socket.set_recv_buffer_size(node.config.max_receive_buffer as usize)?;
    socket.set_send_buffer_size(node.config.max_send_buffer as usize)?;
    let (mut reader, writer_half, local_address, session_id) = establish_transport(
        stream,
        &endpoint,
        options.outbound,
        node.config.network,
        options.transport_v2,
        ProxyRoutingOptions {
            proxy: node.config.proxy,
            onion_proxy: node.onion_proxy(),
            force_proxy: options.connection_type == "private-broadcast",
            randomize_credentials: node.config.proxy_randomize,
            allow_dns_lookup: node.config.dns_lookup,
            connect_timeout: Duration::from_millis(node.config.connect_timeout_ms),
            i2p_sam: node.i2p_sam.clone(),
        },
    )
    .await?;
    let transport_v2 = matches!(&reader, PeerReader::V2(_));
    let peer_endpoint = endpoint.clone();
    let (commands, command_receiver) = mpsc::unbounded_channel();
    let permissions = options.permissions.unwrap_or_else(|| {
        endpoint
            .socket_addr()
            .map_or(PeerPermissions::empty(), |address| {
                node.permissions_for_peer(address, !options.outbound)
            })
    });
    node.register_peer_with_endpoint(
        peer_id,
        endpoint,
        !options.outbound,
        commands,
        PeerRegistrationOptions {
            local_address,
            permissions,
            connection_type: options.connection_type,
        },
    );
    node.set_peer_transport_protocol(peer_id, transport_v2);
    node.set_peer_session_id(peer_id, session_id);
    node.set_peer_connection_type(peer_id, options.connection_type);
    let peer_state = Arc::new(PeerState {
        endpoint: peer_endpoint,
        local_address,
        writer: Arc::new(Mutex::new(writer_half)),
        connection_type: options.connection_type,
        permissions,
        private_broadcast_transaction: options.private_broadcast_transaction,
        private_broadcast_peer: parking_lot::Mutex::new(
            options.connection_type == "private-broadcast",
        ),
        local_relay_transactions: local_transaction_relay_enabled(
            options.connection_type,
            node.config.blocksonly,
            permissions,
        ),
        bloom_filter: parking_lot::Mutex::new(None),
        known_tx_inventory: parking_lot::Mutex::new(KnownTxInventory::new()),
        pending_tx_inventory: parking_lot::Mutex::new(Vec::new()),
        tx_requests: parking_lot::Mutex::new(TxRequestState::default()),
        fee_filter: parking_lot::Mutex::new(0),
        relay_transactions: parking_lot::Mutex::new(false),
        wtxid_relay: parking_lot::Mutex::new(false),
        send_headers: parking_lot::Mutex::new(false),
        last_headers_request: parking_lot::Mutex::new(None),
        compact_block_version: parking_lot::Mutex::new(None),
        compact_block_announce: parking_lot::Mutex::new(false),
        tx_reconciliation_salt: parking_lot::Mutex::new(None),
        tx_reconciliation_registered: parking_lot::Mutex::new(false),
    });
    peers.lock().insert(peer_id, peer_state.clone());
    let result = serve_peer_loop(
        &node,
        &mut reader,
        &peer_state,
        options.outbound,
        &peers,
        peer_id,
        command_receiver,
    )
    .await;
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
    reader: &mut PeerReader,
    peer_state: &PeerState,
    outbound: bool,
    peers: &PeerRegistry,
    peer_id: usize,
    mut commands: mpsc::UnboundedReceiver<PeerCommand>,
) -> Result<()> {
    let writer = &peer_state.writer;
    let bloom_filter = &peer_state.bloom_filter;
    let fee_filter = &peer_state.fee_filter;
    let relay_transactions = &peer_state.relay_transactions;
    let height = node.chain.read().height() as i32;
    let local_nonce = random();
    let mut version = if peer_state.connection_type == "private-broadcast" {
        VersionMessage {
            version: VersionMessage::PROTOCOL_VERSION,
            services: 0,
            timestamp: 0,
            receiver_services: 0,
            receiver_address: [0; 16],
            receiver_port: 0,
            sender_services: 0,
            sender_address: [0; 16],
            sender_port: 0,
            nonce: local_nonce,
            user_agent: "/pynode:0.0.1/".to_owned(),
            start_height: 0,
            relay: false,
        }
    } else {
        VersionMessage::with_bloom_and_comments(
            height,
            local_nonce,
            node.config.peer_bloom_filters
                || peer_state
                    .permissions
                    .contains(PeerPermissions::BLOOM_FILTER),
            &node.config.user_agent_comments,
        )
    };
    if peer_state.connection_type != "private-broadcast" {
        if let Some(address) = advertised_local_address(node, peer_state) {
            version.sender_address = socket_address_bytes(address);
            version.sender_port = address.port();
        }
        if let Some(address) = peer_state.endpoint.socket_addr() {
            version.receiver_address = socket_address_bytes(address);
            version.receiver_port = address.port();
        }
    }
    if peer_state.connection_type != "private-broadcast" && node.chain.read().is_pruned() {
        version.services &= !wire::NODE_NETWORK;
        version.services |= wire::NODE_NETWORK_LIMITED;
        version.receiver_services &= !wire::NODE_NETWORK;
        version.receiver_services |= wire::NODE_NETWORK_LIMITED;
        version.sender_services &= !wire::NODE_NETWORK;
        version.sender_services |= wire::NODE_NETWORK_LIMITED;
    }
    if peer_state.connection_type != "private-broadcast" && !node.config.v2_transport {
        version.services &= !wire::NODE_P2P_V2;
        version.receiver_services &= !wire::NODE_P2P_V2;
        version.sender_services &= !wire::NODE_P2P_V2;
    }
    if peer_state.connection_type != "private-broadcast"
        && !(node.config.blockfilterindex && node.config.peer_block_filters)
    {
        version.services &= !wire::NODE_COMPACT_FILTERS;
        version.receiver_services &= !wire::NODE_COMPACT_FILTERS;
        version.sender_services &= !wire::NODE_COMPACT_FILTERS;
    }
    version.relay = peer_state.local_relay_transactions;
    send_message(
        node,
        peer_id,
        writer,
        node.config.network,
        &Message::Version(version),
    )
    .await?;
    let mut version_received = false;
    let mut verack_received = false;
    let mut verack_sent = false;
    let mut extensions_sent = false;
    let mut addrv2_received = false;
    let mut getaddr_received = false;
    let mut peer_version = 0i32;
    let mut peer_services = 0u64;
    let mut compact_block_version = 2u64;
    let mut pending_compact = None;
    let peer_timeout = Duration::from_secs(node.config.peer_timeout_secs);
    let mut ping_interval = tokio::time::interval(Duration::from_secs(120));
    ping_interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
    let addr_fetch_started_at = unix_time_seconds();
    let mut addr_fetch_interval = tokio::time::interval(Duration::from_secs(1));
    addr_fetch_interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
    let tx_inventory_interval_secs = if peer_state.connection_type == "inbound" {
        5
    } else {
        2
    };
    let mut tx_inventory_interval =
        tokio::time::interval(Duration::from_secs(tx_inventory_interval_secs));
    tx_inventory_interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
    tx_inventory_interval.tick().await;
    let mut pending_block_requests = Vec::new();
    let mut headers_sync: Option<LowWorkHeadersSync> = None;
    let private_broadcast_timeout = tokio::time::sleep(Duration::from_secs(3 * 60));
    tokio::pin!(private_broadcast_timeout);
    loop {
        if !node.network_active() {
            anyhow::bail!("networking is disabled");
        }
        let message = tokio::select! {
            command = commands.recv() => {
                match command {
                    Some(PeerCommand::Disconnect) | None => anyhow::bail!("peer disconnected by node"),
                    Some(PeerCommand::RequestBlock(hash)) => {
                        let request = Inventory {
                            kind: InventoryType::WitnessBlock,
                            hash,
                        };
                        if node.peer_has_inflight_block_request(peer_id, hash) {
                            send_getdata_batches(
                                node,
                                peer_id,
                                writer,
                                node.config.network,
                                std::slice::from_ref(&request),
                            )
                            .await?;
                        } else {
                            queue_block_requests(&mut pending_block_requests, [request]);
                            flush_pending_block_requests(
                                node,
                                peer_id,
                                writer,
                                node.config.network,
                                &mut pending_block_requests,
                            )
                            .await?;
                        }
                        continue;
                    }
                    Some(PeerCommand::Ping(nonce)) => {
                        send_message(
                            node,
                            peer_id,
                            writer,
                            node.config.network,
                            &Message::Ping(nonce),
                        ).await?;
                        continue;
                    }
                    Some(PeerCommand::SendMessage { command, payload }) => {
                        send_message(
                            node,
                            peer_id,
                            writer,
                            node.config.network,
                            &Message::Unknown { command, payload },
                        )
                        .await?;
                        continue;
                    }
                    Some(PeerCommand::RelayAddresses { addresses }) => {
                        if addresses.is_empty() {
                            continue;
                        }
                        let message = relay_address_message(&addresses, addrv2_received);
                        send_message(node, peer_id, writer, node.config.network, &message).await?;
                        continue;
                    }
                }
            }
            message = reader.read_message(node.config.network) => {
                let (message, bytes) = message?;
                node.record_bytes_received(peer_id, bytes, message.command());
                node.capture_message(peer_id, true, &message)?;
                message
            },
            _ = ping_interval.tick(), if version_received && verack_received && !*peer_state.private_broadcast_peer.lock() => {
                if node.ping_timed_out(peer_id, peer_timeout) {
                    anyhow::bail!("peer ping timed out");
                }
                let nonce = random();
                if node.record_ping(peer_id, nonce) {
                    send_message(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &Message::Ping(nonce),
                    )
                    .await?;
                }
                continue;
            }
            _ = addr_fetch_interval.tick(), if peer_state.connection_type == "addr-fetch" => {
                if addr_fetch_timed_out(addr_fetch_started_at, unix_time_seconds()) {
                    anyhow::bail!("addr-fetch connection timed out");
                }
                continue;
            }
            _ = tx_inventory_interval.tick(), if version_received && verack_received => {
                if *peer_state.private_broadcast_peer.lock() {
                    if peer_state.connection_type != "private-broadcast" {
                        flush_peer_transaction_requests(
                            node,
                            peer_id,
                            peer_state,
                            peers,
                            writer,
                            node.config.network,
                        )
                        .await?;
                    }
                    continue;
                }
                if let Some(staller) = node.take_stalled_block_peer() {
                    node.disconnect_peer(staller);
                }
                if headers_download_timed_out(*peer_state.last_headers_request.lock()) {
                    anyhow::bail!("peer timed out responding to getheaders");
                }
                if node.peer_block_download_timed_out(peer_id) {
                    anyhow::bail!("peer timed out downloading blocks");
                }
                let available = MAX_BLOCKS_IN_TRANSIT_PER_PEER
                    .saturating_sub(node.peer_inflight_block_count(peer_id));
                if available > 0 {
                    let schedule = node.next_block_download_schedule(
                        peer_id,
                        available,
                        peer_services,
                    );
                    let staller = schedule.staller;
                    queue_block_requests(
                        &mut pending_block_requests,
                        schedule.requests,
                    );
                    flush_pending_block_requests(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &mut pending_block_requests,
                    )
                    .await?;
                    if pending_block_requests.is_empty()
                        && let Some(staller) = staller
                    {
                        node.note_block_staller(staller);
                    }
                }
                flush_peer_transaction_inventory(
                    node,
                    peer_id,
                    peer_state,
                    writer,
                    node.config.network,
                )
                .await?;
                flush_peer_transaction_requests(
                    node,
                    peer_id,
                    peer_state,
                    peers,
                    writer,
                    node.config.network,
                )
                .await?;
                continue;
            }
            _ = &mut private_broadcast_timeout, if peer_state.connection_type == "private-broadcast" => {
                anyhow::bail!("private broadcast connection timed out")
            }
        };
        if !version_received && !matches!(&message, Message::Version(_)) {
            // Core ignores application messages until VERSION has been
            // received. In particular, a VERACK received first must not
            // complete the handshake state prematurely.
            continue;
        }
        match message {
            Message::Version(version) => {
                if version_received {
                    anyhow::bail!("duplicate version message");
                }
                version_received = true;
                if version.version < 70001 {
                    anyhow::bail!("peer protocol version is too old");
                }
                if version.nonce == local_nonce {
                    anyhow::bail!("peer connected to itself");
                }
                if peer_state.connection_type == "feeler" {
                    anyhow::bail!("feeler connection completed");
                }
                let private_broadcast_version = version.services == 0
                    && version.timestamp == 0
                    && version.start_height == 0
                    && !version.relay
                    && version.user_agent == "/pynode:0.0.1/";
                if private_broadcast_version {
                    *peer_state.private_broadcast_peer.lock() = true;
                }
                peer_version = version.version;
                peer_services = version.services;
                node.update_peer_version(
                    peer_id,
                    version.version,
                    version.services,
                    &version.user_agent,
                    version.start_height,
                    version.relay,
                );
                node.update_peer_reported_local_address(
                    peer_id,
                    socket_address_from_parts(version.receiver_address, version.receiver_port),
                );
                if peer_state.local_relay_transactions {
                    // Core initializes TxRelay's inventory boundary to one
                    // only after the VERSION handshake creates the relay
                    // state. Keep unversioned getpeerinfo at its zero value.
                    node.record_peer_inv_sequence(peer_id, 1);
                }
                let now = i64::try_from(crate::time::unix_time()).unwrap_or(i64::MAX);
                node.update_peer_time_offset(peer_id, version.timestamp.saturating_sub(now));
                *relay_transactions.lock() = version.relay;
                if !verack_sent {
                    send_peer_extensions(
                        node,
                        peer_id,
                        writer,
                        peer_state,
                        node.config.network,
                        &mut extensions_sent,
                        peer_version,
                    )
                    .await?;
                    send_message(node, peer_id, writer, node.config.network, &Message::Verack)
                        .await?;
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
                send_peer_extensions(
                    node,
                    peer_id,
                    writer,
                    peer_state,
                    node.config.network,
                    &mut extensions_sent,
                    peer_version,
                )
                .await?;
                if *peer_state.private_broadcast_peer.lock() {
                    if let Some(transaction) = peer_state.private_broadcast_transaction.as_ref()
                        && node.private_broadcast_transaction_is_pending(transaction)
                    {
                        send_message(
                            node,
                            peer_id,
                            writer,
                            node.config.network,
                            &Message::Inv(vec![Inventory {
                                kind: InventoryType::Transaction,
                                hash: BlockHash::from_raw_hash(
                                    transaction.compute_txid().to_raw_hash(),
                                ),
                            }]),
                        )
                        .await?;
                    }
                    continue;
                }
                if connection_requests_headers(peer_state.connection_type) {
                    request_headers(node, peer_id, writer, peer_state).await?;
                }
                if connection_fetches_addresses(outbound, peer_state.connection_type) {
                    send_message(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &Message::GetAddr,
                    )
                    .await?;
                    node.grant_peer_address_tokens(peer_id, MAX_ADDR_TO_SEND);
                }
            }
            Message::SendAddrV2 => {
                if verack_received {
                    anyhow::bail!("sendaddrv2 received after verack");
                }
                if peer_version >= WTXID_RELAY_VERSION {
                    addrv2_received = true;
                }
            }
            Message::WtxidRelay => {
                if verack_received {
                    anyhow::bail!("wtxidrelay received after verack");
                }
                if peer_version >= WTXID_RELAY_VERSION && peer_state.local_relay_transactions {
                    *peer_state.wtxid_relay.lock() = true;
                }
            }
            Message::SendTxRcncl(message) => {
                if !node.config.zmq.tx_reconciliation {
                    // Core ignores the offer when reconciliation support is
                    // disabled, preserving compatibility with default nodes.
                    continue;
                }
                if verack_received {
                    anyhow::bail!("sendtxrcncl received after verack");
                }
                if peer_version < WTXID_RELAY_VERSION
                    || peer_state.tx_reconciliation_salt.lock().is_none()
                {
                    continue;
                }
                if !*relay_transactions.lock() {
                    anyhow::bail!("sendtxrcncl received from a non-relaying peer");
                }
                if message.version < TX_RECONCILIATION_VERSION {
                    anyhow::bail!("unsupported transaction reconciliation version");
                }
                let mut registered = peer_state.tx_reconciliation_registered.lock();
                if *registered {
                    anyhow::bail!("duplicate sendtxrcncl message");
                }
                *registered = true;
            }
            Message::Ping(nonce) => {
                send_message(
                    node,
                    peer_id,
                    writer,
                    node.config.network,
                    &Message::Pong(nonce),
                )
                .await?;
            }
            Message::Pong(nonce) => {
                if node.record_pong(peer_id, nonce)
                    && peer_state.connection_type == "private-broadcast"
                    && let Some(transaction) = peer_state.private_broadcast_transaction.as_ref()
                    && let Some(address) = node
                        .peer_infos()
                        .into_iter()
                        .find(|peer| peer.id == peer_id)
                        .map(|peer| peer.address)
                {
                    node.mark_private_broadcast_peer_ack(transaction, address);
                    anyhow::bail!("private broadcast peer acknowledged transaction");
                }
            }
            Message::GetHeaders(request) => {
                if node.chain.read().is_initial_block_download()
                    && !peer_state.permissions.contains(PeerPermissions::DOWNLOAD)
                {
                    send_message(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &Message::Headers(Vec::new()),
                    )
                    .await?;
                    continue;
                }
                let headers = node.chain.read().headers_for_getheaders(
                    &request.locator_hashes,
                    request.stop_hash,
                    STALE_RELAY_AGE_LIMIT_SECS,
                );
                if let Some(headers) = headers {
                    send_message(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &Message::Headers(headers),
                    )
                    .await?;
                }
            }
            Message::GetBlocks(request) => {
                let hashes = {
                    let chain = node.chain.read();
                    chain
                        .headers_after_locator(&request.locator_hashes, request.stop_hash)
                        .into_iter()
                        .filter(|header| chain.store.contains(&header.block_hash()))
                        .take(500)
                        .map(|header| Inventory {
                            kind: InventoryType::Block,
                            hash: header.block_hash(),
                        })
                        .collect::<Vec<_>>()
                };
                send_message(
                    node,
                    peer_id,
                    writer,
                    node.config.network,
                    &Message::Inv(hashes),
                )
                .await?;
            }
            Message::Headers(headers) => {
                let request_more_headers = headers.len() == 2_000;
                *peer_state.last_headers_request.lock() = None;
                if headers.is_empty() {
                    headers_sync = None;
                    continue;
                }

                // Core checks proof of work before allowing a header batch to
                // enter its low-work synchronizer. This keeps cheap invalid
                // headers from consuming the commitment budget.
                if headers
                    .iter()
                    .any(|header| !valid_header_pow(node.config.network, header))
                {
                    continue;
                }

                let mut headers_to_accept = headers;
                let mut request_sync_locator = None;
                let mut sync_finished = false;
                if let Some(sync) = headers_sync.as_mut() {
                    let result = sync.process(&headers_to_accept, request_more_headers);
                    if !result.success {
                        headers_sync = None;
                        continue;
                    }
                    headers_to_accept = result.ready;
                    if result.request_more {
                        let locator = {
                            let chain = node.chain.read();
                            sync.next_locator(&chain)
                        };
                        request_sync_locator = Some(locator);
                    }
                    sync_finished = result.finished;
                } else if request_more_headers {
                    let low_work_state = {
                        let chain = node.chain.read();
                        let parent_hash = headers_to_accept[0].prev_blockhash;
                        chain
                            .header_by_hash(&parent_hash)
                            .zip(chain.chain_work_by_hash(&parent_hash))
                            .map(|(parent_header, parent_work)| {
                                let claimed_work = headers_to_accept
                                    .iter()
                                    .fold(Work::from_be_bytes([0; 32]), |work, header| {
                                        add_work_saturating(work, header.work())
                                    });
                                (
                                    parent_header,
                                    parent_work,
                                    claimed_work,
                                    headers_sync_work_threshold(&chain),
                                )
                            })
                    };
                    if let Some((parent_header, parent_work, claimed_work, threshold)) =
                        low_work_state
                    {
                        if add_work_saturating(parent_work, claimed_work) < threshold {
                            let parent_hash = headers_to_accept[0].prev_blockhash;
                            let (parent_height, parent_mtp) = {
                                let chain = node.chain.read();
                                (
                                    chain.block_height_by_hash(&parent_hash).unwrap_or_default(),
                                    chain
                                        .median_time_past_for_hash(&parent_hash)
                                        .unwrap_or(parent_header.time),
                                )
                            };
                            let mut sync = LowWorkHeadersSync::new(
                                node.config.network,
                                threshold,
                                parent_hash,
                                parent_height,
                                parent_work,
                                parent_header,
                                parent_mtp,
                            );
                            let result = sync.process(&headers_to_accept, request_more_headers);
                            if !result.success {
                                continue;
                            }
                            headers_to_accept = result.ready;
                            if result.request_more {
                                let locator = {
                                    let chain = node.chain.read();
                                    sync.next_locator(&chain)
                                };
                                request_sync_locator = Some(locator);
                            }
                            sync_finished = result.finished;
                            if !sync_finished {
                                headers_sync = Some(sync);
                            }
                        }
                    }
                }

                if sync_finished {
                    headers_sync = None;
                }

                let hashes = node.chain.write().accept_headers(&headers_to_accept)?;
                if let Some(hash) = hashes.last().copied() {
                    node.update_peer_best_known_block(peer_id, hash);
                }
                let requests = {
                    let chain = node.chain.read();
                    hashes
                        .into_iter()
                        .filter(|hash| !chain.store.contains(hash))
                        .map(|hash| Inventory {
                            kind: block_request_inventory_type(peer_services),
                            hash,
                        })
                        .collect::<Vec<_>>()
                };
                if !requests.is_empty() {
                    queue_block_requests(&mut pending_block_requests, requests);
                    flush_pending_block_requests(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &mut pending_block_requests,
                    )
                    .await?;
                }
                if let Some(locator) = request_sync_locator {
                    request_headers_with_locator(node, peer_id, writer, peer_state, locator, true)
                        .await?;
                } else if request_more_headers && headers_sync.is_none() {
                    request_headers(node, peer_id, writer, peer_state).await?;
                }
            }
            Message::Inv(items) => {
                if !peer_state.local_relay_transactions
                    && items.iter().any(|item| item.kind.is_transaction())
                {
                    anyhow::bail!("transaction inventory sent to a non-relaying connection");
                }
                let wtxid_relay = *peer_state.wtxid_relay.lock();
                {
                    let mut known = peer_state.known_tx_inventory.lock();
                    for item in &items {
                        let matching_kind = (wtxid_relay && item.kind.is_witness_transaction())
                            || (!wtxid_relay && item.kind == InventoryType::Transaction);
                        if matching_kind {
                            known.insert(&item.hash);
                        }
                    }
                }
                for item in &items {
                    if matches!(
                        item.kind,
                        InventoryType::Block
                            | InventoryType::WitnessBlock
                            | InventoryType::CompactBlock
                    ) {
                        node.update_peer_best_known_block(peer_id, item.hash);
                    }
                }
                let mut needs_headers = false;
                let transaction_requests = {
                    let chain = node.chain.read();
                    let mempool = node.mempool.read();
                    let initial_block_download = chain.is_initial_block_download();
                    items
                        .into_iter()
                        .filter_map(|item| match item.kind {
                            InventoryType::Block
                            | InventoryType::WitnessBlock
                            | InventoryType::CompactBlock => {
                                // Core treats block inventory as an announcement
                                // of a possible new tip, not as permission to
                                // fetch the advertised body immediately. Asking
                                // for headers first lets the normal headers-first
                                // path validate the chain and schedule bounded
                                // block downloads.
                                if chain.block_height_by_hash(&item.hash).is_none() {
                                    needs_headers = true;
                                }
                                None
                            }
                            kind if kind.is_transaction() => {
                                if initial_block_download {
                                    return None;
                                }
                                if (wtxid_relay && item.kind == InventoryType::Transaction)
                                    || (!wtxid_relay && item.kind.is_witness_transaction())
                                {
                                    return None;
                                }
                                if item.kind.is_witness_transaction() {
                                    mempool
                                        .get_by_wtxid(&Wtxid::from_byte_array(
                                            item.hash.to_byte_array(),
                                        ))
                                        .is_none()
                                        .then_some(item)
                                } else {
                                    mempool
                                        .get(&Txid::from_byte_array(item.hash.to_byte_array()))
                                        .is_none()
                                        .then_some(item)
                                }
                            }
                            _ => None,
                        })
                        .take(50_000)
                        .collect::<Vec<_>>()
                };
                // Core tracks at most this many outstanding transaction
                // announcements from one peer to bound announcement-driven
                // memory and download work.
                let has_wtxid_peer = has_wtxid_relay_peer(peers);
                let now = Instant::now();
                for item in transaction_requests
                    .into_iter()
                    .take(MAX_PEER_TX_ANNOUNCEMENTS)
                {
                    let delay = transaction_request_delay(
                        peer_state.connection_type == "outbound-full",
                        item.kind.is_witness_transaction(),
                        has_wtxid_peer,
                        peer_state.tx_requests.lock().in_flight_count()
                            >= MAX_PEER_TX_REQUEST_IN_FLIGHT,
                    );
                    peer_state.tx_requests.lock().queue(item, now + delay);
                }
                flush_peer_transaction_requests(
                    node,
                    peer_id,
                    peer_state,
                    peers,
                    writer,
                    node.config.network,
                )
                .await?;
                if needs_headers {
                    request_headers(node, peer_id, writer, peer_state).await?;
                }
            }
            Message::GetData(items) => {
                if peer_state.connection_type == "private-broadcast" {
                    let Some(transaction) = peer_state.private_broadcast_transaction.as_ref()
                    else {
                        anyhow::bail!("private broadcast peer requested without a transaction")
                    };
                    if items.len() != 1
                        || items[0].kind != InventoryType::Transaction
                        || items[0].hash
                            != BlockHash::from_raw_hash(transaction.compute_txid().to_raw_hash())
                    {
                        anyhow::bail!("unexpected private broadcast transaction request")
                    }
                    send_message(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &Message::Transaction(transaction.clone()),
                    )
                    .await?;
                    let nonce = random();
                    if node.record_ping(peer_id, nonce) {
                        send_message(
                            node,
                            peer_id,
                            writer,
                            node.config.network,
                            &Message::Ping(nonce),
                        )
                        .await?;
                    }
                    continue;
                }
                let mut missing = Vec::new();
                for item in items {
                    match item.kind {
                        InventoryType::Block | InventoryType::WitnessBlock => {
                            if !node
                                .chain
                                .read()
                                .block_request_allowed(&item.hash, STALE_RELAY_AGE_LIMIT_SECS)
                            {
                                continue;
                            }
                            if node.historical_block_serving_limit_reached(
                                &item.hash,
                                false,
                                peer_state.permissions,
                            ) {
                                anyhow::bail!("historical block serving limit reached");
                            }
                            let block = node.chain.write().block(&item.hash)?;
                            if let Some(block) = block {
                                let block = if item.kind == InventoryType::Block {
                                    block_without_witness(&block)
                                } else {
                                    block
                                };
                                send_message(
                                    node,
                                    peer_id,
                                    writer,
                                    node.config.network,
                                    &Message::Block(block),
                                )
                                .await?;
                            }
                        }
                        InventoryType::CompactBlock => {
                            let (block, recent) = {
                                let mut chain = node.chain.write();
                                if !chain
                                    .block_request_allowed(&item.hash, STALE_RELAY_AGE_LIMIT_SECS)
                                {
                                    continue;
                                }
                                let Some(height) = chain.block_height_by_hash(&item.hash) else {
                                    continue;
                                };
                                let recent = compact_block_is_recent(height, chain.height());
                                let Some(block) = chain.block(&item.hash)? else {
                                    continue;
                                };
                                (block, recent)
                            };
                            if !recent {
                                send_message(
                                    node,
                                    peer_id,
                                    writer,
                                    node.config.network,
                                    &Message::Block(block),
                                )
                                .await?;
                                continue;
                            }
                            let compact = HeaderAndShortIds::from_block(
                                &block,
                                random(),
                                compact_block_version as u32,
                                &[],
                            )?;
                            send_message(
                                node,
                                peer_id,
                                writer,
                                node.config.network,
                                &Message::CompactBlock(compact),
                            )
                            .await?;
                        }
                        InventoryType::FilteredBlock => {
                            if !node
                                .chain
                                .read()
                                .block_request_allowed(&item.hash, STALE_RELAY_AGE_LIMIT_SECS)
                            {
                                continue;
                            }
                            if node.historical_block_serving_limit_reached(
                                &item.hash,
                                true,
                                peer_state.permissions,
                            ) {
                                anyhow::bail!("historical block serving limit reached");
                            }
                            let block = node.chain.write().block(&item.hash)?;
                            let Some(block) = block else { continue };
                            let matching = {
                                let mut filter = bloom_filter.lock();
                                let Some(filter) = filter.as_mut() else {
                                    // Core sends no response when a peer asks
                                    // for a filtered block without first
                                    // loading a bloom filter.
                                    continue;
                                };
                                filter.matched_transaction_ids(&block)
                            };
                            let matching: HashSet<Txid> = matching.into_iter().collect();
                            let merkle = MerkleBlock::from_block_with_predicate(&block, |txid| {
                                matching.contains(txid)
                            });
                            send_message(
                                node,
                                peer_id,
                                writer,
                                node.config.network,
                                &Message::MerkleBlock(merkle),
                            )
                            .await?;
                            for transaction in block.txdata.iter().filter(|transaction| {
                                matching.contains(&transaction.compute_txid())
                            }) {
                                send_message(
                                    node,
                                    peer_id,
                                    writer,
                                    node.config.network,
                                    &Message::Transaction(transaction_without_witness(transaction)),
                                )
                                .await?;
                            }
                        }
                        kind if kind.is_transaction() => {
                            if !peer_state.local_relay_transactions || !*relay_transactions.lock() {
                                missing.push(item);
                                continue;
                            }
                            let last_inv_sequence = node
                                .peer_infos()
                                .into_iter()
                                .find(|peer| peer.id == peer_id)
                                .map(|peer| peer.last_inv_sequence)
                                .unwrap_or(1);
                            let transaction = {
                                let mempool = node.mempool.read();
                                if item.kind.is_witness_transaction() {
                                    mempool
                                        .get_by_wtxid_for_relay(
                                            &Wtxid::from_byte_array(item.hash.to_byte_array()),
                                            last_inv_sequence,
                                        )
                                        .map(|entry| entry.transaction.clone())
                                } else {
                                    mempool
                                        .get_for_relay(
                                            &Txid::from_byte_array(item.hash.to_byte_array()),
                                            last_inv_sequence,
                                        )
                                        .map(|entry| entry.transaction.clone())
                                }
                            };
                            let transaction = if transaction.is_some() {
                                transaction
                            } else {
                                transaction_for_getdata_tip(node, &item)?
                            };
                            if let Some(transaction) = transaction {
                                let txid = transaction.compute_txid();
                                let transaction = if item.kind == InventoryType::Transaction {
                                    transaction_without_witness(&transaction)
                                } else {
                                    transaction
                                };
                                send_message(
                                    node,
                                    peer_id,
                                    writer,
                                    node.config.network,
                                    &Message::Transaction(transaction),
                                )
                                .await?;
                                node.mempool.write().remove_unbroadcast(&txid);
                            } else {
                                missing.push(item);
                            }
                        }
                        _ => {}
                    }
                }
                if !missing.is_empty() {
                    send_message(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &Message::NotFound(missing),
                    )
                    .await?;
                }
            }
            Message::Block(block) => {
                let hash = block.header.block_hash();
                for transaction in &block.txdata {
                    forget_transaction_requests(peers, transaction);
                }
                node.clear_peer_block_request(peer_id, hash);
                if handle_received_block(node, peers, peer_id, block).await {
                    node.record_peer_block(peer_id, hash);
                }
                flush_pending_block_requests(
                    node,
                    peer_id,
                    writer,
                    node.config.network,
                    &mut pending_block_requests,
                )
                .await?;
            }
            Message::CompactBlock(compact) => {
                let hash = compact.header.block_hash();
                node.clear_peer_block_request(peer_id, hash);
                flush_pending_block_requests(
                    node,
                    peer_id,
                    writer,
                    node.config.network,
                    &mut pending_block_requests,
                )
                .await?;
                match reconstruct_compact_block(&compact, node, compact_block_version) {
                    Ok((transactions, missing)) if missing.is_empty() => {
                        match complete_compact_block(&compact, transactions) {
                            Ok(block) => {
                                let block_hash = block.block_hash();
                                for transaction in &block.txdata {
                                    forget_transaction_requests(peers, transaction);
                                }
                                if handle_received_block(node, peers, peer_id, block).await {
                                    node.record_peer_block(peer_id, block_hash);
                                }
                            }
                            Err(error) => {
                                debug!(%hash, %error, "invalid compact block reconstruction");
                                request_full_block(
                                    node,
                                    peer_id,
                                    writer,
                                    node.config.network,
                                    hash,
                                )
                                .await?;
                            }
                        }
                    }
                    Ok((transactions, missing)) => {
                        let request = BlockTransactionsRequest {
                            block_hash: hash,
                            indexes: missing.clone(),
                        };
                        pending_compact = Some(PendingCompactBlock {
                            compact,
                            transactions,
                            requested_indexes: missing,
                        });
                        send_message(
                            node,
                            peer_id,
                            writer,
                            node.config.network,
                            &Message::GetBlockTxn(request),
                        )
                        .await?;
                    }
                    Err(error) => {
                        debug!(%hash, %error, "unable to reconstruct compact block");
                        request_full_block(node, peer_id, writer, node.config.network, hash)
                            .await?;
                    }
                }
            }
            Message::GetBlockTxn(request) => {
                if request.indexes.len() > 100_000 {
                    debug!("compact block transaction request is too large");
                    continue;
                }
                if !compact_block_indexes_are_strictly_increasing(&request.indexes) {
                    anyhow::bail!("compact block transaction indexes are not strictly increasing");
                }
                let (block, recent) = {
                    let mut chain = node.chain.write();
                    if !chain.block_request_allowed(&request.block_hash, STALE_RELAY_AGE_LIMIT_SECS)
                    {
                        continue;
                    }
                    let Some(height) = chain.block_height_by_hash(&request.block_hash) else {
                        continue;
                    };
                    let recent = blocktxn_block_is_recent(height, chain.height());
                    let Some(block) = chain.block(&request.block_hash)? else {
                        continue;
                    };
                    (block, recent)
                };
                if !recent {
                    send_message(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &Message::Block(block),
                    )
                    .await?;
                    continue;
                }
                let Some(transactions) = requested_block_transactions(&block, &request.indexes)
                else {
                    // Core records this as peer misbehavior and returns without
                    // sending a response. There is no score accumulator here,
                    // so keep the connection alive and ignore the request.
                    debug!("compact block transaction index is out of bounds");
                    continue;
                };
                send_message(
                    node,
                    peer_id,
                    writer,
                    node.config.network,
                    &Message::BlockTxn(BlockTransactions {
                        block_hash: request.block_hash,
                        transactions,
                    }),
                )
                .await?;
            }
            Message::BlockTxn(response) => {
                let Some(mut pending) = pending_compact.take() else {
                    continue;
                };
                if response.block_hash != pending.compact.header.block_hash()
                    || response.transactions.len() != pending.requested_indexes.len()
                {
                    request_full_block(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        pending.compact.header.block_hash(),
                    )
                    .await?;
                    continue;
                }
                let mut valid = true;
                for (index, transaction) in pending
                    .requested_indexes
                    .iter()
                    .copied()
                    .zip(response.transactions)
                {
                    let Ok(index) = usize::try_from(index) else {
                        valid = false;
                        break;
                    };
                    let Some(slot) = pending.transactions.get_mut(index) else {
                        valid = false;
                        break;
                    };
                    if slot.is_some() {
                        valid = false;
                        break;
                    }
                    *slot = Some(transaction);
                }
                if !valid || pending.transactions.iter().any(Option::is_none) {
                    request_full_block(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        pending.compact.header.block_hash(),
                    )
                    .await?;
                    continue;
                }
                match complete_compact_block(&pending.compact, pending.transactions) {
                    Ok(block) => {
                        let block_hash = block.block_hash();
                        for transaction in &block.txdata {
                            forget_transaction_requests(peers, transaction);
                        }
                        if handle_received_block(node, peers, peer_id, block).await {
                            node.record_peer_block(peer_id, block_hash);
                        }
                    }
                    Err(error) => {
                        let hash = pending.compact.header.block_hash();
                        debug!(%hash, %error, "invalid compact block completion");
                        request_full_block(node, peer_id, writer, node.config.network, hash)
                            .await?;
                    }
                }
            }
            Message::GetCFilters(request) => {
                validate_basic_filter_request(
                    node,
                    request.filter_type,
                    request.start_height,
                    request.stop_hash,
                    1_000,
                )?;
                let Some(range) =
                    basic_filter_range(node, request.start_height, request.stop_hash, 1_000)?
                else {
                    continue;
                };
                for (block_hash, filter, _) in range.filters {
                    send_message(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &Message::CFilter(CFilter {
                            filter_type: 0,
                            block_hash,
                            filter,
                        }),
                    )
                    .await?;
                }
            }
            Message::GetCFHeaders(request) => {
                validate_basic_filter_request(
                    node,
                    request.filter_type,
                    request.start_height,
                    request.stop_hash,
                    2_000,
                )?;
                let Some(range) =
                    basic_filter_range(node, request.start_height, request.stop_hash, 2_000)?
                else {
                    continue;
                };
                let filter_hashes = range
                    .filters
                    .iter()
                    .map(|(_, filter, _)| FilterHash::hash(filter))
                    .collect();
                let stop_hash = range
                    .filters
                    .last()
                    .map(|(hash, _, _)| *hash)
                    .unwrap_or(range.stop_hash);
                send_message(
                    node,
                    peer_id,
                    writer,
                    node.config.network,
                    &Message::CFHeaders(CFHeaders {
                        filter_type: 0,
                        stop_hash,
                        previous_filter_header: range.previous_filter_header,
                        filter_hashes,
                    }),
                )
                .await?;
            }
            Message::GetCFCheckpt(request) => {
                validate_basic_filter_request(
                    node,
                    request.filter_type,
                    0,
                    request.stop_hash,
                    u32::MAX,
                )?;
                let (stop_hash, filter_headers) = {
                    let mut chain = node.chain.write();
                    let stop_hash = request.stop_hash;
                    let stop_height = chain.block_height_by_hash(&stop_hash).ok_or_else(|| {
                        anyhow::anyhow!("compact filter stop block is unavailable")
                    })?;
                    let filter_headers = compact_filter_checkpoint_heights(stop_height)
                        .map(|height| {
                            let block_hash = chain
                                .ancestor_hash_at_height(&stop_hash, height)
                                .ok_or_else(|| {
                                    anyhow::anyhow!("compact filter height is out of range")
                                })?;
                            chain
                                .basic_filter_header_for_block(&block_hash)?
                                .ok_or_else(|| anyhow::anyhow!("compact filter is missing"))
                        })
                        .collect::<Result<Vec<_>>>()?;
                    (stop_hash, filter_headers)
                };
                send_message(
                    node,
                    peer_id,
                    writer,
                    node.config.network,
                    &Message::CFCheckpt(CFCheckpt {
                        filter_type: 0,
                        stop_hash,
                        filter_headers,
                    }),
                )
                .await?;
            }
            Message::Transaction(transaction) => {
                let privately_broadcast = node.mark_private_broadcast_received(&transaction);
                if privately_broadcast {
                    debug!(
                        txid = %transaction.compute_txid(),
                        "received privately broadcast transaction back from the network"
                    );
                }
                if !peer_state.local_relay_transactions {
                    anyhow::bail!("transaction sent to a non-relaying connection");
                }
                let txid = transaction.compute_txid();
                forget_transaction_requests(peers, &transaction);
                if node.chain.read().is_initial_block_download() {
                    continue;
                }
                let known_hash = if *peer_state.wtxid_relay.lock() {
                    BlockHash::from_raw_hash(transaction.compute_wtxid().to_raw_hash())
                } else {
                    BlockHash::from_raw_hash(transaction.compute_txid().to_raw_hash())
                };
                peer_state.known_tx_inventory.lock().insert(&known_hash);
                let transaction_for_force_relay = transaction.clone();
                match node.accept_peer_transaction_from(peer_id, transaction) {
                    Ok(_) => {
                        node.record_peer_transaction(peer_id);
                        debug!(%txid, "accepted peer transaction");
                    }
                    Err(error) => {
                        if peer_state
                            .permissions
                            .contains(PeerPermissions::FORCE_RELAY)
                            && node.mempool.read().get(&txid).is_some()
                        {
                            node.notify_mempool_transaction_force_from_peer(
                                transaction_for_force_relay,
                                peer_id,
                            );
                        }
                        if let Some(MempoolError::MissingInput(outpoint)) =
                            error.downcast_ref::<MempoolError>()
                        {
                            let parent_txid = outpoint.txid;
                            let in_mempool = node.mempool.read().get(&parent_txid).is_some();
                            let in_chain = if in_mempool {
                                true
                            } else {
                                node.chain.write().transaction(&parent_txid)?.is_some()
                            };
                            if !in_chain && {
                                let parent = Inventory {
                                    // Orphan parent fetching uses MSG_TX
                                    // even when wtxid relay is negotiated.
                                    kind: InventoryType::Transaction,
                                    hash: BlockHash::from_raw_hash(parent_txid.to_raw_hash()),
                                };
                                let delay = transaction_request_delay(
                                    peer_state.connection_type == "outbound-full",
                                    false,
                                    has_wtxid_relay_peer(peers),
                                    peer_state.tx_requests.lock().in_flight_count()
                                        >= MAX_PEER_TX_REQUEST_IN_FLIGHT,
                                );
                                peer_state
                                    .tx_requests
                                    .lock()
                                    .queue(parent, Instant::now() + delay)
                            } {
                                flush_peer_transaction_requests(
                                    node,
                                    peer_id,
                                    peer_state,
                                    peers,
                                    writer,
                                    node.config.network,
                                )
                                .await?;
                            }
                        }
                        debug!(%txid, %error, "rejected peer transaction");
                    }
                }
                flush_peer_transaction_requests(
                    node,
                    peer_id,
                    peer_state,
                    peers,
                    writer,
                    node.config.network,
                )
                .await?;
            }
            Message::FilterLoad(filter) => {
                if !node.config.peer_bloom_filters
                    && !peer_state
                        .permissions
                        .contains(PeerPermissions::BLOOM_FILTER)
                {
                    anyhow::bail!("filterload received while bloom filters are disabled");
                }
                if let Err(error) = install_bloom_filter(bloom_filter, relay_transactions, filter) {
                    // Core records an invalid filter as peer misbehavior but keeps
                    // the connection alive. This node has no score-based
                    // discouragement subsystem, so retain the socket and log it.
                    debug!(peer_id, %error, "ignoring malformed bloom filter");
                } else {
                    node.update_peer_relay_transactions(peer_id, true);
                }
            }
            Message::FilterAdd(FilterAdd { data }) => {
                if !node.config.peer_bloom_filters
                    && !peer_state
                        .permissions
                        .contains(PeerPermissions::BLOOM_FILTER)
                {
                    anyhow::bail!("filteradd received while bloom filters are disabled");
                }
                if !apply_bloom_filter_add(bloom_filter, &data) {
                    // Core marks an oversized element or an add before
                    // filterload as misbehavior without immediately closing the
                    // connection. Keep processing later messages.
                    debug!(peer_id, "ignoring malformed bloom filter element");
                }
            }
            Message::FilterClear => {
                if !node.config.peer_bloom_filters
                    && !peer_state
                        .permissions
                        .contains(PeerPermissions::BLOOM_FILTER)
                {
                    anyhow::bail!("filterclear received while bloom filters are disabled");
                }
                clear_bloom_filter(bloom_filter, relay_transactions);
                node.update_peer_relay_transactions(peer_id, true);
            }
            Message::MerkleBlock(_) => {}
            Message::Addr(addresses) => {
                if addresses.len() > MAX_ADDR_TO_SEND {
                    bail!("addr message contains too many addresses");
                }
                if peer_state.connection_type == "addr-fetch" && addresses.len() > 1 {
                    bail!("addr-fetch connection received too many addresses");
                }
                node.enable_peer_address_relay(peer_id);
                let mut relay_addresses = Vec::new();
                for entry in addresses {
                    if let Some(address) = socket_address_from_legacy(&entry)
                        && node.allow_peer_address(peer_id)
                    {
                        let endpoint = NetworkEndpoint::from_socket(address);
                        if node.remember_network_address(
                            endpoint.clone(),
                            entry.services,
                            u64::from(entry.time),
                        ) {
                            relay_addresses.push((endpoint, entry.services, u64::from(entry.time)));
                        }
                    }
                }
                node.relay_peer_addresses(peer_id, relay_addresses);
            }
            Message::AddrV2(addresses) => {
                if addresses.len() > MAX_ADDR_TO_SEND {
                    bail!("addrv2 message contains too many addresses");
                }
                if peer_state.connection_type == "addr-fetch" && addresses.len() > 1 {
                    bail!("addr-fetch connection received too many addresses");
                }
                node.enable_peer_address_relay(peer_id);
                let mut relay_addresses = Vec::new();
                for address in addresses {
                    if let Some(endpoint) = NetworkEndpoint::from_addr_v2(
                        address.network,
                        &address.address,
                        address.port,
                    ) && node.allow_peer_address(peer_id)
                        && node.remember_network_address(
                            endpoint.clone(),
                            address.services,
                            u64::from(address.time),
                        )
                    {
                        relay_addresses.push((endpoint, address.services, u64::from(address.time)));
                    }
                }
                node.relay_peer_addresses(peer_id, relay_addresses);
            }
            Message::SendHeaders => {
                *peer_state.send_headers.lock() = true;
            }
            Message::CFilter(_)
            | Message::CFHeaders(_)
            | Message::CFCheckpt(_)
            | Message::Unknown { .. } => {}
            Message::NotFound(items) => {
                for item in items {
                    if item.kind.is_transaction() {
                        peer_state.tx_requests.lock().remove_inventory(&item);
                    }
                    if matches!(
                        item.kind,
                        InventoryType::Block
                            | InventoryType::WitnessBlock
                            | InventoryType::CompactBlock
                    ) {
                        node.clear_peer_block_request(peer_id, item.hash);
                    }
                }
                flush_pending_block_requests(
                    node,
                    peer_id,
                    writer,
                    node.config.network,
                    &mut pending_block_requests,
                )
                .await?;
                flush_peer_transaction_requests(
                    node,
                    peer_id,
                    peer_state,
                    peers,
                    writer,
                    node.config.network,
                )
                .await?;
            }
            Message::FeeFilter(rate) => {
                if peer_state
                    .permissions
                    .contains(PeerPermissions::FORCE_RELAY)
                {
                    continue;
                }
                let rate = rate.max(0);
                *fee_filter.lock() = rate;
                node.update_peer_fee_filter(peer_id, rate);
            }
            Message::SendCmpct { announce, version } => {
                if version == 1 || version == 2 {
                    compact_block_version = version;
                    *peer_state.compact_block_version.lock() = Some(version);
                    *peer_state.compact_block_announce.lock() = announce;
                    node.update_peer_bip152_highbandwidth_from(peer_id, announce);
                }
            }
            Message::GetAddr => {
                if outbound || getaddr_received {
                    continue;
                }
                getaddr_received = true;
                node.enable_peer_address_relay(peer_id);
                let mut addresses = node.known_network_addresses();
                addresses.shuffle(&mut rand::rng());
                addresses.truncate(MAX_ADDR_TO_SEND);
                if addrv2_received {
                    let addresses = addresses
                        .into_iter()
                        .filter_map(|entry| {
                            network_address_v2(&entry.endpoint, entry.time, entry.services)
                        })
                        .collect::<Vec<_>>();
                    send_message(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &Message::AddrV2(addresses),
                    )
                    .await?;
                } else {
                    let addresses = addresses
                        .into_iter()
                        .filter_map(|entry| {
                            entry.endpoint.legacy_socket_addr().map(|address| {
                                wire::NetworkAddress {
                                    time: u32::try_from(entry.time).unwrap_or(u32::MAX),
                                    services: entry.services,
                                    address: socket_address_bytes(address),
                                    port: address.port(),
                                }
                            })
                        })
                        .collect::<Vec<_>>();
                    send_message(
                        node,
                        peer_id,
                        writer,
                        node.config.network,
                        &Message::Addr(addresses),
                    )
                    .await?;
                }
            }
            Message::Mempool => {
                if !peer_can_request_mempool(node.config.peer_bloom_filters, peer_state.permissions)
                {
                    if !peer_state.permissions.contains(PeerPermissions::NO_BAN) {
                        anyhow::bail!("mempool request received while bloom filters are disabled");
                    }
                    // Core ignores this request for a noban peer instead of
                    // disconnecting it. There is no mempool response to send.
                    debug!(
                        peer_id,
                        "ignoring unauthorized mempool request from noban peer"
                    );
                    continue;
                }
                let transactions = {
                    let mempool = node.mempool.read();
                    let minimum_fee = if peer_state
                        .permissions
                        .contains(PeerPermissions::FORCE_RELAY)
                    {
                        0
                    } else {
                        *fee_filter.lock()
                    };
                    mempool
                        .main_order()
                        .into_iter()
                        .filter_map(|txid| {
                            mempool.get(&txid).and_then(|entry| {
                                let fee_rate = fee_rate_sat_per_kvb(entry.fee_sat, entry.vsize);
                                (fee_rate >= minimum_fee).then(|| entry.transaction.clone())
                            })
                        })
                        .take(50_000)
                        .collect::<Vec<_>>()
                };
                let inventory = {
                    let mut filter = bloom_filter.lock();
                    let wtxid_relay = *peer_state.wtxid_relay.lock();
                    let mut known = peer_state.known_tx_inventory.lock();
                    transactions
                        .into_iter()
                        .filter_map(|transaction| {
                            if let Some(filter) = filter.as_mut()
                                && !filter.is_relevant_and_update(&transaction)
                            {
                                return None;
                            }
                            let item = transaction_inventory(&transaction, wtxid_relay);
                            if known.contains(&item.hash) {
                                return None;
                            }
                            known.insert(&item.hash);
                            Some(item)
                        })
                        .collect::<Vec<_>>()
                };
                let mempool_sequence = node.mempool.read().sequence();
                send_message(
                    node,
                    peer_id,
                    writer,
                    node.config.network,
                    &Message::Inv(inventory),
                )
                .await?;
                node.record_peer_inv_sequence(peer_id, mempool_sequence);
            }
        }
        if version_received && verack_received && !verack_sent {
            send_message(node, peer_id, writer, node.config.network, &Message::Verack).await?;
            verack_sent = true;
        }
    }
}

fn validate_basic_filter_request(
    node: &Arc<Node>,
    filter_type: u8,
    start_height: u32,
    stop_hash: BlockHash,
    max_height_diff: u32,
) -> Result<()> {
    if !(node.config.blockfilterindex && node.config.peer_block_filters) || filter_type != 0 {
        anyhow::bail!("peer requested unsupported block filter type")
    }
    let chain = node.chain.read();
    if !chain.block_request_allowed(&stop_hash, STALE_RELAY_AGE_LIMIT_SECS) {
        anyhow::bail!("peer requested invalid block hash")
    }
    let Some(stop_height) = chain.block_height_by_hash(&stop_hash) else {
        anyhow::bail!("peer requested invalid block hash")
    };
    if start_height > stop_height {
        anyhow::bail!(
            "peer sent invalid getcfilters/getcfheaders with start height {start_height} and stop height {stop_height}"
        )
    }
    if stop_height.saturating_sub(start_height) >= max_height_diff {
        anyhow::bail!(
            "peer requested too many cfilters/cfheaders: {} / {max_height_diff}",
            stop_height.saturating_sub(start_height).saturating_add(1)
        )
    }
    Ok(())
}

fn basic_filter_range(
    node: &Arc<Node>,
    start_height: u32,
    requested_stop_hash: BlockHash,
    limit: usize,
) -> Result<Option<BasicFilterRange>> {
    let mut chain = node.chain.write();
    let stop_hash = requested_stop_hash;
    let Some(stop_height) = chain.block_height_by_hash(&stop_hash) else {
        return Ok(None);
    };
    if start_height > stop_height || limit == 0 {
        return Ok(None);
    }
    let Some(range) = chain.basic_filter_range(start_height, stop_hash, limit)? else {
        return Ok(None);
    };
    Ok(Some(range))
}

async fn handle_received_block(
    node: &Arc<Node>,
    peers: &PeerRegistry,
    peer_id: usize,
    block: Block,
) -> bool {
    let hash = block.block_hash();
    let (was_stored, previous_tip) = {
        let chain = node.chain.read();
        (chain.store.contains(&hash), chain.best_hash())
    };
    match node.connect_block(block) {
        Ok(tip) => {
            info!(%hash, height = tip.height, "accepted peer block");
            node.update_peer_best_known_block(peer_id, hash);
            // Active-tip updates are announced by the chain-event relay. A
            // side-chain block has no tip event, so relay a newly accepted
            // side-chain block here. Avoid announcing duplicate blocks.
            if !was_stored
                && tip.hash == previous_tip
                && hash != previous_tip
                && !node.chain.read().is_initial_block_download()
            {
                broadcast_inventory(
                    node,
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
            true
        }
        Err(error) => {
            debug!(%hash, %error, "rejected peer block");
            false
        }
    }
}

async fn request_full_block(
    node: &Arc<Node>,
    peer_id: usize,
    writer: &PeerWriter,
    network: Network,
    hash: BlockHash,
) -> Result<()> {
    if !node.track_peer_block_request(peer_id, hash) {
        return Ok(());
    }
    send_message(
        node,
        peer_id,
        writer,
        network,
        &Message::GetData(vec![Inventory {
            kind: InventoryType::WitnessBlock,
            hash,
        }]),
    )
    .await
}

async fn flush_pending_block_requests(
    node: &Arc<Node>,
    peer_id: usize,
    writer: &PeerWriter,
    network: Network,
    pending: &mut Vec<Inventory>,
) -> Result<()> {
    let available =
        MAX_BLOCKS_IN_TRANSIT_PER_PEER.saturating_sub(node.peer_inflight_block_count(peer_id));
    if available == 0 || pending.is_empty() {
        return Ok(());
    }

    let queued = std::mem::take(pending);
    let mut requests = Vec::with_capacity(available);
    let mut remaining = Vec::new();
    for request in queued {
        if node.peer_inflight_block_count(peer_id) >= MAX_BLOCKS_IN_TRANSIT_PER_PEER
            || requests.len() >= available
        {
            remaining.push(request);
            continue;
        }
        if node.track_peer_block_request(peer_id, request.hash) {
            requests.push(request);
        }
    }
    *pending = remaining;
    send_getdata_batches(node, peer_id, writer, network, &requests).await
}

async fn send_getdata_batches(
    node: &Arc<Node>,
    peer_id: usize,
    writer: &PeerWriter,
    network: Network,
    requests: &[Inventory],
) -> Result<()> {
    for batch in getdata_batches(requests) {
        send_message(
            node,
            peer_id,
            writer,
            network,
            &Message::GetData(batch.to_vec()),
        )
        .await?;
    }
    Ok(())
}

fn reconstruct_compact_block(
    compact: &HeaderAndShortIds,
    node: &Arc<Node>,
    version: u64,
) -> Result<(Vec<Option<Transaction>>, Vec<u64>)> {
    if version != 1 && version != 2 {
        anyhow::bail!("unsupported compact block version {version}");
    }
    let transaction_count = compact
        .short_ids
        .len()
        .checked_add(compact.prefilled_txs.len())
        .ok_or_else(|| anyhow::anyhow!("compact block transaction count overflow"))?;
    if transaction_count == 0 || transaction_count > 1_000_000 {
        anyhow::bail!("invalid compact block transaction count");
    }
    let mut transactions = vec![None; transaction_count];
    let mut last_prefilled = 0usize;
    for prefilled in &compact.prefilled_txs {
        let index = last_prefilled
            .checked_add(prefilled.idx as usize)
            .ok_or_else(|| anyhow::anyhow!("compact block prefilled index overflow"))?;
        if index >= transaction_count || transactions[index].is_some() {
            anyhow::bail!("invalid compact block prefilled index");
        }
        transactions[index] = Some(prefilled.tx.clone());
        last_prefilled = index.saturating_add(1);
    }

    let siphash_keys = ShortId::calculate_siphash_keys(&compact.header, compact.nonce);
    let mut candidates: HashMap<ShortId, Option<Transaction>> = HashMap::new();
    let mempool = node.mempool.read();
    for transaction in mempool.transactions() {
        add_compact_candidate(&mut candidates, transaction, version, siphash_keys);
    }
    drop(mempool);
    for transaction in node.compact_extra_transactions() {
        add_compact_candidate(&mut candidates, &transaction, version, siphash_keys);
    }

    let mut missing = Vec::new();
    let mut short_ids = compact.short_ids.iter();
    for (index, transaction) in transactions.iter_mut().enumerate() {
        if transaction.is_some() {
            continue;
        }
        let Some(short_id) = short_ids.next() else {
            anyhow::bail!("compact block short-id count is inconsistent");
        };
        match candidates.get(short_id) {
            Some(Some(candidate)) => *transaction = Some(candidate.clone()),
            _ => missing.push(index as u64),
        }
    }
    if short_ids.next().is_some() {
        anyhow::bail!("compact block has too many short ids");
    }
    Ok((transactions, missing))
}

fn add_compact_candidate(
    candidates: &mut HashMap<ShortId, Option<Transaction>>,
    transaction: &Transaction,
    version: u64,
    siphash_keys: (u64, u64),
) {
    let short_id = compact_short_id(transaction, version, siphash_keys);
    match candidates.entry(short_id) {
        std::collections::hash_map::Entry::Vacant(entry) => {
            entry.insert(Some(transaction.clone()));
        }
        std::collections::hash_map::Entry::Occupied(mut entry) => {
            if entry
                .get()
                .as_ref()
                .is_some_and(|candidate| candidate == transaction)
            {
                return;
            }
            entry.insert(None);
        }
    }
}

fn compact_short_id(transaction: &Transaction, version: u64, siphash_keys: (u64, u64)) -> ShortId {
    match version {
        1 => ShortId::with_siphash_keys(&transaction.compute_txid().to_raw_hash(), siphash_keys),
        2 => ShortId::with_siphash_keys(&transaction.compute_wtxid().to_raw_hash(), siphash_keys),
        _ => unreachable!("compact block version validated by caller"),
    }
}

fn complete_compact_block(
    compact: &HeaderAndShortIds,
    transactions: Vec<Option<Transaction>>,
) -> Result<Block> {
    let txdata = transactions
        .into_iter()
        .collect::<Option<Vec<Transaction>>>()
        .ok_or_else(|| anyhow::anyhow!("compact block still has missing transactions"))?;
    let block = Block {
        header: compact.header,
        txdata,
    };
    if block.block_hash() != compact.header.block_hash() {
        anyhow::bail!("compact block header hash changed during reconstruction");
    }
    Ok(block)
}

fn advertised_local_address(node: &Node, peer: &PeerState) -> Option<SocketAddr> {
    let peer_network = peer.endpoint.network_name();
    let matches_peer_network = |address: SocketAddr| {
        let endpoint = NetworkEndpoint::from_socket(address);
        peer_network == "not_publicly_routable" || endpoint.network_name() == peer_network
    };
    let usable = |address: SocketAddr| {
        (is_core_routable_ip(address.ip())
            || (NetworkEndpoint::from_socket(address).network_name() == "cjdns"
                && node.config.cjdns_reachable))
            && node.config.allows_address(address)
            && matches_peer_network(address)
    };
    node.config
        .external_addresses
        .iter()
        .copied()
        .find(|address| usable(*address))
        .or_else(|| {
            node.mapped_addresses()
                .into_iter()
                .find(|address| usable(*address))
        })
        .or_else(|| {
            node.config
                .discover
                .then_some(peer.local_address)
                .flatten()
                .filter(|address| usable(*address))
        })
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

fn socket_address_from_parts(address: [u8; 16], port: u16) -> Option<std::net::SocketAddr> {
    let ip = if address[..10] == [0; 10] && address[10..12] == [0xff, 0xff] {
        std::net::IpAddr::V4(std::net::Ipv4Addr::new(
            address[12],
            address[13],
            address[14],
            address[15],
        ))
    } else {
        std::net::IpAddr::V6(std::net::Ipv6Addr::from(address))
    };
    (port != 0).then(|| std::net::SocketAddr::new(ip, port))
}

fn socket_address_from_legacy(address: &wire::NetworkAddress) -> Option<std::net::SocketAddr> {
    socket_address_from_parts(address.address, address.port)
}

fn network_address_v2(
    endpoint: &NetworkEndpoint,
    connected_at: u64,
    services: u64,
) -> Option<wire::NetworkAddressV2> {
    let (network, address) = endpoint.to_addr_v2()?;
    Some(wire::NetworkAddressV2 {
        time: u32::try_from(connected_at).unwrap_or(u32::MAX),
        services,
        network,
        address,
        port: endpoint.port(),
    })
}

async fn send_peer_extensions(
    node: &Arc<Node>,
    peer_id: usize,
    writer: &PeerWriter,
    peer_state: &PeerState,
    network: Network,
    sent: &mut bool,
    peer_version: i32,
) -> Result<()> {
    if *sent {
        return Ok(());
    }
    if *peer_state.private_broadcast_peer.lock() {
        *sent = true;
        return Ok(());
    }
    if peer_version >= SENDHEADERS_VERSION {
        send_message(node, peer_id, writer, network, &Message::SendHeaders).await?;
    }
    if peer_version >= WTXID_RELAY_VERSION {
        if peer_state.local_relay_transactions {
            send_message(node, peer_id, writer, network, &Message::WtxidRelay).await?;
        }
        send_message(node, peer_id, writer, network, &Message::SendAddrV2).await?;
        if node.config.zmq.tx_reconciliation
            && *peer_state.relay_transactions.lock()
            && peer_state.local_relay_transactions
            && peer_state.connection_type != "addr-fetch"
            && peer_state.connection_type != "feeler"
        {
            let salt = random::<u64>();
            send_message(
                node,
                peer_id,
                writer,
                network,
                &Message::SendTxRcncl(SendTxRcnclMessage {
                    version: TX_RECONCILIATION_VERSION,
                    salt,
                }),
            )
            .await?;
            *peer_state.tx_reconciliation_salt.lock() = Some(salt);
        }
    }
    if peer_version >= SHORT_IDS_BLOCKS_VERSION {
        send_message(
            node,
            peer_id,
            writer,
            network,
            &Message::SendCmpct {
                announce: false,
                version: 2,
            },
        )
        .await?;
    }
    if peer_version >= FEEFILTER_VERSION {
        let relay_fee =
            i64::try_from(node.mempool.write().mempool_min_fee_sat_per_kvb()).unwrap_or(i64::MAX);
        send_message(
            node,
            peer_id,
            writer,
            network,
            &Message::FeeFilter(relay_fee),
        )
        .await?;
    }
    *sent = true;
    Ok(())
}

async fn request_headers(
    node: &Arc<Node>,
    peer_id: usize,
    writer: &PeerWriter,
    peer_state: &PeerState,
) -> Result<()> {
    let locator = node.chain.read().block_locator_hashes();
    request_headers_with_locator(node, peer_id, writer, peer_state, locator, false).await
}

async fn request_headers_with_locator(
    node: &Arc<Node>,
    peer_id: usize,
    writer: &PeerWriter,
    peer_state: &PeerState,
    locator: Vec<BlockHash>,
    force: bool,
) -> Result<()> {
    {
        let mut last_request = peer_state.last_headers_request.lock();
        if !force && !headers_request_is_due(*last_request) {
            return Ok(());
        }
        *last_request = Some(Instant::now());
    }
    send_message(
        node,
        peer_id,
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

async fn send_message(
    node: &Arc<Node>,
    peer_id: usize,
    writer: &PeerWriter,
    network: Network,
    message: &Message,
) -> Result<()> {
    let mut writer = writer.lock().await;
    let bytes = match &mut *writer {
        PeerWriterKind::V1(writer) => {
            wire::write_message_with_size(writer, network, message).await?
        }
        PeerWriterKind::V2(writer) => {
            let contents = wire::encode_v2_message(message)?;
            let bytes = contents.len().saturating_add(20);
            writer.write(&Payload::genuine(contents)).await?;
            bytes
        }
    };
    node.capture_message(peer_id, false, message)?;
    node.record_bytes_sent(peer_id, bytes, message.command());
    Ok(())
}

fn relay_address_message(
    addresses: &[(NetworkEndpoint, u64, u64)],
    addrv2_received: bool,
) -> Message {
    if addrv2_received {
        Message::AddrV2(
            addresses
                .iter()
                .filter_map(|(endpoint, services, time)| {
                    network_address_v2(endpoint, *time, *services)
                })
                .collect(),
        )
    } else {
        Message::Addr(
            addresses
                .iter()
                .filter_map(|(endpoint, services, time)| {
                    endpoint
                        .legacy_socket_addr()
                        .map(|address| wire::NetworkAddress {
                            time: u32::try_from(*time).unwrap_or(u32::MAX),
                            services: *services,
                            address: socket_address_bytes(address),
                            port: address.port(),
                        })
                })
                .collect(),
        )
    }
}

async fn broadcast_inventory(
    node: &Arc<Node>,
    peers: &PeerRegistry,
    excluded_peer: usize,
    network: Network,
    item: Inventory,
) {
    broadcast_inventory_excluding(node, peers, &[excluded_peer], network, false, item).await;
}

fn queue_peer_transaction_inventory(
    node: &Arc<Node>,
    peer_id: usize,
    state: &PeerState,
    item: Inventory,
) {
    let count = {
        let mut pending = state.pending_tx_inventory.lock();
        if !pending
            .iter()
            .any(|candidate| candidate.kind == item.kind && candidate.hash == item.hash)
        {
            pending.push(item);
        }
        pending.len()
    };
    node.set_peer_inv_to_send(peer_id, count);
}

fn transaction_request_delay(
    preferred: bool,
    witness: bool,
    has_wtxid_peer: bool,
    overloaded: bool,
) -> Duration {
    let mut delay = Duration::ZERO;
    if !preferred {
        delay += NONPREF_PEER_TX_DELAY;
    }
    if !witness && has_wtxid_peer {
        delay += TXID_RELAY_DELAY;
    }
    if overloaded {
        delay += OVERLOADED_PEER_TX_DELAY;
    }
    delay
}

fn has_wtxid_relay_peer(peers: &PeerRegistry) -> bool {
    peers.lock().values().any(|state| *state.wtxid_relay.lock())
}

fn tx_request_owned_by_other_peer(
    peers: &PeerRegistry,
    peer_id: usize,
    key: TxRequestKey,
    now: Instant,
) -> bool {
    peers.lock().iter().any(|(other_id, state)| {
        *other_id != peer_id && state.tx_requests.lock().has_live_in_flight(key, now)
    })
}

fn forget_transaction_requests(peers: &PeerRegistry, transaction: &Transaction) {
    for state in peers.lock().values() {
        state.tx_requests.lock().remove_transaction(transaction);
    }
}

async fn flush_peer_transaction_requests(
    node: &Arc<Node>,
    peer_id: usize,
    state: &PeerState,
    peers: &PeerRegistry,
    writer: &PeerWriter,
    network: Network,
) -> Result<()> {
    let now = Instant::now();
    let available = {
        let mut requests = state.tx_requests.lock();
        requests.expire(now);
        MAX_PEER_TX_REQUEST_IN_FLIGHT.saturating_sub(requests.in_flight_count())
    };
    if available == 0 {
        return Ok(());
    }

    let candidates = state.tx_requests.lock().take_ready(now, available);
    let mut requests = Vec::with_capacity(candidates.len());
    for candidate in candidates {
        if tx_request_owned_by_other_peer(peers, peer_id, candidate.key, now) {
            let ready_at = candidate.ready_at;
            state.tx_requests.lock().requeue(candidate, ready_at);
            continue;
        }
        state.tx_requests.lock().mark_sent(&candidate, now);
        requests.push(candidate.item);
    }
    send_getdata_batches(node, peer_id, writer, network, &requests).await
}

async fn flush_peer_transaction_inventory(
    node: &Arc<Node>,
    peer_id: usize,
    state: &PeerState,
    writer: &PeerWriter,
    network: Network,
) -> Result<()> {
    if !*state.relay_transactions.lock() {
        state.pending_tx_inventory.lock().clear();
        node.set_peer_inv_to_send(peer_id, 0);
        return Ok(());
    }

    let pending = {
        let mut pending = state.pending_tx_inventory.lock();
        if pending.is_empty() {
            return Ok(());
        }
        let limit = inventory_broadcast_limit(pending.len());
        let count = pending.len().min(limit);
        pending.drain(..count).collect::<Vec<_>>()
    };
    node.set_peer_inv_to_send(peer_id, state.pending_tx_inventory.lock().len());

    let wtxid_relay = *state.wtxid_relay.lock();
    let minimum_fee = if state.permissions.contains(PeerPermissions::FORCE_RELAY) {
        0
    } else {
        *state.fee_filter.lock()
    };
    let mut inventory = Vec::with_capacity(pending.len());
    for queued in pending {
        let Some(transaction) = transaction_for_inventory(node, &queued) else {
            continue;
        };
        let item = transaction_inventory(&transaction, wtxid_relay);
        if let Some((fee_sat, vsize)) = transaction_fee_for_inventory(node, &item)
            && fee_rate_sat_per_kvb(fee_sat, vsize) < minimum_fee
        {
            continue;
        }
        {
            let mut filter = state.bloom_filter.lock();
            if let Some(filter) = filter.as_mut()
                && !filter.is_relevant_and_update(&transaction)
            {
                continue;
            }
        }
        {
            let mut known = state.known_tx_inventory.lock();
            if known.contains(&item.hash) {
                continue;
            }
            known.insert(&item.hash);
        }
        inventory.push(item);
    }

    for chunk in inventory.chunks(MAX_TX_INVENTORY_BATCH) {
        send_message(
            node,
            peer_id,
            writer,
            network,
            &Message::Inv(chunk.to_vec()),
        )
        .await?;
    }
    node.record_peer_inv_sequence(peer_id, node.mempool.read().sequence());
    let remaining = state.pending_tx_inventory.lock().len();
    node.set_peer_inv_to_send(peer_id, remaining);
    Ok(())
}

async fn broadcast_inventory_excluding(
    node: &Arc<Node>,
    peers: &PeerRegistry,
    excluded_peers: &[usize],
    network: Network,
    force_relay: bool,
    item: Inventory,
) {
    let transaction = if item.kind.is_transaction() {
        transaction_for_inventory(node, &item)
    } else {
        None
    };
    if item.kind.is_transaction() && transaction.is_none() {
        return;
    }
    let recipients: Vec<(usize, Arc<PeerState>)> = peers
        .lock()
        .iter()
        .filter(|(peer_id, _)| {
            excluded_peers
                .iter()
                .all(|excluded_peer| **peer_id != *excluded_peer)
        })
        .map(|(peer_id, state)| (*peer_id, state.clone()))
        .collect();
    for (peer_id, state) in recipients {
        let item = transaction
            .as_ref()
            .map(|transaction| transaction_inventory(transaction, *state.wtxid_relay.lock()))
            .unwrap_or_else(|| item.clone());
        if matches!(
            item.kind,
            InventoryType::Block | InventoryType::WitnessBlock | InventoryType::CompactBlock
        ) {
            let compact_version = *state.compact_block_version.lock();
            let announce_compact = *state.compact_block_announce.lock();
            if announce_compact
                && let Some(version) = compact_version
                && let Some(compact) = compact_block_for_inventory(node, &item, version)
                    .ok()
                    .flatten()
            {
                let message = Message::CompactBlock(compact);
                let _ = send_message(node, peer_id, &state.writer, network, &message).await;
                continue;
            }
            if matches!(
                item.kind,
                InventoryType::Block | InventoryType::WitnessBlock
            ) && *state.send_headers.lock()
            {
                let header = node
                    .chain
                    .write()
                    .block(&item.hash)
                    .ok()
                    .flatten()
                    .map(|block| block.header);
                if let Some(header) = header {
                    let _ = send_message(
                        node,
                        peer_id,
                        &state.writer,
                        network,
                        &Message::Headers(vec![header]),
                    )
                    .await;
                    continue;
                }
            }
        }
        if item.kind.is_transaction() {
            if !state.local_relay_transactions || !*state.relay_transactions.lock() {
                continue;
            }
            if force_relay {
                let sent = send_message(
                    node,
                    peer_id,
                    &state.writer,
                    network,
                    &Message::Inv(vec![item.clone()]),
                )
                .await
                .is_ok();
                if sent {
                    node.record_peer_inv_sequence(peer_id, node.mempool.read().sequence());
                }
            } else {
                queue_peer_transaction_inventory(node, peer_id, &state, item);
            }
            continue;
        }
        let message = Message::Inv(vec![item.clone()]);
        let sent = send_message(node, peer_id, &state.writer, network, &message)
            .await
            .is_ok();
        if sent && item.kind.is_transaction() {
            node.record_peer_inv_sequence(peer_id, node.mempool.read().sequence());
        }
    }
}

fn compact_block_for_inventory(
    node: &Arc<Node>,
    item: &Inventory,
    version: u64,
) -> Result<Option<HeaderAndShortIds>> {
    if !matches!(
        item.kind,
        InventoryType::Block | InventoryType::WitnessBlock | InventoryType::CompactBlock
    ) {
        return Ok(None);
    }
    let block = node.chain.write().block(&item.hash)?;
    block
        .map(|block| {
            HeaderAndShortIds::from_block(&block, random(), version as u32, &[]).map_err(Into::into)
        })
        .transpose()
}

fn transaction_fee_for_inventory(node: &Arc<Node>, item: &Inventory) -> Option<(u64, u64)> {
    let mempool = node.mempool.read();
    match item.kind {
        kind if kind.is_witness_transaction() => mempool
            .get_by_wtxid(&Wtxid::from_byte_array(item.hash.to_byte_array()))
            .map(|entry| (entry.fee_sat, entry.vsize)),
        InventoryType::Transaction => mempool
            .get(&Txid::from_byte_array(item.hash.to_byte_array()))
            .map(|entry| (entry.fee_sat, entry.vsize)),
        _ => None,
    }
}

fn transaction_inventory(transaction: &Transaction, wtxid_relay: bool) -> Inventory {
    if wtxid_relay {
        Inventory {
            kind: InventoryType::WitnessTransaction,
            hash: BlockHash::from_raw_hash(transaction.compute_wtxid().to_raw_hash()),
        }
    } else {
        Inventory {
            kind: InventoryType::Transaction,
            hash: BlockHash::from_raw_hash(transaction.compute_txid().to_raw_hash()),
        }
    }
}

fn transaction_without_witness(transaction: &Transaction) -> Transaction {
    let mut transaction = transaction.clone();
    for input in &mut transaction.input {
        input.witness = Witness::default();
    }
    transaction
}

fn block_without_witness(block: &Block) -> Block {
    let mut block = block.clone();
    for transaction in &mut block.txdata {
        *transaction = transaction_without_witness(transaction);
    }
    block
}

fn compact_block_indexes_are_strictly_increasing(indexes: &[u64]) -> bool {
    indexes.windows(2).all(|pair| pair[0] < pair[1])
}

fn requested_block_transactions(block: &Block, indexes: &[u64]) -> Option<Vec<Transaction>> {
    indexes
        .iter()
        .map(|index| {
            usize::try_from(*index)
                .ok()
                .and_then(|index| block.txdata.get(index).cloned())
        })
        .collect()
}

fn compact_filter_checkpoint_heights(stop_height: u32) -> impl Iterator<Item = u32> {
    (1_000..=stop_height).step_by(1_000)
}

fn peer_can_request_mempool(peer_bloom_filters: bool, permissions: PeerPermissions) -> bool {
    peer_bloom_filters
        || permissions.contains(PeerPermissions::MEMPOOL)
        || permissions.contains(PeerPermissions::BLOOM_FILTER)
}

fn blocktxn_block_is_recent(height: u32, tip_height: u32) -> bool {
    height >= tip_height.saturating_sub(MAX_BLOCKTXN_DEPTH)
}

fn compact_block_is_recent(height: u32, tip_height: u32) -> bool {
    height >= tip_height.saturating_sub(MAX_CMPCTBLOCK_DEPTH)
}

fn fee_rate_sat_per_kvb(fee_sat: u64, vsize: u64) -> i64 {
    if vsize == 0 {
        return i64::MAX;
    }
    i64::try_from(fee_sat.saturating_mul(1_000).saturating_div(vsize)).unwrap_or(i64::MAX)
}

fn install_bloom_filter(
    bloom_filter: &parking_lot::Mutex<Option<BloomFilter>>,
    relay_transactions: &parking_lot::Mutex<bool>,
    filter: FilterLoad,
) -> Result<()> {
    *bloom_filter.lock() = Some(BloomFilter::from_message(filter)?);
    *relay_transactions.lock() = true;
    Ok(())
}

fn apply_bloom_filter_add(
    bloom_filter: &parking_lot::Mutex<Option<BloomFilter>>,
    data: &[u8],
) -> bool {
    if data.len() > MAX_BLOOM_ELEMENT_SIZE {
        return false;
    }
    let mut filter = bloom_filter.lock();
    let Some(filter) = filter.as_mut() else {
        return false;
    };
    filter.insert(data);
    true
}

fn clear_bloom_filter(
    bloom_filter: &parking_lot::Mutex<Option<BloomFilter>>,
    relay_transactions: &parking_lot::Mutex<bool>,
) {
    *bloom_filter.lock() = None;
    *relay_transactions.lock() = true;
}

fn transaction_for_inventory(node: &Arc<Node>, item: &Inventory) -> Option<Transaction> {
    let mempool = node.mempool.read();
    match item.kind {
        kind if kind.is_witness_transaction() => mempool
            .get_by_wtxid(&Wtxid::from_byte_array(item.hash.to_byte_array()))
            .map(|entry| entry.transaction.clone()),
        InventoryType::Transaction => mempool
            .get(&Txid::from_byte_array(item.hash.to_byte_array()))
            .map(|entry| entry.transaction.clone()),
        _ => None,
    }
}

fn transaction_for_getdata_tip(node: &Arc<Node>, item: &Inventory) -> Result<Option<Transaction>> {
    let mut chain = node.chain.write();
    let tip_hash = chain.best_hash();
    let Some(block) = chain.block(&tip_hash)? else {
        return Ok(None);
    };
    let transaction = block.txdata.into_iter().find(|transaction| {
        if item.kind.is_witness_transaction() {
            Wtxid::from_byte_array(item.hash.to_byte_array()) == transaction.compute_wtxid()
        } else {
            Txid::from_byte_array(item.hash.to_byte_array()) == transaction.compute_txid()
        }
    });
    Ok(transaction)
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::Amount;
    use bitcoin::Network;
    use bitcoin::absolute::LockTime;
    use bitcoin::bip158::FilterHeader;
    use bitcoin::block::{Header, Version as BlockVersion};
    use bitcoin::blockdata::constants::genesis_block;
    use bitcoin::blockdata::script::{Builder, ScriptBuf};
    use bitcoin::blockdata::transaction::{OutPoint, TxIn, TxOut, Version};
    use bitcoin::blockdata::witness::Witness;
    use bitcoin::p2p::message_filter::GetCFilters;

    use crate::config::OnlyNet;
    use crate::{Config, Node};

    fn private_broadcast_test_config(
        datadir: &std::path::Path,
        private_broadcast: bool,
        seed_nodes: Vec<SocketAddr>,
    ) -> Config {
        Config {
            network: Network::Regtest,
            datadir: datadir.to_owned(),
            blocks_dir: None,
            blocks_dir_explicit: false,
            blocks_xor: false,
            capture_messages: false,
            debug_log_path: std::path::PathBuf::from("debug.log"),
            pid_path: std::path::PathBuf::from("bitcoind.pid"),
            logging: Default::default(),
            debug_log_file_enabled: false,
            print_to_console: false,
            shrink_debug_file: false,
            settings_path: None,
            asmap: None,
            minimum_chain_work: None,
            assume_valid: None,
            check_blocks: None,
            check_level: None,
            check_block_index: 0,
            check_mempool: 0,
            check_addrman: 0,
            max_tip_age_secs: 24 * 60 * 60,
            mock_time: None,
            stop_at_height: 0,
            p2p_bind: "127.0.0.1:0".parse().unwrap(),
            p2p_binds: Vec::new(),
            listen: true,
            rpc_bind: None,
            rpc_binds: Vec::new(),
            rpc_allow_ips: Vec::new(),
            rpc_auth: Vec::new(),
            rpc_cookie_path: None,
            rpc_cookie_permissions: crate::config::RpcCookiePermissions::Owner,
            rpc_server_timeout_secs: 30,
            rpc_threads: 16,
            rpc_work_queue: 64,
            script_check_threads: 0,
            block_reconstruction_extra_txn: 100,
            user_agent_comments: Vec::new(),
            startup_notify: None,
            block_notify: None,
            shutdown_notify: None,
            alert_notify: None,
            max_sig_cache_mib: 32,
            accept_stale_fee_estimates: false,
            rpc_whitelist: std::collections::HashMap::new(),
            rpc_whitelist_default: false,
            electrum_bind: None,
            rest: false,
            seed_nodes: seed_nodes
                .into_iter()
                .map(NetworkEndpoint::from_socket)
                .collect(),
            connect_disabled: false,
            v2_transport: true,
            network_active: true,
            discover: true,
            external_addresses: Vec::new(),
            dns_lookup: true,
            add_nodes: Vec::new(),
            seed_nodes_for_address_fetch: Vec::new(),
            dnsseed: false,
            fixed_seeds: false,
            force_dns_seed: false,
            onlynet: Vec::new(),
            proxy: private_broadcast.then(|| "127.0.0.1:9050".parse().unwrap()),
            i2p_sam: None,
            onion_proxy: None,
            listen_onion: false,
            tor_control: "127.0.0.1:9051".parse().unwrap(),
            tor_password: None,
            i2p_accept_incoming: false,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
            signet_challenge: None,
            signet_seed_nodes: Vec::new(),
            deployment_parameters: None,
            max_peers: 4,
            max_receive_buffer: 5_000,
            max_send_buffer: 1_000,
            max_upload_target: 0,
            peer_timeout_secs: 60,
            ban_time_secs: 86_400,
            deprecated_rpcs: std::collections::HashSet::new(),
            connect_timeout_ms: 5_000,
            block_max_weight: 4_000_000,
            block_reserved_weight: 8_000,
            block_version: None,
            block_min_tx_fee_sat_per_kvb: 1,
            min_relay_tx_fee_sat_per_kvb: 100,
            incremental_relay_fee_sat_per_kvb: 100,
            dust_relay_fee_sat_per_kvb: 3_000,
            max_datacarrier_bytes: Some(100_000),
            bytes_per_sigop: 20,
            permit_bare_multisig: true,
            peer_bloom_filters: false,
            blocksonly: false,
            private_broadcast,
            accept_nonstd_txn: true,
            rbf_policy: crate::mempool::RbfPolicy::Always,
            truc_policy: crate::mempool::TrucPolicy::Accept,
            cjdns_reachable: false,
            prune: 0,
            fast_prune: false,
            natpmp: false,
            reindex: false,
            reindex_chainstate: false,
            load_blocks: Vec::new(),
            stop_after_block_import: false,
            txindex: false,
            txospenderindex: false,
            coinstatsindex: false,
            blockfilterindex: true,
            peer_block_filters: true,
            max_mempool_mb: 300,
            cluster_count: 64,
            cluster_size_vbytes: 101_000,
            mempool_expiry_hours: 336,
            persist_mempool: false,
            persist_mempool_v1: false,
            zmq: crate::config::ZmqConfig::default(),
        }
    }

    fn mine_private_broadcast_block(previous: &Header, height: u32, now: u32) -> Block {
        let mut block = Block {
            header: Header {
                version: BlockVersion::from_consensus(4),
                prev_blockhash: previous.block_hash(),
                merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                time: now.saturating_sub(101).saturating_add(height),
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
                        .push_slice([height as u8])
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

    fn private_broadcast_test_transaction(node: &Arc<Node>) -> Transaction {
        let funding_hash = node.chain.read().block_hash(1).unwrap();
        let funding_block = node.chain.write().block(&funding_hash).unwrap().unwrap();
        Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(funding_block.txdata[0].compute_txid(), 0),
                script_sig: ScriptBuf::from_bytes(vec![0; 8]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(4_999_999_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        }
    }

    #[tokio::test]
    async fn private_broadcast_handshake_delivers_transaction_and_acknowledges_peer() {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let target_address = listener.local_addr().unwrap();
        let source_directory = tempfile::tempdir().unwrap();
        let target_directory = tempfile::tempdir().unwrap();
        let source = Node::open(private_broadcast_test_config(
            source_directory.path(),
            true,
            vec![target_address],
        ))
        .unwrap();
        let target = Node::open(private_broadcast_test_config(
            target_directory.path(),
            false,
            Vec::new(),
        ))
        .unwrap();

        let now = unix_time_seconds() as u32;
        for height in 1..=101 {
            let previous = *source.chain.read().header(height - 1).unwrap();
            let block = mine_private_broadcast_block(&previous, height, now);
            source.connect_block(block.clone()).unwrap();
            target.connect_block(block).unwrap();
        }
        assert!(!source.chain.read().is_initial_block_download());
        assert!(!target.chain.read().is_initial_block_download());

        let transaction = private_broadcast_test_transaction(&source);
        let txid = transaction.compute_txid();
        let (manager_sender, mut manager_receiver) = tokio::sync::mpsc::unbounded_channel();
        source.set_peer_manager_sender(manager_sender);
        source.queue_private_broadcast(transaction.clone()).unwrap();
        assert!(matches!(
            manager_receiver.try_recv().unwrap(),
            PeerManagerRequest::PrivateBroadcast { .. }
        ));

        let client = TcpStream::connect(target_address);
        let server = listener.accept();
        let (client, server) = tokio::join!(client, server);
        let client = client.unwrap();
        let (server, _) = server.unwrap();
        let target_peer_address = server.peer_addr().unwrap();

        let source_peers = Arc::new(parking_lot::Mutex::new(HashMap::new()));
        let target_peers = Arc::new(parking_lot::Mutex::new(HashMap::new()));
        let source_task = tokio::spawn(serve_peer(
            source.clone(),
            client,
            NetworkEndpoint::Ip(target_address),
            PeerConnectionOptions {
                outbound: true,
                transport_v2: Some(false),
                connection_type: "private-broadcast",
                permissions: None,
                private_broadcast_transaction: Some(transaction),
            },
            source_peers,
            1,
        ));
        let target_task = tokio::spawn(serve_peer(
            target.clone(),
            server,
            NetworkEndpoint::Ip(target_peer_address),
            PeerConnectionOptions {
                outbound: false,
                transport_v2: Some(false),
                connection_type: "inbound",
                permissions: None,
                private_broadcast_transaction: None,
            },
            target_peers,
            1,
        ));

        tokio::time::timeout(Duration::from_secs(10), async {
            loop {
                if target.mempool.read().get(&txid).is_some() {
                    break;
                }
                tokio::time::sleep(Duration::from_millis(20)).await;
            }
        })
        .await
        .unwrap();

        let source_result = tokio::time::timeout(Duration::from_secs(10), source_task)
            .await
            .unwrap()
            .unwrap();
        assert!(source_result.is_err());
        let info = source.private_broadcast_infos();
        assert_eq!(info.len(), 1);
        assert!(info[0].peers.iter().any(|peer| peer.received.is_some()));

        target.disconnect_all_peers();
        let target_result = tokio::time::timeout(Duration::from_secs(10), target_task)
            .await
            .unwrap()
            .unwrap();
        assert!(target_result.is_err());
    }

    #[tokio::test]
    async fn malformed_compact_filter_request_disconnects_peer() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(private_broadcast_test_config(
            directory.path(),
            false,
            Vec::new(),
        ))
        .unwrap();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let address = listener.local_addr().unwrap();
        let client = TcpStream::connect(address);
        let server = listener.accept();
        let (client, server) = tokio::join!(client, server);
        let client = client.unwrap();
        let (server, _) = server.unwrap();
        let client_address = client.local_addr().unwrap();
        let server_task = tokio::spawn(serve_peer(
            node.clone(),
            server,
            NetworkEndpoint::Ip(client_address),
            PeerConnectionOptions {
                outbound: false,
                transport_v2: Some(false),
                connection_type: "inbound",
                permissions: None,
                private_broadcast_transaction: None,
            },
            Arc::new(parking_lot::Mutex::new(HashMap::new())),
            1,
        ));

        let (mut reader, mut writer) = client.into_split();
        wire::write_message_with_size(
            &mut writer,
            Network::Regtest,
            &Message::Version(VersionMessage::with_bloom(0, random(), false)),
        )
        .await
        .unwrap();
        let first_message = tokio::time::timeout(
            Duration::from_secs(5),
            wire::read_message(&mut reader, Network::Regtest),
        )
        .await
        .expect("server did not send version")
        .unwrap();
        assert!(matches!(first_message, Message::Version(_)));
        loop {
            let message = tokio::time::timeout(
                Duration::from_secs(5),
                wire::read_message(&mut reader, Network::Regtest),
            )
            .await
            .expect("server did not complete version handshake")
            .unwrap();
            if matches!(message, Message::Verack) {
                break;
            }
        }
        wire::write_message_with_size(&mut writer, Network::Regtest, &Message::Verack)
            .await
            .unwrap();
        let stop_hash = node.chain.read().best_hash();
        wire::write_message_with_size(
            &mut writer,
            Network::Regtest,
            &Message::GetCFilters(GetCFilters {
                filter_type: 255,
                start_height: 0,
                stop_hash,
            }),
        )
        .await
        .unwrap();

        let result = tokio::time::timeout(Duration::from_secs(5), server_task)
            .await
            .unwrap()
            .unwrap();
        assert!(result.is_err());
    }

    #[test]
    fn connection_types_match_local_transaction_relay_policy() {
        assert!(local_transaction_relay_enabled(
            "outbound-full",
            false,
            PeerPermissions::empty()
        ));
        assert!(local_transaction_relay_enabled(
            "inbound",
            false,
            PeerPermissions::empty()
        ));
        assert!(local_transaction_relay_enabled(
            "addr-fetch",
            false,
            PeerPermissions::empty()
        ));
        for connection_type in ["block-relay-only", "feeler", "private-broadcast"] {
            assert!(!local_transaction_relay_enabled(
                connection_type,
                false,
                PeerPermissions::empty()
            ));
        }
        assert!(!local_transaction_relay_enabled(
            "outbound-full",
            true,
            PeerPermissions::empty()
        ));
        assert!(local_transaction_relay_enabled(
            "outbound-full",
            true,
            PeerPermissions::FORCE_RELAY
        ));
        assert!(!local_transaction_relay_enabled(
            "block-relay-only",
            true,
            PeerPermissions::FORCE_RELAY
        ));
    }

    #[test]
    fn connection_types_match_core_sync_and_address_policies() {
        assert!(connection_requests_headers("outbound-full"));
        assert!(connection_requests_headers("block-relay-only"));
        assert!(!connection_requests_headers("addr-fetch"));
        assert!(!connection_requests_headers("feeler"));

        assert!(connection_fetches_addresses(true, "outbound-full"));
        assert!(connection_fetches_addresses(true, "addr-fetch"));
        assert!(!connection_fetches_addresses(true, "block-relay-only"));
        assert!(!connection_fetches_addresses(true, "feeler"));
        assert!(!connection_fetches_addresses(false, "inbound"));
    }

    #[tokio::test]
    async fn socks5_proxy_negotiation_routes_ipv4_targets() {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let proxy_address = listener.local_addr().unwrap();
        let server = tokio::spawn(async move {
            let (mut stream, _) = listener.accept().await.unwrap();
            let mut greeting = [0; 3];
            stream.read_exact(&mut greeting).await.unwrap();
            assert_eq!(greeting, [5, 1, 0]);
            stream.write_all(&[5, 0]).await.unwrap();

            let mut prefix = [0; 5];
            stream.read_exact(&mut prefix).await.unwrap();
            assert_eq!(&prefix[..4], &[5, 1, 0, 3]);
            assert_eq!(usize::from(prefix[4]), "192.0.2.44".len());
            let mut host = vec![0; usize::from(prefix[4])];
            stream.read_exact(&mut host).await.unwrap();
            assert_eq!(host, b"192.0.2.44");
            let mut port = [0; 2];
            stream.read_exact(&mut port).await.unwrap();
            assert_eq!(port, 18444u16.to_be_bytes());
            stream
                .write_all(&[5, 0, 0, 1, 127, 0, 0, 1, 0, 1])
                .await
                .unwrap();
        });

        let mut stream = TcpStream::connect(proxy_address).await.unwrap();
        socks5_connect(&mut stream, "192.0.2.44:18444".parse().unwrap())
            .await
            .unwrap();
        server.await.unwrap();
    }

    #[tokio::test]
    async fn socks5_proxy_randomized_credentials_are_unique() {
        let endpoint = NetworkEndpoint::Ip("8.8.8.8:18444".parse().unwrap());
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let proxy_address = listener.local_addr().unwrap();
        let server = tokio::spawn(async move {
            let mut credentials = Vec::new();
            for _ in 0..2 {
                let (mut stream, _) = listener.accept().await.unwrap();
                let mut greeting = [0; 4];
                stream.read_exact(&mut greeting).await.unwrap();
                assert_eq!(greeting, [5, 2, 0, 2]);
                stream.write_all(&[5, 2]).await.unwrap();

                let mut authentication_prefix = [0; 2];
                stream.read_exact(&mut authentication_prefix).await.unwrap();
                assert_eq!(authentication_prefix[0], 1);
                let username_length = usize::from(authentication_prefix[1]);
                let mut username = vec![0; username_length];
                stream.read_exact(&mut username).await.unwrap();
                let mut password_length = [0; 1];
                stream.read_exact(&mut password_length).await.unwrap();
                let mut password = vec![0; usize::from(password_length[0])];
                stream.read_exact(&mut password).await.unwrap();
                assert_eq!(username, password);
                credentials.push(username);
                stream.write_all(&[1, 0]).await.unwrap();

                let mut request = [0; 14];
                stream.read_exact(&mut request).await.unwrap();
                assert_eq!(&request[..5], &[5, 1, 0, 3, 7]);
                assert_eq!(&request[5..12], b"8.8.8.8");
                assert_eq!(&request[12..], &18444u16.to_be_bytes());
                stream
                    .write_all(&[5, 0, 0, 1, 127, 0, 0, 1, 0, 1])
                    .await
                    .unwrap();
            }
            credentials
        });

        let first = connect_peer_endpoint_with_options(&endpoint, Some(proxy_address), false, true)
            .await
            .unwrap();
        let second =
            connect_peer_endpoint_with_options(&endpoint, Some(proxy_address), false, true)
                .await
                .unwrap();
        let credentials = server.await.unwrap();
        assert_ne!(credentials[0], credentials[1]);
        drop((first, second));
    }

    #[tokio::test]
    async fn proxy_is_bypassed_for_unroutable_socket_targets() {
        let target_listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let target_address = target_listener.local_addr().unwrap();
        let proxy_listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let proxy_address = proxy_listener.local_addr().unwrap();
        let target = tokio::spawn(async move {
            let (_stream, _) = target_listener.accept().await.unwrap();
        });
        let proxy = tokio::spawn(async move {
            assert!(
                tokio::time::timeout(Duration::from_millis(100), proxy_listener.accept())
                    .await
                    .is_err()
            );
        });

        let endpoint = NetworkEndpoint::Ip(target_address);
        let _stream = connect_peer_endpoint(&endpoint, Some(proxy_address))
            .await
            .unwrap();
        target.await.unwrap();
        proxy.await.unwrap();
    }

    #[tokio::test]
    async fn socks5_proxy_negotiation_routes_onion_domains() {
        let endpoint = NetworkEndpoint::OnionV3 {
            address: [7; 32],
            port: 18444,
        };
        let host = endpoint.host_string();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let proxy_address = listener.local_addr().unwrap();
        let server = tokio::spawn(async move {
            let (mut stream, _) = listener.accept().await.unwrap();
            let mut greeting = [0; 3];
            stream.read_exact(&mut greeting).await.unwrap();
            assert_eq!(greeting, [5, 1, 0]);
            stream.write_all(&[5, 0]).await.unwrap();

            let mut prefix = [0; 5];
            stream.read_exact(&mut prefix).await.unwrap();
            assert_eq!(&prefix[..4], &[5, 1, 0, 3]);
            assert_eq!(usize::from(prefix[4]), host.len());
            let mut received_host = vec![0; usize::from(prefix[4])];
            stream.read_exact(&mut received_host).await.unwrap();
            assert_eq!(received_host, host.as_bytes());
            let mut port = [0; 2];
            stream.read_exact(&mut port).await.unwrap();
            assert_eq!(port, 18444u16.to_be_bytes());
            stream
                .write_all(&[5, 0, 0, 1, 127, 0, 0, 1, 0, 1])
                .await
                .unwrap();
        });

        let _stream = connect_peer_endpoint(&endpoint, Some(proxy_address))
            .await
            .unwrap();
        server.await.unwrap();
    }

    #[tokio::test]
    async fn separate_onion_proxy_overrides_generic_proxy() {
        let endpoint = NetworkEndpoint::OnionV3 {
            address: [8; 32],
            port: 18444,
        };
        let generic_listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let generic_address = generic_listener.local_addr().unwrap();
        let onion_listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let onion_address = onion_listener.local_addr().unwrap();
        let host = endpoint.host_string();
        let port = endpoint.port();
        let onion_server = tokio::spawn(async move {
            let (mut stream, _) = onion_listener.accept().await.unwrap();
            let mut greeting = [0; 3];
            stream.read_exact(&mut greeting).await.unwrap();
            assert_eq!(greeting, [5, 1, 0]);
            stream.write_all(&[5, 0]).await.unwrap();
            let mut prefix = [0; 5];
            stream.read_exact(&mut prefix).await.unwrap();
            assert_eq!(&prefix[..4], &[5, 1, 0, 3]);
            let mut received_host = vec![0; usize::from(prefix[4])];
            stream.read_exact(&mut received_host).await.unwrap();
            assert_eq!(received_host, host.as_bytes());
            let mut received_port = [0; 2];
            stream.read_exact(&mut received_port).await.unwrap();
            assert_eq!(received_port, port.to_be_bytes());
            stream
                .write_all(&[5, 0, 0, 1, 127, 0, 0, 1, 0, 1])
                .await
                .unwrap();
        });

        let _stream = connect_peer_endpoint_with_options_and_dns_with_i2p(
            &endpoint,
            Some(generic_address),
            Some(onion_address),
            false,
            false,
            true,
            Duration::from_secs(1),
            None,
        )
        .await
        .unwrap();
        assert!(
            tokio::time::timeout(Duration::from_millis(100), generic_listener.accept())
                .await
                .is_err()
        );
        onion_server.await.unwrap();
    }

    #[tokio::test]
    async fn socks5_proxy_negotiation_routes_dns_hostnames() {
        let endpoint = NetworkEndpoint::dns("peer.example".to_owned(), 18444).unwrap();
        let host = endpoint.host_string();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let proxy_address = listener.local_addr().unwrap();
        let server = tokio::spawn(async move {
            let (mut stream, _) = listener.accept().await.unwrap();
            let mut greeting = [0; 3];
            stream.read_exact(&mut greeting).await.unwrap();
            assert_eq!(greeting, [5, 1, 0]);
            stream.write_all(&[5, 0]).await.unwrap();

            let mut prefix = [0; 5];
            stream.read_exact(&mut prefix).await.unwrap();
            assert_eq!(&prefix[..4], &[5, 1, 0, 3]);
            assert_eq!(usize::from(prefix[4]), host.len());
            let mut host = vec![0; usize::from(prefix[4])];
            stream.read_exact(&mut host).await.unwrap();
            assert_eq!(host, b"peer.example");
            let mut port = [0; 2];
            stream.read_exact(&mut port).await.unwrap();
            assert_eq!(port, 18444u16.to_be_bytes());
            stream
                .write_all(&[5, 0, 0, 1, 127, 0, 0, 1, 0, 1])
                .await
                .unwrap();
        });

        let _stream = connect_peer_endpoint(&endpoint, Some(proxy_address))
            .await
            .unwrap();
        server.await.unwrap();
    }

    #[tokio::test]
    async fn disabled_dns_rejects_direct_hostname_connections() {
        let endpoint = NetworkEndpoint::dns("peer.example".to_owned(), 18444).unwrap();
        let error =
            connect_peer_endpoint_with_options_and_dns(&endpoint, None, false, false, false)
                .await
                .unwrap_err()
                .to_string();
        assert!(error.contains("DNS lookup is disabled"));
    }

    #[test]
    fn onlynet_filters_discovered_addresses_but_not_manual_nodes() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            blocks_dir: None,
            blocks_dir_explicit: false,
            blocks_xor: false,
            capture_messages: false,
            debug_log_path: std::path::PathBuf::from("debug.log"),
            pid_path: std::path::PathBuf::from("bitcoind.pid"),
            logging: Default::default(),
            debug_log_file_enabled: false,
            print_to_console: false,
            shrink_debug_file: false,
            settings_path: None,
            asmap: None,
            minimum_chain_work: None,
            assume_valid: None,
            check_blocks: None,
            check_level: None,
            check_block_index: 0,
            check_mempool: 0,
            check_addrman: 0,
            max_tip_age_secs: 24 * 60 * 60,
            mock_time: None,
            stop_at_height: 0,
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
            script_check_threads: 0,
            block_reconstruction_extra_txn: 100,
            user_agent_comments: Vec::new(),
            startup_notify: None,
            block_notify: None,
            shutdown_notify: None,
            alert_notify: None,
            max_sig_cache_mib: 32,
            accept_stale_fee_estimates: false,
            rpc_whitelist: std::collections::HashMap::new(),
            rpc_whitelist_default: false,
            electrum_bind: None,
            rest: false,
            listen: true,
            dnsseed: false,
            fixed_seeds: false,
            force_dns_seed: false,
            onlynet: vec![OnlyNet::Ipv4],
            proxy: None,
            i2p_sam: None,
            onion_proxy: None,
            listen_onion: false,
            tor_control: "127.0.0.1:9051".parse().unwrap(),
            tor_password: None,
            i2p_accept_incoming: false,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            rbf_policy: crate::mempool::RbfPolicy::Always,
            truc_policy: crate::mempool::TrucPolicy::Accept,
            cjdns_reachable: false,
            prune: 0,
            fast_prune: false,
            natpmp: false,
            reindex: false,
            reindex_chainstate: false,
            load_blocks: Vec::new(),
            stop_after_block_import: false,
            txindex: false,
            txospenderindex: false,
            max_mempool_mb: 300,
            cluster_count: 64,
            cluster_size_vbytes: 101_000,
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
            signet_seed_nodes: Vec::new(),
            deployment_parameters: None,
            max_peers: 1,
            max_receive_buffer: 5_000,
            max_send_buffer: 1_000,
            max_upload_target: 0,
            peer_bloom_filters: false,
            peer_timeout_secs: 60,
            ban_time_secs: 86_400,
            deprecated_rpcs: std::collections::HashSet::new(),
            connect_timeout_ms: 5_000,
            block_max_weight: 4_000_000,
            block_reserved_weight: 8_000,
            block_version: None,
            block_min_tx_fee_sat_per_kvb: 1,
            min_relay_tx_fee_sat_per_kvb: 100,
            incremental_relay_fee_sat_per_kvb: 100,
            dust_relay_fee_sat_per_kvb: 3_000,
            max_datacarrier_bytes: Some(100_000),
            bytes_per_sigop: 20,
            permit_bare_multisig: true,
            zmq: crate::config::ZmqConfig::default(),
        })
        .unwrap();
        let ipv4 = "192.0.2.10:18444".parse().unwrap();
        let ipv6 = "[2001:db8::10]:18444".parse().unwrap();
        assert!(node.add_peer_address(ipv4, false));
        assert!(node.add_peer_address(ipv6, false));
        assert!(node.add_node(ipv4));
        assert!(node.add_node(ipv6));
        let attempts = Arc::new(parking_lot::Mutex::new(HashSet::new()));
        assert_eq!(select_discovery_addresses(&node, 4, &attempts), Vec::new());
    }

    #[test]
    fn block_downloads_request_witnesses_from_capable_peers() {
        assert_eq!(
            block_request_inventory_type(wire::NODE_NETWORK | wire::NODE_WITNESS),
            InventoryType::WitnessBlock
        );
        assert_eq!(
            block_request_inventory_type(wire::NODE_NETWORK),
            InventoryType::Block
        );
    }

    #[test]
    fn transaction_inventory_budget_matches_core_trickle_limits() {
        assert_eq!(inventory_broadcast_limit(0), 70);
        assert_eq!(inventory_broadcast_limit(999), 70);
        assert_eq!(inventory_broadcast_limit(1_000), 75);
        assert_eq!(inventory_broadcast_limit(50_000), 320);
        assert_eq!(inventory_broadcast_limit(200_000), 1_000);
    }

    #[test]
    fn transaction_request_delays_match_core_policy() {
        assert_eq!(
            transaction_request_delay(true, true, true, false),
            Duration::ZERO
        );
        assert_eq!(
            transaction_request_delay(false, true, true, false),
            NONPREF_PEER_TX_DELAY
        );
        assert_eq!(
            transaction_request_delay(true, false, true, false),
            TXID_RELAY_DELAY
        );
        assert_eq!(
            transaction_request_delay(false, false, true, true),
            NONPREF_PEER_TX_DELAY + TXID_RELAY_DELAY + OVERLOADED_PEER_TX_DELAY
        );
    }

    #[test]
    fn transaction_requests_are_deduplicated_bounded_and_expire() {
        let now = Instant::now();
        let mut state = TxRequestState::default();
        let item = Inventory {
            kind: InventoryType::WitnessTransaction,
            hash: BlockHash::from_byte_array([1; 32]),
        };
        assert!(state.queue(item.clone(), now));
        assert!(!state.queue(item.clone(), now));
        let ready = state.take_ready(now, MAX_PEER_TX_REQUEST_IN_FLIGHT);
        assert_eq!(ready.len(), 1);
        state.mark_sent(&ready[0], now);
        assert_eq!(state.in_flight_count(), 1);
        assert!(!state.queue(item, now));
        state.expire(now + GETDATA_TX_INTERVAL);
        assert_eq!(state.in_flight_count(), 0);

        let mut bounded = TxRequestState::default();
        for index in 0..MAX_PEER_TX_ANNOUNCEMENTS {
            let mut bytes = [0; 32];
            bytes[..8].copy_from_slice(&(index as u64).to_le_bytes());
            assert!(bounded.queue(
                Inventory {
                    kind: InventoryType::Transaction,
                    hash: BlockHash::from_byte_array(bytes),
                },
                now,
            ));
        }
        assert!(!bounded.queue(
            Inventory {
                kind: InventoryType::Transaction,
                hash: BlockHash::from_byte_array([0xff; 32]),
            },
            now,
        ));
    }

    #[tokio::test]
    async fn transaction_request_flush_respects_the_core_inflight_window() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            blocks_dir: None,
            blocks_dir_explicit: false,
            blocks_xor: false,
            capture_messages: false,
            debug_log_path: std::path::PathBuf::from("debug.log"),
            pid_path: std::path::PathBuf::from("bitcoind.pid"),
            logging: Default::default(),
            debug_log_file_enabled: false,
            print_to_console: false,
            shrink_debug_file: false,
            settings_path: None,
            asmap: None,
            minimum_chain_work: None,
            assume_valid: None,
            check_blocks: None,
            check_level: None,
            check_block_index: 0,
            check_mempool: 0,
            check_addrman: 0,
            max_tip_age_secs: 24 * 60 * 60,
            mock_time: None,
            stop_at_height: 0,
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
            script_check_threads: 0,
            block_reconstruction_extra_txn: 100,
            user_agent_comments: Vec::new(),
            startup_notify: None,
            block_notify: None,
            shutdown_notify: None,
            alert_notify: None,
            max_sig_cache_mib: 32,
            accept_stale_fee_estimates: false,
            rpc_whitelist: std::collections::HashMap::new(),
            rpc_whitelist_default: false,
            electrum_bind: None,
            rest: false,
            listen: true,
            dnsseed: false,
            fixed_seeds: false,
            force_dns_seed: false,
            onlynet: Vec::new(),
            proxy: None,
            i2p_sam: None,
            onion_proxy: None,
            listen_onion: false,
            tor_control: "127.0.0.1:9051".parse().unwrap(),
            tor_password: None,
            i2p_accept_incoming: false,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            rbf_policy: crate::mempool::RbfPolicy::Always,
            truc_policy: crate::mempool::TrucPolicy::Accept,
            cjdns_reachable: false,
            prune: 0,
            fast_prune: false,
            natpmp: false,
            reindex: false,
            reindex_chainstate: false,
            load_blocks: Vec::new(),
            stop_after_block_import: false,
            txindex: false,
            txospenderindex: false,
            max_mempool_mb: 300,
            cluster_count: 64,
            cluster_size_vbytes: 101_000,
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
            signet_seed_nodes: Vec::new(),
            deployment_parameters: None,
            max_peers: 1,
            max_receive_buffer: 5_000,
            max_send_buffer: 1_000,
            max_upload_target: 0,
            peer_bloom_filters: false,
            peer_timeout_secs: 60,
            ban_time_secs: 86_400,
            deprecated_rpcs: std::collections::HashSet::new(),
            connect_timeout_ms: 5_000,
            block_max_weight: 4_000_000,
            block_reserved_weight: 8_000,
            block_version: None,
            block_min_tx_fee_sat_per_kvb: 1,
            min_relay_tx_fee_sat_per_kvb: 100,
            incremental_relay_fee_sat_per_kvb: 100,
            dust_relay_fee_sat_per_kvb: 3_000,
            max_datacarrier_bytes: Some(100_000),
            bytes_per_sigop: 20,
            permit_bare_multisig: true,
            zmq: crate::config::ZmqConfig::default(),
        })
        .unwrap();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let address = listener.local_addr().unwrap();
        let client = TcpStream::connect(address);
        let server = listener.accept();
        let (client, server) = tokio::join!(client, server);
        let client = client.unwrap();
        let (server, _) = server.unwrap();
        let (_, client_writer) = client.into_split();
        let (mut server_reader, _) = server.into_split();
        let writer = Arc::new(Mutex::new(PeerWriterKind::V1(client_writer)));
        let state = Arc::new(PeerState {
            endpoint: NetworkEndpoint::Ip(address),
            local_address: None,
            writer: writer.clone(),
            connection_type: "outbound-full",
            permissions: PeerPermissions::empty(),
            private_broadcast_transaction: None,
            private_broadcast_peer: parking_lot::Mutex::new(false),
            local_relay_transactions: true,
            bloom_filter: parking_lot::Mutex::new(None),
            known_tx_inventory: parking_lot::Mutex::new(KnownTxInventory::new()),
            pending_tx_inventory: parking_lot::Mutex::new(Vec::new()),
            tx_requests: parking_lot::Mutex::new(TxRequestState::default()),
            fee_filter: parking_lot::Mutex::new(0),
            relay_transactions: parking_lot::Mutex::new(true),
            wtxid_relay: parking_lot::Mutex::new(true),
            send_headers: parking_lot::Mutex::new(false),
            last_headers_request: parking_lot::Mutex::new(None),
            compact_block_version: parking_lot::Mutex::new(None),
            compact_block_announce: parking_lot::Mutex::new(false),
            tx_reconciliation_salt: parking_lot::Mutex::new(None),
            tx_reconciliation_registered: parking_lot::Mutex::new(false),
        });
        let peers = Arc::new(parking_lot::Mutex::new(HashMap::from([(7, state.clone())])));
        let now = Instant::now();
        for index in 0..=MAX_PEER_TX_REQUEST_IN_FLIGHT {
            let mut bytes = [0; 32];
            bytes[..8].copy_from_slice(&(index as u64).to_le_bytes());
            assert!(state.tx_requests.lock().queue(
                Inventory {
                    kind: InventoryType::WitnessTransaction,
                    hash: BlockHash::from_byte_array(bytes),
                },
                now,
            ));
        }

        flush_peer_transaction_requests(&node, 7, &state, &peers, &writer, Network::Regtest)
            .await
            .unwrap();
        let Message::GetData(items) = wire::read_message(&mut server_reader, Network::Regtest)
            .await
            .unwrap()
        else {
            panic!("expected transaction getdata");
        };
        assert_eq!(items.len(), MAX_PEER_TX_REQUEST_IN_FLIGHT);
        assert_eq!(state.tx_requests.lock().in_flight_count(), 100);
        assert_eq!(state.tx_requests.lock().pending.len(), 1);

        flush_peer_transaction_requests(&node, 7, &state, &peers, &writer, Network::Regtest)
            .await
            .unwrap();
        assert!(
            tokio::time::timeout(
                Duration::from_millis(20),
                wire::read_message(&mut server_reader, Network::Regtest),
            )
            .await
            .is_err()
        );
    }

    #[test]
    fn outbound_getdata_batches_match_core_limit() {
        let requests = (0..2_001)
            .map(|index| Inventory {
                kind: InventoryType::Block,
                hash: BlockHash::from_byte_array([index as u8; 32]),
            })
            .collect::<Vec<_>>();
        let lengths = getdata_batches(&requests)
            .map(<[Inventory]>::len)
            .collect::<Vec<_>>();
        assert_eq!(lengths, [1_000, 1_000, 1]);
    }

    #[test]
    fn addr_fetch_timeout_matches_core_boundary() {
        assert!(!addr_fetch_timed_out(1_000, 1_300));
        assert!(addr_fetch_timed_out(1_000, 1_301));
        assert!(!addr_fetch_timed_out(1_000, 999));
    }

    #[test]
    fn headers_request_rate_limit_and_timeout_match_core_windows() {
        assert!(headers_request_is_due(None));
        let now = Instant::now();
        assert!(!headers_request_is_due(Some(now)));
        assert!(headers_request_is_due(Some(
            now.checked_sub(HEADERS_RESPONSE_TIME).unwrap()
        )));

        assert!(!headers_download_timed_out(Some(now)));
        assert!(headers_download_timed_out(Some(
            now.checked_sub(HEADERS_DOWNLOAD_TIMEOUT).unwrap()
        )));
    }

    fn mined_regtest_headers(count: usize) -> (Header, Vec<Header>) {
        let mut previous = genesis_block(Network::Regtest).header;
        let mut headers = Vec::with_capacity(count);
        for _ in 0..count {
            let mut header = Header {
                version: BlockVersion::from_consensus(4),
                prev_blockhash: previous.block_hash(),
                merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                time: previous.time.saturating_add(1),
                bits: previous.bits,
                nonce: 0,
            };
            while !header.target().is_met_by(header.block_hash()) {
                header.nonce = header.nonce.wrapping_add(1);
            }
            previous = header;
            headers.push(header);
        }
        (genesis_block(Network::Regtest).header, headers)
    }

    #[test]
    fn low_work_headers_transition_to_redownload_and_release_verified_headers() {
        let (chain_start, headers) = mined_regtest_headers(300);
        let per_header = headers[0].work();
        let mut minimum_work = chain_start.work();
        for _ in 0..250 {
            minimum_work = minimum_work + per_header;
        }
        let mut sync = LowWorkHeadersSync::new(
            Network::Regtest,
            minimum_work,
            chain_start.block_hash(),
            0,
            chain_start.work(),
            chain_start,
            chain_start.time,
        );
        // Fix the randomized offset for a deterministic commitment boundary.
        sync.commit_offset = 1;

        let presync = sync.process(&headers, true);
        assert!(presync.success);
        assert!(presync.request_more);
        assert!(!presync.finished);
        assert_eq!(sync.phase(), LowWorkHeadersPhase::Redownload);
        assert_eq!(sync.commitment_count(), 2);

        let redownload = sync.process(&headers, true);
        assert!(redownload.success);
        assert!(redownload.finished);
        assert!(!redownload.request_more);
        assert_eq!(redownload.ready, headers);
    }

    #[test]
    fn low_work_headers_abort_on_a_redownload_commitment_mismatch() {
        let (chain_start, headers) = mined_regtest_headers(300);
        let per_header = headers[0].work();
        let mut minimum_work = chain_start.work();
        for _ in 0..250 {
            minimum_work = minimum_work + per_header;
        }
        let mut sync = LowWorkHeadersSync::new(
            Network::Regtest,
            minimum_work,
            chain_start.block_hash(),
            0,
            chain_start.work(),
            chain_start,
            chain_start.time,
        );
        sync.commit_offset = 1;
        assert!(sync.process(&headers, true).success);

        let expected = sync.commitments.front().unwrap();
        let mut changed = headers[0];
        for tag in 1u8..=u8::MAX {
            changed.merkle_root = bitcoin::TxMerkleNode::from_byte_array([tag; 32]);
            changed.nonce = 0;
            while !changed.target().is_met_by(changed.block_hash()) {
                changed.nonce = changed.nonce.wrapping_add(1);
            }
            if sync.commitment(&changed) != expected {
                break;
            }
        }
        assert_ne!(sync.commitment(&changed), expected);
        let result = sync.process(&[changed], true);
        assert!(!result.success);
        assert!(result.finished);
    }

    #[test]
    fn legacy_transaction_getdata_strips_witness_data() {
        let transaction = Transaction {
            version: bitcoin::blockdata::transaction::Version::TWO,
            lock_time: bitcoin::absolute::LockTime::ZERO,
            input: vec![bitcoin::TxIn {
                previous_output: bitcoin::OutPoint::new(Txid::from_byte_array([1; 32]), 0),
                script_sig: bitcoin::ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::from_slice(&[&[1u8, 2u8][..]]),
            }],
            output: vec![bitcoin::TxOut {
                value: bitcoin::Amount::from_sat(1),
                script_pubkey: bitcoin::ScriptBuf::new(),
            }],
        };
        let legacy = transaction_without_witness(&transaction);

        assert_eq!(legacy.compute_txid(), transaction.compute_txid());
        assert_ne!(legacy.compute_wtxid(), transaction.compute_wtxid());
        assert!(legacy.input.iter().all(|input| input.witness.is_empty()));
    }

    #[test]
    fn legacy_block_getdata_strips_witness_data() {
        let transaction = Transaction {
            version: bitcoin::blockdata::transaction::Version::TWO,
            lock_time: bitcoin::absolute::LockTime::ZERO,
            input: vec![bitcoin::TxIn {
                previous_output: bitcoin::OutPoint::new(Txid::from_byte_array([1; 32]), 0),
                script_sig: bitcoin::ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::from_slice(&[&[1u8, 2u8][..]]),
            }],
            output: vec![bitcoin::TxOut {
                value: bitcoin::Amount::from_sat(1),
                script_pubkey: bitcoin::ScriptBuf::new(),
            }],
        };
        let block = Block {
            header: bitcoin::block::Header {
                version: bitcoin::block::Version::TWO,
                prev_blockhash: BlockHash::all_zeros(),
                merkle_root: transaction.compute_txid().to_raw_hash().into(),
                time: 1,
                bits: bitcoin::CompactTarget::from_consensus(0x207f_ffff),
                nonce: 0,
            },
            txdata: vec![transaction.clone()],
        };
        let legacy = block_without_witness(&block);
        assert_eq!(legacy.txdata[0].compute_txid(), transaction.compute_txid());
        assert_ne!(
            legacy.txdata[0].compute_wtxid(),
            transaction.compute_wtxid()
        );
        assert!(legacy.txdata[0].input[0].witness.is_empty());
    }

    #[test]
    fn compact_block_indexes_must_be_strictly_increasing() {
        assert!(compact_block_indexes_are_strictly_increasing(&[0, 1, 4, 9]));
        assert!(!compact_block_indexes_are_strictly_increasing(&[0, 1, 1]));
        assert!(!compact_block_indexes_are_strictly_increasing(&[2, 1]));
    }

    #[test]
    fn compact_reconstruction_uses_recent_non_mempool_transactions() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(private_broadcast_test_config(
            directory.path(),
            false,
            Vec::new(),
        ))
        .unwrap();
        let transaction = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(Txid::from_byte_array([1; 32]), 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(1),
                script_pubkey: Builder::new().push_int(1).into_script(),
            }],
        };
        assert!(node.accept_peer_transaction(transaction.clone()).is_err());
        let mut block = genesis_block(Network::Regtest);
        block.txdata.push(transaction.clone());
        let compact = HeaderAndShortIds::from_block(&block, 17, 2, &[]).unwrap();

        let (reconstructed, missing) = reconstruct_compact_block(&compact, &node, 2).unwrap();
        assert!(missing.is_empty());
        assert_eq!(reconstructed[1], Some(transaction));
    }

    #[test]
    fn out_of_bounds_compact_block_indexes_do_not_produce_transactions() {
        let transaction = Transaction {
            version: bitcoin::blockdata::transaction::Version::TWO,
            lock_time: bitcoin::absolute::LockTime::ZERO,
            input: vec![bitcoin::TxIn {
                previous_output: bitcoin::OutPoint::new(Txid::from_byte_array([1; 32]), 0),
                script_sig: bitcoin::ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![bitcoin::TxOut {
                value: bitcoin::Amount::from_sat(1),
                script_pubkey: bitcoin::ScriptBuf::new(),
            }],
        };
        let block = Block {
            header: bitcoin::block::Header {
                version: bitcoin::block::Version::TWO,
                prev_blockhash: BlockHash::all_zeros(),
                merkle_root: transaction.compute_txid().to_raw_hash().into(),
                time: 1,
                bits: bitcoin::CompactTarget::from_consensus(0x207f_ffff),
                nonce: 0,
            },
            txdata: vec![transaction.clone()],
        };

        assert_eq!(
            requested_block_transactions(&block, &[0]).unwrap(),
            vec![transaction]
        );
        assert!(requested_block_transactions(&block, &[1]).is_none());
        assert!(requested_block_transactions(&block, &[u64::MAX]).is_none());
    }

    #[test]
    fn compact_block_transaction_serving_uses_core_recency_window() {
        assert!(blocktxn_block_is_recent(90, 100));
        assert!(blocktxn_block_is_recent(100, 100));
        assert!(!blocktxn_block_is_recent(89, 100));
        assert!(blocktxn_block_is_recent(0, 5));

        assert!(compact_block_is_recent(95, 100));
        assert!(compact_block_is_recent(100, 100));
        assert!(!compact_block_is_recent(94, 100));
        assert!(compact_block_is_recent(0, 5));
    }

    #[test]
    fn compact_filter_checkpoint_heights_match_core_interval() {
        assert_eq!(
            compact_filter_checkpoint_heights(999).collect::<Vec<_>>(),
            Vec::<u32>::new()
        );
        assert_eq!(
            compact_filter_checkpoint_heights(1_000).collect::<Vec<_>>(),
            vec![1_000]
        );
        assert_eq!(
            compact_filter_checkpoint_heights(1_999).collect::<Vec<_>>(),
            vec![1_000]
        );
        assert_eq!(
            compact_filter_checkpoint_heights(2_000).collect::<Vec<_>>(),
            vec![1_000, 2_000]
        );
    }

    #[test]
    fn mempool_requests_require_core_advertised_permissions() {
        assert!(!peer_can_request_mempool(false, PeerPermissions::empty()));
        assert!(peer_can_request_mempool(true, PeerPermissions::empty()));
        assert!(peer_can_request_mempool(false, PeerPermissions::MEMPOOL));
        assert!(peer_can_request_mempool(
            false,
            PeerPermissions::BLOOM_FILTER
        ));
    }

    #[test]
    fn address_relay_targets_only_eligible_negotiated_peers() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            blocks_dir: None,
            blocks_dir_explicit: false,
            blocks_xor: false,
            capture_messages: false,
            debug_log_path: std::path::PathBuf::from("debug.log"),
            pid_path: std::path::PathBuf::from("bitcoind.pid"),
            logging: Default::default(),
            debug_log_file_enabled: false,
            print_to_console: false,
            shrink_debug_file: false,
            settings_path: None,
            asmap: None,
            minimum_chain_work: None,
            assume_valid: None,
            check_blocks: None,
            check_level: None,
            check_block_index: 0,
            check_mempool: 0,
            check_addrman: 0,
            max_tip_age_secs: 24 * 60 * 60,
            mock_time: None,
            stop_at_height: 0,
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
            script_check_threads: 0,
            block_reconstruction_extra_txn: 100,
            user_agent_comments: Vec::new(),
            startup_notify: None,
            block_notify: None,
            shutdown_notify: None,
            alert_notify: None,
            max_sig_cache_mib: 32,
            accept_stale_fee_estimates: false,
            rpc_whitelist: std::collections::HashMap::new(),
            rpc_whitelist_default: false,
            electrum_bind: None,
            rest: false,
            listen: true,
            dnsseed: true,
            fixed_seeds: false,
            force_dns_seed: false,
            onlynet: Vec::new(),
            proxy: None,
            i2p_sam: None,
            onion_proxy: None,
            listen_onion: false,
            tor_control: "127.0.0.1:9051".parse().unwrap(),
            tor_password: None,
            i2p_accept_incoming: false,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            rbf_policy: crate::mempool::RbfPolicy::Always,
            truc_policy: crate::mempool::TrucPolicy::Accept,
            cjdns_reachable: false,
            prune: 0,
            fast_prune: false,
            natpmp: false,
            reindex: false,
            reindex_chainstate: false,
            load_blocks: Vec::new(),
            stop_after_block_import: false,
            txindex: false,
            txospenderindex: false,
            max_mempool_mb: 300,
            cluster_count: 64,
            cluster_size_vbytes: 101_000,
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
            signet_seed_nodes: Vec::new(),
            deployment_parameters: None,
            max_peers: 4,
            max_receive_buffer: 5_000,
            max_send_buffer: 1_000,
            max_upload_target: 0,
            peer_bloom_filters: false,
            peer_timeout_secs: 60,
            ban_time_secs: 86_400,
            deprecated_rpcs: std::collections::HashSet::new(),
            connect_timeout_ms: 5_000,
            block_max_weight: 4_000_000,
            block_reserved_weight: 8_000,
            block_version: None,
            block_min_tx_fee_sat_per_kvb: 1,
            min_relay_tx_fee_sat_per_kvb: 100,
            incremental_relay_fee_sat_per_kvb: 100,
            dust_relay_fee_sat_per_kvb: 3_000,
            max_datacarrier_bytes: Some(100_000),
            bytes_per_sigop: 20,
            permit_bare_multisig: true,
            zmq: crate::config::ZmqConfig::default(),
        })
        .unwrap();
        let (origin_sender, mut origin_receiver) = mpsc::unbounded_channel();
        let (outbound_sender, mut outbound_receiver) = mpsc::unbounded_channel();
        let (inbound_sender, mut inbound_receiver) = mpsc::unbounded_channel();
        let (block_sender, mut block_receiver) = mpsc::unbounded_channel();
        node.register_peer(1, "127.0.0.1:18441".parse().unwrap(), true, origin_sender);
        node.register_peer(2, "8.8.8.8:18442".parse().unwrap(), false, outbound_sender);
        node.register_peer(3, "127.0.0.1:18443".parse().unwrap(), true, inbound_sender);
        node.register_peer(4, "8.8.8.8:18444".parse().unwrap(), false, block_sender);
        node.update_peer_version(2, 70016, 0, "/outbound/", 0, true);
        node.update_peer_version(3, 70016, 0, "/inbound/", 0, true);
        node.update_peer_version(4, 70016, 0, "/block/", 0, true);
        node.enable_peer_address_relay(3);
        node.set_peer_connection_type(4, "block-relay-only");

        node.relay_peer_addresses(
            1,
            vec![(
                NetworkEndpoint::Ip("192.0.2.10:18444".parse().unwrap()),
                9,
                123,
            )],
        );

        assert!(origin_receiver.try_recv().is_err());
        assert!(matches!(
            outbound_receiver.try_recv().unwrap(),
            PeerCommand::RelayAddresses { ref addresses } if addresses.len() == 1
        ));
        assert!(matches!(
            inbound_receiver.try_recv().unwrap(),
            PeerCommand::RelayAddresses { ref addresses } if addresses.len() == 1
        ));
        assert!(block_receiver.try_recv().is_err());
    }

    #[test]
    fn address_relay_batches_legacy_and_addrv2_payloads() {
        let addresses = vec![
            (
                NetworkEndpoint::Ip("192.0.2.10:18444".parse().unwrap()),
                1,
                123,
            ),
            (
                NetworkEndpoint::Ip("[2001:db8::10]:18444".parse().unwrap()),
                8,
                456,
            ),
            (
                NetworkEndpoint::OnionV3 {
                    address: [6; 32],
                    port: 18446,
                },
                16,
                789,
            ),
        ];
        let Message::Addr(legacy) = relay_address_message(&addresses, false) else {
            panic!("expected legacy address message");
        };
        assert_eq!(legacy.len(), 2);
        assert_eq!(legacy[0].services, 1);
        assert_eq!(legacy[1].time, 456);

        let Message::AddrV2(addrv2) = relay_address_message(&addresses, true) else {
            panic!("expected ADDRv2 message");
        };
        assert_eq!(addrv2.len(), 3);
        assert_eq!(addrv2[0].services, 1);
        assert_eq!(addrv2[1].time, 456);
        assert_eq!(addrv2[2].network, 4);
        assert_eq!(addrv2[2].address, vec![6; 32]);
    }

    #[test]
    fn builds_a_bounded_basic_filter_range() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            blocks_dir: None,
            blocks_dir_explicit: false,
            blocks_xor: false,
            capture_messages: false,
            debug_log_path: std::path::PathBuf::from("debug.log"),
            pid_path: std::path::PathBuf::from("bitcoind.pid"),
            logging: Default::default(),
            debug_log_file_enabled: false,
            print_to_console: false,
            shrink_debug_file: false,
            settings_path: None,
            asmap: None,
            minimum_chain_work: None,
            assume_valid: None,
            check_blocks: None,
            check_level: None,
            check_block_index: 0,
            check_mempool: 0,
            check_addrman: 0,
            max_tip_age_secs: 24 * 60 * 60,
            mock_time: None,
            stop_at_height: 0,
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
            script_check_threads: 0,
            block_reconstruction_extra_txn: 100,
            user_agent_comments: Vec::new(),
            startup_notify: None,
            block_notify: None,
            shutdown_notify: None,
            alert_notify: None,
            max_sig_cache_mib: 32,
            accept_stale_fee_estimates: false,
            rpc_whitelist: std::collections::HashMap::new(),
            rpc_whitelist_default: false,
            electrum_bind: None,
            rest: false,
            listen: true,
            dnsseed: true,
            fixed_seeds: false,
            force_dns_seed: false,
            onlynet: Vec::new(),
            proxy: None,
            i2p_sam: None,
            onion_proxy: None,
            listen_onion: false,
            tor_control: "127.0.0.1:9051".parse().unwrap(),
            tor_password: None,
            i2p_accept_incoming: false,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            rbf_policy: crate::mempool::RbfPolicy::Always,
            truc_policy: crate::mempool::TrucPolicy::Accept,
            cjdns_reachable: false,
            prune: 0,
            fast_prune: false,
            natpmp: false,
            reindex: false,
            reindex_chainstate: false,
            load_blocks: Vec::new(),
            stop_after_block_import: false,
            txindex: false,
            txospenderindex: false,
            max_mempool_mb: 300,
            cluster_count: 64,
            cluster_size_vbytes: 101_000,
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
            signet_seed_nodes: Vec::new(),
            deployment_parameters: None,
            max_peers: 1,
            max_receive_buffer: 5_000,
            max_send_buffer: 1_000,
            max_upload_target: 0,
            peer_bloom_filters: false,
            peer_timeout_secs: 60,
            ban_time_secs: 86_400,
            deprecated_rpcs: std::collections::HashSet::new(),
            connect_timeout_ms: 5_000,
            block_max_weight: 4_000_000,
            block_reserved_weight: 8_000,
            block_version: None,
            block_min_tx_fee_sat_per_kvb: 1,
            min_relay_tx_fee_sat_per_kvb: 100,
            incremental_relay_fee_sat_per_kvb: 100,
            dust_relay_fee_sat_per_kvb: 3_000,
            max_datacarrier_bytes: Some(100_000),
            bytes_per_sigop: 20,
            permit_bare_multisig: true,
            zmq: crate::config::ZmqConfig::default(),
        })
        .unwrap();
        let stop_hash = node.chain.read().best_hash();
        let range = basic_filter_range(&node, 0, stop_hash, 1).unwrap().unwrap();
        assert_eq!(range.stop_hash, stop_hash);
        assert_eq!(range.filters.len(), 1);
        assert_eq!(range.previous_filter_header, FilterHeader::all_zeros());
        assert!(!range.filters[0].1.is_empty());
        assert!(
            basic_filter_range(&node, 1, stop_hash, 1)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn compact_filter_request_validation_matches_core_disconnect_boundaries() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(private_broadcast_test_config(
            directory.path(),
            false,
            Vec::new(),
        ))
        .unwrap();
        let stop_hash = node.chain.read().best_hash();

        assert!(validate_basic_filter_request(&node, 255, 0, stop_hash, 1_000).is_err());
        assert!(validate_basic_filter_request(&node, 0, 0, BlockHash::all_zeros(), 1_000).is_err());
        assert!(validate_basic_filter_request(&node, 0, 1, stop_hash, 1_000).is_err());
        assert!(validate_basic_filter_request(&node, 0, 0, stop_hash, 0).is_err());
        assert!(validate_basic_filter_request(&node, 0, 0, stop_hash, 1_000).is_ok());
    }

    #[test]
    fn bloom_filter_matches_core_murmur_and_bit_order() {
        let mut filter = BloomFilter::from_message(FilterLoad {
            filter: vec![0; 3],
            hash_funcs: 5,
            tweak: 0,
            flags: BloomFlags::All,
        })
        .unwrap();
        for value in [
            "99108ad8ed9bb6274d3980bab5a85c048f0950c8",
            "b5a2c786d9ef4658287ced5914b37a1b4aa32eee",
            "b9300670b4c5366e95b2699e8b18bc75e5f729c5",
        ] {
            filter.insert(&hex::decode(value).unwrap());
        }
        assert_eq!(filter.data, hex::decode("614e9b").unwrap());
        assert!(
            !filter.contains(&hex::decode("19108ad8ed9bb6274d3980bab5a85c048f0950c8").unwrap())
        );
    }

    #[test]
    fn known_transaction_inventory_is_bounded_and_deduplicated() {
        let first = BlockHash::from_byte_array([1; 32]);
        let second = BlockHash::from_byte_array([2; 32]);
        let mut known = KnownTxInventory::new();
        assert!(!known.contains(&first));
        known.insert(&first);
        assert!(known.contains(&first));
        assert_eq!(known.inserted_in_generation, 1);
        known.insert(&first);
        assert_eq!(known.inserted_in_generation, 1);
        known.insert(&second);
        assert!(known.contains(&second));
        assert!(
            known
                .generations
                .iter()
                .all(|generation| { generation.len() == KNOWN_TX_FILTER_BITS / 8 })
        );
    }

    #[test]
    fn fee_filter_rates_are_measured_in_sat_per_kilobyte() {
        assert_eq!(fee_rate_sat_per_kvb(1_000, 250), 4_000);
        assert_eq!(fee_rate_sat_per_kvb(1, 0), i64::MAX);
    }

    #[test]
    fn compact_block_announcements_prefill_the_coinbase() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            blocks_dir: None,
            blocks_dir_explicit: false,
            blocks_xor: false,
            capture_messages: false,
            debug_log_path: std::path::PathBuf::from("debug.log"),
            pid_path: std::path::PathBuf::from("bitcoind.pid"),
            logging: Default::default(),
            debug_log_file_enabled: false,
            print_to_console: false,
            shrink_debug_file: false,
            settings_path: None,
            asmap: None,
            minimum_chain_work: None,
            assume_valid: None,
            check_blocks: None,
            check_level: None,
            check_block_index: 0,
            check_mempool: 0,
            check_addrman: 0,
            max_tip_age_secs: 24 * 60 * 60,
            mock_time: None,
            stop_at_height: 0,
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
            script_check_threads: 0,
            block_reconstruction_extra_txn: 100,
            user_agent_comments: Vec::new(),
            startup_notify: None,
            block_notify: None,
            shutdown_notify: None,
            alert_notify: None,
            max_sig_cache_mib: 32,
            accept_stale_fee_estimates: false,
            rpc_whitelist: std::collections::HashMap::new(),
            rpc_whitelist_default: false,
            electrum_bind: None,
            rest: false,
            listen: true,
            dnsseed: true,
            fixed_seeds: false,
            force_dns_seed: false,
            onlynet: Vec::new(),
            proxy: None,
            i2p_sam: None,
            onion_proxy: None,
            listen_onion: false,
            tor_control: "127.0.0.1:9051".parse().unwrap(),
            tor_password: None,
            i2p_accept_incoming: false,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            rbf_policy: crate::mempool::RbfPolicy::Always,
            truc_policy: crate::mempool::TrucPolicy::Accept,
            cjdns_reachable: false,
            prune: 0,
            fast_prune: false,
            natpmp: false,
            reindex: false,
            reindex_chainstate: false,
            load_blocks: Vec::new(),
            stop_after_block_import: false,
            txindex: false,
            txospenderindex: false,
            max_mempool_mb: 300,
            cluster_count: 64,
            cluster_size_vbytes: 101_000,
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
            signet_seed_nodes: Vec::new(),
            deployment_parameters: None,
            max_peers: 1,
            max_receive_buffer: 5_000,
            max_send_buffer: 1_000,
            max_upload_target: 0,
            peer_bloom_filters: false,
            peer_timeout_secs: 60,
            ban_time_secs: 86_400,
            deprecated_rpcs: std::collections::HashSet::new(),
            connect_timeout_ms: 5_000,
            block_max_weight: 4_000_000,
            block_reserved_weight: 8_000,
            block_version: None,
            block_min_tx_fee_sat_per_kvb: 1,
            min_relay_tx_fee_sat_per_kvb: 100,
            incremental_relay_fee_sat_per_kvb: 100,
            dust_relay_fee_sat_per_kvb: 3_000,
            max_datacarrier_bytes: Some(100_000),
            bytes_per_sigop: 20,
            permit_bare_multisig: true,
            zmq: crate::config::ZmqConfig::default(),
        })
        .unwrap();
        let hash = node.chain.read().best_hash();
        let compact = compact_block_for_inventory(
            &node,
            &Inventory {
                kind: InventoryType::WitnessBlock,
                hash,
            },
            2,
        )
        .unwrap()
        .unwrap();
        assert_eq!(compact.header.block_hash(), hash);
        assert_eq!(compact.prefilled_txs.len(), 1);
        assert_eq!(compact.prefilled_txs[0].idx, 0);
        assert!(
            compact_block_for_inventory(
                &node,
                &Inventory {
                    kind: InventoryType::WitnessTransaction,
                    hash,
                },
                2,
            )
            .unwrap()
            .is_none()
        );
        let coinbase = &compact.prefilled_txs[0].tx;
        let legacy = transaction_for_getdata_tip(
            &node,
            &Inventory {
                kind: InventoryType::Transaction,
                hash: BlockHash::from_raw_hash(coinbase.compute_txid().to_raw_hash()),
            },
        )
        .unwrap()
        .unwrap();
        assert_eq!(legacy.compute_txid(), coinbase.compute_txid());
        let witness = transaction_for_getdata_tip(
            &node,
            &Inventory {
                kind: InventoryType::WitnessTransaction,
                hash: BlockHash::from_raw_hash(coinbase.compute_wtxid().to_raw_hash()),
            },
        )
        .unwrap()
        .unwrap();
        assert_eq!(witness.compute_wtxid(), coinbase.compute_wtxid());
    }

    #[test]
    fn bloom_filter_matches_script_elements_and_updates_spends() {
        use bitcoin::Amount;
        use bitcoin::absolute::LockTime;
        use bitcoin::blockdata::script::ScriptBuf;
        use bitcoin::blockdata::transaction::{OutPoint, TxIn, TxOut, Version};
        use bitcoin::blockdata::witness::Witness;

        let transaction = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::null(),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![
                TxOut {
                    value: Amount::from_sat(1),
                    script_pubkey: ScriptBuf::from_bytes(vec![1, 0x42]),
                },
                TxOut {
                    value: Amount::from_sat(1),
                    script_pubkey: ScriptBuf::from_bytes(vec![1, 0x43]),
                },
            ],
        };
        let mut filter = BloomFilter::from_message(FilterLoad {
            filter: vec![0; 32],
            hash_funcs: 5,
            tweak: 0,
            flags: BloomFlags::All,
        })
        .unwrap();
        filter.insert(&[0x42]);
        assert!(filter.is_relevant_and_update(&transaction));

        let spending = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(transaction.compute_txid(), 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(1),
                script_pubkey: ScriptBuf::new(),
            }],
        };
        assert!(filter.is_relevant_and_update(&spending));

        let mut txid_filter = BloomFilter::from_message(FilterLoad {
            filter: vec![0; 32],
            hash_funcs: 5,
            tweak: 0,
            flags: BloomFlags::All,
        })
        .unwrap();
        txid_filter.insert(&serialize(&transaction.compute_txid()));
        txid_filter.insert(&[0x42]);
        txid_filter.insert(&[0x43]);
        assert!(txid_filter.is_relevant_and_update(&transaction));
        assert!(txid_filter.contains(&serialize(&OutPoint::new(transaction.compute_txid(), 0,))));
        assert!(txid_filter.contains(&serialize(&OutPoint::new(transaction.compute_txid(), 1,))));
    }

    #[test]
    fn bloom_filter_load_and_clear_enable_transaction_relay() {
        let bloom_filter = parking_lot::Mutex::new(None);
        let relay_transactions = parking_lot::Mutex::new(false);
        let filter = FilterLoad {
            filter: vec![0; 32],
            hash_funcs: 5,
            tweak: 0,
            flags: BloomFlags::All,
        };
        install_bloom_filter(&bloom_filter, &relay_transactions, filter).unwrap();
        assert!(bloom_filter.lock().is_some());
        assert!(*relay_transactions.lock());

        *relay_transactions.lock() = false;
        clear_bloom_filter(&bloom_filter, &relay_transactions);
        assert!(bloom_filter.lock().is_none());
        assert!(*relay_transactions.lock());

        let invalid_filter = FilterLoad {
            filter: vec![0; MAX_BLOOM_FILTER_SIZE + 1],
            hash_funcs: 5,
            tweak: 0,
            flags: BloomFlags::All,
        };
        *relay_transactions.lock() = false;
        assert!(install_bloom_filter(&bloom_filter, &relay_transactions, invalid_filter).is_err());
        assert!(!*relay_transactions.lock());
    }

    #[test]
    fn malformed_bloom_filter_adds_are_ignored_without_mutating_state() {
        let bloom_filter = parking_lot::Mutex::new(None);
        assert!(!apply_bloom_filter_add(&bloom_filter, &[0x42]));

        let filter = FilterLoad {
            filter: vec![0; 32],
            hash_funcs: 5,
            tweak: 0,
            flags: BloomFlags::All,
        };
        let relay_transactions = parking_lot::Mutex::new(false);
        install_bloom_filter(&bloom_filter, &relay_transactions, filter).unwrap();

        assert!(!apply_bloom_filter_add(
            &bloom_filter,
            &vec![0; MAX_BLOOM_ELEMENT_SIZE + 1]
        ));
        assert!(apply_bloom_filter_add(&bloom_filter, &[0x42]));
        assert!(bloom_filter.lock().as_ref().unwrap().contains(&[0x42]));
    }

    #[test]
    fn peer_counters_track_wire_traffic_and_pings() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            blocks_dir: None,
            blocks_dir_explicit: false,
            blocks_xor: false,
            capture_messages: false,
            debug_log_path: std::path::PathBuf::from("debug.log"),
            pid_path: std::path::PathBuf::from("bitcoind.pid"),
            logging: Default::default(),
            debug_log_file_enabled: false,
            print_to_console: false,
            shrink_debug_file: false,
            settings_path: None,
            asmap: None,
            minimum_chain_work: None,
            assume_valid: None,
            check_blocks: None,
            check_level: None,
            check_block_index: 0,
            check_mempool: 0,
            check_addrman: 0,
            max_tip_age_secs: 24 * 60 * 60,
            mock_time: None,
            stop_at_height: 0,
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
            script_check_threads: 0,
            block_reconstruction_extra_txn: 100,
            user_agent_comments: Vec::new(),
            startup_notify: None,
            block_notify: None,
            shutdown_notify: None,
            alert_notify: None,
            max_sig_cache_mib: 32,
            accept_stale_fee_estimates: false,
            rpc_whitelist: std::collections::HashMap::new(),
            rpc_whitelist_default: false,
            electrum_bind: None,
            rest: false,
            listen: true,
            dnsseed: true,
            fixed_seeds: false,
            force_dns_seed: false,
            onlynet: Vec::new(),
            proxy: None,
            i2p_sam: None,
            onion_proxy: None,
            listen_onion: false,
            tor_control: "127.0.0.1:9051".parse().unwrap(),
            tor_password: None,
            i2p_accept_incoming: false,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            rbf_policy: crate::mempool::RbfPolicy::Always,
            truc_policy: crate::mempool::TrucPolicy::Accept,
            cjdns_reachable: false,
            prune: 0,
            fast_prune: false,
            natpmp: false,
            reindex: false,
            reindex_chainstate: false,
            load_blocks: Vec::new(),
            stop_after_block_import: false,
            txindex: false,
            txospenderindex: false,
            max_mempool_mb: 300,
            cluster_count: 64,
            cluster_size_vbytes: 101_000,
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
            signet_seed_nodes: Vec::new(),
            deployment_parameters: None,
            max_peers: 1,
            max_receive_buffer: 5_000,
            max_send_buffer: 1_000,
            max_upload_target: 0,
            peer_bloom_filters: false,
            peer_timeout_secs: 60,
            ban_time_secs: 86_400,
            deprecated_rpcs: std::collections::HashSet::new(),
            connect_timeout_ms: 5_000,
            block_max_weight: 4_000_000,
            block_reserved_weight: 8_000,
            block_version: None,
            block_min_tx_fee_sat_per_kvb: 1,
            min_relay_tx_fee_sat_per_kvb: 100,
            incremental_relay_fee_sat_per_kvb: 100,
            dust_relay_fee_sat_per_kvb: 3_000,
            max_datacarrier_bytes: Some(100_000),
            bytes_per_sigop: 20,
            permit_bare_multisig: true,
            zmq: crate::config::ZmqConfig::default(),
        })
        .unwrap();
        let (sender, mut receiver) = mpsc::unbounded_channel();
        node.register_peer(7, "127.0.0.1:18444".parse().unwrap(), false, sender);
        node.record_bytes_sent(7, 42, "ping");
        node.record_bytes_received(7, 19, "tx");
        node.record_peer_transaction(7);
        node.record_peer_block(7, node.chain.read().best_hash());
        node.record_peer_inv_sequence(7, 12);
        node.update_peer_version(7, 70016, 0, "/peer/", 0, false);
        node.update_peer_fee_filter(7, 4_000);
        assert_eq!(node.total_bytes_sent(), 42);
        assert_eq!(node.total_bytes_received(), 19);
        let peer = node.peer_infos().pop().expect("registered peer");
        assert_eq!(peer.bytes_sent, 42);
        assert_eq!(peer.bytes_received, 19);
        assert_eq!(peer.bytes_sent_per_msg.get("ping"), Some(&42));
        assert_eq!(peer.bytes_received_per_msg.get("tx"), Some(&19));
        assert!(peer.last_transaction > 0);
        assert!(peer.last_block > 0);
        assert_eq!(peer.last_inv_sequence, 12);
        assert!(!peer.relay_transactions);
        assert_eq!(peer.min_fee_filter, 4_000);

        node.update_peer_relay_transactions(7, true);
        assert!(node.peer_infos()[0].relay_transactions);

        node.ping_peers();
        let PeerCommand::Ping(nonce) = receiver.try_recv().unwrap() else {
            panic!("expected a ping command");
        };
        assert!(node.ping_timed_out(7, Duration::ZERO));
        node.ping_peers();
        assert!(receiver.try_recv().is_err());
        node.record_pong(7, nonce);
        assert!(node.peer_infos()[0].ping_time.is_some());
        assert!(node.peer_infos()[0].min_ping.is_some());
        node.unregister_peer(7);
        assert_eq!(
            node.known_addresses()
                .into_iter()
                .find(|known| known.address == "127.0.0.1:18444".parse().unwrap())
                .expect("disconnected peer remains in address table")
                .id,
            0
        );
    }

    #[test]
    fn address_messages_round_trip_into_the_known_address_table() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            blocks_dir: None,
            blocks_dir_explicit: false,
            blocks_xor: false,
            capture_messages: false,
            debug_log_path: std::path::PathBuf::from("debug.log"),
            pid_path: std::path::PathBuf::from("bitcoind.pid"),
            logging: Default::default(),
            debug_log_file_enabled: false,
            print_to_console: false,
            shrink_debug_file: false,
            settings_path: None,
            asmap: None,
            minimum_chain_work: None,
            assume_valid: None,
            check_blocks: None,
            check_level: None,
            check_block_index: 0,
            check_mempool: 0,
            check_addrman: 0,
            max_tip_age_secs: 24 * 60 * 60,
            mock_time: None,
            stop_at_height: 0,
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
            script_check_threads: 0,
            block_reconstruction_extra_txn: 100,
            user_agent_comments: Vec::new(),
            startup_notify: None,
            block_notify: None,
            shutdown_notify: None,
            alert_notify: None,
            max_sig_cache_mib: 32,
            accept_stale_fee_estimates: false,
            rpc_whitelist: std::collections::HashMap::new(),
            rpc_whitelist_default: false,
            electrum_bind: None,
            rest: false,
            listen: true,
            dnsseed: true,
            fixed_seeds: false,
            force_dns_seed: false,
            onlynet: Vec::new(),
            proxy: None,
            i2p_sam: None,
            onion_proxy: None,
            listen_onion: false,
            tor_control: "127.0.0.1:9051".parse().unwrap(),
            tor_password: None,
            i2p_accept_incoming: false,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            rbf_policy: crate::mempool::RbfPolicy::Always,
            truc_policy: crate::mempool::TrucPolicy::Accept,
            cjdns_reachable: false,
            prune: 0,
            fast_prune: false,
            natpmp: false,
            reindex: false,
            reindex_chainstate: false,
            load_blocks: Vec::new(),
            stop_after_block_import: false,
            txindex: false,
            txospenderindex: false,
            max_mempool_mb: 300,
            cluster_count: 64,
            cluster_size_vbytes: 101_000,
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
            signet_seed_nodes: Vec::new(),
            deployment_parameters: None,
            max_peers: 1,
            max_receive_buffer: 5_000,
            max_send_buffer: 1_000,
            max_upload_target: 0,
            peer_bloom_filters: false,
            peer_timeout_secs: 60,
            ban_time_secs: 86_400,
            deprecated_rpcs: std::collections::HashSet::new(),
            connect_timeout_ms: 5_000,
            block_max_weight: 4_000_000,
            block_reserved_weight: 8_000,
            block_version: None,
            block_min_tx_fee_sat_per_kvb: 1,
            min_relay_tx_fee_sat_per_kvb: 100,
            incremental_relay_fee_sat_per_kvb: 100,
            dust_relay_fee_sat_per_kvb: 3_000,
            max_datacarrier_bytes: Some(100_000),
            bytes_per_sigop: 20,
            permit_bare_multisig: true,
            zmq: crate::config::ZmqConfig::default(),
        })
        .unwrap();
        let legacy = wire::NetworkAddress {
            time: 123,
            services: wire::NODE_NETWORK,
            address: socket_address_bytes("192.0.2.10:18444".parse().unwrap()),
            port: 18444,
        };
        let legacy_socket = socket_address_from_legacy(&legacy).unwrap();
        assert!(node.remember_address(legacy_socket, legacy.services, u64::from(legacy.time)));
        assert!(!node.remember_address(legacy_socket, legacy.services, u64::from(legacy.time)));
        let v2 = network_address_v2(
            &NetworkEndpoint::Ip("[2001:db8::10]:18444".parse().unwrap()),
            456,
            wire::NODE_NETWORK | wire::NODE_WITNESS,
        )
        .unwrap();
        let v2_endpoint = NetworkEndpoint::from_addr_v2(v2.network, &v2.address, v2.port).unwrap();
        node.remember_network_address(v2_endpoint.clone(), v2.services, u64::from(v2.time));

        let addresses = node.known_addresses();
        assert!(addresses.iter().any(|peer| peer.address == legacy_socket));
        assert!(
            addresses
                .iter()
                .any(|peer| peer.address == v2_endpoint.socket_addr().unwrap())
        );
        assert_eq!(addresses.iter().filter(|peer| peer.id == 0).count(), 2);
    }

    #[test]
    fn discovery_candidates_skip_connected_added_and_in_flight_addresses() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            blocks_dir: None,
            blocks_dir_explicit: false,
            blocks_xor: false,
            capture_messages: false,
            debug_log_path: std::path::PathBuf::from("debug.log"),
            pid_path: std::path::PathBuf::from("bitcoind.pid"),
            logging: Default::default(),
            debug_log_file_enabled: false,
            print_to_console: false,
            shrink_debug_file: false,
            settings_path: None,
            asmap: None,
            minimum_chain_work: None,
            assume_valid: None,
            check_blocks: None,
            check_level: None,
            check_block_index: 0,
            check_mempool: 0,
            check_addrman: 0,
            max_tip_age_secs: 24 * 60 * 60,
            mock_time: None,
            stop_at_height: 0,
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
            script_check_threads: 0,
            block_reconstruction_extra_txn: 100,
            user_agent_comments: Vec::new(),
            startup_notify: None,
            block_notify: None,
            shutdown_notify: None,
            alert_notify: None,
            max_sig_cache_mib: 32,
            accept_stale_fee_estimates: false,
            rpc_whitelist: std::collections::HashMap::new(),
            rpc_whitelist_default: false,
            electrum_bind: None,
            rest: false,
            listen: true,
            dnsseed: true,
            fixed_seeds: false,
            force_dns_seed: false,
            onlynet: Vec::new(),
            proxy: None,
            i2p_sam: None,
            onion_proxy: None,
            listen_onion: false,
            tor_control: "127.0.0.1:9051".parse().unwrap(),
            tor_password: None,
            i2p_accept_incoming: false,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            rbf_policy: crate::mempool::RbfPolicy::Always,
            truc_policy: crate::mempool::TrucPolicy::Accept,
            cjdns_reachable: false,
            prune: 0,
            fast_prune: false,
            natpmp: false,
            reindex: false,
            reindex_chainstate: false,
            load_blocks: Vec::new(),
            stop_after_block_import: false,
            txindex: false,
            txospenderindex: false,
            max_mempool_mb: 300,
            cluster_count: 64,
            cluster_size_vbytes: 101_000,
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
            signet_seed_nodes: Vec::new(),
            deployment_parameters: None,
            max_peers: 4,
            max_receive_buffer: 5_000,
            max_send_buffer: 1_000,
            max_upload_target: 0,
            peer_bloom_filters: false,
            peer_timeout_secs: 60,
            ban_time_secs: 86_400,
            deprecated_rpcs: std::collections::HashSet::new(),
            connect_timeout_ms: 5_000,
            block_max_weight: 4_000_000,
            block_reserved_weight: 8_000,
            block_version: None,
            block_min_tx_fee_sat_per_kvb: 1,
            min_relay_tx_fee_sat_per_kvb: 100,
            incremental_relay_fee_sat_per_kvb: 100,
            dust_relay_fee_sat_per_kvb: 3_000,
            max_datacarrier_bytes: Some(100_000),
            bytes_per_sigop: 20,
            permit_bare_multisig: true,
            zmq: crate::config::ZmqConfig::default(),
        })
        .unwrap();
        let added = "192.0.2.10:18444".parse().unwrap();
        let connected = "192.0.2.11:18444".parse().unwrap();
        let in_flight = "192.0.2.12:18444".parse().unwrap();
        let eligible = "192.0.2.13:18444".parse().unwrap();
        for address in [added, connected, in_flight, eligible] {
            assert!(node.add_peer_address(address, false));
        }
        assert!(node.add_node(added));
        let (sender, _receiver) = mpsc::unbounded_channel();
        node.register_peer(7, connected, false, sender);
        let attempts = Arc::new(parking_lot::Mutex::new(HashSet::from([
            NetworkEndpoint::Ip(in_flight),
        ])));

        assert_eq!(
            select_discovery_addresses(&node, 4, &attempts),
            vec![eligible]
        );
    }

    #[test]
    fn delayed_dns_seed_fallback_waits_for_known_peers() {
        assert!(!should_query_dns_seed_fallback(
            false,
            DNS_SEED_FALLBACK_DELAY,
            0
        ));
        assert!(!should_query_dns_seed_fallback(
            true,
            DNS_SEED_FALLBACK_DELAY - Duration::from_secs(1),
            0
        ));
        assert!(!should_query_dns_seed_fallback(
            true,
            DNS_SEED_FALLBACK_DELAY,
            DNS_SEED_OUTBOUND_THRESHOLD
        ));
        assert!(should_query_dns_seed_fallback(
            true,
            DNS_SEED_FALLBACK_DELAY,
            DNS_SEED_OUTBOUND_THRESHOLD - 1
        ));
    }

    #[test]
    fn signet_seednode_overrides_only_signet_dns_seeds() {
        let custom = vec!["first.example".to_owned(), "second.example".to_owned()];
        assert_eq!(dns_seed_hosts(Network::Signet, &custom), custom);
        assert_eq!(
            dns_seed_hosts(Network::Signet, &[]),
            vec![
                "seed.signet.bitcoin.sprovoost.nl",
                "seed.signet.achownodes.xyz",
            ]
        );
        assert_eq!(
            dns_seed_hosts(Network::Bitcoin, &custom),
            vec![
                "seed.bitcoin.sipa.be",
                "dnsseed.bluematt.me",
                "seed.bitcoinstats.com",
                "seed.bitcoin.jonasschnelli.ch",
                "seed.btc.petertodd.org",
                "seed.bitcoin.sprovoost.nl",
                "dnsseed.emzy.de",
                "seed.bitcoin.wiz.biz",
            ]
        );
    }

    #[test]
    fn signet_seednode_supports_core_host_and_port_syntax() {
        assert_eq!(
            dns_seed_target("seed.example", 38333),
            ("seed.example", 38333)
        );
        assert_eq!(
            dns_seed_target("seed.example:18444", 38333),
            ("seed.example", 18444)
        );
        assert_eq!(
            dns_seed_target("[2001:db8::1]:18444", 38333),
            ("2001:db8::1", 18444)
        );
        assert_eq!(
            dns_seed_target("seed.example:not-a-port", 38333),
            ("seed.example:not-a-port", 38333)
        );
    }

    #[test]
    fn fixed_seed_fallback_waits_for_configured_seed_sources() {
        assert!(should_add_fixed_seed_fallback(
            true,
            false,
            false,
            false,
            Duration::ZERO,
        ));
        assert!(!should_add_fixed_seed_fallback(
            true,
            false,
            true,
            false,
            Duration::ZERO,
        ));
        assert!(!should_add_fixed_seed_fallback(
            true,
            false,
            false,
            true,
            Duration::ZERO,
        ));
        assert!(!should_add_fixed_seed_fallback(
            true,
            true,
            false,
            false,
            FIXED_SEED_FALLBACK_DELAY - Duration::from_secs(1),
        ));
        assert!(should_add_fixed_seed_fallback(
            true,
            true,
            false,
            false,
            FIXED_SEED_FALLBACK_DELAY,
        ));
        assert!(!should_add_fixed_seed_fallback(
            false,
            false,
            false,
            false,
            FIXED_SEED_FALLBACK_DELAY,
        ));
    }

    #[test]
    fn fixed_seed_fallback_preserves_core_bip155_networks() {
        let main = fixed_seed_endpoints(Network::Bitcoin);
        assert!(main.iter().any(|endpoint| {
            matches!(endpoint, NetworkEndpoint::Ip(address) if address.is_ipv4())
        }));
        assert!(
            main.iter().any(
                |endpoint| matches!(endpoint, NetworkEndpoint::Ip(address) if address.is_ipv6())
            )
        );
        assert!(
            main.iter()
                .any(|endpoint| matches!(endpoint, NetworkEndpoint::OnionV3 { .. }))
        );
        assert!(
            main.iter()
                .any(|endpoint| matches!(endpoint, NetworkEndpoint::I2p { port: 0, .. }))
        );
        assert!(
            main.iter()
                .any(|endpoint| matches!(endpoint, NetworkEndpoint::Cjdns { .. }))
        );
        assert!(!fixed_seed_addresses(Network::Bitcoin).is_empty());
        assert!(!fixed_seed_addresses(Network::Testnet).is_empty());
        assert!(!fixed_seed_addresses(Network::Testnet4).is_empty());
        assert!(!fixed_seed_addresses(Network::Signet).is_empty());
        assert!(fixed_seed_addresses(Network::Regtest).is_empty());
    }

    #[test]
    fn typed_discovery_candidates_preserve_non_ip_endpoints() {
        let directory = tempfile::tempdir().unwrap();
        let node = Node::open(crate::config::Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            blocks_dir: None,
            blocks_dir_explicit: false,
            blocks_xor: false,
            capture_messages: false,
            debug_log_path: std::path::PathBuf::from("debug.log"),
            pid_path: std::path::PathBuf::from("bitcoind.pid"),
            logging: Default::default(),
            debug_log_file_enabled: false,
            print_to_console: false,
            shrink_debug_file: false,
            settings_path: None,
            asmap: None,
            minimum_chain_work: None,
            assume_valid: None,
            check_blocks: None,
            check_level: None,
            check_block_index: 0,
            check_mempool: 0,
            check_addrman: 0,
            max_tip_age_secs: 24 * 60 * 60,
            mock_time: None,
            stop_at_height: 0,
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
            script_check_threads: 0,
            block_reconstruction_extra_txn: 100,
            user_agent_comments: Vec::new(),
            startup_notify: None,
            block_notify: None,
            shutdown_notify: None,
            alert_notify: None,
            max_sig_cache_mib: 32,
            accept_stale_fee_estimates: false,
            rpc_whitelist: std::collections::HashMap::new(),
            rpc_whitelist_default: false,
            electrum_bind: None,
            rest: false,
            listen: true,
            dnsseed: false,
            fixed_seeds: false,
            force_dns_seed: false,
            onlynet: Vec::new(),
            proxy: Some("127.0.0.1:9050".parse().unwrap()),
            i2p_sam: None,
            onion_proxy: None,
            listen_onion: false,
            tor_control: "127.0.0.1:9051".parse().unwrap(),
            tor_password: None,
            i2p_accept_incoming: false,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            rbf_policy: crate::mempool::RbfPolicy::Always,
            truc_policy: crate::mempool::TrucPolicy::Accept,
            cjdns_reachable: false,
            prune: 0,
            fast_prune: false,
            natpmp: false,
            reindex: false,
            reindex_chainstate: false,
            load_blocks: Vec::new(),
            stop_after_block_import: false,
            txindex: false,
            txospenderindex: false,
            max_mempool_mb: 300,
            cluster_count: 64,
            cluster_size_vbytes: 101_000,
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
            signet_seed_nodes: Vec::new(),
            deployment_parameters: None,
            max_peers: 4,
            max_receive_buffer: 5_000,
            max_send_buffer: 1_000,
            max_upload_target: 0,
            peer_bloom_filters: false,
            peer_timeout_secs: 60,
            ban_time_secs: 86_400,
            deprecated_rpcs: std::collections::HashSet::new(),
            connect_timeout_ms: 5_000,
            block_max_weight: 4_000_000,
            block_reserved_weight: 8_000,
            block_version: None,
            block_min_tx_fee_sat_per_kvb: 1,
            min_relay_tx_fee_sat_per_kvb: 100,
            incremental_relay_fee_sat_per_kvb: 100,
            dust_relay_fee_sat_per_kvb: 3_000,
            max_datacarrier_bytes: Some(100_000),
            bytes_per_sigop: 20,
            permit_bare_multisig: true,
            zmq: crate::config::ZmqConfig::default(),
        })
        .unwrap();
        let onion = NetworkEndpoint::OnionV3 {
            address: [8; 32],
            port: 18444,
        };
        let i2p = NetworkEndpoint::I2p {
            address: [9; 32],
            port: 18445,
        };
        assert!(node.remember_network_address(onion.clone(), 1, 10));
        assert!(node.remember_network_address(i2p.clone(), 1, 11));
        let attempts = Arc::new(parking_lot::Mutex::new(HashSet::new()));
        let selected = select_discovery_endpoints(&node, 4, &attempts);
        assert!(selected.contains(&onion));
        assert!(selected.contains(&i2p));
    }

    #[tokio::test]
    async fn bip324_transport_round_trips_encrypted_application_messages() {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let address = listener.local_addr().unwrap();
        let client = TcpStream::connect(address);
        let server = listener.accept();
        let (client, server) = tokio::join!(client, server);
        let client = client.unwrap();
        let (server, _) = server.unwrap();

        let (client_result, server_result) = tokio::join!(
            establish_v2(client, Network::Regtest, Role::Initiator),
            establish_v2(server, Network::Regtest, Role::Responder),
        );
        let (client_reader, client_writer, _, client_session_id) = client_result.unwrap();
        let (server_reader, server_writer, _, server_session_id) = server_result.unwrap();
        assert_eq!(client_session_id, server_session_id);
        assert_eq!(client_session_id.as_ref().map(String::len), Some(64));
        let mut client_reader = match client_reader {
            PeerReader::V2(reader) => reader,
            PeerReader::V1(_) => panic!("expected encrypted client reader"),
        };
        let mut client_writer = match client_writer {
            PeerWriterKind::V2(writer) => writer,
            PeerWriterKind::V1(_) => panic!("expected encrypted client writer"),
        };
        let mut server_reader = match server_reader {
            PeerReader::V2(reader) => reader,
            PeerReader::V1(_) => panic!("expected encrypted server reader"),
        };
        let mut server_writer = match server_writer {
            PeerWriterKind::V2(writer) => writer,
            PeerWriterKind::V1(_) => panic!("expected encrypted server writer"),
        };

        let client_message = Message::Ping(123);
        client_writer
            .write(&Payload::genuine(
                wire::encode_v2_message(&client_message).unwrap(),
            ))
            .await
            .unwrap();
        let payload = server_reader.read().await.unwrap();
        assert_eq!(
            wire::decode_v2_message(payload.contents()).unwrap(),
            client_message
        );

        let server_message = Message::Pong(456);
        server_writer
            .write(&Payload::genuine(
                wire::encode_v2_message(&server_message).unwrap(),
            ))
            .await
            .unwrap();
        let payload = client_reader.read().await.unwrap();
        assert_eq!(
            wire::decode_v2_message(payload.contents()).unwrap(),
            server_message
        );
    }

    #[tokio::test]
    async fn tx_reconciliation_extensions_precede_verack_and_use_core_ordering() {
        let directory = tempfile::tempdir().unwrap();
        let zmq = crate::config::ZmqConfig {
            tx_reconciliation: true,
            ..Default::default()
        };
        let node = Node::open(Config {
            network: Network::Regtest,
            datadir: directory.path().to_owned(),
            blocks_dir: None,
            blocks_dir_explicit: false,
            blocks_xor: false,
            capture_messages: false,
            debug_log_path: std::path::PathBuf::from("debug.log"),
            pid_path: std::path::PathBuf::from("bitcoind.pid"),
            logging: Default::default(),
            debug_log_file_enabled: false,
            print_to_console: false,
            shrink_debug_file: false,
            settings_path: None,
            asmap: None,
            minimum_chain_work: None,
            assume_valid: None,
            check_blocks: None,
            check_level: None,
            check_block_index: 0,
            check_mempool: 0,
            check_addrman: 0,
            max_tip_age_secs: 24 * 60 * 60,
            mock_time: None,
            stop_at_height: 0,
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
            script_check_threads: 0,
            block_reconstruction_extra_txn: 100,
            user_agent_comments: Vec::new(),
            startup_notify: None,
            block_notify: None,
            shutdown_notify: None,
            alert_notify: None,
            max_sig_cache_mib: 32,
            accept_stale_fee_estimates: false,
            rpc_whitelist: std::collections::HashMap::new(),
            rpc_whitelist_default: false,
            electrum_bind: None,
            rest: false,
            listen: true,
            dnsseed: true,
            fixed_seeds: false,
            force_dns_seed: false,
            onlynet: Vec::new(),
            proxy: None,
            i2p_sam: None,
            onion_proxy: None,
            listen_onion: false,
            tor_control: "127.0.0.1:9051".parse().unwrap(),
            tor_password: None,
            i2p_accept_incoming: false,
            proxy_randomize: false,
            peer_permissions: crate::config::PeerPermissionConfig::default(),
            blocksonly: false,
            private_broadcast: false,
            accept_nonstd_txn: true,
            rbf_policy: crate::mempool::RbfPolicy::Always,
            truc_policy: crate::mempool::TrucPolicy::Accept,
            cjdns_reachable: false,
            prune: 0,
            fast_prune: false,
            natpmp: false,
            reindex: false,
            reindex_chainstate: false,
            load_blocks: Vec::new(),
            stop_after_block_import: false,
            txindex: false,
            txospenderindex: false,
            max_mempool_mb: 300,
            cluster_count: 64,
            cluster_size_vbytes: 101_000,
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
            signet_seed_nodes: Vec::new(),
            deployment_parameters: None,
            max_peers: 1,
            max_receive_buffer: 5_000,
            max_send_buffer: 1_000,
            max_upload_target: 0,
            peer_bloom_filters: false,
            peer_timeout_secs: 60,
            ban_time_secs: 86_400,
            deprecated_rpcs: std::collections::HashSet::new(),
            connect_timeout_ms: 5_000,
            block_max_weight: 4_000_000,
            block_reserved_weight: 8_000,
            block_version: None,
            block_min_tx_fee_sat_per_kvb: 1,
            min_relay_tx_fee_sat_per_kvb: 100,
            incremental_relay_fee_sat_per_kvb: 100,
            dust_relay_fee_sat_per_kvb: 3_000,
            max_datacarrier_bytes: Some(100_000),
            bytes_per_sigop: 20,
            permit_bare_multisig: true,
            zmq,
        })
        .unwrap();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let address = listener.local_addr().unwrap();
        let client = TcpStream::connect(address);
        let server = listener.accept();
        let (client, server) = tokio::join!(client, server);
        let client = client.unwrap();
        let (server, _) = server.unwrap();
        let (_, client_writer) = client.into_split();
        let (mut server_reader, _) = server.into_split();
        let writer = Arc::new(Mutex::new(PeerWriterKind::V1(client_writer)));
        let peer_state = PeerState {
            endpoint: NetworkEndpoint::Ip(address),
            local_address: None,
            writer: writer.clone(),
            connection_type: "outbound-full",
            permissions: PeerPermissions::empty(),
            private_broadcast_transaction: None,
            private_broadcast_peer: parking_lot::Mutex::new(false),
            local_relay_transactions: true,
            bloom_filter: parking_lot::Mutex::new(None),
            known_tx_inventory: parking_lot::Mutex::new(KnownTxInventory::new()),
            pending_tx_inventory: parking_lot::Mutex::new(Vec::new()),
            tx_requests: parking_lot::Mutex::new(TxRequestState::default()),
            fee_filter: parking_lot::Mutex::new(0),
            relay_transactions: parking_lot::Mutex::new(true),
            wtxid_relay: parking_lot::Mutex::new(false),
            send_headers: parking_lot::Mutex::new(false),
            last_headers_request: parking_lot::Mutex::new(None),
            compact_block_version: parking_lot::Mutex::new(None),
            compact_block_announce: parking_lot::Mutex::new(false),
            tx_reconciliation_salt: parking_lot::Mutex::new(None),
            tx_reconciliation_registered: parking_lot::Mutex::new(false),
        };
        let mut sent = false;
        send_peer_extensions(
            &node,
            1,
            &writer,
            &peer_state,
            Network::Regtest,
            &mut sent,
            WTXID_RELAY_VERSION,
        )
        .await
        .unwrap();

        assert_eq!(
            wire::read_message(&mut server_reader, Network::Regtest)
                .await
                .unwrap(),
            Message::SendHeaders
        );
        assert_eq!(
            wire::read_message(&mut server_reader, Network::Regtest)
                .await
                .unwrap(),
            Message::WtxidRelay
        );
        assert_eq!(
            wire::read_message(&mut server_reader, Network::Regtest)
                .await
                .unwrap(),
            Message::SendAddrV2
        );
        let Message::SendTxRcncl(reconciliation) =
            wire::read_message(&mut server_reader, Network::Regtest)
                .await
                .unwrap()
        else {
            panic!("expected sendtxrcncl extension");
        };
        assert_eq!(reconciliation.version, TX_RECONCILIATION_VERSION);
        assert_eq!(
            *peer_state.tx_reconciliation_salt.lock(),
            Some(reconciliation.salt)
        );
        assert_eq!(
            wire::read_message(&mut server_reader, Network::Regtest)
                .await
                .unwrap(),
            Message::SendCmpct {
                announce: false,
                version: 2,
            }
        );
        assert_eq!(
            wire::read_message(&mut server_reader, Network::Regtest)
                .await
                .unwrap(),
            Message::FeeFilter(100)
        );
        send_message(&node, 1, &writer, Network::Regtest, &Message::Verack)
            .await
            .unwrap();
        assert_eq!(
            wire::read_message(&mut server_reader, Network::Regtest)
                .await
                .unwrap(),
            Message::Verack
        );
        assert!(sent);
    }
}
