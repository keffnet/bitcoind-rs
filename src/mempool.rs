//! In-memory transaction admission and relay pool.

use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::fs;
use std::mem::size_of;
use std::path::Path;
use std::time::Duration;

use anyhow::{Context, Result, bail};
use bitcoin::blockdata::script::Instruction;
use bitcoin::consensus::encode::{VarInt, deserialize_partial, serialize};
use bitcoin::{
    Amount, Network, OutPoint, PublicKey, Script, ScriptBuf, Transaction, TxIn, TxOut, Txid, Wtxid,
};
use rand::random;
use serde::{Deserialize, Serialize};

use crate::chain::ChainState;
use crate::config::{
    DEFAULT_ACCEPT_DATACARRIER, DEFAULT_BYTES_PER_SIGOP, DEFAULT_CLUSTER_COUNT,
    DEFAULT_CLUSTER_SIZE_KVB, DEFAULT_DUST_RELAY_FEE_SAT_PER_KVB,
    DEFAULT_INCREMENTAL_RELAY_FEE_SAT_PER_KVB, DEFAULT_MAX_DATACARRIER_BYTES,
    DEFAULT_MIN_RELAY_TX_FEE_SAT_PER_KVB, DEFAULT_PERMIT_BARE_MULTISIG, MAX_CLUSTER_COUNT_LIMIT,
};
use crate::time;
use crate::validation::{self, ValidationError};

const DEFAULT_MAX_MEMPOOL_BYTES: usize = 300_000_000;
pub(crate) const MEMPOOL_EXPIRY: Duration = Duration::from_secs(14 * 24 * 60 * 60);
const CORE_MEMPOOL_DUMP_VERSION_V1: u64 = 1;
const CORE_MEMPOOL_DUMP_VERSION_V2: u64 = 2;
const CORE_MEMPOOL_OBFUSCATION_KEY_SIZE: usize = 8;
const MAX_CORE_MEMPOOL_TRANSACTIONS: usize = 1_000_000;
const MAX_CORE_MEMPOOL_FILE_SIZE: usize = 2 * 1024 * 1024 * 1024;
const ROLLING_FEE_HALFLIFE_SECS: f64 = 12.0 * 60.0 * 60.0;
const MAX_STANDARD_TX_WEIGHT: u64 = 400_000;
const MAX_STANDARD_TX_SIGOPS_COST: usize = validation::MAX_BLOCK_SIGOP_COST / 5;
const MAX_TX_LEGACY_SIGOPS: usize = 2_500;
const MIN_STANDARD_TX_NONWITNESS_SIZE: usize = 65;
const MAX_STANDARD_SCRIPTSIG_SIZE: usize = 1_650;
const MAX_SCRIPT_SIZE: usize = 10_000;
/// BIP 431/TRUC transaction version and topology limits.
const TRUC_VERSION: i32 = 3;
const TRUC_ANCESTOR_LIMIT: usize = 2;
const TRUC_DESCENDANT_LIMIT: usize = 2;
const TRUC_MAX_VSIZE: u64 = 10_000;
const TRUC_CHILD_MAX_VSIZE: u64 = 1_000;

/// Core's context-free package limits.
pub const MAX_PACKAGE_COUNT: usize = 25;
pub const MAX_PACKAGE_WEIGHT: u64 = 404_000;
/// Core's default cluster limits for the v31.1 mempool policy.
pub const MAX_CLUSTER_COUNT: usize = MAX_CLUSTER_COUNT_LIMIT;
pub const MAX_CLUSTER_VSIZE: u64 = DEFAULT_CLUSTER_SIZE_KVB * 1_000;
const MAX_REPLACEMENT_CANDIDATES: usize = 100;
/// Maximum non-tree cluster size for which the local optimality certificate
/// enumerates every topological linearization.
const MAX_GRAPH_OPTIMALITY_EXACT_TX_COUNT: usize = 12;
/// Bound the number of partial topological orders explored by the certificate
/// so an RPC query cannot turn into an unbounded factorial search.
const MAX_GRAPH_OPTIMALITY_STATES: usize = 100_000;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum RbfPolicy {
    Never,
    OptIn,
    #[default]
    Always,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum TrucPolicy {
    Reject,
    #[default]
    Accept,
    Enforce,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MempoolPolicy {
    pub min_relay_fee_sat_per_kvb: u64,
    pub incremental_relay_fee_sat_per_kvb: u64,
    pub dust_relay_fee_sat_per_kvb: u64,
    pub bytes_per_sigop: u64,
    pub max_datacarrier_bytes: Option<usize>,
    pub permit_bare_multisig: bool,
    pub require_standard: bool,
    pub cluster_count_limit: usize,
    pub cluster_vsize_limit: u64,
    pub rbf_policy: RbfPolicy,
    pub truc_policy: TrucPolicy,
}

impl Default for MempoolPolicy {
    fn default() -> Self {
        Self {
            min_relay_fee_sat_per_kvb: DEFAULT_MIN_RELAY_TX_FEE_SAT_PER_KVB,
            incremental_relay_fee_sat_per_kvb: DEFAULT_INCREMENTAL_RELAY_FEE_SAT_PER_KVB,
            dust_relay_fee_sat_per_kvb: DEFAULT_DUST_RELAY_FEE_SAT_PER_KVB,
            bytes_per_sigop: DEFAULT_BYTES_PER_SIGOP,
            max_datacarrier_bytes: DEFAULT_ACCEPT_DATACARRIER
                .then_some(usize::try_from(DEFAULT_MAX_DATACARRIER_BYTES).expect("constant fits")),
            permit_bare_multisig: DEFAULT_PERMIT_BARE_MULTISIG,
            require_standard: true,
            cluster_count_limit: DEFAULT_CLUSTER_COUNT,
            cluster_vsize_limit: MAX_CLUSTER_VSIZE,
            rbf_policy: RbfPolicy::default(),
            truc_policy: TrucPolicy::default(),
        }
    }
}

pub const MAX_DATACARRIER_SIZE: usize = DEFAULT_MAX_DATACARRIER_BYTES as usize;

#[derive(Deserialize, Serialize)]
struct DiskMempoolEntry {
    transaction: Transaction,
    added_at: u64,
}

struct CoreMempoolEntry {
    transaction: Transaction,
    added_at: u64,
    fee_delta: i64,
}

type CoreMempoolDeltas = Vec<(Txid, i64)>;
type DecodedCoreMempool = (Vec<CoreMempoolEntry>, CoreMempoolDeltas, Vec<Txid>);

#[derive(Clone, Copy, Debug)]
pub struct MempoolLoadOptions {
    pub use_current_time: bool,
    pub apply_fee_delta_priority: bool,
    pub apply_unbroadcast_set: bool,
}

impl Default for MempoolLoadOptions {
    fn default() -> Self {
        Self {
            use_current_time: false,
            apply_fee_delta_priority: true,
            apply_unbroadcast_set: true,
        }
    }
}

fn append_u64(bytes: &mut Vec<u8>, value: u64) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

fn append_i64(bytes: &mut Vec<u8>, value: i64) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

fn read_bytes<'a>(
    bytes: &'a [u8],
    offset: &mut usize,
    length: usize,
    what: &str,
) -> Result<&'a [u8]> {
    let end = offset
        .checked_add(length)
        .context("mempool file offset overflow")?;
    if end > bytes.len() {
        bail!("mempool file ended while reading {what}");
    }
    let result = &bytes[*offset..end];
    *offset = end;
    Ok(result)
}

fn read_u64(bytes: &[u8], offset: &mut usize, what: &str) -> Result<u64> {
    Ok(u64::from_le_bytes(
        read_bytes(bytes, offset, 8, what)?
            .try_into()
            .expect("read_bytes returned eight bytes"),
    ))
}

fn read_i64(bytes: &[u8], offset: &mut usize, what: &str) -> Result<i64> {
    Ok(i64::from_le_bytes(
        read_bytes(bytes, offset, 8, what)?
            .try_into()
            .expect("read_bytes returned eight bytes"),
    ))
}

fn read_varint(bytes: &[u8], offset: &mut usize, what: &str) -> Result<u64> {
    let (value, consumed) = deserialize_partial::<VarInt>(
        bytes
            .get(*offset..)
            .ok_or_else(|| anyhow::anyhow!("mempool file ended while reading {what}"))?,
    )
    .with_context(|| format!("decoding {what}"))?;
    *offset = offset
        .checked_add(consumed)
        .context("mempool file offset overflow")?;
    Ok(value.0)
}

fn xor_obfuscate(
    bytes: &mut [u8],
    key: &[u8; CORE_MEMPOOL_OBFUSCATION_KEY_SIZE],
    file_offset: usize,
) {
    for (index, byte) in bytes.iter_mut().enumerate() {
        *byte ^= key[(file_offset + index) % CORE_MEMPOOL_OBFUSCATION_KEY_SIZE];
    }
}

fn decode_core_mempool_payload(bytes: &[u8]) -> Result<DecodedCoreMempool> {
    let mut offset = 0;
    let transaction_count =
        usize::try_from(read_u64(bytes, &mut offset, "mempool transaction count")?)
            .context("mempool transaction count does not fit usize")?;
    if transaction_count > MAX_CORE_MEMPOOL_TRANSACTIONS {
        bail!("mempool transaction count is unreasonable");
    }

    let mut entries = Vec::with_capacity(transaction_count);
    for _ in 0..transaction_count {
        let (transaction, consumed) = deserialize_partial::<Transaction>(
            bytes
                .get(offset..)
                .ok_or_else(|| anyhow::anyhow!("mempool file ended before a transaction"))?,
        )
        .context("decoding mempool transaction")?;
        if consumed == 0 {
            bail!("mempool transaction decoder consumed no bytes");
        }
        offset = offset
            .checked_add(consumed)
            .context("mempool file offset overflow")?;
        let added_at = read_i64(bytes, &mut offset, "mempool transaction timestamp")?;
        if added_at < 0 {
            bail!("mempool transaction timestamp is negative");
        }
        let fee_delta = read_i64(bytes, &mut offset, "mempool transaction fee delta")?;
        entries.push(CoreMempoolEntry {
            transaction,
            added_at: added_at as u64,
            fee_delta,
        });
    }

    let delta_count = usize::try_from(read_varint(bytes, &mut offset, "mempool fee-delta count")?)
        .context("mempool fee-delta count does not fit usize")?;
    if delta_count > MAX_CORE_MEMPOOL_TRANSACTIONS {
        bail!("mempool fee-delta count is unreasonable");
    }
    let mut deltas = Vec::with_capacity(delta_count);
    for _ in 0..delta_count {
        let (txid, consumed) = deserialize_partial::<Txid>(
            bytes
                .get(offset..)
                .ok_or_else(|| anyhow::anyhow!("mempool file ended before a fee delta"))?,
        )
        .context("decoding mempool fee-delta transaction id")?;
        offset = offset
            .checked_add(consumed)
            .context("mempool file offset overflow")?;
        deltas.push((txid, read_i64(bytes, &mut offset, "mempool fee delta")?));
    }

    let unbroadcast_count = usize::try_from(read_varint(
        bytes,
        &mut offset,
        "mempool unbroadcast count",
    )?)
    .context("mempool unbroadcast count does not fit usize")?;
    if unbroadcast_count > MAX_CORE_MEMPOOL_TRANSACTIONS {
        bail!("mempool unbroadcast count is unreasonable");
    }
    let mut unbroadcast = Vec::with_capacity(unbroadcast_count);
    for _ in 0..unbroadcast_count {
        let (txid, consumed) = deserialize_partial::<Txid>(
            bytes
                .get(offset..)
                .ok_or_else(|| anyhow::anyhow!("mempool file ended before an unbroadcast id"))?,
        )
        .context("decoding mempool unbroadcast transaction id")?;
        offset = offset
            .checked_add(consumed)
            .context("mempool file offset overflow")?;
        unbroadcast.push(txid);
    }

    if offset != bytes.len() {
        bail!("mempool file contains trailing data");
    }
    Ok((entries, deltas, unbroadcast))
}

fn decode_core_mempool(bytes: &[u8]) -> Result<DecodedCoreMempool> {
    if bytes.len() > MAX_CORE_MEMPOOL_FILE_SIZE {
        bail!("mempool file is too large");
    }
    let mut offset = 0;
    let version = read_u64(bytes, &mut offset, "mempool dump version")?;
    match version {
        CORE_MEMPOOL_DUMP_VERSION_V1 => decode_core_mempool_payload(
            bytes
                .get(offset..)
                .ok_or_else(|| anyhow::anyhow!("mempool file has no payload"))?,
        ),
        CORE_MEMPOOL_DUMP_VERSION_V2 => {
            let key_length = usize::try_from(read_varint(
                bytes,
                &mut offset,
                "mempool obfuscation key length",
            )?)
            .context("mempool obfuscation key length does not fit usize")?;
            if key_length != CORE_MEMPOOL_OBFUSCATION_KEY_SIZE {
                bail!("mempool obfuscation key must be eight bytes");
            }
            let key: [u8; CORE_MEMPOOL_OBFUSCATION_KEY_SIZE] =
                read_bytes(bytes, &mut offset, key_length, "mempool obfuscation key")?
                    .try_into()
                    .expect("obfuscation key length was checked");
            let payload_offset = offset;
            let mut payload = bytes
                .get(payload_offset..)
                .ok_or_else(|| anyhow::anyhow!("mempool file has no payload"))?
                .to_vec();
            xor_obfuscate(&mut payload, &key, payload_offset);
            decode_core_mempool_payload(&payload)
        }
        _ => bail!("unsupported mempool dump version {version}"),
    }
}

#[derive(Clone, Debug)]
pub struct MempoolEntry {
    pub transaction: Transaction,
    pub fee_sat: u64,
    pub vsize: u64,
    pub added_at: u64,
    /// Active-chain height when the transaction entered the mempool.
    pub height: u32,
}

/// Estimate the dynamic allocation footprint of a transaction and its
/// mempool indexes. Core's `CTxMemPool::DynamicMemoryUsage` is necessarily an
/// allocator-specific estimate. Keep the Rust implementation deterministic
/// while accounting for the same categories: transaction-owned buffers,
/// entry/index nodes, and spent-input relationships.
fn mempool_entry_memory_usage(transaction: &Transaction) -> usize {
    let pointer_bytes = size_of::<usize>();
    let index_node_bytes = size_of::<usize>() * 3;
    let mut usage = size_of::<MempoolEntry>()
        .saturating_add(pointer_bytes.saturating_mul(9))
        // entries, adjusted_weights, wtxids, and relay_sequences
        .saturating_add(index_node_bytes.saturating_mul(4))
        .saturating_add(
            transaction.input.len().saturating_mul(
                size_of::<OutPoint>()
                    .saturating_add(size_of::<Txid>())
                    .saturating_add(index_node_bytes.saturating_mul(2)),
            ),
        );

    usage = usage.saturating_add(transaction.input.len().saturating_mul(size_of::<TxIn>()));
    usage = usage.saturating_add(transaction.output.len().saturating_mul(size_of::<TxOut>()));
    for input in &transaction.input {
        usage = usage.saturating_add(input.script_sig.as_bytes().len());
        let witness = input.witness.to_vec();
        usage = usage.saturating_add(witness.capacity().saturating_mul(pointer_bytes * 3));
        for item in witness {
            usage = usage.saturating_add(item.capacity());
        }
    }
    for output in &transaction.output {
        usage = usage.saturating_add(output.script_pubkey.as_bytes().len());
    }
    usage
}

#[derive(Clone, Debug)]
pub(crate) enum MempoolChangeKind {
    Added,
    Removed { notify_zmq: bool },
}

#[derive(Clone, Debug)]
pub(crate) struct MempoolChange {
    pub transaction: Transaction,
    pub sequence: u64,
    pub kind: MempoolChangeKind,
}

#[derive(Clone)]
pub struct Mempool {
    pub network: Network,
    policy: MempoolPolicy,
    max_bytes: usize,
    /// Estimated dynamic memory used by admitted entries and their indexes.
    /// This is separate from `bytes`, which is the serialized transaction
    /// total retained for diagnostics and Core's vsize `bytes` field.
    memory_usage: usize,
    bytes: usize,
    vbytes: u64,
    rolling_min_fee_sat_per_kvb: f64,
    rolling_fee_last_updated: u64,
    block_since_last_rolling_fee_bump: bool,
    sequence: u64,
    entries: HashMap<Txid, MempoolEntry>,
    /// Cached sigop-adjusted transaction weights used by Core's mining and
    /// mempool feerate calculations. Synthetic test entries fall back to
    /// their raw transaction weight when this map has no record.
    adjusted_weights: HashMap<Txid, u64>,
    spent: HashMap<OutPoint, Txid>,
    children: HashMap<Txid, HashSet<Txid>>,
    wtxids: HashMap<Wtxid, Txid>,
    priorities: HashMap<Txid, i64>,
    unbroadcast: HashSet<Txid>,
    /// Mempool sequence at which each transaction was admitted. This is
    /// runtime-only relay metadata and is not persisted in mempool.dat.
    relay_sequences: HashMap<Txid, u64>,
    changes: Vec<MempoolChange>,
    /// Cached result for the Core-style `getmempoolinfo.optimal` projection.
    /// Graph mutations invalidate the result; the certificate is computed on
    /// the next query rather than on the admission/removal hot path.
    graph_optimal: bool,
    graph_optimal_dirty: bool,
}

#[derive(Clone, Copy)]
struct MiningPackageMetrics {
    fee: i128,
    weight: u64,
    version: u64,
}

#[derive(Clone, Copy, Eq, PartialEq)]
struct MiningCandidate {
    txid: Txid,
    fee: i128,
    weight: u64,
    version: u64,
}

impl Ord for MiningCandidate {
    fn cmp(&self, other: &Self) -> Ordering {
        let left = self.fee.saturating_mul(i128::from(other.weight));
        let right = other.fee.saturating_mul(i128::from(self.weight));
        left.cmp(&right)
            // BinaryHeap is a max-heap, while Core's deterministic tie break
            // prefers the lexicographically smaller transaction id.
            .then_with(|| other.txid.to_string().cmp(&self.txid.to_string()))
            .then_with(|| self.version.cmp(&other.version))
            .then_with(|| self.fee.cmp(&other.fee))
            .then_with(|| self.weight.cmp(&other.weight))
    }
}

impl PartialOrd for MiningCandidate {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, thiserror::Error)]
pub enum MempoolError {
    #[error("coinbase transactions cannot enter the mempool")]
    Coinbase,
    #[error("transaction already exists in the mempool")]
    AlreadyPresent,
    #[error("Transaction outputs already in utxo set")]
    AlreadyInChain,
    #[error("transaction input is already spent by mempool transaction {0}")]
    Conflict(Txid),
    #[error("bip125-replacement-disallowed")]
    ReplacementDisallowed,
    #[error(
        "too many potential replacements, rejecting replacement {txid}; too many conflicting clusters ({count} > {limit})"
    )]
    TooManyReplacementCandidates {
        txid: Txid,
        count: usize,
        limit: usize,
    },
    #[error("replacement transaction fee is too low")]
    ReplacementFee,
    #[error("replacement transaction spends an unconfirmed output outside the conflicts")]
    ReplacementUnconfirmedInput,
    #[error("insufficient feerate: does not improve feerate diagram")]
    ReplacementFeerateDiagram,
    #[error("transaction {0} input is missing")]
    MissingInput(OutPoint),
    #[error("transaction contains a duplicate input")]
    DuplicateInput,
    #[error("transaction contains a null prevout")]
    NullPrevout,
    #[error("transaction has no inputs or outputs")]
    Empty,
    #[error("bad-txns-oversize")]
    Oversized,
    #[error("transaction output value is invalid")]
    BadOutput,
    #[error("transaction spends more than its inputs")]
    NegativeFee,
    #[error("transaction fee rate is below the relay minimum")]
    FeeRate,
    #[error("transaction script validation failed: {0}")]
    Script(String),
    #[error("transaction is non-standard: {0}")]
    NonStandard(String),
    #[error("mempool size limit exceeded")]
    Full,
    #[error("transaction cluster exceeds the mempool cluster limits")]
    ClusterLimit,
    #[error("TRUC-violation, {0}")]
    Truc(String),
}

impl Mempool {
    pub fn new(network: Network) -> Self {
        Self::with_max_bytes(network, DEFAULT_MAX_MEMPOOL_BYTES)
    }

    pub fn with_max_bytes(network: Network, max_bytes: usize) -> Self {
        // Preserve the low-level helper's historical behavior for synthetic
        // regtest fixtures. Node::open supplies the explicit Core policy.
        let policy = MempoolPolicy {
            require_standard: network != Network::Regtest,
            ..MempoolPolicy::default()
        };
        Self::with_max_bytes_and_policy(network, max_bytes, policy)
    }

    pub fn with_max_bytes_and_policy(
        network: Network,
        max_bytes: usize,
        policy: MempoolPolicy,
    ) -> Self {
        Self {
            network,
            policy,
            max_bytes: max_bytes.max(1),
            memory_usage: 0,
            bytes: 0,
            vbytes: 0,
            rolling_min_fee_sat_per_kvb: 0.0,
            rolling_fee_last_updated: time::unix_time(),
            block_since_last_rolling_fee_bump: false,
            sequence: 1,
            entries: HashMap::new(),
            adjusted_weights: HashMap::new(),
            spent: HashMap::new(),
            children: HashMap::new(),
            wtxids: HashMap::new(),
            priorities: HashMap::new(),
            unbroadcast: HashSet::new(),
            relay_sequences: HashMap::new(),
            changes: Vec::new(),
            graph_optimal: true,
            graph_optimal_dirty: false,
        }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn bytes(&self) -> usize {
        self.bytes
    }

    /// Return the deterministic dynamic-memory estimate used by the pool
    /// limit and exposed as Core's `getmempoolinfo.usage` value.
    pub fn dynamic_memory_usage(&self) -> usize {
        let index_node_bytes = size_of::<usize>() * 3;
        self.memory_usage
            // Fee deltas and unbroadcast transaction ids may outlive an
            // entry, just as Core's auxiliary mempool maps do.
            .saturating_add(
                self.priorities
                    .len()
                    .saturating_mul(size_of::<Txid>() + size_of::<i64>() + index_node_bytes),
            )
            .saturating_add(
                self.unbroadcast
                    .len()
                    .saturating_mul(size_of::<Txid>() + index_node_bytes),
            )
    }

    /// Sum of virtual transaction sizes, matching Core's `getmempoolinfo.bytes`.
    pub fn vbytes(&self) -> u64 {
        self.vbytes
    }

    /// Return Core's sigop-adjusted weight for a mempool transaction.
    pub fn adjusted_weight(&self, txid: &Txid) -> u64 {
        self.adjusted_weights
            .get(txid)
            .copied()
            .or_else(|| {
                self.entries
                    .get(txid)
                    .map(|entry| entry.transaction.weight().to_wu())
            })
            .unwrap_or_default()
    }

    pub fn max_bytes(&self) -> usize {
        self.max_bytes
    }

    /// Change the memory limit used by admission and eviction. Core's RPC
    /// validates the minimum before mutating the pool; keeping the setter
    /// small lets callers apply that policy while reusing the normal eviction
    /// path and its sequence/change notifications.
    pub fn set_max_bytes(&mut self, max_bytes: usize) {
        self.max_bytes = max_bytes.max(1);
    }

    pub fn min_relay_fee_sat_per_kvb(&self) -> u64 {
        self.policy.min_relay_fee_sat_per_kvb
    }

    pub fn mempool_min_fee_sat_per_kvb(&mut self) -> u64 {
        self.decay_rolling_min_fee();
        self.policy.min_relay_fee_sat_per_kvb.max(
            self.rolling_min_fee_sat_per_kvb
                .round()
                .clamp(0.0, u64::MAX as f64) as u64,
        )
    }

    pub fn incremental_relay_fee_sat_per_kvb(&self) -> u64 {
        self.policy.incremental_relay_fee_sat_per_kvb
    }

    pub fn dust_relay_fee_sat_per_kvb(&self) -> u64 {
        self.policy.dust_relay_fee_sat_per_kvb
    }

    pub fn bytes_per_sigop(&self) -> u64 {
        self.policy.bytes_per_sigop
    }

    pub fn max_datacarrier_bytes(&self) -> Option<usize> {
        self.policy.max_datacarrier_bytes
    }

    pub fn cluster_count_limit(&self) -> usize {
        self.policy.cluster_count_limit
    }

    pub fn cluster_vsize_limit(&self) -> u64 {
        self.policy.cluster_vsize_limit
    }

    pub fn permit_bare_multisig(&self) -> bool {
        self.policy.permit_bare_multisig
    }

    pub fn rbf_policy(&self) -> RbfPolicy {
        self.policy.rbf_policy
    }

    pub fn full_rbf(&self) -> bool {
        self.policy.rbf_policy == RbfPolicy::Always
    }

    pub fn truc_policy(&self) -> TrucPolicy {
        self.policy.truc_policy
    }

    pub fn sequence(&self) -> u64 {
        self.sequence
    }

    /// Return whether the mempool graph has a known optimal linearization.
    ///
    /// Core's TxGraph exposes this as a best-effort work status: `true` means
    /// the graph has no currently available optimization work, not that every
    /// possible graph is solved by an unbounded optimizer. Keep the same
    /// meaning here by reporting `false` when a bounded local certificate
    /// cannot prove optimality.
    pub fn optimal(&mut self) -> bool {
        if self.graph_optimal_dirty {
            self.graph_optimal = self.compute_graph_optimality();
            self.graph_optimal_dirty = false;
        }
        self.graph_optimal
    }

    fn invalidate_graph_optimality(&mut self) {
        self.graph_optimal_dirty = true;
    }

    fn compute_graph_optimality(&self) -> bool {
        graph_optimality_certificate(self)
    }

    /// Return entries whose admission sequence is at least `start_sequence`.
    /// The sequence is assigned once when an entry enters the pool and is
    /// deliberately kept separate from the topology/mining order.
    pub fn transactions_since_sequence(&self, start_sequence: u64) -> Vec<(u64, Txid)> {
        let mut transactions = self
            .relay_sequences
            .iter()
            .filter_map(|(txid, sequence)| {
                (*sequence >= start_sequence).then_some((*sequence, *txid))
            })
            .collect::<Vec<_>>();
        transactions.sort_by(|(left_sequence, left_txid), (right_sequence, right_txid)| {
            left_sequence
                .cmp(right_sequence)
                .then_with(|| left_txid.to_string().cmp(&right_txid.to_string()))
        });
        transactions
    }

    /// Verify the bidirectional indexes and accounting maintained by the
    /// mempool. This is intentionally explicit and deterministic so the
    /// Core-style debug consistency options can catch a mutation bug without
    /// depending on allocator internals.
    pub fn check_consistency(&self) -> Result<()> {
        let mut expected_spent = HashMap::new();
        let mut expected_children: HashMap<Txid, HashSet<Txid>> = HashMap::new();
        let mut expected_wtxids = HashMap::new();
        let mut expected_bytes = 0usize;
        let mut expected_vbytes = 0u64;
        let mut expected_memory_usage = 0usize;

        for (txid, entry) in &self.entries {
            let computed_txid = entry.transaction.compute_txid();
            if computed_txid != *txid {
                bail!("mempool txid index mismatch: key {txid}, transaction {computed_txid}");
            }
            let wtxid = entry.transaction.compute_wtxid();
            if expected_wtxids.insert(wtxid, *txid).is_some() {
                bail!("mempool contains duplicate wtxid {wtxid}");
            }
            for input in &entry.transaction.input {
                if expected_spent
                    .insert(input.previous_output, *txid)
                    .is_some()
                {
                    bail!(
                        "mempool input {} is claimed by more than one transaction",
                        input.previous_output
                    );
                }
                if self.entries.contains_key(&input.previous_output.txid) {
                    expected_children
                        .entry(input.previous_output.txid)
                        .or_default()
                        .insert(*txid);
                }
            }
            expected_bytes = expected_bytes
                .saturating_add(bitcoin::consensus::encode::serialize(&entry.transaction).len());
            expected_vbytes = expected_vbytes.saturating_add(entry.vsize);
            expected_memory_usage = expected_memory_usage
                .saturating_add(mempool_entry_memory_usage(&entry.transaction));
        }

        if self.spent != expected_spent {
            bail!("mempool spent-input index is inconsistent");
        }
        if self.children != expected_children {
            bail!("mempool parent/child index is inconsistent");
        }
        if self.wtxids != expected_wtxids {
            bail!("mempool wtxid index is inconsistent");
        }
        if self.adjusted_weights.len() != self.entries.len()
            || self
                .adjusted_weights
                .keys()
                .any(|txid| !self.entries.contains_key(txid))
        {
            bail!("mempool adjusted-weight index is inconsistent");
        }
        if self.relay_sequences.len() != self.entries.len()
            || self
                .relay_sequences
                .keys()
                .any(|txid| !self.entries.contains_key(txid))
        {
            bail!("mempool relay-sequence index is inconsistent");
        }
        if self.bytes != expected_bytes {
            bail!(
                "mempool byte accounting is inconsistent: stored {}, expected {expected_bytes}",
                self.bytes
            );
        }
        if self.vbytes != expected_vbytes {
            bail!(
                "mempool vbyte accounting is inconsistent: stored {}, expected {expected_vbytes}",
                self.vbytes
            );
        }
        if self.memory_usage != expected_memory_usage {
            bail!(
                "mempool memory accounting is inconsistent: stored {}, expected {expected_memory_usage}",
                self.memory_usage
            );
        }
        if self
            .unbroadcast
            .iter()
            .any(|txid| !self.entries.contains_key(txid))
        {
            bail!("mempool unbroadcast set contains an unknown transaction");
        }
        Ok(())
    }

    pub(crate) fn take_changes(&mut self) -> Vec<MempoolChange> {
        std::mem::take(&mut self.changes)
    }

    pub fn get(&self, txid: &Txid) -> Option<&MempoolEntry> {
        self.entries.get(txid)
    }

    #[cfg(test)]
    pub(crate) fn insert_test_entry(&mut self, entry: MempoolEntry) {
        let txid = entry.transaction.compute_txid();
        let wtxid = entry.transaction.compute_wtxid();
        self.entries.insert(txid, entry);
        self.wtxids.insert(wtxid, txid);
        self.invalidate_graph_optimality();
    }

    pub fn get_by_wtxid(&self, wtxid: &Wtxid) -> Option<&MempoolEntry> {
        self.wtxids
            .get(wtxid)
            .and_then(|txid| self.entries.get(txid))
    }

    pub(crate) fn fee_estimation_entries(&self) -> Vec<(Txid, Transaction, u64, u64, u32)> {
        self.entries
            .iter()
            .map(|(txid, entry)| {
                (
                    *txid,
                    entry.transaction.clone(),
                    entry.fee_sat,
                    entry.vsize,
                    entry.height,
                )
            })
            .collect()
    }

    pub(crate) fn has_mempool_parent(&self, transaction: &Transaction) -> bool {
        transaction
            .input
            .iter()
            .any(|input| self.entries.contains_key(&input.previous_output.txid))
    }

    /// Return a transaction only when it entered the mempool before the
    /// peer's most recent inventory announcement. This mirrors Core's
    /// `info_for_relay` gate for GETDATA transaction requests.
    pub fn get_for_relay(&self, txid: &Txid, last_sequence: u64) -> Option<&MempoolEntry> {
        let entry = self.entries.get(txid)?;
        let sequence = self.relay_sequences.get(txid).copied().unwrap_or(0);
        (sequence < last_sequence).then_some(entry)
    }

    pub fn get_by_wtxid_for_relay(
        &self,
        wtxid: &Wtxid,
        last_sequence: u64,
    ) -> Option<&MempoolEntry> {
        let txid = self.wtxids.get(wtxid)?;
        self.get_for_relay(txid, last_sequence)
    }

    pub fn is_spent(&self, outpoint: &OutPoint) -> bool {
        self.spent.contains_key(outpoint)
    }

    pub fn spender(&self, outpoint: &OutPoint) -> Option<Txid> {
        self.spent.get(outpoint).copied()
    }

    pub fn transactions(&self) -> impl Iterator<Item = &Transaction> {
        self.entries.values().map(|entry| &entry.transaction)
    }

    /// Core refuses to change the priority of an in-mempool transaction with
    /// dust outputs while standard policy is enabled.
    pub fn has_dust_outputs(&self, txid: &Txid) -> bool {
        self.policy.require_standard
            && self.entries.get(txid).is_some_and(|entry| {
                entry.transaction.output.iter().any(|output| {
                    is_dust_output_with_fee(output, self.policy.dust_relay_fee_sat_per_kvb)
                })
            })
    }

    pub fn prioritise(&mut self, txid: Txid, fee_delta: i64) {
        let in_mempool = self.entries.contains_key(&txid);
        let delta = self.priorities.entry(txid).or_insert(0);
        *delta = delta.saturating_add(fee_delta);
        if *delta == 0 {
            self.priorities.remove(&txid);
        }
        if in_mempool && fee_delta != 0 {
            self.invalidate_graph_optimality();
        }
    }

    pub fn prioritised_transactions(&self) -> Vec<(Txid, i64, bool, Option<i64>)> {
        let mut result = self
            .priorities
            .iter()
            .map(|(txid, delta)| {
                let modified_fee = self.entries.get(txid).map(|entry| {
                    i64::try_from(entry.fee_sat)
                        .unwrap_or(i64::MAX)
                        .saturating_add(*delta)
                });
                (*txid, *delta, modified_fee.is_some(), modified_fee)
            })
            .collect::<Vec<_>>();
        result.sort_by_key(|(txid, _, _, _)| txid.to_string());
        result
    }

    pub fn fee_delta(&self, txid: &Txid) -> i64 {
        self.priorities.get(txid).copied().unwrap_or(0)
    }

    pub fn modified_fee_sat_for(&self, txid: &Txid, base_fee_sat: u64) -> i128 {
        self.modified_fee_sat(txid, base_fee_sat)
    }

    pub fn add_unbroadcast(&mut self, txid: Txid) {
        if self.entries.contains_key(&txid) {
            self.unbroadcast.insert(txid);
        }
    }

    pub fn remove_unbroadcast(&mut self, txid: &Txid) {
        self.unbroadcast.remove(txid);
    }

    pub fn is_unbroadcast(&self, txid: &Txid) -> bool {
        self.unbroadcast.contains(txid)
    }

    pub fn unbroadcast_txids(&self) -> Vec<Txid> {
        let mut txids = self.unbroadcast.iter().copied().collect::<Vec<_>>();
        txids.sort_by_key(ToString::to_string);
        txids.retain(|txid| self.entries.contains_key(txid));
        txids
    }

    fn modified_fee_sat(&self, txid: &Txid, base_fee_sat: u64) -> i128 {
        i128::from(base_fee_sat) + i128::from(self.fee_delta(txid))
    }

    pub fn transaction_order(&self) -> Vec<Txid> {
        let mut transaction_ids: Vec<Txid> = self.entries.keys().copied().collect();
        transaction_ids.sort_by(|left, right| {
            self.fee_delta(right)
                .cmp(&self.fee_delta(left))
                .then_with(|| left.to_string().cmp(&right.to_string()))
        });
        let mut ordered = Vec::with_capacity(transaction_ids.len());
        let mut visited = HashSet::new();
        let mut visiting = HashSet::new();

        fn visit(
            txid: Txid,
            entries: &HashMap<Txid, MempoolEntry>,
            visited: &mut HashSet<Txid>,
            visiting: &mut HashSet<Txid>,
            ordered: &mut Vec<Txid>,
        ) {
            if visited.contains(&txid) || !visiting.insert(txid) {
                return;
            }
            if let Some(entry) = entries.get(&txid) {
                let mut parents: Vec<Txid> = entry
                    .transaction
                    .input
                    .iter()
                    .map(|input| input.previous_output.txid)
                    .filter(|parent| entries.contains_key(parent))
                    .collect();
                parents.sort_by_key(ToString::to_string);
                for parent in parents {
                    visit(parent, entries, visited, visiting, ordered);
                }
            }
            visiting.remove(&txid);
            visited.insert(txid);
            ordered.push(txid);
        }

        for txid in transaction_ids {
            visit(
                txid,
                &self.entries,
                &mut visited,
                &mut visiting,
                &mut ordered,
            );
        }
        ordered
    }

    /// Return the topology-aware score order used by Core's mempool
    /// enumeration APIs. With no practical weight limit this includes every
    /// entry while still placing ancestors before children.
    pub fn main_order(&self) -> Vec<Txid> {
        self.mining_order(u64::MAX, 0)
    }

    /// Return transactions in ancestor-package feerate order for block
    /// assembly. A package consists of an unselected transaction and all of
    /// its unselected ancestors. Packages are scored by effective fee
    /// (including prioritisation deltas) per weight, while the returned list
    /// remains topologically ordered.
    pub fn mining_order(&self, max_weight: u64, reserved_weight: u64) -> Vec<Txid> {
        self.mining_order_with_min_fee(max_weight, reserved_weight, 0)
    }

    /// Return transactions in ancestor-package feerate order, excluding
    /// packages below the configured block-creation feerate. The fee rate is
    /// expressed in satoshis per virtual kilobyte, matching Core's
    /// `-blockmintxfee` option.
    pub fn mining_order_with_min_fee(
        &self,
        max_weight: u64,
        reserved_weight: u64,
        min_fee_sat_per_kvb: u64,
    ) -> Vec<Txid> {
        let weight_limit = max_weight.saturating_sub(reserved_weight);
        let mut selected = HashSet::new();
        let mut ordered = Vec::new();
        let mut selected_weight = 0u64;
        let mut metrics = HashMap::with_capacity(self.entries.len());
        let mut candidates = BinaryHeap::with_capacity(self.entries.len());

        for txid in self.entries.keys().copied() {
            let mut package = HashSet::new();
            if !collect_mining_package(
                self,
                txid,
                &HashSet::new(),
                &mut package,
                &mut HashSet::new(),
            ) {
                continue;
            }
            let package_weight = package
                .iter()
                .map(|candidate| self.adjusted_weight(candidate))
                .fold(0u64, u64::saturating_add);
            let package_fee = package
                .iter()
                .filter_map(|candidate| {
                    self.entries.get(candidate).map(|entry| {
                        i128::from(entry.fee_sat) + i128::from(self.fee_delta(candidate))
                    })
                })
                .fold(0i128, i128::saturating_add);
            let package_metrics = MiningPackageMetrics {
                fee: package_fee,
                weight: package_weight,
                version: 0,
            };
            metrics.insert(txid, package_metrics);
            candidates.push(MiningCandidate {
                txid,
                fee: package_fee,
                weight: package_weight,
                version: 0,
            });
        }

        while selected.len() < self.entries.len() {
            let Some(candidate) = next_mining_candidate(
                &mut candidates,
                &metrics,
                &selected,
                selected_weight,
                weight_limit,
                min_fee_sat_per_kvb,
            ) else {
                break;
            };
            let txid = candidate.txid;
            let mut package = HashSet::new();
            if !collect_mining_package(self, txid, &selected, &mut package, &mut HashSet::new()) {
                continue;
            }
            let package_weight = package
                .iter()
                .map(|candidate| self.adjusted_weight(candidate))
                .fold(0u64, u64::saturating_add);
            let mut package_order = Vec::with_capacity(package.len());
            append_mining_package(self, txid, &package, &mut selected, &mut package_order);
            selected_weight = selected_weight.saturating_add(package_weight);
            ordered.extend(package_order);

            for selected_txid in package {
                metrics.remove(&selected_txid);
                let fee = self
                    .entries
                    .get(&selected_txid)
                    .map(|entry| {
                        i128::from(entry.fee_sat) + i128::from(self.fee_delta(&selected_txid))
                    })
                    .unwrap_or_default();
                let weight = self.adjusted_weight(&selected_txid);
                let mut descendants = vec![selected_txid];
                let mut index = 0;
                while let Some(current) = descendants.get(index).copied() {
                    index += 1;
                    let Some(children) = self.children.get(&current) else {
                        continue;
                    };
                    descendants.extend(
                        children
                            .iter()
                            .copied()
                            .filter(|child| self.entries.contains_key(child)),
                    );
                }
                for descendant in descendants {
                    if selected.contains(&descendant) {
                        continue;
                    }
                    let Some(package_metrics) = metrics.get_mut(&descendant) else {
                        continue;
                    };
                    package_metrics.fee = package_metrics.fee.saturating_sub(fee);
                    package_metrics.weight = package_metrics.weight.saturating_sub(weight);
                    package_metrics.version = package_metrics.version.saturating_add(1);
                    candidates.push(MiningCandidate {
                        txid: descendant,
                        fee: package_metrics.fee,
                        weight: package_metrics.weight,
                        version: package_metrics.version,
                    });
                }
            }
        }

        ordered
    }

    pub fn parents(&self, txid: &Txid) -> Vec<Txid> {
        let Some(entry) = self.entries.get(txid) else {
            return Vec::new();
        };
        let mut parents: Vec<Txid> = entry
            .transaction
            .input
            .iter()
            .map(|input| input.previous_output.txid)
            .filter(|parent| self.entries.contains_key(parent))
            .collect();
        parents.sort_by_key(ToString::to_string);
        parents.dedup();
        parents
    }

    pub fn children(&self, txid: &Txid) -> Vec<Txid> {
        let mut children = self.children.get(txid).map_or_else(Vec::new, |children| {
            children
                .iter()
                .filter(|child| self.entries.contains_key(*child))
                .copied()
                .collect::<Vec<_>>()
        });
        children.sort_by_key(ToString::to_string);
        children
    }

    pub fn ancestors(&self, txid: &Txid) -> Vec<Txid> {
        if !self.entries.contains_key(txid) {
            return Vec::new();
        }
        let mut found = HashSet::new();
        let mut pending = vec![*txid];
        while let Some(current) = pending.pop() {
            for parent in self.parents(&current) {
                if parent != *txid && found.insert(parent) {
                    pending.push(parent);
                }
            }
        }
        self.transaction_order()
            .into_iter()
            .filter(|candidate| found.contains(candidate))
            .collect()
    }

    pub fn descendants(&self, txid: &Txid) -> Vec<Txid> {
        if !self.entries.contains_key(txid) {
            return Vec::new();
        }
        let mut found = HashSet::new();
        let mut pending = vec![*txid];
        while let Some(current) = pending.pop() {
            for candidate in self.children(&current) {
                if candidate != *txid && found.insert(candidate) {
                    pending.push(candidate);
                }
            }
        }
        self.transaction_order()
            .into_iter()
            .filter(|candidate| found.contains(candidate))
            .collect()
    }

    pub fn load_from_file(&mut self, path: &Path, chain: &ChainState) -> Result<()> {
        self.load_from_file_with_expiry(path, chain, MEMPOOL_EXPIRY)
    }

    pub fn load_from_file_with_expiry(
        &mut self,
        path: &Path,
        chain: &ChainState,
        expiry: Duration,
    ) -> Result<()> {
        self.load_from_file_with_expiry_and_options(
            path,
            chain,
            expiry,
            MempoolLoadOptions::default(),
        )
    }

    pub fn load_from_file_with_expiry_and_options(
        &mut self,
        path: &Path,
        chain: &ChainState,
        expiry: Duration,
        options: MempoolLoadOptions,
    ) -> Result<()> {
        if !path.exists() {
            return Ok(());
        }
        let bytes = fs::read(path).with_context(|| format!("reading {}", path.display()))?;
        let now = time::unix_time();
        if bytes.first() == Some(&b'[') {
            let entries: Vec<DiskMempoolEntry> = serde_json::from_slice(&bytes)
                .with_context(|| format!("decoding legacy JSON mempool {}", path.display()))?;
            let cutoff = now.saturating_sub(expiry.as_secs());
            for entry in entries {
                let added_at = if options.use_current_time {
                    now
                } else {
                    entry.added_at
                };
                if added_at > cutoff {
                    let _ = self.accept_at(entry.transaction, chain, added_at);
                }
            }
        } else {
            let (entries, deltas, unbroadcast) = decode_core_mempool(&bytes)
                .with_context(|| format!("decoding Core mempool {}", path.display()))?;
            let cutoff = now.saturating_sub(expiry.as_secs());
            for entry in entries {
                let added_at = if options.use_current_time {
                    now
                } else {
                    entry.added_at
                };
                let txid = entry.transaction.compute_txid();
                if options.apply_fee_delta_priority && entry.fee_delta != 0 {
                    // Core restores transaction-specific prioritisation before
                    // re-admission so it affects the fee-rate policy check.
                    self.prioritise(txid, entry.fee_delta);
                }
                if added_at > cutoff {
                    let _ = self.accept_at(entry.transaction, chain, added_at);
                }
            }
            if options.apply_fee_delta_priority {
                for (txid, fee_delta) in deltas {
                    self.prioritise(txid, fee_delta);
                }
            }
            if options.apply_unbroadcast_set {
                for txid in unbroadcast {
                    self.add_unbroadcast(txid);
                }
            }
        }
        Ok(())
    }

    pub fn save_to_file(&self, path: &Path) -> Result<()> {
        self.save_to_file_with_format(path, false)
    }

    pub fn save_to_file_with_format(&self, path: &Path, legacy_v1: bool) -> Result<()> {
        let mut payload = Vec::new();
        let transaction_ids = self.main_order();
        append_u64(&mut payload, transaction_ids.len() as u64);
        let mut serialized_transactions = HashSet::with_capacity(transaction_ids.len());
        for txid in transaction_ids {
            let Some(entry) = self.entries.get(&txid) else {
                continue;
            };
            payload.extend_from_slice(&serialize(&entry.transaction));
            append_i64(
                &mut payload,
                i64::try_from(entry.added_at).unwrap_or(i64::MAX),
            );
            append_i64(&mut payload, self.fee_delta(&txid));
            serialized_transactions.insert(txid);
        }

        let deltas = self
            .priorities
            .iter()
            .filter(|(txid, _)| !serialized_transactions.contains(*txid))
            .collect::<Vec<_>>();
        payload.extend_from_slice(&serialize(&VarInt(deltas.len() as u64)));
        for (txid, fee_delta) in deltas {
            payload.extend_from_slice(&serialize(txid));
            append_i64(&mut payload, *fee_delta);
        }
        let unbroadcast = self.unbroadcast_txids();
        payload.extend_from_slice(&serialize(&VarInt(unbroadcast.len() as u64)));
        for txid in unbroadcast {
            payload.extend_from_slice(&serialize(&txid));
        }

        let key = random::<[u8; CORE_MEMPOOL_OBFUSCATION_KEY_SIZE]>();
        let mut bytes = Vec::with_capacity(if legacy_v1 { 8 } else { 17 } + payload.len());
        append_u64(
            &mut bytes,
            if legacy_v1 {
                CORE_MEMPOOL_DUMP_VERSION_V1
            } else {
                CORE_MEMPOOL_DUMP_VERSION_V2
            },
        );
        if !legacy_v1 {
            bytes.extend_from_slice(&serialize(&key.to_vec()));
            let payload_offset = bytes.len();
            xor_obfuscate(&mut payload, &key, payload_offset);
        }
        bytes.extend_from_slice(&payload);
        let temp = path.with_file_name(format!(
            "{}.tmp",
            path.file_name().unwrap_or_default().to_string_lossy()
        ));
        fs::write(&temp, bytes).with_context(|| format!("writing {}", temp.display()))?;
        fs::rename(&temp, path)
            .with_context(|| format!("replacing mempool file {}", path.display()))?;
        Ok(())
    }

    pub fn accept(
        &mut self,
        transaction: Transaction,
        chain: &ChainState,
    ) -> Result<Txid, MempoolError> {
        self.accept_with_sibling(transaction, chain, true)
    }

    /// Validate a transaction without Core's single-transaction TRUC sibling
    /// eviction carve-out. `testmempoolaccept` uses this mode because it must
    /// not mutate even a cloned mempool's replacement set.
    pub(crate) fn accept_without_sibling(
        &mut self,
        transaction: Transaction,
        chain: &ChainState,
    ) -> Result<Txid, MempoolError> {
        self.accept_with_sibling(transaction, chain, false)
    }

    /// Validate a transaction for testmempoolaccept without allowing it to
    /// replace an existing mempool transaction. Core deliberately keeps
    /// replacement disabled for this dry-run RPC even though normal local
    /// admission uses full-RBF.
    pub(crate) fn accept_for_test(
        &mut self,
        transaction: Transaction,
        chain: &ChainState,
    ) -> Result<Txid, MempoolError> {
        let conflicts = self.conflicts_for(&transaction);
        self.check_replacement_cluster_limit(transaction.compute_txid(), &conflicts)?;
        if !conflicts.is_empty() {
            return Err(MempoolError::ReplacementDisallowed);
        }
        self.accept_without_sibling(transaction, chain)
    }

    fn accept_with_sibling(
        &mut self,
        transaction: Transaction,
        chain: &ChainState,
        allow_sibling_eviction: bool,
    ) -> Result<Txid, MempoolError> {
        let added_at = time::unix_time();
        match self.accept_at(transaction.clone(), chain, added_at) {
            Err(MempoolError::Conflict(_)) => {
                let mut conflicts = self.conflicts_for(&transaction);
                let sibling = allow_sibling_eviction
                    .then(|| self.truc_sibling_for(&transaction))
                    .flatten();
                if let Some(sibling) = sibling
                    && !conflicts.contains(&sibling)
                {
                    conflicts.push(sibling);
                    self.replace_with_conflicts(transaction, chain, added_at, conflicts, true)
                } else {
                    self.replace(transaction, chain, added_at)
                }
            }
            Err(error @ MempoolError::Truc(_)) if allow_sibling_eviction => {
                if let Some(sibling) = self.truc_sibling_for(&transaction) {
                    self.replace_with_conflicts(transaction, chain, added_at, vec![sibling], true)
                } else {
                    Err(error)
                }
            }
            result => result,
        }
    }

    /// Admit a topologically ordered package using the package feerate for
    /// the minimum-relay check. This models Core's one-parent/one-child
    /// package relay policy: an individual parent may be below the relay
    /// floor when the package as a whole pays it.
    pub fn accept_package(
        &mut self,
        transactions: &[Transaction],
        chain: &ChainState,
    ) -> Result<Vec<Txid>, MempoolError> {
        let (candidate, result, _) = self.accept_package_with_state(transactions, chain);
        if result.is_ok() {
            *self = candidate;
        }
        result
    }

    /// Validate a package on a cloned mempool and return the candidate even
    /// when a later transaction fails. The returned boolean identifies an
    /// actual two-transaction package-RBF attempt, rather than merely a
    /// package that could have used the package-RBF topology. Core can commit
    /// a valid prefix from ordinary package submission; package RBF remains
    /// atomic.
    pub(crate) fn accept_package_with_state(
        &self,
        transactions: &[Transaction],
        chain: &ChainState,
    ) -> (Self, Result<Vec<Txid>, MempoolError>, bool) {
        let mut candidate = self.clone();
        let package_has_preexisting = transactions
            .iter()
            .any(|transaction| candidate.get(&transaction.compute_txid()).is_some());
        let allow_low_fee_parent = package_is_child_with_parents_tree(transactions);
        let package_rbf = transactions.len() == 2
            && allow_low_fee_parent
            && !package_has_preexisting
            && transactions
                .iter()
                .any(|transaction| !candidate.conflicts_for(transaction).is_empty());
        let result = self.accept_package_inner(&mut candidate, transactions, chain);
        (candidate, result, package_rbf)
    }

    fn accept_package_inner(
        &self,
        candidate: &mut Self,
        transactions: &[Transaction],
        chain: &ChainState,
    ) -> Result<Vec<Txid>, MempoolError> {
        if transactions.is_empty() {
            return Err(MempoolError::Empty);
        }
        let added_at = time::unix_time();
        let mut accepted = Vec::with_capacity(transactions.len());
        let mut package_fee = 0i128;
        let mut package_vsize = 0u64;
        let allow_low_fee_parent = package_is_child_with_parents_tree(transactions);
        let package_has_preexisting = transactions
            .iter()
            .any(|transaction| candidate.get(&transaction.compute_txid()).is_some());
        let package_rbf = transactions.len() == 2
            && allow_low_fee_parent
            && !package_has_preexisting
            && transactions
                .iter()
                .any(|transaction| !candidate.conflicts_for(transaction).is_empty());
        let mut conflicting_fee = 0i128;
        let mut package_replaced = false;
        if package_rbf {
            let mut direct_conflicts = transactions
                .iter()
                .flat_map(|transaction| candidate.conflicts_for(transaction))
                .collect::<Vec<_>>();
            direct_conflicts.sort_by_key(ToString::to_string);
            direct_conflicts.dedup();
            if let Some(transaction) = transactions.first() {
                candidate.check_replacement_cluster_limit(
                    transaction.compute_txid(),
                    &direct_conflicts,
                )?;
            }
            if !direct_conflicts.is_empty() {
                candidate.check_replacement_policy(&direct_conflicts)?;
                package_replaced = true;
                let removal = candidate.conflicts_and_descendants(&direct_conflicts);
                if transactions.iter().any(|transaction| {
                    transaction.input.iter().any(|input| {
                        candidate.entries.contains_key(&input.previous_output.txid)
                            && !removal.contains(&input.previous_output.txid)
                    })
                }) {
                    return Err(MempoolError::ReplacementUnconfirmedInput);
                }
                conflicting_fee = removal
                    .iter()
                    .filter_map(|txid| {
                        candidate
                            .entries
                            .get(txid)
                            .map(|entry| candidate.modified_fee_sat(txid, entry.fee_sat))
                    })
                    .fold(0i128, i128::saturating_add);
                for txid in removal {
                    candidate.remove(&txid);
                }
            }
        }
        let mut new_count = 0usize;
        for transaction in transactions {
            let txid = transaction.compute_txid();
            if let Some(existing) = candidate.get(&txid) {
                if existing.transaction.compute_wtxid() != transaction.compute_wtxid() {
                    return Err(MempoolError::AlreadyPresent);
                }
                accepted.push(txid);
                continue;
            }
            let txid = if transactions.len() == 1 {
                // Core's package path still permits a single transaction to
                // replace an existing mempool conflict, but does not apply
                // the single-transaction TRUC sibling-eviction carve-out.
                candidate.accept_without_sibling(transaction.clone(), chain)?
            } else {
                candidate.accept_at_with_policy(
                    transaction.clone(),
                    chain,
                    added_at,
                    !allow_low_fee_parent,
                )?
            };
            let entry = candidate.get(&txid).ok_or(MempoolError::BadOutput)?;
            package_fee =
                package_fee.saturating_add(candidate.modified_fee_sat(&txid, entry.fee_sat));
            package_vsize = package_vsize.saturating_add(entry.vsize);
            accepted.push(txid);
            new_count += 1;
        }
        if allow_low_fee_parent && new_count > 0 {
            let child_txid = transactions
                .last()
                .ok_or(MempoolError::Empty)?
                .compute_txid();
            let child = candidate.get(&child_txid).ok_or(MempoolError::BadOutput)?;
            if !fee_rate_meets(
                candidate.modified_fee_sat(&child_txid, child.fee_sat),
                child.vsize,
                candidate.mempool_min_fee_sat_per_kvb(),
            ) {
                return Err(MempoolError::FeeRate);
            }
        }
        if new_count > 0
            && !fee_rate_meets(
                package_fee,
                package_vsize,
                candidate.mempool_min_fee_sat_per_kvb(),
            )
        {
            return Err(MempoolError::FeeRate);
        }
        if package_rbf && conflicting_fee > 0 {
            let required_fee = conflicting_fee.saturating_add(fee_for_rate(
                candidate.policy.incremental_relay_fee_sat_per_kvb,
                package_vsize,
            ));
            if package_fee < required_fee {
                return Err(MempoolError::ReplacementFee);
            }
            let parent_txid = transactions[0].compute_txid();
            let parent = candidate.get(&parent_txid).ok_or(MempoolError::BadOutput)?;
            let parent_fee = candidate.modified_fee_sat(&parent_txid, parent.fee_sat);
            if package_fee.saturating_mul(i128::from(parent.vsize))
                <= parent_fee.saturating_mul(i128::from(package_vsize))
            {
                return Err(MempoolError::ReplacementFee);
            }
        }
        if package_rbf && package_replaced && !self.improves_feerate_diagram(candidate) {
            return Err(MempoolError::ReplacementFeerateDiagram);
        }
        validate_ephemeral_spends(transactions, candidate)?;
        Ok(accepted)
    }

    /// Validate a package for testmempoolaccept. Package feerates and
    /// replacement are intentionally disabled for this dry-run path, just as
    /// in Core's PackageTestAccept arguments.
    pub(crate) fn accept_package_for_test(
        &mut self,
        transactions: &[Transaction],
        chain: &ChainState,
    ) -> Result<Vec<Txid>, MempoolError> {
        if transactions.is_empty() {
            return Err(MempoolError::Empty);
        }
        let added_at = time::unix_time();
        let mut candidate = self.clone();
        let mut accepted = Vec::with_capacity(transactions.len());
        for transaction in transactions {
            let txid = transaction.compute_txid();
            let conflicts = candidate.conflicts_for(transaction);
            candidate.check_replacement_cluster_limit(txid, &conflicts)?;
            if candidate.entries.contains_key(&txid) || !conflicts.is_empty() {
                return Err(MempoolError::ReplacementDisallowed);
            }
            accepted.push(candidate.accept_at(transaction.clone(), chain, added_at)?);
        }
        validate_ephemeral_spends(transactions, &candidate)?;
        *self = candidate;
        Ok(accepted)
    }

    fn replace(
        &mut self,
        transaction: Transaction,
        chain: &ChainState,
        added_at: u64,
    ) -> Result<Txid, MempoolError> {
        let conflicts = self.conflicts_for(&transaction);
        self.replace_with_conflicts(transaction, chain, added_at, conflicts, false)
    }

    fn replace_with_conflicts(
        &mut self,
        transaction: Transaction,
        chain: &ChainState,
        added_at: u64,
        conflicts: Vec<Txid>,
        sibling_eviction: bool,
    ) -> Result<Txid, MempoolError> {
        if conflicts.is_empty() {
            return Err(MempoolError::Conflict(transaction.compute_txid()));
        }
        let direct_conflicts = self.conflicts_for(&transaction);
        self.check_replacement_cluster_limit(transaction.compute_txid(), &direct_conflicts)?;
        self.check_replacement_policy(&direct_conflicts)?;
        let removal = self.conflicts_and_descendants(&conflicts);
        let mut allowed_unconfirmed = HashSet::new();
        for conflict in &conflicts {
            allowed_unconfirmed.extend(self.ancestors(conflict));
        }
        for input in &transaction.input {
            if self.entries.contains_key(&input.previous_output.txid)
                && !removal.contains(&input.previous_output.txid)
                && !allowed_unconfirmed.contains(&input.previous_output.txid)
            {
                return Err(MempoolError::ReplacementUnconfirmedInput);
            }
        }
        let conflict_fees = removal
            .iter()
            .filter_map(|txid| self.entries.get(txid))
            .map(|entry| self.modified_fee_sat(&entry.transaction.compute_txid(), entry.fee_sat))
            .fold(0i128, i128::saturating_add);
        let mut candidate = self.clone();
        for txid in &removal {
            candidate.remove(txid);
        }
        let txid = candidate.accept_at(transaction, chain, added_at)?;
        let replacement_fee = candidate
            .get(&txid)
            .map(|entry| candidate.modified_fee_sat(&txid, entry.fee_sat))
            .ok_or(MempoolError::BadOutput)?;
        let replacement_vsize = candidate
            .get(&txid)
            .map(|entry| entry.vsize)
            .unwrap_or_default();
        let required_fee = conflict_fees.saturating_add(fee_for_rate(
            candidate.policy.incremental_relay_fee_sat_per_kvb,
            replacement_vsize,
        ));
        if replacement_fee < required_fee {
            return Err(MempoolError::ReplacementFee);
        }
        if sibling_eviction {
            let replacement_vsize = candidate
                .get(&txid)
                .map(|entry| entry.vsize)
                .ok_or(MempoolError::BadOutput)?;
            for sibling in conflicts
                .iter()
                .filter(|conflict| !direct_conflicts.contains(conflict))
            {
                let sibling_entry = self.get(sibling).ok_or(MempoolError::BadOutput)?;
                let replacement_fee_rate = replacement_fee * i128::from(sibling_entry.vsize);
                let sibling_fee_rate = self.modified_fee_sat(sibling, sibling_entry.fee_sat)
                    * i128::from(replacement_vsize);
                if replacement_fee_rate <= sibling_fee_rate {
                    return Err(MempoolError::ReplacementFee);
                }
            }
        }
        if !self.improves_feerate_diagram(&candidate) {
            return Err(MempoolError::ReplacementFeerateDiagram);
        }
        *self = candidate;
        Ok(txid)
    }

    fn conflicts_for(&self, transaction: &Transaction) -> Vec<Txid> {
        let mut conflicts = transaction
            .input
            .iter()
            .filter_map(|input| self.spent.get(&input.previous_output).copied())
            .collect::<Vec<_>>();
        conflicts.sort_by_key(ToString::to_string);
        conflicts.dedup();
        conflicts
    }

    fn conflicts_and_descendants(&self, conflicts: &[Txid]) -> HashSet<Txid> {
        let mut removal = HashSet::new();
        let mut pending = conflicts.to_vec();
        while let Some(txid) = pending.pop() {
            if !removal.insert(txid) {
                continue;
            }
            pending.extend(self.children(&txid));
        }
        removal
    }

    fn check_replacement_cluster_limit(
        &self,
        txid: Txid,
        direct_conflicts: &[Txid],
    ) -> Result<(), MempoolError> {
        let count = self.conflicting_cluster_count(direct_conflicts);
        if count > MAX_REPLACEMENT_CANDIDATES {
            return Err(MempoolError::TooManyReplacementCandidates {
                txid,
                count,
                limit: MAX_REPLACEMENT_CANDIDATES,
            });
        }
        Ok(())
    }

    fn check_replacement_policy(&self, direct_conflicts: &[Txid]) -> Result<(), MempoolError> {
        if self.policy.rbf_policy == RbfPolicy::Never {
            return Err(MempoolError::ReplacementDisallowed);
        }
        if self.policy.rbf_policy == RbfPolicy::OptIn
            && direct_conflicts.iter().any(|txid| {
                self.entries.get(txid).is_some_and(|entry| {
                    entry.transaction.version.0 != TRUC_VERSION
                        && !signals_replaceability(&entry.transaction)
                })
            })
        {
            return Err(MempoolError::ReplacementDisallowed);
        }
        Ok(())
    }

    /// Count the distinct connected mempool clusters touched by direct
    /// conflicts. Core limits this count rather than the number of individual
    /// transactions so a replacement can still evict a large connected
    /// package while bounding work across unrelated clusters.
    fn conflicting_cluster_count(&self, direct_conflicts: &[Txid]) -> usize {
        let mut visited = HashSet::new();
        let mut clusters = 0;
        for conflict in direct_conflicts {
            if !self.entries.contains_key(conflict) || !visited.insert(*conflict) {
                continue;
            }
            clusters += 1;
            let mut pending = vec![*conflict];
            while let Some(txid) = pending.pop() {
                pending.extend(self.parents(&txid));
                pending.extend(self.children(&txid));
                for connected in std::mem::take(&mut pending) {
                    if visited.insert(connected) {
                        pending.push(connected);
                    }
                }
            }
        }
        clusters
    }

    fn feerate_diagram(&self) -> Vec<(i128, u64)> {
        let mut chunks = Vec::new();
        for txid in self.mining_order(u64::MAX, 0) {
            let Some(entry) = self.entries.get(&txid) else {
                continue;
            };
            append_feerate_chunk(
                &mut chunks,
                self.modified_fee_sat(&txid, entry.fee_sat),
                self.adjusted_weight(&txid),
            );
        }
        chunks
    }

    fn improves_feerate_diagram(&self, candidate: &Self) -> bool {
        compare_fee_rate_diagrams(&candidate.feerate_diagram(), &self.feerate_diagram())
            == Some(Ordering::Greater)
    }

    fn truc_sibling_for(&self, transaction: &Transaction) -> Option<Txid> {
        if transaction.version.0 != TRUC_VERSION
            || transaction.vsize() as u64 > TRUC_CHILD_MAX_VSIZE
        {
            return None;
        }
        let mut parent_ids = transaction
            .input
            .iter()
            .map(|input| input.previous_output.txid)
            .filter(|parent| self.entries.contains_key(parent))
            .collect::<Vec<_>>();
        parent_ids.sort_by_key(ToString::to_string);
        parent_ids.dedup();
        if parent_ids.len() != 1 {
            return None;
        }
        let parent_id = parent_ids[0];
        let parent = self.entries.get(&parent_id)?;
        if parent.transaction.version.0 != TRUC_VERSION
            || self.ancestors(&parent_id).len().saturating_add(2) > TRUC_ANCESTOR_LIMIT
        {
            return None;
        }
        let descendants = self.descendants(&parent_id);
        if descendants.len() != 1 {
            return None;
        }
        let sibling = descendants[0];
        self.descendants(&sibling).is_empty().then_some(sibling)
    }

    fn accept_at(
        &mut self,
        transaction: Transaction,
        chain: &ChainState,
        added_at: u64,
    ) -> Result<Txid, MempoolError> {
        self.accept_at_with_options(transaction, chain, added_at, true, true)
    }

    fn accept_at_with_policy(
        &mut self,
        transaction: Transaction,
        chain: &ChainState,
        added_at: u64,
        enforce_fee_rate: bool,
    ) -> Result<Txid, MempoolError> {
        self.accept_at_with_options(transaction, chain, added_at, enforce_fee_rate, true)
    }

    pub(crate) fn accept_reorg(
        &mut self,
        transaction: Transaction,
        chain: &ChainState,
        added_at: u64,
    ) -> Result<Txid, MempoolError> {
        let txid = self.accept_at_with_options(transaction, chain, added_at, false, false)?;
        self.relay_sequences.insert(txid, 0);
        Ok(txid)
    }

    fn accept_at_with_options(
        &mut self,
        transaction: Transaction,
        chain: &ChainState,
        added_at: u64,
        enforce_fee_rate: bool,
        enforce_mempool_policy: bool,
    ) -> Result<Txid, MempoolError> {
        self.accept_at_with_sequence(
            transaction,
            chain,
            added_at,
            enforce_fee_rate,
            enforce_mempool_policy,
            true,
        )
    }

    fn accept_at_without_sequence(
        &mut self,
        transaction: Transaction,
        chain: &ChainState,
        added_at: u64,
    ) -> Result<Txid, MempoolError> {
        self.accept_at_with_sequence(transaction, chain, added_at, false, false, false)
    }

    fn accept_at_with_sequence(
        &mut self,
        transaction: Transaction,
        chain: &ChainState,
        added_at: u64,
        enforce_fee_rate: bool,
        enforce_mempool_policy: bool,
        record_sequence: bool,
    ) -> Result<Txid, MempoolError> {
        let txid = transaction.compute_txid();
        if self.entries.contains_key(&txid) {
            return Err(MempoolError::AlreadyPresent);
        }
        if transaction.output.iter().enumerate().any(|(vout, _)| {
            u32::try_from(vout)
                .ok()
                .and_then(|vout| chain.utxo(&OutPoint::new(txid, vout)))
                .is_some()
        }) {
            return Err(MempoolError::AlreadyInChain);
        }
        if transaction.is_coinbase() {
            return Err(MempoolError::Coinbase);
        }
        if transaction
            .input
            .iter()
            .any(|input| input.previous_output.is_null())
        {
            return Err(MempoolError::NullPrevout);
        }
        if transaction.input.is_empty() || transaction.output.is_empty() {
            return Err(MempoolError::Empty);
        }
        if transaction.base_size().saturating_mul(4) > validation::MAX_BLOCK_WEIGHT {
            return Err(MempoolError::Oversized);
        }
        let mut seen = HashSet::with_capacity(transaction.input.len());
        let mut input_total = 0u64;
        let mut previous_outputs = Vec::with_capacity(transaction.input.len());
        let mut previous_entries = Vec::with_capacity(transaction.input.len());
        for input in &transaction.input {
            if !seen.insert(input.previous_output) {
                return Err(MempoolError::DuplicateInput);
            }
            if let Some(conflict) = self.spent.get(&input.previous_output) {
                return Err(MempoolError::Conflict(*conflict));
            }
            let previous = if let Some(entry) = self.entries.get(&input.previous_output.txid) {
                let output = entry
                    .transaction
                    .output
                    .get(input.previous_output.vout as usize)
                    .ok_or(MempoolError::MissingInput(input.previous_output))?;
                previous_entries.push(crate::chain::UtxoEntry {
                    output: output.clone(),
                    height: chain.height().saturating_add(1),
                    median_time_past: chain.median_time_past_value(),
                    coinbase: false,
                });
                output
            } else {
                let entry = chain
                    .utxo(&input.previous_output)
                    .ok_or(MempoolError::MissingInput(input.previous_output))?;
                if entry.coinbase && chain.height() + 1 < entry.height.saturating_add(100) {
                    return Err(MempoolError::MissingInput(input.previous_output));
                }
                previous_entries.push(entry.clone());
                &entry.output
            };
            input_total = input_total
                .checked_add(previous.value.to_sat())
                .ok_or(MempoolError::BadOutput)?;
            if input_total > Amount::MAX_MONEY.to_sat() {
                return Err(MempoolError::BadOutput);
            }
            previous_outputs.push(previous.clone());
        }
        validation::validate_transaction_finality(
            &transaction,
            chain.height() + 1,
            chain.median_time_past_value(),
            // Core's mempool policy always enforces BIP68 sequence locks. The
            // consensus CSV deployment height only controls block connection;
            // it must not let a pre-activation mempool accept a transaction
            // that cannot be included in the next block under Core policy.
            true,
            &previous_entries,
        )
        .map_err(|error| MempoolError::Script(error.to_string()))?;
        chain
            .validate_mempool_transaction_scripts(&transaction, &previous_outputs)
            .map_err(|error| MempoolError::Script(error.to_string()))?;
        let output_total = transaction
            .output
            .iter()
            .map(|output| output.value.to_sat())
            .try_fold(0u64, u64::checked_add)
            .ok_or(MempoolError::BadOutput)?;
        if output_total > Amount::MAX_MONEY.to_sat() {
            return Err(MempoolError::BadOutput);
        }
        if output_total > input_total {
            return Err(MempoolError::NegativeFee);
        }
        if transaction
            .output
            .iter()
            .any(|output| output.value > Amount::MAX_MONEY)
        {
            return Err(MempoolError::BadOutput);
        }
        let fee_sat = input_total - output_total;
        let script_flags =
            validation::script_flags_for_block(chain.network, chain.height().saturating_add(1), 0);
        let sigop_cost =
            validation::transaction_sigop_cost(&transaction, &previous_outputs, script_flags)
                as u64;
        let adjusted_weight = transaction
            .weight()
            .to_wu()
            .max(sigop_cost.saturating_mul(self.policy.bytes_per_sigop));
        let vsize = adjusted_weight.saturating_add(3) / 4;
        if transaction.base_size() < MIN_STANDARD_TX_NONWITNESS_SIZE {
            return Err(MempoolError::NonStandard("tx-size-small".to_owned()));
        }
        let modified_fee_sat = i64::try_from(fee_sat)
            .unwrap_or(i64::MAX)
            .saturating_add(self.fee_delta(&txid));
        if self.policy.require_standard {
            validate_standard_policy_with_modified_fee_and_policy(
                &transaction,
                &previous_outputs,
                fee_sat,
                modified_fee_sat,
                &self.policy,
            )?;
        }
        let truc_min_fee_exempt =
            self.policy.truc_policy == TrucPolicy::Enforce && transaction.version.0 == TRUC_VERSION;
        if enforce_fee_rate
            && !truc_min_fee_exempt
            && !fee_rate_meets(
                i128::from(modified_fee_sat),
                vsize,
                self.mempool_min_fee_sat_per_kvb(),
            )
        {
            return Err(MempoolError::FeeRate);
        }
        if enforce_mempool_policy {
            match self.policy.truc_policy {
                TrucPolicy::Reject if transaction.version.0 == TRUC_VERSION => {
                    return Err(MempoolError::NonStandard("version".to_owned()));
                }
                TrucPolicy::Enforce => self.check_truc_policy(&transaction, vsize)?,
                TrucPolicy::Accept | TrucPolicy::Reject => {}
            }
            validate_ephemeral_spends(std::slice::from_ref(&transaction), self)?;
        }
        let size = bitcoin::consensus::encode::serialize(&transaction).len();
        let memory_usage = mempool_entry_memory_usage(&transaction);
        if enforce_mempool_policy {
            self.check_cluster_limits_with_vsize(&transaction, vsize)?;
            let protected = self.ancestors_for_transaction(&transaction);
            self.ensure_space(memory_usage, &protected)?;
        }
        let entry = MempoolEntry {
            transaction,
            fee_sat,
            vsize,
            added_at,
            height: chain.height(),
        };
        let wtxid = entry.transaction.compute_wtxid();
        for input in &entry.transaction.input {
            self.spent.insert(input.previous_output, txid);
            if self.entries.contains_key(&input.previous_output.txid) {
                self.children
                    .entry(input.previous_output.txid)
                    .or_default()
                    .insert(txid);
            }
        }
        self.memory_usage = self.memory_usage.saturating_add(memory_usage);
        self.bytes += size;
        self.vbytes = self.vbytes.saturating_add(vsize);
        self.entries.insert(txid, entry);
        self.adjusted_weights.insert(txid, adjusted_weight);
        self.wtxids.insert(wtxid, txid);
        self.relay_sequences.insert(txid, self.sequence);
        self.invalidate_graph_optimality();
        if record_sequence {
            let sequence = self.sequence;
            self.sequence = self.sequence.saturating_add(1);
            self.changes.push(MempoolChange {
                transaction: self
                    .entries
                    .get(&txid)
                    .expect("inserted mempool transaction")
                    .transaction
                    .clone(),
                sequence,
                kind: MempoolChangeKind::Added,
            });
        }
        Ok(txid)
    }

    fn record_removal(&mut self, transaction: Transaction, notify_zmq: bool) {
        let sequence = self.sequence;
        self.sequence = self.sequence.saturating_add(1);
        self.changes.push(MempoolChange {
            transaction,
            sequence,
            kind: MempoolChangeKind::Removed { notify_zmq },
        });
    }

    fn ancestors_for_transaction(&self, transaction: &Transaction) -> HashSet<Txid> {
        let mut ancestors = HashSet::new();
        let mut pending = transaction
            .input
            .iter()
            .map(|input| input.previous_output.txid)
            .collect::<Vec<_>>();
        while let Some(txid) = pending.pop() {
            if !self.entries.contains_key(&txid) || !ancestors.insert(txid) {
                continue;
            }
            pending.extend(self.parents(&txid));
        }
        ancestors
    }

    fn ensure_space(
        &mut self,
        additional_memory: usize,
        protected: &HashSet<Txid>,
    ) -> Result<(), MempoolError> {
        if additional_memory > self.max_bytes {
            return Err(MempoolError::Full);
        }
        while self.memory_usage.saturating_add(additional_memory) > self.max_bytes {
            let Some((package, package_vsize, package_fee)) =
                self.lowest_eviction_package(protected)
            else {
                return Err(MempoolError::Full);
            };
            let package_fee_rate = fee_rate_from_package(package_fee, package_vsize);
            self.rolling_min_fee_sat_per_kvb = self.rolling_min_fee_sat_per_kvb.max(
                package_fee_rate.saturating_add(self.policy.incremental_relay_fee_sat_per_kvb)
                    as f64,
            );
            self.block_since_last_rolling_fee_bump = false;
            for txid in package {
                self.remove(&txid);
            }
        }
        Ok(())
    }

    pub(crate) fn enforce_size_limit(&mut self) {
        let _ = self.ensure_space(0, &HashSet::new());
    }

    fn decay_rolling_min_fee(&mut self) {
        if !self.block_since_last_rolling_fee_bump || self.rolling_min_fee_sat_per_kvb == 0.0 {
            return;
        }
        let now = time::unix_time();
        if now <= self.rolling_fee_last_updated.saturating_add(10) {
            return;
        }
        let mut halflife = ROLLING_FEE_HALFLIFE_SECS;
        if self.memory_usage < self.max_bytes / 4 {
            halflife /= 4.0;
        } else if self.memory_usage < self.max_bytes / 2 {
            halflife /= 2.0;
        }
        let elapsed = now.saturating_sub(self.rolling_fee_last_updated) as f64;
        self.rolling_min_fee_sat_per_kvb /= 2.0_f64.powf(elapsed / halflife);
        self.rolling_fee_last_updated = now;
        if self.rolling_min_fee_sat_per_kvb
            < self.policy.incremental_relay_fee_sat_per_kvb as f64 / 2.0
        {
            self.rolling_min_fee_sat_per_kvb = 0.0;
        }
    }

    fn check_truc_policy(&self, transaction: &Transaction, vsize: u64) -> Result<(), MempoolError> {
        let transaction_id = transaction.compute_txid();
        let transaction_wtxid = transaction.compute_wtxid();
        let mut parent_ids = Vec::new();
        let mut seen_parents = HashSet::new();
        for input in &transaction.input {
            let parent_id = input.previous_output.txid;
            if self.entries.contains_key(&parent_id) && seen_parents.insert(parent_id) {
                parent_ids.push(parent_id);
            }
        }

        for parent_id in &parent_ids {
            let parent = self
                .entries
                .get(parent_id)
                .expect("mempool parent exists when checking TRUC policy");
            if transaction.version.0 != TRUC_VERSION && parent.transaction.version.0 == TRUC_VERSION
            {
                return Err(MempoolError::Truc(format!(
                    "non-version=3 tx {transaction_id} (wtxid={transaction_wtxid}) cannot spend from version=3 tx {parent_id} (wtxid={})",
                    parent.transaction.compute_wtxid()
                )));
            }
            if transaction.version.0 == TRUC_VERSION && parent.transaction.version.0 != TRUC_VERSION
            {
                return Err(MempoolError::Truc(format!(
                    "version=3 tx {transaction_id} (wtxid={transaction_wtxid}) cannot spend from non-version=3 tx {parent_id} (wtxid={})",
                    parent.transaction.compute_wtxid()
                )));
            }
        }

        if transaction.version.0 != TRUC_VERSION {
            return Ok(());
        }
        if vsize > TRUC_MAX_VSIZE {
            return Err(MempoolError::Truc(format!(
                "version=3 tx {transaction_id} (wtxid={transaction_wtxid}) is too big: {vsize} > {TRUC_MAX_VSIZE} virtual bytes"
            )));
        }
        if parent_ids.len().saturating_add(1) > TRUC_ANCESTOR_LIMIT {
            return Err(MempoolError::Truc(format!(
                "tx {transaction_id} (wtxid={transaction_wtxid}) would have too many ancestors"
            )));
        }

        let Some(parent_id) = parent_ids.first() else {
            return Ok(());
        };
        let parent_ancestor_count = self.ancestors(parent_id).len().saturating_add(1);
        if parent_ancestor_count.saturating_add(1) > TRUC_ANCESTOR_LIMIT {
            return Err(MempoolError::Truc(format!(
                "tx {transaction_id} (wtxid={transaction_wtxid}) would have too many ancestors"
            )));
        }
        if vsize > TRUC_CHILD_MAX_VSIZE {
            return Err(MempoolError::Truc(format!(
                "version=3 child tx {transaction_id} (wtxid={transaction_wtxid}) is too big: {vsize} > {TRUC_CHILD_MAX_VSIZE} virtual bytes"
            )));
        }
        if self.descendants(parent_id).len().saturating_add(2) > TRUC_DESCENDANT_LIMIT {
            return Err(MempoolError::Truc(format!(
                "tx {parent_id} (wtxid={}) would exceed descendant count limit",
                self.entries
                    .get(parent_id)
                    .expect("mempool parent exists when checking TRUC policy")
                    .transaction
                    .compute_wtxid()
            )));
        }
        Ok(())
    }

    fn lowest_eviction_package(
        &self,
        protected: &HashSet<Txid>,
    ) -> Option<(HashSet<Txid>, u64, i128)> {
        let mut best: Option<(HashSet<Txid>, Txid, u64, i128)> = None;
        for txid in self.entries.keys().copied() {
            let mut package = HashSet::from([txid]);
            package.extend(self.descendants(&txid));
            if package
                .iter()
                .any(|candidate| protected.contains(candidate))
            {
                continue;
            }
            let package_vsize = package
                .iter()
                .filter_map(|candidate| self.entries.get(candidate))
                .map(|entry| entry.vsize)
                .fold(0u64, u64::saturating_add);
            if package_vsize == 0 {
                continue;
            }
            let package_fee = package
                .iter()
                .filter_map(|candidate| {
                    self.entries.get(candidate).map(|entry| {
                        i128::from(entry.fee_sat) + i128::from(self.fee_delta(candidate))
                    })
                })
                .fold(0i128, i128::saturating_add);
            let replace = match &best {
                None => true,
                Some((_, best_txid, best_vsize, best_fee)) => {
                    let left = package_fee.saturating_mul(i128::from(*best_vsize));
                    let right = best_fee.saturating_mul(i128::from(package_vsize));
                    left < right || (left == right && txid.to_string() < best_txid.to_string())
                }
            };
            if replace {
                best = Some((package, txid, package_vsize, package_fee));
            }
        }
        best.map(|(package, _, package_vsize, package_fee)| (package, package_vsize, package_fee))
    }

    #[cfg(test)]
    fn check_cluster_limits(&self, transaction: &Transaction) -> Result<(), MempoolError> {
        self.check_cluster_limits_with_vsize(transaction, transaction.vsize() as u64)
    }

    fn check_cluster_limits_with_vsize(
        &self,
        transaction: &Transaction,
        transaction_vsize: u64,
    ) -> Result<(), MempoolError> {
        let mut connected = HashSet::new();
        let mut pending = transaction
            .input
            .iter()
            .filter_map(|input| {
                self.entries
                    .contains_key(&input.previous_output.txid)
                    .then_some(input.previous_output.txid)
            })
            .collect::<Vec<_>>();
        while let Some(txid) = pending.pop() {
            if !connected.insert(txid) {
                continue;
            }
            if let Some(entry) = self.entries.get(&txid) {
                pending.extend(entry.transaction.input.iter().filter_map(|input| {
                    self.entries
                        .contains_key(&input.previous_output.txid)
                        .then_some(input.previous_output.txid)
                }));
            }
            pending.extend(self.children(&txid));
        }
        let connected_vsize = connected
            .iter()
            .filter_map(|txid| self.entries.get(txid))
            .map(|entry| entry.vsize)
            .fold(0u64, u64::saturating_add)
            .saturating_add(transaction_vsize);
        if connected.len().saturating_add(1) > self.policy.cluster_count_limit
            || connected_vsize > self.policy.cluster_vsize_limit
        {
            return Err(MempoolError::ClusterLimit);
        }
        Ok(())
    }

    /// Rebuild the pool against a new active chain, dropping transactions
    /// whose inputs, scripts, or locktimes are no longer valid. Parents are
    /// replayed before children so valid unconfirmed chains are retained.
    pub fn revalidate(&mut self, chain: &ChainState) {
        let entries: HashMap<Txid, (u64, Transaction)> = self
            .entries
            .values()
            .map(|entry| {
                (
                    entry.transaction.compute_txid(),
                    (entry.added_at, entry.transaction.clone()),
                )
            })
            .collect();
        let mut transaction_ids: Vec<Txid> = entries.keys().copied().collect();
        transaction_ids.sort_by_key(ToString::to_string);
        let mut ordered = Vec::with_capacity(entries.len());
        let mut visited = HashSet::new();
        let mut visiting = HashSet::new();

        fn visit(
            txid: Txid,
            entries: &HashMap<Txid, (u64, Transaction)>,
            visited: &mut HashSet<Txid>,
            visiting: &mut HashSet<Txid>,
            ordered: &mut Vec<(u64, Transaction)>,
        ) {
            if visited.contains(&txid) || !visiting.insert(txid) {
                return;
            }
            if let Some((_, transaction)) = entries.get(&txid) {
                let mut parents: Vec<Txid> = transaction
                    .input
                    .iter()
                    .map(|input| input.previous_output.txid)
                    .filter(|parent| entries.contains_key(parent))
                    .collect();
                parents.sort_by_key(ToString::to_string);
                for parent in parents {
                    visit(parent, entries, visited, visiting, ordered);
                }
            }
            if let Some((added_at, transaction)) = entries.get(&txid) {
                ordered.push((*added_at, transaction.clone()));
            }
            visiting.remove(&txid);
            visited.insert(txid);
        }

        for txid in transaction_ids {
            visit(txid, &entries, &mut visited, &mut visiting, &mut ordered);
        }
        self.entries.clear();
        self.adjusted_weights.clear();
        self.spent.clear();
        self.children.clear();
        self.wtxids.clear();
        self.invalidate_graph_optimality();
        let relay_sequences = std::mem::take(&mut self.relay_sequences);
        self.memory_usage = 0;
        self.bytes = 0;
        self.vbytes = 0;
        let unbroadcast = std::mem::take(&mut self.unbroadcast);
        for (added_at, transaction) in ordered {
            let txid = transaction.compute_txid();
            if self
                .accept_at_without_sequence(transaction.clone(), chain, added_at)
                .is_err()
            {
                self.record_removal(transaction, true);
            } else {
                if let Some(sequence) = relay_sequences.get(&txid) {
                    self.relay_sequences.insert(txid, *sequence);
                }
                if unbroadcast.contains(&txid) {
                    self.unbroadcast.insert(txid);
                }
            }
        }
    }

    pub fn remove(&mut self, txid: &Txid) -> Option<MempoolEntry> {
        self.remove_with_notification(txid, true)
    }

    fn remove_with_notification(&mut self, txid: &Txid, notify_zmq: bool) -> Option<MempoolEntry> {
        let entry = self.entries.remove(txid)?;
        self.adjusted_weights.remove(txid);
        self.unbroadcast.remove(txid);
        self.wtxids.remove(&entry.transaction.compute_wtxid());
        self.relay_sequences.remove(txid);
        let size = bitcoin::consensus::encode::serialize(&entry.transaction).len();
        self.memory_usage = self
            .memory_usage
            .saturating_sub(mempool_entry_memory_usage(&entry.transaction));
        self.bytes = self.bytes.saturating_sub(size);
        self.vbytes = self.vbytes.saturating_sub(entry.vsize);
        for input in &entry.transaction.input {
            self.spent.remove(&input.previous_output);
            if let Some(children) = self.children.get_mut(&input.previous_output.txid) {
                children.remove(txid);
                if children.is_empty() {
                    self.children.remove(&input.previous_output.txid);
                }
            }
        }
        self.children.remove(txid);
        self.record_removal(entry.transaction.clone(), notify_zmq);
        self.invalidate_graph_optimality();
        Some(entry)
    }

    pub fn remove_confirmed(&mut self, block: &bitcoin::Block) {
        for transaction in &block.txdata {
            let txid = transaction.compute_txid();
            self.remove_with_notification(&txid, false);
        }
        self.rolling_fee_last_updated = time::unix_time();
        self.block_since_last_rolling_fee_bump = true;
    }

    pub fn clear_expired(&mut self, now: u64, age: Duration) {
        let cutoff = now.saturating_sub(age.as_secs());
        let expired: Vec<Txid> = self
            .entries
            .iter()
            .filter_map(|(txid, entry)| (entry.added_at < cutoff).then_some(*txid))
            .collect();
        for txid in expired {
            self.remove(&txid);
        }
    }

    pub fn is_replaceable(&self, txid: &Txid) -> bool {
        fn signals_with_ancestors(
            mempool: &Mempool,
            txid: Txid,
            visiting: &mut HashSet<Txid>,
        ) -> bool {
            if !visiting.insert(txid) {
                return false;
            }
            let Some(entry) = mempool.entries.get(&txid) else {
                return false;
            };
            signals_replaceability(&entry.transaction)
                || entry.transaction.input.iter().any(|input| {
                    mempool.entries.contains_key(&input.previous_output.txid)
                        && signals_with_ancestors(mempool, input.previous_output.txid, visiting)
                })
        }

        signals_with_ancestors(self, *txid, &mut HashSet::new())
    }
}

/// Build a bounded certificate for the Core-style mempool graph optimality
/// status. The production graph is maintained lazily because recomputing all
/// clusters on every admission would put graph analysis on the hot path.
fn graph_optimality_certificate(mempool: &Mempool) -> bool {
    if mempool.entries.len() <= 1 {
        return true;
    }

    let mut parents = HashMap::<Txid, Vec<Txid>>::new();
    let mut children = HashMap::<Txid, Vec<Txid>>::new();
    for (txid, entry) in &mempool.entries {
        let mut tx_parents = Vec::new();
        for input in &entry.transaction.input {
            let parent = input.previous_output.txid;
            if parent != *txid
                && mempool.entries.contains_key(&parent)
                && !tx_parents.contains(&parent)
            {
                tx_parents.push(parent);
            }
        }
        if tx_parents.is_empty() {
            continue;
        }
        for parent in &tx_parents {
            children.entry(*parent).or_default().push(*txid);
        }
        parents.insert(*txid, tx_parents);
    }
    if parents.is_empty() {
        return true;
    }
    for txids in children.values_mut() {
        txids.sort_by_key(ToString::to_string);
        txids.dedup();
    }

    let mut visited = HashSet::with_capacity(mempool.entries.len());
    for start in mempool.entries.keys().copied() {
        if !visited.insert(start) {
            continue;
        }
        let component = graph_component(start, &parents, &children, &mut visited);
        if !component_graph_is_known_optimal(mempool, &component, &parents, &children) {
            return false;
        }
    }
    true
}

fn graph_component(
    start: Txid,
    parents: &HashMap<Txid, Vec<Txid>>,
    children: &HashMap<Txid, Vec<Txid>>,
    visited: &mut HashSet<Txid>,
) -> Vec<Txid> {
    let mut component = Vec::new();
    let mut pending = vec![start];
    while let Some(txid) = pending.pop() {
        component.push(txid);
        if let Some(txids) = parents.get(&txid) {
            for parent in txids {
                if visited.insert(*parent) {
                    pending.push(*parent);
                }
            }
        }
        if let Some(txids) = children.get(&txid) {
            for child in txids {
                if visited.insert(*child) {
                    pending.push(*child);
                }
            }
        }
    }
    component.sort_by_key(ToString::to_string);
    component
}

fn component_graph_is_known_optimal(
    mempool: &Mempool,
    component: &[Txid],
    parents: &HashMap<Txid, Vec<Txid>>,
    children: &HashMap<Txid, Vec<Txid>>,
) -> bool {
    if component.len() <= 1 {
        return true;
    }

    // Core's post-linearization is provably optimal for a graph that is a
    // tree in either direction. The existing package order has the same
    // ancestor-before-descendant property, so these common chain/fan-in/fan-
    // out clusters do not need factorial enumeration.
    let at_most_one_parent = component
        .iter()
        .all(|txid| parents.get(txid).map_or(0, Vec::len) <= 1);
    let at_most_one_child = component
        .iter()
        .all(|txid| children.get(txid).map_or(0, Vec::len) <= 1);
    if at_most_one_parent || at_most_one_child {
        return true;
    }

    if component.len() > MAX_GRAPH_OPTIMALITY_EXACT_TX_COUNT {
        return false;
    }

    exact_component_optimality(mempool, component, parents, children)
}

fn exact_component_optimality(
    mempool: &Mempool,
    component: &[Txid],
    parents: &HashMap<Txid, Vec<Txid>>,
    children: &HashMap<Txid, Vec<Txid>>,
) -> bool {
    let indegree = component
        .iter()
        .map(|txid| (*txid, parents.get(txid).map_or(0, Vec::len)))
        .collect::<HashMap<_, _>>();
    let mut search = ComponentOrderSearch {
        mempool,
        component,
        children,
        indegree,
        order: Vec::with_capacity(component.len()),
        best_diagram: None,
        incomparable: false,
        states: 0,
    };
    search.visit() && !search.incomparable
}

struct ComponentOrderSearch<'a> {
    mempool: &'a Mempool,
    component: &'a [Txid],
    children: &'a HashMap<Txid, Vec<Txid>>,
    indegree: HashMap<Txid, usize>,
    order: Vec<Txid>,
    best_diagram: Option<Vec<(i128, u64)>>,
    incomparable: bool,
    states: usize,
}

impl ComponentOrderSearch<'_> {
    fn visit(&mut self) -> bool {
        self.states = self.states.saturating_add(1);
        if self.states > MAX_GRAPH_OPTIMALITY_STATES {
            return false;
        }
        if self.order.len() == self.component.len() {
            let diagram = component_feerate_diagram(self.mempool, &self.order);
            if let Some(previous) = self.best_diagram.as_ref() {
                match compare_fee_rate_diagrams(&diagram, previous) {
                    Some(Ordering::Greater) => self.best_diagram = Some(diagram),
                    Some(Ordering::Equal | Ordering::Less) => {}
                    None => self.incomparable = true,
                }
            } else {
                self.best_diagram = Some(diagram);
            }
            return true;
        }

        let mut available = self
            .component
            .iter()
            .copied()
            .filter(|txid| !self.order.contains(txid) && self.indegree.get(txid) == Some(&0))
            .collect::<Vec<_>>();
        available.sort_by_key(ToString::to_string);
        if available.is_empty() {
            return false;
        }

        for txid in available {
            self.order.push(txid);
            if let Some(txids) = self.children.get(&txid) {
                for child in txids {
                    let degree = self
                        .indegree
                        .get_mut(child)
                        .expect("component child has an indegree entry");
                    *degree = degree.saturating_sub(1);
                }
            }
            let complete = self.visit();
            if let Some(txids) = self.children.get(&txid) {
                for child in txids {
                    let degree = self
                        .indegree
                        .get_mut(child)
                        .expect("component child has an indegree entry");
                    *degree = degree.saturating_add(1);
                }
            }
            self.order.pop();
            if !complete {
                return false;
            }
        }
        true
    }
}

fn component_feerate_diagram(mempool: &Mempool, order: &[Txid]) -> Vec<(i128, u64)> {
    let mut chunks = Vec::with_capacity(order.len());
    for txid in order {
        let Some(entry) = mempool.entries.get(txid) else {
            continue;
        };
        append_feerate_chunk(
            &mut chunks,
            mempool.modified_fee_sat(txid, entry.fee_sat),
            mempool.adjusted_weight(txid),
        );
    }
    chunks
}

fn fee_rate_meets(fee_sat: i128, vsize: u64, fee_rate_sat_per_kvb: u64) -> bool {
    fee_sat.saturating_mul(1_000) >= i128::from(fee_rate_sat_per_kvb) * i128::from(vsize)
}

fn fee_rate_from_package(fee_sat: i128, vsize: u64) -> u64 {
    if fee_sat <= 0 || vsize == 0 {
        return 0;
    }
    u64::try_from((fee_sat.saturating_mul(1_000) + i128::from(vsize) - 1) / i128::from(vsize))
        .unwrap_or(u64::MAX)
}

fn fee_for_rate(fee_rate_sat_per_kvb: u64, vsize: u64) -> i128 {
    (i128::from(fee_rate_sat_per_kvb) * i128::from(vsize) + 999) / 1_000
}

fn append_feerate_chunk(chunks: &mut Vec<(i128, u64)>, fee: i128, size: u64) {
    if size == 0 {
        return;
    }
    chunks.push((fee, size));
    while chunks.len() >= 2 {
        let right = chunks.len() - 1;
        let left = right - 1;
        let should_merge = compare_fee_rate(
            chunks[left].0,
            chunks[left].1,
            chunks[right].0,
            chunks[right].1,
        ) == Ordering::Less;
        if !should_merge {
            break;
        }
        let (right_fee, right_size) = chunks.pop().expect("right feerate chunk exists");
        let left = chunks.last_mut().expect("left feerate chunk exists");
        left.0 = left.0.saturating_add(right_fee);
        left.1 = left.1.saturating_add(right_size);
    }
}

fn compare_fee_rate(left_fee: i128, left_size: u64, right_fee: i128, right_size: u64) -> Ordering {
    if left_size == 0 || right_size == 0 {
        return left_size.cmp(&right_size);
    }
    left_fee
        .saturating_mul(i128::from(right_size))
        .cmp(&right_fee.saturating_mul(i128::from(left_size)))
}

/// Compare the convexified fee-rate diagrams represented by sorted chunks.
/// `Greater` means the left diagram is strictly better, `Less` means the
/// right diagram is strictly better, and `None` means the diagrams cross.
fn compare_fee_rate_diagrams(left: &[(i128, u64)], right: &[(i128, u64)]) -> Option<Ordering> {
    let diagrams = [left, right];
    let mut next = [0usize; 2];
    let mut accumulated_fee = [0i128; 2];
    let mut accumulated_size = [0u64; 2];
    let mut better = [false; 2];

    loop {
        let done = [next[0] == diagrams[0].len(), next[1] == diagrams[1].len()];
        if done[0] && done[1] {
            break;
        }

        let side = if done[0] {
            1
        } else if done[1] {
            0
        } else {
            let left_size = accumulated_size[0].saturating_add(diagrams[0][next[0]].1);
            let right_size = accumulated_size[1].saturating_add(diagrams[1][next[1]].1);
            usize::from(left_size > right_size)
        };
        let other = 1 - side;
        let point_fee = accumulated_fee[side].saturating_add(diagrams[side][next[side]].0);
        let point_size = accumulated_size[side].saturating_add(diagrams[side][next[side]].1);
        let previous_fee = accumulated_fee[other];
        let previous_size = accumulated_size[other];
        let slope_fee = point_fee.saturating_sub(previous_fee);
        let slope_size = point_size.saturating_sub(previous_size);

        let comparison = if done[other] {
            compare_fee_rate(slope_fee, slope_size, 0, 1)
        } else {
            let next_fee = accumulated_fee[other].saturating_add(diagrams[other][next[other]].0);
            let next_size = accumulated_size[other].saturating_add(diagrams[other][next[other]].1);
            if next_size == point_size {
                accumulated_fee[other] = next_fee;
                accumulated_size[other] = next_size;
                next[other] += 1;
            }
            compare_fee_rate(
                slope_fee,
                slope_size,
                next_fee.saturating_sub(previous_fee),
                next_size.saturating_sub(previous_size),
            )
        };

        if comparison == Ordering::Greater {
            better[side] = true;
        } else if comparison == Ordering::Less {
            better[other] = true;
        }
        if better[0] && better[1] {
            return None;
        }

        accumulated_fee[side] = point_fee;
        accumulated_size[side] = point_size;
        next[side] += 1;
    }

    if better[0] == better[1] {
        Some(Ordering::Equal)
    } else if better[0] {
        Some(Ordering::Greater)
    } else {
        Some(Ordering::Less)
    }
}

#[cfg(test)]
fn validate_standard_policy(
    transaction: &Transaction,
    previous_outputs: &[TxOut],
    fee_sat: u64,
) -> Result<(), MempoolError> {
    validate_standard_policy_with_modified_fee(
        transaction,
        previous_outputs,
        fee_sat,
        i64::try_from(fee_sat).unwrap_or(i64::MAX),
    )
}

#[cfg(test)]
fn validate_standard_policy_with_modified_fee(
    transaction: &Transaction,
    previous_outputs: &[TxOut],
    base_fee_sat: u64,
    modified_fee_sat: i64,
) -> Result<(), MempoolError> {
    validate_standard_policy_with_modified_fee_and_policy(
        transaction,
        previous_outputs,
        base_fee_sat,
        modified_fee_sat,
        &MempoolPolicy::default(),
    )
}

fn validate_standard_policy_with_modified_fee_and_policy(
    transaction: &Transaction,
    previous_outputs: &[TxOut],
    base_fee_sat: u64,
    modified_fee_sat: i64,
    policy: &MempoolPolicy,
) -> Result<(), MempoolError> {
    if !(1..=3).contains(&transaction.version.0) {
        return Err(MempoolError::NonStandard("version".to_owned()));
    }
    if transaction.weight().to_wu() > MAX_STANDARD_TX_WEIGHT {
        return Err(MempoolError::NonStandard("tx-size".to_owned()));
    }
    if transaction
        .input
        .iter()
        .any(|input| input.script_sig.len() > MAX_STANDARD_SCRIPTSIG_SIZE)
    {
        return Err(MempoolError::NonStandard("scriptsig-size".to_owned()));
    }
    if transaction
        .input
        .iter()
        .any(|input| !input.script_sig.is_push_only())
    {
        return Err(MempoolError::NonStandard(
            "scriptsig-not-pushonly".to_owned(),
        ));
    }

    let mut data_carrier_bytes = 0usize;
    let mut dust_outputs = 0usize;
    for output in &transaction.output {
        if is_core_nulldata(&output.script_pubkey) {
            data_carrier_bytes = data_carrier_bytes.saturating_add(output.script_pubkey.len());
            if policy
                .max_datacarrier_bytes
                .is_none_or(|max| data_carrier_bytes > max)
            {
                return Err(MempoolError::NonStandard("datacarrier".to_owned()));
            }
        } else if !is_standard_output_script(&output.script_pubkey, true) {
            return Err(MempoolError::NonStandard("scriptpubkey".to_owned()));
        } else if !policy.permit_bare_multisig && is_standard_bare_multisig(&output.script_pubkey) {
            return Err(MempoolError::NonStandard("bare-multisig".to_owned()));
        }
        if is_dust_output_with_fee(output, policy.dust_relay_fee_sat_per_kvb) {
            dust_outputs = dust_outputs.saturating_add(1);
        }
    }
    if dust_outputs > 1 || ((base_fee_sat != 0 || modified_fee_sat != 0) && dust_outputs != 0) {
        return Err(MempoolError::NonStandard("dust".to_owned()));
    }

    validate_standard_inputs(transaction, previous_outputs)?;
    let mut legacy_sigops = 0usize;
    for (input, previous) in transaction.input.iter().zip(previous_outputs) {
        legacy_sigops = legacy_sigops
            .saturating_add(input.script_sig.count_sigops())
            .saturating_add(if previous.script_pubkey.is_p2sh() {
                push_only_stack_top(&input.script_sig)
                    .map(|redeem| Script::from_bytes(&redeem).count_sigops())
                    .unwrap_or_default()
            } else {
                previous.script_pubkey.count_sigops()
            });
        if legacy_sigops > MAX_TX_LEGACY_SIGOPS {
            return Err(MempoolError::NonStandard(
                "bad-txns-nonstandard-inputs".to_owned(),
            ));
        }
    }
    let sigop_cost = validation::transaction_sigop_cost(
        transaction,
        previous_outputs,
        bitcoinconsensus::VERIFY_P2SH | bitcoinconsensus::VERIFY_WITNESS,
    );
    if sigop_cost > MAX_STANDARD_TX_SIGOPS_COST {
        return Err(MempoolError::NonStandard(
            "bad-txns-too-many-sigops".to_owned(),
        ));
    }
    validate_standard_witnesses(transaction, previous_outputs)?;
    validate_standard_simple_ecdsa_spends(transaction, previous_outputs)
}

fn is_minimal_push_encoding(script: &Script) -> bool {
    let bytes = script.as_bytes();
    let mut offset = 0usize;
    while offset < bytes.len() {
        let opcode = bytes[offset];
        offset += 1;
        let length = match opcode {
            0x00 => 0,
            0x4f | 0x51..=0x60 => continue,
            0x01..=0x4b => usize::from(opcode),
            0x4c => {
                let Some(&length) = bytes.get(offset) else {
                    return false;
                };
                offset += 1;
                usize::from(length)
            }
            0x4d => {
                let Some(length) = bytes.get(offset..offset.saturating_add(2)) else {
                    return false;
                };
                offset += 2;
                usize::from(u16::from_le_bytes([length[0], length[1]]))
            }
            0x4e => {
                let Some(length) = bytes.get(offset..offset.saturating_add(4)) else {
                    return false;
                };
                offset += 4;
                usize::try_from(u32::from_le_bytes([
                    length[0], length[1], length[2], length[3],
                ]))
                .ok()
                .unwrap_or(usize::MAX)
            }
            _ => return false,
        };
        let Some(end) = offset.checked_add(length) else {
            return false;
        };
        let Some(data) = bytes.get(offset..end) else {
            return false;
        };
        if length == 0 {
            if opcode != 0x00 {
                return false;
            }
        } else if (length == 1 && ((1..=16).contains(&data[0]) || data[0] == 0x81))
            || (opcode == 0x4c && length <= 75)
            || (opcode == 0x4d && length <= 255)
            || (opcode == 0x4e && length <= 65_535)
        {
            return false;
        }
        offset = end;
    }
    true
}

fn contains_tapscript_op_success(script: &[u8]) -> bool {
    let mut offset = 0usize;
    while offset < script.len() {
        let opcode = script[offset];
        offset += 1;
        if opcode == 0x50
            || opcode == 0x62
            || (0x7e..=0x81).contains(&opcode)
            || (0x83..=0x86).contains(&opcode)
            || (0x89..=0x8a).contains(&opcode)
            || (0x8d..=0x8e).contains(&opcode)
            || (0x95..=0x99).contains(&opcode)
            || (0xbb..=0xfe).contains(&opcode)
        {
            return true;
        }
        let length = match opcode {
            0x00 | 0x51..=0x60 | 0x61..=0xff => continue,
            0x01..=0x4b => usize::from(opcode),
            0x4c => {
                let Some(&length) = script.get(offset) else {
                    return false;
                };
                offset += 1;
                usize::from(length)
            }
            0x4d => {
                let Some(length) = script.get(offset..offset.saturating_add(2)) else {
                    return false;
                };
                offset += 2;
                usize::from(u16::from_le_bytes([length[0], length[1]]))
            }
            0x4e => {
                let Some(length) = script.get(offset..offset.saturating_add(4)) else {
                    return false;
                };
                offset += 4;
                usize::try_from(u32::from_le_bytes([
                    length[0], length[1], length[2], length[3],
                ]))
                .ok()
                .unwrap_or(usize::MAX)
            }
            _ => return false,
        };
        let Some(end) = offset.checked_add(length) else {
            return false;
        };
        if end > script.len() {
            return false;
        }
        offset = end;
    }
    false
}

fn validate_standard_inputs(
    transaction: &Transaction,
    previous_outputs: &[TxOut],
) -> Result<(), MempoolError> {
    if previous_outputs.len() != transaction.input.len() {
        return Err(MempoolError::NonStandard(
            "bad-txns-nonstandard-inputs".to_owned(),
        ));
    }
    for (input, previous) in transaction.input.iter().zip(previous_outputs) {
        if !is_minimal_push_encoding(&input.script_sig) {
            return Err(MempoolError::NonStandard(
                "bad-txns-nonstandard-inputs".to_owned(),
            ));
        }
        let redeem_script = if previous.script_pubkey.is_p2sh() {
            let Some(redeem_script) = push_only_stack_top(&input.script_sig) else {
                return Err(MempoolError::NonStandard(
                    "bad-txns-nonstandard-inputs".to_owned(),
                ));
            };
            let redeem_script = ScriptBuf::from_bytes(redeem_script);
            let redeem_script_view = redeem_script.as_script();
            if redeem_script_view.count_sigops() > 15 {
                return Err(MempoolError::NonStandard(
                    "bad-txns-nonstandard-inputs".to_owned(),
                ));
            }
            if contains_opcode(redeem_script_view, 0xab) {
                return Err(standard_script_policy_failure(
                    "Using OP_CODESEPARATOR in non-witness script",
                ));
            }
            if contains_unconditional_upgradable_nop(redeem_script_view) {
                return Err(standard_script_policy_failure(
                    "NOPx reserved for soft-fork upgrades",
                ));
            }
            if !contains_conditional_opcode(redeem_script_view)
                && contains_nonminimal_script_push(redeem_script_view)
            {
                return Err(standard_script_policy_failure(
                    "Data push larger than necessary",
                ));
            }
            Some(redeem_script)
        } else {
            None
        };
        let spending_script = redeem_script.as_deref().unwrap_or(&previous.script_pubkey);
        if spending_script.is_witness_program()
            && !(spending_script.is_p2wpkh()
                || spending_script.is_p2wsh()
                || spending_script.is_p2tr()
                || is_p2a_script(spending_script))
        {
            return Err(MempoolError::NonStandard(
                "bad-txns-nonstandard-inputs".to_owned(),
            ));
        }
        if !is_standard_spend_script(&previous.script_pubkey) {
            return Err(MempoolError::NonStandard(
                "bad-txns-nonstandard-inputs".to_owned(),
            ));
        }
    }
    Ok(())
}

fn validate_standard_witnesses(
    transaction: &Transaction,
    previous_outputs: &[TxOut],
) -> Result<(), MempoolError> {
    for (input, previous) in transaction.input.iter().zip(previous_outputs) {
        if input.witness.is_empty() {
            continue;
        }
        let redeem_script = if previous.script_pubkey.is_p2sh() {
            let Some(redeem_script) = push_only_stack_top(&input.script_sig) else {
                return Err(MempoolError::NonStandard(
                    "bad-witness-nonstandard".to_owned(),
                ));
            };
            Some(ScriptBuf::from_bytes(redeem_script))
        } else {
            None
        };
        let spending_script = redeem_script.as_deref().unwrap_or(&previous.script_pubkey);
        if !spending_script.is_witness_program() {
            return Err(MempoolError::NonStandard(
                "bad-witness-nonstandard".to_owned(),
            ));
        }
        if is_p2a_script(spending_script) && !previous.script_pubkey.is_p2sh() {
            return Err(MempoolError::NonStandard(
                "bad-witness-nonstandard".to_owned(),
            ));
        } else if spending_script.is_p2wpkh() {
            let Some(pubkey) = input.witness.iter().nth(1) else {
                return Err(MempoolError::NonStandard(
                    "bad-witness-nonstandard".to_owned(),
                ));
            };
            if input.witness.len() != 2
                || pubkey.len() != 33
                || !matches!(pubkey.first(), Some(0x02) | Some(0x03))
            {
                return Err(MempoolError::NonStandard(
                    "bad-witness-nonstandard".to_owned(),
                ));
            }
        } else if spending_script.is_p2wsh() {
            let Some(witness_script) = input.witness.last() else {
                return Err(MempoolError::NonStandard(
                    "bad-witness-nonstandard".to_owned(),
                ));
            };
            if witness_script.len() > 3_600 {
                return Err(MempoolError::NonStandard(
                    "bad-witness-nonstandard".to_owned(),
                ));
            }
            let stack_len = input.witness.len().saturating_sub(1);
            if stack_len > 100
                || input
                    .witness
                    .iter()
                    .take(stack_len)
                    .any(|item| item.len() > 80)
            {
                return Err(MempoolError::NonStandard(
                    "bad-witness-nonstandard".to_owned(),
                ));
            }
            if witness_v0_script_starts_with_nonminimal_if(
                witness_script,
                input.witness.iter().take(stack_len).last(),
            ) {
                return Err(standard_script_policy_failure(
                    "OP_IF/NOTIF argument must be minimal",
                ));
            }
        } else if spending_script.is_p2tr() && !previous.script_pubkey.is_p2sh() {
            let witness_items = input.witness.iter().collect::<Vec<_>>();
            if witness_items
                .last()
                .is_some_and(|item| item.first() == Some(&0x50))
            {
                return Err(MempoolError::NonStandard(
                    "bad-witness-nonstandard".to_owned(),
                ));
            }
            if witness_items.len() >= 2 {
                let control_block = witness_items[witness_items.len() - 1];
                if control_block.is_empty() {
                    return Err(MempoolError::NonStandard(
                        "bad-witness-nonstandard".to_owned(),
                    ));
                }
                let leaf_version = control_block[0] & 0xfe;
                if leaf_version != 0xc0 {
                    return Err(MempoolError::NonStandard(
                        "bad-witness-nonstandard".to_owned(),
                    ));
                }
                if contains_tapscript_op_success(witness_items[witness_items.len() - 2]) {
                    return Err(MempoolError::NonStandard(
                        "bad-witness-nonstandard".to_owned(),
                    ));
                }
                if witness_items[..witness_items.len() - 2]
                    .iter()
                    .any(|item| item.len() > 80)
                {
                    return Err(MempoolError::NonStandard(
                        "bad-witness-nonstandard".to_owned(),
                    ));
                }
            } else if witness_items.is_empty() {
                return Err(MempoolError::NonStandard(
                    "bad-witness-nonstandard".to_owned(),
                ));
            }
        }
    }
    Ok(())
}

fn standard_script_policy_failure(reason: &'static str) -> MempoolError {
    MempoolError::NonStandard(format!("mempool-script-verify-flag-failed ({reason})"))
}

/// Validate the non-consensus signature policy rules for the simple standard
/// templates whose executed CHECKSIG arguments are directly visible in the
/// input. More general P2WSH and multisig scripts need an execution-aware
/// policy interpreter because their signature arguments can be produced or
/// consumed by arbitrary script operations.
fn validate_standard_simple_ecdsa_spends(
    transaction: &Transaction,
    previous_outputs: &[TxOut],
) -> Result<(), MempoolError> {
    for (input, previous) in transaction.input.iter().zip(previous_outputs) {
        if previous.script_pubkey.is_p2sh() {
            let Some(mut stack) = push_only_stack_items(&input.script_sig) else {
                continue;
            };
            let Some(redeem_script) = stack.pop() else {
                continue;
            };
            let redeem_script = Script::from_bytes(&redeem_script);

            if redeem_script.is_p2pkh() {
                if stack.len() != 2 {
                    return Err(standard_script_policy_failure(
                        "Stack size must be exactly one after execution",
                    ));
                }
                validate_standard_ecdsa_pair(&stack[0], &stack[1], false)?;
            } else if redeem_script.is_p2wpkh() {
                validate_standard_wpkh_witness(input)?;
            } else if let Some(pubkey) = p2pk_pubkey_bytes(redeem_script) {
                if stack.len() != 1 {
                    return Err(standard_script_policy_failure(
                        "Stack size must be exactly one after execution",
                    ));
                }
                validate_standard_ecdsa_pair(&stack[0], &pubkey, false)?;
            }
            continue;
        }

        if previous.script_pubkey.is_p2pkh() {
            let Some(stack) = push_only_stack_items(&input.script_sig) else {
                continue;
            };
            if stack.len() != 2 {
                return Err(standard_script_policy_failure(
                    "Stack size must be exactly one after execution",
                ));
            }
            validate_standard_ecdsa_pair(&stack[0], &stack[1], false)?;
        } else if previous.script_pubkey.is_p2wpkh() {
            validate_standard_wpkh_witness(input)?;
        } else if let Some(pubkey) = p2pk_pubkey_bytes(&previous.script_pubkey) {
            let Some(stack) = push_only_stack_items(&input.script_sig) else {
                continue;
            };
            if stack.len() != 1 {
                return Err(standard_script_policy_failure(
                    "Stack size must be exactly one after execution",
                ));
            }
            validate_standard_ecdsa_pair(&stack[0], &pubkey, false)?;
        }
    }
    Ok(())
}

fn validate_standard_wpkh_witness(input: &TxIn) -> Result<(), MempoolError> {
    let witness = input.witness.iter().collect::<Vec<_>>();
    if witness.len() == 2 {
        validate_standard_ecdsa_pair(witness[0], witness[1], true)?;
    }
    Ok(())
}

fn validate_standard_ecdsa_pair(
    signature: &[u8],
    pubkey: &[u8],
    witness_v0: bool,
) -> Result<(), MempoolError> {
    validate_standard_ecdsa_signature(signature).map_err(standard_script_policy_failure)?;

    if witness_v0 && !(pubkey.len() == 33 && matches!(pubkey[0], 0x02 | 0x03)) {
        return Err(standard_script_policy_failure(
            "Public key is not compressed",
        ));
    }
    if !is_strict_pubkey_encoding(pubkey) {
        return Err(standard_script_policy_failure(
            "Public key is neither compressed or uncompressed",
        ));
    }
    Ok(())
}

fn validate_standard_ecdsa_signature(signature: &[u8]) -> Result<(), &'static str> {
    // Core permits an empty signature as the intentional false value used by
    // CHECK(MULTI)SIG. The surrounding standard templates still have to pass
    // consensus validation, but the encoding policy itself accepts it.
    if signature.is_empty() {
        return Ok(());
    }
    if !is_valid_der_signature(signature) {
        return Err("Non-canonical DER signature");
    }

    let der = &signature[..signature.len() - 1];
    let mut parsed = bitcoin::secp256k1::ecdsa::Signature::from_der(der)
        .map_err(|_| "Non-canonical DER signature")?;
    let original = parsed;
    parsed.normalize_s();
    if parsed != original {
        return Err("Non-canonical signature: S value is unnecessarily high");
    }

    let hash_type = signature[signature.len() - 1] & 0x7f;
    if !(1..=3).contains(&hash_type) {
        return Err("Signature hash type missing or not understood");
    }
    Ok(())
}

/// Bitcoin Core's IsValidSignatureEncoding, including the final sighash byte.
fn is_valid_der_signature(signature: &[u8]) -> bool {
    if !(9..=73).contains(&signature.len())
        || signature[0] != 0x30
        || usize::from(signature[1]) != signature.len() - 3
    {
        return false;
    }

    let len_r = usize::from(signature[3]);
    if 5 + len_r >= signature.len() {
        return false;
    }
    let len_s = usize::from(signature[5 + len_r]);
    if len_r + len_s + 7 != signature.len()
        || signature[2] != 0x02
        || len_r == 0
        || signature[4] & 0x80 != 0
        || (len_r > 1 && signature[4] == 0x00 && signature[5] & 0x80 == 0)
    {
        return false;
    }

    let s_tag = len_r + 4;
    let s_start = s_tag + 2;
    len_s != 0
        && signature[s_tag] == 0x02
        && signature[s_start] & 0x80 == 0
        && !(len_s > 1 && signature[s_start + 1] == 0x00 && signature[s_start + 2] & 0x80 == 0)
}

fn is_strict_pubkey_encoding(pubkey: &[u8]) -> bool {
    (pubkey.len() == 33 && matches!(pubkey.first(), Some(0x02 | 0x03)))
        || (pubkey.len() == 65 && pubkey.first() == Some(&0x04))
}

fn p2pk_pubkey_bytes(script: &Script) -> Option<Vec<u8>> {
    let mut instructions = script.instructions();
    let pubkey = match instructions.next()? {
        Ok(Instruction::PushBytes(bytes)) => bytes.as_bytes().to_vec(),
        _ => return None,
    };
    match instructions.next()? {
        Ok(Instruction::Op(op)) if op.to_u8() == 0xac && instructions.next().is_none() => {
            Some(pubkey)
        }
        _ => None,
    }
}

fn is_standard_output_script(script: &Script, permit_bare_multisig: bool) -> bool {
    script.is_p2pkh()
        || script.is_p2sh()
        || script.p2pk_public_key().is_some()
        || script.is_p2wpkh()
        || script.is_p2wsh()
        || script.is_p2tr()
        || is_p2a_script(script)
        || (permit_bare_multisig && is_standard_bare_multisig(script))
}

fn is_p2a_script(script: &Script) -> bool {
    script.as_bytes() == [0x51, 0x02, 0x4e, 0x73]
}

fn is_core_nulldata(script: &Script) -> bool {
    script.as_bytes().first() == Some(&0x6a)
        && Script::from_bytes(&script.as_bytes()[1..]).is_push_only()
}

fn contains_opcode(script: &Script, opcode: u8) -> bool {
    script
        .instructions()
        .any(|instruction| matches!(instruction, Ok(Instruction::Op(op)) if op.to_u8() == opcode))
}

fn contains_unconditional_upgradable_nop(script: &Script) -> bool {
    let mut has_conditional = false;
    let mut has_upgradable_nop = false;
    for instruction in script.instructions() {
        let Ok(Instruction::Op(op)) = instruction else {
            continue;
        };
        if matches!(op.to_u8(), 0x63..=0x68) {
            has_conditional = true;
        }
        if op.to_u8() == 0xb0 || (0xb3..=0xb9).contains(&op.to_u8()) {
            has_upgradable_nop = true;
        }
    }
    has_upgradable_nop && !has_conditional
}

fn contains_conditional_opcode(script: &Script) -> bool {
    script.instructions().any(|instruction| {
        matches!(instruction, Ok(Instruction::Op(op)) if (0x63..=0x68).contains(&op.to_u8()))
    })
}

fn contains_nonminimal_script_push(script: &Script) -> bool {
    let bytes = script.as_bytes();
    let mut offset = 0usize;
    while offset < bytes.len() {
        let opcode = bytes[offset];
        offset += 1;
        let length = match opcode {
            0x00 | 0x4f | 0x50 | 0x51..=0x60 | 0x61..=0xff => continue,
            0x01..=0x4b => usize::from(opcode),
            0x4c => {
                let Some(&length) = bytes.get(offset) else {
                    return false;
                };
                offset += 1;
                usize::from(length)
            }
            0x4d => {
                let Some(length) = bytes.get(offset..offset.saturating_add(2)) else {
                    return false;
                };
                offset += 2;
                usize::from(u16::from_le_bytes([length[0], length[1]]))
            }
            0x4e => {
                let Some(length) = bytes.get(offset..offset.saturating_add(4)) else {
                    return false;
                };
                offset += 4;
                usize::try_from(u32::from_le_bytes([
                    length[0], length[1], length[2], length[3],
                ]))
                .ok()
                .unwrap_or(usize::MAX)
            }
        };
        let Some(end) = offset.checked_add(length) else {
            return false;
        };
        let Some(data) = bytes.get(offset..end) else {
            return false;
        };
        if (length == 1 && ((1..=16).contains(&data[0]) || data[0] == 0x81))
            || (opcode == 0x4c && length <= 75)
            || (opcode == 0x4d && length <= 255)
            || (opcode == 0x4e && length <= 65_535)
        {
            return true;
        }
        offset = end;
    }
    false
}

fn witness_v0_script_starts_with_nonminimal_if(
    witness_script: &[u8],
    top_stack_item: Option<&[u8]>,
) -> bool {
    let Some(Ok(Instruction::Op(op))) = Script::from_bytes(witness_script).instructions().next()
    else {
        return false;
    };
    if !matches!(op.to_u8(), 0x63 | 0x64) {
        return false;
    }
    let Some(item) = top_stack_item else {
        return false;
    };
    item.len() > 1 || (item.len() == 1 && item[0] != 1)
}

fn push_only_stack_items(script: &Script) -> Option<Vec<Vec<u8>>> {
    let mut stack = Vec::new();
    for instruction in script.instructions() {
        match instruction {
            Ok(Instruction::PushBytes(bytes)) => stack.push(bytes.as_bytes().to_vec()),
            Ok(Instruction::Op(op)) => {
                let value = match op.to_u8() {
                    0x00 => Vec::new(),
                    0x4f => vec![0x81],
                    0x51..=0x60 => vec![op.to_u8() - 0x50],
                    _ => return None,
                };
                stack.push(value);
            }
            Err(_) => return None,
        }
    }
    Some(stack)
}

fn push_only_stack_top(script: &Script) -> Option<Vec<u8>> {
    push_only_stack_items(script)?.pop()
}

fn is_standard_spend_script(script: &Script) -> bool {
    is_standard_output_script(script, true)
        && !(script.is_witness_program()
            && !(script.is_p2wpkh()
                || script.is_p2wsh()
                || script.is_p2tr()
                || is_p2a_script(script)))
}

fn is_standard_bare_multisig(script: &Script) -> bool {
    if !script.is_multisig() {
        return false;
    }
    let Some(Ok(Instruction::Op(required))) = script.instructions().next() else {
        return false;
    };
    if required.to_u8() == 0x00 {
        return false;
    }
    let keys = script
        .instructions()
        .filter_map(|instruction| match instruction {
            Ok(Instruction::PushBytes(bytes)) => Some(bytes.as_bytes()),
            _ => None,
        })
        .collect::<Vec<_>>();
    !keys.is_empty() && keys.len() <= 3 && keys.iter().all(|key| PublicKey::from_slice(key).is_ok())
}

#[cfg(test)]
fn is_dust_output(output: &TxOut) -> bool {
    is_dust_output_with_fee(output, DEFAULT_DUST_RELAY_FEE_SAT_PER_KVB)
}

fn is_dust_output_with_fee(output: &TxOut, dust_relay_fee_sat_per_kvb: u64) -> bool {
    if output.script_pubkey.is_op_return() || output.script_pubkey.len() > MAX_SCRIPT_SIZE {
        return false;
    }
    let output_size = bitcoin::consensus::encode::serialize(output).len() as u64;
    let input_size = if output.script_pubkey.is_witness_program() {
        67
    } else {
        148
    };
    let threshold = output_size
        .saturating_add(input_size)
        .saturating_mul(dust_relay_fee_sat_per_kvb)
        .saturating_add(999)
        / 1_000;
    output.value.to_sat() < threshold
}

fn validate_ephemeral_spends(
    transactions: &[Transaction],
    mempool: &Mempool,
) -> Result<(), MempoolError> {
    let package_transactions = transactions
        .iter()
        .map(|transaction| (transaction.compute_txid(), transaction))
        .collect::<HashMap<_, _>>();
    for transaction in transactions {
        let mut processed_parents = HashSet::new();
        let mut unspent_dust = HashSet::new();
        for input in &transaction.input {
            if !processed_parents.insert(input.previous_output.txid) {
                continue;
            }
            let parent = package_transactions
                .get(&input.previous_output.txid)
                .copied()
                .or_else(|| {
                    mempool
                        .get(&input.previous_output.txid)
                        .map(|entry| &entry.transaction)
                });
            if let Some(parent) = parent {
                for (vout, output) in parent.output.iter().enumerate() {
                    if is_dust_output_with_fee(output, mempool.policy.dust_relay_fee_sat_per_kvb) {
                        unspent_dust.insert(OutPoint::new(input.previous_output.txid, vout as u32));
                    }
                }
            }
        }
        for input in &transaction.input {
            unspent_dust.remove(&input.previous_output);
        }
        if !unspent_dust.is_empty() {
            return Err(MempoolError::NonStandard(
                "missing-ephemeral-spends".to_owned(),
            ));
        }
    }
    Ok(())
}

fn collect_mining_package(
    mempool: &Mempool,
    txid: Txid,
    selected: &HashSet<Txid>,
    package: &mut HashSet<Txid>,
    visiting: &mut HashSet<Txid>,
) -> bool {
    if selected.contains(&txid) {
        return true;
    }
    if package.contains(&txid) {
        return true;
    }
    if mempool.get(&txid).is_none() || !visiting.insert(txid) {
        return false;
    }
    for parent in mempool.parents(&txid) {
        if !collect_mining_package(mempool, parent, selected, package, visiting) {
            visiting.remove(&txid);
            return false;
        }
    }
    visiting.remove(&txid);
    package.insert(txid);
    true
}

fn next_mining_candidate(
    candidates: &mut BinaryHeap<MiningCandidate>,
    metrics: &HashMap<Txid, MiningPackageMetrics>,
    selected: &HashSet<Txid>,
    selected_weight: u64,
    weight_limit: u64,
    min_fee_sat_per_kvb: u64,
) -> Option<MiningCandidate> {
    while let Some(candidate) = candidates.pop() {
        if selected.contains(&candidate.txid) {
            continue;
        }
        let Some(current) = metrics.get(&candidate.txid) else {
            continue;
        };
        if current.version != candidate.version
            || current.fee != candidate.fee
            || current.weight != candidate.weight
        {
            continue;
        }
        if selected_weight.saturating_add(candidate.weight) > weight_limit {
            // A package that does not fit cannot become smaller unless one of
            // its ancestors is selected; that selection pushes a fresh heap
            // entry through the descendant update path.
            continue;
        }
        if min_fee_sat_per_kvb != 0 {
            let package_vsize = candidate.weight.saturating_add(3) / 4;
            if candidate.fee.saturating_mul(1_000)
                < i128::from(min_fee_sat_per_kvb) * i128::from(package_vsize)
            {
                continue;
            }
        }
        return Some(candidate);
    }
    None
}

fn append_mining_package(
    mempool: &Mempool,
    txid: Txid,
    package: &HashSet<Txid>,
    selected: &mut HashSet<Txid>,
    ordered: &mut Vec<Txid>,
) {
    if selected.contains(&txid) || !package.contains(&txid) {
        return;
    }
    for parent in mempool.parents(&txid) {
        append_mining_package(mempool, parent, package, selected, ordered);
    }
    if selected.insert(txid) {
        ordered.push(txid);
    }
}

fn signals_replaceability(transaction: &Transaction) -> bool {
    transaction
        .input
        .iter()
        .any(|input| input.sequence.to_consensus_u32() < 0xffff_fffe)
}

pub fn package_is_topologically_sorted(transactions: &[Transaction]) -> bool {
    let positions = transactions
        .iter()
        .enumerate()
        .map(|(index, transaction)| (transaction.compute_txid(), index))
        .collect::<HashMap<_, _>>();
    transactions.iter().enumerate().all(|(index, transaction)| {
        transaction.input.iter().all(|input| {
            positions
                .get(&input.previous_output.txid)
                .is_none_or(|parent_index| *parent_index < index)
        })
    })
}

pub fn package_is_child_with_parents_tree(transactions: &[Transaction]) -> bool {
    if transactions.len() < 2 || !package_is_topologically_sorted(transactions) {
        return false;
    }
    let child = transactions.last().expect("package length checked");
    let parent_txids = transactions[..transactions.len() - 1]
        .iter()
        .map(Transaction::compute_txid)
        .collect::<HashSet<_>>();
    if parent_txids.len() != transactions.len() - 1 {
        return false;
    }
    transactions[..transactions.len() - 1].iter().all(|parent| {
        parent
            .input
            .iter()
            .all(|input| !parent_txids.contains(&input.previous_output.txid))
    }) && transactions[..transactions.len() - 1].iter().all(|parent| {
        child
            .input
            .iter()
            .any(|input| input.previous_output.txid == parent.compute_txid())
    })
}

pub fn package_weight(transactions: &[Transaction]) -> u64 {
    transactions
        .iter()
        .map(|transaction| transaction.weight().to_wu())
        .sum()
}

impl From<ValidationError> for MempoolError {
    fn from(error: ValidationError) -> Self {
        MempoolError::Script(error.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::Network;
    use bitcoin::absolute::LockTime;
    use bitcoin::block::{Header, Version as BlockVersion};
    use bitcoin::blockdata::script::Builder;
    use bitcoin::blockdata::script::ScriptBuf;
    use bitcoin::blockdata::transaction::{OutPoint, TxIn, TxOut, Version};
    use bitcoin::blockdata::witness::Witness;
    use bitcoin::hashes::Hash;

    fn graph_transaction(previous: Txid, marker: u8) -> Transaction {
        Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(previous, 0),
                script_sig: ScriptBuf::from_bytes(vec![marker]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(1),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        }
    }

    #[test]
    fn consistency_check_validates_empty_pool_and_accounting() {
        let mut pool = Mempool::new(Network::Regtest);
        pool.check_consistency().unwrap();

        pool.bytes = 1;
        assert!(pool.check_consistency().is_err());
    }

    #[test]
    fn consistency_check_accepts_an_admitted_transaction() {
        let directory = tempfile::tempdir().unwrap();
        let mut chain = ChainState::open(Network::Regtest, directory.path()).unwrap();
        for height in 1..=101 {
            let previous = *chain.header(height - 1).expect("previous header");
            chain
                .connect_block(mine_regtest_block(&previous, height))
                .unwrap();
        }
        let (outpoint, utxo) = chain
            .all_utxos()
            .find(|(_, entry)| chain.height() + 1 >= entry.height + 100)
            .map(|(outpoint, entry)| (*outpoint, entry.clone()))
            .expect("matured coinbase output");
        let transaction = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: outpoint,
                script_sig: ScriptBuf::from_bytes(vec![0; 65]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(utxo.output.value.to_sat() - 1_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let mut pool = Mempool::new(Network::Regtest);
        pool.accept(transaction, &chain).unwrap();
        pool.check_consistency().unwrap();
    }

    fn mine_regtest_block(previous: &Header, height: u32) -> bitcoin::Block {
        let transaction = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::null(),
                script_sig: Builder::new()
                    .push_int(height as i64)
                    .push_int(0)
                    .into_script(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(crate::validation::block_subsidy_for_network(
                    Network::Regtest,
                    height,
                )),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let mut block = bitcoin::Block {
            header: Header {
                version: BlockVersion::from_consensus(4),
                prev_blockhash: previous.block_hash(),
                merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                time: previous.time + 1,
                bits: previous.bits,
                nonce: 0,
            },
            txdata: vec![transaction],
        };
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        while !block.header.target().is_met_by(block.block_hash()) {
            block.header.nonce = block.header.nonce.wrapping_add(1);
        }
        block
    }

    #[test]
    fn persists_and_loads_an_empty_pool() {
        let directory = tempfile::tempdir().unwrap();
        let chain = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let path = directory.path().join("mempool.dat");
        let pool = Mempool::new(Network::Regtest);
        pool.save_to_file(&path).unwrap();
        let bytes = fs::read(&path).unwrap();
        assert_eq!(u64::from_le_bytes(bytes[..8].try_into().unwrap()), 2);
        let mut loaded = Mempool::new(Network::Regtest);
        loaded.load_from_file(&path, &chain).unwrap();
        assert!(loaded.is_empty());
    }

    #[test]
    fn persists_core_v1_without_obfuscation() {
        let directory = tempfile::tempdir().unwrap();
        let chain = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let path = directory.path().join("mempool-v1.dat");
        Mempool::new(Network::Regtest)
            .save_to_file_with_format(&path, true)
            .unwrap();

        let bytes = fs::read(&path).unwrap();
        assert_eq!(u64::from_le_bytes(bytes[..8].try_into().unwrap()), 1);
        assert_eq!(u64::from_le_bytes(bytes[8..16].try_into().unwrap()), 0);
        let mut loaded = Mempool::new(Network::Regtest);
        loaded.load_from_file(&path, &chain).unwrap();
        assert!(loaded.is_empty());
    }

    #[test]
    fn round_trips_core_v2_entries_and_fee_deltas() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("mempool.dat");
        let transaction = graph_transaction(Txid::from_byte_array([7; 32]), 7);
        let txid = transaction.compute_txid();
        let mut pool = Mempool::new(Network::Regtest);
        let inserted = insert_policy_entry(&mut pool, transaction.clone());
        assert_eq!(inserted, txid);
        pool.prioritise(txid, 123);
        pool.add_unbroadcast(txid);

        pool.save_to_file(&path).unwrap();
        let bytes = fs::read(path).unwrap();
        let (entries, deltas, unbroadcast) = decode_core_mempool(&bytes).unwrap();
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].transaction, transaction);
        assert_eq!(entries[0].fee_delta, 123);
        assert!(deltas.is_empty());
        assert_eq!(unbroadcast, vec![txid]);
    }

    #[test]
    fn restores_entry_fee_delta_before_policy_admission() {
        let directory = tempfile::tempdir().unwrap();
        let mut chain = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let mut previous = *chain.header(0).unwrap();
        let mut funding_txid = None;
        for height in 1..=101 {
            let block = mine_regtest_block(&previous, height);
            if height == 1 {
                funding_txid = Some(block.txdata[0].compute_txid());
            }
            previous = block.header;
            chain.connect_block(block).unwrap();
        }
        let funding_txid = funding_txid.expect("funding block was mined");

        let transaction = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(funding_txid, 0),
                script_sig: ScriptBuf::from_bytes(vec![0x61; 10]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(4_999_999_999),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let txid = transaction.compute_txid();
        let path = directory.path().join("mempool.dat");
        let mut source = Mempool::new(Network::Regtest);
        insert_policy_entry(&mut source, transaction.clone());
        source.prioritise(txid, 10_000_000);
        source.save_to_file(&path).unwrap();

        let policy = MempoolPolicy {
            min_relay_fee_sat_per_kvb: 100_000,
            require_standard: false,
            ..MempoolPolicy::default()
        };
        let mut probe = Mempool::with_max_bytes_and_policy(Network::Regtest, 300_000_000, policy);
        probe.prioritise(txid, 10_000_000);
        let probe_result = probe.accept_at(transaction.clone(), &chain, 1);
        assert!(
            probe_result.is_ok(),
            "probe admission failed: {probe_result:?}"
        );
        let mut loaded = Mempool::with_max_bytes_and_policy(Network::Regtest, 300_000_000, policy);
        loaded
            .load_from_file_with_expiry(&path, &chain, Duration::from_secs(u64::MAX))
            .unwrap();

        assert!(loaded.get(&txid).is_some());
        assert_eq!(loaded.fee_delta(&txid), 10_000_000);
    }

    #[test]
    fn mempool_enforces_bip68_before_csv_activation() {
        let directory = tempfile::tempdir().unwrap();
        let mut deployment_parameters =
            validation::DeploymentParameters::for_network(Network::Regtest);
        deployment_parameters.buried.csv = 10_000;
        let blocks_dir = directory.path().join("blocks");
        let mut chain = ChainState::open_with_options_and_tx_index_in_dirs_with_minimum_chain_work_and_assume_valid_and_blocks_xor_and_deployment_parameters(
            Network::Regtest,
            directory.path(),
            &blocks_dir,
            None,
            false,
            false,
            false,
            false,
            None,
            None,
            false,
            deployment_parameters,
        )
        .unwrap();
        let mut previous = *chain.header(0).unwrap();
        let mut funding_txid = None;
        for height in 1..=101 {
            let block = mine_regtest_block(&previous, height);
            if height == 1 {
                funding_txid = Some(block.txdata[0].compute_txid());
            }
            previous = block.header;
            chain.connect_block(block).unwrap();
        }

        let previous_output = OutPoint::new(funding_txid.unwrap(), 0);
        let value = chain.utxo(&previous_output).unwrap().output.value.to_sat();
        let transaction = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output,
                script_sig: ScriptBuf::from_bytes(vec![0; 65]),
                sequence: bitcoin::Sequence::from_consensus(500),
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(value - 1_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };

        let result = Mempool::new(Network::Regtest).accept(transaction, &chain);
        assert!(
            matches!(result, Err(MempoolError::Script(message)) if message.contains("locktime"))
        );
    }

    #[test]
    fn decodes_core_v1_fee_delta_records_without_obfuscation() {
        let txid = Txid::from_byte_array([8; 32]);
        let mut payload = Vec::new();
        append_u64(&mut payload, 0);
        payload.extend_from_slice(&serialize(&VarInt(1)));
        payload.extend_from_slice(&serialize(&txid));
        append_i64(&mut payload, -42);
        payload.extend_from_slice(&serialize(&VarInt(0)));

        let mut bytes = Vec::new();
        append_u64(&mut bytes, CORE_MEMPOOL_DUMP_VERSION_V1);
        bytes.extend_from_slice(&payload);
        let (entries, deltas, unbroadcast) = decode_core_mempool(&bytes).unwrap();
        assert!(entries.is_empty());
        assert_eq!(deltas, vec![(txid, -42)]);
        assert!(unbroadcast.is_empty());
    }

    #[test]
    fn configurable_mempool_size_uses_the_requested_byte_limit() {
        let pool = Mempool::with_max_bytes(Network::Regtest, 12_345);
        assert_eq!(pool.max_bytes(), 12_345);
        let nonzero = Mempool::with_max_bytes(Network::Regtest, 0);
        assert_eq!(nonzero.max_bytes(), 1);
    }

    #[test]
    fn relay_lookup_obeys_mempool_sequence_boundary() {
        let transaction = graph_transaction(Txid::from_byte_array([9; 32]), 9);
        let txid = transaction.compute_txid();
        let wtxid = transaction.compute_wtxid();
        let mut pool = Mempool::new(Network::Regtest);
        pool.entries.insert(
            txid,
            MempoolEntry {
                transaction,
                fee_sat: 1,
                vsize: 1,
                added_at: 1,
                height: 0,
            },
        );
        pool.wtxids.insert(wtxid, txid);
        pool.relay_sequences.insert(txid, 4);

        assert!(pool.get_for_relay(&txid, 4).is_none());
        assert!(pool.get_for_relay(&txid, 5).is_some());
        assert!(pool.get_by_wtxid_for_relay(&wtxid, 5).is_some());
    }

    #[test]
    fn revalidation_sequences_only_removed_transactions() {
        let directory = tempfile::tempdir().unwrap();
        let chain = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let root = graph_transaction(Txid::from_byte_array([1; 32]), 1);
        let child = graph_transaction(root.compute_txid(), 2);
        let mut pool = Mempool::new(Network::Regtest);
        insert_policy_entry(&mut pool, root);
        insert_policy_entry(&mut pool, child);

        pool.revalidate(&chain);

        assert!(pool.is_empty());
        assert_eq!(pool.sequence(), 3);
        let changes = pool.take_changes();
        assert_eq!(changes.len(), 2);
        assert!(changes.iter().all(|change| matches!(
            &change.kind,
            &MempoolChangeKind::Removed { notify_zmq: true }
        )));
        assert_eq!(changes[0].sequence, 1);
        assert_eq!(changes[1].sequence, 2);
    }

    #[test]
    fn revalidation_preserves_relay_sequences_for_retained_transactions() {
        let directory = tempfile::tempdir().unwrap();
        let mut chain = ChainState::open(Network::Regtest, directory.path()).unwrap();
        for height in 1..=101 {
            let previous = chain.header(height - 1).expect("previous header");
            chain
                .connect_block(mine_regtest_block(previous, height))
                .unwrap();
        }
        let (outpoint, entry) = chain
            .all_utxos()
            .find(|(_, entry)| chain.height() + 1 >= entry.height + 100)
            .map(|(outpoint, entry)| (*outpoint, entry.clone()))
            .expect("matured coinbase output");
        let transaction = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: outpoint,
                script_sig: ScriptBuf::from_bytes(vec![0; 65]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(entry.output.value.to_sat() - 1_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let txid = transaction.compute_txid();
        let mut pool = Mempool::new(Network::Regtest);
        pool.accept(transaction, &chain).unwrap();
        let sequence = pool.relay_sequences[&txid];

        pool.revalidate(&chain);

        assert_eq!(pool.relay_sequences[&txid], sequence);
        assert!(pool.get_for_relay(&txid, sequence + 1).is_some());

        let transaction = pool
            .remove(&txid)
            .expect("retained transaction")
            .transaction;
        pool.take_changes();
        pool.accept_reorg(transaction, &chain, 1).unwrap();
        assert_eq!(pool.relay_sequences[&txid], 0);
    }

    #[test]
    fn standardness_policy_can_be_explicitly_disabled_on_regtest() {
        let directory = tempfile::tempdir().unwrap();
        let mut chain = ChainState::open(Network::Regtest, directory.path()).unwrap();
        for height in 1..=101 {
            let previous = chain.header(height - 1).expect("previous header");
            chain
                .connect_block(mine_regtest_block(previous, height))
                .unwrap();
        }
        let (outpoint, entry) = chain
            .all_utxos()
            .find(|(_, entry)| chain.height() + 1 >= entry.height + 100)
            .map(|(outpoint, entry)| (*outpoint, entry.clone()))
            .expect("matured coinbase output");
        let transaction = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: outpoint,
                script_sig: ScriptBuf::from_bytes(vec![0; 65]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(entry.output.value.to_sat() - 1_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };

        let strict_policy = MempoolPolicy {
            require_standard: true,
            ..MempoolPolicy::default()
        };
        let mut strict = Mempool::with_max_bytes_and_policy(
            Network::Regtest,
            DEFAULT_MAX_MEMPOOL_BYTES,
            strict_policy,
        );
        assert!(matches!(
            strict.accept(transaction.clone(), &chain),
            Err(MempoolError::NonStandard(reason)) if reason == "scriptpubkey"
        ));

        let mut permissive_policy = strict_policy;
        permissive_policy.require_standard = false;
        let mut permissive = Mempool::with_max_bytes_and_policy(
            Network::Regtest,
            DEFAULT_MAX_MEMPOOL_BYTES,
            permissive_policy,
        );
        assert!(permissive.accept(transaction, &chain).is_ok());
    }

    #[test]
    fn rejects_transactions_whose_outputs_are_already_in_the_chain() {
        let directory = tempfile::tempdir().unwrap();
        let mut chain = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let mut previous = *chain.header(0).unwrap();
        let mut funding = None;
        for height in 1..=101 {
            let block = mine_regtest_block(&previous, height);
            if height == 1 {
                funding = Some(OutPoint::new(block.txdata[0].compute_txid(), 0));
            }
            previous = block.header;
            chain.connect_block(block).unwrap();
        }
        let funding = funding.expect("funding output exists");
        let transaction = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: funding,
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(4_999_999_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let mut block = mine_regtest_block(&previous, 102);
        block.txdata.push(transaction.clone());
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        block.header.nonce = 0;
        while !block.header.target().is_met_by(block.block_hash()) {
            block.header.nonce = block.header.nonce.wrapping_add(1);
        }
        chain.connect_block(block).unwrap();

        let mut pool = Mempool::new(Network::Regtest);
        assert!(matches!(
            pool.accept(transaction, &chain),
            Err(MempoolError::AlreadyInChain)
        ));
    }

    #[test]
    fn accepted_entries_use_sigop_adjusted_weight_for_vsize() {
        let directory = tempfile::tempdir().unwrap();
        let mut chain = ChainState::open(Network::Regtest, directory.path()).unwrap();
        for height in 1..=101 {
            let previous = chain.header(height - 1).expect("previous header");
            chain
                .connect_block(mine_regtest_block(previous, height))
                .unwrap();
        }
        let (outpoint, entry) = chain
            .all_utxos()
            .find(|(_, entry)| chain.height() + 1 >= entry.height + 100)
            .map(|(outpoint, entry)| (*outpoint, entry.clone()))
            .expect("matured coinbase output");

        let sigop_count = 100usize;
        let transaction = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: outpoint,
                script_sig: Builder::new().push_int(1).into_script(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(entry.output.value.to_sat() - 1_000),
                script_pubkey: ScriptBuf::from_bytes(vec![
                    bitcoin::opcodes::all::OP_CHECKSIG
                        .to_u8();
                    sigop_count
                ]),
            }],
        };
        let raw_weight = transaction.weight().to_wu();
        let expected_weight = raw_weight.max(
            (sigop_count as u64)
                .saturating_mul(4)
                .saturating_mul(DEFAULT_BYTES_PER_SIGOP),
        );
        assert!(expected_weight > raw_weight);

        let mut pool = Mempool::new(Network::Regtest);
        let txid = pool.accept_reorg(transaction.clone(), &chain, 1).unwrap();
        let entry = pool.get(&txid).expect("accepted transaction");
        assert_eq!(pool.adjusted_weight(&txid), expected_weight);
        assert_eq!(entry.vsize, expected_weight.saturating_add(3) / 4);

        let policy = MempoolPolicy {
            bytes_per_sigop: 10,
            require_standard: false,
            ..MempoolPolicy::default()
        };
        let mut custom_pool =
            Mempool::with_max_bytes_and_policy(Network::Regtest, 300_000_000, policy);
        let custom_txid = custom_pool.accept_reorg(transaction, &chain, 1).unwrap();
        let custom_entry = custom_pool
            .get(&custom_txid)
            .expect("custom-policy transaction");
        let custom_weight = raw_weight.max((sigop_count as u64).saturating_mul(4 * 10));
        assert_eq!(custom_pool.adjusted_weight(&custom_txid), custom_weight);
        assert_eq!(custom_entry.vsize, custom_weight.saturating_add(3) / 4);
    }

    #[test]
    fn expires_old_entries_and_records_removal_sequence() {
        let transaction = graph_transaction(Txid::from_byte_array([1; 32]), 1);
        let txid = transaction.compute_txid();
        let wtxid = transaction.compute_wtxid();
        let mut pool = Mempool::new(Network::Regtest);
        pool.entries.insert(
            txid,
            MempoolEntry {
                transaction,
                fee_sat: 1,
                vsize: 1,
                added_at: 1,
                height: 0,
            },
        );
        pool.wtxids.insert(wtxid, txid);
        pool.clear_expired(2 + MEMPOOL_EXPIRY.as_secs(), MEMPOOL_EXPIRY);
        assert!(pool.is_empty());
        let changes = pool.take_changes();
        assert_eq!(changes.len(), 1);
        assert_eq!(changes[0].sequence, 1);
        assert!(matches!(
            changes[0].kind,
            MempoolChangeKind::Removed { notify_zmq: true }
        ));
    }

    #[test]
    fn tracks_transitive_mempool_relationships() {
        let root = graph_transaction(Txid::from_byte_array([1; 32]), 1);
        let root_id = root.compute_txid();
        let child = graph_transaction(root_id, 2);
        let child_id = child.compute_txid();
        let grandchild = graph_transaction(child_id, 3);
        let grandchild_id = grandchild.compute_txid();
        let grandchild_wtxid = grandchild.compute_wtxid();
        let mut pool = Mempool::new(Network::Regtest);
        for (time, transaction) in [(1, root), (2, child), (3, grandchild)] {
            let txid = transaction.compute_txid();
            let wtxid = transaction.compute_wtxid();
            pool.entries.insert(
                txid,
                MempoolEntry {
                    vsize: transaction.vsize() as u64,
                    fee_sat: 10,
                    added_at: time,
                    height: 0,
                    transaction,
                },
            );
            pool.wtxids.insert(wtxid, txid);
        }
        pool.children.entry(root_id).or_default().insert(child_id);
        pool.children
            .entry(child_id)
            .or_default()
            .insert(grandchild_id);

        assert_eq!(pool.parents(&grandchild_id), vec![child_id]);
        assert_eq!(pool.children(&root_id), vec![child_id]);
        assert_eq!(pool.ancestors(&grandchild_id), vec![root_id, child_id]);
        assert_eq!(pool.descendants(&root_id), vec![child_id, grandchild_id]);
        assert_eq!(pool.get_by_wtxid(&grandchild_wtxid).unwrap().added_at, 3);
    }

    #[test]
    fn inherited_rbf_signal_marks_descendants_replaceable() {
        let mut parent = graph_transaction(Txid::from_byte_array([4; 32]), 4);
        parent.input[0].sequence = bitcoin::Sequence::from_consensus(0xffff_fffd);
        let parent_id = parent.compute_txid();
        let child = graph_transaction(parent_id, 5);
        let child_id = child.compute_txid();
        let mut pool = Mempool::new(Network::Regtest);
        for transaction in [parent, child] {
            let txid = transaction.compute_txid();
            let wtxid = transaction.compute_wtxid();
            pool.entries.insert(
                txid,
                MempoolEntry {
                    vsize: transaction.vsize() as u64,
                    fee_sat: 10,
                    added_at: 1,
                    height: 0,
                    transaction,
                },
            );
            pool.wtxids.insert(wtxid, txid);
        }
        pool.children.entry(parent_id).or_default().insert(child_id);

        assert!(pool.is_replaceable(&parent_id));
        assert!(pool.is_replaceable(&child_id));
    }

    #[test]
    fn mining_order_prefers_high_feerate_ancestor_packages() {
        let parent = graph_transaction(Txid::from_byte_array([1; 32]), 1);
        let parent_id = parent.compute_txid();
        let child = graph_transaction(parent_id, 2);
        let child_id = child.compute_txid();
        let independent = graph_transaction(Txid::from_byte_array([3; 32]), 3);
        let independent_id = independent.compute_txid();
        let mut pool = Mempool::new(Network::Regtest);
        for (transaction, fee_sat) in [(parent, 1), (child, 200), (independent, 20)] {
            let txid = transaction.compute_txid();
            let wtxid = transaction.compute_wtxid();
            pool.entries.insert(
                txid,
                MempoolEntry {
                    vsize: transaction.vsize() as u64,
                    fee_sat,
                    added_at: 1,
                    height: 0,
                    transaction,
                },
            );
            pool.wtxids.insert(wtxid, txid);
        }

        assert_eq!(
            pool.mining_order(4_000_000, 0),
            vec![parent_id, child_id, independent_id]
        );
        assert_eq!(pool.main_order(), vec![parent_id, child_id, independent_id]);
        assert_eq!(
            pool.mining_order_with_min_fee(4_000_000, 0, 1_000),
            vec![parent_id, child_id]
        );
    }

    #[test]
    fn tracks_fee_delta_prioritisation_for_present_and_absent_transactions() {
        let transaction = graph_transaction(Txid::from_byte_array([9; 32]), 9);
        let txid = transaction.compute_txid();
        let mut pool = Mempool::new(Network::Regtest);
        pool.entries.insert(
            txid,
            MempoolEntry {
                vsize: transaction.vsize() as u64,
                fee_sat: 10,
                added_at: 1,
                height: 0,
                transaction,
            },
        );
        pool.prioritise(txid, 25);
        assert_eq!(pool.fee_delta(&txid), 25);
        assert_eq!(
            pool.prioritised_transactions(),
            vec![(txid, 25, true, Some(35))]
        );

        let absent = Txid::from_byte_array([8; 32]);
        pool.prioritise(absent, -4);
        assert_eq!(
            pool.prioritised_transactions(),
            vec![(absent, -4, false, None), (txid, 25, true, Some(35))]
        );
        pool.prioritise(txid, -25);
        assert_eq!(pool.fee_delta(&txid), 0);
    }

    #[test]
    fn rejects_transactions_that_exceed_cluster_count_limit() {
        let mut pool = Mempool::new(Network::Regtest);
        let mut previous = Txid::from_byte_array([0; 32]);
        let mut chain = Vec::with_capacity(MAX_CLUSTER_COUNT);
        for marker in 0..MAX_CLUSTER_COUNT {
            let transaction = graph_transaction(previous, marker as u8);
            let txid = transaction.compute_txid();
            pool.entries.insert(
                txid,
                MempoolEntry {
                    vsize: transaction.vsize() as u64,
                    fee_sat: 1,
                    added_at: 1,
                    height: 0,
                    transaction,
                },
            );
            pool.children.entry(previous).or_default().insert(txid);
            pool.wtxids.insert(
                pool.entries
                    .get(&txid)
                    .expect("inserted transaction")
                    .transaction
                    .compute_wtxid(),
                txid,
            );
            chain.push(txid);
            previous = txid;
        }
        let candidate = graph_transaction(previous, 0xff);
        assert!(matches!(
            pool.check_cluster_limits(&candidate),
            Err(MempoolError::ClusterLimit)
        ));
        assert_eq!(chain.len(), MAX_CLUSTER_COUNT);
    }

    #[test]
    fn configured_cluster_limits_are_enforced() {
        let policy = MempoolPolicy {
            cluster_count_limit: 1,
            cluster_vsize_limit: MAX_CLUSTER_VSIZE,
            ..MempoolPolicy::default()
        };
        let mut pool = Mempool::with_max_bytes_and_policy(Network::Regtest, 300_000_000, policy);
        let parent = graph_transaction(Txid::from_byte_array([31; 32]), 31);
        let parent_id = insert_policy_entry(&mut pool, parent);
        let child = graph_transaction(parent_id, 32);
        assert!(matches!(
            pool.check_cluster_limits(&child),
            Err(MempoolError::ClusterLimit)
        ));
        assert_eq!(pool.cluster_count_limit(), 1);
        assert_eq!(pool.cluster_vsize_limit(), MAX_CLUSTER_VSIZE);
    }

    #[test]
    fn eviction_removes_the_lowest_feerate_package_but_protects_ancestors() {
        let low = graph_transaction(Txid::from_byte_array([20; 32]), 20);
        let low_id = low.compute_txid();
        let high = graph_transaction(Txid::from_byte_array([21; 32]), 21);
        let high_id = high.compute_txid();
        let low_memory = mempool_entry_memory_usage(&low);
        let high_memory = mempool_entry_memory_usage(&high);
        let mut pool = Mempool::new(Network::Regtest);
        pool.max_bytes = low_memory.saturating_add(high_memory).saturating_sub(1);
        for (transaction, fee_sat) in [(low, 1), (high, 100)] {
            let txid = transaction.compute_txid();
            let wtxid = transaction.compute_wtxid();
            pool.memory_usage = pool
                .memory_usage
                .saturating_add(mempool_entry_memory_usage(&transaction));
            pool.bytes = pool
                .bytes
                .saturating_add(bitcoin::consensus::encode::serialize(&transaction).len());
            pool.entries.insert(
                txid,
                MempoolEntry {
                    vsize: transaction.vsize() as u64,
                    fee_sat,
                    added_at: 1,
                    height: 0,
                    transaction,
                },
            );
            pool.wtxids.insert(wtxid, txid);
        }
        pool.enforce_size_limit();
        assert!(!pool.entries.contains_key(&low_id));
        assert!(pool.entries.contains_key(&high_id));
        assert!(pool.mempool_min_fee_sat_per_kvb() > pool.min_relay_fee_sat_per_kvb());

        let parent = graph_transaction(Txid::from_byte_array([22; 32]), 22);
        let parent_id = parent.compute_txid();
        let parent_size = bitcoin::consensus::encode::serialize(&parent).len();
        let parent_memory = mempool_entry_memory_usage(&parent);
        let mut protected_pool = Mempool::new(Network::Regtest);
        protected_pool.max_bytes = parent_memory;
        protected_pool.bytes = parent_size;
        protected_pool.memory_usage = parent_memory;
        protected_pool.entries.insert(
            parent_id,
            MempoolEntry {
                vsize: parent.vsize() as u64,
                fee_sat: 1,
                added_at: 1,
                height: 0,
                transaction: parent,
            },
        );
        assert!(matches!(
            protected_pool.ensure_space(1, &HashSet::from([parent_id])),
            Err(MempoolError::Full)
        ));
        assert!(protected_pool.entries.contains_key(&parent_id));
    }

    #[test]
    fn rolling_minimum_fee_decays_after_a_block() {
        let mut pool = Mempool::new(Network::Regtest);
        pool.rolling_min_fee_sat_per_kvb = 10_000.0;
        pool.block_since_last_rolling_fee_bump = true;
        pool.rolling_fee_last_updated = time::unix_time().saturating_sub(12 * 60 * 60);

        let decayed = pool.mempool_min_fee_sat_per_kvb();
        assert!(decayed < 10_000);
        assert!(decayed >= pool.min_relay_fee_sat_per_kvb());
    }

    fn insert_policy_entry(pool: &mut Mempool, transaction: Transaction) -> Txid {
        let txid = transaction.compute_txid();
        let wtxid = transaction.compute_wtxid();
        for input in &transaction.input {
            if pool.entries.contains_key(&input.previous_output.txid) {
                pool.children
                    .entry(input.previous_output.txid)
                    .or_default()
                    .insert(txid);
            }
        }
        pool.entries.insert(
            txid,
            MempoolEntry {
                vsize: transaction.vsize() as u64,
                fee_sat: 1,
                added_at: 1,
                height: 0,
                transaction,
            },
        );
        pool.wtxids.insert(wtxid, txid);
        pool.invalidate_graph_optimality();
        txid
    }

    #[test]
    fn mempool_graph_optimality_is_invalidated_by_graph_and_fee_changes() {
        let mut pool = Mempool::new(Network::Regtest);
        assert!(pool.optimal());

        let parent = graph_transaction(Txid::from_byte_array([40; 32]), 40);
        let parent_id = insert_policy_entry(&mut pool, parent);
        assert!(pool.optimal());

        let child = graph_transaction(parent_id, 41);
        let child_id = insert_policy_entry(&mut pool, child);
        assert!(pool.optimal());

        pool.prioritise(child_id, 100);
        assert!(pool.optimal());

        pool.remove(&parent_id);
        assert!(pool.optimal());
    }

    #[test]
    fn unresolved_large_non_tree_cluster_is_not_reported_as_optimal() {
        let mut pool = Mempool::new(Network::Regtest);
        let first = graph_transaction(Txid::from_byte_array([50; 32]), 50);
        let first_id = insert_policy_entry(&mut pool, first);
        let second = graph_transaction(Txid::from_byte_array([51; 32]), 51);
        let second_id = insert_policy_entry(&mut pool, second);

        for marker in 0..11u8 {
            let transaction = Transaction {
                version: Version::ONE,
                lock_time: LockTime::ZERO,
                input: vec![
                    TxIn {
                        previous_output: OutPoint::new(first_id, 0),
                        script_sig: ScriptBuf::from_bytes(vec![marker]),
                        sequence: bitcoin::Sequence::MAX,
                        witness: Witness::default(),
                    },
                    TxIn {
                        previous_output: OutPoint::new(second_id, 0),
                        script_sig: ScriptBuf::from_bytes(vec![marker, 1]),
                        sequence: bitcoin::Sequence::MAX,
                        witness: Witness::default(),
                    },
                ],
                output: vec![TxOut {
                    value: Amount::from_sat(1),
                    script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
                }],
            };
            insert_policy_entry(&mut pool, transaction);
        }

        assert!(!pool.optimal());
    }

    #[test]
    fn replacement_cluster_limit_counts_connected_clusters() {
        let mut pool = Mempool::new(Network::Regtest);
        let mut independent_conflicts = Vec::new();
        for marker in 0..=100u8 {
            let transaction = graph_transaction(Txid::from_byte_array([marker; 32]), marker);
            independent_conflicts.push(insert_policy_entry(&mut pool, transaction));
        }

        assert_eq!(
            pool.conflicting_cluster_count(&independent_conflicts),
            MAX_REPLACEMENT_CANDIDATES + 1
        );
        assert!(matches!(
            pool.check_replacement_cluster_limit(
                Txid::from_byte_array([201; 32]),
                &independent_conflicts,
            ),
            Err(MempoolError::TooManyReplacementCandidates {
                count: 101,
                limit: 100,
                ..
            })
        ));

        let parent = graph_transaction(Txid::from_byte_array([202; 32]), 202);
        let parent_id = insert_policy_entry(&mut pool, parent);
        let child = graph_transaction(parent_id, 203);
        let child_id = insert_policy_entry(&mut pool, child);
        assert_eq!(pool.conflicting_cluster_count(&[parent_id, child_id]), 1);
        assert!(
            pool.check_replacement_cluster_limit(Txid::from_byte_array([204; 32]), &[child_id])
                .is_ok()
        );
    }

    #[test]
    fn feerate_diagram_comparison_matches_core_ordering() {
        let old = vec![(950, 300), (100, 100)];
        let new = vec![(1_000, 300), (50, 100)];
        assert_eq!(
            compare_fee_rate_diagrams(&new, &old),
            Some(Ordering::Greater)
        );
        assert_eq!(compare_fee_rate_diagrams(&old, &new), Some(Ordering::Less));

        let incomparable = vec![(750, 100), (249, 250), (151, 650)];
        assert_eq!(compare_fee_rate_diagrams(&old, &incomparable), None);
        assert_eq!(compare_fee_rate_diagrams(&incomparable, &old), None);

        let smaller_tail = vec![(950, 300), (100, 99)];
        assert_eq!(
            compare_fee_rate_diagrams(&smaller_tail, &old),
            Some(Ordering::Greater)
        );
        assert_eq!(
            compare_fee_rate_diagrams(&old, &smaller_tail),
            Some(Ordering::Less)
        );
    }

    #[test]
    fn enforces_truc_inheritance_size_and_topology() {
        let mut pool = Mempool::new(Network::Regtest);
        let mut v3_parent = graph_transaction(Txid::from_byte_array([30; 32]), 30);
        v3_parent.version = Version::non_standard(TRUC_VERSION);
        let v3_parent_id = insert_policy_entry(&mut pool, v3_parent);

        let v2_child = graph_transaction(v3_parent_id, 31);
        assert!(matches!(
            pool.check_truc_policy(&v2_child, v2_child.vsize() as u64),
            Err(MempoolError::Truc(reason)) if reason.contains("non-version=3 tx")
        ));

        let mut v2_parent = graph_transaction(Txid::from_byte_array([32; 32]), 32);
        v2_parent.version = Version::TWO;
        let v2_parent_id = insert_policy_entry(&mut pool, v2_parent);
        let mut v3_child_of_v2 = graph_transaction(v2_parent_id, 33);
        v3_child_of_v2.version = Version::non_standard(TRUC_VERSION);
        assert!(matches!(
            pool.check_truc_policy(&v3_child_of_v2, v3_child_of_v2.vsize() as u64),
            Err(MempoolError::Truc(reason)) if reason.contains("cannot spend from non-version=3")
        ));

        let mut v3_child = graph_transaction(v3_parent_id, 34);
        v3_child.version = Version::non_standard(TRUC_VERSION);
        let v3_child_id = v3_child.compute_txid();
        assert!(
            pool.check_truc_policy(&v3_child, v3_child.vsize() as u64)
                .is_ok()
        );
        insert_policy_entry(&mut pool, v3_child);

        let mut v3_grandchild = graph_transaction(v3_child_id, 35);
        v3_grandchild.version = Version::non_standard(TRUC_VERSION);
        assert!(matches!(
            pool.check_truc_policy(&v3_grandchild, v3_grandchild.vsize() as u64),
            Err(MempoolError::Truc(reason)) if reason.contains("too many ancestors")
        ));

        let mut v3_sibling = graph_transaction(v3_parent_id, 36);
        v3_sibling.version = Version::non_standard(TRUC_VERSION);
        assert!(matches!(
            pool.check_truc_policy(&v3_sibling, v3_sibling.vsize() as u64),
            Err(MempoolError::Truc(reason)) if reason.contains("descendant count limit")
        ));

        let mut huge = graph_transaction(Txid::from_byte_array([37; 32]), 37);
        huge.version = Version::non_standard(TRUC_VERSION);
        huge.output = (0..1_200)
            .map(|_| TxOut {
                value: Amount::from_sat(1),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            })
            .collect();
        assert!(huge.vsize() as u64 > TRUC_MAX_VSIZE);
        assert!(matches!(
            pool.check_truc_policy(&huge, huge.vsize() as u64),
            Err(MempoolError::Truc(reason)) if reason.contains("is too big")
        ));

        let mut child_size_parent = graph_transaction(Txid::from_byte_array([38; 32]), 38);
        child_size_parent.version = Version::non_standard(TRUC_VERSION);
        let child_size_parent_id = insert_policy_entry(&mut pool, child_size_parent);
        let mut large_child = graph_transaction(child_size_parent_id, 39);
        large_child.version = Version::non_standard(TRUC_VERSION);
        large_child.output = (0..120)
            .map(|_| TxOut {
                value: Amount::from_sat(1),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            })
            .collect();
        assert!(large_child.vsize() as u64 > TRUC_CHILD_MAX_VSIZE);
        assert!(matches!(
            pool.check_truc_policy(&large_child, large_child.vsize() as u64),
            Err(MempoolError::Truc(reason)) if reason.contains("child tx")
        ));
    }

    #[test]
    fn single_transaction_truc_acceptance_can_evict_a_sibling() {
        let directory = tempfile::tempdir().unwrap();
        let chain = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let mut pool = Mempool::with_max_bytes_and_policy(
            Network::Regtest,
            DEFAULT_MAX_MEMPOOL_BYTES,
            MempoolPolicy {
                require_standard: false,
                truc_policy: TrucPolicy::Enforce,
                ..MempoolPolicy::default()
            },
        );
        let mut parent = graph_transaction(Txid::from_byte_array([40; 32]), 40);
        parent.version = Version::non_standard(TRUC_VERSION);
        parent.input[0].script_sig = ScriptBuf::from_bytes(vec![0; 8]);
        parent.output = vec![
            TxOut {
                value: Amount::from_sat(100_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            },
            TxOut {
                value: Amount::from_sat(100_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            },
        ];
        let parent_id = insert_policy_entry(&mut pool, parent);

        let mut sibling = graph_transaction(parent_id, 41);
        sibling.version = Version::non_standard(TRUC_VERSION);
        sibling.input[0].previous_output.vout = 0;
        sibling.input[0].script_sig = ScriptBuf::from_bytes(vec![0; 8]);
        sibling.output[0].value = Amount::from_sat(99_900);
        let sibling_id = insert_policy_entry(&mut pool, sibling);

        let mut replacement = graph_transaction(parent_id, 42);
        replacement.version = Version::non_standard(TRUC_VERSION);
        replacement.input[0].previous_output.vout = 1;
        replacement.input[0].script_sig = ScriptBuf::from_bytes(vec![0; 8]);
        replacement.output[0].value = Amount::from_sat(98_000);
        let replacement_id = replacement.compute_txid();

        let mut test_pool = pool.clone();
        let test_result = test_pool.accept_without_sibling(replacement.clone(), &chain);
        assert!(matches!(
            test_result,
            Err(MempoolError::Truc(reason)) if reason.contains("descendant count limit")
        ));
        assert_eq!(pool.truc_sibling_for(&replacement), Some(sibling_id));
        assert_eq!(pool.accept(replacement, &chain).unwrap(), replacement_id);
        assert!(pool.get(&sibling_id).is_none());
        assert!(pool.get(&replacement_id).is_some());
        assert_eq!(pool.children(&parent_id), vec![replacement_id]);
    }

    #[test]
    fn replacement_policy_matches_core_modes() {
        let old = graph_transaction(Txid::from_byte_array([50; 32]), 50);
        let old_id = old.compute_txid();

        let mut never = Mempool::with_max_bytes_and_policy(
            Network::Regtest,
            DEFAULT_MAX_MEMPOOL_BYTES,
            MempoolPolicy {
                require_standard: false,
                rbf_policy: RbfPolicy::Never,
                ..MempoolPolicy::default()
            },
        );
        insert_policy_entry(&mut never, old.clone());
        assert!(matches!(
            never.check_replacement_policy(&[old_id]),
            Err(MempoolError::ReplacementDisallowed)
        ));

        let mut opt_in = Mempool::with_max_bytes_and_policy(
            Network::Regtest,
            DEFAULT_MAX_MEMPOOL_BYTES,
            MempoolPolicy {
                require_standard: false,
                rbf_policy: RbfPolicy::OptIn,
                ..MempoolPolicy::default()
            },
        );
        insert_policy_entry(&mut opt_in, old);
        assert!(matches!(
            opt_in.check_replacement_policy(&[old_id]),
            Err(MempoolError::ReplacementDisallowed)
        ));

        let mut signaling = graph_transaction(Txid::from_byte_array([51; 32]), 51);
        signaling.input[0].sequence = bitcoin::Sequence::from_consensus(0xffff_fffd);
        let signaling_id = signaling.compute_txid();
        insert_policy_entry(&mut opt_in, signaling);
        assert!(opt_in.check_replacement_policy(&[signaling_id]).is_ok());

        let mut truc = graph_transaction(Txid::from_byte_array([52; 32]), 52);
        truc.version = Version::non_standard(TRUC_VERSION);
        let truc_id = truc.compute_txid();
        insert_policy_entry(&mut opt_in, truc);
        assert!(opt_in.check_replacement_policy(&[truc_id]).is_ok());
    }

    #[test]
    fn standard_policy_accepts_known_scripts_and_rejects_nonstandard_outputs() {
        let previous = TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: ScriptBuf::from_bytes({
                let mut bytes = vec![0x76, 0xa9, 0x14];
                bytes.extend([0u8; 20]);
                bytes.extend([0x88, 0xac]);
                bytes
            }),
        };
        let mut nonstandard = graph_transaction(Txid::from_byte_array([7; 32]), 7);
        let standard_p2pkh_script_sig = ScriptBuf::from_bytes({
            let mut bytes = vec![0x00, 0x21, 0x02];
            bytes.extend([0u8; 32]);
            bytes
        });
        nonstandard.input[0].script_sig = standard_p2pkh_script_sig.clone();
        assert!(matches!(
            validate_standard_policy(&nonstandard, std::slice::from_ref(&previous), 1),
            Err(MempoolError::NonStandard(reason)) if reason == "scriptpubkey"
        ));

        nonstandard.output[0].script_pubkey = ScriptBuf::new_p2a();
        nonstandard.output[0].value = Amount::from_sat(100_000);
        assert!(validate_standard_policy(&nonstandard, std::slice::from_ref(&previous), 0).is_ok());

        nonstandard.output[0].script_pubkey = ScriptBuf::from_bytes({
            let mut bytes = vec![0x00, 0x14];
            bytes.extend([0u8; 20]);
            bytes
        });
        nonstandard.output[0].value = Amount::from_sat(100_000);
        assert!(validate_standard_policy(&nonstandard, std::slice::from_ref(&previous), 1).is_ok());

        nonstandard.input[0].script_sig = ScriptBuf::from_bytes(vec![0x4c, 0x01, 0x01]);
        assert!(matches!(
            validate_standard_policy(&nonstandard, std::slice::from_ref(&previous), 1),
            Err(MempoolError::NonStandard(reason)) if reason == "bad-txns-nonstandard-inputs"
        ));
        nonstandard.input[0].script_sig = standard_p2pkh_script_sig;

        nonstandard.output[0].value = Amount::from_sat(1);
        assert!(is_dust_output(&nonstandard.output[0]));

        let mut strict_pool = Mempool::new(Network::Bitcoin);
        let dust_id = insert_policy_entry(&mut strict_pool, nonstandard.clone());
        assert!(strict_pool.has_dust_outputs(&dust_id));
        nonstandard.output[0].script_pubkey =
            ScriptBuf::from_bytes(vec![0x6a; MAX_SCRIPT_SIZE + 1]);
        let unspendable_id = insert_policy_entry(&mut strict_pool, nonstandard.clone());
        assert!(!strict_pool.has_dust_outputs(&unspendable_id));

        nonstandard.output[0].value = Amount::from_sat(100_000);
        nonstandard.output[0].script_pubkey = ScriptBuf::from_bytes({
            let mut bytes = vec![0x52, 0x20];
            bytes.extend([0u8; 32]);
            bytes
        });
        assert!(matches!(
            validate_standard_policy(&nonstandard, std::slice::from_ref(&previous), 1),
            Err(MempoolError::NonStandard(reason)) if reason == "scriptpubkey"
        ));

        let redeem_script = ScriptBuf::new();
        let redeem_hash = bitcoin::hashes::hash160::Hash::hash(redeem_script.as_bytes());
        let mut p2sh = vec![0xa9, 0x14];
        p2sh.extend_from_slice(&redeem_hash.to_byte_array());
        p2sh.push(0x87);
        let p2sh_previous = TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: ScriptBuf::from_bytes(p2sh),
        };
        let mut empty_redeem = graph_transaction(Txid::from_byte_array([12; 32]), 12);
        empty_redeem.input[0].script_sig = ScriptBuf::from_bytes(vec![0x00]);
        empty_redeem.output[0].value = Amount::from_sat(100_000);
        empty_redeem.output[0].script_pubkey = previous.script_pubkey.clone();
        assert!(validate_standard_policy(&empty_redeem, &[p2sh_previous], 0).is_ok());

        let negative_one_redeem = ScriptBuf::from_bytes(vec![0x81]);
        let negative_one_hash =
            bitcoin::hashes::hash160::Hash::hash(negative_one_redeem.as_bytes());
        let mut negative_one_p2sh = vec![0xa9, 0x14];
        negative_one_p2sh.extend_from_slice(&negative_one_hash.to_byte_array());
        negative_one_p2sh.push(0x87);
        empty_redeem.input[0].script_sig = ScriptBuf::from_bytes(vec![0x4f]);
        assert!(
            validate_standard_policy(
                &empty_redeem,
                &[TxOut {
                    value: Amount::from_sat(100_000),
                    script_pubkey: ScriptBuf::from_bytes(negative_one_p2sh),
                }],
                0,
            )
            .is_ok()
        );

        let wpkh_previous = TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: ScriptBuf::from_bytes({
                let mut bytes = vec![0x00, 0x14];
                bytes.extend([0u8; 20]);
                bytes
            }),
        };
        let mut witness_transaction = graph_transaction(Txid::from_byte_array([9; 32]), 9);
        witness_transaction.input[0].script_sig = ScriptBuf::new();
        witness_transaction.input[0].witness = Witness::from_slice(&[vec![1u8], vec![0x04; 65]]);
        witness_transaction.output[0].script_pubkey = ScriptBuf::from_bytes({
            let mut bytes = vec![0x00, 0x14];
            bytes.extend([0u8; 20]);
            bytes
        });
        witness_transaction.output[0].value = Amount::from_sat(100_000);
        let witness_policy = validate_standard_policy(
            &witness_transaction,
            std::slice::from_ref(&wpkh_previous),
            1,
        );
        assert!(matches!(
            witness_policy,
            Err(MempoolError::NonStandard(reason)) if reason == "bad-witness-nonstandard"
        ));

        let taproot_previous = TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: ScriptBuf::from_bytes({
                let mut bytes = vec![0x51, 0x20];
                bytes.extend([0u8; 32]);
                bytes
            }),
        };
        let mut future_taproot = graph_transaction(Txid::from_byte_array([10; 32]), 10);
        future_taproot.input[0].script_sig = ScriptBuf::new();
        future_taproot.input[0].witness = Witness::from_slice(&[vec![0x51], vec![0xc2; 33]]);
        future_taproot.output[0].value = Amount::from_sat(100_000);
        future_taproot.output[0].script_pubkey = taproot_previous.script_pubkey.clone();
        assert!(matches!(
            validate_standard_policy(
                &future_taproot,
                std::slice::from_ref(&taproot_previous),
                1,
            ),
            Err(MempoolError::NonStandard(reason)) if reason == "bad-witness-nonstandard"
        ));
        future_taproot.input[0].witness = Witness::from_slice(&[vec![0x50], vec![0xc0; 33]]);
        assert!(matches!(
            validate_standard_policy(
                &future_taproot,
                std::slice::from_ref(&taproot_previous),
                1,
            ),
            Err(MempoolError::NonStandard(reason)) if reason == "bad-witness-nonstandard"
        ));

        let anchor_previous = TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: ScriptBuf::new_p2a(),
        };
        let mut anchor_spend = graph_transaction(Txid::from_byte_array([11; 32]), 11);
        anchor_spend.input[0].script_sig = ScriptBuf::new();
        anchor_spend.input[0].witness = Witness::from_slice(&[vec![1u8]]);
        anchor_spend.output[0].value = Amount::from_sat(100_000);
        anchor_spend.output[0].script_pubkey = previous.script_pubkey.clone();
        assert!(matches!(
            validate_standard_policy(&anchor_spend, std::slice::from_ref(&anchor_previous), 0),
            Err(MempoolError::NonStandard(reason)) if reason == "bad-witness-nonstandard"
        ));
        anchor_spend.input[0].witness = Witness::default();
        assert!(
            validate_standard_policy(&anchor_spend, std::slice::from_ref(&anchor_previous), 0)
                .is_ok()
        );
    }

    #[test]
    fn standard_policy_enforces_simple_ecdsa_script_flags() {
        let pubkey =
            hex::decode("03363d90d447b00c9c99ceac05b6262ee053441c7e55552ffe526bad8f83ff4640")
                .unwrap();
        let previous = TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: {
                let mut bytes = vec![0x76, 0xa9, 0x14];
                bytes.extend([0u8; 20]);
                bytes.extend([0x88, 0xac]);
                ScriptBuf::from_bytes(bytes)
            },
        };
        let mut transaction = graph_transaction(Txid::from_byte_array([13; 32]), 13);
        transaction.output[0] = TxOut {
            value: Amount::from_sat(99_999),
            script_pubkey: ScriptBuf::from_bytes({
                let mut bytes = vec![0x00, 0x14];
                bytes.extend([0u8; 20]);
                bytes
            }),
        };

        let push_signature_and_pubkey = |signature: &[u8], pubkey: &[u8]| {
            let mut bytes = Vec::with_capacity(signature.len() + pubkey.len() + 2);
            bytes.push(u8::try_from(signature.len()).unwrap());
            bytes.extend_from_slice(signature);
            bytes.push(u8::try_from(pubkey.len()).unwrap());
            bytes.extend_from_slice(pubkey);
            ScriptBuf::from_bytes(bytes)
        };

        let high_s_signature = hex::decode(
            "304502203e4516da7253cf068effec6b95c41221c0cf3a8e6ccb8cbf1725b562e9afde2c022100ab1e3da73d67e32045a20e0b999e049978ea8d6ee5480d485fcf2ce0d03b2ef001",
        )
        .unwrap();
        transaction.input[0].script_sig = push_signature_and_pubkey(&high_s_signature, &pubkey);
        assert!(matches!(
            validate_standard_policy(&transaction, std::slice::from_ref(&previous), 1),
            Err(MempoolError::NonStandard(reason))
                if reason.contains("S value is unnecessarily high")
        ));

        transaction.input[0].script_sig = push_signature_and_pubkey(&[0x30, 0x01], &pubkey);
        assert!(matches!(
            validate_standard_policy(&transaction, std::slice::from_ref(&previous), 1),
            Err(MempoolError::NonStandard(reason))
                if reason.contains("Non-canonical DER signature")
        ));

        let secp = bitcoin::secp256k1::Secp256k1::new();
        let secret_key = bitcoin::secp256k1::SecretKey::from_slice(&[1u8; 32]).unwrap();
        let message = bitcoin::secp256k1::Message::from_digest([2u8; 32]);
        let mut undefined_hash_type = secp
            .sign_ecdsa(&message, &secret_key)
            .serialize_der()
            .to_vec();
        undefined_hash_type.push(0x05);
        transaction.input[0].script_sig = push_signature_and_pubkey(&undefined_hash_type, &pubkey);
        assert!(matches!(
            validate_standard_policy(&transaction, std::slice::from_ref(&previous), 1),
            Err(MempoolError::NonStandard(reason))
                if reason.contains("Signature hash type missing or not understood")
        ));

        let hybrid_pubkey = hex::decode(
            "0679be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8",
        )
        .unwrap();
        undefined_hash_type.pop();
        undefined_hash_type.push(0x01);
        transaction.input[0].script_sig =
            push_signature_and_pubkey(&undefined_hash_type, &hybrid_pubkey);
        assert!(matches!(
            validate_standard_policy(&transaction, std::slice::from_ref(&previous), 1),
            Err(MempoolError::NonStandard(reason))
                if reason.contains("neither compressed or uncompressed")
        ));
    }

    #[test]
    fn standard_policy_rejects_legacy_code_separator() {
        let redeem_script = ScriptBuf::from_bytes(vec![0x51, 0xab, 0x51]);
        let redeem_hash = bitcoin::hashes::hash160::Hash::hash(redeem_script.as_bytes());
        let p2sh_previous = TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: {
                let mut bytes = vec![0xa9, 0x14];
                bytes.extend_from_slice(&redeem_hash.to_byte_array());
                bytes.push(0x87);
                ScriptBuf::from_bytes(bytes)
            },
        };
        let mut transaction = graph_transaction(Txid::from_byte_array([14; 32]), 14);
        transaction.input[0].script_sig = ScriptBuf::from_bytes({
            let mut bytes = vec![redeem_script.len() as u8];
            bytes.extend_from_slice(redeem_script.as_bytes());
            bytes
        });
        transaction.output[0] = TxOut {
            value: Amount::from_sat(99_999),
            script_pubkey: ScriptBuf::from_bytes({
                let mut bytes = vec![0x00, 0x14];
                bytes.extend([0u8; 20]);
                bytes
            }),
        };

        assert!(matches!(
            validate_standard_policy(&transaction, std::slice::from_ref(&p2sh_previous), 1),
            Err(MempoolError::NonStandard(reason))
                if reason.contains("Using OP_CODESEPARATOR in non-witness script")
        ));

        let nop_redeem_script = ScriptBuf::from_bytes(vec![0xb3]);
        let nop_redeem_hash = bitcoin::hashes::hash160::Hash::hash(nop_redeem_script.as_bytes());
        let nop_previous = TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: {
                let mut bytes = vec![0xa9, 0x14];
                bytes.extend_from_slice(&nop_redeem_hash.to_byte_array());
                bytes.push(0x87);
                ScriptBuf::from_bytes(bytes)
            },
        };
        transaction.input[0].script_sig = ScriptBuf::from_bytes({
            let mut bytes = vec![nop_redeem_script.len() as u8];
            bytes.extend_from_slice(nop_redeem_script.as_bytes());
            bytes
        });
        assert!(matches!(
            validate_standard_policy(&transaction, std::slice::from_ref(&nop_previous), 1),
            Err(MempoolError::NonStandard(reason))
                if reason.contains("NOPx reserved for soft-fork upgrades")
        ));

        let nonminimal_redeem_script = ScriptBuf::from_bytes(vec![0x4c, 0x01, 0x51]);
        let nonminimal_redeem_hash =
            bitcoin::hashes::hash160::Hash::hash(nonminimal_redeem_script.as_bytes());
        let nonminimal_previous = TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: {
                let mut bytes = vec![0xa9, 0x14];
                bytes.extend_from_slice(&nonminimal_redeem_hash.to_byte_array());
                bytes.push(0x87);
                ScriptBuf::from_bytes(bytes)
            },
        };
        transaction.input[0].script_sig = ScriptBuf::from_bytes({
            let mut bytes = vec![nonminimal_redeem_script.len() as u8];
            bytes.extend_from_slice(nonminimal_redeem_script.as_bytes());
            bytes
        });
        assert!(matches!(
            validate_standard_policy(
                &transaction,
                std::slice::from_ref(&nonminimal_previous),
                1,
            ),
            Err(MempoolError::NonStandard(reason))
                if reason.contains("Data push larger than necessary")
        ));
    }

    #[test]
    fn standard_policy_enforces_minimal_if_for_simple_witness_scripts() {
        let witness_script = ScriptBuf::from_bytes(vec![0x63, 0x51, 0x68]);
        let witness_hash = bitcoin::hashes::sha256::Hash::hash(witness_script.as_bytes());
        let previous = TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: {
                let mut bytes = vec![0x00, 0x20];
                bytes.extend_from_slice(&witness_hash.to_byte_array());
                ScriptBuf::from_bytes(bytes)
            },
        };
        let mut transaction = graph_transaction(Txid::from_byte_array([15; 32]), 15);
        transaction.input[0].script_sig = ScriptBuf::new();
        transaction.input[0].witness =
            Witness::from_slice(&[vec![0x00, 0x01], witness_script.as_bytes().to_vec()]);
        transaction.output[0] = TxOut {
            value: Amount::from_sat(99_999),
            script_pubkey: ScriptBuf::from_bytes({
                let mut bytes = vec![0x00, 0x14];
                bytes.extend([0u8; 20]);
                bytes
            }),
        };

        assert!(matches!(
            validate_standard_policy(&transaction, std::slice::from_ref(&previous), 1),
            Err(MempoolError::NonStandard(reason))
                if reason.contains("OP_IF/NOTIF argument must be minimal")
        ));
    }

    #[test]
    fn standard_policy_honors_data_carrier_and_bare_multisig_switches() {
        let previous = TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: ScriptBuf::from_bytes({
                let mut bytes = vec![0x76, 0xa9, 0x14];
                bytes.extend([0u8; 20]);
                bytes.extend([0x88, 0xac]);
                bytes
            }),
        };
        let mut transaction = graph_transaction(Txid::from_byte_array([8; 32]), 8);
        transaction.input[0].script_sig = ScriptBuf::from_bytes({
            let mut bytes = vec![0x00, 0x21, 0x02];
            bytes.extend([0u8; 32]);
            bytes
        });
        transaction.output[0].script_pubkey = ScriptBuf::from_bytes(vec![0x6a, 0x01, 0x01]);
        let mut policy = MempoolPolicy {
            max_datacarrier_bytes: None,
            ..MempoolPolicy::default()
        };
        assert!(matches!(
            validate_standard_policy_with_modified_fee_and_policy(
                &transaction,
                std::slice::from_ref(&previous),
                1,
                1,
                &policy,
            ),
            Err(MempoolError::NonStandard(reason)) if reason == "datacarrier"
        ));

        let mut bare_multisig = vec![0x51, 0x21];
        transaction.output[0].script_pubkey = ScriptBuf::from_bytes(vec![0x6a, 0xab]);
        assert!(matches!(
            validate_standard_policy_with_modified_fee_and_policy(
                &transaction,
                std::slice::from_ref(&previous),
                1,
                1,
                &policy,
            ),
            Err(MempoolError::NonStandard(reason)) if reason == "scriptpubkey"
        ));

        bare_multisig.extend(
            hex::decode("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")
                .unwrap(),
        );
        bare_multisig.extend([0x51, 0xae]);
        transaction.output[0].script_pubkey = ScriptBuf::from_bytes(bare_multisig.clone());
        policy.max_datacarrier_bytes = Some(100_000);
        policy.permit_bare_multisig = false;
        assert!(matches!(
            validate_standard_policy_with_modified_fee_and_policy(
                &transaction,
                std::slice::from_ref(&previous),
                1,
                1,
                &policy,
            ),
            Err(MempoolError::NonStandard(reason)) if reason == "bare-multisig"
        ));

        policy.permit_bare_multisig = true;
        transaction.output[0].value = Amount::from_sat(100_000);
        assert!(
            validate_standard_policy_with_modified_fee_and_policy(
                &transaction,
                std::slice::from_ref(&previous),
                1,
                1,
                &policy,
            )
            .is_ok()
        );
        let mut zero_of_one = bare_multisig.clone();
        zero_of_one[0] = 0x00;
        transaction.output[0].script_pubkey = ScriptBuf::from_bytes(zero_of_one);
        assert!(matches!(
            validate_standard_policy_with_modified_fee_and_policy(
                &transaction,
                std::slice::from_ref(&previous),
                1,
                1,
                &policy,
            ),
            Err(MempoolError::NonStandard(reason)) if reason == "scriptpubkey"
        ));
    }

    #[test]
    fn standard_policy_limits_legacy_input_sigops() {
        let mut p2sh_script = vec![0xa9, 0x14];
        p2sh_script.extend([0u8; 20]);
        p2sh_script.push(0x87);
        let previous_outputs = (0..167)
            .map(|_| TxOut {
                value: Amount::from_sat(100_000),
                script_pubkey: ScriptBuf::from_bytes(p2sh_script.clone()),
            })
            .collect::<Vec<_>>();
        let mut redeem_script = vec![0x0f];
        redeem_script.extend([0xac; 15]);
        let transaction = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: (0..167)
                .map(|index| TxIn {
                    previous_output: OutPoint::new(Txid::from_byte_array([index as u8; 32]), 0),
                    script_sig: ScriptBuf::from_bytes(redeem_script.clone()),
                    sequence: bitcoin::Sequence::MAX,
                    witness: Witness::default(),
                })
                .collect(),
            output: vec![TxOut {
                value: Amount::from_sat(100_000),
                script_pubkey: ScriptBuf::from_bytes({
                    let mut bytes = vec![0x00, 0x14];
                    bytes.extend([0u8; 20]);
                    bytes
                }),
            }],
        };
        assert!(matches!(
            validate_standard_policy(&transaction, &previous_outputs, 1),
            Err(MempoolError::NonStandard(reason)) if reason == "bad-txns-nonstandard-inputs"
        ));
    }

    #[test]
    fn standard_policy_limits_total_sigop_cost() {
        let p2pkh = || {
            let mut bytes = vec![0x76, 0xa9, 0x14];
            bytes.extend([0u8; 20]);
            bytes.extend([0x88, 0xac]);
            ScriptBuf::from_bytes(bytes)
        };
        let witness_script = vec![0xac; 3_600];
        let previous_outputs = (0..5)
            .map(|_| TxOut {
                value: Amount::from_sat(100_000),
                script_pubkey: ScriptBuf::from_bytes({
                    let mut bytes = vec![0x00, 0x20];
                    bytes.extend([0u8; 32]);
                    bytes
                }),
            })
            .collect::<Vec<_>>();
        let transaction = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: (0..5)
                .map(|index| TxIn {
                    previous_output: OutPoint::new(Txid::from_byte_array([index as u8; 32]), 0),
                    script_sig: ScriptBuf::new(),
                    sequence: bitcoin::Sequence::MAX,
                    witness: Witness::from_slice(&[witness_script.as_slice()]),
                })
                .collect(),
            output: vec![TxOut {
                value: Amount::from_sat(100_000),
                script_pubkey: p2pkh(),
            }],
        };
        assert!(matches!(
            validate_standard_policy(&transaction, &previous_outputs, 1),
            Err(MempoolError::NonStandard(reason)) if reason == "bad-txns-too-many-sigops"
        ));
    }

    #[test]
    fn ephemeral_dust_must_be_spent_by_the_package_child() {
        let mut parent = graph_transaction(Txid::from_byte_array([10; 32]), 10);
        parent.input[0].script_sig = ScriptBuf::from_bytes(vec![0x00]);
        parent.output = vec![
            TxOut {
                value: Amount::from_sat(1),
                script_pubkey: ScriptBuf::from_bytes({
                    let mut bytes = vec![0x00, 0x14];
                    bytes.extend([0u8; 20]);
                    bytes
                }),
            },
            TxOut {
                value: Amount::from_sat(100_000),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            },
        ];
        let mut child = graph_transaction(parent.compute_txid(), 11);
        child.input[0].previous_output.vout = 1;
        let pool = Mempool::new(Network::Regtest);
        assert!(matches!(
            validate_ephemeral_spends(&[parent.clone(), child], &pool),
            Err(MempoolError::NonStandard(reason)) if reason == "missing-ephemeral-spends"
        ));

        let mut dust_child = graph_transaction(parent.compute_txid(), 12);
        dust_child.input[0].previous_output.vout = 0;
        assert!(validate_ephemeral_spends(&[parent, dust_child], &pool).is_ok());
    }
}
