//! Active-chain state, UTXO application, and Electrum indexing.

use std::collections::{HashMap, HashSet, VecDeque};
use std::fs;
use std::io::{Cursor, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::{
    Arc,
    atomic::{AtomicBool, AtomicU32, Ordering},
};
use std::thread;

use anyhow::{Context, Result, anyhow, bail};
use bincode::{deserialize as deserialize_binary, serialize as serialize_binary};
use bitcoin::bip158::{BlockFilter, FilterHeader};
use bitcoin::blockdata::constants::genesis_block;
use bitcoin::consensus::encode::{Decodable, VarInt, serialize};
use bitcoin::hashes::{Hash, HashEngine};
use bitcoin::pow::{CompactTarget, Target, Work};
use bitcoin::{
    Amount, Block, BlockHash, Network, OutPoint, Script, ScriptBuf, Transaction, TxOut, Txid,
    Witness,
};
use num_bigint::BigUint;
use parking_lot::Mutex;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use tracing::debug;

use crate::config::{
    DEFAULT_SCRIPT_CHECK_THREADS, MAX_SCRIPT_CHECK_THREADS, network_data_dir_name,
};
use crate::muhash::MuHash3072;
use crate::storage::{
    BlockStore, BlockStoreReader, ChainstateStore, CoinStatsRecord, CoinStatsStore,
    ElectrumBlockStore, ElectrumHistoryStore, FilterStore, StoredUtxo, UtxoStore,
};
use crate::validation::{self, ValidationError};

const COINBASE_MATURITY: u32 = 100;
const BIP34_IMPLIES_BIP30_LIMIT: u32 = 1_983_702;
const SNAPSHOT_INTERVAL: u32 = 1_000;
const MAX_UNDO_CACHE_ENTRIES: usize = 1_024;
const MAX_BASIC_FILTER_CACHE_ENTRIES: usize = 256;
const MAX_MISSING_UTXO_CACHE_ENTRIES: usize = 8_192;
// Core's default validation cache is 32 MiB. A compact 32-byte digest plus
// hash-table/deque bookkeeping is accounted for as roughly 64 bytes here.
const DEFAULT_SCRIPT_CACHE_ENTRIES: usize = (32 * 1024 * 1024) / 64;
const MIN_BLOCKS_TO_KEEP: u32 = 288;
const MIN_SUFFIX_ACTIVATION_BLOCKS: usize = 32;
const FAST_PRUNE_BLOCKFILE_SIZE: usize = 0x10_000;
const MAX_ORPHAN_BLOCKS: usize = 128;
const MAX_TIP_AGE_SECS: u64 = 24 * 60 * 60;
const MAX_UNSPENDABLE_SCRIPT_SIZE: usize = 10_000;
const CORE_UTXO_SNAPSHOT_MAGIC: [u8; 5] = [b'u', b't', b'x', b'o', 0xff];
const CORE_UTXO_SNAPSHOT_VERSION: u16 = 2;
const CHAIN_METADATA_MAGIC: &[u8] = b"bitcoind-rs-chainstate-v1\0";
const CHAIN_SNAPSHOT_MAGIC: &[u8] = b"bitcoind-rs-snapshot-v1\0";
const CHAINSTATE_DELTA_MAGIC: &[u8] = b"bitcoind-rs-chainstate-delta-v1\0";
const CHAIN_TX_COUNTS_MAGIC: &[u8] = b"bitcoind-rs-tx-counts-v1\0";
const ASSUMEUTXO_STATE_MAGIC: &[u8] = b"bitcoind-rs-assumeutxo-v1\0";
const ASSUMEUTXO_BASE_MAGIC: &[u8] = b"bitcoind-rs-assumeutxo-base-v1\0";
const ASSUMEUTXO_CHECKPOINT_MAGIC: &[u8] = b"bitcoind-rs-assumeutxo-checkpoint-v1\0";
const ASSUMEUTXO_CHECKPOINT_INTERVAL: u32 = 256;

fn merkle_branch_for_block(block: &Block, transaction_index: usize) -> Vec<Txid> {
    let mut layer: Vec<Txid> = block.txdata.iter().map(Transaction::compute_txid).collect();
    let mut index = transaction_index;
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
            let left = pair[0];
            let right = *pair.get(1).unwrap_or(&left);
            let mut engine = bitcoin::hashes::sha256d::Hash::engine();
            engine.input(&left.to_raw_hash().to_byte_array());
            engine.input(&right.to_raw_hash().to_byte_array());
            next.push(Txid::from_raw_hash(
                bitcoin::hashes::sha256d::Hash::from_engine(engine),
            ));
        }
        layer = next;
        index /= 2;
    }
    branch
}

#[derive(Clone, Copy)]
struct ChainTxData {
    time: i64,
    tx_count: u64,
    tx_rate: f64,
}

#[derive(Default)]
struct MissingUtxoCache {
    entries: HashSet<OutPoint>,
    order: VecDeque<OutPoint>,
}

impl MissingUtxoCache {
    fn contains(&self, outpoint: &OutPoint) -> bool {
        self.entries.contains(outpoint)
    }

    fn insert(&mut self, outpoint: OutPoint) {
        if !self.entries.insert(outpoint) {
            return;
        }
        self.order.push_back(outpoint);
        while self.order.len() > MAX_MISSING_UTXO_CACHE_ENTRIES {
            if let Some(oldest) = self.order.pop_front() {
                self.entries.remove(&oldest);
            }
        }
    }

    fn remove(&mut self, outpoint: &OutPoint) {
        if self.entries.remove(outpoint) {
            self.order.retain(|queued| queued != outpoint);
        }
    }
}

/// A hardcoded UTXO commitment from Bitcoin Core v31.1's chain parameters.
///
/// These values are deliberately kept as data rather than inferred from a
/// local chain. They are the trust anchor used by strict `loadtxoutset`
/// activation, just as Core uses its `AssumeutxoData` table.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AssumeUtxoData {
    pub height: u32,
    pub hash_serialized: &'static str,
    pub chain_tx_count: u64,
    pub blockhash: &'static str,
}

const MAINNET_ASSUMEUTXO: &[AssumeUtxoData] = &[
    AssumeUtxoData {
        height: 840_000,
        hash_serialized: "a2a5521b1b5ab65f67818e5e8eccabb7171a517f9e2382208f77687310768f96",
        chain_tx_count: 991_032_194,
        blockhash: "0000000000000000000320283a032748cef8227873ff4872689bf23f1cda83a5",
    },
    AssumeUtxoData {
        height: 880_000,
        hash_serialized: "dbd190983eaf433ef7c15f78a278ae42c00ef52e0fd2a54953782175fbadcea9",
        chain_tx_count: 1_145_604_538,
        blockhash: "000000000000000000010b17283c3c400507969a9c2afd1dcf2082ec5cca2880",
    },
    AssumeUtxoData {
        height: 910_000,
        hash_serialized: "4daf8a17b4902498c5787966a2b51c613acdab5df5db73f196fa59a4da2f1568",
        chain_tx_count: 1_226_586_151,
        blockhash: "0000000000000000000108970acb9522ffd516eae17acddcb1bd16469194a821",
    },
    AssumeUtxoData {
        height: 935_000,
        hash_serialized: "e4b90ef9eae834f56c4b64d2d50143cee10ad87994c614d7d04125e2a6025050",
        chain_tx_count: 1_305_397_408,
        blockhash: "0000000000000000000147034958af1652b2b91bba607beacc5e72a56f0fb5ee",
    },
];

const TESTNET_ASSUMEUTXO: &[AssumeUtxoData] = &[
    AssumeUtxoData {
        height: 2_500_000,
        hash_serialized: "f841584909f68e47897952345234e37fcd9128cd818f41ee6c3ca68db8071be7",
        chain_tx_count: 66_484_552,
        blockhash: "0000000000000093bcb68c03a9a168ae252572d348a2eaeba2cdf9231d73206f",
    },
    AssumeUtxoData {
        height: 4_840_000,
        hash_serialized: "ce6bb677bb2ee9789c4a1c9d73e6683c53fc20e8fdbedbdaaf468982a0c8db2a",
        chain_tx_count: 536_078_574,
        blockhash: "00000000000000f4971a7fb37fbdff89315b69a2e1920c467654a382f0d64786",
    },
];

const TESTNET4_ASSUMEUTXO: &[AssumeUtxoData] = &[
    AssumeUtxoData {
        height: 90_000,
        hash_serialized: "784fb5e98241de66fdd429f4392155c9e7db5c017148e66e8fdbc95746f8b9b5",
        chain_tx_count: 11_347_043,
        blockhash: "0000000002ebe8bcda020e0dd6ccfbdfac531d2f6a81457191b99fc2df2dbe3b",
    },
    AssumeUtxoData {
        height: 120_000,
        hash_serialized: "10b05d05ad468d0971162e1b222a4aa66caca89da2bb2a93f8f37fb29c4794b0",
        chain_tx_count: 14_141_057,
        blockhash: "000000000bd2317e51b3c5794981c35ba894ce27d3e772d5c39ecd9cbce01dc8",
    },
];

const DEFAULT_SIGNET_ASSUMEUTXO: &[AssumeUtxoData] = &[
    AssumeUtxoData {
        height: 160_000,
        hash_serialized: "fe0a44309b74d6b5883d246cb419c6221bcccf0b308c9b59b7d70783dbdf928a",
        chain_tx_count: 2_289_496,
        blockhash: "0000003ca3c99aff040f2563c2ad8f8ec88bd0fd6b8f0895cfaf1ef90353a62c",
    },
    AssumeUtxoData {
        height: 290_000,
        hash_serialized: "97267e000b4b876800167e71b9123f1529d13b14308abec2888bbd2160d14545",
        chain_tx_count: 28_547_497,
        blockhash: "0000000577f2741bb30cd9d39d6d71b023afbeb9764f6260786a97969d5c9ac0",
    },
];

const REGTEST_ASSUMEUTXO: &[AssumeUtxoData] = &[
    AssumeUtxoData {
        height: 110,
        hash_serialized: "b952555c8ab81fec46f3d4253b7af256d766ceb39fb7752b9d18cdf4a0141327",
        chain_tx_count: 111,
        blockhash: "6affe030b7965ab538f820a56ef56c8149b7dc1d1c144af57113be080db7c397",
    },
    AssumeUtxoData {
        height: 200,
        hash_serialized: "17dcc016d188d16068907cdeb38b75691a118d43053b8cd6a25969419381d13a",
        chain_tx_count: 201,
        blockhash: "385901ccbd69dff6bbd00065d01fb8a9e464dede7cfe0372443884f9b1dcf6b9",
    },
    AssumeUtxoData {
        height: 299,
        hash_serialized: "d2b051ff5e8eef46520350776f4100dd710a63447a8e01d917e92e79751a63e2",
        chain_tx_count: 334,
        blockhash: "7cc695046fec709f8c9394b6f928f81e81fd3ac20977bb68760fa1faa7916ea2",
    },
];

fn assumeutxo_data_for_network(network: Network) -> &'static [AssumeUtxoData] {
    match network {
        Network::Bitcoin => MAINNET_ASSUMEUTXO,
        Network::Testnet => TESTNET_ASSUMEUTXO,
        Network::Testnet4 => TESTNET4_ASSUMEUTXO,
        Network::Signet => DEFAULT_SIGNET_ASSUMEUTXO,
        Network::Regtest => REGTEST_ASSUMEUTXO,
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct UtxoEntry {
    pub output: TxOut,
    pub height: u32,
    pub median_time_past: u32,
    pub coinbase: bool,
}

trait UtxoLookup {
    fn contains(&self, outpoint: &OutPoint) -> Result<bool>;
    fn get(&self, outpoint: &OutPoint) -> Result<Option<UtxoEntry>>;
}

impl UtxoLookup for HashMap<OutPoint, UtxoEntry> {
    fn contains(&self, outpoint: &OutPoint) -> Result<bool> {
        Ok(self.contains_key(outpoint))
    }

    fn get(&self, outpoint: &OutPoint) -> Result<Option<UtxoEntry>> {
        Ok(HashMap::get(self, outpoint).cloned())
    }
}

impl UtxoLookup for UtxoStore {
    fn contains(&self, outpoint: &OutPoint) -> Result<bool> {
        Ok(UtxoStore::contains(self, outpoint))
    }

    fn get(&self, outpoint: &OutPoint) -> Result<Option<UtxoEntry>> {
        Ok(UtxoStore::get(self, outpoint)?.map(|entry| UtxoEntry {
            output: entry.output,
            height: entry.height,
            median_time_past: entry.median_time_past,
            coinbase: entry.coinbase,
        }))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct TxLocation {
    pub block_hash: BlockHash,
    pub height: u32,
    pub transaction_index: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ActiveTxLocation {
    height: u32,
    transaction_index: usize,
}

impl From<&TxLocation> for ActiveTxLocation {
    fn from(location: &TxLocation) -> Self {
        Self {
            height: location.height,
            transaction_index: location.transaction_index,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct HistoryEntry {
    pub txid: Txid,
    pub height: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ChainTip {
    pub hash: BlockHash,
    pub height: u32,
    pub work: Work,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BlockFeeStats {
    pub total_fee_sat: u64,
    pub transaction_fees_sat: Vec<u64>,
    pub spent_outputs: Vec<TxOut>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BasicFilterRange {
    pub stop_hash: BlockHash,
    pub previous_filter_header: FilterHeader,
    pub filters: Vec<(BlockHash, Vec<u8>, FilterHeader)>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct UtxoSetStats {
    pub transactions: usize,
    pub outputs: usize,
    pub total_amount_sat: u64,
    pub bogo_size: u64,
    pub serialized_hash: Option<String>,
    pub muhash: Option<String>,
    pub total_prevout_spent_sat: u64,
    pub total_new_outputs_ex_coinbase_sat: u64,
    pub total_coinbase_sat: u64,
    pub total_unspendable_genesis_sat: u64,
    pub total_unspendable_bip30_sat: u64,
    pub total_unspendable_scripts_sat: u64,
    pub total_unspendable_unclaimed_rewards_sat: u64,
}

#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
struct CoinStatsBlockMetrics {
    prevout_spent_sat: u64,
    new_outputs_ex_coinbase_sat: u64,
    coinbase_sat: u64,
    unspendable_scripts_sat: u64,
    unspendable_bip30_sat: u64,
    subsidy_sat: u64,
}

type SpentTransaction = (Txid, usize, BlockHash, u32);

#[derive(Clone, Default)]
struct CoinStatsState {
    transaction_outputs: HashMap<Txid, u64>,
    outputs: u64,
    total_amount_sat: u64,
    bogo_size: u64,
    muhash: MuHash3072,
    total_subsidy_sat: u64,
    total_prevout_spent_sat: u64,
    total_new_outputs_ex_coinbase_sat: u64,
    total_coinbase_sat: u64,
    total_unspendable_genesis_sat: u64,
    total_unspendable_bip30_sat: u64,
    total_unspendable_scripts_sat: u64,
    total_unspendable_unclaimed_rewards_sat: u64,
}

impl CoinStatsState {
    fn from_utxos(utxos: &HashMap<OutPoint, UtxoEntry>) -> Self {
        let mut state = Self::default();
        for (outpoint, entry) in utxos {
            state.add(outpoint, entry);
        }
        state
    }

    fn add(&mut self, outpoint: &OutPoint, entry: &UtxoEntry) {
        *self.transaction_outputs.entry(outpoint.txid).or_default() += 1;
        self.outputs = self.outputs.saturating_add(1);
        self.total_amount_sat = self
            .total_amount_sat
            .saturating_add(entry.output.value.to_sat());
        self.bogo_size = self.bogo_size.saturating_add(utxo_bogo_size(entry));
        self.muhash.insert(&serialize_utxo_coin(outpoint, entry));
    }

    fn remove(&mut self, outpoint: &OutPoint, entry: &UtxoEntry) {
        if let Some(count) = self.transaction_outputs.get_mut(&outpoint.txid) {
            *count = count.saturating_sub(1);
            if *count == 0 {
                self.transaction_outputs.remove(&outpoint.txid);
            }
        }
        self.outputs = self.outputs.saturating_sub(1);
        self.total_amount_sat = self
            .total_amount_sat
            .saturating_sub(entry.output.value.to_sat());
        self.bogo_size = self.bogo_size.saturating_sub(utxo_bogo_size(entry));
        self.muhash.remove(&serialize_utxo_coin(outpoint, entry));
    }

    fn record(&self, hash: BlockHash, height: u32) -> CoinStatsRecord {
        CoinStatsRecord {
            block_hash: hash,
            height,
            transactions: self.transaction_outputs.len() as u64,
            outputs: self.outputs,
            total_amount_sat: self.total_amount_sat,
            bogo_size: self.bogo_size,
            muhash: self.muhash.finalize(),
            total_subsidy_sat: self.total_subsidy_sat,
            total_prevout_spent_sat: self.total_prevout_spent_sat,
            total_new_outputs_ex_coinbase_sat: self.total_new_outputs_ex_coinbase_sat,
            total_coinbase_sat: self.total_coinbase_sat,
            total_unspendable_genesis_sat: self.total_unspendable_genesis_sat,
            total_unspendable_bip30_sat: self.total_unspendable_bip30_sat,
            total_unspendable_scripts_sat: self.total_unspendable_scripts_sat,
            total_unspendable_unclaimed_rewards_sat: self.total_unspendable_unclaimed_rewards_sat,
        }
    }

    fn apply_genesis(&mut self, network: Network) {
        let subsidy = validation::block_subsidy_for_network(network, 0);
        self.total_subsidy_sat = self.total_subsidy_sat.saturating_add(subsidy);
        self.total_unspendable_genesis_sat =
            self.total_unspendable_genesis_sat.saturating_add(subsidy);
    }

    fn apply_block_metrics(&mut self, metrics: CoinStatsBlockMetrics) {
        self.total_subsidy_sat = self.total_subsidy_sat.saturating_add(metrics.subsidy_sat);
        self.total_prevout_spent_sat = self
            .total_prevout_spent_sat
            .saturating_add(metrics.prevout_spent_sat);
        self.total_new_outputs_ex_coinbase_sat = self
            .total_new_outputs_ex_coinbase_sat
            .saturating_add(metrics.new_outputs_ex_coinbase_sat);
        self.total_coinbase_sat = self.total_coinbase_sat.saturating_add(metrics.coinbase_sat);
        self.total_unspendable_bip30_sat = self
            .total_unspendable_bip30_sat
            .saturating_add(metrics.unspendable_bip30_sat);
        self.total_unspendable_scripts_sat = self
            .total_unspendable_scripts_sat
            .saturating_add(metrics.unspendable_scripts_sat);
        let accounted = self
            .total_new_outputs_ex_coinbase_sat
            .saturating_add(self.total_coinbase_sat)
            .saturating_add(self.total_unspendable_genesis_sat)
            .saturating_add(self.total_unspendable_bip30_sat)
            .saturating_add(self.total_unspendable_scripts_sat)
            .saturating_add(self.total_unspendable_unclaimed_rewards_sat);
        let available = self
            .total_prevout_spent_sat
            .saturating_add(self.total_subsidy_sat);
        self.total_unspendable_unclaimed_rewards_sat = self
            .total_unspendable_unclaimed_rewards_sat
            .saturating_add(available.saturating_sub(accounted));
    }

    fn load_cumulative_from_record(&mut self, record: &CoinStatsRecord) {
        self.total_subsidy_sat = record.total_subsidy_sat;
        self.total_prevout_spent_sat = record.total_prevout_spent_sat;
        self.total_new_outputs_ex_coinbase_sat = record.total_new_outputs_ex_coinbase_sat;
        self.total_coinbase_sat = record.total_coinbase_sat;
        self.total_unspendable_genesis_sat = record.total_unspendable_genesis_sat;
        self.total_unspendable_bip30_sat = record.total_unspendable_bip30_sat;
        self.total_unspendable_scripts_sat = record.total_unspendable_scripts_sat;
        self.total_unspendable_unclaimed_rewards_sat =
            record.total_unspendable_unclaimed_rewards_sat;
    }

    fn statistics(&self, include_muhash: bool) -> UtxoSetStats {
        UtxoSetStats {
            transactions: self.transaction_outputs.len(),
            outputs: self.outputs as usize,
            total_amount_sat: self.total_amount_sat,
            bogo_size: self.bogo_size,
            serialized_hash: None,
            muhash: include_muhash.then(|| self.muhash.finalize()),
            total_prevout_spent_sat: self.total_prevout_spent_sat,
            total_new_outputs_ex_coinbase_sat: self.total_new_outputs_ex_coinbase_sat,
            total_coinbase_sat: self.total_coinbase_sat,
            total_unspendable_genesis_sat: self.total_unspendable_genesis_sat,
            total_unspendable_bip30_sat: self.total_unspendable_bip30_sat,
            total_unspendable_scripts_sat: self.total_unspendable_scripts_sat,
            total_unspendable_unclaimed_rewards_sat: self.total_unspendable_unclaimed_rewards_sat,
        }
    }
}

struct BlockApplication {
    spent_entries: Vec<(OutPoint, UtxoEntry)>,
    metrics: CoinStatsBlockMetrics,
}

/// Keep the most recently validated side-chain UTXO state so sequential
/// headers-first downloads do not replay the whole fork from genesis for
/// every body.  A single rolling entry is enough for the normal in-order
/// download path; callers fall back to full replay when a branch arrives out
/// of order.
struct SideChainUtxoCache {
    hash: BlockHash,
    utxos: HashMap<OutPoint, UtxoEntry>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KnownChainTip {
    pub hash: BlockHash,
    pub height: u32,
    pub branch_len: u32,
    pub status: &'static str,
    pub work: Work,
}

#[derive(Clone, Copy, Debug)]
struct BlockNode {
    header: bitcoin::block::Header,
    height: u32,
    chain_work: Work,
}

#[derive(Serialize, Deserialize)]
struct ChainMetadata {
    active_chain: Vec<String>,
    #[serde(default)]
    headers: Vec<bitcoin::block::Header>,
    #[serde(default)]
    invalid_blocks: Vec<String>,
    #[serde(default)]
    prune_height: Option<u32>,
    #[serde(default)]
    prune_locks: HashMap<String, PruneLock>,
    #[serde(default)]
    prune_protected_blocks: HashMap<String, u32>,
    /// Active-chain bodies that were accepted while SegWit consensus rules
    /// were enabled.  Core stores the equivalent BLOCK_OPT_WITNESS bit in
    /// each block-index entry; keeping the hashes here preserves that state
    /// without adopting Core's block-index database format.
    #[serde(default)]
    segwit_validated_blocks: Option<Vec<String>>,
}

#[derive(Deserialize)]
struct LegacyChainMetadata {
    active_chain: Vec<String>,
    #[serde(default)]
    headers: Vec<bitcoin::block::Header>,
    #[serde(default)]
    invalid_blocks: Vec<String>,
    #[serde(default)]
    prune_height: Option<u32>,
    #[serde(default)]
    prune_locks: HashMap<String, PruneLock>,
}

impl From<LegacyChainMetadata> for ChainMetadata {
    fn from(metadata: LegacyChainMetadata) -> Self {
        Self {
            active_chain: metadata.active_chain,
            headers: metadata.headers,
            invalid_blocks: metadata.invalid_blocks,
            prune_height: metadata.prune_height,
            prune_locks: metadata.prune_locks,
            prune_protected_blocks: HashMap::new(),
            segwit_validated_blocks: None,
        }
    }
}

/// A Core-style pruning lock. An unbounded upper height is represented by
/// `u64::MAX`, matching the way Core serializes an omitted range end.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PruneLock {
    pub desc: String,
    pub height_first: u64,
    pub height_last: u64,
    pub temporary: bool,
}

#[derive(Serialize, Deserialize)]
struct ChainSnapshot {
    tip: String,
    headers: Vec<bitcoin::block::Header>,
    utxos: HashMap<OutPoint, UtxoEntry>,
    tx_index: HashMap<Txid, TxLocation>,
    #[serde(default)]
    tx_index_all: HashMap<Txid, TxLocation>,
    history: HashMap<String, Vec<HistoryEntry>>,
    #[serde(default)]
    spent_by: Option<HashMap<OutPoint, SpentTransaction>>,
    #[serde(default)]
    prune_height: Option<u32>,
    #[serde(default)]
    tx_index_duplicates: HashMap<Txid, Vec<TxLocation>>,
}

#[derive(Serialize, Deserialize)]
struct LegacyChainSnapshot {
    tip: String,
    headers: Vec<bitcoin::block::Header>,
    utxos: HashMap<OutPoint, UtxoEntry>,
    tx_index: HashMap<Txid, TxLocation>,
    tx_index_all: HashMap<Txid, TxLocation>,
    history: HashMap<String, Vec<HistoryEntry>>,
    spent_by: Option<HashMap<OutPoint, SpentTransaction>>,
    prune_height: Option<u32>,
}

impl From<LegacyChainSnapshot> for ChainSnapshot {
    fn from(snapshot: LegacyChainSnapshot) -> Self {
        Self {
            tip: snapshot.tip,
            headers: snapshot.headers,
            utxos: snapshot.utxos,
            tx_index: snapshot.tx_index,
            tx_index_all: snapshot.tx_index_all,
            history: snapshot.history,
            spent_by: snapshot.spent_by,
            prune_height: snapshot.prune_height,
            tx_index_duplicates: HashMap::new(),
        }
    }
}

#[derive(Clone, Serialize, Deserialize)]
struct ChainstateDelta {
    block_hash: BlockHash,
    parent_hash: BlockHash,
    height: u32,
    spent: Vec<(OutPoint, UtxoEntry)>,
    created: Vec<(OutPoint, UtxoEntry)>,
    transactions: Vec<(Txid, TxLocation)>,
    history: Vec<(String, HistoryEntry)>,
    #[serde(default)]
    spent_by: Vec<(OutPoint, SpentTransaction)>,
    metrics: CoinStatsBlockMetrics,
}

#[derive(Serialize, Deserialize)]
struct StoredChainstateDelta {
    delta: ChainstateDelta,
    checksum: [u8; 32],
}

/// Compact active-chain metadata used by chain statistics after pruning.
/// Bitcoin Core keeps transaction counts in each `CBlockIndex`, so
/// `getchaintxstats` does not need the historical block bodies.  Keep this
/// in a separate sidecar instead of changing the existing metadata format so
/// older binary chainstate files remain readable.
#[derive(Serialize, Deserialize)]
struct ActiveTxCounts {
    active_tip: String,
    counts: Vec<u32>,
}

#[derive(Serialize, Deserialize)]
struct SnapshotProvenance {
    base_hash: String,
    #[serde(default)]
    validated: bool,
    #[serde(default)]
    failure: Option<String>,
}

#[derive(Serialize, Deserialize)]
struct AssumeUtxoBaseSnapshot {
    base_hash: String,
    utxos: HashMap<OutPoint, UtxoEntry>,
}

#[derive(Serialize, Deserialize)]
struct AssumeUtxoCheckpoint {
    base_hash: String,
    height: u32,
    block_hash: String,
    #[serde(default)]
    base_matches: Option<bool>,
    utxos: HashMap<OutPoint, UtxoEntry>,
}

#[derive(Debug)]
enum BackgroundValidationOutcome {
    Complete {
        target_tip: BlockHash,
        utxos: HashMap<OutPoint, UtxoEntry>,
        base_matches: bool,
    },
    Failed {
        target_tip: BlockHash,
        error: String,
        utxos: Option<HashMap<OutPoint, UtxoEntry>>,
    },
}

#[derive(Clone)]
struct BackgroundValidation {
    base_hash: BlockHash,
    cancel: Arc<AtomicBool>,
    progress: Arc<AtomicU32>,
    outcome: Arc<Mutex<Option<BackgroundValidationOutcome>>>,
}

struct BackgroundValidationJob {
    data_dir: PathBuf,
    blocks_dir: PathBuf,
    blocks_xor: bool,
    network: Network,
    signet_challenge: Option<Vec<u8>>,
    deployment_parameters: validation::DeploymentParameters,
    active_chain: Vec<BlockHash>,
    block_index: HashMap<BlockHash, BlockNode>,
    base_hash: BlockHash,
    base_height: u32,
    target_tip: BlockHash,
    script_check_workers: usize,
    script_cache_max_entries: usize,
    cancel: Arc<AtomicBool>,
}

struct ScriptCheckJob<'a> {
    tx_index: usize,
    transaction: &'a Transaction,
    previous_outputs: Vec<TxOut>,
}

struct ScriptValidationCache {
    entries: HashSet<[u8; 32]>,
    order: VecDeque<[u8; 32]>,
    max_entries: usize,
}

impl Default for ScriptValidationCache {
    fn default() -> Self {
        Self {
            entries: HashSet::new(),
            order: VecDeque::new(),
            max_entries: DEFAULT_SCRIPT_CACHE_ENTRIES,
        }
    }
}

impl ScriptValidationCache {
    fn with_max_entries(max_entries: usize) -> Self {
        Self {
            max_entries: max_entries.max(2),
            ..Self::default()
        }
    }
}

fn script_check_workers(par: i32) -> usize {
    let cores = thread::available_parallelism()
        .map(|cores| i32::try_from(cores.get()).unwrap_or(i32::MAX))
        .unwrap_or(1);
    let script_threads = if par <= 0 {
        par.saturating_add(cores)
    } else {
        par
    };
    script_threads.saturating_sub(1).clamp(
        0,
        i32::try_from(MAX_SCRIPT_CHECK_THREADS).unwrap_or(i32::MAX),
    ) as usize
}

fn serialize_internal<T: Serialize>(magic: &[u8], value: &T) -> Result<Vec<u8>> {
    let payload = serialize_binary(value).context("serializing internal chainstate")?;
    let mut bytes = Vec::with_capacity(magic.len() + payload.len());
    bytes.extend_from_slice(magic);
    bytes.extend_from_slice(&payload);
    Ok(bytes)
}

fn deserialize_internal<T: DeserializeOwned>(bytes: &[u8], magic: &[u8]) -> Result<T> {
    if !bytes.starts_with(magic) {
        bail!("internal chainstate format marker is invalid")
    }
    deserialize_binary(&bytes[magic.len()..]).context("decoding internal chainstate")
}

fn deserialize_chain_snapshot(bytes: &[u8]) -> Result<ChainSnapshot> {
    match deserialize_internal::<ChainSnapshot>(bytes, CHAIN_SNAPSHOT_MAGIC) {
        Ok(snapshot) => Ok(snapshot),
        Err(new_format_error) => {
            deserialize_internal::<LegacyChainSnapshot>(bytes, CHAIN_SNAPSHOT_MAGIC)
                .map(ChainSnapshot::from)
                .with_context(|| {
                    format!("decoding chainstate snapshot (new format: {new_format_error})")
                })
        }
    }
}

fn serialize_chainstate_delta(delta: &ChainstateDelta) -> Result<Vec<u8>> {
    let body = serialize_binary(delta).context("serializing chainstate delta body")?;
    let stored = StoredChainstateDelta {
        delta: delta.clone(),
        checksum: Sha256::digest(&body).into(),
    };
    serialize_internal(CHAINSTATE_DELTA_MAGIC, &stored)
}

fn deserialize_chainstate_delta(bytes: &[u8]) -> Result<ChainstateDelta> {
    let stored: StoredChainstateDelta = deserialize_internal(bytes, CHAINSTATE_DELTA_MAGIC)?;
    let body = serialize_binary(&stored.delta).context("serializing stored chainstate delta")?;
    if Sha256::digest(&body).as_slice() != stored.checksum {
        bail!("chainstate delta checksum mismatch")
    }
    Ok(stored.delta)
}

fn load_active_tx_counts(data_dir: &Path, active_chain: &[BlockHash]) -> Result<Option<Vec<u32>>> {
    let path = data_dir.join("chainstate.txcounters");
    if !path.exists() {
        return Ok(None);
    }
    let bytes = fs::read(&path)
        .with_context(|| format!("reading transaction-count index {}", path.display()))?;
    let index: ActiveTxCounts = deserialize_internal(&bytes, CHAIN_TX_COUNTS_MAGIC)
        .with_context(|| format!("decoding transaction-count index {}", path.display()))?;
    let Some(active_tip) = active_chain.last() else {
        return Ok(None);
    };
    let stored_tip = active_tip
        .to_string()
        .eq_ignore_ascii_case(&index.active_tip);
    if !stored_tip || index.counts.len() != active_chain.len() {
        return Ok(None);
    }
    Ok(Some(index.counts))
}

fn cumulative_tx_counts(counts: &[u32]) -> Vec<u64> {
    let mut total = 0u64;
    counts
        .iter()
        .map(|count| {
            total = total.saturating_add(u64::from(*count));
            total
        })
        .collect()
}

fn load_snapshot_provenance(path: &Path) -> Result<SnapshotProvenance> {
    let bytes = fs::read(path)
        .with_context(|| format!("reading AssumeUTXO provenance {}", path.display()))?;
    deserialize_internal(&bytes, ASSUMEUTXO_STATE_MAGIC)
        .with_context(|| format!("decoding AssumeUTXO provenance {}", path.display()))
}

pub struct ChainState {
    pub network: Network,
    data_dir: PathBuf,
    blocks_dir: PathBuf,
    blocks_xor: bool,
    minimum_chain_work_override: Option<Work>,
    assume_valid_block: Option<BlockHash>,
    max_tip_age_secs: u64,
    script_check_workers: usize,
    script_checks_enabled: bool,
    signet_challenge: Option<Vec<u8>>,
    deployment_parameters: validation::DeploymentParameters,
    pub store: BlockStore,
    electrum_store: Option<ElectrumBlockStore>,
    filter_store: FilterStore,
    chainstate_store: ChainstateStore,
    utxo_store: UtxoStore,
    missing_utxo_cache: Mutex<MissingUtxoCache>,
    electrum_history_store: ElectrumHistoryStore,
    blockfilter_index_enabled: bool,
    tx_index_all_enabled: bool,
    coinstats_store: CoinStatsStore,
    txospender_index_enabled: bool,
    coinstats_index_enabled: bool,
    coin_stats: Option<CoinStatsState>,
    active_chain: Vec<BlockHash>,
    segwit_validated_blocks: HashSet<BlockHash>,
    headers: Vec<bitcoin::block::Header>,
    // Electrum checkpoint proofs are requested repeatedly while a client
    // downloads a header chain. Cache the materialized tree for the current
    // header prefix and checkpoint so each proof only walks the tree height
    // and extending the checkpoint only updates the new right-hand path.
    header_merkle_cache: Mutex<Option<HeaderMerkleCache>>,
    active_tx_counts: Vec<u32>,
    active_tx_totals: Vec<u64>,
    initial_block_download: bool,
    max_tip_age_configured: bool,
    snapshot_base: Option<BlockHash>,
    snapshot_validated: bool,
    snapshot_validation_error: Option<String>,
    background_validation: Option<BackgroundValidation>,
    block_index: HashMap<BlockHash, BlockNode>,
    // Core's candidate ordering uses a memory-only sequence ID after
    // chainwork.  Keep the same ordering for equal-work forks; this is not
    // persisted because Core resets the active chain to zero on restart.
    block_sequence_ids: HashMap<BlockHash, u64>,
    next_block_sequence_id: u64,
    // Preserve the arrival order of bodies whose parent data is not yet
    // available. Core replays these bodies in insertion order when the
    // missing parent arrives, which determines equal-work chain selection.
    unlinked_body_order: HashMap<BlockHash, u64>,
    next_unlinked_body_order: u64,
    // Core keeps the first header seen at a given chainwork.  This arrival
    // order is runtime-only; restart initialization below provides neutral
    // values for headers whose original order was not persisted.
    header_sequence_ids: HashMap<BlockHash, u64>,
    next_header_sequence_id: u64,
    orphans: HashMap<BlockHash, Vec<Block>>,
    invalid_blocks: HashSet<BlockHash>,
    prune_height: Option<u32>,
    prune_locks: HashMap<String, PruneLock>,
    // Bodies fetched again after pruning live in the current block file in
    // Core. Keep them protected until the file's height range is old enough
    // to be pruned, rather than dropping them solely by block height.
    prune_protected_blocks: HashMap<BlockHash, u32>,
    prune_mode: bool,
    prune_target_size: Option<u64>,
    prune_after_height: u32,
    fast_prune: bool,
    utxos: HashMap<OutPoint, UtxoEntry>,
    utxos_materialized: bool,
    side_chain_utxos: Option<SideChainUtxoCache>,
    tx_index: HashMap<Txid, ActiveTxLocation>,
    // Most txids have one active-chain location. Keep duplicate locations
    // separately so the Core-style txindex remains a latest-location map
    // while Electrum can return the earliest occurrence.
    tx_index_duplicates: HashMap<Txid, Vec<ActiveTxLocation>>,
    tx_index_all: HashMap<Txid, TxLocation>,
    history: HashMap<String, Vec<HistoryEntry>>,
    history_materialized: bool,
    spent_by: HashMap<OutPoint, SpentTransaction>,
    // Core stores preciousblock preferences as negative reverse sequence IDs.
    // They are runtime-only and are intentionally not persisted.
    precious_blocks: HashMap<BlockHash, i32>,
    precious_sequence: i32,
    precious_last_chainwork: Option<Work>,
    basic_filter_cache: HashMap<BlockHash, (Vec<u8>, FilterHeader)>,
    block_undo_cache: HashMap<BlockHash, Vec<Vec<TxOut>>>,
    script_cache: Mutex<ScriptValidationCache>,
}

struct HeaderMerkleCache {
    checkpoint_hash: BlockHash,
    checkpoint: u32,
    levels: Vec<Vec<BlockHash>>,
}

impl HeaderMerkleCache {
    fn from_hashes(
        checkpoint_hash: BlockHash,
        checkpoint: u32,
        hashes: Vec<BlockHash>,
    ) -> Result<Self> {
        if hashes.is_empty() {
            bail!("cannot build an empty header proof");
        }
        let mut levels = vec![hashes];
        while levels.last().is_some_and(|layer| layer.len() > 1) {
            let layer = levels.last().expect("header merkle layer exists");
            let mut next = Vec::with_capacity(layer.len().div_ceil(2));
            for pair in layer.chunks(2) {
                let right = *pair.get(1).unwrap_or(&pair[0]);
                next.push(combine_header_hashes(pair[0], right));
            }
            levels.push(next);
        }
        Ok(Self {
            checkpoint_hash,
            checkpoint,
            levels,
        })
    }

    fn append_hash(&mut self, hash: BlockHash) {
        self.levels[0].push(hash);
        let mut level = 1;
        loop {
            let lower = &self.levels[level - 1];
            let lower_len = lower.len();
            let parent = if lower_len % 2 == 0 {
                combine_header_hashes(lower[lower_len - 2], lower[lower_len - 1])
            } else {
                combine_header_hashes(lower[lower_len - 1], lower[lower_len - 1])
            };
            let desired_len = lower_len.div_ceil(2);
            if level == self.levels.len() {
                self.levels.push(Vec::new());
            }
            let last_level = self.levels.len() - 1;
            let is_root = {
                let current = &mut self.levels[level];
                if current.len() < desired_len {
                    current.push(parent);
                } else {
                    *current
                        .last_mut()
                        .expect("header merkle layer has a parent") = parent;
                }
                level == last_level && current.len() == 1
            };
            if is_root {
                break;
            }
            level += 1;
        }
        self.checkpoint = self.checkpoint.saturating_add(1);
        self.checkpoint_hash = hash;
    }

    fn proof(&self, height: u32) -> Result<(Vec<BlockHash>, BlockHash)> {
        let mut index =
            usize::try_from(height).map_err(|_| anyhow!("header height is too large"))?;
        let leaves = self
            .levels
            .first()
            .context("header merkle cache has no leaves")?;
        if index >= leaves.len() {
            bail!("header height exceeds checkpoint")
        }
        let mut branch = Vec::with_capacity(self.levels.len().saturating_sub(1));
        for layer in self.levels.iter().take_while(|layer| layer.len() > 1) {
            let sibling = if index ^ 1 < layer.len() {
                index ^ 1
            } else {
                index
            };
            branch.push(layer[sibling]);
            index /= 2;
        }
        let root = *self
            .levels
            .last()
            .and_then(|layer| layer.first())
            .context("header merkle cache has no root")?;
        Ok((branch, root))
    }
}

pub(crate) fn combine_header_hashes(left: BlockHash, right: BlockHash) -> BlockHash {
    let mut bytes = [0u8; 64];
    bytes[..32].copy_from_slice(&left.to_byte_array());
    bytes[32..].copy_from_slice(&right.to_byte_array());
    BlockHash::from_raw_hash(bitcoin::hashes::sha256d::Hash::hash(&bytes))
}

#[cfg(test)]
pub(crate) fn header_merkle_proof_from_hashes(
    hashes: &[BlockHash],
    height: u32,
) -> Result<(Vec<BlockHash>, BlockHash)> {
    if hashes.is_empty() {
        bail!("cannot build an empty header proof");
    }
    let mut layer = hashes.to_vec();
    let mut index = usize::try_from(height).map_err(|_| anyhow!("header height is too large"))?;
    if index >= layer.len() {
        bail!("header height exceeds checkpoint");
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

impl ChainState {
    pub fn open(network: Network, data_dir: impl AsRef<Path>) -> Result<Self> {
        Self::open_with_signet_challenge(network, data_dir, None)
    }

    pub fn open_with_signet_challenge(
        network: Network,
        data_dir: impl AsRef<Path>,
        signet_challenge: Option<&[u8]>,
    ) -> Result<Self> {
        Self::open_with_signet_challenge_and_filter_index(network, data_dir, signet_challenge, true)
    }

    pub fn open_with_signet_challenge_and_filter_index(
        network: Network,
        data_dir: impl AsRef<Path>,
        signet_challenge: Option<&[u8]>,
        blockfilter_index_enabled: bool,
    ) -> Result<Self> {
        Self::open_with_options(
            network,
            data_dir,
            signet_challenge,
            blockfilter_index_enabled,
            false,
            false,
        )
    }

    pub fn open_with_options(
        network: Network,
        data_dir: impl AsRef<Path>,
        signet_challenge: Option<&[u8]>,
        blockfilter_index_enabled: bool,
        reindex: bool,
        reindex_chainstate: bool,
    ) -> Result<Self> {
        Self::open_with_options_and_tx_index(
            network,
            data_dir,
            signet_challenge,
            blockfilter_index_enabled,
            reindex,
            reindex_chainstate,
            true,
        )
    }

    /// Open chainstate with optional side-chain transaction indexing.
    ///
    /// The active-chain transaction map is always retained because it powers
    /// Electrum, REST, merkle proofs, and block metadata.  The second map is
    /// only needed for Core's optional `-txindex` lookup of transactions that
    /// are not currently active; avoiding it is a substantial memory saving
    /// for ordinary node and Electrum deployments.
    pub fn open_with_options_and_tx_index(
        network: Network,
        data_dir: impl AsRef<Path>,
        signet_challenge: Option<&[u8]>,
        blockfilter_index_enabled: bool,
        reindex: bool,
        reindex_chainstate: bool,
        tx_index_all_enabled: bool,
    ) -> Result<Self> {
        let data_dir = data_dir.as_ref();
        Self::open_with_options_and_tx_index_in_dirs(
            network,
            data_dir,
            data_dir.join("blocks"),
            signet_challenge,
            blockfilter_index_enabled,
            reindex,
            reindex_chainstate,
            tx_index_all_enabled,
        )
    }

    /// Open chainstate with block records stored in a separate directory.
    /// Metadata, indexes, and chainstate remain rooted in `data_dir`, matching
    /// Core's `-blocksdir` layout.
    #[allow(clippy::too_many_arguments)]
    pub fn open_with_options_and_tx_index_in_dirs(
        network: Network,
        data_dir: impl AsRef<Path>,
        blocks_dir: impl AsRef<Path>,
        signet_challenge: Option<&[u8]>,
        blockfilter_index_enabled: bool,
        reindex: bool,
        reindex_chainstate: bool,
        tx_index_all_enabled: bool,
    ) -> Result<Self> {
        Self::open_with_options_and_tx_index_in_dirs_with_minimum_chain_work(
            network,
            data_dir,
            blocks_dir,
            signet_challenge,
            blockfilter_index_enabled,
            reindex,
            reindex_chainstate,
            tx_index_all_enabled,
            None,
        )
    }

    /// Open chainstate with a Core-style minimum-chainwork override.
    #[allow(clippy::too_many_arguments)]
    pub fn open_with_options_and_tx_index_in_dirs_with_minimum_chain_work(
        network: Network,
        data_dir: impl AsRef<Path>,
        blocks_dir: impl AsRef<Path>,
        signet_challenge: Option<&[u8]>,
        blockfilter_index_enabled: bool,
        reindex: bool,
        reindex_chainstate: bool,
        tx_index_all_enabled: bool,
        minimum_chain_work_override: Option<Work>,
    ) -> Result<Self> {
        Self::open_with_options_and_tx_index_in_dirs_with_minimum_chain_work_and_assume_valid(
            network,
            data_dir,
            blocks_dir,
            signet_challenge,
            blockfilter_index_enabled,
            reindex,
            reindex_chainstate,
            tx_index_all_enabled,
            minimum_chain_work_override,
            None,
        )
    }

    /// Open chainstate with Core-style minimum-chainwork and assume-valid
    /// overrides.
    #[allow(clippy::too_many_arguments)]
    pub fn open_with_options_and_tx_index_in_dirs_with_minimum_chain_work_and_assume_valid(
        network: Network,
        data_dir: impl AsRef<Path>,
        blocks_dir: impl AsRef<Path>,
        signet_challenge: Option<&[u8]>,
        blockfilter_index_enabled: bool,
        reindex: bool,
        reindex_chainstate: bool,
        tx_index_all_enabled: bool,
        minimum_chain_work_override: Option<Work>,
        assume_valid_block: Option<BlockHash>,
    ) -> Result<Self> {
        Self::open_with_options_and_tx_index_in_dirs_with_minimum_chain_work_and_assume_valid_and_blocks_xor(
            network,
            data_dir,
            blocks_dir,
            signet_challenge,
            blockfilter_index_enabled,
            reindex,
            reindex_chainstate,
            tx_index_all_enabled,
            minimum_chain_work_override,
            assume_valid_block,
            false,
        )
    }

    /// Open chainstate with Core-style chainwork, assume-valid, and blocksdir
    /// XOR configuration.
    #[allow(clippy::too_many_arguments)]
    pub fn open_with_options_and_tx_index_in_dirs_with_minimum_chain_work_and_assume_valid_and_blocks_xor(
        network: Network,
        data_dir: impl AsRef<Path>,
        blocks_dir: impl AsRef<Path>,
        signet_challenge: Option<&[u8]>,
        blockfilter_index_enabled: bool,
        reindex: bool,
        reindex_chainstate: bool,
        tx_index_all_enabled: bool,
        minimum_chain_work_override: Option<Work>,
        assume_valid_block: Option<BlockHash>,
        blocks_xor: bool,
    ) -> Result<Self> {
        Self::open_with_options_and_tx_index_in_dirs_with_minimum_chain_work_and_assume_valid_and_blocks_xor_and_deployment_parameters(
            network,
            data_dir,
            blocks_dir,
            signet_challenge,
            blockfilter_index_enabled,
            reindex,
            reindex_chainstate,
            tx_index_all_enabled,
            minimum_chain_work_override,
            assume_valid_block,
            blocks_xor,
            validation::DeploymentParameters::for_network(network),
        )
    }

    /// Open chainstate with explicit consensus deployment parameters.
    #[allow(clippy::too_many_arguments)]
    pub fn open_with_options_and_tx_index_in_dirs_with_minimum_chain_work_and_assume_valid_and_blocks_xor_and_deployment_parameters(
        network: Network,
        data_dir: impl AsRef<Path>,
        blocks_dir: impl AsRef<Path>,
        signet_challenge: Option<&[u8]>,
        blockfilter_index_enabled: bool,
        reindex: bool,
        reindex_chainstate: bool,
        tx_index_all_enabled: bool,
        minimum_chain_work_override: Option<Work>,
        assume_valid_block: Option<BlockHash>,
        blocks_xor: bool,
        deployment_parameters: validation::DeploymentParameters,
    ) -> Result<Self> {
        if deployment_parameters.network != network {
            bail!("consensus deployment parameters use a different network");
        }
        let data_dir = data_dir.as_ref().to_owned();
        let blocks_dir = blocks_dir.as_ref().to_owned();
        fs::create_dir_all(&data_dir)
            .with_context(|| format!("creating chain data directory {}", data_dir.display()))?;
        let mut store = BlockStore::open_with_xor(&blocks_dir, blocks_xor)?;
        let filter_store = FilterStore::open(data_dir.join("filters"))?;
        let coinstats_store = CoinStatsStore::open(data_dir.join("indexes/coinstatsindex"))?;
        let genesis = genesis_block(network);
        let genesis_hash = genesis.block_hash();
        if !store.contains(&genesis_hash) {
            store.insert(&genesis)?;
        }

        let metadata_path = data_dir.join("chainstate.bin");
        let legacy_metadata_path = data_dir.join("chainstate.json");
        let snapshot_provenance_path = data_dir.join("assumeutxo.bin");
        let rebuild_chainstate = reindex || reindex_chainstate;
        let chainstate_path = data_dir.join("chainstate");
        if rebuild_chainstate {
            match fs::remove_dir_all(&chainstate_path) {
                Ok(()) => {}
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Err(error) => {
                    return Err(error).with_context(|| {
                        format!("removing reindex state {}", chainstate_path.display())
                    });
                }
            }
        }
        let chainstate_store = ChainstateStore::open(&chainstate_path)?;
        let utxo_store = UtxoStore::open(chainstate_path.join("utxos"))?;
        let electrum_history_store =
            ElectrumHistoryStore::open(data_dir.join("indexes/electrum-history"))?;
        if rebuild_chainstate {
            // Reindex rebuilds the UTXO/chainstate data, but Core keeps the
            // block-index headers that describe pruned ancestors.  Preserve
            // our equivalent metadata so a pruned block store can still
            // connect newly supplied bodies after the rebuild.
            for path in [
                data_dir.join("chainstate.snapshot"),
                data_dir.join("chainstate.snapshot.sha256"),
                data_dir.join("chainstate.txcounters"),
                snapshot_provenance_path.clone(),
            ] {
                match fs::remove_file(&path) {
                    Ok(()) => {}
                    Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                    Err(error) => {
                        return Err(error)
                            .with_context(|| format!("removing reindex state {}", path.display()));
                    }
                }
            }
        }
        let (
            active_chain,
            persisted_headers,
            invalid_blocks,
            prune_height,
            prune_locks,
            prune_protected_blocks,
            persisted_segwit_validated_blocks,
        ) = if metadata_path.exists() || legacy_metadata_path.exists() {
            let metadata = if metadata_path.exists() {
                let bytes = fs::read(&metadata_path)
                    .with_context(|| format!("reading {}", metadata_path.display()))?;
                match deserialize_internal::<ChainMetadata>(&bytes, CHAIN_METADATA_MAGIC) {
                    Ok(metadata) => metadata,
                    Err(new_format_error) => {
                        deserialize_internal::<LegacyChainMetadata>(&bytes, CHAIN_METADATA_MAGIC)
                            .map(ChainMetadata::from)
                            .with_context(|| {
                                format!(
                                    "decoding {} (new format: {new_format_error})",
                                    metadata_path.display()
                                )
                            })?
                    }
                }
            } else {
                let bytes = fs::read(&legacy_metadata_path)
                    .with_context(|| format!("reading {}", legacy_metadata_path.display()))?;
                serde_json::from_slice(&bytes)
                    .with_context(|| format!("decoding {}", legacy_metadata_path.display()))?
            };
            let metadata: ChainMetadata = metadata;
            let active_chain = metadata
                .active_chain
                .into_iter()
                .map(|hash| {
                    hash.parse()
                        .with_context(|| format!("invalid block hash {hash}"))
                })
                .collect::<Result<Vec<BlockHash>>>()?;
            let invalid_blocks = metadata
                .invalid_blocks
                .into_iter()
                .map(|hash| {
                    hash.parse()
                        .with_context(|| format!("invalid invalidated block hash {hash}"))
                })
                .collect::<Result<HashSet<BlockHash>>>()?;
            let prune_protected_blocks = metadata
                .prune_protected_blocks
                .into_iter()
                .map(|(hash, height)| {
                    hash.parse()
                        .map(|hash| (hash, height))
                        .with_context(|| format!("invalid protected pruned block hash {hash}"))
                })
                .collect::<Result<HashMap<BlockHash, u32>>>()?;
            let persisted_segwit_validated_blocks = metadata
                .segwit_validated_blocks
                .map(|blocks| {
                    blocks
                        .into_iter()
                        .map(|hash| {
                            hash.parse().with_context(|| {
                                format!("invalid SegWit-validated block hash {hash}")
                            })
                        })
                        .collect::<Result<HashSet<BlockHash>>>()
                })
                .transpose()?;
            (
                active_chain,
                metadata.headers,
                invalid_blocks,
                metadata.prune_height,
                metadata.prune_locks,
                prune_protected_blocks,
                persisted_segwit_validated_blocks,
            )
        } else {
            (
                vec![genesis_hash],
                Vec::new(),
                HashSet::new(),
                None,
                HashMap::new(),
                HashMap::new(),
                None,
            )
        };
        let persisted_tx_counts = if rebuild_chainstate {
            None
        } else {
            load_active_tx_counts(&data_dir, &active_chain)?
        };
        let persisted_tx_totals = persisted_tx_counts
            .as_deref()
            .map(cumulative_tx_counts)
            .unwrap_or_default();
        let persisted_snapshot_provenance =
            if !rebuild_chainstate && snapshot_provenance_path.exists() {
                Some(load_snapshot_provenance(&snapshot_provenance_path)?)
            } else {
                None
            };
        if active_chain.first().copied() != Some(genesis_hash) {
            bail!("chainstate does not start at the configured network genesis block");
        }

        // Core refuses to start when the active chain contains blocks at or
        // above a newly enabled SegWit height that were previously accepted
        // by a pre-SegWit validation path.  The block-index database carries
        // this information in BLOCK_OPT_WITNESS; native storage keeps the
        // equivalent set in chainstate metadata.
        if !rebuild_chainstate
            && let Some(validated_blocks) = persisted_segwit_validated_blocks.as_ref()
            && active_chain
                .iter()
                .enumerate()
                .skip(
                    usize::try_from(deployment_parameters.buried.segwit)
                        .unwrap_or(usize::MAX)
                        .max(1),
                )
                .any(|(_, hash)| !validated_blocks.contains(hash))
        {
            return Err(
                crate::CoreStartupError::witness(deployment_parameters.buried.segwit).into(),
            );
        }

        // A full reindex rebuilds the block index from bodies that may have
        // been stored before SegWit was enabled.  Those bodies remain on
        // disk, but Core deliberately leaves the first insufficiently
        // witnessed suffix disconnected so it can be redownloaded.  Keep
        // the same boundary while retaining all native block records.
        let reindex_witness_tip = if rebuild_chainstate {
            persisted_segwit_validated_blocks
                .as_ref()
                .and_then(|validated| {
                    active_chain
                        .iter()
                        .enumerate()
                        .skip(
                            usize::try_from(deployment_parameters.buried.segwit)
                                .unwrap_or(usize::MAX)
                                .max(1),
                        )
                        .find_map(|(height, hash)| {
                            (!validated.contains(hash))
                                .then(|| height.checked_sub(1))
                                .flatten()
                                .and_then(|height| active_chain.get(height).copied())
                        })
                })
        } else {
            None
        };

        let mut state = Self {
            network,
            data_dir,
            blocks_dir,
            blocks_xor,
            minimum_chain_work_override,
            assume_valid_block,
            max_tip_age_secs: MAX_TIP_AGE_SECS,
            script_check_workers: script_check_workers(DEFAULT_SCRIPT_CHECK_THREADS),
            script_checks_enabled: script_check_workers(DEFAULT_SCRIPT_CHECK_THREADS) > 0,
            signet_challenge: (network == Network::Signet).then(|| {
                signet_challenge
                    .map(ToOwned::to_owned)
                    .unwrap_or_else(validation::default_signet_challenge)
            }),
            deployment_parameters,
            store,
            electrum_store: None,
            filter_store,
            chainstate_store,
            utxo_store,
            missing_utxo_cache: Mutex::new(MissingUtxoCache::default()),
            electrum_history_store,
            blockfilter_index_enabled,
            tx_index_all_enabled,
            coinstats_store,
            txospender_index_enabled: false,
            coinstats_index_enabled: false,
            coin_stats: None,
            active_chain: Vec::new(),
            segwit_validated_blocks: persisted_segwit_validated_blocks
                .clone()
                .unwrap_or_default(),
            headers: Vec::new(),
            header_merkle_cache: Mutex::new(None),
            active_tx_counts: persisted_tx_counts.unwrap_or_default(),
            active_tx_totals: persisted_tx_totals,
            initial_block_download: true,
            max_tip_age_configured: false,
            snapshot_base: persisted_snapshot_provenance
                .as_ref()
                .map(|provenance| provenance.base_hash.parse())
                .transpose()
                .context("decoding AssumeUTXO snapshot base hash")?,
            snapshot_validated: persisted_snapshot_provenance
                .as_ref()
                .is_some_and(|provenance| provenance.validated),
            snapshot_validation_error: persisted_snapshot_provenance
                .as_ref()
                .and_then(|provenance| provenance.failure.clone()),
            background_validation: None,
            block_index: HashMap::new(),
            block_sequence_ids: HashMap::new(),
            next_block_sequence_id: 1,
            unlinked_body_order: HashMap::new(),
            next_unlinked_body_order: 1,
            header_sequence_ids: HashMap::new(),
            next_header_sequence_id: 1,
            orphans: HashMap::new(),
            invalid_blocks,
            prune_height,
            prune_locks,
            prune_protected_blocks,
            prune_mode: false,
            prune_target_size: None,
            // Keep the direct ChainState API's historical test behavior until
            // the owning Node applies the network-specific Core parameter.
            prune_after_height: MIN_BLOCKS_TO_KEEP,
            fast_prune: false,
            utxos: HashMap::new(),
            utxos_materialized: true,
            side_chain_utxos: None,
            tx_index: HashMap::new(),
            tx_index_duplicates: HashMap::new(),
            tx_index_all: HashMap::new(),
            history: HashMap::new(),
            history_materialized: true,
            spent_by: HashMap::new(),
            precious_blocks: HashMap::new(),
            precious_sequence: -1,
            precious_last_chainwork: None,
            basic_filter_cache: HashMap::new(),
            block_undo_cache: HashMap::new(),
            script_cache: Mutex::new(ScriptValidationCache::default()),
        };
        let snapshot = if rebuild_chainstate {
            None
        } else {
            state.load_snapshot(&active_chain)?
        };
        let loaded_snapshot = snapshot.is_some();
        let snapshot_verified = snapshot.as_ref().is_some_and(|(_, verified)| *verified);
        if rebuild_chainstate {
            state.initialize_genesis(&genesis)?;
            state.index_persisted_headers(&persisted_headers)?;
            state.rebuild_block_index()?;
            // The optional Core-style txindex is independent of the active
            // chainstate.  Reindexing deliberately removes the snapshot that
            // normally carries this map, so rebuild it from the native block
            // records before replaying the selected best chain.  This keeps
            // side-chain getrawtransaction lookups intact without creating a
            // Core block-index or blk*/rev* storage file.
            state.rebuild_transaction_index()?;
            let best = state
                .best_valid_tip_hash()
                .context("reindex found no valid chain tip")?;
            let best = reindex_witness_tip
                .filter(|hash| state.block_index.contains_key(hash))
                .unwrap_or(best);
            if best != state.network_genesis_hash() {
                state.activate_chain(best)?;
            }
        } else if let Some((snapshot, _)) = snapshot {
            let snapshot_chain_len = snapshot.headers.len();
            state.active_chain = active_chain[..snapshot_chain_len].to_vec();
            state.headers = snapshot.headers;
            state.utxos = snapshot.utxos;
            let snapshot_tx_index = snapshot.tx_index;
            state.tx_index = snapshot_tx_index
                .iter()
                .map(|(txid, location)| (*txid, ActiveTxLocation::from(location)))
                .collect();
            state.tx_index_duplicates = snapshot
                .tx_index_duplicates
                .into_iter()
                .map(|(txid, locations)| {
                    (txid, locations.iter().map(ActiveTxLocation::from).collect())
                })
                .collect();
            state.tx_index_all = if state.tx_index_all_enabled {
                if snapshot.tx_index_all.is_empty() {
                    snapshot_tx_index.into_iter().collect()
                } else {
                    snapshot.tx_index_all
                }
            } else {
                HashMap::new()
            };
            state.history = snapshot.history;
            state.history_materialized = true;
            state.prune_height = snapshot.prune_height.or(state.prune_height);
            let persisted_spent_by = snapshot.spent_by;
            state.active_tx_counts.truncate(snapshot_chain_len);
            state.active_tx_totals.truncate(snapshot_chain_len);
            let headers = state.headers.clone();
            state.index_active_headers(&headers)?;
            if state.txospender_index_enabled {
                if let Some(spent_by) = persisted_spent_by {
                    state.spent_by = spent_by;
                    state.validate_persisted_spent_index()?;
                } else {
                    state.rebuild_spent_index()?;
                }
            } else {
                state.spent_by.clear();
            }
            state.index_persisted_headers(&persisted_headers)?;
            let deltas = state.load_chainstate_deltas(&active_chain, snapshot_chain_len);
            if let Some(deltas) =
                deltas.filter(|deltas| state.validate_chainstate_deltas(deltas).is_ok())
            {
                for delta in deltas {
                    state.apply_chainstate_delta(delta)?;
                }
            } else {
                for hash in active_chain.iter().skip(snapshot_chain_len) {
                    let block = state.store.get(hash)?.with_context(|| {
                        format!("active block {hash} is missing from block store")
                    })?;
                    state.connect_block_internal(&block, false)?;
                }
            }
        } else {
            state.snapshot_base = None;
            state.snapshot_validated = true;
            state.snapshot_validation_error = None;
            state.active_tx_counts.clear();
            state.active_tx_totals.clear();
            let mut blocks = Vec::with_capacity(active_chain.len());
            for hash in &active_chain {
                let block = state
                    .store
                    .get(hash)?
                    .with_context(|| format!("active block {hash} is missing from block store"))?;
                blocks.push(block);
            }
            state.initialize_genesis(&blocks[0])?;
            for block in blocks.iter().skip(1) {
                state.connect_block_internal(block, false)?;
            }
        }
        if state.active_tx_counts.len() != state.active_chain.len() {
            state.active_tx_counts = state.tx_counts_from_index().unwrap_or_default();
        }
        if state.active_tx_counts.len() != state.active_chain.len() && state.prune_height.is_none()
        {
            state.rebuild_active_tx_counts()?;
        }
        state.active_tx_totals = cumulative_tx_counts(&state.active_tx_counts);
        if !rebuild_chainstate && state.active_chain != active_chain {
            bail!("chainstate metadata does not match replayed active chain");
        }
        if loaded_snapshot
            && state.snapshot_base.is_some_and(|base| {
                !state.is_active_block(&base)
                    && (state.snapshot_validated || state.snapshot_validation_error.is_some())
            })
        {
            bail!("AssumeUTXO snapshot base is not on the active chain");
        }
        if !loaded_snapshot {
            state.snapshot_base = None;
            state.snapshot_validated = true;
            state.snapshot_validation_error = None;
            state.remove_snapshot_provenance_file()?;
        }
        state.index_persisted_headers(&persisted_headers)?;
        state.rebuild_block_index()?;
        state.initialize_block_sequence_ids_after_load();
        if state
            .active_chain
            .iter()
            .any(|hash| state.invalid_blocks.contains(hash))
        {
            let best_valid = state
                .best_valid_tip_hash()
                .context("invalidated chain has no valid alternative")?;
            state.activate_chain(best_valid)?;
            state.initialize_block_sequence_ids_after_load();
        }
        if loaded_snapshot {
            let snapshot_utxos = state.utxos.clone();
            let pending_assumeutxo = state.snapshot_base.is_some()
                && !state.snapshot_validated
                && state.snapshot_validation_error.is_none();
            if pending_assumeutxo {
                let snapshot_height = state
                    .snapshot_base
                    .and_then(|base| state.block_height_by_hash(&base))
                    .unwrap_or_else(|| state.height());
                state.validate_snapshot_utxo_shape(&snapshot_utxos, snapshot_height)?;
            } else {
                state.validate_snapshot_utxos(&snapshot_utxos)?;
            }
            if !pending_assumeutxo && !snapshot_verified {
                if state.prune_height.is_none() {
                    let expected = state
                        .replay_utxos_for_block(state.best_hash(), false)?
                        .context("cannot verify persisted chainstate snapshot")?;
                    if expected != state.utxos {
                        bail!("persisted chainstate snapshot does not match the active chain");
                    }
                }
                state.persist_snapshot_checksum()?;
            }
        }
        state.reconcile_utxo_store()?;
        state.reconcile_electrum_history_store()?;
        state.update_ibd_status();
        state.persist_metadata()?;
        if state.snapshot_base.is_some()
            && !state.snapshot_validated
            && state.snapshot_validation_error.is_none()
        {
            state.start_background_validation()?;
        }
        state.release_materialized_utxos();
        state.release_materialized_history();
        Ok(state)
    }

    pub fn tip(&self) -> ChainTip {
        let hash = *self.active_chain.last().expect("genesis is always active");
        let node = self.block_index.get(&hash).expect("active tip is indexed");
        ChainTip {
            hash,
            height: node.height,
            work: node.chain_work,
        }
    }

    /// Return the chainstate tip used for UTXO-serving RPCs. During
    /// AssumeUTXO activation the normal chain may still end below the
    /// snapshot base while the snapshot chainstate serves coins at its base
    /// header.
    pub fn utxo_tip(&self) -> ChainTip {
        let tip = self.tip();
        let Some(base_hash) = self.snapshot_base.filter(|_| !self.snapshot_validated) else {
            return tip;
        };
        let Some(base) = self.block_index.get(&base_hash).copied() else {
            return tip;
        };
        if tip.height >= base.height {
            tip
        } else {
            ChainTip {
                hash: base_hash,
                height: base.height,
                work: base.chain_work,
            }
        }
    }

    /// Extend the active header chain to a loaded AssumeUTXO base without
    /// requiring the historical block bodies between the ordinary tip and
    /// that base.  The snapshot UTXOs already represent the base state, so
    /// forward block bodies can connect directly on top of it.
    fn promote_snapshot_chain_to_base(&mut self) -> Result<()> {
        let Some(base_hash) = self.snapshot_base.filter(|_| !self.snapshot_validated) else {
            return Ok(());
        };
        if self.is_active_block(&base_hash) {
            return Ok(());
        }
        let Some(base_node) = self.block_index.get(&base_hash).copied() else {
            return Ok(());
        };
        let current_height = self.height();
        if base_node.height <= current_height
            || self.ancestor_hash(base_hash, current_height) != Some(self.best_hash())
        {
            return Ok(());
        }

        let mut path = Vec::with_capacity(base_node.height as usize + 1);
        let mut cursor = base_hash;
        loop {
            path.push(cursor);
            if cursor == self.network_genesis_hash() {
                break;
            }
            let Some(node) = self.block_index.get(&cursor) else {
                return Ok(());
            };
            cursor = node.header.prev_blockhash;
        }
        path.reverse();
        let old_len = self.active_chain.len();
        if path.len() < old_len || path[..old_len] != self.active_chain[..] {
            return Ok(());
        }

        for hash in path.iter().skip(old_len) {
            let header = self
                .block_index
                .get(hash)
                .context("snapshot base header is not indexed")?
                .header;
            self.headers.push(header);
        }
        self.active_chain = path;
        self.active_tx_counts.resize(self.active_chain.len(), 0);
        self.active_tx_totals = cumulative_tx_counts(&self.active_tx_counts);
        self.persist_metadata()?;
        self.persist_snapshot()?;
        self.update_ibd_status();
        Ok(())
    }

    pub fn height(&self) -> u32 {
        self.active_chain.len().saturating_sub(1) as u32
    }

    /// Verify the block-index parent links, chain-work accumulation, active
    /// chain vectors, and persisted transaction-count accounting.
    pub fn check_consistency(&self) -> Result<()> {
        if self.active_chain.is_empty() {
            bail!("chain active chain is empty");
        }
        if self.active_chain.first().copied() != Some(self.network_genesis_hash()) {
            bail!("chain active chain does not begin at genesis");
        }
        if self.headers.len() != self.active_chain.len()
            || self.active_tx_counts.len() != self.active_chain.len()
            || self.active_tx_totals.len() != self.active_chain.len()
        {
            bail!(
                "chain active vectors have inconsistent lengths (chain={}, headers={}, tx_counts={}, tx_totals={})",
                self.active_chain.len(),
                self.headers.len(),
                self.active_tx_counts.len(),
                self.active_tx_totals.len()
            );
        }

        let mut cumulative_transactions = 0u64;
        for (height, hash) in self.active_chain.iter().enumerate() {
            let node = self
                .block_index
                .get(hash)
                .with_context(|| format!("active chain is missing block index entry {hash}"))?;
            let height_u32 = u32::try_from(height).context("active chain height exceeds u32")?;
            if node.height != height_u32 {
                bail!(
                    "active chain height mismatch for {hash}: index {}, vector {height}",
                    node.height
                );
            }
            if node.header.block_hash() != *hash
                || self.headers[height].block_hash() != *hash
                || self.headers[height] != node.header
            {
                bail!("active chain header mismatch for {hash}");
            }
            if height > 0 {
                let parent_hash = self.active_chain[height - 1];
                if node.header.prev_blockhash != parent_hash {
                    bail!("active chain parent mismatch for {hash}");
                }
                let parent = self
                    .block_index
                    .get(&parent_hash)
                    .context("active chain parent is missing from block index")?;
                if node.chain_work != parent.chain_work + node.header.work() {
                    bail!("active chain work mismatch for {hash}");
                }
            }
            cumulative_transactions =
                cumulative_transactions.saturating_add(u64::from(self.active_tx_counts[height]));
            if self.active_tx_totals[height] != cumulative_transactions {
                bail!("active chain transaction total mismatch at height {height}");
            }
        }

        for (hash, node) in &self.block_index {
            if node.header.block_hash() != *hash {
                bail!("block index key does not match its header hash: {hash}");
            }
            if node.height == 0 {
                if *hash != self.network_genesis_hash() {
                    bail!("non-genesis block index entry has height zero: {hash}");
                }
                continue;
            }
            let parent = self
                .block_index
                .get(&node.header.prev_blockhash)
                .with_context(|| format!("block index parent is missing for {hash}"))?;
            if node.height != parent.height.saturating_add(1)
                || node.chain_work != parent.chain_work + node.header.work()
            {
                bail!("block index linkage or work mismatch for {hash}");
            }
        }
        if self
            .invalid_blocks
            .iter()
            .any(|hash| !self.block_index.contains_key(hash))
        {
            bail!("invalid-block set contains an unknown block");
        }
        Ok(())
    }

    pub fn prune_height(&self) -> Option<u32> {
        self.prune_height
    }

    pub fn is_pruned(&self) -> bool {
        self.prune_mode || self.prune_height.is_some()
    }

    /// Return whether the block body was removed by pruning.
    ///
    /// A block-index entry can outlive its body for two different reasons:
    /// the body may never have been downloaded, or it may have been removed
    /// by pruning. RPCs use this distinction to match Core's diagnostics.
    pub fn is_block_pruned(&self, hash: &BlockHash) -> bool {
        self.prune_height.is_some_and(|prune_height| {
            self.block_height_by_hash(hash).is_some_and(|height| {
                if height >= prune_height {
                    return false;
                }
                // A body fetched again after pruning is written into the
                // current file and remains available until a later prune
                // removes that file.  Core can also prune the file which
                // contains genesis, even though this implementation keeps
                // a compact copy in blocks.dat for chain initialization.
                let refetched = self.prune_protected_blocks.contains_key(hash);
                !refetched && (!self.store.contains(hash) || height == 0)
            })
        })
    }

    /// Return whether the node must advertise limited historical block
    /// service. Core keeps NODE_NETWORK disabled while an AssumeUTXO
    /// background chainstate is validating, even when explicit prune mode is
    /// off.
    pub fn is_network_limited(&self) -> bool {
        self.is_pruned() || (self.snapshot_base.is_some() && !self.snapshot_validated)
    }

    pub fn prune_target_size(&self) -> Option<u64> {
        self.prune_target_size
    }

    pub fn prune_locks(&self) -> Vec<(String, PruneLock)> {
        let mut locks = self
            .prune_locks
            .iter()
            .map(|(id, lock)| (id.clone(), lock.clone()))
            .collect::<Vec<_>>();
        locks.sort_by(|(left, _), (right, _)| left.cmp(right));
        locks
    }

    /// Add, replace, or remove a pruning lock and persist non-temporary
    /// changes with the chain metadata. Deleting `*` succeeds even when no
    /// locks are currently installed, as in Core.
    pub fn set_prune_lock(&mut self, id: &str, lock: Option<PruneLock>) -> Result<bool> {
        let success = if let Some(lock) = lock {
            if id == "*" {
                bail!("id \"*\" only makes sense when deleting")
            }
            self.prune_locks.insert(id.to_owned(), lock);
            true
        } else if id == "*" {
            self.prune_locks.clear();
            true
        } else {
            self.prune_locks.remove(id).is_some()
        };
        self.persist_metadata()?;
        Ok(success)
    }

    /// Apply Core's network-specific minimum chain height for pruning. The
    /// debug-only fast-prune mode changes regtest's threshold from 1000 to
    /// 100, as in Core v31.1.
    pub fn configure_prune_after_height(&mut self, network: Network, fast_prune: bool) {
        self.fast_prune = fast_prune;
        self.prune_after_height = match network {
            Network::Bitcoin => 100_000,
            Network::Regtest if fast_prune => 100,
            Network::Regtest | Network::Testnet | Network::Testnet4 | Network::Signet => 1_000,
        };
    }

    fn fast_prune_boundary(&mut self, requested_height: u32) -> Result<Option<u32>> {
        let mut file_size = 0usize;
        let mut first_retained = None;
        let start_height = usize::try_from(self.prune_height.unwrap_or_default()).unwrap_or(0);
        let end_height = usize::try_from(requested_height).unwrap_or(usize::MAX);
        if start_height > end_height {
            return Ok(None);
        }
        // Core writes a body fetched again through getblockfrompeer at the
        // current tip, rather than restoring it to its original block file.
        // That extra record can move a later 64 KiB file boundary by one or
        // more blocks. Preserve the fetch height and replay the append here.
        let mut refetched = self
            .prune_protected_blocks
            .iter()
            .map(|(hash, height)| (*height, *hash))
            .collect::<Vec<_>>();
        refetched.sort_by_key(|(height, _)| *height);
        for (height, hash) in self
            .active_chain
            .iter()
            .enumerate()
            .skip(start_height)
            .take(end_height.saturating_sub(start_height).saturating_add(1))
        {
            let height = u32::try_from(height).context("active chain height does not fit u32")?;
            let Some(block) = self.store.get(hash)? else {
                break;
            };
            let block_size = serialize(&block).len().saturating_add(8);
            if file_size != 0 && file_size.saturating_add(block_size) >= FAST_PRUNE_BLOCKFILE_SIZE {
                if height <= requested_height {
                    first_retained = Some(height);
                }
                file_size = 0;
            }
            file_size = file_size.saturating_add(block_size);

            for (_, refetched_hash) in refetched
                .iter()
                .filter(|(fetch_height, _)| *fetch_height == height)
            {
                let Some(refetched_block) = self.store.get(refetched_hash)? else {
                    continue;
                };
                let refetched_size = serialize(&refetched_block).len().saturating_add(8);
                if file_size != 0
                    && file_size.saturating_add(refetched_size) >= FAST_PRUNE_BLOCKFILE_SIZE
                {
                    let boundary = height.saturating_add(1);
                    if boundary <= requested_height {
                        first_retained = Some(boundary);
                    }
                    file_size = 0;
                }
                file_size = file_size.saturating_add(refetched_size);
            }
        }
        Ok(first_retained.or_else(|| {
            (start_height > 0).then(|| u32::try_from(start_height).unwrap_or(u32::MAX))
        }))
    }

    /// Return the first active block for which Core would enable script
    /// verification. Validation during startup runs before the logging
    /// subscriber is installed, so the daemon uses this to replay the first
    /// visible reindex transition into debug.log.
    pub fn first_script_verification_reason(&self) -> Option<(u32, BlockHash, &'static str)> {
        for (height, hash) in self.active_chain.iter().copied().enumerate().skip(1) {
            let Ok(height) = u32::try_from(height) else {
                break;
            };
            let Ok(Some(block)) = self.store.get_readonly(&hash) else {
                continue;
            };
            if let Some(reason) = self.script_check_reason(&block, height) {
                return Some((height, hash, reason));
            }
        }
        None
    }

    pub fn blockfilter_index_enabled(&self) -> bool {
        self.blockfilter_index_enabled
    }

    pub fn coinstats_index_enabled(&self) -> bool {
        self.coinstats_index_enabled
    }

    /// Return the estimated on-disk footprint of the active UTXO database,
    /// matching Core's `gettxoutsetinfo` `disk_size` field. Other durable
    /// metadata and historical mutation logs are not part of that estimate.
    pub fn utxo_disk_size(&self) -> Result<u64> {
        self.utxo_store.disk_usage()
    }

    pub fn txospender_index_enabled(&self) -> bool {
        self.txospender_index_enabled
    }

    /// Enable or disable the durable transaction-output spender index.
    /// Rebuilding it is independent from the active UTXO set and therefore
    /// remains useful for historical `gettxspendingprevout` queries.
    pub fn configure_txospender_index(&mut self, enabled: bool) -> Result<()> {
        self.txospender_index_enabled = enabled;
        if enabled {
            self.rebuild_spent_index()?;
        } else {
            self.spent_by.clear();
        }
        Ok(())
    }

    /// Enable the durable transaction-body sidecar required by the in-process
    /// Electrum service when pruning is active. An unpruned node already has
    /// every authoritative block body in `BlockStore`, so creating the
    /// sidecar there would duplicate all transaction data for no benefit.
    /// The sidecar is intentionally separate from Core's txindex: only
    /// block-hash keyed bodies are retained, and normal block serving
    /// continues to respect pruning.
    pub fn configure_electrum_index(&mut self, enabled: bool) -> Result<()> {
        if !enabled {
            self.electrum_store = None;
            return Ok(());
        }
        if !self.is_pruned() {
            self.electrum_store = None;
            return Ok(());
        }
        let mut store = ElectrumBlockStore::open(self.data_dir.join("indexes/electrum"))?;
        for hash in self.active_chain.clone() {
            if store.contains(&hash) {
                continue;
            }
            if let Some(block) = self.store.get(&hash)? {
                store.insert(&block)?;
            }
        }
        self.electrum_store = Some(store);
        Ok(())
    }

    /// Enable or disable the durable coinstats index. Enabling it builds any
    /// missing active-chain records in one forward pass, then keeps the live
    /// accumulator current as blocks connect.
    pub fn configure_coinstats_index(&mut self, enabled: bool) -> Result<()> {
        self.coinstats_index_enabled = enabled;
        if !enabled {
            self.coin_stats = None;
            self.prune_locks.remove("coinstatsindex");
            return Ok(());
        }
        let utxos = if self.utxos_materialized {
            self.utxos.clone()
        } else {
            self.load_utxo_map_from_store()?
        };
        self.coin_stats = Some(CoinStatsState::from_utxos(&utxos));
        self.rebuild_coinstats_index()?;
        self.update_index_prune_locks(self.height());
        Ok(())
    }

    pub fn coinstats_at(
        &mut self,
        hash: &BlockHash,
        include_muhash: bool,
    ) -> Result<Option<(u32, UtxoSetStats)>> {
        if let Some(record) = self.coinstats_store.get(hash)?
            && self.block_height_by_hash(hash) == Some(record.height)
        {
            return Ok(Some((
                record.height,
                UtxoSetStats {
                    transactions: record.transactions as usize,
                    outputs: record.outputs as usize,
                    total_amount_sat: record.total_amount_sat,
                    bogo_size: record.bogo_size,
                    serialized_hash: None,
                    muhash: include_muhash.then_some(record.muhash),
                    total_prevout_spent_sat: record.total_prevout_spent_sat,
                    total_new_outputs_ex_coinbase_sat: record.total_new_outputs_ex_coinbase_sat,
                    total_coinbase_sat: record.total_coinbase_sat,
                    total_unspendable_genesis_sat: record.total_unspendable_genesis_sat,
                    total_unspendable_bip30_sat: record.total_unspendable_bip30_sat,
                    total_unspendable_scripts_sat: record.total_unspendable_scripts_sat,
                    total_unspendable_unclaimed_rewards_sat: record
                        .total_unspendable_unclaimed_rewards_sat,
                },
            )));
        }

        let Some(height) = self.block_height_by_hash(hash) else {
            return Ok(None);
        };
        let mut path = Vec::with_capacity(height as usize + 1);
        let mut cursor = *hash;
        loop {
            path.push(cursor);
            if cursor == self.network_genesis_hash() {
                break;
            }
            let Some(header) = self.header_by_hash(&cursor) else {
                return Ok(None);
            };
            cursor = header.prev_blockhash;
        }
        path.reverse();

        let mut stats = CoinStatsState::default();
        let mut utxos = HashMap::new();
        for (height, block_hash) in path.into_iter().enumerate() {
            let Some(block) = self.store.get(&block_hash)? else {
                return Ok(None);
            };
            apply_block_to_coin_stats(
                self.network,
                &mut utxos,
                &mut stats,
                &block,
                u32::try_from(height).context("coinstats height does not fit u32")?,
            );
        }
        Ok(Some((height, stats.statistics(include_muhash))))
    }

    /// Apply the startup pruning mode from the node configuration.
    pub fn configure_pruning(&mut self, requested: u64) -> Result<()> {
        if requested == 0 && self.prune_height.is_some() {
            bail!(
                "The data directory contains pruned blocks; restart with --prune or rebuild with reindex."
            );
        }
        self.prune_mode = requested != 0;
        self.prune_target_size = if requested > 1 {
            Some(
                requested
                    .checked_mul(1024 * 1024)
                    .context("prune target is too large")?,
            )
        } else {
            None
        };
        if !self.blockfilter_index_enabled {
            self.prune_locks.remove("basic block filter index");
        }
        if !self.coinstats_index_enabled {
            self.prune_locks.remove("coinstatsindex");
        }
        self.update_index_prune_locks(self.height());
        Ok(())
    }

    pub fn validate_persisted_indices_against_pruning(
        &mut self,
        coinstats_index_enabled: bool,
    ) -> Result<()> {
        let Some(prune_height) = self.prune_height else {
            return Ok(());
        };
        if self.blockfilter_index_enabled {
            let best_height = self
                .active_chain
                .iter()
                .enumerate()
                .rev()
                .find_map(|(height, hash)| {
                    self.filter_store
                        .get(hash)
                        .ok()
                        .flatten()
                        .map(|_| u32::try_from(height).unwrap_or(u32::MAX))
                })
                .unwrap_or_default();
            if best_height < prune_height {
                bail!(
                    "basic block filter index best block of the index goes beyond pruned data (including undo data). Please disable the index or reindex (which will download the whole blockchain again)"
                );
            }
        }
        if coinstats_index_enabled {
            let best_height = self
                .active_chain
                .iter()
                .enumerate()
                .rev()
                .find_map(|(height, hash)| {
                    self.coinstats_store
                        .get(hash)
                        .ok()
                        .flatten()
                        .map(|_| u32::try_from(height).unwrap_or(u32::MAX))
                })
                .unwrap_or_default();
            if best_height < prune_height {
                bail!(
                    "coinstatsindex best block of the index goes beyond pruned data (including undo data). Please disable the index or reindex (which will download the whole blockchain again)"
                );
            }
        }
        Ok(())
    }

    fn update_index_prune_locks(&mut self, height: u32) {
        if !self.prune_mode {
            return;
        }
        if self.blockfilter_index_enabled {
            self.prune_locks.insert(
                "basic block filter index".to_owned(),
                PruneLock {
                    desc: "basic block filter index".to_owned(),
                    height_first: u64::from(height),
                    height_last: u64::MAX,
                    temporary: false,
                },
            );
        }
        if self.coinstats_index_enabled {
            self.prune_locks.insert(
                "coinstatsindex".to_owned(),
                PruneLock {
                    desc: "coinstatsindex".to_owned(),
                    height_first: u64::from(height),
                    height_last: u64::MAX,
                    temporary: false,
                },
            );
        }
    }

    /// Prune automatically when the configured block/undo target is
    /// exceeded. Keeping the recent block window is the same safety boundary
    /// used by manual pruning and leaves enough data for ordinary reorgs.
    pub fn maybe_auto_prune(&mut self) -> Result<bool> {
        let Some(target_size) = self.prune_target_size else {
            return Ok(false);
        };
        // Core's snapshot chainstate keeps the historical block range needed
        // by background validation until that validation completes.  This
        // block store is record-based rather than Core's block-file layout,
        // so it cannot represent the same discontiguous prune range without
        // making the contiguous prune-height metadata lie.  Defer pruning
        // until the snapshot is validated instead.
        if self.snapshot_base.is_some() && !self.snapshot_validated {
            return Ok(false);
        }
        if self.height() <= self.prune_after_height {
            return Ok(false);
        }
        if self.store.disk_usage()? <= target_size {
            return Ok(false);
        }
        let maximum_height = self.height().saturating_sub(MIN_BLOCKS_TO_KEEP);
        if maximum_height == 0
            || self
                .prune_height
                .is_some_and(|previous| previous >= maximum_height)
        {
            return Ok(false);
        }
        self.prune(u64::from(maximum_height))?;
        Ok(true)
    }

    /// Permanently remove old block and undo records while retaining enough
    /// recent history for normal reorg handling. The active chainstate is
    /// snapshotted before returning so a pruned node can restart without the
    /// removed block bodies.
    pub fn prune(&mut self, requested: u64) -> Result<u32> {
        // The historical chain must remain available while an AssumeUTXO
        // snapshot is being validated in the background.  Returning the
        // current boundary is the same observable no-op as Core's prune
        // range when no block file falls entirely outside that protected
        // prefix.
        if self.snapshot_base.is_some() && !self.snapshot_validated {
            return Ok(self.prune_height.unwrap_or_default());
        }
        let tip_height = self.height();
        if tip_height < self.prune_after_height {
            bail!("Blockchain is too short for pruning.");
        }
        let requested_height = if requested > 1_000_000_000 {
            let target_time = requested.saturating_sub(2 * 60 * 60);
            let target_time = u32::try_from(target_time).unwrap_or(u32::MAX);
            self.headers
                .iter()
                .position(|header| header.time >= target_time)
                .map(|height| height as u32)
                .context("Could not find block with at least the specified timestamp.")?
        } else {
            u32::try_from(requested).context("block height is too large")?
        };
        if requested_height > tip_height {
            bail!("Blockchain is shorter than the attempted prune height.");
        }
        let mut target_height = requested_height.min(tip_height - MIN_BLOCKS_TO_KEEP);
        for lock in self.prune_locks.values() {
            if lock.height_first == u64::MAX {
                continue;
            }
            let lock_height = u32::try_from(lock.height_first.saturating_sub(11))
                .unwrap_or(u32::MAX)
                .max(1);
            if lock_height < tip_height {
                debug!("{} limited pruning to height {lock_height}", lock.desc);
                target_height = target_height.min(lock_height);
            }
        }
        if self.fast_prune {
            let Some(file_boundary) = self.fast_prune_boundary(target_height)? else {
                return Ok(self.prune_height.unwrap_or_default());
            };
            target_height = file_boundary;
        }
        if let Some(previous) = self.prune_height
            && target_height <= previous
        {
            return Ok(previous);
        }
        // The genesis block is retained permanently, so a boundary at
        // height 1 would not have removed any block data yet.
        if target_height <= 1 {
            return Ok(self.prune_height.unwrap_or_default());
        }

        let stored_hashes = self.store.hashes().copied().collect::<HashSet<_>>();
        let retained_blocks = self
            .block_index
            .iter()
            .filter_map(|(hash, node)| {
                let protected = self
                    .prune_protected_blocks
                    .get(hash)
                    .is_some_and(|height| *height >= target_height);
                (stored_hashes.contains(hash)
                    && (node.height == 0 || node.height >= target_height || protected))
                    .then_some(*hash)
            })
            .collect::<HashSet<_>>();
        self.store.prune(&retained_blocks, &retained_blocks)?;
        self.prune_height = Some(target_height);
        self.prune_protected_blocks
            .retain(|hash, height| *height >= target_height && retained_blocks.contains(hash));
        self.persist_metadata()?;
        self.persist_snapshot()?;
        Ok(target_height)
    }

    pub fn best_hash(&self) -> BlockHash {
        self.tip().hash
    }

    pub fn best_header_tip(&self) -> ChainTip {
        self.block_index
            .iter()
            .filter(|(hash, _)| !self.has_invalid_ancestor(**hash))
            .max_by(|(left_hash, left), (right_hash, right)| {
                left.chain_work
                    .cmp(&right.chain_work)
                    .then_with(|| {
                        self.header_sequence_id(right_hash)
                            .cmp(&self.header_sequence_id(left_hash))
                    })
                    .then_with(|| right_hash.to_string().cmp(&left_hash.to_string()))
            })
            .map(|(hash, node)| ChainTip {
                hash: *hash,
                height: node.height,
                work: node.chain_work,
            })
            .expect("genesis header is indexed")
    }

    /// Estimate validation progress using Core's ChainTxData model.
    ///
    /// Core uses the cumulative transaction count at the active tip rather
    /// than chainwork for this RPC value.  When the tip's timestamp is recent
    /// and the best known header extends it, the estimate uses the expected
    /// block spacing so the value reaches exactly 1.0 for a synchronized tip.
    pub fn verification_progress(&self) -> f64 {
        self.verification_progress_at(crate::time::unix_time_i64())
    }

    fn verification_progress_at(&self, now: i64) -> f64 {
        self.verification_progress_for_height(self.height(), now)
    }

    /// Estimate verification progress for the chainstate tip at `height`.
    ///
    /// Core's `getchainstates` calls `GuessVerificationProgress` separately
    /// for the active and historical chainstate tips. The transaction-count
    /// model is shared with `getblockchaininfo`, but the height must remain
    /// explicit for the background AssumeUTXO chainstate.
    pub fn verification_progress_for_height(&self, height: u32, now: i64) -> f64 {
        let Some(chain_tx_count) = self.chain_transaction_count(height) else {
            return 0.0;
        };
        if chain_tx_count == 0 {
            return 0.0;
        }

        let tip_header = self
            .header(height)
            .expect("active tip header is always indexed");
        let best_header = self.best_header_tip();
        let spacing = i64::try_from(self.network.params().pow_target_spacing).unwrap_or(i64::MAX);
        let block_time = if best_header.height >= height
            && now.abs_diff(i64::from(tip_header.time)) <= 2 * 60 * 60
        {
            now.saturating_sub(
                i64::from(best_header.height.saturating_sub(height)).saturating_mul(spacing),
            )
        } else {
            i64::from(tip_header.time)
        };

        let data = self.chain_tx_data();
        let total = if chain_tx_count <= data.tx_count {
            data.tx_count as f64 + (now - data.time) as f64 * data.tx_rate
        } else {
            chain_tx_count as f64 + (now - block_time) as f64 * data.tx_rate
        };
        (chain_tx_count as f64 / total).min(1.0)
    }

    fn chain_tx_data(&self) -> ChainTxData {
        if self.network == Network::Signet
            && self.signet_challenge.as_deref()
                != Some(validation::default_signet_challenge().as_slice())
        {
            return ChainTxData {
                time: 0,
                tx_count: 0,
                tx_rate: 0.0,
            };
        }
        match self.network {
            Network::Bitcoin => ChainTxData {
                time: 1_772_055_173,
                tx_count: 1_315_805_869,
                tx_rate: 5.401_110_064_961_22,
            },
            Network::Testnet => ChainTxData {
                time: 1_772_051_651,
                tx_count: 536_108_416,
                tx_rate: 0.026_914_790_162_571_17,
            },
            Network::Testnet4 => ChainTxData {
                time: 1_772_013_387,
                tx_count: 14_191_421,
                tx_rate: 0.018_485_795_795_284_12,
            },
            Network::Signet => ChainTxData {
                time: 1_772_055_248,
                tx_count: 28_676_833,
                tx_rate: 0.067_366_234_363_389_29,
            },
            Network::Regtest => ChainTxData {
                time: 0,
                tx_count: 0,
                tx_rate: 0.001,
            },
        }
    }

    /// Return the number of header-only blocks by which the best header
    /// extends the active tip. Competing branches are deliberately ignored,
    /// matching Core's `ChainstateManager::BlocksAheadOfTip()` contract used
    /// by the mining-interface cooldown.
    pub fn blocks_ahead_of_tip(&self) -> Option<u32> {
        let tip = self.tip();
        let best_header = self.best_header_tip();
        (best_header.work > tip.work
            && best_header.height > tip.height
            && self.ancestor_hash_at_height(&best_header.hash, tip.height) == Some(tip.hash))
        .then_some(best_header.height - tip.height)
    }

    /// Return Core v31.1's default minimum chainwork threshold for this
    /// network. Custom Signet challenges intentionally have no public-chain
    /// work assumption.
    pub fn minimum_chain_work(&self) -> Work {
        if let Some(work) = self.minimum_chain_work_override {
            return work;
        }
        if self.network == Network::Signet
            && self.signet_challenge.as_deref()
                != Some(validation::default_signet_challenge().as_slice())
        {
            return Work::from_be_bytes([0; 32]);
        }
        let hex = match self.network {
            Network::Bitcoin => "0000000000000000000000000000000000000001128750f82f4c366153a3a030",
            Network::Testnet => "0000000000000000000000000000000000000000000017dde1c649f3708d14b6",
            Network::Testnet4 => "0000000000000000000000000000000000000000000009a0fe15d0177d086304",
            Network::Signet => "00000000000000000000000000000000000000000000000000000b463ea0a4b8",
            Network::Regtest => return Work::from_be_bytes([0; 32]),
        };
        Work::from_unprefixed_hex(hex).expect("Core minimum chainwork is valid hex")
    }

    fn script_check_reason(&self, block: &Block, height: u32) -> Option<&'static str> {
        const TWO_WEEKS_SECS: u32 = 14 * 24 * 60 * 60;
        let block_hash = block.block_hash();
        let Some(assume_valid_block) = self.assume_valid_block else {
            return Some("assumevalid=0 (always verify)");
        };
        let Some(assumed_node) = self.block_index.get(&assume_valid_block) else {
            return Some("assumevalid hash not in headers");
        };
        if height > assumed_node.height {
            return Some("block height above assumevalid height");
        }
        let best_header = self.best_header_tip();
        if self.ancestor_hash(assume_valid_block, height) != Some(block_hash) {
            return Some("block not in assumevalid chain");
        }
        if self.ancestor_hash(best_header.hash, height) != Some(block_hash) {
            return Some("block not in best header chain");
        }
        if best_header.work < self.minimum_chain_work() {
            return Some("best header chainwork below minimumchainwork");
        }
        let Some(best_header_record) = self.block_index.get(&best_header.hash) else {
            return Some("best header chainwork below minimumchainwork");
        };
        let Some(block_node) = self.block_index.get(&block_hash) else {
            return Some("block too recent relative to best header");
        };
        if best_header.work < block_node.chain_work {
            return Some("block too recent relative to best header");
        }
        let work_delta = best_header.work - block_node.chain_work;
        let tip_proof = BigUint::from_bytes_be(&best_header_record.header.work().to_be_bytes());
        let equivalent_time = if tip_proof == BigUint::from(0u8) {
            BigUint::from(0u8)
        } else {
            BigUint::from_bytes_be(&work_delta.to_be_bytes())
                * BigUint::from(self.network.params().pow_target_spacing)
                / tip_proof
        };
        if equivalent_time <= BigUint::from(TWO_WEEKS_SECS) {
            return Some("block too recent relative to best header");
        }
        None
    }

    fn should_skip_script_checks(&self, block: &Block, height: u32) -> bool {
        self.script_check_reason(block, height).is_none()
    }

    /// Return the hardcoded AssumeUTXO commitments for this network.
    ///
    /// Custom Signet challenges intentionally have no commitments because
    /// their chain is not the public default Signet chain.
    pub fn assumeutxo_data(&self) -> &'static [AssumeUtxoData] {
        if self.network == Network::Signet
            && self.signet_challenge.as_deref()
                != Some(validation::default_signet_challenge().as_slice())
        {
            return &[];
        }
        assumeutxo_data_for_network(self.network)
    }

    /// Return the commitment for a supported snapshot base block.
    pub fn assumeutxo_for_block(&self, hash: BlockHash) -> Option<AssumeUtxoData> {
        self.assumeutxo_data()
            .iter()
            .copied()
            .find(|data| data.blockhash.parse::<BlockHash>().ok() == Some(hash))
    }

    /// Return the base block and validation state of the active snapshot
    /// chainstate, if one was loaded through strict AssumeUTXO activation.
    pub fn snapshot_provenance(&self) -> Option<(BlockHash, bool)> {
        self.snapshot_base
            .map(|base| (base, self.snapshot_validated))
    }

    /// Return Core's network-relative marker directory for an active
    /// AssumeUTXO snapshot chainstate.
    pub fn snapshot_chainstate_path(&self) -> PathBuf {
        let network_dir = network_data_dir_name(self.network);
        if network_dir.is_empty() {
            self.data_dir.join("chainstate_snapshot")
        } else {
            self.data_dir.join(network_dir).join("chainstate_snapshot")
        }
    }

    pub fn snapshot_validation_error(&self) -> Option<String> {
        self.snapshot_validation_error.clone()
    }

    /// Return the background validation chainstate's current replay point.
    /// The active snapshot chainstate remains the serving tip while this
    /// point advances independently.
    pub fn background_chainstate(&self) -> Option<(u32, BlockHash, BlockHash, Option<String>)> {
        let base_hash = self.snapshot_base?;
        if self.snapshot_validated {
            return None;
        }
        let progress_height = self
            .background_validation
            .as_ref()
            .map(|validation| validation.progress.load(Ordering::Acquire))
            .or_else(|| {
                if self.is_active_block(&base_hash) {
                    Some(self.block_height_by_hash(&base_hash).unwrap_or_default())
                } else {
                    Some(self.height())
                }
            })
            .unwrap_or_default()
            .min(self.height());
        let progress_hash = self
            .active_chain
            .get(progress_height as usize)
            .copied()
            .unwrap_or(base_hash);
        Some((
            progress_height,
            progress_hash,
            base_hash,
            self.snapshot_validation_error.clone(),
        ))
    }

    /// Complete a background AssumeUTXO validation job, if its worker has
    /// published a result.  This is intentionally called from the node's
    /// periodic supervisor and from synchronous chain-entry points so the
    /// worker never mutates the serving chainstate behind its lock.
    pub fn poll_background_validation(&mut self) -> Result<()> {
        if self.snapshot_base.is_some()
            && !self.snapshot_validated
            && self.snapshot_validation_error.is_none()
            && self.background_validation.is_none()
            && self
                .snapshot_base
                .is_some_and(|base| self.is_active_block(&base))
        {
            self.start_background_validation()?;
        }
        let Some(validation) = self.background_validation.as_ref() else {
            return Ok(());
        };
        let outcome = validation.outcome.lock().take();
        let Some(outcome) = outcome else {
            return Ok(());
        };
        let target_tip = match &outcome {
            BackgroundValidationOutcome::Complete { target_tip, .. }
            | BackgroundValidationOutcome::Failed { target_tip, .. } => *target_tip,
        };
        let base_hash = validation.base_hash;
        let target_is_current = target_tip == self.best_hash()
            && self
                .block_height_by_hash(&target_tip)
                .is_some_and(|height| self.active_chain.get(height as usize) == Some(&target_tip));
        self.background_validation = None;
        if !target_is_current || self.snapshot_base != Some(base_hash) {
            if self.snapshot_base == Some(base_hash)
                && !self.snapshot_validated
                && self.snapshot_validation_error.is_none()
            {
                self.start_background_validation()?;
            }
            return Ok(());
        }

        match outcome {
            BackgroundValidationOutcome::Complete {
                base_matches: true, ..
            } => {
                self.snapshot_base = None;
                self.snapshot_validated = true;
                self.snapshot_validation_error = None;
                self.persist_snapshot()?;
                self.remove_assumeutxo_artifacts()?;
                self.persist_snapshot_provenance()?;
            }
            BackgroundValidationOutcome::Complete {
                base_matches: false,
                utxos,
                ..
            } => {
                self.utxos = utxos;
                self.utxos_materialized = true;
                self.snapshot_base = None;
                self.snapshot_validated = true;
                self.snapshot_validation_error = None;
                self.persist_snapshot()?;
                self.remove_assumeutxo_artifacts()?;
                self.persist_snapshot_provenance()?;
            }
            BackgroundValidationOutcome::Failed { error, utxos, .. } => {
                if let Some(utxos) = utxos {
                    self.utxos = utxos;
                    self.utxos_materialized = true;
                    self.snapshot_base = None;
                    self.snapshot_validated = true;
                    self.snapshot_validation_error = None;
                    self.persist_snapshot()?;
                    self.remove_assumeutxo_artifacts()?;
                    self.persist_snapshot_provenance()?;
                } else {
                    self.snapshot_validation_error = Some(error);
                    self.persist_snapshot_provenance()?;
                }
            }
        }
        Ok(())
    }

    /// Return Core's latched initial-block-download state. Transaction relay
    /// is intentionally paused while this is true, but headers and blocks
    /// continue to synchronize. Once the tip reaches the work/age boundary,
    /// the state remains false for the lifetime of this chain instance.
    pub fn is_initial_block_download(&self) -> bool {
        self.initial_block_download
    }

    /// Configure Core's IBD tip-age boundary and refresh the latched state.
    pub fn configure_max_tip_age(&mut self, max_tip_age_secs: u64) {
        if !self.max_tip_age_configured {
            // ChainState evaluates IBD once while opening with Core's default
            // 24-hour boundary. Apply the user-supplied boundary to that
            // initial decision instead of treating the already-false value
            // as the runtime latch.
            self.initial_block_download = true;
            self.max_tip_age_configured = true;
        }
        self.max_tip_age_secs = max_tip_age_secs;
        self.update_ibd_status();
    }

    /// Configure the number of parallel script-check workers using Core's
    /// `-par` convention. Zero autodetects, while a negative value leaves
    /// that many cores available to the rest of the node.
    pub fn configure_script_check_threads(&mut self, par: i32) {
        self.script_check_workers = script_check_workers(par);
        self.script_checks_enabled = self.script_check_workers > 0;
    }

    pub fn script_checks_enabled(&self) -> bool {
        self.script_checks_enabled && self.script_check_workers > 0
    }

    pub fn script_check_thread_count(&self) -> usize {
        if self.script_checks_enabled() {
            self.script_check_workers.saturating_add(1)
        } else {
            1
        }
    }

    pub fn set_script_checks_enabled(&mut self, enabled: bool) -> Result<()> {
        if enabled && self.script_check_workers == 0 {
            bail!(
                "Script verification threads are disabled (single core machine or -par=<-<numcores>)"
            )
        }
        self.script_checks_enabled = enabled;
        Ok(())
    }

    /// Configure the bounded successful-script-validation cache. The cache
    /// stores compact digests rather than transaction data, so its capacity
    /// is expressed in approximate bytes to match Core's `-maxsigcachesize`.
    pub fn configure_script_cache_size_mib(&mut self, mib: i64) {
        let bytes = u64::try_from(mib.max(0))
            .unwrap_or(u64::MAX)
            .saturating_mul(1024 * 1024);
        let mut cache = self.script_cache.lock();
        cache.max_entries = usize::try_from(bytes / 64).unwrap_or(usize::MAX).max(2);
        while cache.order.len() > cache.max_entries {
            if let Some(key) = cache.order.pop_front() {
                cache.entries.remove(&key);
            }
        }
    }

    /// Configure the custom append-only store's decoded block cache from the
    /// Core-compatible `-dbcache` setting.
    pub fn configure_storage_cache_size_mib(&mut self, mib: i64) {
        self.store.configure_cache_size_mib(mib);
        self.utxo_store.configure_cache_size_mib(mib);
    }

    /// Configure chainstate write batching from Core's debug-only
    /// `-dbbatchsize` option.
    pub fn configure_storage_batch_size_bytes(&mut self, bytes: i64) {
        self.chainstate_store
            .configure_write_batch_size_bytes(bytes);
    }

    /// Configure Core's debug-only chainstate crash simulation. The UTXO
    /// store injects the abrupt exit after the durable block/UTXO state and
    /// active-chain metadata agree, so restart can resume at the submitted
    /// block just as Core's recovery test expects.
    pub fn configure_storage_crash_ratio(&mut self, ratio: Option<u64>) {
        self.utxo_store.configure_crash_ratio(ratio);
    }

    pub fn maybe_simulate_storage_recovery_crash(&self) -> Result<()> {
        self.utxo_store.maybe_simulate_recovery_crash()
    }

    fn update_ibd_status(&mut self) {
        self.update_ibd_status_at(crate::time::unix_time());
    }

    fn update_ibd_status_at(&mut self, now: u64) {
        if !self.initial_block_download {
            return;
        }
        let tip = self.tip();
        let header = self
            .header(tip.height)
            .expect("the active tip header is always indexed");
        if tip.work >= self.minimum_chain_work()
            && u64::from(header.time).saturating_add(self.max_tip_age_secs) >= now
        {
            self.initial_block_download = false;
        }
    }

    pub fn chain_tips(&self) -> Vec<KnownChainTip> {
        let mut parents = HashSet::new();
        for node in self.block_index.values() {
            if node.height > 0 {
                parents.insert(node.header.prev_blockhash);
            }
        }
        let active: HashSet<BlockHash> = self.active_chain.iter().copied().collect();
        let active_tip = self.best_hash();
        let mut tips = self
            .block_index
            .iter()
            .filter(|(hash, _)| **hash == active_tip || !parents.contains(*hash))
            .map(|(hash, node)| {
                if active.contains(hash) {
                    return KnownChainTip {
                        hash: *hash,
                        height: node.height,
                        branch_len: 0,
                        status: "active",
                        work: node.chain_work,
                    };
                }
                let mut cursor = *hash;
                let mut branch_len: u32 = 0;
                let mut has_full_blocks = true;
                while !active.contains(&cursor) {
                    if !self.store.contains(&cursor) {
                        has_full_blocks = false;
                    }
                    let Some(current) = self.block_index.get(&cursor) else {
                        break;
                    };
                    cursor = current.header.prev_blockhash;
                    branch_len = branch_len.saturating_add(1);
                }
                let status =
                    if self.invalid_blocks.contains(hash) || self.has_invalid_ancestor(*hash) {
                        "invalid"
                    } else if has_full_blocks {
                        "valid-fork"
                    } else {
                        "headers-only"
                    };
                KnownChainTip {
                    hash: *hash,
                    height: node.height,
                    branch_len,
                    status,
                    work: node.chain_work,
                }
            })
            .collect::<Vec<_>>();
        tips.sort_by(|left, right| {
            right
                .height
                .cmp(&left.height)
                .then_with(|| right.work.cmp(&left.work))
                .then_with(|| left.hash.to_string().cmp(&right.hash.to_string()))
        });
        tips
    }

    pub fn is_active_block(&self, hash: &BlockHash) -> bool {
        let Some(node) = self.block_index.get(hash) else {
            return false;
        };
        self.active_chain
            .get(node.height as usize)
            .is_some_and(|active_hash| active_hash == hash)
    }

    pub fn has_large_work_invalid_chain(&self) -> bool {
        let active_height = self.height();
        self.invalid_blocks.iter().any(|hash| {
            self.block_index
                .get(hash)
                .is_some_and(|node| node.height > active_height.saturating_add(6))
        })
    }

    /// Return the BIP22 proposal result for a block already known to the
    /// node. Full blocks that passed validation are duplicates; headers that
    /// have not received a body yet are inconclusive.
    pub fn proposal_duplicate_status(&self, hash: &BlockHash) -> Option<&'static str> {
        if !self.block_index.contains_key(hash) {
            return None;
        }
        if self.has_invalid_ancestor(*hash) {
            return Some("duplicate-invalid");
        }
        // Active-chain entries remain fully validated after their block body
        // is pruned. Core's proposal path uses the block-index validation
        // status rather than requiring the body to remain available, so a
        // pruned active block is still an exact duplicate.
        if self.is_active_block(hash) {
            Some("duplicate")
        } else if self.store.contains(hash) {
            // A body fetched before a restart can be present without having
            // been connected. Allow submitblock to retry it once its parent
            // is the active tip; side-chain bodies remain ordinary
            // duplicates.
            let reconnectable = self
                .block_index
                .get(hash)
                .is_some_and(|node| node.header.prev_blockhash == self.best_hash());
            (!reconnectable).then_some("duplicate")
        } else {
            Some("duplicate-inconclusive")
        }
    }

    /// Apply Core's submitblock-only normalization for an omitted coinbase
    /// witness reserved value. The block hash and txid are unchanged because
    /// the witness is outside the transaction merkle tree.
    pub fn update_uncommitted_block_structures(&self, block: &mut Block) {
        let Some(parent) = self.block_index.get(&block.header.prev_blockhash) else {
            return;
        };
        let height = parent.height.saturating_add(1);
        if height < self.deployment_parameters.buried.segwit {
            return;
        }
        let Some(coinbase) = block.txdata.first_mut() else {
            return;
        };
        let has_witness_commitment = coinbase.output.iter().any(|output| {
            output.script_pubkey.len() >= 38
                && output.script_pubkey.as_bytes()[..6] == [0x6a, 0x24, 0xaa, 0x21, 0xa9, 0xed]
        });
        if has_witness_commitment
            && coinbase.input.iter().all(|input| input.witness.is_empty())
            && let Some(input) = coinbase.input.first_mut()
        {
            input.witness = Witness::from_slice(&[vec![0u8; 32]]);
        }
    }

    pub fn invalidate_block(&mut self, hash: &BlockHash) -> Result<ChainTip> {
        let node = self
            .block_index
            .get(hash)
            .copied()
            .with_context(|| format!("block {hash} not found"))?;
        if node.height == 0 {
            bail!("cannot invalidate the genesis block")
        }
        let invalidated: Vec<BlockHash> = self
            .block_index
            .keys()
            .copied()
            .filter(|candidate| self.is_descendant_or_self(candidate, hash))
            .collect();
        self.invalid_blocks.extend(invalidated);
        let best_valid = self
            .best_valid_tip_hash()
            .context("invalidated chain has no valid alternative")?;
        let activated = best_valid != self.best_hash();
        if activated {
            self.activate_chain(best_valid)?;
        } else {
            self.persist_metadata()?;
        }
        Ok(self.tip())
    }

    /// Cache a consensus-invalid block discovered while processing a peer
    /// body.  Core keeps the header in the block index but marks it failed so
    /// that a later child header is rejected without re-running validation.
    /// Mutation failures are filtered by the caller before reaching this
    /// method.
    pub fn mark_block_invalid(&mut self, hash: &BlockHash) -> Result<()> {
        if self.block_index.contains_key(hash) && self.invalid_blocks.insert(*hash) {
            self.persist_metadata()?;
        }
        Ok(())
    }

    pub fn reconsider_block(&mut self, hash: &BlockHash) -> Result<ChainTip> {
        self.block_index
            .get(hash)
            .copied()
            .with_context(|| format!("block {hash} not found"))?;
        let reconsidered: Vec<BlockHash> = self
            .invalid_blocks
            .iter()
            .copied()
            // Core clears BLOCK_FAILED_VALID on the requested block, all of
            // its descendants, and all of its ancestors.  The ancestor
            // portion matters when a descendant is supplied to
            // reconsiderblock after its invalid parent was marked failed.
            .filter(|candidate| {
                self.is_descendant_or_self(candidate, hash)
                    || self.is_descendant_or_self(hash, candidate)
            })
            .collect();
        for candidate in reconsidered {
            self.invalid_blocks.remove(&candidate);
        }
        if let Some(best_valid) = self.best_valid_tip_hash()
            && best_valid != self.best_hash()
        {
            self.activate_chain(best_valid)?;
        }
        self.persist_metadata()?;
        Ok(self.tip())
    }

    pub fn precious_block(&mut self, hash: &BlockHash) -> Result<ChainTip> {
        let node = self
            .block_index
            .get(hash)
            .copied()
            .with_context(|| format!("block {hash} not found"))?;
        // Core treats a preciousblock request below the current tip's
        // chainwork as a no-op and does not attach a preference to it.
        if node.chain_work < self.tip().work {
            return Ok(self.tip());
        }
        if self
            .precious_last_chainwork
            .is_none_or(|last| self.tip().work > last)
        {
            self.precious_sequence = -1;
        }
        self.precious_last_chainwork = Some(self.tip().work);
        self.precious_blocks.insert(*hash, self.precious_sequence);
        self.precious_sequence = self.precious_sequence.saturating_sub(1);
        let best = self
            .best_valid_tip_hash()
            .context("chain has no valid tip")?;
        if best != self.best_hash() {
            self.activate_chain(best)?;
        }
        Ok(self.tip())
    }

    pub fn header(&self, height: u32) -> Option<&bitcoin::block::Header> {
        self.headers.get(height as usize)
    }

    /// Return an Electrum header checkpoint proof. The tree is built lazily
    /// once for a header prefix and then extended incrementally as a larger
    /// checkpoint is requested. A reorg below the cached prefix rebuilds it.
    pub fn header_merkle_proof(
        &self,
        height: u32,
        checkpoint: u32,
    ) -> Result<(Vec<BlockHash>, BlockHash)> {
        if height > checkpoint {
            bail!("checkpoint height must not precede requested height");
        }
        let checkpoint_index =
            usize::try_from(checkpoint).context("checkpoint height does not fit in memory")?;
        let checkpoint_hash = self
            .headers
            .get(checkpoint_index)
            .map(bitcoin::block::Header::block_hash)
            .context("checkpoint height out of range")?;
        let mut cache = self.header_merkle_cache.lock();
        let can_extend = cache.as_ref().is_some_and(|cached| {
            checkpoint > cached.checkpoint
                && self
                    .headers
                    .get(cached.checkpoint as usize)
                    .is_some_and(|header| header.block_hash() == cached.checkpoint_hash)
        });
        let reuse = cache.as_ref().is_some_and(|cached| {
            cached.checkpoint == checkpoint && cached.checkpoint_hash == checkpoint_hash
        });
        if !reuse && !can_extend {
            let hashes = self
                .headers
                .get(..=checkpoint_index)
                .context("checkpoint height out of range")?
                .iter()
                .map(bitcoin::block::Header::block_hash)
                .collect();
            *cache = Some(HeaderMerkleCache::from_hashes(
                checkpoint_hash,
                checkpoint,
                hashes,
            )?);
        } else if can_extend {
            let cached = cache
                .as_mut()
                .expect("header merkle cache was checked for extension");
            for height in cached.checkpoint.saturating_add(1)..=checkpoint {
                let hash = self
                    .headers
                    .get(height as usize)
                    .map(bitcoin::block::Header::block_hash)
                    .expect("checkpoint extension height is in range");
                cached.append_hash(hash);
            }
        }
        cache
            .as_ref()
            .expect("header merkle cache was initialized")
            .proof(height)
    }

    pub fn active_headers(&self) -> &[bitcoin::block::Header] {
        &self.headers
    }

    pub fn header_by_hash(&self, hash: &BlockHash) -> Option<bitcoin::block::Header> {
        self.block_index.get(hash).map(|node| node.header)
    }

    pub fn headers_to_hash(&self, hash: &BlockHash) -> Option<Vec<bitcoin::block::Header>> {
        let node = self.block_index.get(hash)?;
        if self
            .active_chain
            .get(node.height as usize)
            .is_some_and(|active_hash| active_hash == hash)
            && let Some(headers) = self.headers.get(..=node.height as usize)
        {
            return Some(headers.to_vec());
        }
        let mut headers = Vec::new();
        let mut cursor = *hash;
        loop {
            let node = self.block_index.get(&cursor)?;
            headers.push(node.header);
            if node.height == 0 {
                break;
            }
            cursor = node.header.prev_blockhash;
        }
        headers.reverse();
        Some(headers)
    }

    pub fn block_height_by_hash(&self, hash: &BlockHash) -> Option<u32> {
        self.block_index.get(hash).map(|node| node.height)
    }

    /// Match Core's `BlockRequestAllowed` policy for non-active blocks.
    ///
    /// Active-chain blocks are always eligible to be served (subject to the
    /// caller discovering that pruning removed their body). A side-chain
    /// block must remain within the stale-relay age in both header time and
    /// equivalent proof-of-work time; callers separately check whether its
    /// body or filter is available.
    pub fn block_request_allowed(&self, hash: &BlockHash, max_age_secs: u64) -> bool {
        let Some(node) = self.block_index.get(hash) else {
            return false;
        };
        if self
            .active_chain
            .get(node.height as usize)
            .is_some_and(|active_hash| active_hash == hash)
        {
            return true;
        }
        // Core's BlockRequestAllowed requires BLOCK_VALID_SCRIPTS for
        // non-active blocks. Header-only branches have no script-validation
        // state; in this storage model a retained side-chain body is the
        // corresponding validation marker.
        if !self.store.contains(hash) {
            return false;
        }
        let best_header = self.best_header_tip();
        let Some(best_node) = self.block_index.get(&best_header.hash) else {
            return false;
        };
        let time_delta = i64::from(best_node.header.time) - i64::from(node.header.time);
        if time_delta >= i64::try_from(max_age_secs).unwrap_or(i64::MAX) {
            return false;
        }

        // A retained side branch can have more work than the selected header
        // tip while headers are still being reconciled. Core treats that
        // branch as ineligible here; do not subtract the work values in the
        // opposite order because Work's debug subtraction is checked.
        if node.chain_work > best_node.chain_work {
            return false;
        }
        let work_delta = best_node.chain_work - node.chain_work;
        let tip_proof = BigUint::from_bytes_be(&best_node.header.work().to_be_bytes());
        if tip_proof == BigUint::from(0u8) {
            return false;
        }
        let equivalent_time = BigUint::from_bytes_be(&work_delta.to_be_bytes())
            * BigUint::from(self.network.params().pow_target_spacing)
            / tip_proof;
        equivalent_time < BigUint::from(max_age_secs)
    }

    pub fn ancestor_hash_at_height(&self, hash: &BlockHash, height: u32) -> Option<BlockHash> {
        self.ancestor_hash(*hash, height)
    }

    pub fn next_block_hash(&self, hash: &BlockHash) -> Option<BlockHash> {
        let node = self.block_index.get(hash)?;
        self.active_chain
            .get(node.height as usize)
            .is_some_and(|active_hash| active_hash == hash)
            .then(|| self.active_chain.get(node.height as usize + 1).copied())
            .flatten()
    }

    pub fn median_time_past_for_hash(&self, hash: &BlockHash) -> Option<u32> {
        let mut times = Vec::with_capacity(11);
        let mut cursor = *hash;
        for _ in 0..11 {
            let node = self.block_index.get(&cursor)?;
            times.push(node.header.time);
            if node.height == 0 {
                break;
            }
            cursor = node.header.prev_blockhash;
        }
        times.sort_unstable();
        times.get(times.len() / 2).copied()
    }

    pub fn block_transaction_count(&mut self, hash: &BlockHash) -> Result<Option<usize>> {
        if let Some(node) = self.block_index.get(hash)
            && self.active_chain.get(node.height as usize) == Some(hash)
            && let Some(count) = self.active_tx_counts.get(node.height as usize)
        {
            return Ok(Some(*count as usize));
        }
        Ok(self.store.get(hash)?.map(|block| block.txdata.len()))
    }

    pub fn chain_transaction_count(&self, height: u32) -> Option<u64> {
        let height = usize::try_from(height).ok()?;
        (self.active_chain.len() == self.active_tx_counts.len()
            && self.active_chain.len() == self.active_tx_totals.len())
        .then(|| self.active_tx_totals.get(height).copied())
        .flatten()
    }

    /// Return the cumulative transaction count for a header on the serving
    /// chain, including the hardcoded AssumeUTXO count at a snapshot base
    /// whose body is not yet present locally.
    pub fn chain_transaction_count_for_hash(&self, hash: &BlockHash) -> Option<u64> {
        if let Some(base_hash) = self.snapshot_base
            && !self.snapshot_validated
            && base_hash == *hash
        {
            return self
                .assumeutxo_for_block(base_hash)
                .map(|data| data.chain_tx_count);
        }
        let node = self.block_index.get(hash)?;
        self.is_active_block(hash)
            .then(|| self.chain_transaction_count(node.height))
            .flatten()
    }

    pub fn block_fee_stats(&mut self, hash: &BlockHash) -> Result<Option<BlockFeeStats>> {
        if !self.block_index.contains_key(hash) {
            return Ok(None);
        }
        let Some(block) = self.store.get(hash)? else {
            return Ok(None);
        };
        let Some(undo) = self.spent_outputs_by_transaction(hash)? else {
            return Ok(None);
        };
        if undo.len() != block.txdata.len() {
            bail!("block undo transaction count does not match block");
        }
        let mut total_fee_sat = 0u64;
        let mut transaction_fees_sat = Vec::new();
        let mut spent_outputs = Vec::new();
        for (transaction, input_outputs) in block.txdata.iter().skip(1).zip(undo.iter().skip(1)) {
            if input_outputs.len() != transaction.input.len() {
                bail!("block undo input count does not match transaction");
            }
            let input_total = input_outputs
                .iter()
                .try_fold(0u64, |total, output| {
                    total.checked_add(output.value.to_sat())
                })
                .ok_or_else(|| anyhow::anyhow!("transaction input total overflow"))?;
            let output_total = transaction
                .output
                .iter()
                .try_fold(0u64, |total, output| {
                    total.checked_add(output.value.to_sat())
                })
                .ok_or_else(|| anyhow::anyhow!("transaction output total overflow"))?;
            if input_total < output_total {
                bail!("block transaction has a negative fee");
            }
            let fee = input_total - output_total;
            total_fee_sat = total_fee_sat
                .checked_add(fee)
                .ok_or_else(|| anyhow::anyhow!("block fee total overflow"))?;
            transaction_fees_sat.push(fee);
            spent_outputs.extend(input_outputs.iter().cloned());
        }
        Ok(Some(BlockFeeStats {
            total_fee_sat,
            transaction_fees_sat,
            spent_outputs,
        }))
    }

    /// Return confirmed transaction fee samples as `(fee_sat, vsize)` pairs.
    ///
    /// Undo data makes this proportional to the requested block rather than
    /// requiring a UTXO replay from genesis. Older stores without an undo
    /// record use the existing replay fallback in
    /// [`spent_outputs_by_transaction`].
    pub fn block_fee_samples(&mut self, hash: &BlockHash) -> Result<Option<Vec<(u64, u64)>>> {
        let Some(block) = self.store.get(hash)? else {
            return Ok(None);
        };
        let Some(undo) = self.spent_outputs_by_transaction(hash)? else {
            return Ok(None);
        };
        if undo.len() != block.txdata.len() {
            bail!("block undo transaction count does not match block");
        }
        let mut samples = Vec::with_capacity(block.txdata.len().saturating_sub(1));
        for (transaction, input_outputs) in block.txdata.iter().skip(1).zip(undo.iter().skip(1)) {
            if input_outputs.len() != transaction.input.len() {
                bail!("block undo input count does not match transaction");
            }
            let input_total = input_outputs
                .iter()
                .try_fold(0u64, |total, output| {
                    total.checked_add(output.value.to_sat())
                })
                .ok_or_else(|| anyhow::anyhow!("transaction input total overflow"))?;
            let output_total = transaction
                .output
                .iter()
                .try_fold(0u64, |total, output| {
                    total.checked_add(output.value.to_sat())
                })
                .ok_or_else(|| anyhow::anyhow!("transaction output total overflow"))?;
            if input_total < output_total {
                bail!("block transaction has a negative fee");
            }
            samples.push((input_total - output_total, transaction.vsize() as u64));
        }
        Ok(Some(samples))
    }

    /// Return recent confirmed transaction fee-rate samples as
    /// `(sat_per_kvb, vsize)` pairs.
    pub fn recent_fee_rate_samples(&mut self, max_blocks: u32) -> Result<Vec<(u64, u64)>> {
        if max_blocks == 0 {
            return Ok(Vec::new());
        }
        let tip_height = self.height();
        let start_height = tip_height.saturating_sub(max_blocks.saturating_sub(1));
        let mut samples = Vec::new();
        for height in start_height..=tip_height {
            let Some(hash) = self.block_hash(height) else {
                continue;
            };
            if let Some(block_samples) = self.block_fee_samples(&hash)? {
                samples.extend(block_samples.into_iter().filter_map(|(fee, vsize)| {
                    (vsize > 0).then_some((
                        fee.saturating_mul(1_000)
                            .checked_div(vsize)
                            .unwrap_or(u64::MAX),
                        vsize,
                    ))
                }));
            }
        }
        Ok(samples)
    }

    /// Estimate a fee rate in satoshis per virtual kilobyte from recent
    /// confirmed transactions. The returned block count is the requested
    /// target; `None` means there is not enough confirmed fee data yet.
    pub fn estimate_fee_rate_sat_per_kvb(
        &mut self,
        conf_target: u32,
        conservative: bool,
    ) -> Result<Option<u64>> {
        if conf_target == 0 || conf_target > 1_008 {
            bail!("confirmation target must be between 1 and 1008 blocks");
        }
        let sample_blocks = if conservative {
            conf_target.saturating_mul(2).clamp(conf_target, 1_008)
        } else {
            conf_target
        };
        let mut samples = self.recent_fee_rate_samples(sample_blocks)?;
        if samples.is_empty() {
            return Ok(None);
        }
        samples.sort_unstable_by_key(|(rate, _)| *rate);
        let percentile = if conservative || conf_target <= 2 {
            90
        } else if conf_target <= 6 {
            75
        } else if conf_target <= 12 {
            50
        } else {
            25
        };
        let target_weight = samples
            .iter()
            .map(|(_, vsize)| *vsize)
            .sum::<u64>()
            .saturating_mul(percentile)
            / 100;
        let mut cumulative_weight = 0u64;
        let mut estimate = 0u64;
        for (rate, vsize) in samples {
            cumulative_weight = cumulative_weight.saturating_add(vsize);
            estimate = rate;
            if cumulative_weight >= target_weight {
                break;
            }
        }
        Ok(Some(estimate.max(1_000)))
    }

    /// Keep only a bounded working set of filter bodies in memory. The
    /// durable filter store remains the source of truth for older blocks.
    fn cache_basic_filter(
        &mut self,
        hash: BlockHash,
        content: Vec<u8>,
        filter_header: FilterHeader,
    ) {
        if !self.basic_filter_cache.contains_key(&hash)
            && self.basic_filter_cache.len() >= MAX_BASIC_FILTER_CACHE_ENTRIES
            && let Some(evicted) = self.basic_filter_cache.keys().next().copied()
        {
            self.basic_filter_cache.remove(&evicted);
        }
        self.basic_filter_cache
            .insert(hash, (content, filter_header));
    }

    /// Build the BIP158 basic filter and filter header for every block from
    /// genesis through `hash`. Missing filters are computed on demand and
    /// appended to the durable filter index in one batch.
    pub fn basic_filter_chain(
        &mut self,
        hash: &BlockHash,
    ) -> Result<Option<Vec<(BlockHash, BlockFilter, FilterHeader)>>> {
        if !self.blockfilter_index_enabled {
            return Ok(None);
        }
        let Some(headers) = self.headers_to_hash(hash) else {
            return Ok(None);
        };
        let mut stored_filters = Vec::with_capacity(headers.len());
        let mut all_filters_stored = true;
        for header in &headers {
            let block_hash = header.block_hash();
            let filter =
                if let Some((content, filter_header)) = self.basic_filter_cache.get(&block_hash) {
                    Some((content.clone(), *filter_header))
                } else {
                    self.filter_store.get(&block_hash)?
                };
            let Some(filter) = filter else {
                all_filters_stored = false;
                break;
            };
            stored_filters.push((block_hash, filter.0, filter.1));
        }
        if all_filters_stored {
            return Ok(Some(
                stored_filters
                    .into_iter()
                    .map(|(block_hash, content, filter_header)| {
                        (block_hash, BlockFilter::new(&content), filter_header)
                    })
                    .collect(),
            ));
        }
        let mut previous_outputs: HashMap<OutPoint, TxOut> = HashMap::new();
        let mut previous_filter_header = FilterHeader::all_zeros();
        let mut filters = Vec::with_capacity(headers.len());

        for (height, header) in headers.into_iter().enumerate() {
            let block_hash = header.block_hash();
            let Some(block) = self.store.get(&block_hash)? else {
                return Ok(None);
            };
            let mut created_outputs = HashMap::new();
            for transaction in &block.txdata {
                let txid = transaction.compute_txid();
                for (vout, output) in transaction.output.iter().enumerate() {
                    created_outputs.insert(OutPoint::new(txid, vout as u32), output.clone());
                }
            }
            let filter = BlockFilter::new_script_filter(&block, |outpoint| {
                previous_outputs
                    .get(outpoint)
                    .or_else(|| created_outputs.get(outpoint))
                    .map(|output| output.script_pubkey.clone())
                    .ok_or(bitcoin::bip158::Error::UtxoMissing(*outpoint))
            })?;
            let filter_header = filter.filter_header(&previous_filter_header);
            filters.push((block_hash, filter, filter_header));
            previous_filter_header = filter_header;

            // The genesis coinbase output is intentionally not part of the
            // spendable UTXO set, matching Bitcoin Core's chainstate rules.
            if height > 0 {
                for transaction in &block.txdata {
                    for input in &transaction.input {
                        previous_outputs.remove(&input.previous_output);
                    }
                    let txid = transaction.compute_txid();
                    for (vout, output) in transaction.output.iter().enumerate() {
                        previous_outputs.insert(OutPoint::new(txid, vout as u32), output.clone());
                    }
                }
            }
        }

        let filter_records = filters
            .iter()
            .map(|(block_hash, filter, filter_header)| {
                (*block_hash, filter.content.as_slice(), *filter_header)
            })
            .collect::<Vec<_>>();
        self.filter_store.insert_batch(&filter_records)?;
        if let Some((hash, _, _)) = filters.last()
            && let Some(node) = self.block_index.get(hash)
        {
            self.update_index_prune_locks(node.height);
        }
        Ok(Some(filters))
    }

    /// Return one durable BIP158 basic filter without rebuilding the chain
    /// from genesis. Older stores may not have a record for the requested
    /// block, so retain the full-chain computation as a compatibility
    /// fallback.
    pub fn basic_filter_for_block(
        &mut self,
        hash: &BlockHash,
    ) -> Result<Option<(Vec<u8>, FilterHeader)>> {
        if !self.blockfilter_index_enabled {
            return Ok(None);
        }
        if !self.block_index.contains_key(hash) {
            return Ok(None);
        }
        if let Some((content, filter_header)) = self.basic_filter_cache.get(hash) {
            return Ok(Some((content.clone(), *filter_header)));
        }
        if let Some((content, filter_header)) = self.filter_store.get(hash)? {
            self.cache_basic_filter(*hash, content.clone(), filter_header);
            return Ok(Some((content, filter_header)));
        }
        Ok(self.basic_filter_chain(hash)?.and_then(|filters| {
            filters
                .into_iter()
                .next_back()
                .map(|(_, filter, filter_header)| (filter.content, filter_header))
        }))
    }

    /// Return one basic filter header without reading its filter body.
    pub fn basic_filter_header_for_block(
        &mut self,
        hash: &BlockHash,
    ) -> Result<Option<FilterHeader>> {
        if !self.blockfilter_index_enabled {
            return Ok(None);
        }
        if !self.block_index.contains_key(hash) {
            return Ok(None);
        }
        if let Some((_, filter_header)) = self.basic_filter_cache.get(hash) {
            return Ok(Some(*filter_header));
        }
        if let Some(filter_header) = self.filter_store.get_header(hash)? {
            return Ok(Some(filter_header));
        }
        Ok(self
            .basic_filter_for_block(hash)?
            .map(|(_, filter_header)| filter_header))
    }

    /// Return a bounded active-chain range of BIP158 basic filters. The
    /// durable index is consulted one block at a time; only a store missing a
    /// requested record falls back to the legacy genesis-to-tip computation.
    pub fn basic_filter_range(
        &mut self,
        start_height: u32,
        stop_hash: BlockHash,
        limit: usize,
    ) -> Result<Option<BasicFilterRange>> {
        if !self.blockfilter_index_enabled {
            return Ok(None);
        }
        let Some(stop_height) = self.block_height_by_hash(&stop_hash) else {
            return Ok(None);
        };
        if start_height > stop_height || limit == 0 {
            return Ok(None);
        }
        let end_height = start_height
            .saturating_add(u32::try_from(limit.saturating_sub(1)).unwrap_or(u32::MAX))
            .min(stop_height);
        let end_hash = self
            .ancestor_hash(stop_hash, end_height)
            .ok_or_else(|| anyhow::anyhow!("compact filter height is out of range"))?;
        let previous_filter_header = if start_height == 0 {
            FilterHeader::all_zeros()
        } else {
            let previous_hash = self
                .ancestor_hash(stop_hash, start_height - 1)
                .ok_or_else(|| anyhow::anyhow!("compact filter predecessor is unavailable"))?;
            self.basic_filter_for_block(&previous_hash)?
                .map(|(_, filter_header)| filter_header)
                .ok_or_else(|| anyhow::anyhow!("compact filter predecessor is unavailable"))?
        };
        let mut filters = Vec::new();
        if limit != 0 {
            let range_len = end_height.saturating_sub(start_height).saturating_add(1);
            filters.reserve(usize::try_from(range_len).unwrap_or(usize::MAX));
            for height in start_height..=end_height {
                let block_hash = self
                    .ancestor_hash(stop_hash, height)
                    .ok_or_else(|| anyhow::anyhow!("compact filter height is out of range"))?;
                let (content, filter_header) = self
                    .basic_filter_for_block(&block_hash)?
                    .ok_or_else(|| anyhow::anyhow!("compact filter is missing"))?;
                filters.push((block_hash, content, filter_header));
            }
        }
        Ok(Some(BasicFilterRange {
            stop_hash: end_hash,
            previous_filter_header,
            filters,
        }))
    }

    /// Return the outputs spent by each transaction in a block, with an empty
    /// first entry for the coinbase transaction as in Core's block undo data.
    pub fn spent_outputs_by_transaction(
        &mut self,
        hash: &BlockHash,
    ) -> Result<Option<Vec<Vec<TxOut>>>> {
        if let Some(undo) = self.block_undo_cache.get(hash) {
            return Ok(Some(undo.clone()));
        }
        if let Some(undo) = self.store.get_undo(hash)? {
            self.remember_block_undo(*hash, undo.clone());
            return Ok(Some(undo));
        }
        let Some(block) = self.store.get(hash)? else {
            return Ok(None);
        };
        let Some(node) = self.block_index.get(hash).copied() else {
            return Ok(None);
        };
        let mut undo = vec![Vec::new()];
        if node.height == 0 {
            self.remember_block_undo(*hash, undo.clone());
            return Ok(Some(undo));
        }
        let Some(mut outputs) = self.replay_utxos_for_block(block.header.prev_blockhash, true)?
        else {
            // A body can be accepted before its parent's body arrives. Core
            // still serves that block, but has no undo information from which
            // to derive fees or prevouts yet.
            return Ok(None);
        };
        for transaction in block.txdata.iter().skip(1) {
            let mut spent = Vec::with_capacity(transaction.input.len());
            for input in &transaction.input {
                let entry = outputs.remove(&input.previous_output).with_context(|| {
                    format!("block undo is missing output {}", input.previous_output)
                })?;
                spent.push(entry.output);
            }
            undo.push(spent);
            let txid = transaction.compute_txid();
            for (vout, output) in transaction.output.iter().enumerate() {
                outputs.insert(
                    OutPoint::new(txid, vout as u32),
                    UtxoEntry {
                        output: output.clone(),
                        height: node.height,
                        median_time_past: 0,
                        coinbase: false,
                    },
                );
            }
        }
        self.remember_block_undo(*hash, undo.clone());
        Ok(Some(undo))
    }

    pub fn chain_work_by_hash(&self, hash: &BlockHash) -> Option<Work> {
        self.block_index.get(hash).map(|node| node.chain_work)
    }

    pub fn block_hash(&self, height: u32) -> Option<BlockHash> {
        self.active_chain.get(height as usize).copied()
    }

    /// Build the exponentially backed-off locator used by `getheaders` and
    /// `getblocks`. Keeping the first ten entries dense makes short reorgs
    /// cheap while the older entries still let a peer find a common ancestor
    /// without sending the entire active chain.
    pub fn block_locator_hashes(&self) -> Vec<BlockHash> {
        self.block_locator_hashes_from(self.best_hash())
    }

    /// Build a locator from any indexed header. Core uses this form while
    /// re-downloading a low-work header chain: the locator must retain the
    /// common chain start even though the headers being synchronized are not
    /// in the active chain yet.
    pub fn block_locator_hashes_from(&self, start_hash: BlockHash) -> Vec<BlockHash> {
        let Some(start) = self.block_index.get(&start_hash) else {
            return self.block_locator_hashes();
        };
        let mut locator = Vec::new();
        let mut hash = start_hash;
        let mut height = start.height;
        let mut step = 1u32;
        loop {
            locator.push(hash);
            if height == 0 {
                break;
            }
            if locator.len() > 10 {
                step = step.saturating_mul(2);
            }
            let target_height = height.saturating_sub(step);
            let Some(ancestor) = self.ancestor_hash(hash, target_height) else {
                break;
            };
            hash = ancestor;
            height = target_height;
        }
        locator
    }

    pub fn headers_after_locator(
        &self,
        locator: &[BlockHash],
        stop_hash: BlockHash,
    ) -> Vec<bitcoin::block::Header> {
        if locator.is_empty() {
            return Vec::new();
        }
        // Match Core's FindForkInGlobalIndex: a locator entry on a side
        // branch that extends the active tip still identifies the active tip
        // as the common fork. Without this case, a header-only branch causes
        // us to fall back to genesis and resend the entire active chain.
        let active_tip_height = self.active_chain.len().saturating_sub(1) as u32;
        let fork_height = locator.iter().find_map(|hash| {
            let node = self.block_index.get(hash)?;
            if self
                .active_chain
                .get(node.height as usize)
                .is_some_and(|active_hash| active_hash == hash)
            {
                return Some(node.height);
            }
            (node.height >= active_tip_height
                && self.ancestor_hash(*hash, active_tip_height) == Some(self.best_hash()))
            .then_some(active_tip_height)
        });
        let start = fork_height
            .and_then(|height| usize::try_from(height).ok())
            .and_then(|height| height.checked_add(1))
            .unwrap_or(0);
        let stop = if stop_hash == BlockHash::all_zeros() {
            self.active_chain.len()
        } else {
            self.block_index
                .get(&stop_hash)
                .filter(|node| {
                    self.active_chain
                        .get(node.height as usize)
                        .is_some_and(|active_hash| active_hash == &stop_hash)
                })
                .map_or(self.active_chain.len(), |node| node.height as usize + 1)
        };
        let stop = stop.min(self.headers.len());
        if start >= stop {
            return Vec::new();
        }
        self.headers[start..stop]
            .iter()
            .take(2_000)
            .copied()
            .collect()
    }

    /// Return the block inventory Core would produce for `getblocks`.
    ///
    /// Unlike `getheaders`, the stop hash is not included. Core also stops
    /// at the first block whose body is unavailable, rather than skipping it
    /// and advertising later blocks. In prune mode it applies the same
    /// recent-block safety window even when an older body happens to remain
    /// on disk.
    pub fn block_hashes_after_locator_for_getblocks(
        &self,
        locator: &[BlockHash],
        stop_hash: BlockHash,
        max_blocks: usize,
    ) -> Vec<BlockHash> {
        let recent_blocks = MIN_BLOCKS_TO_KEEP.saturating_sub(
            u32::try_from(3600 / self.network.params().pow_target_spacing).unwrap_or(u32::MAX),
        );
        let oldest_allowed_height = self.height().saturating_sub(recent_blocks);
        self.headers_after_locator(locator, stop_hash)
            .into_iter()
            .take_while(|header| {
                let hash = header.block_hash();
                if hash == stop_hash || !self.store.contains(&hash) {
                    return false;
                }
                !self.is_pruned()
                    || self
                        .block_height_by_hash(&hash)
                        .is_some_and(|height| height > oldest_allowed_height)
            })
            .take(max_blocks)
            .map(|header| header.block_hash())
            .collect()
    }

    /// Match Core's special `getheaders` behavior for a null locator.
    ///
    /// A null locator is not a request for the active chain from genesis. Core
    /// uses it to request exactly the stop header, and ignores the request if
    /// that hash is null, unknown, or not eligible for serving.
    pub fn headers_for_getheaders(
        &self,
        locator: &[BlockHash],
        stop_hash: BlockHash,
        max_age_secs: u64,
    ) -> Option<Vec<bitcoin::block::Header>> {
        if locator.is_empty() {
            if stop_hash == BlockHash::all_zeros()
                || !self.block_request_allowed(&stop_hash, max_age_secs)
            {
                return None;
            }
            return self.header_by_hash(&stop_hash).map(|header| vec![header]);
        }

        // During headers-first synchronization the best-known header chain
        // can extend well beyond the active chain (notably while an
        // AssumeUTXO node is waiting for its snapshot body).  Core serves
        // that branch from the global block index, rather than returning an
        // empty range from the active-chain header vector.
        let best_header = self.best_header_tip().hash;
        let mut path = Vec::new();
        let mut cursor = best_header;
        loop {
            path.push(cursor);
            if cursor == self.network_genesis_hash() {
                break;
            }
            let Some(node) = self.block_index.get(&cursor) else {
                return Some(Vec::new());
            };
            cursor = node.header.prev_blockhash;
        }
        path.reverse();

        if let Some(snapshot_base) = self.snapshot_base.filter(|_| !self.snapshot_validated)
            && let Some(base_index) = path.iter().position(|hash| *hash == snapshot_base)
        {
            path.truncate(base_index.saturating_add(1));
        }

        let fork_height = locator.iter().find_map(|hash| {
            self.block_index
                .get(hash)
                .filter(|_| self.is_descendant_or_self(&best_header, hash))
                .map(|node| node.height)
        });
        let start = fork_height
            .and_then(|height| usize::try_from(height).ok())
            .and_then(|height| height.checked_add(1))
            .unwrap_or_default();
        let stop = if stop_hash == BlockHash::all_zeros() {
            path.len()
        } else {
            path.iter()
                .position(|hash| *hash == stop_hash)
                .map_or(path.len(), |height| height.saturating_add(1))
        };
        if start >= stop || start >= path.len() {
            return Some(Vec::new());
        }
        Some(
            path[start..stop.min(path.len())]
                .iter()
                .filter_map(|hash| self.block_index.get(hash).map(|node| node.header))
                .take(2_000)
                .collect(),
        )
    }

    /// Validate and index a contiguous header batch without requiring the
    /// corresponding full blocks yet. This is the headers-first sync boundary
    /// used by the peer manager.
    pub fn accept_headers(&mut self, headers: &[bitcoin::block::Header]) -> Result<Vec<BlockHash>> {
        let (hashes, inserted) = self.accept_headers_internal(headers)?;
        if inserted {
            self.persist_metadata()?;
        }
        Ok(hashes)
    }

    fn accept_headers_internal(
        &mut self,
        headers: &[bitcoin::block::Header],
    ) -> Result<(Vec<BlockHash>, bool)> {
        let mut hashes = Vec::with_capacity(headers.len());
        let mut inserted = false;
        for header in headers {
            let hash = header.block_hash();
            if let Some(existing) = self.block_index.get(&hash) {
                if existing.header != *header {
                    bail!("header hash collision for {hash}");
                }
                if self.has_invalid_ancestor(hash) {
                    bail!("header {hash} is on an invalidated branch");
                }
                hashes.push(hash);
                continue;
            }
            let parent_hash = header.prev_blockhash;
            let parent = self
                .block_index
                .get(&parent_hash)
                .copied()
                .with_context(|| format!("header {hash} has an unknown parent {parent_hash}"))?;
            if self.has_invalid_ancestor(parent_hash) {
                bail!("header {hash} has an invalidated parent {parent_hash}");
            }
            validation::validate_bip94_timewarp_with_params(
                &self.deployment_parameters,
                parent.height.saturating_add(1),
                header.time,
                parent.header.time,
            )?;
            validation::validate_block_version_with_params(
                &self.deployment_parameters,
                parent.height.saturating_add(1),
                header.version.to_consensus(),
            )?;
            self.validate_header_context(
                header,
                parent_hash,
                self.expected_target_for_parent(parent_hash, header.time),
                self.median_time_past_for_parent(parent_hash),
                true,
            )?;
            self.block_index.insert(
                hash,
                BlockNode {
                    header: *header,
                    height: parent.height.saturating_add(1),
                    chain_work: parent.chain_work + header.work(),
                },
            );
            self.assign_header_sequence_id(hash);
            inserted = true;
            hashes.push(hash);
        }
        Ok((hashes, inserted))
    }

    pub fn block(&mut self, hash: &BlockHash) -> Result<Option<Block>> {
        if self.is_block_pruned(hash) {
            return Ok(None);
        }
        self.store.get(hash)
    }

    pub fn block_for_serving(&self, hash: &BlockHash) -> Result<Option<Block>> {
        if self.is_block_pruned(hash) {
            return Ok(None);
        }
        self.store.get_readonly(hash)
    }

    pub fn block_store_reader(&self) -> BlockStoreReader {
        self.store.reader()
    }

    pub fn disconnected_suffix_has_non_coinbase_transactions(
        &mut self,
        previous_tip: BlockHash,
    ) -> Result<bool> {
        let active = self.active_chain.iter().copied().collect::<HashSet<_>>();
        let mut cursor = previous_tip;
        while !active.contains(&cursor) {
            if self
                .store
                .transaction_count(&cursor)?
                .is_none_or(|count| count > 1)
            {
                return Ok(true);
            }
            cursor = self
                .block_index
                .get(&cursor)
                .context("previous active tip is not indexed")?
                .header
                .prev_blockhash;
        }
        Ok(false)
    }

    pub fn active_blocks_after(&mut self, previous_tip: BlockHash) -> Result<Vec<Block>> {
        if previous_tip == self.best_hash() {
            return Ok(Vec::new());
        }
        let active: HashSet<BlockHash> = self.active_chain.iter().copied().collect();
        let mut cursor = previous_tip;
        let common = loop {
            if active.contains(&cursor) {
                break cursor;
            }
            cursor = self
                .block_index
                .get(&cursor)
                .context("previous active tip is not indexed")?
                .header
                .prev_blockhash;
        };
        let start = self
            .active_chain
            .iter()
            .position(|hash| *hash == common)
            .expect("common active ancestor is in active chain")
            .saturating_add(1);
        self.active_chain[start..]
            .iter()
            .map(|hash| {
                self.store
                    .get(hash)?
                    .with_context(|| format!("active block {hash} is missing"))
            })
            .collect()
    }

    pub fn disconnected_blocks_after(&mut self, previous_tip: BlockHash) -> Result<Vec<Block>> {
        let active: HashSet<BlockHash> = self.active_chain.iter().copied().collect();
        if active.contains(&previous_tip) {
            return Ok(Vec::new());
        }
        let mut path = Vec::new();
        let mut cursor = previous_tip;
        while !active.contains(&cursor) {
            path.push(cursor);
            cursor = self
                .block_index
                .get(&cursor)
                .context("previous active tip is not indexed")?
                .header
                .prev_blockhash;
        }
        path.reverse();
        path.into_iter()
            .map(|hash| {
                self.store
                    .get(&hash)?
                    .with_context(|| format!("disconnected block {hash} is missing"))
            })
            .collect()
    }

    fn transaction_at_location(
        &mut self,
        txid: &Txid,
        location: TxLocation,
    ) -> Result<Option<(Transaction, TxLocation)>> {
        if let Some(block) = self.store.get(&location.block_hash)? {
            let Some(transaction) = block.txdata.get(location.transaction_index).cloned() else {
                bail!("transaction index is inconsistent with stored block");
            };
            return Ok(Some((transaction, location)));
        }
        let Some(store) = self.electrum_store.as_mut() else {
            return Ok(None);
        };
        let Some(transaction) =
            store.transaction(&location.block_hash, location.transaction_index)?
        else {
            return Ok(None);
        };
        if transaction.compute_txid() != *txid {
            bail!("Electrum transaction sidecar does not match transaction index");
        }
        Ok(Some((transaction, location)))
    }

    /// Return a transaction from the active chain only.
    ///
    /// Electrum indexes the best chain, whereas [`Self::transaction`] also
    /// serves side-chain transactions when the optional Core-style `-txindex`
    /// is enabled.
    pub fn active_transaction(&mut self, txid: &Txid) -> Result<Option<(Transaction, TxLocation)>> {
        for location in self.active_transaction_locations(txid) {
            if let Some((transaction, location)) = self.transaction_at_location(txid, location)? {
                if transaction.compute_txid() == *txid {
                    return Ok(Some((transaction, location)));
                }
            }
        }
        Ok(None)
    }

    /// Return active-chain locations in Electrum's chronological order.
    /// Ordinary txids take the fast single-map path; only duplicate txids use
    /// the side index.
    pub(crate) fn active_transaction_locations(&self, txid: &Txid) -> Vec<TxLocation> {
        let mut compact_locations = self
            .tx_index_duplicates
            .get(txid)
            .cloned()
            .unwrap_or_default();
        if let Some(location) = self.tx_index.get(txid)
            && !compact_locations
                .iter()
                .any(|candidate| candidate == location)
        {
            compact_locations.push(*location);
        }
        compact_locations.sort_by_key(|location| (location.height, location.transaction_index));
        compact_locations
            .into_iter()
            .filter_map(|location| self.expand_active_tx_location(location))
            .collect()
    }

    fn expand_active_tx_location(&self, location: ActiveTxLocation) -> Option<TxLocation> {
        self.active_chain
            .get(usize::try_from(location.height).ok()?)
            .copied()
            .map(|block_hash| TxLocation {
                block_hash,
                height: location.height,
                transaction_index: location.transaction_index,
            })
    }

    fn active_tx_index_for_snapshot(&self) -> Result<HashMap<Txid, TxLocation>> {
        self.tx_index
            .iter()
            .map(|(txid, location)| {
                Ok((
                    *txid,
                    self.expand_active_tx_location(*location).with_context(|| {
                        format!(
                            "active transaction {} points outside the active chain",
                            txid
                        )
                    })?,
                ))
            })
            .collect()
    }

    fn active_tx_duplicates_for_snapshot(&self) -> Result<HashMap<Txid, Vec<TxLocation>>> {
        self.tx_index_duplicates
            .iter()
            .map(|(txid, locations)| {
                let locations = locations
                    .iter()
                    .map(|location| {
                        self.expand_active_tx_location(*location).with_context(|| {
                            format!(
                                "duplicate transaction {} points outside the active chain",
                                txid
                            )
                        })
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ok((*txid, locations))
            })
            .collect()
    }

    /// Find an active occurrence at an exact height, including a duplicate
    /// txid whose latest location is in a later block.
    pub(crate) fn active_transaction_location_at_height(
        &self,
        txid: &Txid,
        height: u32,
    ) -> Option<TxLocation> {
        self.active_transaction_locations(txid)
            .into_iter()
            .find(|location| location.height == height)
    }

    pub fn transaction(&mut self, txid: &Txid) -> Result<Option<(Transaction, TxLocation)>> {
        let location = self
            .tx_index
            .get(txid)
            .and_then(|location| self.expand_active_tx_location(*location))
            .or_else(|| self.tx_index_all.get(txid).cloned());
        let Some(location) = location else {
            return Ok(None);
        };
        self.transaction_at_location(txid, location)
    }

    pub fn transaction_location(&self, txid: &Txid) -> Option<TxLocation> {
        self.tx_index
            .get(txid)
            .and_then(|location| self.expand_active_tx_location(*location))
    }

    pub fn spending_transaction(
        &self,
        outpoint: &OutPoint,
    ) -> Option<(Txid, usize, BlockHash, u32)> {
        self.txospender_index_enabled
            .then(|| self.spent_by.get(outpoint).copied())
            .flatten()
    }

    pub fn get_history(&self, script_hash: &str) -> Vec<HistoryEntry> {
        self.get_history_checked(script_hash).unwrap_or_default()
    }

    pub fn get_history_checked(&self, script_hash: &str) -> Result<Vec<HistoryEntry>> {
        if self.history_materialized {
            return Ok(self.history.get(script_hash).cloned().unwrap_or_default());
        }
        Ok(self
            .electrum_history_store
            .get(script_hash)?
            .into_iter()
            .map(|(txid, height)| HistoryEntry { txid, height })
            .collect())
    }

    pub fn script_hashes(&self) -> Vec<String> {
        if self.history_materialized {
            self.history.keys().cloned().collect()
        } else {
            self.electrum_history_store.keys()
        }
    }

    pub fn get_utxos(&self, script_hash: &str) -> Vec<(OutPoint, UtxoEntry)> {
        self.utxo_store
            .entries()
            .unwrap_or_default()
            .into_iter()
            .filter(|(_, entry)| electrum_script_hash(&entry.output.script_pubkey) == script_hash)
            .map(|(outpoint, entry)| {
                (
                    outpoint,
                    UtxoEntry {
                        output: entry.output,
                        height: entry.height,
                        median_time_past: entry.median_time_past,
                        coinbase: entry.coinbase,
                    },
                )
            })
            .collect()
    }

    /// Return the active-chain outputs that electrs would consider unspent
    /// for a script hash.  Unlike Core's UTXO set, electrs keeps matching
    /// outputs whose scripts are provably unspendable (for example
    /// `OP_RETURN`) in its scripthash status index.  The Electrum node path
    /// enables the durable spender index, which lets this projection retain
    /// those outputs without polluting consensus UTXO accounting.
    pub(crate) fn electrum_unspent_for_script(
        &mut self,
        script_hash: &str,
    ) -> Result<Vec<(OutPoint, i64, usize, u64)>> {
        let mut outputs = HashMap::new();
        for history in self.get_history_checked(script_hash)? {
            let Some(location) =
                self.active_transaction_location_at_height(&history.txid, history.height)
            else {
                continue;
            };
            let Some((transaction, location)) =
                self.transaction_at_location(&history.txid, location)?
            else {
                continue;
            };
            for (vout, output) in transaction.output.iter().enumerate() {
                if electrum_script_hash(&output.script_pubkey) != script_hash {
                    continue;
                }
                let outpoint = OutPoint::new(history.txid, vout as u32);
                let unspent = if self.utxo_store.contains(&outpoint) {
                    true
                } else {
                    // The Electrum integration enables this index before it
                    // serves requests.  Without it, an output absent from
                    // the consensus UTXO set cannot be distinguished from a
                    // spendable output that was already spent.
                    self.txospender_index_enabled && self.spending_transaction(&outpoint).is_none()
                };
                if unspent {
                    outputs.insert(
                        outpoint,
                        (
                            i64::from(location.height),
                            location.transaction_index,
                            output.value.to_sat(),
                        ),
                    );
                }
            }
        }
        let mut outputs = outputs
            .into_iter()
            .map(|(outpoint, (height, transaction_index, value))| {
                (outpoint, height, transaction_index, value)
            })
            .collect::<Vec<_>>();
        outputs.sort_by(|left, right| {
            left.1
                .cmp(&right.1)
                .then_with(|| left.2.cmp(&right.2))
                .then_with(|| left.0.txid.cmp(&right.0.txid))
                .then_with(|| left.0.vout.cmp(&right.0.vout))
        });
        Ok(outputs)
    }

    pub fn utxo(&self, outpoint: &OutPoint) -> Option<UtxoEntry> {
        self.utxo_checked(outpoint).ok().flatten()
    }

    pub fn utxo_checked(&self, outpoint: &OutPoint) -> Result<Option<UtxoEntry>> {
        if self.missing_utxo_cache.lock().contains(outpoint) {
            return Ok(None);
        }
        let entry = self
            .utxo_store
            .get(outpoint)?
            .map(Self::decoded_utxo)
            .or_else(|| self.utxos.get(outpoint).cloned());
        if entry.is_none() {
            self.missing_utxo_cache.lock().insert(*outpoint);
        }
        Ok(entry)
    }

    pub fn all_utxos(&self) -> impl Iterator<Item = (OutPoint, UtxoEntry)> {
        self.all_utxos_checked()
            .unwrap_or_else(|_| {
                self.utxos
                    .iter()
                    .map(|(outpoint, entry)| (*outpoint, entry.clone()))
                    .collect()
            })
            .into_iter()
    }

    pub fn all_utxos_checked(&self) -> Result<Vec<(OutPoint, UtxoEntry)>> {
        let entries = self
            .utxo_store
            .entries()?
            .into_iter()
            .map(|(outpoint, entry)| (outpoint, Self::decoded_utxo(entry)))
            .collect::<Vec<_>>();
        if entries.is_empty() && !self.utxos.is_empty() {
            return Ok(self
                .utxos
                .iter()
                .map(|(outpoint, entry)| (*outpoint, entry.clone()))
                .collect());
        }
        Ok(entries)
    }

    pub fn utxo_stats(&self) -> (usize, usize, u64) {
        let stats = self.utxo_statistics(false, false);
        (stats.transactions, stats.outputs, stats.total_amount_sat)
    }

    /// Return the number of transactions in the active chain through the tip.
    /// This is the chain transaction count reported by UTXO snapshot RPCs.
    pub fn active_transaction_count(&self) -> usize {
        self.tx_index.len()
    }

    pub fn utxo_bogo_size(&self) -> u64 {
        self.utxo_statistics(false, false).bogo_size
    }

    /// Calculate statistics for the active UTXO set. Hashes are optional so a
    /// caller requesting `none` does not pay for either cryptographic pass.
    pub fn utxo_statistics(
        &self,
        include_serialized_hash: bool,
        include_muhash: bool,
    ) -> UtxoSetStats {
        if let Some(coin_stats) = &self.coin_stats {
            if !include_serialized_hash {
                return coin_stats.statistics(include_muhash);
            }
            let entries = self.active_utxo_entries_for_read();
            let mut statistics = calculate_utxo_statistics_from_entries(&entries, true, false);
            if include_muhash {
                statistics.muhash = Some(coin_stats.muhash.finalize());
            }
            return statistics;
        }
        let entries = self.active_utxo_entries_for_read();
        calculate_utxo_statistics_from_entries(&entries, include_serialized_hash, include_muhash)
    }

    pub fn utxo_statistics_without_index(
        &self,
        include_serialized_hash: bool,
        include_muhash: bool,
    ) -> UtxoSetStats {
        let entries = self.active_utxo_entries_for_read();
        calculate_utxo_statistics_from_entries(&entries, include_serialized_hash, include_muhash)
    }

    /// Calculate UTXO statistics at a stored block. A historical state is
    /// reconstructed by replaying the validated branch from genesis; the
    /// caller holds the chain write lock because the replay reads through the
    /// append-only block store.
    pub fn utxo_statistics_at(
        &mut self,
        hash: BlockHash,
        include_serialized_hash: bool,
        include_muhash: bool,
    ) -> Result<Option<(u32, UtxoSetStats)>> {
        let Some(node) = self.block_index.get(&hash).copied() else {
            return Ok(None);
        };
        let utxos = if hash == self.best_hash() {
            self.active_utxo_map_for_read()
        } else {
            let Some(utxos) = self.replay_utxos_for_block(hash, false)? else {
                return Ok(None);
            };
            utxos
        };
        Ok(Some((
            node.height,
            calculate_utxo_statistics(&utxos, include_serialized_hash, include_muhash),
        )))
    }

    pub fn signet_challenge(&self) -> Option<&[u8]> {
        self.signet_challenge.as_deref()
    }

    pub fn deployment_parameters(&self) -> validation::DeploymentParameters {
        self.deployment_parameters
    }

    pub fn utxo_serialized_hash(&self) -> String {
        self.utxo_statistics(true, false)
            .serialized_hash
            .expect("serialized hash was requested")
    }

    /// Return the Core-compatible MuHash commitment for the active UTXO set.
    pub fn utxo_muhash(&self) -> String {
        self.utxo_statistics(false, true)
            .muhash
            .expect("MuHash was requested")
    }

    /// Return the newest block at which this implementation persists a
    /// periodic chainstate snapshot. It is the default target for a rollback
    /// request that does not name an explicit height or hash.
    pub fn latest_snapshot_hash(&self) -> BlockHash {
        if let Some(snapshot) = self
            .assumeutxo_data()
            .iter()
            .rev()
            .find(|snapshot| snapshot.height <= self.height())
            && let Ok(hash) = snapshot.blockhash.parse::<BlockHash>()
            && self.is_active_block(&hash)
        {
            return hash;
        }
        let height = self.height() / SNAPSHOT_INTERVAL * SNAPSHOT_INTERVAL;
        self.block_hash(height)
            .expect("the periodic snapshot target is on the active chain")
    }

    pub fn dump_utxo_set(&self, path: impl AsRef<Path>) -> Result<(u64, BlockHash, u32)> {
        let utxos = self.load_utxo_map_from_store()?;
        write_core_utxo_snapshot(
            path.as_ref(),
            self.network,
            self.signet_challenge.as_deref(),
            self.best_hash(),
            &utxos,
        )?;
        Ok((utxos.len() as u64, self.best_hash(), self.height()))
    }

    /// Write a snapshot for an active historical block without changing the
    /// node's active chainstate. This is the equivalent of Core's temporary
    /// rollback used by `dumptxoutset ... rollback`.
    pub fn dump_utxo_set_at(
        &mut self,
        path: impl AsRef<Path>,
        target_hash: BlockHash,
    ) -> Result<(u64, BlockHash, u32, String, usize)> {
        let target = self
            .block_index
            .get(&target_hash)
            .copied()
            .context("rollback target is unknown")?;
        let target_height = target.height;
        if !self.is_active_block(&target_hash) {
            bail!("rollback target is not on the active chain")
        }

        let utxos = if target_hash == self.best_hash() {
            self.load_utxo_map_from_store()?
        } else {
            self.replay_utxos_for_block(target_hash, false)?
                .context("could not reconstruct the historical UTXO set")?
        };
        let active_hashes: HashSet<BlockHash> = self
            .active_chain
            .iter()
            .take(target_height as usize + 1)
            .copied()
            .collect();
        let tx_index = self
            .tx_index
            .iter()
            .filter_map(|(txid, location)| {
                let location = self.expand_active_tx_location(*location)?;
                (location.height <= target_height && active_hashes.contains(&location.block_hash))
                    .then_some((*txid, location))
            })
            .collect();
        let tx_index_duplicates = self
            .tx_index_duplicates
            .iter()
            .filter_map(|(txid, locations)| {
                let locations = locations
                    .iter()
                    .filter_map(|location| {
                        let location = self.expand_active_tx_location(*location)?;
                        (location.height <= target_height
                            && active_hashes.contains(&location.block_hash))
                        .then_some(location)
                    })
                    .collect::<Vec<_>>();
                (!locations.is_empty()).then_some((*txid, locations))
            })
            .collect();
        let tx_index_all = self
            .tx_index_all
            .iter()
            .filter(|(_, location)| {
                location.height <= target_height && active_hashes.contains(&location.block_hash)
            })
            .map(|(txid, location)| (*txid, location.clone()))
            .collect();
        let active_history = self.active_history_map_for_read()?;
        let history = active_history
            .iter()
            .filter_map(|(script_hash, entries)| {
                let entries = entries
                    .iter()
                    .filter(|entry| entry.height <= target_height)
                    .cloned()
                    .collect::<Vec<_>>();
                (!entries.is_empty()).then_some((script_hash.clone(), entries))
            })
            .collect();
        let spent_by = self.txospender_index_enabled.then(|| {
            self.spent_by
                .iter()
                .filter(|(_, (_, _, block_hash, height))| {
                    *height <= target_height && active_hashes.contains(block_hash)
                })
                .map(|(outpoint, spender)| (*outpoint, *spender))
                .collect()
        });
        let snapshot = ChainSnapshot {
            tip: target_hash.to_string(),
            headers: self
                .headers
                .iter()
                .take(target_height as usize + 1)
                .copied()
                .collect(),
            utxos,
            tx_index,
            tx_index_duplicates,
            tx_index_all,
            history,
            spent_by,
            prune_height: self.prune_height,
        };
        let stats = calculate_utxo_statistics(&snapshot.utxos, true, false);
        let serialized_hash = stats
            .serialized_hash
            .clone()
            .context("historical UTXO hash was not calculated")?;
        let coins_written = snapshot.utxos.len() as u64;
        let nchaintx = self
            .chain_transaction_count(target_height)
            .unwrap_or(snapshot.tx_index.len() as u64) as usize;
        let path = path.as_ref();
        write_core_utxo_snapshot(
            path,
            self.network,
            self.signet_challenge.as_deref(),
            target_hash,
            &snapshot.utxos,
        )?;
        Ok((
            coins_written,
            target_hash,
            target_height,
            serialized_hash,
            nchaintx,
        ))
    }

    /// Load a local snapshot using the implementation's compatibility
    /// formats. This helper intentionally accepts arbitrary active-chain
    /// snapshots and is separate from strict Core RPC activation.
    pub fn load_utxo_set(&mut self, path: impl AsRef<Path>) -> Result<(u64, BlockHash, u32)> {
        self.load_utxo_set_with_options(path, false)
    }

    /// Load a Core UTXO snapshot through the AssumeUTXO trust boundary.
    /// Snapshot activation is restricted to the v31.1 hardcoded commitments.
    pub fn load_assumeutxo_set(&mut self, path: impl AsRef<Path>) -> Result<(u64, BlockHash, u32)> {
        self.load_utxo_set_with_options(path, true)
    }

    fn load_utxo_set_with_options(
        &mut self,
        path: impl AsRef<Path>,
        strict_assumeutxo: bool,
    ) -> Result<(u64, BlockHash, u32)> {
        let bytes = fs::read(path.as_ref())
            .with_context(|| format!("reading UTXO snapshot {}", path.as_ref().display()))?;
        if strict_assumeutxo || bytes.starts_with(&CORE_UTXO_SNAPSHOT_MAGIC) {
            let (result, _fully_validated) = self.load_core_utxo_set(&bytes, strict_assumeutxo)?;
            if strict_assumeutxo {
                // Core keeps a separate snapshot-chainstate directory until
                // the background chainstate has been validated.  The
                // directory is also the durable marker used on the next
                // startup to perform the cleanup outside normal block
                // processing.
                fs::create_dir_all(self.snapshot_chainstate_path())?;
                self.snapshot_base = Some(result.1);
                // Strict activation always creates a second, independently
                // replayed chainstate.  Even when local block data happens to
                // be complete, doing the replay asynchronously preserves the
                // same trust boundary as Core and keeps RPC activation fast.
                self.snapshot_validated = false;
                self.snapshot_validation_error = None;
                self.persist_snapshot_provenance()?;
                self.start_background_validation()?;
            } else {
                self.clear_snapshot_provenance()?;
            }
            return Ok(result);
        }
        let snapshot: ChainSnapshot = serde_json::from_slice(&bytes)
            .with_context(|| format!("decoding UTXO snapshot {}", path.as_ref().display()))?;
        if snapshot.tip != self.best_hash().to_string()
            || snapshot.headers.len() != self.headers.len()
            || snapshot
                .headers
                .iter()
                .zip(&self.headers)
                .any(|(snapshot, current)| snapshot.block_hash() != current.block_hash())
        {
            bail!("UTXO snapshot does not match the active chain")
        }
        self.validate_snapshot_utxos(&snapshot.utxos)?;
        if self.prune_height.is_none() {
            let expected = self
                .replay_utxos_for_block(self.best_hash(), false)?
                .context("cannot verify UTXO snapshot because active block data is unavailable")?;
            if expected != snapshot.utxos {
                bail!("UTXO snapshot contents do not match the active chain")
            }
        }
        self.utxos = snapshot.utxos;
        self.utxos_materialized = true;
        self.block_undo_cache.clear();
        self.persist_snapshot()?;
        self.clear_snapshot_provenance()?;
        Ok((self.utxos.len() as u64, self.best_hash(), self.height()))
    }

    fn load_core_utxo_set(
        &mut self,
        bytes: &[u8],
        strict_assumeutxo: bool,
    ) -> Result<((u64, BlockHash, u32), bool)> {
        if strict_assumeutxo && self.snapshot_base.is_some() {
            bail!("Can't activate a snapshot-based chainstate more than once")
        }
        let mut snapshot =
            read_core_utxo_snapshot(bytes, self.network, self.signet_challenge.as_deref())?;
        let commitment = if strict_assumeutxo {
            Some(
                self.assumeutxo_for_block(snapshot.base_hash)
                    .with_context(|| {
                        let heights = self
                            .assumeutxo_data()
                            .iter()
                            .map(|data| data.height.to_string())
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!(
                            "assumeutxo block hash in snapshot metadata not recognized (hash: {}). The following snapshot heights are available: {}.",
                            snapshot.base_hash, heights
                        )
                    })?,
            )
        } else {
            None
        };
        let Some(base_height) = self.block_height_by_hash(&snapshot.base_hash) else {
            bail!(
                "The base block header ({}) must appear in the headers chain. Make sure all headers are syncing, and call loadtxoutset again.",
                snapshot.base_hash
            )
        };
        if self.has_invalid_ancestor(snapshot.base_hash) {
            bail!(
                "The base block header ({}) is part of an invalid chain.",
                snapshot.base_hash
            )
        }
        if strict_assumeutxo
            && self.ancestor_hash(self.best_header_tip().hash, base_height)
                != Some(snapshot.base_hash)
        {
            bail!(
                "A forked headers-chain with more work than the chain with the snapshot base block header exists. Please proceed to sync without AssumeUtxo."
            )
        }
        if strict_assumeutxo
            && self
                .block_index
                .get(&snapshot.base_hash)
                .is_some_and(|node| node.chain_work <= self.tip().work)
        {
            bail!("Population failed: Work does not exceed active chainstate.")
        }
        if snapshot
            .utxos
            .values()
            .any(|entry| entry.height > base_height)
        {
            bail!("Population failed: Bad snapshot data after deserializing 0 coins")
        }
        if snapshot
            .utxos
            .values()
            .any(|entry| entry.output.value > Amount::MAX_MONEY)
        {
            bail!(
                "Population failed: Bad snapshot data after deserializing 0 coins - bad tx out value"
            )
        }
        if strict_assumeutxo {
            let commitment = commitment.expect("strict AssumeUTXO commitment is present");
            if base_height != commitment.height {
                bail!(
                    "UTXO snapshot base {} has height {}, expected committed height {}",
                    snapshot.base_hash,
                    base_height,
                    commitment.height
                );
            }
            let actual_hash = calculate_utxo_statistics(&snapshot.utxos, true, false)
                .serialized_hash
                .context("UTXO snapshot serialized hash was not calculated")?;
            if actual_hash != commitment.hash_serialized {
                bail!(
                    "Population failed: Bad snapshot content hash: expected {}, got {}.",
                    commitment.hash_serialized,
                    actual_hash
                );
            }
        }
        for entry in snapshot.utxos.values_mut() {
            entry.median_time_past = if entry.height == 0 {
                0
            } else {
                let parent = self
                    .ancestor_hash(snapshot.base_hash, entry.height - 1)
                    .context("UTXO snapshot entry is outside the base chain")?;
                self.median_time_past_for_parent(parent)
            };
        }
        if strict_assumeutxo {
            self.validate_snapshot_utxo_shape(&snapshot.utxos, base_height)?;
        } else {
            self.validate_snapshot_utxos_at(&snapshot.utxos, snapshot.base_hash)?;
        }
        if strict_assumeutxo {
            self.persist_assumeutxo_base_snapshot(snapshot.base_hash, &snapshot.utxos)?;
        }
        let fully_validated = if strict_assumeutxo {
            false
        } else if let Some(expected) = self.replay_utxos_for_block(snapshot.base_hash, false)? {
            if expected != snapshot.utxos {
                bail!("UTXO snapshot contents do not match the base chain")
            }
            true
        } else {
            false
        };

        let active_height = self.height();
        if base_height < active_height {
            let mut utxos = snapshot.utxos;
            for height in base_height + 1..=active_height {
                let block_hash = self.active_chain[height as usize];
                let block = self
                    .store
                    .get(&block_hash)?
                    .with_context(|| {
                        format!(
                            "cannot advance UTXO snapshot past height {base_height}: block {block_hash} is unavailable"
                        )
                    })?;
                let parent_hash = block.header.prev_blockhash;
                let parent = self
                    .block_index
                    .get(&parent_hash)
                    .copied()
                    .context("UTXO snapshot forward replay parent is not indexed")?;
                validation::validate_bip94_timewarp_with_params(
                    &self.deployment_parameters,
                    height,
                    block.header.time,
                    parent.header.time,
                )?;
                self.validate_header_context(
                    &block.header,
                    parent_hash,
                    self.expected_target_for_parent(parent_hash, block.header.time),
                    self.median_time_past_for_parent(parent_hash),
                    true,
                )?;
                self.validate_block_structure(
                    &block,
                    self.network,
                    height,
                    Amount::MAX_MONEY.to_sat(),
                )?;
                let median_time_past = self.median_time_past_for_parent(parent_hash);
                let application = self.validate_block_transactions_with_options(
                    &block,
                    height,
                    &utxos,
                    median_time_past,
                    false,
                )?;
                apply_block_to_utxos(
                    &mut utxos,
                    &block,
                    height,
                    median_time_past,
                    application.spent_entries,
                );
            }
            snapshot.utxos = utxos;
        }
        let coins_count = snapshot.coins_count;
        let base_hash = snapshot.base_hash;
        self.utxos = snapshot.utxos;
        self.utxos_materialized = true;
        self.block_undo_cache.clear();
        self.persist_snapshot()?;
        Ok(((coins_count, base_hash, base_height), fully_validated))
    }

    fn validate_snapshot_utxos(&mut self, utxos: &HashMap<OutPoint, UtxoEntry>) -> Result<()> {
        self.validate_snapshot_utxos_at(utxos, self.best_hash())
    }

    fn validate_snapshot_utxo_shape(
        &self,
        utxos: &HashMap<OutPoint, UtxoEntry>,
        tip_height: u32,
    ) -> Result<()> {
        for entry in utxos.values() {
            if entry.height > tip_height {
                bail!("UTXO snapshot contains an output from the future")
            }
            if entry.output.value > Amount::MAX_MONEY {
                bail!("UTXO snapshot contains an output above the money range")
            }
        }
        Ok(())
    }

    fn validate_snapshot_utxos_at(
        &mut self,
        utxos: &HashMap<OutPoint, UtxoEntry>,
        tip_hash: BlockHash,
    ) -> Result<()> {
        let tip_height = self
            .block_height_by_hash(&tip_hash)
            .context("UTXO snapshot target block is not indexed")?;
        if !self.is_active_block(&tip_hash) {
            bail!("UTXO snapshot target block is not on the active chain")
        }
        self.validate_snapshot_utxo_shape(utxos, tip_height)?;
        let mut entries_by_block: HashMap<BlockHash, Vec<(&OutPoint, &UtxoEntry, TxLocation)>> =
            HashMap::new();
        for (outpoint, entry) in utxos {
            if entry.height > tip_height {
                bail!("UTXO snapshot contains an output from the future")
            }
            if entry.output.value > Amount::MAX_MONEY {
                bail!("UTXO snapshot contains an output above the money range")
            }
            let location = if self.tx_index_all_enabled {
                self.tx_index_all.get(&outpoint.txid).cloned().or_else(|| {
                    self.tx_index
                        .get(&outpoint.txid)
                        .and_then(|location| self.expand_active_tx_location(*location))
                })
            } else {
                self.tx_index
                    .get(&outpoint.txid)
                    .and_then(|location| self.expand_active_tx_location(*location))
            }
            .with_context(|| {
                format!(
                    "UTXO snapshot references unknown transaction {}",
                    outpoint.txid
                )
            })?;
            if location.height != entry.height
                || self.ancestor_hash(tip_hash, location.height) != Some(location.block_hash)
            {
                bail!("UTXO snapshot references an inactive or mismatched transaction")
            }
            entries_by_block
                .entry(location.block_hash)
                .or_default()
                .push((outpoint, entry, location.clone()));
        }

        for (block_hash, entries) in entries_by_block {
            let Some(block) = self.store.get(&block_hash)? else {
                continue;
            };
            for (outpoint, entry, location) in entries {
                let transaction =
                    block
                        .txdata
                        .get(location.transaction_index)
                        .with_context(|| {
                            format!(
                                "UTXO snapshot transaction index is invalid for {}",
                                location.block_hash
                            )
                        })?;
                let output = transaction
                    .output
                    .get(outpoint.vout as usize)
                    .with_context(|| {
                        format!(
                            "UTXO snapshot output index is invalid for {}",
                            outpoint.txid
                        )
                    })?;
                if output != &entry.output
                    || entry.coinbase != (location.transaction_index == 0)
                    || (location.height != 0
                        && entry.median_time_past
                            != self.median_time_past_for_parent(
                                self.ancestor_hash(tip_hash, location.height - 1)
                                    .context("UTXO transaction parent is not indexed")?,
                            ))
                {
                    bail!("UTXO snapshot output metadata does not match the active chain")
                }
            }
        }
        Ok(())
    }

    pub fn verify_active_chain(&mut self, depth: u32) -> Result<()> {
        self.verify_active_chain_with_level(3, depth)
    }

    /// Verify recent active-chain records with Core's `verifychain` levels.
    ///
    /// Level 0 reads and decodes block records, level 1 performs context-free
    /// block validation, level 2 validates undo shape, level 3 disconnects
    /// the requested suffix against the live UTXO set, and level 4 reconnects
    /// it while checking that the UTXO set is unchanged.  The verification
    /// state is entirely temporary, so this RPC never changes the serving
    /// chainstate.
    pub fn verify_active_chain_with_level(&mut self, check_level: u8, depth: u32) -> Result<()> {
        let check_level = check_level.min(4);
        let tip_height = self.height();
        if tip_height == 0 {
            return Ok(());
        }
        let block_count = if depth == 0 || depth > tip_height {
            tip_height
        } else {
            depth
        };
        let first_height = tip_height.saturating_sub(block_count).saturating_add(1);
        let mut blocks = Vec::with_capacity(block_count as usize);
        for height in first_height..=tip_height {
            let hash = *self
                .active_chain
                .get(height as usize)
                .with_context(|| format!("active chain is missing height {height}"))?;
            let node = self
                .block_index
                .get(&hash)
                .with_context(|| format!("active block {hash} is not indexed"))?;
            let block = match self.store.get(&hash)? {
                Some(block) => block,
                None if self.is_pruned() => {
                    tracing::info!(
                        "Block verification stopping at height {height} (no data). This could be due to pruning or use of an assumeutxo snapshot."
                    );
                    bail!("active block {hash} is missing from block store")
                }
                None => bail!("active block {hash} is missing from block store"),
            };
            if block.header != node.header {
                bail!("stored block header does not match active index at height {height}")
            }
            if check_level >= 1 {
                validation::validate_block_structure_for_verification(
                    &block,
                    &self.deployment_parameters,
                    height,
                    Amount::MAX_MONEY.to_sat(),
                    self.signet_challenge.as_deref(),
                )
                .with_context(|| {
                    format!(
                        "block structure verification failed at height {height} (segwit activation {})",
                        self.deployment_parameters.buried.segwit
                    )
                })?;
            }
            let undo = if check_level >= 2 {
                let undo = self
                    .store
                    .get_undo(&hash)?
                    .with_context(|| format!("undo for active block {hash} is missing"))?;
                self.validate_block_undo(&block, &undo)?;
                Some(undo)
            } else {
                None
            };
            blocks.push((height, block, undo));
        }

        if check_level < 3 {
            return Ok(());
        }

        let original_utxos = if self.utxos_materialized {
            self.utxos.clone()
        } else {
            self.load_utxo_map_from_store()?
        };
        let mut working_utxos = original_utxos.clone();
        for (height, block, undo) in blocks.iter().rev() {
            self.disconnect_block_for_verification(
                &mut working_utxos,
                block,
                *height,
                undo.as_ref().expect("level 3 verification loads undo"),
            )?;
        }

        if check_level < 4 {
            return Ok(());
        }

        // The two historical BIP30 repeats overwrite an older coinbase and
        // require special disconnect metadata that is intentionally not
        // represented in this node's compact undo format.  Reconstruct the
        // prefix independently in that rare full-depth case, then perform
        // the same reconnect check as ordinary blocks.
        if blocks
            .iter()
            .any(|(height, block, _)| is_bip30_repeat(self.network, *height, block.block_hash()))
        {
            let base_height = first_height.saturating_sub(1);
            let base_hash = self
                .active_chain
                .get(base_height as usize)
                .copied()
                .context("verification prefix is missing")?;
            working_utxos = self
                .replay_utxos_for_block(base_hash, false)?
                .context("verification prefix UTXO replay did not reach its base")?;
        }

        for (height, block, _) in &blocks {
            let median_time_past = self.median_time_past_for_parent(block.header.prev_blockhash);
            let application = self.validate_block_transactions_with_options(
                block,
                *height,
                &working_utxos,
                median_time_past,
                false,
            )?;
            apply_block_to_utxos(
                &mut working_utxos,
                block,
                *height,
                median_time_past,
                application.spent_entries,
            );
        }
        if working_utxos != original_utxos {
            bail!("active chain UTXO set changed during verification")
        }
        Ok(())
    }

    /// Validate a proposed block against the current active tip without
    /// storing it or changing chain state. This is the validation boundary
    /// used by RPC proposal/template clients.
    pub fn validate_candidate_block(&self, block: &Block) -> Result<()> {
        self.validate_candidate_block_internal(block, true)
    }

    /// Validate a block-template proposal without requiring the miner's
    /// proof-of-work nonce to be solved yet.
    pub fn validate_candidate_block_without_pow(&self, block: &Block) -> Result<()> {
        self.validate_candidate_block_internal(block, false)
    }

    /// Validate a mining-interface candidate with independently selectable
    /// proof-of-work and merkle-root checks.
    pub fn validate_candidate_block_with_options(
        &self,
        block: &Block,
        check_pow: bool,
        check_merkle_root: bool,
    ) -> Result<()> {
        self.validate_candidate_block_internal_with_options(block, check_pow, check_merkle_root)
    }

    fn validate_candidate_block_internal(&self, block: &Block, check_pow: bool) -> Result<()> {
        self.validate_candidate_block_internal_with_options(block, check_pow, true)
    }

    fn validate_candidate_block_internal_with_options(
        &self,
        block: &Block,
        check_pow: bool,
        check_merkle_root: bool,
    ) -> Result<()> {
        let parent_hash = block.header.prev_blockhash;
        if parent_hash != self.best_hash() {
            return Err(ValidationError::WrongPreviousBlock.into());
        }
        let height = self.height().saturating_add(1);
        let parent = self
            .block_index
            .get(&parent_hash)
            .expect("active tip is indexed");
        validation::validate_bip94_timewarp_with_params(
            &self.deployment_parameters,
            height,
            block.header.time,
            parent.header.time,
        )?;
        let expected_target = self.expected_target_for_parent(parent_hash, block.header.time);
        let median_time_past = self.median_time_past_for_parent(parent_hash);
        self.validate_header_context(
            &block.header,
            parent_hash,
            expected_target,
            median_time_past,
            check_pow,
        )?;
        validation::validate_block_structure_with_signet_options_with_params_and_merkle(
            block,
            &self.deployment_parameters,
            height,
            Amount::MAX_MONEY.to_sat(),
            self.signet_challenge.as_deref(),
            check_pow,
            check_merkle_root,
        )?;
        self.validate_block_transactions(block, height, &self.utxo_store, median_time_past)?;
        Ok(())
    }

    pub fn median_time_past_value(&self) -> u32 {
        self.median_time_past()
    }

    pub fn next_bits(&self, candidate_time: u32) -> u32 {
        self.expected_target(candidate_time)
            .to_compact_lossy()
            .to_consensus()
    }

    pub fn history_status(&self, script_hash: &str) -> Option<String> {
        let history = self.get_history_checked(script_hash).ok()?;
        if history.is_empty() {
            return None;
        }
        let mut input = String::new();
        for entry in history {
            input.push_str(&entry.txid.to_string());
            input.push(':');
            input.push_str(&entry.height.to_string());
            input.push(':');
        }
        Some(hex::encode(Sha256::digest(input.as_bytes())))
    }

    pub fn merkle_branch(&mut self, txid: &Txid) -> Result<Option<(Vec<Txid>, usize, u32)>> {
        let Some(location) = self
            .tx_index
            .get(txid)
            .and_then(|location| self.expand_active_tx_location(*location))
        else {
            return Ok(None);
        };
        let branch = if let Some(block) = self.store.get(&location.block_hash)? {
            merkle_branch_for_block(&block, location.transaction_index)
        } else {
            let Some(store) = self.electrum_store.as_mut() else {
                return Ok(None);
            };
            let Some(branch) =
                store.merkle_branch(&location.block_hash, location.transaction_index)?
            else {
                return Ok(None);
            };
            branch
        };
        Ok(Some((branch, location.transaction_index, location.height)))
    }

    /// Return a transaction merkle branch only when the transaction is in the
    /// active-chain block at `height`. Electrum supplies the confirmation
    /// height as part of `blockchain.transaction.get_merkle`; using the
    /// height here prevents a stale or incorrect height from silently
    /// producing a proof for another block.
    pub fn merkle_branch_at_height(
        &mut self,
        txid: &Txid,
        height: u32,
    ) -> Result<Option<(Vec<Txid>, usize, u32)>> {
        let Some(block_hash) = self.block_hash(height) else {
            return Ok(None);
        };
        let (transaction_index, branch) = if let Some(block) = self.store.get(&block_hash)? {
            let Some(transaction_index) = block
                .txdata
                .iter()
                .position(|transaction| transaction.compute_txid() == *txid)
            else {
                return Ok(None);
            };
            (
                transaction_index,
                merkle_branch_for_block(&block, transaction_index),
            )
        } else {
            let Some(location) = self.active_transaction_location_at_height(txid, height) else {
                return Ok(None);
            };
            if location.block_hash != block_hash || location.height != height {
                return Ok(None);
            }
            let Some(store) = self.electrum_store.as_mut() else {
                return Ok(None);
            };
            let Some(branch) = store.merkle_branch(&block_hash, location.transaction_index)? else {
                return Ok(None);
            };
            (location.transaction_index, branch)
        };
        Ok(Some((branch, transaction_index, height)))
    }

    /// Return an Electrum-indexed transaction by active-chain height and
    /// position when the ordinary block body has been pruned.
    pub(crate) fn electrum_transaction_at_height(
        &mut self,
        height: u32,
        transaction_index: usize,
    ) -> Result<Option<Transaction>> {
        let Some(block_hash) = self.block_hash(height) else {
            return Ok(None);
        };
        if let Some(block) = self.store.get(&block_hash)? {
            return Ok(block.txdata.get(transaction_index).cloned());
        }
        self.electrum_store
            .as_mut()
            .map(|store| store.transaction(&block_hash, transaction_index))
            .transpose()
            .map(|value| value.flatten())
    }

    pub fn connect_block(&mut self, block: Block) -> Result<ChainTip> {
        self.connect_block_with_existing_body(block, false, false)
    }

    pub(crate) fn connect_block_from_peer(&mut self, block: Block) -> Result<ChainTip> {
        self.connect_block_with_existing_body(block, false, true)
    }

    fn connect_block_with_existing_body(
        &mut self,
        block: Block,
        allow_existing_body: bool,
        retain_invalid_body: bool,
    ) -> Result<ChainTip> {
        self.poll_background_validation()?;
        self.promote_snapshot_chain_to_base()?;
        let hash = block.block_hash();
        if self.has_invalid_ancestor(hash) {
            bail!("block {hash} is on an invalidated branch")
        }
        if self.active_chain.contains(&hash) {
            if self.store.contains(&hash) {
                return Ok(self.tip());
            }
            // A pruned active-chain block still has a block-index entry, but
            // its body can be fetched again through getblockfrompeer.  Do
            // not treat that body as a duplicate merely because the header
            // remains on the active chain.
            let node = self
                .block_index
                .get(&hash)
                .copied()
                .context("active block index entry is missing")?;
            self.validate_block_structure(
                &block,
                self.network,
                node.height,
                Amount::MAX_MONEY.to_sat(),
            )?;
            self.store.insert(&block)?;
            if let Some(store) = self.electrum_store.as_mut() {
                store.insert(&block)?;
            }
            self.index_active_transactions(&block, node.height);
            self.index_all_transactions(&block, node.height);
            let count =
                u32::try_from(block.txdata.len()).context("transaction count does not fit u32")?;
            let height = usize::try_from(node.height).context("block height does not fit usize")?;
            if self.active_tx_counts.len() <= height {
                self.active_tx_counts.resize(height.saturating_add(1), 0);
            }
            self.active_tx_counts[height] = count;
            self.active_tx_totals = cumulative_tx_counts(&self.active_tx_counts);
            if self.prune_height.is_some() {
                self.prune_protected_blocks.insert(hash, self.height());
            }
            self.persist_metadata()?;
            return Ok(self.tip());
        }
        // Core's AcceptBlock returns immediately for an already-stored body
        // in the ordinary duplicate/side-chain cases. A block fetched into a
        // pruned node is different: its header may be indexed, its body may
        // already be present, and the node may have restarted just before it
        // could connect that body. Let a sequential submitblock or peer
        // response finish that active-chain candidate when its parent is the
        // current tip.
        if self.store.contains(&hash) && !allow_existing_body {
            let reconnectable_active_candidate = self.block_index.get(&hash).is_some_and(|node| {
                !self.active_chain.contains(&hash) && node.header.prev_blockhash == self.best_hash()
            });
            if !reconnectable_active_candidate {
                return Ok(self.tip());
            }
        }
        let parent_hash = block.header.prev_blockhash;
        let Some(parent) = self.block_index.get(&parent_hash).copied() else {
            self.queue_orphan_block(parent_hash, block)?;
            bail!("block {} has an unknown parent {}", hash, parent_hash);
        };
        if self.has_invalid_ancestor(parent_hash) {
            bail!("block {hash} is on an invalidated branch")
        }
        if parent_hash == self.best_hash() {
            if let Err(error) = self.connect_block_internal(&block, true) {
                if retain_invalid_body
                    && error
                        .downcast_ref::<ValidationError>()
                        .is_some_and(ValidationError::should_mark_block_invalid)
                {
                    self.store.insert(&block)?;
                    if let Some(store) = self.electrum_store.as_mut() {
                        store.insert(&block)?;
                    }
                    self.assign_block_sequence_id(hash);
                    self.persist_metadata()?;
                }
                return Err(error);
            }
            self.process_orphans(hash);
            self.process_known_children(hash);
            self.update_ibd_status();
            return Ok(self.tip());
        }

        // Core writes a block body once its parent header is known, even when
        // the parent body (and therefore its UTXO state) is not available.
        // Keep the body indexed as an unconnected candidate so getblock can
        // serve it without fabricating undo data. A later arrival of the
        // parent body will revisit it through process_known_children().
        if !self.store.contains(&parent_hash) {
            let height = parent.height.saturating_add(1);
            validation::validate_bip94_timewarp_with_params(
                &self.deployment_parameters,
                height,
                block.header.time,
                parent.header.time,
            )?;
            self.validate_header_context(
                &block.header,
                parent_hash,
                self.expected_target_for_parent(parent_hash, block.header.time),
                self.median_time_past_for_parent(parent_hash),
                true,
            )?;
            self.validate_block_structure(
                &block,
                self.network,
                height,
                Amount::MAX_MONEY.to_sat(),
            )?;
            self.record_unlinked_body(hash);
            self.insert_side_chain_body(&block)?;
            if let Some(store) = self.electrum_store.as_mut() {
                store.insert_unsynced(&block)?;
            }
            self.index_all_transactions(&block, height);
            self.block_index.insert(
                hash,
                BlockNode {
                    header: block.header,
                    height,
                    chain_work: parent.chain_work + block.header.work(),
                },
            );
            self.assign_header_sequence_id(hash);
            bail!("block {} has a parent whose full body is unavailable", hash)
        }

        let height = parent.height.saturating_add(1);
        validation::validate_bip94_timewarp_with_params(
            &self.deployment_parameters,
            height,
            block.header.time,
            parent.header.time,
        )?;
        self.validate_header_context(
            &block.header,
            parent_hash,
            self.expected_target_for_parent(parent_hash, block.header.time),
            self.median_time_past_for_parent(parent_hash),
            true,
        )?;
        self.validate_block_structure(&block, self.network, height, Amount::MAX_MONEY.to_sat())?;
        if retain_invalid_body {
            // Core's peer path accepts and stores a structurally valid
            // side-chain body without checking its UTXO-dependent rules. The
            // branch is validated only if it later becomes the best-chain
            // candidate; this keeps a same-height invalid fork from
            // disconnecting the announcing peer before it can announce a
            // longer descendant.
            self.side_chain_utxos = None;
            self.insert_side_chain_body(&block)?;
            if let Some(store) = self.electrum_store.as_mut() {
                store.insert_unsynced(&block)?;
            }
            self.index_all_transactions(&block, height);
            let chain_work = parent.chain_work + block.header.work();
            self.block_index.insert(
                hash,
                BlockNode {
                    header: block.header,
                    height,
                    chain_work,
                },
            );
            self.assign_header_sequence_id(hash);
            self.assign_block_sequence_id(hash);
            if chain_work > self.tip().work {
                self.store.flush()?;
                if let Some(store) = self.electrum_store.as_mut() {
                    store.flush()?;
                }
                self.activate_chain(hash)?;
            }
            self.process_orphans(hash);
            self.process_known_children(hash);
            self.update_ibd_status();
            return Ok(self.tip());
        }
        // Once BIP34 is active, a coinbase-only block has no UTXO-dependent
        // transaction validation: its height commits to a unique coinbase
        // transaction ID, and there are no spends to look up.  Headers-first
        // reorg tests (and ordinary mining bursts) commonly consist of such
        // blocks; avoid rebuilding a side-chain UTXO map for each one while
        // retaining the full path for mixed-transaction blocks.
        let coinbase_only =
            block.txdata.len() == 1 && height >= self.deployment_parameters.buried.bip34;
        if coinbase_only {
            let empty_utxos = HashMap::new();
            let application = match self.validate_block_transactions(
                &block,
                height,
                &empty_utxos,
                self.median_time_past_for_parent(parent_hash),
            ) {
                Ok(application) => application,
                Err(error) => {
                    if retain_invalid_body
                        && error
                            .downcast_ref::<ValidationError>()
                            .is_some_and(ValidationError::should_mark_block_invalid)
                    {
                        self.insert_side_chain_body(&block)?;
                        if let Some(store) = self.electrum_store.as_mut() {
                            store.insert_unsynced(&block)?;
                        }
                        self.assign_block_sequence_id(hash);
                    }
                    return Err(error);
                }
            };
            // Keep a UTXO snapshot for a run of coinbase-only side-chain
            // blocks.  The blocks themselves do not spend anything, but
            // their coinbase outputs still become available to descendants.
            if let Some(mut parent_utxos) = if self
                .side_chain_utxos
                .as_ref()
                .is_some_and(|cache| cache.hash == parent_hash)
            {
                self.side_chain_utxos.take().map(|cache| cache.utxos)
            } else {
                self.utxos_for_block(parent_hash)?
            } {
                apply_block_to_utxos(
                    &mut parent_utxos,
                    &block,
                    height,
                    self.median_time_past_for_parent(parent_hash),
                    application.spent_entries,
                );
                self.side_chain_utxos = Some(SideChainUtxoCache {
                    hash,
                    utxos: parent_utxos,
                });
            } else {
                self.side_chain_utxos = None;
            }
        } else {
            let parent_utxos = if self
                .side_chain_utxos
                .as_ref()
                .is_some_and(|cache| cache.hash == parent_hash)
            {
                self.side_chain_utxos.take().map(|cache| cache.utxos)
            } else {
                self.utxos_for_block(parent_hash)?
            };
            let Some(mut parent_utxos) = parent_utxos else {
                // Preserve a validated side-chain body even when its ancestry
                // is not connected to the active UTXO set. Core keeps this
                // body available for getblock and later reprocessing after
                // the missing ancestor arrives, while postponing script
                // validation.
                self.record_unlinked_body(hash);
                self.insert_side_chain_body(&block)?;
                if let Some(store) = self.electrum_store.as_mut() {
                    store.insert_unsynced(&block)?;
                }
                self.index_all_transactions(&block, height);
                self.block_index.insert(
                    hash,
                    BlockNode {
                        header: block.header,
                        height,
                        chain_work: parent.chain_work + block.header.work(),
                    },
                );
                self.assign_header_sequence_id(hash);
                bail!("side-chain parent UTXO state is unavailable")
            };
            let application = match self.validate_block_transactions(
                &block,
                height,
                &parent_utxos,
                self.median_time_past_for_parent(parent_hash),
            ) {
                Ok(application) => application,
                Err(error) => {
                    if retain_invalid_body
                        && error
                            .downcast_ref::<ValidationError>()
                            .is_some_and(ValidationError::should_mark_block_invalid)
                    {
                        self.insert_side_chain_body(&block)?;
                        if let Some(store) = self.electrum_store.as_mut() {
                            store.insert_unsynced(&block)?;
                        }
                        self.assign_block_sequence_id(hash);
                    }
                    return Err(error);
                }
            };
            apply_block_to_utxos(
                &mut parent_utxos,
                &block,
                height,
                self.median_time_past_for_parent(parent_hash),
                application.spent_entries,
            );
            self.side_chain_utxos = Some(SideChainUtxoCache {
                hash,
                utxos: parent_utxos,
            });
        }
        self.insert_side_chain_body(&block)?;
        if let Some(store) = self.electrum_store.as_mut() {
            store.insert_unsynced(&block)?;
        }
        self.index_all_transactions(&block, height);
        let chain_work = parent.chain_work + block.header.work();
        self.block_index.insert(
            hash,
            BlockNode {
                header: block.header,
                height,
                chain_work,
            },
        );
        self.assign_header_sequence_id(hash);
        self.assign_block_sequence_id(hash);
        if chain_work > self.tip().work {
            self.store.flush()?;
            if let Some(store) = self.electrum_store.as_mut() {
                store.flush()?;
            }
            self.activate_chain(hash)?;
        }
        self.process_orphans(hash);
        self.process_known_children(hash);
        self.update_ibd_status();
        Ok(self.tip())
    }

    fn insert_side_chain_body(&mut self, block: &Block) -> Result<()> {
        self.store.insert_unsynced(block)?;
        if self.prune_height.is_some() {
            self.prune_protected_blocks
                .insert(block.block_hash(), self.height());
        }
        Ok(())
    }

    fn process_orphans(&mut self, parent_hash: BlockHash) {
        let Some(children) = self.orphans.remove(&parent_hash) else {
            return;
        };
        for child in children {
            let _ = self.connect_block_with_existing_body(child, true, false);
        }
    }

    fn queue_orphan_block(&mut self, parent_hash: BlockHash, block: Block) -> Result<()> {
        let hash = block.block_hash();
        if self
            .orphans
            .values()
            .any(|children| children.iter().any(|child| child.block_hash() == hash))
        {
            return Ok(());
        }
        let orphan_count = self.orphans.values().map(Vec::len).sum::<usize>();
        if orphan_count >= MAX_ORPHAN_BLOCKS {
            bail!("too many orphan blocks")
        }
        self.orphans.entry(parent_hash).or_default().push(block);
        Ok(())
    }

    fn record_unlinked_body(&mut self, hash: BlockHash) {
        if self.unlinked_body_order.contains_key(&hash) {
            return;
        }
        let order = self.next_unlinked_body_order;
        self.unlinked_body_order.insert(hash, order);
        self.next_unlinked_body_order = self.next_unlinked_body_order.saturating_add(1);
    }

    fn process_known_children(&mut self, parent_hash: BlockHash) {
        let mut children: Vec<BlockHash> = self
            .block_index
            .iter()
            .filter_map(|(hash, node)| {
                (node.header.prev_blockhash == parent_hash && self.store.contains(hash))
                    .then_some(*hash)
            })
            .collect();
        children.sort_by(|left, right| {
            self.unlinked_body_order
                .get(left)
                .copied()
                .unwrap_or(u64::MAX)
                .cmp(
                    &self
                        .unlinked_body_order
                        .get(right)
                        .copied()
                        .unwrap_or(u64::MAX),
                )
                .then_with(|| left.to_string().cmp(&right.to_string()))
        });
        for child_hash in children {
            let Ok(Some(child)) = self.store.get(&child_hash) else {
                continue;
            };
            let _ = self.connect_block_with_existing_body(child, true, false);
        }
    }

    fn utxos_for_block(&mut self, hash: BlockHash) -> Result<Option<HashMap<OutPoint, UtxoEntry>>> {
        self.replay_utxos_for_block(hash, true)
    }

    /// Reconstruct an older active-chain UTXO set by applying block undo data
    /// backwards from the serving tip.  The normal forward replay remains the
    /// compatibility fallback for pruned stores and historical BIP30 edge
    /// cases, but reverse replay avoids walking the entire chain for ordinary
    /// historical RPC and snapshot queries.
    fn replay_active_utxos_backwards(
        &mut self,
        hash: BlockHash,
    ) -> Result<Option<HashMap<OutPoint, UtxoEntry>>> {
        if !self.is_active_block(&hash) {
            return Ok(None);
        }
        let target_height = self
            .block_height_by_hash(&hash)
            .context("active block height is unavailable")?;
        let tip_height = self.height();
        if target_height >= tip_height {
            return Ok(Some(if self.utxos_materialized {
                self.utxos.clone()
            } else {
                self.load_utxo_map_from_store()?
            }));
        }

        // The two historical duplicate-coinbase branches require Core's
        // special disconnect handling.  Their undo records do not contain
        // enough information to reproduce an overwritten coin exactly, so
        // leave those paths to the validated forward replay below.
        if (target_height + 1..=tip_height).any(|height| {
            let block_hash = self.active_chain[height as usize];
            is_bip30_repeat(self.network, height, block_hash)
                || is_bip30_unspendable(self.network, height, block_hash)
        }) {
            return Ok(None);
        }

        let mut utxos = if self.utxos_materialized {
            self.utxos.clone()
        } else {
            self.load_utxo_map_from_store()?
        };
        for height in (target_height + 1..=tip_height).rev() {
            let block_hash = self.active_chain[height as usize];
            let Some(block) = self.store.get(&block_hash)? else {
                return Ok(None);
            };
            let undo = if let Some(undo) = self.block_undo_cache.get(&block_hash) {
                undo.clone()
            } else {
                let Some(undo) = self.store.get_undo(&block_hash)? else {
                    return Ok(None);
                };
                self.remember_block_undo(block_hash, undo.clone());
                undo
            };
            self.disconnect_block_from_utxos(&mut utxos, &block, height, &undo)?;
        }
        Ok(Some(utxos))
    }

    fn disconnect_block_from_utxos(
        &self,
        utxos: &mut HashMap<OutPoint, UtxoEntry>,
        block: &Block,
        height: u32,
        undo: &[Vec<TxOut>],
    ) -> Result<()> {
        self.validate_block_undo(block, undo)?;

        // Disconnect transactions in reverse order. Removing each
        // transaction immediately before restoring its inputs is important
        // for transactions that spend outputs created earlier in the same
        // block: the earlier output is restored by the child, then removed
        // again when its own transaction is disconnected.
        for (transaction_index, transaction) in block.txdata.iter().enumerate().rev() {
            let txid = transaction.compute_txid();
            for output_index in 0..transaction.output.len() {
                utxos.remove(&OutPoint::new(txid, output_index as u32));
            }
            if transaction_index == 0 {
                continue;
            }
            let spent_outputs = undo
                .get(transaction_index)
                .context("block undo is missing a transaction entry")?;
            if spent_outputs.len() != transaction.input.len() {
                bail!(
                    "block undo contains {} spent outputs for transaction with {} inputs",
                    spent_outputs.len(),
                    transaction.input.len()
                );
            }
            for (input, output) in transaction.input.iter().zip(spent_outputs).rev() {
                let outpoint = input.previous_output;
                let entry = self
                    .restored_utxo_entry(&outpoint, output, block, height)
                    .with_context(|| format!("cannot reconstruct undo metadata for {outpoint}"))?;
                utxos.insert(outpoint, entry);
            }
        }
        Ok(())
    }

    fn validate_block_undo(&self, block: &Block, undo: &[Vec<TxOut>]) -> Result<()> {
        if undo.len() != block.txdata.len() {
            bail!(
                "block undo contains {} transaction entries for a block with {} transactions",
                undo.len(),
                block.txdata.len()
            );
        }
        if !undo.first().is_some_and(Vec::is_empty) {
            bail!("coinbase transaction has unexpected undo outputs")
        }
        for (transaction, spent_outputs) in block.txdata.iter().skip(1).zip(undo.iter().skip(1)) {
            if spent_outputs.len() != transaction.input.len() {
                bail!(
                    "block undo contains {} spent outputs for transaction with {} inputs",
                    spent_outputs.len(),
                    transaction.input.len()
                );
            }
            if spent_outputs
                .iter()
                .any(|output| output.value > Amount::MAX_MONEY)
            {
                bail!("block undo contains an output above the money range")
            }
        }
        Ok(())
    }

    fn disconnect_block_for_verification(
        &self,
        utxos: &mut HashMap<OutPoint, UtxoEntry>,
        block: &Block,
        height: u32,
        undo: &[Vec<TxOut>],
    ) -> Result<()> {
        self.validate_block_undo(block, undo)?;
        if is_bip30_repeat(self.network, height, block.block_hash()) {
            self.disconnect_block_from_utxos(utxos, block, height, undo)?;
            return Ok(());
        }

        for (transaction_index, transaction) in block.txdata.iter().enumerate().rev() {
            let txid = transaction.compute_txid();
            for (output_index, output) in transaction.output.iter().enumerate() {
                if is_unspendable_script(&output.script_pubkey) {
                    continue;
                }
                let outpoint = OutPoint::new(txid, output_index as u32);
                if utxos.remove(&outpoint).is_none() {
                    bail!(
                        "block disconnect is missing created output {}:{}",
                        txid,
                        output_index
                    )
                }
            }
            if transaction_index == 0 {
                continue;
            }
            for (input, output) in transaction.input.iter().zip(undo[transaction_index].iter()) {
                let outpoint = input.previous_output;
                if utxos.contains_key(&outpoint) {
                    bail!("block disconnect restores an already unspent output {outpoint}")
                }
                let entry = self
                    .restored_utxo_entry(&outpoint, output, block, height)
                    .with_context(|| format!("cannot reconstruct undo metadata for {outpoint}"))?;
                utxos.insert(outpoint, entry);
            }
        }
        Ok(())
    }

    fn restored_utxo_entry(
        &self,
        outpoint: &OutPoint,
        output: &TxOut,
        current_block: &Block,
        current_height: u32,
    ) -> Option<UtxoEntry> {
        let current_block_hash = current_block.block_hash();
        let current_transaction =
            current_block
                .txdata
                .iter()
                .enumerate()
                .find_map(|(index, transaction)| {
                    (transaction.compute_txid() == outpoint.txid).then_some(index)
                });
        let (height, block_hash, transaction_index) =
            if let Some(transaction_index) = current_transaction {
                (current_height, current_block_hash, transaction_index)
            } else {
                let location = self
                    .tx_index
                    .get(&outpoint.txid)
                    .and_then(|location| self.expand_active_tx_location(*location))
                    .or_else(|| self.tx_index_all.get(&outpoint.txid).cloned())?;
                (
                    location.height,
                    location.block_hash,
                    location.transaction_index,
                )
            };
        let node = self.block_index.get(&block_hash)?;
        let median_time_past = if height == 0 {
            0
        } else {
            self.median_time_past_for_parent(node.header.prev_blockhash)
        };
        Some(UtxoEntry {
            output: output.clone(),
            height,
            median_time_past,
            coinbase: transaction_index == 0,
        })
    }

    fn replay_utxos_for_block(
        &mut self,
        hash: BlockHash,
        use_active_cache: bool,
    ) -> Result<Option<HashMap<OutPoint, UtxoEntry>>> {
        if use_active_cache && hash == self.best_hash() {
            return Ok(Some(if self.utxos_materialized {
                self.utxos.clone()
            } else {
                self.load_utxo_map_from_store()?
            }));
        }
        if let Some(utxos) = self.replay_active_utxos_backwards(hash)? {
            return Ok(Some(utxos));
        }
        let mut path = Vec::new();
        let mut cursor = hash;
        loop {
            path.push(cursor);
            if cursor == self.network_genesis_hash() {
                break;
            }
            let Some(node) = self.block_index.get(&cursor) else {
                return Ok(None);
            };
            cursor = node.header.prev_blockhash;
        }
        path.reverse();
        let Some(_genesis) = self.store.get(&path[0])? else {
            return Ok(None);
        };
        let mut utxos = HashMap::new();
        for block_hash in path.into_iter().skip(1) {
            let Some(block) = self.store.get(&block_hash)? else {
                return Ok(None);
            };
            let node = self
                .block_index
                .get(&block_hash)
                .copied()
                .context("side-chain block index entry is missing")?;
            let parent_hash = block.header.prev_blockhash;
            let parent = self
                .block_index
                .get(&parent_hash)
                .copied()
                .context("side-chain parent block index entry is missing")?;
            validation::validate_bip94_timewarp_with_params(
                &self.deployment_parameters,
                node.height,
                block.header.time,
                parent.header.time,
            )?;
            self.validate_header_context(
                &block.header,
                parent_hash,
                self.expected_target_for_parent(parent_hash, block.header.time),
                self.median_time_past_for_parent(parent_hash),
                true,
            )?;
            self.validate_block_structure(
                &block,
                self.network,
                node.height,
                Amount::MAX_MONEY.to_sat(),
            )?;
            let median_time_past = self.median_time_past_for_parent(parent_hash);
            let application =
                self.validate_block_transactions(&block, node.height, &utxos, median_time_past)?;
            apply_block_to_utxos(
                &mut utxos,
                &block,
                node.height,
                median_time_past,
                application.spent_entries,
            );
        }
        Ok(Some(utxos))
    }

    fn validate_block_transactions<U: UtxoLookup + ?Sized>(
        &self,
        block: &Block,
        height: u32,
        utxos: &U,
        block_median_time_past: u32,
    ) -> Result<BlockApplication> {
        let script_check_reason = self.script_check_reason(block, height);
        let block_hash = block.block_hash();
        if let Some(reason) = script_check_reason {
            tracing::info!(
                "Enabling script verification at block #{height} ({block_hash}): {reason}."
            );
        } else {
            tracing::info!("Disabling script verification at block #{height} ({block_hash}).");
        }
        let skip_script_checks = self.should_skip_script_checks(block, height);
        self.validate_block_transactions_with_options(
            block,
            height,
            utxos,
            block_median_time_past,
            skip_script_checks,
        )
    }

    fn validate_block_transactions_with_options<U: UtxoLookup + ?Sized>(
        &self,
        block: &Block,
        height: u32,
        utxos: &U,
        block_median_time_past: u32,
        skip_script_checks: bool,
    ) -> Result<BlockApplication> {
        if self.enforce_bip30(height, block.block_hash(), block.header.prev_blockhash) {
            for transaction in &block.txdata {
                let txid = transaction.compute_txid();
                for (vout, _) in transaction.output.iter().enumerate() {
                    if utxos.contains(&OutPoint::new(txid, vout as u32))? {
                        return Err(ValidationError::Bip30(txid).into());
                    }
                }
            }
        }
        let mut spent_entries = Vec::new();
        let mut spent = HashSet::new();
        let mut created = HashMap::new();
        let mut total_fees = 0u64;
        let mut metrics = CoinStatsBlockMetrics {
            subsidy_sat: validation::block_subsidy_for_network(self.network, height),
            ..CoinStatsBlockMetrics::default()
        };
        let mut script_jobs = Vec::new();
        let block_hash = block.block_hash();
        let sigop_flags = validation::script_flags_for_block_with_params(
            &self.deployment_parameters,
            height,
            Some(block_hash),
        );
        let reduced_data_activation_height = self
            .headers_to_hash(&block.header.prev_blockhash)
            .and_then(|headers| {
                validation::reduced_data_activation_height(
                    &headers,
                    self.deployment_parameters.bip9[2],
                    height,
                )
            });
        let csv_active = height >= self.deployment_parameters.buried.csv;
        let lock_time_cutoff = if csv_active {
            block_median_time_past
        } else {
            block.header.time
        };
        validation::validate_transaction_finality(
            &block.txdata[0],
            height,
            lock_time_cutoff,
            csv_active,
            &[],
        )?;
        if reduced_data_activation_height.is_some() {
            validation::validate_reduced_data_output_sizes(&block.txdata[0])?;
        }
        let mut sigop_cost = validation::transaction_sigop_cost(&block.txdata[0], &[], sigop_flags);
        if sigop_cost > validation::MAX_BLOCK_SIGOP_COST {
            return Err(ValidationError::TooManySigopsInConnect.into());
        }
        for (transaction_index, transaction) in block.txdata.iter().enumerate().skip(1) {
            let txid = transaction.compute_txid();
            let mut transaction_spent = HashSet::new();
            let mut input_total = 0u64;
            let mut previous_outputs = Vec::with_capacity(transaction.input.len());
            let mut previous_entries = Vec::with_capacity(transaction.input.len());
            for input in &transaction.input {
                let outpoint = input.previous_output;
                if !transaction_spent.insert(outpoint) {
                    return Err(ValidationError::DuplicateInput(txid).into());
                }
                if !spent.insert(outpoint) {
                    return Err(ValidationError::MissingInput { outpoint }.into());
                }
                let entry = if let Some(entry) = created.get(&outpoint).cloned() {
                    entry
                } else if let Some(entry) = utxos.get(&outpoint)? {
                    entry
                } else {
                    return Err(ValidationError::MissingInput { outpoint }.into());
                };
                if entry.coinbase && height < entry.height.saturating_add(COINBASE_MATURITY) {
                    return Err(ValidationError::ImmatureCoinbase { outpoint }.into());
                }
                input_total = input_total
                    .checked_add(entry.output.value.to_sat())
                    .ok_or(ValidationError::InputTotalOverflow)?;
                if input_total > Amount::MAX_MONEY.to_sat() {
                    return Err(ValidationError::InputTotalOverflow.into());
                }
                metrics.prevout_spent_sat = metrics
                    .prevout_spent_sat
                    .saturating_add(entry.output.value.to_sat());
                previous_outputs.push(entry.output.clone());
                previous_entries.push(entry.clone());
                spent_entries.push((outpoint, entry));
            }
            if let Some(activation_height) = reduced_data_activation_height {
                validation::validate_reduced_data_output_sizes(transaction)?;
                if !skip_script_checks {
                    let previous_heights = previous_entries
                        .iter()
                        .map(|entry| entry.height)
                        .collect::<Vec<_>>();
                    validation::validate_reduced_data_input_sizes(
                        transaction,
                        &previous_outputs,
                        &previous_heights,
                        activation_height,
                    )?;
                }
            }
            sigop_cost = sigop_cost.saturating_add(validation::transaction_sigop_cost(
                transaction,
                &previous_outputs,
                sigop_flags,
            ));
            if sigop_cost > validation::MAX_BLOCK_SIGOP_COST {
                return Err(ValidationError::TooManySigopsInConnect.into());
            }
            validation::validate_transaction_finality(
                transaction,
                height,
                lock_time_cutoff,
                csv_active,
                &previous_entries,
            )?;
            if !skip_script_checks {
                script_jobs.push(ScriptCheckJob {
                    tx_index: transaction_index,
                    transaction,
                    previous_outputs,
                });
            }
            let output_total = transaction
                .output
                .iter()
                .try_fold(0u64, |total, output| {
                    total.checked_add(output.value.to_sat())
                })
                .ok_or(ValidationError::OutputTotalOverflow)?;
            if output_total > input_total {
                return Err(ValidationError::NegativeFee { txid }.into());
            }
            total_fees = total_fees
                .checked_add(input_total - output_total)
                .ok_or(ValidationError::AccumulatedFeeOverflow)?;
            if total_fees > Amount::MAX_MONEY.to_sat() {
                return Err(ValidationError::AccumulatedFeeOverflow.into());
            }
            for (output_index, output) in transaction.output.iter().enumerate() {
                if is_unspendable_script(&output.script_pubkey) {
                    metrics.unspendable_scripts_sat = metrics
                        .unspendable_scripts_sat
                        .saturating_add(output.value.to_sat());
                } else {
                    metrics.new_outputs_ex_coinbase_sat = metrics
                        .new_outputs_ex_coinbase_sat
                        .saturating_add(output.value.to_sat());
                    created.insert(
                        OutPoint::new(txid, output_index as u32),
                        UtxoEntry {
                            output: output.clone(),
                            height,
                            median_time_past: block_median_time_past,
                            coinbase: false,
                        },
                    );
                }
            }
        }
        if !skip_script_checks {
            self.validate_script_checks(block, height, &script_jobs)?;
        }
        // Core checks the accumulated fees against MAX_MONEY above, then
        // compares the coinbase output with subsidy + fees. The reward sum
        // itself is allowed to exceed MAX_MONEY; only each transaction's
        // output total is range-limited.
        let allowed_coinbase = validation::block_subsidy_for_network(self.network, height)
            .checked_add(total_fees)
            .expect("subsidy plus bounded fees fits in u64");
        let actual_coinbase = block.txdata[0]
            .output
            .iter()
            .try_fold(0u64, |total, output| {
                total.checked_add(output.value.to_sat())
            })
            .ok_or(ValidationError::OutputTotalOverflow)?;
        if actual_coinbase > allowed_coinbase {
            return Err(ValidationError::CoinbaseOverpay {
                actual: actual_coinbase,
                allowed: allowed_coinbase,
            }
            .into());
        }
        if is_bip30_unspendable(self.network, height, block_hash) {
            metrics.unspendable_bip30_sat = metrics
                .unspendable_bip30_sat
                .saturating_add(metrics.subsidy_sat);
        } else {
            for output in &block.txdata[0].output {
                if is_unspendable_script(&output.script_pubkey) {
                    metrics.unspendable_scripts_sat = metrics
                        .unspendable_scripts_sat
                        .saturating_add(output.value.to_sat());
                } else {
                    metrics.coinbase_sat =
                        metrics.coinbase_sat.saturating_add(output.value.to_sat());
                }
            }
        }
        Ok(BlockApplication {
            spent_entries,
            metrics,
        })
    }

    fn validate_script_checks(
        &self,
        block: &Block,
        height: u32,
        jobs: &[ScriptCheckJob<'_>],
    ) -> Result<()> {
        if jobs.is_empty() {
            return Ok(());
        }
        let block_hash = block.block_hash();
        let script_flags = validation::script_flags_for_block_with_params(
            &self.deployment_parameters,
            height,
            Some(block_hash),
        );
        let pending = jobs
            .iter()
            .filter(|job| {
                let key =
                    self.script_cache_key(script_flags, job.transaction, &job.previous_outputs);
                !self.script_cache.lock().entries.contains(&key)
            })
            .collect::<Vec<_>>();
        if pending.is_empty() {
            return Ok(());
        }
        let thread_count = self.script_check_thread_count().min(pending.len());
        let deployment_parameters = self.deployment_parameters;
        let block_time = block.header.time;
        if thread_count <= 1 {
            for job in &pending {
                validation::validate_transaction_scripts_at_time_with_block_hash_with_params(
                    &deployment_parameters,
                    height,
                    block_time,
                    Some(block_hash),
                    job.transaction,
                    &job.previous_outputs,
                )?;
            }
        } else {
            let chunk_size = pending.len().div_ceil(thread_count);
            let failures = thread::scope(|scope| {
                let handles = pending
                    .chunks(chunk_size)
                    .map(|chunk| {
                        scope.spawn(move || {
                            for job in chunk {
                                if let Err(error) =
                                    validation::validate_transaction_scripts_at_time_with_block_hash_with_params(
                                        &deployment_parameters,
                                        height,
                                        block_time,
                                        Some(block_hash),
                                        job.transaction,
                                        &job.previous_outputs,
                                    )
                                {
                                    return Some((job.tx_index, error));
                                }
                            }
                            None
                        })
                    })
                    .collect::<Vec<_>>();
                handles
                    .into_iter()
                    .filter_map(|handle| handle.join().expect("script validation worker panicked"))
                    .collect::<Vec<_>>()
            });
            if let Some((_, error)) = failures.into_iter().min_by_key(|(tx_index, _)| *tx_index) {
                return Err(error.into());
            }
        }

        let mut cache = self.script_cache.lock();
        for job in pending {
            let key = self.script_cache_key(script_flags, job.transaction, &job.previous_outputs);
            if cache.entries.contains(&key) {
                continue;
            }
            if cache.order.len() >= cache.max_entries
                && let Some(evicted) = cache.order.pop_front()
            {
                cache.entries.remove(&evicted);
            }
            cache.entries.insert(key);
            cache.order.push_back(key);
        }
        Ok(())
    }

    /// Validate a mempool transaction through the same bounded script cache
    /// used by block connection. Core shares its script-execution cache so a
    /// transaction is not fully checked again when it later arrives in a
    /// block; the cache key is safe across contexts because it commits to the
    /// effective consensus flags and every spent output.
    pub(crate) fn validate_mempool_transaction_scripts(
        &self,
        transaction: &Transaction,
        previous_outputs: &[TxOut],
    ) -> std::result::Result<(), ValidationError> {
        let script_flags = validation::mempool_script_flags();
        let key = self.script_cache_key(script_flags, transaction, previous_outputs);
        if self.script_cache.lock().entries.contains(&key) {
            return Ok(());
        }
        validation::validate_transaction_scripts_with_flags(
            transaction,
            previous_outputs,
            script_flags,
        )?;
        self.cache_script_validation(key);
        Ok(())
    }

    pub(crate) fn reduced_data_active_for_next_block(&self) -> Option<u32> {
        validation::reduced_data_activation_height(
            &self.headers,
            self.deployment_parameters.bip9[2],
            self.height().saturating_add(1),
        )
    }

    fn cache_script_validation(&self, key: [u8; 32]) {
        let mut cache = self.script_cache.lock();
        if cache.entries.contains(&key) {
            return;
        }
        if cache.order.len() >= cache.max_entries
            && let Some(evicted) = cache.order.pop_front()
        {
            cache.entries.remove(&evicted);
        }
        cache.entries.insert(key);
        cache.order.push_back(key);
    }

    fn script_cache_key(
        &self,
        script_flags: u32,
        transaction: &Transaction,
        previous_outputs: &[TxOut],
    ) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(match self.network {
            Network::Bitcoin => b"bitcoin".as_slice(),
            Network::Testnet => b"testnet".as_slice(),
            Network::Testnet4 => b"testnet4".as_slice(),
            Network::Signet => b"signet".as_slice(),
            Network::Regtest => b"regtest".as_slice(),
        });
        hasher.update(script_flags.to_le_bytes());
        hasher.update(transaction.compute_wtxid().to_byte_array());
        for output in previous_outputs {
            hasher.update(serialize(output));
        }
        hasher.finalize().into()
    }

    fn enforce_bip30(&self, height: u32, block_hash: BlockHash, parent_hash: BlockHash) -> bool {
        if height >= BIP34_IMPLIES_BIP30_LIMIT {
            return true;
        }
        if is_bip30_repeat(self.network, height, block_hash) {
            return false;
        }
        let Some(expected_bip34_hash) = bip34_activation_hash(self.network) else {
            return true;
        };
        self.ancestor_hash(parent_hash, self.deployment_parameters.buried.bip34)
            .map(|hash| hash.to_string() != expected_bip34_hash)
            .unwrap_or(true)
    }

    fn connect_block_internal(&mut self, block: &Block, persist: bool) -> Result<()> {
        self.connect_block_internal_with_index_journal(block, persist, None)
    }

    fn connect_block_internal_with_index_journal(
        &mut self,
        block: &Block,
        persist: bool,
        mut tx_index_all_changes: Option<&mut HashMap<Txid, Option<TxLocation>>>,
    ) -> Result<()> {
        let height = self.height().saturating_add(1);
        let previous = self.best_hash();
        let previous_node = self
            .block_index
            .get(&previous)
            .expect("active tip is indexed");
        validation::validate_bip94_timewarp_with_params(
            &self.deployment_parameters,
            height,
            block.header.time,
            previous_node.header.time,
        )?;
        let expected_target = self.expected_target(block.header.time);
        self.validate_header_context(
            &block.header,
            previous,
            expected_target,
            self.median_time_past(),
            true,
        )?;
        self.validate_block_structure(block, self.network, height, Amount::MAX_MONEY.to_sat())?;
        let block_median_time_past = self.median_time_past();
        let application = if persist {
            self.validate_block_transactions(
                block,
                height,
                &self.utxo_store,
                block_median_time_past,
            )?
        } else {
            self.validate_block_transactions(block, height, &self.utxos, block_median_time_past)?
        };
        self.cache_block_undo(block, &application.spent_entries)?;
        let previous_filter_header = self
            .basic_filter_for_block(&previous)?
            .map(|(_, header)| header)
            .unwrap_or(FilterHeader::all_zeros());
        self.cache_basic_filter_for_block(
            block,
            &application.spent_entries,
            &previous_filter_header,
        )?;

        let hash = block.block_hash();
        let spent_entries: HashMap<OutPoint, UtxoEntry> =
            application.spent_entries.iter().cloned().collect();
        if persist {
            self.store.insert(block)?;
        }
        if let Some(store) = self.electrum_store.as_mut() {
            store.insert(block)?;
        }
        if persist {
            let delta = self.chainstate_delta_for_block(
                block,
                height,
                block_median_time_past,
                &spent_entries,
                application.metrics,
            );
            let bytes = serialize_chainstate_delta(&delta)?;
            self.chainstate_store.insert(hash, &bytes)?;
        }
        let mut created_utxos = Vec::new();
        let removals = application
            .spent_entries
            .iter()
            .map(|(outpoint, _)| *outpoint)
            .collect::<Vec<_>>();
        for (outpoint, entry) in &application.spent_entries {
            let was_in_utxo_set = if self.utxos_materialized {
                self.utxos.remove(outpoint).is_some()
            } else {
                self.utxo_store.get(outpoint)?.is_some()
            };
            if was_in_utxo_set {
                self.remove_utxo_entry(outpoint, entry);
            }
        }
        let spent_outpoints: HashSet<OutPoint> = spent_entries.keys().copied().collect();
        let mut history_updates = HashMap::new();
        for (transaction_index, transaction) in block.txdata.iter().enumerate() {
            let txid = transaction.compute_txid();
            let mut affected_scripts = HashSet::new();
            for input in &transaction.input {
                if let Some(entry) = spent_entries.get(&input.previous_output) {
                    affected_scripts.insert(electrum_script_hash(&entry.output.script_pubkey));
                }
            }
            for (output_index, output) in transaction.output.iter().enumerate() {
                let outpoint = OutPoint::new(txid, output_index as u32);
                if !spent_outpoints.contains(&outpoint)
                    && !is_unspendable_script(&output.script_pubkey)
                {
                    let entry = UtxoEntry {
                        output: output.clone(),
                        height,
                        median_time_past: block_median_time_past,
                        coinbase: transaction_index == 0,
                    };
                    created_utxos.push((outpoint, entry.clone()));
                    self.insert_utxo(outpoint, entry);
                }
                affected_scripts.insert(electrum_script_hash(&output.script_pubkey));
            }
            for script_hash in affected_scripts {
                let entry = HistoryEntry { txid, height };
                if persist {
                    self.append_history_update(&mut history_updates, &script_hash, entry)?;
                } else {
                    self.add_history(&script_hash, entry);
                }
            }
            let location = TxLocation {
                block_hash: hash,
                height,
                transaction_index,
            };
            self.index_active_transaction(txid, location.clone());
            if self.tx_index_all_enabled {
                if let Some(changes) = tx_index_all_changes.as_deref_mut()
                    && !changes.contains_key(&txid)
                    && self.tx_index_all.get(&txid) != Some(&location)
                {
                    changes.insert(txid, self.tx_index_all.get(&txid).cloned());
                }
                self.tx_index_all.insert(txid, location);
            }
        }
        if persist {
            let additions = created_utxos
                .iter()
                .map(|(outpoint, entry)| (*outpoint, Self::stored_utxo(entry)))
                .collect::<Vec<_>>();
            self.utxo_store.apply_batch(&removals, &additions)?;
            self.persist_history_updates(history_updates)?;
        }
        if self.txospender_index_enabled {
            if persist {
                // The Core index may still expose spenders from a just
                // disconnected branch until its next block notification.
                // Reconcile those entries immediately before indexing the
                // next connected block, then let the new block overwrite any
                // matching outpoints.
                let active_blocks: HashSet<BlockHash> = self.active_chain.iter().copied().collect();
                self.spent_by
                    .retain(|_, (_, _, block_hash, _)| active_blocks.contains(block_hash));
            }
            self.index_block_spends(block, height);
        }
        self.active_chain.push(hash);
        if height >= self.deployment_parameters.buried.segwit {
            self.segwit_validated_blocks.insert(hash);
        }
        self.headers.push(block.header);
        let count =
            u32::try_from(block.txdata.len()).context("transaction count does not fit u32")?;
        self.active_tx_counts.push(count);
        let total = self
            .active_tx_totals
            .last()
            .copied()
            .unwrap_or_default()
            .saturating_add(u64::from(count));
        self.active_tx_totals.push(total);
        let parent_work = self
            .block_index
            .get(&block.header.prev_blockhash)
            .context("block parent is not indexed")?
            .chain_work;
        self.block_index.insert(
            hash,
            BlockNode {
                header: block.header,
                height,
                chain_work: parent_work + block.header.work(),
            },
        );
        self.update_index_prune_locks(height);
        self.assign_header_sequence_id(hash);
        self.assign_block_sequence_id(hash);
        if persist {
            self.persist_utxo_store_tip()?;
            self.persist_electrum_history_store_tip()?;
        }
        if let Some(stats) = self.coin_stats.as_mut() {
            stats.apply_block_metrics(application.metrics);
        }
        self.persist_coinstats_record(hash, height)?;
        if persist {
            self.persist_metadata()?;
            if self.height() % SNAPSHOT_INTERVAL == 0 {
                self.persist_snapshot()?;
            }
            self.utxo_store.maybe_simulate_crash()?;
        }
        Ok(())
    }

    fn chainstate_delta_for_block(
        &self,
        block: &Block,
        height: u32,
        median_time_past: u32,
        spent_entries: &HashMap<OutPoint, UtxoEntry>,
        metrics: CoinStatsBlockMetrics,
    ) -> ChainstateDelta {
        let block_hash = block.block_hash();
        let spent_outpoints: HashSet<OutPoint> = spent_entries.keys().copied().collect();
        let mut created = Vec::new();
        let mut transactions = Vec::with_capacity(block.txdata.len());
        let mut history = Vec::new();
        let mut spent_by = Vec::new();
        for (transaction_index, transaction) in block.txdata.iter().enumerate() {
            let txid = transaction.compute_txid();
            transactions.push((
                txid,
                TxLocation {
                    block_hash,
                    height,
                    transaction_index,
                },
            ));
            let mut affected_scripts = HashSet::new();
            for (input_index, input) in transaction.input.iter().enumerate() {
                if let Some(entry) = spent_entries.get(&input.previous_output) {
                    affected_scripts.insert(electrum_script_hash(&entry.output.script_pubkey));
                }
                if self.txospender_index_enabled && !input.previous_output.is_null() {
                    spent_by.push((
                        input.previous_output,
                        (txid, input_index, block_hash, height),
                    ));
                }
            }
            for (output_index, output) in transaction.output.iter().enumerate() {
                let outpoint = OutPoint::new(txid, output_index as u32);
                if !spent_outpoints.contains(&outpoint)
                    && !is_unspendable_script(&output.script_pubkey)
                {
                    created.push((
                        outpoint,
                        UtxoEntry {
                            output: output.clone(),
                            height,
                            median_time_past,
                            coinbase: transaction_index == 0,
                        },
                    ));
                }
                affected_scripts.insert(electrum_script_hash(&output.script_pubkey));
            }
            for script_hash in affected_scripts {
                history.push((script_hash, HistoryEntry { txid, height }));
            }
        }
        ChainstateDelta {
            block_hash,
            parent_hash: block.header.prev_blockhash,
            height,
            spent: spent_entries
                .iter()
                .map(|(outpoint, entry)| (*outpoint, entry.clone()))
                .collect(),
            created,
            transactions,
            history,
            spent_by,
            metrics,
        }
    }

    fn initialize_genesis(&mut self, genesis: &Block) -> Result<()> {
        if genesis.block_hash() != self.network_genesis_hash() {
            bail!("genesis block does not match network");
        }
        self.active_chain.push(genesis.block_hash());
        self.headers.push(genesis.header);
        let count =
            u32::try_from(genesis.txdata.len()).context("transaction count does not fit u32")?;
        self.active_tx_counts.push(count);
        self.active_tx_totals.push(u64::from(count));
        self.block_index.insert(
            genesis.block_hash(),
            BlockNode {
                header: genesis.header,
                height: 0,
                chain_work: genesis.header.work(),
            },
        );
        self.assign_header_sequence_id(genesis.block_hash());
        self.index_transactions(genesis, 0);
        self.cache_basic_filter_for_block(genesis, &[], &FilterHeader::all_zeros())?;
        self.remember_block_undo(genesis.block_hash(), vec![Vec::new()]);
        self.store
            .insert_undo(genesis.block_hash(), &[Vec::new()])?;
        if let Some(stats) = self.coin_stats.as_mut() {
            stats.apply_genesis(self.network);
        }
        self.persist_coinstats_record(genesis.block_hash(), 0)?;
        Ok(())
    }

    fn persist_coinstats_record(&mut self, hash: BlockHash, height: u32) -> Result<()> {
        if !self.coinstats_index_enabled {
            return Ok(());
        }
        let stats = self
            .coin_stats
            .as_ref()
            .context("coinstats accumulator is not initialized")?;
        self.coinstats_store.insert(&stats.record(hash, height))?;
        self.update_index_prune_locks(height);
        Ok(())
    }

    fn rebuild_block_index(&mut self) -> Result<()> {
        let hashes: Vec<BlockHash> = self.store.hashes().copied().collect();
        let mut blocks = Vec::new();
        for hash in hashes {
            if self.block_index.contains_key(&hash) {
                continue;
            }
            if let Some(block) = self.store.get(&hash)? {
                blocks.push((hash, block));
            }
        }
        for _ in 0..blocks.len() {
            let mut progress = false;
            for (hash, block) in &blocks {
                if self.block_index.contains_key(hash) {
                    continue;
                }
                let Some(parent) = self.block_index.get(&block.header.prev_blockhash).copied()
                else {
                    continue;
                };
                self.block_index.insert(
                    *hash,
                    BlockNode {
                        header: block.header,
                        height: parent.height.saturating_add(1),
                        chain_work: parent.chain_work + block.header.work(),
                    },
                );
                self.assign_header_sequence_id(*hash);
                progress = true;
            }
            if !progress {
                break;
            }
        }
        for (hash, block) in blocks {
            if let Some(node) = self.block_index.get(&hash).copied() {
                self.index_all_transactions(&block, node.height);
            } else {
                let _ = self.queue_orphan_block(block.header.prev_blockhash, block);
            }
        }
        Ok(())
    }

    fn rebuild_transaction_index(&mut self) -> Result<()> {
        if !self.tx_index_all_enabled {
            return Ok(());
        }
        let mut hashes: Vec<BlockHash> = self.store.hashes().copied().collect();
        hashes.sort_by_key(|hash| {
            self.block_index
                .get(hash)
                .map(|node| (node.height, hash.to_string()))
                .unwrap_or((u32::MAX, hash.to_string()))
        });
        self.tx_index_all.clear();
        for hash in hashes {
            let Some(node) = self.block_index.get(&hash).copied() else {
                continue;
            };
            let Some(block) = self.store.get(&hash)? else {
                continue;
            };
            self.index_all_transactions(&block, node.height);
        }
        Ok(())
    }

    fn rebuild_coinstats_index(&mut self) -> Result<()> {
        let active_chain = self.active_chain.clone();
        let tip_height = self.height();
        let current_utxos = if self.utxos_materialized {
            self.utxos.clone()
        } else {
            self.load_utxo_map_from_store()?
        };
        let indexed_base = active_chain
            .iter()
            .enumerate()
            .rev()
            .find_map(|(height, hash)| {
                self.coinstats_store
                    .get(hash)
                    .ok()
                    .flatten()
                    .filter(|record| {
                        record.height == u32::try_from(height).unwrap_or(u32::MAX)
                            && record.total_subsidy_sat != 0
                    })
                    .map(|record| (u32::try_from(height).unwrap_or(u32::MAX), record))
            });

        let (mut utxos, mut stats, first_height) = if let Some((base_height, record)) = indexed_base
        {
            let mut utxos = current_utxos;
            for height in (base_height.saturating_add(1)..=tip_height).rev() {
                let hash = active_chain
                    .get(usize::try_from(height).unwrap_or(usize::MAX))
                    .copied()
                    .context("coinstats active chain height is out of range")?;
                let block = self
                    .store
                    .get(&hash)?
                    .with_context(|| format!("coinstats index is missing block {hash}"))?;
                let undo = self
                    .store
                    .get_undo(&hash)?
                    .with_context(|| format!("coinstats undo is missing block {hash}"))?;
                self.disconnect_block_from_utxos(&mut utxos, &block, height, &undo)?;
            }
            let mut stats = CoinStatsState::from_utxos(&utxos);
            stats.load_cumulative_from_record(&record);
            (utxos, stats, base_height.saturating_add(1))
        } else {
            (HashMap::new(), CoinStatsState::default(), 0)
        };

        for height in first_height..=tip_height {
            let hash = active_chain
                .get(usize::try_from(height).unwrap_or(usize::MAX))
                .copied()
                .context("coinstats active chain height is out of range")?;
            let block = self
                .store
                .get(&hash)?
                .with_context(|| format!("coinstats index is missing block {hash}"))?;
            apply_block_to_coin_stats(self.network, &mut utxos, &mut stats, &block, height);
            let record = stats.record(hash, height);
            self.coinstats_store.insert(&record)?;
        }
        self.coin_stats = Some(stats);
        Ok(())
    }

    fn activate_chain(&mut self, tip_hash: BlockHash) -> Result<()> {
        if self.has_invalid_ancestor(tip_hash) {
            bail!("cannot activate an invalidated chain")
        }
        self.materialize_utxos()?;
        let mut path = Vec::new();
        let mut cursor = tip_hash;
        loop {
            path.push(cursor);
            if cursor == self.network_genesis_hash() {
                break;
            }
            let node = self
                .block_index
                .get(&cursor)
                .copied()
                .context("candidate chain is missing a block index entry")?;
            cursor = node.header.prev_blockhash;
        }
        path.reverse();
        let snapshot_invalidated = self.snapshot_base.is_some_and(|base| !path.contains(&base));
        let replay_snapshot = if !snapshot_invalidated {
            self.load_snapshot(&path)
                .ok()
                .flatten()
                .and_then(|(snapshot, verified)| verified.then_some(snapshot))
        } else {
            None
        };
        let replay_start = replay_snapshot
            .as_ref()
            .map_or(0, |snapshot| snapshot.headers.len());
        let common_height = path.iter().enumerate().rev().find_map(|(height, hash)| {
            self.active_chain
                .get(height)
                .is_some_and(|active_hash| active_hash == hash)
                .then_some(u32::try_from(height).ok())
                .flatten()
        });
        // While a snapshot is serving UTXOs, the ordinary active headers may
        // still be on a shorter divergent fork.  The live UTXO map then
        // belongs to the snapshot chain, so disconnecting the divergent
        // suffix against it would make the candidate's first block appear to
        // violate BIP30.  Use the full replay path for this transition; it
        // starts from genesis and validates the candidate chain against its
        // own UTXO history.
        let pending_snapshot_reorg = self.snapshot_base.is_some_and(|base| {
            !self.snapshot_validated && !self.is_active_block(&base) && path.contains(&base)
        });
        if let Some(common_height) = common_height.filter(|_| !pending_snapshot_reorg) {
            let active_suffix_len =
                usize::try_from(self.height().saturating_sub(common_height)).unwrap_or(usize::MAX);
            let common_height_index = usize::try_from(common_height).unwrap_or(usize::MAX);
            let candidate_suffix_len = path
                .len()
                .saturating_sub(common_height_index.saturating_add(1));
            let suffix_len = active_suffix_len.max(candidate_suffix_len);
            if (common_height < self.height()
                || candidate_suffix_len >= MIN_SUFFIX_ACTIVATION_BLOCKS)
                && (self.is_pruned() || suffix_len >= MIN_SUFFIX_ACTIVATION_BLOCKS)
                && self.activate_chain_from_pruned_suffix(&path, common_height)?
            {
                return Ok(());
            }
        }
        let missing_block = {
            let mut missing = None;
            for hash in path.iter().skip(replay_start) {
                if self.store.get(hash)?.is_none() {
                    missing = Some(*hash);
                    break;
                }
            }
            missing
        };
        if let Some(missing_hash) = missing_block {
            bail!("candidate block {missing_hash} is missing");
        }
        let blocks = path
            .iter()
            .skip(replay_start)
            .map(|hash| self.store.get(hash))
            .collect::<Result<Vec<Option<Block>>>>()?
            .into_iter()
            .enumerate()
            .map(|(index, block)| {
                block.with_context(|| {
                    format!("candidate block {} is missing", path[replay_start + index])
                })
            })
            .collect::<Result<Vec<Block>>>()?;

        let old_active_chain = std::mem::take(&mut self.active_chain);
        let old_segwit_validated_blocks = self.segwit_validated_blocks.clone();
        let old_headers = std::mem::take(&mut self.headers);
        let old_active_tx_counts = std::mem::take(&mut self.active_tx_counts);
        let old_active_tx_totals = std::mem::take(&mut self.active_tx_totals);
        let old_utxos = std::mem::take(&mut self.utxos);
        let old_utxos_materialized = self.utxos_materialized;
        let old_tx_index = std::mem::take(&mut self.tx_index);
        let old_tx_index_duplicates = std::mem::take(&mut self.tx_index_duplicates);
        let mut tx_index_all_changes = HashMap::new();
        let old_history = std::mem::take(&mut self.history);
        let old_history_materialized = self.history_materialized;
        let old_spent_by = std::mem::take(&mut self.spent_by);
        let old_basic_filter_cache = std::mem::take(&mut self.basic_filter_cache);
        let old_block_undo_cache = std::mem::take(&mut self.block_undo_cache);
        let old_coin_stats = std::mem::take(&mut self.coin_stats);
        let old_snapshot_base = self.snapshot_base;
        let old_snapshot_validated = self.snapshot_validated;
        let old_snapshot_validation_error = self.snapshot_validation_error.clone();
        let old_background_validation = self.background_validation.take();
        self.active_chain.clear();
        self.headers.clear();
        self.active_tx_counts.clear();
        self.active_tx_totals.clear();
        self.utxos.clear();
        self.utxos_materialized = true;
        self.tx_index.clear();
        self.tx_index_duplicates.clear();
        self.history.clear();
        self.history_materialized = true;
        self.spent_by.clear();
        self.coin_stats = self.coinstats_index_enabled.then(CoinStatsState::default);
        let replay = (|| -> Result<()> {
            if snapshot_invalidated {
                self.snapshot_base = None;
                self.snapshot_validated = true;
                self.snapshot_validation_error = None;
            }
            if let Some(snapshot) = replay_snapshot {
                let snapshot_chain_len = snapshot.headers.len();
                self.active_chain = path[..snapshot_chain_len].to_vec();
                self.headers = snapshot.headers;
                self.utxos = snapshot.utxos;
                self.tx_index = snapshot
                    .tx_index
                    .into_iter()
                    .map(|(txid, location)| (txid, ActiveTxLocation::from(&location)))
                    .collect();
                self.tx_index_duplicates = snapshot
                    .tx_index_duplicates
                    .into_iter()
                    .map(|(txid, locations)| {
                        (txid, locations.iter().map(ActiveTxLocation::from).collect())
                    })
                    .collect();
                self.history = snapshot.history;
                self.active_tx_counts = old_active_tx_counts
                    .get(..snapshot_chain_len)
                    .unwrap_or_default()
                    .to_vec();
                self.active_tx_totals = cumulative_tx_counts(&self.active_tx_counts);
                if self.txospender_index_enabled {
                    // Core's txospender index rewinds asynchronously.  Keep
                    // the previous map visible while the chain transition is
                    // reported, then let the next connected block overwrite
                    // or remove entries from the disconnected branch.
                    self.spent_by = old_spent_by.clone();
                    if self.spent_by.is_empty() {
                        self.spent_by = snapshot.spent_by.unwrap_or_default();
                    }
                }
                let headers = self.headers.clone();
                self.index_active_headers(&headers)?;
                if let Some(stats) = self.coin_stats.as_mut() {
                    *stats = CoinStatsState::from_utxos(&self.utxos);
                    if let Some(record) = self.coinstats_store.get(&path[snapshot_chain_len - 1])? {
                        stats.load_cumulative_from_record(&record);
                    }
                }
                for block in &blocks {
                    self.connect_block_internal_with_index_journal(
                        block,
                        false,
                        Some(&mut tx_index_all_changes),
                    )?;
                }
            } else {
                self.initialize_genesis(&blocks[0])?;
                for block in blocks.iter().skip(1) {
                    self.connect_block_internal_with_index_journal(
                        block,
                        false,
                        Some(&mut tx_index_all_changes),
                    )?;
                }
            }
            self.persist_metadata()?;
            self.persist_snapshot()
        })();
        if let Err(error) = replay {
            self.active_chain = old_active_chain;
            self.segwit_validated_blocks = old_segwit_validated_blocks;
            self.headers = old_headers;
            self.active_tx_counts = old_active_tx_counts;
            self.active_tx_totals = old_active_tx_totals;
            self.utxos = old_utxos;
            self.utxos_materialized = old_utxos_materialized;
            self.tx_index = old_tx_index;
            self.tx_index_duplicates = old_tx_index_duplicates;
            for (txid, previous) in tx_index_all_changes {
                match previous {
                    Some(location) => {
                        self.tx_index_all.insert(txid, location);
                    }
                    None => {
                        self.tx_index_all.remove(&txid);
                    }
                }
            }
            self.history = old_history;
            self.history_materialized = old_history_materialized;
            self.spent_by = old_spent_by;
            self.basic_filter_cache = old_basic_filter_cache;
            self.block_undo_cache = old_block_undo_cache;
            self.coin_stats = old_coin_stats;
            self.snapshot_base = old_snapshot_base;
            self.snapshot_validated = old_snapshot_validated;
            self.snapshot_validation_error = old_snapshot_validation_error;
            self.background_validation = old_background_validation.clone();
            return Err(error);
        }
        if snapshot_invalidated {
            if let Some(background) = old_background_validation.as_ref() {
                background.cancel.store(true, Ordering::Release);
            }
            self.background_validation = None;
            self.remove_snapshot_provenance_file()?;
            self.remove_assumeutxo_artifacts()?;
        } else {
            self.background_validation = old_background_validation;
        }
        self.release_materialized_utxos();
        self.release_materialized_history();
        self.update_ibd_status();
        Ok(())
    }

    /// Activate a fork without replaying the pruned prefix of the active
    /// chain. Core's normal reorg path disconnects the old active suffix with
    /// undo data and then connects the candidate suffix; doing the same here
    /// keeps a pruned node able to reorganize without requiring block one.
    ///
    /// The method returns `Ok(false)` when the required old-branch bodies or
    /// undo records are unavailable. In that case the caller retains the
    /// ordinary full-replay error, which is more useful for callers that are
    /// not operating on a pruned chain.
    fn activate_chain_from_pruned_suffix(
        &mut self,
        path: &[BlockHash],
        common_height: u32,
    ) -> Result<bool> {
        let old_tip_height = self.height();
        let common_height_usize =
            usize::try_from(common_height).context("common chain height does not fit in memory")?;
        if common_height_usize >= self.active_chain.len()
            || path.get(common_height_usize) != self.active_chain.get(common_height_usize)
        {
            return Ok(false);
        }

        let mut disconnected = Vec::new();
        for height in (common_height.saturating_add(1)..=old_tip_height).rev() {
            let Some(hash) = self.active_chain.get(height as usize).copied() else {
                return Ok(false);
            };
            let Some(block) = self.store.get(&hash)? else {
                return Ok(false);
            };
            let undo = if let Some(undo) = self.block_undo_cache.get(&hash) {
                undo.clone()
            } else {
                let Some(undo) = self.store.get_undo(&hash)? else {
                    return Ok(false);
                };
                undo
            };
            disconnected.push((height, block, undo));
        }

        let candidate_blocks = path
            .iter()
            .skip(common_height_usize.saturating_add(1))
            .map(|hash| self.store.get(hash))
            .collect::<Result<Vec<Option<Block>>>>()?
            .into_iter()
            .enumerate()
            .map(|(offset, block)| {
                block.with_context(|| {
                    format!(
                        "candidate block {} is missing",
                        path[common_height_usize.saturating_add(1) + offset]
                    )
                })
            })
            .collect::<Result<Vec<Block>>>()?;

        // Validate the whole transition against a temporary UTXO map before
        // changing any active-chain indexes. This keeps malformed candidate
        // blocks from leaving the live chain half-disconnected.
        let mut disconnected_utxos = self.utxos.clone();
        for (height, block, undo) in &disconnected {
            self.disconnect_block_from_utxos(&mut disconnected_utxos, block, *height, undo)?;
        }
        let mut candidate_utxos = disconnected_utxos.clone();
        for (offset, block) in candidate_blocks.iter().enumerate() {
            let height = common_height
                .saturating_add(1)
                .saturating_add(u32::try_from(offset).context("candidate chain is too long")?);
            let parent_hash = block.header.prev_blockhash;
            let application = self.validate_block_transactions(
                block,
                height,
                &candidate_utxos,
                self.median_time_past_for_parent(parent_hash),
            )?;
            apply_block_to_utxos(
                &mut candidate_utxos,
                block,
                height,
                self.median_time_past_for_parent(parent_hash),
                application.spent_entries,
            );
        }

        // The temporary maps above are the exact common-ancestor and
        // candidate UTXO states. The durable store, however, still contains
        // the old active tip. Persist only the delta from that old serving
        // state to the candidate state: replacing the entire UTXO log here
        // is prohibitively expensive for pruning tests whose coinbase
        // scripts are close to one megabyte each.
        let mut utxo_removals = Vec::new();
        for (outpoint, previous) in &self.utxos {
            if candidate_utxos.get(outpoint) != Some(previous) {
                utxo_removals.push(*outpoint);
            }
        }
        let mut utxo_additions = Vec::new();
        for (outpoint, current) in &candidate_utxos {
            if self.utxos.get(outpoint) != Some(current) {
                utxo_additions.push((*outpoint, Self::stored_utxo(current)));
            }
        }

        if !self.history_materialized {
            self.history = self.load_history_map_from_store()?;
            self.history_materialized = true;
        }

        let snapshot_invalidated = self.snapshot_base.is_some_and(|base| !path.contains(&base));

        for (height, _, _) in &disconnected {
            self.move_index_prune_locks_back(height.saturating_sub(1));
        }
        self.active_chain.truncate(common_height_usize + 1);
        self.headers.truncate(common_height_usize + 1);
        self.active_tx_counts.truncate(common_height_usize + 1);
        self.active_tx_totals.truncate(common_height_usize + 1);
        // The live map must start at the common ancestor. The candidate map
        // above was advanced only as a validation dry run; the normal block
        // connector will apply that suffix again while updating all indexes.
        self.utxos = disconnected_utxos;
        self.utxos_materialized = true;
        self.side_chain_utxos = None;

        self.history.retain(|_, entries| {
            entries.retain(|entry| entry.height <= common_height);
            !entries.is_empty()
        });
        self.rebuild_active_transaction_index_through(common_height);
        if self.txospender_index_enabled {
            self.spent_by.retain(|_, (_, _, block_hash, height)| {
                *height <= common_height && self.active_chain.contains(block_hash)
            });
        } else {
            self.spent_by.clear();
        }

        if self.coinstats_index_enabled {
            let mut stats = CoinStatsState::from_utxos(&self.utxos);
            if let Some(common_hash) = path.get(common_height_usize)
                && let Some(record) = self.coinstats_store.get(common_hash)?
            {
                stats.load_cumulative_from_record(&record);
            }
            self.coin_stats = Some(stats);
        } else {
            self.coin_stats = None;
        }

        let mut tx_index_all_changes = HashMap::new();
        for block in &candidate_blocks {
            self.connect_block_internal_with_index_journal(
                block,
                false,
                Some(&mut tx_index_all_changes),
            )?;
        }

        self.utxo_store
            .apply_batch(&utxo_removals, &utxo_additions)?;
        self.persist_utxo_store_tip()?;
        self.sync_electrum_history_store()?;
        self.persist_electrum_history_store_tip()?;
        self.persist_metadata()?;

        if snapshot_invalidated {
            if let Some(background) = self.background_validation.take() {
                background.cancel.store(true, Ordering::Release);
            }
            self.snapshot_base = None;
            self.snapshot_validated = true;
            self.snapshot_validation_error = None;
            self.remove_snapshot_provenance_file()?;
            self.remove_assumeutxo_artifacts()?;
        }
        self.release_materialized_utxos();
        self.release_materialized_history();
        self.update_ibd_status();
        Ok(true)
    }

    fn move_index_prune_locks_back(&mut self, max_height_first: u32) {
        if !self.prune_mode {
            return;
        }
        for lock in self.prune_locks.values_mut() {
            if lock.height_first <= u64::from(max_height_first) {
                continue;
            }
            lock.height_first = u64::from(max_height_first);
            debug!(
                "{} prune lock moved back to {}",
                lock.desc, max_height_first
            );
        }
    }

    fn rebuild_active_transaction_index_through(&mut self, max_height: u32) {
        let mut locations: HashMap<Txid, Vec<ActiveTxLocation>> = HashMap::new();
        for (txid, location) in &self.tx_index {
            if location.height <= max_height {
                locations.entry(*txid).or_default().push(*location);
            }
        }
        for (txid, tx_locations) in &self.tx_index_duplicates {
            let retained = tx_locations
                .iter()
                .copied()
                .filter(|location| location.height <= max_height);
            locations.entry(*txid).or_default().extend(retained);
        }

        self.tx_index.clear();
        self.tx_index_duplicates.clear();
        for (txid, mut tx_locations) in locations {
            tx_locations.sort_by_key(|location| (location.height, location.transaction_index));
            tx_locations.dedup();
            let Some(latest) = tx_locations.last().copied() else {
                continue;
            };
            self.tx_index.insert(txid, latest);
            if tx_locations.len() > 1 {
                self.tx_index_duplicates.insert(txid, tx_locations);
            }
        }
    }

    fn cache_basic_filter_for_block(
        &mut self,
        block: &Block,
        spent_entries: &[(OutPoint, UtxoEntry)],
        previous_filter_header: &FilterHeader,
    ) -> Result<()> {
        if !self.blockfilter_index_enabled {
            return Ok(());
        }
        let previous_outputs: HashMap<OutPoint, TxOut> = spent_entries
            .iter()
            .map(|(outpoint, entry)| (*outpoint, entry.output.clone()))
            .collect();
        let mut created_outputs = HashMap::new();
        for transaction in &block.txdata {
            let txid = transaction.compute_txid();
            for (vout, output) in transaction.output.iter().enumerate() {
                created_outputs.insert(OutPoint::new(txid, vout as u32), output.clone());
            }
        }
        let filter = BlockFilter::new_script_filter(block, |outpoint| {
            previous_outputs
                .get(outpoint)
                .or_else(|| created_outputs.get(outpoint))
                .map(|output| output.script_pubkey.clone())
                .ok_or(bitcoin::bip158::Error::UtxoMissing(*outpoint))
        })?;
        let filter_header = filter.filter_header(previous_filter_header);
        self.filter_store
            .insert(block.block_hash(), &filter.content, filter_header)?;
        self.cache_basic_filter(block.block_hash(), filter.content, filter_header);
        if let Some(node) = self.block_index.get(&block.block_hash()) {
            self.update_index_prune_locks(node.height);
        }
        Ok(())
    }

    fn cache_block_undo(
        &mut self,
        block: &Block,
        spent_entries: &[(OutPoint, UtxoEntry)],
    ) -> Result<()> {
        let mut undo = vec![Vec::new()];
        let mut offset = 0usize;
        for transaction in block.txdata.iter().skip(1) {
            let end = offset
                .checked_add(transaction.input.len())
                .ok_or_else(|| anyhow::anyhow!("block undo input count overflow"))?;
            if end > spent_entries.len() {
                bail!("block undo input count does not match validation state")
            }
            undo.push(
                spent_entries[offset..end]
                    .iter()
                    .map(|(_, entry)| entry.output.clone())
                    .collect(),
            );
            offset = end;
        }
        if offset != spent_entries.len() {
            bail!("block undo contains unexpected spent outputs")
        }
        self.store.insert_undo(block.block_hash(), &undo)?;
        self.remember_block_undo(block.block_hash(), undo);
        Ok(())
    }

    fn remember_block_undo(&mut self, hash: BlockHash, undo: Vec<Vec<TxOut>>) {
        self.block_undo_cache.insert(hash, undo);
        while self.block_undo_cache.len() > MAX_UNDO_CACHE_ENTRIES {
            let Some(oldest) = self.block_undo_cache.keys().next().copied() else {
                break;
            };
            self.block_undo_cache.remove(&oldest);
        }
    }

    fn is_descendant_or_self(&self, candidate: &BlockHash, ancestor: &BlockHash) -> bool {
        let mut cursor = *candidate;
        loop {
            if cursor == *ancestor {
                return true;
            }
            let Some(node) = self.block_index.get(&cursor) else {
                return false;
            };
            if node.height == 0 {
                return false;
            }
            cursor = node.header.prev_blockhash;
        }
    }

    fn has_invalid_ancestor(&self, hash: BlockHash) -> bool {
        if self.invalid_blocks.is_empty() {
            return false;
        }
        let mut cursor = hash;
        loop {
            if self.invalid_blocks.contains(&cursor) {
                return true;
            }
            let Some(node) = self.block_index.get(&cursor) else {
                return false;
            };
            if node.height == 0 {
                return false;
            }
            cursor = node.header.prev_blockhash;
        }
    }

    fn best_valid_tip_hash(&self) -> Option<BlockHash> {
        self.block_index
            .iter()
            .filter(|(hash, _)| {
                !self.has_invalid_ancestor(**hash)
                    && self.has_full_block_data_to_active_fork(**hash)
            })
            .max_by(|(left_hash, left), (right_hash, right)| {
                left.chain_work
                    .cmp(&right.chain_work)
                    .then_with(|| {
                        self.precious_priority(right_hash)
                            .cmp(&self.precious_priority(left_hash))
                    })
                    // Core's CBlockIndexWorkComparator prefers the block
                    // that became fully available first when chainwork is
                    // equal.  Loaded non-active blocks share one sequence
                    // ID, so retain a deterministic fallback for that case.
                    .then_with(|| {
                        self.block_sequence_id(right_hash)
                            .cmp(&self.block_sequence_id(left_hash))
                    })
                    .then_with(|| right_hash.to_string().cmp(&left_hash.to_string()))
            })
            .map(|(hash, _)| *hash)
    }

    fn assign_block_sequence_id(&mut self, hash: BlockHash) {
        if self.block_sequence_ids.contains_key(&hash) {
            return;
        }
        self.unlinked_body_order.remove(&hash);
        let sequence_id = self.next_block_sequence_id;
        self.block_sequence_ids.insert(hash, sequence_id);
        self.next_block_sequence_id = self.next_block_sequence_id.saturating_add(1);
    }

    fn block_sequence_id(&self, hash: &BlockHash) -> u64 {
        self.block_sequence_ids
            .get(hash)
            .copied()
            .unwrap_or(u64::MAX)
    }

    fn assign_header_sequence_id(&mut self, hash: BlockHash) {
        if self.header_sequence_ids.contains_key(&hash) {
            return;
        }
        let sequence_id = self.next_header_sequence_id;
        self.header_sequence_ids.insert(hash, sequence_id);
        self.next_header_sequence_id = self.next_header_sequence_id.saturating_add(1);
    }

    fn header_sequence_id(&self, hash: &BlockHash) -> u64 {
        self.header_sequence_ids
            .get(hash)
            .copied()
            .unwrap_or(u64::MAX)
    }

    /// Recreate Core's restart behavior for its memory-only candidate order:
    /// active-chain entries are loaded with sequence zero, while full blocks
    /// already present on non-active forks are loaded with the same neutral
    /// sequence. Newly received blocks then get increasing IDs.
    fn initialize_block_sequence_ids_after_load(&mut self) {
        self.block_sequence_ids.clear();
        self.header_sequence_ids.clear();
        for hash in &self.active_chain {
            self.block_sequence_ids.insert(*hash, 0);
            self.header_sequence_ids.insert(*hash, 0);
        }
        let active: HashSet<BlockHash> = self.active_chain.iter().copied().collect();
        let mut has_loaded_fork = false;
        for hash in self.block_index.keys().copied().collect::<Vec<_>>() {
            if !active.contains(&hash) && self.store.contains(&hash) {
                self.block_sequence_ids.insert(hash, 1);
                has_loaded_fork = true;
            }
            if !active.contains(&hash) {
                self.header_sequence_ids.insert(hash, 1);
            }
        }
        self.next_block_sequence_id = if has_loaded_fork { 2 } else { 1 };
        self.next_header_sequence_id = 2;
    }

    fn has_full_block_data_to_active_fork(&self, hash: BlockHash) -> bool {
        let mut cursor = hash;
        while !self.is_active_block(&cursor) {
            if !self.store.contains(&cursor) {
                return false;
            }
            let Some(node) = self.block_index.get(&cursor) else {
                return false;
            };
            cursor = node.header.prev_blockhash;
        }
        true
    }

    fn precious_priority(&self, hash: &BlockHash) -> i32 {
        // Core's PreciousBlock assigns a reverse sequence ID to exactly the
        // requested block index.  Descendants receive their own normal
        // arrival sequence IDs and must not inherit the preference.
        self.precious_blocks.get(hash).copied().unwrap_or(0)
    }

    fn index_transactions(&mut self, block: &Block, height: u32) {
        for (transaction_index, transaction) in block.txdata.iter().enumerate() {
            let txid = transaction.compute_txid();
            let mut scripts = HashSet::new();
            for (output_index, output) in transaction.output.iter().enumerate() {
                let outpoint = OutPoint::new(txid, output_index as u32);
                if height != 0 && !is_unspendable_script(&output.script_pubkey) {
                    self.insert_utxo(
                        outpoint,
                        UtxoEntry {
                            output: output.clone(),
                            height,
                            median_time_past: block.header.time,
                            coinbase: transaction_index == 0,
                        },
                    );
                }
                scripts.insert(electrum_script_hash(&output.script_pubkey));
            }
            for script_hash in scripts {
                self.add_history(&script_hash, HistoryEntry { txid, height });
            }
            self.index_active_transaction(
                txid,
                TxLocation {
                    block_hash: block.block_hash(),
                    height,
                    transaction_index,
                },
            );
            if self.tx_index_all_enabled {
                self.tx_index_all.insert(
                    txid,
                    TxLocation {
                        block_hash: block.block_hash(),
                        height,
                        transaction_index,
                    },
                );
            }
        }
        if self.txospender_index_enabled {
            self.index_block_spends(block, height);
        }
    }

    fn index_block_spends(&mut self, block: &Block, height: u32) {
        let block_hash = block.block_hash();
        for transaction in &block.txdata {
            let txid = transaction.compute_txid();
            for (input_index, input) in transaction.input.iter().enumerate() {
                if !input.previous_output.is_null() {
                    self.spent_by.insert(
                        input.previous_output,
                        (txid, input_index, block_hash, height),
                    );
                }
            }
        }
    }

    fn rebuild_spent_index(&mut self) -> Result<()> {
        self.spent_by.clear();
        if !self.txospender_index_enabled {
            return Ok(());
        }
        let active_chain = self.active_chain.clone();
        for hash in active_chain {
            let height = self
                .block_index
                .get(&hash)
                .map(|node| node.height)
                .with_context(|| format!("active block {hash} is not indexed"))?;
            let Some(block) = self.store.get(&hash)? else {
                if self
                    .prune_height
                    .is_some_and(|prune_height| height < prune_height)
                {
                    continue;
                }
                bail!("active block {hash} is missing from block store")
            };
            self.index_block_spends(&block, height);
        }
        Ok(())
    }

    fn validate_persisted_spent_index(&self) -> Result<()> {
        let active_chain: HashSet<BlockHash> = self.active_chain.iter().copied().collect();
        for (outpoint, (txid, _input_index, block_hash, height)) in &self.spent_by {
            let node = self
                .block_index
                .get(block_hash)
                .with_context(|| format!("spent index references unknown block {block_hash}"))?;
            if node.height != *height || !active_chain.contains(block_hash) {
                bail!("spent index references an inactive or mismatched block");
            }
            let location = if self.tx_index_all_enabled {
                self.tx_index_all.get(txid).cloned().or_else(|| {
                    self.tx_index
                        .get(txid)
                        .and_then(|location| self.expand_active_tx_location(*location))
                })
            } else {
                self.tx_index
                    .get(txid)
                    .and_then(|location| self.expand_active_tx_location(*location))
            }
            .with_context(|| format!("spent index references unknown transaction {txid}"))?;
            if location.block_hash != *block_hash || location.height != *height {
                bail!(
                    "spent index transaction {} does not match its spending block",
                    txid
                );
            }
            if outpoint.is_null() {
                bail!("spent index contains a null outpoint");
            }
        }
        Ok(())
    }

    fn index_all_transactions(&mut self, block: &Block, height: u32) {
        if !self.tx_index_all_enabled {
            return;
        }
        for (transaction_index, transaction) in block.txdata.iter().enumerate() {
            let txid = transaction.compute_txid();
            self.tx_index_all.insert(
                txid,
                TxLocation {
                    block_hash: block.block_hash(),
                    height,
                    transaction_index,
                },
            );
        }
    }

    fn index_active_transactions(&mut self, block: &Block, height: u32) {
        for (transaction_index, transaction) in block.txdata.iter().enumerate() {
            self.index_active_transaction(
                transaction.compute_txid(),
                TxLocation {
                    block_hash: block.block_hash(),
                    height,
                    transaction_index,
                },
            );
        }
    }

    fn index_active_transaction(&mut self, txid: Txid, location: TxLocation) {
        let compact_location = ActiveTxLocation::from(&location);
        let previous = self.tx_index.insert(txid, compact_location);
        if let Some(previous) = previous {
            if previous == compact_location {
                return;
            }
            let locations = self.tx_index_duplicates.entry(txid).or_default();
            if !locations.iter().any(|candidate| candidate == &previous) {
                locations.push(previous);
            }
        }
        if let Some(locations) = self.tx_index_duplicates.get_mut(&txid) {
            if !locations
                .iter()
                .any(|candidate| candidate == &compact_location)
            {
                locations.push(compact_location);
            }
            locations.sort_by_key(|candidate| (candidate.height, candidate.transaction_index));
        }
    }

    fn stored_utxo(entry: &UtxoEntry) -> StoredUtxo {
        StoredUtxo {
            output: entry.output.clone(),
            height: entry.height,
            median_time_past: entry.median_time_past,
            coinbase: entry.coinbase,
        }
    }

    fn decoded_utxo(entry: StoredUtxo) -> UtxoEntry {
        UtxoEntry {
            output: entry.output,
            height: entry.height,
            median_time_past: entry.median_time_past,
            coinbase: entry.coinbase,
        }
    }

    fn load_utxo_map_from_store(&self) -> Result<HashMap<OutPoint, UtxoEntry>> {
        Ok(self.load_utxo_entries_from_store()?.into_iter().collect())
    }

    fn load_utxo_entries_from_store(&self) -> Result<Vec<(OutPoint, UtxoEntry)>> {
        Ok(self
            .utxo_store
            .entries()?
            .into_iter()
            .map(|(outpoint, entry)| (outpoint, Self::decoded_utxo(entry)))
            .collect())
    }

    fn load_history_map_from_store(&self) -> Result<HashMap<String, Vec<HistoryEntry>>> {
        Ok(self
            .electrum_history_store
            .entries()?
            .into_iter()
            .map(|(script_hash, entries)| {
                (
                    script_hash,
                    entries
                        .into_iter()
                        .map(|(txid, height)| HistoryEntry { txid, height })
                        .collect(),
                )
            })
            .collect())
    }

    fn active_history_map_for_read(&self) -> Result<HashMap<String, Vec<HistoryEntry>>> {
        if self.history_materialized {
            Ok(self.history.clone())
        } else {
            self.load_history_map_from_store()
        }
    }

    fn history_entries_for_update(&self, script_hash: &str) -> Result<Vec<HistoryEntry>> {
        if self.history_materialized {
            return Ok(self.history.get(script_hash).cloned().unwrap_or_default());
        }
        Ok(self
            .electrum_history_store
            .get(script_hash)?
            .into_iter()
            .map(|(txid, height)| HistoryEntry { txid, height })
            .collect())
    }

    fn append_history_update(
        &self,
        updates: &mut HashMap<String, Vec<HistoryEntry>>,
        script_hash: &str,
        entry: HistoryEntry,
    ) -> Result<()> {
        if !updates.contains_key(script_hash) {
            updates.insert(
                script_hash.to_owned(),
                self.history_entries_for_update(script_hash)?,
            );
        }
        let history = updates
            .get_mut(script_hash)
            .expect("history update was inserted above");
        if history.last() != Some(&entry) {
            history.push(entry);
        }
        Ok(())
    }

    fn persist_history_updates(
        &mut self,
        updates: HashMap<String, Vec<HistoryEntry>>,
    ) -> Result<()> {
        if updates.is_empty() {
            return Ok(());
        }
        let store_updates = updates
            .iter()
            .map(|(script_hash, entries)| {
                (
                    script_hash.clone(),
                    entries
                        .iter()
                        .map(|entry| (entry.txid, entry.height))
                        .collect(),
                )
            })
            .collect::<Vec<_>>();
        self.electrum_history_store.apply_batch(&store_updates)?;
        if self.history_materialized {
            for (script_hash, entries) in updates {
                self.history.insert(script_hash, entries);
            }
        }
        Ok(())
    }

    fn active_utxo_entries_for_read(&self) -> Vec<(OutPoint, UtxoEntry)> {
        if self.utxos_materialized {
            self.utxos
                .iter()
                .map(|(outpoint, entry)| (*outpoint, entry.clone()))
                .collect()
        } else {
            self.load_utxo_entries_from_store().unwrap_or_else(|_| {
                self.utxos
                    .iter()
                    .map(|(outpoint, entry)| (*outpoint, entry.clone()))
                    .collect()
            })
        }
    }

    fn active_utxo_map_for_read(&self) -> HashMap<OutPoint, UtxoEntry> {
        if self.utxos_materialized {
            self.utxos.clone()
        } else {
            self.load_utxo_map_from_store()
                .unwrap_or_else(|_| self.utxos.clone())
        }
    }

    fn materialize_utxos(&mut self) -> Result<()> {
        if !self.utxos_materialized {
            self.utxos = self.load_utxo_map_from_store()?;
            self.utxos_materialized = true;
        }
        Ok(())
    }

    fn release_materialized_utxos(&mut self) {
        self.utxos.clear();
        self.utxos_materialized = false;
    }

    fn release_materialized_history(&mut self) {
        self.history.clear();
        self.history_materialized = false;
    }

    fn utxo_store_tip_path(&self) -> PathBuf {
        self.data_dir.join("chainstate/utxos.tip")
    }

    fn persist_utxo_store_tip(&self) -> Result<()> {
        let path = self.utxo_store_tip_path();
        let temp = path.with_extension("tip.tmp");
        let contents = format!("{}\n{}\n", self.best_hash(), self.utxo_store.generation());
        fs::write(&temp, contents)?;
        fs::rename(temp, path)?;
        Ok(())
    }

    fn sync_utxo_store(&mut self) -> Result<()> {
        if !self.utxos_materialized {
            // Normal active-chain connects already commit the exact mutation
            // batch to the durable store. There is no resident map to copy
            // back, and rewriting the store here would destroy that state.
            return self.persist_utxo_store_tip();
        }
        let entries = self
            .utxos
            .iter()
            .map(|(outpoint, entry)| (*outpoint, Self::stored_utxo(entry)))
            .collect::<Vec<_>>();
        self.utxo_store.replace_all(entries)?;
        self.persist_utxo_store_tip()
    }

    fn reconcile_utxo_store(&mut self) -> Result<()> {
        let tip = fs::read_to_string(self.utxo_store_tip_path()).ok();
        let expected_tip = self.best_hash().to_string();
        let marker_matches = tip.as_deref().is_some_and(|tip| {
            let mut lines = tip.lines();
            lines.next().map(str::trim) == Some(expected_tip.as_str())
                && lines
                    .next()
                    .and_then(|generation| generation.trim().parse::<u64>().ok())
                    == Some(self.utxo_store.generation())
                && lines.next().is_none()
        });
        if marker_matches && self.utxo_store.len() == self.utxos.len() {
            return Ok(());
        }
        self.sync_utxo_store()
    }

    fn electrum_history_store_tip_path(&self) -> PathBuf {
        self.data_dir.join("indexes/electrum-history.tip")
    }

    fn persist_electrum_history_store_tip(&self) -> Result<()> {
        let path = self.electrum_history_store_tip_path();
        let temp = path.with_extension("tip.tmp");
        let contents = format!(
            "{}\n{}\n{}\n",
            self.best_hash(),
            self.electrum_history_store.generation(),
            self.electrum_history_store.len()
        );
        fs::write(&temp, contents)?;
        fs::rename(temp, path)?;
        Ok(())
    }

    fn sync_electrum_history_store(&mut self) -> Result<()> {
        if !self.history_materialized {
            // Normal active-chain connects append exact replacement values to
            // the durable store. There is no resident map to copy back.
            return self.persist_electrum_history_store_tip();
        }
        let entries = self
            .history
            .iter()
            .map(|(script_hash, history)| {
                (
                    script_hash.clone(),
                    history
                        .iter()
                        .map(|entry| (entry.txid, entry.height))
                        .collect(),
                )
            })
            .collect::<Vec<_>>();
        self.electrum_history_store.replace_all(entries)?;
        self.persist_electrum_history_store_tip()
    }

    fn reconcile_electrum_history_store(&mut self) -> Result<()> {
        let tip = fs::read_to_string(self.electrum_history_store_tip_path()).ok();
        let expected_tip = self.best_hash().to_string();
        let marker_matches = tip.as_deref().is_some_and(|tip| {
            let mut lines = tip.lines();
            lines.next().map(str::trim) == Some(expected_tip.as_str())
                && lines
                    .next()
                    .and_then(|generation| generation.trim().parse::<u64>().ok())
                    == Some(self.electrum_history_store.generation())
                && lines
                    .next()
                    .and_then(|length| length.trim().parse::<usize>().ok())
                    == Some(self.electrum_history_store.len())
                && lines.next().is_none()
        });
        if marker_matches && self.electrum_history_store.len() == self.history.len() {
            return Ok(());
        }
        self.sync_electrum_history_store()
    }

    fn insert_utxo(&mut self, outpoint: OutPoint, entry: UtxoEntry) {
        self.missing_utxo_cache.lock().remove(&outpoint);
        if self.utxos_materialized {
            if self.utxos.contains_key(&outpoint) {
                self.remove_utxo(&outpoint);
            }
            self.utxos.insert(outpoint, entry.clone());
        } else if let Ok(Some(previous)) = self.utxo_store.get(&outpoint) {
            if let Some(stats) = self.coin_stats.as_mut() {
                stats.remove(&outpoint, &Self::decoded_utxo(previous));
            }
        }
        if let Some(stats) = self.coin_stats.as_mut() {
            stats.add(&outpoint, &entry);
        }
    }

    fn remove_utxo(&mut self, outpoint: &OutPoint) -> Option<UtxoEntry> {
        let entry = self
            .utxos_materialized
            .then(|| self.utxos.remove(outpoint))??;
        self.remove_utxo_entry(outpoint, &entry);
        Some(entry)
    }

    fn remove_utxo_entry(&mut self, outpoint: &OutPoint, entry: &UtxoEntry) {
        if let Some(stats) = self.coin_stats.as_mut() {
            stats.remove(outpoint, entry);
        }
    }

    fn add_history(&mut self, script_hash: &str, entry: HistoryEntry) {
        let history = self.history.entry(script_hash.to_owned()).or_default();
        if history.last() != Some(&entry) {
            history.push(entry);
        }
    }

    fn expected_target(&self, candidate_time: u32) -> Target {
        self.expected_target_for_parent(self.best_hash(), candidate_time)
    }

    fn validate_block_structure(
        &self,
        block: &Block,
        _network: Network,
        height: u32,
        expected_coinbase_value: u64,
    ) -> Result<validation::BlockValidationStats, ValidationError> {
        validation::validate_block_structure_with_signet_options_with_params(
            block,
            &self.deployment_parameters,
            height,
            expected_coinbase_value,
            self.signet_challenge.as_deref(),
            true,
        )
    }

    fn validate_header_context(
        &self,
        header: &bitcoin::block::Header,
        parent_hash: BlockHash,
        expected_target: Target,
        median_time_past: u32,
        check_pow: bool,
    ) -> Result<()> {
        if check_pow {
            validation::validate_header(
                self.network,
                header,
                parent_hash,
                expected_target,
                median_time_past,
            )?;
        } else {
            validation::validate_header_without_pow(
                self.network,
                header,
                parent_hash,
                expected_target,
                median_time_past,
            )?;
        }
        let parent = self
            .block_index
            .get(&parent_hash)
            .context("header parent is not indexed")?;
        let headers = self
            .headers_to_hash(&parent_hash)
            .context("header parent has no contiguous ancestor chain")?;
        validation::validate_mandatory_version_bits_with_params(
            &headers,
            &self.deployment_parameters,
            parent.height.saturating_add(1),
            header.version.to_consensus(),
        )?;
        Ok(())
    }

    fn expected_target_for_parent(&self, parent_hash: BlockHash, candidate_time: u32) -> Target {
        let parent_node = self
            .block_index
            .get(&parent_hash)
            .expect("parent is indexed");
        let height = parent_node.height.saturating_add(1);
        let previous = &parent_node.header;
        let params = self.network.params();
        let difficulty_interval = validation::difficulty_adjustment_interval(self.network);
        if params.no_pow_retargeting {
            return previous.target();
        }
        if height % difficulty_interval != 0 {
            if params.allow_min_difficulty_blocks
                && candidate_time
                    > previous
                        .time
                        .saturating_add((params.pow_target_spacing * 2) as u32)
            {
                return params.max_attainable_target;
            }
            if params.allow_min_difficulty_blocks
                && previous.target() == params.max_attainable_target
            {
                let mut cursor = parent_hash;
                while let Some(node) = self.block_index.get(&cursor) {
                    if node.height % difficulty_interval == 0
                        || node.header.target() != params.max_attainable_target
                    {
                        return node.header.target();
                    }
                    cursor = node.header.prev_blockhash;
                }
            }
            return previous.target();
        }
        let first_hash = self
            .ancestor_hash(parent_hash, height - difficulty_interval)
            .expect("difficulty interval ancestor exists");
        let first = &self
            .block_index
            .get(&first_hash)
            .expect("ancestor is indexed")
            .header;
        let timespan = previous.time.saturating_sub(first.time) as u64;
        let base_bits = if self.network == Network::Testnet4 {
            first.bits
        } else {
            previous.bits
        };
        CompactTarget::from_next_work_required(base_bits, timespan, params).into()
    }

    fn ancestor_hash(&self, mut hash: BlockHash, height: u32) -> Option<BlockHash> {
        let mut current_height = self.block_index.get(&hash)?.height;
        if current_height < height {
            return None;
        }
        while current_height > height {
            if self
                .active_chain
                .get(current_height as usize)
                .is_some_and(|active_hash| active_hash == &hash)
            {
                return self.active_chain.get(height as usize).copied();
            }
            hash = self.block_index.get(&hash)?.header.prev_blockhash;
            current_height -= 1;
        }
        (current_height == height).then_some(hash)
    }

    fn median_time_past(&self) -> u32 {
        let start = self.headers.len().saturating_sub(11);
        let mut times: Vec<u32> = self.headers[start..]
            .iter()
            .map(|header| header.time)
            .collect();
        times.sort_unstable();
        times[times.len() / 2]
    }

    fn median_time_past_for_parent(&self, parent_hash: BlockHash) -> u32 {
        let mut times = Vec::with_capacity(11);
        let mut cursor = parent_hash;
        for _ in 0..11 {
            let Some(node) = self.block_index.get(&cursor) else {
                break;
            };
            times.push(node.header.time);
            if node.height == 0 {
                break;
            }
            cursor = node.header.prev_blockhash;
        }
        times.sort_unstable();
        times[times.len() / 2]
    }

    fn network_genesis_hash(&self) -> BlockHash {
        genesis_block(self.network).block_hash()
    }

    fn persist_metadata(&self) -> Result<()> {
        let metadata = ChainMetadata {
            active_chain: self.active_chain.iter().map(ToString::to_string).collect(),
            headers: self.known_headers(),
            invalid_blocks: self
                .invalid_blocks
                .iter()
                .map(ToString::to_string)
                .collect(),
            prune_height: self.prune_height,
            prune_locks: self
                .prune_locks
                .iter()
                .filter(|(_, lock)| !lock.temporary)
                .map(|(id, lock)| (id.clone(), lock.clone()))
                .collect(),
            prune_protected_blocks: self
                .prune_protected_blocks
                .iter()
                .map(|(hash, height)| (hash.to_string(), *height))
                .collect(),
            segwit_validated_blocks: Some(
                self.active_chain
                    .iter()
                    .filter(|hash| self.segwit_validated_blocks.contains(*hash))
                    .map(ToString::to_string)
                    .collect(),
            ),
        };
        let bytes = serialize_internal(CHAIN_METADATA_MAGIC, &metadata)?;
        let path = self.data_dir.join("chainstate.bin");
        let temp = self.data_dir.join("chainstate.bin.tmp");
        fs::write(&temp, bytes)?;
        fs::rename(temp, path)?;
        self.persist_tx_counts()
    }

    fn persist_tx_counts(&self) -> Result<()> {
        if self.active_tx_counts.len() != self.active_chain.len() {
            // A pre-sidecar pruned snapshot may not contain enough data to
            // reconstruct old block counts. Keep that legacy node startable;
            // newly connected/reindexed nodes always have a complete vector.
            return Ok(());
        }
        let index = ActiveTxCounts {
            active_tip: self.best_hash().to_string(),
            counts: self.active_tx_counts.clone(),
        };
        let bytes = serialize_internal(CHAIN_TX_COUNTS_MAGIC, &index)?;
        let path = self.data_dir.join("chainstate.txcounters");
        let temp = self.data_dir.join("chainstate.txcounters.tmp");
        fs::write(&temp, bytes)?;
        fs::rename(temp, path)?;
        Ok(())
    }

    fn load_snapshot(&self, active_chain: &[BlockHash]) -> Result<Option<(ChainSnapshot, bool)>> {
        let path = self.data_dir.join("chainstate.snapshot");
        if !path.exists() {
            return Ok(None);
        }
        let bytes = fs::read(path)?;
        let snapshot = if bytes.starts_with(CHAIN_SNAPSHOT_MAGIC) {
            deserialize_chain_snapshot(&bytes)?
        } else {
            let Ok(snapshot) = serde_json::from_slice::<ChainSnapshot>(&bytes) else {
                return Ok(None);
            };
            snapshot
        };
        let checksum_path = self.snapshot_checksum_path();
        let verified = match fs::read_to_string(checksum_path) {
            Ok(checksum) => {
                if checksum.trim() != snapshot_checksum(&bytes) {
                    bail!("chainstate snapshot checksum mismatch");
                }
                true
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => false,
            Err(error) => return Err(error.into()),
        };
        let Some(snapshot_height) = snapshot.headers.len().checked_sub(1) else {
            return Ok(None);
        };
        if snapshot.headers.len() > active_chain.len()
            || active_chain
                .get(snapshot_height)
                .is_none_or(|hash| snapshot.tip != hash.to_string())
            || snapshot
                .headers
                .iter()
                .zip(active_chain.iter())
                .any(|(header, hash)| header.block_hash() != *hash)
        {
            return Ok(None);
        }
        Ok(Some((snapshot, verified)))
    }

    /// Load the durable mutation suffix after a full chainstate snapshot.
    /// The log is deliberately advisory: any missing, malformed, or
    /// mismatched record returns `None`, and startup falls back to ordinary
    /// consensus replay from the snapshot.
    fn load_chainstate_deltas(
        &mut self,
        active_chain: &[BlockHash],
        start_height: usize,
    ) -> Option<Vec<ChainstateDelta>> {
        if start_height >= active_chain.len() {
            return Some(Vec::new());
        }
        let mut parent_hash = *active_chain.get(start_height.checked_sub(1)?)?;
        let mut deltas = Vec::with_capacity(active_chain.len() - start_height);
        for (height, block_hash) in active_chain.iter().enumerate().skip(start_height) {
            let bytes = self.chainstate_store.get(block_hash).ok().flatten()?;
            let delta = deserialize_chainstate_delta(&bytes).ok()?;
            if delta.block_hash != *block_hash
                || delta.parent_hash != parent_hash
                || delta.height != u32::try_from(height).ok()?
                || delta.transactions.is_empty()
                || delta.transactions.iter().any(|(_, location)| {
                    location.block_hash != *block_hash
                        || location.height != u32::try_from(height).unwrap_or(u32::MAX)
                })
            {
                return None;
            }
            parent_hash = *block_hash;
            deltas.push(delta);
        }
        Some(deltas)
    }

    fn validate_chainstate_deltas(&self, deltas: &[ChainstateDelta]) -> Result<()> {
        let mut parent_hash = self.best_hash();
        let mut height = u32::try_from(self.active_chain.len())
            .context("active chain height does not fit u32")?;
        let mut touched = HashMap::<OutPoint, Option<UtxoEntry>>::new();
        for delta in deltas {
            if delta.height != height
                || delta.parent_hash != parent_hash
                || delta.transactions.is_empty()
            {
                bail!("chainstate delta does not extend the active chain")
            }
            let node = self.block_index.get(&delta.block_hash).with_context(|| {
                format!("chainstate delta block {} is not indexed", delta.block_hash)
            })?;
            if node.height != delta.height || node.header.prev_blockhash != delta.parent_hash {
                bail!("chainstate delta block index is inconsistent")
            }
            for (outpoint, entry) in &delta.spent {
                if entry.output.value > Amount::MAX_MONEY {
                    bail!("chainstate delta contains an output above the money range")
                }
                let current = match touched.get(outpoint) {
                    Some(current) => current.as_ref(),
                    None => self.utxos.get(outpoint),
                }
                .context("chainstate delta spends a missing output")?;
                if current != entry {
                    bail!("chainstate delta spent output metadata does not match")
                }
                touched.insert(*outpoint, None);
            }
            for (outpoint, entry) in &delta.created {
                if entry.height != delta.height || entry.output.value > Amount::MAX_MONEY {
                    bail!("chainstate delta contains invalid created output metadata")
                }
                touched.insert(*outpoint, Some(entry.clone()));
            }
            for (_, entry) in &delta.history {
                if entry.height != delta.height {
                    bail!("chainstate delta contains invalid history metadata")
                }
            }
            for (_, location) in &delta.transactions {
                if location.block_hash != delta.block_hash || location.height != delta.height {
                    bail!("chainstate delta contains invalid transaction metadata")
                }
            }
            for (_, (_, _, block_hash, spender_height)) in &delta.spent_by {
                if *block_hash != delta.block_hash || *spender_height != delta.height {
                    bail!("chainstate delta contains invalid spender metadata")
                }
            }
            parent_hash = delta.block_hash;
            height = height.saturating_add(1);
        }
        Ok(())
    }

    fn apply_chainstate_delta(&mut self, delta: ChainstateDelta) -> Result<()> {
        let height = u32::try_from(self.active_chain.len())
            .context("active chain height does not fit u32")?;
        if delta.height != height || delta.parent_hash != self.best_hash() {
            bail!("chainstate delta does not extend the active chain")
        }
        let node = self
            .block_index
            .get(&delta.block_hash)
            .copied()
            .with_context(|| {
                format!("chainstate delta block {} is not indexed", delta.block_hash)
            })?;
        if node.height != delta.height || node.header.prev_blockhash != delta.parent_hash {
            bail!("chainstate delta block index is inconsistent")
        }
        for (outpoint, entry) in &delta.spent {
            if entry.output.value > Amount::MAX_MONEY {
                bail!("chainstate delta contains an output above the money range")
            }
            let removed = self.remove_utxo(outpoint).with_context(|| {
                format!(
                    "chainstate delta tries to spend missing output {}",
                    outpoint
                )
            })?;
            if removed != *entry {
                bail!("chainstate delta spent output metadata does not match")
            }
        }
        for (outpoint, entry) in &delta.created {
            if entry.height != delta.height || entry.output.value > Amount::MAX_MONEY {
                bail!("chainstate delta contains invalid created output metadata")
            }
            self.insert_utxo(*outpoint, entry.clone());
        }
        for (script_hash, entry) in &delta.history {
            if entry.height != delta.height {
                bail!("chainstate delta contains invalid history metadata")
            }
            self.add_history(script_hash, entry.clone());
        }
        for (txid, location) in &delta.transactions {
            if location.block_hash != delta.block_hash || location.height != delta.height {
                bail!("chainstate delta contains invalid transaction metadata")
            }
            self.index_active_transaction(*txid, location.clone());
            if self.tx_index_all_enabled {
                self.tx_index_all.insert(*txid, location.clone());
            }
        }
        if self.txospender_index_enabled {
            for (outpoint, spender) in delta.spent_by {
                self.spent_by.insert(outpoint, spender);
            }
        }
        self.active_chain.push(delta.block_hash);
        self.headers.push(node.header);
        let count = u32::try_from(delta.transactions.len())
            .context("chainstate delta transaction count does not fit u32")?;
        self.active_tx_counts.push(count);
        let total = self
            .active_tx_totals
            .last()
            .copied()
            .unwrap_or_default()
            .saturating_add(u64::from(count));
        self.active_tx_totals.push(total);
        if let Some(stats) = self.coin_stats.as_mut() {
            stats.apply_block_metrics(delta.metrics);
        }
        Ok(())
    }

    fn persist_snapshot(&mut self) -> Result<()> {
        self.sync_utxo_store()?;
        self.utxo_store.compact_if_needed()?;
        self.sync_electrum_history_store()?;
        self.electrum_history_store.compact_if_needed()?;
        let snapshot = self.current_snapshot()?;
        let bytes = serialize_internal(CHAIN_SNAPSHOT_MAGIC, &snapshot)?;
        let path = self.data_dir.join("chainstate.snapshot");
        let temp = self.data_dir.join("chainstate.snapshot.tmp");
        fs::write(&temp, &bytes)?;
        fs::rename(temp, path)?;
        self.persist_snapshot_checksum_bytes(&bytes)?;
        self.persist_tx_counts()?;
        self.chainstate_store.clear()
    }

    fn persist_snapshot_checksum(&self) -> Result<()> {
        let bytes = fs::read(self.data_dir.join("chainstate.snapshot"))?;
        self.persist_snapshot_checksum_bytes(&bytes)
    }

    fn persist_snapshot_checksum_bytes(&self, bytes: &[u8]) -> Result<()> {
        let checksum = snapshot_checksum(bytes);
        let path = self.snapshot_checksum_path();
        let temp = self.data_dir.join("chainstate.snapshot.sha256.tmp");
        fs::write(&temp, checksum)?;
        fs::rename(temp, path)?;
        Ok(())
    }

    fn snapshot_checksum_path(&self) -> PathBuf {
        self.data_dir.join("chainstate.snapshot.sha256")
    }

    fn assumeutxo_base_snapshot_path(&self) -> PathBuf {
        self.data_dir.join("assumeutxo-base.bin")
    }

    fn assumeutxo_checkpoint_path(&self) -> PathBuf {
        self.data_dir.join("assumeutxo-checkpoint.bin")
    }

    fn persist_assumeutxo_base_snapshot(
        &self,
        base_hash: BlockHash,
        utxos: &HashMap<OutPoint, UtxoEntry>,
    ) -> Result<()> {
        let snapshot = AssumeUtxoBaseSnapshot {
            base_hash: base_hash.to_string(),
            utxos: utxos.clone(),
        };
        let bytes = serialize_internal(ASSUMEUTXO_BASE_MAGIC, &snapshot)?;
        let path = self.assumeutxo_base_snapshot_path();
        let temp = path.with_extension("bin.tmp");
        fs::write(&temp, bytes)?;
        fs::rename(temp, path)?;
        Ok(())
    }

    fn remove_assumeutxo_artifacts(&self) -> Result<()> {
        for path in [
            self.assumeutxo_base_snapshot_path(),
            self.assumeutxo_checkpoint_path(),
        ] {
            match fs::remove_file(path) {
                Ok(()) => {}
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Err(error) => return Err(error.into()),
            }
        }
        Ok(())
    }

    fn start_background_validation(&mut self) -> Result<()> {
        let Some(base_hash) = self.snapshot_base else {
            return Ok(());
        };
        if self.snapshot_validated || self.snapshot_validation_error.is_some() {
            return Ok(());
        }
        let base_height = self
            .block_height_by_hash(&base_hash)
            .context("AssumeUTXO base block is not indexed")?;
        if !self.is_active_block(&base_hash) {
            // A snapshot can be loaded while the node is following a
            // shorter divergent chain.  Defer the background replay until
            // the snapshot base becomes the active-chain ancestor after
            // synchronization, as Core does for its second chainstate.
            return Ok(());
        }
        if self
            .active_chain
            .iter()
            .any(|hash| !self.store.contains(hash))
        {
            // Historical bodies may still be downloading on a pruned node.
            // Starting the replay before they arrive would permanently turn
            // a temporary missing-body condition into a validation failure.
            return Ok(());
        }
        let target_tip = self.best_hash();
        let active_chain = self.active_chain.clone();
        let block_index = self.block_index.clone();
        let data_dir = self.data_dir.clone();
        let blocks_dir = self.blocks_dir.clone();
        let blocks_xor = self.blocks_xor;
        let network = self.network;
        let signet_challenge = self.signet_challenge.clone();
        let deployment_parameters = self.deployment_parameters;
        let script_check_workers = self.script_check_workers;
        let script_cache_max_entries = self.script_cache.lock().max_entries;
        if let Some(previous) = self.background_validation.take() {
            previous.cancel.store(true, Ordering::Release);
        }
        let progress = Arc::new(AtomicU32::new(
            load_assumeutxo_checkpoint(&data_dir, base_hash, &active_chain)
                .ok()
                .flatten()
                .map_or(0, |checkpoint| checkpoint.height),
        ));
        let outcome = Arc::new(Mutex::new(None));
        let cancel = Arc::new(AtomicBool::new(false));
        let job = BackgroundValidationJob {
            data_dir,
            blocks_dir,
            blocks_xor,
            network,
            signet_challenge,
            deployment_parameters,
            active_chain,
            block_index,
            base_hash,
            base_height,
            target_tip,
            script_check_workers,
            script_cache_max_entries,
            cancel: cancel.clone(),
        };
        self.background_validation = Some(BackgroundValidation {
            base_hash,
            cancel,
            progress: progress.clone(),
            outcome: outcome.clone(),
        });
        let worker = thread::Builder::new()
            .name("assumeutxo-validation".to_owned())
            .spawn(move || {
                let result = run_background_validation(job, progress);
                *outcome.lock() = Some(result);
            });
        if let Err(error) = worker {
            self.background_validation = None;
            return Err(error.into());
        }
        Ok(())
    }

    fn snapshot_provenance_path(&self) -> PathBuf {
        self.data_dir.join("assumeutxo.bin")
    }

    fn persist_snapshot_provenance(&self) -> Result<()> {
        let Some(base_hash) = self.snapshot_base else {
            return self.remove_snapshot_provenance_file();
        };
        let provenance = SnapshotProvenance {
            base_hash: base_hash.to_string(),
            validated: self.snapshot_validated,
            failure: self.snapshot_validation_error.clone(),
        };
        let bytes = serialize_internal(ASSUMEUTXO_STATE_MAGIC, &provenance)?;
        let temp = self.data_dir.join("assumeutxo.bin.tmp");
        fs::write(&temp, bytes)?;
        fs::rename(temp, self.snapshot_provenance_path())?;
        Ok(())
    }

    fn remove_snapshot_provenance_file(&self) -> Result<()> {
        match fs::remove_file(self.snapshot_provenance_path()) {
            Ok(()) => Ok(()),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
            Err(error) => Err(error.into()),
        }
    }

    fn clear_snapshot_provenance(&mut self) -> Result<()> {
        self.snapshot_base = None;
        self.snapshot_validated = true;
        self.snapshot_validation_error = None;
        if let Some(background) = self.background_validation.take() {
            background.cancel.store(true, Ordering::Release);
        }
        self.remove_assumeutxo_artifacts()?;
        self.remove_snapshot_provenance_file()
    }

    fn current_snapshot(&self) -> Result<ChainSnapshot> {
        let utxos = if self.utxos_materialized {
            self.utxos.clone()
        } else {
            self.load_utxo_map_from_store()?
        };
        let tx_index = self.active_tx_index_for_snapshot()?;
        let tx_index_duplicates = self.active_tx_duplicates_for_snapshot()?;
        Ok(ChainSnapshot {
            tip: self.best_hash().to_string(),
            headers: self.headers.clone(),
            utxos,
            tx_index,
            tx_index_duplicates,
            tx_index_all: if self.tx_index_all_enabled {
                self.tx_index_all.clone()
            } else {
                HashMap::new()
            },
            history: if self.history_materialized {
                self.history.clone()
            } else {
                self.load_history_map_from_store()?
            },
            spent_by: self.txospender_index_enabled.then(|| self.spent_by.clone()),
            prune_height: self.prune_height,
        })
    }

    fn index_active_headers(&mut self, headers: &[bitcoin::block::Header]) -> Result<()> {
        if headers.len() != self.active_chain.len() {
            bail!("active block/header count mismatch");
        }
        for (height, header) in headers.iter().enumerate() {
            let hash = header.block_hash();
            let chain_work = if height == 0 {
                header.work()
            } else {
                self.block_index
                    .get(&header.prev_blockhash)
                    .context("active block parent is not indexed")?
                    .chain_work
                    + header.work()
            };
            self.block_index.insert(
                hash,
                BlockNode {
                    header: *header,
                    height: height as u32,
                    chain_work,
                },
            );
            self.assign_header_sequence_id(hash);
        }
        Ok(())
    }

    fn index_persisted_headers(&mut self, headers: &[bitcoin::block::Header]) -> Result<()> {
        if headers.is_empty() {
            return Ok(());
        }
        let mut pending = headers.to_vec();
        while !pending.is_empty() {
            let before = pending.len();
            let mut remaining = Vec::with_capacity(before);
            for header in pending {
                let hash = header.block_hash();
                if let Some(existing) = self.block_index.get(&hash) {
                    if existing.header != header {
                        bail!("header hash collision for {hash}");
                    }
                    continue;
                }
                if self.block_index.contains_key(&header.prev_blockhash) {
                    if self.has_invalid_ancestor(header.prev_blockhash) {
                        let parent = self
                            .block_index
                            .get(&header.prev_blockhash)
                            .copied()
                            .expect("persisted header parent is indexed");
                        let hash = header.block_hash();
                        self.block_index.insert(
                            hash,
                            BlockNode {
                                header,
                                height: parent.height.saturating_add(1),
                                chain_work: parent.chain_work + header.work(),
                            },
                        );
                        self.assign_header_sequence_id(hash);
                    } else {
                        self.accept_headers_internal(&[header])?;
                    }
                } else {
                    remaining.push(header);
                }
            }
            if remaining.len() == before {
                let header = remaining[0];
                bail!(
                    "persisted header {} has an unknown parent {}",
                    header.block_hash(),
                    header.prev_blockhash
                );
            }
            pending = remaining;
        }
        Ok(())
    }

    fn tx_counts_from_index(&self) -> Option<Vec<u32>> {
        let mut counts = vec![0u32; self.active_chain.len()];
        if self.tx_index_all_enabled {
            for location in self.tx_index_all.values() {
                let height = usize::try_from(location.height).ok()?;
                if self.active_chain.get(height) != Some(&location.block_hash) {
                    continue;
                }
                let count = u32::try_from(location.transaction_index)
                    .ok()?
                    .checked_add(1)?;
                counts[height] = counts[height].max(count);
            }
        } else {
            for location in self.tx_index.values() {
                let height = usize::try_from(location.height).ok()?;
                if height >= self.active_chain.len() {
                    continue;
                }
                let count = u32::try_from(location.transaction_index)
                    .ok()?
                    .checked_add(1)?;
                counts[height] = counts[height].max(count);
            }
        }
        counts.iter().all(|count| *count > 0).then_some(counts)
    }

    fn rebuild_active_tx_counts(&mut self) -> Result<()> {
        let mut counts = Vec::with_capacity(self.active_chain.len());
        for hash in &self.active_chain {
            let block = self
                .store
                .get(hash)?
                .with_context(|| format!("active block {hash} is missing from block store"))?;
            counts.push(
                u32::try_from(block.txdata.len()).context("transaction count does not fit u32")?,
            );
        }
        self.active_tx_counts = counts;
        self.active_tx_totals = cumulative_tx_counts(&self.active_tx_counts);
        Ok(())
    }

    fn known_headers(&self) -> Vec<bitcoin::block::Header> {
        let mut nodes: Vec<(&BlockHash, &BlockNode)> = self.block_index.iter().collect();
        nodes.sort_by(|(left_hash, left), (right_hash, right)| {
            left.height
                .cmp(&right.height)
                .then_with(|| left_hash.to_string().cmp(&right_hash.to_string()))
        });
        nodes.into_iter().map(|(_, node)| node.header).collect()
    }
}

impl Drop for ChainState {
    fn drop(&mut self) {
        if let Some(background) = self.background_validation.as_ref() {
            background.cancel.store(true, Ordering::Release);
        }
    }
}

fn load_assumeutxo_checkpoint(
    data_dir: &Path,
    base_hash: BlockHash,
    active_chain: &[BlockHash],
) -> Result<Option<AssumeUtxoCheckpoint>> {
    let path = data_dir.join("assumeutxo-checkpoint.bin");
    if !path.exists() {
        return Ok(None);
    }
    let bytes = fs::read(&path)
        .with_context(|| format!("reading AssumeUTXO checkpoint {}", path.display()))?;
    let checkpoint: AssumeUtxoCheckpoint =
        deserialize_internal(&bytes, ASSUMEUTXO_CHECKPOINT_MAGIC)
            .with_context(|| format!("decoding AssumeUTXO checkpoint {}", path.display()))?;
    let checkpoint_base = checkpoint
        .base_hash
        .parse::<BlockHash>()
        .context("decoding AssumeUTXO checkpoint base hash")?;
    let checkpoint_block = checkpoint
        .block_hash
        .parse::<BlockHash>()
        .context("decoding AssumeUTXO checkpoint block hash")?;
    if checkpoint_base != base_hash
        || active_chain.get(checkpoint.height as usize) != Some(&checkpoint_block)
    {
        return Ok(None);
    }
    Ok(Some(checkpoint))
}

fn load_assumeutxo_expected_snapshot(
    data_dir: &Path,
    base_hash: BlockHash,
    target_tip: BlockHash,
) -> Result<HashMap<OutPoint, UtxoEntry>> {
    let base_path = data_dir.join("assumeutxo-base.bin");
    if base_path.exists() {
        let bytes = fs::read(&base_path)
            .with_context(|| format!("reading AssumeUTXO base snapshot {}", base_path.display()))?;
        let snapshot: AssumeUtxoBaseSnapshot = deserialize_internal(&bytes, ASSUMEUTXO_BASE_MAGIC)
            .with_context(|| {
                format!("decoding AssumeUTXO base snapshot {}", base_path.display())
            })?;
        let stored_base = snapshot
            .base_hash
            .parse::<BlockHash>()
            .context("decoding AssumeUTXO base snapshot hash")?;
        if stored_base != base_hash {
            bail!("AssumeUTXO base snapshot does not match its provenance")
        }
        return Ok(snapshot.utxos);
    }

    // Compatibility for an interrupted upgrade from the original single
    // chainstate implementation: when the base is the serving tip, the
    // durable chainstate snapshot is itself the expected validation input.
    if target_tip != base_hash {
        bail!("AssumeUTXO base snapshot is missing")
    }
    let path = data_dir.join("chainstate.snapshot");
    let bytes = fs::read(&path)
        .with_context(|| format!("reading chainstate snapshot {}", path.display()))?;
    let snapshot: ChainSnapshot = if bytes.starts_with(CHAIN_SNAPSHOT_MAGIC) {
        deserialize_chain_snapshot(&bytes)?
    } else {
        serde_json::from_slice(&bytes).context("decoding chainstate snapshot")?
    };
    if snapshot.tip.parse::<BlockHash>().ok() != Some(base_hash) {
        bail!("chainstate snapshot does not contain the AssumeUTXO base")
    }
    Ok(snapshot.utxos)
}

fn persist_assumeutxo_checkpoint(data_dir: &Path, checkpoint: &AssumeUtxoCheckpoint) -> Result<()> {
    let bytes = serialize_internal(ASSUMEUTXO_CHECKPOINT_MAGIC, checkpoint)?;
    let path = data_dir.join("assumeutxo-checkpoint.bin");
    let temp = path.with_extension("bin.tmp");
    fs::write(&temp, bytes)?;
    fs::rename(temp, path)?;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn open_background_replay_state(
    network: Network,
    data_dir: &Path,
    blocks_dir: &Path,
    blocks_xor: bool,
    signet_challenge: Option<Vec<u8>>,
    deployment_parameters: validation::DeploymentParameters,
    active_chain: &[BlockHash],
    block_index: &HashMap<BlockHash, BlockNode>,
    script_check_workers: usize,
    script_cache_max_entries: usize,
) -> Result<ChainState> {
    let store = BlockStore::open_read_only_with_xor(blocks_dir, blocks_xor)?;
    // The replay worker validates against its in-memory UTXO map and only
    // reads block bodies.  Opening the live append-only stores here would
    // allow startup recovery or index rebuilding to race with the serving
    // chainstate while it connects new blocks on top of the snapshot.
    let background_data_dir = data_dir.join("assumeutxo-background");
    let filter_store = FilterStore::open(background_data_dir.join("filters"))?;
    let chainstate_store = ChainstateStore::open(background_data_dir.join("chainstate"))?;
    let utxo_store = UtxoStore::open(background_data_dir.join("chainstate/utxos"))?;
    let electrum_history_store =
        ElectrumHistoryStore::open(background_data_dir.join("indexes/electrum-history"))?;
    let coinstats_store = CoinStatsStore::open(background_data_dir.join("indexes/coinstatsindex"))?;
    let headers = active_chain
        .iter()
        .map(|hash| {
            block_index
                .get(hash)
                .map(|node| node.header)
                .context("background validator is missing an active header")
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(ChainState {
        network,
        data_dir: data_dir.to_owned(),
        blocks_dir: blocks_dir.to_owned(),
        blocks_xor,
        minimum_chain_work_override: None,
        assume_valid_block: None,
        max_tip_age_secs: MAX_TIP_AGE_SECS,
        script_check_workers,
        script_checks_enabled: script_check_workers > 0,
        signet_challenge,
        deployment_parameters,
        store,
        electrum_store: None,
        filter_store,
        chainstate_store,
        utxo_store,
        missing_utxo_cache: Mutex::new(MissingUtxoCache::default()),
        electrum_history_store,
        blockfilter_index_enabled: false,
        tx_index_all_enabled: false,
        coinstats_store,
        txospender_index_enabled: false,
        coinstats_index_enabled: false,
        coin_stats: None,
        active_chain: active_chain.to_vec(),
        segwit_validated_blocks: HashSet::new(),
        headers,
        header_merkle_cache: Mutex::new(None),
        active_tx_counts: Vec::new(),
        active_tx_totals: Vec::new(),
        initial_block_download: true,
        max_tip_age_configured: false,
        snapshot_base: None,
        snapshot_validated: true,
        snapshot_validation_error: None,
        background_validation: None,
        block_index: block_index.clone(),
        block_sequence_ids: HashMap::new(),
        next_block_sequence_id: 1,
        unlinked_body_order: HashMap::new(),
        next_unlinked_body_order: 1,
        header_sequence_ids: HashMap::new(),
        next_header_sequence_id: 1,
        orphans: HashMap::new(),
        invalid_blocks: HashSet::new(),
        prune_height: None,
        prune_locks: HashMap::new(),
        prune_protected_blocks: HashMap::new(),
        prune_mode: false,
        prune_target_size: None,
        prune_after_height: MIN_BLOCKS_TO_KEEP,
        fast_prune: false,
        utxos: HashMap::new(),
        utxos_materialized: true,
        side_chain_utxos: None,
        tx_index: HashMap::new(),
        tx_index_duplicates: HashMap::new(),
        tx_index_all: HashMap::new(),
        history: HashMap::new(),
        history_materialized: true,
        spent_by: HashMap::new(),
        precious_blocks: HashMap::new(),
        precious_sequence: -1,
        precious_last_chainwork: None,
        basic_filter_cache: HashMap::new(),
        block_undo_cache: HashMap::new(),
        script_cache: Mutex::new(ScriptValidationCache::with_max_entries(
            script_cache_max_entries,
        )),
    })
}

fn run_background_validation(
    job: BackgroundValidationJob,
    progress: Arc<AtomicU32>,
) -> BackgroundValidationOutcome {
    let BackgroundValidationJob {
        data_dir,
        blocks_dir,
        blocks_xor,
        network,
        signet_challenge,
        deployment_parameters,
        active_chain,
        block_index,
        base_hash,
        base_height,
        target_tip,
        script_check_workers,
        script_cache_max_entries,
        cancel,
    } = job;
    let result = (|| -> Result<(HashMap<OutPoint, UtxoEntry>, bool)> {
        let target_height = active_chain
            .iter()
            .position(|hash| *hash == target_tip)
            .context("background validator target tip is not active")?
            as u32;
        if active_chain.get(base_height as usize) != Some(&base_hash) {
            bail!("background validator base block is not active")
        }
        let expected = load_assumeutxo_expected_snapshot(&data_dir, base_hash, target_tip)?;
        let checkpoint = load_assumeutxo_checkpoint(&data_dir, base_hash, &active_chain)?;
        let (mut utxos, mut start_height, mut base_matches) = if let Some(checkpoint) = checkpoint {
            let height = checkpoint.height;
            (checkpoint.utxos, height, checkpoint.base_matches)
        } else {
            (HashMap::new(), 0, None)
        };
        if start_height > target_height {
            start_height = 0;
            utxos.clear();
            base_matches = None;
        }
        if start_height > base_height && base_matches.is_none() {
            bail!("AssumeUTXO checkpoint crossed its base without a comparison")
        }
        progress.store(start_height, Ordering::Release);

        let mut state = open_background_replay_state(
            network,
            &data_dir,
            &blocks_dir,
            blocks_xor,
            signet_challenge,
            deployment_parameters,
            &active_chain,
            &block_index,
            script_check_workers,
            script_cache_max_entries,
        )?;
        if base_height == 0 && start_height == 0 {
            base_matches = Some(utxos == expected);
        }
        for height in start_height.saturating_add(1)..=target_height {
            if cancel.load(Ordering::Acquire) {
                bail!("background AssumeUTXO validation was cancelled")
            }
            let block_hash = active_chain[height as usize];
            let block = state
                .store
                .get(&block_hash)?
                .with_context(|| format!("background validator is missing block {block_hash}"))?;
            let node = state
                .block_index
                .get(&block_hash)
                .copied()
                .context("background validator block index entry is missing")?;
            let parent_hash = block.header.prev_blockhash;
            let parent = state
                .block_index
                .get(&parent_hash)
                .copied()
                .context("background validator parent index entry is missing")?;
            validation::validate_bip94_timewarp_with_params(
                &state.deployment_parameters,
                node.height,
                block.header.time,
                parent.header.time,
            )?;
            state.validate_header_context(
                &block.header,
                parent_hash,
                state.expected_target_for_parent(parent_hash, block.header.time),
                state.median_time_past_for_parent(parent_hash),
                true,
            )?;
            state.validate_block_structure(
                &block,
                state.network,
                node.height,
                Amount::MAX_MONEY.to_sat(),
            )?;
            let median_time_past = state.median_time_past_for_parent(parent_hash);
            let application = state.validate_block_transactions_with_options(
                &block,
                node.height,
                &utxos,
                median_time_past,
                false,
            )?;
            apply_block_to_utxos(
                &mut utxos,
                &block,
                node.height,
                median_time_past,
                application.spent_entries,
            );
            if height == base_height {
                base_matches = Some(utxos == expected);
            }
            progress.store(height, Ordering::Release);
            if height % ASSUMEUTXO_CHECKPOINT_INTERVAL == 0
                || height == base_height
                || height == target_height
            {
                if cancel.load(Ordering::Acquire) {
                    bail!("background AssumeUTXO validation was cancelled")
                }
                persist_assumeutxo_checkpoint(
                    &data_dir,
                    &AssumeUtxoCheckpoint {
                        base_hash: base_hash.to_string(),
                        height,
                        block_hash: block_hash.to_string(),
                        base_matches,
                        utxos: utxos.clone(),
                    },
                )?;
            }
        }
        let base_matches =
            base_matches.context("background validator did not reach the snapshot base")?;
        Ok((utxos, base_matches))
    })();

    match result {
        Ok((utxos, base_matches)) => BackgroundValidationOutcome::Complete {
            target_tip,
            utxos,
            base_matches,
        },
        Err(error) => BackgroundValidationOutcome::Failed {
            target_tip,
            error: error.to_string(),
            utxos: None,
        },
    }
}

fn calculate_utxo_statistics(
    utxos: &HashMap<OutPoint, UtxoEntry>,
    include_serialized_hash: bool,
    include_muhash: bool,
) -> UtxoSetStats {
    calculate_utxo_statistics_iter(
        utxos.iter(),
        utxos.len(),
        include_serialized_hash,
        include_muhash,
    )
}

fn calculate_utxo_statistics_from_entries(
    entries: &[(OutPoint, UtxoEntry)],
    include_serialized_hash: bool,
    include_muhash: bool,
) -> UtxoSetStats {
    calculate_utxo_statistics_iter(
        entries.iter().map(|(outpoint, entry)| (outpoint, entry)),
        entries.len(),
        include_serialized_hash,
        include_muhash,
    )
}

fn calculate_utxo_statistics_iter<'a, I>(
    entries: I,
    output_count: usize,
    include_serialized_hash: bool,
    include_muhash: bool,
) -> UtxoSetStats
where
    I: IntoIterator<Item = (&'a OutPoint, &'a UtxoEntry)>,
{
    let mut transactions = HashSet::new();
    let mut total_amount_sat = 0u64;
    let mut bogo_size = 0u64;

    let mut accumulate_stats = |outpoint: &OutPoint, entry: &UtxoEntry| {
        transactions.insert(outpoint.txid);
        total_amount_sat = total_amount_sat.saturating_add(entry.output.value.to_sat());
        bogo_size = bogo_size.saturating_add(
            32u64
                .saturating_add(4)
                .saturating_add(4)
                .saturating_add(8)
                .saturating_add(2)
                .saturating_add(entry.output.script_pubkey.len() as u64),
        );
    };

    let entries = entries.into_iter().collect::<Vec<_>>();
    let (serialized_hash, muhash) = if include_serialized_hash {
        let mut sorted_entries = entries;
        sorted_entries.sort_by_key(|(outpoint, _)| (outpoint.txid.to_byte_array(), outpoint.vout));
        let mut serialized_engine = bitcoin::hashes::sha256d::Hash::engine();
        let mut muhash = include_muhash.then(MuHash3072::default);
        for (outpoint, entry) in sorted_entries {
            accumulate_stats(outpoint, entry);
            let coin_bytes = serialize_utxo_coin(outpoint, entry);
            use bitcoin::hashes::HashEngine;
            serialized_engine.input(&coin_bytes);
            if let Some(accumulator) = muhash.as_mut() {
                accumulator.insert(&coin_bytes);
            }
        }
        (
            Some(bitcoin::hashes::sha256d::Hash::from_engine(serialized_engine).to_string()),
            muhash,
        )
    } else {
        let mut muhash = include_muhash.then(MuHash3072::default);
        for (outpoint, entry) in entries {
            accumulate_stats(outpoint, entry);
            if let Some(accumulator) = muhash.as_mut() {
                let coin_bytes = serialize_utxo_coin(outpoint, entry);
                accumulator.insert(&coin_bytes);
            }
        }
        (None, muhash)
    };

    UtxoSetStats {
        transactions: transactions.len(),
        outputs: output_count,
        total_amount_sat,
        bogo_size,
        serialized_hash,
        muhash: muhash.map(|accumulator| accumulator.finalize()),
        total_prevout_spent_sat: 0,
        total_new_outputs_ex_coinbase_sat: 0,
        total_coinbase_sat: 0,
        total_unspendable_genesis_sat: 0,
        total_unspendable_bip30_sat: 0,
        total_unspendable_scripts_sat: 0,
        total_unspendable_unclaimed_rewards_sat: 0,
    }
}

fn utxo_bogo_size(entry: &UtxoEntry) -> u64 {
    32u64
        .saturating_add(4)
        .saturating_add(4)
        .saturating_add(8)
        .saturating_add(2)
        .saturating_add(entry.output.script_pubkey.len() as u64)
}

fn snapshot_checksum(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}

struct CoreUtxoSnapshot {
    base_hash: BlockHash,
    coins_count: u64,
    utxos: HashMap<OutPoint, UtxoEntry>,
}

fn write_core_utxo_snapshot(
    path: &Path,
    network: Network,
    signet_challenge: Option<&[u8]>,
    base_hash: BlockHash,
    utxos: &HashMap<OutPoint, UtxoEntry>,
) -> Result<()> {
    let temporary = PathBuf::from(format!("{}.incomplete", path.display()));
    let mut file = fs::File::create(&temporary)
        .with_context(|| format!("writing UTXO snapshot {}", temporary.display()))?;
    file.write_all(&CORE_UTXO_SNAPSHOT_MAGIC)?;
    file.write_all(&CORE_UTXO_SNAPSHOT_VERSION.to_le_bytes())?;
    file.write_all(&crate::wire::network_magic_with_signet_challenge(
        network,
        signet_challenge,
    ))?;
    file.write_all(&base_hash.to_byte_array())?;
    file.write_all(&(utxos.len() as u64).to_le_bytes())?;

    let mut entries: Vec<(&OutPoint, &UtxoEntry)> = utxos.iter().collect();
    entries.sort_unstable_by(|(left, _), (right, _)| {
        left.txid
            .to_byte_array()
            .cmp(&right.txid.to_byte_array())
            .then_with(|| left.vout.cmp(&right.vout))
    });
    let mut offset = 0usize;
    while offset < entries.len() {
        let txid = entries[offset].0.txid;
        let end = offset
            + entries[offset..]
                .iter()
                .take_while(|(outpoint, _)| outpoint.txid == txid)
                .count();
        file.write_all(&txid.to_byte_array())?;
        write_snapshot_compact_size(&mut file, (end - offset) as u64)?;
        for (outpoint, entry) in &entries[offset..end] {
            write_snapshot_compact_size(&mut file, u64::from(outpoint.vout))?;
            write_core_coin(&mut file, entry)?;
        }
        offset = end;
    }
    file.flush()?;
    file.sync_all()?;
    drop(file);
    fs::rename(&temporary, path)
        .with_context(|| format!("installing UTXO snapshot {}", path.display()))?;
    Ok(())
}

fn write_snapshot_compact_size(writer: &mut impl Write, value: u64) -> Result<()> {
    writer.write_all(&serialize(&VarInt(value)))?;
    Ok(())
}

fn write_snapshot_varint(writer: &mut impl Write, mut value: u64) -> Result<()> {
    let mut digits = Vec::with_capacity(10);
    loop {
        let continuation = if digits.is_empty() { 0 } else { 0x80 };
        digits.push((value as u8 & 0x7f) | continuation);
        if value <= 0x7f {
            break;
        }
        value = (value >> 7) - 1;
    }
    for digit in digits.into_iter().rev() {
        writer.write_all(&[digit])?;
    }
    Ok(())
}

fn write_core_coin(writer: &mut impl Write, entry: &UtxoEntry) -> Result<()> {
    let code = u64::from(entry.height)
        .checked_mul(2)
        .and_then(|code| code.checked_add(u64::from(entry.coinbase)))
        .context("UTXO snapshot height is too large")?;
    write_snapshot_varint(writer, code)?;
    write_snapshot_varint(
        writer,
        compress_snapshot_amount(entry.output.value.to_sat()),
    )?;
    write_compressed_snapshot_script(writer, &entry.output.script_pubkey)
}

fn write_compressed_snapshot_script(writer: &mut impl Write, script: &Script) -> Result<()> {
    let bytes = script.as_bytes();
    if bytes.len() == 25 && bytes[0..3] == [0x76, 0xa9, 0x14] && bytes[23..] == [0x88, 0xac] {
        writer.write_all(&[0])?;
        writer.write_all(&bytes[3..23])?;
    } else if bytes.len() == 23 && bytes[0..2] == [0xa9, 0x14] && bytes[22] == 0x87 {
        writer.write_all(&[1])?;
        writer.write_all(&bytes[2..22])?;
    } else if bytes.len() == 35
        && bytes[0] == 33
        && matches!(bytes[1], 0x02 | 0x03)
        && bytes[34] == 0xac
    {
        writer.write_all(&bytes[1..34])?;
    } else if bytes.len() == 67
        && bytes[0] == 65
        && bytes[1] == 0x04
        && bytes[66] == 0xac
        && bitcoin::secp256k1::PublicKey::from_slice(&bytes[1..66])
            .is_ok_and(|key| key.serialize_uncompressed().as_slice() == &bytes[1..66])
    {
        let key = &bytes[1..66];
        let prefix = 0x04 | (key[64] & 1);
        writer.write_all(&[prefix])?;
        writer.write_all(&key[1..33])?;
    } else {
        let size = u64::try_from(bytes.len())
            .ok()
            .and_then(|size| size.checked_add(6))
            .context("script is too large for UTXO snapshot serialization")?;
        write_snapshot_varint(writer, size)?;
        writer.write_all(bytes)?;
    }
    Ok(())
}

fn read_core_utxo_snapshot(
    bytes: &[u8],
    network: Network,
    signet_challenge: Option<&[u8]>,
) -> Result<CoreUtxoSnapshot> {
    let mut cursor = Cursor::new(bytes);
    let magic = read_snapshot_array::<5>(&mut cursor).map_err(|_| {
        anyhow!(
            "Unable to parse metadata: Invalid UTXO set snapshot magic bytes. Please check if this is indeed a snapshot file or if you are using an outdated snapshot format."
        )
    })?;
    if magic != CORE_UTXO_SNAPSHOT_MAGIC {
        bail!(
            "Unable to parse metadata: Invalid UTXO set snapshot magic bytes. Please check if this is indeed a snapshot file or if you are using an outdated snapshot format."
        )
    }
    let version = read_snapshot_u16(&mut cursor).map_err(|_| {
        anyhow!(
            "Unable to parse metadata: Invalid UTXO set snapshot metadata. Please check if this is indeed a snapshot file or if you are using an outdated snapshot format."
        )
    })?;
    if version != CORE_UTXO_SNAPSHOT_VERSION {
        bail!(
            "Unable to parse metadata: Version of snapshot {version} does not match any of the supported versions."
        )
    }
    let network_magic = read_snapshot_array::<4>(&mut cursor).map_err(|_| {
        anyhow!(
            "Unable to parse metadata: Invalid UTXO set snapshot metadata. Please check if this is indeed a snapshot file or if you are using an outdated snapshot format."
        )
    })?;
    if network_magic != crate::wire::network_magic_with_signet_challenge(network, signet_challenge)
    {
        let snapshot_network = match network_magic {
            [0xf9, 0xbe, 0xb4, 0xd9] => Some("main"),
            [0x0b, 0x11, 0x09, 0x07] => Some("test"),
            [0x0a, 0x03, 0xcf, 0x40] => Some("signet"),
            [0xfa, 0xbf, 0xb5, 0xda] => Some("regtest"),
            [0x1c, 0x16, 0x3f, 0x28] => Some("testnet4"),
            _ => None,
        };
        if let Some(snapshot_network) = snapshot_network {
            let node_network = match network {
                Network::Bitcoin => "main",
                Network::Testnet => "test",
                Network::Signet => "signet",
                Network::Regtest => "regtest",
                Network::Testnet4 => "testnet4",
            };
            bail!(
                "Unable to parse metadata: The network of the snapshot ({snapshot_network}) does not match the network of this node ({node_network})."
            )
        }
        bail!(
            "Unable to parse metadata: This snapshot has been created for an unrecognized network. This could be a custom signet, a new testnet or possibly caused by data corruption."
        )
    }
    let base_hash = BlockHash::from_byte_array(read_snapshot_array::<32>(&mut cursor).map_err(
        |_| anyhow!("Population failed: Bad snapshot format or truncated snapshot after deserializing 0 coins."),
    )?);
    let coins_count = read_snapshot_u64(&mut cursor).map_err(|_| {
        anyhow!(
            "Population failed: Bad snapshot format or truncated snapshot after deserializing 0 coins."
        )
    })?;
    if coins_count > bytes.len() as u64 {
        bail!(
            "Population failed: Bad snapshot format or truncated snapshot after deserializing 0 coins."
        )
    }
    let capacity = usize::try_from(coins_count.min(1_000_000)).unwrap_or(0);
    let mut utxos = HashMap::with_capacity(capacity);
    let mut coins_left = coins_count;
    let mut coins_deserialized = 0u64;
    while coins_left != 0 {
        let txid = Txid::from_byte_array(read_snapshot_array::<32>(&mut cursor).map_err(
            |_| anyhow!(
                "Population failed: Bad snapshot format or truncated snapshot after deserializing {coins_deserialized} coins."
            ),
        )?);
        let group_count = read_snapshot_compact_size(&mut cursor).map_err(|_| {
            anyhow!(
                "Population failed: Bad snapshot format or truncated snapshot after deserializing {coins_deserialized} coins."
            )
        })?;
        if group_count == 0 || group_count > coins_left {
            bail!(
                "Population failed: Mismatch in coins count in snapshot metadata and actual snapshot data"
            )
        }
        for _ in 0..group_count {
            let vout = read_snapshot_compact_size(&mut cursor).map_err(|_| {
                anyhow!(
                    "Population failed: Bad snapshot format or truncated snapshot after deserializing {coins_deserialized} coins."
                )
            })?;
            let vout = u32::try_from(vout).map_err(|_| {
                anyhow!(
                    "Population failed: Bad snapshot format or truncated snapshot after deserializing {coins_deserialized} coins."
                )
            })?;
            if vout == u32::MAX {
                bail!(
                    "Population failed: Bad snapshot format or truncated snapshot after deserializing {coins_deserialized} coins."
                )
            }
            let entry = match read_core_coin(&mut cursor) {
                Ok(entry) => entry,
                Err(error)
                    if coins_deserialized == 0
                        && error.to_string() == "UTXO snapshot coin value is out of range" =>
                {
                    bail!(
                        "Population failed: Bad snapshot data after deserializing {coins_deserialized} coins - bad tx out value"
                    )
                }
                Err(_) => {
                    bail!(
                        "Population failed: Bad snapshot format or truncated snapshot after deserializing {coins_deserialized} coins."
                    )
                }
            };
            if utxos.insert(OutPoint::new(txid, vout), entry).is_some() {
                bail!(
                    "Population failed: Bad snapshot format or truncated snapshot after deserializing {coins_deserialized} coins."
                )
            }
            coins_left -= 1;
            coins_deserialized += 1;
        }
    }
    if cursor.position() as usize != bytes.len() {
        bail!(
            "Population failed: Bad snapshot - coins left over after deserializing {coins_deserialized} coins."
        )
    }
    Ok(CoreUtxoSnapshot {
        base_hash,
        coins_count,
        utxos,
    })
}

fn read_core_coin(cursor: &mut Cursor<&[u8]>) -> Result<UtxoEntry> {
    let code = u32::try_from(read_snapshot_varint(cursor)?)
        .context("UTXO snapshot coin metadata is too large")?;
    let height = code >> 1;
    let coinbase = code & 1 != 0;
    let value = decompress_snapshot_amount(read_snapshot_varint(cursor)?)?;
    if value > Amount::MAX_MONEY.to_sat() {
        bail!("UTXO snapshot coin value is out of range")
    }
    let script_pubkey = read_compressed_snapshot_script(cursor)?;
    Ok(UtxoEntry {
        output: TxOut {
            value: Amount::from_sat(value),
            script_pubkey,
        },
        height,
        median_time_past: 0,
        coinbase,
    })
}

fn read_compressed_snapshot_script(cursor: &mut Cursor<&[u8]>) -> Result<ScriptBuf> {
    let size = read_snapshot_varint(cursor)?;
    if size < 6 {
        let length = match size {
            0 | 1 => 20,
            2..=5 => 32,
            _ => unreachable!(),
        };
        let data = read_snapshot_vec(cursor, length)?;
        let mut script = Vec::with_capacity(length + 5);
        match size {
            0 => {
                script.extend_from_slice(&[0x76, 0xa9, 0x14]);
                script.extend_from_slice(&data);
                script.extend_from_slice(&[0x88, 0xac]);
            }
            1 => {
                script.extend_from_slice(&[0xa9, 0x14]);
                script.extend_from_slice(&data);
                script.push(0x87);
            }
            2 | 3 => {
                script.push(33);
                script.push(size as u8);
                script.extend_from_slice(&data);
                script.push(0xac);
            }
            4 | 5 => {
                let mut compressed = Vec::with_capacity(33);
                compressed.push((size - 2) as u8);
                compressed.extend_from_slice(&data);
                let key = bitcoin::secp256k1::PublicKey::from_slice(&compressed)
                    .context("invalid compressed public key in UTXO snapshot")?;
                script.push(65);
                script.extend_from_slice(&key.serialize_uncompressed());
                script.push(0xac);
            }
            _ => unreachable!(),
        }
        return Ok(ScriptBuf::from_bytes(script));
    }
    let length = usize::try_from(size - 6).context("UTXO snapshot script is too large")?;
    if length > MAX_UNSPENDABLE_SCRIPT_SIZE {
        bail!("UTXO snapshot script exceeds the maximum script size")
    }
    Ok(ScriptBuf::from_bytes(read_snapshot_vec(cursor, length)?))
}

fn compress_snapshot_amount(mut value: u64) -> u64 {
    if value == 0 {
        return 0;
    }
    let mut exponent = 0u64;
    while value % 10 == 0 && exponent < 9 {
        value /= 10;
        exponent += 1;
    }
    if exponent < 9 {
        let digit = value % 10;
        value /= 10;
        1 + (value * 9 + digit - 1) * 10 + exponent
    } else {
        1 + (value - 1) * 10 + 9
    }
}

fn decompress_snapshot_amount(mut value: u64) -> Result<u64> {
    if value == 0 {
        return Ok(0);
    }
    value -= 1;
    let exponent = value % 10;
    value /= 10;
    let mut number = if exponent < 9 {
        let digit = value % 9 + 1;
        value /= 9;
        value
            .checked_mul(10)
            .and_then(|value| value.checked_add(digit))
            .context("UTXO snapshot amount overflows")?
    } else {
        value
            .checked_add(1)
            .context("UTXO snapshot amount overflows")?
    };
    for _ in 0..exponent {
        number = number
            .checked_mul(10)
            .context("UTXO snapshot amount overflows")?;
    }
    Ok(number)
}

fn read_snapshot_array<const N: usize>(cursor: &mut Cursor<&[u8]>) -> Result<[u8; N]> {
    let mut bytes = [0; N];
    cursor.read_exact(&mut bytes)?;
    Ok(bytes)
}

fn read_snapshot_vec(cursor: &mut Cursor<&[u8]>, length: usize) -> Result<Vec<u8>> {
    let mut bytes = vec![0; length];
    cursor.read_exact(&mut bytes)?;
    Ok(bytes)
}

fn read_snapshot_u16(cursor: &mut Cursor<&[u8]>) -> Result<u16> {
    Ok(u16::from_le_bytes(read_snapshot_array(cursor)?))
}

fn read_snapshot_u64(cursor: &mut Cursor<&[u8]>) -> Result<u64> {
    Ok(u64::from_le_bytes(read_snapshot_array(cursor)?))
}

fn read_snapshot_compact_size(cursor: &mut Cursor<&[u8]>) -> Result<u64> {
    Ok(VarInt::consensus_decode(cursor)
        .map_err(|error| anyhow::anyhow!("invalid UTXO snapshot compact size: {error}"))?
        .0)
}

fn read_snapshot_varint(cursor: &mut Cursor<&[u8]>) -> Result<u64> {
    let mut value = 0u64;
    loop {
        let digit = read_snapshot_array::<1>(cursor)?[0];
        if value > (u64::MAX >> 7) {
            bail!("UTXO snapshot VARINT is too large")
        }
        value = (value << 7) | u64::from(digit & 0x7f);
        if digit & 0x80 != 0 {
            if value == u64::MAX {
                bail!("UTXO snapshot VARINT is too large")
            }
            value += 1;
        } else {
            return Ok(value);
        }
    }
}

fn is_unspendable_script(script: &Script) -> bool {
    script.is_op_return() || script.len() > MAX_UNSPENDABLE_SCRIPT_SIZE
}

fn serialize_utxo_coin(outpoint: &OutPoint, entry: &UtxoEntry) -> Vec<u8> {
    let mut coin_bytes = Vec::new();
    coin_bytes.extend_from_slice(&serialize(outpoint));
    coin_bytes.extend_from_slice(
        &(entry.height.saturating_mul(2) | u32::from(entry.coinbase)).to_le_bytes(),
    );
    coin_bytes.extend_from_slice(&serialize(&entry.output));
    coin_bytes
}

fn apply_block_to_coin_stats(
    network: Network,
    utxos: &mut HashMap<OutPoint, UtxoEntry>,
    stats: &mut CoinStatsState,
    block: &Block,
    height: u32,
) {
    if height == 0 {
        stats.apply_genesis(network);
        return;
    }
    let mut metrics = CoinStatsBlockMetrics {
        subsidy_sat: validation::block_subsidy_for_network(network, height),
        ..CoinStatsBlockMetrics::default()
    };
    for (transaction_index, transaction) in block.txdata.iter().enumerate() {
        if transaction_index == 0 && is_bip30_unspendable(network, height, block.block_hash()) {
            metrics.unspendable_bip30_sat = metrics
                .unspendable_bip30_sat
                .saturating_add(metrics.subsidy_sat);
            continue;
        }
        for input in &transaction.input {
            if let Some(entry) = utxos.remove(&input.previous_output) {
                stats.remove(&input.previous_output, &entry);
                metrics.prevout_spent_sat = metrics
                    .prevout_spent_sat
                    .saturating_add(entry.output.value.to_sat());
            }
        }
        let txid = transaction.compute_txid();
        for (output_index, output) in transaction.output.iter().enumerate() {
            if is_unspendable_script(&output.script_pubkey) {
                metrics.unspendable_scripts_sat = metrics
                    .unspendable_scripts_sat
                    .saturating_add(output.value.to_sat());
                continue;
            }
            let outpoint = OutPoint::new(txid, output_index as u32);
            let entry = UtxoEntry {
                output: output.clone(),
                height,
                median_time_past: block.header.time,
                coinbase: transaction_index == 0,
            };
            if let Some(previous) = utxos.insert(outpoint, entry.clone()) {
                stats.remove(&outpoint, &previous);
            }
            stats.add(&outpoint, &entry);
            if transaction_index == 0 {
                metrics.coinbase_sat = metrics.coinbase_sat.saturating_add(output.value.to_sat());
            } else {
                metrics.new_outputs_ex_coinbase_sat = metrics
                    .new_outputs_ex_coinbase_sat
                    .saturating_add(output.value.to_sat());
            }
        }
    }
    stats.apply_block_metrics(metrics);
}

fn apply_block_to_utxos(
    utxos: &mut HashMap<OutPoint, UtxoEntry>,
    block: &Block,
    height: u32,
    median_time_past: u32,
    spent_entries: Vec<(OutPoint, UtxoEntry)>,
) {
    let spent_outpoints: HashSet<OutPoint> = spent_entries
        .iter()
        .map(|(outpoint, _)| *outpoint)
        .collect();
    for (outpoint, _) in spent_entries {
        utxos.remove(&outpoint);
    }
    for (transaction_index, transaction) in block.txdata.iter().enumerate() {
        let txid = transaction.compute_txid();
        for (output_index, output) in transaction.output.iter().enumerate() {
            let outpoint = OutPoint::new(txid, output_index as u32);
            if !spent_outpoints.contains(&outpoint) && !is_unspendable_script(&output.script_pubkey)
            {
                utxos.insert(
                    outpoint,
                    UtxoEntry {
                        output: output.clone(),
                        height,
                        median_time_past,
                        coinbase: transaction_index == 0,
                    },
                );
            }
        }
    }
}

pub(crate) fn is_bip30_repeat(network: Network, height: u32, hash: BlockHash) -> bool {
    if network != Network::Bitcoin {
        return false;
    }
    let hash = hash.to_string();
    (height == 91_842 && hash == "00000000000a4d0a398161ffc163c503763b1f4360639393e0e4c8e300e0caec")
        || (height == 91_880
            && hash == "00000000000743f190a18c5577a3c2d2a1f610ae9601ac046a38084ccb7cd721")
}

fn is_bip30_unspendable(network: Network, height: u32, hash: BlockHash) -> bool {
    if network != Network::Bitcoin {
        return false;
    }
    let hash = hash.to_string();
    (height == 91_722 && hash == "00000000000271a2dc26e7667f8419f2e15416dc6955e5a6c6cdf3f2574dd08e")
        || (height == 91_812
            && hash == "00000000000af0aed4792b1acee3d966af36cf5def14935db8de83d6f9306f2f")
}

fn bip34_activation_hash(network: Network) -> Option<&'static str> {
    match network {
        Network::Bitcoin => {
            Some("000000000000024b89b42a942fe0d9fea3bb44ab7bd1b19115dd6a759c0808b8")
        }
        Network::Testnet => {
            Some("0000000023b3a96d3484e5abb3755c413e7d41500f8e2a5c3f0dd01299cd8ef8")
        }
        Network::Testnet4 | Network::Signet | Network::Regtest => None,
    }
}

pub fn electrum_script_hash(script: &Script) -> String {
    let mut digest = Sha256::digest(script.as_bytes()).to_vec();
    digest.reverse();
    hex::encode(digest)
}

pub fn transaction_hex(transaction: &Transaction) -> String {
    hex::encode(serialize(transaction))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mempool::Mempool;
    use bitcoin::Sequence;
    use bitcoin::absolute::LockTime;
    use bitcoin::block::{Header, Version as BlockVersion};
    use bitcoin::blockdata::constants::genesis_block;
    use bitcoin::blockdata::script::Builder;
    use bitcoin::blockdata::transaction::{OutPoint, Transaction, TxIn, TxOut, Version};
    use bitcoin::blockdata::witness::Witness;

    #[test]
    fn opens_network_genesis() {
        let directory = tempfile::tempdir().unwrap();
        let state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(state.height(), 0);
        assert_eq!(
            state.best_hash(),
            genesis_block(Network::Regtest).block_hash()
        );
        assert_eq!(state.utxo_stats(), (0, 0, 0));
    }

    #[test]
    fn header_merkle_cache_matches_reference_for_odd_and_even_lengths() {
        for len in 1..=64usize {
            let hashes = (0..len)
                .map(|index| {
                    let mut bytes = [0u8; 32];
                    bytes[..8].copy_from_slice(&(index as u64).to_le_bytes());
                    bytes[8..16].copy_from_slice(&(len as u64).to_le_bytes());
                    BlockHash::from_byte_array(bytes)
                })
                .collect::<Vec<_>>();
            let cache = HeaderMerkleCache::from_hashes(
                hashes.last().copied().unwrap(),
                (len - 1) as u32,
                hashes.clone(),
            )
            .unwrap();

            for height in 0..len as u32 {
                assert_eq!(
                    cache.proof(height).unwrap(),
                    header_merkle_proof_from_hashes(&hashes, height).unwrap(),
                    "length {len}, height {height}"
                );
            }

            let mut incremental =
                HeaderMerkleCache::from_hashes(hashes[0], 0, vec![hashes[0]]).unwrap();
            for checkpoint in 1..len {
                incremental.append_hash(hashes[checkpoint]);
                for height in 0..=checkpoint as u32 {
                    assert_eq!(
                        incremental.proof(height).unwrap(),
                        header_merkle_proof_from_hashes(&hashes[..=checkpoint], height).unwrap(),
                        "incremental length {checkpoint}, height {height}"
                    );
                }
            }
        }
    }

    #[test]
    fn chain_header_merkle_proofs_follow_active_headers_and_tip_changes() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        for height in 1..=6 {
            state.connect_block(mine_block(&state, height)).unwrap();
        }

        for checkpoint in 0..=state.height() {
            let hashes = state
                .active_headers()
                .iter()
                .take(checkpoint as usize + 1)
                .map(Header::block_hash)
                .collect::<Vec<_>>();
            for height in 0..=checkpoint {
                assert_eq!(
                    state.header_merkle_proof(height, checkpoint).unwrap(),
                    header_merkle_proof_from_hashes(&hashes, height).unwrap(),
                    "checkpoint {checkpoint}, height {height}"
                );
            }
        }

        state.connect_block(mine_block(&state, 7)).unwrap();
        let _ = state.header_merkle_proof(0, 6).unwrap();
        assert_eq!(
            state
                .header_merkle_cache
                .lock()
                .as_ref()
                .map(|cache| cache.checkpoint_hash),
            state.header(6).map(Header::block_hash)
        );
    }

    #[test]
    fn legacy_chain_snapshot_defaults_duplicate_index() {
        let legacy = LegacyChainSnapshot {
            tip: String::new(),
            headers: Vec::new(),
            utxos: HashMap::new(),
            tx_index: HashMap::new(),
            tx_index_all: HashMap::new(),
            history: HashMap::new(),
            spent_by: None,
            prune_height: None,
        };
        let bytes = serialize_internal(CHAIN_SNAPSHOT_MAGIC, &legacy).unwrap();
        let snapshot = deserialize_chain_snapshot(&bytes).unwrap();
        assert!(snapshot.tx_index_duplicates.is_empty());
    }

    #[test]
    fn checks_fresh_chain_consistency() {
        let directory = tempfile::tempdir().unwrap();
        let state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        state.check_consistency().unwrap();
    }

    #[test]
    fn core_par_resolves_script_worker_counts() {
        let cores = thread::available_parallelism()
            .map(|cores| cores.get())
            .unwrap_or(1);
        let max_workers = MAX_SCRIPT_CHECK_THREADS;
        assert_eq!(
            script_check_workers(0),
            cores.saturating_sub(1).min(max_workers)
        );
        assert_eq!(
            script_check_workers(-1),
            cores.saturating_sub(2).min(max_workers)
        );
        assert_eq!(script_check_workers(1), 0);
        assert_eq!(script_check_workers(2), 1);
        assert_eq!(script_check_workers(15), 14);
        assert_eq!(script_check_workers(100), max_workers);
    }

    #[test]
    fn parallel_script_checks_report_the_lowest_transaction_index() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        state.configure_script_check_threads(2);
        let block = mine_block(&state, 1);
        let first = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(bitcoin::Txid::from_byte_array([1; 32]), 0),
                script_sig: Builder::new().into_script(),
                sequence: Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(1),
                script_pubkey: Builder::new().push_int(1).into_script(),
            }],
        };
        let second = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(bitcoin::Txid::from_byte_array([2; 32]), 0),
                script_sig: Builder::new().into_script(),
                sequence: Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(1),
                script_pubkey: Builder::new().push_int(1).into_script(),
            }],
        };
        let first_txid = first.compute_txid();
        let jobs = [
            ScriptCheckJob {
                tx_index: 1,
                transaction: &first,
                previous_outputs: vec![TxOut {
                    value: Amount::from_sat(1),
                    script_pubkey: Builder::new().push_int(0).into_script(),
                }],
            },
            ScriptCheckJob {
                tx_index: 2,
                transaction: &second,
                previous_outputs: vec![TxOut {
                    value: Amount::from_sat(1),
                    script_pubkey: Builder::new().push_int(0).into_script(),
                }],
            },
        ];

        let error = state.validate_script_checks(&block, 1, &jobs).unwrap_err();
        let validation = error
            .downcast_ref::<ValidationError>()
            .expect("script failure retains its validation error");
        assert!(matches!(
            validation,
            ValidationError::Script { txid, .. } if *txid == first_txid
        ));
    }

    #[test]
    fn successful_script_checks_share_mempool_and_block_cache() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let block = mine_block(&state, 1);
        let transaction = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(bitcoin::Txid::from_byte_array([3; 32]), 0),
                script_sig: Builder::new().into_script(),
                sequence: Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(1),
                script_pubkey: Builder::new().push_int(1).into_script(),
            }],
        };
        let jobs = [ScriptCheckJob {
            tx_index: 1,
            transaction: &transaction,
            previous_outputs: vec![TxOut {
                value: Amount::from_sat(1),
                script_pubkey: Builder::new().push_int(1).into_script(),
            }],
        }];

        state
            .validate_mempool_transaction_scripts(&transaction, &jobs[0].previous_outputs)
            .unwrap();
        assert_eq!(state.script_cache.lock().entries.len(), 1);
        state.validate_script_checks(&block, 1, &jobs).unwrap();
        assert_eq!(state.script_cache.lock().entries.len(), 1);
        state.validate_script_checks(&block, 1, &jobs).unwrap();
        assert_eq!(state.script_cache.lock().entries.len(), 1);
        state.configure_script_cache_size_mib(0);
        assert_eq!(state.script_cache.lock().max_entries, 2);
    }

    #[test]
    fn assumeutxo_commitments_match_core_v31_1_network_tables() {
        let expected = [
            (Network::Bitcoin, 4, 935_000),
            (Network::Testnet, 2, 4_840_000),
            (Network::Testnet4, 2, 120_000),
            (Network::Signet, 2, 290_000),
            (Network::Regtest, 3, 299),
        ];
        for (network, count, last_height) in expected {
            let directory = tempfile::tempdir().unwrap();
            let state = ChainState::open(network, directory.path()).unwrap();
            let data = state.assumeutxo_data();
            assert_eq!(data.len(), count);
            assert_eq!(data.last().unwrap().height, last_height);
            for commitment in data {
                assert_eq!(commitment.hash_serialized.len(), 64);
                assert_eq!(commitment.blockhash.len(), 64);
                assert!(commitment.blockhash.parse::<BlockHash>().is_ok());
            }
        }
    }

    #[test]
    fn custom_signet_has_no_assumeutxo_commitments() {
        let directory = tempfile::tempdir().unwrap();
        let state = ChainState::open_with_signet_challenge(
            Network::Signet,
            directory.path(),
            Some(&[0x51]),
        )
        .unwrap();
        assert!(state.assumeutxo_data().is_empty());
    }

    #[test]
    fn strict_assumeutxo_rejects_an_uncommitted_snapshot_base() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        state.connect_block(mine_block(&state, 1)).unwrap();
        let path = directory.path().join("uncommitted.snapshot");
        state.dump_utxo_set(&path).unwrap();

        let error = state.load_assumeutxo_set(&path).unwrap_err().to_string();
        assert!(error.contains("assumeutxo block hash in snapshot metadata not recognized"));
        assert!(state.snapshot_provenance().is_none());
        assert!(!directory.path().join("assumeutxo.bin").exists());
    }

    #[test]
    fn snapshot_provenance_survives_restart_and_reports_unvalidated_state() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        state.connect_block(mine_block(&state, 1)).unwrap();
        let base = state.best_hash();
        state.persist_snapshot().unwrap();
        state.snapshot_base = Some(base);
        state.snapshot_validated = false;
        state.persist_snapshot_provenance().unwrap();
        drop(state);

        let reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(reopened.snapshot_provenance(), Some((base, false)));
        assert!(reopened.background_chainstate().is_some());
        assert!(!reopened.is_pruned());
        assert!(reopened.is_network_limited());
    }

    #[test]
    fn reopens_from_a_prefix_snapshot_without_old_block_bodies() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        for height in 1..=3 {
            state.connect_block(mine_block(&state, height)).unwrap();
        }
        state.persist_snapshot().unwrap();
        for height in 4..=5 {
            state.connect_block(mine_block(&state, height)).unwrap();
        }
        let expected_tip = state.best_hash();
        let expected_stats = state.utxo_stats();
        let retained_blocks = [
            state.block_hash(0).unwrap(),
            state.block_hash(4).unwrap(),
            state.block_hash(5).unwrap(),
        ]
        .into_iter()
        .collect::<HashSet<_>>();
        state
            .store
            .prune(&retained_blocks, &retained_blocks)
            .unwrap();
        drop(state);

        let reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(reopened.best_hash(), expected_tip);
        assert_eq!(reopened.utxo_stats(), expected_stats);
        assert_eq!(reopened.height(), 5);
    }

    #[test]
    fn background_assumeutxo_validation_promotes_a_matching_chainstate() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        for height in 1..=3 {
            let block = mine_block(&state, height);
            state.connect_block(block).unwrap();
        }
        let base = state.best_hash();
        let expected = state.load_utxo_map_from_store().unwrap();
        state.persist_snapshot().unwrap();
        state
            .persist_assumeutxo_base_snapshot(base, &expected)
            .unwrap();
        state.snapshot_base = Some(base);
        state.snapshot_validated = false;
        state.persist_snapshot_provenance().unwrap();
        state.start_background_validation().unwrap();

        for _ in 0..200 {
            state.poll_background_validation().unwrap();
            if state.snapshot_provenance().is_none() {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
        assert!(state.snapshot_provenance().is_none());
        assert!(state.background_chainstate().is_none());
        assert_eq!(state.load_utxo_map_from_store().unwrap(), expected);
        assert!(!directory.path().join("assumeutxo.bin").exists());
        assert!(!directory.path().join("assumeutxo-base.bin").exists());
    }

    #[test]
    fn background_assumeutxo_validation_discards_a_mismatching_snapshot() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        for height in 1..=3 {
            let block = mine_block(&state, height);
            state.connect_block(block).unwrap();
        }
        let base = state.best_hash();
        let expected = state.load_utxo_map_from_store().unwrap();
        state.persist_snapshot().unwrap();
        state
            .persist_assumeutxo_base_snapshot(base, &HashMap::new())
            .unwrap();
        state.snapshot_base = Some(base);
        state.snapshot_validated = false;
        state.persist_snapshot_provenance().unwrap();
        state.start_background_validation().unwrap();

        for _ in 0..200 {
            state.poll_background_validation().unwrap();
            if state.snapshot_provenance().is_none() {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
        assert!(state.snapshot_provenance().is_none());
        assert_eq!(state.load_utxo_map_from_store().unwrap(), expected);
        assert!(state.snapshot_validation_error().is_none());
    }

    #[test]
    fn initial_block_download_is_true_for_an_old_regtest_tip() {
        let directory = tempfile::tempdir().unwrap();
        let state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert!(state.is_initial_block_download());
    }

    #[test]
    fn verification_progress_matches_core_recent_header_adjustment() {
        let directory = tempfile::tempdir().unwrap();
        let state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let genesis_time = i64::from(state.header(0).unwrap().time);

        assert_eq!(state.verification_progress_at(genesis_time), 1.0);
        assert_eq!(
            state.verification_progress_at(genesis_time + 2 * 60 * 60),
            1.0
        );
        assert!(state.verification_progress_at(genesis_time + 2 * 60 * 60 + 1) < 1.0);
    }

    #[test]
    fn initial_block_download_latches_false_after_a_recent_tip() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let genesis_time = u64::from(state.header(0).unwrap().time);
        state.update_ibd_status_at(genesis_time + MAX_TIP_AGE_SECS);
        assert!(!state.is_initial_block_download());

        state.update_ibd_status_at(genesis_time + MAX_TIP_AGE_SECS + 1_000_000);
        assert!(!state.is_initial_block_download());
    }

    #[test]
    fn configurable_max_tip_age_updates_the_latched_ibd_boundary() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        state.configure_max_tip_age(u64::MAX);
        assert!(!state.is_initial_block_download());
    }

    #[test]
    fn assume_valid_skips_only_mature_ancestors_of_best_header() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let first = mine_block(&state, 1);
        let first_hash = first.block_hash();
        state.connect_block(first.clone()).unwrap();
        state.assume_valid_block = Some(first_hash);

        let mut second = mine_block(&state, 2);
        second.header.time = first.header.time + 14 * 24 * 60 * 60 + 1;
        second.header.nonce = 0;
        while !second.header.target().is_met_by(second.block_hash()) {
            second.header.nonce = second.header.nonce.wrapping_add(1);
        }
        state.connect_block(second.clone()).unwrap();

        // Core uses equivalent work time, not the raw header timestamp. A
        // single regtest block cannot mature an AssumeValid target merely by
        // setting its timestamp two weeks ahead.
        assert!(!state.should_skip_script_checks(&first, 1));
        assert!(!state.should_skip_script_checks(&second, 2));
    }

    #[test]
    fn reindex_rebuilds_chainstate_from_stored_blocks() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        for height in 1..=3 {
            let block = mine_block(&state, height);
            state.connect_block(block).unwrap();
        }
        let tip_hash = state.best_hash();
        let tip_stats = state.utxo_stats();
        drop(state);

        let rebuilt = ChainState::open_with_options(
            Network::Regtest,
            directory.path(),
            None,
            true,
            true,
            false,
        )
        .unwrap();
        assert_eq!(rebuilt.best_hash(), tip_hash);
        assert_eq!(rebuilt.height(), 3);
        assert_eq!(rebuilt.utxo_stats(), tip_stats);
        assert!(directory.path().join("chainstate.bin").exists());
    }

    #[test]
    fn reindex_chainstate_preserves_persisted_side_chain_transactions() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open_with_options_and_tx_index(
            Network::Regtest,
            directory.path(),
            None,
            false,
            false,
            false,
            true,
        )
        .unwrap();
        state.connect_block(mine_block(&state, 1)).unwrap();
        state.connect_block(mine_block(&state, 2)).unwrap();

        let genesis = *state.header(0).unwrap();
        let side = mine_block_from_header(&genesis, 1, 77);
        let side_txid = side.txdata[0].compute_txid();
        state.connect_block(side).unwrap();
        state.persist_metadata().unwrap();
        assert!(state.transaction(&side_txid).unwrap().is_some());
        drop(state);

        let mut rebuilt = ChainState::open_with_options_and_tx_index(
            Network::Regtest,
            directory.path(),
            None,
            false,
            false,
            true,
            true,
        )
        .unwrap();
        assert!(rebuilt.transaction(&side_txid).unwrap().is_some());
    }

    #[test]
    fn legacy_json_chainstate_files_migrate_to_binary_storage() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        for height in 1..=3 {
            let block = mine_block(&state, height);
            state.connect_block(block).unwrap();
        }
        let metadata = ChainMetadata {
            active_chain: state.active_chain.iter().map(ToString::to_string).collect(),
            headers: state.known_headers(),
            invalid_blocks: state
                .invalid_blocks
                .iter()
                .map(ToString::to_string)
                .collect(),
            prune_height: state.prune_height,
            prune_locks: HashMap::new(),
            prune_protected_blocks: HashMap::new(),
            segwit_validated_blocks: None,
        };
        let snapshot = state.current_snapshot().unwrap();
        let metadata_json = serde_json::to_vec_pretty(&metadata).unwrap();
        let snapshot_json = serde_json::to_vec(&snapshot).unwrap();
        let tip = state.best_hash();
        let height = state.height();
        drop(state);

        fs::remove_file(directory.path().join("chainstate.bin")).unwrap();
        fs::write(directory.path().join("chainstate.json"), &metadata_json).unwrap();
        fs::write(directory.path().join("chainstate.snapshot"), &snapshot_json).unwrap();
        let mut reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(reopened.best_hash(), tip);
        assert_eq!(reopened.height(), height);
        assert!(directory.path().join("chainstate.bin").exists());
        reopened.persist_snapshot().unwrap();
        drop(reopened);

        let binary_metadata = fs::read(directory.path().join("chainstate.bin")).unwrap();
        assert!(binary_metadata.starts_with(CHAIN_METADATA_MAGIC));
        assert!(binary_metadata.len() < metadata_json.len());
        let binary_snapshot = fs::read(directory.path().join("chainstate.snapshot")).unwrap();
        assert!(binary_snapshot.starts_with(CHAIN_SNAPSHOT_MAGIC));
        assert!(binary_snapshot.len() < snapshot_json.len());
    }

    #[test]
    fn indexed_basic_filter_lookups_survive_restart() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        for height in 1..=3 {
            let block = mine_block(&state, height);
            state.connect_block(block).unwrap();
        }
        let tip_hash = state.best_hash();
        let expected = state
            .basic_filter_for_block(&tip_hash)
            .unwrap()
            .expect("tip filter");
        state.persist_snapshot().unwrap();
        drop(state);

        let mut reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert!(reopened.basic_filter_cache.is_empty());
        assert_eq!(
            reopened.basic_filter_header_for_block(&tip_hash).unwrap(),
            Some(expected.1)
        );
        assert!(reopened.basic_filter_cache.is_empty());
        assert_eq!(
            reopened.basic_filter_for_block(&tip_hash).unwrap(),
            Some(expected)
        );
        assert_eq!(reopened.basic_filter_cache.len(), 1);

        let range = reopened
            .basic_filter_range(1, tip_hash, 2)
            .unwrap()
            .expect("filter range");
        assert_eq!(range.stop_hash, reopened.block_hash(2).unwrap());
        assert_eq!(range.filters.len(), 2);
        assert_eq!(range.filters[0].0, reopened.block_hash(1).unwrap());
        assert_eq!(range.filters[1].0, range.stop_hash);
        let genesis_hash = reopened.block_hash(0).unwrap();
        assert_eq!(
            range.previous_filter_header,
            reopened
                .basic_filter_for_block(&genesis_hash)
                .unwrap()
                .unwrap()
                .1
        );
    }

    #[test]
    fn basic_filter_ranges_follow_side_chain_ancestry() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let main_one = mine_block(&state, 1);
        state.connect_block(main_one).unwrap();
        let main_two = mine_block(&state, 2);
        let main_two_hash = main_two.block_hash();
        state.connect_block(main_two).unwrap();

        let genesis = *state.header(0).unwrap();
        let side_one = mine_block_from_header(&genesis, 1, 1);
        let side_one_hash = side_one.block_hash();
        state.connect_block(side_one).unwrap();
        let side_one_header = state.block_index[&side_one_hash].header;
        let side_two = mine_block_from_header(&side_one_header, 2, 2);
        let side_two_hash = side_two.block_hash();
        state.connect_block(side_two).unwrap();

        assert_eq!(state.best_hash(), main_two_hash);
        assert!(state.block_request_allowed(&main_two_hash, 30 * 24 * 60 * 60));
        assert!(state.block_request_allowed(&side_two_hash, 30 * 24 * 60 * 60));
        assert!(!state.block_request_allowed(&BlockHash::all_zeros(), 30 * 24 * 60 * 60));
        let range = state
            .basic_filter_range(1, side_two_hash, 2)
            .unwrap()
            .expect("side-chain filter range");
        assert_eq!(range.stop_hash, side_two_hash);
        assert_eq!(range.filters.len(), 2);
        assert_eq!(range.filters[0].0, side_one_hash);
        assert_eq!(range.filters[1].0, side_two_hash);
        assert_eq!(
            range.previous_filter_header,
            state
                .basic_filter_header_for_block(&state.block_hash(0).unwrap())
                .unwrap()
                .expect("genesis filter header")
        );
    }

    #[test]
    fn backfilled_basic_filters_survive_restart() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        for height in 1..=3 {
            state.connect_block(mine_block(&state, height)).unwrap();
        }
        let tip_hash = state.best_hash();
        state.persist_snapshot().unwrap();
        drop(state);

        fs::remove_dir_all(directory.path().join("filters")).unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(state.filter_store.len(), 0);
        let expected = state
            .basic_filter_for_block(&tip_hash)
            .unwrap()
            .expect("backfilled tip filter");
        assert_eq!(state.filter_store.len(), 4);
        drop(state);

        let mut reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(reopened.filter_store.len(), 4);
        assert_eq!(
            reopened.basic_filter_header_for_block(&tip_hash).unwrap(),
            Some(expected.1)
        );
    }

    #[test]
    fn basic_filter_cache_is_bounded() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        for height in 1..=u32::try_from(MAX_BASIC_FILTER_CACHE_ENTRIES).unwrap() + 16 {
            state.connect_block(mine_block(&state, height)).unwrap();
        }
        assert!(state.basic_filter_cache.len() <= MAX_BASIC_FILTER_CACHE_ENTRIES);
        assert!(state.basic_filter_cache.contains_key(&state.best_hash()));
    }

    #[test]
    fn block_locators_back_off_and_reverse_ranges_are_empty() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        for height in 1..=20 {
            let block = mine_block(&state, height);
            state.connect_block(block).unwrap();
        }

        let locator_heights = state
            .block_locator_hashes()
            .into_iter()
            .map(|hash| state.block_height_by_hash(&hash).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            locator_heights,
            vec![20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 8, 4, 0]
        );

        let locator = vec![state.block_hash(15).unwrap()];
        let stop_hash = state.block_hash(10).unwrap();
        assert!(state.headers_after_locator(&locator, stop_hash).is_empty());
        assert!(
            state
                .headers_after_locator(&[], state.block_hash(10).unwrap())
                .is_empty()
        );

        let stop_hash = state.block_hash(10).unwrap();
        assert_eq!(
            state
                .headers_for_getheaders(&[], stop_hash, 30 * 24 * 60 * 60)
                .unwrap(),
            vec![*state.header(10).unwrap()]
        );
        assert!(
            state
                .headers_for_getheaders(&[], BlockHash::all_zeros(), 30 * 24 * 60 * 60)
                .is_none()
        );
        assert!(
            state
                .headers_for_getheaders(
                    &[],
                    BlockHash::from_byte_array([0x55; 32]),
                    30 * 24 * 60 * 60
                )
                .is_none()
        );
    }

    #[test]
    fn getblocks_excludes_stop_and_stops_at_missing_body() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        for height in 1..=4 {
            state.connect_block(mine_block(&state, height)).unwrap();
        }

        let locator = [state.block_hash(0).unwrap()];
        let stop = state.block_hash(3).unwrap();
        assert_eq!(
            state.block_hashes_after_locator_for_getblocks(&locator, stop, 500),
            vec![state.block_hash(1).unwrap(), state.block_hash(2).unwrap(),]
        );

        let retained = [
            state.block_hash(0).unwrap(),
            state.block_hash(1).unwrap(),
            state.block_hash(3).unwrap(),
            state.block_hash(4).unwrap(),
        ]
        .into_iter()
        .collect::<HashSet<_>>();
        state.store.prune(&retained, &retained).unwrap();
        assert_eq!(
            state.block_hashes_after_locator_for_getblocks(&locator, BlockHash::all_zeros(), 500),
            vec![state.block_hash(1).unwrap()]
        );
    }

    #[test]
    fn getheaders_uses_active_tip_for_a_side_branch_locator() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let active = mine_block(&state, 1);
        state.connect_block(active).unwrap();

        // A header-only branch extending the active tip is present in Core's
        // global block index but is not itself part of the active chain.
        let side = mine_block(&state, 2);
        let side_hash = side.block_hash();
        state
            .accept_headers(std::slice::from_ref(&side.header))
            .unwrap();

        assert_eq!(
            state.headers_after_locator(&[side_hash], BlockHash::all_zeros()),
            Vec::new()
        );
    }

    #[test]
    fn rejects_a_modified_unpruned_utxo_snapshot() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let first = mine_block(&state, 1);
        state.connect_block(first).unwrap();
        let path = directory.path().join("external.snapshot");
        state.dump_utxo_set(&path).unwrap();

        let mut bytes = fs::read(&path).unwrap();
        bytes.pop();
        fs::write(&path, bytes).unwrap();

        assert!(state.load_utxo_set(&path).is_err());
        assert_eq!(state.utxo_stats().2, 5_000_000_000);
    }

    #[test]
    fn core_utxo_snapshot_round_trips_with_compressed_coin_encoding() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let block = mine_block(&state, 1);
        state.connect_block(block).unwrap();
        let path = directory.path().join("core-utxo.dat");

        let expected = state.utxo_stats();
        let (written, base_hash, base_height) = state.dump_utxo_set(&path).unwrap();
        assert_eq!(written as usize, expected.1);
        assert_eq!(base_hash, state.best_hash());
        assert_eq!(base_height, state.height());
        assert!(
            fs::read(&path)
                .unwrap()
                .starts_with(&CORE_UTXO_SNAPSHOT_MAGIC)
        );

        let (loaded, loaded_hash, loaded_height) = state.load_utxo_set(&path).unwrap();
        assert_eq!(loaded, written);
        assert_eq!(loaded_hash, base_hash);
        assert_eq!(loaded_height, base_height);
        assert_eq!(state.utxo_stats(), expected);
    }

    #[test]
    fn core_utxo_snapshot_at_a_historical_base_advances_to_the_active_tip() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        for height in 1..=3 {
            state.connect_block(mine_block(&state, height)).unwrap();
        }
        let expected = state.utxo_stats();
        let base_hash = state.block_hash(1).unwrap();
        let path = directory.path().join("historical-core-utxo.dat");
        let (base_coins, dumped_hash, dumped_height, _, _) =
            state.dump_utxo_set_at(&path, base_hash).unwrap();
        assert_eq!(base_coins, 1);
        assert_eq!(dumped_hash, base_hash);
        assert_eq!(dumped_height, 1);

        let (loaded, loaded_hash, loaded_height) = state.load_utxo_set(&path).unwrap();
        assert_eq!(loaded, base_coins);
        assert_eq!(loaded_hash, base_hash);
        assert_eq!(loaded_height, 1);
        assert_eq!(state.utxo_stats(), expected);

        let reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(reopened.best_hash(), state.best_hash());
        assert_eq!(reopened.utxo_stats(), expected);
    }

    #[test]
    fn core_snapshot_script_compression_matches_core_special_cases() {
        for (value, expected) in [
            (0, vec![0x00]),
            (127, vec![0x7f]),
            (128, vec![0x80, 0x00]),
            (255, vec![0x80, 0x7f]),
            (16_384, vec![0xff, 0x00]),
        ] {
            let mut encoded = Vec::new();
            write_snapshot_varint(&mut encoded, value).unwrap();
            assert_eq!(encoded, expected);
            let mut cursor = Cursor::new(encoded.as_slice());
            assert_eq!(read_snapshot_varint(&mut cursor).unwrap(), value);
        }

        let compressed_key = [
            0x02, 0x79, 0xbe, 0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac, 0x55, 0xa0, 0x62, 0x95, 0xce,
            0x87, 0x0b, 0x07, 0x02, 0x9b, 0xfc, 0xdb, 0x2d, 0xce, 0x28, 0xd9, 0x59, 0xf2, 0x81,
            0x5b, 0x16, 0xf8, 0x17, 0x98,
        ];
        let uncompressed_key = bitcoin::secp256k1::PublicKey::from_slice(&compressed_key)
            .unwrap()
            .serialize_uncompressed();
        let scripts = [
            ScriptBuf::from_bytes({
                let mut bytes = vec![0x76, 0xa9, 0x14];
                bytes.extend_from_slice(&[3; 20]);
                bytes.extend_from_slice(&[0x88, 0xac]);
                bytes
            }),
            ScriptBuf::from_bytes({
                let mut bytes = vec![0xa9, 0x14];
                bytes.extend_from_slice(&[4; 20]);
                bytes.push(0x87);
                bytes
            }),
            ScriptBuf::from_bytes({
                let mut bytes = vec![33];
                bytes.extend_from_slice(&compressed_key);
                bytes.push(0xac);
                bytes
            }),
            ScriptBuf::from_bytes({
                let mut bytes = vec![65];
                bytes.extend_from_slice(&uncompressed_key);
                bytes.push(0xac);
                bytes
            }),
            ScriptBuf::from_bytes(vec![0x51; 37]),
        ];

        for script in scripts {
            let mut encoded = Vec::new();
            write_compressed_snapshot_script(&mut encoded, &script).unwrap();
            let mut cursor = Cursor::new(encoded.as_slice());
            assert_eq!(
                read_compressed_snapshot_script(&mut cursor).unwrap(),
                script
            );
            assert_eq!(cursor.position() as usize, encoded.len());
        }
        for amount in [0, 1, 10, 100_000_000, 5_000_000_000] {
            assert_eq!(
                decompress_snapshot_amount(compress_snapshot_amount(amount)).unwrap(),
                amount
            );
        }
    }

    #[test]
    fn core_utxo_snapshot_rejects_truncation_duplicates_and_trailing_data() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        state.connect_block(mine_block(&state, 1)).unwrap();
        let path = directory.path().join("core-utxo.dat");
        state.dump_utxo_set(&path).unwrap();
        let valid = fs::read(&path).unwrap();
        assert_eq!(
            read_core_utxo_snapshot(&valid, Network::Regtest, None)
                .unwrap()
                .coins_count,
            1
        );

        let mut truncated = valid.clone();
        truncated.pop();
        assert!(read_core_utxo_snapshot(&truncated, Network::Regtest, None).is_err());

        let mut trailing = valid.clone();
        trailing.push(0);
        assert!(read_core_utxo_snapshot(&trailing, Network::Regtest, None).is_err());

        let metadata_len = CORE_UTXO_SNAPSHOT_MAGIC.len() + 2 + 4 + 32 + 8;
        let group_offset = metadata_len + 32;
        assert_eq!(valid[group_offset], 1);
        let mut duplicate = valid.clone();
        duplicate[metadata_len - 8..metadata_len].copy_from_slice(&2u64.to_le_bytes());
        duplicate[group_offset] = 2;
        duplicate.extend_from_slice(&valid[group_offset + 1..]);
        assert!(read_core_utxo_snapshot(&duplicate, Network::Regtest, None).is_err());
    }

    #[test]
    fn pruned_chain_restarts_from_its_snapshot() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let mut old_block_hash = None;
        for height in 1..=300 {
            let block = mine_block(&state, height);
            if height == 5 {
                old_block_hash = Some(block.block_hash());
            }
            state.connect_block(block).unwrap();
        }
        let tip_hash = state.best_hash();
        let old_block_hash = old_block_hash.expect("prune test block");
        assert!(state.store.contains(&old_block_hash));
        assert!(!state.is_block_pruned(&old_block_hash));
        assert_eq!(state.prune(1).unwrap(), 0);
        assert_eq!(state.prune_height(), None);
        assert_eq!(state.prune(50).unwrap(), 12);
        assert!(!state.store.contains(&old_block_hash));
        assert!(state.is_block_pruned(&old_block_hash));
        assert!(!state.is_block_pruned(&state.block_hash(12).unwrap()));
        assert!(!state.is_block_pruned(&state.block_hash(13).unwrap()));
        assert_eq!(
            state.proposal_duplicate_status(&old_block_hash),
            Some("duplicate")
        );
        assert_eq!(state.prune_height(), Some(12));
        let path = directory.path().to_owned();
        drop(state);
        let mut reopened = ChainState::open(Network::Regtest, &path).unwrap();
        assert_eq!(reopened.best_hash(), tip_hash);
        assert_eq!(reopened.height(), 300);
        assert_eq!(reopened.prune_height(), Some(12));
        assert!(!reopened.store.contains(&old_block_hash));
        assert!(reopened.is_block_pruned(&old_block_hash));
        assert_eq!(
            reopened.block_transaction_count(&old_block_hash).unwrap(),
            Some(1)
        );
        assert!(path.join("chainstate.txcounters").exists());
    }

    #[test]
    fn electrum_transaction_sidecar_survives_pruning_and_restart() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        state.configure_pruning(1).unwrap();
        state.configure_electrum_index(true).unwrap();
        let mut old_block_hash = None;
        let mut old_txid = None;
        for height in 1..=300 {
            let block = mine_block(&state, height);
            if height == 5 {
                old_block_hash = Some(block.block_hash());
                old_txid = Some(block.txdata[0].compute_txid());
            }
            state.connect_block(block).unwrap();
        }
        let old_block_hash = old_block_hash.expect("sidecar test block");
        let old_txid = old_txid.expect("sidecar test transaction");
        assert!(state.transaction(&old_txid).unwrap().is_some());
        state.prune(50).unwrap();
        assert!(!state.store.contains(&old_block_hash));
        let (transaction, location) = state
            .transaction(&old_txid)
            .unwrap()
            .expect("pruned transaction remains indexed");
        assert_eq!(transaction.compute_txid(), old_txid);
        assert_eq!(location.block_hash, old_block_hash);
        assert_eq!(
            state.merkle_branch(&old_txid).unwrap(),
            Some((Vec::new(), 0, 5))
        );

        let path = directory.path().to_owned();
        drop(state);
        let mut reopened = ChainState::open(Network::Regtest, &path).unwrap();
        reopened.configure_pruning(1).unwrap();
        reopened.configure_electrum_index(true).unwrap();
        let (transaction, location) = reopened
            .transaction(&old_txid)
            .unwrap()
            .expect("pruned transaction survives restart");
        assert_eq!(transaction.compute_txid(), old_txid);
        assert_eq!(location.block_hash, old_block_hash);
        assert_eq!(
            reopened.merkle_branch(&old_txid).unwrap(),
            Some((Vec::new(), 0, 5))
        );
    }

    #[test]
    fn unpruned_electrum_uses_native_blocks_without_a_transaction_sidecar() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        state.configure_electrum_index(true).unwrap();

        let block = mine_block(&state, 1);
        let txid = block.txdata[0].compute_txid();
        state.connect_block(block).unwrap();

        assert!(state.electrum_store.is_none());
        assert!(
            !directory
                .path()
                .join("indexes/electrum/txblocks.dat")
                .exists()
        );
        assert_eq!(
            state
                .electrum_transaction_at_height(1, 0)
                .unwrap()
                .expect("native block store transaction"),
            state.transaction(&txid).unwrap().unwrap().0
        );
    }

    #[test]
    fn configured_pruning_reports_mode_and_target() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        state.configure_prune_after_height(Network::Regtest, false);
        assert_eq!(state.prune_after_height, 1_000);
        state.configure_prune_after_height(Network::Regtest, true);
        assert_eq!(state.prune_after_height, 100);
        state.configure_pruning(1).unwrap();
        assert!(state.is_pruned());
        assert_eq!(state.prune_target_size(), None);

        state.configure_pruning(550).unwrap();
        assert!(state.is_pruned());
        assert_eq!(state.prune_target_size(), Some(550 * 1024 * 1024));
    }

    #[test]
    fn prune_locks_persist_only_non_temporary_entries() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        state
            .set_prune_lock(
                "persistent",
                Some(PruneLock {
                    desc: "keep history".to_owned(),
                    height_first: 100,
                    height_last: u64::MAX,
                    temporary: false,
                }),
            )
            .unwrap();
        state
            .set_prune_lock(
                "temporary",
                Some(PruneLock {
                    desc: "one run".to_owned(),
                    height_first: 200,
                    height_last: 300,
                    temporary: true,
                }),
            )
            .unwrap();
        assert_eq!(state.prune_locks().len(), 2);
        drop(state);

        let reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let locks = reopened.prune_locks();
        assert_eq!(locks.len(), 1);
        assert_eq!(locks[0].0, "persistent");
        assert_eq!(locks[0].1.height_first, 100);
    }

    #[test]
    fn automatic_pruning_keeps_the_recent_reorg_window() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let mut old_block_hash = None;
        for height in 1..=300 {
            let block = mine_block(&state, height);
            if height == 5 {
                old_block_hash = Some(block.block_hash());
            }
            state.connect_block(block).unwrap();
        }
        state.prune_mode = true;
        state.prune_target_size = Some(0);
        assert!(state.maybe_auto_prune().unwrap());
        assert_eq!(state.prune_height(), Some(12));
        assert!(!state.store.contains(&old_block_hash.unwrap()));
        assert!(state.store.contains(&state.block_hash(13).unwrap()));
        assert!(state.store.contains(&state.block_hash(12).unwrap()));
    }

    #[test]
    fn pruning_waits_for_assumeutxo_background_validation() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        state.configure_prune_after_height(Network::Regtest, true);
        let mut old_block_hash = None;
        for height in 1..=300 {
            let block = mine_block(&state, height);
            if height == 5 {
                old_block_hash = Some(block.block_hash());
            }
            state.connect_block(block).unwrap();
        }
        let snapshot_base = state.block_hash(3).unwrap();
        state.snapshot_base = Some(snapshot_base);
        state.snapshot_validated = false;
        state.prune_mode = true;
        state.prune_target_size = Some(0);

        assert!(!state.maybe_auto_prune().unwrap());
        assert_eq!(state.prune(50).unwrap(), 0);
        assert!(state.store.contains(&old_block_hash.unwrap()));
        assert_eq!(state.prune_height(), None);

        state.snapshot_validated = true;
        // Fast-prune follows the implementation's 64 KiB record-batch
        // granularity. These synthetic blocks do not fill a batch, so
        // validation becoming complete still leaves the chain unchanged.
        assert_eq!(state.prune(50).unwrap(), 0);
        assert!(state.store.contains(&old_block_hash.unwrap()));
    }

    #[test]
    fn coinstats_index_matches_live_and_historical_utxo_statistics() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let first = mine_block(&state, 1);
        let first_hash = first.block_hash();
        state.connect_block(first).unwrap();
        let second = mine_block(&state, 2);
        let second_hash = second.block_hash();
        state.connect_block(second).unwrap();
        state.configure_coinstats_index(true).unwrap();

        let live = state.utxo_statistics(false, true);
        let indexed = state.coinstats_at(&second_hash, true).unwrap().unwrap().1;
        assert_eq!(indexed.transactions, live.transactions);
        assert_eq!(indexed.outputs, live.outputs);
        assert_eq!(indexed.total_amount_sat, live.total_amount_sat);
        assert_eq!(indexed.bogo_size, live.bogo_size);
        assert_eq!(indexed.muhash, live.muhash);

        let first_stats = state.coinstats_at(&first_hash, true).unwrap().unwrap();
        assert_eq!(first_stats.0, 1);
        assert_eq!(first_stats.1.outputs, 1);

        let path = directory.path().to_owned();
        drop(state);
        let mut reopened = ChainState::open(Network::Regtest, path).unwrap();
        reopened.configure_coinstats_index(true).unwrap();
        assert_eq!(
            reopened
                .coinstats_at(&second_hash, true)
                .unwrap()
                .unwrap()
                .1
                .muhash,
            live.muhash
        );
    }

    #[test]
    fn coinstats_index_replays_side_chain_block_by_hash() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let main_one = mine_block(&state, 1);
        state.connect_block(main_one).unwrap();
        let main_two = mine_block(&state, 2);
        let main_two_hash = main_two.block_hash();
        state.connect_block(main_two).unwrap();

        let genesis = *state.header(0).unwrap();
        let side_one = mine_block_from_header(&genesis, 1, 1);
        let side_one_hash = side_one.block_hash();
        state.connect_block(side_one).unwrap();
        let side_one_header = state.block_index[&side_one_hash].header;
        let side_two = mine_block_from_header(&side_one_header, 2, 2);
        let side_two_hash = side_two.block_hash();
        state.connect_block(side_two).unwrap();

        assert_eq!(state.best_hash(), main_two_hash);
        state.configure_coinstats_index(true).unwrap();
        let (height, stats) = state
            .coinstats_at(&side_two_hash, true)
            .unwrap()
            .expect("side-chain coinstats");
        assert_eq!(height, 2);
        assert_eq!(stats.outputs, 2);
        assert_eq!(stats.total_amount_sat, 10_000_000_000);
        assert!(stats.muhash.is_some());
    }

    #[test]
    fn coinstats_excludes_unspendable_outputs_and_tracks_unclaimed_rewards() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let mut block = mine_block(&state, 1);
        block.txdata[0].output[0].value = Amount::from_sat(4_000_000_000);
        block.txdata[0].output.push(TxOut {
            value: Amount::from_sat(500_000_000),
            script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x6a]),
        });
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        block.header.nonce = 0;
        while !block.header.target().is_met_by(block.block_hash()) {
            block.header.nonce = block.header.nonce.wrapping_add(1);
        }
        let coinbase_txid = block.txdata[0].compute_txid();
        let block_hash = block.block_hash();
        state.connect_block(block).unwrap();
        state.configure_coinstats_index(true).unwrap();

        let stats = state.coinstats_at(&block_hash, false).unwrap().unwrap().1;
        assert_eq!(stats.outputs, 1);
        assert_eq!(stats.total_amount_sat, 4_000_000_000);
        assert_eq!(stats.total_coinbase_sat, 4_000_000_000);
        assert_eq!(stats.total_unspendable_genesis_sat, 5_000_000_000);
        assert_eq!(stats.total_unspendable_scripts_sat, 500_000_000);
        assert_eq!(stats.total_unspendable_unclaimed_rewards_sat, 500_000_000);

        state.configure_txospender_index(true).unwrap();
        let script_hash = electrum_script_hash(&bitcoin::ScriptBuf::from_bytes(vec![0x6a]));
        assert_eq!(
            state.electrum_unspent_for_script(&script_hash).unwrap(),
            vec![(OutPoint::new(coinbase_txid, 1), 1, 0, 500_000_000,)]
        );
    }

    #[test]
    fn recognizes_only_the_two_bip30_mainnet_repeats() {
        assert!(is_bip30_repeat(
            Network::Bitcoin,
            91_842,
            "00000000000a4d0a398161ffc163c503763b1f4360639393e0e4c8e300e0caec"
                .parse()
                .unwrap()
        ));
        assert!(!is_bip30_repeat(
            Network::Regtest,
            91_842,
            BlockHash::all_zeros()
        ));
        assert!(is_bip30_unspendable(
            Network::Bitcoin,
            91_722,
            "00000000000271a2dc26e7667f8419f2e15416dc6955e5a6c6cdf3f2574dd08e"
                .parse()
                .unwrap()
        ));
        assert!(is_bip30_unspendable(
            Network::Bitcoin,
            91_812,
            "00000000000af0aed4792b1acee3d966af36cf5def14935db8de83d6f9306f2f"
                .parse()
                .unwrap()
        ));
        assert!(!is_bip30_unspendable(
            Network::Testnet,
            91_722,
            BlockHash::all_zeros()
        ));
    }

    #[test]
    fn connects_and_replays_regtest_blocks() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let first = mine_block(&state, 1);
        let first_hash = first.block_hash();
        state.connect_block(first).unwrap();
        assert_eq!(
            state.block_fee_stats(&first_hash).unwrap(),
            Some(BlockFeeStats {
                total_fee_sat: 0,
                transaction_fees_sat: Vec::new(),
                spent_outputs: Vec::new(),
            })
        );
        let second = mine_block(&state, 2);
        state.connect_block(second).unwrap();
        assert_eq!(state.height(), 2);
        assert_eq!(state.best_hash(), state.block_hash(2).unwrap());
        let script_hash = electrum_script_hash(&Builder::new().push_int(1).into_script());
        assert_eq!(state.get_utxos(&script_hash).len(), 2);
        state.verify_active_chain(0).unwrap();
        for check_level in 0..=4 {
            state
                .verify_active_chain_with_level(check_level, 1)
                .unwrap();
        }
        state.verify_active_chain_with_level(4, 0).unwrap();
        state.materialize_utxos().unwrap();
        let original_utxos = state.utxos.clone();
        let corrupted_outpoint = *state.utxos.keys().next().unwrap();
        state
            .utxos
            .get_mut(&corrupted_outpoint)
            .unwrap()
            .output
            .value = Amount::from_sat(1);
        assert!(state.verify_active_chain_with_level(4, 0).is_err());
        state.utxos = original_utxos;
        state.persist_snapshot().unwrap();
        assert!(directory.path().join("chainstate/utxos/utxos.dat").exists());
        assert!(
            directory
                .path()
                .join("chainstate/utxos/utxos.index")
                .exists()
        );
        assert!(directory.path().join("chainstate/utxos.tip").exists());
        drop(state);
        let reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(reopened.height(), 2);
        assert_eq!(reopened.block_hash(1), Some(first_hash));
        assert_eq!(reopened.all_utxos().count(), 2);
        assert_eq!(reopened.get_utxos(&script_hash).len(), 2);
        drop(reopened);
        let snapshot_path = directory.path().join("chainstate.snapshot");
        let bytes = fs::read(&snapshot_path).unwrap();
        assert!(bytes.starts_with(CHAIN_SNAPSHOT_MAGIC));
        let mut snapshot: ChainSnapshot =
            deserialize_internal(&bytes, CHAIN_SNAPSHOT_MAGIC).unwrap();
        let entry = snapshot.utxos.values_mut().next().unwrap();
        entry.output.value = Amount::from_sat(entry.output.value.to_sat().saturating_sub(1));
        fs::write(
            &snapshot_path,
            serialize_internal(CHAIN_SNAPSHOT_MAGIC, &snapshot).unwrap(),
        )
        .unwrap();
        assert!(ChainState::open(Network::Regtest, directory.path()).is_err());
        fs::write(directory.path().join("chainstate.snapshot"), b"corrupt").unwrap();
        let replayed = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(replayed.height(), 2);
    }

    #[test]
    fn active_utxo_values_are_served_from_the_durable_store() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        state.connect_block(mine_block(&state, 1)).unwrap();
        state.connect_block(mine_block(&state, 2)).unwrap();
        let script_hash = electrum_script_hash(&Builder::new().push_int(1).into_script());
        let expected_history = state.get_history(&script_hash);

        assert!(!state.utxos_materialized);
        assert!(state.utxos.is_empty());
        assert!(!state.history_materialized);
        assert!(state.history.is_empty());
        assert_eq!(state.all_utxos().count(), 2);
        assert_eq!(state.utxo_stats(), (2, 2, 10_000_000_000));
        assert_eq!(state.utxo_store.len(), 2);
        assert_eq!(
            state
                .electrum_history_store
                .get(&script_hash)
                .unwrap()
                .into_iter()
                .map(|(txid, height)| HistoryEntry { txid, height })
                .collect::<Vec<_>>(),
            expected_history
        );

        drop(state);
        let reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert!(!reopened.history_materialized);
        assert_eq!(reopened.get_history(&script_hash), expected_history);
    }

    #[test]
    fn active_transaction_locations_omit_redundant_block_hash() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let block = mine_block(&state, 1);
        let txid = block.txdata[0].compute_txid();
        state.connect_block(block).unwrap();

        assert!(std::mem::size_of::<ActiveTxLocation>() < std::mem::size_of::<TxLocation>());
        let compact = state.tx_index.get(&txid).copied().unwrap();
        assert_eq!(compact.height, 1);
        assert_eq!(compact.transaction_index, 0);
        let location = state.transaction_location(&txid).unwrap();
        assert_eq!(location.block_hash, state.block_hash(1).unwrap());
        assert_eq!(location.height, compact.height);
        assert_eq!(location.transaction_index, compact.transaction_index);

        drop(state);
        let reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(reopened.transaction_location(&txid), Some(location));
    }

    #[test]
    fn reopens_from_a_durable_chainstate_delta_suffix() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        state.connect_block(mine_block(&state, 1)).unwrap();
        state.persist_snapshot().unwrap();
        let second = mine_block(&state, 2);
        let second_hash = second.block_hash();
        state.connect_block(second).unwrap();
        let expected_stats = state.utxo_stats();
        let expected_script_hash = electrum_script_hash(&Builder::new().push_int(1).into_script());
        let expected_history = state.get_history(&expected_script_hash);
        assert!(
            fs::metadata(directory.path().join("chainstate/deltas.dat"))
                .unwrap()
                .len()
                > 0
        );
        drop(state);

        let reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(reopened.best_hash(), second_hash);
        assert_eq!(reopened.utxo_stats(), expected_stats);
        assert_eq!(
            reopened.get_history(&expected_script_hash),
            expected_history
        );
        drop(reopened);

        let delta_path = directory.path().join("chainstate/deltas.dat");
        let mut delta_bytes = fs::read(&delta_path).unwrap();
        *delta_bytes.last_mut().unwrap() ^= 1;
        fs::write(&delta_path, delta_bytes).unwrap();
        let replayed = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(replayed.best_hash(), second_hash);
        assert_eq!(replayed.utxo_stats(), expected_stats);
    }

    #[test]
    fn omits_side_chain_transactions_without_the_optional_txindex() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open_with_options_and_tx_index(
            Network::Regtest,
            directory.path(),
            None,
            false,
            false,
            false,
            false,
        )
        .unwrap();
        let main = mine_block(&state, 1);
        let main_hash = main.block_hash();
        let main_txid = main.txdata[0].compute_txid();
        state.connect_block(main).unwrap();
        assert!(state.tx_index_all.is_empty());
        assert!(state.transaction(&main_txid).unwrap().is_some());

        let genesis = *state.header(0).unwrap();
        let side = mine_block_from_header(&genesis, 1, 77);
        let side_hash = side.block_hash();
        let side_txid = side.txdata[0].compute_txid();
        state.connect_block(side).unwrap();
        assert_eq!(state.best_hash(), main_hash);
        assert!(!state.is_active_block(&side_hash));
        assert!(state.transaction(&side_txid).unwrap().is_none());

        drop(state);
        let mut reopened = ChainState::open_with_options_and_tx_index(
            Network::Regtest,
            directory.path(),
            None,
            false,
            false,
            false,
            false,
        )
        .unwrap();
        assert!(reopened.tx_index_all.is_empty());
        assert!(reopened.transaction(&main_txid).unwrap().is_some());
        assert!(reopened.transaction(&side_txid).unwrap().is_none());
    }

    #[test]
    fn active_transaction_lookup_omits_side_chain_with_optional_txindex() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open_with_options_and_tx_index(
            Network::Regtest,
            directory.path(),
            None,
            false,
            false,
            false,
            true,
        )
        .unwrap();
        let main = mine_block(&state, 1);
        let main_txid = main.txdata[0].compute_txid();
        state.connect_block(main).unwrap();
        assert!(state.active_transaction(&main_txid).unwrap().is_some());

        let genesis = *state.header(0).unwrap();
        let side = mine_block_from_header(&genesis, 1, 77);
        let side_txid = side.txdata[0].compute_txid();
        state.connect_block(side).unwrap();
        assert!(state.transaction(&side_txid).unwrap().is_some());
        assert!(state.active_transaction(&side_txid).unwrap().is_none());

        drop(state);
        let mut reopened = ChainState::open_with_options_and_tx_index(
            Network::Regtest,
            directory.path(),
            None,
            false,
            false,
            false,
            true,
        )
        .unwrap();
        assert!(reopened.transaction(&side_txid).unwrap().is_some());
        assert!(reopened.active_transaction(&side_txid).unwrap().is_none());
    }

    #[test]
    fn active_transaction_lookup_returns_earliest_duplicate_txid() {
        let directory = tempfile::tempdir().unwrap();
        let mut deployment_parameters =
            validation::DeploymentParameters::for_network(Network::Regtest);
        // Regtest activates BIP34 at height one, while the historical
        // duplicate-coinbase shape predates that rule. Delay it for this
        // focused index test so the genesis coinbase can be repeated.
        deployment_parameters.buried.bip34 = 500;
        let mut state = ChainState::open_with_options_and_tx_index_in_dirs_with_minimum_chain_work_and_assume_valid_and_blocks_xor_and_deployment_parameters(
            Network::Regtest,
            directory.path(),
            directory.path(),
            None,
            true,
            false,
            false,
            false,
            None,
            None,
            false,
            deployment_parameters,
        )
        .unwrap();
        let genesis = genesis_block(Network::Regtest);
        let duplicate_txid = genesis.txdata[0].compute_txid();
        let previous = *state.header(0).unwrap();
        let mut duplicate = Block {
            header: Header {
                version: BlockVersion::from_consensus(4),
                prev_blockhash: previous.block_hash(),
                merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                time: previous.time.saturating_add(1),
                bits: previous.bits,
                nonce: 0,
            },
            txdata: vec![genesis.txdata[0].clone()],
        };
        duplicate.header.merkle_root = duplicate.compute_merkle_root().unwrap();
        while !duplicate.header.target().is_met_by(duplicate.block_hash()) {
            duplicate.header.nonce = duplicate.header.nonce.wrapping_add(1);
        }
        state.connect_block(duplicate).unwrap();

        let (_, earliest) = state
            .active_transaction(&duplicate_txid)
            .unwrap()
            .expect("duplicate transaction is indexed");
        assert_eq!(earliest.height, 0);
        let (_, latest) = state
            .transaction(&duplicate_txid)
            .unwrap()
            .expect("latest transaction index location is present");
        assert_eq!(latest.height, 1);

        state.persist_snapshot().unwrap();
        drop(state);
        let mut reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let (_, earliest) = reopened
            .active_transaction(&duplicate_txid)
            .unwrap()
            .expect("duplicate transaction survives snapshot reload");
        assert_eq!(earliest.height, 0);
    }

    fn mine_block(state: &ChainState, height: u32) -> Block {
        let previous = state.header(height - 1).expect("parent header");
        mine_block_from_header(previous, height, 0)
    }

    #[test]
    fn selects_and_replays_a_higher_work_fork() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let main_one = mine_block(&state, 1);
        let main_one_hash = main_one.block_hash();
        state.connect_block(main_one).unwrap();
        let main_two = mine_block(&state, 2);
        let main_two_coinbase = main_two.txdata[0].compute_txid();
        let old_tip = main_two.block_hash();
        state.connect_block(main_two).unwrap();

        let genesis = *state.header(0).unwrap();
        let side_one = mine_block_from_header(&genesis, 1, 1);
        let side_one_hash = side_one.block_hash();
        state.connect_block(side_one).unwrap();
        let side_one_header = *state.block_index.get(&side_one_hash).unwrap();
        let side_two = mine_block_from_header(&side_one_header.header, 2, 2);
        let side_two_hash = side_two.block_hash();
        state.connect_block(side_two).unwrap();
        let side_two_header = *state.block_index.get(&side_two_hash).unwrap();
        let side_three = mine_block_from_header(&side_two_header.header, 3, 3);
        let side_three_hash = side_three.block_hash();
        state.connect_block(side_three).unwrap();

        assert_eq!(state.height(), 3);
        assert_eq!(state.best_hash(), side_three_hash);
        assert_eq!(state.block_hash(1), Some(side_one_hash));
        let replacement = state.active_blocks_after(old_tip).unwrap();
        assert_eq!(replacement.len(), 3);
        assert_eq!(replacement[0].block_hash(), side_one_hash);
        let disconnected = state.disconnected_blocks_after(old_tip).unwrap();
        assert_eq!(disconnected.len(), 2);
        assert_eq!(disconnected[0].block_hash(), main_one_hash);
        assert_eq!(disconnected[1].block_hash(), old_tip);
        let tips = state.chain_tips();
        assert_eq!(tips.len(), 2);
        assert_eq!(tips[0].status, "active");
        assert_eq!(tips[1].status, "valid-fork");

        drop(state);
        let mut reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(reopened.best_hash(), side_three_hash);
        assert_eq!(reopened.block_hash(1), Some(side_one_hash));
        assert!(reopened.transaction(&main_two_coinbase).unwrap().is_some());
    }

    #[test]
    fn reorg_reuses_a_verified_prefix_snapshot_without_old_bodies() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        for height in 1..=3 {
            state.connect_block(mine_block(&state, height)).unwrap();
        }
        state.persist_snapshot().unwrap();
        let prefix_tip = state.best_hash();
        let side_four = mine_block_from_header(state.header(3).unwrap(), 4, 71);
        let side_five = mine_block_from_header(&side_four.header, 5, 72);
        let side_four_hash = side_four.block_hash();
        let side_five_hash = side_five.block_hash();
        state.store.insert(&side_four).unwrap();
        state.store.insert(&side_five).unwrap();
        state.index_all_transactions(&side_four, 4);
        state.index_all_transactions(&side_five, 5);
        let prefix_work = state.block_index[&prefix_tip].chain_work;
        let side_four_work = prefix_work + side_four.header.work();
        state.block_index.insert(
            side_four_hash,
            BlockNode {
                header: side_four.header,
                height: 4,
                chain_work: side_four_work,
            },
        );
        state.block_index.insert(
            side_five_hash,
            BlockNode {
                header: side_five.header,
                height: 5,
                chain_work: side_four_work + side_five.header.work(),
            },
        );
        let retained = [state.block_hash(0).unwrap(), side_four_hash, side_five_hash]
            .into_iter()
            .collect::<HashSet<_>>();
        state.store.prune(&retained, &retained).unwrap();
        assert!(!state.store.contains(&state.block_hash(1).unwrap()));
        assert!(!state.store.contains(&state.block_hash(3).unwrap()));

        state.activate_chain(side_five_hash).unwrap();
        assert_eq!(state.best_hash(), side_five_hash);
        assert_eq!(state.block_hash(3), Some(prefix_tip));
        assert_eq!(state.block_hash(4), Some(side_four_hash));
        assert_eq!(state.height(), 5);
    }

    #[test]
    fn invalidation_state_survives_restart_and_reconsideration() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        state.connect_block(mine_block(&state, 1)).unwrap();
        let second = mine_block(&state, 2);
        let second_hash = second.block_hash();
        state.connect_block(second).unwrap();
        state.invalidate_block(&second_hash).unwrap();
        assert_eq!(state.height(), 1);
        assert_eq!(state.best_header_tip().hash, state.best_hash());
        drop(state);

        let mut reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(reopened.height(), 1);
        assert_eq!(
            reopened
                .chain_tips()
                .into_iter()
                .find(|tip| tip.hash == second_hash)
                .map(|tip| tip.status),
            Some("invalid")
        );
        reopened.reconsider_block(&second_hash).unwrap();
        assert_eq!(reopened.height(), 2);
        assert_eq!(reopened.best_hash(), second_hash);
        assert_eq!(reopened.best_header_tip().hash, second_hash);
    }

    #[test]
    fn failed_reorg_replay_restores_the_all_transaction_index() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let genesis_hash = state.best_hash();
        let genesis = *state.header(0).unwrap();
        let side_one = mine_block_from_header(&genesis, 1, 51);
        let side_one_hash = side_one.block_hash();
        let mut invalid_side_two = mine_block_from_header(&side_one.header, 2, 52);
        invalid_side_two.txdata[0].output[0].value = Amount::MAX_MONEY;
        invalid_side_two.header.merkle_root = invalid_side_two.compute_merkle_root().unwrap();
        invalid_side_two.header.nonce = 0;
        while !invalid_side_two
            .header
            .target()
            .is_met_by(invalid_side_two.block_hash())
        {
            invalid_side_two.header.nonce = invalid_side_two.header.nonce.wrapping_add(1);
        }

        state.store.insert(&side_one).unwrap();
        state.store.insert(&invalid_side_two).unwrap();
        let genesis_work = state.block_index[&genesis_hash].chain_work;
        let side_one_work = genesis_work + side_one.header.work();
        state.block_index.insert(
            side_one_hash,
            BlockNode {
                header: side_one.header,
                height: 1,
                chain_work: side_one_work,
            },
        );
        state.block_index.insert(
            invalid_side_two.block_hash(),
            BlockNode {
                header: invalid_side_two.header,
                height: 2,
                chain_work: side_one_work + invalid_side_two.header.work(),
            },
        );

        let side_one_txid = side_one.txdata[0].compute_txid();
        let previous_location = TxLocation {
            block_hash: genesis_hash,
            height: 0,
            transaction_index: 0,
        };
        state
            .tx_index_all
            .insert(side_one_txid, previous_location.clone());
        assert!(state.activate_chain(invalid_side_two.block_hash()).is_err());
        assert_eq!(state.best_hash(), genesis_hash);
        assert_eq!(
            state.tx_index_all.get(&side_one_txid),
            Some(&previous_location)
        );
    }

    #[test]
    fn next_block_hash_only_reports_the_active_chain_successor() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let main_one = mine_block(&state, 1);
        let main_one_hash = main_one.block_hash();
        state.connect_block(main_one).unwrap();
        let main_two = mine_block(&state, 2);
        let main_two_hash = main_two.block_hash();
        state.connect_block(main_two).unwrap();
        let main_three = mine_block(&state, 3);
        let main_three_hash = main_three.block_hash();
        state.connect_block(main_three).unwrap();

        let genesis = *state.header(0).unwrap();
        let side_one = mine_block_from_header(&genesis, 1, 1);
        let side_one_hash = side_one.block_hash();
        state.connect_block(side_one).unwrap();
        let side_one_header = *state.block_index.get(&side_one_hash).unwrap();
        let side_two = mine_block_from_header(&side_one_header.header, 2, 2);
        let side_two_hash = side_two.block_hash();
        state.connect_block(side_two).unwrap();

        assert_eq!(
            state.next_block_hash(&state.network_genesis_hash()),
            Some(main_one_hash)
        );
        assert_eq!(state.next_block_hash(&main_one_hash), Some(main_two_hash));
        assert_eq!(state.next_block_hash(&main_three_hash), None);
        assert_eq!(state.next_block_hash(&side_one_hash), None);
        assert_eq!(state.next_block_hash(&side_two_hash), None);
    }

    #[test]
    fn chain_tips_keep_the_active_tip_when_a_header_only_fork_extends_it() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let side = mine_block(&state, 1);
        let side_hash = side.block_hash();
        state
            .accept_headers(std::slice::from_ref(&side.header))
            .unwrap();

        let tips = state.chain_tips();
        let active = tips
            .iter()
            .find(|tip| tip.status == "active")
            .expect("active tip is always reported");
        assert_eq!(active.hash, state.network_genesis_hash());
        let header_only = tips
            .iter()
            .find(|tip| tip.hash == side_hash)
            .expect("header-only fork is reported");
        assert_eq!(header_only.status, "headers-only");
        assert_eq!(header_only.branch_len, 1);
        assert!(!state.block_request_allowed(&side_hash, 30 * 24 * 60 * 60));
        assert!(
            state
                .headers_for_getheaders(&[], side_hash, 30 * 24 * 60 * 60)
                .is_none()
        );
    }

    #[test]
    fn invalidation_does_not_activate_a_header_only_fork() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let active = mine_block(&state, 1);
        let active_hash = active.block_hash();
        state.connect_block(active).unwrap();

        let genesis = *state.header(0).unwrap();
        let side_one = mine_block_from_header(&genesis, 1, 41);
        let side_two = mine_block_from_header(&side_one.header, 2, 42);
        state
            .accept_headers(&[side_one.header, side_two.header])
            .unwrap();

        let tip = state.invalidate_block(&active_hash).unwrap();
        assert_eq!(tip.hash, genesis.block_hash());
        assert_eq!(state.height(), 0);
        assert_eq!(
            state
                .chain_tips()
                .into_iter()
                .find(|candidate| candidate.hash == side_two.block_hash())
                .map(|candidate| candidate.status),
            Some("headers-only")
        );
    }

    #[test]
    fn precious_block_preference_survives_equal_work_reconsideration() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let main_one = mine_block(&state, 1);
        state.connect_block(main_one).unwrap();
        let main_two = mine_block(&state, 2);
        let main_two_hash = main_two.block_hash();
        state.connect_block(main_two).unwrap();

        let genesis = *state.header(0).unwrap();
        let side_one = mine_block_from_header(&genesis, 1, 31);
        let side_one_hash = side_one.block_hash();
        state.connect_block(side_one).unwrap();
        let side_one_header = *state.block_index.get(&side_one_hash).unwrap();
        let side_two = mine_block_from_header(&side_one_header.header, 2, 32);
        let side_two_hash = side_two.block_hash();
        state.connect_block(side_two).unwrap();

        state.precious_block(&side_two_hash).unwrap();
        assert_eq!(state.best_hash(), side_two_hash);
        state.invalidate_block(&side_one_hash).unwrap();
        assert_eq!(state.best_hash(), main_two_hash);
        // Core accepts preciousblock for a failed branch as a preference
        // update, but activation continues to ignore the invalid candidate.
        state.precious_block(&side_two_hash).unwrap();
        assert_eq!(state.best_hash(), main_two_hash);
        state.reconsider_block(&side_one_hash).unwrap();
        assert_eq!(state.best_hash(), side_two_hash);
    }

    #[test]
    fn precious_block_does_not_prefer_later_descendants() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let main_one = mine_block(&state, 1);
        state.connect_block(main_one).unwrap();
        let main_two = mine_block(&state, 2);
        let main_two_header = main_two.header;
        state.connect_block(main_two).unwrap();
        let main_two_hash = state.best_hash();

        let genesis = *state.header(0).unwrap();
        let side_one = mine_block_from_header(&genesis, 1, 51);
        let side_one_hash = side_one.block_hash();
        state.connect_block(side_one).unwrap();
        let side_one_header = *state.block_index.get(&side_one_hash).unwrap();
        state.precious_block(&side_one_hash).unwrap();
        assert_eq!(state.best_hash(), main_two_hash);
        assert!(!state.precious_blocks.contains_key(&side_one_hash));
        let side_two = mine_block_from_header(&side_one_header.header, 2, 52);
        let side_two_hash = side_two.block_hash();
        state.connect_block(side_two).unwrap();

        state.precious_block(&side_two_hash).unwrap();
        assert_eq!(state.best_hash(), side_two_hash);

        let main_three = mine_block_from_header(&main_two_header, 3, 53);
        let main_three_hash = main_three.block_hash();
        state.connect_block(main_three).unwrap();
        let side_two_header = *state.block_index.get(&side_two_hash).unwrap();
        let side_three = mine_block_from_header(&side_two_header.header, 3, 54);
        state.connect_block(side_three).unwrap();
        assert_eq!(state.best_hash(), main_three_hash);

        // Re-running activation must not inherit side_two's precious
        // preference onto side_three. Core compares the block's own
        // sequence ID, so main_three arrived first and remains preferred.
        state.reconsider_block(&side_two_hash).unwrap();
        assert_eq!(state.best_hash(), main_three_hash);
        assert_ne!(main_two_hash, main_three_hash);
    }

    #[test]
    fn equal_work_reconsideration_prefers_the_earlier_received_chain() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();

        let main_one = mine_block(&state, 1);
        let main_one_hash = main_one.block_hash();
        state.connect_block(main_one).unwrap();
        let main_two = mine_block(&state, 2);
        let main_two_hash = main_two.block_hash();
        state.connect_block(main_two).unwrap();

        let genesis = *state.header(0).unwrap();
        let side_one = mine_block_from_header(&genesis, 1, 1);
        let side_one_hash = side_one.block_hash();
        state.connect_block(side_one).unwrap();
        let side_one_header = *state.block_index.get(&side_one_hash).unwrap();
        let main_two_display_hash = main_two_hash.to_string();
        let side_two = (2u8..=u8::MAX)
            .map(|tag| mine_block_from_header(&side_one_header.header, 2, tag))
            .find(|block| block.block_hash().to_string() > main_two_display_hash)
            .expect("a side block with a higher display hash");
        let side_two_hash = side_two.block_hash();
        state.connect_block(side_two).unwrap();

        assert_eq!(state.best_hash(), main_two_hash);
        state.invalidate_block(&main_one_hash).unwrap();
        assert_eq!(state.best_hash(), side_two_hash);
        state.reconsider_block(&main_one_hash).unwrap();

        // Core's sequence-ID tie-break restores the chain that arrived first,
        // even though the side-chain hash is larger in display order.
        assert_eq!(state.best_hash(), main_two_hash);

        drop(state);
        let mut reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
        reopened.invalidate_block(&main_one_hash).unwrap();
        assert_eq!(reopened.best_hash(), side_two_hash);
        reopened.reconsider_block(&main_one_hash).unwrap();
        assert_eq!(reopened.best_hash(), main_two_hash);
    }

    #[test]
    fn rejects_invalid_transaction_on_a_side_chain() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let main_one = mine_block(&state, 1);
        state.connect_block(main_one).unwrap();
        let main_two = mine_block(&state, 2);
        state.connect_block(main_two).unwrap();

        let genesis = *state.header(0).unwrap();
        let mut side = mine_block_from_header(&genesis, 1, 99);
        side.txdata.push(Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(Txid::from_byte_array([42; 32]), 0),
                script_sig: Builder::new().push_int(1).into_script(),
                sequence: Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(1),
                script_pubkey: Builder::new().push_int(1).into_script(),
            }],
        });
        side.header.merkle_root = side.compute_merkle_root().unwrap();
        while !side.header.target().is_met_by(side.block_hash()) {
            side.header.nonce = side.header.nonce.wrapping_add(1);
        }
        let side_hash = side.block_hash();
        assert!(state.connect_block(side).is_err());
        assert!(!state.store.contains(&side_hash));
        assert_eq!(state.height(), 2);
    }

    #[test]
    fn rejects_transaction_input_total_above_max_money() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let first_outpoint = OutPoint::new(Txid::from_byte_array([1; 32]), 0);
        let second_outpoint = OutPoint::new(Txid::from_byte_array([2; 32]), 0);
        let half_money = Amount::MAX_MONEY.to_sat() / 2;
        for outpoint in [first_outpoint, second_outpoint] {
            state.utxos.insert(
                outpoint,
                UtxoEntry {
                    output: TxOut {
                        value: Amount::from_sat(half_money.saturating_add(1)),
                        script_pubkey: Builder::new().push_int(1).into_script(),
                    },
                    height: 0,
                    median_time_past: 0,
                    coinbase: false,
                },
            );
        }
        let mut block = mine_block(&state, 1);
        block.txdata.push(Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![
                TxIn {
                    previous_output: first_outpoint,
                    script_sig: ScriptBuf::new(),
                    sequence: Sequence::MAX,
                    witness: Witness::default(),
                },
                TxIn {
                    previous_output: second_outpoint,
                    script_sig: ScriptBuf::new(),
                    sequence: Sequence::MAX,
                    witness: Witness::default(),
                },
            ],
            output: vec![TxOut {
                value: Amount::MAX_MONEY,
                script_pubkey: Builder::new().push_int(1).into_script(),
            }],
        });
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        while !block.header.target().is_met_by(block.block_hash()) {
            block.header.nonce = block.header.nonce.wrapping_add(1);
        }
        assert!(state.connect_block(block).is_err());
        assert_eq!(state.height(), 0);
    }

    #[test]
    fn mempool_rejects_transaction_input_total_above_max_money() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let first_outpoint = OutPoint::new(Txid::from_byte_array([3; 32]), 0);
        let second_outpoint = OutPoint::new(Txid::from_byte_array([4; 32]), 0);
        let half_money = Amount::MAX_MONEY.to_sat() / 2;
        for outpoint in [first_outpoint, second_outpoint] {
            state.utxos.insert(
                outpoint,
                UtxoEntry {
                    output: TxOut {
                        value: Amount::from_sat(half_money.saturating_add(1)),
                        script_pubkey: Builder::new().push_int(1).into_script(),
                    },
                    height: 0,
                    median_time_past: 0,
                    coinbase: false,
                },
            );
        }
        let transaction = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![
                TxIn {
                    previous_output: first_outpoint,
                    script_sig: ScriptBuf::new(),
                    sequence: Sequence::MAX,
                    witness: Witness::default(),
                },
                TxIn {
                    previous_output: second_outpoint,
                    script_sig: ScriptBuf::new(),
                    sequence: Sequence::MAX,
                    witness: Witness::default(),
                },
            ],
            output: vec![TxOut {
                value: Amount::MAX_MONEY,
                script_pubkey: Builder::new().push_int(1).into_script(),
            }],
        };
        let mut mempool = Mempool::new(Network::Regtest);
        assert!(matches!(
            mempool.accept(transaction, &state),
            Err(crate::mempool::MempoolError::BadOutput)
        ));
    }

    #[test]
    fn queues_an_orphan_until_its_parent_arrives() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let parent = mine_block(&state, 1);
        let child = mine_block_from_header(&parent.header, 2, 7);
        let child_hash = child.block_hash();
        assert!(state.connect_block(child).is_err());
        assert!(!state.store.contains(&child_hash));
        state.connect_block(parent).unwrap();
        assert_eq!(state.best_hash(), child_hash);
        assert_eq!(state.height(), 2);
    }

    #[test]
    fn bounds_transient_orphan_blocks_without_persisting_them() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let genesis = genesis_block(Network::Regtest);
        let unknown_parent = BlockHash::from_byte_array([7; 32]);
        for nonce in 0..=MAX_ORPHAN_BLOCKS {
            let transaction = coinbase_transaction(
                1,
                validation::block_subsidy_for_network(Network::Regtest, 1),
                u8::try_from(nonce).unwrap(),
            );
            let mut block = Block {
                header: Header {
                    version: BlockVersion::from_consensus(4),
                    prev_blockhash: unknown_parent,
                    merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                    time: genesis.header.time + 1,
                    bits: genesis.header.bits,
                    nonce: u32::try_from(nonce).unwrap(),
                },
                txdata: vec![transaction],
            };
            block.header.merkle_root = block.compute_merkle_root().unwrap();
            assert!(state.connect_block(block).is_err());
        }
        assert_eq!(
            state
                .orphans
                .values()
                .map(|children| children.len())
                .sum::<usize>(),
            MAX_ORPHAN_BLOCKS
        );
        assert_eq!(state.store.len(), 1);
    }

    #[test]
    fn indexes_headers_before_full_blocks_arrive() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let parent = mine_block(&state, 1);
        let child = mine_block_from_header(&parent.header, 2, 9);
        let hashes = state
            .accept_headers(&[parent.header, child.header])
            .unwrap();
        assert_eq!(hashes, vec![parent.block_hash(), child.block_hash()]);
        assert_eq!(state.block_height_by_hash(&child.block_hash()), Some(2));
        assert_eq!(state.blocks_ahead_of_tip(), Some(2));
        drop(state);
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(state.height(), 0);
        assert_eq!(
            state.best_header_tip().hash,
            child.block_hash(),
            "header-only index should survive a restart"
        );
        assert_eq!(state.blocks_ahead_of_tip(), Some(2));
        state.connect_block(parent).unwrap();
        state.connect_block(child).unwrap();
        assert_eq!(state.height(), 2);
        assert_eq!(state.blocks_ahead_of_tip(), None);
    }

    #[test]
    fn stores_a_block_body_when_only_its_parent_header_is_known() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let parent = mine_block(&state, 1);
        let child = mine_block_from_header(&parent.header, 2, 13);
        let child_hash = child.block_hash();

        state.accept_headers(&[parent.header]).unwrap();
        assert!(state.connect_block(child).is_err());
        assert!(state.store.contains(&child_hash));
        assert_eq!(state.block_height_by_hash(&child_hash), Some(2));

        state.connect_block(parent).unwrap();
        assert_eq!(state.best_hash(), child_hash);
    }

    #[test]
    fn equal_work_headers_keep_the_first_received_header_tip() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let genesis = *state.header(0).unwrap();
        let first = mine_block_from_header(&genesis, 1, 1);
        let first_hash = first.block_hash();
        let first_display_hash = first_hash.to_string();
        let second = (2u8..=u8::MAX)
            .map(|tag| mine_block_from_header(&genesis, 1, tag))
            .find(|block| block.block_hash().to_string() > first_display_hash)
            .expect("a later header with a higher display hash");
        let second_hash = second.block_hash();

        state.accept_headers(&[first.header]).unwrap();
        state.accept_headers(&[second.header]).unwrap();

        assert_eq!(
            state.block_index[&first_hash].chain_work,
            state.block_index[&second_hash].chain_work
        );
        assert_eq!(state.best_header_tip().hash, first_hash);
    }

    #[test]
    fn rejects_outdated_versions_during_header_sync() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let parent = mine_block(&state, 1);
        let mut stale = mine_block_from_header(&parent.header, 2, 11);
        stale.header.version = BlockVersion::ONE;
        stale.header.nonce = 0;
        while !stale.header.target().is_met_by(stale.block_hash()) {
            stale.header.nonce = stale.header.nonce.wrapping_add(1);
        }
        state.accept_headers(&[parent.header]).unwrap();
        assert!(state.accept_headers(&[stale.header]).is_err());
    }

    #[test]
    fn header_sync_rejects_invalidated_branches() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let parent = mine_block(&state, 1);
        let child = mine_block_from_header(&parent.header, 2, 12);

        state.accept_headers(&[parent.header]).unwrap();
        state.invalidate_block(&parent.block_hash()).unwrap();

        assert!(state.accept_headers(&[parent.header]).is_err());
        assert!(state.accept_headers(&[child.header]).is_err());
        assert!(state.block_height_by_hash(&child.block_hash()).is_none());
    }

    #[test]
    fn duplicate_side_block_bodies_are_not_reprocessed() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        state.connect_block(mine_block(&state, 1)).unwrap();
        state.connect_block(mine_block(&state, 2)).unwrap();

        let genesis = *state.header(0).unwrap();
        let side = mine_block_from_header(&genesis, 1, 77);
        state.connect_block(side.clone()).unwrap();
        let stored_bytes = state.store.data_size().unwrap();
        let tip = state.best_hash();

        state.connect_block(side).unwrap();

        assert_eq!(state.best_hash(), tip);
        assert_eq!(state.store.data_size().unwrap(), stored_bytes);
    }

    #[test]
    fn rejects_a_nonfinal_coinbase_transaction() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let mut block = mine_block(&state, 1);
        block.txdata[0].lock_time = LockTime::from_consensus(2);
        block.txdata[0].input[0].sequence = Sequence::ZERO;
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        block.header.nonce = 0;
        while !block.header.target().is_met_by(block.block_hash()) {
            block.header.nonce = block.header.nonce.wrapping_add(1);
        }
        assert!(state.connect_block(block).is_err());
        assert_eq!(state.height(), 0);
    }

    #[test]
    fn replays_known_child_after_parent_block_arrives() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let parent = mine_block(&state, 1);
        let child = mine_block_from_header(&parent.header, 2, 10);
        state
            .accept_headers(&[parent.header, child.header])
            .unwrap();
        assert!(state.connect_block(child).is_err());
        assert_eq!(state.height(), 0);
        state.connect_block(parent).unwrap();
        assert_eq!(state.height(), 2);
    }

    #[test]
    fn accepts_transactions_spending_outputs_created_in_the_same_block() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        state.configure_txospender_index(true).unwrap();
        let mut funding_block = None;
        for height in 1..=100 {
            let block = mine_block(&state, height);
            if height == 1 {
                funding_block = Some(block.clone());
            }
            state.connect_block(block).unwrap();
        }
        let funding = funding_block.expect("funding block");
        let funding_outpoint = OutPoint::new(funding.txdata[0].compute_txid(), 0);
        let first = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: funding_outpoint,
                script_sig: Builder::new().push_int(1).into_script(),
                sequence: Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(4_000_000_000),
                script_pubkey: Builder::new().push_int(1).into_script(),
            }],
        };
        let first_txid = first.compute_txid();
        let second = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(first_txid, 0),
                script_sig: Builder::new().push_int(1).into_script(),
                sequence: Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(3_000_000_000),
                script_pubkey: Builder::new().push_int(1).into_script(),
            }],
        };
        let second_txid = second.compute_txid();
        state.persist_snapshot().unwrap();
        let expected_before_spend = state.load_utxo_map_from_store().unwrap();
        let previous = *state.header(100).expect("height 100 header");
        let mut block = Block {
            header: Header {
                version: BlockVersion::from_consensus(4),
                prev_blockhash: previous.block_hash(),
                merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                time: previous.time + 1,
                bits: previous.bits,
                nonce: 0,
            },
            txdata: vec![coinbase_transaction(101, 7_000_000_000, 11), first, second],
        };
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        while !block.header.target().is_met_by(block.block_hash()) {
            block.header.nonce = block.header.nonce.wrapping_add(1);
        }
        let block_hash = block.block_hash();
        state.connect_block(block).unwrap();
        assert_eq!(state.height(), 101);
        assert!(state.utxo(&OutPoint::new(first_txid, 0)).is_none());
        let replayed = state
            .replay_utxos_for_block(state.block_hash(100).unwrap(), false)
            .unwrap()
            .expect("active historical UTXO state");
        assert_eq!(replayed, expected_before_spend);
        assert_eq!(
            state.block_fee_stats(&block_hash).unwrap(),
            Some(BlockFeeStats {
                total_fee_sat: 2_000_000_000,
                transaction_fees_sat: vec![1_000_000_000, 1_000_000_000],
                spent_outputs: vec![
                    TxOut {
                        value: Amount::from_sat(5_000_000_000),
                        script_pubkey: Builder::new().push_int(1).into_script(),
                    },
                    TxOut {
                        value: Amount::from_sat(4_000_000_000),
                        script_pubkey: Builder::new().push_int(1).into_script(),
                    },
                ],
            })
        );
        let samples = state.block_fee_samples(&block_hash).unwrap().unwrap();
        assert_eq!(samples.len(), 2);
        assert!(
            samples
                .iter()
                .all(|(fee, vsize)| *fee == 1_000_000_000 && *vsize > 0)
        );
        assert_eq!(
            state.estimate_fee_rate_sat_per_kvb(1, false).unwrap(),
            Some(
                samples[0]
                    .0
                    .saturating_mul(1_000)
                    .checked_div(samples[0].1)
                    .unwrap()
            )
        );
        assert_eq!(
            state.spending_transaction(&funding_outpoint),
            Some((first_txid, 0, block_hash, 101))
        );
        let first_output = OutPoint::new(first_txid, 0);
        assert_eq!(
            state.spending_transaction(&first_output),
            Some((second_txid, 0, block_hash, 101))
        );
        state.persist_snapshot().unwrap();
        drop(state);
        let mut reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
        reopened.configure_txospender_index(true).unwrap();
        assert_eq!(
            reopened.spending_transaction(&funding_outpoint),
            Some((first_txid, 0, block_hash, 101))
        );
        assert_eq!(
            reopened.spending_transaction(&first_output),
            Some((second_txid, 0, block_hash, 101))
        );
    }

    fn mine_block_from_header(previous: &Header, height: u32, tag: u8) -> Block {
        let transaction = coinbase_transaction(
            height,
            validation::block_subsidy_for_network(Network::Regtest, height),
            tag,
        );
        let mut block = Block {
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

    fn coinbase_transaction(height: u32, value: u64, tag: u8) -> Transaction {
        Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::null(),
                script_sig: Builder::new()
                    .push_int(height as i64)
                    .push_slice([tag])
                    .push_slice([0u8])
                    .into_script(),
                sequence: Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(value),
                script_pubkey: Builder::new().push_int(1).into_script(),
            }],
        }
    }
}
