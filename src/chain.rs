//! Active-chain state, UTXO application, and Electrum indexing.

use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use bitcoin::bip158::{BlockFilter, FilterHeader};
use bitcoin::blockdata::constants::genesis_block;
use bitcoin::consensus::encode::serialize;
use bitcoin::hashes::{Hash, HashEngine};
use bitcoin::pow::{CompactTarget, Target, Work};
use bitcoin::{Amount, Block, BlockHash, Network, OutPoint, Script, Transaction, TxOut, Txid};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::muhash::MuHash3072;
use crate::storage::{BlockStore, FilterStore};
use crate::validation::{self, ValidationError};

const COINBASE_MATURITY: u32 = 100;
const DIFFICULTY_INTERVAL: u32 = 2016;
const BIP34_IMPLIES_BIP30_LIMIT: u32 = 1_983_702;
const SNAPSHOT_INTERVAL: u32 = 1_000;
const MAX_UNDO_CACHE_ENTRIES: usize = 1_024;
const MIN_BLOCKS_TO_KEEP: u32 = 288;
const MAX_ORPHAN_BLOCKS: usize = 128;

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct UtxoEntry {
    pub output: TxOut,
    pub height: u32,
    pub median_time_past: u32,
    pub coinbase: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct TxLocation {
    pub block_hash: BlockHash,
    pub height: u32,
    pub transaction_index: usize,
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UtxoSetStats {
    pub transactions: usize,
    pub outputs: usize,
    pub total_amount_sat: u64,
    pub bogo_size: u64,
    pub serialized_hash: Option<String>,
    pub muhash: Option<String>,
}

type SpentTransaction = (Txid, usize, BlockHash, u32);

struct BlockApplication {
    spent_entries: Vec<(OutPoint, UtxoEntry)>,
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
}

pub struct ChainState {
    pub network: Network,
    data_dir: PathBuf,
    signet_challenge: Option<Vec<u8>>,
    pub store: BlockStore,
    filter_store: FilterStore,
    active_chain: Vec<BlockHash>,
    headers: Vec<bitcoin::block::Header>,
    block_index: HashMap<BlockHash, BlockNode>,
    orphans: HashMap<BlockHash, Vec<Block>>,
    invalid_blocks: HashSet<BlockHash>,
    prune_height: Option<u32>,
    prune_mode: bool,
    prune_target_size: Option<u64>,
    utxos: HashMap<OutPoint, UtxoEntry>,
    utxos_by_script: HashMap<String, HashSet<OutPoint>>,
    tx_index: HashMap<Txid, TxLocation>,
    tx_index_all: HashMap<Txid, TxLocation>,
    history: HashMap<String, Vec<HistoryEntry>>,
    spent_by: HashMap<OutPoint, SpentTransaction>,
    precious_blocks: HashMap<BlockHash, u64>,
    precious_sequence: u64,
    basic_filter_cache: HashMap<BlockHash, (Vec<u8>, FilterHeader)>,
    block_undo_cache: HashMap<BlockHash, Vec<Vec<TxOut>>>,
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
        let data_dir = data_dir.as_ref().to_owned();
        fs::create_dir_all(&data_dir)
            .with_context(|| format!("creating chain data directory {}", data_dir.display()))?;
        let mut store = BlockStore::open(data_dir.join("blocks"))?;
        let filter_store = FilterStore::open(data_dir.join("filters"))?;
        let genesis = genesis_block(network);
        let genesis_hash = genesis.block_hash();
        if !store.contains(&genesis_hash) {
            store.insert(&genesis)?;
        }

        let metadata_path = data_dir.join("chainstate.json");
        let (active_chain, persisted_headers, invalid_blocks, prune_height) =
            if metadata_path.exists() {
                let bytes = fs::read(&metadata_path)
                    .with_context(|| format!("reading {}", metadata_path.display()))?;
                let metadata: ChainMetadata = serde_json::from_slice(&bytes)
                    .with_context(|| format!("decoding {}", metadata_path.display()))?;
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
                (
                    active_chain,
                    metadata.headers,
                    invalid_blocks,
                    metadata.prune_height,
                )
            } else {
                (vec![genesis_hash], Vec::new(), HashSet::new(), None)
            };
        if active_chain.first().copied() != Some(genesis_hash) {
            bail!("chainstate does not start at the configured network genesis block");
        }

        let mut state = Self {
            network,
            data_dir,
            signet_challenge: (network == Network::Signet).then(|| {
                signet_challenge
                    .map(ToOwned::to_owned)
                    .unwrap_or_else(validation::default_signet_challenge)
            }),
            store,
            filter_store,
            active_chain: Vec::new(),
            headers: Vec::new(),
            block_index: HashMap::new(),
            orphans: HashMap::new(),
            invalid_blocks,
            prune_height,
            prune_mode: false,
            prune_target_size: None,
            utxos: HashMap::new(),
            utxos_by_script: HashMap::new(),
            tx_index: HashMap::new(),
            tx_index_all: HashMap::new(),
            history: HashMap::new(),
            spent_by: HashMap::new(),
            precious_blocks: HashMap::new(),
            precious_sequence: 0,
            basic_filter_cache: HashMap::new(),
            block_undo_cache: HashMap::new(),
        };
        let snapshot = state.load_snapshot(&active_chain)?;
        let loaded_snapshot = snapshot.is_some();
        let snapshot_verified = snapshot.as_ref().is_some_and(|(_, verified)| *verified);
        if let Some((snapshot, _)) = snapshot {
            state.active_chain = active_chain.clone();
            state.headers = snapshot.headers;
            state.utxos = snapshot.utxos;
            state.rebuild_utxo_index();
            state.tx_index = snapshot.tx_index;
            state.tx_index_all = if snapshot.tx_index_all.is_empty() {
                state.tx_index.clone()
            } else {
                snapshot.tx_index_all
            };
            state.history = snapshot.history;
            state.prune_height = snapshot.prune_height.or(state.prune_height);
            let persisted_spent_by = snapshot.spent_by;
            let headers = state.headers.clone();
            state.index_active_headers(&headers)?;
            if let Some(spent_by) = persisted_spent_by {
                state.spent_by = spent_by;
                state.validate_persisted_spent_index()?;
            } else {
                state.rebuild_spent_index()?;
            }
        } else {
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
        if state.active_chain != active_chain {
            bail!("chainstate metadata does not match replayed active chain");
        }
        state.index_persisted_headers(&persisted_headers)?;
        state.rebuild_block_index()?;
        if state
            .active_chain
            .iter()
            .any(|hash| state.invalid_blocks.contains(hash))
        {
            let best_valid = state
                .best_valid_tip_hash()
                .context("invalidated chain has no valid alternative")?;
            state.activate_chain(best_valid)?;
        }
        if loaded_snapshot {
            let snapshot_utxos = state.utxos.clone();
            state.validate_snapshot_utxos(&snapshot_utxos)?;
            if !snapshot_verified {
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
        state.persist_metadata()?;
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

    pub fn height(&self) -> u32 {
        self.active_chain.len().saturating_sub(1) as u32
    }

    pub fn prune_height(&self) -> Option<u32> {
        self.prune_height
    }

    pub fn is_pruned(&self) -> bool {
        self.prune_mode || self.prune_height.is_some()
    }

    pub fn prune_target_size(&self) -> Option<u64> {
        self.prune_target_size
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
        Ok(())
    }

    /// Prune automatically when the configured block/undo target is
    /// exceeded. Keeping the recent block window is the same safety boundary
    /// used by manual pruning and leaves enough data for ordinary reorgs.
    pub fn maybe_auto_prune(&mut self) -> Result<bool> {
        let Some(target_size) = self.prune_target_size else {
            return Ok(false);
        };
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
        let tip_height = self.height();
        if tip_height < MIN_BLOCKS_TO_KEEP {
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
        let target_height = requested_height.min(tip_height - MIN_BLOCKS_TO_KEEP);
        if let Some(previous) = self.prune_height
            && target_height <= previous
        {
            return Ok(previous);
        }
        if target_height == 0 {
            return Ok(self.prune_height.unwrap_or_default());
        }

        let stored_hashes = self.store.hashes().copied().collect::<HashSet<_>>();
        let retained_blocks = self
            .block_index
            .iter()
            .filter_map(|(hash, node)| {
                (stored_hashes.contains(hash) && (node.height == 0 || node.height >= target_height))
                    .then_some(*hash)
            })
            .collect::<HashSet<_>>();
        self.store.prune(&retained_blocks, &retained_blocks)?;
        self.prune_height = Some(target_height);
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
            .max_by(|(left_hash, left), (right_hash, right)| {
                left.chain_work
                    .cmp(&right.chain_work)
                    .then_with(|| right_hash.to_string().cmp(&left_hash.to_string()))
            })
            .map(|(hash, node)| ChainTip {
                hash: *hash,
                height: node.height,
                work: node.chain_work,
            })
            .expect("genesis header is indexed")
    }

    pub fn chain_tips(&self) -> Vec<KnownChainTip> {
        let mut parents = HashSet::new();
        for node in self.block_index.values() {
            if node.height > 0 {
                parents.insert(node.header.prev_blockhash);
            }
        }
        let active: HashSet<BlockHash> = self.active_chain.iter().copied().collect();
        let mut tips = self
            .block_index
            .iter()
            .filter(|(hash, _)| !parents.contains(*hash))
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
                if self.invalid_blocks.contains(hash) || self.has_invalid_ancestor(*hash) {
                    return KnownChainTip {
                        hash: *hash,
                        height: node.height,
                        branch_len: 0,
                        status: "invalid",
                        work: node.chain_work,
                    };
                }
                let mut cursor = *hash;
                let mut branch_len: u32 = 0;
                while !active.contains(&cursor) {
                    let Some(current) = self.block_index.get(&cursor) else {
                        break;
                    };
                    cursor = current.header.prev_blockhash;
                    branch_len = branch_len.saturating_add(1);
                }
                KnownChainTip {
                    hash: *hash,
                    height: node.height,
                    branch_len,
                    status: "valid-fork",
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
        self.active_chain.contains(hash)
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
        if self.store.contains(hash) {
            Some("duplicate")
        } else {
            Some("duplicate-inconclusive")
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
        if best_valid != self.best_hash() {
            self.activate_chain(best_valid)?;
        }
        self.persist_metadata()?;
        Ok(self.tip())
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
            .filter(|candidate| self.is_descendant_or_self(candidate, hash))
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
        self.block_index
            .get(hash)
            .copied()
            .with_context(|| format!("block {hash} not found"))?;
        if self.has_invalid_ancestor(*hash) {
            bail!("cannot prefer an invalidated chain")
        }
        self.precious_sequence = self.precious_sequence.saturating_add(1);
        self.precious_blocks.insert(*hash, self.precious_sequence);
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

    pub fn active_headers(&self) -> &[bitcoin::block::Header] {
        &self.headers
    }

    pub fn header_by_hash(&self, hash: &BlockHash) -> Option<bitcoin::block::Header> {
        self.block_index.get(hash).map(|node| node.header)
    }

    pub fn headers_to_hash(&self, hash: &BlockHash) -> Option<Vec<bitcoin::block::Header>> {
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

    pub fn next_block_hash(&self, hash: &BlockHash) -> Option<BlockHash> {
        if let Some(position) = self
            .active_chain
            .iter()
            .position(|candidate| candidate == hash)
        {
            return self.active_chain.get(position + 1).copied();
        }
        self.block_index
            .iter()
            .filter(|(_, node)| node.header.prev_blockhash == *hash)
            .map(|(candidate, _)| *candidate)
            .min_by_key(ToString::to_string)
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
        Ok(self.store.get(hash)?.map(|block| block.txdata.len()))
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

    /// Build the BIP158 basic filter and filter header for every block from
    /// genesis through `hash`. Filters are computed on demand until a durable
    /// filter index is added.
    pub fn basic_filter_chain(
        &mut self,
        hash: &BlockHash,
    ) -> Result<Option<Vec<(BlockHash, BlockFilter, FilterHeader)>>> {
        let Some(headers) = self.headers_to_hash(hash) else {
            return Ok(None);
        };
        for header in &headers {
            let block_hash = header.block_hash();
            if !self.basic_filter_cache.contains_key(&block_hash)
                && let Some((content, filter_header)) = self.filter_store.get(&block_hash)?
            {
                self.basic_filter_cache
                    .insert(block_hash, (content, filter_header));
            }
        }
        if headers
            .iter()
            .all(|header| self.basic_filter_cache.contains_key(&header.block_hash()))
        {
            return Ok(Some(
                headers
                    .into_iter()
                    .map(|header| {
                        let block_hash = header.block_hash();
                        let (content, filter_header) = self
                            .basic_filter_cache
                            .get(&block_hash)
                            .expect("filter cache was checked above");
                        (block_hash, BlockFilter::new(content), *filter_header)
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
            self.basic_filter_cache
                .insert(block_hash, (filter.content.clone(), filter_header));
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
        if !self.block_index.contains_key(hash) {
            return Ok(None);
        }
        if let Some((content, filter_header)) = self.basic_filter_cache.get(hash) {
            return Ok(Some((content.clone(), *filter_header)));
        }
        if let Some((content, filter_header)) = self.filter_store.get(hash)? {
            self.basic_filter_cache
                .insert(*hash, (content.clone(), filter_header));
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
        let Some(stop_height) = self.block_height_by_hash(&stop_hash) else {
            return Ok(None);
        };
        if self.block_hash(stop_height) != Some(stop_hash) || start_height > stop_height {
            return Ok(None);
        }
        let end_height = start_height
            .saturating_add(u32::try_from(limit.saturating_sub(1)).unwrap_or(u32::MAX))
            .min(stop_height);
        let end_hash = self
            .block_hash(end_height)
            .ok_or_else(|| anyhow::anyhow!("compact filter height is out of range"))?;
        let previous_filter_header = if start_height == 0 {
            FilterHeader::all_zeros()
        } else {
            let previous_hash = self
                .block_hash(start_height - 1)
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
                    .block_hash(height)
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
        let mut outputs = self
            .replay_utxos_for_block(block.header.prev_blockhash, true)?
            .context("block undo parent UTXO state is unavailable")?;
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
        let mut locator = Vec::new();
        let mut height = self.height();
        let mut step = 1u32;
        loop {
            if let Some(hash) = self.block_hash(height) {
                locator.push(hash);
            }
            if height == 0 {
                break;
            }
            if locator.len() > 10 {
                step = step.saturating_mul(2);
            }
            height = height.saturating_sub(step);
        }
        locator
    }

    pub fn headers_after_locator(
        &self,
        locator: &[BlockHash],
        stop_hash: BlockHash,
    ) -> Vec<bitcoin::block::Header> {
        let start = locator
            .iter()
            .find_map(|hash| {
                self.active_chain
                    .iter()
                    .position(|candidate| candidate == hash)
            })
            .map_or(0, |position| position.saturating_add(1));
        let stop = if stop_hash == BlockHash::all_zeros() {
            self.active_chain.len()
        } else {
            self.active_chain
                .iter()
                .position(|hash| *hash == stop_hash)
                .map_or(self.active_chain.len(), |position| {
                    position.saturating_add(1)
                })
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
                hashes.push(hash);
                continue;
            }
            let parent_hash = header.prev_blockhash;
            let parent = self
                .block_index
                .get(&parent_hash)
                .copied()
                .with_context(|| format!("header {hash} has an unknown parent {parent_hash}"))?;
            validation::validate_bip94_timewarp(
                self.network,
                parent.height.saturating_add(1),
                header.time,
                parent.header.time,
            )?;
            validation::validate_block_version(
                self.network,
                parent.height.saturating_add(1),
                header.version.to_consensus(),
            )?;
            validation::validate_header(
                self.network,
                header,
                parent_hash,
                self.expected_target_for_parent(parent_hash, header.time),
                self.median_time_past_for_parent(parent_hash),
            )?;
            self.block_index.insert(
                hash,
                BlockNode {
                    header: *header,
                    height: parent.height.saturating_add(1),
                    chain_work: parent.chain_work + header.work(),
                },
            );
            inserted = true;
            hashes.push(hash);
        }
        Ok((hashes, inserted))
    }

    pub fn block(&mut self, hash: &BlockHash) -> Result<Option<Block>> {
        self.store.get(hash)
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

    pub fn transaction(&mut self, txid: &Txid) -> Result<Option<(Transaction, TxLocation)>> {
        let Some(location) = self
            .tx_index
            .get(txid)
            .or_else(|| self.tx_index_all.get(txid))
            .cloned()
        else {
            return Ok(None);
        };
        let Some(block) = self.store.get(&location.block_hash)? else {
            return Ok(None);
        };
        let Some(transaction) = block.txdata.get(location.transaction_index).cloned() else {
            bail!("transaction index is inconsistent with stored block");
        };
        Ok(Some((transaction, location)))
    }

    pub fn spending_transaction(
        &self,
        outpoint: &OutPoint,
    ) -> Option<(Txid, usize, BlockHash, u32)> {
        self.spent_by.get(outpoint).copied()
    }

    pub fn get_history(&self, script_hash: &str) -> Vec<HistoryEntry> {
        self.history.get(script_hash).cloned().unwrap_or_default()
    }

    pub fn script_hashes(&self) -> Vec<String> {
        self.history.keys().cloned().collect()
    }

    pub fn get_utxos(&self, script_hash: &str) -> Vec<(OutPoint, UtxoEntry)> {
        self.utxos_by_script
            .get(script_hash)
            .into_iter()
            .flat_map(|outpoints| outpoints.iter())
            .filter_map(|outpoint| {
                self.utxos
                    .get(outpoint)
                    .map(|entry| (*outpoint, entry.clone()))
            })
            .collect()
    }

    pub fn utxo(&self, outpoint: &OutPoint) -> Option<&UtxoEntry> {
        self.utxos.get(outpoint)
    }

    pub fn all_utxos(&self) -> impl Iterator<Item = (&OutPoint, &UtxoEntry)> {
        self.utxos.iter()
    }

    pub fn utxo_stats(&self) -> (usize, usize, u64) {
        let stats = self.utxo_statistics(false, false);
        (stats.transactions, stats.outputs, stats.total_amount_sat)
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
        calculate_utxo_statistics(&self.utxos, include_serialized_hash, include_muhash)
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
            self.utxos.clone()
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

    pub fn dump_utxo_set(&self, path: impl AsRef<Path>) -> Result<(u64, BlockHash, u32)> {
        let snapshot = self.current_snapshot();
        let bytes = serde_json::to_vec(&snapshot)?;
        fs::write(path.as_ref(), bytes)
            .with_context(|| format!("writing UTXO snapshot {}", path.as_ref().display()))?;
        Ok((self.utxos.len() as u64, self.best_hash(), self.height()))
    }

    pub fn load_utxo_set(&mut self, path: impl AsRef<Path>) -> Result<(u64, BlockHash, u32)> {
        let bytes = fs::read(path.as_ref())
            .with_context(|| format!("reading UTXO snapshot {}", path.as_ref().display()))?;
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
        self.rebuild_utxo_index();
        self.block_undo_cache.clear();
        self.persist_snapshot()?;
        Ok((self.utxos.len() as u64, self.best_hash(), self.height()))
    }

    fn validate_snapshot_utxos(&mut self, utxos: &HashMap<OutPoint, UtxoEntry>) -> Result<()> {
        let mut entries_by_block: HashMap<BlockHash, Vec<(&OutPoint, &UtxoEntry, TxLocation)>> =
            HashMap::new();
        for (outpoint, entry) in utxos {
            if entry.height > self.height() {
                bail!("UTXO snapshot contains an output from the future")
            }
            if entry.output.value > Amount::MAX_MONEY {
                bail!("UTXO snapshot contains an output above the money range")
            }
            let location = self
                .tx_index_all
                .get(&outpoint.txid)
                .or_else(|| self.tx_index.get(&outpoint.txid))
                .with_context(|| {
                    format!(
                        "UTXO snapshot references unknown transaction {}",
                        outpoint.txid
                    )
                })?;
            if location.height != entry.height
                || location.height as usize >= self.active_chain.len()
                || self.active_chain[location.height as usize] != location.block_hash
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
                                self.active_chain[location.height as usize - 1],
                            ))
                {
                    bail!("UTXO snapshot output metadata does not match the active chain")
                }
            }
        }
        Ok(())
    }

    pub fn verify_active_chain(&mut self, depth: u32) -> Result<()> {
        let _requested_depth = depth;
        self.replay_utxos_for_block(self.best_hash(), false)?
            .context("active chain UTXO replay did not reach the tip")?;
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

    fn validate_candidate_block_internal(&self, block: &Block, check_pow: bool) -> Result<()> {
        let parent_hash = block.header.prev_blockhash;
        if parent_hash != self.best_hash() {
            bail!("proposed block does not build on the active tip")
        }
        let height = self.height().saturating_add(1);
        let parent = self
            .block_index
            .get(&parent_hash)
            .expect("active tip is indexed");
        validation::validate_bip94_timewarp(
            self.network,
            height,
            block.header.time,
            parent.header.time,
        )?;
        let expected_target = self.expected_target_for_parent(parent_hash, block.header.time);
        let median_time_past = self.median_time_past_for_parent(parent_hash);
        if check_pow {
            validation::validate_header(
                self.network,
                &block.header,
                parent_hash,
                expected_target,
                median_time_past,
            )?;
        } else {
            validation::validate_header_without_pow(
                self.network,
                &block.header,
                parent_hash,
                expected_target,
                median_time_past,
            )?;
        }
        self.validate_block_structure(block, self.network, height, Amount::MAX_MONEY.to_sat())?;
        self.validate_block_transactions(block, height, &self.utxos, median_time_past)?;
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
        let history = self.history.get(script_hash)?;
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
        let Some(location) = self.tx_index.get(txid).cloned() else {
            return Ok(None);
        };
        let Some(block) = self.store.get(&location.block_hash)? else {
            return Ok(None);
        };
        let mut layer: Vec<Txid> = block.txdata.iter().map(Transaction::compute_txid).collect();
        let mut index = location.transaction_index;
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
        Ok(Some((branch, location.transaction_index, location.height)))
    }

    pub fn connect_block(&mut self, block: Block) -> Result<ChainTip> {
        let hash = block.block_hash();
        if self.has_invalid_ancestor(hash) {
            bail!("block {hash} is on an invalidated branch")
        }
        if self.active_chain.contains(&hash) {
            return Ok(self.tip());
        }
        let parent_hash = block.header.prev_blockhash;
        let Some(parent) = self.block_index.get(&parent_hash).copied() else {
            self.queue_orphan_block(parent_hash, block)?;
            bail!("block {} has an unknown parent {}", hash, parent_hash);
        };
        if self.has_invalid_ancestor(parent_hash) {
            bail!("block {hash} is on an invalidated branch")
        }
        // Headers can arrive before full block bodies. Keep a child pending
        // until its parent UTXO state is available so an unvalidated body
        // cannot influence chain selection.
        if !self.store.contains(&parent_hash) {
            self.queue_orphan_block(parent_hash, block)?;
            bail!("block {} has a parent whose full body is unavailable", hash)
        }
        if parent_hash == self.best_hash() {
            self.connect_block_internal(&block, true)?;
            self.process_orphans(hash);
            self.process_known_children(hash);
            return Ok(self.tip());
        }

        let height = parent.height.saturating_add(1);
        validation::validate_bip94_timewarp(
            self.network,
            height,
            block.header.time,
            parent.header.time,
        )?;
        validation::validate_header(
            self.network,
            &block.header,
            parent_hash,
            self.expected_target_for_parent(parent_hash, block.header.time),
            self.median_time_past_for_parent(parent_hash),
        )?;
        self.validate_block_structure(&block, self.network, height, Amount::MAX_MONEY.to_sat())?;
        let parent_utxos = self
            .utxos_for_block(parent_hash)?
            .context("side-chain parent UTXO state is unavailable")?;
        self.validate_block_transactions(
            &block,
            height,
            &parent_utxos,
            self.median_time_past_for_parent(parent_hash),
        )?;
        self.store.insert(&block)?;
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
        if chain_work > self.tip().work {
            self.activate_chain(hash)?;
        }
        self.process_orphans(hash);
        self.process_known_children(hash);
        Ok(self.tip())
    }

    fn process_orphans(&mut self, parent_hash: BlockHash) {
        let Some(children) = self.orphans.remove(&parent_hash) else {
            return;
        };
        for child in children {
            let _ = self.connect_block(child);
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

    fn process_known_children(&mut self, parent_hash: BlockHash) {
        let children: Vec<BlockHash> = self
            .block_index
            .iter()
            .filter_map(|(hash, node)| {
                (node.header.prev_blockhash == parent_hash && self.store.contains(hash))
                    .then_some(*hash)
            })
            .collect();
        for child_hash in children {
            let Ok(Some(child)) = self.store.get(&child_hash) else {
                continue;
            };
            let _ = self.connect_block(child);
        }
    }

    fn utxos_for_block(&mut self, hash: BlockHash) -> Result<Option<HashMap<OutPoint, UtxoEntry>>> {
        self.replay_utxos_for_block(hash, true)
    }

    fn replay_utxos_for_block(
        &mut self,
        hash: BlockHash,
        use_active_cache: bool,
    ) -> Result<Option<HashMap<OutPoint, UtxoEntry>>> {
        if use_active_cache && hash == self.best_hash() {
            return Ok(Some(self.utxos.clone()));
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
            validation::validate_bip94_timewarp(
                self.network,
                node.height,
                block.header.time,
                parent.header.time,
            )?;
            validation::validate_header(
                self.network,
                &block.header,
                parent_hash,
                self.expected_target_for_parent(parent_hash, block.header.time),
                self.median_time_past_for_parent(parent_hash),
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

    fn validate_block_transactions(
        &self,
        block: &Block,
        height: u32,
        utxos: &HashMap<OutPoint, UtxoEntry>,
        block_median_time_past: u32,
    ) -> Result<BlockApplication> {
        if self.enforce_bip30(height, block.block_hash(), block.header.prev_blockhash) {
            for transaction in &block.txdata {
                let txid = transaction.compute_txid();
                if transaction
                    .output
                    .iter()
                    .enumerate()
                    .any(|(vout, _)| utxos.contains_key(&OutPoint::new(txid, vout as u32)))
                {
                    bail!("block tries to overwrite an unspent transaction {txid}");
                }
            }
        }
        let mut spent = HashSet::new();
        let mut spent_entries = Vec::new();
        let mut created = HashMap::new();
        let mut total_fees = 0u64;
        let block_hash = block.block_hash();
        let sigop_flags =
            validation::script_flags_for_block_with_hash(self.network, height, Some(block_hash));
        let csv_active = height >= validation::buried_deployment_heights(self.network).csv;
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
        let mut sigop_cost = validation::transaction_sigop_cost(&block.txdata[0], &[], sigop_flags);
        if sigop_cost > validation::MAX_BLOCK_SIGOP_COST {
            return Err(ValidationError::TooManySigops.into());
        }
        for transaction in block.txdata.iter().skip(1) {
            let txid = transaction.compute_txid();
            let mut input_total = 0u64;
            let mut previous_outputs = Vec::with_capacity(transaction.input.len());
            let mut previous_entries = Vec::with_capacity(transaction.input.len());
            for input in &transaction.input {
                let outpoint = input.previous_output;
                if !spent.insert(outpoint) {
                    return Err(ValidationError::DuplicateInput(txid).into());
                }
                let Some(entry) = created
                    .get(&outpoint)
                    .or_else(|| utxos.get(&outpoint))
                    .cloned()
                else {
                    return Err(ValidationError::MissingInput { outpoint }.into());
                };
                if entry.coinbase && height < entry.height.saturating_add(COINBASE_MATURITY) {
                    return Err(ValidationError::ImmatureCoinbase { outpoint }.into());
                }
                input_total = input_total
                    .checked_add(entry.output.value.to_sat())
                    .ok_or(ValidationError::InputTotalOverflow)?;
                previous_outputs.push(entry.output.clone());
                previous_entries.push(entry.clone());
                spent_entries.push((outpoint, entry));
            }
            sigop_cost = sigop_cost.saturating_add(validation::transaction_sigop_cost(
                transaction,
                &previous_outputs,
                sigop_flags,
            ));
            if sigop_cost > validation::MAX_BLOCK_SIGOP_COST {
                return Err(ValidationError::TooManySigops.into());
            }
            validation::validate_transaction_finality(
                transaction,
                height,
                lock_time_cutoff,
                csv_active,
                &previous_entries,
            )?;
            validation::validate_transaction_scripts_at_time_with_block_hash(
                self.network,
                height,
                block.header.time,
                Some(block_hash),
                transaction,
                &previous_outputs,
            )?;
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
                .ok_or(ValidationError::InputTotalOverflow)?;
            for (output_index, output) in transaction.output.iter().enumerate() {
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
        let allowed_coinbase = validation::checked_money_add(
            validation::block_subsidy_for_network(self.network, height),
            total_fees,
        )?;
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
        Ok(BlockApplication { spent_entries })
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
        self.ancestor_hash(
            parent_hash,
            validation::buried_deployment_heights(self.network).bip34,
        )
        .map(|hash| hash.to_string() != expected_bip34_hash)
        .unwrap_or(true)
    }

    fn connect_block_internal(&mut self, block: &Block, persist: bool) -> Result<()> {
        let height = self.height().saturating_add(1);
        let previous = self.best_hash();
        let previous_node = self
            .block_index
            .get(&previous)
            .expect("active tip is indexed");
        validation::validate_bip94_timewarp(
            self.network,
            height,
            block.header.time,
            previous_node.header.time,
        )?;
        let expected_target = self.expected_target(block.header.time);
        validation::validate_header(
            self.network,
            &block.header,
            previous,
            expected_target,
            self.median_time_past(),
        )?;
        self.validate_block_structure(block, self.network, height, Amount::MAX_MONEY.to_sat())?;
        let block_median_time_past = self.median_time_past();
        let application =
            self.validate_block_transactions(block, height, &self.utxos, block_median_time_past)?;
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
        if persist {
            self.store.insert(block)?;
        }
        for (outpoint, _) in &application.spent_entries {
            self.remove_utxo(outpoint);
        }
        let spent_entries: HashMap<OutPoint, UtxoEntry> =
            application.spent_entries.into_iter().collect();
        let spent_outpoints: HashSet<OutPoint> = spent_entries.keys().copied().collect();
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
                if !spent_outpoints.contains(&outpoint) {
                    self.insert_utxo(
                        outpoint,
                        UtxoEntry {
                            output: output.clone(),
                            height,
                            median_time_past: block_median_time_past,
                            coinbase: transaction_index == 0,
                        },
                    );
                }
                affected_scripts.insert(electrum_script_hash(&output.script_pubkey));
            }
            for script_hash in affected_scripts {
                self.add_history(&script_hash, HistoryEntry { txid, height });
            }
            self.tx_index.insert(
                txid,
                TxLocation {
                    block_hash: hash,
                    height,
                    transaction_index,
                },
            );
            self.tx_index_all.insert(
                txid,
                TxLocation {
                    block_hash: hash,
                    height,
                    transaction_index,
                },
            );
        }
        self.index_block_spends(block, height);
        self.active_chain.push(hash);
        self.headers.push(block.header);
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
        if persist {
            self.persist_metadata()?;
            if self.height() % SNAPSHOT_INTERVAL == 0 {
                self.persist_snapshot()?;
            }
        }
        Ok(())
    }

    fn initialize_genesis(&mut self, genesis: &Block) -> Result<()> {
        if genesis.block_hash() != self.network_genesis_hash() {
            bail!("genesis block does not match network");
        }
        self.active_chain.push(genesis.block_hash());
        self.headers.push(genesis.header);
        self.block_index.insert(
            genesis.block_hash(),
            BlockNode {
                header: genesis.header,
                height: 0,
                chain_work: genesis.header.work(),
            },
        );
        self.index_transactions(genesis, 0);
        self.cache_basic_filter_for_block(genesis, &[], &FilterHeader::all_zeros())?;
        self.remember_block_undo(genesis.block_hash(), vec![Vec::new()]);
        self.store
            .insert_undo(genesis.block_hash(), &[Vec::new()])?;
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

    fn activate_chain(&mut self, tip_hash: BlockHash) -> Result<()> {
        if self.has_invalid_ancestor(tip_hash) {
            bail!("cannot activate an invalidated chain")
        }
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
        let blocks = path
            .iter()
            .map(|hash| self.store.get(hash))
            .collect::<Result<Vec<Option<Block>>>>()?
            .into_iter()
            .enumerate()
            .map(|(index, block)| {
                block.with_context(|| format!("candidate block {} is missing", path[index]))
            })
            .collect::<Result<Vec<Block>>>()?;

        let old_active_chain = self.active_chain.clone();
        let old_headers = self.headers.clone();
        let old_utxos = self.utxos.clone();
        let old_utxos_by_script = self.utxos_by_script.clone();
        let old_tx_index = self.tx_index.clone();
        let old_history = self.history.clone();
        let old_spent_by = self.spent_by.clone();
        let old_basic_filter_cache = self.basic_filter_cache.clone();
        let old_block_undo_cache = self.block_undo_cache.clone();
        self.active_chain.clear();
        self.headers.clear();
        self.utxos.clear();
        self.utxos_by_script.clear();
        self.tx_index.clear();
        self.history.clear();
        self.spent_by.clear();
        let replay = (|| -> Result<()> {
            self.initialize_genesis(&blocks[0])?;
            for block in blocks.iter().skip(1) {
                self.connect_block_internal(block, false)?;
            }
            self.persist_metadata()?;
            self.persist_snapshot()
        })();
        if let Err(error) = replay {
            self.active_chain = old_active_chain;
            self.headers = old_headers;
            self.utxos = old_utxos;
            self.utxos_by_script = old_utxos_by_script;
            self.tx_index = old_tx_index;
            self.history = old_history;
            self.spent_by = old_spent_by;
            self.basic_filter_cache = old_basic_filter_cache;
            self.block_undo_cache = old_block_undo_cache;
            return Err(error);
        }
        Ok(())
    }

    fn cache_basic_filter_for_block(
        &mut self,
        block: &Block,
        spent_entries: &[(OutPoint, UtxoEntry)],
        previous_filter_header: &FilterHeader,
    ) -> Result<()> {
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
        self.basic_filter_cache
            .insert(block.block_hash(), (filter.content, filter_header));
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
            .filter(|(hash, _)| !self.has_invalid_ancestor(**hash))
            .max_by(|(left_hash, left), (right_hash, right)| {
                left.chain_work
                    .cmp(&right.chain_work)
                    .then_with(|| {
                        self.precious_priority(left_hash)
                            .cmp(&self.precious_priority(right_hash))
                    })
                    .then_with(|| right_hash.to_string().cmp(&left_hash.to_string()))
            })
            .map(|(hash, _)| *hash)
    }

    fn precious_priority(&self, hash: &BlockHash) -> u64 {
        let mut priority = 0;
        let mut cursor = *hash;
        loop {
            priority = priority.max(self.precious_blocks.get(&cursor).copied().unwrap_or(0));
            let Some(node) = self.block_index.get(&cursor) else {
                break;
            };
            if node.height == 0 {
                break;
            }
            cursor = node.header.prev_blockhash;
        }
        priority
    }

    fn index_transactions(&mut self, block: &Block, height: u32) {
        for (transaction_index, transaction) in block.txdata.iter().enumerate() {
            let txid = transaction.compute_txid();
            let mut scripts = HashSet::new();
            for (output_index, output) in transaction.output.iter().enumerate() {
                let outpoint = OutPoint::new(txid, output_index as u32);
                if height != 0 {
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
            self.tx_index.insert(
                txid,
                TxLocation {
                    block_hash: block.block_hash(),
                    height,
                    transaction_index,
                },
            );
            self.tx_index_all.insert(
                txid,
                TxLocation {
                    block_hash: block.block_hash(),
                    height,
                    transaction_index,
                },
            );
        }
        self.index_block_spends(block, height);
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
            let location = self
                .tx_index_all
                .get(txid)
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

    fn insert_utxo(&mut self, outpoint: OutPoint, entry: UtxoEntry) {
        if self.utxos.contains_key(&outpoint) {
            self.remove_utxo(&outpoint);
        }
        let script_hash = electrum_script_hash(&entry.output.script_pubkey);
        self.utxos.insert(outpoint, entry);
        self.utxos_by_script
            .entry(script_hash)
            .or_default()
            .insert(outpoint);
    }

    fn remove_utxo(&mut self, outpoint: &OutPoint) -> Option<UtxoEntry> {
        let entry = self.utxos.remove(outpoint)?;
        let script_hash = electrum_script_hash(&entry.output.script_pubkey);
        if let Some(outpoints) = self.utxos_by_script.get_mut(&script_hash) {
            outpoints.remove(outpoint);
            if outpoints.is_empty() {
                self.utxos_by_script.remove(&script_hash);
            }
        }
        Some(entry)
    }

    fn rebuild_utxo_index(&mut self) {
        self.utxos_by_script.clear();
        for (outpoint, entry) in &self.utxos {
            self.utxos_by_script
                .entry(electrum_script_hash(&entry.output.script_pubkey))
                .or_default()
                .insert(*outpoint);
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
        network: Network,
        height: u32,
        expected_coinbase_value: u64,
    ) -> Result<validation::BlockValidationStats, ValidationError> {
        validation::validate_block_structure_with_signet(
            block,
            network,
            height,
            expected_coinbase_value,
            self.signet_challenge.as_deref(),
        )
    }

    fn expected_target_for_parent(&self, parent_hash: BlockHash, candidate_time: u32) -> Target {
        let parent_node = self
            .block_index
            .get(&parent_hash)
            .expect("parent is indexed");
        let height = parent_node.height.saturating_add(1);
        let previous = &parent_node.header;
        let params = self.network.params();
        if params.no_pow_retargeting {
            return previous.target();
        }
        if height % DIFFICULTY_INTERVAL != 0 {
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
                    if node.height % DIFFICULTY_INTERVAL == 0
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
            .ancestor_hash(parent_hash, height - DIFFICULTY_INTERVAL)
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
        while current_height > height {
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
        };
        let bytes = serde_json::to_vec_pretty(&metadata)?;
        let path = self.data_dir.join("chainstate.json");
        let temp = self.data_dir.join("chainstate.json.tmp");
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
        let Ok(snapshot) = serde_json::from_slice::<ChainSnapshot>(&bytes) else {
            return Ok(None);
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
        let Some(tip) = active_chain.last() else {
            return Ok(None);
        };
        if snapshot.tip != tip.to_string()
            || snapshot.headers.len() != active_chain.len()
            || snapshot
                .headers
                .iter()
                .zip(active_chain)
                .any(|(header, hash)| header.block_hash() != *hash)
        {
            return Ok(None);
        }
        Ok(Some((snapshot, verified)))
    }

    fn persist_snapshot(&self) -> Result<()> {
        let snapshot = self.current_snapshot();
        let bytes = serde_json::to_vec(&snapshot)?;
        let path = self.data_dir.join("chainstate.snapshot");
        let temp = self.data_dir.join("chainstate.snapshot.tmp");
        fs::write(&temp, &bytes)?;
        fs::rename(temp, path)?;
        self.persist_snapshot_checksum_bytes(&bytes)?;
        Ok(())
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

    fn current_snapshot(&self) -> ChainSnapshot {
        ChainSnapshot {
            tip: self.best_hash().to_string(),
            headers: self.headers.clone(),
            utxos: self.utxos.clone(),
            tx_index: self.tx_index.clone(),
            tx_index_all: self.tx_index_all.clone(),
            history: self.history.clone(),
            spent_by: Some(self.spent_by.clone()),
            prune_height: self.prune_height,
        }
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
                    self.accept_headers_internal(&[header])?;
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

fn calculate_utxo_statistics(
    utxos: &HashMap<OutPoint, UtxoEntry>,
    include_serialized_hash: bool,
    include_muhash: bool,
) -> UtxoSetStats {
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

    let (serialized_hash, muhash) = if include_serialized_hash {
        let mut entries: Vec<(&OutPoint, &UtxoEntry)> = utxos.iter().collect();
        entries.sort_by_key(|(outpoint, _)| (outpoint.txid.to_byte_array(), outpoint.vout));
        let mut serialized_engine = bitcoin::hashes::sha256d::Hash::engine();
        let mut muhash = include_muhash.then(MuHash3072::default);
        for (outpoint, entry) in entries {
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
        for (outpoint, entry) in utxos {
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
        outputs: utxos.len(),
        total_amount_sat,
        bogo_size,
        serialized_hash,
        muhash: muhash.map(|accumulator| accumulator.finalize()),
    }
}

fn snapshot_checksum(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
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
            if !spent_outpoints.contains(&outpoint) {
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
    }

    #[test]
    fn rejects_a_modified_unpruned_utxo_snapshot() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let first = mine_block(&state, 1);
        state.connect_block(first).unwrap();
        let path = directory.path().join("external.snapshot");
        state.dump_utxo_set(&path).unwrap();

        let bytes = fs::read(&path).unwrap();
        let mut snapshot: ChainSnapshot = serde_json::from_slice(&bytes).unwrap();
        let entry = snapshot.utxos.values_mut().next().unwrap();
        entry.output.value = Amount::from_sat(entry.output.value.to_sat().saturating_sub(1));
        fs::write(&path, serde_json::to_vec(&snapshot).unwrap()).unwrap();

        assert!(state.load_utxo_set(&path).is_err());
        assert_eq!(state.utxo_stats().2, 5_000_000_000);
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
        assert_eq!(state.prune(50).unwrap(), 12);
        assert!(!state.store.contains(&old_block_hash));
        assert_eq!(state.prune_height(), Some(12));
        let path = directory.path().to_owned();
        drop(state);
        let reopened = ChainState::open(Network::Regtest, &path).unwrap();
        assert_eq!(reopened.best_hash(), tip_hash);
        assert_eq!(reopened.height(), 300);
        assert_eq!(reopened.prune_height(), Some(12));
        assert!(!reopened.store.contains(&old_block_hash));
    }

    #[test]
    fn configured_pruning_reports_mode_and_target() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        state.configure_pruning(1).unwrap();
        assert!(state.is_pruned());
        assert_eq!(state.prune_target_size(), None);

        state.configure_pruning(550).unwrap();
        assert!(state.is_pruned());
        assert_eq!(state.prune_target_size(), Some(550 * 1024 * 1024));
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
        state.persist_snapshot().unwrap();
        drop(state);
        let reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(reopened.height(), 2);
        assert_eq!(reopened.block_hash(1), Some(first_hash));
        assert_eq!(reopened.utxos.len(), 2);
        assert_eq!(reopened.get_utxos(&script_hash).len(), 2);
        drop(reopened);
        let snapshot_path = directory.path().join("chainstate.snapshot");
        let bytes = fs::read(&snapshot_path).unwrap();
        let mut snapshot: ChainSnapshot = serde_json::from_slice(&bytes).unwrap();
        let entry = snapshot.utxos.values_mut().next().unwrap();
        entry.output.value = Amount::from_sat(entry.output.value.to_sat().saturating_sub(1));
        fs::write(&snapshot_path, serde_json::to_vec(&snapshot).unwrap()).unwrap();
        assert!(ChainState::open(Network::Regtest, directory.path()).is_err());
        fs::write(directory.path().join("chainstate.snapshot"), b"corrupt").unwrap();
        let replayed = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(replayed.height(), 2);
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
        state.reconsider_block(&side_one_hash).unwrap();
        assert_eq!(state.best_hash(), side_two_hash);
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
        drop(state);
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(state.height(), 0);
        assert_eq!(
            state.best_header_tip().hash,
            child.block_hash(),
            "header-only index should survive a restart"
        );
        state.connect_block(parent).unwrap();
        state.connect_block(child).unwrap();
        assert_eq!(state.height(), 2);
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
        let reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
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
