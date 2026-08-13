//! Active-chain state, UTXO application, and Electrum indexing.

use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use bitcoin::blockdata::constants::genesis_block;
use bitcoin::consensus::encode::serialize;
use bitcoin::hashes::{Hash, HashEngine};
use bitcoin::pow::{CompactTarget, Target, Work};
use bitcoin::{Amount, Block, BlockHash, Network, OutPoint, Script, Transaction, TxOut, Txid};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::storage::BlockStore;
use crate::validation::{self, ValidationError};

const COINBASE_MATURITY: u32 = 100;
const DIFFICULTY_INTERVAL: u32 = 2016;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UtxoEntry {
    pub output: TxOut,
    pub height: u32,
    pub coinbase: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TxLocation {
    pub block_hash: BlockHash,
    pub height: u32,
    pub transaction_index: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
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

#[derive(Clone, Copy, Debug)]
struct BlockNode {
    header: bitcoin::block::Header,
    height: u32,
    chain_work: Work,
}

#[derive(Serialize, Deserialize)]
struct ChainMetadata {
    active_chain: Vec<String>,
}

pub struct ChainState {
    pub network: Network,
    data_dir: PathBuf,
    pub store: BlockStore,
    active_chain: Vec<BlockHash>,
    headers: Vec<bitcoin::block::Header>,
    block_index: HashMap<BlockHash, BlockNode>,
    utxos: HashMap<OutPoint, UtxoEntry>,
    tx_index: HashMap<Txid, TxLocation>,
    history: HashMap<String, Vec<HistoryEntry>>,
}

impl ChainState {
    pub fn open(network: Network, data_dir: impl AsRef<Path>) -> Result<Self> {
        let data_dir = data_dir.as_ref().to_owned();
        fs::create_dir_all(&data_dir)
            .with_context(|| format!("creating chain data directory {}", data_dir.display()))?;
        let mut store = BlockStore::open(data_dir.join("blocks"))?;
        let genesis = genesis_block(network);
        let genesis_hash = genesis.block_hash();
        if !store.contains(&genesis_hash) {
            store.insert(&genesis)?;
        }

        let metadata_path = data_dir.join("chainstate.json");
        let active_chain = if metadata_path.exists() {
            let bytes = fs::read(&metadata_path)
                .with_context(|| format!("reading {}", metadata_path.display()))?;
            let metadata: ChainMetadata = serde_json::from_slice(&bytes)
                .with_context(|| format!("decoding {}", metadata_path.display()))?;
            metadata
                .active_chain
                .into_iter()
                .map(|hash| {
                    hash.parse()
                        .with_context(|| format!("invalid block hash {hash}"))
                })
                .collect::<Result<Vec<BlockHash>>>()?
        } else {
            vec![genesis_hash]
        };
        if active_chain.first().copied() != Some(genesis_hash) {
            bail!("chainstate does not start at the configured network genesis block");
        }

        let mut blocks = Vec::with_capacity(active_chain.len());
        for hash in &active_chain {
            let block = store
                .get(hash)?
                .with_context(|| format!("active block {hash} is missing from block store"))?;
            blocks.push(block);
        }

        let mut state = Self {
            network,
            data_dir,
            store,
            active_chain: Vec::new(),
            headers: Vec::new(),
            block_index: HashMap::new(),
            utxos: HashMap::new(),
            tx_index: HashMap::new(),
            history: HashMap::new(),
        };
        state.initialize_genesis(&blocks[0])?;
        for block in blocks.iter().skip(1) {
            state.connect_block_internal(block, false)?;
        }
        if state.active_chain != active_chain {
            bail!("chainstate metadata does not match replayed active chain");
        }
        state.rebuild_block_index()?;
        if !metadata_path.exists() {
            state.persist_metadata()?;
        }
        Ok(state)
    }

    pub fn tip(&self) -> ChainTip {
        let mut headers = self.headers.iter();
        let mut work = headers.next().expect("genesis header exists").work();
        for header in headers {
            work = work + header.work();
        }
        ChainTip {
            hash: *self.active_chain.last().expect("genesis is always active"),
            height: self.height(),
            work,
        }
    }

    pub fn height(&self) -> u32 {
        self.active_chain.len().saturating_sub(1) as u32
    }

    pub fn best_hash(&self) -> BlockHash {
        self.tip().hash
    }

    pub fn is_active_block(&self, hash: &BlockHash) -> bool {
        self.active_chain.contains(hash)
    }

    pub fn header(&self, height: u32) -> Option<&bitcoin::block::Header> {
        self.headers.get(height as usize)
    }

    pub fn block_hash(&self, height: u32) -> Option<BlockHash> {
        self.active_chain.get(height as usize).copied()
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
        self.headers[start..stop.min(self.headers.len())]
            .iter()
            .take(2_000)
            .copied()
            .collect()
    }

    pub fn block(&mut self, hash: &BlockHash) -> Result<Option<Block>> {
        self.store.get(hash)
    }

    pub fn transaction(&mut self, txid: &Txid) -> Result<Option<(Transaction, TxLocation)>> {
        let Some(location) = self.tx_index.get(txid).cloned() else {
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

    pub fn get_history(&self, script_hash: &str) -> Vec<HistoryEntry> {
        self.history.get(script_hash).cloned().unwrap_or_default()
    }

    pub fn script_hashes(&self) -> Vec<String> {
        self.history.keys().cloned().collect()
    }

    pub fn get_utxos(&self, script_hash: &str) -> Vec<(OutPoint, UtxoEntry)> {
        self.utxos
            .iter()
            .filter(|(_, entry)| electrum_script_hash(&entry.output.script_pubkey) == script_hash)
            .map(|(outpoint, entry)| (*outpoint, entry.clone()))
            .collect()
    }

    pub fn utxo(&self, outpoint: &OutPoint) -> Option<&UtxoEntry> {
        self.utxos.get(outpoint)
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
        let mut digest = Sha256::digest(input.as_bytes()).to_vec();
        digest.reverse();
        Some(hex::encode(digest))
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
        if self.active_chain.contains(&hash) {
            return Ok(self.tip());
        }
        let parent_hash = block.header.prev_blockhash;
        let Some(parent) = self.block_index.get(&parent_hash).copied() else {
            self.store.insert(&block)?;
            bail!("block {} has an unknown parent {}", hash, parent_hash);
        };
        if parent_hash == self.best_hash() {
            self.connect_block_internal(&block, true)?;
            return Ok(self.tip());
        }

        let height = parent.height.saturating_add(1);
        validation::validate_header(
            self.network,
            &block.header,
            parent_hash,
            self.expected_target_for_parent(parent_hash, block.header.time),
            self.median_time_past_for_parent(parent_hash),
        )?;
        validation::validate_block_structure(
            &block,
            self.network,
            height,
            Amount::MAX_MONEY.to_sat(),
        )?;
        self.store.insert(&block)?;
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
        Ok(self.tip())
    }

    fn connect_block_internal(&mut self, block: &Block, persist: bool) -> Result<()> {
        let height = self.height().saturating_add(1);
        let previous = self.best_hash();
        let expected_target = self.expected_target(block.header.time);
        validation::validate_header(
            self.network,
            &block.header,
            previous,
            expected_target,
            self.median_time_past(),
        )?;
        validation::validate_block_structure(
            block,
            self.network,
            height,
            Amount::MAX_MONEY.to_sat(),
        )?;

        let mut spent = HashSet::new();
        let mut removals = Vec::new();
        let mut total_fees = 0u64;
        for transaction in block.txdata.iter().skip(1) {
            let txid = transaction.compute_txid();
            let mut input_total = 0u64;
            let mut previous_outputs = Vec::with_capacity(transaction.input.len());
            for input in &transaction.input {
                let outpoint = input.previous_output;
                if !spent.insert(outpoint) {
                    return Err(ValidationError::DuplicateInput(txid).into());
                }
                let Some(entry) = self.utxos.get(&outpoint).cloned() else {
                    return Err(ValidationError::MissingInput { outpoint }.into());
                };
                if entry.coinbase && height < entry.height.saturating_add(COINBASE_MATURITY) {
                    return Err(ValidationError::ImmatureCoinbase { outpoint }.into());
                }
                input_total = input_total
                    .checked_add(entry.output.value.to_sat())
                    .ok_or(ValidationError::InputTotalOverflow)?;
                previous_outputs.push(entry.output.clone());
                removals.push((outpoint, entry));
            }
            validation::validate_transaction_scripts(transaction, &previous_outputs)?;
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
        }
        let allowed_coinbase =
            validation::checked_money_add(validation::block_subsidy(height), total_fees)?;
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

        let hash = block.block_hash();
        if persist {
            self.store.insert(block)?;
        }
        for (outpoint, _) in &removals {
            self.utxos.remove(outpoint);
        }
        for (transaction_index, transaction) in block.txdata.iter().enumerate() {
            let txid = transaction.compute_txid();
            let mut affected_scripts = HashSet::new();
            for input in &transaction.input {
                if let Some(entry) =
                    self.lookup_spent_entry(block, input.previous_output, &spent, &removals)
                {
                    affected_scripts.insert(electrum_script_hash(&entry.output.script_pubkey));
                }
            }
            for (output_index, output) in transaction.output.iter().enumerate() {
                let outpoint = OutPoint::new(txid, output_index as u32);
                self.utxos.insert(
                    outpoint,
                    UtxoEntry {
                        output: output.clone(),
                        height,
                        coinbase: transaction_index == 0,
                    },
                );
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
        }
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
        Ok(())
    }

    fn activate_chain(&mut self, tip_hash: BlockHash) -> Result<()> {
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
        let old_tx_index = self.tx_index.clone();
        let old_history = self.history.clone();
        self.active_chain.clear();
        self.headers.clear();
        self.utxos.clear();
        self.tx_index.clear();
        self.history.clear();
        let replay = (|| -> Result<()> {
            self.initialize_genesis(&blocks[0])?;
            for block in blocks.iter().skip(1) {
                self.connect_block_internal(block, false)?;
            }
            self.persist_metadata()
        })();
        if let Err(error) = replay {
            self.active_chain = old_active_chain;
            self.headers = old_headers;
            self.utxos = old_utxos;
            self.tx_index = old_tx_index;
            self.history = old_history;
            return Err(error);
        }
        Ok(())
    }

    fn index_transactions(&mut self, block: &Block, height: u32) {
        for (transaction_index, transaction) in block.txdata.iter().enumerate() {
            let txid = transaction.compute_txid();
            let mut scripts = HashSet::new();
            for (output_index, output) in transaction.output.iter().enumerate() {
                let outpoint = OutPoint::new(txid, output_index as u32);
                self.utxos.insert(
                    outpoint,
                    UtxoEntry {
                        output: output.clone(),
                        height,
                        coinbase: transaction_index == 0,
                    },
                );
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
        }
    }

    fn add_history(&mut self, script_hash: &str, entry: HistoryEntry) {
        let history = self.history.entry(script_hash.to_owned()).or_default();
        if history.last() != Some(&entry) {
            history.push(entry);
        }
    }

    fn lookup_spent_entry(
        &self,
        _block: &Block,
        outpoint: OutPoint,
        _spent: &HashSet<OutPoint>,
        removals: &[(OutPoint, UtxoEntry)],
    ) -> Option<UtxoEntry> {
        removals
            .iter()
            .find(|(candidate, _)| *candidate == outpoint)
            .map(|(_, entry)| entry.clone())
    }

    fn expected_target(&self, candidate_time: u32) -> Target {
        self.expected_target_for_parent(self.best_hash(), candidate_time)
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
        CompactTarget::from_next_work_required(previous.bits, timespan, params).into()
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
        };
        let bytes = serde_json::to_vec_pretty(&metadata)?;
        let path = self.data_dir.join("chainstate.json");
        let temp = self.data_dir.join("chainstate.json.tmp");
        fs::write(&temp, bytes)?;
        fs::rename(temp, path)?;
        Ok(())
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
    }

    #[test]
    fn connects_and_replays_regtest_blocks() {
        let directory = tempfile::tempdir().unwrap();
        let mut state = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let first = mine_block(&state, 1);
        let first_hash = first.block_hash();
        state.connect_block(first).unwrap();
        let second = mine_block(&state, 2);
        state.connect_block(second).unwrap();
        assert_eq!(state.height(), 2);
        assert_eq!(state.best_hash(), state.block_hash(2).unwrap());
        drop(state);
        let reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(reopened.height(), 2);
        assert_eq!(reopened.block_hash(1), Some(first_hash));
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
        state.connect_block(main_one).unwrap();
        let main_two = mine_block(&state, 2);
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

        drop(state);
        let reopened = ChainState::open(Network::Regtest, directory.path()).unwrap();
        assert_eq!(reopened.best_hash(), side_three_hash);
        assert_eq!(reopened.block_hash(1), Some(side_one_hash));
    }

    fn mine_block_from_header(previous: &Header, height: u32, tag: u8) -> Block {
        let transaction = Transaction {
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
                value: Amount::from_sat(5_000_000_000),
                script_pubkey: bitcoin::ScriptBuf::new(),
            }],
        };
        let mut block = Block {
            header: Header {
                version: BlockVersion::TWO,
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
}
