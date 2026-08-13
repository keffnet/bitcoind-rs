//! In-memory transaction admission and relay pool.

use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::Path;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use anyhow::{Context, Result};
use bitcoin::{Amount, Network, OutPoint, Transaction, Txid, Wtxid};
use serde::{Deserialize, Serialize};

use crate::chain::ChainState;
use crate::validation::{self, ValidationError};

const DEFAULT_MAX_MEMPOOL_BYTES: usize = 300 * 1024 * 1024;
const MIN_RELAY_SAT_PER_VBYTE: u64 = 1;
const MEMPOOL_EXPIRY: Duration = Duration::from_secs(14 * 24 * 60 * 60);

#[derive(Deserialize, Serialize)]
struct DiskMempoolEntry {
    transaction: Transaction,
    added_at: u64,
}

#[derive(Clone, Debug)]
pub struct MempoolEntry {
    pub transaction: Transaction,
    pub fee_sat: u64,
    pub vsize: u64,
    pub added_at: u64,
}

#[derive(Clone)]
pub struct Mempool {
    pub network: Network,
    max_bytes: usize,
    bytes: usize,
    entries: HashMap<Txid, MempoolEntry>,
    spent: HashMap<OutPoint, Txid>,
    children: HashMap<Txid, HashSet<Txid>>,
    wtxids: HashMap<Wtxid, Txid>,
}

#[derive(Debug, thiserror::Error)]
pub enum MempoolError {
    #[error("coinbase transactions cannot enter the mempool")]
    Coinbase,
    #[error("transaction already exists in the mempool")]
    AlreadyPresent,
    #[error("transaction input is already spent by mempool transaction {0}")]
    Conflict(Txid),
    #[error("transaction {0} input is missing")]
    MissingInput(OutPoint),
    #[error("transaction contains a duplicate input")]
    DuplicateInput,
    #[error("transaction has no inputs or outputs")]
    Empty,
    #[error("transaction output value is invalid")]
    BadOutput,
    #[error("transaction spends more than its inputs")]
    NegativeFee,
    #[error("transaction fee rate is below the relay minimum")]
    FeeRate,
    #[error("transaction script validation failed: {0}")]
    Script(String),
    #[error("mempool size limit exceeded")]
    Full,
}

impl Mempool {
    pub fn new(network: Network) -> Self {
        Self {
            network,
            max_bytes: DEFAULT_MAX_MEMPOOL_BYTES,
            bytes: 0,
            entries: HashMap::new(),
            spent: HashMap::new(),
            children: HashMap::new(),
            wtxids: HashMap::new(),
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

    pub fn max_bytes(&self) -> usize {
        self.max_bytes
    }

    pub fn get(&self, txid: &Txid) -> Option<&MempoolEntry> {
        self.entries.get(txid)
    }

    pub fn get_by_wtxid(&self, wtxid: &Wtxid) -> Option<&MempoolEntry> {
        self.wtxids
            .get(wtxid)
            .and_then(|txid| self.entries.get(txid))
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

    pub fn transaction_order(&self) -> Vec<Txid> {
        let mut transaction_ids: Vec<Txid> = self.entries.keys().copied().collect();
        transaction_ids.sort_by_key(ToString::to_string);
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
        if !path.exists() {
            return Ok(());
        }
        let bytes = fs::read(path).with_context(|| format!("reading {}", path.display()))?;
        let entries: Vec<DiskMempoolEntry> = serde_json::from_slice(&bytes)
            .with_context(|| format!("decoding {}", path.display()))?;
        for entry in entries {
            let _ = self.accept_at(entry.transaction, chain, entry.added_at);
        }
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or(Duration::ZERO)
            .as_secs();
        self.clear_expired(now, MEMPOOL_EXPIRY);
        Ok(())
    }

    pub fn save_to_file(&self, path: &Path) -> Result<()> {
        let entries = self
            .transaction_order()
            .into_iter()
            .filter_map(|txid| self.entries.get(&txid))
            .map(|entry| DiskMempoolEntry {
                transaction: entry.transaction.clone(),
                added_at: entry.added_at,
            })
            .collect::<Vec<_>>();
        let bytes = serde_json::to_vec(&entries)?;
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
        let added_at = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or(Duration::ZERO)
            .as_secs();
        self.accept_at(transaction, chain, added_at)
    }

    fn accept_at(
        &mut self,
        transaction: Transaction,
        chain: &ChainState,
        added_at: u64,
    ) -> Result<Txid, MempoolError> {
        let txid = transaction.compute_txid();
        if self.entries.contains_key(&txid) {
            return Err(MempoolError::AlreadyPresent);
        }
        if transaction.is_coinbase() {
            return Err(MempoolError::Coinbase);
        }
        if transaction.input.is_empty() || transaction.output.is_empty() {
            return Err(MempoolError::Empty);
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
            previous_outputs.push(previous.clone());
        }
        validation::validate_transaction_finality(
            &transaction,
            chain.height() + 1,
            chain.median_time_past_value(),
            &previous_entries,
        )
        .map_err(|error| MempoolError::Script(error.to_string()))?;
        validation::validate_transaction_scripts(
            chain.network,
            chain.height() + 1,
            &transaction,
            &previous_outputs,
        )
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
        let vsize = transaction.vsize() as u64;
        if fee_sat < vsize.saturating_mul(MIN_RELAY_SAT_PER_VBYTE) {
            return Err(MempoolError::FeeRate);
        }
        let size = bitcoin::consensus::encode::serialize(&transaction).len();
        if self.bytes.saturating_add(size) > self.max_bytes {
            return Err(MempoolError::Full);
        }
        let entry = MempoolEntry {
            transaction,
            fee_sat,
            vsize,
            added_at,
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
        self.bytes += size;
        self.entries.insert(txid, entry);
        self.wtxids.insert(wtxid, txid);
        Ok(txid)
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
        self.spent.clear();
        self.children.clear();
        self.wtxids.clear();
        self.bytes = 0;
        for (added_at, transaction) in ordered {
            let _ = self.accept_at(transaction, chain, added_at);
        }
    }

    pub fn remove(&mut self, txid: &Txid) -> Option<MempoolEntry> {
        let entry = self.entries.remove(txid)?;
        self.wtxids.remove(&entry.transaction.compute_wtxid());
        let size = bitcoin::consensus::encode::serialize(&entry.transaction).len();
        self.bytes = self.bytes.saturating_sub(size);
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
        Some(entry)
    }

    pub fn remove_confirmed(&mut self, block: &bitcoin::Block) {
        for transaction in &block.txdata {
            let txid = transaction.compute_txid();
            self.remove(&txid);
        }
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
    fn persists_and_loads_an_empty_pool() {
        let directory = tempfile::tempdir().unwrap();
        let chain = ChainState::open(Network::Regtest, directory.path()).unwrap();
        let path = directory.path().join("mempool.json");
        let pool = Mempool::new(Network::Regtest);
        pool.save_to_file(&path).unwrap();
        let mut loaded = Mempool::new(Network::Regtest);
        loaded.load_from_file(&path, &chain).unwrap();
        assert!(loaded.is_empty());
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
}
