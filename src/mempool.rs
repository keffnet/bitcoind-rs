//! In-memory transaction admission and relay pool.

use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::Path;
use std::time::Duration;

use anyhow::{Context, Result};
use bitcoin::blockdata::script::Instruction;
use bitcoin::{Amount, Network, OutPoint, PublicKey, Script, Transaction, TxOut, Txid, Wtxid};
use serde::{Deserialize, Serialize};

use crate::chain::ChainState;
use crate::time;
use crate::validation::{self, ValidationError};

const DEFAULT_MAX_MEMPOOL_BYTES: usize = 300 * 1024 * 1024;
const MIN_RELAY_SAT_PER_VBYTE: u64 = 1;
const MEMPOOL_EXPIRY: Duration = Duration::from_secs(14 * 24 * 60 * 60);
const MAX_STANDARD_TX_WEIGHT: u64 = 400_000;
const MIN_STANDARD_TX_NONWITNESS_SIZE: usize = 65;
const MAX_STANDARD_SCRIPTSIG_SIZE: usize = 1_650;
const MAX_DATACARRIER_BYTES: usize = 100_000;
const DUST_RELAY_SAT_PER_KVB: u64 = 3_000;

/// Core's context-free package limits.
pub const MAX_PACKAGE_COUNT: usize = 25;
pub const MAX_PACKAGE_WEIGHT: u64 = 404_000;
/// Core's default cluster limits for the v31.1 mempool policy.
pub const MAX_CLUSTER_COUNT: usize = 64;
pub const MAX_CLUSTER_VSIZE: u64 = 101_000;
pub const MAX_DATACARRIER_SIZE: usize = MAX_DATACARRIER_BYTES;

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
    /// Active-chain height when the transaction entered the mempool.
    pub height: u32,
}

#[derive(Clone)]
pub struct Mempool {
    pub network: Network,
    max_bytes: usize,
    bytes: usize,
    sequence: u64,
    entries: HashMap<Txid, MempoolEntry>,
    spent: HashMap<OutPoint, Txid>,
    children: HashMap<Txid, HashSet<Txid>>,
    wtxids: HashMap<Wtxid, Txid>,
    priorities: HashMap<Txid, i64>,
}

#[derive(Debug, thiserror::Error)]
pub enum MempoolError {
    #[error("coinbase transactions cannot enter the mempool")]
    Coinbase,
    #[error("transaction already exists in the mempool")]
    AlreadyPresent,
    #[error("transaction input is already spent by mempool transaction {0}")]
    Conflict(Txid),
    #[error("conflicting transaction does not signal replaceability")]
    ReplacementNotSignaled,
    #[error("replacement transaction fee is too low")]
    ReplacementFee,
    #[error("replacement transaction spends an unconfirmed output outside the conflicts")]
    ReplacementUnconfirmedInput,
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
    #[error("transaction is non-standard: {0}")]
    NonStandard(String),
    #[error("mempool size limit exceeded")]
    Full,
    #[error("transaction cluster exceeds the mempool cluster limits")]
    ClusterLimit,
}

impl Mempool {
    pub fn new(network: Network) -> Self {
        Self {
            network,
            max_bytes: DEFAULT_MAX_MEMPOOL_BYTES,
            bytes: 0,
            sequence: 0,
            entries: HashMap::new(),
            spent: HashMap::new(),
            children: HashMap::new(),
            wtxids: HashMap::new(),
            priorities: HashMap::new(),
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

    pub fn sequence(&self) -> u64 {
        self.sequence
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

    pub fn prioritise(&mut self, txid: Txid, fee_delta: i64) {
        let delta = self.priorities.entry(txid).or_insert(0);
        *delta = delta.saturating_add(fee_delta);
        if *delta == 0 {
            self.priorities.remove(&txid);
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

    /// Return transactions in ancestor-package feerate order for block
    /// assembly. A package consists of an unselected transaction and all of
    /// its unselected ancestors. Packages are scored by effective fee
    /// (including prioritisation deltas) per weight, while the returned list
    /// remains topologically ordered.
    pub fn mining_order(&self, max_weight: u64, reserved_weight: u64) -> Vec<Txid> {
        let weight_limit = max_weight.saturating_sub(reserved_weight);
        let mut selected = HashSet::new();
        let mut ordered = Vec::new();
        let mut selected_weight = 0u64;

        while selected.len() < self.entries.len() {
            let mut best: Option<(Txid, HashSet<Txid>, u64, i128)> = None;
            for txid in self.entries.keys().copied() {
                if selected.contains(&txid) {
                    continue;
                }
                let mut package = HashSet::new();
                if !collect_mining_package(self, txid, &selected, &mut package, &mut HashSet::new())
                {
                    continue;
                }
                let package_weight = package
                    .iter()
                    .filter_map(|candidate| self.entries.get(candidate))
                    .map(|entry| entry.transaction.weight().to_wu())
                    .fold(0u64, u64::saturating_add);
                if selected_weight.saturating_add(package_weight) > weight_limit {
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
                let better = match &best {
                    None => true,
                    Some((best_txid, _, best_weight, best_fee)) => {
                        let left = package_fee.saturating_mul(i128::from(*best_weight));
                        let right = best_fee.saturating_mul(i128::from(package_weight));
                        left > right || (left == right && txid.to_string() < best_txid.to_string())
                    }
                };
                if better {
                    best = Some((txid, package, package_weight, package_fee));
                }
            }

            let Some((txid, package, package_weight, _)) = best else {
                break;
            };
            let mut package_order = Vec::with_capacity(package.len());
            append_mining_package(self, txid, &package, &mut selected, &mut package_order);
            selected_weight = selected_weight.saturating_add(package_weight);
            ordered.extend(package_order);
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
        let now = time::unix_time();
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
        let added_at = time::unix_time();
        match self.accept_at(transaction.clone(), chain, added_at) {
            Err(MempoolError::Conflict(_)) => self.replace(transaction, chain, added_at),
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
        if transactions.is_empty() {
            return Err(MempoolError::Empty);
        }
        let added_at = time::unix_time();
        let mut candidate = self.clone();
        let mut accepted = Vec::with_capacity(transactions.len());
        let mut package_fee = 0u64;
        let mut package_vsize = 0u64;
        let allow_low_fee_parent = package_is_child_with_parents_tree(transactions);
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
            let txid = candidate.accept_at_with_policy(
                transaction.clone(),
                chain,
                added_at,
                !allow_low_fee_parent,
            )?;
            let entry = candidate.get(&txid).ok_or(MempoolError::BadOutput)?;
            package_fee = package_fee.saturating_add(entry.fee_sat);
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
            if child.fee_sat < child.vsize.saturating_mul(MIN_RELAY_SAT_PER_VBYTE) {
                return Err(MempoolError::FeeRate);
            }
        }
        if new_count > 0 && package_fee < package_vsize.saturating_mul(MIN_RELAY_SAT_PER_VBYTE) {
            return Err(MempoolError::FeeRate);
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
        if conflicts.is_empty() {
            return Err(MempoolError::Conflict(transaction.compute_txid()));
        }
        if conflicts.iter().any(|txid| !self.is_replaceable(txid)) {
            return Err(MempoolError::ReplacementNotSignaled);
        }
        let removal = self.conflicts_and_descendants(&conflicts);
        for input in &transaction.input {
            if self.entries.contains_key(&input.previous_output.txid)
                && !removal.contains(&input.previous_output.txid)
            {
                return Err(MempoolError::ReplacementUnconfirmedInput);
            }
        }
        let conflict_fees = removal
            .iter()
            .filter_map(|txid| self.entries.get(txid))
            .map(|entry| entry.fee_sat)
            .try_fold(0u64, u64::checked_add)
            .ok_or(MempoolError::BadOutput)?;
        let mut candidate = self.clone();
        for txid in &removal {
            candidate.remove(txid);
        }
        let txid = candidate.accept_at(transaction, chain, added_at)?;
        let replacement_fee = candidate
            .get(&txid)
            .map(|entry| entry.fee_sat)
            .ok_or(MempoolError::BadOutput)?;
        let required_fee = conflict_fees
            .checked_add(
                candidate
                    .get(&txid)
                    .map(|entry| entry.vsize)
                    .unwrap_or_default()
                    .saturating_mul(MIN_RELAY_SAT_PER_VBYTE),
            )
            .ok_or(MempoolError::BadOutput)?;
        if replacement_fee < required_fee {
            return Err(MempoolError::ReplacementFee);
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

    fn accept_at(
        &mut self,
        transaction: Transaction,
        chain: &ChainState,
        added_at: u64,
    ) -> Result<Txid, MempoolError> {
        self.accept_at_with_policy(transaction, chain, added_at, true)
    }

    fn accept_at_with_policy(
        &mut self,
        transaction: Transaction,
        chain: &ChainState,
        added_at: u64,
        enforce_fee_rate: bool,
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
        if transaction.base_size() < MIN_STANDARD_TX_NONWITNESS_SIZE {
            return Err(MempoolError::NonStandard("tx-size-small".to_owned()));
        }
        if chain.network != Network::Regtest {
            validate_standard_policy(&transaction, &previous_outputs, fee_sat)?;
        }
        if enforce_fee_rate && fee_sat < vsize.saturating_mul(MIN_RELAY_SAT_PER_VBYTE) {
            return Err(MempoolError::FeeRate);
        }
        let size = bitcoin::consensus::encode::serialize(&transaction).len();
        if self.bytes.saturating_add(size) > self.max_bytes {
            return Err(MempoolError::Full);
        }
        self.check_cluster_limits(&transaction)?;
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
        self.bytes += size;
        self.entries.insert(txid, entry);
        self.wtxids.insert(wtxid, txid);
        self.sequence = self.sequence.saturating_add(1);
        Ok(txid)
    }

    fn check_cluster_limits(&self, transaction: &Transaction) -> Result<(), MempoolError> {
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
            .fold(transaction.vsize() as u64, u64::saturating_add);
        if connected.len().saturating_add(1) > MAX_CLUSTER_COUNT
            || connected_vsize > MAX_CLUSTER_VSIZE
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
        self.sequence = self
            .sequence
            .saturating_add(u64::try_from(self.entries.len()).unwrap_or(u64::MAX));
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
        self.sequence = self.sequence.saturating_add(1);
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

fn validate_standard_policy(
    transaction: &Transaction,
    previous_outputs: &[TxOut],
    fee_sat: u64,
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
        if output.script_pubkey.is_op_return() {
            data_carrier_bytes = data_carrier_bytes.saturating_add(output.script_pubkey.len());
            if data_carrier_bytes > MAX_DATACARRIER_BYTES {
                return Err(MempoolError::NonStandard("datacarrier".to_owned()));
            }
        } else if !is_standard_output_script(&output.script_pubkey) {
            return Err(MempoolError::NonStandard("scriptpubkey".to_owned()));
        }
        if is_dust_output(output) {
            dust_outputs = dust_outputs.saturating_add(1);
        }
    }
    if dust_outputs > 1 || (fee_sat != 0 && dust_outputs != 0) {
        return Err(MempoolError::NonStandard("dust".to_owned()));
    }

    validate_standard_inputs(transaction, previous_outputs)?;
    validate_standard_witnesses(transaction, previous_outputs)
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
        let mut spending_script = &previous.script_pubkey as &Script;
        if previous.script_pubkey.is_p2sh() {
            let Some(redeem_script) = last_push_data(&input.script_sig) else {
                return Err(MempoolError::NonStandard(
                    "bad-txns-nonstandard-inputs".to_owned(),
                ));
            };
            let redeem_script = Script::from_bytes(redeem_script);
            if redeem_script.count_sigops() > 15 {
                return Err(MempoolError::NonStandard(
                    "bad-txns-nonstandard-inputs".to_owned(),
                ));
            }
            spending_script = redeem_script;
        }
        if spending_script.is_witness_program()
            && !(spending_script.is_p2wpkh()
                || spending_script.is_p2wsh()
                || spending_script.is_p2tr())
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
        let spending_script = if previous.script_pubkey.is_p2sh() {
            let Some(redeem_script) = last_push_data(&input.script_sig) else {
                return Err(MempoolError::NonStandard(
                    "bad-witness-nonstandard".to_owned(),
                ));
            };
            Script::from_bytes(redeem_script)
        } else {
            &previous.script_pubkey
        };
        if !spending_script.is_witness_program() {
            return Err(MempoolError::NonStandard(
                "bad-witness-nonstandard".to_owned(),
            ));
        }
        if spending_script.is_p2wsh() {
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
                if leaf_version == 0xc0
                    && witness_items[..witness_items.len() - 2]
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

fn is_standard_output_script(script: &Script) -> bool {
    script.is_p2pkh()
        || script.is_p2sh()
        || script.p2pk_public_key().is_some()
        || script.is_witness_program()
        || is_standard_bare_multisig(script)
}

fn last_push_data(script: &Script) -> Option<&[u8]> {
    let mut last = None;
    for instruction in script.instructions() {
        match instruction {
            Ok(Instruction::PushBytes(bytes)) => last = Some(bytes.as_bytes()),
            Ok(Instruction::Op(_)) => {}
            Err(_) => return None,
        }
    }
    last
}

fn is_standard_spend_script(script: &Script) -> bool {
    is_standard_output_script(script)
        && !(script.is_witness_program()
            && !(script.is_p2wpkh() || script.is_p2wsh() || script.is_p2tr()))
}

fn is_standard_bare_multisig(script: &Script) -> bool {
    if !script.is_multisig() {
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

fn is_dust_output(output: &TxOut) -> bool {
    if output.script_pubkey.is_op_return() {
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
        .saturating_mul(DUST_RELAY_SAT_PER_KVB)
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
                    if is_dust_output(output) {
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
        nonstandard.input[0].script_sig = ScriptBuf::from_bytes(vec![0x00]);
        assert!(matches!(
            validate_standard_policy(&nonstandard, std::slice::from_ref(&previous), 1),
            Err(MempoolError::NonStandard(reason)) if reason == "scriptpubkey"
        ));

        nonstandard.output[0].script_pubkey = ScriptBuf::from_bytes({
            let mut bytes = vec![0x00, 0x14];
            bytes.extend([0u8; 20]);
            bytes
        });
        nonstandard.output[0].value = Amount::from_sat(100_000);
        assert!(validate_standard_policy(&nonstandard, std::slice::from_ref(&previous), 1).is_ok());

        nonstandard.output[0].value = Amount::from_sat(1);
        assert!(is_dust_output(&nonstandard.output[0]));
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
