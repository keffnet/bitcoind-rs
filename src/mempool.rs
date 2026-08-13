//! In-memory transaction admission and relay pool.

use std::collections::{HashMap, HashSet};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use bitcoin::{Amount, Network, OutPoint, Transaction, Txid};

use crate::chain::ChainState;
use crate::validation::ValidationError;

const DEFAULT_MAX_MEMPOOL_BYTES: usize = 300 * 1024 * 1024;
const MIN_RELAY_SAT_PER_VBYTE: u64 = 1;

#[derive(Clone, Debug)]
pub struct MempoolEntry {
    pub transaction: Transaction,
    pub fee_sat: u64,
    pub vsize: u64,
    pub added_at: u64,
}

pub struct Mempool {
    pub network: Network,
    max_bytes: usize,
    bytes: usize,
    entries: HashMap<Txid, MempoolEntry>,
    spent: HashMap<OutPoint, Txid>,
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

    pub fn get(&self, txid: &Txid) -> Option<&MempoolEntry> {
        self.entries.get(txid)
    }

    pub fn transactions(&self) -> impl Iterator<Item = &Transaction> {
        self.entries.values().map(|entry| &entry.transaction)
    }

    pub fn accept(
        &mut self,
        transaction: Transaction,
        chain: &ChainState,
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
        for input in &transaction.input {
            if !seen.insert(input.previous_output) {
                return Err(MempoolError::DuplicateInput);
            }
            if let Some(conflict) = self.spent.get(&input.previous_output) {
                return Err(MempoolError::Conflict(*conflict));
            }
            let previous = self
                .entries
                .get(&input.previous_output.txid)
                .and_then(|entry| {
                    entry
                        .transaction
                        .output
                        .get(input.previous_output.vout as usize)
                })
                .or_else(|| {
                    chain
                        .utxo(&input.previous_output)
                        .map(|entry| &entry.output)
                })
                .ok_or(MempoolError::MissingInput(input.previous_output))?;
            input_total = input_total
                .checked_add(previous.value.to_sat())
                .ok_or(MempoolError::BadOutput)?;
        }
        let output_total = transaction
            .output
            .iter()
            .map(|output| output.value.to_sat())
            .try_fold(0u64, u64::checked_add)
            .ok_or(MempoolError::BadOutput)?;
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
            added_at: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or(Duration::ZERO)
                .as_secs(),
        };
        for input in &entry.transaction.input {
            self.spent.insert(input.previous_output, txid);
        }
        self.bytes += size;
        self.entries.insert(txid, entry);
        Ok(txid)
    }

    pub fn remove(&mut self, txid: &Txid) -> Option<MempoolEntry> {
        let entry = self.entries.remove(txid)?;
        let size = bitcoin::consensus::encode::serialize(&entry.transaction).len();
        self.bytes = self.bytes.saturating_sub(size);
        for input in &entry.transaction.input {
            self.spent.remove(&input.previous_output);
        }
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
    fn from(_: ValidationError) -> Self {
        MempoolError::BadOutput
    }
}
