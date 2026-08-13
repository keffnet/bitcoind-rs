//! Consensus-adjacent block and transaction structure checks.
//!
//! Full script execution is intentionally kept behind this module's public
//! validation boundary. The checks here cover the inexpensive, deterministic
//! rules that must run before touching the UTXO set: proof of work, merkle and
//! witness commitments, transaction shape, money range, and block weight.

use std::collections::HashSet;
use std::time::{SystemTime, UNIX_EPOCH};

use bitcoin::blockdata::locktime::absolute::{Height, Time};
use bitcoin::consensus::Params;
use bitcoin::pow::Target;
use bitcoin::{Amount, Block, BlockHash, Network, OutPoint, Transaction, Txid};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BlockValidationStats {
    pub tx_count: usize,
    pub total_output_sat: u64,
}

#[derive(Debug, thiserror::Error)]
pub enum ValidationError {
    #[error("block does not extend the active tip")]
    WrongPreviousBlock,
    #[error("block proof of work target is invalid")]
    BadTarget,
    #[error("block proof of work is invalid")]
    BadProofOfWork,
    #[error("block target exceeds the network limit")]
    TargetAboveLimit,
    #[error("block timestamp is not after median time past")]
    TimeTooOld,
    #[error("block timestamp is too far in the future")]
    TimeTooNew,
    #[error("block contains no transactions")]
    EmptyBlock,
    #[error("block merkle root is invalid")]
    BadMerkleRoot,
    #[error("block witness commitment is invalid")]
    BadWitnessCommitment,
    #[error("block weight exceeds the consensus limit")]
    OversizedBlock,
    #[error("coinbase transaction is missing or malformed")]
    BadCoinbase,
    #[error("non-coinbase transaction appears in the coinbase position")]
    FirstTransactionNotCoinbase,
    #[error("transaction {0} is unexpectedly coinbase")]
    ExtraCoinbase(Txid),
    #[error("transaction {0} has no inputs")]
    EmptyInputs(Txid),
    #[error("transaction {0} has no outputs")]
    EmptyOutputs(Txid),
    #[error("transaction {0} contains a duplicate input")]
    DuplicateInput(Txid),
    #[error("block contains duplicate transaction {0}")]
    DuplicateTransaction(Txid),
    #[error("transaction {0} output value is out of range")]
    BadOutputValue(Txid),
    #[error("block output total exceeds MAX_MONEY")]
    OutputTotalOverflow,
    #[error("block subsidy and fees cannot be represented")]
    SubsidyOverflow,
    #[error("coinbase value {actual} exceeds allowed value {allowed}")]
    CoinbaseOverpay { actual: u64, allowed: u64 },
    #[error("transaction input {outpoint} is missing from the UTXO set")]
    MissingInput { outpoint: OutPoint },
    #[error("coinbase input {outpoint} has not matured")]
    ImmatureCoinbase { outpoint: OutPoint },
    #[error("transaction input values exceed MAX_MONEY")]
    InputTotalOverflow,
    #[error("transaction {txid} creates more value than it spends")]
    NegativeFee { txid: Txid },
    #[error("block height is not encoded in the coinbase script")]
    BadCoinbaseHeight,
    #[error("transaction locktime is not yet satisfied")]
    NonFinalTransaction,
    #[error("script validation failed for transaction {txid} input {input}: {reason}")]
    Script {
        txid: Txid,
        input: usize,
        reason: String,
    },
}

pub fn network_params(network: Network) -> &'static Params {
    network.params()
}

pub fn validate_header(
    network: Network,
    header: &bitcoin::block::Header,
    expected_previous: BlockHash,
    expected_target: Target,
    median_time_past: u32,
) -> Result<(), ValidationError> {
    if header.prev_blockhash != expected_previous {
        return Err(ValidationError::WrongPreviousBlock);
    }
    if header.time <= median_time_past {
        return Err(ValidationError::TimeTooOld);
    }
    if header.time
        > SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs()
            .saturating_add(2 * 60 * 60) as u32
    {
        return Err(ValidationError::TimeTooNew);
    }
    if header.target() != expected_target
        || header.bits.to_consensus() != expected_target.to_compact_lossy().to_consensus()
    {
        return Err(ValidationError::BadTarget);
    }
    let compact = header.bits.to_consensus();
    let mantissa = compact & 0x007f_ffff;
    if mantissa == 0 || (compact & 0x0080_0000) != 0 || header.target() == Target::ZERO {
        return Err(ValidationError::BadTarget);
    }
    if header.target() > network_params(network).max_attainable_target {
        return Err(ValidationError::TargetAboveLimit);
    }
    if !header.target().is_met_by(header.block_hash()) {
        return Err(ValidationError::BadProofOfWork);
    }
    Ok(())
}

pub fn validate_block_structure(
    block: &Block,
    network: Network,
    height: u32,
    expected_coinbase_value: u64,
) -> Result<BlockValidationStats, ValidationError> {
    if block.txdata.is_empty() {
        return Err(ValidationError::EmptyBlock);
    }
    if !block.check_merkle_root() {
        return Err(ValidationError::BadMerkleRoot);
    }
    if !block.check_witness_commitment() {
        return Err(ValidationError::BadWitnessCommitment);
    }
    if block.weight().to_wu() > 4_000_000 {
        return Err(ValidationError::OversizedBlock);
    }
    let first = &block.txdata[0];
    if !first.is_coinbase() {
        return Err(ValidationError::FirstTransactionNotCoinbase);
    }
    if first.input[0].script_sig.len() < 2 || first.input[0].script_sig.len() > 100 {
        return Err(ValidationError::BadCoinbase);
    }
    if height >= network_params(network).bip34_height {
        let encoded_height = bitcoin::script::Builder::new()
            .push_int(height as i64)
            .into_script();
        if !first.input[0]
            .script_sig
            .as_bytes()
            .starts_with(encoded_height.as_bytes())
        {
            return Err(ValidationError::BadCoinbaseHeight);
        }
    }

    let coinbase_total = first
        .output
        .iter()
        .try_fold(0u64, |total, output| {
            total.checked_add(output.value.to_sat())
        })
        .ok_or(ValidationError::OutputTotalOverflow)?;
    let mut txids = HashSet::with_capacity(block.txdata.len());
    let mut total_output_sat = 0u64;
    for (position, tx) in block.txdata.iter().enumerate() {
        let txid = tx.compute_txid();
        if !txids.insert(txid) {
            return Err(ValidationError::DuplicateTransaction(txid));
        }
        if position > 0 && tx.is_coinbase() {
            return Err(ValidationError::ExtraCoinbase(txid));
        }
        if tx.input.is_empty() {
            return Err(ValidationError::EmptyInputs(txid));
        }
        if tx.output.is_empty() {
            return Err(ValidationError::EmptyOutputs(txid));
        }
        let mut inputs = HashSet::with_capacity(tx.input.len());
        for input in &tx.input {
            if !inputs.insert(input.previous_output) {
                return Err(ValidationError::DuplicateInput(txid));
            }
        }
        let mut tx_total = 0u64;
        for output in &tx.output {
            let value = output.value.to_sat();
            if output.value > Amount::MAX_MONEY {
                return Err(ValidationError::BadOutputValue(txid));
            }
            tx_total = tx_total
                .checked_add(value)
                .ok_or(ValidationError::OutputTotalOverflow)?;
        }
        if tx_total > Amount::MAX_MONEY.to_sat() {
            return Err(ValidationError::BadOutputValue(txid));
        }
        total_output_sat = total_output_sat
            .checked_add(tx_total)
            .ok_or(ValidationError::OutputTotalOverflow)?;
    }
    if coinbase_total > expected_coinbase_value {
        return Err(ValidationError::CoinbaseOverpay {
            actual: coinbase_total,
            allowed: expected_coinbase_value,
        });
    }
    Ok(BlockValidationStats {
        tx_count: block.txdata.len(),
        total_output_sat,
    })
}

pub fn block_subsidy(height: u32) -> u64 {
    let halvings = height / 210_000;
    if halvings >= 64 {
        0
    } else {
        (50 * 100_000_000) >> halvings
    }
}

pub fn checked_money_add(left: u64, right: u64) -> Result<u64, ValidationError> {
    let sum = left
        .checked_add(right)
        .ok_or(ValidationError::SubsidyOverflow)?;
    if sum > Amount::MAX_MONEY.to_sat() {
        return Err(ValidationError::SubsidyOverflow);
    }
    Ok(sum)
}

pub fn validate_transaction_finality(
    transaction: &Transaction,
    height: u32,
    median_time_past: u32,
    previous_entries: &[crate::chain::UtxoEntry],
) -> Result<(), ValidationError> {
    let block_height = Height::from_consensus(height).expect("block height fits consensus range");
    let block_time =
        Time::from_consensus(median_time_past).expect("median time is a valid timestamp");
    if !transaction.is_absolute_timelock_satisfied(block_height, block_time) {
        return Err(ValidationError::NonFinalTransaction);
    }
    if transaction.version.0 < 2 || previous_entries.len() != transaction.input.len() {
        return Ok(());
    }
    for (input, entry) in transaction.input.iter().zip(previous_entries) {
        let sequence = input.sequence.to_consensus_u32();
        if !input.sequence.is_relative_lock_time() {
            continue;
        }
        let relative = u32::from((sequence & 0x0000_ffff) as u16);
        if input.sequence.is_height_locked() {
            if height < entry.height.saturating_add(relative) {
                return Err(ValidationError::NonFinalTransaction);
            }
        } else {
            let relative_seconds = relative.saturating_mul(512);
            if median_time_past
                <= entry
                    .median_time_past
                    .saturating_add(relative_seconds.saturating_sub(1))
            {
                return Err(ValidationError::NonFinalTransaction);
            }
        }
    }
    Ok(())
}

/// Verify every non-coinbase input using the same libbitcoinconsensus script
/// engine used by Bitcoin Core's consensus boundary. The previous outputs are
/// supplied as a parallel slice so SegWit and Taproot spends receive the full
/// spent-output context they require.
pub fn validate_transaction_scripts(
    network: Network,
    height: u32,
    transaction: &Transaction,
    previous_outputs: &[bitcoin::TxOut],
) -> Result<(), ValidationError> {
    if previous_outputs.len() != transaction.input.len() {
        return Err(ValidationError::Script {
            txid: transaction.compute_txid(),
            input: 0,
            reason: "previous-output count does not match input count".to_owned(),
        });
    }
    let serialized = bitcoin::consensus::encode::serialize(transaction);
    let spent_outputs: Vec<bitcoinconsensus::Utxo> = previous_outputs
        .iter()
        .map(|output| bitcoinconsensus::Utxo {
            script_pubkey: output.script_pubkey.as_bytes().as_ptr(),
            script_pubkey_len: output.script_pubkey.len() as u32,
            value: output.value.to_sat() as i64,
        })
        .collect();
    let flags = match network {
        Network::Bitcoin => {
            let mut flags = bitcoinconsensus::height_to_flags(height);
            if height >= 709_632 {
                flags |= bitcoinconsensus::VERIFY_TAPROOT;
            }
            flags
        }
        Network::Testnet | Network::Testnet4 | Network::Signet | Network::Regtest => {
            bitcoinconsensus::VERIFY_ALL_PRE_TAPROOT | bitcoinconsensus::VERIFY_TAPROOT
        }
    };
    for (input, previous_output) in previous_outputs.iter().enumerate() {
        if let Err(error) = bitcoinconsensus::verify_with_flags(
            previous_output.script_pubkey.as_bytes(),
            previous_output.value.to_sat(),
            &serialized,
            Some(&spent_outputs),
            input,
            flags,
        ) {
            return Err(ValidationError::Script {
                txid: transaction.compute_txid(),
                input,
                reason: format!("{error:?}"),
            });
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::Block;
    use bitcoin::absolute::LockTime;
    use bitcoin::block::{Header, Version as BlockVersion};
    use bitcoin::blockdata::script::ScriptBuf;
    use bitcoin::blockdata::transaction::{OutPoint, TxIn, TxOut, Version};
    use bitcoin::blockdata::witness::Witness;
    use bitcoin::hashes::Hash;

    #[test]
    fn subsidy_halves_and_eventually_stops() {
        assert_eq!(block_subsidy(0), 5_000_000_000);
        assert_eq!(block_subsidy(210_000), 2_500_000_000);
        assert_eq!(block_subsidy(64 * 210_000), 0);
    }

    #[test]
    fn consensus_engine_accepts_an_anyone_can_spend_input() {
        let previous = TxOut {
            value: Amount::from_sat(10_000),
            script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
        };
        let transaction = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(bitcoin::Txid::from_byte_array([1u8; 32]), 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(9_000),
                script_pubkey: ScriptBuf::new(),
            }],
        };
        validate_transaction_scripts(Network::Regtest, 1, &transaction, &[previous]).unwrap();
    }

    #[test]
    fn relative_height_lock_is_enforced() {
        let transaction = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(bitcoin::Txid::from_byte_array([2u8; 32]), 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::from_height(2),
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(1),
                script_pubkey: ScriptBuf::new(),
            }],
        };
        let entry = crate::chain::UtxoEntry {
            output: TxOut {
                value: Amount::from_sat(2),
                script_pubkey: ScriptBuf::new(),
            },
            height: 10,
            median_time_past: 500_000_000,
            coinbase: false,
        };
        assert!(
            validate_transaction_finality(
                &transaction,
                11,
                500_000_001,
                std::slice::from_ref(&entry),
            )
            .is_err()
        );
        assert!(validate_transaction_finality(&transaction, 12, 500_000_001, &[entry]).is_ok());
    }

    #[test]
    fn rejects_transaction_output_totals_above_money_range() {
        let coinbase = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::null(),
                script_sig: ScriptBuf::from_bytes(vec![1, 1]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(5_000_000_000),
                script_pubkey: ScriptBuf::new(),
            }],
        };
        let transaction = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(bitcoin::Txid::from_byte_array([3u8; 32]), 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![
                TxOut {
                    value: Amount::MAX_MONEY,
                    script_pubkey: ScriptBuf::new(),
                },
                TxOut {
                    value: Amount::MAX_MONEY,
                    script_pubkey: ScriptBuf::new(),
                },
            ],
        };
        let mut block = Block {
            header: Header {
                version: BlockVersion::TWO,
                prev_blockhash: BlockHash::all_zeros(),
                merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                time: 1,
                bits: bitcoin::pow::CompactTarget::from_consensus(0x207f_ffff),
                nonce: 0,
            },
            txdata: vec![coinbase, transaction],
        };
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        assert!(matches!(
            validate_block_structure(&block, Network::Regtest, 1, Amount::MAX_MONEY.to_sat()),
            Err(ValidationError::BadOutputValue(_))
        ));
    }
}
