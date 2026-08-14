//! Consensus-adjacent block and transaction structure checks.
//!
//! Full script execution is intentionally kept behind this module's public
//! validation boundary. The checks here cover the inexpensive, deterministic
//! rules that must run before touching the UTXO set: proof of work, merkle and
//! witness commitments, transaction shape, money range, and block weight.

use std::collections::HashSet;

use bitcoin::absolute::LockTime;
use bitcoin::blockdata::locktime::absolute::{Height, Time};
use bitcoin::blockdata::script::{Instruction, PushBytesBuf, ScriptBuf};
use bitcoin::blockdata::transaction::{OutPoint as TransactionOutPoint, TxIn, TxOut, Version};
use bitcoin::blockdata::witness::Witness;
use bitcoin::consensus::Params;
use bitcoin::consensus::encode::{deserialize_partial, serialize};
use bitcoin::opcodes::OP_0;
use bitcoin::pow::Target;
use bitcoin::{Amount, Block, BlockHash, Network, OutPoint, Sequence, Transaction, Txid};

use crate::time;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BlockValidationStats {
    pub tx_count: usize,
    pub total_output_sat: u64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BuriedDeploymentHeights {
    pub bip34: u32,
    pub bip65: u32,
    pub bip66: u32,
    pub csv: u32,
    pub segwit: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Bip9Deployment {
    pub bit: u8,
    pub start_time: i64,
    pub timeout: i64,
    pub min_activation_height: u32,
    pub threshold: u32,
    pub period: u32,
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
    #[error("block signet solution is invalid")]
    BadSignetSolution,
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

/// Consensus activation heights used by Bitcoin Core v31.1.
pub fn buried_deployment_heights(network: Network) -> BuriedDeploymentHeights {
    match network {
        Network::Bitcoin => BuriedDeploymentHeights {
            bip34: 227_931,
            bip65: 388_381,
            bip66: 363_725,
            csv: 419_328,
            segwit: 481_824,
        },
        Network::Testnet => BuriedDeploymentHeights {
            bip34: 21_111,
            bip65: 581_885,
            bip66: 330_776,
            csv: 770_112,
            segwit: 834_624,
        },
        Network::Testnet4 | Network::Signet => BuriedDeploymentHeights {
            bip34: 1,
            bip65: 1,
            bip66: 1,
            csv: 1,
            segwit: 1,
        },
        Network::Regtest => BuriedDeploymentHeights {
            bip34: 1,
            bip65: 1,
            bip66: 1,
            csv: 1,
            segwit: 0,
        },
    }
}

pub fn bip9_deployments(network: Network) -> [Bip9Deployment; 2] {
    let testdummy = match network {
        Network::Regtest => Bip9Deployment {
            bit: 28,
            start_time: 0,
            timeout: i64::MAX,
            min_activation_height: 0,
            threshold: 108,
            period: 144,
        },
        Network::Bitcoin | Network::Signet => Bip9Deployment {
            bit: 28,
            start_time: -2,
            timeout: i64::MAX,
            min_activation_height: 0,
            threshold: 1815,
            period: 2016,
        },
        Network::Testnet | Network::Testnet4 => Bip9Deployment {
            bit: 28,
            start_time: -2,
            timeout: i64::MAX,
            min_activation_height: 0,
            threshold: 1512,
            period: 2016,
        },
    };
    let taproot = match network {
        Network::Bitcoin => Bip9Deployment {
            bit: 2,
            start_time: 1_619_222_400,
            timeout: 1_628_640_000,
            min_activation_height: 709_632,
            threshold: 1815,
            period: 2016,
        },
        Network::Testnet => Bip9Deployment {
            bit: 2,
            start_time: 1_619_222_400,
            timeout: 1_628_640_000,
            min_activation_height: 0,
            threshold: 1512,
            period: 2016,
        },
        Network::Testnet4 => Bip9Deployment {
            bit: 2,
            start_time: -1,
            timeout: i64::MAX,
            min_activation_height: 0,
            threshold: 1512,
            period: 2016,
        },
        Network::Signet => Bip9Deployment {
            bit: 2,
            start_time: -1,
            timeout: i64::MAX,
            min_activation_height: 0,
            threshold: 1815,
            period: 2016,
        },
        Network::Regtest => Bip9Deployment {
            bit: 2,
            start_time: -1,
            timeout: i64::MAX,
            min_activation_height: 0,
            threshold: 108,
            period: 144,
        },
    };
    [testdummy, taproot]
}

pub fn script_flags_for_block(network: Network, height: u32, block_time: u32) -> u32 {
    let heights = buried_deployment_heights(network);
    let mut flags = bitcoinconsensus::VERIFY_NONE;
    let p2sh_active = match network {
        Network::Regtest | Network::Signet | Network::Testnet4 => true,
        Network::Bitcoin | Network::Testnet => block_time >= network_params(network).bip16_time,
    };
    if p2sh_active {
        flags |= bitcoinconsensus::VERIFY_P2SH;
    }
    if height >= heights.bip66 {
        flags |= bitcoinconsensus::VERIFY_DERSIG;
    }
    if height >= heights.bip65 {
        flags |= bitcoinconsensus::VERIFY_CHECKLOCKTIMEVERIFY;
    }
    if height >= heights.csv {
        flags |= bitcoinconsensus::VERIFY_CHECKSEQUENCEVERIFY;
    }
    if height >= heights.segwit {
        flags |= bitcoinconsensus::VERIFY_NULLDUMMY | bitcoinconsensus::VERIFY_WITNESS;
    }
    let taproot_active = match network {
        Network::Bitcoin => height >= 709_632,
        Network::Testnet | Network::Testnet4 | Network::Signet | Network::Regtest => true,
    };
    if taproot_active {
        flags |= bitcoinconsensus::VERIFY_TAPROOT;
    }
    flags
}

pub fn validate_header(
    network: Network,
    header: &bitcoin::block::Header,
    expected_previous: BlockHash,
    expected_target: Target,
    median_time_past: u32,
) -> Result<(), ValidationError> {
    validate_header_internal(
        network,
        header,
        expected_previous,
        expected_target,
        median_time_past,
        true,
    )
}

/// Validate a candidate header for block-template proposal mode. Proposal
/// validation checks the expected target and header rules but intentionally
/// skips proof-of-work; the miner has not selected a nonce yet.
pub fn validate_header_without_pow(
    network: Network,
    header: &bitcoin::block::Header,
    expected_previous: BlockHash,
    expected_target: Target,
    median_time_past: u32,
) -> Result<(), ValidationError> {
    validate_header_internal(
        network,
        header,
        expected_previous,
        expected_target,
        median_time_past,
        false,
    )
}

fn validate_header_internal(
    network: Network,
    header: &bitcoin::block::Header,
    expected_previous: BlockHash,
    expected_target: Target,
    median_time_past: u32,
    check_pow: bool,
) -> Result<(), ValidationError> {
    if header.prev_blockhash != expected_previous {
        return Err(ValidationError::WrongPreviousBlock);
    }
    if header.time <= median_time_past {
        return Err(ValidationError::TimeTooOld);
    }
    if header.time > time::unix_time().saturating_add(2 * 60 * 60) as u32 {
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
    if check_pow && !header.target().is_met_by(header.block_hash()) {
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
    let default_challenge = (network == Network::Signet).then(default_signet_challenge);
    validate_block_structure_with_signet(
        block,
        network,
        height,
        expected_coinbase_value,
        default_challenge.as_deref(),
    )
}

pub fn validate_block_structure_with_signet(
    block: &Block,
    network: Network,
    height: u32,
    expected_coinbase_value: u64,
    signet_challenge: Option<&[u8]>,
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
    if height >= buried_deployment_heights(network).bip34 {
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
    if let Some(challenge) = signet_challenge {
        validate_signet_block_solution(block, challenge)?;
    }
    Ok(BlockValidationStats {
        tx_count: block.txdata.len(),
        total_output_sat,
    })
}

/// The default signet challenge used by Bitcoin Core's public signet.
pub fn default_signet_challenge() -> Vec<u8> {
    hex::decode(
        "512103ad5e0edad18cb1f0fc0d28a3d4f1f3e445640337489abb10404f2d1e086be430210359ef5021964fe22d6f8e05b2463c9540ce96883fe3b278760f048f5189f2e6c452ae",
    )
    .expect("the built-in signet challenge is valid hex")
}

const SIGNET_HEADER: [u8; 4] = [0xec, 0xc7, 0xda, 0xa2];

/// Validate the BIP325 solution committed to a signet block.
pub fn validate_signet_block_solution(
    block: &Block,
    challenge: &[u8],
) -> Result<(), ValidationError> {
    if block.block_hash()
        == bitcoin::blockdata::constants::genesis_block(Network::Signet).block_hash()
    {
        return Ok(());
    }

    let Some(coinbase) = block.txdata.first() else {
        return Err(ValidationError::BadSignetSolution);
    };
    let Some(commitment_index) = coinbase.output.iter().rposition(|output| {
        output.script_pubkey.len() >= 38
            && output.script_pubkey.as_bytes()[..6] == [0x6a, 0x24, 0xaa, 0x21, 0xa9, 0xed]
    }) else {
        return Err(ValidationError::BadSignetSolution);
    };

    let (modified_commitment, solution) =
        extract_signet_solution(&coinbase.output[commitment_index].script_pubkey)?;
    let mut modified_coinbase = coinbase.clone();
    modified_coinbase.output[commitment_index].script_pubkey = modified_commitment;

    let mut merkle_leaves = Vec::with_capacity(block.txdata.len());
    merkle_leaves.push(modified_coinbase.compute_txid());
    merkle_leaves.extend(block.txdata.iter().skip(1).map(Transaction::compute_txid));
    let modified_merkle = bitcoin::merkle_tree::calculate_root(merkle_leaves.into_iter())
        .ok_or(ValidationError::BadSignetSolution)?;

    let block_data = signet_block_data(block, &modified_merkle);
    let block_data =
        PushBytesBuf::try_from(block_data).map_err(|_| ValidationError::BadSignetSolution)?;

    let mut to_spend_script_sig = ScriptBuf::new();
    to_spend_script_sig.push_opcode(OP_0);
    to_spend_script_sig.push_slice(block_data);
    let tx_to_spend = Transaction {
        version: Version::non_standard(0),
        lock_time: LockTime::ZERO,
        input: vec![TxIn {
            previous_output: TransactionOutPoint::null(),
            script_sig: to_spend_script_sig,
            sequence: Sequence::ZERO,
            witness: Witness::default(),
        }],
        output: vec![TxOut {
            value: Amount::ZERO,
            script_pubkey: ScriptBuf::from_bytes(challenge.to_vec()),
        }],
    };

    let (script_sig, witness) = parse_signet_solution(&solution)?;
    let tx_spending = Transaction {
        version: Version::non_standard(0),
        lock_time: LockTime::ZERO,
        input: vec![TxIn {
            previous_output: TransactionOutPoint::new(tx_to_spend.compute_txid(), 0),
            script_sig,
            sequence: Sequence::ZERO,
            witness,
        }],
        output: vec![TxOut {
            value: Amount::ZERO,
            script_pubkey: ScriptBuf::from_bytes(vec![0x6a]),
        }],
    };
    let serialized = serialize(&tx_spending);
    let spent_outputs = [bitcoinconsensus::Utxo {
        script_pubkey: tx_to_spend.output[0].script_pubkey.as_bytes().as_ptr(),
        script_pubkey_len: tx_to_spend.output[0].script_pubkey.len() as u32,
        value: 0,
    }];
    let flags = bitcoinconsensus::VERIFY_P2SH
        | bitcoinconsensus::VERIFY_WITNESS
        | bitcoinconsensus::VERIFY_DERSIG
        | bitcoinconsensus::VERIFY_NULLDUMMY;
    bitcoinconsensus::verify_with_flags(
        tx_to_spend.output[0].script_pubkey.as_bytes(),
        0,
        &serialized,
        Some(&spent_outputs),
        0,
        flags,
    )
    .map_err(|_| ValidationError::BadSignetSolution)
}

fn signet_block_data(block: &Block, modified_merkle: &Txid) -> Vec<u8> {
    let mut block_data = Vec::with_capacity(72);
    block_data.extend_from_slice(&serialize(&block.header.version));
    block_data.extend_from_slice(&serialize(&block.header.prev_blockhash));
    block_data.extend_from_slice(&serialize(modified_merkle));
    block_data.extend_from_slice(&serialize(&block.header.time));
    block_data
}

fn extract_signet_solution(
    commitment: &bitcoin::Script,
) -> Result<(ScriptBuf, Vec<u8>), ValidationError> {
    let mut replacement = ScriptBuf::new();
    let mut solution = Vec::new();
    let mut found_header = false;
    for instruction in commitment.instructions() {
        match instruction {
            Ok(Instruction::PushBytes(pushdata)) => {
                let bytes = pushdata.as_bytes();
                if !found_header
                    && bytes.len() > SIGNET_HEADER.len()
                    && bytes.starts_with(&SIGNET_HEADER)
                {
                    solution.extend_from_slice(&bytes[SIGNET_HEADER.len()..]);
                    replacement.push_slice(SIGNET_HEADER);
                    found_header = true;
                } else {
                    replacement.push_slice(pushdata);
                }
            }
            Ok(Instruction::Op(opcode)) => replacement.push_opcode(opcode),
            Err(_) => break,
        }
    }
    if found_header {
        Ok((replacement, solution))
    } else {
        Ok((commitment.to_owned(), Vec::new()))
    }
}

fn parse_signet_solution(solution: &[u8]) -> Result<(ScriptBuf, Witness), ValidationError> {
    if solution.is_empty() {
        return Ok((ScriptBuf::new(), Witness::default()));
    }
    let (script_sig, script_size) = deserialize_partial::<ScriptBuf>(solution)
        .map_err(|_| ValidationError::BadSignetSolution)?;
    let remaining = solution
        .get(script_size..)
        .ok_or(ValidationError::BadSignetSolution)?;
    let (witness, witness_size) = deserialize_partial::<Witness>(remaining)
        .map_err(|_| ValidationError::BadSignetSolution)?;
    if script_size + witness_size != solution.len() {
        return Err(ValidationError::BadSignetSolution);
    }
    Ok((script_sig, witness))
}

pub fn block_subsidy(height: u32) -> u64 {
    block_subsidy_for_network(Network::Bitcoin, height)
}

pub fn block_subsidy_for_network(network: Network, height: u32) -> u64 {
    let halving_interval = if network == Network::Regtest {
        150
    } else {
        210_000
    };
    let halvings = height / halving_interval;
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
    validate_transaction_scripts_at_time(network, height, u32::MAX, transaction, previous_outputs)
}

pub fn validate_transaction_scripts_at_time(
    network: Network,
    height: u32,
    block_time: u32,
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
    let flags = script_flags_for_block(network, height, block_time);
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
        assert_eq!(
            block_subsidy_for_network(Network::Regtest, 150),
            2_500_000_000
        );
        assert_eq!(block_subsidy_for_network(Network::Regtest, 64 * 150), 0);
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
    fn signet_message_has_the_bip325_header_fields_once() {
        let block = Block {
            header: Header {
                version: BlockVersion::TWO,
                prev_blockhash: BlockHash::from_byte_array([1; 32]),
                merkle_root: bitcoin::TxMerkleNode::from_byte_array([2; 32]),
                time: 123,
                bits: bitcoin::pow::CompactTarget::from_consensus(0x207f_ffff),
                nonce: 0,
            },
            txdata: Vec::new(),
        };
        let modified_merkle = Txid::from_byte_array([3; 32]);
        let data = signet_block_data(&block, &modified_merkle);
        assert_eq!(data.len(), 72);
        assert_eq!(&data[0..4], &2i32.to_le_bytes());
        assert_eq!(&data[36..68], &modified_merkle.to_byte_array());
        assert_eq!(&data[68..72], &123u32.to_le_bytes());
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
                script_sig: ScriptBuf::from_bytes(vec![0x51, 0]),
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
        let mut invalid_height = block.clone();
        invalid_height.txdata[0].input[0].script_sig = ScriptBuf::from_bytes(vec![1, 1]);
        invalid_height.header.merkle_root = invalid_height.compute_merkle_root().unwrap();
        assert!(matches!(
            validate_block_structure(
                &invalid_height,
                Network::Regtest,
                1,
                Amount::MAX_MONEY.to_sat()
            ),
            Err(ValidationError::BadCoinbaseHeight)
        ));
        assert!(matches!(
            validate_block_structure(&block, Network::Regtest, 1, Amount::MAX_MONEY.to_sat()),
            Err(ValidationError::BadOutputValue(_))
        ));
    }

    fn signet_block(commitment_extension: Option<&[u8]>) -> Block {
        let mut commitment = vec![0x6a, 0x24, 0xaa, 0x21, 0xa9, 0xed];
        commitment.extend_from_slice(&[0u8; 32]);
        if let Some(extension) = commitment_extension {
            assert!(extension.len() < 76);
            commitment.push(extension.len() as u8);
            commitment.extend_from_slice(extension);
        }
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
                value: Amount::ZERO,
                script_pubkey: ScriptBuf::from_bytes(commitment),
            }],
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
            txdata: vec![coinbase],
        };
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        block
    }

    #[test]
    fn accepts_a_trivial_signet_challenge_without_a_solution_extension() {
        let block = signet_block(None);
        validate_signet_block_solution(&block, &[0x51]).unwrap();
    }

    #[test]
    fn rejects_an_invalid_signet_solution() {
        let block = signet_block(Some(&[0xec, 0xc7, 0xda, 0xa2, 0x00]));
        assert!(matches!(
            validate_signet_block_solution(&block, &[0x51]),
            Err(ValidationError::BadSignetSolution)
        ));
    }
}
