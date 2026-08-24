//! Consensus-adjacent block and transaction structure checks.
//!
//! Full script execution is intentionally kept behind this module's public
//! validation boundary. The checks here cover the inexpensive, deterministic
//! rules that must run before touching the UTXO set: proof of work, merkle and
//! witness commitments, transaction shape, money range, and block weight.

use std::collections::HashSet;

use bitcoin::absolute::{LOCK_TIME_THRESHOLD, LockTime};
use bitcoin::blockdata::script::{Instruction, PushBytesBuf, ScriptBuf};
use bitcoin::blockdata::transaction::{OutPoint as TransactionOutPoint, TxIn, TxOut, Version};
use bitcoin::blockdata::witness::Witness;
use bitcoin::consensus::Params;
use bitcoin::consensus::encode::{VarInt, deserialize_partial, serialize};
use bitcoin::hashes::{Hash, HashEngine};
use bitcoin::opcodes::{Class, ClassifyContext, OP_0};
use bitcoin::pow::Target;
use bitcoin::{
    Amount, Block, BlockHash, Network, OutPoint, Script, Sequence, Transaction, TxMerkleNode, Txid,
    WitnessCommitment,
};

use crate::script::verify_transaction_scripts;
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
    pub max_activation_height: u32,
    pub active_duration: u32,
    pub threshold: u32,
    pub period: u32,
}

impl Bip9Deployment {
    pub const ALWAYS_ACTIVE_TIME: i64 = -1;
    pub const NEVER_ACTIVE_TIME: i64 = -2;
    // Core stores these two fields as signed 32-bit integers and uses
    // INT_MAX as the sentinel for an unbounded deployment.
    pub const MAX_ACTIVATION_HEIGHT: u32 = i32::MAX as u32;
    pub const PERMANENT_ACTIVE_DURATION: u32 = i32::MAX as u32;

    pub fn is_enabled(self) -> bool {
        self.start_time != Self::NEVER_ACTIVE_TIME
    }
}

/// Consensus deployment parameters for one chain instance.
///
/// Bitcoin Core creates these from the selected chain and then applies
/// regtest-only command-line overrides before validation starts. Keeping the
/// values together lets multiple nodes in one process use different regtest
/// activation schedules without relying on global state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DeploymentParameters {
    pub network: Network,
    pub buried: BuriedDeploymentHeights,
    pub bip9: [Bip9Deployment; 3],
    pub bip94: bool,
}

impl DeploymentParameters {
    pub fn for_network(network: Network) -> Self {
        Self {
            network,
            buried: buried_deployment_heights(network),
            bip9: bip9_deployments(network),
            bip94: network == Network::Testnet4,
        }
    }
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
    #[error("node software has expired")]
    NodeExpired,
    #[error("block timestamp violates the BIP94 timewarp limit")]
    Bip94TimeWarp,
    #[error("block contains no transactions")]
    EmptyBlock,
    #[error("block merkle root is invalid")]
    BadMerkleRoot,
    #[error("block witness reserved value has the wrong size")]
    BadWitnessNonceSize,
    #[error("block witness commitment does not match the witness merkle root")]
    BadWitnessMerkleMatch,
    #[error("block contains witness data before SegWit activation")]
    UnexpectedWitness,
    #[error("block signet solution is invalid")]
    BadSignetSolution,
    #[error("block non-witness size exceeds the consensus limit")]
    OversizedBlockBase,
    #[error("block weight exceeds the consensus limit")]
    OversizedBlock,
    #[error("transaction {0} exceeds the consensus size limit")]
    OversizedTransaction(Txid),
    #[error("block sigop cost exceeds the consensus limit")]
    TooManySigops,
    #[error("block sigop cost exceeds the consensus limit while connecting")]
    TooManySigopsInConnect,
    #[error("block version {actual} is below the required version {required}")]
    BadBlockVersion { actual: i32, required: i32 },
    #[error(
        "block must signal for {deployment} approaching max_activation_height={max_activation_height}"
    )]
    BadVersionBits {
        deployment: &'static str,
        max_activation_height: u32,
    },
    #[error("coinbase transaction is missing or malformed")]
    BadCoinbase,
    #[error("non-coinbase transaction appears in the coinbase position")]
    FirstTransactionNotCoinbase,
    #[error("transaction {0} is unexpectedly coinbase")]
    ExtraCoinbase(Txid),
    #[error("transaction {0} contains a null prevout")]
    NullPrevout(Txid),
    #[error("transaction {0} has no inputs")]
    EmptyInputs(Txid),
    #[error("transaction {0} has no outputs")]
    EmptyOutputs(Txid),
    #[error("transaction {0} contains a duplicate input")]
    DuplicateInput(Txid),
    #[error("block contains duplicate transaction {0}")]
    DuplicateTransaction(Txid),
    #[error("transaction {0} output value is negative")]
    NegativeOutputValue(Txid),
    #[error("transaction {0} output value is out of range")]
    BadOutputValue(Txid),
    #[error("transaction {0} output script exceeds ReducedData limits")]
    ReducedDataOutputTooLarge(Txid),
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
    #[error("accumulated transaction fees exceed MAX_MONEY")]
    AccumulatedFeeOverflow,
    #[error("transaction {txid} creates more value than it spends")]
    NegativeFee { txid: Txid },
    #[error("block tries to overwrite an unspent transaction {0}")]
    Bip30(Txid),
    #[error("block height is not encoded in the coinbase script")]
    BadCoinbaseHeight,
    #[error("transaction locktime is not yet satisfied")]
    NonFinalTransaction,
    #[error("transaction locktime/sequence locks are not yet satisfied")]
    NonFinalSequence,
    #[error("script validation failed for transaction {txid} input {input}: {reason}")]
    Script {
        txid: Txid,
        input: usize,
        reason: String,
    },
}

impl ValidationError {
    /// Whether Core would cache this block as invalid after accepting its
    /// header.  Merkle and witness-commitment failures are deliberately
    /// treated as mutation failures: a peer may have supplied the wrong body
    /// for a valid header, so caching them would incorrectly poison the
    /// header.  UTXO, finality, and script failures, on the other hand, prove
    /// that the block itself is invalid and its descendants must be rejected.
    pub(crate) fn should_mark_block_invalid(&self) -> bool {
        matches!(
            self,
            Self::OversizedBlock
                | Self::TooManySigopsInConnect
                | Self::BadCoinbaseHeight
                | Self::MissingInput { .. }
                | Self::ImmatureCoinbase { .. }
                | Self::InputTotalOverflow
                | Self::AccumulatedFeeOverflow
                | Self::NegativeFee { .. }
                | Self::Bip30(_)
                | Self::NonFinalTransaction
                | Self::NonFinalSequence
                | Self::Script { .. }
                | Self::CoinbaseOverpay { .. }
                | Self::SubsidyOverflow
                | Self::ReducedDataOutputTooLarge(_)
        )
    }

    /// Return the reject reason used by Core's BIP22 proposal and submitblock
    /// responses. Keep this separate from `Display`: the latter is intended
    /// for operator diagnostics, while BIP22 exposes stable protocol strings.
    pub(crate) fn bip22_reject_reason(&self) -> String {
        match self {
            Self::WrongPreviousBlock => "inconclusive-not-best-prevblk".to_owned(),
            Self::BadTarget | Self::TargetAboveLimit => "bad-diffbits".to_owned(),
            Self::BadProofOfWork => "high-hash".to_owned(),
            Self::TimeTooOld => "time-too-old".to_owned(),
            Self::TimeTooNew => "time-too-new".to_owned(),
            Self::NodeExpired => "node-expired".to_owned(),
            Self::Bip94TimeWarp => "time-timewarp-attack".to_owned(),
            Self::EmptyBlock => "bad-blk-length".to_owned(),
            Self::BadMerkleRoot => "bad-txnmrklroot".to_owned(),
            Self::BadWitnessNonceSize => "bad-witness-nonce-size".to_owned(),
            Self::BadWitnessMerkleMatch => "bad-witness-merkle-match".to_owned(),
            Self::UnexpectedWitness => "unexpected-witness".to_owned(),
            Self::BadSignetSolution => "bad-signet-blksig".to_owned(),
            Self::OversizedBlock => "bad-blk-weight".to_owned(),
            Self::OversizedBlockBase => "bad-blk-length".to_owned(),
            Self::OversizedTransaction(_) => "bad-txns-oversize".to_owned(),
            Self::TooManySigops => "bad-blk-sigops, out-of-bounds SigOpCount".to_owned(),
            Self::TooManySigopsInConnect => "bad-blk-sigops, out-of-bounds SigOpCount".to_owned(),
            Self::BadBlockVersion { actual, .. } => {
                format!("bad-version(0x{:08x})", *actual as u32)
            }
            Self::BadVersionBits { deployment, .. } => format!("bad-version-{deployment}"),
            Self::BadCoinbase => "bad-cb-length".to_owned(),
            Self::FirstTransactionNotCoinbase => "bad-cb-missing".to_owned(),
            Self::ExtraCoinbase(_) => "bad-cb-multiple".to_owned(),
            Self::NullPrevout(_) => "bad-txns-prevout-null".to_owned(),
            Self::EmptyInputs(_) => "bad-txns-vin-empty".to_owned(),
            Self::EmptyOutputs(_) => "bad-txns-vout-empty".to_owned(),
            Self::DuplicateInput(_) => "bad-txns-inputs-duplicate".to_owned(),
            Self::DuplicateTransaction(_) => "bad-txns-duplicate".to_owned(),
            Self::NegativeOutputValue(_) => "bad-txns-vout-negative".to_owned(),
            Self::BadOutputValue(_) => "bad-txns-vout-toolarge".to_owned(),
            Self::ReducedDataOutputTooLarge(_) => "bad-txns-vout-script-toolarge".to_owned(),
            Self::OutputTotalOverflow => "bad-txns-txouttotal-toolarge".to_owned(),
            Self::SubsidyOverflow => "bad-txns-fee-outofrange".to_owned(),
            Self::CoinbaseOverpay { .. } => "bad-cb-amount".to_owned(),
            Self::MissingInput { .. } => "bad-txns-inputs-missingorspent".to_owned(),
            Self::ImmatureCoinbase { .. } => "bad-txns-premature-spend-of-coinbase".to_owned(),
            Self::InputTotalOverflow => "bad-txns-inputvalues-outofrange".to_owned(),
            Self::AccumulatedFeeOverflow => "bad-txns-accumulated-fee-outofrange".to_owned(),
            Self::NegativeFee { .. } => "bad-txns-in-belowout".to_owned(),
            Self::Bip30(_) => "bad-txns-BIP30".to_owned(),
            Self::BadCoinbaseHeight => "bad-cb-height".to_owned(),
            Self::NonFinalTransaction => "bad-txns-nonfinal".to_owned(),
            Self::NonFinalSequence => "bad-txns-nonfinal".to_owned(),
            Self::Script { reason, .. } => {
                format!("mandatory-script-verify-flag-failed ({reason})")
            }
        }
    }
}

const REDUCED_DATA_MAX_SCRIPT_ELEMENT_SIZE: usize = 256;
const REDUCED_DATA_MAX_OUTPUT_SCRIPT_SIZE: usize = 34;
const REDUCED_DATA_MAX_OUTPUT_DATA_SIZE: usize = 83;
const REDUCED_DATA_TAPROOT_CONTROL_BASE_SIZE: usize = 33;
const REDUCED_DATA_TAPROOT_CONTROL_NODE_SIZE: usize = 32;
const REDUCED_DATA_TAPROOT_CONTROL_MAX_SIZE: usize =
    REDUCED_DATA_TAPROOT_CONTROL_BASE_SIZE + REDUCED_DATA_TAPROOT_CONTROL_NODE_SIZE * 7;

pub(crate) fn validate_reduced_data_output_sizes(
    transaction: &Transaction,
) -> Result<(), ValidationError> {
    for output in &transaction.output {
        let script = output.script_pubkey.as_bytes();
        if script.is_empty() {
            continue;
        }
        let limit = if script[0] == 0x6a {
            REDUCED_DATA_MAX_OUTPUT_DATA_SIZE
        } else {
            REDUCED_DATA_MAX_OUTPUT_SCRIPT_SIZE
        };
        if script.len() > limit {
            return Err(ValidationError::ReducedDataOutputTooLarge(
                transaction.compute_txid(),
            ));
        }
    }
    Ok(())
}

fn reduced_data_script_pushes_fit(script: &Script) -> bool {
    script.instructions().all(|instruction| match instruction {
        Ok(Instruction::PushBytes(bytes)) => bytes.len() <= REDUCED_DATA_MAX_SCRIPT_ELEMENT_SIZE,
        Ok(Instruction::Op(_)) | Err(_) => true,
    })
}

fn reduced_data_script_error(transaction: &Transaction, input: usize) -> ValidationError {
    ValidationError::Script {
        txid: transaction.compute_txid(),
        input,
        reason: "Push value size limit exceeded".to_owned(),
    }
}

/// Apply the structural parts of Core's REDUCED_DATA script flag that are not
/// available through the older libbitcoinconsensus ABI used by this crate.
/// The caller supplies each spent output's creation height because Core
/// deliberately exempts UTXOs created before the deployment activated.
pub(crate) fn validate_reduced_data_input_sizes(
    transaction: &Transaction,
    previous_outputs: &[TxOut],
    previous_heights: &[u32],
    activation_height: u32,
) -> Result<(), ValidationError> {
    for (input_index, ((input, previous_output), previous_height)) in transaction
        .input
        .iter()
        .zip(previous_outputs)
        .zip(previous_heights)
        .enumerate()
    {
        if *previous_height < activation_height {
            continue;
        }

        let script_sig_items = push_only_stack_items(input.script_sig.as_script());
        if previous_output.script_pubkey.is_p2sh() {
            if let Some(items) = &script_sig_items {
                for item in items.iter().take(items.len().saturating_sub(1)) {
                    if item.len() > REDUCED_DATA_MAX_SCRIPT_ELEMENT_SIZE {
                        return Err(reduced_data_script_error(transaction, input_index));
                    }
                }
                if let Some(redeem_script) = items.last()
                    && !reduced_data_script_pushes_fit(Script::from_bytes(redeem_script))
                {
                    return Err(reduced_data_script_error(transaction, input_index));
                }
            } else if !reduced_data_script_pushes_fit(input.script_sig.as_script()) {
                return Err(reduced_data_script_error(transaction, input_index));
            }
        } else if !reduced_data_script_pushes_fit(input.script_sig.as_script()) {
            return Err(reduced_data_script_error(transaction, input_index));
        }
        if !reduced_data_script_pushes_fit(previous_output.script_pubkey.as_script()) {
            return Err(reduced_data_script_error(transaction, input_index));
        }

        let witness_program = if previous_output.script_pubkey.is_witness_program() {
            Some(previous_output.script_pubkey.clone())
        } else if previous_output.script_pubkey.is_p2sh() {
            script_sig_items
                .as_ref()
                .and_then(|items| items.last())
                .map(|redeem| ScriptBuf::from_bytes(redeem.clone()))
                .filter(|redeem| redeem.is_witness_program())
        } else {
            None
        };
        let Some(witness_program) = witness_program else {
            continue;
        };
        let witness_items = input.witness.iter().collect::<Vec<_>>();
        // Core treats the 4-byte Pay-to-Anchor program (v1, program 0x4e73)
        // as consensus-valid when its witness is empty. It remains subject
        // to the reduced-data limits when witness items are present.
        let is_p2a = witness_program.as_bytes() == [0x51, 0x02, 0x4e, 0x73];
        if is_p2a && witness_items.is_empty() {
            continue;
        }
        if witness_program.is_witness_program()
            && !witness_program.is_p2wpkh()
            && !witness_program.is_p2wsh()
            && !witness_program.is_p2tr()
        {
            return Err(reduced_data_script_error(transaction, input_index));
        } else if witness_program.is_p2wsh() {
            for item in witness_items
                .iter()
                .take(witness_items.len().saturating_sub(1))
            {
                if item.len() > REDUCED_DATA_MAX_SCRIPT_ELEMENT_SIZE {
                    return Err(reduced_data_script_error(transaction, input_index));
                }
            }
            if let Some(witness_script) = witness_items.last()
                && !reduced_data_script_pushes_fit(Script::from_bytes(witness_script))
            {
                return Err(reduced_data_script_error(transaction, input_index));
            }
        } else if witness_program.is_p2tr() {
            if witness_items.len() >= 2 {
                let script_index = witness_items.len() - 2;
                let control = witness_items[script_index + 1];
                if control.len() < REDUCED_DATA_TAPROOT_CONTROL_BASE_SIZE
                    || control.len() > REDUCED_DATA_TAPROOT_CONTROL_MAX_SIZE
                    || (control.len() - REDUCED_DATA_TAPROOT_CONTROL_BASE_SIZE)
                        % REDUCED_DATA_TAPROOT_CONTROL_NODE_SIZE
                        != 0
                {
                    return Err(reduced_data_script_error(transaction, input_index));
                }
                for item in witness_items.iter().take(script_index) {
                    if item.len() > REDUCED_DATA_MAX_SCRIPT_ELEMENT_SIZE {
                        return Err(reduced_data_script_error(transaction, input_index));
                    }
                }
                let taproot_script = Script::from_bytes(witness_items[script_index]);
                if !reduced_data_script_pushes_fit(taproot_script) {
                    return Err(reduced_data_script_error(transaction, input_index));
                }
                if control[0] & 0xfe == 0xc0
                    && (taproot_script.instructions().any(|instruction| {
                        matches!(
                            instruction,
                            Ok(Instruction::Op(op)) if matches!(op.to_u8(), 0x63 | 0x64)
                        )
                    }) || reduced_data_tapscript_has_op_success(taproot_script))
                {
                    return Err(reduced_data_script_error(transaction, input_index));
                }
                if witness_items.len() >= 3
                    && witness_items[script_index - 1].first() == Some(&0x50)
                {
                    return Err(reduced_data_script_error(transaction, input_index));
                }
            } else if witness_items
                .first()
                .is_some_and(|item| item.len() > REDUCED_DATA_MAX_SCRIPT_ELEMENT_SIZE)
            {
                return Err(reduced_data_script_error(transaction, input_index));
            }
        } else if witness_items
            .iter()
            .any(|item| item.len() > REDUCED_DATA_MAX_SCRIPT_ELEMENT_SIZE)
        {
            return Err(reduced_data_script_error(transaction, input_index));
        }
    }
    Ok(())
}

fn reduced_data_tapscript_has_op_success(script: &Script) -> bool {
    script.instructions().any(|instruction| {
        matches!(
            instruction,
            Ok(Instruction::Op(opcode))
                if opcode.classify(ClassifyContext::TapScript) == Class::SuccessOp
        )
    })
}

pub fn network_params(network: Network) -> &'static Params {
    network.params()
}

/// Return Core's difficulty-adjustment interval for the selected network.
///
/// Core's regtest chain parameters intentionally use a one-day interval
/// (144 blocks), while the bitcoin crate's generic regtest parameters retain
/// the two-week mainnet-style interval.
pub fn difficulty_adjustment_interval(network: Network) -> u32 {
    if network == Network::Regtest {
        144
    } else {
        network_params(network).difficulty_adjustment_interval() as u32
    }
}

/// Validate only the proof-of-work claim in a block header.
///
/// Core performs this cheap check before attempting to connect a submitted
/// block to its parent.  Keeping it separate from contextual header checks
/// lets callers preserve BIP22's `high-hash` result even for an otherwise
/// unknown-parent block.
pub fn validate_proof_of_work(
    network: Network,
    header: &bitcoin::block::Header,
) -> Result<(), ValidationError> {
    let compact = header.bits.to_consensus();
    let mantissa = compact & 0x007f_ffff;
    let compact_valid =
        mantissa != 0 && (compact & 0x0080_0000) == 0 && header.target() != Target::ZERO;
    if !compact_valid
        || header.target() > network_params(network).max_attainable_target
        || !header.target().is_met_by(header.block_hash())
    {
        return Err(ValidationError::BadProofOfWork);
    }
    Ok(())
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

pub fn bip9_deployments(network: Network) -> [Bip9Deployment; 3] {
    let testdummy = match network {
        Network::Regtest => Bip9Deployment {
            bit: 28,
            start_time: 0,
            timeout: i64::MAX,
            min_activation_height: 0,
            max_activation_height: Bip9Deployment::MAX_ACTIVATION_HEIGHT,
            active_duration: Bip9Deployment::PERMANENT_ACTIVE_DURATION,
            threshold: 108,
            period: 144,
        },
        Network::Bitcoin | Network::Signet => Bip9Deployment {
            bit: 28,
            start_time: Bip9Deployment::NEVER_ACTIVE_TIME,
            timeout: i64::MAX,
            min_activation_height: 0,
            max_activation_height: Bip9Deployment::MAX_ACTIVATION_HEIGHT,
            active_duration: Bip9Deployment::PERMANENT_ACTIVE_DURATION,
            threshold: 1815,
            period: 2016,
        },
        Network::Testnet | Network::Testnet4 => Bip9Deployment {
            bit: 28,
            start_time: Bip9Deployment::NEVER_ACTIVE_TIME,
            timeout: i64::MAX,
            min_activation_height: 0,
            max_activation_height: Bip9Deployment::MAX_ACTIVATION_HEIGHT,
            active_duration: Bip9Deployment::PERMANENT_ACTIVE_DURATION,
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
            max_activation_height: Bip9Deployment::MAX_ACTIVATION_HEIGHT,
            active_duration: Bip9Deployment::PERMANENT_ACTIVE_DURATION,
            threshold: 1815,
            period: 2016,
        },
        Network::Testnet => Bip9Deployment {
            bit: 2,
            start_time: 1_619_222_400,
            timeout: 1_628_640_000,
            min_activation_height: 0,
            max_activation_height: Bip9Deployment::MAX_ACTIVATION_HEIGHT,
            active_duration: Bip9Deployment::PERMANENT_ACTIVE_DURATION,
            threshold: 1512,
            period: 2016,
        },
        Network::Testnet4 => Bip9Deployment {
            bit: 2,
            start_time: Bip9Deployment::ALWAYS_ACTIVE_TIME,
            timeout: i64::MAX,
            min_activation_height: 0,
            max_activation_height: Bip9Deployment::MAX_ACTIVATION_HEIGHT,
            active_duration: Bip9Deployment::PERMANENT_ACTIVE_DURATION,
            threshold: 1512,
            period: 2016,
        },
        Network::Signet => Bip9Deployment {
            bit: 2,
            start_time: Bip9Deployment::ALWAYS_ACTIVE_TIME,
            timeout: i64::MAX,
            min_activation_height: 0,
            max_activation_height: Bip9Deployment::MAX_ACTIVATION_HEIGHT,
            active_duration: Bip9Deployment::PERMANENT_ACTIVE_DURATION,
            threshold: 1815,
            period: 2016,
        },
        Network::Regtest => Bip9Deployment {
            bit: 2,
            start_time: Bip9Deployment::ALWAYS_ACTIVE_TIME,
            timeout: i64::MAX,
            min_activation_height: 0,
            max_activation_height: Bip9Deployment::MAX_ACTIVATION_HEIGHT,
            active_duration: Bip9Deployment::PERMANENT_ACTIVE_DURATION,
            threshold: 108,
            period: 144,
        },
    };
    // `reduced_data` is retained as an opt-in regtest extension for focused
    // experiments, but it is not part of Bitcoin Core v31.1.  In particular,
    // do not enable it on mainnet: doing so would enforce a future mandatory
    // signaling window against valid v31.1 peer headers.
    let reduced_data = Bip9Deployment {
        bit: 4,
        start_time: Bip9Deployment::NEVER_ACTIVE_TIME,
        timeout: i64::MAX,
        min_activation_height: 0,
        max_activation_height: Bip9Deployment::MAX_ACTIVATION_HEIGHT,
        active_duration: Bip9Deployment::PERMANENT_ACTIVE_DURATION,
        threshold: 0,
        period: if network == Network::Regtest {
            144
        } else {
            2_016
        },
    };
    [testdummy, taproot, reduced_data]
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Bip9State {
    Defined,
    Started,
    LockedIn,
    Active,
    Failed,
    Expired,
}

impl Bip9State {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Defined => "defined",
            Self::Started => "started",
            Self::LockedIn => "locked_in",
            Self::Active => "active",
            Self::Failed => "failed",
            Self::Expired => "expired",
        }
    }
}

fn median_versionbits_time(headers: &[bitcoin::block::Header], end: usize) -> u32 {
    let start = end.saturating_sub(10);
    let mut times = headers[start..=end]
        .iter()
        .map(|header| header.time)
        .collect::<Vec<_>>();
    times.sort_unstable();
    times[times.len() / 2]
}

pub(crate) fn versionbits_signals(header: &bitcoin::block::Header, bit: u8) -> bool {
    let version = header.version.to_consensus() as u32;
    version & 0xe000_0000 == 0x2000_0000 && version & (1u32 << bit) != 0
}

/// Return the threshold state governing the block at `height` and the first
/// height at which that state applies. The header slice must start at genesis
/// and contain the branch through the queried parent or block, as applicable.
pub(crate) fn bip9_state_at_height(
    headers: &[bitcoin::block::Header],
    deployment: Bip9Deployment,
    height: u32,
) -> (Bip9State, u32) {
    if deployment.start_time == Bip9Deployment::ALWAYS_ACTIVE_TIME {
        return (Bip9State::Active, 0);
    }
    if deployment.start_time == Bip9Deployment::NEVER_ACTIVE_TIME {
        return (Bip9State::Failed, 0);
    }
    let period = deployment.period.max(1);
    let mut state = Bip9State::Defined;
    let mut since = 0;
    let mut activation_height: Option<u32> = None;
    let mut boundary = period;
    while boundary <= height {
        if headers.is_empty() {
            break;
        }
        let previous_end = usize::try_from(boundary - 1)
            .unwrap_or(usize::MAX)
            .min(headers.len().saturating_sub(1));
        let previous_start = usize::try_from(boundary.saturating_sub(period))
            .unwrap_or(usize::MAX)
            .min(previous_end);
        let median_time = median_versionbits_time(headers, previous_end);
        let signal_count = headers[previous_start..=previous_end]
            .iter()
            .filter(|header| versionbits_signals(header, deployment.bit))
            .count() as u32;
        let next_state = match state {
            Bip9State::Defined if i64::from(median_time) >= deployment.start_time => {
                Bip9State::Started
            }
            Bip9State::Started if signal_count >= deployment.threshold => Bip9State::LockedIn,
            Bip9State::Started
                if deployment.max_activation_height < Bip9Deployment::MAX_ACTIVATION_HEIGHT
                    && boundary >= deployment.max_activation_height.saturating_sub(period) =>
            {
                Bip9State::LockedIn
            }
            Bip9State::Started
                if deployment.timeout != i64::MAX
                    && i64::from(median_time) >= deployment.timeout =>
            {
                Bip9State::Failed
            }
            Bip9State::LockedIn if boundary >= deployment.min_activation_height => {
                Bip9State::Active
            }
            Bip9State::Active
                if deployment.active_duration < Bip9Deployment::PERMANENT_ACTIVE_DURATION
                    && activation_height.is_some_and(|height| {
                        boundary >= height.saturating_add(deployment.active_duration)
                    }) =>
            {
                Bip9State::Expired
            }
            _ => state,
        };
        if next_state != state {
            state = next_state;
            since = boundary;
            if state == Bip9State::Active {
                activation_height = Some(boundary);
            }
        }
        let Some(next_boundary) = boundary.checked_add(period) else {
            break;
        };
        boundary = next_boundary;
    }
    (state, since)
}

pub(crate) fn reduced_data_activation_height(
    headers: &[bitcoin::block::Header],
    deployment: Bip9Deployment,
    height: u32,
) -> Option<u32> {
    let (state, since) = bip9_state_at_height(headers, deployment, height);
    (state == Bip9State::Active).then_some(since)
}

/// Enforce Core's mandatory-signaling window for deployments with a
/// `max_activation_height`. The window covers the two periods immediately
/// before the forced lock-in period; blocks in that window must signal while
/// the deployment is still in STARTED.
pub(crate) fn validate_mandatory_version_bits_with_params(
    headers: &[bitcoin::block::Header],
    params: &DeploymentParameters,
    height: u32,
    version: i32,
) -> Result<(), ValidationError> {
    const VERSIONBITS_TOP_MASK: u32 = 0xe000_0000;
    const VERSIONBITS_TOP_BITS: u32 = 0x2000_0000;

    if height == 0 {
        return Ok(());
    }
    let version = version as u32;
    const DEPLOYMENT_NAMES: [&str; 3] = ["testdummy", "taproot", "reduced_data"];
    for (deployment_index, deployment) in params.bip9.into_iter().enumerate() {
        if deployment.max_activation_height >= Bip9Deployment::MAX_ACTIVATION_HEIGHT {
            continue;
        }
        let period = deployment.period.max(1);
        let enforcement_start = deployment
            .max_activation_height
            .saturating_sub(period.saturating_mul(2));
        let enforcement_end = deployment.max_activation_height.saturating_sub(period);
        if !(enforcement_start..enforcement_end).contains(&height) {
            continue;
        }
        let (state, _) = bip9_state_at_height(headers, deployment, height - 1);
        if state == Bip9State::Started
            && ((version & VERSIONBITS_TOP_MASK) != VERSIONBITS_TOP_BITS
                || version & (1u32 << deployment.bit) == 0)
        {
            return Err(ValidationError::BadVersionBits {
                deployment: DEPLOYMENT_NAMES[deployment_index],
                max_activation_height: deployment.max_activation_height,
            });
        }
    }
    Ok(())
}

/// Return the first unknown BIP9 version bit that has reached the active
/// state on the supplied active chain.
///
/// Core runs the same threshold state machine for every version bit that is
/// not currently assigned to a known deployment. An unknown bit is warned
/// about only after it has met the network threshold for one complete period
/// and then spent a complete period locked in. The headers slice is expected
/// to start at the network genesis block and remain in height order.
pub fn unknown_versionbits_active(
    headers: &[bitcoin::block::Header],
    network: Network,
) -> Option<u8> {
    unknown_versionbits_active_with_params(headers, &DeploymentParameters::for_network(network))
}

pub fn unknown_versionbits_active_with_params(
    headers: &[bitcoin::block::Header],
    params: &DeploymentParameters,
) -> Option<u8> {
    const VERSIONBITS_TOP_MASK: u32 = 0xe000_0000;
    const VERSIONBITS_TOP_BITS: u32 = 0x2000_0000;
    const VERSIONBITS_NUM_BITS: u8 = 29;

    if headers.is_empty() {
        return None;
    }

    let [testdummy, ..] = params.bip9;
    let known_bits = params
        .bip9
        .iter()
        .filter(|deployment| deployment.is_enabled())
        .fold(0u32, |bits, deployment| bits | (1u32 << deployment.bit));
    let period = usize::try_from(testdummy.period).ok()?;
    let threshold = usize::try_from(testdummy.threshold).ok()?;
    if period == 0 || threshold > period {
        return None;
    }
    let min_warning_height = match params.network {
        Network::Bitcoin => 483_840,
        Network::Testnet => 836_640,
        Network::Testnet4 | Network::Signet | Network::Regtest => 0,
    };

    // Every period starts with the state produced by the previous period.
    // The first period is DEFINED, the first boundary moves it to STARTED,
    // a successful signaling period moves it to LOCKED_IN, and the following
    // boundary moves it to ACTIVE.
    for bit in 0..VERSIONBITS_NUM_BITS {
        if known_bits & (1u32 << bit) != 0 {
            continue;
        }

        let mut state = 0u8; // 0=DEFINED, 1=STARTED, 2=LOCKED_IN, 3=ACTIVE
        let complete_periods = headers.len() / period;
        for period_index in 0..complete_periods {
            let start = period_index * period;
            let end = start + period;
            match state {
                0 => state = 1,
                1 => {
                    let count = headers[start..end]
                        .iter()
                        .enumerate()
                        .filter(|(offset, header)| {
                            let height = start + *offset;
                            let version = header.version.to_consensus() as u32;
                            height >= min_warning_height
                                && version & VERSIONBITS_TOP_MASK == VERSIONBITS_TOP_BITS
                                && version & (1u32 << bit) != 0
                        })
                        .count();
                    if count >= threshold {
                        state = 2;
                    }
                }
                2 => state = 3,
                _ => return Some(bit),
            }
            if state == 3 {
                return Some(bit);
            }
        }
    }
    None
}

/// Check only the period immediately preceding a complete current period.
/// Once the historical chain has been checked, this is sufficient to detect
/// a newly active unknown bit without rescanning the entire chain on every
/// period boundary.
pub fn unknown_versionbits_active_at_boundary(
    headers: &[bitcoin::block::Header],
    network: Network,
) -> Option<u8> {
    unknown_versionbits_active_at_boundary_with_params(
        headers,
        &DeploymentParameters::for_network(network),
    )
}

pub fn unknown_versionbits_active_at_boundary_with_params(
    headers: &[bitcoin::block::Header],
    params: &DeploymentParameters,
) -> Option<u8> {
    const VERSIONBITS_TOP_MASK: u32 = 0xe000_0000;
    const VERSIONBITS_TOP_BITS: u32 = 0x2000_0000;
    const VERSIONBITS_NUM_BITS: u8 = 29;

    let [testdummy, ..] = params.bip9;
    let known_bits = params
        .bip9
        .iter()
        .filter(|deployment| deployment.is_enabled())
        .fold(0u32, |bits, deployment| bits | (1u32 << deployment.bit));
    let period = usize::try_from(testdummy.period).ok()?;
    let threshold = usize::try_from(testdummy.threshold).ok()?;
    if period == 0 || threshold > period || headers.len() < period * 3 {
        return None;
    }
    if headers.len() % period != 0 {
        return None;
    }
    let min_warning_height = match params.network {
        Network::Bitcoin => 483_840,
        Network::Testnet => 836_640,
        Network::Testnet4 | Network::Signet | Network::Regtest => 0,
    };
    let start = headers.len() - period * 2;
    let end = headers.len() - period;

    for bit in 0..VERSIONBITS_NUM_BITS {
        if known_bits & (1u32 << bit) != 0 {
            continue;
        }
        let count = headers[start..end]
            .iter()
            .enumerate()
            .filter(|(offset, header)| {
                let height = start + *offset;
                let version = header.version.to_consensus() as u32;
                height >= min_warning_height
                    && version & VERSIONBITS_TOP_MASK == VERSIONBITS_TOP_BITS
                    && version & (1u32 << bit) != 0
            })
            .count();
        if count >= threshold {
            return Some(bit);
        }
    }
    None
}

pub fn script_flags_for_block(network: Network, height: u32, block_time: u32) -> u32 {
    let _ = block_time;
    script_flags_for_block_with_hash(network, height, None)
}

/// Return the consensus script flags for a block, including Core's historical
/// block-specific exceptions.
pub fn script_flags_for_block_with_hash(
    network: Network,
    height: u32,
    block_hash: Option<BlockHash>,
) -> u32 {
    script_flags_for_block_with_params(
        &DeploymentParameters::for_network(network),
        height,
        block_hash,
    )
}

pub fn script_flags_for_block_with_params(
    params: &DeploymentParameters,
    height: u32,
    block_hash: Option<BlockHash>,
) -> u32 {
    let heights = params.buried;
    // Core keeps these flags enabled for historical block replay because only
    // the listed blocks violate the modern rules. The block hash is required
    // to reproduce those exceptions exactly.
    let mut flags = bitcoinconsensus::VERIFY_P2SH
        | bitcoinconsensus::VERIFY_WITNESS
        | bitcoinconsensus::VERIFY_TAPROOT;
    let hash = block_hash.map(|hash| hash.to_string());
    let exception = match (params.network, hash.as_deref()) {
        (
            Network::Bitcoin,
            Some("00000000000002dc756eebf4f49723ed8d30cc28a5f108eb94b1ba88ac4f9c22"),
        )
        | (
            Network::Testnet,
            Some("00000000dd30457c001f4095d208cc1296b0eed002427aa599874af7a432b105"),
        ) => Some(bitcoinconsensus::VERIFY_NONE),
        (
            Network::Bitcoin,
            Some("0000000000000000000f14c35b2d841e986ab5441de8c585d5ffe55ea1e395ad"),
        ) => Some(bitcoinconsensus::VERIFY_P2SH | bitcoinconsensus::VERIFY_WITNESS),
        _ => None,
    };
    if let Some(exception) = exception {
        flags = exception;
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

/// Enforce the BIP94 difficulty-adjustment timestamp rule.
///
/// Core enables this rule by default on Testnet4 and exposes it on regtest
/// through the `-test=bip94` startup option.
pub fn validate_bip94_timewarp(
    network: Network,
    height: u32,
    block_time: u32,
    previous_block_time: u32,
) -> Result<(), ValidationError> {
    validate_bip94_timewarp_with_params(
        &DeploymentParameters::for_network(network),
        height,
        block_time,
        previous_block_time,
    )
}

pub fn validate_bip94_timewarp_with_params(
    params: &DeploymentParameters,
    height: u32,
    block_time: u32,
    previous_block_time: u32,
) -> Result<(), ValidationError> {
    if !params.bip94 {
        return Ok(());
    }
    let difficulty_interval = difficulty_adjustment_interval(params.network);
    if height % difficulty_interval == 0 && block_time < previous_block_time.saturating_sub(600) {
        return Err(ValidationError::Bip94TimeWarp);
    }
    Ok(())
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
    if u64::from(header.time) > time::unix_time().saturating_add(2 * 60 * 60) {
        return Err(ValidationError::TimeTooNew);
    }
    let compact = header.bits.to_consensus();
    let mantissa = compact & 0x007f_ffff;
    let compact_valid =
        mantissa != 0 && (compact & 0x0080_0000) == 0 && header.target() != Target::ZERO;
    if check_pow {
        // Core's CheckBlockHeader validates the claimed target and proof of
        // work before ContextualCheckBlockHeader compares nBits with the
        // difficulty required by the parent.  Keep that ordering so
        // submitblock reports "high-hash" for malformed or out-of-range
        // compact targets rather than the contextual "bad-diffbits" result.
        if !compact_valid
            || header.target() > network_params(network).max_attainable_target
            || !header.target().is_met_by(header.block_hash())
        {
            return Err(ValidationError::BadProofOfWork);
        }
    } else if !compact_valid {
        return Err(ValidationError::BadTarget);
    }
    if header.target() != expected_target
        || header.bits.to_consensus() != expected_target.to_compact_lossy().to_consensus()
    {
        return Err(ValidationError::BadTarget);
    }
    if header.target() > network_params(network).max_attainable_target {
        return Err(ValidationError::TargetAboveLimit);
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

/// Run the context-free body checks that Core performs before admitting a
/// block header through `AcceptBlockHeader`.
///
/// In particular, merkle-root failures must not leave the otherwise valid
/// header indexed: another body with the same header may be valid. Witness
/// commitment, full-weight, height, finality, and UTXO-dependent checks are
/// intentionally deferred until after the header has been accepted because
/// those checks require chain context.
pub(crate) fn validate_block_before_header(
    block: &Block,
    signet_challenge: Option<&[u8]>,
) -> Result<(), ValidationError> {
    if block.txdata.is_empty() {
        return Err(ValidationError::EmptyBlock);
    }
    if let Some(challenge) = signet_challenge {
        validate_signet_block_solution(block, challenge)?;
    }

    let transaction_ids = block
        .txdata
        .iter()
        .map(Transaction::compute_txid)
        .collect::<Vec<_>>();
    let (merkle_root, mutated_txid) = merkle_root_and_mutated_txid(&transaction_ids);
    if merkle_root != Some(block.header.merkle_root) {
        return Err(ValidationError::BadMerkleRoot);
    }
    if let Some(txid) = mutated_txid {
        return Err(ValidationError::DuplicateTransaction(txid));
    }

    let base_size = serialize(&block.header).len()
        + VarInt::from(block.txdata.len()).size()
        + block
            .txdata
            .iter()
            .map(|transaction| transaction.base_size())
            .sum::<usize>();
    if base_size.saturating_mul(4) > MAX_BLOCK_WEIGHT {
        return Err(ValidationError::OversizedBlockBase);
    }

    let first = &block.txdata[0];
    if !first.is_coinbase() {
        return Err(ValidationError::FirstTransactionNotCoinbase);
    }
    let mut legacy_sigop_cost = 0usize;
    for (position, (transaction, txid)) in block
        .txdata
        .iter()
        .zip(transaction_ids.iter().copied())
        .enumerate()
    {
        if transaction.base_size().saturating_mul(4) > MAX_BLOCK_WEIGHT {
            return Err(ValidationError::OversizedTransaction(txid));
        }
        if position > 0 && transaction.is_coinbase() {
            return Err(ValidationError::ExtraCoinbase(txid));
        }
        if transaction.input.is_empty() {
            return Err(ValidationError::EmptyInputs(txid));
        }
        if transaction.output.is_empty() {
            return Err(ValidationError::EmptyOutputs(txid));
        }

        let mut transaction_output_total = 0u64;
        for output in &transaction.output {
            let value = output.value.to_sat();
            if value > i64::MAX as u64 {
                return Err(ValidationError::NegativeOutputValue(txid));
            }
            if output.value > Amount::MAX_MONEY {
                return Err(ValidationError::BadOutputValue(txid));
            }
            transaction_output_total = transaction_output_total
                .checked_add(value)
                .ok_or(ValidationError::OutputTotalOverflow)?;
        }
        if transaction_output_total > Amount::MAX_MONEY.to_sat() {
            return Err(ValidationError::OutputTotalOverflow);
        }

        let mut inputs = HashSet::with_capacity(transaction.input.len());
        for input in &transaction.input {
            if !inputs.insert(input.previous_output) {
                return Err(ValidationError::DuplicateInput(txid));
            }
        }
        if !transaction.is_coinbase()
            && transaction
                .input
                .iter()
                .any(|input| input.previous_output.is_null())
        {
            return Err(ValidationError::NullPrevout(txid));
        }
        if transaction.is_coinbase()
            && (transaction.input[0].script_sig.len() < 2
                || transaction.input[0].script_sig.len() > 100)
        {
            return Err(ValidationError::BadCoinbase);
        }

        legacy_sigop_cost =
            legacy_sigop_cost.saturating_add(legacy_sigop_cost_for_transaction(transaction));
        if legacy_sigop_cost > MAX_BLOCK_SIGOP_COST {
            return Err(ValidationError::TooManySigops);
        }
    }
    Ok(())
}

fn validate_witness_commitment(
    block: &Block,
    expect_witness_commitment: bool,
) -> Result<(), ValidationError> {
    const MAGIC: [u8; 6] = [0x6a, 0x24, 0xaa, 0x21, 0xa9, 0xed];
    let commitment = block.txdata.first().and_then(|coinbase| {
        coinbase
            .output
            .iter()
            .rposition(|output| {
                output.script_pubkey.len() >= 38 && output.script_pubkey.as_bytes()[..6] == MAGIC
            })
            .map(|index| &coinbase.output[index])
    });

    if expect_witness_commitment {
        if let Some(output) = commitment {
            let coinbase = block
                .txdata
                .first()
                .ok_or(ValidationError::BadWitnessMerkleMatch)?;
            let witness = coinbase
                .input
                .first()
                .map(|input| &input.witness)
                .ok_or(ValidationError::BadWitnessNonceSize)?;
            if witness.len() != 1 || witness[0].len() != 32 {
                return Err(ValidationError::BadWitnessNonceSize);
            }
            let commitment = WitnessCommitment::from_slice(&output.script_pubkey.as_bytes()[6..38])
                .map_err(|_| ValidationError::BadWitnessMerkleMatch)?;
            let witness_root = block
                .witness_root()
                .ok_or(ValidationError::BadWitnessMerkleMatch)?;
            let expected = Block::compute_witness_commitment(&witness_root, &witness[0]);
            if commitment != expected {
                return Err(ValidationError::BadWitnessMerkleMatch);
            }
        } else if block.txdata.iter().any(|transaction| {
            transaction
                .input
                .iter()
                .any(|input| !input.witness.is_empty())
        }) {
            return Err(ValidationError::UnexpectedWitness);
        }
    } else if block.txdata.iter().any(|transaction| {
        transaction
            .input
            .iter()
            .any(|input| !input.witness.is_empty())
    }) {
        return Err(ValidationError::UnexpectedWitness);
    }
    Ok(())
}

pub fn validate_block_structure_with_signet(
    block: &Block,
    network: Network,
    height: u32,
    expected_coinbase_value: u64,
    signet_challenge: Option<&[u8]>,
) -> Result<BlockValidationStats, ValidationError> {
    validate_block_structure_with_signet_options_with_params(
        block,
        &DeploymentParameters::for_network(network),
        height,
        expected_coinbase_value,
        signet_challenge,
        true,
    )
}

#[cfg(test)]
pub(crate) fn validate_block_structure_with_signet_options(
    block: &Block,
    network: Network,
    height: u32,
    expected_coinbase_value: u64,
    signet_challenge: Option<&[u8]>,
    check_signet_solution: bool,
) -> Result<BlockValidationStats, ValidationError> {
    validate_block_structure_with_signet_options_with_params(
        block,
        &DeploymentParameters::for_network(network),
        height,
        expected_coinbase_value,
        signet_challenge,
        check_signet_solution,
    )
}

pub(crate) fn validate_block_structure_with_signet_options_with_params(
    block: &Block,
    params: &DeploymentParameters,
    height: u32,
    expected_coinbase_value: u64,
    signet_challenge: Option<&[u8]>,
    check_signet_solution: bool,
) -> Result<BlockValidationStats, ValidationError> {
    let transaction_ids = block
        .txdata
        .iter()
        .map(Transaction::compute_txid)
        .collect::<Vec<_>>();
    validate_block_structure_with_signet_options_with_params_and_txids(
        block,
        &transaction_ids,
        params,
        height,
        expected_coinbase_value,
        signet_challenge,
        check_signet_solution,
    )
}

pub(crate) fn validate_block_structure_with_signet_options_with_params_and_txids(
    block: &Block,
    transaction_ids: &[Txid],
    params: &DeploymentParameters,
    height: u32,
    expected_coinbase_value: u64,
    signet_challenge: Option<&[u8]>,
    check_signet_solution: bool,
) -> Result<BlockValidationStats, ValidationError> {
    validate_block_structure_with_options_internal(
        block,
        transaction_ids,
        params,
        height,
        expected_coinbase_value,
        signet_challenge,
        check_signet_solution,
        true,
        true,
    )
}

/// Validate the context-free portion of a block with the same switches used
/// by Core's mining interface.  A miner may deliberately omit the merkle-root
/// check while checking a block assembled by external software; all other
/// structure and witness rules still run.
pub(crate) fn validate_block_structure_with_signet_options_with_params_and_merkle(
    block: &Block,
    params: &DeploymentParameters,
    height: u32,
    expected_coinbase_value: u64,
    signet_challenge: Option<&[u8]>,
    check_signet_solution: bool,
    check_merkle_root: bool,
) -> Result<BlockValidationStats, ValidationError> {
    let transaction_ids = block
        .txdata
        .iter()
        .map(Transaction::compute_txid)
        .collect::<Vec<_>>();
    validate_block_structure_with_options_internal(
        block,
        &transaction_ids,
        params,
        height,
        expected_coinbase_value,
        signet_challenge,
        check_signet_solution,
        check_merkle_root,
        true,
    )
}

/// Validate a block for `verifychain` without reapplying contextual witness
/// activation. Core's VerifyDB checks block structure and ConnectBlock, but
/// deliberately does not rerun ContextualCheckBlock; this matters when a
/// regtest node is restarted with a different test activation height.
pub(crate) fn validate_block_structure_for_verification(
    block: &Block,
    params: &DeploymentParameters,
    height: u32,
    expected_coinbase_value: u64,
    signet_challenge: Option<&[u8]>,
) -> Result<BlockValidationStats, ValidationError> {
    let transaction_ids = block
        .txdata
        .iter()
        .map(Transaction::compute_txid)
        .collect::<Vec<_>>();
    validate_block_structure_with_options_internal(
        block,
        &transaction_ids,
        params,
        height,
        expected_coinbase_value,
        signet_challenge,
        true,
        true,
        false,
    )
}

/// Compute the merkle root and report a hash involved in a tree mutation,
/// matching Bitcoin Core's `ComputeMerkleRoot` behavior. An odd final hash is
/// repeated for hashing but does not count as a mutation; only an actual pair
/// of equal entries does.
fn merkle_root_and_mutated_txid(transaction_ids: &[Txid]) -> (Option<TxMerkleNode>, Option<Txid>) {
    if transaction_ids.is_empty() {
        return (None, None);
    }
    let mut layer = transaction_ids.to_vec();
    let mut mutated = None;

    while layer.len() > 1 {
        let mut next = Vec::with_capacity(layer.len().div_ceil(2));
        for pair in layer.chunks(2) {
            let left = pair[0];
            let right = *pair.get(1).unwrap_or(&left);
            if pair.len() == 2 && left == right && mutated.is_none() {
                mutated = Some(left);
            }

            let mut engine = bitcoin::hashes::sha256d::Hash::engine();
            engine.input(&left.to_raw_hash().to_byte_array());
            engine.input(&right.to_raw_hash().to_byte_array());
            next.push(Txid::from_raw_hash(
                bitcoin::hashes::sha256d::Hash::from_engine(engine),
            ));
        }
        layer = next;
    }

    (
        Some(TxMerkleNode::from_raw_hash(layer[0].to_raw_hash())),
        mutated,
    )
}

#[allow(clippy::too_many_arguments)]
fn validate_block_structure_with_options_internal(
    block: &Block,
    transaction_ids: &[Txid],
    params: &DeploymentParameters,
    height: u32,
    expected_coinbase_value: u64,
    signet_challenge: Option<&[u8]>,
    check_signet_solution: bool,
    check_merkle_root: bool,
    check_witness_commitment: bool,
) -> Result<BlockValidationStats, ValidationError> {
    if block.txdata.is_empty() {
        return Err(ValidationError::EmptyBlock);
    }
    debug_assert_eq!(transaction_ids.len(), block.txdata.len());
    validate_block_version_with_params(params, height, block.header.version.to_consensus())?;
    if check_merkle_root {
        let (merkle_root, mutated_txid) = merkle_root_and_mutated_txid(transaction_ids);
        if merkle_root != Some(block.header.merkle_root) {
            return Err(ValidationError::BadMerkleRoot);
        }
        if let Some(txid) = mutated_txid {
            return Err(ValidationError::DuplicateTransaction(txid));
        }
    }
    if check_witness_commitment {
        validate_witness_commitment(block, height >= params.buried.segwit)?;
    }
    let base_size = serialize(&block.header).len()
        + VarInt::from(block.txdata.len()).size()
        + block
            .txdata
            .iter()
            .map(|transaction| transaction.base_size())
            .sum::<usize>();
    if base_size.saturating_mul(4) > MAX_BLOCK_WEIGHT {
        return Err(ValidationError::OversizedBlockBase);
    }
    if block.weight().to_wu() > MAX_BLOCK_WEIGHT as u64 {
        return Err(ValidationError::OversizedBlock);
    }
    let first = &block.txdata[0];
    if !first.is_coinbase() {
        return Err(ValidationError::FirstTransactionNotCoinbase);
    }

    let coinbase_total = first
        .output
        .iter()
        .try_fold(0u64, |total, output| {
            total.checked_add(output.value.to_sat())
        })
        .ok_or(ValidationError::OutputTotalOverflow)?;
    let mut total_output_sat = 0u64;
    let mut legacy_sigop_cost = 0usize;
    for (position, (tx, txid)) in block
        .txdata
        .iter()
        .zip(transaction_ids.iter().copied())
        .enumerate()
    {
        if tx.base_size().saturating_mul(4) > MAX_BLOCK_WEIGHT {
            return Err(ValidationError::OversizedTransaction(txid));
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
        let mut tx_total = 0u64;
        for output in &tx.output {
            let value = output.value.to_sat();
            if output.value.to_sat() > i64::MAX as u64 {
                return Err(ValidationError::NegativeOutputValue(txid));
            }
            if output.value > Amount::MAX_MONEY {
                return Err(ValidationError::BadOutputValue(txid));
            }
            tx_total = tx_total
                .checked_add(value)
                .ok_or(ValidationError::OutputTotalOverflow)?;
        }
        if tx_total > Amount::MAX_MONEY.to_sat() {
            return Err(ValidationError::OutputTotalOverflow);
        }
        let mut inputs = HashSet::with_capacity(tx.input.len());
        for input in &tx.input {
            if !inputs.insert(input.previous_output) {
                return Err(ValidationError::DuplicateInput(txid));
            }
        }
        if !tx.is_coinbase() && tx.input.iter().any(|input| input.previous_output.is_null()) {
            return Err(ValidationError::NullPrevout(txid));
        }
        if tx.is_coinbase()
            && (tx.input[0].script_sig.len() < 2 || tx.input[0].script_sig.len() > 100)
        {
            return Err(ValidationError::BadCoinbase);
        }
        total_output_sat = total_output_sat
            .checked_add(tx_total)
            .ok_or(ValidationError::OutputTotalOverflow)?;
        legacy_sigop_cost = legacy_sigop_cost.saturating_add(legacy_sigop_cost_for_transaction(tx));
        if legacy_sigop_cost > MAX_BLOCK_SIGOP_COST {
            return Err(ValidationError::TooManySigops);
        }
    }
    if height >= params.buried.bip34 {
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
    if coinbase_total > expected_coinbase_value {
        return Err(ValidationError::CoinbaseOverpay {
            actual: coinbase_total,
            allowed: expected_coinbase_value,
        });
    }
    if check_signet_solution && let Some(challenge) = signet_challenge {
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
    lock_time_cutoff: u32,
    csv_active: bool,
    previous_entries: &[crate::chain::UtxoEntry],
) -> Result<(), ValidationError> {
    let metadata = previous_entries
        .iter()
        .map(|entry| (entry.height, entry.median_time_past))
        .collect::<Vec<_>>();
    validate_transaction_finality_with_metadata(
        transaction,
        height,
        lock_time_cutoff,
        csv_active,
        &metadata,
    )
}

/// Check the absolute nLockTime portion of transaction finality.
///
/// Block connection can validate relative locks as each prevout is already
/// borrowed. Keeping this part separate avoids materializing a metadata
/// vector merely to make a second pass over the inputs.
pub fn validate_transaction_absolute_finality(
    transaction: &Transaction,
    height: u32,
    lock_time_cutoff: u32,
) -> Result<(), ValidationError> {
    if !transaction.is_lock_time_enabled() {
        return Ok(());
    }
    let lock_time = transaction.lock_time.to_consensus_u32();
    if lock_time == 0 {
        return Ok(());
    }
    let limit = if lock_time < LOCK_TIME_THRESHOLD {
        height
    } else {
        lock_time_cutoff
    };
    if lock_time >= limit {
        return Err(ValidationError::NonFinalTransaction);
    }
    Ok(())
}

/// Check one BIP68 relative lock while its spent coin is borrowed.
///
/// This is equivalent to Core's `CalculateSequenceLocks` plus
/// `EvaluateSequenceLocks` for one input. The stored median time is the MTP
/// of the block before the one that created the output, which is the same
/// time base Core derives from the coin's height.
pub fn validate_transaction_sequence_lock_input(
    input: &bitcoin::TxIn,
    transaction_version: bitcoin::transaction::Version,
    height: u32,
    lock_time_cutoff: u32,
    csv_active: bool,
    entry_height: u32,
    entry_median_time_past: u32,
) -> Result<(), ValidationError> {
    if !csv_active || transaction_version.0 < 2 || !input.sequence.is_relative_lock_time() {
        return Ok(());
    }
    let sequence = input.sequence.to_consensus_u32();
    let relative = u32::from((sequence & 0x0000_ffff) as u16);
    if input.sequence.is_height_locked() {
        if height < entry_height.saturating_add(relative) {
            return Err(ValidationError::NonFinalSequence);
        }
    } else {
        let relative_seconds = relative.saturating_mul(512);
        let required_time = i64::from(entry_median_time_past) + i64::from(relative_seconds) - 1;
        if i64::from(lock_time_cutoff) <= required_time {
            return Err(ValidationError::NonFinalSequence);
        }
    }
    Ok(())
}

/// Validate transaction finality using only the metadata needed by BIP68.
/// Consensus block connection already owns the full prevout for undo and
/// script work; retaining a second full `TxOut` per input just to check height
/// and median-time locks needlessly multiplies IBD allocations.
pub fn validate_transaction_finality_with_metadata(
    transaction: &Transaction,
    height: u32,
    lock_time_cutoff: u32,
    csv_active: bool,
    previous_entries: &[(u32, u32)],
) -> Result<(), ValidationError> {
    validate_transaction_absolute_finality(transaction, height, lock_time_cutoff)?;
    if !csv_active || transaction.version.0 < 2 || previous_entries.len() != transaction.input.len()
    {
        return Ok(());
    }
    for (input, (entry_height, entry_median_time_past)) in
        transaction.input.iter().zip(previous_entries)
    {
        validate_transaction_sequence_lock_input(
            input,
            transaction.version,
            height,
            lock_time_cutoff,
            csv_active,
            *entry_height,
            *entry_median_time_past,
        )?;
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
    validate_transaction_scripts_at_time_with_block_hash(
        network,
        height,
        block_time,
        None,
        transaction,
        previous_outputs,
    )
}

pub fn validate_transaction_scripts_at_time_with_block_hash(
    network: Network,
    height: u32,
    block_time: u32,
    block_hash: Option<BlockHash>,
    transaction: &Transaction,
    previous_outputs: &[bitcoin::TxOut],
) -> Result<(), ValidationError> {
    validate_transaction_scripts_at_time_with_block_hash_with_params(
        &DeploymentParameters::for_network(network),
        height,
        block_time,
        block_hash,
        transaction,
        previous_outputs,
    )
}

pub fn validate_transaction_scripts_at_time_with_block_hash_with_params(
    params: &DeploymentParameters,
    height: u32,
    block_time: u32,
    block_hash: Option<BlockHash>,
    transaction: &Transaction,
    previous_outputs: &[bitcoin::TxOut],
) -> Result<(), ValidationError> {
    let _ = block_time;
    let flags = script_flags_for_block_with_params(params, height, block_hash);
    validate_transaction_scripts_with_flags(transaction, previous_outputs, flags)
}

/// Core's mempool verifier uses all mandatory script rules regardless of the
/// active chain height. This is stricter than the height-dependent flags used
/// when validating a block and prevents policy-validity from changing merely
/// because a node is on regtest or an early testnet block.
pub(crate) fn mempool_script_flags() -> u32 {
    bitcoinconsensus::VERIFY_ALL_PRE_TAPROOT | bitcoinconsensus::VERIFY_TAPROOT
}

pub(crate) fn validate_transaction_scripts_with_flags(
    transaction: &Transaction,
    previous_outputs: &[bitcoin::TxOut],
    flags: u32,
) -> Result<(), ValidationError> {
    if previous_outputs.len() != transaction.input.len() {
        return Err(ValidationError::Script {
            txid: transaction.compute_txid(),
            input: 0,
            reason: "previous-output count does not match input count".to_owned(),
        });
    }
    if let Err(input) = verify_transaction_scripts(transaction, previous_outputs, flags) {
        return Err(ValidationError::Script {
            txid: transaction.compute_txid(),
            input,
            reason: script_error_reason_hint(transaction, previous_outputs, input)
                .map(str::to_owned)
                .unwrap_or_else(|| "script verification failed".to_owned()),
        });
    }
    Ok(())
}

/// libbitcoinconsensus exposes only the coarse `ERR_SCRIPT` result, while
/// Core's RPC and block rejection paths retain the script interpreter's
/// human-readable reason. Recover the consensus reasons that can be inferred
/// safely from the transaction's executed script shape.
pub(crate) fn script_error_reason_hint(
    transaction: &Transaction,
    previous_outputs: &[TxOut],
    input_index: usize,
) -> Option<&'static str> {
    let input = transaction.input.get(input_index)?;
    let previous_output = previous_outputs.get(input_index)?;

    if previous_output.script_pubkey.is_witness_program() && !input.script_sig.is_empty() {
        return Some("Witness requires empty scriptSig");
    }
    if !input.witness.is_empty() && !spends_witness_program(input, previous_output) {
        return Some("Witness provided for non-witness script");
    }
    if input.witness.is_empty()
        && (spends_witness_program(input, previous_output)
            || (previous_output.script_pubkey.is_p2sh()
                && push_only_stack_items(input.script_sig.as_script()).is_some_and(|items| {
                    items.len() > 1
                        && items
                            .iter()
                            .any(|item| Script::from_bytes(item).is_witness_program())
                })))
    {
        if previous_output.script_pubkey.is_p2sh()
            && push_only_stack_items(input.script_sig.as_script()).is_some_and(|items| {
                items.len() > 1
                    && items
                        .iter()
                        .any(|item| Script::from_bytes(item).is_witness_program())
            })
        {
            return Some(
                "Script evaluated without error but finished with a false/empty top stack element",
            );
        }
        return Some("Witness program was passed an empty witness");
    }
    if witness_script_is_oversized(input, previous_output) {
        return Some("Script is too big");
    }
    if witness_has_oversized_stack_item(input, previous_output) {
        return Some("Push value size limit exceeded");
    }
    if let Some(reason) = witness_drop_true_script_error(input, previous_output) {
        return Some(reason);
    }
    if has_noncanonical_der_signature(input) {
        return Some("Non-canonical DER signature");
    }
    if witness_p2pk_script_failed(input, previous_output) {
        return Some(
            "Script evaluated without error but finished with a false/empty top stack element",
        );
    }
    if let Some(reason) = script_interpreter_hint(input.script_sig.as_script())
        .or_else(|| script_interpreter_hint(previous_output.script_pubkey.as_script()))
    {
        return Some(reason);
    }
    if null_dummy_script_hint(input, previous_output) {
        return Some("Dummy CHECKMULTISIG argument must be zero");
    }
    cltv_script_hint(transaction, input, previous_output)
}

fn witness_p2pk_script_failed(input: &TxIn, previous_output: &TxOut) -> bool {
    let is_p2wsh = if previous_output.script_pubkey.is_p2wsh() {
        true
    } else if previous_output.script_pubkey.is_p2sh() {
        last_push_bytes(&input.script_sig)
            .is_some_and(|redeem| ScriptBuf::from_bytes(redeem).is_p2wsh())
    } else {
        false
    };
    if !is_p2wsh {
        return false;
    }
    let Some(witness_script) = input.witness.last() else {
        return false;
    };
    let mut instructions = Script::from_bytes(witness_script).instructions();
    matches!(instructions.next(), Some(Ok(Instruction::PushBytes(_))))
        && matches!(
            instructions.next(),
            Some(Ok(Instruction::Op(opcode))) if opcode.to_u8() == 0xac
        )
        && instructions.next().is_none()
        && input.witness.len() >= 2
}

fn has_noncanonical_der_signature(input: &TxIn) -> bool {
    let mut candidates = push_only_stack_items(input.script_sig.as_script()).unwrap_or_default();
    candidates.extend(input.witness.iter().map(ToOwned::to_owned));

    // A DER-encoded ECDSA signature starts with 0x30. Restricting the hint to
    // those stack items avoids turning arbitrary failed script data into a
    // signature-encoding diagnostic while still covering bare, P2SH, and
    // witness spends (including multisig arguments).
    candidates
        .iter()
        .any(|candidate| candidate.first() == Some(&0x30) && !is_valid_der_signature(candidate))
}

/// Bitcoin Core's `IsValidSignatureEncoding`, including the final sighash
/// byte. This is a diagnostic helper; cryptographic validity is checked by
/// libbitcoinconsensus separately.
pub(crate) fn is_valid_der_signature(signature: &[u8]) -> bool {
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
        && !(len_s > 1 && signature[s_start] == 0x00 && signature[s_start + 1] & 0x80 == 0)
}

fn script_interpreter_hint(script: &Script) -> Option<&'static str> {
    let mut conditional_depth = 0usize;
    let mut code_separator = false;
    for instruction in script.instructions() {
        let Ok(Instruction::Op(opcode)) = instruction else {
            continue;
        };
        match opcode.to_u8() {
            0x7e..=0x81 | 0x83..=0x86 | 0x8d..=0x8e | 0x95..=0x99 => {
                return Some("disabled opcode");
            }
            0x6a => return Some("OP_RETURN was encountered"),
            0xab => code_separator = true,
            0x63 | 0x64 => conditional_depth = conditional_depth.saturating_add(1),
            0x67 | 0x68 if conditional_depth == 0 => {
                return Some("Invalid OP_IF construction");
            }
            0x67 | 0x68 => conditional_depth = conditional_depth.saturating_sub(1),
            _ => {}
        }
    }
    if conditional_depth != 0 {
        return Some("Invalid OP_IF construction");
    }
    code_separator.then_some("Using OP_CODESEPARATOR in non-witness script")
}

fn spends_witness_program(input: &TxIn, previous_output: &TxOut) -> bool {
    if previous_output.script_pubkey.is_witness_program() {
        return true;
    }
    if !previous_output.script_pubkey.is_p2sh() {
        return false;
    }
    let Some(items) = push_only_stack_items(input.script_sig.as_script()) else {
        return false;
    };
    items
        .last()
        .map(|redeem| Script::from_bytes(redeem).is_witness_program())
        .unwrap_or(false)
}

fn witness_drop_true_script_error(input: &TxIn, previous_output: &TxOut) -> Option<&'static str> {
    let is_p2wsh = previous_output.script_pubkey.is_p2wsh()
        || (previous_output.script_pubkey.is_p2sh()
            && push_only_stack_items(input.script_sig.as_script()).is_some_and(|items| {
                items
                    .last()
                    .is_some_and(|redeem| Script::from_bytes(redeem).is_p2wsh())
            }));
    let is_drop_true_script = input
        .witness
        .iter()
        .last()
        .is_some_and(|script| script == [0x75, 0x51]);
    if !is_p2wsh || !is_drop_true_script {
        return None;
    }
    Some(match input.witness.len() {
        1 => "Operation not valid with the current stack size",
        2 => return None,
        _ => "Stack size must be exactly one after execution",
    })
}

fn witness_has_oversized_stack_item(input: &TxIn, previous_output: &TxOut) -> bool {
    let is_p2wsh = previous_output.script_pubkey.is_p2wsh()
        || (previous_output.script_pubkey.is_p2sh()
            && push_only_stack_items(input.script_sig.as_script()).is_some_and(|items| {
                items
                    .last()
                    .is_some_and(|redeem| Script::from_bytes(redeem).is_p2wsh())
            }));
    is_p2wsh
        && input
            .witness
            .iter()
            .take(input.witness.len().saturating_sub(1))
            .any(|item| item.len() > 520)
}

fn witness_script_is_oversized(input: &TxIn, previous_output: &TxOut) -> bool {
    let is_p2wsh = previous_output.script_pubkey.is_p2wsh()
        || (previous_output.script_pubkey.is_p2sh()
            && push_only_stack_items(input.script_sig.as_script()).is_some_and(|items| {
                items
                    .last()
                    .is_some_and(|redeem| Script::from_bytes(redeem).is_p2wsh())
            }));
    is_p2wsh
        && input
            .witness
            .iter()
            .last()
            .is_some_and(|script| script.len() > 10_000)
}

fn null_dummy_script_hint(input: &TxIn, previous_output: &TxOut) -> bool {
    let script_sig_items = push_only_stack_items(input.script_sig.as_script());
    if previous_output.script_pubkey.is_p2sh()
        && let Some(items) = script_sig_items.as_ref()
        && let Some(redeem_script) = items.last()
        && !items.first().is_none_or(Vec::is_empty)
        && script_contains_checkmultisig(redeem_script)
    {
        return true;
    }

    let witness_script = if previous_output.script_pubkey.is_witness_program() {
        input.witness.iter().last().map(|script| script.to_vec())
    } else if previous_output.script_pubkey.is_p2sh() {
        script_sig_items
            .as_ref()
            .and_then(|items| items.last())
            .and_then(|redeem| {
                let redeem = Script::from_bytes(redeem);
                redeem
                    .is_witness_program()
                    .then(|| input.witness.iter().last().map(|script| script.to_vec()))
            })
            .flatten()
    } else {
        None
    };
    let Some(witness_script) = witness_script else {
        return false;
    };
    !input.witness.is_empty()
        && !input
            .witness
            .iter()
            .next()
            .is_none_or(|dummy| dummy.is_empty())
        && script_contains_checkmultisig(&witness_script)
}

fn cltv_script_hint(
    transaction: &Transaction,
    input: &TxIn,
    previous_output: &TxOut,
) -> Option<&'static str> {
    let mut stack = Vec::new();
    if let Some(reason) =
        cltv_script_hint_for_script(transaction, input, input.script_sig.as_script(), &mut stack)
    {
        return Some(reason);
    }
    cltv_script_hint_for_script(
        transaction,
        input,
        previous_output.script_pubkey.as_script(),
        &mut stack,
    )
}

fn cltv_script_hint_for_script(
    transaction: &Transaction,
    input: &TxIn,
    script: &Script,
    stack: &mut Vec<Vec<u8>>,
) -> Option<&'static str> {
    for instruction in script.instructions() {
        match instruction.ok()? {
            Instruction::PushBytes(bytes) => stack.push(bytes.as_bytes().to_vec()),
            Instruction::Op(opcode) => match opcode.to_u8() {
                0x00 => stack.push(Vec::new()),
                0x4f => stack.push(vec![0x81]),
                0x51..=0x60 => stack.push(vec![opcode.to_u8() - 0x50]),
                0xb1 | 0xb2 => {
                    let Some(value) = stack.last().and_then(|item| script_num_value(item)) else {
                        return Some("Operation not valid with the current stack size");
                    };
                    if value < 0 {
                        return Some("Negative locktime");
                    }
                    if opcode.to_u8() == 0xb2 {
                        let sequence = input.sequence.to_consensus_u32();
                        let required = value as u32;
                        if transaction.version.0 < 2
                            || sequence & 0x8000_0000 != 0
                            || required & 0x8000_0000 == 0
                                && ((required ^ sequence) & 0x0040_0000 != 0
                                    || (required & 0x0000_ffff) > (sequence & 0x0000_ffff))
                        {
                            return Some("Locktime requirement not satisfied");
                        }
                        continue;
                    }
                    let tx_lock_time = transaction.lock_time.to_consensus_u32();
                    let script_is_time = value as u32 >= LOCK_TIME_THRESHOLD;
                    let tx_is_time = tx_lock_time >= LOCK_TIME_THRESHOLD;
                    if script_is_time != tx_is_time
                        || value as u64 > u64::from(tx_lock_time)
                        || input.sequence == Sequence::MAX
                    {
                        return Some("Locktime requirement not satisfied");
                    }
                }
                0x75 => {
                    stack.pop()?;
                }
                _ => {}
            },
        }
    }
    None
}

fn script_contains_checkmultisig(script: &[u8]) -> bool {
    Script::from_bytes(script)
        .instructions()
        .any(|instruction| {
            matches!(
                instruction,
                Ok(Instruction::Op(opcode)) if matches!(opcode.to_u8(), 0xae | 0xaf)
            )
        })
}

fn push_only_stack_items(script: &Script) -> Option<Vec<Vec<u8>>> {
    script
        .instructions()
        .map(|instruction| match instruction {
            Ok(Instruction::PushBytes(bytes)) => Some(bytes.as_bytes().to_vec()),
            Ok(Instruction::Op(opcode)) => match opcode.to_u8() {
                0x00 => Some(Vec::new()),
                0x4f => Some(vec![0x81]),
                0x51..=0x60 => Some(vec![opcode.to_u8() - 0x50]),
                _ => None,
            },
            Err(_) => None,
        })
        .collect()
}

fn script_num_value(bytes: &[u8]) -> Option<i64> {
    if bytes.len() > 5 {
        return None;
    }
    let mut value = bytes.iter().enumerate().fold(0i64, |value, (index, byte)| {
        value | (i64::from(*byte) << (8 * index))
    });
    if bytes.last().is_some_and(|byte| byte & 0x80 != 0) {
        value &= !(0x80i64 << (8 * (bytes.len().saturating_sub(1))));
        value = -value;
    }
    Some(value)
}

pub(crate) const MAX_BLOCK_SERIALIZED_SIZE: usize = 4_000_000;
pub(crate) const MAX_BLOCK_WEIGHT: usize = 4_000_000;
pub(crate) const MAX_BLOCK_SIGOP_COST: usize = 80_000;

pub fn validate_block_version(
    network: Network,
    height: u32,
    actual: i32,
) -> Result<(), ValidationError> {
    validate_block_version_with_params(&DeploymentParameters::for_network(network), height, actual)
}

pub fn validate_block_version_with_params(
    params: &DeploymentParameters,
    height: u32,
    actual: i32,
) -> Result<(), ValidationError> {
    let heights = params.buried;
    let required = if height >= heights.bip65 {
        4
    } else if height >= heights.bip66 {
        3
    } else if height >= heights.bip34 {
        2
    } else {
        1
    };
    if actual < required {
        return Err(ValidationError::BadBlockVersion { actual, required });
    }
    Ok(())
}

fn legacy_sigop_cost_for_transaction(transaction: &Transaction) -> usize {
    transaction
        .input
        .iter()
        .map(|input| input.script_sig.count_sigops_legacy())
        .chain(
            transaction
                .output
                .iter()
                .map(|output| output.script_pubkey.count_sigops_legacy()),
        )
        .sum::<usize>()
        .saturating_mul(4)
}

/// Count the contextual sigop cost used by ConnectBlock. Taproot spends do
/// not contribute to the legacy block-wide sigop budget; P2SH and witness
/// spends do when their respective consensus deployments are active.
pub(crate) fn transaction_sigop_cost(
    transaction: &Transaction,
    previous_outputs: &[TxOut],
    flags: u32,
) -> usize {
    let mut cost = legacy_sigop_cost_for_transaction(transaction);
    if transaction.is_coinbase() || previous_outputs.len() != transaction.input.len() {
        return cost;
    }

    for (input, previous_output) in transaction.input.iter().zip(previous_outputs) {
        cost = cost.saturating_add(transaction_input_sigop_cost(input, previous_output, flags));
    }
    cost
}

/// Return the contextual sigop contribution for one input without requiring
/// the caller to materialize a complete `TxOut` slice. Core reads each coin
/// directly from its cache while calculating this value; the replay path uses
/// this helper to keep that same borrowed-coin behavior when script checks are
/// skipped by assumevalid.
pub(crate) fn transaction_input_sigop_cost(
    input: &TxIn,
    previous_output: &TxOut,
    flags: u32,
) -> usize {
    let mut cost = 0usize;
    if flags & bitcoinconsensus::VERIFY_P2SH != 0
        && previous_output.script_pubkey.is_p2sh()
        && input.script_sig.is_push_only()
        && let Some(redeem_script) = last_push_bytes(&input.script_sig)
    {
        cost = cost.saturating_add(
            ScriptBuf::from_bytes(redeem_script)
                .count_sigops()
                .saturating_mul(4),
        );
    }

    if flags & bitcoinconsensus::VERIFY_WITNESS == 0 {
        return cost;
    }
    let witness_program = if previous_output.script_pubkey.is_witness_program() {
        Some(previous_output.script_pubkey.clone())
    } else if previous_output.script_pubkey.is_p2sh() && input.script_sig.is_push_only() {
        last_push_bytes(&input.script_sig).map(ScriptBuf::from_bytes)
    } else {
        None
    };
    let Some(witness_program) = witness_program else {
        return cost;
    };
    if witness_program.is_p2wpkh() {
        cost.saturating_add(1)
    } else if witness_program.is_p2wsh()
        && let Some(witness_script) = input.witness.last()
    {
        cost.saturating_add(ScriptBuf::from_bytes(witness_script.to_vec()).count_sigops())
    } else {
        cost
    }
}

fn last_push_bytes(script: &ScriptBuf) -> Option<Vec<u8>> {
    match script.instructions().last()? {
        Ok(Instruction::PushBytes(bytes)) => Some(bytes.as_bytes().to_vec()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::Block;
    use bitcoin::absolute::LockTime;
    use bitcoin::block::{Header, Version as BlockVersion};
    use bitcoin::blockdata::script::{Builder, ScriptBuf};
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
    fn cached_transaction_ids_compute_merkle_root_and_mutation_together() {
        let first = Txid::from_byte_array([1; 32]);
        let second = Txid::from_byte_array([2; 32]);
        let third = Txid::from_byte_array([3; 32]);
        let odd_ids = [first, second, third];
        let expected = bitcoin::merkle_tree::calculate_root(odd_ids.into_iter())
            .map(|root| TxMerkleNode::from_raw_hash(root.to_raw_hash()));
        assert_eq!(merkle_root_and_mutated_txid(&odd_ids), (expected, None));

        let mutated_ids = [first, second, third, third];
        let expected = bitcoin::merkle_tree::calculate_root(mutated_ids.into_iter())
            .map(|root| TxMerkleNode::from_raw_hash(root.to_raw_hash()));
        assert_eq!(
            merkle_root_and_mutated_txid(&mutated_ids),
            (expected, Some(third))
        );
    }

    #[test]
    fn pre_header_validation_rejects_mutation_but_defers_witness_context() {
        let coinbase = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::null(),
                script_sig: Builder::new().push_int(1).push_int(0).into_script(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::from_slice(&[vec![7]]),
            }],
            output: vec![TxOut {
                value: Amount::ZERO,
                script_pubkey: ScriptBuf::new(),
            }],
        };
        let mut block = Block {
            header: Header {
                version: BlockVersion::from_consensus(4),
                prev_blockhash: BlockHash::all_zeros(),
                merkle_root: TxMerkleNode::all_zeros(),
                time: 1,
                bits: bitcoin::pow::CompactTarget::from_consensus(0x207f_ffff),
                nonce: 0,
            },
            txdata: vec![coinbase],
        };
        block.header.merkle_root = block.compute_merkle_root().unwrap();

        assert!(validate_block_before_header(&block, None).is_ok());
        block.header.merkle_root = TxMerkleNode::all_zeros();
        assert!(matches!(
            validate_block_before_header(&block, None),
            Err(ValidationError::BadMerkleRoot)
        ));
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
    fn consensus_engine_matches_core_bip341_keypath_vector() {
        // Bitcoin Core v31.1 src/test/data/bip341_wallet_vectors.json. This
        // transaction mixes seven Taproot key-path spends with one P2PKH and
        // one P2WPKH spend, exercising all Taproot sighash modes and the full
        // spent-output context passed across the libbitcoinconsensus boundary.
        let raw = concat!(
            "020000000001097de20cbff686da83a54981d2b9bab3586f4ca7e48f57f5b55963115f3b334e9c010000000000000000d7b7cab57b1393ace2d064f4d4a2cb8af6def61273e127517d44759b6dafdd990000000000fffffffff8e1f583384333689228c5d28eac13366be082dc57441760d957275419a41842000000006b4830450221008f3b8f8f0537c420654d2283673a761b7ee2ea3c130753103e08ce79201cf32a022079e7ab904a1980ef1c5890b648c8783f4d10103dd62f740d13daa79e298d50c201210279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798fffffffff0689180aa63b30cb162a73c6d2a38b7eeda2a83ece74310fda0843ad604853b0100000000feffffffaa5202bdf6d8ccd2ee0f0202afbbb7461d9264a25e5bfd3c5a52ee1239e0ba6c0000000000feffffff956149bdc66faa968eb2be2d2faa29718acbfe3941215893a2a3446d32acd050000000000000000000e664b9773b88c09c32cb70a2a3e4da0ced63b7ba3b22f848531bbb1d5d5f4c94010000000000000000e9aa6b8e6c9de67619e6a3924ae25696bb7b694bb677a632a74ef7eadfd4eabf0000000000ffffffff",
            "a778eb6a263dc090464cd125c466b5a99667720b1c110468831d058aa1b82af10100000000ffffffff0200ca9a3b000000001976a91406afd46bcdfd22ef94ac122aa11f241244a37ecc88ac807840cb0000000020ac9a87f5594be208f8532db38cff670c450ed2fea8fcdefcc9a663f78bab962b0141ed7c1647cb97379e76892be0cacff57ec4a7102aa24296ca39af7541246d8ff14d38958d4cc1e2e478e4d4a764bbfd835b16d4e314b72937b29833060b87276c030141052aedffc554b41f52b521071793a6b88d6dbca9dba94cf34c83696de0c1ec35ca9c5ed4ab28059bd606a4f3a657eec0bb96661d42921b5f50a95ad33675b54f83000141ff45f742a876139946a149ab4d9185574b98dc919d2eb6754f8abaa59d18b025637a3aa043b91817739554f4ed2026cf8022dbd83e351ce1fabc272841d2510a010140b4010dd48a617db09926f729e79c33ae0b4e94b79f04a1ae93ede6315eb3669de185a17d2b0ac9ee09fd4c64b678a0b61a0a86fa888a273c8511be83bfd6810f0247304402202b795e4de72646d76eab3f0ab27dfa30b810e856ff3a46c9a702df53bb0d8cc302203ccc4d822edab5f35caddb10af1be93583526ccfbade4b4ead350781e2f8adcd012102f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9",
            "0141a3785919a2ce3c4ce26f298c3d51619bc474ae24014bcdd31328cd8cfbab2eff3395fa0a16fe5f486d12f22a9cedded5ae74feb4bbe5351346508c5405bcfee0020141ea0c6ba90763c2d3a296ad82ba45881abb4f426b3f87af162dd24d5109edc1cdd11915095ba47c3a9963dc1e6c432939872bc49212fe34c632cd3ab9fed429c4820141bbc9584a11074e83bc8c6759ec55401f0ae7b03ef290c3139814f545b58a9f8127258000874f44bc46db7646322107d4d86aec8e73b8719a61fff761d75b5dd9810065cd1d"
        );
        let transaction: Transaction =
            bitcoin::consensus::deserialize(&hex::decode(raw).unwrap()).unwrap();
        let previous_outputs = [
            (
                420_000_000,
                "512053a1f6e454df1aa2776a2814a721372d6258050de330b3c6d10ee8f4e0dda343",
            ),
            (
                462_000_000,
                "5120147c9c57132f6e7ecddba9800bb0c4449251c92a1e60371ee77557b6620f3ea3",
            ),
            (
                294_000_000,
                "76a914751e76e8199196d454941c45d1b3a323f1433bd688ac",
            ),
            (
                504_000_000,
                "5120e4d810fd50586274face62b8a807eb9719cef49c04177cc6b76a9a4251d5450e",
            ),
            (
                630_000_000,
                "512091b64d5324723a985170e4dc5a0f84c041804f2cd12660fa5dec09fc21783605",
            ),
            (378_000_000, "00147dd65592d0ab2fe0d0257d571abf032cd9db93dc"),
            (
                672_000_000,
                "512075169f4001aa68f15bbed28b218df1d0a62cbbcf1188c6665110c293c907b831",
            ),
            (
                546_000_000,
                "5120712447206d7a5238acc7ff53fbe94a3b64539ad291c7cdbc490b7577e4b17df5",
            ),
            (
                588_000_000,
                "512077e30a5522dd9f894c3f8b8bd4c4b2cf82ca7da8a3ea6a239655c39c050ab220",
            ),
        ]
        .map(|(value, script)| TxOut {
            value: Amount::from_sat(value),
            script_pubkey: ScriptBuf::from_bytes(hex::decode(script).unwrap()),
        });
        let flags = bitcoinconsensus::VERIFY_ALL_PRE_TAPROOT | bitcoinconsensus::VERIFY_TAPROOT;

        validate_transaction_scripts_with_flags(&transaction, &previous_outputs, flags).unwrap();

        let mut corrupted = transaction;
        let mut signature = corrupted.input[0].witness.iter().next().unwrap().to_vec();
        signature[0] ^= 1;
        corrupted.input[0].witness = Witness::from_slice(&[signature]);
        assert!(
            validate_transaction_scripts_with_flags(&corrupted, &previous_outputs, flags).is_err()
        );
    }

    #[test]
    #[ignore = "generate with contrib/generate_core_taproot_assets.py and set CORE_TAPROOT_ASSETS"]
    fn consensus_engine_matches_generated_core_taproot_assets() {
        let path = std::env::var("CORE_TAPROOT_ASSETS").expect("CORE_TAPROOT_ASSETS is required");
        let vectors: serde_json::Value =
            serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
        let vectors = vectors.as_array().unwrap();

        for vector in vectors {
            let comment = vector["comment"].as_str().unwrap();
            let raw = hex::decode(vector["tx"].as_str().unwrap()).unwrap();
            let transaction: Transaction = bitcoin::consensus::deserialize(&raw).unwrap();
            let previous_outputs = vector["prevouts"]
                .as_array()
                .unwrap()
                .iter()
                .map(|output| {
                    bitcoin::consensus::deserialize(&hex::decode(output.as_str().unwrap()).unwrap())
                        .unwrap()
                })
                .collect::<Vec<TxOut>>();
            let input = usize::try_from(vector["index"].as_u64().unwrap()).unwrap();
            let flags = bitcoinconsensus::VERIFY_ALL_PRE_TAPROOT
                | if vector["flags"].as_str().unwrap().contains("TAPROOT") {
                    bitcoinconsensus::VERIFY_TAPROOT
                } else {
                    0
                };

            let apply_satisfaction = |name: &str| {
                let mut candidate = transaction.clone();
                let satisfaction = &vector[name];
                candidate.input[input].script_sig = ScriptBuf::from_bytes(
                    hex::decode(satisfaction["scriptSig"].as_str().unwrap()).unwrap(),
                );
                let witness = satisfaction["witness"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|item| hex::decode(item.as_str().unwrap()).unwrap())
                    .collect::<Vec<_>>();
                candidate.input[input].witness = Witness::from_slice(&witness);
                candidate
            };

            let success = apply_satisfaction("success");
            assert!(
                validate_transaction_scripts_with_flags(&success, &previous_outputs, flags).is_ok(),
                "Core Taproot success vector failed: {comment}"
            );
            if vector.get("failure").is_some() {
                let failure = apply_satisfaction("failure");
                assert!(
                    validate_transaction_scripts_with_flags(&failure, &previous_outputs, flags)
                        .is_err(),
                    "Core Taproot failure vector passed: {comment}"
                );
            }
        }

        assert!(vectors.len() >= 2_800);
    }

    #[test]
    fn p2sh_sigops_ignore_non_push_only_script_sigs() {
        let redeem_script = ScriptBuf::from_bytes(vec![bitcoin::opcodes::all::OP_CHECKSIG.to_u8()]);
        let previous = TxOut {
            value: Amount::ZERO,
            script_pubkey: Builder::new()
                .push_opcode(bitcoin::opcodes::all::OP_HASH160)
                .push_slice([0u8; 20])
                .push_opcode(bitcoin::opcodes::all::OP_EQUAL)
                .into_script(),
        };
        let mut script_sig = ScriptBuf::new();
        script_sig.push_opcode(bitcoin::opcodes::all::OP_CHECKSIG);
        script_sig.push_slice(PushBytesBuf::try_from(redeem_script.as_bytes().to_vec()).unwrap());
        let transaction = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(Txid::from_byte_array([1; 32]), 0),
                script_sig,
                sequence: Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::ZERO,
                script_pubkey: ScriptBuf::new(),
            }],
        };
        assert_eq!(
            transaction_sigop_cost(&transaction, &[previous], bitcoinconsensus::VERIFY_P2SH,),
            4
        );
    }

    #[test]
    fn rejects_blocks_over_the_sigop_cost_limit() {
        let coinbase = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::null(),
                script_sig: Builder::new().push_int(1).push_int(0).into_script(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::ZERO,
                script_pubkey: ScriptBuf::new(),
            }],
        };
        let mut sigop_script = ScriptBuf::new();
        for _ in 0..20_001 {
            sigop_script.push_opcode(bitcoin::opcodes::all::OP_CHECKSIG);
        }
        let transaction = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(Txid::from_byte_array([7; 32]), 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::ZERO,
                script_pubkey: sigop_script,
            }],
        };
        let mut block = Block {
            header: Header {
                version: BlockVersion::from_consensus(4),
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
            Err(ValidationError::TooManySigops)
        ));
    }

    #[test]
    fn rejects_null_prevouts_in_non_coinbase_transactions() {
        let coinbase = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::null(),
                script_sig: Builder::new().push_int(1).push_int(0).into_script(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::ZERO,
                script_pubkey: ScriptBuf::new(),
            }],
        };
        let malformed = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![
                TxIn {
                    previous_output: OutPoint::null(),
                    script_sig: ScriptBuf::new(),
                    sequence: bitcoin::Sequence::MAX,
                    witness: Witness::default(),
                },
                TxIn {
                    previous_output: OutPoint::new(Txid::from_byte_array([8; 32]), 0),
                    script_sig: ScriptBuf::new(),
                    sequence: bitcoin::Sequence::MAX,
                    witness: Witness::default(),
                },
            ],
            output: vec![TxOut {
                value: Amount::ZERO,
                script_pubkey: ScriptBuf::new(),
            }],
        };
        let mut block = Block {
            header: Header {
                version: BlockVersion::from_consensus(4),
                prev_blockhash: BlockHash::all_zeros(),
                merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                time: 1,
                bits: bitcoin::pow::CompactTarget::from_consensus(0x207f_ffff),
                nonce: 0,
            },
            txdata: vec![coinbase, malformed],
        };
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        assert!(matches!(
            validate_block_structure(&block, Network::Regtest, 1, Amount::MAX_MONEY.to_sat()),
            Err(ValidationError::NullPrevout(_))
        ));
    }

    #[test]
    fn buried_deployments_require_their_block_versions() {
        assert!(validate_block_version(Network::Regtest, 0, 1).is_ok());
        assert!(matches!(
            validate_block_version(Network::Regtest, 1, 1),
            Err(ValidationError::BadBlockVersion {
                actual: 1,
                required: 4
            })
        ));
        assert!(validate_block_version(Network::Bitcoin, 227_930, 1).is_ok());
        assert!(matches!(
            validate_block_version(Network::Bitcoin, 227_931, 1),
            Err(ValidationError::BadBlockVersion {
                actual: 1,
                required: 2
            })
        ));
    }

    #[test]
    fn unknown_versionbits_require_lock_in_period_before_warning() {
        let [deployment, ..] = bip9_deployments(Network::Regtest);
        let period = usize::try_from(deployment.period).unwrap();
        let threshold = usize::try_from(deployment.threshold).unwrap();
        let unknown_bit = 27u32;
        let mut headers = Vec::with_capacity(period * 3);
        for height in 0..period * 2 {
            let signals = height >= period && height < period + threshold;
            headers.push(Header {
                version: BlockVersion::from_consensus(if signals {
                    0x2000_0000 | (1 << unknown_bit)
                } else {
                    4
                }),
                prev_blockhash: BlockHash::all_zeros(),
                merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                time: u32::try_from(height + 1).unwrap(),
                bits: bitcoin::pow::CompactTarget::from_consensus(0x207f_ffff),
                nonce: 0,
            });
        }

        assert_eq!(unknown_versionbits_active(&headers, Network::Regtest), None);

        headers.extend((period * 2..period * 3).map(|height| Header {
            version: BlockVersion::from_consensus(4),
            prev_blockhash: BlockHash::all_zeros(),
            merkle_root: bitcoin::TxMerkleNode::all_zeros(),
            time: u32::try_from(height + 1).unwrap(),
            bits: bitcoin::pow::CompactTarget::from_consensus(0x207f_ffff),
            nonce: 0,
        }));
        assert_eq!(
            unknown_versionbits_active(&headers, Network::Regtest),
            Some(unknown_bit as u8)
        );
        assert_eq!(
            unknown_versionbits_active_at_boundary(&headers, Network::Regtest),
            Some(unknown_bit as u8)
        );
    }

    #[test]
    fn temporary_versionbits_deployment_expires_at_period_boundary() {
        let deployment = Bip9Deployment {
            bit: 4,
            start_time: 0,
            timeout: i64::MAX,
            min_activation_height: 0,
            max_activation_height: Bip9Deployment::MAX_ACTIVATION_HEIGHT,
            active_duration: 144,
            threshold: 108,
            period: 144,
        };
        let headers = (0..576)
            .map(|height| Header {
                version: BlockVersion::from_consensus(if (144..252).contains(&height) {
                    0x2000_0000 | (1 << deployment.bit)
                } else {
                    4
                }),
                prev_blockhash: BlockHash::all_zeros(),
                merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                time: height + 1,
                bits: bitcoin::pow::CompactTarget::from_consensus(0x207f_ffff),
                nonce: 0,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            bip9_state_at_height(&headers, deployment, 143),
            (Bip9State::Defined, 0)
        );
        assert_eq!(
            bip9_state_at_height(&headers, deployment, 287),
            (Bip9State::Started, 144)
        );
        assert_eq!(
            bip9_state_at_height(&headers, deployment, 431),
            (Bip9State::LockedIn, 288)
        );
        assert_eq!(
            bip9_state_at_height(&headers, deployment, 575),
            (Bip9State::Active, 432)
        );
        assert_eq!(
            bip9_state_at_height(&headers, deployment, 576),
            (Bip9State::Expired, 576)
        );
    }

    #[test]
    fn core_v31_1_defaults_do_not_enable_reduced_data() {
        let params = DeploymentParameters::for_network(Network::Bitcoin);
        let deployment = params.bip9[2];
        assert!(!deployment.is_enabled());
        assert_eq!(
            deployment.max_activation_height,
            Bip9Deployment::MAX_ACTIVATION_HEIGHT
        );
        assert!(validate_mandatory_version_bits_with_params(&[], &params, 963_648, 4).is_ok());
    }

    #[test]
    fn reduced_data_limits_output_and_new_witness_data() {
        let oversized_op_return = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(Txid::from_byte_array([9; 32]), 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::ZERO,
                script_pubkey: ScriptBuf::from_bytes(
                    std::iter::once(0x6a)
                        .chain(std::iter::repeat_n(0, 83))
                        .collect(),
                ),
            }],
        };
        assert!(matches!(
            validate_reduced_data_output_sizes(&oversized_op_return),
            Err(ValidationError::ReducedDataOutputTooLarge(_))
        ));

        let previous_output = TxOut {
            value: Amount::from_sat(1_000),
            script_pubkey: ScriptBuf::from_bytes(
                std::iter::once(0x00)
                    .chain(std::iter::once(0x20))
                    .chain(std::iter::repeat_n(0, 32))
                    .collect(),
            ),
        };
        let spending = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(Txid::from_byte_array([8; 32]), 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::from_slice(&[vec![0x42; 300], vec![0x51]]),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(900),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        assert!(
            validate_reduced_data_input_sizes(
                &spending,
                std::slice::from_ref(&previous_output),
                &[10],
                10,
            )
            .is_err()
        );
        assert!(validate_reduced_data_input_sizes(&spending, &[previous_output], &[9], 10).is_ok());
    }

    #[test]
    fn enforces_testnet4_bip94_timewarp_at_adjustment_boundaries() {
        assert!(validate_bip94_timewarp(Network::Testnet4, 2_015, 1, 10_000).is_ok());
        assert!(validate_bip94_timewarp(Network::Testnet4, 2_016, 9_400, 10_000).is_ok());
        assert!(matches!(
            validate_bip94_timewarp(Network::Testnet4, 2_016, 9_399, 10_000),
            Err(ValidationError::Bip94TimeWarp)
        ));
        assert!(validate_bip94_timewarp(Network::Regtest, 2_016, 1, 10_000).is_ok());
    }

    #[test]
    fn matches_core_historical_script_flag_exceptions() {
        let mainnet_bip16 = "00000000000002dc756eebf4f49723ed8d30cc28a5f108eb94b1ba88ac4f9c22"
            .parse()
            .unwrap();
        let testnet_bip16 = "00000000dd30457c001f4095d208cc1296b0eed002427aa599874af7a432b105"
            .parse()
            .unwrap();
        let mainnet_taproot = "0000000000000000000f14c35b2d841e986ab5441de8c585d5ffe55ea1e395ad"
            .parse()
            .unwrap();
        assert_eq!(
            script_flags_for_block_with_hash(Network::Bitcoin, 1, Some(mainnet_bip16)),
            bitcoinconsensus::VERIFY_NONE
        );
        assert_eq!(
            script_flags_for_block_with_hash(Network::Testnet, 1, Some(testnet_bip16)),
            bitcoinconsensus::VERIFY_NONE
        );
        let taproot_exception =
            script_flags_for_block_with_hash(Network::Bitcoin, 700_000, Some(mainnet_taproot));
        assert_eq!(
            taproot_exception & bitcoinconsensus::VERIFY_TAPROOT,
            bitcoinconsensus::VERIFY_NONE
        );
        assert_ne!(
            taproot_exception & bitcoinconsensus::VERIFY_WITNESS,
            bitcoinconsensus::VERIFY_NONE
        );
        assert_ne!(
            script_flags_for_block_with_hash(Network::Bitcoin, 1, None)
                & bitcoinconsensus::VERIFY_TAPROOT,
            bitcoinconsensus::VERIFY_NONE
        );
    }

    #[test]
    fn mempool_script_flags_are_independent_of_block_height() {
        let flags = mempool_script_flags();
        assert_eq!(
            flags,
            bitcoinconsensus::VERIFY_ALL_PRE_TAPROOT | bitcoinconsensus::VERIFY_TAPROOT
        );
        assert_ne!(
            script_flags_for_block(Network::Regtest, 0, 0) & bitcoinconsensus::VERIFY_DERSIG,
            flags & bitcoinconsensus::VERIFY_DERSIG
        );
    }

    #[test]
    fn der_signature_encoding_matches_core() {
        // The second byte of S is zero. Core checks for a redundant leading
        // zero at the first S byte, not at this position.
        let signature = hex::decode(
            "3045022100d4dc054081c69caccef36ed255657ba589f3f63289c4cb5d1172e5c028e6138e0220620060cdcde8f91924bc0570319cf3fa6cb42584e2c496fdba8910693a11eabf01",
        )
        .unwrap();
        assert!(is_valid_der_signature(&signature));

        let mut redundant_leading_zero = signature.clone();
        redundant_leading_zero[39] = 0;
        assert!(!is_valid_der_signature(&redundant_leading_zero));
    }

    #[test]
    fn rejects_witness_data_before_segwit_activation() {
        let coinbase = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::null(),
                script_sig: Builder::new().push_int(1).push_int(0).into_script(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::from_slice(&[vec![0u8; 32]]),
            }],
            output: vec![TxOut {
                value: Amount::ZERO,
                script_pubkey: ScriptBuf::new(),
            }],
        };
        let mut block = Block {
            header: Header {
                version: BlockVersion::ONE,
                prev_blockhash: BlockHash::all_zeros(),
                merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                time: 1,
                bits: bitcoin::pow::CompactTarget::from_consensus(0x207f_ffff),
                nonce: 0,
            },
            txdata: vec![coinbase],
        };
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        assert!(matches!(
            validate_block_structure(&block, Network::Bitcoin, 0, Amount::MAX_MONEY.to_sat()),
            Err(ValidationError::UnexpectedWitness)
        ));
    }

    #[test]
    fn rejects_a_malformed_witness_commitment_without_witness_data() {
        let mut commitment_script = vec![0x6a, 0x24, 0xaa, 0x21, 0xa9, 0xed];
        commitment_script.extend([0u8; 32]);
        let coinbase = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::null(),
                script_sig: Builder::new().push_int(1).push_int(0).into_script(),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::ZERO,
                script_pubkey: ScriptBuf::from_bytes(commitment_script),
            }],
        };
        let mut block = Block {
            header: Header {
                version: BlockVersion::from_consensus(4),
                prev_blockhash: BlockHash::all_zeros(),
                merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                time: 1,
                bits: bitcoin::pow::CompactTarget::from_consensus(0x207f_ffff),
                nonce: 0,
            },
            txdata: vec![coinbase],
        };
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        assert!(matches!(
            validate_block_structure(&block, Network::Regtest, 1, Amount::MAX_MONEY.to_sat()),
            Err(ValidationError::BadWitnessNonceSize)
        ));
    }

    #[test]
    fn witness_commitment_reject_reasons_match_core_bip22() {
        assert_eq!(
            ValidationError::BadWitnessNonceSize.bip22_reject_reason(),
            "bad-witness-nonce-size"
        );
        assert_eq!(
            ValidationError::BadWitnessMerkleMatch.bip22_reject_reason(),
            "bad-witness-merkle-match"
        );
        assert_eq!(
            ValidationError::Bip30(Txid::from_byte_array([7; 32])).bip22_reject_reason(),
            "bad-txns-BIP30"
        );
        assert_eq!(
            ValidationError::AccumulatedFeeOverflow.bip22_reject_reason(),
            "bad-txns-accumulated-fee-outofrange"
        );
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
    fn absolute_locktime_is_strict_and_handles_large_block_heights() {
        let transaction = Transaction {
            version: Version::TWO,
            lock_time: LockTime::from_consensus(12),
            input: vec![TxIn {
                previous_output: OutPoint::new(bitcoin::Txid::from_byte_array([4u8; 32]), 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::ZERO,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(1),
                script_pubkey: ScriptBuf::new(),
            }],
        };
        assert!(validate_transaction_finality(&transaction, 12, 500_000_001, false, &[]).is_err());
        assert!(validate_transaction_finality(&transaction, 13, 500_000_001, false, &[]).is_ok());
        assert!(
            validate_transaction_finality(
                &transaction,
                bitcoin::absolute::LOCK_TIME_THRESHOLD,
                500_000_001,
                false,
                &[],
            )
            .is_ok()
        );
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
                true,
                std::slice::from_ref(&entry),
            )
            .is_err()
        );
        assert!(
            validate_transaction_finality(&transaction, 12, 500_000_001, true, &[entry]).is_ok()
        );
        assert!(validate_transaction_finality(&transaction, 11, 500_000_000, false, &[]).is_ok());
    }

    #[test]
    fn zero_value_relative_time_lock_is_satisfied_at_the_prevout_mtp() {
        let transaction = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::new(bitcoin::Txid::from_byte_array([3u8; 32]), 0),
                script_sig: ScriptBuf::new(),
                sequence: bitcoin::Sequence::from_consensus(1 << 22),
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
        assert!(validate_transaction_finality(
            &transaction,
            11,
            entry.median_time_past,
            true,
            &[entry],
        )
        .is_ok());
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
                version: BlockVersion::from_consensus(4),
                prev_blockhash: BlockHash::all_zeros(),
                merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                time: 1,
                bits: bitcoin::pow::CompactTarget::from_consensus(0x207f_ffff),
                nonce: 0,
            },
            txdata: vec![coinbase, transaction],
        };
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        let mut valid_height = block.clone();
        valid_height.txdata[1].output[1].value = Amount::ZERO;
        valid_height.header.merkle_root = valid_height.compute_merkle_root().unwrap();
        let mut invalid_height = valid_height;
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
            Err(ValidationError::OutputTotalOverflow)
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

    #[test]
    fn proposal_structure_validation_skips_the_signet_solution_without_pow() {
        let block = signet_block(Some(&[0xec, 0xc7, 0xda, 0xa2, 0x00]));
        assert!(matches!(
            validate_block_structure_with_signet_options(
                &block,
                Network::Signet,
                0,
                Amount::MAX_MONEY.to_sat(),
                Some(&[0x51]),
                true,
            ),
            Err(ValidationError::BadSignetSolution)
        ));
        assert!(
            validate_block_structure_with_signet_options(
                &block,
                Network::Signet,
                0,
                Amount::MAX_MONEY.to_sat(),
                Some(&[0x51]),
                false,
            )
            .is_ok()
        );
    }
}
