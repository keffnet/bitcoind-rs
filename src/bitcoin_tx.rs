//! Wallet-free implementation of Core's `bitcoin-tx` utility.
//!
//! The command edits or creates consensus-serialized transactions. Signing
//! uses only keys and prevout metadata supplied on the command line through
//! JSON registers; no wallet or persistent key store is involved.

use std::collections::HashMap;
use std::env;
use std::fs;
use std::io::{self, Cursor, Read};
use std::process::ExitCode;

use anyhow::{Context, Result, anyhow, bail};
use bitcoin::absolute::LockTime;
use bitcoin::address::NetworkUnchecked;
use bitcoin::blockdata::opcodes::{Opcode, all::*};
use bitcoin::blockdata::script::{Builder, PushBytesBuf, ScriptBuf};
use bitcoin::blockdata::transaction::Version;
use bitcoin::consensus::{Decodable, Encodable, deserialize, serialize};
use bitcoin::{
    Address, Amount, Network, OutPoint, PrivateKey, PublicKey, Sequence, Transaction, TxIn, TxOut,
    Txid, Witness,
};
use serde_json::{Map, Value, json};

const VERSION: &str = "31.1.0";
const MAX_MONEY_SAT: u64 = 2_100_000_000_000_000;
const MAX_BLOCK_WEIGHT: u64 = 4_000_000;
const WITNESS_SCALE_FACTOR: u64 = 4;
const MIN_TXOUT_SIZE: u64 = 9;
const MAX_SCRIPT_SIZE: usize = 10_000;
const MAX_SCRIPT_ELEMENT_SIZE: usize = 520;
const MAX_SEQUENCE_NONFINAL: u32 = 0xffff_fffd;

fn main() -> ExitCode {
    match run(env::args().skip(1).collect()) {
        Ok(output) => {
            if !output.is_empty() {
                print!("{output}");
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::from(1)
        }
    }
}

fn run(arguments: Vec<String>) -> Result<String> {
    let mut create = false;
    let mut json_output = false;
    let mut txid_output = false;
    let mut version_output = false;
    let mut network = Network::Bitcoin;
    let mut positional = Vec::new();

    for argument in arguments {
        if argument == "-create" || argument == "--create" {
            create = true;
        } else if argument == "-json" || argument == "--json" {
            json_output = true;
        } else if argument == "-txid" || argument == "--txid" {
            txid_output = true;
        } else if argument == "-version" || argument == "--version" {
            version_output = true;
        } else if argument == "-help" || argument == "--help" || argument == "-?" {
            return Ok(help_text());
        } else if argument == "-mainnet" || argument == "--mainnet" {
            network = Network::Bitcoin;
        } else if argument == "-testnet" || argument == "--testnet" {
            network = Network::Testnet;
        } else if argument == "-testnet4" || argument == "--testnet4" {
            network = Network::Testnet4;
        } else if argument == "-signet" || argument == "--signet" {
            network = Network::Signet;
        } else if argument == "-regtest" || argument == "--regtest" {
            network = Network::Regtest;
        } else if let Some(value) = argument
            .strip_prefix("-chain=")
            .or_else(|| argument.strip_prefix("--chain="))
        {
            network = parse_network(value)?;
        } else if argument.starts_with('-') && argument != "-" {
            bail!("Invalid parameter {argument}");
        } else {
            positional.push(argument);
        }
    }

    if version_output {
        return Ok(format!(
            "Bitcoin Core bitcoin-tx utility version {VERSION}\n"
        ));
    }
    if positional.is_empty() && !create {
        return Err(anyhow!("too few parameters"));
    }

    let (mut transaction, commands) = if create {
        (
            Transaction {
                version: Version::TWO,
                lock_time: LockTime::ZERO,
                input: Vec::new(),
                output: Vec::new(),
            },
            positional,
        )
    } else {
        let transaction_hex = if positional[0] == "-" {
            let mut input = String::new();
            io::stdin().read_to_string(&mut input)?;
            input.trim().to_owned()
        } else {
            positional[0].clone()
        };
        let bytes = hex::decode(transaction_hex).context("invalid transaction encoding")?;
        let transaction =
            decode_transaction_core(&bytes).context("invalid transaction encoding")?;
        (transaction, positional.into_iter().skip(1).collect())
    };

    let mut registers = HashMap::new();
    for command in commands {
        let (name, value) = command
            .split_once('=')
            .map_or((command.as_str(), ""), |(name, value)| (name, value));
        mutate_transaction(&mut transaction, name, value, network, &mut registers)?;
    }

    let serialized = serialize_core(&transaction);
    if json_output {
        let value = core_transaction_json(&transaction, network, &serialized);
        return Ok(format_core_json(&value) + "\n");
    }
    if txid_output {
        return Ok(format!("{}\n", transaction.compute_txid()));
    }
    Ok(format!("{}\n", hex::encode(serialized)))
}

fn parse_network(value: &str) -> Result<Network> {
    match value {
        "main" | "mainnet" | "bitcoin" => Ok(Network::Bitcoin),
        "test" | "testnet" | "testnet3" => Ok(Network::Testnet),
        "testnet4" => Ok(Network::Testnet4),
        "signet" => Ok(Network::Signet),
        "regtest" => Ok(Network::Regtest),
        _ => bail!("Unknown chain {value}"),
    }
}

fn mutate_transaction(
    transaction: &mut Transaction,
    command: &str,
    value: &str,
    network: Network,
    registers: &mut HashMap<String, Value>,
) -> Result<()> {
    match command {
        "nversion" => {
            let version = parse_decimal_u32(value, "Invalid TX version requested")?;
            if !(1..=2).contains(&version) {
                bail!("Invalid TX version requested: '{value}'")
            }
            transaction.version = Version(version as i32);
        }
        "locktime" => {
            transaction.lock_time = LockTime::from_consensus(parse_decimal_u32(
                value,
                "Invalid TX locktime requested",
            )?);
        }
        "replaceable" => mutate_rbf(transaction, value)?,
        "delin" => {
            let index = parse_decimal_u32(value, "Invalid TX input index")? as usize;
            if index >= transaction.input.len() {
                bail!("Invalid TX input index '{value}'")
            }
            transaction.input.remove(index);
        }
        "delout" => {
            let index = parse_decimal_u32(value, "Invalid TX output index")? as usize;
            if index >= transaction.output.len() {
                bail!("Invalid TX output index '{value}'")
            }
            transaction.output.remove(index);
        }
        "in" => add_input(transaction, value)?,
        "outaddr" => add_address_output(transaction, value, network)?,
        "outpubkey" => add_pubkey_output(transaction, value, network)?,
        "outmultisig" => add_multisig_output(transaction, value, network)?,
        "outscript" => add_script_output(transaction, value)?,
        "outdata" => add_data_output(transaction, value)?,
        "set" => set_register(value, registers)?,
        "load" => load_register(value, registers)?,
        "sign" => sign_transaction(transaction, value, registers)?,
        _ => bail!("unknown command"),
    }
    Ok(())
}

fn parse_decimal_u32(value: &str, message: &str) -> Result<u32> {
    if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
        bail!("{message}: '{value}'")
    }
    value.parse().map_err(|_| anyhow!("{message}: '{value}'"))
}

fn parse_trimmed_decimal_u32(value: &str, message: &str) -> Result<u32> {
    let value = value.trim();
    if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
        bail!("{message} '{value}'")
    }
    value.parse().map_err(|_| anyhow!("{message} '{value}'"))
}

fn mutate_rbf(transaction: &mut Transaction, value: &str) -> Result<()> {
    let value = value.trim();
    if !value.is_empty() {
        let index = parse_decimal_u32(value, "Invalid TX input index")? as usize;
        if index >= transaction.input.len() {
            bail!("Invalid TX input index '{value}'")
        }
        let sequence = transaction.input[index].sequence.to_consensus_u32();
        if sequence > MAX_SEQUENCE_NONFINAL {
            transaction.input[index].sequence = Sequence::from_consensus(MAX_SEQUENCE_NONFINAL);
        }
        return Ok(());
    }
    for input in &mut transaction.input {
        if input.sequence.to_consensus_u32() > MAX_SEQUENCE_NONFINAL {
            input.sequence = Sequence::from_consensus(MAX_SEQUENCE_NONFINAL);
        }
    }
    Ok(())
}

fn add_input(transaction: &mut Transaction, value: &str) -> Result<()> {
    let fields = value.split(':').collect::<Vec<_>>();
    if fields.len() < 2 {
        bail!("TX input missing separator")
    }
    if fields[0].len() != 64 {
        bail!("invalid TX input txid")
    }
    let txid: Txid = fields[0]
        .parse()
        .map_err(|_| anyhow!("invalid TX input txid"))?;
    let vout = parse_decimal_u32(fields[1], "invalid TX input vout")?;
    let max_vout = (MAX_BLOCK_WEIGHT / (WITNESS_SCALE_FACTOR * MIN_TXOUT_SIZE)) as u32;
    if vout > max_vout {
        bail!("invalid TX input vout '{}'", fields[1])
    }
    let sequence = fields
        .get(2)
        .map(|value| parse_trimmed_decimal_u32(value, "invalid TX sequence id"))
        .transpose()?
        .unwrap_or(Sequence::MAX.to_consensus_u32());
    transaction.input.push(TxIn {
        previous_output: OutPoint::new(txid, vout),
        script_sig: ScriptBuf::new(),
        sequence: Sequence::from_consensus(sequence),
        witness: Witness::default(),
    });
    Ok(())
}

fn parse_amount(value: &str) -> Result<Amount> {
    let value = value.trim();
    if value.is_empty() || value.starts_with('-') || value.starts_with('+') {
        bail!("invalid TX output value")
    }
    let (whole, fraction) = value.split_once('.').map_or((value, ""), |parts| parts);
    if whole.is_empty() && fraction.is_empty()
        || !whole.bytes().all(|byte| byte.is_ascii_digit())
        || !fraction.bytes().all(|byte| byte.is_ascii_digit())
        || fraction.len() > 8
    {
        bail!("invalid TX output value")
    }
    let whole = if whole.is_empty() {
        0
    } else {
        whole
            .parse::<u64>()
            .map_err(|_| anyhow!("invalid TX output value"))?
    };
    let fraction_value = if fraction.is_empty() {
        0
    } else {
        fraction
            .parse::<u64>()
            .map_err(|_| anyhow!("invalid TX output value"))?
            * 10u64.pow((8 - fraction.len()) as u32)
    };
    let satoshis = whole
        .checked_mul(100_000_000)
        .and_then(|value| value.checked_add(fraction_value))
        .ok_or_else(|| anyhow!("Amount out of range"))?;
    if satoshis > MAX_MONEY_SAT {
        bail!("Amount out of range")
    }
    Ok(Amount::from_sat(satoshis))
}

fn add_address_output(transaction: &mut Transaction, value: &str, network: Network) -> Result<()> {
    let fields = value.split(':').collect::<Vec<_>>();
    if fields.len() != 2 {
        bail!("TX output missing or too many separators")
    }
    let amount = parse_amount(fields[0])?;
    let address: Address<NetworkUnchecked> = fields[1]
        .parse()
        .map_err(|_| anyhow!("invalid TX output address"))?;
    let address = address
        .require_network(network)
        .map_err(|_| anyhow!("invalid TX output address"))?;
    transaction.output.push(TxOut {
        value: amount,
        script_pubkey: address.script_pubkey(),
    });
    Ok(())
}

fn parse_pubkey(value: &str) -> Result<PublicKey> {
    let bytes = hex::decode(value).map_err(|_| anyhow!("invalid TX output pubkey"))?;
    PublicKey::from_slice(&bytes).map_err(|_| anyhow!("invalid TX output pubkey"))
}

fn add_pubkey_output(transaction: &mut Transaction, value: &str, network: Network) -> Result<()> {
    let fields = value.split(':').collect::<Vec<_>>();
    if fields.len() < 2 || fields.len() > 3 {
        bail!("TX output missing or too many separators")
    }
    let amount = parse_amount(fields[0])?;
    let public_key = parse_pubkey(fields[1])?;
    let flags = fields.get(2).copied().unwrap_or_default();
    let mut script = Builder::new()
        .push_key(&public_key)
        .push_opcode(OP_CHECKSIG)
        .into_script();
    if flags.contains('W') {
        if !public_key.compressed {
            bail!("Uncompressed pubkeys are not useable for SegWit outputs")
        }
        let compressed = bitcoin::CompressedPublicKey::try_from(public_key)
            .map_err(|_| anyhow!("Uncompressed pubkeys are not useable for SegWit outputs"))?;
        script = Address::p2wpkh(&compressed, network).script_pubkey();
    }
    if flags.contains('S') {
        script = script.to_p2sh();
    }
    transaction.output.push(TxOut {
        value: amount,
        script_pubkey: script,
    });
    Ok(())
}

fn add_multisig_output(transaction: &mut Transaction, value: &str, network: Network) -> Result<()> {
    let fields = value.split(':').collect::<Vec<_>>();
    if fields.len() < 3 {
        bail!("Not enough multisig parameters")
    }
    let amount = parse_amount(fields[0])?;
    let required = parse_trimmed_decimal_u32(fields[1], "invalid multisig required number")?;
    let key_count = parse_trimmed_decimal_u32(fields[2], "invalid multisig total number")?;
    if fields.len() < key_count as usize + 3 {
        bail!("incorrect number of multisig pubkeys")
    }
    if !(1..=16).contains(&required) || !(1..=16).contains(&key_count) || key_count < required {
        bail!("multisig parameter mismatch. Required {required} of {key_count}signatures.")
    }
    let public_keys = (0..key_count as usize)
        .map(|index| parse_pubkey(fields[index + 3]))
        .collect::<Result<Vec<_>>>()?;
    let flags_index = key_count as usize + 3;
    if fields.len() > flags_index + 1 {
        bail!("Too many parameters")
    }
    let flags = fields.get(flags_index).copied().unwrap_or_default();
    let mut builder = Builder::new().push_int(i64::from(required));
    for public_key in &public_keys {
        builder = builder.push_key(public_key);
    }
    let mut script = builder
        .push_int(i64::from(key_count))
        .push_opcode(OP_CHECKMULTISIG)
        .into_script();
    if flags.contains('W') {
        if public_keys.iter().any(|key| !key.compressed) {
            bail!("Uncompressed pubkeys are not useable for SegWit outputs")
        }
        script = script.to_p2wsh();
    }
    if flags.contains('S') {
        if script.len() > MAX_SCRIPT_ELEMENT_SIZE {
            bail!(
                "redeemScript exceeds size limit: {} > {}",
                script.len(),
                MAX_SCRIPT_ELEMENT_SIZE
            )
        }
        script = script.to_p2sh();
    }
    transaction.output.push(TxOut {
        value: amount,
        script_pubkey: script,
    });
    let _ = network;
    Ok(())
}

fn add_data_output(transaction: &mut Transaction, value: &str) -> Result<()> {
    let (amount, data) = if let Some((amount, data)) = value.split_once(':') {
        if amount.is_empty() {
            bail!("TX output value not specified")
        }
        (parse_amount(amount)?, data)
    } else {
        (Amount::ZERO, value)
    };
    if data.is_empty() || !is_hex(data) {
        bail!("invalid TX output data")
    }
    let bytes = hex::decode(data).map_err(|_| anyhow!("invalid TX output data"))?;
    let data = PushBytesBuf::try_from(bytes).map_err(|_| anyhow!("invalid TX output data"))?;
    transaction.output.push(TxOut {
        value: amount,
        script_pubkey: Builder::new()
            .push_opcode(OP_RETURN)
            .push_slice(data)
            .into_script(),
    });
    Ok(())
}

fn add_script_output(transaction: &mut Transaction, value: &str) -> Result<()> {
    let fields = value.split(':').collect::<Vec<_>>();
    if fields.len() < 2 {
        bail!("TX output missing separator")
    }
    let amount = parse_amount(fields[0])?;
    let mut script = parse_script(fields[1])?;
    if script.len() > MAX_SCRIPT_SIZE {
        bail!(
            "script exceeds size limit: {} > {}",
            script.len(),
            MAX_SCRIPT_SIZE
        )
    }
    let flags = fields.get(2).copied().unwrap_or_default();
    if flags.contains('W') {
        script = script.to_p2wsh();
    }
    if flags.contains('S') {
        if script.len() > MAX_SCRIPT_ELEMENT_SIZE {
            bail!(
                "redeemScript exceeds size limit: {} > {}",
                script.len(),
                MAX_SCRIPT_ELEMENT_SIZE
            )
        }
        script = script.to_p2sh();
    }
    transaction.output.push(TxOut {
        value: amount,
        script_pubkey: script,
    });
    Ok(())
}

fn is_hex(value: &str) -> bool {
    value.len() % 2 == 0 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn parse_script(value: &str) -> Result<ScriptBuf> {
    let mut builder = Builder::new();
    for token in value.split_whitespace() {
        if let Some(opcode) = parse_opcode(token) {
            builder = builder.push_opcode(opcode);
        } else if let Ok(number) = token.parse::<i64>() {
            if !(-(u32::MAX as i64)..=(u32::MAX as i64)).contains(&number) {
                bail!(
                    "script parse error: decimal numeric value only allowed in the range -0xFFFFFFFF...0xFFFFFFFF"
                )
            }
            builder = builder.push_int(number);
        } else if is_decimal_token(token) {
            bail!(
                "script parse error: decimal numeric value only allowed in the range -0xFFFFFFFF...0xFFFFFFFF"
            )
        } else if is_hex(token) {
            let bytes = hex::decode(token).map_err(|_| anyhow!("script parse error"))?;
            if bytes.len() > MAX_SCRIPT_ELEMENT_SIZE {
                bail!("script element exceeds size limit")
            }
            let bytes = PushBytesBuf::try_from(bytes).map_err(|_| anyhow!("script parse error"))?;
            builder = builder.push_slice(bytes);
        } else {
            bail!("script parse error: unknown opcode")
        }
    }
    Ok(builder.into_script())
}

fn parse_opcode(token: &str) -> Option<Opcode> {
    let code = match token {
        "OP_0" | "OP_FALSE" => 0x00,
        "OP_1NEGATE" => 0x4f,
        "OP_1" | "OP_TRUE" => 0x51,
        "OP_2" => 0x52,
        "OP_3" => 0x53,
        "OP_4" => 0x54,
        "OP_5" => 0x55,
        "OP_6" => 0x56,
        "OP_7" => 0x57,
        "OP_8" => 0x58,
        "OP_9" => 0x59,
        "OP_10" => 0x5a,
        "OP_11" => 0x5b,
        "OP_12" => 0x5c,
        "OP_13" => 0x5d,
        "OP_14" => 0x5e,
        "OP_15" => 0x5f,
        "OP_16" => 0x60,
        "OP_NOP" => 0x61,
        "OP_IF" => 0x63,
        "OP_NOTIF" => 0x64,
        "OP_ELSE" => 0x67,
        "OP_ENDIF" => 0x68,
        "OP_VERIFY" => 0x69,
        "OP_RETURN" => 0x6a,
        "OP_TOALTSTACK" => 0x6b,
        "OP_FROMALTSTACK" => 0x6c,
        "OP_2DROP" => 0x6d,
        "OP_2DUP" => 0x6e,
        "OP_3DUP" => 0x6f,
        "OP_2OVER" => 0x70,
        "OP_2ROT" => 0x71,
        "OP_2SWAP" => 0x72,
        "OP_IFDUP" => 0x73,
        "OP_DEPTH" => 0x74,
        "OP_DROP" => 0x75,
        "OP_DUP" => 0x76,
        "OP_NIP" => 0x77,
        "OP_OVER" => 0x78,
        "OP_PICK" => 0x79,
        "OP_ROLL" => 0x7a,
        "OP_ROT" => 0x7b,
        "OP_SWAP" => 0x7c,
        "OP_TUCK" => 0x7d,
        "OP_2MUL" => 0x8d,
        "OP_2DIV" => 0x8e,
        "OP_INVERT" => 0x83,
        "OP_ADD" => 0x93,
        "OP_SUB" => 0x94,
        "OP_BOOLAND" => 0x9a,
        "OP_BOOLOR" => 0x9b,
        "OP_NUMEQUAL" => 0x9c,
        "OP_NUMEQUALVERIFY" => 0x9d,
        "OP_NUMNOTEQUAL" => 0x9e,
        "OP_LESSTHAN" => 0x9f,
        "OP_GREATERTHAN" => 0xa0,
        "OP_LESSTHANOREQUAL" => 0xa1,
        "OP_GREATERTHANOREQUAL" => 0xa2,
        "OP_MIN" => 0xa3,
        "OP_MAX" => 0xa4,
        "OP_WITHIN" => 0xa5,
        "OP_RIPEMD160" => 0xa6,
        "OP_SHA1" => 0xa7,
        "OP_SHA256" => 0xa8,
        "OP_HASH160" => 0xa9,
        "OP_HASH256" => 0xaa,
        "OP_CODESEPARATOR" => 0xab,
        "OP_CHECKSIG" => 0xac,
        "OP_CHECKSIGVERIFY" => 0xad,
        "OP_CHECKMULTISIG" => 0xae,
        "OP_CHECKMULTISIGVERIFY" => 0xaf,
        "OP_NOP1" => 0xb0,
        "OP_CHECKLOCKTIMEVERIFY" | "OP_NOP2" => 0xb1,
        "OP_CHECKSEQUENCEVERIFY" | "OP_NOP3" => 0xb2,
        "OP_NOP4" => 0xb3,
        "OP_NOP5" => 0xb4,
        "OP_NOP6" => 0xb5,
        "OP_NOP7" => 0xb6,
        "OP_NOP8" => 0xb7,
        "OP_NOP9" => 0xb8,
        "OP_NOP10" => 0xb9,
        "OP_CHECKSIGADD" => 0xba,
        _ => return None,
    };
    Some(Opcode::from(code))
}

fn set_register(value: &str, registers: &mut HashMap<String, Value>) -> Result<()> {
    let (name, json) = value
        .split_once(':')
        .ok_or_else(|| anyhow!("Register input requires NAME:VALUE"))?;
    if name.is_empty() || json.is_empty() {
        bail!("Register input requires NAME:VALUE")
    }
    let value: Value =
        serde_json::from_str(json).map_err(|_| anyhow!("Cannot parse JSON for key {name}"))?;
    registers.insert(name.to_owned(), value);
    Ok(())
}

fn load_register(value: &str, registers: &mut HashMap<String, Value>) -> Result<()> {
    let (name, filename) = value
        .split_once(':')
        .ok_or_else(|| anyhow!("Register load requires NAME:FILENAME"))?;
    if name.is_empty() || filename.is_empty() {
        bail!("Register load requires NAME:FILENAME")
    }
    let contents =
        fs::read_to_string(filename).with_context(|| format!("Cannot open file {filename}"))?;
    let value: Value =
        serde_json::from_str(&contents).map_err(|_| anyhow!("Cannot parse JSON for key {name}"))?;
    registers.insert(name.to_owned(), value);
    Ok(())
}

fn sign_transaction(
    transaction: &mut Transaction,
    sighash_name: &str,
    registers: &HashMap<String, Value>,
) -> Result<()> {
    let sighash_name = if sighash_name.is_empty() {
        "ALL"
    } else {
        sighash_name
    };
    let private_keys = registers
        .get("privatekeys")
        .ok_or_else(|| anyhow!("privatekeys register variable must be set."))?
        .as_array()
        .ok_or_else(|| anyhow!("privatekeys register variable must be set."))?
        .iter()
        .map(|value| {
            let wif = value
                .as_str()
                .ok_or_else(|| anyhow!("privatekey not a std::string"))?;
            PrivateKey::from_wif(wif).map_err(|_| anyhow!("privatekey not valid"))
        })
        .collect::<Result<Vec<_>>>()?;
    let prevouts = registers
        .get("prevtxs")
        .ok_or_else(|| anyhow!("prevtxs register variable must be set."))?;
    let prevouts = parse_prevouts(prevouts)?;
    bitcoind_rs::rpc::sign_transaction_offline(transaction, &private_keys, &prevouts, sighash_name)
}

fn parse_prevouts(value: &Value) -> Result<HashMap<OutPoint, bitcoind_rs::rpc::SigningPrevout>> {
    let entries = value
        .as_array()
        .ok_or_else(|| anyhow!("expected prevtxs internal object"))?;
    entries
        .iter()
        .map(|entry| {
            let entry = entry
                .as_object()
                .ok_or_else(|| anyhow!("expected prevtxs internal object"))?;
            let txid_value = entry
                .get("txid")
                .and_then(Value::as_str)
                .ok_or_else(|| anyhow!("txid must be hexadecimal string"))?;
            if txid_value.len() != 64 {
                bail!("txid must be hexadecimal string (not '{txid_value}')")
            }
            let txid: Txid = txid_value
                .parse()
                .map_err(|_| anyhow!("txid must be hexadecimal string (not '{txid_value}')"))?;
            let vout_value = entry
                .get("vout")
                .and_then(Value::as_u64)
                .ok_or_else(|| anyhow!("prevtxs internal object typecheck fail"))?;
            let vout = u32::try_from(vout_value).map_err(|_| anyhow!("vout is out of range"))?;
            let script_hex = entry
                .get("scriptPubKey")
                .and_then(Value::as_str)
                .ok_or_else(|| anyhow!("scriptPubKey must be hexadecimal string"))?;
            if !is_hex(script_hex) && !script_hex.is_empty() {
                bail!("scriptPubKey must be hexadecimal string")
            }
            let script_pubkey = ScriptBuf::from_bytes(hex::decode(script_hex)?);
            let amount_provided = entry.get("amount").is_some_and(|value| !value.is_null());
            let amount = entry
                .get("amount")
                .filter(|value| !value.is_null())
                .map(value_to_amount)
                .transpose()?
                .unwrap_or_else(|| Amount::from_sat(MAX_MONEY_SAT));
            let redeem_script = parse_optional_script(entry.get("redeemScript"))?;
            let witness_script = parse_optional_script(entry.get("witnessScript"))?;
            Ok((
                OutPoint::new(txid, vout),
                bitcoind_rs::rpc::SigningPrevout {
                    output: TxOut {
                        value: amount,
                        script_pubkey,
                    },
                    amount_provided,
                    redeem_script,
                    witness_script,
                },
            ))
        })
        .collect()
}

fn value_to_amount(value: &Value) -> Result<Amount> {
    match value {
        Value::String(value) => parse_amount(value),
        Value::Number(value) => parse_amount(&value.to_string()),
        _ => bail!("Amount is not a number or string"),
    }
}

fn parse_optional_script(value: Option<&Value>) -> Result<Option<ScriptBuf>> {
    value
        .filter(|value| !value.is_null())
        .map(|value| {
            let script = value
                .as_str()
                .ok_or_else(|| anyhow!("script must be hexadecimal string"))?;
            Ok(ScriptBuf::from_bytes(hex::decode(script)?))
        })
        .transpose()
}

fn format_core_json(value: &Value) -> String {
    let mut output = String::new();
    write_core_json(value, 0, None, &mut output);
    output
}

fn write_core_json(value: &Value, depth: usize, key: Option<&str>, output: &mut String) {
    match value {
        Value::Object(object) => {
            output.push('{');
            output.push('\n');
            for (index, (key, value)) in object.iter().enumerate() {
                write_indent(depth + 1, output);
                output.push_str(&serde_json::to_string(key).expect("JSON object key"));
                output.push_str(": ");
                write_core_json(value, depth + 1, Some(key), output);
                if index + 1 != object.len() {
                    output.push(',');
                }
                output.push('\n');
            }
            write_indent(depth, output);
            output.push('}');
        }
        Value::Array(array) => {
            output.push('[');
            output.push('\n');
            for (index, value) in array.iter().enumerate() {
                write_indent(depth + 1, output);
                write_core_json(value, depth + 1, None, output);
                if index + 1 != array.len() {
                    output.push(',');
                }
                output.push('\n');
            }
            write_indent(depth, output);
            output.push(']');
        }
        Value::String(value) => {
            output.push_str(&serde_json::to_string(value).expect("JSON string"));
        }
        Value::Number(value) => {
            if key == Some("value") {
                if let Some(value) = value.as_f64() {
                    output.push_str(&format!("{value:.8}"));
                } else {
                    output.push_str(&value.to_string());
                }
            } else {
                output.push_str(&value.to_string());
            }
        }
        Value::Bool(value) => output.push_str(if *value { "true" } else { "false" }),
        Value::Null => output.push_str("null"),
    }
}

fn write_indent(depth: usize, output: &mut String) {
    for _ in 0..depth {
        output.push_str("    ");
    }
}

fn is_decimal_token(value: &str) -> bool {
    let digits = value.strip_prefix('-').unwrap_or(value);
    !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit())
}

fn decode_transaction_core(bytes: &[u8]) -> Result<Transaction> {
    if let Ok(transaction) = deserialize(bytes) {
        return Ok(transaction);
    }
    let mut cursor = Cursor::new(bytes);
    let version = Version::consensus_decode_from_finite_reader(&mut cursor)?;
    let input = Vec::<TxIn>::consensus_decode_from_finite_reader(&mut cursor)?;
    let output = Vec::<TxOut>::consensus_decode_from_finite_reader(&mut cursor)?;
    let lock_time = LockTime::consensus_decode_from_finite_reader(&mut cursor)?;
    if cursor.position() != bytes.len() as u64 {
        bail!("invalid transaction encoding")
    }
    Ok(Transaction {
        version,
        lock_time,
        input,
        output,
    })
}

fn serialize_core(transaction: &Transaction) -> Vec<u8> {
    if !transaction.input.is_empty() {
        return serialize(transaction);
    }
    let mut bytes = Vec::new();
    transaction
        .version
        .consensus_encode(&mut bytes)
        .expect("Vec cannot fail");
    transaction
        .input
        .consensus_encode(&mut bytes)
        .expect("Vec cannot fail");
    transaction
        .output
        .consensus_encode(&mut bytes)
        .expect("Vec cannot fail");
    transaction
        .lock_time
        .consensus_encode(&mut bytes)
        .expect("Vec cannot fail");
    bytes
}

fn core_transaction_json(transaction: &Transaction, network: Network, serialized: &[u8]) -> Value {
    let decoded = bitcoind_rs::rpc::decoded_transaction_json(transaction, network);
    let object = decoded.as_object().expect("decoded transaction object");
    let txid = transaction.compute_txid().to_string();
    let wtxid = if transaction.input.is_empty() {
        txid.clone()
    } else {
        transaction.compute_wtxid().to_string()
    };
    let (size, vsize, weight) = if transaction.input.is_empty() {
        let size = serialized.len();
        (size, size, size * 4)
    } else {
        (
            serialized.len(),
            transaction.vsize(),
            transaction.weight().to_wu() as usize,
        )
    };
    let mut result = Map::new();
    result.insert("txid".to_owned(), Value::String(txid));
    result.insert("hash".to_owned(), Value::String(wtxid));
    result.insert("version".to_owned(), json!(transaction.version.0 as u32));
    result.insert("size".to_owned(), json!(size));
    result.insert("vsize".to_owned(), json!(vsize));
    result.insert("weight".to_owned(), json!(weight));
    result.insert(
        "locktime".to_owned(),
        json!(transaction.lock_time.to_consensus_u32()),
    );
    result.insert(
        "vin".to_owned(),
        object.get("vin").cloned().unwrap_or_else(|| json!([])),
    );
    result.insert(
        "vout".to_owned(),
        object.get("vout").cloned().unwrap_or_else(|| json!([])),
    );
    result.insert("hex".to_owned(), Value::String(hex::encode(serialized)));
    Value::Object(result)
}

fn help_text() -> String {
    format!(
        "Bitcoin Core bitcoin-tx utility version {VERSION}\n\n\
The bitcoin-tx tool is used for creating and modifying bitcoin transactions.\n\n\
Usage: bitcoin-tx [options] <hex-tx> [commands]\n\
or:    bitcoin-tx [options] -create [commands]\n"
    )
}

#[cfg(test)]
mod tests {
    use super::{decode_transaction_core, parse_amount, parse_script, run};
    use bitcoin::Transaction;

    #[test]
    fn creates_blank_transactions() {
        let output = run(vec!["-create".to_owned(), "nversion=1".to_owned()]).unwrap();
        let transaction: Transaction =
            decode_transaction_core(&hex::decode(output.trim()).unwrap()).unwrap();
        assert_eq!(transaction.version.0, 1);
        assert_eq!(output.trim().len() / 2, 10);
    }

    #[test]
    fn parses_core_script_numbers_and_opcodes() {
        assert_eq!(parse_script("OP_DROP").unwrap().as_bytes(), &[0x75]);
        assert_eq!(parse_script("4294967295").unwrap().len(), 6);
        assert!(parse_script("4294967296").is_err());
    }

    #[test]
    fn parses_fixed_point_amounts() {
        assert_eq!(parse_amount("0.00000001").unwrap().to_sat(), 1);
        assert_eq!(parse_amount(" 1.25 ").unwrap().to_sat(), 125_000_000);
        assert!(parse_amount("1.000000001").is_err());
    }
}
