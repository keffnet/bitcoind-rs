//! Wallet-free implementation of Core's `bitcoin-util` utility.
//!
//! Bitcoin Core exposes `grind`, which searches the nonce field of a
//! serialized block header for proof of work. This implementation also adds
//! `compressioninfo`, a node-independent inspector for native append-only
//! storage files.

use std::env;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::{
    Arc,
    atomic::{AtomicBool, AtomicU32, Ordering},
};
use std::thread;

use bitcoin::block::Header;
use bitcoin::consensus::{deserialize, serialize};
use bitcoind_rs::storage::{STORAGE_COMPRESSION_LEVEL, inspect_storage_file_compression};
use serde_json::json;

const VERSION: &str = "31.1.0";

fn main() -> ExitCode {
    match run(env::args().skip(1).collect()) {
        Ok(output) => {
            if !output.is_empty() {
                println!("{output}");
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("{error}");
            ExitCode::from(1)
        }
    }
}

fn run(arguments: Vec<String>) -> Result<String, String> {
    if arguments.iter().any(|argument| {
        matches!(
            argument.as_str(),
            "-help" | "--help" | "-?" | "--version" | "-version"
        )
    }) {
        if arguments
            .iter()
            .any(|argument| matches!(argument.as_str(), "--version" | "-version"))
        {
            return Ok(format!(
                "Bitcoin Core bitcoin-util utility version {VERSION}"
            ));
        }
        return Ok(help_text());
    }

    let mut command_arguments = Vec::with_capacity(arguments.len());
    for argument in arguments {
        if argument.starts_with('-') && argument != "-" {
            let option = argument
                .split_once('=')
                .map_or(argument.as_str(), |(name, _)| name);
            if matches!(
                option,
                "-mainnet"
                    | "--mainnet"
                    | "-testnet"
                    | "--testnet"
                    | "-testnet4"
                    | "--testnet4"
                    | "-signet"
                    | "--signet"
                    | "-regtest"
                    | "--regtest"
                    | "-chain"
                    | "--chain"
                    | "-datadir"
                    | "--datadir"
                    | "-conf"
                    | "--conf"
            ) {
                continue;
            }
            return Err(format!(
                "Error parsing command line arguments: Invalid parameter {argument}"
            ));
        }
        command_arguments.push(argument);
    }

    let Some(command) = command_arguments.first() else {
        return Err(format!("{}\nError: must specify a command", help_text()));
    };
    match command.as_str() {
        "grind" => grind(&command_arguments[1..]),
        "compressioninfo" => compression_info(&command_arguments[1..]),
        _ => Err(format!(
            "Error parsing command line arguments: Invalid command '{command}'"
        )),
    }
}

fn grind(arguments: &[String]) -> Result<String, String> {
    if arguments.len() != 1 {
        return Err("Must specify block header to grind".to_owned());
    }
    let bytes =
        hex::decode(&arguments[0]).map_err(|_| "Could not decode block header".to_owned())?;
    let mut header: Header =
        deserialize(&bytes).map_err(|_| "Could not decode block header".to_owned())?;
    if bytes.len() != 80 {
        return Err("Could not decode block header".to_owned());
    }

    let thread_count = thread::available_parallelism()
        .map_or(1, |parallelism| parallelism.get())
        .min(64);
    let found = Arc::new(AtomicBool::new(false));
    let proposed_nonce = Arc::new(AtomicU32::new(0));
    let mut workers = Vec::with_capacity(thread_count);

    for offset in 0..thread_count {
        let mut worker_header = header;
        let found = Arc::clone(&found);
        let proposed_nonce = Arc::clone(&proposed_nonce);
        workers.push(thread::spawn(move || {
            let step = thread_count as u32;
            let mut nonce = offset as u32;
            loop {
                if found.load(Ordering::Acquire) {
                    return;
                }
                worker_header.nonce = nonce;
                if worker_header.target().is_met_by(worker_header.block_hash()) {
                    if !found.swap(true, Ordering::AcqRel) {
                        proposed_nonce.store(nonce, Ordering::Release);
                    }
                    return;
                }
                if nonce > u32::MAX - step {
                    return;
                }
                nonce += step;
            }
        }));
    }
    for worker in workers {
        worker
            .join()
            .map_err(|_| "Could not satisfy difficulty target".to_owned())?;
    }

    if !found.load(Ordering::Acquire) {
        return Err("Could not satisfy difficulty target".to_owned());
    }
    header.nonce = proposed_nonce.load(Ordering::Acquire);
    Ok(hex::encode(serialize(&header)))
}

fn compression_info(arguments: &[String]) -> Result<String, String> {
    if !(1..=2).contains(&arguments.len()) {
        return Err("Usage: bitcoin-util compressioninfo <storage-file> [xor-key-file]".to_owned());
    }
    let path = PathBuf::from(&arguments[0]);
    let xor_key_path = arguments.get(1).map(Path::new);
    let info = inspect_storage_file_compression(&path, xor_key_path)
        .map_err(|error| format!("Could not inspect native storage file: {error:#}"))?;
    serde_json::to_string_pretty(&json!({
        "path": path,
        "codec": "zstd",
        "compression_level": STORAGE_COMPRESSION_LEVEL,
        "records": info.records,
        "compressed_records": info.compressed_records,
        "uncompressed_records": info.uncompressed_records,
        "original_payload_bytes": info.original_payload_bytes,
        "stored_payload_bytes": info.stored_payload_bytes,
        "framing_bytes": info.framing_bytes,
        "uncompressed_size_bytes": info.uncompressed_size_bytes,
        "stored_size_bytes": info.stored_size_bytes,
        "saved_bytes": info.saved_bytes,
        "space_saved_percent": info.space_saved_percent,
        "compression_ratio": info.compression_ratio,
    }))
    .map_err(|error| format!("Could not encode compression report: {error}"))
}

fn help_text() -> String {
    format!(
        "Bitcoin Core bitcoin-util utility version {VERSION}\n\n\
The bitcoin-util tool provides bitcoin related functionality that does not rely on a running node.\n\n\
Usage: bitcoin-util [options] [command]\n\
       bitcoin-util [options] grind <hex-block-header>\n\
       bitcoin-util compressioninfo <storage-file> [xor-key-file]\n\n\
Commands:\n\
  grind             Perform proof of work on a serialized block header\n\
  compressioninfo   Report native append-only Zstandard storage savings"
    )
}

#[cfg(test)]
mod tests {
    use super::{compression_info, grind, run};
    use bitcoin::Network;
    use bitcoin::block::{Header, Version};
    use bitcoin::blockdata::constants::genesis_block;
    use bitcoin::consensus::serialize;
    use bitcoin::hashes::Hash;
    use bitcoin::pow::CompactTarget;
    use bitcoind_rs::storage::BlockStore;

    #[test]
    fn rejects_unknown_commands_like_core() {
        assert_eq!(
            run(vec!["foo".to_owned()]).unwrap_err(),
            "Error parsing command line arguments: Invalid command 'foo'"
        );
    }

    #[test]
    fn rejects_invalid_grind_inputs() {
        assert_eq!(
            grind(&[]).unwrap_err(),
            "Must specify block header to grind"
        );
        assert_eq!(
            grind(&["aa".to_owned()]).unwrap_err(),
            "Could not decode block header"
        );
    }

    #[test]
    fn grinds_a_regtest_header() {
        let header = Header {
            version: Version::TWO,
            prev_blockhash: bitcoin::BlockHash::all_zeros(),
            merkle_root: bitcoin::TxMerkleNode::all_zeros(),
            time: 1,
            bits: CompactTarget::from_consensus(0x207f_ffff),
            nonce: 0,
        };
        let output = grind(&[hex::encode(serialize(&header))]).unwrap();
        let solved: Header =
            bitcoin::consensus::deserialize(&hex::decode(output).unwrap()).unwrap();
        assert!(solved.target().is_met_by(solved.block_hash()));
    }

    #[test]
    fn reports_compression_for_a_native_xored_storage_file() {
        let directory = tempfile::tempdir().unwrap();
        let block = genesis_block(Network::Regtest);
        let mut store = BlockStore::open_with_xor(directory.path(), true).unwrap();
        store.insert(&block).unwrap();
        drop(store);

        let output = compression_info(&[directory
            .path()
            .join("blocks.dat")
            .to_string_lossy()
            .into_owned()])
        .unwrap();
        let report: serde_json::Value = serde_json::from_str(&output).unwrap();
        assert_eq!(report["codec"], serde_json::json!("zstd"));
        assert_eq!(report["records"], serde_json::json!(1));
        assert_eq!(
            report["stored_size_bytes"],
            serde_json::json!(
                std::fs::metadata(directory.path().join("blocks.dat"))
                    .unwrap()
                    .len()
            )
        );
    }
}
