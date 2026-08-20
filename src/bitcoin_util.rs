//! Wallet-free implementation of Core's `bitcoin-util` utility.
//!
//! Bitcoin Core currently exposes one command from this binary: `grind`,
//! which searches the nonce field of a serialized block header for a proof of
//! work.  The command is deliberately independent of a running node and of
//! any wallet state.

use std::env;
use std::process::ExitCode;
use std::sync::{
    Arc,
    atomic::{AtomicBool, AtomicU32, Ordering},
};
use std::thread;

use bitcoin::block::Header;
use bitcoin::consensus::{deserialize, serialize};

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
    if command != "grind" {
        return Err(format!(
            "Error parsing command line arguments: Invalid command '{command}'"
        ));
    }
    grind(&command_arguments[1..])
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

fn help_text() -> String {
    format!(
        "Bitcoin Core bitcoin-util utility version {VERSION}\n\n\
The bitcoin-util tool provides bitcoin related functionality that does not rely on a running node.\n\n\
Usage: bitcoin-util [options] [command]\n\
       bitcoin-util [options] grind <hex-block-header>\n\n\
Commands:\n\
  grind   Perform proof of work on a serialized block header"
    )
}

#[cfg(test)]
mod tests {
    use super::{grind, run};
    use bitcoin::block::{Header, Version};
    use bitcoin::consensus::serialize;
    use bitcoin::hashes::Hash;
    use bitcoin::pow::CompactTarget;

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
}
