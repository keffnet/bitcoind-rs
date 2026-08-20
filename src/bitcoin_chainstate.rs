//! Wallet-free implementation of Core's experimental `bitcoin-chainstate`
//! consensus demo utility.
//!
//! The utility opens a native chainstate directory, reads full blocks as hex
//! lines from stdin, and reports whether each block was accepted or was a
//! duplicate. It deliberately uses the same validation and durable stores as
//! the daemon without starting network, RPC, wallet, or Electrum services.

use std::env;
use std::io::{self, BufRead, Write};
use std::path::PathBuf;
use std::process::ExitCode;

use anyhow::{Context, Result, anyhow, bail};
use bitcoin::consensus::deserialize;
use bitcoin::{Block, Network};
use bitcoind_rs::chain::ChainState;

fn main() -> ExitCode {
    match run(env::args().skip(1).collect()) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error:#}");
            ExitCode::from(1)
        }
    }
}

fn run(arguments: Vec<String>) -> Result<()> {
    let (network, data_dir) = parse_arguments(&arguments)?;
    let mut chain = ChainState::open_with_options_and_tx_index_in_dirs_with_minimum_chain_work_and_assume_valid_and_blocks_xor(
        network,
        &data_dir,
        data_dir.join("blocks"),
        None,
        true,
        false,
        false,
        true,
        None,
        None,
        true,
    )
    .with_context(|| format!("opening chainstate directory {}", data_dir.display()))?;

    println!("Enter the block you want to validate on the next line:");
    io::stdout().flush()?;
    for line in io::stdin().lock().lines() {
        let line = line?;
        if line.is_empty() {
            eprintln!("Empty line found, try again:");
            continue;
        }

        let bytes = match hex::decode(&line) {
            Ok(bytes) => bytes,
            Err(_) => {
                eprintln!("Block decode failed, try again:");
                continue;
            }
        };
        let block: Block = match deserialize(&bytes) {
            Ok(block) => block,
            Err(_) => {
                eprintln!("Block decode failed, try again:");
                continue;
            }
        };
        let hash = block.block_hash();
        let duplicate = chain
            .block(&hash)
            .with_context(|| format!("checking whether block {hash} is already stored"))?
            .is_some();
        let previous_tip = chain.best_hash();

        match chain.connect_block(block) {
            Ok(tip) if duplicate => {
                let _ = tip;
                eprintln!("Block is a duplicate");
            }
            Ok(tip) => {
                eprintln!("Block has not yet been rejected");
                if tip.hash != previous_tip {
                    println!("Block tip changed");
                }
            }
            Err(error) => eprintln!("Block was not accepted: {error}"),
        }
    }
    Ok(())
}

fn parse_arguments(arguments: &[String]) -> Result<(Network, PathBuf)> {
    match arguments {
        [data_dir] if !data_dir.starts_with('-') => Ok((Network::Bitcoin, PathBuf::from(data_dir))),
        [flag, data_dir] if flag == "-regtest" || flag == "--regtest" => {
            Ok((Network::Regtest, PathBuf::from(data_dir)))
        }
        [] => bail!(usage()),
        _ => Err(anyhow!(usage())),
    }
}

fn usage() -> &'static str {
    "Usage: bitcoin-chainstate [-regtest] DATADIR"
}
