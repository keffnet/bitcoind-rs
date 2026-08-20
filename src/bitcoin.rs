//! Core-compatible launcher for the wallet-free node command.
//!
//! Bitcoin Core v31 exposes a `bitcoin` wrapper whose `node` subcommand
//! selects the daemon and whose `-m` form selects the multiprocess node.  The
//! Rust implementation uses one native daemon binary for both modes: the
//! transport and IPC services already live in that process, so a second
//! process boundary would only add overhead without adding functionality.

use std::env;
use std::path::PathBuf;
use std::process::{Command, ExitCode};

const VERSION: &str = "31.1.0";

fn main() -> ExitCode {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    let explicitly_multiprocess = arguments
        .iter()
        .any(|argument| matches!(argument.as_str(), "-m" | "--multiprocess"));
    let explicitly_monolithic = arguments
        .iter()
        .any(|argument| matches!(argument.as_str(), "-M" | "--monolithic"));
    let ipc_argument = arguments.iter().any(|argument| {
        matches!(
            argument
                .split_once('=')
                .map(|(name, _)| name)
                .unwrap_or(argument),
            "-ipcbind" | "--ipcbind" | "-ipcconnect" | "--ipcconnect" | "-ipcfd" | "--ipcfd"
        )
    });
    let ipc_configured = config_requests_ipc(&arguments);
    let multiprocess =
        explicitly_multiprocess || (!explicitly_monolithic && (ipc_argument || ipc_configured));
    let mut arguments = daemon_arguments(arguments);

    // Core's `bitcoin` launcher starts the IPC node without any of the
    // daemon-only auxiliary listeners.  Electrum is an intentional extra
    // service of bitcoind-rs, but leaving its default listener enabled here
    // makes a Core-style IPC launch unexpectedly claim port 30001 and can
    // collide with an independently managed Electrum service.  Preserve an
    // explicit command-line or config-file choice; otherwise disable only
    // the extra listener for IPC launches.
    if (ipc_argument || ipc_configured)
        && !has_electrum_argument(&arguments)
        && !config_requests_electrum(&arguments)
    {
        arguments.push("--electrum=0".to_owned());
    }

    if explicitly_monolithic && (ipc_argument || ipc_configured) {
        let invalid = arguments
            .iter()
            .find(|argument| argument.starts_with("-ipcbind") || argument.starts_with("--ipcbind"))
            .map(String::as_str)
            .unwrap_or("-ipcbind");
        eprintln!("Error: Error parsing command line arguments: Invalid parameter {invalid}");
        return ExitCode::from(1);
    }

    if arguments.iter().any(|argument| {
        matches!(
            argument.as_str(),
            "-version" | "--version" | "-version=1" | "--version=1"
        )
    }) {
        println!(
            "Bitcoin Core daemon version {VERSION} {}",
            if multiprocess {
                "bitcoin-node"
            } else {
                "bitcoind"
            }
        );
        return ExitCode::SUCCESS;
    }

    let daemon = daemon_path();
    match Command::new(&daemon).args(arguments).status() {
        Ok(status) => status
            .code()
            .and_then(|code| u8::try_from(code).ok())
            .map_or(ExitCode::from(1), ExitCode::from),
        Err(error) => {
            eprintln!("Error: failed to launch {}: {error}", daemon.display());
            ExitCode::from(1)
        }
    }
}

fn daemon_arguments(arguments: Vec<String>) -> Vec<String> {
    let mut arguments = arguments.into_iter();
    let mut filtered = Vec::new();
    let mut command_seen = false;
    for argument in arguments.by_ref() {
        if matches!(
            argument.as_str(),
            "-m" | "-M" | "--multiprocess" | "--monolithic"
        ) {
            continue;
        }
        if !command_seen && argument == "node" {
            command_seen = true;
            continue;
        }
        filtered.push(argument);
    }
    filtered
}

fn config_requests_ipc(arguments: &[String]) -> bool {
    let datadir = arguments.iter().find_map(|argument| {
        argument
            .strip_prefix("-datadir=")
            .or_else(|| argument.strip_prefix("--datadir="))
    });
    let Some(datadir) = datadir else {
        return false;
    };
    let path = PathBuf::from(datadir).join("bitcoin.conf");
    std::fs::read_to_string(path).is_ok_and(|contents| {
        contents.lines().any(|line| {
            let line = line.split('#').next().unwrap_or_default().trim();
            line.starts_with("ipcbind=")
                || line.starts_with("ipcconnect=")
                || line.starts_with("ipcfd=")
        })
    })
}

fn has_electrum_argument(arguments: &[String]) -> bool {
    arguments.iter().any(|argument| {
        matches!(
            argument
                .split_once('=')
                .map(|(name, _)| name)
                .unwrap_or(argument),
            "-electrum" | "--electrum"
        )
    })
}

fn config_requests_electrum(arguments: &[String]) -> bool {
    let datadir = arguments.iter().find_map(|argument| {
        argument
            .strip_prefix("-datadir=")
            .or_else(|| argument.strip_prefix("--datadir="))
    });
    let Some(datadir) = datadir else {
        return false;
    };
    let path = PathBuf::from(datadir).join("bitcoin.conf");
    std::fs::read_to_string(path).is_ok_and(|contents| {
        contents.lines().any(|line| {
            let line = line.split('#').next().unwrap_or_default().trim();
            line.starts_with("electrum=")
        })
    })
}

fn daemon_path() -> PathBuf {
    if let Some(path) = env::var_os("BITCOIND_RS_BIN") {
        return PathBuf::from(path);
    }
    if let Ok(path) = env::current_exe()
        && let Some(parent) = path.parent()
    {
        let candidate = parent.join(if cfg!(windows) {
            "bitcoind-rs.exe"
        } else {
            "bitcoind-rs"
        });
        if candidate.is_file() {
            return candidate;
        }
    }
    PathBuf::from(if cfg!(windows) {
        "bitcoind-rs.exe"
    } else {
        "bitcoind-rs"
    })
}

#[cfg(test)]
mod tests {
    use super::{config_requests_ipc, daemon_arguments, has_electrum_argument};

    #[test]
    fn strips_core_wrapper_modes_and_node_subcommand() {
        assert_eq!(
            daemon_arguments(vec![
                "-m".to_owned(),
                "node".to_owned(),
                "-datadir=/tmp/data".to_owned(),
            ]),
            vec!["-datadir=/tmp/data"]
        );
        assert_eq!(
            daemon_arguments(vec![
                "-M".to_owned(),
                "node".to_owned(),
                "-version".to_owned()
            ]),
            vec!["-version"]
        );
        assert!(!config_requests_ipc(&[
            "-datadir=/tmp/does-not-exist".to_owned()
        ]));
        assert!(has_electrum_argument(&["--electrum=0".to_owned()]));
        assert!(has_electrum_argument(&[
            "--electrum".to_owned(),
            "0".to_owned()
        ]));
    }
}
