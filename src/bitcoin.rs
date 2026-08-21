//! Core-compatible launcher for the wallet-free command suite.
//!
//! The Rust implementation uses one native daemon for Core's monolithic and
//! multiprocess node modes because IPC is hosted directly by that process.
//! Wallet and GUI commands are intentionally absent from this wallet-free
//! build; RPC, transaction, utility, and chainstate tools remain available.

use std::env;
use std::path::PathBuf;
use std::process::{Command, ExitCode};

const VERSION: &str = "31.1.0";
const HELP_USAGE: &str = r#"Usage: bitcoin [OPTIONS] COMMAND...

Options:
  -m, --multiprocess     Run the IPC-capable node mode.
  -M, --monolithic       Run the monolithic node mode. (Default behavior)
  -v, --version          Show version information
  -h, --help             Show full help message
Commands:
  node [ARGS]       Start node, equivalent to running 'bitcoind-rs [ARGS]'.
  rpc [ARGS]        Call RPC method, equivalent to running 'bitcoin-cli -named [ARGS]'.
  tx [ARGS]         Manipulate hex-encoded transactions, equivalent to running 'bitcoin-tx [ARGS]'.
  util [ARGS]       Run offline Bitcoin utilities, equivalent to running 'bitcoin-util [ARGS]'.
  chainstate [ARGS] Run the chainstate utility, equivalent to running 'bitcoin-chainstate [ARGS]'.
  help              Show full help message.
"#;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct WrapperCommandLine {
    use_multiprocess: Option<bool>,
    show_version: bool,
    show_help: bool,
    command: Option<String>,
    arguments: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Invocation {
    executable: &'static str,
    arguments: Vec<String>,
}

fn main() -> ExitCode {
    let command_line = match parse_command_line(env::args().skip(1)) {
        Ok(command_line) => command_line,
        Err(error) => return wrapper_error(&error),
    };
    if command_line.show_version {
        println!("Bitcoin Core version {VERSION}");
        return ExitCode::SUCCESS;
    }
    if command_line.show_help {
        print!("{HELP_USAGE}");
        return ExitCode::SUCCESS;
    }
    if command_line.command.is_none() {
        print!("{HELP_USAGE}\nRun 'bitcoin help' to see all wallet-free commands.\n");
        return ExitCode::from(1);
    }

    let invocation = match command_invocation(command_line) {
        Ok(invocation) => invocation,
        Err(error) => return wrapper_error(&error),
    };
    let executable = executable_path(invocation.executable);
    match Command::new(&executable)
        .args(invocation.arguments)
        .status()
    {
        Ok(status) => status
            .code()
            .and_then(|code| u8::try_from(code).ok())
            .map_or(ExitCode::from(1), ExitCode::from),
        Err(error) => {
            eprintln!("Error: failed to launch {}: {error}", executable.display());
            ExitCode::from(1)
        }
    }
}

fn wrapper_error(error: &str) -> ExitCode {
    eprintln!("Error: {error}\nTry 'bitcoin --help' for more information.");
    ExitCode::from(1)
}

fn parse_command_line(
    arguments: impl IntoIterator<Item = String>,
) -> Result<WrapperCommandLine, String> {
    let mut command_line = WrapperCommandLine::default();
    for argument in arguments {
        if command_line.command.is_some() {
            command_line.arguments.push(argument);
            continue;
        }
        match argument.as_str() {
            "-m" | "--multiprocess" => command_line.use_multiprocess = Some(true),
            "-M" | "--monolithic" => command_line.use_multiprocess = Some(false),
            "-v" | "--version" => command_line.show_version = true,
            "-h" | "--help" | "help" => command_line.show_help = true,
            value if value.starts_with('-') => {
                return Err(format!("Unknown option: {value}"));
            }
            "" => {}
            value => command_line.command = Some(value.to_owned()),
        }
    }
    Ok(command_line)
}

fn command_invocation(command_line: WrapperCommandLine) -> Result<Invocation, String> {
    match command_line.command.as_deref() {
        Some("node") => node_invocation(command_line),
        Some("rpc") => {
            let mut arguments = vec!["-named".to_owned()];
            arguments.extend(command_line.arguments);
            Ok(Invocation {
                executable: "bitcoin-cli",
                arguments,
            })
        }
        Some("tx") => Ok(Invocation {
            executable: "bitcoin-tx",
            arguments: command_line.arguments,
        }),
        Some("util") => Ok(Invocation {
            executable: "bitcoin-util",
            arguments: command_line.arguments,
        }),
        Some("chainstate") => Ok(Invocation {
            executable: "bitcoin-chainstate",
            arguments: command_line.arguments,
        }),
        Some(command) => Err(format!("Unrecognized command: '{command}'")),
        None => Err("No command specified".to_owned()),
    }
}

fn node_invocation(command_line: WrapperCommandLine) -> Result<Invocation, String> {
    let mut arguments = command_line.arguments;
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
    let ipc_requested = ipc_argument || ipc_configured;
    if command_line.use_multiprocess == Some(false) && ipc_requested {
        let invalid = arguments
            .iter()
            .find(|argument| argument.starts_with("-ipcbind") || argument.starts_with("--ipcbind"))
            .map(String::as_str)
            .unwrap_or("-ipcbind");
        return Err(format!(
            "Error parsing command line arguments: Invalid parameter {invalid}"
        ));
    }

    // The single Rust daemon hosts both node modes. For an IPC launch, do not
    // implicitly claim the project-specific Electrum port unless requested.
    if ipc_requested && !has_electrum_argument(&arguments) && !config_requests_electrum(&arguments)
    {
        arguments.push("--electrum=0".to_owned());
    }
    Ok(Invocation {
        executable: "bitcoind-rs",
        arguments,
    })
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

fn executable_path(executable: &str) -> PathBuf {
    if executable == "bitcoind-rs"
        && let Some(path) = env::var_os("BITCOIND_RS_BIN")
    {
        return PathBuf::from(path);
    }
    let filename = if cfg!(windows) {
        format!("{executable}.exe")
    } else {
        executable.to_owned()
    };
    if let Ok(path) = env::current_exe()
        && let Some(parent) = path.parent()
    {
        let candidate = parent.join(&filename);
        if candidate.is_file() {
            return candidate;
        }
    }
    PathBuf::from(filename)
}

#[cfg(test)]
mod tests {
    use super::{
        Invocation, command_invocation, config_requests_ipc, has_electrum_argument,
        parse_command_line,
    };

    #[test]
    fn parses_core_wrapper_modes_before_the_subcommand() {
        assert_eq!(
            parse_command_line(vec![
                "-m".to_owned(),
                "node".to_owned(),
                "-datadir=/tmp/data".to_owned(),
            ])
            .unwrap()
            .use_multiprocess,
            Some(true)
        );
        assert_eq!(
            parse_command_line(vec![
                "-M".to_owned(),
                "node".to_owned(),
                "-version".to_owned()
            ])
            .unwrap()
            .arguments,
            vec!["-version"]
        );
        assert!(parse_command_line(vec!["--unknown".to_owned()]).is_err());
    }

    #[test]
    fn dispatches_the_wallet_free_core_command_suite() {
        let invocation = |arguments: &[&str]| {
            command_invocation(
                parse_command_line(arguments.iter().map(|value| (*value).to_owned())).unwrap(),
            )
            .unwrap()
        };
        assert_eq!(
            invocation(&["rpc", "getblockhash", "height=0"]),
            Invocation {
                executable: "bitcoin-cli",
                arguments: vec![
                    "-named".to_owned(),
                    "getblockhash".to_owned(),
                    "height=0".to_owned(),
                ],
            }
        );
        assert_eq!(invocation(&["tx", "-create"]).executable, "bitcoin-tx");
        assert_eq!(invocation(&["util", "grind"]).executable, "bitcoin-util");
        assert_eq!(
            invocation(&["chainstate", "-help"]).executable,
            "bitcoin-chainstate"
        );
        assert!(command_invocation(parse_command_line(["wallet".to_owned()]).unwrap()).is_err());
    }

    #[test]
    fn ipc_node_launches_disable_only_the_implicit_electrum_listener() {
        let invocation = command_invocation(
            parse_command_line([
                "node".to_owned(),
                "--ipcbind=unix".to_owned(),
                "--datadir=/tmp/data".to_owned(),
            ])
            .unwrap(),
        )
        .unwrap();
        assert_eq!(invocation.executable, "bitcoind-rs");
        assert!(invocation.arguments.contains(&"--electrum=0".to_owned()));

        let error = command_invocation(
            parse_command_line([
                "-M".to_owned(),
                "node".to_owned(),
                "--ipcbind=unix".to_owned(),
            ])
            .unwrap(),
        )
        .unwrap_err();
        assert!(error.contains("Invalid parameter --ipcbind=unix"));

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
