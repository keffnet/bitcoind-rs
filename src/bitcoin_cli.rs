//! A small, wallet-free bitcoin-cli compatible JSON-RPC client.
//!
//! The daemon deliberately owns its native storage format, but its command
//! line client speaks the same HTTP JSON-RPC interface as Core. Keeping the
//! client here avoids making users depend on curl or on a test-only adapter.

use std::collections::HashMap;
use std::env;
use std::fs;
use std::io::{self, IsTerminal, Read, Write};
use std::net::{IpAddr, SocketAddr, TcpStream, ToSocketAddrs};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use base64::Engine;
use serde_json::{Map, Value, json};

const CLIENT_NAME: &str = "bitcoind-rs";
const CLIENT_VERSION: &str = "0.1.0";
const DEFAULT_RPC_CONNECT: &str = "127.0.0.1";
const DEFAULT_RPC_CLIENT_TIMEOUT: u64 = 900;
const DEFAULT_RPC_WAIT_TIMEOUT: u64 = 0;

#[derive(Debug)]
enum Failure {
    Local(String),
    Connection(String),
    Authentication(String),
    Rpc { code: i64, message: String },
}

impl Failure {
    fn local(message: impl Into<String>) -> Self {
        Self::Local(message.into())
    }

    fn connection(message: impl Into<String>) -> Self {
        Self::Connection(message.into())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Network {
    Main,
    Testnet,
    Testnet4,
    Signet,
    Regtest,
}

impl Network {
    fn directory(self) -> &'static str {
        match self {
            Self::Main => "",
            Self::Testnet => "testnet3",
            Self::Testnet4 => "testnet4",
            Self::Signet => "signet",
            Self::Regtest => "regtest",
        }
    }

    fn rpc_port(self) -> u16 {
        match self {
            Self::Main => 8332,
            Self::Testnet => 18332,
            Self::Testnet4 => 48332,
            Self::Signet => 38332,
            Self::Regtest => 18443,
        }
    }

    fn display_suffix(self) -> &'static str {
        match self {
            Self::Main => "",
            Self::Testnet => " testnet",
            Self::Testnet4 => " testnet4",
            Self::Signet => " signet",
            Self::Regtest => " regtest",
        }
    }
}

#[derive(Debug, Default)]
struct Options {
    datadir: Option<PathBuf>,
    conf: Option<PathBuf>,
    network: Option<Network>,
    rpc_connect: Option<String>,
    rpc_port: Option<String>,
    rpc_cookie_file: Option<PathBuf>,
    rpc_user: Option<String>,
    rpc_password: Option<String>,
    no_rpc_cookie_file: bool,
    rpc_wallet: Option<String>,
    rpc_wait: bool,
    rpc_wait_timeout: Option<String>,
    rpc_client_timeout: Option<String>,
    stdin: bool,
    stdin_rpc_pass: bool,
    stdin_wallet_passphrase: bool,
    named: bool,
    color: String,
    get_info: bool,
    net_info: bool,
    addr_info: bool,
    generate: bool,
    version: bool,
    help: bool,
    positional: Vec<String>,
}

#[derive(Debug)]
struct ConfigFile {
    values: HashMap<String, String>,
    section_values: HashMap<String, HashMap<String, String>>,
}

impl ConfigFile {
    fn read(path: &Path) -> Self {
        let Ok(contents) = fs::read_to_string(path) else {
            return Self {
                values: HashMap::new(),
                section_values: HashMap::new(),
            };
        };
        let mut values = HashMap::new();
        let mut section_values: HashMap<String, HashMap<String, String>> = HashMap::new();
        let mut section = String::new();
        for line in contents.lines() {
            let line = line.split('#').next().unwrap_or_default().trim();
            if line.is_empty() {
                continue;
            }
            if let Some(name) = line
                .strip_prefix('[')
                .and_then(|line| line.strip_suffix(']'))
            {
                section = name.trim().to_ascii_lowercase();
                continue;
            }
            let Some((key, value)) = line.split_once('=') else {
                continue;
            };
            let key = key.trim().trim_start_matches('-').to_ascii_lowercase();
            let value = value.trim().to_owned();
            if section.is_empty() {
                values.insert(key, value);
            } else {
                section_values
                    .entry(section.clone())
                    .or_default()
                    .insert(key, value);
            }
        }
        Self {
            values,
            section_values,
        }
    }

    fn value(&self, network: Network, key: &str) -> Option<&str> {
        let key = key.trim_start_matches('-').to_ascii_lowercase();
        let section = match network {
            Network::Main => "main",
            Network::Testnet => "testnet",
            Network::Testnet4 => "testnet4",
            Network::Signet => "signet",
            Network::Regtest => "regtest",
        };
        self.section_values
            .get(section)
            .and_then(|values| values.get(&key))
            .map(String::as_str)
            .or_else(|| self.values.get(&key).map(String::as_str))
    }

    fn enabled(&self, key: &str) -> bool {
        self.values
            .get(key)
            .is_some_and(|value| parse_bool(value).unwrap_or(false))
    }
}

struct RpcClient {
    host: String,
    port: u16,
    display_host: String,
    timeout: Duration,
    wait: bool,
    wait_timeout: Option<Duration>,
    auth: String,
    wallet: Option<String>,
}

fn main() {
    match run() {
        Ok(Some(output)) => {
            print!("{output}");
            if !output.ends_with('\n') {
                println!();
            }
        }
        Ok(None) => {}
        Err(Failure::Rpc { code, message }) => {
            eprintln!("error code: {code}\nerror message:\n{message}");
            std::process::exit(1);
        }
        Err(Failure::Authentication(message)) => {
            eprintln!("{message}");
            std::process::exit(1);
        }
        Err(Failure::Connection(message) | Failure::Local(message)) => {
            eprintln!("error: {message}");
            std::process::exit(1);
        }
    }
}

fn run() -> Result<Option<String>, Failure> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    let mut options = parse_options(&arguments)?;
    if options.help || (arguments.is_empty() && !options.version) {
        return Ok(Some(help_text()));
    }
    if options.version {
        return Ok(Some(format!(
            "{CLIENT_NAME} RPC client version {CLIENT_VERSION}\n"
        )));
    }

    let datadir = options
        .datadir
        .clone()
        .unwrap_or_else(|| PathBuf::from(".bitcoin"));
    let config_path = options
        .conf
        .clone()
        .map(|path| {
            if path.is_absolute() {
                path
            } else {
                datadir.join(path)
            }
        })
        .unwrap_or_else(|| datadir.join("bitcoin.conf"));
    let config = ConfigFile::read(&config_path);
    if options.network.is_none() {
        options.network = infer_network(&config, &datadir);
    }
    let network = options.network.unwrap_or(Network::Main);

    if options.get_info && options.net_info {
        return Err(Failure::local(
            "Only one of -getinfo, -netinfo may be specified",
        ));
    }
    if options.get_info && !options.positional.is_empty() {
        return Err(Failure::local("-getinfo takes no arguments"));
    }
    if options.color != "always" && options.color != "auto" && options.color != "never" {
        return Err(Failure::local(
            "Invalid value for -color option. Valid values: always, auto, never.",
        ));
    }

    let (host, connect_port) = parse_rpc_connect(
        options
            .rpc_connect
            .as_deref()
            .unwrap_or(DEFAULT_RPC_CONNECT),
    )?;
    let port = choose_rpc_port(&options, &config, network, connect_port)?;
    let mut stdin_lines =
        if options.stdin || options.stdin_rpc_pass || options.stdin_wallet_passphrase {
            let mut input = String::new();
            io::stdin().read_to_string(&mut input).map_err(|error| {
                Failure::local(format!("could not read standard input: {error}"))
            })?;
            input.lines().map(str::to_owned).collect::<Vec<_>>()
        } else {
            Vec::new()
        };
    if options.stdin_rpc_pass {
        let Some(password) = stdin_lines.first().cloned() else {
            return Err(Failure::local(
                "-stdinrpcpass specified but failed to read from standard input",
            ));
        };
        options.rpc_password = Some(password);
        stdin_lines.remove(0);
    }
    if options.stdin_wallet_passphrase {
        return Err(Failure::local(
            "-stdinwalletpassphrase is not supported by this wallet-free build",
        ));
    }
    if options.stdin {
        options.positional.extend(stdin_lines);
    }
    let auth = match read_auth(&options, &config, &config_path, &datadir, network) {
        Ok(auth) => auth,
        // Core reports the connection failure when -rpcwait is used against
        // a stopped node, even though its cookie has already been removed.
        Err(Failure::Authentication(_)) if options.rpc_wait => String::new(),
        Err(error) => return Err(error),
    };
    let timeout = parse_duration_seconds(
        options.rpc_client_timeout.as_deref().unwrap_or("900"),
        "-rpcclienttimeout",
        DEFAULT_RPC_CLIENT_TIMEOUT,
    )?;
    let wait_timeout = parse_wait_timeout(
        options.rpc_wait_timeout.as_deref(),
        DEFAULT_RPC_WAIT_TIMEOUT,
    )?;
    let client = RpcClient {
        display_host: host.clone(),
        host,
        port,
        timeout,
        wait: options.rpc_wait,
        wait_timeout,
        auth,
        wallet: options.rpc_wallet.clone(),
    };

    if options.net_info {
        return Ok(Some(net_info(&client, network, &options.positional)?));
    }
    if options.addr_info {
        let result = client.call("getaddrmaninfo", &Value::Array(Vec::new()))?;
        return Ok(Some(render_result(&result)));
    }
    if options.get_info {
        return Ok(Some(get_info(&client, &options.color)?));
    }
    if options.generate {
        return Err(Failure::Rpc {
            code: -32601,
            message: "generate\n\nhas been replaced by the -generate cli option. Refer to -help for more information.\n"
                .to_owned(),
        });
    }

    let Some(method) = options.positional.first().cloned() else {
        return Err(Failure::local("too few parameters (need at least command)"));
    };
    let raw_params = options.positional[1..].to_vec();
    if method == "help" && raw_params.is_empty() {
        return Ok(Some(help_text()));
    }
    let params = build_params(&method, &raw_params, options.named)?;
    let result = client.call(&method, &params)?;
    Ok(Some(render_result(&result)))
}

fn parse_options(arguments: &[String]) -> Result<Options, Failure> {
    let mut options = Options {
        named: false,
        color: "auto".to_owned(),
        ..Options::default()
    };
    let mut index = 0;
    while index < arguments.len() {
        let argument = &arguments[index];
        if argument == "--" {
            options
                .positional
                .extend(arguments[index + 1..].iter().cloned());
            break;
        }
        if !argument.starts_with('-') || argument == "-" {
            options.positional.push(argument.clone());
            index += 1;
            continue;
        }
        let (raw_name, inline_value) = argument
            .split_once('=')
            .map_or((argument.as_str(), None), |(name, value)| {
                (name, Some(value))
            });
        let name = raw_name.trim_start_matches('-');
        let value = |index: &mut usize| -> Result<String, Failure> {
            if let Some(value) = inline_value {
                return Ok(value.to_owned());
            }
            *index += 1;
            arguments
                .get(*index)
                .cloned()
                .ok_or_else(|| Failure::local(format!("option '-{name}' requires an argument")))
        };
        match name {
            "datadir" => options.datadir = Some(PathBuf::from(value(&mut index)?)),
            "conf" => options.conf = Some(PathBuf::from(value(&mut index)?)),
            "rpcconnect" => options.rpc_connect = Some(value(&mut index)?),
            "rpcport" => options.rpc_port = Some(value(&mut index)?),
            "rpccookiefile" => options.rpc_cookie_file = Some(PathBuf::from(value(&mut index)?)),
            "rpcuser" => options.rpc_user = Some(value(&mut index)?),
            "rpcpassword" => options.rpc_password = Some(value(&mut index)?),
            "rpcwallet" => options.rpc_wallet = Some(value(&mut index)?),
            "rpcclienttimeout" => options.rpc_client_timeout = Some(value(&mut index)?),
            "rpcwaittimeout" => options.rpc_wait_timeout = Some(value(&mut index)?),
            "color" => options.color = value(&mut index)?,
            "named" => options.named = inline_value.map(parse_bool).transpose()?.unwrap_or(true),
            "nonamed" => options.named = false,
            "rpcwait" => {
                options.rpc_wait = inline_value.map(parse_bool).transpose()?.unwrap_or(true)
            }
            "stdin" => options.stdin = inline_value.map(parse_bool).transpose()?.unwrap_or(true),
            "stdinrpcpass" => {
                options.stdin_rpc_pass = inline_value.map(parse_bool).transpose()?.unwrap_or(true)
            }
            "stdinwalletpassphrase" => {
                options.stdin_wallet_passphrase =
                    inline_value.map(parse_bool).transpose()?.unwrap_or(true)
            }
            "norpccookiefile" => options.no_rpc_cookie_file = true,
            "norpcwallet" => options.rpc_wallet = None,
            "getinfo" => {
                options.get_info = inline_value.map(parse_bool).transpose()?.unwrap_or(true)
            }
            "netinfo" => {
                options.net_info = inline_value.map(parse_bool).transpose()?.unwrap_or(true)
            }
            "addrinfo" => {
                options.addr_info = inline_value.map(parse_bool).transpose()?.unwrap_or(true)
            }
            "generate" => {
                options.generate = inline_value.map(parse_bool).transpose()?.unwrap_or(true)
            }
            "version" => {
                options.version = inline_value.map(parse_bool).transpose()?.unwrap_or(true)
            }
            "help" | "h" => options.help = true,
            "mainnet" => options.network = Some(Network::Main),
            "testnet" | "test" => options.network = Some(Network::Testnet),
            "testnet4" => options.network = Some(Network::Testnet4),
            "signet" => options.network = Some(Network::Signet),
            "regtest" => options.network = Some(Network::Regtest),
            // Chain and compatibility switches are accepted by Core's CLI
            // even though they do not alter the RPC request itself.
            _ if name.starts_with("rpc") || name.starts_with("no") => {}
            _ => {}
        }
        index += 1;
    }
    Ok(options)
}

fn parse_bool(value: &str) -> Result<bool, Failure> {
    match value.to_ascii_lowercase().as_str() {
        "1" | "true" | "yes" | "on" => Ok(true),
        "0" | "false" | "no" | "off" => Ok(false),
        _ => Err(Failure::local(format!("invalid boolean value '{value}'"))),
    }
}

fn infer_network(config: &ConfigFile, datadir: &Path) -> Option<Network> {
    if config.enabled("regtest") {
        return Some(Network::Regtest);
    }
    if config.enabled("testnet4") {
        return Some(Network::Testnet4);
    }
    if config.enabled("signet") {
        return Some(Network::Signet);
    }
    if config.enabled("testnet") || config.enabled("test") {
        return Some(Network::Testnet);
    }
    [
        Network::Regtest,
        Network::Testnet4,
        Network::Signet,
        Network::Testnet,
    ]
    .into_iter()
    .find(|network| datadir.join(network.directory()).join(".cookie").exists())
}

fn parse_rpc_connect(value: &str) -> Result<(String, Option<u16>), Failure> {
    if let Some(rest) = value.strip_prefix('[') {
        let Some(end) = rest.find(']') else {
            return Err(Failure::local(format!(
                "Invalid port provided in -rpcconnect: {value}"
            )));
        };
        let host = &rest[..end];
        let suffix = &rest[end + 1..];
        if suffix.is_empty() {
            return Ok((host.to_owned(), None));
        }
        let Some(raw_port) = suffix.strip_prefix(':') else {
            return Err(Failure::local(format!(
                "Invalid port provided in -rpcconnect: {value}"
            )));
        };
        return Ok((
            host.to_owned(),
            Some(parse_port(raw_port, "-rpcconnect", value)?),
        ));
    }
    if value.matches(':').count() == 1 {
        let (host, raw_port) = value.split_once(':').expect("one colon implies a split");
        return Ok((
            host.to_owned(),
            Some(parse_port(raw_port, "-rpcconnect", value)?),
        ));
    }
    Ok((value.to_owned(), None))
}

fn parse_port(value: &str, option: &str, original: &str) -> Result<u16, Failure> {
    let port = value.parse::<u16>().ok();
    if port.is_none_or(|port| port == 0) {
        return Err(Failure::local(format!(
            "Invalid port provided in {option}: {original}"
        )));
    }
    Ok(port.expect("port checked above"))
}

fn choose_rpc_port(
    options: &Options,
    config: &ConfigFile,
    network: Network,
    connect_port: Option<u16>,
) -> Result<u16, Failure> {
    if let Some(value) = options.rpc_port.as_deref() {
        return parse_port(value, "-rpcport", value);
    }
    if let Some(value) = config.value(network, "rpcport") {
        return parse_port(value, "-rpcport", value);
    }
    Ok(connect_port.unwrap_or_else(|| network.rpc_port()))
}

fn parse_duration_seconds(value: &str, option: &str, default: u64) -> Result<Duration, Failure> {
    let seconds = if value.is_empty() {
        default
    } else {
        value
            .parse::<u64>()
            .map_err(|_| Failure::local(format!("Invalid value for {option}: {value}")))?
    };
    Ok(Duration::from_secs(seconds))
}

fn parse_wait_timeout(value: Option<&str>, default: u64) -> Result<Option<Duration>, Failure> {
    let value = value.unwrap_or("0");
    let seconds = if value.is_empty() {
        default
    } else {
        value
            .parse::<u64>()
            .map_err(|_| Failure::local(format!("Invalid value for -rpcwaittimeout: {value}")))?
    };
    Ok((seconds != 0).then(|| Duration::from_secs(seconds)))
}

fn read_auth(
    options: &Options,
    config: &ConfigFile,
    config_path: &Path,
    datadir: &Path,
    network: Network,
) -> Result<String, Failure> {
    let username = options
        .rpc_user
        .as_deref()
        .or_else(|| config.value(network, "rpcuser"))
        .unwrap_or_default();
    let password = options
        .rpc_password
        .as_deref()
        .or_else(|| config.value(network, "rpcpassword"));
    if password.is_some_and(|password| !password.is_empty()) {
        return Ok(format!("{username}:{}", password.unwrap_or_default()));
    }
    if !options.no_rpc_cookie_file {
        let mut candidates = Vec::new();
        if let Some(path) = options.rpc_cookie_file.as_deref() {
            if path.is_absolute() {
                candidates.push(path.to_owned());
            } else {
                candidates.push(datadir.join(network.directory()).join(path));
                candidates.push(datadir.join(path));
            }
        } else {
            if !network.directory().is_empty() {
                candidates.push(datadir.join(network.directory()).join(".cookie"));
            }
            candidates.push(datadir.join(".cookie"));
        }
        for path in candidates {
            if let Ok(cookie) = fs::read_to_string(path) {
                return Ok(cookie.trim_end_matches(['\r', '\n']).to_owned());
            }
        }
    }
    Err(Failure::Authentication(format!(
        "Could not locate RPC credentials. No authentication cookie could be found, and RPC password is not set.  See -rpcpassword and -stdinrpcpass.  Configuration file: ({})",
        config_path.display()
    )))
}

fn build_params(method: &str, raw: &[String], named: bool) -> Result<Value, Failure> {
    if !named {
        let values = raw
            .iter()
            .enumerate()
            .map(|(index, value)| cli_value(method, Some(index), None, value))
            .collect::<Result<Vec<_>, _>>()?;
        return Ok(Value::Array(values));
    }
    let mut positional = Vec::new();
    let mut named_values = Map::new();
    let mut has_named_args = false;
    for value in raw {
        let Some((name, raw_value)) = split_named_argument(value) else {
            let index = positional.len();
            positional.push(cli_value(method, Some(index), None, value)?);
            continue;
        };
        if !cli_named_parameter(method, name)
            && cli_string_parameter(method, Some(positional.len()), None)
        {
            let index = positional.len();
            positional.push(cli_value(method, Some(index), None, value)?);
            continue;
        }
        has_named_args = true;
        if name == "args" && !positional.is_empty() {
            return Err(Failure::Rpc {
                code: -8,
                message: "Parameter args specified multiple times".to_owned(),
            });
        }
        named_values.insert(
            name.to_owned(),
            cli_value(method, None, Some(name), raw_value)?,
        );
    }
    if !has_named_args {
        return Ok(Value::Array(positional));
    }
    if named_values.contains_key("args") && !positional.is_empty() {
        return Err(Failure::Rpc {
            code: -8,
            message: "Parameter args specified multiple times".to_owned(),
        });
    }
    if !positional.is_empty() {
        let mut params = Map::new();
        params.insert("args".to_owned(), Value::Array(positional));
        params.extend(named_values);
        Ok(Value::Object(params))
    } else {
        Ok(Value::Object(named_values))
    }
}

fn split_named_argument(value: &str) -> Option<(&str, &str)> {
    let (name, value) = value.split_once('=')?;
    let mut characters = name.chars();
    let first = characters.next()?;
    if !(first.is_ascii_alphabetic() || first == '_')
        || !characters.all(|character| character.is_ascii_alphanumeric() || character == '_')
    {
        return None;
    }
    Some((name, value))
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum CliParamFormat {
    Json,
    JsonOrString,
    String,
}

fn cli_value(
    method: &str,
    position: Option<usize>,
    name: Option<&str>,
    value: &str,
) -> Result<Value, Failure> {
    match cli_param_format(method, position, name) {
        Some(CliParamFormat::String) | None => Ok(Value::String(value.to_owned())),
        Some(CliParamFormat::JsonOrString) => {
            Ok(serde_json::from_str(value).unwrap_or_else(|_| Value::String(value.to_owned())))
        }
        Some(CliParamFormat::Json) => serde_json::from_str(value)
            .map_err(|_| Failure::local(format!("Error parsing JSON: {value}"))),
    }
}

fn parameter_matches(
    position: Option<usize>,
    name: Option<&str>,
    index: usize,
    names: &[&str],
) -> bool {
    position == Some(index) || name.is_some_and(|name| names.contains(&name))
}

/// Core's `vRPCConvertParams` table for the wallet-free RPC surface. An
/// argument absent from this table is deliberately passed as a raw string;
/// this is how Core's CLI distinguishes natural string arguments from JSON
/// values that need conversion.
fn cli_param_format(
    method: &str,
    position: Option<usize>,
    name: Option<&str>,
) -> Option<CliParamFormat> {
    if name == Some("args") {
        return Some(CliParamFormat::Json);
    }
    if method == "echo" {
        return Some(CliParamFormat::String);
    }
    if method == "echojson"
        && (position.is_some_and(|position| position < 10)
            || name
                .and_then(|name| name.strip_prefix("arg"))
                .and_then(|index| index.parse::<usize>().ok())
                .is_some_and(|index| index < 10))
    {
        return Some(CliParamFormat::Json);
    }

    match method {
        "setmocktime" => {
            parameter_matches(position, name, 0, &["timestamp"]).then_some(CliParamFormat::Json)
        }
        "mockscheduler" => {
            parameter_matches(position, name, 0, &["delta_time"]).then_some(CliParamFormat::Json)
        }
        "utxoupdatepsbt" => {
            if parameter_matches(position, name, 0, &["psbt"]) {
                Some(CliParamFormat::String)
            } else if parameter_matches(position, name, 1, &["descriptors"]) {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "generatetoaddress" => {
            if parameter_matches(position, name, 0, &["nblocks"])
                || parameter_matches(position, name, 2, &["maxtries"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "generatetodescriptor" => {
            if parameter_matches(position, name, 0, &["num_blocks"])
                || parameter_matches(position, name, 2, &["maxtries"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "generateblock" => {
            if parameter_matches(position, name, 1, &["transactions"])
                || parameter_matches(position, name, 2, &["submit"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "getnetworkhashps" => {
            if parameter_matches(position, name, 0, &["nblocks"])
                || parameter_matches(position, name, 1, &["height"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "getblockfrompeer" => {
            parameter_matches(position, name, 1, &["peer_id"]).then_some(CliParamFormat::Json)
        }
        "getblockhash" => {
            parameter_matches(position, name, 0, &["height"]).then_some(CliParamFormat::Json)
        }
        "waitforblockheight" => {
            if parameter_matches(position, name, 0, &["height"])
                || parameter_matches(position, name, 1, &["timeout"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "waitforblock" => {
            parameter_matches(position, name, 1, &["timeout"]).then_some(CliParamFormat::Json)
        }
        "waitfornewblock" => {
            parameter_matches(position, name, 0, &["timeout"]).then_some(CliParamFormat::Json)
        }
        "getblocktemplate" => parameter_matches(position, name, 0, &["template_request"])
            .then_some(CliParamFormat::Json),
        "deriveaddresses" => {
            parameter_matches(position, name, 1, &["range"]).then_some(CliParamFormat::Json)
        }
        "scanblocks" => {
            if parameter_matches(position, name, 1, &["scanobjects"])
                || parameter_matches(position, name, 2, &["start_height"])
                || parameter_matches(position, name, 3, &["stop_height"])
                || parameter_matches(position, name, 5, &["options", "filter_false_positives"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "getdescriptoractivity" => {
            if parameter_matches(position, name, 0, &["blockhashes"])
                || parameter_matches(position, name, 1, &["scanobjects"])
                || parameter_matches(position, name, 2, &["include_mempool"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "scantxoutset" => {
            parameter_matches(position, name, 1, &["scanobjects"]).then_some(CliParamFormat::Json)
        }
        "createmultisig" => {
            if parameter_matches(position, name, 0, &["nrequired"])
                || parameter_matches(position, name, 1, &["keys"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "getblock" | "getrawtransaction" => {
            parameter_matches(position, name, 1, &["verbosity", "verbose"])
                .then_some(CliParamFormat::Json)
        }
        "getblockheader" => {
            parameter_matches(position, name, 1, &["verbose"]).then_some(CliParamFormat::Json)
        }
        "getchaintxstats" => {
            parameter_matches(position, name, 0, &["nblocks"]).then_some(CliParamFormat::Json)
        }
        "createrawtransaction" | "createpsbt" => {
            if position.is_some_and(|position| position < 5)
                || name.is_some_and(|name| {
                    matches!(
                        name,
                        "inputs" | "outputs" | "locktime" | "replaceable" | "version"
                    )
                })
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "decoderawtransaction" => {
            parameter_matches(position, name, 1, &["iswitness"]).then_some(CliParamFormat::Json)
        }
        "signrawtransactionwithkey" => {
            if parameter_matches(position, name, 1, &["privkeys"])
                || parameter_matches(position, name, 2, &["prevtxs"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "sendrawtransaction" => {
            if parameter_matches(position, name, 1, &["maxfeerate"])
                || parameter_matches(position, name, 2, &["maxburnamount"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "testmempoolaccept" => {
            if parameter_matches(position, name, 0, &["rawtxs"])
                || parameter_matches(position, name, 1, &["maxfeerate"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "submitpackage" => {
            if parameter_matches(position, name, 0, &["package"])
                || parameter_matches(position, name, 1, &["maxfeerate"])
                || parameter_matches(position, name, 2, &["maxburnamount"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "combinerawtransaction" | "combinepsbt" | "joinpsbts" => {
            parameter_matches(position, name, 0, &["txs"]).then_some(CliParamFormat::Json)
        }
        "descriptorprocesspsbt" => {
            if parameter_matches(position, name, 0, &["psbt"])
                || parameter_matches(position, name, 2, &["sighashtype"])
            {
                Some(CliParamFormat::String)
            } else if parameter_matches(position, name, 1, &["descriptors"])
                || parameter_matches(position, name, 3, &["bip32derivs"])
                || parameter_matches(position, name, 4, &["finalize"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "finalizepsbt" => {
            if parameter_matches(position, name, 0, &["psbt"]) {
                Some(CliParamFormat::String)
            } else if parameter_matches(position, name, 1, &["extract"]) {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "converttopsbt" => {
            if parameter_matches(position, name, 1, &["permitsigdata"])
                || parameter_matches(position, name, 2, &["iswitness"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "gettxout" => {
            if parameter_matches(position, name, 1, &["n"])
                || parameter_matches(position, name, 2, &["include_mempool"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "gettxoutproof" => {
            parameter_matches(position, name, 0, &["txids"]).then_some(CliParamFormat::Json)
        }
        "gettxoutsetinfo" => {
            if parameter_matches(position, name, 1, &["hash_or_height"]) {
                Some(CliParamFormat::JsonOrString)
            } else if parameter_matches(position, name, 2, &["use_index"]) {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "dumptxoutset" => {
            if parameter_matches(position, name, 0, &["path"])
                || parameter_matches(position, name, 1, &["type"])
            {
                Some(CliParamFormat::String)
            } else if parameter_matches(position, name, 2, &["rollback"])
                && name == Some("rollback")
            {
                Some(CliParamFormat::JsonOrString)
            } else if parameter_matches(position, name, 2, &["options"]) || position == Some(2) {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "verifychain" => {
            if parameter_matches(position, name, 0, &["checklevel"])
                || parameter_matches(position, name, 1, &["nblocks"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "getblockstats" => {
            if parameter_matches(position, name, 0, &["hash_or_height"]) {
                Some(CliParamFormat::JsonOrString)
            } else if parameter_matches(position, name, 1, &["stats"]) {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "pruneblockchain" => {
            parameter_matches(position, name, 0, &["height"]).then_some(CliParamFormat::Json)
        }
        "getrawmempool" => {
            if parameter_matches(position, name, 0, &["verbose"])
                || parameter_matches(position, name, 1, &["mempool_sequence"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "getorphantxs" => {
            parameter_matches(position, name, 0, &["verbosity"]).then_some(CliParamFormat::Json)
        }
        "estimatesmartfee" => {
            parameter_matches(position, name, 0, &["conf_target"]).then_some(CliParamFormat::Json)
        }
        "estimaterawfee" => {
            if parameter_matches(position, name, 0, &["conf_target"])
                || parameter_matches(position, name, 1, &["threshold"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "prioritisetransaction" => {
            if parameter_matches(position, name, 1, &["dummy"])
                || parameter_matches(position, name, 2, &["fee_delta"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "setban" => {
            if parameter_matches(position, name, 2, &["bantime"])
                || parameter_matches(position, name, 3, &["absolute"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "setnetworkactive" => {
            parameter_matches(position, name, 0, &["state"]).then_some(CliParamFormat::Json)
        }
        "getmempoolancestors" | "getmempooldescendants" => {
            parameter_matches(position, name, 1, &["verbose"]).then_some(CliParamFormat::Json)
        }
        "gettxspendingprevout" => {
            if parameter_matches(position, name, 0, &["outputs"])
                || parameter_matches(
                    position,
                    name,
                    1,
                    &["options", "mempool_only", "return_spending_tx"],
                )
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "logging" => {
            if parameter_matches(position, name, 0, &["include"])
                || parameter_matches(position, name, 1, &["exclude"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "getnodeaddresses" => {
            parameter_matches(position, name, 0, &["count"]).then_some(CliParamFormat::Json)
        }
        "addpeeraddress" => {
            if parameter_matches(position, name, 1, &["port"])
                || parameter_matches(position, name, 2, &["tried"])
            {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        "sendmsgtopeer" => {
            parameter_matches(position, name, 0, &["peer_id"]).then_some(CliParamFormat::Json)
        }
        "stop" => parameter_matches(position, name, 0, &["wait"]).then_some(CliParamFormat::Json),
        "addnode" => {
            parameter_matches(position, name, 2, &["v2transport"]).then_some(CliParamFormat::Json)
        }
        "addconnection" => {
            parameter_matches(position, name, 2, &["v2transport"]).then_some(CliParamFormat::Json)
        }
        "decodepsbt" | "analyzepsbt" => {
            parameter_matches(position, name, 0, &["psbt"]).then_some(CliParamFormat::String)
        }
        "verifymessage" => {
            if parameter_matches(position, name, 1, &["signature"])
                || parameter_matches(position, name, 2, &["message"])
            {
                Some(CliParamFormat::String)
            } else {
                None
            }
        }
        "echoipc" => {
            parameter_matches(position, name, 0, &["arg"]).then_some(CliParamFormat::String)
        }
        "loadtxoutset" => {
            parameter_matches(position, name, 0, &["path"]).then_some(CliParamFormat::String)
        }
        "signmessagewithprivkey" => {
            parameter_matches(position, name, 1, &["message"]).then_some(CliParamFormat::String)
        }
        "importmempool" => {
            if parameter_matches(position, name, 0, &["filepath"]) {
                Some(CliParamFormat::String)
            } else if parameter_matches(
                position,
                name,
                1,
                &[
                    "options",
                    "apply_fee_delta_priority",
                    "use_current_time",
                    "apply_unbroadcast_set",
                ],
            ) {
                Some(CliParamFormat::Json)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Return whether Core's bitcoin-cli treats a parameter as a literal string.
fn cli_string_parameter(method: &str, position: Option<usize>, name: Option<&str>) -> bool {
    cli_param_format(method, position, name) == Some(CliParamFormat::String)
}

/// Names recognized by the affected RPCs when `-named` is used.  This lets
/// the Core-compatible `name=value` heuristic preserve a literal string such
/// as `message=part=one` while still accepting a real named argument.
fn cli_named_parameter(method: &str, name: &str) -> bool {
    match method {
        "echo" | "echojson" => {
            name == "args"
                || name
                    .strip_prefix("arg")
                    .and_then(|index| index.parse::<usize>().ok())
                    .is_some_and(|index| index < 10)
        }
        "utxoupdatepsbt" => matches!(name, "psbt" | "descriptors"),
        "descriptorprocesspsbt" => matches!(
            name,
            "psbt" | "descriptors" | "sighashtype" | "bip32derivs" | "finalize"
        ),
        "finalizepsbt" => matches!(name, "psbt" | "extract"),
        "decodepsbt" | "analyzepsbt" => name == "psbt",
        "dumptxoutset" => matches!(name, "path" | "type" | "options" | "rollback"),
        "importmempool" => matches!(
            name,
            "filepath"
                | "options"
                | "apply_fee_delta_priority"
                | "use_current_time"
                | "apply_unbroadcast_set"
        ),
        "loadtxoutset" => name == "path",
        "verifymessage" => matches!(name, "address" | "signature" | "message"),
        "signmessagewithprivkey" => matches!(name, "privkey" | "message"),
        "echoipc" => name == "arg",
        _ => false,
    }
}

impl RpcClient {
    fn call(&self, method: &str, params: &Value) -> Result<Value, Failure> {
        let deadline = self.wait_timeout.map(|timeout| {
            Instant::now()
                .checked_add(timeout)
                .unwrap_or_else(Instant::now)
        });
        loop {
            match self.call_once(method, params) {
                Ok(result) => return Ok(result),
                Err(error @ Failure::Connection(_)) if self.wait => {
                    if deadline.is_none_or(|deadline| Instant::now() < deadline) {
                        sleep_before_retry(deadline);
                        continue;
                    }
                    return Err(error);
                }
                Err(error @ Failure::Rpc { code: -28, .. }) if self.wait => {
                    if deadline.is_none_or(|deadline| Instant::now() < deadline) {
                        sleep_before_retry(deadline);
                        continue;
                    }
                    return Err(error);
                }
                Err(error) => return Err(error),
            }
        }
    }

    fn call_once(&self, method: &str, params: &Value) -> Result<Value, Failure> {
        let address = resolve_address(&self.host, self.port).map_err(|error| {
            Failure::connection(format!(
                "Could not connect to the server {}:{} ({error})",
                self.display_host, self.port
            ))
        })?;
        let connect_timeout = if self.timeout.is_zero() {
            Duration::from_secs(30)
        } else {
            self.timeout.min(Duration::from_secs(30))
        };
        let mut stream = TcpStream::connect_timeout(&address, connect_timeout).map_err(|_| {
            Failure::connection(format!(
                "Could not connect to the server {}:{}",
                self.display_host, self.port
            ))
        })?;
        if !self.timeout.is_zero() {
            stream
                .set_read_timeout(Some(self.timeout))
                .map_err(|error| Failure::connection(error.to_string()))?;
            stream
                .set_write_timeout(Some(self.timeout))
                .map_err(|error| Failure::connection(error.to_string()))?;
        }
        let request = json!({
            "jsonrpc": "1.0",
            "id": 1,
            "method": method,
            "params": params,
        });
        let body = serde_json::to_vec(&request)
            .map_err(|error| Failure::local(format!("could not encode RPC request: {error}")))?;
        let path = self.wallet.as_deref().map_or_else(
            || "/".to_owned(),
            |wallet| format!("/wallet/{}", percent_encode(wallet)),
        );
        let authorization = base64::engine::general_purpose::STANDARD.encode(self.auth.as_bytes());
        let header = format!(
            "POST {path} HTTP/1.1\r\nHost: {}\r\nConnection: close\r\nContent-Type: application/json\r\nAuthorization: Basic {authorization}\r\nContent-Length: {}\r\n\r\n",
            host_header(&self.host),
            body.len()
        );
        stream
            .write_all(header.as_bytes())
            .and_then(|_| stream.write_all(&body))
            .map_err(|error| {
                Failure::connection(format!("Could not connect to the server: {error}"))
            })?;
        let mut response = Vec::new();
        stream
            .read_to_end(&mut response)
            .map_err(|error| Failure::connection(format!("RPC request failed: {error}")))?;
        let (status, response_body) = parse_http_response(&response)?;
        if status == 401 {
            return Err(Failure::Authentication(
                "Authorization failed: Incorrect rpcuser or rpcpassword".to_owned(),
            ));
        }
        if status == 503 {
            let message = String::from_utf8_lossy(response_body)
                .trim_end_matches(['\r', '\n'])
                .to_owned();
            return Err(Failure::local(format!("Server response: {message}")));
        }
        if response_body.is_empty() {
            return Err(Failure::connection("no response from server"));
        }
        let response: Value = serde_json::from_slice(response_body).map_err(|error| {
            Failure::local(format!("couldn't parse reply from server: {error}"))
        })?;
        if let Some(error) = response.get("error").filter(|value| !value.is_null()) {
            let code = error.get("code").and_then(Value::as_i64).unwrap_or(-1);
            let message = error
                .get("message")
                .and_then(Value::as_str)
                .unwrap_or("RPC error")
                .to_owned();
            return Err(Failure::Rpc { code, message });
        }
        Ok(response.get("result").cloned().unwrap_or(Value::Null))
    }
}

fn sleep_before_retry(deadline: Option<Instant>) {
    let duration = deadline
        .and_then(|deadline| deadline.checked_duration_since(Instant::now()))
        .map_or(Duration::from_secs(1), |remaining| {
            remaining.min(Duration::from_secs(1))
        });
    if !duration.is_zero() {
        std::thread::sleep(duration);
    }
}

fn resolve_address(host: &str, port: u16) -> Result<SocketAddr, String> {
    (host, port)
        .to_socket_addrs()
        .map_err(|error| error.to_string())?
        .next()
        .ok_or_else(|| "address did not resolve".to_owned())
}

fn host_header(host: &str) -> String {
    host.parse::<IpAddr>()
        .map_or_else(|_| host.to_owned(), |address| address.to_string())
}

fn parse_http_response(response: &[u8]) -> Result<(u16, &[u8]), Failure> {
    let Some(header_end) = response.windows(4).position(|window| window == b"\r\n\r\n") else {
        return Err(Failure::local("truncated HTTP response"));
    };
    let headers = &response[..header_end];
    let body = &response[header_end + 4..];
    let status = headers
        .split(|byte| *byte == b'\n')
        .next()
        .and_then(|line| {
            std::str::from_utf8(line)
                .ok()?
                .split_whitespace()
                .nth(1)?
                .parse::<u16>()
                .ok()
        })
        .ok_or_else(|| Failure::local("invalid HTTP response"))?;
    let content_length = headers.split(|byte| *byte == b'\n').find_map(|line| {
        let line = std::str::from_utf8(line).ok()?;
        let (name, value) = line.split_once(':')?;
        name.eq_ignore_ascii_case("content-length")
            .then(|| value.trim().parse::<usize>().ok())
            .flatten()
    });
    let body = content_length.map_or(body, |length| &body[..length.min(body.len())]);
    Ok((status, body))
}

fn percent_encode(value: &str) -> String {
    let mut encoded = String::with_capacity(value.len());
    for byte in value.bytes() {
        if byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.' | b'~') {
            encoded.push(byte as char);
        } else {
            encoded.push('%');
            encoded.push(hex_digit(byte >> 4));
            encoded.push(hex_digit(byte & 0x0f));
        }
    }
    encoded
}

fn hex_digit(value: u8) -> char {
    match value {
        0..=9 => (b'0' + value) as char,
        _ => (b'A' + value - 10) as char,
    }
}

fn render_result(result: &Value) -> String {
    match result {
        Value::Null => String::new(),
        Value::String(value) => value.clone(),
        _ => serde_json::to_string_pretty(result).unwrap_or_else(|_| "null".to_owned()),
    }
}

fn get_info(client: &RpcClient, color: &str) -> Result<String, Failure> {
    let blockchain = client.call("getblockchaininfo", &Value::Array(Vec::new()))?;
    let network = client.call("getnetworkinfo", &Value::Array(Vec::new()))?;
    let reset = if color == "always" || (color == "auto" && io::stdout().is_terminal()) {
        "\x1b[0m"
    } else {
        ""
    };
    let blue = if reset.is_empty() { "" } else { "\x1b[34m" };
    let green = if reset.is_empty() { "" } else { "\x1b[32m" };
    let yellow = if reset.is_empty() { "" } else { "\x1b[33m" };
    let chain = string_value(&blockchain, "chain");
    let progress = number_value(&blockchain, "verificationprogress")
        .parse::<f64>()
        .unwrap_or_default()
        * 100.0;
    let connections_in = number_value(&network, "connections_in");
    let connections_out = number_value(&network, "connections_out");
    let connections = number_value(&network, "connections");
    let mut output = format!(
        "{blue}Chain: {chain}{reset}\nBlocks: {}\nHeaders: {}\nVerification progress: {:.4}%\nDifficulty: {}\n\n{green}Network: in {connections_in}, out {connections_out}, total {connections}{reset}\nVersion: {}\nTime offset (s): {}\nProxies: {}\nMin tx relay fee rate (BTC/kvB): {}\n\n",
        number_value(&blockchain, "blocks"),
        number_value(&blockchain, "headers"),
        progress,
        number_value(&blockchain, "difficulty"),
        number_value(&network, "version"),
        number_value(&network, "timeoffset"),
        format_proxies(&network),
        number_value(&network, "relayfee"),
    );
    let warnings = warning_value(&network);
    output.push_str(&format!(
        "{yellow}Warnings:{reset} {}",
        if warnings.is_empty() {
            "(none)"
        } else {
            &warnings
        }
    ));
    Ok(output)
}

fn warning_value(object: &Value) -> String {
    match object.get("warnings") {
        Some(Value::Array(values)) => values
            .iter()
            .filter_map(Value::as_str)
            .collect::<Vec<_>>()
            .join("; "),
        Some(value) => display_value(value),
        None => String::new(),
    }
}

fn number_value(object: &Value, key: &str) -> String {
    object.get(key).map_or_else(String::new, display_value)
}

fn string_value(object: &Value, key: &str) -> String {
    object
        .get(key)
        .and_then(Value::as_str)
        .map_or_else(|| number_value(object, key), ToOwned::to_owned)
}

fn display_value(value: &Value) -> String {
    match value {
        Value::String(value) => value.clone(),
        Value::Null => String::new(),
        _ => value.to_string(),
    }
}

fn format_proxies(network: &Value) -> String {
    let Some(networks) = network.get("networks").and_then(Value::as_array) else {
        return "n/a".to_owned();
    };
    let mut grouped: Vec<(String, Vec<String>)> = Vec::new();
    for entry in networks {
        let proxy = entry
            .get("proxy")
            .and_then(Value::as_str)
            .unwrap_or_default();
        if proxy.is_empty() {
            continue;
        }
        let name = entry
            .get("name")
            .and_then(Value::as_str)
            .unwrap_or_default();
        if let Some((_, names)) = grouped.iter_mut().find(|(value, _)| value == proxy) {
            names.push(name.to_owned());
        } else {
            grouped.push((proxy.to_owned(), vec![name.to_owned()]));
        }
    }
    if grouped.is_empty() {
        return "n/a".to_owned();
    }
    grouped
        .into_iter()
        .map(|(proxy, names)| format!("{proxy} ({})", names.join(", ")))
        .collect::<Vec<_>>()
        .join(", ")
}

fn net_info(client: &RpcClient, network: Network, arguments: &[String]) -> Result<String, Failure> {
    if arguments
        .first()
        .is_some_and(|value| value == "h" || value == "help")
    {
        return Ok(net_info_help());
    }
    let level = arguments
        .first()
        .map_or(0, |value| value.parse::<u8>().unwrap_or(0).min(4));
    let network_info = client.call("getnetworkinfo", &Value::Array(Vec::new()))?;
    let peers = client.call("getpeerinfo", &Value::Array(Vec::new()))?;
    let services = network_info
        .get("localservicesnames")
        .and_then(Value::as_array)
        .map(|values| {
            values
                .iter()
                .filter_map(Value::as_str)
                .map(|service| match service {
                    "NETWORK_LIMITED" => 'l',
                    "P2P_V2" => '2',
                    service => service
                        .chars()
                        .next()
                        .unwrap_or_default()
                        .to_ascii_lowercase(),
                })
                .collect::<String>()
        })
        .unwrap_or_default();
    let version = number_value(&network_info, "protocolversion");
    let subversion = string_value(&network_info, "subversion");
    let mut output = format!(
        "{CLIENT_NAME} client {CLIENT_VERSION}{} - server {version}{subversion}{}\n\n",
        network.display_suffix(),
        if level > 0 {
            format!(" services {services}")
        } else {
            String::new()
        }
    );
    if level > 0 {
        output.push_str("Peer connections\n\n");
        output.push_str(&format!(
            "{} peer(s)\n\n",
            peers.as_array().map_or(0, Vec::len)
        ));
    }
    output.push_str("Peer counts\n");
    output.push_str(&format!(
        "in {}\nout {}\ntotal {}\n",
        number_value(&network_info, "connections_in"),
        number_value(&network_info, "connections_out"),
        number_value(&network_info, "connections"),
    ));
    if level == 0 {
        output.push_str(&format!(
            "\nLocal services: {}",
            services_list(&network_info)
        ));
    }
    output.push_str("\n\nLocal addresses: ");
    let addresses = network_info
        .get("localaddresses")
        .and_then(Value::as_array)
        .map_or_else(String::new, |addresses| {
            addresses
                .iter()
                .filter_map(|address| {
                    Some(format!(
                        "{}:{}",
                        address.get("address")?.as_str()?,
                        address.get("port")?.as_u64()?
                    ))
                })
                .collect::<Vec<_>>()
                .join(", ")
        });
    output.push_str(if addresses.is_empty() {
        "n/a"
    } else {
        &addresses
    });
    Ok(output)
}

fn services_list(network: &Value) -> String {
    network
        .get("localservicesnames")
        .and_then(Value::as_array)
        .map_or_else(String::new, |services| {
            services
                .iter()
                .filter_map(Value::as_str)
                .map(|service| service.replace('_', " ").to_ascii_lowercase())
                .collect::<Vec<_>>()
                .join(", ")
        })
}

fn net_info_help() -> String {
    "-netinfo (level [outonly]) | help\n\nReturns a network peer connections dashboard with information from the remote server.\n"
        .to_owned()
}

fn help_text() -> String {
    format!(
        "{CLIENT_NAME} RPC client version {CLIENT_VERSION}\n\nUsage: bitcoin-cli [options] <command> [params]\n       bitcoin-cli [options] -named <command> [name=value]...\n\nOptions:\n  -datadir=<dir>       Specify data directory\n  -rpcconnect=<ip>     Send commands to node running on <ip>\n  -rpcport=<port>      Connect to JSON-RPC on <port>\n  -rpcuser=<user>      Username for JSON-RPC connections\n  -rpcpassword=<pw>   Password for JSON-RPC connections\n  -rpccookiefile=<p>  Location of the auth cookie\n  -rpcwait             Wait for RPC server to start\n  -stdin               Read extra arguments from standard input\n  -stdinrpcpass       Read RPC password from standard input\n  -named               Pass named instead of positional arguments\n  -getinfo             Get general information\n  -netinfo             Get network peer connection information\n"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn named_json_with_equals_is_positional() {
        let params = build_params(
            "echojson",
            &[r#"["key=value"]"#.to_owned(), "42".to_owned()],
            true,
        )
        .unwrap();
        assert_eq!(params, json!([["key=value"], 42]));
    }

    #[test]
    fn named_echo_values_remain_strings() {
        let params =
            build_params("echo", &["arg0=0".to_owned(), "arg1=1".to_owned()], true).unwrap();
        assert_eq!(params, json!({"arg0": "0", "arg1": "1"}));
    }

    #[test]
    fn core_string_conversion_entries_preserve_json_looking_values() {
        let params = build_params(
            "signmessagewithprivkey",
            &["privkey=1abc".to_owned(), "message=123".to_owned()],
            true,
        )
        .unwrap();
        assert_eq!(params, json!({"privkey": "1abc", "message": "123"}));

        let params = build_params(
            "finalizepsbt",
            &["psbt=123".to_owned(), "extract=false".to_owned()],
            true,
        )
        .unwrap();
        assert_eq!(params, json!({"psbt": "123", "extract": false}));
    }

    #[test]
    fn core_named_string_heuristic_preserves_equals_in_positional_paths() {
        let params = build_params("loadtxoutset", &["snapshot=part=one".to_owned()], true).unwrap();
        assert_eq!(params, json!(["snapshot=part=one"]));

        let params =
            build_params("loadtxoutset", &["path=snapshot=part=one".to_owned()], true).unwrap();
        assert_eq!(params, json!({"path": "snapshot=part=one"}));
    }

    #[test]
    fn core_conversion_table_leaves_unlisted_strings_raw() {
        assert_eq!(
            build_params("getrawtransaction", &["123".to_owned()], false).unwrap(),
            json!(["123"])
        );
        assert_eq!(
            build_params("getrawtransaction", &["txid=123".to_owned()], true).unwrap(),
            json!({"txid": "123"})
        );
        assert_eq!(
            build_params("getblockhash", &["123".to_owned()], false).unwrap(),
            json!([123])
        );
        assert_eq!(
            build_params("getblockstats", &["not-a-height".to_owned()], false).unwrap(),
            json!(["not-a-height"])
        );
    }

    #[test]
    fn rpc_connect_port_errors_keep_original_argument() {
        let error = parse_rpc_connect("127.0.0.1:notaport").unwrap_err();
        assert!(matches!(error, Failure::Local(message) if message.contains("127.0.0.1:notaport")));
    }
}
