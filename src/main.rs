use std::collections::HashMap;
use std::ffi::CString;
use std::fmt;
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufWriter, Write};
use std::path::PathBuf;
use std::sync::{
    Arc, Mutex,
    atomic::{AtomicBool, AtomicU64, Ordering},
    mpsc,
};
use std::thread;
use std::time::{Duration, Instant};

#[cfg(not(unix))]
use anyhow::bail;
use anyhow::{Context, Result};
use bitcoin::Network;
use clap::error::ErrorKind as ClapErrorKind;
use time::{OffsetDateTime, macros::format_description};
use tracing::Metadata;
use tracing_subscriber::EnvFilter;
use tracing_subscriber::fmt::{
    format::Writer,
    time::FormatTime,
    writer::{BoxMakeWriter, MakeWriter, MakeWriterExt},
};

use bitcoind_rs::{
    Node,
    config::{Args, Config, ConfigFileArg, is_known_config_option, network_data_dir_name},
};

const CORE_NODE_VERSION: &str = "31.1.0";

fn nested_core_startup_error(error: &anyhow::Error) -> Option<&bitcoind_rs::CoreStartupError> {
    error
        .chain()
        .find_map(|cause| cause.downcast_ref::<bitcoind_rs::CoreStartupError>())
}

fn main() {
    // Match Core's private data-file default.  This must be set before any
    // configuration, directory, or log file is created so the process umask
    // also protects paths opened by the storage and RPC subsystems.
    #[cfg(unix)]
    unsafe {
        libc::umask(0o077);
    }
    let result = {
        #[cfg(unix)]
        {
            match spawned_ipc_fd() {
                Ok(Some(fd)) => bitcoind_rs::run_spawned_ipc(fd),
                Ok(None) => run(),
                Err(error) => Err(error),
            }
        }
        #[cfg(not(unix))]
        {
            run()
        }
    };
    if let Err(error) = result {
        if let Some(core_error) = nested_core_startup_error(&error) {
            // Core prints translated chainstate recovery messages directly;
            // callers (including the functional test harness) compare this
            // diagnostic without an additional prefix.
            eprintln!("{core_error}");
        } else {
            eprintln!("Error: {error}");
        }
        std::process::exit(1);
    }
}

#[cfg(unix)]
fn spawned_ipc_fd() -> Result<Option<std::os::unix::io::RawFd>> {
    if env!("CARGO_BIN_NAME") != "bitcoin-node" {
        return Ok(None);
    }
    let arguments = std::env::args_os().collect::<Vec<_>>();
    if arguments.len() != 3 || arguments.get(1).and_then(|arg| arg.to_str()) != Some("-ipcfd") {
        return Ok(None);
    }
    let value = arguments
        .get(2)
        .and_then(|arg| arg.to_str())
        .unwrap_or_default();
    let fd = value
        .parse::<std::os::unix::io::RawFd>()
        .map_err(|_| anyhow::anyhow!("Invalid -ipcfd number '{value}'"))?;
    Ok(Some(fd))
}

fn run() -> Result<()> {
    let args = match Args::parse_with_config() {
        Ok(args) => args,
        Err(error) => {
            if let Some(clap_error) = error.downcast_ref::<clap::Error>() {
                match clap_error.kind() {
                    ClapErrorKind::DisplayVersion => {
                        print!("{}", daemon_version_banner(env!("CARGO_BIN_NAME")));
                        return Ok(());
                    }
                    ClapErrorKind::DisplayHelp => {
                        clap_error.print()?;
                        return Ok(());
                    }
                    _ => {}
                }
            }
            return Err(error);
        }
    };
    let daemon = args.daemon || args.daemon_wait;
    let daemon_wait = args.daemon_wait;
    let config = Config::from_args(args)?;
    let readiness = if daemon {
        daemonize(daemon_wait)?
    } else {
        None
    };
    let mut readiness = DaemonReadyGuard::new(readiness);
    let runtime = match tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
    {
        Ok(runtime) => runtime,
        Err(error) => {
            readiness.notify(false);
            return Err(error.into());
        }
    };
    runtime.block_on(tokio::task::LocalSet::new().run_until(run_node(config, readiness)))
}

fn daemon_version_banner(executable: &str) -> String {
    format!("Bitcoin Core daemon version v{CORE_NODE_VERSION} {executable}\n")
}

async fn run_node(config: Config, mut readiness: DaemonReadyGuard) -> Result<()> {
    let network_dir_name = network_data_dir_name(config.network);
    let network_data_dir = if network_dir_name.is_empty() {
        config.datadir.clone()
    } else {
        config.datadir.join(network_dir_name)
    };
    fs::create_dir_all(&network_data_dir).with_context(|| {
        format!(
            "creating network data directory {}",
            network_data_dir.display()
        )
    })?;
    let filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new(config.logging.tracing_filter()));
    let (writer, log_file) = if let Some(path) = config
        .debug_log_file_enabled
        .then_some(&config.debug_log_path)
    {
        let log_file = AsyncLogFile::open(path, config.shrink_debug_file)
            .with_context(|| format!("Could not open debug log file {}", path.display()))?;
        let log_file_handle = log_file.handle();
        if config.print_to_console {
            let writer = if config.logging.log_rate_limit {
                BoxMakeWriter::new(
                    std::io::stdout.and(RateLimitedLogFile::new(log_file_handle.clone())),
                )
            } else {
                BoxMakeWriter::new(std::io::stdout.and(log_file_handle.clone()))
            };
            (writer, Some(log_file))
        } else {
            let writer = if config.logging.log_rate_limit {
                BoxMakeWriter::new(RateLimitedLogFile::new(log_file_handle.clone()))
            } else {
                BoxMakeWriter::new(log_file_handle.clone())
            };
            (writer, Some(log_file))
        }
    } else if config.print_to_console {
        (BoxMakeWriter::new(std::io::stdout), None)
    } else {
        (BoxMakeWriter::new(std::io::sink), None)
    };
    let builder = tracing_subscriber::fmt()
        .with_env_filter(filter)
        .with_target(false)
        .with_ansi(false)
        .with_writer(writer)
        .with_level(config.logging.level_always)
        .with_thread_names(config.logging.thread_names)
        .with_file(config.logging.source_locations)
        .with_line_number(config.logging.source_locations);
    if !config.logging.timestamps {
        builder.without_time().init();
    } else if config.logging.time_micros {
        builder
            .with_timer(CoreLogTimer { microseconds: true })
            .init();
    } else {
        builder.init();
    }
    let shutdown_requested = Arc::new(AtomicBool::new(false));
    let startup_signal_task = install_startup_signal_listener(shutdown_requested.clone())?;
    tracing::info!("version 31.1.0 (bitcoind-rs)");
    tracing::info!("Loading block index");
    let node = match Node::open_with_shutdown(config, shutdown_requested.clone()) {
        Ok(node) => node,
        Err(_) if shutdown_requested.load(Ordering::Acquire) => {
            tracing::info!("Shutdown requested during startup");
            startup_signal_task.abort();
            return Ok(());
        }
        Err(error) => {
            startup_signal_task.abort();
            return Err(error);
        }
    };
    if shutdown_requested.load(Ordering::Acquire) {
        node.request_shutdown();
    }
    let _pid_file = (!node.config.pid_path.as_os_str().is_empty())
        .then(|| PidFile::create(node.config.pid_path.clone()))
        .transpose()?;
    let (best_height, best_hash) = {
        let chain = node.chain.read();
        (chain.height(), chain.best_hash())
    };
    tracing::info!("Loaded best chain: hash={best_hash} height={best_height}");
    node.log_asmap_configuration();
    if node.config.network == Network::Signet {
        tracing::info!(
            "Signet derived magic (message start): {}",
            hex::encode(node.network_magic())
        );
    }
    let snapshot_chainstate = node.chain.read().snapshot_chainstate_path();
    if node.chain.read().snapshot_provenance().is_none() && snapshot_chainstate.is_dir() {
        fs::remove_dir_all(&snapshot_chainstate).with_context(|| {
            format!(
                "cleaning up AssumeUTXO background chainstate {}",
                snapshot_chainstate.display()
            )
        })?;
        tracing::info!("[snapshot] cleaning up unneeded background chainstate");
    }
    if std::env::args().any(|argument| argument == "-nolisten=0" || argument == "--nolisten=0") {
        tracing::warn!("[warning] Parsed potentially confusing double-negative -listen=0");
    }
    log_config_file_path(&node.config.config_file_args);
    log_startup_arguments(&node.config.config_file_args);
    log_settings_file(node.config.settings_path());
    log_ignored_config_values(&node.config.config_file_args);
    log_config_warnings(&node.config.config_file_args);
    log_config_section_warnings(&node.config.config_file_args);
    if node.config.reindex || node.config.reindex_chainstate {
        if let Some((height, block_hash, reason)) =
            node.chain.read().first_script_verification_reason()
        {
            tracing::info!(
                "Enabling script verification at block #{height} ({block_hash}): {reason}."
            );
        }
    }
    if node.config.reindex {
        tracing::info!("Reindexing finished");
    }
    if node.config.network == Network::Testnet {
        tracing::warn!(
            "Warning: Support for testnet3 is deprecated and will be removed in an upcoming release. Consider switching to testnet4."
        );
    }
    log_parameter_interactions(&node.config.config_file_args);
    log_ignored_config(&node.config.datadir);
    #[cfg(unix)]
    let log_reopen_task = log_file
        .as_ref()
        .map(|log_file| tokio::spawn(reopen_log_on_sighup(log_file.handle())));
    let (startup_sender, startup_receiver) = tokio::sync::oneshot::channel();
    let mut node_run = Box::pin(node.run_with_startup(Some(startup_sender)));
    let result = tokio::select! {
        ready = startup_receiver => {
            readiness.notify(ready.is_ok());
            node_run.await
        }
        result = &mut node_run => {
            readiness.notify(false);
            result
        }
    };
    #[cfg(unix)]
    if let Some(task) = log_reopen_task {
        task.abort();
    }
    startup_signal_task.abort();
    if let Some(log_file) = log_file {
        log_file.shutdown();
    }
    result
}

#[cfg(unix)]
fn install_startup_signal_listener(
    shutdown_requested: Arc<AtomicBool>,
) -> Result<tokio::task::JoinHandle<()>> {
    use tokio::signal::unix::{SignalKind, signal};

    let mut interrupt = signal(SignalKind::interrupt()).context("installing SIGINT handler")?;
    let mut terminate = signal(SignalKind::terminate()).context("installing SIGTERM handler")?;
    Ok(tokio::spawn(async move {
        tokio::select! {
            _ = interrupt.recv() => {}
            _ = terminate.recv() => {}
        }
        shutdown_requested.store(true, Ordering::Release);
    }))
}

#[cfg(not(unix))]
fn install_startup_signal_listener(
    shutdown_requested: Arc<AtomicBool>,
) -> Result<tokio::task::JoinHandle<()>> {
    Ok(tokio::spawn(async move {
        if tokio::signal::ctrl_c().await.is_ok() {
            shutdown_requested.store(true, Ordering::Release);
        }
    }))
}

fn log_config_file_path(config_file_args: &[ConfigFileArg]) {
    if let Some(path) = config_file_args.first().map(|entry| &entry.path) {
        tracing::info!("Config file: {}", path.display());
    }
}

fn log_settings_file(path: Option<&std::path::Path>) {
    let Some(path) = path else {
        return;
    };
    let Ok(contents) = fs::read_to_string(path) else {
        return;
    };
    let Ok(serde_json::Value::Object(settings)) = serde_json::from_str(&contents) else {
        return;
    };

    let mut unknown = settings
        .keys()
        .filter(|key| key.as_str() != "_warning_" && !is_known_config_option(key))
        .collect::<Vec<_>>();
    unknown.sort_unstable();
    for key in unknown {
        tracing::warn!("Ignoring unknown rw_settings value {key}");
    }
    for (key, value) in settings {
        if key == "_warning_" {
            continue;
        }
        let value = serde_json::to_string(&value).unwrap_or_else(|_| "null".to_owned());
        tracing::info!("Setting file arg: {key} = {value}");
    }
}

fn log_ignored_config_values(config_file_args: &[ConfigFileArg]) {
    for entry in config_file_args {
        if !entry.key.is_empty() && !is_known_config_option(&entry.key) {
            tracing::info!("Ignoring unknown configuration value {}", entry.key);
        }
    }
}

fn log_config_section_warnings(config_file_args: &[ConfigFileArg]) {
    let mut first = true;
    for entry in config_file_args {
        let section = if entry.key.is_empty() {
            entry.section.as_deref()
        } else if entry.section.is_none() {
            entry.key.split_once('.').map(|(section, _)| section)
        } else {
            None
        };
        let Some(section) = section else {
            continue;
        };
        if matches!(section, "main" | "regtest" | "test" | "testnet4" | "signet") {
            continue;
        }
        if first {
            eprintln!(
                "Warning: {}:{} Section [{}] is not recognized.",
                entry.path.display(),
                entry.line,
                section
            );
            first = false;
        } else {
            eprintln!(
                "{}:{} Section [{}] is not recognized.",
                entry.path.display(),
                entry.line,
                section
            );
        }
    }
}

fn log_config_warnings(config_file_args: &[ConfigFileArg]) {
    if config_file_args
        .iter()
        .any(|entry| entry.key == "reindex" && (entry.value == "1" || entry.value == "true"))
    {
        tracing::warn!(
            "[warning] reindex=1 is set in the configuration file, which will significantly slow down startup. Consider removing or commenting out this option for better performance, unless there is currently a condition which makes rebuilding the indexes necessary"
        );
    }
}

fn log_startup_arguments(config_file_args: &[ConfigFileArg]) {
    for argument in std::env::args().skip(1) {
        let Some(argument) = argument
            .strip_prefix("--")
            .or_else(|| argument.strip_prefix('-'))
        else {
            continue;
        };
        let (key, value) = argument.split_once('=').unwrap_or((argument, "1"));
        let mut key = key.to_ascii_lowercase();
        let mut value = value.to_owned();
        if key == "nosettings" && (value == "1" || value.eq_ignore_ascii_case("true")) {
            key = "settings".to_owned();
            value = "false".to_owned();
        }
        if matches!(key.as_str(), "rpcbind" | "rpcallowip") {
            continue;
        }
        let redacted = matches!(
            key.as_str(),
            "rpcauth" | "rpcpassword" | "rpcuser" | "torpassword"
        );
        if redacted {
            tracing::info!("Command-line arg: {key}=****");
        } else if key == "settings" && value == "false" {
            tracing::info!("Command-line arg: {key}={value}");
        } else {
            tracing::info!("Command-line arg: {key}=\"{value}\"");
        }
    }

    for entry in config_file_args {
        if entry.key.is_empty() {
            continue;
        }
        let (key, value, unquoted) = if entry.key == "nosettings"
            && (entry.value == "1" || entry.value.eq_ignore_ascii_case("true"))
        {
            ("settings", "false", true)
        } else if matches!(
            entry.key.as_str(),
            "rpcauth" | "rpcpassword" | "rpcuser" | "torpassword"
        ) {
            (&*entry.key, "****", false)
        } else {
            (&*entry.key, entry.value.as_str(), false)
        };
        if let Some(section) = &entry.section {
            if unquoted {
                tracing::info!("Config file arg: [{section}] {key}={value}");
            } else {
                tracing::info!("Config file arg: [{section}] {key}=\"{value}\"");
            }
        } else {
            if unquoted {
                tracing::info!("Config file arg: {key}={value}");
            } else {
                tracing::info!("Config file arg: {key}=\"{value}\"");
            }
        }
    }
}

fn log_parameter_interactions(config_file_args: &[ConfigFileArg]) {
    let mut connect_enabled = false;
    let mut connect_disabled = false;
    let mut seednode = false;
    let mut explicit_dnsseed = false;
    let mut proxy = false;
    for argument in std::env::args().skip(1) {
        let Some(argument) = argument
            .strip_prefix("--")
            .or_else(|| argument.strip_prefix('-'))
        else {
            continue;
        };
        let (key, value) = argument.split_once('=').unwrap_or((argument, "1"));
        match key.to_ascii_lowercase().as_str() {
            "connect" => {
                let disabled = value == "0" || value.eq_ignore_ascii_case("false");
                connect_disabled |= disabled;
                connect_enabled |= !disabled;
            }
            "noconnect" => connect_disabled = true,
            "seednode" => seednode = true,
            "dnsseed" => {
                explicit_dnsseed = true;
            }
            "proxy" => proxy = true,
            _ => {}
        }
    }
    if connect_enabled && seednode {
        tracing::warn!("-seednode is ignored when -connect is used");
    }
    if (connect_enabled || connect_disabled) && explicit_dnsseed && proxy {
        tracing::warn!("-dnsseed is ignored when -connect is used and -proxy is specified");
    }
    let config_has = |key: &str| config_file_args.iter().any(|entry| entry.key == key);
    if connect_disabled && !explicit_dnsseed && !config_has("dnsseed") {
        tracing::warn!(
            "parameter interaction: -connect or -maxconnections=0 set -> setting -dnsseed=0"
        );
    }
    if connect_disabled && !config_has("bind") && !config_has("whitebind") {
        tracing::warn!(
            "parameter interaction: -connect or -maxconnections=0 set -> setting -listen=0"
        );
    }
}

fn log_ignored_config(datadir: &std::path::Path) {
    let noconf = std::env::args().skip(1).any(|argument| {
        let argument = argument
            .strip_prefix("--")
            .or_else(|| argument.strip_prefix('-'))
            .unwrap_or_default();
        let (key, value) = argument.split_once('=').unwrap_or((argument, "1"));
        key.eq_ignore_ascii_case("noconf") && (value == "1" || value.eq_ignore_ascii_case("true"))
    });
    if noconf && datadir.join("bitcoin.conf").exists() {
        tracing::info!(
            "Data directory \"{}\" contains a \"bitcoin.conf\" file which is explicitly ignored using -noconf.",
            datadir.display()
        );
    }
}

const ASYNC_LOG_QUEUE_CAPACITY: usize = 16_384;
const ASYNC_LOG_FILE_BUFFER_BYTES: usize = 1024 * 1024;
// Keep asynchronous logging decoupled from request handling while making
// diagnostics visible promptly to Core-compatible log watchers.
const ASYNC_LOG_FLUSH_INTERVAL: Duration = Duration::from_millis(25);

enum AsyncLogCommand {
    Write(Vec<u8>),
    Reopen,
    #[cfg(test)]
    Flush(mpsc::Sender<io::Result<()>>),
    Shutdown(mpsc::Sender<io::Result<()>>),
}

struct AsyncLogState {
    sender: mpsc::SyncSender<AsyncLogCommand>,
    dropped_bytes: AtomicU64,
    last_error: Mutex<Option<String>>,
}

#[derive(Clone)]
struct AsyncLogFileHandle {
    state: Arc<AsyncLogState>,
    path: PathBuf,
}

struct AsyncLogFile {
    handle: AsyncLogFileHandle,
    worker: Option<thread::JoinHandle<()>>,
}

impl AsyncLogFile {
    fn open(path: &std::path::Path, shrink: bool) -> io::Result<Self> {
        let mut options = OpenOptions::new();
        options.create(true).write(true);
        if shrink {
            options.truncate(true);
        } else {
            options.append(true);
        }
        let file = options.open(path)?;
        let (sender, receiver) = mpsc::sync_channel(ASYNC_LOG_QUEUE_CAPACITY);
        let log_path = path.to_owned();
        let state = Arc::new(AsyncLogState {
            sender,
            dropped_bytes: AtomicU64::new(0),
            last_error: Mutex::new(None),
        });
        let worker_state = state.clone();
        let worker_path = log_path.clone();
        let worker = thread::Builder::new()
            .name("debug-log".to_owned())
            .spawn(move || async_log_worker(file, worker_path, receiver, worker_state))?;
        Ok(Self {
            handle: AsyncLogFileHandle {
                state,
                path: log_path,
            },
            worker: Some(worker),
        })
    }

    fn handle(&self) -> AsyncLogFileHandle {
        self.handle.clone()
    }

    fn shutdown(mut self) {
        self.shutdown_inner();
    }

    fn shutdown_inner(&mut self) {
        let Some(worker) = self.worker.take() else {
            return;
        };
        let (sender, receiver) = mpsc::channel();
        let _ = self
            .handle
            .state
            .sender
            .send(AsyncLogCommand::Shutdown(sender));
        let _ = receiver.recv();
        let _ = worker.join();
        let dropped = self.handle.state.dropped_bytes.load(Ordering::Relaxed);
        if dropped != 0 {
            eprintln!("[debug-log] dropped {dropped} bytes because the async log queue was full");
        }
        if let Ok(last_error) = self.handle.state.last_error.lock()
            && let Some(error) = last_error.as_deref()
        {
            eprintln!("[debug-log] worker error: {error}");
        }
    }
}

impl Drop for AsyncLogFile {
    fn drop(&mut self) {
        // Startup has several fallible steps after the logger is installed.
        // Drain the worker on those early-return paths too; otherwise the
        // final diagnostic records can be lost when `run_node` unwinds.
        self.shutdown_inner();
    }
}

impl AsyncLogFileHandle {
    fn enqueue(&self, bytes: Vec<u8>) {
        let byte_count = bytes.len() as u64;
        if let Err(error) = self.state.sender.try_send(AsyncLogCommand::Write(bytes)) {
            match error {
                mpsc::TrySendError::Full(AsyncLogCommand::Write(_))
                | mpsc::TrySendError::Disconnected(AsyncLogCommand::Write(_)) => {
                    self.state
                        .dropped_bytes
                        .fetch_add(byte_count, Ordering::Relaxed);
                }
                // Only Write commands are sent through this non-blocking path.
                mpsc::TrySendError::Full(_) | mpsc::TrySendError::Disconnected(_) => unreachable!(),
            }
        }
    }

    fn reopen(&self) -> io::Result<()> {
        // Reopen is a control operation rather than a log record.  It is rare,
        // so waiting for room preserves ordering even if the diagnostic queue
        // is temporarily saturated.
        self.state
            .sender
            .send(AsyncLogCommand::Reopen)
            .map_err(|_| io::Error::new(io::ErrorKind::BrokenPipe, "debug log worker stopped"))
    }

    #[cfg(test)]
    fn flush(&self) -> io::Result<()> {
        let (sender, receiver) = mpsc::channel();
        self.state
            .sender
            .send(AsyncLogCommand::Flush(sender))
            .map_err(|_| io::Error::new(io::ErrorKind::BrokenPipe, "debug log worker stopped"))?;
        receiver
            .recv()
            .map_err(|_| io::Error::new(io::ErrorKind::BrokenPipe, "debug log worker stopped"))?
    }
}

fn async_log_worker(
    file: File,
    path: PathBuf,
    receiver: mpsc::Receiver<AsyncLogCommand>,
    state: Arc<AsyncLogState>,
) {
    let mut file = BufWriter::with_capacity(ASYNC_LOG_FILE_BUFFER_BYTES, file);
    let mut last_flush = Instant::now();
    loop {
        // A timeout alone is not sufficient here: while the node is busy the
        // queue can remain continuously readable, so recv_timeout() never
        // times out and a large BufWriter would hide recent records from
        // tools that tail debug.log. Keep an explicit deadline and flush
        // after processing a command once it expires.
        let wait = ASYNC_LOG_FLUSH_INTERVAL.saturating_sub(last_flush.elapsed());
        let command = match receiver.recv_timeout(wait) {
            Ok(command) => command,
            Err(mpsc::RecvTimeoutError::Timeout) => {
                if let Err(error) = file.flush() {
                    record_async_log_error(&state, error);
                }
                last_flush = Instant::now();
                continue;
            }
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                if let Err(error) = file.flush() {
                    record_async_log_error(&state, error);
                }
                break;
            }
        };
        match command {
            AsyncLogCommand::Write(bytes) => {
                if let Err(error) = file.write_all(&bytes) {
                    record_async_log_error(&state, error);
                }
            }
            AsyncLogCommand::Reopen => {
                if let Err(error) = file.flush() {
                    record_async_log_error(&state, error);
                }
                last_flush = Instant::now();
                match OpenOptions::new().create(true).append(true).open(&path) {
                    Ok(new_file) => {
                        file = BufWriter::with_capacity(ASYNC_LOG_FILE_BUFFER_BYTES, new_file);
                    }
                    Err(error) => record_async_log_error(&state, error),
                }
            }
            #[cfg(test)]
            AsyncLogCommand::Flush(reply) => {
                let result = file.flush().map_err(|error| {
                    record_async_log_error(&state, io::Error::other(error.to_string()));
                    error
                });
                last_flush = Instant::now();
                let _ = reply.send(result);
            }
            AsyncLogCommand::Shutdown(reply) => {
                let result = file.flush().map_err(|error| {
                    record_async_log_error(&state, io::Error::other(error.to_string()));
                    error
                });
                let _ = reply.send(result);
                break;
            }
        }
        if last_flush.elapsed() >= ASYNC_LOG_FLUSH_INTERVAL {
            if let Err(error) = file.flush() {
                record_async_log_error(&state, error);
            }
            last_flush = Instant::now();
        }
    }
}

fn record_async_log_error(state: &AsyncLogState, error: io::Error) {
    if let Ok(mut last_error) = state.last_error.lock() {
        if last_error.is_none() {
            *last_error = Some(error.to_string());
        }
    }
}

struct AsyncLogWriter {
    file: AsyncLogFileHandle,
    buffer: Vec<u8>,
}

impl Write for AsyncLogWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.buffer.extend_from_slice(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        if self.buffer.is_empty() {
            return Ok(());
        }
        let buffer = std::mem::take(&mut self.buffer);
        self.file.enqueue(buffer);
        Ok(())
    }
}

impl Drop for AsyncLogWriter {
    fn drop(&mut self) {
        let _ = self.flush();
    }
}

impl<'a> MakeWriter<'a> for AsyncLogFileHandle {
    type Writer = AsyncLogWriter;

    fn make_writer(&'a self) -> Self::Writer {
        AsyncLogWriter {
            file: self.clone(),
            buffer: Vec::new(),
        }
    }
}

const LOG_RATE_LIMIT_MAX_BYTES: u64 = 1024 * 1024;
const LOG_RATE_LIMIT_WINDOW: Duration = Duration::from_secs(60 * 60);

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct LogSource {
    file: Option<String>,
    line: Option<u32>,
    module: Option<String>,
    target: String,
    name: &'static str,
}

impl LogSource {
    fn from_metadata(metadata: &Metadata<'_>) -> Self {
        Self {
            file: metadata.file().map(str::to_owned),
            line: metadata.line(),
            module: metadata.module_path().map(str::to_owned),
            target: metadata.target().to_owned(),
            name: metadata.name(),
        }
    }

    #[cfg(test)]
    fn test(name: &'static str) -> Self {
        Self {
            file: Some("test.rs".to_owned()),
            line: Some(1),
            module: Some("test".to_owned()),
            target: "test".to_owned(),
            name,
        }
    }
}

#[derive(Debug)]
struct LogSourceStats {
    available_bytes: u64,
    dropped_bytes: u64,
}

#[derive(Debug)]
struct LogRateLimitState {
    window_started: Instant,
    sources: HashMap<LogSource, LogSourceStats>,
}

#[derive(Debug)]
struct LogRateLimiter {
    state: Mutex<LogRateLimitState>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LogRateLimitDecision {
    Allowed { suppression_active: bool },
    NewlySuppressed,
    Suppressed,
}

impl LogRateLimiter {
    fn new() -> Self {
        Self {
            state: Mutex::new(LogRateLimitState {
                window_started: Instant::now(),
                sources: HashMap::new(),
            }),
        }
    }

    fn consume(&self, source: LogSource, bytes: usize) -> LogRateLimitDecision {
        let Ok(mut state) = self.state.lock() else {
            // Logging must not take down the node if the limiter is poisoned.
            return LogRateLimitDecision::Allowed {
                suppression_active: false,
            };
        };
        if state.window_started.elapsed() >= LOG_RATE_LIMIT_WINDOW {
            state.window_started = Instant::now();
            state.sources.clear();
        }

        let bytes = bytes as u64;
        let stats = state
            .sources
            .entry(source)
            .or_insert_with(|| LogSourceStats {
                available_bytes: LOG_RATE_LIMIT_MAX_BYTES,
                dropped_bytes: 0,
            });
        if stats.dropped_bytes > 0 {
            stats.dropped_bytes = stats.dropped_bytes.saturating_add(bytes);
            return LogRateLimitDecision::Suppressed;
        }
        if bytes > stats.available_bytes {
            stats.dropped_bytes = bytes;
            return LogRateLimitDecision::NewlySuppressed;
        }
        stats.available_bytes -= bytes;
        let suppression_active = state
            .sources
            .values()
            .any(|source| source.dropped_bytes > 0);
        LogRateLimitDecision::Allowed { suppression_active }
    }
}

#[derive(Clone)]
struct RateLimitedLogFile {
    file: AsyncLogFileHandle,
    limiter: Arc<LogRateLimiter>,
}

impl RateLimitedLogFile {
    fn new(file: AsyncLogFileHandle) -> Self {
        Self {
            file,
            limiter: Arc::new(LogRateLimiter::new()),
        }
    }
}

struct RateLimitedLogWriter {
    inner: AsyncLogWriter,
    limiter: Arc<LogRateLimiter>,
    source: LogSource,
    buffer: Vec<u8>,
}

impl Write for RateLimitedLogWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.buffer.extend_from_slice(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        if self.buffer.is_empty() {
            return Ok(());
        }
        let buffer = std::mem::take(&mut self.buffer);
        match self.limiter.consume(self.source.clone(), buffer.len()) {
            LogRateLimitDecision::Suppressed => Ok(()),
            LogRateLimitDecision::NewlySuppressed => {
                self.inner.write_all(b"[*] ")?;
                self.inner.write_all(&buffer)?;
                self.inner.flush()
            }
            LogRateLimitDecision::Allowed { suppression_active } => {
                if suppression_active {
                    self.inner.write_all(b"[*] ")?;
                }
                self.inner.write_all(&buffer)?;
                self.inner.flush()
            }
        }
    }
}

impl Drop for RateLimitedLogWriter {
    fn drop(&mut self) {
        let _ = self.flush();
    }
}

impl<'a> MakeWriter<'a> for RateLimitedLogFile {
    type Writer = RateLimitedLogWriter;

    fn make_writer(&'a self) -> Self::Writer {
        RateLimitedLogWriter {
            inner: self.file.make_writer(),
            limiter: self.limiter.clone(),
            source: LogSource {
                file: None,
                line: None,
                module: None,
                target: "unknown".to_owned(),
                name: "unknown",
            },
            buffer: Vec::new(),
        }
    }

    fn make_writer_for(&'a self, metadata: &Metadata<'_>) -> Self::Writer {
        RateLimitedLogWriter {
            inner: self.file.make_writer(),
            limiter: self.limiter.clone(),
            source: LogSource::from_metadata(metadata),
            buffer: Vec::new(),
        }
    }
}

#[cfg(unix)]
async fn reopen_log_on_sighup(log_file: AsyncLogFileHandle) {
    use tokio::signal::unix::{SignalKind, signal};

    let mut sighup = match signal(SignalKind::hangup()) {
        Ok(signal) => signal,
        Err(error) => {
            tracing::warn!(%error, "unable to install SIGHUP handler for debug log reopening");
            return;
        }
    };
    while sighup.recv().await.is_some() {
        if let Err(error) = log_file.reopen() {
            tracing::warn!(%error, path = %log_file.path.display(), "unable to reopen debug log file");
        }
    }
}

struct DaemonReadyGuard {
    readiness: Option<DaemonReady>,
}

impl DaemonReadyGuard {
    fn new(readiness: Option<DaemonReady>) -> Self {
        Self { readiness }
    }

    fn notify(&mut self, success: bool) {
        if let Some(readiness) = self.readiness.take() {
            readiness.notify(success);
        }
    }
}

impl Drop for DaemonReadyGuard {
    fn drop(&mut self) {
        self.notify(false);
    }
}

#[cfg(unix)]
struct DaemonReady {
    fd: Option<std::os::unix::io::RawFd>,
}

#[cfg(unix)]
impl DaemonReady {
    fn notify(self, success: bool) {
        if let Some(fd) = self.fd {
            signal_ready_fd(fd, success);
        }
    }
}

#[cfg(not(unix))]
struct DaemonReady;

#[cfg(not(unix))]
impl DaemonReady {
    fn notify(self, _success: bool) {}
}

#[cfg(unix)]
fn signal_ready_fd(fd: std::os::unix::io::RawFd, success: bool) {
    let status = [u8::from(success)];
    // SAFETY: `fd` is the write end of the private readiness pipe created by
    // `daemonize`, and `status` remains alive for the duration of the write.
    unsafe {
        let _ = libc::write(fd, status.as_ptr().cast(), status.len());
        libc::close(fd);
    }
}

#[cfg(unix)]
fn daemonize(wait: bool) -> Result<Option<DaemonReady>> {
    use std::os::unix::io::RawFd;

    let mut pipe = [-1 as RawFd; 2];
    // SAFETY: `pipe` points to space for the two descriptors requested by
    // libc and is not aliased during the call.
    if unsafe { libc::pipe(pipe.as_mut_ptr()) } != 0 {
        return Err(std::io::Error::last_os_error()).context("creating daemon readiness pipe");
    }

    // SAFETY: No Tokio runtime or other application threads exist yet; the
    // process is forked before the async runtime is created.
    let pid = unsafe { libc::fork() };
    if pid < 0 {
        // SAFETY: both descriptors were created by the private pipe above.
        unsafe {
            libc::close(pipe[0]);
            libc::close(pipe[1]);
        }
        return Err(std::io::Error::last_os_error()).context("forking daemon process");
    }
    if pid > 0 {
        // SAFETY: the parent owns the read end and no longer needs the write
        // end after forking.
        unsafe { libc::close(pipe[1]) };
        let mut status = [0u8; 1];
        // SAFETY: `status` is writable storage for the one-byte child result.
        let read = unsafe { libc::read(pipe[0], status.as_mut_ptr().cast(), status.len()) };
        // SAFETY: the parent owns this descriptor.
        unsafe { libc::close(pipe[0]) };
        if read == 1 && status[0] == 1 {
            std::process::exit(0);
        }
        eprintln!("daemon process failed during initialization");
        std::process::exit(1);
    }

    let readiness_fd = pipe[1];
    // SAFETY: the child owns the write end after the fork.
    unsafe { libc::close(pipe[0]) };
    // SAFETY: the child is the only process calling these process-level setup
    // functions, before the Tokio runtime or application threads exist.
    if unsafe { libc::setsid() } < 0 {
        signal_ready_fd(readiness_fd, false);
        return Err(std::io::Error::last_os_error()).context("creating daemon session");
    }

    let null_path = CString::new("/dev/null").expect("null path contains no NUL");
    // SAFETY: `null_path` is a valid NUL-terminated path and the flags do not
    // mutate Rust-managed memory.
    let null_fd = unsafe { libc::open(null_path.as_ptr(), libc::O_RDWR) };
    if null_fd < 0 {
        signal_ready_fd(readiness_fd, false);
        return Err(std::io::Error::last_os_error()).context("opening /dev/null");
    }
    for target in 0..=2 {
        // SAFETY: `null_fd` and the standard descriptor targets are valid file
        // descriptor integers at this point.
        if unsafe { libc::dup2(null_fd, target) } < 0 {
            if null_fd > 2 {
                // SAFETY: the child owns the descriptor opened above.
                unsafe { libc::close(null_fd) };
            }
            signal_ready_fd(readiness_fd, false);
            return Err(std::io::Error::last_os_error()).context("redirecting daemon descriptors");
        }
    }
    if null_fd > 2 {
        // SAFETY: the child owns the descriptor opened above.
        unsafe { libc::close(null_fd) };
    }
    if !wait {
        signal_ready_fd(readiness_fd, true);
        return Ok(Some(DaemonReady { fd: None }));
    }
    Ok(Some(DaemonReady {
        fd: Some(readiness_fd),
    }))
}

#[cfg(not(unix))]
fn daemonize(_wait: bool) -> Result<Option<DaemonReady>> {
    bail!("--daemon is only supported on Unix platforms")
}

#[derive(Clone, Copy, Debug)]
struct CoreLogTimer {
    microseconds: bool,
}

impl FormatTime for CoreLogTimer {
    fn format_time(&self, writer: &mut Writer<'_>) -> fmt::Result {
        let now = OffsetDateTime::now_local().unwrap_or_else(|_| OffsetDateTime::now_utc());
        let format = if self.microseconds {
            format_description!(
                "[year]-[month]-[day] [hour]:[minute]:[second].[subsecond digits:6]"
            )
        } else {
            format_description!("[year]-[month]-[day] [hour]:[minute]:[second]")
        };
        let timestamp = now.format(format).map_err(|_| fmt::Error)?;
        write!(writer, "{timestamp}")
    }
}

#[derive(Debug)]
struct PidFile {
    path: PathBuf,
    contents: Vec<u8>,
}

impl PidFile {
    fn create(path: PathBuf) -> Result<Self> {
        if path.as_os_str().is_empty() {
            anyhow::bail!("PID file path must not be empty");
        }
        let contents = format!("{}\n", std::process::id()).into_bytes();
        let mut file = OpenOptions::new()
            .create(true)
            .truncate(true)
            .write(true)
            .open(&path)
            .with_context(|| format!("Could not open PID file {}", path.display()))?;
        file.write_all(&contents)
            .with_context(|| format!("Could not write PID file {}", path.display()))?;
        file.sync_all()
            .with_context(|| format!("Could not flush PID file {}", path.display()))?;
        Ok(Self { path, contents })
    }
}

impl Drop for PidFile {
    fn drop(&mut self) {
        let owned = fs::read(&self.path)
            .ok()
            .is_some_and(|contents| contents == self.contents);
        if owned {
            let _ = fs::remove_file(&self.path);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn version_banner_identifies_the_selected_node_executable() {
        assert_eq!(
            daemon_version_banner(env!("CARGO_BIN_NAME")),
            format!(
                "Bitcoin Core daemon version v31.1.0 {}\n",
                env!("CARGO_BIN_NAME")
            )
        );
    }

    #[test]
    fn pid_file_is_written_and_removed_by_owner() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("bitcoind.pid");
        {
            let pid_file = PidFile::create(path.clone()).unwrap();
            assert_eq!(
                fs::read_to_string(&path).unwrap(),
                format!("{}\n", std::process::id())
            );
            drop(pid_file);
        }
        assert!(!path.exists());
    }

    #[test]
    fn pid_file_does_not_remove_a_replacement() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("bitcoind.pid");
        let pid_file = PidFile::create(path.clone()).unwrap();
        fs::write(&path, b"replacement\n").unwrap();
        drop(pid_file);
        assert_eq!(fs::read_to_string(path).unwrap(), "replacement\n");
    }

    #[test]
    fn pid_file_rejects_empty_paths() {
        let error = PidFile::create(std::path::Path::new("").to_owned()).unwrap_err();
        assert!(error.to_string().contains("must not be empty"));
    }

    #[test]
    fn debug_log_reopens_after_rotation() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("debug.log");
        let rotated = directory.path().join("debug.log.1");
        let log_file = AsyncLogFile::open(&path, true).unwrap();
        let handle = log_file.handle();

        let mut writer = handle.make_writer();
        writer.write_all(b"before rotation\n").unwrap();
        writer.flush().unwrap();
        drop(writer);
        handle.flush().unwrap();

        fs::rename(&path, &rotated).unwrap();
        handle.reopen().unwrap();
        let mut writer = handle.make_writer();
        writer.write_all(b"after rotation\n").unwrap();
        writer.flush().unwrap();
        drop(writer);
        handle.flush().unwrap();

        assert_eq!(fs::read_to_string(rotated).unwrap(), "before rotation\n");
        assert_eq!(fs::read_to_string(path).unwrap(), "after rotation\n");
        log_file.shutdown();
    }

    #[test]
    fn debug_log_flushes_while_worker_is_idle() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("debug.log");
        let log_file = AsyncLogFile::open(&path, true).unwrap();
        let handle = log_file.handle();

        let mut writer = handle.make_writer();
        writer.write_all(b"visible during startup\n").unwrap();
        writer.flush().unwrap();
        drop(writer);

        let deadline = Instant::now() + Duration::from_secs(2);
        loop {
            if fs::read_to_string(&path)
                .unwrap()
                .contains("visible during startup")
            {
                break;
            }
            assert!(Instant::now() < deadline, "async log worker did not flush");
            thread::sleep(Duration::from_millis(20));
        }
        log_file.shutdown();
    }

    #[test]
    fn debug_log_flushes_while_worker_is_busy() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("debug.log");
        let log_file = AsyncLogFile::open(&path, true).unwrap();
        let handle = log_file.handle();
        let producer = thread::spawn(move || {
            for index in 0..600 {
                let mut writer = handle.make_writer();
                writeln!(writer, "busy record {index}").unwrap();
                writer.flush().unwrap();
                thread::sleep(Duration::from_millis(1));
            }
        });

        let deadline = Instant::now() + Duration::from_secs(2);
        loop {
            if fs::metadata(&path).unwrap().len() > 0 {
                break;
            }
            assert!(
                Instant::now() < deadline,
                "busy async log worker did not flush"
            );
            thread::sleep(Duration::from_millis(20));
        }
        producer.join().unwrap();
        log_file.shutdown();
    }

    #[test]
    fn log_rate_limiter_is_per_source_and_preserves_the_transition_record() {
        let limiter = LogRateLimiter::new();
        let first = LogSource::test("first");
        let second = LogSource::test("second");

        assert_eq!(
            limiter.consume(first.clone(), LOG_RATE_LIMIT_MAX_BYTES as usize),
            LogRateLimitDecision::Allowed {
                suppression_active: false
            }
        );
        assert_eq!(
            limiter.consume(first.clone(), 1),
            LogRateLimitDecision::NewlySuppressed
        );
        assert_eq!(limiter.consume(first, 1), LogRateLimitDecision::Suppressed);
        assert_eq!(
            limiter.consume(second, LOG_RATE_LIMIT_MAX_BYTES as usize),
            LogRateLimitDecision::Allowed {
                suppression_active: true
            }
        );
    }
}
