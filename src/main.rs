use std::collections::HashMap;
use std::ffi::CString;
use std::fmt;
use std::fs::{self, OpenOptions};
use std::io::{self, Write};
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
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
    config::{Args, Config, ConfigFileArg, is_known_config_option},
};

fn main() {
    // Match Core's private data-file default.  This must be set before any
    // configuration, directory, or log file is created so the process umask
    // also protects paths opened by the storage and RPC subsystems.
    #[cfg(unix)]
    unsafe {
        libc::umask(0o077);
    }
    if let Err(error) = run() {
        if error
            .downcast_ref::<bitcoind_rs::CoreStartupError>()
            .is_some()
        {
            eprintln!("{error}");
        } else {
            eprintln!("Error: {error}");
        }
        std::process::exit(1);
    }
}

fn run() -> Result<()> {
    let args = match Args::parse_with_config() {
        Ok(args) => args,
        Err(error) => {
            if let Some(clap_error) = error.downcast_ref::<clap::Error>()
                && matches!(
                    clap_error.kind(),
                    ClapErrorKind::DisplayHelp | ClapErrorKind::DisplayVersion
                )
            {
                clap_error.print()?;
                return Ok(());
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

async fn run_node(config: Config, mut readiness: DaemonReadyGuard) -> Result<()> {
    let node = Node::open(config)?;
    let _pid_file = PidFile::create(node.config.pid_path.clone())?;
    let filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new(node.config.logging.tracing_filter()));
    let (writer, log_file) = if let Some(path) = node
        .config
        .debug_log_file_enabled
        .then_some(&node.config.debug_log_path)
    {
        let log_file = ReloadableLogFile::open(path, node.config.shrink_debug_file)
            .with_context(|| format!("Could not open debug log file {}", path.display()))?;
        let log_file_for_signal = log_file.clone();
        if node.config.print_to_console {
            let writer = if node.config.logging.log_rate_limit {
                BoxMakeWriter::new(std::io::stdout.and(RateLimitedLogFile::new(log_file.clone())))
            } else {
                BoxMakeWriter::new(std::io::stdout.and(log_file.clone()))
            };
            (writer, Some(log_file_for_signal))
        } else {
            let writer = if node.config.logging.log_rate_limit {
                BoxMakeWriter::new(RateLimitedLogFile::new(log_file.clone()))
            } else {
                BoxMakeWriter::new(log_file.clone())
            };
            (writer, Some(log_file_for_signal))
        }
    } else if node.config.print_to_console {
        (BoxMakeWriter::new(std::io::stdout), None)
    } else {
        (BoxMakeWriter::new(std::io::sink), None)
    };
    let builder = tracing_subscriber::fmt()
        .with_env_filter(filter)
        .with_target(false)
        .with_ansi(false)
        .with_writer(writer)
        .with_level(node.config.logging.level_always)
        .with_thread_names(node.config.logging.thread_names)
        .with_file(node.config.logging.source_locations)
        .with_line_number(node.config.logging.source_locations);
    if !node.config.logging.timestamps {
        builder.without_time().init();
    } else if node.config.logging.time_micros {
        builder
            .with_timer(CoreLogTimer { microseconds: true })
            .init();
    } else {
        builder.init();
    }
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
    let log_reopen_task = log_file.map(|log_file| tokio::spawn(reopen_log_on_sighup(log_file)));
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
    result
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

#[derive(Clone)]
struct ReloadableLogFile {
    path: PathBuf,
    file: Arc<Mutex<std::fs::File>>,
}

impl ReloadableLogFile {
    fn open(path: &std::path::Path, shrink: bool) -> io::Result<Self> {
        let mut options = OpenOptions::new();
        options.create(true).write(true);
        if shrink {
            options.truncate(true);
        } else {
            options.append(true);
        }
        let file = options.open(path)?;
        Ok(Self {
            path: path.to_owned(),
            file: Arc::new(Mutex::new(file)),
        })
    }

    fn reopen(&self) -> io::Result<()> {
        let file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.path)?;
        let mut current = self
            .file
            .lock()
            .map_err(|_| io::Error::other("debug log lock poisoned"))?;
        *current = file;
        Ok(())
    }
}

struct ReloadableLogWriter {
    file: Arc<Mutex<std::fs::File>>,
    buffer: Vec<u8>,
}

impl Write for ReloadableLogWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.buffer.extend_from_slice(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        if self.buffer.is_empty() {
            return Ok(());
        }
        let mut file = self
            .file
            .lock()
            .map_err(|_| io::Error::other("debug log lock poisoned"))?;
        file.write_all(&self.buffer)?;
        file.flush()?;
        self.buffer.clear();
        Ok(())
    }
}

impl Drop for ReloadableLogWriter {
    fn drop(&mut self) {
        let _ = self.flush();
    }
}

impl<'a> MakeWriter<'a> for ReloadableLogFile {
    type Writer = ReloadableLogWriter;

    fn make_writer(&'a self) -> Self::Writer {
        ReloadableLogWriter {
            file: self.file.clone(),
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
    file: ReloadableLogFile,
    limiter: Arc<LogRateLimiter>,
}

impl RateLimitedLogFile {
    fn new(file: ReloadableLogFile) -> Self {
        Self {
            file,
            limiter: Arc::new(LogRateLimiter::new()),
        }
    }
}

struct RateLimitedLogWriter {
    inner: ReloadableLogWriter,
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
async fn reopen_log_on_sighup(log_file: ReloadableLogFile) {
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
        let log_file = ReloadableLogFile::open(&path, true).unwrap();

        let mut writer = log_file.make_writer();
        writer.write_all(b"before rotation\n").unwrap();
        writer.flush().unwrap();
        drop(writer);

        fs::rename(&path, &rotated).unwrap();
        log_file.reopen().unwrap();
        let mut writer = log_file.make_writer();
        writer.write_all(b"after rotation\n").unwrap();
        writer.flush().unwrap();

        assert_eq!(fs::read_to_string(rotated).unwrap(), "before rotation\n");
        assert_eq!(fs::read_to_string(path).unwrap(), "after rotation\n");
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
