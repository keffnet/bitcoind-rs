use std::ffi::CString;
use std::fmt;
use std::fs::{self, OpenOptions};
use std::io::{self, Write};
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

#[cfg(not(unix))]
use anyhow::bail;
use anyhow::{Context, Result};
use time::{OffsetDateTime, macros::format_description};
use tracing_subscriber::EnvFilter;
use tracing_subscriber::fmt::{
    format::Writer,
    time::FormatTime,
    writer::{BoxMakeWriter, MakeWriter, MakeWriterExt},
};

use bitcoind_rs::{
    Node,
    config::{Args, Config},
};

fn main() -> Result<()> {
    let args = Args::parse_with_config()?;
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
    runtime.block_on(run_node(config, readiness))
}

async fn run_node(config: Config, mut readiness: DaemonReadyGuard) -> Result<()> {
    let node = Node::open(config)?;
    let _pid_file = PidFile::create(node.config.pid_path.clone())?;
    let filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info"));
    let (writer, log_file) = if let Some(path) = node
        .config
        .debug_log_file_enabled
        .then_some(&node.config.debug_log_path)
    {
        let log_file = ReloadableLogFile::open(path, node.config.shrink_debug_file)
            .with_context(|| format!("Could not open debug log file {}", path.display()))?;
        let log_file_for_signal = log_file.clone();
        if node.config.print_to_console {
            (
                BoxMakeWriter::new(std::io::stdout.and(log_file)),
                Some(log_file_for_signal),
            )
        } else {
            (BoxMakeWriter::new(log_file), Some(log_file_for_signal))
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
}
