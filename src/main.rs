use std::fmt;
use std::fs::{self, OpenOptions};
use std::io::Write as _;
use std::path::PathBuf;

use anyhow::{Context, Result};
use time::{OffsetDateTime, macros::format_description};
use tracing_subscriber::EnvFilter;
use tracing_subscriber::fmt::{
    format::Writer,
    time::FormatTime,
    writer::{BoxMakeWriter, MakeWriterExt},
};

use bitcoind_rs::{
    Node,
    config::{Args, Config},
};

#[tokio::main]
async fn main() -> Result<()> {
    let config = Config::from_args(Args::parse_with_config()?)?;
    let node = Node::open(config)?;
    let _pid_file = PidFile::create(node.config.pid_path.clone())?;
    let filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info"));
    let writer = if let Some(path) = node
        .config
        .debug_log_file_enabled
        .then_some(&node.config.debug_log_path)
    {
        let mut options = OpenOptions::new();
        options.create(true).write(true);
        if node.config.shrink_debug_file {
            options.truncate(true);
        } else {
            options.append(true);
        }
        let file = options
            .open(path)
            .with_context(|| format!("Could not open debug log file {}", path.display()))?;
        if node.config.print_to_console {
            BoxMakeWriter::new(std::io::stdout.and(file))
        } else {
            BoxMakeWriter::new(file)
        }
    } else if node.config.print_to_console {
        BoxMakeWriter::new(std::io::stdout)
    } else {
        BoxMakeWriter::new(std::io::sink)
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
    node.run().await
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
}
