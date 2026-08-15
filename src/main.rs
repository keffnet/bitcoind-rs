use std::fs::OpenOptions;

use anyhow::{Context, Result};
use tracing_subscriber::EnvFilter;
use tracing_subscriber::fmt::writer::MakeWriterExt;

use bitcoind_rs::{
    Node,
    config::{Args, Config},
};

#[tokio::main]
async fn main() -> Result<()> {
    let config = Config::from_args(Args::parse_with_config()?)?;
    let node = Node::open(config)?;
    let filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info"));
    if let Some(path) = node
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
            tracing_subscriber::fmt()
                .with_env_filter(filter)
                .with_target(false)
                .with_writer(std::io::stdout.and(file))
                .init();
        } else {
            tracing_subscriber::fmt()
                .with_env_filter(filter)
                .with_target(false)
                .with_writer(file)
                .init();
        }
    } else if node.config.print_to_console {
        tracing_subscriber::fmt()
            .with_env_filter(filter)
            .with_target(false)
            .init();
    } else {
        tracing_subscriber::fmt()
            .with_env_filter(filter)
            .with_target(false)
            .with_writer(std::io::sink)
            .init();
    }
    node.run().await
}
