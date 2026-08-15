use anyhow::Result;
use tracing_subscriber::EnvFilter;

use bitcoind_rs::{
    Node,
    config::{Args, Config},
};

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter(
            EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info")),
        )
        .with_target(false)
        .init();

    let config = Config::from_args(Args::parse_with_config()?)?;
    Node::open(config)?.run().await
}
