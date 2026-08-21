//! Electrs-compatible Prometheus monitoring.

use std::sync::Arc;
use std::time::Duration;

use anyhow::{Context, Result};
use prometheus::{
    Encoder, GaugeVec, HistogramOpts, HistogramTimer, HistogramVec, Opts, Registry, TEXT_FORMAT,
    TextEncoder,
};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};
use tracing::{debug, info};

use crate::mempool::Mempool;
use crate::{Node, StartupLatch};

const MEMPOOL_FEE_BINS: usize = 65;
const MAX_MONITORING_REQUEST_BYTES: usize = 16 * 1024;

fn duration_buckets() -> Vec<f64> {
    vec![
        1e-6, 2e-6, 5e-6, 1e-5, 2e-5, 5e-5, 1e-4, 2e-4, 5e-4, 1e-3, 2e-3, 5e-3, 1e-2, 2e-2, 5e-2,
        1e-1, 2e-1, 5e-1, 1.0, 2.0, 5.0, 10.0, 20.0, 50.0, 100.0,
    ]
}

fn size_buckets() -> Vec<f64> {
    vec![
        1.0, 2.0, 5.0, 1e1, 2e1, 5e1, 1e2, 2e2, 5e2, 1e3, 2e3, 5e3, 1e4, 2e4, 5e4, 1e5, 2e5, 5e5,
        1e6, 2e6, 5e6, 1e7,
    ]
}

/// Metric families exported by electrs' default `metrics` feature.
pub(crate) struct ElectrumMetrics {
    registry: Registry,
    rpc_duration: HistogramVec,
    server_batch_size: HistogramVec,
    server_loop_duration: HistogramVec,
    mempool_txs_vsize: GaugeVec,
    mempool_txs_count: GaugeVec,
}

impl ElectrumMetrics {
    pub(crate) fn new() -> Result<Self> {
        let registry = Registry::new();
        let rpc_duration = HistogramVec::new(
            HistogramOpts::new("electrs_rpc_duration", "RPC duration (in seconds)")
                .buckets(duration_buckets()),
            &["method"],
        )?;
        let server_batch_size = HistogramVec::new(
            HistogramOpts::new(
                "electrs_server_batch_size",
                "# of server events handled in a single batch",
            )
            .buckets(size_buckets()),
            &["type"],
        )?;
        let server_loop_duration = HistogramVec::new(
            HistogramOpts::new("electrs_server_loop_duration", "server loop duration")
                .buckets(duration_buckets()),
            &["step"],
        )?;
        let mempool_txs_vsize = GaugeVec::new(
            Opts::new(
                "electrs_mempool_txs_vsize",
                "Total vsize of mempool transactions (in bytes)",
            ),
            &["fee_rate"],
        )?;
        let mempool_txs_count = GaugeVec::new(
            Opts::new(
                "electrs_mempool_txs_count",
                "Total number of mempool transactions",
            ),
            &["fee_rate"],
        )?;

        for collector in [
            Box::new(rpc_duration.clone()) as Box<dyn prometheus::core::Collector>,
            Box::new(server_batch_size.clone()),
            Box::new(server_loop_duration.clone()),
            Box::new(mempool_txs_vsize.clone()),
            Box::new(mempool_txs_count.clone()),
        ] {
            registry.register(collector)?;
        }

        Ok(Self {
            registry,
            rpc_duration,
            server_batch_size,
            server_loop_duration,
            mempool_txs_vsize,
            mempool_txs_count,
        })
    }

    pub(crate) fn rpc_timer(&self, method: &str) -> HistogramTimer {
        self.rpc_duration.with_label_values(&[method]).start_timer()
    }

    pub(crate) fn observe_rpc_duration(&self, method: &str, duration: Duration) {
        self.rpc_duration
            .with_label_values(&[method])
            .observe(duration.as_secs_f64());
    }

    pub(crate) fn server_loop_timer(&self, step: &str) -> HistogramTimer {
        self.server_loop_duration
            .with_label_values(&[step])
            .start_timer()
    }

    pub(crate) fn observe_server_batch_size(&self, event_type: &str, size: usize) {
        self.server_batch_size
            .with_label_values(&[event_type])
            .observe(size as f64);
    }

    fn refresh_mempool_metrics(&self, mempool: &Mempool) {
        let mut vsize = [0u64; MEMPOOL_FEE_BINS];
        let mut count = [0u64; MEMPOOL_FEE_BINS];
        for entry in mempool.iter_entries() {
            let fee_rate = entry.fee_sat / entry.vsize.max(1);
            let bin = usize::try_from(fee_rate.leading_zeros()).unwrap_or(MEMPOOL_FEE_BINS - 1);
            if let (Some(vsize), Some(count)) = (vsize.get_mut(bin), count.get_mut(bin)) {
                *vsize = vsize.saturating_add(entry.vsize);
                *count = count.saturating_add(1);
            }
        }

        for bin in (0..MEMPOOL_FEE_BINS).rev() {
            let upper = 1u128 << (MEMPOOL_FEE_BINS - bin - 1);
            let label = format!("[{:20.0}, {:20.0})", upper / 2, upper);
            self.mempool_txs_vsize
                .with_label_values(&[&label])
                .set(vsize[bin] as f64);
            self.mempool_txs_count
                .with_label_values(&[&label])
                .set(count[bin] as f64);
        }
    }

    fn encode(&self, mempool: &Mempool) -> Result<Vec<u8>> {
        self.refresh_mempool_metrics(mempool);
        let mut body = Vec::new();
        TextEncoder::new()
            .encode(&self.registry.gather(), &mut body)
            .context("encoding Prometheus metrics")?;
        Ok(body)
    }
}

pub(crate) struct MonitoringServer {
    node: Arc<Node>,
}

impl MonitoringServer {
    pub(crate) fn new(node: Arc<Node>) -> Self {
        Self { node }
    }

    pub(crate) async fn run_with_startup(self, startup: Option<Arc<StartupLatch>>) -> Result<()> {
        let Some(address) = self.node.config.electrum_monitoring_bind() else {
            return std::future::pending::<Result<()>>().await;
        };
        let listener = TcpListener::bind(address)
            .await
            .with_context(|| format!("binding Electrum monitoring listener {address}"))?;
        let local_address = listener.local_addr()?;
        info!(address = %local_address, "serving Prometheus metrics");
        if let Some(startup) = startup.as_deref() {
            startup.service_ready();
        }

        loop {
            let (stream, peer) = tokio::select! {
                result = listener.accept() => result?,
                _ = self.node.wait_for_shutdown() => return Ok(()),
            };
            let node = self.node.clone();
            tokio::spawn(async move {
                if let Err(error) = serve_monitoring_client(node, stream).await {
                    debug!(%peer, %error, "monitoring connection ended");
                }
            });
        }
    }
}

async fn serve_monitoring_client(node: Arc<Node>, mut stream: TcpStream) -> Result<()> {
    let mut request = Vec::new();
    loop {
        let mut buffer = [0u8; 1_024];
        let bytes = stream.read(&mut buffer).await?;
        if bytes == 0 {
            return Ok(());
        }
        request.extend_from_slice(&buffer[..bytes]);
        if request.len() > MAX_MONITORING_REQUEST_BYTES {
            stream
                .write_all(&http_response("413 Payload Too Large", "text/plain", b""))
                .await?;
            return Ok(());
        }
        if request.windows(4).any(|window| window == b"\r\n\r\n") {
            break;
        }
    }

    let body = {
        let mempool = node.mempool.read();
        node.electrum_metrics.encode(&mempool)?
    };
    stream
        .write_all(&http_response("200 OK", TEXT_FORMAT, &body))
        .await?;
    stream.shutdown().await?;
    Ok(())
}

fn http_response(status: &str, content_type: &str, body: &[u8]) -> Vec<u8> {
    let header = format!(
        "HTTP/1.1 {status}\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        body.len()
    );
    let mut response = Vec::with_capacity(header.len() + body.len());
    response.extend_from_slice(header.as_bytes());
    response.extend_from_slice(body);
    response
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::Network;

    #[test]
    fn exports_electrs_metric_families_and_labels() {
        let metrics = ElectrumMetrics::new().unwrap();
        metrics.observe_server_batch_size("recv", 3);
        drop(metrics.rpc_timer("server.ping"));
        drop(metrics.server_loop_timer("handle"));
        let body =
            String::from_utf8(metrics.encode(&Mempool::new(Network::Regtest)).unwrap()).unwrap();

        assert!(body.contains("electrs_rpc_duration_bucket{method=\"server.ping\""));
        assert!(body.contains("electrs_server_batch_size_bucket{type=\"recv\""));
        assert!(body.contains("electrs_server_loop_duration_bucket{step=\"handle\""));
        assert!(body.contains("electrs_mempool_txs_vsize{fee_rate="));
        assert!(body.contains("electrs_mempool_txs_count{fee_rate="));
    }

    #[test]
    fn monitoring_http_response_is_prometheus_scrapeable() {
        let response = http_response("200 OK", TEXT_FORMAT, b"metric 1\n");
        let response = String::from_utf8(response).unwrap();
        assert!(response.starts_with("HTTP/1.1 200 OK\r\n"));
        assert!(response.contains(&format!("Content-Type: {TEXT_FORMAT}\r\n")));
        assert!(response.contains("Content-Length: 9\r\n"));
        assert!(response.ends_with("\r\n\r\nmetric 1\n"));
    }
}
