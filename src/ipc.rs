//! Bitcoin Core v31.1-compatible local IPC transport.
//!
//! Core's multiprocess interface is a Cap'n Proto two-party RPC service over
//! Unix sockets.  Keep the transport isolated here so the ordinary JSON-RPC,
//! Electrum, and P2P services do not need to know about Cap'n Proto details.

use std::path::{Path, PathBuf};
#[cfg(unix)]
use std::process::Command;
use std::sync::{
    Arc,
    atomic::{AtomicBool, AtomicU64, Ordering},
};
use std::time::Duration;

use anyhow::{Context, Result, bail};
use bitcoin::consensus::encode::{deserialize, serialize};
use bitcoin::hashes::{Hash as _, HashEngine as _};
use bitcoin::{Block, BlockHash, Transaction};
use capnp::capability::Rc;
use capnp::message::ReaderOptions;
use capnp_rpc::rpc_twoparty_capnp::Side;
use capnp_rpc::twoparty::VatNetwork;
use capnp_rpc::{RpcSystem, new_client};
use futures::io::{BufReader, BufWriter};
use parking_lot::Mutex;
use tokio::net::{UnixListener, UnixStream};
use tokio::sync::Notify;
use tokio_util::compat::{TokioAsyncReadCompatExt, TokioAsyncWriteCompatExt};
use tracing::{debug, warn};

#[cfg(unix)]
use std::os::unix::fs::FileTypeExt;
#[cfg(unix)]
use std::os::unix::io::{AsRawFd, FromRawFd, OwnedFd, RawFd};

use crate::Node;
use crate::config::network_data_dir_name;

const DEFAULT_SOCKET_NAME: &str = "node.sock";
const MAX_UNIX_SOCKET_PATH: usize = 107;

#[cfg(unix)]
fn set_close_on_exec(fd: RawFd, close_on_exec: bool) -> Result<()> {
    // SAFETY: F_GETFD and F_SETFD only inspect/update descriptor flags and do
    // not retain pointers. The descriptor comes from socketpair or the
    // process command line and is validated by the syscall result.
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
    if flags == -1 {
        return Err(std::io::Error::last_os_error()).context("reading IPC descriptor flags");
    }
    let flags = if close_on_exec {
        flags | libc::FD_CLOEXEC
    } else {
        flags & !libc::FD_CLOEXEC
    };
    // SAFETY: The descriptor was validated above and F_SETFD takes an integer
    // flag value without retaining any borrowed memory.
    if unsafe { libc::fcntl(fd, libc::F_SETFD, flags) } == -1 {
        return Err(std::io::Error::last_os_error()).context("setting IPC descriptor flags");
    }
    Ok(())
}

#[cfg(unix)]
fn validate_stream_socket_fd(fd: RawFd) -> Result<()> {
    if fd < 0 {
        bail!("IPC file descriptor must be non-negative");
    }
    let mut socket_type = 0i32;
    let mut length = std::mem::size_of_val(&socket_type) as libc::socklen_t;
    // SAFETY: socket_type and length point to initialized writable storage for
    // getsockopt, and the syscall does not retain either pointer.
    let result = unsafe {
        libc::getsockopt(
            fd,
            libc::SOL_SOCKET,
            libc::SO_TYPE,
            (&raw mut socket_type).cast(),
            &raw mut length,
        )
    };
    if result == -1 {
        return Err(std::io::Error::last_os_error()).context("validating IPC file descriptor");
    }
    if socket_type != libc::SOCK_STREAM {
        bail!("IPC file descriptor is not a stream socket");
    }
    let mut address: libc::sockaddr_storage = unsafe { std::mem::zeroed() };
    let mut address_length = std::mem::size_of_val(&address) as libc::socklen_t;
    // SAFETY: address and address_length provide initialized writable storage
    // large enough for any socket address and are not retained by getsockname.
    if unsafe { libc::getsockname(fd, (&raw mut address).cast(), &raw mut address_length) } == -1 {
        return Err(std::io::Error::last_os_error()).context("reading IPC socket family");
    }
    if i32::from(address.ss_family) != libc::AF_UNIX {
        bail!("IPC file descriptor is not a Unix-domain socket");
    }
    Ok(())
}

/// Serve Core's internal `bitcoin-node -ipcfd N` socketpair mode until the
/// controlling process closes its endpoint.
#[cfg(unix)]
pub(crate) fn run_spawned_process(fd: RawFd) -> Result<()> {
    validate_stream_socket_fd(fd)?;
    // SAFETY: validate_stream_socket_fd established that fd is an owned stream
    // socket inherited specifically for this child process. From this point
    // the standard UnixStream is responsible for closing it exactly once.
    let stream = unsafe { std::os::unix::net::UnixStream::from_raw_fd(fd) };
    stream
        .set_nonblocking(true)
        .context("configuring spawned IPC socket")?;
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .context("creating spawned IPC runtime")?;
    runtime.block_on(tokio::task::LocalSet::new().run_until(async move {
        let stream = UnixStream::from_std(stream).context("adopting spawned IPC socket")?;
        serve_connection_with_node(stream, None).await
    }))
}

#[cfg(unix)]
fn create_ipc_socket_pair() -> Result<(OwnedFd, OwnedFd)> {
    let mut descriptors = [-1; 2];
    // SAFETY: descriptors points to storage for exactly two file descriptors;
    // socketpair initializes both entries or returns an error.
    if unsafe {
        libc::socketpair(
            libc::AF_UNIX,
            libc::SOCK_STREAM,
            0,
            descriptors.as_mut_ptr(),
        )
    } == -1
    {
        return Err(std::io::Error::last_os_error()).context("creating IPC socket pair");
    }
    // SAFETY: socketpair succeeded, so both descriptors are fresh and owned by
    // this process. OwnedFd takes responsibility for closing each exactly once.
    let parent = unsafe { OwnedFd::from_raw_fd(descriptors[0]) };
    // SAFETY: See the ownership argument above for the second fresh descriptor.
    let child = unsafe { OwnedFd::from_raw_fd(descriptors[1]) };
    set_close_on_exec(parent.as_raw_fd(), true)?;
    set_close_on_exec(child.as_raw_fd(), false)?;
    Ok((parent, child))
}

#[cfg(unix)]
fn bitcoin_node_executable() -> Result<PathBuf> {
    let current = std::env::current_exe().context("locating current executable")?;
    if current.file_name().and_then(|name| name.to_str()) == Some("bitcoin-node") {
        return Ok(current);
    }
    let candidate = current
        .parent()
        .map(|parent| parent.join("bitcoin-node"))
        .unwrap_or_else(|| PathBuf::from("bitcoin-node"));
    Ok(candidate)
}

#[cfg(unix)]
pub(crate) fn current_process_is_bitcoin_node() -> bool {
    std::env::current_exe()
        .ok()
        .and_then(|path| path.file_name().map(|name| name == "bitcoin-node"))
        .unwrap_or(false)
}

/// Match Core's test-only `echoipc` behavior by passing the value through a
/// newly spawned bitcoin-node process over an inherited socketpair.
#[cfg(unix)]
pub(crate) fn echo_through_spawned_process(value: &str) -> Result<String> {
    let (parent_fd, child_fd) = create_ipc_socket_pair()?;
    let mut child = Command::new(bitcoin_node_executable()?)
        .arg("-ipcfd")
        .arg(child_fd.as_raw_fd().to_string())
        .spawn()
        .context("spawning bitcoin-node IPC process")?;
    drop(child_fd);

    // Once the child exists, always close our endpoint and reap it, including
    // local runtime/setup failures, so echoipc cannot accumulate zombies.
    let result = (|| -> Result<String> {
        let stream = std::os::unix::net::UnixStream::from(parent_fd);
        stream
            .set_nonblocking(true)
            .context("configuring parent IPC socket")?;
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .context("creating parent IPC runtime")?;
        runtime.block_on(tokio::task::LocalSet::new().run_until(async move {
            let stream = UnixStream::from_std(stream).context("adopting parent IPC socket")?;
            echo_over_ipc_stream(stream, value).await
        }))
    })();

    let status = child.wait().context("waiting for spawned bitcoin-node")?;
    if result.is_ok() && !status.success() {
        bail!("spawned bitcoin-node exited with status {status}");
    }
    result
}

#[cfg(unix)]
async fn echo_over_ipc_stream(stream: UnixStream, value: &str) -> Result<String> {
    let (reader, writer) = stream.into_split();
    let network = VatNetwork::new(
        BufReader::new(reader.compat()),
        BufWriter::new(writer.compat_write()),
        Side::Client,
        ReaderOptions::new(),
    );
    let mut rpc_system = RpcSystem::new(Box::new(network), None);
    let init: crate::init_capnp::init::Client = rpc_system.bootstrap(Side::Server);
    let rpc_task = tokio::task::spawn_local(rpc_system);
    let echo_response = init
        .make_echo_request()
        .send()
        .promise
        .await
        .context("requesting spawned echo interface")?;
    let echo = echo_response
        .get()
        .context("reading spawned echo interface")?
        .get_result()
        .context("accessing spawned echo interface")?;
    let mut request = echo.echo_request();
    request.get().set_echo(value);
    let response = request
        .send()
        .promise
        .await
        .context("calling spawned echo interface")?;
    let output = response
        .get()
        .context("reading spawned echo response")?
        .get_result()
        .context("accessing spawned echo response")?
        .to_str()
        .context("decoding spawned echo response")?
        .to_owned();
    rpc_task.abort();
    Ok(output)
}

#[derive(Clone, Default)]
struct InterruptHandle {
    generation: Arc<AtomicU64>,
    pending: Arc<AtomicBool>,
    notify: Arc<Notify>,
}

impl InterruptHandle {
    fn generation(&self) -> u64 {
        self.generation.load(Ordering::Acquire)
    }

    fn begin(&self) -> (u64, bool) {
        (
            self.generation(),
            self.pending.swap(false, Ordering::AcqRel),
        )
    }

    fn interrupt(&self) {
        self.pending.store(true, Ordering::Release);
        self.generation.fetch_add(1, Ordering::AcqRel);
        self.notify.notify_waiters();
    }

    fn was_interrupted(&self, generation: u64) -> bool {
        let interrupted = self.generation() != generation;
        if interrupted {
            self.pending.store(false, Ordering::Release);
        }
        interrupted
    }
}

struct ThreadMapService;

impl crate::proxy_capnp::thread_map::Server for ThreadMapService {
    async fn make_thread(
        self: Rc<Self>,
        params: crate::proxy_capnp::thread_map::MakeThreadParams,
        mut results: crate::proxy_capnp::thread_map::MakeThreadResults,
    ) -> Result<(), capnp::Error> {
        let name = params
            .get()
            .and_then(|params| params.get_name())?
            .to_str()?
            .to_owned();
        results.get().set_result(new_client(ThreadService { name }));
        Ok(())
    }
}

struct ThreadService {
    name: String,
}

impl crate::proxy_capnp::thread::Server for ThreadService {
    async fn get_name(
        self: Rc<Self>,
        _params: crate::proxy_capnp::thread::GetNameParams,
        mut results: crate::proxy_capnp::thread::GetNameResults,
    ) -> Result<(), capnp::Error> {
        results.get().set_result(&self.name);
        Ok(())
    }
}

struct EchoService;

impl crate::echo_capnp::echo::Server for EchoService {
    async fn destroy(
        self: Rc<Self>,
        _params: crate::echo_capnp::echo::DestroyParams,
        _results: crate::echo_capnp::echo::DestroyResults,
    ) -> Result<(), capnp::Error> {
        Ok(())
    }

    async fn echo(
        self: Rc<Self>,
        params: crate::echo_capnp::echo::EchoParams,
        mut results: crate::echo_capnp::echo::EchoResults,
    ) -> Result<(), capnp::Error> {
        let value = params
            .get()
            .and_then(|params| params.get_echo())?
            .to_str()?
            .to_owned();
        results.get().set_result(value);
        Ok(())
    }
}

struct InitService {
    node: Option<Arc<Node>>,
}

impl crate::init_capnp::init::Server for InitService {
    async fn construct(
        self: Rc<Self>,
        _params: crate::init_capnp::init::ConstructParams,
        mut results: crate::init_capnp::init::ConstructResults,
    ) -> Result<(), capnp::Error> {
        results.get().set_thread_map(new_client(ThreadMapService));
        Ok(())
    }

    async fn make_echo(
        self: Rc<Self>,
        _params: crate::init_capnp::init::MakeEchoParams,
        mut results: crate::init_capnp::init::MakeEchoResults,
    ) -> Result<(), capnp::Error> {
        results.get().set_result(new_client(EchoService));
        Ok(())
    }

    async fn make_mining_old2(
        self: Rc<Self>,
        _params: crate::init_capnp::init::MakeMiningOld2Params,
        _results: crate::init_capnp::init::MakeMiningOld2Results,
    ) -> Result<(), capnp::Error> {
        Err(capnp::Error::failed(
            "std::exception: Old mining interface (@2) not supported. Please update your client!"
                .to_owned(),
        ))
    }

    async fn make_mining(
        self: Rc<Self>,
        _params: crate::init_capnp::init::MakeMiningParams,
        mut results: crate::init_capnp::init::MakeMiningResults,
    ) -> Result<(), capnp::Error> {
        let node = self.node.clone().ok_or_else(|| {
            capnp::Error::failed("mining is unavailable in a spawned echo process".to_owned())
        })?;
        results.get().set_result(new_client(MiningService {
            node,
            interrupt: InterruptHandle::default(),
        }));
        Ok(())
    }
}

struct MiningService {
    node: Arc<Node>,
    interrupt: InterruptHandle,
}

struct BlockTemplateData {
    template: crate::rpc::IpcBlockTemplate,
}

struct BlockTemplateService {
    node: Arc<Node>,
    data: Arc<Mutex<BlockTemplateData>>,
    options: crate::rpc::IpcBlockCreateOptions,
    interrupt: InterruptHandle,
}

struct WaitNextCancellationGuard {
    node: Arc<Node>,
    completed: bool,
}

impl WaitNextCancellationGuard {
    fn new(node: Arc<Node>) -> Self {
        Self {
            node,
            completed: false,
        }
    }

    fn complete(&mut self) {
        self.completed = true;
    }
}

impl Drop for WaitNextCancellationGuard {
    fn drop(&mut self) {
        if !self.completed {
            debug!("IPC server: socket disconnected");
            debug!("IPC server request canceled while executing");
            self.node.note_ipc_wait_cancellation();
        }
    }
}

fn set_block_ref(
    mut builder: crate::common_capnp::block_ref::Builder<'_>,
    hash: &[u8],
    height: u32,
) {
    let data = builder.reborrow().init_hash(hash.len() as u32);
    data.copy_from_slice(hash);
    builder.set_height(i32::try_from(height).unwrap_or(i32::MAX));
}

fn set_empty_block_ref(mut builder: crate::common_capnp::block_ref::Builder<'_>) {
    builder.set_height(-1);
}

fn timeout_duration(milliseconds: f64) -> Option<std::time::Duration> {
    if !milliseconds.is_finite() || milliseconds >= 100.0 * 365.0 * 24.0 * 60.0 * 60.0 * 1_000.0 {
        return None;
    }
    Some(std::time::Duration::from_secs_f64(
        milliseconds.max(0.0) / 1_000.0,
    ))
}

fn set_data(builder: capnp::data::Builder<'_>, value: &[u8]) {
    builder.copy_from_slice(value);
}

fn ipc_block_create_options(
    options: crate::mining_capnp::block_create_options::Reader<'_>,
) -> crate::rpc::IpcBlockCreateOptions {
    crate::rpc::IpcBlockCreateOptions {
        use_mempool: options.get_use_mempool(),
        block_reserved_weight: options.get_block_reserved_weight(),
        coinbase_output_max_additional_sigops: options.get_coinbase_output_max_additional_sigops(),
    }
}

fn block_template_client(
    node: Arc<Node>,
    template: crate::rpc::IpcBlockTemplate,
    options: crate::rpc::IpcBlockCreateOptions,
) -> crate::mining_capnp::block_template::Client {
    new_client(BlockTemplateService {
        node,
        data: Arc::new(Mutex::new(BlockTemplateData { template })),
        options,
        interrupt: InterruptHandle::default(),
    })
}

fn ipc_template_tip_requires_refresh(node: &Node, previous: BlockHash) -> bool {
    let chain = node.chain.read();
    if chain.best_hash() != previous {
        return true;
    }
    if !chain.network.params().allow_min_difficulty_blocks {
        return false;
    }
    let Some(tip_header) = chain.header(chain.height()) else {
        return false;
    };
    crate::time::unix_time() > u64::from(tip_header.time).saturating_add(20 * 60)
}

fn coinbase_merkle_path(block: &Block) -> Vec<[u8; 32]> {
    let mut layer = block
        .txdata
        .iter()
        .map(|transaction| transaction.compute_txid().to_byte_array())
        .collect::<Vec<_>>();
    let mut index = 0usize;
    let mut path = Vec::new();
    while layer.len() > 1 {
        let sibling = if index ^ 1 < layer.len() {
            index ^ 1
        } else {
            index
        };
        path.push(layer[sibling]);
        let mut next = Vec::with_capacity(layer.len().div_ceil(2));
        for pair in layer.chunks(2) {
            let right = *pair.get(1).unwrap_or(&pair[0]);
            let mut engine = bitcoin::hashes::sha256d::Hash::engine();
            engine.input(&pair[0]);
            engine.input(&right);
            next.push(bitcoin::hashes::sha256d::Hash::from_engine(engine).to_byte_array());
        }
        layer = next;
        index /= 2;
    }
    path
}

struct CoinbaseFields {
    version: u32,
    sequence: u32,
    script_sig_prefix: Vec<u8>,
    witness: Option<Vec<u8>>,
    reward: i64,
    required_outputs: Vec<Vec<u8>>,
    lock_time: u32,
}

fn block_template_coinbase(template: &crate::rpc::IpcBlockTemplate) -> Option<CoinbaseFields> {
    let coinbase = template.block.txdata.first()?;
    let input = coinbase.input.first()?;
    let witness = input
        .witness
        .iter()
        .next()
        .filter(|value| value.len() == 32)
        .map(|value| value.to_vec());
    let required_outputs = coinbase
        .output
        .iter()
        .skip(1)
        .map(serialize)
        .collect::<Vec<_>>();
    let reward = coinbase
        .output
        .first()
        .map(|output| i64::try_from(output.value.to_sat()).unwrap_or(i64::MAX))?;
    Some(CoinbaseFields {
        version: coinbase.version.0 as u32,
        sequence: input.sequence.to_consensus_u32(),
        script_sig_prefix: input.script_sig.as_bytes().to_vec(),
        witness,
        reward,
        required_outputs,
        lock_time: coinbase.lock_time.to_consensus_u32(),
    })
}

impl crate::mining_capnp::mining::Server for MiningService {
    async fn is_test_chain(
        self: Rc<Self>,
        _params: crate::mining_capnp::mining::IsTestChainParams,
        mut results: crate::mining_capnp::mining::IsTestChainResults,
    ) -> Result<(), capnp::Error> {
        results.get().set_result(!matches!(
            self.node.config.network,
            bitcoin::Network::Bitcoin
        ));
        Ok(())
    }

    async fn is_initial_block_download(
        self: Rc<Self>,
        _params: crate::mining_capnp::mining::IsInitialBlockDownloadParams,
        mut results: crate::mining_capnp::mining::IsInitialBlockDownloadResults,
    ) -> Result<(), capnp::Error> {
        results
            .get()
            .set_result(self.node.chain.read().is_initial_block_download());
        Ok(())
    }

    async fn get_tip(
        self: Rc<Self>,
        _params: crate::mining_capnp::mining::GetTipParams,
        mut results: crate::mining_capnp::mining::GetTipResults,
    ) -> Result<(), capnp::Error> {
        let tip = self.node.chain.read().tip();
        let mut output = results.get();
        output.set_has_result(true);
        set_block_ref(output.init_result(), tip.hash.as_byte_array(), tip.height);
        Ok(())
    }

    async fn wait_tip_changed(
        self: Rc<Self>,
        params: crate::mining_capnp::mining::WaitTipChangedParams,
        mut results: crate::mining_capnp::mining::WaitTipChangedResults,
    ) -> Result<(), capnp::Error> {
        debug!("Mining.waitTipChanged");
        let params = params.get()?;
        let current_tip = params.get_current_tip()?.to_vec();
        let timeout = timeout_duration(params.get_timeout());
        let mut chain_events = self.node.subscribe_chain();
        let (interrupt_generation, interrupted_before_wait) = self.interrupt.begin();

        if interrupted_before_wait {
            set_empty_block_ref(results.get().init_result());
            return Ok(());
        }

        let current_hash = bitcoin::BlockHash::from_slice(&current_tip).ok();
        let already_changed = {
            let tip = self.node.chain.read().tip();
            current_hash != Some(tip.hash)
        };

        let outcome = if already_changed {
            WaitTipOutcome::Tip(self.node.chain.read().tip())
        } else {
            let wait = async {
                loop {
                    if self.interrupt.was_interrupted(interrupt_generation) {
                        return WaitTipOutcome::Interrupted;
                    }
                    tokio::select! {
                        _ = self.node.wait_for_shutdown() => return WaitTipOutcome::Interrupted,
                        _ = self.interrupt.notify.notified() => {
                            if self.interrupt.was_interrupted(interrupt_generation) {
                                return WaitTipOutcome::Interrupted;
                            }
                        }
                        event = chain_events.recv() => match event {
                            Ok(event) if Some(event.hash) != current_hash => return WaitTipOutcome::Tip(event),
                            Ok(_) => continue,
                            Err(tokio::sync::broadcast::error::RecvError::Lagged(_)) => {
                                let tip = self.node.chain.read().tip();
                                if Some(tip.hash) != current_hash {
                                    return WaitTipOutcome::Tip(tip);
                                }
                            }
                            Err(tokio::sync::broadcast::error::RecvError::Closed) => {
                                return WaitTipOutcome::Interrupted;
                            }
                        }
                    }
                }
            };
            match timeout {
                Some(timeout) => match tokio::time::timeout(timeout, wait).await {
                    Ok(outcome) => outcome,
                    Err(_) => WaitTipOutcome::Tip(self.node.chain.read().tip()),
                },
                None => wait.await,
            }
        };

        match outcome {
            WaitTipOutcome::Tip(tip) => {
                set_block_ref(
                    results.get().init_result(),
                    tip.hash.as_byte_array(),
                    tip.height,
                );
            }
            WaitTipOutcome::Interrupted => {
                set_empty_block_ref(results.get().init_result());
            }
        }
        Ok(())
    }

    async fn create_new_block(
        self: Rc<Self>,
        params: crate::mining_capnp::mining::CreateNewBlockParams,
        mut results: crate::mining_capnp::mining::CreateNewBlockResults,
    ) -> Result<(), capnp::Error> {
        debug!("Mining.createNewBlock");
        let params = params.get()?;
        let options = ipc_block_create_options(params.get_options()?);
        let (interrupt_generation, interrupted_before_start) = self.interrupt.begin();
        if interrupted_before_start {
            return Ok(());
        }
        if params.get_cooldown() {
            let mut chain_events = self.node.subscribe_chain();
            while self.node.chain.read().is_initial_block_download() {
                tokio::select! {
                    _ = self.node.wait_for_shutdown() => return Ok(()),
                    _ = self.interrupt.notify.notified() => {
                        if self.interrupt.was_interrupted(interrupt_generation) {
                            return Ok(());
                        }
                    }
                    _ = chain_events.recv() => {}
                    _ = tokio::time::sleep(Duration::from_secs(1)) => {}
                }
            }

            // Match Core's CooldownIfHeadersAhead: only a header chain that
            // extends the active tip is considered, and every newly connected
            // tip restarts the bounded cooldown window.
            'cooldown: loop {
                let Some(blocks_ahead) = self.node.chain.read().blocks_ahead_of_tip() else {
                    break;
                };
                let cooldown_seconds = u64::from(blocks_ahead.clamp(3, 20));
                debug!(
                    blocks_ahead,
                    cooldown_seconds, "Mining.createNewBlock cooldown"
                );
                let deadline = tokio::time::Instant::now() + Duration::from_secs(cooldown_seconds);
                let last_tip = self.node.chain.read().best_hash();
                loop {
                    if self.interrupt.was_interrupted(interrupt_generation) {
                        return Ok(());
                    }
                    let remaining = deadline.saturating_duration_since(tokio::time::Instant::now());
                    if remaining.is_zero() {
                        break;
                    }
                    tokio::select! {
                        _ = self.node.wait_for_shutdown() => return Ok(()),
                        _ = self.interrupt.notify.notified() => {
                            if self.interrupt.was_interrupted(interrupt_generation) {
                                return Ok(());
                            }
                        }
                        event = chain_events.recv() => {
                            match event {
                                Ok(event) if event.hash != last_tip => continue 'cooldown,
                                Ok(_) | Err(tokio::sync::broadcast::error::RecvError::Lagged(_)) => {}
                                Err(tokio::sync::broadcast::error::RecvError::Closed) => break,
                            }
                        }
                        _ = tokio::time::sleep(remaining) => break,
                    }
                }
                break 'cooldown;
            }
        }
        debug!("Mining.createNewBlock template");
        if self.interrupt.was_interrupted(interrupt_generation) {
            return Ok(());
        }
        let template = crate::rpc::create_ipc_block_template(&self.node, options)
            .map_err(|error| capnp::Error::failed(format!("std::exception: {error}")))?;
        results
            .get()
            .set_result(block_template_client(self.node.clone(), template, options));
        Ok(())
    }

    async fn check_block(
        self: Rc<Self>,
        params: crate::mining_capnp::mining::CheckBlockParams,
        mut results: crate::mining_capnp::mining::CheckBlockResults,
    ) -> Result<(), capnp::Error> {
        let params = params.get()?;
        let bytes = params.get_block()?.to_vec();
        let block: Block =
            deserialize(&bytes).map_err(|error| capnp::Error::failed(format!("{error}")))?;
        let options = params.get_options()?;
        let result = self
            .node
            .chain
            .read()
            .validate_candidate_block_with_options(
                &block,
                options.get_check_pow(),
                options.get_check_merkle_root(),
            );
        let mut output = results.get();
        match result {
            Ok(()) => {
                output.set_reason("");
                output.set_debug("");
                output.set_result(true);
            }
            Err(error) => {
                let reason = error
                    .downcast_ref::<crate::validation::ValidationError>()
                    .map(crate::validation::ValidationError::bip22_reject_reason)
                    .unwrap_or_else(|| "rejected".to_owned());
                output.set_reason(reason);
                output.set_debug(error.to_string());
                output.set_result(false);
            }
        }
        Ok(())
    }

    async fn interrupt(
        self: Rc<Self>,
        _params: crate::mining_capnp::mining::InterruptParams,
        _results: crate::mining_capnp::mining::InterruptResults,
    ) -> Result<(), capnp::Error> {
        debug!("Mining.interrupt");
        self.interrupt.interrupt();
        Ok(())
    }
}

impl crate::mining_capnp::block_template::Server for BlockTemplateService {
    async fn destroy(
        self: Rc<Self>,
        _params: crate::mining_capnp::block_template::DestroyParams,
        _results: crate::mining_capnp::block_template::DestroyResults,
    ) -> Result<(), capnp::Error> {
        Ok(())
    }

    async fn get_block_header(
        self: Rc<Self>,
        _params: crate::mining_capnp::block_template::GetBlockHeaderParams,
        mut results: crate::mining_capnp::block_template::GetBlockHeaderResults,
    ) -> Result<(), capnp::Error> {
        let block = self.data.lock().template.block.clone();
        let bytes = serialize(&block.header);
        set_data(results.get().init_result(bytes.len() as u32), &bytes);
        Ok(())
    }

    async fn get_block(
        self: Rc<Self>,
        _params: crate::mining_capnp::block_template::GetBlockParams,
        mut results: crate::mining_capnp::block_template::GetBlockResults,
    ) -> Result<(), capnp::Error> {
        let block = self.data.lock().template.block.clone();
        let bytes = serialize(&block);
        set_data(results.get().init_result(bytes.len() as u32), &bytes);
        Ok(())
    }

    async fn get_tx_fees(
        self: Rc<Self>,
        _params: crate::mining_capnp::block_template::GetTxFeesParams,
        mut results: crate::mining_capnp::block_template::GetTxFeesResults,
    ) -> Result<(), capnp::Error> {
        let fees = self.data.lock().template.tx_fees.clone();
        let mut output = results.get().init_result(fees.len() as u32);
        for (index, fee) in fees.into_iter().enumerate() {
            output.set(index as u32, fee);
        }
        Ok(())
    }

    async fn get_tx_sigops(
        self: Rc<Self>,
        _params: crate::mining_capnp::block_template::GetTxSigopsParams,
        mut results: crate::mining_capnp::block_template::GetTxSigopsResults,
    ) -> Result<(), capnp::Error> {
        let sigops = self.data.lock().template.tx_sigops.clone();
        let mut output = results.get().init_result(sigops.len() as u32);
        for (index, value) in sigops.into_iter().enumerate() {
            output.set(index as u32, value);
        }
        Ok(())
    }

    async fn get_coinbase_tx(
        self: Rc<Self>,
        _params: crate::mining_capnp::block_template::GetCoinbaseTxParams,
        mut results: crate::mining_capnp::block_template::GetCoinbaseTxResults,
    ) -> Result<(), capnp::Error> {
        let template = self.data.lock().template.clone();
        let Some(fields) = block_template_coinbase(&template) else {
            return Err(capnp::Error::failed(
                "template has no coinbase transaction".to_owned(),
            ));
        };
        let mut output = results.get().init_result();
        output.set_version(fields.version);
        output.set_sequence(fields.sequence);
        set_data(
            output
                .reborrow()
                .init_script_sig_prefix(fields.script_sig_prefix.len() as u32),
            &fields.script_sig_prefix,
        );
        if let Some(witness) = fields.witness {
            set_data(
                output.reborrow().init_witness(witness.len() as u32),
                &witness,
            );
        }
        output.set_block_reward_remaining(fields.reward);
        let mut required = output
            .reborrow()
            .init_required_outputs(fields.required_outputs.len() as u32);
        for (index, script) in fields.required_outputs.into_iter().enumerate() {
            required.set(index as u32, &script);
        }
        output.set_lock_time(fields.lock_time);
        Ok(())
    }

    async fn get_coinbase_merkle_path(
        self: Rc<Self>,
        _params: crate::mining_capnp::block_template::GetCoinbaseMerklePathParams,
        mut results: crate::mining_capnp::block_template::GetCoinbaseMerklePathResults,
    ) -> Result<(), capnp::Error> {
        let block = self.data.lock().template.block.clone();
        let path = coinbase_merkle_path(&block);
        let mut output = results.get().init_result(path.len() as u32);
        for (index, hash) in path.into_iter().enumerate() {
            output.set(index as u32, &hash);
        }
        Ok(())
    }

    async fn submit_solution(
        self: Rc<Self>,
        params: crate::mining_capnp::block_template::SubmitSolutionParams,
        mut results: crate::mining_capnp::block_template::SubmitSolutionResults,
    ) -> Result<(), capnp::Error> {
        let params = params.get()?;
        let coinbase_bytes = params.get_coinbase()?.to_vec();
        let coinbase: Transaction = deserialize(&coinbase_bytes).map_err(|error| {
            if coinbase_bytes.is_empty() {
                capnp::Error::failed("std::exception: SpanReader::read(): end of data:".to_owned())
            } else {
                capnp::Error::failed(format!("{error}"))
            }
        })?;
        let block = {
            let mut data = self.data.lock();
            let mut block = data.template.block.clone();
            let Some(first) = block.txdata.first_mut() else {
                return Err(capnp::Error::failed(
                    "template has no coinbase transaction".to_owned(),
                ));
            };
            *first = coinbase;
            block.header.version =
                bitcoin::block::Version::from_consensus(params.get_version() as i32);
            block.header.time = params.get_timestamp();
            block.header.nonce = params.get_nonce();
            block.header.merkle_root = block
                .compute_merkle_root()
                .ok_or_else(|| capnp::Error::failed("cannot compute merkle root".to_owned()))?;
            data.template.block = block.clone();
            block
        };
        let submitted = self.node.connect_block(block).is_ok();
        results.get().set_result(submitted);
        Ok(())
    }

    async fn wait_next(
        self: Rc<Self>,
        params: crate::mining_capnp::block_template::WaitNextParams,
        mut results: crate::mining_capnp::block_template::WaitNextResults,
    ) -> Result<(), capnp::Error> {
        debug!("BlockTemplate.waitNext");
        debug!("IPC server post request");
        let params = params.get()?;
        let wait_options = params.get_options()?;
        let timeout = timeout_duration(wait_options.get_timeout());
        let fee_threshold =
            u64::try_from(wait_options.get_fee_threshold().max(0)).unwrap_or(u64::MAX);
        let current = self.data.lock().template.clone();
        let (generation, interrupted_before_wait) = self.interrupt.begin();
        let mut cancellation = WaitNextCancellationGuard::new(self.node.clone());
        if interrupted_before_wait {
            cancellation.complete();
            return Ok(());
        }

        // Core performs one fee comparison even when the timeout has already
        // elapsed. In particular, fee_threshold == 0 is the documented way
        // for a client to request a refreshed template immediately; checking
        // the deadline first would incorrectly return nullptr.
        if fee_threshold == 0 {
            let template = match crate::rpc::create_ipc_block_template(&self.node, self.options) {
                Ok(template) => template,
                Err(error) => {
                    cancellation.complete();
                    return Err(capnp::Error::failed(error.to_string()));
                }
            };
            debug!("IPC server send response");
            results.get().set_result(block_template_client(
                self.node.clone(),
                template,
                self.options,
            ));
            cancellation.complete();
            return Ok(());
        }

        let mut chain_events = self.node.subscribe_chain();
        let mut mempool_events = self.node.subscribe_mempool();
        let deadline = timeout.map(|duration| tokio::time::Instant::now() + duration);

        loop {
            if self.interrupt.was_interrupted(generation) {
                cancellation.complete();
                return Ok(());
            }
            if ipc_template_tip_requires_refresh(&self.node, current.block.header.prev_blockhash) {
                let template = match crate::rpc::create_ipc_block_template(&self.node, self.options)
                {
                    Ok(template) => template,
                    Err(error) => {
                        cancellation.complete();
                        return Err(capnp::Error::failed(error.to_string()));
                    }
                };
                debug!("IPC server send response");
                results.get().set_result(block_template_client(
                    self.node.clone(),
                    template,
                    self.options,
                ));
                cancellation.complete();
                return Ok(());
            }

            let wait = async {
                tokio::select! {
                    _ = self.node.wait_for_shutdown() => WaitEvent::Shutdown,
                    _ = self.interrupt.notify.notified() => WaitEvent::Interrupt,
                    _ = chain_events.recv() => WaitEvent::Chain,
                    _ = mempool_events.recv() => WaitEvent::Mempool,
                    _ = tokio::time::sleep(Duration::from_secs(1)) => WaitEvent::Tick,
                }
            };
            let event = match deadline {
                Some(deadline) => {
                    let remaining = deadline.saturating_duration_since(tokio::time::Instant::now());
                    if remaining.is_zero() {
                        cancellation.complete();
                        return Ok(());
                    }
                    tokio::time::timeout(remaining, wait).await.ok()
                }
                None => Some(wait.await),
            };
            match event {
                None | Some(WaitEvent::Shutdown | WaitEvent::Interrupt) => {
                    cancellation.complete();
                    return Ok(());
                }
                Some(WaitEvent::Chain | WaitEvent::Mempool | WaitEvent::Tick) => {}
            }

            if ipc_template_tip_requires_refresh(&self.node, current.block.header.prev_blockhash) {
                let template = match crate::rpc::create_ipc_block_template(&self.node, self.options)
                {
                    Ok(template) => template,
                    Err(error) => {
                        cancellation.complete();
                        return Err(capnp::Error::failed(error.to_string()));
                    }
                };
                debug!("IPC server send response");
                results.get().set_result(block_template_client(
                    self.node.clone(),
                    template,
                    self.options,
                ));
                cancellation.complete();
                return Ok(());
            }
            if fee_threshold < crate::mining_capnp::MAX_MONEY as u64 {
                let template = match crate::rpc::create_ipc_block_template(&self.node, self.options)
                {
                    Ok(template) => template,
                    Err(error) => {
                        cancellation.complete();
                        return Err(capnp::Error::failed(error.to_string()));
                    }
                };
                if template.total_fees_sat >= current.total_fees_sat.saturating_add(fee_threshold) {
                    debug!("IPC server send response");
                    results.get().set_result(block_template_client(
                        self.node.clone(),
                        template,
                        self.options,
                    ));
                    cancellation.complete();
                    return Ok(());
                }
            }
        }
    }

    async fn interrupt_wait(
        self: Rc<Self>,
        _params: crate::mining_capnp::block_template::InterruptWaitParams,
        _results: crate::mining_capnp::block_template::InterruptWaitResults,
    ) -> Result<(), capnp::Error> {
        self.interrupt.interrupt();
        Ok(())
    }
}

enum WaitEvent {
    Chain,
    Mempool,
    Tick,
    Interrupt,
    Shutdown,
}

enum WaitTipOutcome {
    Tip(crate::chain::ChainTip),
    Interrupted,
}

pub(crate) struct IpcServer {
    node: Arc<Node>,
    listeners: Vec<UnixListener>,
    cleanup: IpcSocketCleanup,
}

struct IpcSocketCleanup {
    paths: Vec<PathBuf>,
}

impl Drop for IpcSocketCleanup {
    fn drop(&mut self) {
        for path in &self.paths {
            if let Err(error) = std::fs::remove_file(path)
                && error.kind() != std::io::ErrorKind::NotFound
            {
                warn!(path = %path.display(), %error, "unable to remove IPC socket");
            }
        }
    }
}

impl IpcServer {
    pub(crate) async fn bind(node: Arc<Node>) -> Result<Option<Self>> {
        if node.config.ipc_bind.is_empty() {
            return Ok(None);
        }

        #[cfg(not(unix))]
        {
            let _ = node;
            bail!("--ipcbind is only supported on Unix platforms");
        }

        #[cfg(unix)]
        {
            let mut listeners = Vec::with_capacity(node.config.ipc_bind.len());
            let mut paths = Vec::with_capacity(node.config.ipc_bind.len());
            for address in &node.config.ipc_bind {
                let path = parse_socket_path(address, &node.config.datadir, node.config.network)?;
                if path.as_os_str().is_empty() {
                    bail!("IPC socket path must not be empty");
                }
                if path.as_os_str().len() > MAX_UNIX_SOCKET_PATH {
                    bail!("IPC socket path is too long: {}", path.display());
                }
                if let Some(parent) = path.parent() {
                    std::fs::create_dir_all(parent).with_context(|| {
                        format!("creating IPC socket directory {}", parent.display())
                    })?;
                }
                if std::fs::symlink_metadata(&path)
                    .map(|metadata| metadata.file_type().is_socket())
                    .unwrap_or(false)
                {
                    std::fs::remove_file(&path)
                        .with_context(|| format!("removing stale IPC socket {}", path.display()))?;
                }
                let listener = UnixListener::bind(&path)
                    .with_context(|| format!("binding IPC socket {}", path.display()))?;
                listeners.push(listener);
                paths.push(path);
            }
            Ok(Some(Self {
                node,
                listeners,
                cleanup: IpcSocketCleanup { paths },
            }))
        }
    }

    pub(crate) async fn run(self) -> Result<()> {
        let Self {
            node,
            listeners,
            cleanup,
        } = self;
        let mut accept_tasks = Vec::with_capacity(listeners.len());
        for listener in listeners {
            let node = node.clone();
            accept_tasks.push(tokio::task::spawn_local(async move {
                loop {
                    match listener.accept().await {
                        Ok((stream, _)) => {
                            let node = node.clone();
                            tokio::task::spawn_local(async move {
                                if let Err(error) = serve_connection(stream, node).await {
                                    debug!(%error, "IPC connection ended with an error");
                                }
                            });
                        }
                        Err(error) => {
                            warn!(%error, "IPC listener accept failed");
                            break;
                        }
                    }
                }
            }));
        }

        node.wait_for_shutdown().await;
        for task in accept_tasks {
            task.abort();
        }
        drop(cleanup);
        Ok(())
    }
}

async fn serve_connection(stream: UnixStream, node: Arc<Node>) -> Result<()> {
    serve_connection_with_node(stream, Some(node)).await
}

async fn serve_connection_with_node(stream: UnixStream, node: Option<Arc<Node>>) -> Result<()> {
    let (reader, writer) = stream.into_split();
    let network = VatNetwork::new(
        BufReader::new(reader.compat()),
        BufWriter::new(writer.compat_write()),
        Side::Server,
        ReaderOptions::new(),
    );
    let bootstrap: crate::init_capnp::init::Client = new_client(InitService { node: node.clone() });
    let rpc_system = RpcSystem::new(Box::new(network), Some(bootstrap.client));
    if let Some(node) = node {
        tokio::select! {
            result = rpc_system => {
                result.context("serving IPC connection")?;
                Ok(())
            }
            _ = node.wait_for_shutdown() => Ok(()),
        }
    } else {
        rpc_system.await.context("serving spawned IPC connection")
    }
}

fn parse_socket_path(address: &str, datadir: &Path, network: bitcoin::Network) -> Result<PathBuf> {
    let path = if address == "unix" {
        PathBuf::from(DEFAULT_SOCKET_NAME)
    } else if let Some(path) = address.strip_prefix("unix:") {
        if path.is_empty() {
            bail!("IPC address unix: has an empty path");
        }
        PathBuf::from(path)
    } else {
        bail!("unrecognized IPC address {address:?}; expected unix or unix:<path>");
    };
    Ok(if path.is_absolute() {
        path
    } else {
        datadir.join(network_data_dir_name(network)).join(path)
    })
}

#[cfg(test)]
mod tests {
    use super::IpcServer;
    use super::parse_socket_path;
    #[cfg(unix)]
    use super::{create_ipc_socket_pair, echo_over_ipc_stream, run_spawned_process};
    use bitcoin::Network;
    use bitcoin::consensus::encode::deserialize;
    use bitcoin::hashes::Hash as _;
    use bitcoin::script::Builder;
    use capnp::message::ReaderOptions;
    use capnp_rpc::RpcSystem;
    use capnp_rpc::rpc_twoparty_capnp::Side;
    use capnp_rpc::twoparty::VatNetwork;
    use clap::Parser;
    use futures::io::{BufReader, BufWriter};
    #[cfg(unix)]
    use std::os::unix::io::IntoRawFd;
    use std::path::Path;
    use tokio::net::UnixStream;
    use tokio_util::compat::{TokioAsyncReadCompatExt, TokioAsyncWriteCompatExt};

    #[test]
    fn parses_core_unix_socket_addresses() {
        assert_eq!(
            parse_socket_path("unix", Path::new("/tmp/node"), Network::Regtest).unwrap(),
            Path::new("/tmp/node/regtest/node.sock")
        );
        assert_eq!(
            parse_socket_path(
                "unix:custom/node.sock",
                Path::new("/tmp/node"),
                Network::Regtest,
            )
            .unwrap(),
            Path::new("/tmp/node/regtest/custom/node.sock")
        );
        assert_eq!(
            parse_socket_path(
                "unix:/tmp/custom.sock",
                Path::new("/tmp/node"),
                Network::Regtest,
            )
            .unwrap(),
            Path::new("/tmp/custom.sock")
        );
        assert!(
            parse_socket_path("tcp:127.0.0.1:1", Path::new("/tmp/node"), Network::Regtest).is_err()
        );
    }

    #[cfg(unix)]
    #[test]
    fn inherited_fd_ipc_echo_round_trip() {
        let (client_fd, server_fd) = create_ipc_socket_pair().unwrap();
        let server = std::thread::spawn(move || run_spawned_process(server_fd.into_raw_fd()));
        let stream = std::os::unix::net::UnixStream::from(client_fd);
        stream.set_nonblocking(true).unwrap();
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        let echoed = runtime
            .block_on(tokio::task::LocalSet::new().run_until(async move {
                let stream = UnixStream::from_std(stream).unwrap();
                echo_over_ipc_stream(stream, "inherited-fd").await
            }))
            .unwrap();
        drop(runtime);

        assert_eq!(echoed, "inherited-fd");
        server.join().unwrap().unwrap();
    }

    #[tokio::test(flavor = "current_thread")]
    async fn capnp_ipc_echo_and_mining_round_trip() {
        let local_set = tokio::task::LocalSet::new();
        local_set
            .run_until(async {
                let directory = tempfile::tempdir().unwrap();
                let socket = directory.path().join("nested").join("node.sock");
                let args = crate::config::Args::try_parse_from([
                    "bitcoind-rs".to_owned(),
                    "--datadir".to_owned(),
                    directory.path().display().to_string(),
                    "--network=regtest".to_owned(),
                    "--disablewallet".to_owned(),
                    "--p2p=127.0.0.1:0".to_owned(),
                    "--rpcbind=127.0.0.1:0".to_owned(),
                    format!("--ipcbind=unix:{}", socket.display()),
                ])
                .unwrap();
                let node =
                    crate::Node::open(crate::config::Config::from_args(args).unwrap()).unwrap();
                let server = IpcServer::bind(node.clone()).await.unwrap().unwrap();
                let server_task = tokio::task::spawn_local(server.run());

                let stream = UnixStream::connect(&socket).await.unwrap();
                let (reader, writer) = stream.into_split();
                let network = VatNetwork::new(
                    BufReader::new(reader.compat()),
                    BufWriter::new(writer.compat_write()),
                    Side::Client,
                    ReaderOptions::new(),
                );
                let mut rpc_system = RpcSystem::new(Box::new(network), None);
                let init: crate::init_capnp::init::Client = rpc_system.bootstrap(Side::Server);
                let rpc_task = tokio::task::spawn_local(rpc_system);

                let echo_response = init.make_echo_request().send().promise.await.unwrap();
                let echo = echo_response.get().unwrap().get_result().unwrap();
                let mut echo_request = echo.echo_request();
                echo_request.get().set_echo("round-trip");
                let echo_result = echo_request.send().promise.await.unwrap();
                assert_eq!(
                    echo_result
                        .get()
                        .unwrap()
                        .get_result()
                        .unwrap()
                        .to_str()
                        .unwrap(),
                    "round-trip"
                );

                let mining_response = init.make_mining_request().send().promise.await.unwrap();
                let mining = mining_response.get().unwrap().get_result().unwrap();
                let tip_response = mining.get_tip_request().send().promise.await.unwrap();
                let tip = tip_response.get().unwrap();
                assert!(tip.get_has_result());
                assert_eq!(tip.get_result().unwrap().get_height(), 0);
                let current_hash = tip.get_result().unwrap().get_hash().unwrap().to_vec();
                let mut wait_request = mining.wait_tip_changed_request();
                wait_request.get().set_current_tip(&current_hash);
                wait_request.get().set_timeout(1.0);
                let waited = wait_request.send().promise.await.unwrap();
                assert_eq!(waited.get().unwrap().get_result().unwrap().get_height(), 0);

                // Core may enqueue interrupt() before the corresponding wait
                // request is dispatched.  The next interruptible request must
                // consume that pending interruption rather than wait for its
                // timeout.
                mining.interrupt_request().send().promise.await.unwrap();
                let mut pre_interrupted_wait = mining.wait_tip_changed_request();
                pre_interrupted_wait.get().set_current_tip(&current_hash);
                pre_interrupted_wait.get().set_timeout(60_000.0);
                let pre_interrupted = pre_interrupted_wait.send().promise.await.unwrap();
                assert_eq!(
                    pre_interrupted
                        .get()
                        .unwrap()
                        .get_result()
                        .unwrap()
                        .get_height(),
                    -1
                );

                let mut interruptible_wait = mining.wait_tip_changed_request();
                interruptible_wait.get().set_current_tip(&current_hash);
                interruptible_wait.get().set_timeout(60_000.0);
                let wait_task = tokio::task::spawn_local(interruptible_wait.send().promise);
                tokio::time::sleep(std::time::Duration::from_millis(20)).await;
                mining.interrupt_request().send().promise.await.unwrap();
                let interrupted = wait_task.await.unwrap().unwrap();
                assert_eq!(
                    interrupted
                        .get()
                        .unwrap()
                        .get_result()
                        .unwrap()
                        .get_height(),
                    -1
                );

                // Make the active tip eligible for mining, then index a
                // valid header-only descendant. Core's cooldown must remain
                // pending while those headers are ahead of the tip and must
                // be interruptible through the Mining capability.
                node.chain.write().configure_max_tip_age(u64::MAX);
                let genesis = *node.chain.read().header(0).unwrap();
                let mut header_one = bitcoin::block::Header {
                    version: bitcoin::block::Version::from_consensus(4),
                    prev_blockhash: genesis.block_hash(),
                    merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                    time: genesis.time.saturating_add(1),
                    bits: genesis.bits,
                    nonce: 0,
                };
                while !header_one.target().is_met_by(header_one.block_hash()) {
                    header_one.nonce = header_one.nonce.saturating_add(1);
                }
                let mut header_two = bitcoin::block::Header {
                    version: bitcoin::block::Version::from_consensus(4),
                    prev_blockhash: header_one.block_hash(),
                    merkle_root: bitcoin::TxMerkleNode::all_zeros(),
                    time: header_one.time.saturating_add(1),
                    bits: header_one.bits,
                    nonce: 0,
                };
                while !header_two.target().is_met_by(header_two.block_hash()) {
                    header_two.nonce = header_two.nonce.saturating_add(1);
                }
                node.chain
                    .write()
                    .accept_headers(&[header_one, header_two])
                    .unwrap();
                assert_eq!(node.chain.read().blocks_ahead_of_tip(), Some(2));

                let normal_cooldown = mining.create_new_block_request().send().promise;
                let normal_response =
                    tokio::time::timeout(std::time::Duration::from_secs(5), normal_cooldown)
                        .await
                        .unwrap()
                        .unwrap();
                assert!(normal_response.get().unwrap().get_result().is_ok());

                let cooldown_request = mining.create_new_block_request();
                let cooldown_task = tokio::task::spawn_local(cooldown_request.send().promise);
                tokio::time::sleep(std::time::Duration::from_millis(20)).await;
                mining.interrupt_request().send().promise.await.unwrap();
                let cooldown_response = cooldown_task.await.unwrap().unwrap();
                assert!(cooldown_response.get().unwrap().get_result().is_err());

                let mut create_request = mining.create_new_block_request();
                create_request.get().set_cooldown(false);
                let mut options = create_request.get().init_options();
                options.set_use_mempool(false);
                options.set_block_reserved_weight(8_000);
                options.set_coinbase_output_max_additional_sigops(
                    crate::rpc::DEFAULT_COINBASE_OUTPUT_MAX_ADDITIONAL_SIGOPS,
                );
                let template_response = create_request.send().promise.await.unwrap();
                let template = template_response.get().unwrap().get_result().unwrap();
                let mut immediate_wait = template.wait_next_request();
                let mut immediate_options = immediate_wait.get().init_options();
                immediate_options.set_timeout(0.0);
                immediate_options.set_fee_threshold(0);
                let immediate_response = immediate_wait.send().promise.await.unwrap();
                assert!(immediate_response.get().unwrap().get_result().is_ok());
                let block_response = template.get_block_request().send().promise.await.unwrap();
                let block: bitcoin::Block =
                    deserialize(block_response.get().unwrap().get_result().unwrap()).unwrap();
                assert_eq!(block.txdata.len(), 1);
                assert_eq!(
                    block.txdata[0].input[0].script_sig.as_bytes(),
                    Builder::new().push_int(1).into_script().as_bytes()
                );
                let coinbase_response = template
                    .get_coinbase_tx_request()
                    .send()
                    .promise
                    .await
                    .unwrap();
                let coinbase = coinbase_response.get().unwrap().get_result().unwrap();
                assert_eq!(coinbase.get_sequence(), u32::MAX);
                assert_eq!(
                    coinbase.get_script_sig_prefix().unwrap().to_vec(),
                    Builder::new().push_int(1).into_script().into_bytes()
                );
                assert!(coinbase.has_witness());
                assert_eq!(coinbase.get_required_outputs().unwrap().len(), 1);

                let mut malformed_submit = template.submit_solution_request();
                malformed_submit.get().set_coinbase(&[]);
                let malformed_result = malformed_submit.send().promise.await;
                assert!(matches!(
                    malformed_result,
                    Err(error) if error
                        .to_string()
                        .contains("SpanReader::read(): end of data:")
                ));

                let mut payout = bitcoin::Transaction {
                    version: bitcoin::transaction::Version::non_standard(
                        coinbase.get_version() as i32
                    ),
                    lock_time: bitcoin::absolute::LockTime::from_consensus(
                        coinbase.get_lock_time(),
                    ),
                    input: vec![bitcoin::TxIn {
                        previous_output: bitcoin::OutPoint::null(),
                        script_sig: bitcoin::ScriptBuf::from_bytes({
                            let mut script = coinbase.get_script_sig_prefix().unwrap().to_vec();
                            script.push(0);
                            script
                        }),
                        sequence: bitcoin::Sequence::from_consensus(coinbase.get_sequence()),
                        witness: bitcoin::Witness::from_slice(&[coinbase
                            .get_witness()
                            .unwrap()
                            .to_vec()]),
                    }],
                    output: vec![bitcoin::TxOut {
                        value: bitcoin::Amount::from_sat(
                            coinbase.get_block_reward_remaining() as u64
                        ),
                        script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
                    }],
                };
                for output_data in coinbase.get_required_outputs().unwrap() {
                    payout
                        .output
                        .push(deserialize(output_data.unwrap()).unwrap());
                }
                let mut solved_block = block.clone();
                solved_block.txdata[0] = payout.clone();
                solved_block.header.merkle_root = solved_block.compute_merkle_root().unwrap();
                while !solved_block
                    .header
                    .target()
                    .is_met_by(solved_block.block_hash())
                {
                    solved_block.header.nonce = solved_block.header.nonce.saturating_add(1);
                }
                let mut submit_request = template.submit_solution_request();
                submit_request
                    .get()
                    .set_version(solved_block.header.version.to_consensus() as u32);
                submit_request.get().set_timestamp(solved_block.header.time);
                submit_request.get().set_nonce(solved_block.header.nonce);
                submit_request
                    .get()
                    .set_coinbase(&bitcoin::consensus::encode::serialize(&payout));
                let submitted = submit_request.send().promise.await.unwrap();
                assert!(submitted.get().unwrap().get_result());
                assert_eq!(node.chain.read().height(), 1);

                node.request_shutdown();
                let _ = tokio::time::timeout(std::time::Duration::from_secs(2), server_task)
                    .await
                    .unwrap()
                    .unwrap();
                assert!(!socket.exists());
                rpc_task.abort();
            })
            .await;
    }
}
