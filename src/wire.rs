//! Bitcoin peer-to-peer wire framing.
//!
//! The wire layer deliberately owns framing and message limits. Higher layers
//! only receive fully decoded messages, which makes it possible to apply the
//! same bounds to inbound peers and outbound requests.

use std::io::Cursor;

use anyhow::{Result, bail};
use bitcoin::absolute::LockTime;
use bitcoin::bip152::{BlockTransactions, BlockTransactionsRequest, HeaderAndShortIds};
use bitcoin::blockdata::transaction::Version;
use bitcoin::consensus::encode::{VarInt, deserialize, deserialize_partial, serialize};
use bitcoin::hashes::Hash;
use bitcoin::p2p::message_bloom::{FilterAdd, FilterLoad};
use bitcoin::p2p::message_compact_blocks::{BlockTxn, CmpctBlock, GetBlockTxn};
use bitcoin::p2p::message_filter::{
    CFCheckpt, CFHeaders, CFilter, GetCFCheckpt, GetCFHeaders, GetCFilters,
};
use bitcoin::{Block, BlockHash, MerkleBlock, Network, Transaction};
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};

pub const MAX_MESSAGE_SIZE: usize = 4_000_000;
const HEADER_SIZE: usize = 24;
const MAX_INVENTORY_ITEMS: usize = 50_000;
pub(crate) const MAX_LOCATOR_HASHES: usize = 101;
const MAX_USER_AGENT_LENGTH: usize = 256;
const MAX_BLOCK_TRANSACTIONS: usize = 1_000_000;
const MAX_TRANSACTION_OUTPUTS: usize = 1_000_000;
const INVENTORY_ITEM_SIZE: usize = 36;
const ADDR_ITEM_SIZE: usize = 30;
const ADDRV2_MIN_ITEM_SIZE: usize = 9;
const HEADER_ITEM_MIN_SIZE: usize = 81;
// Core accepts the otherwise non-standard legacy transaction shape with no
// inputs and no outputs. Its smallest serialization is version + two
// CompactSize fields + locktime.
const MIN_SERIALIZED_EMPTY_TRANSACTION_SIZE: usize = 10;
const MIN_SERIALIZED_TXOUT_SIZE: usize = 9;

pub const NODE_NETWORK: u64 = 1;
pub const NODE_BLOOM: u64 = 1 << 2;
pub const NODE_WITNESS: u64 = 1 << 3;
pub const NODE_NETWORK_LIMITED: u64 = 1 << 10;
pub const NODE_COMPACT_FILTERS: u64 = 1 << 6;
pub const NODE_P2P_V2: u64 = 1 << 11;
/// Optional project-specific service bit for peers that enforce ReducedData
/// rules. It is not advertised by the default v31.1-compatible node.
pub const NODE_REDUCED_DATA: u64 = 1 << 27;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InventoryType {
    Error,
    Transaction,
    Block,
    FilteredBlock,
    CompactBlock,
    WitnessTransaction,
    WitnessBlock,
    /// Legacy BIP144 witness transaction type. This is valid for GETDATA
    /// requests, but BIP339 INV/GETDATA wtxid relay uses MSG_WTX instead.
    LegacyWitnessTransaction,
    Unknown(u32),
}

impl InventoryType {
    pub fn from_u32(value: u32) -> Self {
        match value {
            0 => Self::Error,
            1 => Self::Transaction,
            2 => Self::Block,
            3 => Self::FilteredBlock,
            4 => Self::CompactBlock,
            5 => Self::WitnessTransaction,
            0x4000_0002 => Self::WitnessBlock,
            0x4000_0001 => Self::LegacyWitnessTransaction,
            other => Self::Unknown(other),
        }
    }

    pub fn as_u32(self) -> u32 {
        match self {
            Self::Error => 0,
            Self::Transaction => 1,
            Self::Block => 2,
            Self::FilteredBlock => 3,
            Self::CompactBlock => 4,
            Self::WitnessTransaction => 5,
            Self::WitnessBlock => 0x4000_0002,
            Self::LegacyWitnessTransaction => 0x4000_0001,
            Self::Unknown(value) => value,
        }
    }

    pub fn is_transaction(self) -> bool {
        matches!(
            self,
            Self::Transaction | Self::WitnessTransaction | Self::LegacyWitnessTransaction
        )
    }

    pub fn is_witness_transaction(self) -> bool {
        matches!(
            self,
            Self::WitnessTransaction | Self::LegacyWitnessTransaction
        )
    }

    /// Whether the inventory hash is a witness transaction id.
    ///
    /// `MSG_WTX` (type 5) is keyed by wtxid, while the legacy
    /// `MSG_TX | MSG_WITNESS_FLAG` type carries a txid and merely requests
    /// the witness-bearing serialization.
    pub fn uses_wtxid(self) -> bool {
        self == Self::WitnessTransaction
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Inventory {
    pub kind: InventoryType,
    pub hash: BlockHash,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NetworkAddress {
    pub time: u32,
    pub services: u64,
    pub address: [u8; 16],
    pub port: u16,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NetworkAddressV2 {
    pub time: u32,
    pub services: u64,
    pub network: u8,
    pub address: Vec<u8>,
    pub port: u16,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VersionMessage {
    pub version: i32,
    pub services: u64,
    pub timestamp: i64,
    pub receiver_services: u64,
    pub receiver_address: [u8; 16],
    pub receiver_port: u16,
    pub sender_services: u64,
    pub sender_address: [u8; 16],
    pub sender_port: u16,
    pub nonce: u64,
    pub user_agent: String,
    pub start_height: i32,
    pub relay: bool,
}

impl VersionMessage {
    pub const PROTOCOL_VERSION: i32 = 70016;

    pub fn new(start_height: i32, nonce: u64) -> Self {
        Self::with_bloom(start_height, nonce, false)
    }

    pub fn with_bloom(start_height: i32, nonce: u64, bloom_filters: bool) -> Self {
        Self::with_bloom_and_comments(start_height, nonce, bloom_filters, &[])
    }

    pub fn with_bloom_and_comments(
        start_height: i32,
        nonce: u64,
        bloom_filters: bool,
        comments: &[String],
    ) -> Self {
        let services = NODE_NETWORK
            | NODE_WITNESS
            | NODE_COMPACT_FILTERS
            | NODE_P2P_V2
            | if bloom_filters { NODE_BLOOM } else { 0 };
        let user_agent = if comments.is_empty() {
            "/bitcoind-rs:0.1.0/".to_owned()
        } else {
            format!("/bitcoind-rs:0.1.0({})/", comments.join("; "))
        };
        Self {
            version: Self::PROTOCOL_VERSION,
            services,
            timestamp: chrono_like_unix_time(),
            receiver_services: services,
            receiver_address: [0; 16],
            receiver_port: 0,
            sender_services: services,
            sender_address: [0; 16],
            sender_port: 0,
            nonce,
            user_agent,
            start_height,
            relay: true,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GetHeadersMessage {
    pub version: i32,
    pub locator_hashes: Vec<BlockHash>,
    pub stop_hash: BlockHash,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SendTxRcnclMessage {
    pub version: u32,
    pub salt: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Message {
    Version(VersionMessage),
    Verack,
    Addr(Vec<NetworkAddress>),
    AddrV2(Vec<NetworkAddressV2>),
    GetAddr,
    SendAddrV2,
    SendHeaders,
    WtxidRelay,
    SendTxRcncl(SendTxRcnclMessage),
    Ping(u64),
    Pong(u64),
    GetHeaders(GetHeadersMessage),
    GetBlocks(GetHeadersMessage),
    Headers(Vec<bitcoin::block::Header>),
    Inv(Vec<Inventory>),
    GetData(Vec<Inventory>),
    NotFound(Vec<Inventory>),
    Block(Block),
    MerkleBlock(MerkleBlock),
    Transaction(Transaction),
    FilterLoad(FilterLoad),
    FilterAdd(FilterAdd),
    FilterClear,
    Mempool,
    FeeFilter(i64),
    SendCmpct { announce: bool, version: u64 },
    CompactBlock(HeaderAndShortIds),
    GetBlockTxn(BlockTransactionsRequest),
    BlockTxn(BlockTransactions),
    GetCFilters(GetCFilters),
    CFilter(CFilter),
    GetCFHeaders(GetCFHeaders),
    CFHeaders(CFHeaders),
    GetCFCheckpt(GetCFCheckpt),
    CFCheckpt(CFCheckpt),
    Unknown { command: String, payload: Vec<u8> },
}

impl Message {
    pub fn command(&self) -> &str {
        match self {
            Self::Version(_) => "version",
            Self::Verack => "verack",
            Self::Addr(_) => "addr",
            Self::AddrV2(_) => "addrv2",
            Self::GetAddr => "getaddr",
            Self::SendAddrV2 => "sendaddrv2",
            Self::SendHeaders => "sendheaders",
            Self::WtxidRelay => "wtxidrelay",
            Self::SendTxRcncl(_) => "sendtxrcncl",
            Self::Ping(_) => "ping",
            Self::Pong(_) => "pong",
            Self::GetHeaders(_) => "getheaders",
            Self::GetBlocks(_) => "getblocks",
            Self::Headers(_) => "headers",
            Self::Inv(_) => "inv",
            Self::GetData(_) => "getdata",
            Self::NotFound(_) => "notfound",
            Self::Block(_) => "block",
            Self::MerkleBlock(_) => "merkleblock",
            Self::Transaction(_) => "tx",
            Self::FilterLoad(_) => "filterload",
            Self::FilterAdd(_) => "filteradd",
            Self::FilterClear => "filterclear",
            Self::Mempool => "mempool",
            Self::FeeFilter(_) => "feefilter",
            Self::SendCmpct { .. } => "sendcmpct",
            Self::CompactBlock(_) => "cmpctblock",
            Self::GetBlockTxn(_) => "getblocktxn",
            Self::BlockTxn(_) => "blocktxn",
            Self::GetCFilters(_) => "getcfilters",
            Self::CFilter(_) => "cfilter",
            Self::GetCFHeaders(_) => "getcfheaders",
            Self::CFHeaders(_) => "cfheaders",
            Self::GetCFCheckpt(_) => "getcfcheckpt",
            Self::CFCheckpt(_) => "cfcheckpt",
            Self::Unknown { command, .. } => command.as_str(),
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum WireError {
    #[error("invalid network magic {0:02x?}")]
    Magic([u8; 4]),
    #[error("message payload exceeds limit: {0} bytes")]
    Oversized(usize),
    #[error("message payload exceeds limit: {command}, {size} bytes")]
    OversizedFrame { command: String, size: usize },
    #[error("invalid message checksum")]
    Checksum {
        command: String,
        payload_size: usize,
        expected: [u8; 4],
        actual: [u8; 4],
    },
    #[error("invalid message type")]
    InvalidMessageType,
    #[error("unknown command {0}")]
    UnknownCommand(String),
    #[error("malformed payload: {0}")]
    Payload(String),
    #[error("invalid compact-size integer")]
    CompactSize,
}

pub fn network_magic(network: Network) -> [u8; 4] {
    match network {
        Network::Bitcoin => [0xf9, 0xbe, 0xb4, 0xd9],
        Network::Testnet => [0x0b, 0x11, 0x09, 0x07],
        Network::Signet => [0x0a, 0x03, 0xcf, 0x40],
        Network::Regtest => [0xfa, 0xbf, 0xb5, 0xda],
        Network::Testnet4 => [0x1c, 0x16, 0x3f, 0x28],
    }
}

/// Return the message-start bytes for a chain instance.  Signet derives its
/// message start from the serialized challenge, whereas the other networks
/// use fixed constants.  Keeping the legacy `network_magic` helper intact
/// preserves the public-network defaults used by file formats and unit tests.
pub fn network_magic_with_signet_challenge(
    network: Network,
    signet_challenge: Option<&[u8]>,
) -> [u8; 4] {
    if network != Network::Signet {
        return network_magic(network);
    }
    let challenge = signet_challenge
        .map(ToOwned::to_owned)
        .unwrap_or_else(crate::validation::default_signet_challenge);
    let serialized = serialize(&challenge);
    let hash = bitcoin::hashes::sha256d::Hash::hash(&serialized).to_byte_array();
    hash[..4]
        .try_into()
        .expect("sha256d is four-byte-prefix capable")
}

pub fn encode_message(network: Network, message: &Message) -> Result<Vec<u8>> {
    encode_message_with_magic(network_magic(network), message)
}

pub fn encode_message_with_magic(magic: [u8; 4], message: &Message) -> Result<Vec<u8>> {
    let payload = encode_payload(message)?;
    validate_payload_size(payload.len())?;
    let command = message.command();
    validate_command(command)?;
    let command = command.as_bytes();
    let mut frame = Vec::with_capacity(HEADER_SIZE + payload.len());
    frame.extend_from_slice(&magic);
    let mut command_bytes = [0u8; 12];
    command_bytes[..command.len()].copy_from_slice(command);
    frame.extend_from_slice(&command_bytes);
    frame.extend_from_slice(&(payload.len() as u32).to_le_bytes());
    frame.extend_from_slice(&checksum(&payload));
    frame.extend_from_slice(&payload);
    Ok(frame)
}

pub fn decode_message(network: Network, frame: &[u8]) -> Result<Message> {
    decode_message_with_magic(network_magic(network), frame)
}

pub fn decode_message_with_magic(expected_magic: [u8; 4], frame: &[u8]) -> Result<Message> {
    if frame.len() < HEADER_SIZE {
        bail!("short Bitcoin message frame");
    }
    let mut received_magic = [0u8; 4];
    received_magic.copy_from_slice(&frame[..4]);
    if received_magic != expected_magic {
        return Err(WireError::Magic(received_magic).into());
    }
    let command = decode_command(&frame[4..16]).map_err(|_| WireError::InvalidMessageType)?;
    let length = u32::from_le_bytes(frame[16..20].try_into().expect("slice length")) as usize;
    if length > MAX_MESSAGE_SIZE {
        return Err(WireError::Oversized(length).into());
    }
    if frame.len() != HEADER_SIZE + length {
        bail!("message frame length does not match payload length");
    }
    let expected = checksum(&frame[24..]);
    if frame[20..24] != expected {
        return Err(WireError::Checksum {
            command: command.to_owned(),
            payload_size: length,
            expected,
            actual: frame[20..24].try_into().expect("checksum is four bytes"),
        }
        .into());
    }
    decode_payload(command, &frame[24..]).map_err(Into::into)
}

pub async fn read_message<R: AsyncRead + Unpin>(
    reader: &mut R,
    network: Network,
) -> Result<Message> {
    read_message_with_magic(reader, network_magic(network)).await
}

pub async fn read_message_with_magic<R: AsyncRead + Unpin>(
    reader: &mut R,
    magic: [u8; 4],
) -> Result<Message> {
    Ok(read_message_with_size_with_magic(reader, magic).await?.0)
}

pub async fn read_message_with_size<R: AsyncRead + Unpin>(
    reader: &mut R,
    network: Network,
) -> Result<(Message, usize)> {
    read_message_with_size_with_magic(reader, network_magic(network)).await
}

pub async fn read_message_with_size_with_magic<R: AsyncRead + Unpin>(
    reader: &mut R,
    magic: [u8; 4],
) -> Result<(Message, usize)> {
    let (frame, size) = read_frame_with_size(reader).await?;
    Ok((decode_message_with_magic(magic, &frame)?, size))
}

/// A cancellation-safe v1 frame reader.  Peer processing uses `select!` to
/// interleave socket reads with timers and commands; `read_exact` cannot be
/// canceled halfway through a frame because the bytes already consumed would
/// otherwise be lost.  Keep the partial frame in this reader instead.
pub(crate) struct MessageReader<R> {
    reader: R,
    buffer: Vec<u8>,
    discard_remaining: usize,
    discard_frame_size: usize,
    discard_buffer: Vec<u8>,
}

impl<R: AsyncRead + Unpin> MessageReader<R> {
    pub(crate) fn new(reader: R) -> Self {
        Self {
            reader,
            buffer: Vec::new(),
            discard_remaining: 0,
            discard_frame_size: 0,
            discard_buffer: Vec::new(),
        }
    }

    pub(crate) fn has_partial_frame(&self) -> bool {
        !self.buffer.is_empty() || self.discard_remaining != 0
    }

    #[cfg(test)]
    pub(crate) async fn read_message_with_size_allow_reject(
        &mut self,
        network: Network,
    ) -> Result<(Option<Message>, usize)> {
        self.read_message_with_size_allow_reject_with_magic_callback(
            network_magic(network),
            &mut |_| {},
        )
        .await
    }

    pub(crate) async fn read_message_with_size_allow_reject_with_magic_callback(
        &mut self,
        magic: [u8; 4],
        on_bytes: &mut impl FnMut(usize),
    ) -> Result<(Option<Message>, usize)> {
        loop {
            if self.discard_remaining != 0 {
                let buffered = self.discard_remaining.min(self.buffer.len());
                if buffered != 0 {
                    self.buffer.drain(..buffered);
                    self.discard_remaining -= buffered;
                }
                if self.discard_remaining == 0 {
                    let size = self.discard_frame_size;
                    self.discard_frame_size = 0;
                    return Ok((None, size));
                }

                if self.discard_buffer.is_empty() {
                    self.discard_buffer.resize(256 * 1024, 0);
                }
                let read_limit = self.discard_remaining.min(self.discard_buffer.len());
                let count = self
                    .reader
                    .read(&mut self.discard_buffer[..read_limit])
                    .await?;
                if count == 0 {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::UnexpectedEof,
                        "peer closed during Bitcoin message",
                    )
                    .into());
                }
                on_bytes(count);
                self.discard_remaining -= count;
                continue;
            }

            if self.buffer.len() >= HEADER_SIZE {
                let length = u32::from_le_bytes(
                    self.buffer[16..20]
                        .try_into()
                        .expect("v1 header has a length field"),
                ) as usize;
                if length > MAX_MESSAGE_SIZE {
                    let command = command_for_header_log(&self.buffer[4..16]);
                    let error = WireError::OversizedFrame {
                        command,
                        size: length,
                    };
                    log_v1_header_error(&error);
                    return Err(error.into());
                }
                let frame_size = HEADER_SIZE + length;
                if length > 1_000_000 && decode_command(&self.buffer[4..16]).is_err() {
                    log_v1_header_error(&WireError::InvalidMessageType);
                    self.discard_remaining = frame_size;
                    self.discard_frame_size = frame_size;
                    continue;
                }
                if self.buffer.len() >= frame_size {
                    let remainder = self.buffer.split_off(frame_size);
                    let frame = std::mem::replace(&mut self.buffer, remainder);
                    return match decode_message_with_magic(magic, &frame) {
                        Ok(message) => Ok((Some(message), frame.len())),
                        Err(error) => {
                            log_v1_header_error_for_frame_with_magic(magic, &frame);
                            if let Some(message) =
                                recoverable_payload_message_with_magic(magic, &frame)
                            {
                                Ok((Some(message), frame.len()))
                            } else if frame_has_recoverable_error_with_magic(magic, &frame) {
                                Ok((None, frame.len()))
                            } else {
                                Err(error)
                            }
                        }
                    };
                }
            }

            let mut chunk = [0u8; 16 * 1024];
            let count = self.reader.read(&mut chunk).await?;
            if count == 0 {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::UnexpectedEof,
                    "peer closed during Bitcoin message",
                )
                .into());
            }
            on_bytes(count);
            self.buffer.extend_from_slice(&chunk[..count]);
        }
    }
}

/// Read a v1 frame while preserving Core's distinction between a recoverable
/// message rejection and a fatal transport/framing error. Core discards a
/// complete frame with a bad checksum or invalid command header, accounts its
/// bytes as `*other*`, and continues reading the connection.
#[cfg(test)]
pub(crate) async fn read_message_with_size_allow_reject<R: AsyncRead + Unpin>(
    reader: &mut R,
    network: Network,
) -> Result<(Option<Message>, usize)> {
    let (frame, size) = read_frame_with_size(reader).await?;
    match decode_message_with_magic(network_magic(network), &frame) {
        Ok(message) => Ok((Some(message), size)),
        Err(error) => {
            if let Some(message) =
                recoverable_payload_message_with_magic(network_magic(network), &frame)
            {
                Ok((Some(message), size))
            } else if frame_has_recoverable_error_with_magic(network_magic(network), &frame) {
                Ok((None, size))
            } else {
                Err(error)
            }
        }
    }
}

async fn read_frame_with_size<R: AsyncRead + Unpin>(reader: &mut R) -> Result<(Vec<u8>, usize)> {
    let mut header = [0u8; HEADER_SIZE];
    reader.read_exact(&mut header).await?;
    let length = u32::from_le_bytes(header[16..20].try_into().expect("slice length")) as usize;
    if length > MAX_MESSAGE_SIZE {
        let command = command_for_header_log(&header[4..16]);
        let error = WireError::OversizedFrame {
            command,
            size: length,
        };
        log_v1_header_error(&error);
        return Err(error.into());
    }
    let mut frame = Vec::with_capacity(HEADER_SIZE + length);
    frame.extend_from_slice(&header);
    frame.resize(HEADER_SIZE + length, 0);
    reader.read_exact(&mut frame[HEADER_SIZE..]).await?;
    let size = frame.len();
    Ok((frame, size))
}

fn log_v1_header_error(error: &WireError) {
    match error {
        WireError::Magic(magic) => {
            tracing::debug!(target: "bitcoind_rs::p2p",
                "Header error: Wrong MessageStart {} received",
                hex::encode(magic)
            );
        }
        WireError::Checksum {
            command,
            payload_size,
            expected,
            actual,
        } => {
            tracing::debug!(target: "bitcoind_rs::p2p",
                "Header error: Wrong checksum ({command}, {payload_size} bytes), expected {} was {}",
                hex::encode(expected),
                hex::encode(actual),
            );
        }
        WireError::OversizedFrame { command, size } => {
            tracing::debug!(target: "bitcoind_rs::p2p", "Header error: Size too large ({command}, {size} bytes)");
        }
        WireError::InvalidMessageType => {
            tracing::debug!(target: "bitcoind_rs::p2p", "Header error: Invalid message type");
        }
        WireError::Oversized(_)
        | WireError::UnknownCommand(_)
        | WireError::Payload(_)
        | WireError::CompactSize => {}
    }
    // Header errors are part of the protocol's immediate diagnostics. Core's
    // tests and operators inspect these records while the connection remains
    // open, so do not leave them behind the normal asynchronous log batch.
    crate::flush_debug_log();
}

fn log_v1_header_error_for_frame_with_magic(magic: [u8; 4], frame: &[u8]) {
    if frame.len() < HEADER_SIZE {
        return;
    }
    if frame[..4] != magic {
        let mut received_magic = [0u8; 4];
        received_magic.copy_from_slice(&frame[..4]);
        log_v1_header_error(&WireError::Magic(received_magic));
        return;
    }
    let length = u32::from_le_bytes(frame[16..20].try_into().expect("slice length")) as usize;
    let command_valid = decode_command(&frame[4..16]).is_ok();
    if !command_valid && length > 1_000_000 {
        log_v1_header_error(&WireError::InvalidMessageType);
        return;
    }
    let expected = checksum(&frame[24..]);
    if frame[20..24] != expected {
        log_v1_header_error(&WireError::Checksum {
            command: command_for_header_log(&frame[4..16]),
            payload_size: length,
            expected,
            actual: frame[20..24].try_into().expect("checksum is four bytes"),
        });
        return;
    }
    let Ok(command) = decode_command(&frame[4..16]) else {
        log_v1_header_error(&WireError::InvalidMessageType);
        return;
    };
    if length > MAX_MESSAGE_SIZE {
        log_v1_header_error(&WireError::OversizedFrame {
            command: command.to_owned(),
            size: length,
        });
    }
}

fn command_for_header_log(bytes: &[u8]) -> String {
    let end = bytes
        .iter()
        .position(|byte| *byte == 0 || !byte.is_ascii_graphic())
        .unwrap_or(bytes.len());
    if end == 0 {
        "unknown".to_owned()
    } else {
        String::from_utf8_lossy(&bytes[..end]).into_owned()
    }
}

fn frame_has_recoverable_error_with_magic(magic: [u8; 4], frame: &[u8]) -> bool {
    if frame.len() < HEADER_SIZE || frame[..4] != magic {
        return false;
    }
    let Ok(command) = decode_command(&frame[4..16]) else {
        return true;
    };
    if frame[20..24] != checksum(&frame[24..]) {
        return true;
    }
    if command == "block"
        && let Err(WireError::Payload(reason)) = decode_payload(command, &frame[24..])
    {
        if reason.contains("non-minimal varint") {
            tracing::debug!(target: "bitcoind_rs::p2p", "non-canonical ReadCompactSize()");
        } else {
            // Core catches block deserialization exceptions in
            // ProcessMessages, logs the exception, and continues reading
            // from the peer. In particular this keeps malformed witness
            // vector tests from turning a recoverable payload error into a
            // transport disconnect.
            tracing::debug!(
                target: "bitcoind_rs::p2p",
                "Exception 'DataStream::read(): end of data' (std::ios_base::failure) caught"
            );
        }
        return true;
    }
    if command == "tx"
        && let Err(WireError::Payload(reason)) = decode_payload(command, &frame[24..])
    {
        if let Some(transaction_reason) = transaction_optional_data_error(&frame[24..]) {
            tracing::debug!(target: "bitcoind_rs::p2p", "{transaction_reason}");
        } else if reason.contains("non-minimal varint") {
            tracing::debug!(target: "bitcoind_rs::p2p", "non-canonical ReadCompactSize()");
        } else {
            // Core catches transaction deserialization exceptions in
            // ProcessMessages and keeps the peer connected after discarding
            // the complete frame.
            tracing::debug!(
                target: "bitcoind_rs::p2p",
                "Exception 'DataStream::read(): end of data' (std::ios_base::failure) caught"
            );
        }
        crate::flush_debug_log();
        return true;
    }
    false
}

fn transaction_optional_data_error(payload: &[u8]) -> Option<&'static str> {
    let mut reader = Reader::new(payload);
    reader.bytes(4).ok()?;
    if reader.u8().ok()? != 0 {
        return None;
    }
    let flags = reader.u8().ok()?;
    if flags == 0 {
        return None;
    }

    let input_count = bounded_count(reader.compact_size().ok()?).ok()?;
    for _ in 0..input_count {
        reader.bytes(36).ok()?;
        let script_len = bounded_count(reader.compact_size().ok()?).ok()?;
        reader.bytes(script_len).ok()?;
        reader.bytes(4).ok()?;
    }
    let output_count = bounded_count(reader.compact_size().ok()?).ok()?;
    for _ in 0..output_count {
        reader.bytes(8).ok()?;
        let script_len = bounded_count(reader.compact_size().ok()?).ok()?;
        reader.bytes(script_len).ok()?;
    }

    if flags & 1 != 0 {
        let mut has_witness = false;
        for _ in 0..input_count {
            let item_count = bounded_count(reader.compact_size().ok()?).ok()?;
            for _ in 0..item_count {
                let item_len = bounded_count(reader.compact_size().ok()?).ok()?;
                has_witness |= item_len != 0;
                reader.bytes(item_len).ok()?;
            }
        }
        if !has_witness {
            return Some("Superfluous witness record");
        }
    }
    (flags != 1).then_some("Unknown transaction optional data")
}

pub(crate) fn v2_transaction_optional_data_error(payload: &[u8]) -> Option<&'static str> {
    let message_type = *payload.first()?;
    let payload_start = if message_type == 0 { 13 } else { 1 };
    let command = if message_type == 0 {
        decode_command(payload.get(1..13)?).ok()?
    } else {
        v2_message_command(message_type)?
    };
    (command == "tx")
        .then(|| transaction_optional_data_error(payload.get(payload_start..)?))
        .flatten()
}

fn recoverable_payload_message_with_magic(magic: [u8; 4], frame: &[u8]) -> Option<Message> {
    if frame.len() < HEADER_SIZE || frame[..4] != magic {
        return None;
    }
    let command = decode_command(&frame[4..16]).ok()?;
    if frame[20..24] != checksum(&frame[24..])
        || !matches!(command, "addr" | "addrv2" | "inv" | "getdata" | "headers")
    {
        return None;
    }
    Some(Message::Unknown {
        command: command.to_owned(),
        payload: frame[24..].to_vec(),
    })
}

pub async fn write_message<W: AsyncWrite + Unpin>(
    writer: &mut W,
    network: Network,
    message: &Message,
) -> Result<()> {
    write_message_with_magic(writer, network_magic(network), message)
        .await
        .map(|_| ())
}

pub async fn write_message_with_size<W: AsyncWrite + Unpin>(
    writer: &mut W,
    network: Network,
    message: &Message,
) -> Result<usize> {
    write_message_with_magic_size(writer, network_magic(network), message).await
}

pub async fn write_message_with_magic<W: AsyncWrite + Unpin>(
    writer: &mut W,
    magic: [u8; 4],
    message: &Message,
) -> Result<usize> {
    write_message_with_magic_size(writer, magic, message).await
}

async fn write_message_with_magic_size<W: AsyncWrite + Unpin>(
    writer: &mut W,
    magic: [u8; 4],
    message: &Message,
) -> Result<usize> {
    let frame = encode_message_with_magic(magic, message)?;
    let size = frame.len();
    writer.write_all(&frame).await?;
    writer.flush().await?;
    Ok(size)
}

fn checksum(payload: &[u8]) -> [u8; 4] {
    let hash = bitcoin::hashes::sha256d::Hash::hash(payload).to_byte_array();
    hash[..4].try_into().expect("sha256d is 32 bytes")
}

fn encode_payload(message: &Message) -> Result<Vec<u8>> {
    let mut out = Vec::new();
    match message {
        Message::Version(version) => encode_version(version, &mut out)?,
        Message::Verack
        | Message::GetAddr
        | Message::SendAddrV2
        | Message::SendHeaders
        | Message::WtxidRelay
        | Message::FilterClear
        | Message::Mempool => {}
        Message::SendTxRcncl(message) => {
            put_u32(message.version, &mut out);
            put_u64(message.salt, &mut out);
        }
        Message::Addr(entries) => {
            if entries.len() > 1_000 {
                return Err(WireError::Payload("too many address records".to_owned()).into());
            }
            put_compact_size(entries.len(), &mut out)?;
            for entry in entries {
                put_u32(entry.time, &mut out);
                put_u64(entry.services, &mut out);
                out.extend_from_slice(&entry.address);
                out.extend_from_slice(&entry.port.to_be_bytes());
            }
        }
        Message::AddrV2(entries) => {
            if entries.len() > 1_000 {
                return Err(WireError::Payload("too many address records".to_owned()).into());
            }
            put_compact_size(entries.len(), &mut out)?;
            for entry in entries {
                put_u32(entry.time, &mut out);
                put_compact_size_u64(entry.services, &mut out);
                out.push(entry.network);
                if entry.address.len() > 512 {
                    return Err(WireError::Payload("address record is too large".to_owned()).into());
                }
                put_compact_size(entry.address.len(), &mut out)?;
                out.extend_from_slice(&entry.address);
                out.extend_from_slice(&entry.port.to_be_bytes());
            }
        }
        Message::Ping(nonce) | Message::Pong(nonce) => put_u64(*nonce, &mut out),
        Message::GetHeaders(request) | Message::GetBlocks(request) => {
            put_i32(request.version, &mut out);
            put_compact_size(request.locator_hashes.len(), &mut out)?;
            for hash in &request.locator_hashes {
                out.extend_from_slice(&hash.to_byte_array());
            }
            out.extend_from_slice(&request.stop_hash.to_byte_array());
        }
        Message::Headers(headers) => {
            put_compact_size(headers.len(), &mut out)?;
            for header in headers {
                out.extend_from_slice(&serialize(header));
                out.push(0);
            }
        }
        Message::Inv(items) | Message::GetData(items) | Message::NotFound(items) => {
            encode_inventory(items, &mut out)?;
        }
        Message::Block(block) => out.extend_from_slice(&serialize(block)),
        Message::MerkleBlock(block) => out.extend_from_slice(&serialize(block)),
        Message::Transaction(transaction) => out.extend_from_slice(&serialize(transaction)),
        Message::FilterLoad(filter) => out.extend_from_slice(&serialize(filter)),
        Message::FilterAdd(filter) => out.extend_from_slice(&serialize(filter)),
        Message::FeeFilter(rate) => put_i64(*rate, &mut out),
        Message::SendCmpct { announce, version } => {
            out.push(u8::from(*announce));
            put_u64(*version, &mut out);
        }
        Message::CompactBlock(compact) => out.extend_from_slice(&serialize(&CmpctBlock {
            compact_block: compact.clone(),
        })),
        Message::GetBlockTxn(request) => out.extend_from_slice(&serialize(&GetBlockTxn {
            txs_request: request.clone(),
        })),
        Message::BlockTxn(transactions) => out.extend_from_slice(&serialize(&BlockTxn {
            transactions: transactions.clone(),
        })),
        Message::GetCFilters(request) => out.extend_from_slice(&serialize(request)),
        Message::CFilter(response) => out.extend_from_slice(&serialize(response)),
        Message::GetCFHeaders(request) => out.extend_from_slice(&serialize(request)),
        Message::CFHeaders(response) => out.extend_from_slice(&serialize(response)),
        Message::GetCFCheckpt(request) => out.extend_from_slice(&serialize(request)),
        Message::CFCheckpt(response) => out.extend_from_slice(&serialize(response)),
        Message::Unknown { payload, .. } => out.extend_from_slice(payload),
    }
    Ok(out)
}

/// Encode the application payload used by the legacy Bitcoin message frame.
///
/// This is also the payload captured by Core's `-capturemessages` debug
/// facility. Transport-specific headers are intentionally excluded.
pub(crate) fn encode_message_payload(message: &Message) -> Result<Vec<u8>> {
    encode_payload(message)
}

/// Encode the application-layer contents used inside a BIP324 packet.
///
/// Unlike v1 framing, the network magic, length, checksum, and 12-byte
/// command header are not transported separately. Common commands use their
/// one-byte BIP324 type id; extensions use a zero byte followed by the
/// conventional 12-byte command name.
pub fn encode_v2_message(message: &Message) -> Result<Vec<u8>> {
    let command = message.command();
    validate_command(command)?;
    let mut result = Vec::new();
    if let Some(message_id) = v2_message_id(command) {
        result.push(message_id);
    } else {
        result.push(0);
        let mut command_bytes = [0u8; 12];
        command_bytes[..command.len()].copy_from_slice(command.as_bytes());
        result.extend_from_slice(&command_bytes);
    }
    result.extend_from_slice(&encode_payload(message)?);
    Ok(result)
}

/// Decode a BIP324 application-layer message into the normal wire message
/// representation used by the peer state machine.
pub fn decode_v2_message(payload: &[u8]) -> Result<Message> {
    let Some(&message_type) = payload.first() else {
        bail!("empty BIP324 application message");
    };
    let (command, payload_start) = if message_type == 0 {
        let command_bytes = payload
            .get(1..13)
            .ok_or_else(|| anyhow::anyhow!("short BIP324 command header"))?;
        (decode_command(command_bytes)?.to_owned(), 13)
    } else {
        (
            v2_message_command(message_type)
                .ok_or_else(|| anyhow::anyhow!("unknown BIP324 message type {message_type}"))?
                .to_owned(),
            1,
        )
    };
    decode_payload(&command, payload.get(payload_start..).unwrap_or_default()).map_err(Into::into)
}

pub(crate) fn v2_message_type_is_valid(payload: &[u8]) -> bool {
    let Some(&message_type) = payload.first() else {
        return false;
    };
    if message_type == 0 {
        return payload
            .get(1..13)
            .is_some_and(|command| decode_command(command).is_ok());
    }
    v2_message_command(message_type).is_some()
}

fn validate_payload_size(size: usize) -> Result<()> {
    if size > MAX_MESSAGE_SIZE {
        return Err(WireError::Oversized(size).into());
    }
    Ok(())
}

fn validate_command(command: &str) -> Result<()> {
    let bytes = command.as_bytes();
    if bytes.is_empty()
        || bytes.len() > 12
        || bytes
            .iter()
            .any(|byte| !byte.is_ascii_graphic() || *byte == b' ')
    {
        bail!("invalid Bitcoin command name");
    }
    Ok(())
}

fn decode_command(bytes: &[u8]) -> Result<&str> {
    let command_end = bytes
        .iter()
        .position(|byte| *byte == 0)
        .unwrap_or(bytes.len());
    if command_end == 0
        || bytes[command_end + usize::from(command_end < bytes.len())..]
            .iter()
            .any(|byte| *byte != 0)
    {
        bail!("invalid Bitcoin command padding");
    }
    let command = std::str::from_utf8(&bytes[..command_end])?;
    validate_command(command)?;
    Ok(command)
}

fn v2_message_id(command: &str) -> Option<u8> {
    Some(match command {
        "addr" => 1,
        "block" => 2,
        "blocktxn" => 3,
        "cmpctblock" => 4,
        "feefilter" => 5,
        "filteradd" => 6,
        "filterclear" => 7,
        "filterload" => 8,
        "getblocks" => 9,
        "getblocktxn" => 10,
        "getdata" => 11,
        "getheaders" => 12,
        "headers" => 13,
        "inv" => 14,
        "mempool" => 15,
        "merkleblock" => 16,
        "notfound" => 17,
        "ping" => 18,
        "pong" => 19,
        "sendcmpct" => 20,
        "tx" => 21,
        "getcfilters" => 22,
        "cfilter" => 23,
        "getcfheaders" => 24,
        "cfheaders" => 25,
        "getcfcheckpt" => 26,
        "cfcheckpt" => 27,
        "addrv2" => 28,
        _ => return None,
    })
}

fn v2_message_command(message_type: u8) -> Option<&'static str> {
    Some(match message_type {
        1 => "addr",
        2 => "block",
        3 => "blocktxn",
        4 => "cmpctblock",
        5 => "feefilter",
        6 => "filteradd",
        7 => "filterclear",
        8 => "filterload",
        9 => "getblocks",
        10 => "getblocktxn",
        11 => "getdata",
        12 => "getheaders",
        13 => "headers",
        14 => "inv",
        15 => "mempool",
        16 => "merkleblock",
        17 => "notfound",
        18 => "ping",
        19 => "pong",
        20 => "sendcmpct",
        21 => "tx",
        22 => "getcfilters",
        23 => "cfilter",
        24 => "getcfheaders",
        25 => "cfheaders",
        26 => "getcfcheckpt",
        27 => "cfcheckpt",
        28 => "addrv2",
        _ => return None,
    })
}

/// Decode transactions using the ambiguity rule from Core's
/// `UnserializeTransaction`. In particular, a transaction with zero inputs,
/// zero outputs, and a four-byte locktime is a valid legacy transaction. The
/// bitcoin crate interprets the second zero as a SegWit flag and rejects it,
/// but Core treats it as the output count in this case.
fn decode_transaction_core_compatible(payload: &[u8]) -> Result<Transaction, WireError> {
    if payload.len() == 10 && payload[4] == 0 && payload[5] == 0 {
        return Ok(Transaction {
            version: Version::non_standard(i32::from_le_bytes(
                payload[..4].try_into().expect("transaction version length"),
            )),
            lock_time: LockTime::from_consensus(u32::from_le_bytes(
                payload[6..]
                    .try_into()
                    .expect("transaction locktime length"),
            )),
            input: Vec::new(),
            output: Vec::new(),
        });
    }
    deserialize(payload).map_err(payload_error)
}

fn decode_block_core_compatible(payload: &[u8]) -> Result<Block, WireError> {
    let (header, header_consumed) =
        deserialize_partial::<bitcoin::block::Header>(payload).map_err(payload_error)?;
    let (transaction_count, count_consumed) =
        deserialize_partial::<VarInt>(&payload[header_consumed..]).map_err(payload_error)?;
    let transaction_count = usize::try_from(transaction_count.0)
        .map_err(|_| WireError::Payload("block transaction count is too large".to_owned()))?;
    if transaction_count > MAX_BLOCK_TRANSACTIONS {
        return Err(WireError::Payload(
            "block transaction count is too large".to_owned(),
        ));
    }

    let mut offset = header_consumed.saturating_add(count_consumed);
    let remaining_len = payload.len().saturating_sub(offset);
    if transaction_count > remaining_len / MIN_SERIALIZED_EMPTY_TRANSACTION_SIZE {
        return Err(WireError::Payload(
            "block transaction count exceeds payload size".to_owned(),
        ));
    }

    // Preflight the vector count before asking the bitcoin crate to decode the
    // block. A peer can otherwise advertise a large transaction count in a
    // tiny malformed payload and make deserialization reserve a large Vec
    // before it discovers that the bytes are missing.
    if let Ok(block) = deserialize(payload) {
        return Ok(block);
    }

    let mut txdata = Vec::with_capacity(transaction_count);
    for _ in 0..transaction_count {
        let remaining = payload
            .get(offset..)
            .ok_or_else(|| WireError::Payload("truncated block transaction".to_owned()))?;
        match deserialize_partial::<Transaction>(remaining) {
            Ok((transaction, consumed)) => {
                txdata.push(transaction);
                offset = offset.saturating_add(consumed);
            }
            Err(_) => {
                let (transaction, consumed) = decode_empty_input_transaction(remaining)?;
                txdata.push(transaction);
                offset = offset.saturating_add(consumed);
            }
        }
    }
    if offset != payload.len() {
        // Core's block deserializer does not require the stream to be
        // exhausted after the transaction vector. This matters for a
        // malformed SegWit transaction whose witness vector has more
        // records than inputs: Core parses the transaction up to its
        // locktime, then lets normal block validation report the resulting
        // merkle-root mismatch instead of disconnecting the peer.
        if offset < payload.len()
            && txdata.last().is_some_and(|transaction| {
                transaction
                    .input
                    .iter()
                    .any(|input| !input.witness.is_empty())
            })
        {
            return Ok(Block { header, txdata });
        }
        return Err(WireError::Payload(
            "block contains trailing transaction bytes".to_owned(),
        ));
    }
    Ok(Block { header, txdata })
}

fn decode_empty_input_transaction(payload: &[u8]) -> Result<(Transaction, usize), WireError> {
    let (version, version_consumed) =
        deserialize_partial::<Version>(payload).map_err(payload_error)?;
    let (input_count, input_count_consumed) = deserialize_partial::<VarInt>(
        payload
            .get(version_consumed..)
            .ok_or_else(|| WireError::Payload("truncated transaction inputs".to_owned()))?,
    )
    .map_err(payload_error)?;
    if input_count.0 != 0 {
        return Err(WireError::Payload(
            "transaction decoder could not recover an empty-input transaction".to_owned(),
        ));
    }
    let output_offset = version_consumed.saturating_add(input_count_consumed);
    let (output_count, output_count_consumed) = deserialize_partial::<VarInt>(
        payload
            .get(output_offset..)
            .ok_or_else(|| WireError::Payload("truncated transaction outputs".to_owned()))?,
    )
    .map_err(payload_error)?;
    let output_count = usize::try_from(output_count.0)
        .map_err(|_| WireError::Payload("transaction output count is too large".to_owned()))?;
    if output_count > MAX_TRANSACTION_OUTPUTS {
        return Err(WireError::Payload(
            "transaction output count is too large".to_owned(),
        ));
    }
    let mut offset = output_offset.saturating_add(output_count_consumed);
    let remaining_len = payload.len().saturating_sub(offset);
    let max_outputs_from_payload =
        remaining_len.saturating_sub(std::mem::size_of::<u32>()) / MIN_SERIALIZED_TXOUT_SIZE;
    if output_count > max_outputs_from_payload {
        return Err(WireError::Payload(
            "transaction output count exceeds payload size".to_owned(),
        ));
    }
    let mut output = Vec::with_capacity(output_count);
    for _ in 0..output_count {
        let (txout, consumed) = deserialize_partial::<bitcoin::TxOut>(
            payload
                .get(offset..)
                .ok_or_else(|| WireError::Payload("truncated transaction output".to_owned()))?,
        )
        .map_err(payload_error)?;
        output.push(txout);
        offset = offset.saturating_add(consumed);
    }
    let (lock_time, lock_time_consumed) = deserialize_partial::<LockTime>(
        payload
            .get(offset..)
            .ok_or_else(|| WireError::Payload("truncated transaction locktime".to_owned()))?,
    )
    .map_err(payload_error)?;
    offset = offset.saturating_add(lock_time_consumed);
    Ok((
        Transaction {
            version,
            lock_time,
            input: Vec::new(),
            output,
        },
        offset,
    ))
}

fn decode_payload(command: &str, payload: &[u8]) -> Result<Message, WireError> {
    let mut reader = Reader::new(payload);
    let message = match command {
        "version" => Message::Version(decode_version(&mut reader)?),
        "verack" => Message::Verack,
        "getaddr" => Message::GetAddr,
        "sendaddrv2" => Message::SendAddrV2,
        "sendheaders" => Message::SendHeaders,
        "wtxidrelay" => Message::WtxidRelay,
        "sendtxrcncl" => Message::SendTxRcncl(SendTxRcnclMessage {
            version: reader.u32_le()?,
            salt: reader.u64_le()?,
        }),
        "mempool" => Message::Mempool,
        "addr" => Message::Addr(decode_addr(&mut reader)?),
        "addrv2" => Message::AddrV2(decode_addr_v2(&mut reader)?),
        "ping" => Message::Ping(if reader.remaining() == 0 {
            0
        } else {
            reader.u64_le()?
        }),
        "pong" => {
            if reader.remaining() == 0 {
                Message::Pong(0)
            } else if reader.remaining() == 8 {
                Message::Pong(reader.u64_le()?)
            } else {
                let payload = reader.bytes(reader.remaining())?.to_vec();
                Message::Unknown {
                    command: "pong".to_owned(),
                    payload,
                }
            }
        }
        "getheaders" => Message::GetHeaders(decode_getheaders(&mut reader)?),
        "getblocks" => Message::GetBlocks(decode_getheaders(&mut reader)?),
        "headers" => Message::Headers(decode_headers(&mut reader)?),
        "inv" => Message::Inv(decode_inventory(&mut reader)?),
        "getdata" => Message::GetData(decode_inventory(&mut reader)?),
        "notfound" => Message::NotFound(decode_inventory(&mut reader)?),
        "block" => Message::Block(decode_block_core_compatible(payload)?),
        "merkleblock" => Message::MerkleBlock(deserialize(payload).map_err(payload_error)?),
        "tx" => Message::Transaction(decode_transaction_core_compatible(payload)?),
        "filterload" => Message::FilterLoad(deserialize(payload).map_err(payload_error)?),
        "filteradd" => Message::FilterAdd(deserialize(payload).map_err(payload_error)?),
        "filterclear" => Message::FilterClear,
        "feefilter" => Message::FeeFilter(reader.i64_le()?),
        "sendcmpct" => Message::SendCmpct {
            announce: reader.u8()? != 0,
            version: reader.u64_le()?,
        },
        "cmpctblock" => Message::CompactBlock(
            deserialize::<CmpctBlock>(payload)
                .map_err(payload_error)?
                .compact_block,
        ),
        "getblocktxn" => Message::GetBlockTxn(
            deserialize::<GetBlockTxn>(payload)
                .map_err(payload_error)?
                .txs_request,
        ),
        "blocktxn" => Message::BlockTxn(
            deserialize::<BlockTxn>(payload)
                .map_err(payload_error)?
                .transactions,
        ),
        "getcfilters" => Message::GetCFilters(deserialize(payload).map_err(payload_error)?),
        "cfilter" => Message::CFilter(deserialize(payload).map_err(payload_error)?),
        "getcfheaders" => Message::GetCFHeaders(deserialize(payload).map_err(payload_error)?),
        "cfheaders" => Message::CFHeaders(deserialize(payload).map_err(payload_error)?),
        "getcfcheckpt" => Message::GetCFCheckpt(deserialize(payload).map_err(payload_error)?),
        "cfcheckpt" => Message::CFCheckpt(deserialize(payload).map_err(payload_error)?),
        other => Message::Unknown {
            command: other.to_owned(),
            payload: payload.to_vec(),
        },
    };
    if reader.remaining() != 0
        && !matches!(
            message,
            Message::Block(_)
                | Message::MerkleBlock(_)
                | Message::Transaction(_)
                | Message::FilterLoad(_)
                | Message::FilterAdd(_)
                | Message::FilterClear
                | Message::CompactBlock(_)
                | Message::GetBlockTxn(_)
                | Message::BlockTxn(_)
                | Message::GetCFilters(_)
                | Message::CFilter(_)
                | Message::GetCFHeaders(_)
                | Message::CFHeaders(_)
                | Message::GetCFCheckpt(_)
                | Message::CFCheckpt(_)
                | Message::Unknown { .. }
        )
    {
        return Err(WireError::Payload("trailing bytes".to_owned()));
    }
    Ok(message)
}

fn encode_version(version: &VersionMessage, out: &mut Vec<u8>) -> Result<()> {
    if version.user_agent.len() > MAX_USER_AGENT_LENGTH {
        bail!("user agent exceeds Core's 256-byte limit");
    }
    put_i32(version.version, out);
    put_u64(version.services, out);
    put_i64(version.timestamp, out);
    put_u64(version.receiver_services, out);
    out.extend_from_slice(&version.receiver_address);
    out.extend_from_slice(&version.receiver_port.to_be_bytes());
    put_u64(version.sender_services, out);
    out.extend_from_slice(&version.sender_address);
    out.extend_from_slice(&version.sender_port.to_be_bytes());
    put_u64(version.nonce, out);
    put_compact_size(version.user_agent.len(), out)?;
    out.extend_from_slice(version.user_agent.as_bytes());
    put_i32(version.start_height, out);
    out.push(u8::from(version.relay));
    Ok(())
}

fn decode_version(reader: &mut Reader<'_>) -> Result<VersionMessage, WireError> {
    let version = reader.i32_le()?;
    let services = reader.u64_le()?;
    let timestamp = reader.i64_le()?;
    let receiver_services = reader.u64_le()?;
    let receiver_address = reader.array::<16>()?;
    let receiver_port = reader.u16_be()?;
    let (sender_services, sender_address, sender_port, nonce) = if reader.remaining() != 0 {
        (
            reader.u64_le()?,
            reader.array::<16>()?,
            reader.u16_be()?,
            reader.u64_le()?,
        )
    } else {
        (0, [0; 16], 0, 1)
    };
    let user_agent = if reader.remaining() != 0 {
        let user_agent_len = usize::try_from(reader.compact_size()?)
            .map_err(|_| WireError::Payload("user agent length is out of range".to_owned()))?;
        if user_agent_len > MAX_USER_AGENT_LENGTH {
            return Err(WireError::Payload(
                "user agent exceeds Core's 256-byte limit".to_owned(),
            ));
        }
        String::from_utf8(reader.bytes(user_agent_len)?.to_vec())
            .map_err(|_| WireError::Payload("user agent is not UTF-8".to_owned()))?
    } else {
        String::new()
    };
    let start_height = if reader.remaining() != 0 {
        reader.i32_le()?
    } else {
        -1
    };
    let relay = if reader.remaining() == 0 {
        true
    } else {
        reader.u8()? != 0
    };
    Ok(VersionMessage {
        version,
        services,
        timestamp,
        receiver_services,
        receiver_address,
        receiver_port,
        sender_services,
        sender_address,
        sender_port,
        nonce,
        user_agent,
        start_height,
        relay,
    })
}

fn encode_inventory(items: &[Inventory], out: &mut Vec<u8>) -> Result<()> {
    if items.len() > MAX_INVENTORY_ITEMS {
        return Err(WireError::Payload("too many inventory items".to_owned()).into());
    }
    put_compact_size(items.len(), out)?;
    for item in items {
        put_u32(item.kind.as_u32(), out);
        out.extend_from_slice(&item.hash.to_byte_array());
    }
    Ok(())
}

fn decode_inventory(reader: &mut Reader<'_>) -> Result<Vec<Inventory>, WireError> {
    let count = bounded_count(reader.compact_size()?)?;
    if count > MAX_INVENTORY_ITEMS {
        return Err(WireError::Payload("too many inventory items".to_owned()));
    }
    if count > reader.remaining() / INVENTORY_ITEM_SIZE {
        return Err(WireError::Payload(
            "inventory count exceeds payload size".to_owned(),
        ));
    }
    let mut items = Vec::with_capacity(count);
    for _ in 0..count {
        items.push(Inventory {
            kind: InventoryType::from_u32(reader.u32_le()?),
            hash: BlockHash::from_byte_array(reader.array::<32>()?),
        });
    }
    Ok(items)
}

fn decode_addr(reader: &mut Reader<'_>) -> Result<Vec<NetworkAddress>, WireError> {
    let count = bounded_count(reader.compact_size()?)?;
    if count > 1_000 {
        return Err(WireError::Payload("too many address records".to_owned()));
    }
    if count > reader.remaining() / ADDR_ITEM_SIZE {
        return Err(WireError::Payload(
            "address count exceeds payload size".to_owned(),
        ));
    }
    let mut entries = Vec::with_capacity(count);
    for _ in 0..count {
        let time = reader.u32_le()?;
        let services = reader.u64_le()?;
        let address = reader.array::<16>()?;
        let port = reader.u16_be()?;
        entries.push(NetworkAddress {
            time,
            services,
            address,
            port,
        });
    }
    Ok(entries)
}

fn decode_addr_v2(reader: &mut Reader<'_>) -> Result<Vec<NetworkAddressV2>, WireError> {
    let count = bounded_count(reader.compact_size()?)?;
    if count > 1_000 {
        return Err(WireError::Payload("too many address records".to_owned()));
    }
    if count > reader.remaining() / ADDRV2_MIN_ITEM_SIZE {
        return Err(WireError::Payload(
            "address count exceeds payload size".to_owned(),
        ));
    }
    let mut entries = Vec::with_capacity(count);
    for _ in 0..count {
        let time = reader.u32_le()?;
        let services = reader.compact_size()?;
        let network = reader.u8()?;
        let address_length = usize::try_from(reader.compact_size()?)
            .map_err(|_| WireError::Payload("address length is out of range".to_owned()))?;
        if address_length > 512 {
            return Err(WireError::Payload("address record is too large".to_owned()));
        }
        let address = reader.bytes(address_length)?.to_vec();
        let port = reader.u16_be()?;
        entries.push(NetworkAddressV2 {
            time,
            services,
            network,
            address,
            port,
        });
    }
    Ok(entries)
}

fn decode_getheaders(reader: &mut Reader<'_>) -> Result<GetHeadersMessage, WireError> {
    let version = reader.i32_le()?;
    let count = bounded_count(reader.compact_size()?)?;
    if count > MAX_LOCATOR_HASHES {
        return Err(WireError::Payload("too many locator hashes".to_owned()));
    }
    let hash_bytes = reader.remaining().saturating_sub(32);
    if count > hash_bytes / 32 {
        return Err(WireError::Payload(
            "locator hash count exceeds payload size".to_owned(),
        ));
    }
    let mut locator_hashes = Vec::with_capacity(count);
    for _ in 0..count {
        locator_hashes.push(BlockHash::from_byte_array(reader.array::<32>()?));
    }
    Ok(GetHeadersMessage {
        version,
        locator_hashes,
        stop_hash: BlockHash::from_byte_array(reader.array::<32>()?),
    })
}

fn decode_headers(reader: &mut Reader<'_>) -> Result<Vec<bitcoin::block::Header>, WireError> {
    let count = bounded_count(reader.compact_size()?)?;
    if count > 2_000 {
        return Err(WireError::Payload("too many headers".to_owned()));
    }
    if count > reader.remaining() / HEADER_ITEM_MIN_SIZE {
        return Err(WireError::Payload(
            "header count exceeds payload size".to_owned(),
        ));
    }
    let mut headers = Vec::with_capacity(count);
    for _ in 0..count {
        let bytes = reader.bytes(80)?;
        headers.push(deserialize(bytes).map_err(payload_error)?);
        // Core consumes the transaction-count field but intentionally ignores
        // its value. Keep the same wire compatibility: a nonzero count does
        // not turn an otherwise decodable header message into a disconnect.
        reader.compact_size()?;
    }
    Ok(headers)
}

fn payload_error(error: bitcoin::consensus::encode::Error) -> WireError {
    WireError::Payload(error.to_string())
}

fn put_compact_size(value: usize, out: &mut Vec<u8>) -> Result<()> {
    put_compact_size_u64(value as u64, out);
    Ok(())
}

fn put_compact_size_u64(value: u64, out: &mut Vec<u8>) {
    if value < 0xfd {
        out.push(value as u8);
    } else if value <= u64::from(u16::MAX) {
        out.push(0xfd);
        out.extend_from_slice(&(value as u16).to_le_bytes());
    } else if value <= u64::from(u32::MAX) {
        out.push(0xfe);
        out.extend_from_slice(&(value as u32).to_le_bytes());
    } else {
        out.push(0xff);
        out.extend_from_slice(&value.to_le_bytes());
    }
}

fn put_u32(value: u32, out: &mut Vec<u8>) {
    out.extend_from_slice(&value.to_le_bytes());
}
fn put_u64(value: u64, out: &mut Vec<u8>) {
    out.extend_from_slice(&value.to_le_bytes());
}
fn put_i32(value: i32, out: &mut Vec<u8>) {
    out.extend_from_slice(&value.to_le_bytes());
}
fn put_i64(value: i64, out: &mut Vec<u8>) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn bounded_count(value: u64) -> Result<usize, WireError> {
    let value = usize::try_from(value).map_err(|_| WireError::CompactSize)?;
    if value > 1_000_000 {
        return Err(WireError::Payload("vector count exceeds limit".to_owned()));
    }
    Ok(value)
}

struct Reader<'a> {
    cursor: Cursor<&'a [u8]>,
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self {
            cursor: Cursor::new(bytes),
        }
    }

    fn remaining(&self) -> usize {
        self.cursor.get_ref().len() - self.cursor.position() as usize
    }

    fn bytes(&mut self, length: usize) -> Result<&'a [u8], WireError> {
        if length > self.remaining() {
            return Err(WireError::Payload("unexpected end of payload".to_owned()));
        }
        let start = self.cursor.position() as usize;
        self.cursor.set_position((start + length) as u64);
        Ok(&self.cursor.get_ref()[start..start + length])
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], WireError> {
        self.bytes(N)?
            .try_into()
            .map_err(|_| WireError::Payload("invalid fixed-size field".to_owned()))
    }

    fn u8(&mut self) -> Result<u8, WireError> {
        Ok(self.bytes(1)?[0])
    }

    fn u16_be(&mut self) -> Result<u16, WireError> {
        Ok(u16::from_be_bytes(self.array()?))
    }

    fn u32_le(&mut self) -> Result<u32, WireError> {
        Ok(u32::from_le_bytes(self.array()?))
    }

    fn u64_le(&mut self) -> Result<u64, WireError> {
        Ok(u64::from_le_bytes(self.array()?))
    }

    fn i32_le(&mut self) -> Result<i32, WireError> {
        Ok(i32::from_le_bytes(self.array()?))
    }

    fn i64_le(&mut self) -> Result<i64, WireError> {
        Ok(i64::from_le_bytes(self.array()?))
    }

    fn compact_size(&mut self) -> Result<u64, WireError> {
        match self.u8()? {
            value @ 0..=0xfc => Ok(value as u64),
            0xfd => {
                let value = u16::from_le_bytes(self.array()?);
                if value < 0xfd {
                    return Err(WireError::CompactSize);
                }
                Ok(value as u64)
            }
            0xfe => {
                let value = u32::from_le_bytes(self.array()?);
                if value <= u16::MAX as u32 {
                    return Err(WireError::CompactSize);
                }
                Ok(value as u64)
            }
            0xff => {
                let value = u64::from_le_bytes(self.array()?);
                if value <= u32::MAX as u64 {
                    return Err(WireError::CompactSize);
                }
                Ok(value)
            }
        }
    }
}

fn chrono_like_unix_time() -> i64 {
    crate::time::unix_time_i64()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn signet_message_magic_is_derived_from_the_serialized_challenge() {
        assert_eq!(
            network_magic_with_signet_challenge(Network::Signet, None),
            [0x0a, 0x03, 0xcf, 0x40]
        );
        assert_eq!(
            network_magic_with_signet_challenge(Network::Signet, Some(&[0x51])),
            [0x54, 0xd2, 0x6f, 0xbd]
        );
        assert_eq!(
            network_magic_with_signet_challenge(Network::Regtest, Some(&[0x51])),
            network_magic(Network::Regtest)
        );
    }

    #[test]
    fn custom_signet_frames_use_the_derived_message_start() {
        let magic = network_magic_with_signet_challenge(Network::Signet, Some(&[0x51]));
        let frame = encode_message_with_magic(magic, &Message::Ping(42)).unwrap();

        assert_eq!(&frame[..4], &magic);
        assert_eq!(
            decode_message_with_magic(magic, &frame).unwrap(),
            Message::Ping(42)
        );
        assert!(decode_message(Network::Signet, &frame).is_err());
    }

    #[test]
    fn ping_round_trip() {
        let frame = encode_message(Network::Regtest, &Message::Ping(42)).unwrap();
        assert_eq!(
            decode_message(Network::Regtest, &frame).unwrap(),
            Message::Ping(42)
        );
    }

    #[test]
    fn legacy_ping_and_pong_payloads_are_empty() {
        for (command, expected) in [("ping", Message::Ping(0)), ("pong", Message::Pong(0))] {
            let frame = encode_message(
                Network::Regtest,
                &Message::Unknown {
                    command: command.to_owned(),
                    payload: Vec::new(),
                },
            )
            .unwrap();
            assert_eq!(decode_message(Network::Regtest, &frame).unwrap(), expected);
        }
    }

    #[test]
    fn rejects_malformed_command_padding() {
        let frame = encode_message(Network::Regtest, &Message::Ping(42)).unwrap();
        let mut nonzero_padding = frame.clone();
        nonzero_padding[4 + 5] = b'x';
        assert!(decode_message(Network::Regtest, &nonzero_padding).is_err());

        let mut empty_command = frame;
        empty_command[4] = 0;
        assert!(decode_message(Network::Regtest, &empty_command).is_err());

        assert!(
            encode_message(
                Network::Regtest,
                &Message::Unknown {
                    command: "bad command".to_owned(),
                    payload: Vec::new(),
                }
            )
            .is_err()
        );
    }

    #[test]
    fn version_round_trip() {
        let message = Message::Version(VersionMessage::new(12, 99));
        let frame = encode_message(Network::Bitcoin, &message).unwrap();
        assert_eq!(decode_message(Network::Bitcoin, &frame).unwrap(), message);
    }

    #[test]
    fn version_accepts_core_legacy_trailing_field_omissions() {
        let message = VersionMessage::new(12, 99);
        let mut expected = message.clone();
        expected.sender_services = 0;
        expected.sender_address = [0; 16];
        expected.sender_port = 0;
        expected.nonce = 1;
        expected.user_agent.clear();
        expected.start_height = -1;
        expected.relay = true;

        let mut frame = encode_message(Network::Bitcoin, &Message::Version(message)).unwrap();
        frame.truncate(24 + 46);
        frame[16..20].copy_from_slice(&46u32.to_le_bytes());
        let frame_checksum = checksum(&frame[24..]);
        frame[20..24].copy_from_slice(&frame_checksum);

        assert_eq!(
            decode_message(Network::Bitcoin, &frame).unwrap(),
            Message::Version(expected)
        );
    }

    #[test]
    fn version_user_agent_uses_core_length_limit() {
        let mut accepted = VersionMessage::new(12, 99);
        accepted.user_agent = "x".repeat(256);
        let frame = encode_message(Network::Bitcoin, &Message::Version(accepted.clone())).unwrap();
        assert_eq!(
            decode_message(Network::Bitcoin, &frame).unwrap(),
            Message::Version(accepted)
        );

        let mut rejected = VersionMessage::new(12, 99);
        rejected.user_agent = "x".repeat(257);
        assert!(encode_message(Network::Bitcoin, &Message::Version(rejected)).is_err());
    }

    #[test]
    fn headers_ignore_transaction_counts_like_core() {
        let header = bitcoin::blockdata::constants::genesis_block(Network::Regtest).header;
        let mut frame = encode_message(Network::Regtest, &Message::Headers(vec![header])).unwrap();
        frame[24 + 1 + 80] = 1;
        let frame_checksum = checksum(&frame[24..]);
        frame[20..24].copy_from_slice(&frame_checksum);
        assert_eq!(
            decode_message(Network::Regtest, &frame).unwrap(),
            Message::Headers(vec![header])
        );
    }

    #[test]
    fn decodes_core_empty_legacy_transaction() {
        let transaction = decode_transaction_core_compatible(&[
            2, 0, 0, 0, // version
            0, // input count
            0, // output count
            0, 0, 0, 0, // locktime
        ])
        .unwrap();
        assert_eq!(transaction.version, Version::non_standard(2));
        assert!(transaction.input.is_empty());
        assert!(transaction.output.is_empty());
        assert_eq!(transaction.lock_time, LockTime::from_consensus(0));
    }

    #[test]
    fn rejects_block_transaction_count_that_cannot_fit_in_payload() {
        let header = bitcoin::blockdata::constants::genesis_block(Network::Regtest).header;
        let mut payload = serialize(&header);
        put_compact_size(MAX_BLOCK_TRANSACTIONS, &mut payload).unwrap();

        assert!(decode_block_core_compatible(&payload).is_err());
    }

    #[test]
    fn rejects_empty_input_output_count_that_cannot_fit_in_payload() {
        let mut payload = Vec::new();
        payload.extend_from_slice(&2i32.to_le_bytes());
        put_compact_size(0, &mut payload).unwrap();
        put_compact_size(MAX_TRANSACTION_OUTPUTS, &mut payload).unwrap();

        assert!(decode_empty_input_transaction(&payload).is_err());
    }

    #[tokio::test]
    async fn recoverable_v1_frames_are_accounted_and_skipped() {
        let mut bad_checksum = encode_message(Network::Regtest, &Message::Ping(1)).unwrap();
        bad_checksum[20] ^= 1;
        let mut bad_command = encode_message(Network::Regtest, &Message::Verack).unwrap();
        bad_command[11] = b'x';
        let valid = encode_message(Network::Regtest, &Message::Pong(2)).unwrap();
        let total = bad_checksum.len() + bad_command.len() + valid.len();
        let (mut writer, mut reader) = tokio::io::duplex(total);
        writer.write_all(&bad_checksum).await.unwrap();
        writer.write_all(&bad_command).await.unwrap();
        writer.write_all(&valid).await.unwrap();
        drop(writer);

        let (message, size) = read_message_with_size_allow_reject(&mut reader, Network::Regtest)
            .await
            .unwrap();
        assert!(message.is_none());
        assert_eq!(size, bad_checksum.len());
        let (message, size) = read_message_with_size_allow_reject(&mut reader, Network::Regtest)
            .await
            .unwrap();
        assert!(message.is_none());
        assert_eq!(size, bad_command.len());
        let (message, size) = read_message_with_size_allow_reject(&mut reader, Network::Regtest)
            .await
            .unwrap();
        assert_eq!(message, Some(Message::Pong(2)));
        assert_eq!(size, valid.len());
    }

    #[tokio::test]
    async fn buffered_v1_reader_survives_cancellation_mid_frame() {
        let first = encode_message(Network::Regtest, &Message::Ping(1)).unwrap();
        let second = encode_message(Network::Regtest, &Message::Pong(2)).unwrap();
        let (mut writer, reader) = tokio::io::duplex(first.len() + second.len());
        writer.write_all(&first[..HEADER_SIZE + 2]).await.unwrap();
        let mut reader = MessageReader::new(reader);

        let timed_out = tokio::time::timeout(
            std::time::Duration::from_millis(1),
            reader.read_message_with_size_allow_reject(Network::Regtest),
        )
        .await;
        assert!(timed_out.is_err());

        writer.write_all(&first[HEADER_SIZE + 2..]).await.unwrap();
        writer.write_all(&second).await.unwrap();
        assert_eq!(
            reader
                .read_message_with_size_allow_reject(Network::Regtest)
                .await
                .unwrap()
                .0,
            Some(Message::Ping(1))
        );
        assert_eq!(
            reader
                .read_message_with_size_allow_reject(Network::Regtest)
                .await
                .unwrap()
                .0,
            Some(Message::Pong(2))
        );
    }

    #[test]
    fn invalid_v2_message_types_are_recoverable() {
        assert!(!v2_message_type_is_valid(&[]));
        assert!(!v2_message_type_is_valid(&[0xff]));
        assert!(!v2_message_type_is_valid(&[0]));
        assert!(v2_message_type_is_valid(
            &encode_v2_message(&Message::Ping(42)).unwrap()
        ));
    }

    #[test]
    fn bip324_malformed_transactions_use_core_optional_data_diagnostic() {
        let transaction_payload = [0u8; 4].into_iter().chain([0, 2, 0, 0]).collect::<Vec<_>>();

        let mut short_id_payload = vec![21];
        short_id_payload.extend_from_slice(&transaction_payload);
        assert_eq!(
            v2_transaction_optional_data_error(&short_id_payload),
            Some("Unknown transaction optional data")
        );

        let mut extended_payload = vec![0];
        extended_payload.extend_from_slice(b"tx\0\0\0\0\0\0\0\0\0\0");
        extended_payload.extend_from_slice(&transaction_payload);
        assert_eq!(
            v2_transaction_optional_data_error(&extended_payload),
            Some("Unknown transaction optional data")
        );
        assert_eq!(
            v2_transaction_optional_data_error(&encode_v2_message(&Message::Ping(1)).unwrap()),
            None
        );
    }

    #[test]
    fn version_user_agent_comments_follow_bip14_format() {
        let message = VersionMessage::with_bloom_and_comments(
            12,
            99,
            false,
            &["lab".to_owned(), "operator".to_owned()],
        );
        assert_eq!(message.user_agent, "/bitcoind-rs:0.1.0(lab; operator)/");
        let frame = encode_message(Network::Bitcoin, &Message::Version(message.clone())).unwrap();
        assert_eq!(
            decode_message(Network::Bitcoin, &frame).unwrap(),
            Message::Version(message)
        );
    }

    #[test]
    fn tx_reconciliation_round_trip_uses_core_payload_layout() {
        let message = Message::SendTxRcncl(SendTxRcnclMessage {
            version: 1,
            salt: 2,
        });
        let frame = encode_message(Network::Regtest, &message).unwrap();
        assert_eq!(decode_message(Network::Regtest, &frame).unwrap(), message);

        let mut malformed = frame;
        malformed[16..20].copy_from_slice(&13u32.to_le_bytes());
        malformed.push(0);
        let checksum = bitcoin::hashes::sha256d::Hash::hash(&malformed[24..]).to_byte_array();
        malformed[20..24].copy_from_slice(&checksum[..4]);
        assert!(decode_message(Network::Regtest, &malformed).is_err());
    }

    #[test]
    fn unknown_bounded_message_is_preserved() {
        let message = Message::Unknown {
            command: "mystery".to_owned(),
            payload: Vec::new(),
        };
        let frame = encode_message(Network::Regtest, &message).unwrap();
        assert_eq!(decode_message(Network::Regtest, &frame).unwrap(), message);
    }

    #[test]
    fn rejects_oversized_inventory_and_locator_vectors() {
        let mut inventory = Vec::new();
        put_compact_size(50_001, &mut inventory).unwrap();
        assert!(decode_inventory(&mut Reader::new(&inventory)).is_err());

        let mut short_inventory = Vec::new();
        put_compact_size(MAX_INVENTORY_ITEMS, &mut short_inventory).unwrap();
        assert!(decode_inventory(&mut Reader::new(&short_inventory)).is_err());

        let mut locator = Vec::new();
        put_i32(VersionMessage::PROTOCOL_VERSION, &mut locator);
        put_compact_size(102, &mut locator).unwrap();
        locator.extend_from_slice(&[0; 32 * 103]);
        assert!(decode_getheaders(&mut Reader::new(&locator)).is_err());

        let mut short_locator = Vec::new();
        put_i32(VersionMessage::PROTOCOL_VERSION, &mut short_locator);
        put_compact_size(MAX_LOCATOR_HASHES, &mut short_locator).unwrap();
        assert!(decode_getheaders(&mut Reader::new(&short_locator)).is_err());

        let mut short_headers = Vec::new();
        put_compact_size(2_000, &mut short_headers).unwrap();
        assert!(decode_headers(&mut Reader::new(&short_headers)).is_err());

        let mut short_addr = Vec::new();
        put_compact_size(1_000, &mut short_addr).unwrap();
        assert!(decode_addr(&mut Reader::new(&short_addr)).is_err());

        let mut short_addrv2 = Vec::new();
        put_compact_size(1_000, &mut short_addrv2).unwrap();
        assert!(decode_addr_v2(&mut Reader::new(&short_addrv2)).is_err());
    }

    #[test]
    fn uses_core_legacy_protocol_message_size_limit() {
        assert_eq!(MAX_MESSAGE_SIZE, 4_000_000);
        let at_limit = Message::Unknown {
            command: "mystery".to_owned(),
            payload: vec![0; MAX_MESSAGE_SIZE],
        };
        assert!(encode_message(Network::Regtest, &at_limit).is_ok());
        let over_limit = Message::Unknown {
            command: "mystery".to_owned(),
            payload: vec![0; MAX_MESSAGE_SIZE + 1],
        };
        assert!(encode_message(Network::Regtest, &over_limit).is_err());
    }

    #[test]
    fn malformed_wire_frames_do_not_panic() {
        // Keep a deterministic parser-fuzz smoke test in the regular suite.
        // Each payload-bearing command is fed truncated, structurally random,
        // and boundary-sized payloads with a valid frame checksum. The parser
        // must reject malformed application data as an error, never unwind.
        const COMMANDS: &[&str] = &[
            "version",
            "addr",
            "addrv2",
            "ping",
            "pong",
            "getheaders",
            "getblocks",
            "headers",
            "inv",
            "getdata",
            "notfound",
            "block",
            "merkleblock",
            "tx",
            "filterload",
            "filteradd",
            "feefilter",
            "sendcmpct",
            "cmpctblock",
            "getblocktxn",
            "blocktxn",
            "getcfilters",
            "cfilter",
            "getcfheaders",
            "cfheaders",
            "getcfcheckpt",
            "cfcheckpt",
        ];
        const LENGTHS: &[usize] = &[0, 1, 2, 7, 8, 16, 32, 80, 256, 1024];

        let mut state = 0x6a09_e667_f3bc_c908_u64;
        let next_byte = |state: &mut u64| {
            *state ^= state.wrapping_shl(13);
            *state ^= state.wrapping_shr(7);
            *state ^= state.wrapping_shl(17);
            (*state >> 24) as u8
        };

        for command in COMMANDS {
            for &length in LENGTHS {
                let mut payload = vec![0; length];
                for byte in &mut payload {
                    *byte = next_byte(&mut state);
                }

                let mut frame = Vec::with_capacity(HEADER_SIZE + payload.len());
                frame.extend_from_slice(&network_magic(Network::Regtest));
                let mut command_bytes = [0; 12];
                command_bytes[..command.len()].copy_from_slice(command.as_bytes());
                frame.extend_from_slice(&command_bytes);
                frame.extend_from_slice(&(payload.len() as u32).to_le_bytes());
                frame.extend_from_slice(&checksum(&payload));
                frame.extend_from_slice(&payload);

                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let _ = decode_message(Network::Regtest, &frame);
                }));
                assert!(
                    result.is_ok(),
                    "parser panicked for {command} payload length {length}"
                );
            }
        }

        for length in [0, 1, 2, 13, 32, 256, 1024] {
            let mut payload = vec![0; length];
            for byte in &mut payload {
                *byte = next_byte(&mut state);
            }
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let _ = decode_v2_message(&payload);
            }));
            assert!(
                result.is_ok(),
                "BIP324 parser panicked for payload length {length}"
            );
        }
    }

    #[test]
    fn uses_bip339_wtx_inventory_type_and_keeps_legacy_witness_getdata() {
        assert_eq!(InventoryType::WitnessTransaction.as_u32(), 5);
        assert_eq!(
            InventoryType::from_u32(5),
            InventoryType::WitnessTransaction
        );
        assert_eq!(
            InventoryType::from_u32(0x4000_0001),
            InventoryType::LegacyWitnessTransaction
        );
        assert!(InventoryType::LegacyWitnessTransaction.is_witness_transaction());
        assert!(!InventoryType::LegacyWitnessTransaction.uses_wtxid());
        assert!(InventoryType::WitnessTransaction.uses_wtxid());
        assert_eq!(
            InventoryType::LegacyWitnessTransaction.as_u32(),
            0x4000_0001
        );
    }

    #[test]
    fn bip324_application_messages_round_trip_with_short_and_extended_ids() {
        for message in [Message::Ping(42), Message::Verack, Message::WtxidRelay] {
            let encoded = encode_v2_message(&message).unwrap();
            let decoded = decode_v2_message(&encoded).unwrap();
            assert_eq!(decoded, message);
        }

        let message = Message::Unknown {
            command: "futurecmd".to_owned(),
            payload: vec![1, 2, 3],
        };
        let encoded = encode_v2_message(&message).unwrap();
        assert_eq!(encoded[0], 0);
        assert_eq!(decode_v2_message(&encoded).unwrap(), message);
    }

    #[test]
    fn addrv2_round_trip_uses_compact_services_and_network_ids() {
        let message = Message::AddrV2(vec![
            NetworkAddressV2 {
                time: 123,
                services: NODE_NETWORK | NODE_WITNESS,
                network: 1,
                address: vec![127, 0, 0, 1],
                port: 8333,
            },
            NetworkAddressV2 {
                time: 456,
                services: NODE_NETWORK,
                network: 2,
                address: vec![0; 16],
                port: 18333,
            },
        ]);
        let frame = encode_message(Network::Regtest, &message).unwrap();
        assert_eq!(decode_message(Network::Regtest, &frame).unwrap(), message);
    }

    #[test]
    fn address_round_trip_includes_timestamp_and_services() {
        let message = Message::Addr(vec![NetworkAddress {
            time: 123,
            services: NODE_NETWORK | NODE_WITNESS,
            address: [7; 16],
            port: 8333,
        }]);
        let frame = encode_message(Network::Regtest, &message).unwrap();
        assert_eq!(decode_message(Network::Regtest, &frame).unwrap(), message);
    }

    #[test]
    fn compact_block_messages_round_trip() {
        use bitcoin::absolute::LockTime;
        use bitcoin::bip152::HeaderAndShortIds;
        use bitcoin::block::{Header, Version as BlockVersion};
        use bitcoin::blockdata::script::ScriptBuf;
        use bitcoin::blockdata::transaction::{OutPoint, TxIn, TxOut, Version};
        use bitcoin::blockdata::witness::Witness;
        use bitcoin::{Amount, Block, TxMerkleNode};

        let transaction = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::null(),
                script_sig: ScriptBuf::from_bytes(vec![1, 2]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(1),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let mut block = Block {
            header: Header {
                version: BlockVersion::TWO,
                prev_blockhash: BlockHash::all_zeros(),
                merkle_root: TxMerkleNode::all_zeros(),
                time: 1,
                bits: bitcoin::pow::CompactTarget::from_consensus(0x207f_ffff),
                nonce: 0,
            },
            txdata: vec![transaction],
        };
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        let compact = HeaderAndShortIds::from_block(&block, 7, 2, &[]).unwrap();
        let message = Message::CompactBlock(compact);
        let frame = encode_message(Network::Regtest, &message).unwrap();
        assert_eq!(decode_message(Network::Regtest, &frame).unwrap(), message);
    }

    #[test]
    fn compact_filter_messages_round_trip() {
        use bitcoin::bip158::{FilterHash, FilterHeader};

        let block_hash = BlockHash::from_byte_array([3; 32]);
        let message = Message::GetCFilters(GetCFilters {
            filter_type: 0,
            start_height: 12,
            stop_hash: block_hash,
        });
        let frame = encode_message(Network::Regtest, &message).unwrap();
        assert_eq!(decode_message(Network::Regtest, &frame).unwrap(), message);

        let message = Message::CFHeaders(CFHeaders {
            filter_type: 0,
            stop_hash: block_hash,
            previous_filter_header: FilterHeader::from_byte_array([4; 32]),
            filter_hashes: vec![FilterHash::from_byte_array([5; 32])],
        });
        let frame = encode_message(Network::Regtest, &message).unwrap();
        assert_eq!(decode_message(Network::Regtest, &frame).unwrap(), message);
    }

    #[test]
    fn bip37_messages_round_trip() {
        use bitcoin::absolute::LockTime;
        use bitcoin::block::{Header, Version as BlockVersion};
        use bitcoin::blockdata::script::ScriptBuf;
        use bitcoin::blockdata::transaction::{OutPoint, TxIn, TxOut, Version};
        use bitcoin::blockdata::witness::Witness;
        use bitcoin::p2p::message_bloom::{BloomFlags, FilterAdd, FilterLoad};
        use bitcoin::{Amount, TxMerkleNode};

        let filter_load = Message::FilterLoad(FilterLoad {
            filter: vec![0xaa, 0x55, 0x01],
            hash_funcs: 7,
            tweak: 11,
            flags: BloomFlags::All,
        });
        let filter_add = Message::FilterAdd(FilterAdd {
            data: vec![1, 2, 3, 4],
        });
        for message in [filter_load, filter_add, Message::FilterClear] {
            let frame = encode_message(Network::Regtest, &message).unwrap();
            assert_eq!(decode_message(Network::Regtest, &frame).unwrap(), message);
        }

        let transaction = Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::null(),
                script_sig: ScriptBuf::from_bytes(vec![1]),
                sequence: bitcoin::Sequence::MAX,
                witness: Witness::default(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(1),
                script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
            }],
        };
        let mut block = Block {
            header: Header {
                version: BlockVersion::TWO,
                prev_blockhash: BlockHash::all_zeros(),
                merkle_root: TxMerkleNode::all_zeros(),
                time: 1,
                bits: bitcoin::pow::CompactTarget::from_consensus(0x207f_ffff),
                nonce: 0,
            },
            txdata: vec![transaction],
        };
        block.header.merkle_root = block.compute_merkle_root().unwrap();
        let merkle = MerkleBlock::from_block_with_predicate(&block, |_| true);
        let message = Message::MerkleBlock(merkle);
        let frame = encode_message(Network::Regtest, &message).unwrap();
        let decoded = decode_message(Network::Regtest, &frame).unwrap();
        let Message::MerkleBlock(decoded) = decoded else {
            panic!("decoded BIP37 message was not merkleblock");
        };
        let Message::MerkleBlock(expected) = message else {
            unreachable!();
        };
        let mut matches = Vec::new();
        let mut indexes = Vec::new();
        decoded.extract_matches(&mut matches, &mut indexes).unwrap();
        assert_eq!(decoded.header, expected.header);
        assert_eq!(matches, vec![block.txdata[0].compute_txid()]);
        assert_eq!(indexes, vec![0]);
    }
}
