//! Bitcoin peer-to-peer wire framing.
//!
//! The wire layer deliberately owns framing and message limits. Higher layers
//! only receive fully decoded messages, which makes it possible to apply the
//! same bounds to inbound peers and outbound requests.

use std::io::Cursor;

use anyhow::{Result, bail};
use bitcoin::bip152::{BlockTransactions, BlockTransactionsRequest, HeaderAndShortIds};
use bitcoin::consensus::encode::{deserialize, serialize};
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
const MAX_LOCATOR_HASHES: usize = 101;
const MAX_USER_AGENT_LENGTH: usize = 256;

pub const NODE_NETWORK: u64 = 1;
pub const NODE_BLOOM: u64 = 1 << 2;
pub const NODE_WITNESS: u64 = 1 << 3;
pub const NODE_NETWORK_LIMITED: u64 = 1 << 10;
pub const NODE_COMPACT_FILTERS: u64 = 1 << 6;
pub const NODE_P2P_V2: u64 = 1 << 11;

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
    #[error("invalid message checksum")]
    Checksum,
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

pub fn encode_message(network: Network, message: &Message) -> Result<Vec<u8>> {
    let payload = encode_payload(message)?;
    validate_payload_size(payload.len())?;
    let command = message.command();
    validate_command(command)?;
    let command = command.as_bytes();
    let mut frame = Vec::with_capacity(HEADER_SIZE + payload.len());
    frame.extend_from_slice(&network_magic(network));
    let mut command_bytes = [0u8; 12];
    command_bytes[..command.len()].copy_from_slice(command);
    frame.extend_from_slice(&command_bytes);
    frame.extend_from_slice(&(payload.len() as u32).to_le_bytes());
    frame.extend_from_slice(&checksum(&payload));
    frame.extend_from_slice(&payload);
    Ok(frame)
}

pub fn decode_message(network: Network, frame: &[u8]) -> Result<Message> {
    if frame.len() < HEADER_SIZE {
        bail!("short Bitcoin message frame");
    }
    let mut magic = [0u8; 4];
    magic.copy_from_slice(&frame[..4]);
    if magic != network_magic(network) {
        return Err(WireError::Magic(magic).into());
    }
    let command = decode_command(&frame[4..16])?;
    let length = u32::from_le_bytes(frame[16..20].try_into().expect("slice length")) as usize;
    if length > MAX_MESSAGE_SIZE {
        return Err(WireError::Oversized(length).into());
    }
    if frame.len() != HEADER_SIZE + length {
        bail!("message frame length does not match payload length");
    }
    if frame[20..24] != checksum(&frame[24..]) {
        return Err(WireError::Checksum.into());
    }
    decode_payload(command, &frame[24..]).map_err(Into::into)
}

pub async fn read_message<R: AsyncRead + Unpin>(
    reader: &mut R,
    network: Network,
) -> Result<Message> {
    Ok(read_message_with_size(reader, network).await?.0)
}

pub async fn read_message_with_size<R: AsyncRead + Unpin>(
    reader: &mut R,
    network: Network,
) -> Result<(Message, usize)> {
    let (frame, size) = read_frame_with_size(reader).await?;
    Ok((decode_message(network, &frame)?, size))
}

/// Read a v1 frame while preserving Core's distinction between a recoverable
/// message rejection and a fatal transport/framing error. Core discards a
/// complete frame with a bad checksum or invalid command header, accounts its
/// bytes as `*other*`, and continues reading the connection.
pub(crate) async fn read_message_with_size_allow_reject<R: AsyncRead + Unpin>(
    reader: &mut R,
    network: Network,
) -> Result<(Option<Message>, usize)> {
    let (frame, size) = read_frame_with_size(reader).await?;
    match decode_message(network, &frame) {
        Ok(message) => Ok((Some(message), size)),
        Err(_error) if frame_has_recoverable_error(network, &frame) => Ok((None, size)),
        Err(error) => Err(error),
    }
}

async fn read_frame_with_size<R: AsyncRead + Unpin>(reader: &mut R) -> Result<(Vec<u8>, usize)> {
    let mut header = [0u8; HEADER_SIZE];
    reader.read_exact(&mut header).await?;
    let length = u32::from_le_bytes(header[16..20].try_into().expect("slice length")) as usize;
    if length > MAX_MESSAGE_SIZE {
        return Err(WireError::Oversized(length).into());
    }
    let mut frame = Vec::with_capacity(HEADER_SIZE + length);
    frame.extend_from_slice(&header);
    frame.resize(HEADER_SIZE + length, 0);
    reader.read_exact(&mut frame[HEADER_SIZE..]).await?;
    let size = frame.len();
    Ok((frame, size))
}

fn frame_has_recoverable_error(network: Network, frame: &[u8]) -> bool {
    if frame.len() < HEADER_SIZE || frame[..4] != network_magic(network) {
        return false;
    }
    let command_valid = decode_command(&frame[4..16]).is_ok();
    let checksum_valid = frame[20..24] == checksum(&frame[24..]);
    !command_valid || !checksum_valid
}

pub async fn write_message<W: AsyncWrite + Unpin>(
    writer: &mut W,
    network: Network,
    message: &Message,
) -> Result<()> {
    write_message_with_size(writer, network, message)
        .await
        .map(|_| ())
}

pub async fn write_message_with_size<W: AsyncWrite + Unpin>(
    writer: &mut W,
    network: Network,
    message: &Message,
) -> Result<usize> {
    let frame = encode_message(network, message)?;
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
        "pong" => Message::Pong(if reader.remaining() == 0 {
            0
        } else {
            reader.u64_le()?
        }),
        "getheaders" => Message::GetHeaders(decode_getheaders(&mut reader)?),
        "getblocks" => Message::GetBlocks(decode_getheaders(&mut reader)?),
        "headers" => Message::Headers(decode_headers(&mut reader)?),
        "inv" => Message::Inv(decode_inventory(&mut reader)?),
        "getdata" => Message::GetData(decode_inventory(&mut reader)?),
        "notfound" => Message::NotFound(decode_inventory(&mut reader)?),
        "block" => Message::Block(deserialize(payload).map_err(payload_error)?),
        "merkleblock" => Message::MerkleBlock(deserialize(payload).map_err(payload_error)?),
        "tx" => Message::Transaction(deserialize(payload).map_err(payload_error)?),
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
    let sender_services = reader.u64_le()?;
    let sender_address = reader.array::<16>()?;
    let sender_port = reader.u16_be()?;
    let nonce = reader.u64_le()?;
    let user_agent_len = usize::try_from(reader.compact_size()?)
        .map_err(|_| WireError::Payload("user agent length is out of range".to_owned()))?;
    if user_agent_len > MAX_USER_AGENT_LENGTH {
        return Err(WireError::Payload(
            "user agent exceeds Core's 256-byte limit".to_owned(),
        ));
    }
    let user_agent = String::from_utf8(reader.bytes(user_agent_len)?.to_vec())
        .map_err(|_| WireError::Payload("user agent is not UTF-8".to_owned()))?;
    let start_height = reader.i32_le()?;
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

        let mut locator = Vec::new();
        put_i32(VersionMessage::PROTOCOL_VERSION, &mut locator);
        put_compact_size(102, &mut locator).unwrap();
        locator.extend_from_slice(&[0; 32 * 103]);
        assert!(decode_getheaders(&mut Reader::new(&locator)).is_err());
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
