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
use bitcoin::p2p::message_compact_blocks::{BlockTxn, CmpctBlock, GetBlockTxn};
use bitcoin::{Block, BlockHash, Network, Transaction};
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};

pub const MAX_MESSAGE_SIZE: usize = 4 * 1024 * 1024;
const HEADER_SIZE: usize = 24;

pub const NODE_NETWORK: u64 = 1;
pub const NODE_WITNESS: u64 = 1 << 3;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InventoryType {
    Error,
    Transaction,
    Block,
    FilteredBlock,
    CompactBlock,
    WitnessTransaction,
    WitnessBlock,
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
            0x4000_0001 => Self::WitnessTransaction,
            0x4000_0002 => Self::WitnessBlock,
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
            Self::WitnessTransaction => 0x4000_0001,
            Self::WitnessBlock => 0x4000_0002,
            Self::Unknown(value) => value,
        }
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
        Self {
            version: Self::PROTOCOL_VERSION,
            services: NODE_NETWORK | NODE_WITNESS,
            timestamp: chrono_like_unix_time(),
            receiver_services: NODE_NETWORK | NODE_WITNESS,
            receiver_address: [0; 16],
            receiver_port: 0,
            sender_services: NODE_NETWORK | NODE_WITNESS,
            sender_address: [0; 16],
            sender_port: 0,
            nonce,
            user_agent: "/bitcoind-rs:0.1.0/".to_owned(),
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Message {
    Version(VersionMessage),
    Verack,
    Addr(Vec<NetworkAddress>),
    GetAddr,
    SendHeaders,
    WtxidRelay,
    Ping(u64),
    Pong(u64),
    GetHeaders(GetHeadersMessage),
    GetBlocks(GetHeadersMessage),
    Headers(Vec<bitcoin::block::Header>),
    Inv(Vec<Inventory>),
    GetData(Vec<Inventory>),
    NotFound(Vec<Inventory>),
    Block(Block),
    Transaction(Transaction),
    Mempool,
    FeeFilter(i64),
    SendCmpct { announce: bool, version: u64 },
    CompactBlock(HeaderAndShortIds),
    GetBlockTxn(BlockTransactionsRequest),
    BlockTxn(BlockTransactions),
    Unknown { command: String, payload: Vec<u8> },
}

impl Message {
    pub fn command(&self) -> &str {
        match self {
            Self::Version(_) => "version",
            Self::Verack => "verack",
            Self::Addr(_) => "addr",
            Self::GetAddr => "getaddr",
            Self::SendHeaders => "sendheaders",
            Self::WtxidRelay => "wtxidrelay",
            Self::Ping(_) => "ping",
            Self::Pong(_) => "pong",
            Self::GetHeaders(_) => "getheaders",
            Self::GetBlocks(_) => "getblocks",
            Self::Headers(_) => "headers",
            Self::Inv(_) => "inv",
            Self::GetData(_) => "getdata",
            Self::NotFound(_) => "notfound",
            Self::Block(_) => "block",
            Self::Transaction(_) => "tx",
            Self::Mempool => "mempool",
            Self::FeeFilter(_) => "feefilter",
            Self::SendCmpct { .. } => "sendcmpct",
            Self::CompactBlock(_) => "cmpctblock",
            Self::GetBlockTxn(_) => "getblocktxn",
            Self::BlockTxn(_) => "blocktxn",
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
    if payload.len() > MAX_MESSAGE_SIZE {
        return Err(WireError::Oversized(payload.len()).into());
    }
    let command = message.command().as_bytes();
    if command.is_empty() || command.len() > 12 || command.contains(&0) {
        bail!("invalid Bitcoin command name");
    }
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
    let command_end = frame[4..16]
        .iter()
        .position(|byte| *byte == 0)
        .unwrap_or(12);
    let command = std::str::from_utf8(&frame[4..4 + command_end])?;
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
    decode_message(network, &frame)
}

pub async fn write_message<W: AsyncWrite + Unpin>(
    writer: &mut W,
    network: Network,
    message: &Message,
) -> Result<()> {
    let frame = encode_message(network, message)?;
    writer.write_all(&frame).await?;
    writer.flush().await?;
    Ok(())
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
        | Message::SendHeaders
        | Message::WtxidRelay
        | Message::Mempool => {}
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
        Message::Transaction(transaction) => out.extend_from_slice(&serialize(transaction)),
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
        Message::Unknown { payload, .. } => out.extend_from_slice(payload),
    }
    Ok(out)
}

fn decode_payload(command: &str, payload: &[u8]) -> Result<Message, WireError> {
    let mut reader = Reader::new(payload);
    let message = match command {
        "version" => Message::Version(decode_version(&mut reader)?),
        "verack" => Message::Verack,
        "getaddr" => Message::GetAddr,
        "sendheaders" => Message::SendHeaders,
        "wtxidrelay" => Message::WtxidRelay,
        "mempool" => Message::Mempool,
        "addr" => Message::Addr(decode_addr(&mut reader)?),
        "ping" => Message::Ping(reader.u64_le()?),
        "pong" => Message::Pong(reader.u64_le()?),
        "getheaders" => Message::GetHeaders(decode_getheaders(&mut reader)?),
        "getblocks" => Message::GetBlocks(decode_getheaders(&mut reader)?),
        "headers" => Message::Headers(decode_headers(&mut reader)?),
        "inv" => Message::Inv(decode_inventory(&mut reader)?),
        "getdata" => Message::GetData(decode_inventory(&mut reader)?),
        "notfound" => Message::NotFound(decode_inventory(&mut reader)?),
        "block" => Message::Block(deserialize(payload).map_err(payload_error)?),
        "tx" => Message::Transaction(deserialize(payload).map_err(payload_error)?),
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
        other => Message::Unknown {
            command: other.to_owned(),
            payload: payload.to_vec(),
        },
    };
    if reader.remaining() != 0
        && !matches!(
            message,
            Message::Block(_)
                | Message::Transaction(_)
                | Message::CompactBlock(_)
                | Message::GetBlockTxn(_)
                | Message::BlockTxn(_)
                | Message::Unknown { .. }
        )
    {
        return Err(WireError::Payload("trailing bytes".to_owned()));
    }
    Ok(message)
}

fn encode_version(version: &VersionMessage, out: &mut Vec<u8>) -> Result<()> {
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
    let user_agent_len = reader.compact_size()? as usize;
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
    put_compact_size(items.len(), out)?;
    for item in items {
        put_u32(item.kind.as_u32(), out);
        out.extend_from_slice(&item.hash.to_byte_array());
    }
    Ok(())
}

fn decode_inventory(reader: &mut Reader<'_>) -> Result<Vec<Inventory>, WireError> {
    let count = bounded_count(reader.compact_size()?)?;
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

fn decode_getheaders(reader: &mut Reader<'_>) -> Result<GetHeadersMessage, WireError> {
    let version = reader.i32_le()?;
    let count = bounded_count(reader.compact_size()?)?;
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
        if reader.compact_size()? != 0 {
            return Err(WireError::Payload(
                "headers message contains transactions".to_owned(),
            ));
        }
    }
    Ok(headers)
}

fn payload_error(error: bitcoin::consensus::encode::Error) -> WireError {
    WireError::Payload(error.to_string())
}

fn put_compact_size(value: usize, out: &mut Vec<u8>) -> Result<()> {
    if value < 0xfd {
        out.push(value as u8);
    } else if value <= u16::MAX as usize {
        out.push(0xfd);
        out.extend_from_slice(&(value as u16).to_le_bytes());
    } else if value <= u32::MAX as usize {
        out.push(0xfe);
        out.extend_from_slice(&(value as u32).to_le_bytes());
    } else {
        out.push(0xff);
        out.extend_from_slice(&(value as u64).to_le_bytes());
    }
    Ok(())
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
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|duration| duration.as_secs() as i64)
        .unwrap_or(0)
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
    fn version_round_trip() {
        let message = Message::Version(VersionMessage::new(12, 99));
        let frame = encode_message(Network::Bitcoin, &message).unwrap();
        assert_eq!(decode_message(Network::Bitcoin, &frame).unwrap(), message);
    }

    #[test]
    fn unknown_bounded_message_is_preserved() {
        let message = Message::Unknown {
            command: "sendaddrv2".to_owned(),
            payload: Vec::new(),
        };
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
}
