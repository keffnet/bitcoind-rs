//! Append-only block storage.
//!
//! Blocks are written as length-prefixed consensus-encoded records. The
//! in-memory hash index makes reads O(1). A durable location index avoids
//! decoding the append-only file on normal restarts; truncated, stale, or
//! corrupt index files fall back to a complete record scan.

use std::collections::{HashMap, HashSet};
use std::fs::{File, OpenOptions, create_dir_all};
use std::io::{ErrorKind, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use bitcoin::bip158::FilterHeader;
use bitcoin::consensus::encode::{VarInt, deserialize, deserialize_partial, serialize};
use bitcoin::hashes::Hash;
use bitcoin::{Block, BlockHash, TxOut};

const MAX_STORED_BLOCK_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_UNDO_SIZE: usize = 4 * 1024 * 1024;
const MAX_STORED_FILTER_SIZE: usize = 4 * 1024 * 1024;
const INDEX_HEADER_SIZE: u64 = 8;
const INDEX_RECORD_SIZE: u64 = 44;

#[derive(Clone, Copy, Debug)]
struct Record {
    offset: u64,
    length: u32,
}

pub struct BlockStore {
    path: PathBuf,
    file: File,
    index_file: File,
    index: HashMap<BlockHash, Record>,
    undo_file: File,
    undo_index_file: File,
    undo_index: HashMap<BlockHash, Record>,
}

impl BlockStore {
    pub fn open(directory: impl AsRef<Path>) -> Result<Self> {
        let directory = directory.as_ref();
        create_dir_all(directory)
            .with_context(|| format!("creating block directory {}", directory.display()))?;
        let path = directory.join("blocks.dat");
        let mut file = OpenOptions::new()
            .create(true)
            .read(true)
            .append(true)
            .open(&path)
            .with_context(|| format!("opening block store {}", path.display()))?;
        let index_path = directory.join("blocks.index");
        let mut index_file = OpenOptions::new()
            .create(true)
            .truncate(false)
            .read(true)
            .write(true)
            .open(&index_path)
            .with_context(|| format!("opening block index {}", index_path.display()))?;
        let data_len = file.metadata()?.len();
        let index = match load_index(&mut index_file, data_len)? {
            Some(index) => index,
            None => {
                let index = scan_index(&mut file)
                    .with_context(|| format!("scanning {}", path.display()))?;
                rewrite_index(&mut index_file, data_len, &index)?;
                index
            }
        };
        let undo_path = directory.join("undo.dat");
        let mut undo_file = OpenOptions::new()
            .create(true)
            .read(true)
            .append(true)
            .open(&undo_path)
            .with_context(|| format!("opening undo store {}", undo_path.display()))?;
        let undo_index_path = directory.join("undo.index");
        let mut undo_index_file = OpenOptions::new()
            .create(true)
            .truncate(false)
            .read(true)
            .write(true)
            .open(&undo_index_path)
            .with_context(|| format!("opening undo index {}", undo_index_path.display()))?;
        let undo_data_len = undo_file.metadata()?.len();
        let undo_index = match load_index(&mut undo_index_file, undo_data_len)? {
            Some(index) => index,
            None => {
                let index = scan_undo_index(&mut undo_file)
                    .with_context(|| format!("scanning {}", undo_path.display()))?;
                rewrite_index(&mut undo_index_file, undo_data_len, &index)?;
                index
            }
        };
        Ok(Self {
            path,
            file,
            index_file,
            index,
            undo_file,
            undo_index_file,
            undo_index,
        })
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn contains(&self, hash: &BlockHash) -> bool {
        self.index.contains_key(hash)
    }

    pub fn len(&self) -> usize {
        self.index.len()
    }

    pub fn is_empty(&self) -> bool {
        self.index.is_empty()
    }

    pub fn insert(&mut self, block: &Block) -> Result<BlockHash> {
        let hash = block.block_hash();
        if self.index.contains_key(&hash) {
            return Ok(hash);
        }
        let bytes = serialize(block);
        if bytes.len() > MAX_STORED_BLOCK_SIZE {
            bail!("block is too large: {} bytes", bytes.len());
        }
        let offset = self.file.seek(SeekFrom::End(0))?;
        let length = u32::try_from(bytes.len()).context("block length does not fit u32")?;
        self.file.write_all(&length.to_le_bytes())?;
        self.file.write_all(&bytes)?;
        self.file.sync_data()?;
        persist_index_entry(
            &mut self.index_file,
            offset + 4 + bytes.len() as u64,
            hash,
            Record { offset, length },
        )?;
        self.index.insert(hash, Record { offset, length });
        Ok(hash)
    }

    pub fn get(&mut self, hash: &BlockHash) -> Result<Option<Block>> {
        let Some(record) = self.index.get(hash).copied() else {
            return Ok(None);
        };
        self.file.seek(SeekFrom::Start(record.offset))?;
        let mut length = [0u8; 4];
        self.file.read_exact(&mut length)?;
        let actual = u32::from_le_bytes(length);
        if actual != record.length {
            bail!("block store index disagrees with record length");
        }
        let mut bytes = vec![0u8; record.length as usize];
        self.file.read_exact(&mut bytes)?;
        let block: Block = deserialize(&bytes).context("decoding stored block")?;
        if block.block_hash() != *hash {
            bail!("stored block hash does not match block index");
        }
        Ok(Some(block))
    }

    pub fn get_undo(&mut self, hash: &BlockHash) -> Result<Option<Vec<Vec<TxOut>>>> {
        let Some(record) = self.undo_index.get(hash).copied() else {
            return Ok(None);
        };
        self.undo_file.seek(SeekFrom::Start(record.offset))?;
        let mut length = [0u8; 4];
        self.undo_file.read_exact(&mut length)?;
        let actual = u32::from_le_bytes(length);
        if actual != record.length {
            bail!("undo store index disagrees with record length");
        }
        let mut bytes = vec![0u8; record.length as usize];
        self.undo_file.read_exact(&mut bytes)?;
        let (stored_hash, undo) = decode_undo_record(&bytes)?;
        if stored_hash != *hash {
            bail!("stored block undo hash does not match undo index");
        }
        Ok(Some(undo))
    }

    pub fn insert_undo(&mut self, hash: BlockHash, undo: &[Vec<TxOut>]) -> Result<()> {
        if self.undo_index.contains_key(&hash) {
            return Ok(());
        }
        let bytes = encode_undo_record(hash, undo)?;
        if bytes.len() > MAX_STORED_UNDO_SIZE {
            bail!("block undo is too large: {} bytes", bytes.len());
        }
        let offset = self.undo_file.seek(SeekFrom::End(0))?;
        let length = u32::try_from(bytes.len()).context("undo length does not fit u32")?;
        self.undo_file.write_all(&length.to_le_bytes())?;
        self.undo_file.write_all(&bytes)?;
        self.undo_file.sync_data()?;
        persist_index_entry(
            &mut self.undo_index_file,
            offset + 4 + bytes.len() as u64,
            hash,
            Record { offset, length },
        )?;
        self.undo_index.insert(hash, Record { offset, length });
        Ok(())
    }

    pub fn hashes(&self) -> impl Iterator<Item = &BlockHash> {
        self.index.keys()
    }

    /// Rewrite the append-only files, retaining only the supplied records.
    /// This is used by manual pruning after the chainstate snapshot has made
    /// the retained active tip restartable without old block bodies.
    pub fn prune(
        &mut self,
        retained_blocks: &HashSet<BlockHash>,
        retained_undo: &HashSet<BlockHash>,
    ) -> Result<()> {
        let block_hashes = self
            .index
            .keys()
            .copied()
            .filter(|hash| retained_blocks.contains(hash))
            .collect::<Vec<_>>();
        let mut block_records = Vec::with_capacity(block_hashes.len());
        for hash in block_hashes {
            let block = self
                .get(&hash)?
                .with_context(|| format!("block {hash} disappeared during pruning"))?;
            block_records.push((hash, serialize(&block)));
        }
        let (file, index, data_len) = rewrite_record_file(&self.path, &block_records)?;
        self.file = file;
        self.index = index;
        rewrite_index(&mut self.index_file, data_len, &self.index)?;

        let undo_path = self
            .path
            .parent()
            .context("block store has no parent directory")?
            .join("undo.dat");
        let undo_hashes = self
            .undo_index
            .keys()
            .copied()
            .filter(|hash| retained_undo.contains(hash))
            .collect::<Vec<_>>();
        let mut undo_records = Vec::with_capacity(undo_hashes.len());
        for hash in undo_hashes {
            let undo = self
                .get_undo(&hash)?
                .with_context(|| format!("undo for block {hash} disappeared during pruning"))?;
            undo_records.push((hash, encode_undo_record(hash, &undo)?));
        }
        let (undo_file, undo_index, undo_data_len) =
            rewrite_record_file(&undo_path, &undo_records)?;
        self.undo_file = undo_file;
        self.undo_index = undo_index;
        rewrite_index(&mut self.undo_index_file, undo_data_len, &self.undo_index)?;
        Ok(())
    }
}

fn rewrite_record_file(
    path: &Path,
    records: &[(BlockHash, Vec<u8>)],
) -> Result<(File, HashMap<BlockHash, Record>, u64)> {
    let temp_path = path.with_file_name(format!(
        "{}.prune.tmp",
        path.file_name().unwrap_or_default().to_string_lossy()
    ));
    let mut temp = OpenOptions::new()
        .create(true)
        .truncate(true)
        .read(true)
        .write(true)
        .open(&temp_path)
        .with_context(|| format!("opening temporary store {}", temp_path.display()))?;
    let mut index = HashMap::with_capacity(records.len());
    for (hash, bytes) in records {
        let offset = temp.seek(SeekFrom::End(0))?;
        let length = u32::try_from(bytes.len()).context("record length does not fit u32")?;
        temp.write_all(&length.to_le_bytes())?;
        temp.write_all(bytes)?;
        index.insert(*hash, Record { offset, length });
    }
    temp.sync_all()?;
    drop(temp);
    std::fs::rename(&temp_path, path)
        .with_context(|| format!("replacing pruned store {}", path.display()))?;
    let data_len = std::fs::metadata(path)?.len();
    let file = OpenOptions::new()
        .read(true)
        .append(true)
        .open(path)
        .with_context(|| format!("reopening pruned store {}", path.display()))?;
    Ok((file, index, data_len))
}

/// Durable BIP158 filter content and filter-header storage.
///
/// Filters are immutable by block hash, so an append-only record file with a
/// compact hash index gives restart-time lookups without replaying block
/// bodies or the UTXO set.
pub struct FilterStore {
    file: File,
    index_file: File,
    index: HashMap<BlockHash, Record>,
}

impl FilterStore {
    pub fn open(directory: impl AsRef<Path>) -> Result<Self> {
        let directory = directory.as_ref();
        create_dir_all(directory)
            .with_context(|| format!("creating filter directory {}", directory.display()))?;
        let path = directory.join("basic-filters.dat");
        let mut file = OpenOptions::new()
            .create(true)
            .read(true)
            .append(true)
            .open(&path)
            .with_context(|| format!("opening filter store {}", path.display()))?;
        let index_path = directory.join("basic-filters.index");
        let mut index_file = OpenOptions::new()
            .create(true)
            .truncate(false)
            .read(true)
            .write(true)
            .open(&index_path)
            .with_context(|| format!("opening filter index {}", index_path.display()))?;
        let data_len = file.metadata()?.len();
        let index = match load_filter_index(&mut index_file, data_len)? {
            Some(index) => index,
            None => {
                let index = scan_filter_index(&mut file)?;
                rewrite_index(&mut index_file, data_len, &index)?;
                index
            }
        };
        Ok(Self {
            file,
            index_file,
            index,
        })
    }

    pub fn len(&self) -> usize {
        self.index.len()
    }

    pub fn is_empty(&self) -> bool {
        self.index.is_empty()
    }

    pub fn get(&mut self, hash: &BlockHash) -> Result<Option<(Vec<u8>, FilterHeader)>> {
        let Some(record) = self.index.get(hash).copied() else {
            return Ok(None);
        };
        self.file.seek(SeekFrom::Start(record.offset))?;
        let mut length = [0u8; 4];
        self.file.read_exact(&mut length)?;
        let actual = u32::from_le_bytes(length);
        if actual != record.length {
            bail!("filter store index disagrees with record length");
        }
        if actual as usize > MAX_STORED_FILTER_SIZE + 64 {
            bail!("stored filter record is too large");
        }
        let mut bytes = vec![0u8; record.length as usize];
        self.file.read_exact(&mut bytes)?;
        if bytes.len() < 64 {
            bail!("stored filter record is truncated");
        }
        let stored_hash = BlockHash::from_byte_array(
            bytes[..32]
                .try_into()
                .expect("filter block hash has fixed width"),
        );
        if stored_hash != *hash {
            bail!("stored filter hash does not match filter index");
        }
        let header = FilterHeader::from_byte_array(
            bytes[32..64]
                .try_into()
                .expect("filter header has fixed width"),
        );
        Ok(Some((bytes[64..].to_vec(), header)))
    }

    pub fn insert(&mut self, hash: BlockHash, content: &[u8], header: FilterHeader) -> Result<()> {
        if self.index.contains_key(&hash) {
            return Ok(());
        }
        if content.len() > MAX_STORED_FILTER_SIZE {
            bail!("basic filter is too large: {} bytes", content.len());
        }
        let mut bytes = Vec::with_capacity(64 + content.len());
        bytes.extend_from_slice(&hash.to_byte_array());
        bytes.extend_from_slice(&header.to_byte_array());
        bytes.extend_from_slice(content);
        let offset = self.file.seek(SeekFrom::End(0))?;
        let length = u32::try_from(bytes.len()).context("filter length does not fit u32")?;
        self.file.write_all(&length.to_le_bytes())?;
        self.file.write_all(&bytes)?;
        self.file.sync_data()?;
        let record = Record { offset, length };
        persist_index_entry(
            &mut self.index_file,
            offset + 4 + bytes.len() as u64,
            hash,
            record,
        )?;
        self.index.insert(hash, record);
        Ok(())
    }
}

fn load_filter_index(file: &mut File, data_len: u64) -> Result<Option<HashMap<BlockHash, Record>>> {
    let index_len = file.metadata()?.len();
    if index_len < INDEX_HEADER_SIZE || (index_len - INDEX_HEADER_SIZE) % INDEX_RECORD_SIZE != 0 {
        return Ok(None);
    }
    file.seek(SeekFrom::Start(0))?;
    let mut expected_data_len = [0u8; 8];
    file.read_exact(&mut expected_data_len)?;
    if u64::from_le_bytes(expected_data_len) != data_len {
        return Ok(None);
    }
    let count = (index_len - INDEX_HEADER_SIZE) / INDEX_RECORD_SIZE;
    let mut index = HashMap::with_capacity(count as usize);
    let mut max_end = 0u64;
    for _ in 0..count {
        let mut hash_bytes = [0u8; 32];
        file.read_exact(&mut hash_bytes)?;
        let mut offset_bytes = [0u8; 8];
        file.read_exact(&mut offset_bytes)?;
        let mut length_bytes = [0u8; 4];
        file.read_exact(&mut length_bytes)?;
        let record = Record {
            offset: u64::from_le_bytes(offset_bytes),
            length: u32::from_le_bytes(length_bytes),
        };
        if record.length < 64
            || record.length as usize > MAX_STORED_FILTER_SIZE + 64
            || record
                .offset
                .saturating_add(4)
                .saturating_add(record.length as u64)
                > data_len
        {
            return Ok(None);
        }
        let hash = BlockHash::from_byte_array(hash_bytes);
        if index.insert(hash, record).is_some() {
            return Ok(None);
        }
        max_end = max_end.max(record.offset + 4 + record.length as u64);
    }
    if max_end != data_len && data_len != 0 {
        return Ok(None);
    }
    Ok(Some(index))
}

fn scan_filter_index(file: &mut File) -> Result<HashMap<BlockHash, Record>> {
    file.seek(SeekFrom::Start(0))?;
    let mut index = HashMap::new();
    loop {
        let offset = file.stream_position()?;
        let mut length_bytes = [0u8; 4];
        match file.read_exact(&mut length_bytes) {
            Ok(()) => {}
            Err(error) if error.kind() == ErrorKind::UnexpectedEof => {
                if offset == file.metadata()?.len() {
                    break;
                }
                return Err(error.into());
            }
            Err(error) => return Err(error.into()),
        }
        let length = u32::from_le_bytes(length_bytes);
        if length < 64 || length as usize > MAX_STORED_FILTER_SIZE + 64 {
            bail!(
                "invalid filter record length {} at offset {}",
                length,
                offset
            );
        }
        let mut bytes = vec![0u8; length as usize];
        file.read_exact(&mut bytes).map_err(|error| {
            anyhow::anyhow!("truncated filter record at offset {}: {}", offset, error)
        })?;
        let hash = BlockHash::from_byte_array(
            bytes[..32]
                .try_into()
                .expect("filter block hash has fixed width"),
        );
        if index.insert(hash, Record { offset, length }).is_some() {
            bail!("duplicate block hash in filter store");
        }
    }
    file.seek(SeekFrom::End(0))?;
    Ok(index)
}

fn load_index(file: &mut File, data_len: u64) -> Result<Option<HashMap<BlockHash, Record>>> {
    let index_len = file.metadata()?.len();
    if index_len < INDEX_HEADER_SIZE || (index_len - INDEX_HEADER_SIZE) % INDEX_RECORD_SIZE != 0 {
        return Ok(None);
    }
    file.seek(SeekFrom::Start(0))?;
    let mut expected_data_len = [0u8; 8];
    file.read_exact(&mut expected_data_len)?;
    if u64::from_le_bytes(expected_data_len) != data_len {
        return Ok(None);
    }
    let count = (index_len - INDEX_HEADER_SIZE) / INDEX_RECORD_SIZE;
    let mut index = HashMap::with_capacity(count as usize);
    let mut max_end = 0u64;
    for _ in 0..count {
        let mut hash_bytes = [0u8; 32];
        file.read_exact(&mut hash_bytes)?;
        let mut offset_bytes = [0u8; 8];
        file.read_exact(&mut offset_bytes)?;
        let mut length_bytes = [0u8; 4];
        file.read_exact(&mut length_bytes)?;
        let record = Record {
            offset: u64::from_le_bytes(offset_bytes),
            length: u32::from_le_bytes(length_bytes),
        };
        if record.length == 0
            || record.length as usize > MAX_STORED_BLOCK_SIZE
            || record
                .offset
                .saturating_add(4)
                .saturating_add(record.length as u64)
                > data_len
        {
            return Ok(None);
        }
        let hash = BlockHash::from_byte_array(hash_bytes);
        if index.insert(hash, record).is_some() {
            return Ok(None);
        }
        max_end = max_end.max(record.offset + 4 + record.length as u64);
    }
    if max_end != data_len && data_len != 0 {
        return Ok(None);
    }
    Ok(Some(index))
}

fn rewrite_index(file: &mut File, data_len: u64, index: &HashMap<BlockHash, Record>) -> Result<()> {
    file.set_len(0)?;
    file.seek(SeekFrom::Start(0))?;
    file.write_all(&data_len.to_le_bytes())?;
    let mut entries: Vec<(&BlockHash, &Record)> = index.iter().collect();
    entries.sort_by_key(|(hash, _)| hash.to_string());
    for (hash, record) in entries {
        file.write_all(&hash.to_byte_array())?;
        file.write_all(&record.offset.to_le_bytes())?;
        file.write_all(&record.length.to_le_bytes())?;
    }
    file.sync_data()?;
    Ok(())
}

fn persist_index_entry(
    file: &mut File,
    data_len: u64,
    hash: BlockHash,
    record: Record,
) -> Result<()> {
    file.seek(SeekFrom::Start(0))?;
    file.write_all(&data_len.to_le_bytes())?;
    file.seek(SeekFrom::End(0))?;
    file.write_all(&hash.to_byte_array())?;
    file.write_all(&record.offset.to_le_bytes())?;
    file.write_all(&record.length.to_le_bytes())?;
    file.sync_data()?;
    Ok(())
}

fn scan_index(file: &mut File) -> Result<HashMap<BlockHash, Record>> {
    file.seek(SeekFrom::Start(0))?;
    let mut index = HashMap::new();
    loop {
        let offset = file.stream_position()?;
        let mut length_bytes = [0u8; 4];
        match file.read_exact(&mut length_bytes) {
            Ok(()) => {}
            Err(error) if error.kind() == ErrorKind::UnexpectedEof => {
                if offset == file.metadata()?.len() {
                    break;
                }
                return Err(error.into());
            }
            Err(error) => return Err(error.into()),
        }
        let length = u32::from_le_bytes(length_bytes);
        if length == 0 || length as usize > MAX_STORED_BLOCK_SIZE {
            bail!(
                "invalid block record length {} at offset {}",
                length,
                offset
            );
        }
        let mut bytes = vec![0u8; length as usize];
        file.read_exact(&mut bytes).map_err(|error| {
            anyhow::anyhow!("truncated block record at offset {}: {}", offset, error)
        })?;
        let block: Block = deserialize(&bytes).context("decoding block record")?;
        index.insert(block.block_hash(), Record { offset, length });
    }
    file.seek(SeekFrom::End(0))?;
    Ok(index)
}

fn scan_undo_index(file: &mut File) -> Result<HashMap<BlockHash, Record>> {
    file.seek(SeekFrom::Start(0))?;
    let mut index = HashMap::new();
    let mut max_end = 0u64;
    loop {
        let offset = file.stream_position()?;
        let mut length_bytes = [0u8; 4];
        match file.read_exact(&mut length_bytes) {
            Ok(()) => {}
            Err(error) if error.kind() == ErrorKind::UnexpectedEof => {
                if offset == file.metadata()?.len() {
                    break;
                }
                return Err(error.into());
            }
            Err(error) => return Err(error.into()),
        }
        let length = u32::from_le_bytes(length_bytes);
        if length == 0 || length as usize > MAX_STORED_UNDO_SIZE {
            bail!("invalid undo record length {} at offset {}", length, offset);
        }
        let mut bytes = vec![0u8; length as usize];
        file.read_exact(&mut bytes).map_err(|error| {
            anyhow::anyhow!("truncated undo record at offset {}: {}", offset, error)
        })?;
        let (hash, _) = decode_undo_record(&bytes)?;
        if index.insert(hash, Record { offset, length }).is_some() {
            bail!("duplicate block hash in undo store")
        }
        max_end = offset + 4 + u64::from(length);
    }
    if max_end != file.metadata()?.len() && max_end != 0 {
        bail!("undo store contains trailing data")
    }
    Ok(index)
}

fn encode_undo_record(hash: BlockHash, undo: &[Vec<TxOut>]) -> Result<Vec<u8>> {
    let mut bytes = serialize(&hash);
    bytes.extend_from_slice(&serialize(&VarInt(undo.len() as u64)));
    for outputs in undo {
        bytes.extend_from_slice(&serialize(&VarInt(outputs.len() as u64)));
        for output in outputs {
            bytes.extend_from_slice(&serialize(output));
        }
    }
    Ok(bytes)
}

fn decode_undo_record(bytes: &[u8]) -> Result<(BlockHash, Vec<Vec<TxOut>>)> {
    let (hash, mut consumed) =
        deserialize_partial::<BlockHash>(bytes).context("decoding stored block undo hash")?;
    let (transaction_count, count_consumed) = deserialize_partial::<VarInt>(&bytes[consumed..])
        .context("decoding stored block undo transaction count")?;
    consumed = consumed.saturating_add(count_consumed);
    let transaction_count = usize::try_from(transaction_count.0)
        .context("stored block undo transaction count is too large")?;
    if transaction_count > MAX_STORED_UNDO_SIZE {
        bail!("stored block undo transaction count is unreasonable")
    }
    let mut undo = Vec::with_capacity(transaction_count);
    for _ in 0..transaction_count {
        let (output_count, count_consumed) = deserialize_partial::<VarInt>(&bytes[consumed..])
            .context("decoding stored block undo output count")?;
        consumed = consumed.saturating_add(count_consumed);
        let output_count = usize::try_from(output_count.0)
            .context("stored block undo output count is too large")?;
        if output_count > MAX_STORED_UNDO_SIZE {
            bail!("stored block undo output count is unreasonable")
        }
        let mut outputs = Vec::with_capacity(output_count);
        for _ in 0..output_count {
            let (output, output_consumed) = deserialize_partial::<TxOut>(&bytes[consumed..])
                .context("decoding stored block undo output")?;
            consumed = consumed.saturating_add(output_consumed);
            outputs.push(output);
        }
        undo.push(outputs);
    }
    if consumed != bytes.len() {
        bail!("stored block undo contains trailing data")
    }
    Ok((hash, undo))
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::Network;
    use bitcoin::blockdata::constants::genesis_block;
    use std::collections::HashSet;

    #[test]
    fn persists_and_reopens_genesis() {
        let directory = tempfile::tempdir().unwrap();
        let block = genesis_block(Network::Regtest);
        let hash = {
            let mut store = BlockStore::open(directory.path()).unwrap();
            let hash = store.insert(&block).unwrap();
            assert_eq!(store.get(&hash).unwrap().unwrap(), block);
            hash
        };
        let index_path = directory.path().join("blocks.index");
        assert!(index_path.exists());
        std::fs::write(&index_path, b"corrupt").unwrap();
        let mut reopened = BlockStore::open(directory.path()).unwrap();
        assert!(reopened.contains(&hash));
        assert_eq!(reopened.get(&hash).unwrap().unwrap(), block);
    }

    #[test]
    fn persists_and_reopens_block_undo() {
        let directory = tempfile::tempdir().unwrap();
        let hash = BlockHash::from_byte_array([7; 32]);
        let undo = vec![
            Vec::new(),
            vec![TxOut {
                value: bitcoin::Amount::from_sat(42),
                script_pubkey: bitcoin::ScriptBuf::from_bytes(vec![0x51]),
            }],
        ];
        {
            let mut store = BlockStore::open(directory.path()).unwrap();
            store.insert_undo(hash, &undo).unwrap();
            assert_eq!(store.get_undo(&hash).unwrap(), Some(undo.clone()));
        }
        let mut reopened = BlockStore::open(directory.path()).unwrap();
        assert_eq!(reopened.get_undo(&hash).unwrap(), Some(undo));
    }

    #[test]
    fn persists_and_reopens_basic_filter() {
        let directory = tempfile::tempdir().unwrap();
        let hash = BlockHash::from_byte_array([8; 32]);
        let header = FilterHeader::from_byte_array([9; 32]);
        {
            let mut store = FilterStore::open(directory.path()).unwrap();
            store.insert(hash, &[1, 2, 3], header).unwrap();
            assert_eq!(store.get(&hash).unwrap(), Some((vec![1, 2, 3], header)));
        }
        let mut reopened = FilterStore::open(directory.path()).unwrap();
        assert_eq!(reopened.get(&hash).unwrap(), Some((vec![1, 2, 3], header)));
    }

    #[test]
    fn pruning_rewrites_block_and_undo_records() {
        let directory = tempfile::tempdir().unwrap();
        let first = genesis_block(Network::Regtest);
        let mut second = first.clone();
        second.header.nonce = 1;
        let first_hash = first.block_hash();
        let second_hash = second.block_hash();
        let retained = HashSet::from([second_hash]);
        let mut store = BlockStore::open(directory.path()).unwrap();
        store.insert(&first).unwrap();
        store.insert(&second).unwrap();
        store.insert_undo(first_hash, &[Vec::new()]).unwrap();
        store.insert_undo(second_hash, &[Vec::new()]).unwrap();
        store.prune(&retained, &retained).unwrap();
        assert!(!store.contains(&first_hash));
        assert_eq!(store.get(&second_hash).unwrap(), Some(second));
        assert!(store.get_undo(&first_hash).unwrap().is_none());
        assert_eq!(
            store.get_undo(&second_hash).unwrap(),
            Some(vec![Vec::new()])
        );
    }
}
