//! Append-only block storage.
//!
//! Blocks are written as length-prefixed consensus-encoded records. The
//! in-memory hash index makes reads O(1), while startup scans the append-only
//! file and rejects truncated or oversized records instead of silently
//! accepting corrupted chain data.

use std::collections::HashMap;
use std::fs::{File, OpenOptions, create_dir_all};
use std::io::{ErrorKind, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use bitcoin::consensus::encode::{deserialize, serialize};
use bitcoin::hashes::Hash;
use bitcoin::{Block, BlockHash};

const MAX_STORED_BLOCK_SIZE: usize = 4 * 1024 * 1024;
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
        Ok(Self {
            path,
            file,
            index_file,
            index,
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

    pub fn hashes(&self) -> impl Iterator<Item = &BlockHash> {
        self.index.keys()
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::Network;
    use bitcoin::blockdata::constants::genesis_block;

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
}
