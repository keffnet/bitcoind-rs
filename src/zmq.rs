//! Core-compatible ZeroMQ publisher notifications.
//!
//! The publisher uses one PUB socket for all configured endpoints and keeps
//! the per-topic message sequence counters required by Bitcoin Core. Events
//! are delivered through a bounded broadcast channel so a slow external
//! subscriber never blocks validation or mempool admission.

use std::collections::HashSet;
use std::sync::Arc;

use anyhow::{Context, Result, anyhow};
use bitcoin::consensus::encode::serialize;
use bitcoin::{Block, Transaction};
use bytes::Bytes;
use tokio::sync::broadcast;
use tracing::warn;
use zeromq::{PubSocket, Socket, SocketSend, ZmqMessage};

use crate::StartupLatch;
use crate::config::ZmqConfig;

const DEFAULT_ZMQ_EVENT_BUFFER: usize = 4_096;
const MAX_ZMQ_EVENT_BUFFER: usize = 65_536;

/// Return the bounded validation-event buffer used before notifications reach
/// the ZMQ transport.
///
/// Core applies each configured HWM to the corresponding PUB socket queue.
/// The Rust transport also has a byte-oriented write buffer, so the shared
/// validation channel is a second, deliberately conservative loss boundary.
/// Using the smallest active message HWM ensures that no topic can retain
/// more pending validation events than its configured limit. A hard ceiling
/// prevents an accidental very large command-line HWM from preallocating an
/// unbounded amount of memory in the broadcast ring.
pub(crate) fn event_buffer_capacity(config: &ZmqConfig) -> usize {
    config
        .notifications()
        .iter()
        .map(|notification| usize::try_from(notification.hwm).unwrap_or(usize::MAX))
        .min()
        .map_or(DEFAULT_ZMQ_EVENT_BUFFER, |hwm| {
            hwm.clamp(1, MAX_ZMQ_EVENT_BUFFER)
        })
}

#[derive(Clone, Debug)]
pub(crate) enum Event {
    TransactionAdded {
        transaction: Arc<Transaction>,
        mempool_sequence: u64,
    },
    TransactionRemoved {
        transaction: Arc<Transaction>,
        mempool_sequence: u64,
    },
    BlockConnected(Arc<Block>),
    BlockDisconnected(Arc<Block>),
    BlockTip(Arc<Block>),
}

#[derive(Default)]
struct TopicSequences {
    hash_tx: u32,
    hash_block: u32,
    raw_tx: u32,
    raw_block: u32,
    sequence: u32,
}

impl TopicSequences {
    fn next(&mut self, topic: &'static str) -> u32 {
        let sequence = match topic {
            "hashtx" => &mut self.hash_tx,
            "hashblock" => &mut self.hash_block,
            "rawtx" => &mut self.raw_tx,
            "rawblock" => &mut self.raw_block,
            "sequence" => &mut self.sequence,
            _ => unreachable!("unknown ZMQ topic {topic}"),
        };
        let current = *sequence;
        *sequence = sequence.wrapping_add(1);
        current
    }
}

pub(crate) async fn run_with_startup(
    config: ZmqConfig,
    mut events: broadcast::Receiver<Event>,
    startup: Option<Arc<StartupLatch>>,
) -> Result<()> {
    let notifications = config.notifications();
    if !config.is_enabled() {
        if let Some(startup) = startup.as_deref() {
            startup.service_ready();
        }
        return std::future::pending::<Result<()>>().await;
    }

    let mut socket = PubSocket::new();
    let mut bound = HashSet::new();
    for notification in &notifications {
        if bound.insert(notification.address.clone()) {
            if let Err(error) = socket.bind(&notification.address).await {
                warn!(
                    address = %notification.address,
                    %error,
                    "unable to bind ZMQ publisher; ignoring endpoint"
                );
                bound.remove(&notification.address);
            }
        }
    }
    if let Some(startup) = startup.as_deref() {
        startup.service_ready();
    }
    if bound.is_empty() {
        return std::future::pending::<Result<()>>().await;
    }

    let enabled_hash_tx = !config.pub_hash_tx.is_empty();
    let enabled_hash_block = !config.pub_hash_block.is_empty();
    let enabled_raw_tx = !config.pub_raw_tx.is_empty();
    let enabled_raw_block = !config.pub_raw_block.is_empty();
    let enabled_sequence = !config.pub_sequence.is_empty();
    let mut sequences = TopicSequences::default();

    loop {
        let event = match events.recv().await {
            Ok(event) => event,
            Err(broadcast::error::RecvError::Lagged(count)) => {
                warn!(
                    count,
                    "ZMQ notification subscriber lagged; events were dropped"
                );
                continue;
            }
            Err(broadcast::error::RecvError::Closed) => return Ok(()),
        };
        match event {
            Event::TransactionAdded {
                transaction,
                mempool_sequence,
            } => {
                publish_transaction(
                    &mut socket,
                    &mut sequences,
                    &transaction,
                    enabled_hash_tx,
                    enabled_raw_tx,
                )
                .await?;
                if enabled_sequence {
                    publish_sequence(
                        &mut socket,
                        &mut sequences,
                        transaction.compute_txid(),
                        b'A',
                        Some(mempool_sequence),
                    )
                    .await?;
                }
            }
            Event::TransactionRemoved {
                transaction,
                mempool_sequence,
            } => {
                if enabled_sequence {
                    publish_sequence(
                        &mut socket,
                        &mut sequences,
                        transaction.compute_txid(),
                        b'R',
                        Some(mempool_sequence),
                    )
                    .await?;
                }
            }
            Event::BlockConnected(block) => {
                publish_block_transactions(
                    &mut socket,
                    &mut sequences,
                    &block,
                    enabled_hash_tx,
                    enabled_raw_tx,
                )
                .await?;
                if enabled_sequence {
                    publish_sequence(&mut socket, &mut sequences, block.block_hash(), b'C', None)
                        .await?;
                }
            }
            Event::BlockDisconnected(block) => {
                publish_block_transactions(
                    &mut socket,
                    &mut sequences,
                    &block,
                    enabled_hash_tx,
                    enabled_raw_tx,
                )
                .await?;
                if enabled_sequence {
                    publish_sequence(&mut socket, &mut sequences, block.block_hash(), b'D', None)
                        .await?;
                }
            }
            Event::BlockTip(block) => {
                if enabled_hash_block {
                    publish(
                        &mut socket,
                        &mut sequences,
                        "hashblock",
                        display_hash_bytes(block.block_hash()),
                    )
                    .await?;
                }
                if enabled_raw_block {
                    publish(
                        &mut socket,
                        &mut sequences,
                        "rawblock",
                        serialize(block.as_ref()),
                    )
                    .await?;
                }
            }
        }
    }
}

async fn publish_transaction(
    socket: &mut PubSocket,
    sequences: &mut TopicSequences,
    transaction: &Transaction,
    hash_enabled: bool,
    raw_enabled: bool,
) -> Result<()> {
    if hash_enabled {
        publish(
            socket,
            sequences,
            "hashtx",
            display_hash_bytes(transaction.compute_txid()),
        )
        .await?;
    }
    if raw_enabled {
        publish(socket, sequences, "rawtx", serialize(transaction)).await?;
    }
    Ok(())
}

async fn publish_block_transactions(
    socket: &mut PubSocket,
    sequences: &mut TopicSequences,
    block: &Block,
    hash_enabled: bool,
    raw_enabled: bool,
) -> Result<()> {
    for transaction in &block.txdata {
        publish_transaction(socket, sequences, transaction, hash_enabled, raw_enabled).await?;
    }
    Ok(())
}

async fn publish_sequence(
    socket: &mut PubSocket,
    sequences: &mut TopicSequences,
    hash: impl std::fmt::Display,
    label: u8,
    mempool_sequence: Option<u64>,
) -> Result<()> {
    let mut payload = display_hash_bytes(hash);
    payload.push(label);
    if let Some(sequence) = mempool_sequence {
        payload.extend_from_slice(&sequence.to_le_bytes());
    }
    publish(socket, sequences, "sequence", payload).await
}

async fn publish(
    socket: &mut PubSocket,
    sequences: &mut TopicSequences,
    topic: &'static str,
    payload: Vec<u8>,
) -> Result<()> {
    let message_sequence = sequences.next(topic);
    let message = ZmqMessage::try_from(vec![
        Bytes::from_static(topic.as_bytes()),
        Bytes::from(payload),
        Bytes::copy_from_slice(&message_sequence.to_le_bytes()),
    ])
    .map_err(|_| anyhow!("constructing ZMQ multipart message"))?;
    socket
        .send(message)
        .await
        .with_context(|| format!("publishing ZMQ topic {topic}"))
}

fn display_hash_bytes(hash: impl std::fmt::Display) -> Vec<u8> {
    hex::decode(hash.to_string()).expect("Bitcoin hash Display is always valid hex")
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::Txid;
    use bitcoin::hashes::Hash;
    use std::time::Duration;
    use tokio::time::{sleep, timeout};
    use zeromq::{Socket, SocketRecv, SubSocket};

    #[test]
    fn event_buffer_capacity_tracks_active_message_hwms() {
        let mut config = ZmqConfig::default();
        assert_eq!(event_buffer_capacity(&config), DEFAULT_ZMQ_EVENT_BUFFER);

        config.pub_hash_tx.push("tcp://127.0.0.1:0".to_owned());
        config.hash_tx_hwm = 7;
        assert_eq!(event_buffer_capacity(&config), 7);

        config.pub_sequence.push("tcp://127.0.0.1:0".to_owned());
        config.sequence_hwm = 3;
        assert_eq!(event_buffer_capacity(&config), 3);

        config.sequence_hwm = u32::MAX;
        assert_eq!(event_buffer_capacity(&config), 7);
        config.hash_tx_hwm = u32::MAX;
        assert_eq!(event_buffer_capacity(&config), MAX_ZMQ_EVENT_BUFFER);
    }

    #[test]
    fn sequence_payload_matches_core_layout() {
        let hash = Txid::from_byte_array([0x11; 32]);
        let mut payload = display_hash_bytes(hash);
        payload.push(b'A');
        payload.extend_from_slice(&42u64.to_le_bytes());
        assert_eq!(payload.len(), 41);
        assert_eq!(&payload[32..33], b"A");
        assert_eq!(&payload[33..], &42u64.to_le_bytes());
    }

    #[tokio::test]
    async fn publishes_topic_data_and_message_sequence_frames() {
        let mut publisher = PubSocket::new();
        let endpoint = publisher
            .bind("tcp://127.0.0.1:0")
            .await
            .unwrap()
            .to_string();
        let mut subscriber = SubSocket::new();
        subscriber.subscribe("hashtx").await.unwrap();
        subscriber.connect(&endpoint).await.unwrap();
        sleep(Duration::from_millis(50)).await;

        let mut sequences = TopicSequences::default();
        let txid = Txid::from_byte_array([0x22; 32]);
        publish(
            &mut publisher,
            &mut sequences,
            "hashtx",
            display_hash_bytes(txid),
        )
        .await
        .unwrap();

        let message = timeout(Duration::from_secs(1), subscriber.recv())
            .await
            .unwrap()
            .unwrap();
        let frames = message.into_vec();
        assert_eq!(frames.len(), 3);
        assert_eq!(frames[0].as_ref(), b"hashtx");
        assert_eq!(frames[1].as_ref(), &[0x22; 32]);
        assert_eq!(frames[2].as_ref(), &[0, 0, 0, 0]);
    }
}
