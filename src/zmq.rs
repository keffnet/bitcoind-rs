//! Core-compatible ZeroMQ publisher notifications.
//!
//! Each configured address owns one PUB socket, matching Bitcoin Core's
//! socket-sharing boundary: topics configured at the same address share a
//! socket, while distinct endpoints are isolated. Events are delivered
//! through independent bounded per-topic channels so a slow external
//! subscriber never blocks validation or mempool admission.

use std::collections::{HashMap, HashSet};
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

#[cfg(test)]
const DEFAULT_ZMQ_EVENT_BUFFER: usize = 4_096;
const MAX_ZMQ_EVENT_BUFFER: usize = 65_536;

/// Return the bounded diagnostic-event buffer used by unit tests.
///
/// Production uses one channel per configured topic. The diagnostic stream is
/// only retained for source-level event tests and uses the smallest active
/// HWM as a conservative bound.
#[cfg(test)]
pub(crate) fn event_buffer_capacity(config: &ZmqConfig) -> usize {
    config
        .notifications()
        .iter()
        .map(|notification| usize::try_from(notification.hwm).unwrap_or(usize::MAX))
        .min()
        .map_or(4_096, |hwm| hwm.clamp(1, MAX_ZMQ_EVENT_BUFFER))
}

fn topic_event_capacity(hwm: u32) -> usize {
    usize::try_from(hwm)
        .unwrap_or(usize::MAX)
        .clamp(1, MAX_ZMQ_EVENT_BUFFER)
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

/// Receivers used by the production publisher. Each topic has its own ring,
/// matching Core's independent PUB notifier queues and preventing a small HWM
/// on one topic from dropping messages from another topic.
pub(crate) struct EventReceivers {
    hash_tx: Option<broadcast::Receiver<Event>>,
    hash_block: Option<broadcast::Receiver<Event>>,
    raw_tx: Option<broadcast::Receiver<Event>>,
    raw_block: Option<broadcast::Receiver<Event>>,
    sequence: Option<broadcast::Receiver<Event>>,
}

pub(crate) struct EventBus {
    #[cfg(test)]
    all: broadcast::Sender<Event>,
    hash_tx: Option<broadcast::Sender<Event>>,
    hash_block: Option<broadcast::Sender<Event>>,
    raw_tx: Option<broadcast::Sender<Event>>,
    raw_block: Option<broadcast::Sender<Event>>,
    sequence: Option<broadcast::Sender<Event>>,
}

impl EventBus {
    pub(crate) fn new(config: &ZmqConfig) -> Self {
        Self {
            #[cfg(test)]
            all: broadcast::channel(event_buffer_capacity(config)).0,
            hash_tx: topic_sender(!config.pub_hash_tx.is_empty(), config.hash_tx_hwm),
            hash_block: topic_sender(!config.pub_hash_block.is_empty(), config.hash_block_hwm),
            raw_tx: topic_sender(!config.pub_raw_tx.is_empty(), config.raw_tx_hwm),
            raw_block: topic_sender(!config.pub_raw_block.is_empty(), config.raw_block_hwm),
            sequence: topic_sender(!config.pub_sequence.is_empty(), config.sequence_hwm),
        }
    }

    #[cfg(test)]
    pub(crate) fn subscribe_all(&self) -> broadcast::Receiver<Event> {
        self.all.subscribe()
    }

    pub(crate) fn subscribe_topics(&self) -> EventReceivers {
        EventReceivers {
            hash_tx: self.hash_tx.as_ref().map(broadcast::Sender::subscribe),
            hash_block: self.hash_block.as_ref().map(broadcast::Sender::subscribe),
            raw_tx: self.raw_tx.as_ref().map(broadcast::Sender::subscribe),
            raw_block: self.raw_block.as_ref().map(broadcast::Sender::subscribe),
            sequence: self.sequence.as_ref().map(broadcast::Sender::subscribe),
        }
    }

    pub(crate) fn receiver_count(&self) -> usize {
        #[cfg(test)]
        let count = self.all.receiver_count();
        #[cfg(not(test))]
        let count = 0;
        count
            + self
                .hash_tx
                .as_ref()
                .map_or(0, broadcast::Sender::receiver_count)
            + self
                .hash_block
                .as_ref()
                .map_or(0, broadcast::Sender::receiver_count)
            + self
                .raw_tx
                .as_ref()
                .map_or(0, broadcast::Sender::receiver_count)
            + self
                .raw_block
                .as_ref()
                .map_or(0, broadcast::Sender::receiver_count)
            + self
                .sequence
                .as_ref()
                .map_or(0, broadcast::Sender::receiver_count)
    }

    pub(crate) fn send(&self, event: Event) {
        #[cfg(test)]
        if self.all.receiver_count() != 0 {
            let _ = self.all.send(event.clone());
        }
        match &event {
            Event::TransactionAdded { .. } => {
                self.send_topic(&self.hash_tx, &event);
                self.send_topic(&self.raw_tx, &event);
                self.send_topic(&self.sequence, &event);
            }
            Event::TransactionRemoved { .. } => {
                self.send_topic(&self.sequence, &event);
            }
            Event::BlockConnected(_) | Event::BlockDisconnected(_) => {
                self.send_topic(&self.hash_tx, &event);
                self.send_topic(&self.raw_tx, &event);
                self.send_topic(&self.sequence, &event);
            }
            Event::BlockTip(_) => {
                self.send_topic(&self.hash_block, &event);
                self.send_topic(&self.raw_block, &event);
            }
        }
    }

    fn send_topic(&self, sender: &Option<broadcast::Sender<Event>>, event: &Event) {
        if sender
            .as_ref()
            .is_some_and(|sender| sender.receiver_count() != 0)
        {
            let _ = sender.as_ref().expect("checked above").send(event.clone());
        }
    }
}

impl EventReceivers {
    fn resubscribe(&self) -> Self {
        Self {
            hash_tx: self.hash_tx.as_ref().map(broadcast::Receiver::resubscribe),
            hash_block: self
                .hash_block
                .as_ref()
                .map(broadcast::Receiver::resubscribe),
            raw_tx: self.raw_tx.as_ref().map(broadcast::Receiver::resubscribe),
            raw_block: self
                .raw_block
                .as_ref()
                .map(broadcast::Receiver::resubscribe),
            sequence: self.sequence.as_ref().map(broadcast::Receiver::resubscribe),
        }
    }

    fn retain_topics(&mut self, topics: &HashSet<Topic>) {
        if !topics.contains(&Topic::HashTx) {
            self.hash_tx = None;
        }
        if !topics.contains(&Topic::HashBlock) {
            self.hash_block = None;
        }
        if !topics.contains(&Topic::RawTx) {
            self.raw_tx = None;
        }
        if !topics.contains(&Topic::RawBlock) {
            self.raw_block = None;
        }
        if !topics.contains(&Topic::Sequence) {
            self.sequence = None;
        }
    }
}

fn topic_sender(enabled: bool, hwm: u32) -> Option<broadcast::Sender<Event>> {
    enabled.then(|| broadcast::channel(topic_event_capacity(hwm)).0)
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
    events: EventReceivers,
    startup: Option<Arc<StartupLatch>>,
) -> Result<()> {
    if !config.is_enabled() {
        if let Some(startup) = startup.as_deref() {
            startup.service_ready();
        }
        return std::future::pending::<Result<()>>().await;
    }

    let mut endpoint_tasks = tokio::task::JoinSet::new();
    for endpoint in endpoint_publishers(&config) {
        let mut socket = PubSocket::new();
        match socket.bind(&endpoint.address).await {
            Ok(_) => {
                let mut endpoint_events = events.resubscribe();
                endpoint_events.retain_topics(&endpoint.topics);
                endpoint_tasks.spawn(run_endpoint(socket, endpoint_events));
            }
            Err(error) => {
                warn!(
                    address = %endpoint.address,
                    %error,
                    "unable to bind ZMQ publisher; ignoring endpoint"
                );
            }
        }
    }
    drop(events);
    if let Some(startup) = startup.as_deref() {
        startup.service_ready();
    }
    if endpoint_tasks.is_empty() {
        return std::future::pending::<Result<()>>().await;
    }

    // A failed endpoint is isolated from every other configured publisher.
    // Core likewise owns sockets per address rather than allowing one broken
    // or slow destination to disable unrelated endpoints.
    while let Some(result) = endpoint_tasks.join_next().await {
        match result {
            Ok(Ok(())) => {}
            Ok(Err(error)) => warn!(%error, "ZMQ publisher endpoint stopped"),
            Err(error) => warn!(%error, "ZMQ publisher endpoint task failed"),
        }
        if endpoint_tasks.is_empty() {
            return std::future::pending::<Result<()>>().await;
        }
    }
    std::future::pending::<Result<()>>().await
}

struct EndpointPublisher {
    address: String,
    topics: HashSet<Topic>,
}

fn endpoint_publishers(config: &ZmqConfig) -> Vec<EndpointPublisher> {
    let mut publishers = Vec::<EndpointPublisher>::new();
    let mut positions = HashMap::<String, usize>::new();
    for notification in config.notifications() {
        let topic = Topic::from_notification_kind(notification.kind);
        if let Some(position) = positions.get(&notification.address).copied() {
            publishers[position].topics.insert(topic);
            continue;
        }
        positions.insert(notification.address.clone(), publishers.len());
        publishers.push(EndpointPublisher {
            address: notification.address,
            topics: HashSet::from([topic]),
        });
    }
    publishers
}

async fn run_endpoint(mut socket: PubSocket, mut events: EventReceivers) -> Result<()> {
    let mut sequences = TopicSequences::default();

    loop {
        tokio::select! {
            result = receive_event(&mut events.hash_tx) => {
                process_topic_result(&mut events.hash_tx, &mut socket, &mut sequences, Topic::HashTx, result).await?;
            }
            result = receive_event(&mut events.hash_block) => {
                process_topic_result(&mut events.hash_block, &mut socket, &mut sequences, Topic::HashBlock, result).await?;
            }
            result = receive_event(&mut events.raw_tx) => {
                process_topic_result(&mut events.raw_tx, &mut socket, &mut sequences, Topic::RawTx, result).await?;
            }
            result = receive_event(&mut events.raw_block) => {
                process_topic_result(&mut events.raw_block, &mut socket, &mut sequences, Topic::RawBlock, result).await?;
            }
            result = receive_event(&mut events.sequence) => {
                process_topic_result(&mut events.sequence, &mut socket, &mut sequences, Topic::Sequence, result).await?;
            }
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Topic {
    HashTx,
    HashBlock,
    RawTx,
    RawBlock,
    Sequence,
}

impl Topic {
    fn from_notification_kind(kind: &str) -> Self {
        match kind {
            "pubhashblock" => Self::HashBlock,
            "pubhashtx" => Self::HashTx,
            "pubrawblock" => Self::RawBlock,
            "pubrawtx" => Self::RawTx,
            "pubsequence" => Self::Sequence,
            _ => unreachable!("unknown ZMQ notification kind {kind}"),
        }
    }
}

async fn receive_event(
    receiver: &mut Option<broadcast::Receiver<Event>>,
) -> Result<Event, broadcast::error::RecvError> {
    match receiver {
        Some(receiver) => receiver.recv().await,
        None => std::future::pending().await,
    }
}

async fn process_topic_result(
    receiver: &mut Option<broadcast::Receiver<Event>>,
    socket: &mut PubSocket,
    sequences: &mut TopicSequences,
    topic: Topic,
    result: Result<Event, broadcast::error::RecvError>,
) -> Result<()> {
    let event = match result {
        Ok(event) => event,
        Err(broadcast::error::RecvError::Lagged(count)) => {
            warn!(count, "ZMQ notification topic lagged; events were dropped");
            return Ok(());
        }
        Err(broadcast::error::RecvError::Closed) => {
            *receiver = None;
            return Ok(());
        }
    };
    publish_topic_event(socket, sequences, topic, event).await
}

async fn publish_topic_event(
    socket: &mut PubSocket,
    sequences: &mut TopicSequences,
    topic: Topic,
    event: Event,
) -> Result<()> {
    match topic {
        Topic::HashTx => match event {
            Event::TransactionAdded { transaction, .. } => {
                publish_transaction(socket, sequences, &transaction, true, false).await
            }
            Event::BlockConnected(block) | Event::BlockDisconnected(block) => {
                publish_block_transactions(socket, sequences, &block, true, false).await
            }
            _ => Ok(()),
        },
        Topic::RawTx => match event {
            Event::TransactionAdded { transaction, .. } => {
                publish_transaction(socket, sequences, &transaction, false, true).await
            }
            Event::BlockConnected(block) | Event::BlockDisconnected(block) => {
                publish_block_transactions(socket, sequences, &block, false, true).await
            }
            _ => Ok(()),
        },
        Topic::Sequence => match event {
            Event::TransactionAdded {
                transaction,
                mempool_sequence,
            } => {
                publish_sequence(
                    socket,
                    sequences,
                    transaction.compute_txid(),
                    b'A',
                    Some(mempool_sequence),
                )
                .await
            }
            Event::TransactionRemoved {
                transaction,
                mempool_sequence,
            } => {
                publish_sequence(
                    socket,
                    sequences,
                    transaction.compute_txid(),
                    b'R',
                    Some(mempool_sequence),
                )
                .await
            }
            Event::BlockConnected(block) => {
                publish_sequence(socket, sequences, block.block_hash(), b'C', None).await
            }
            Event::BlockDisconnected(block) => {
                publish_sequence(socket, sequences, block.block_hash(), b'D', None).await
            }
            _ => Ok(()),
        },
        Topic::HashBlock => match event {
            Event::BlockTip(block) => {
                publish(
                    socket,
                    sequences,
                    "hashblock",
                    display_hash_bytes(block.block_hash()),
                )
                .await
            }
            _ => Ok(()),
        },
        Topic::RawBlock => match event {
            Event::BlockTip(block) => {
                publish(socket, sequences, "rawblock", serialize(block.as_ref())).await
            }
            _ => Ok(()),
        },
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

    fn unused_tcp_endpoint() -> String {
        let listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        let port = listener.local_addr().unwrap().port();
        drop(listener);
        format!("tcp://127.0.0.1:{port}")
    }

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
    fn event_bus_routes_topics_to_independent_hwm_rings() {
        let mut config = ZmqConfig::default();
        config.pub_hash_tx.push("tcp://127.0.0.1:0".to_owned());
        config.pub_raw_tx.push("tcp://127.0.0.1:0".to_owned());
        config.pub_sequence.push("tcp://127.0.0.1:0".to_owned());
        config.hash_tx_hwm = 1;
        config.raw_tx_hwm = 8;
        config.sequence_hwm = 8;

        let bus = EventBus::new(&config);
        let mut receivers = bus.subscribe_topics();
        let transaction = Arc::new(Transaction {
            version: bitcoin::transaction::Version::TWO,
            lock_time: bitcoin::absolute::LockTime::ZERO,
            input: Vec::new(),
            output: Vec::new(),
        });
        for sequence in 0..2 {
            bus.send(Event::TransactionAdded {
                transaction: transaction.clone(),
                mempool_sequence: sequence,
            });
        }

        assert!(matches!(
            receivers.hash_tx.as_mut().unwrap().try_recv(),
            Err(broadcast::error::TryRecvError::Lagged(1))
        ));
        assert!(receivers.raw_tx.as_mut().unwrap().try_recv().is_ok());
        assert!(receivers.sequence.as_mut().unwrap().try_recv().is_ok());
        assert!(receivers.hash_block.is_none());
        assert!(receivers.raw_block.is_none());
    }

    #[test]
    fn endpoint_publishers_share_only_topics_at_the_same_address() {
        let mut config = ZmqConfig::default();
        config.pub_hash_tx.push("tcp://127.0.0.1:28001".to_owned());
        config.pub_sequence.push("tcp://127.0.0.1:28001".to_owned());
        config.pub_raw_tx.push("tcp://127.0.0.1:28002".to_owned());

        let publishers = endpoint_publishers(&config);
        assert_eq!(publishers.len(), 2);
        let shared = publishers
            .iter()
            .find(|publisher| publisher.address.ends_with("28001"))
            .unwrap();
        assert_eq!(
            shared.topics,
            HashSet::from([Topic::HashTx, Topic::Sequence])
        );
        let isolated = publishers
            .iter()
            .find(|publisher| publisher.address.ends_with("28002"))
            .unwrap();
        assert_eq!(isolated.topics, HashSet::from([Topic::RawTx]));
    }

    #[tokio::test]
    async fn distinct_endpoints_publish_only_their_configured_topics() {
        let hash_endpoint = unused_tcp_endpoint();
        let mut raw_endpoint = unused_tcp_endpoint();
        while raw_endpoint == hash_endpoint {
            raw_endpoint = unused_tcp_endpoint();
        }
        let mut config = ZmqConfig::default();
        config.pub_hash_tx.push(hash_endpoint.clone());
        config.pub_raw_tx.push(raw_endpoint.clone());
        let bus = EventBus::new(&config);
        let publisher = tokio::spawn(run_with_startup(config, bus.subscribe_topics(), None));

        let mut hash_subscriber = SubSocket::new();
        hash_subscriber.subscribe("").await.unwrap();
        hash_subscriber.connect(&hash_endpoint).await.unwrap();
        let mut raw_subscriber = SubSocket::new();
        raw_subscriber.subscribe("").await.unwrap();
        raw_subscriber.connect(&raw_endpoint).await.unwrap();
        sleep(Duration::from_millis(100)).await;

        bus.send(Event::TransactionAdded {
            transaction: Arc::new(Transaction {
                version: bitcoin::transaction::Version::TWO,
                lock_time: bitcoin::absolute::LockTime::ZERO,
                input: Vec::new(),
                output: Vec::new(),
            }),
            mempool_sequence: 0,
        });

        let hash_message = timeout(Duration::from_secs(1), hash_subscriber.recv())
            .await
            .unwrap()
            .unwrap()
            .into_vec();
        let raw_message = timeout(Duration::from_secs(1), raw_subscriber.recv())
            .await
            .unwrap()
            .unwrap()
            .into_vec();
        assert_eq!(hash_message[0].as_ref(), b"hashtx");
        assert_eq!(raw_message[0].as_ref(), b"rawtx");

        publisher.abort();
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
