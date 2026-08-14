# bitcoind-rs

`bitcoind-rs` is a wallet-free Bitcoin node and Electrum-compatible indexer written in Rust.

The project targets the consensus and network behavior of Bitcoin Core 31.1 while keeping the implementation modular:

- `chain`: chain selection, block persistence, UTXO state, and validation
- `mempool`: policy checks and transaction admission
- `p2p`: Bitcoin peer handshake and block/transaction propagation
- `rpc`: wallet-free JSON-RPC methods
- `electrum`: TCP JSON-RPC server with address/scripthash history and subscriptions
- `zmq`: Core-compatible PUB notifications for transactions, blocks, and sequences

## Status

The implementation is an actively developed, wallet-free Core-compatible node subset. It includes:

- regtest, testnet, testnet4, signet, and mainnet chain parameters, proof-of-work/header checks, UTXO validation, libbitcoinconsensus script checks, reorgs, invalidation/reconsideration, compact filters, and durable block undo data;
- Bitcoin P2P handshake, header/block/transaction relay, compact blocks, BIP157 relay, optional BIP37 Bloom-filter relay and merkle blocks (`--peer-bloom-filters`), bounded peer-transaction orphan handling, peer controls, bans, dynamic connections, traffic counters, and ping measurements;
- mining templates and proposal validation, package-aware transaction selection, raw transaction submission, wallet-free raw signing, PSBT lifecycle including descriptor-driven updates and transient descriptor-key signing, message-signing, and multisig RPCs, opt-in RBF, BIP431/TRUC topology and size policy, ephemeral-dust package checks, package submission, wallet-free descriptors (`addr`, `raw`, `pk`, `pkh`, `wpkh`, `combo`, `multi`, `sortedmulti`, `sh`, `wsh`, `tr`, and `rawtr`) with generic Miniscript v0 wrappers, multipath expansion, and checksum metadata, UTXO scans, and the implemented JSON-RPC/REST methods;
- an Electrum protocol server with header and scripthash subscriptions, history, balances, UTXOs, mempool queries, transaction retrieval, merkle proofs, broadcasts, and fee histograms.
- Core-compatible ZeroMQ PUB topics (`hashtx`, `hashblock`, `rawtx`, `rawblock`, and `sequence`) with multipart message and per-topic sequence framing;
- optional BIP330 `sendtxrcncl` negotiation (`--tx-reconciliation`) with Core-compatible pre-`verack` wire framing;

It is not yet a drop-in replacement for every Bitcoin Core 31.1 behavior. In particular, the storage engine uses indexed append-only records with JSON chain metadata and a lightweight JSON `peers.json` address table rather than Core's production database, mempool import/export uses this implementation's JSON format rather than Core's binary `mempool.dat`, manual pruning rewrites this implementation's block and undo stores, UTXO snapshot files use this implementation's JSON format, and Electrum indexing is in-process rather than a separate electrs database. Miniscript-backed taproot-tree derivation, PSBT leaf metadata, and transient-descriptor-key script-path signing/finalization are supported, but the broader wallet/policy satisfaction surface is not a complete wallet replacement. Full mainnet deployment still requires broader Core test-vector, reorg, fuzz, and interoperability testing.

The node never creates, imports, or stores private keys. A private extended key supplied directly in a descriptor RPC is used only for that request and is not retained. Wallet RPCs are intentionally not implemented.

## Running

```text
cargo run -- --network regtest --datadir ./data
```

The default configuration listens on `127.0.0.1:8333` for P2P, `127.0.0.1:8332` for JSON-RPC, and `127.0.0.1:30001` for Electrum. Select `--network regtest` when using the standard regtest ports in external tooling.

JSON-RPC uses the standard cookie file at `<datadir>/.cookie`; clients should send it as HTTP Basic authentication (`curl --user "$(cat data/.cookie)" ...`).

For the public signet, use `--network signet`. Custom BIP325 challenges can be supplied as script hex with `--signet-challenge <hex>`.

Bloom-filter peer relay is disabled by default, matching Core's default; enable it with `--peer-bloom-filters` when serving BIP37 clients.

Inbound P2P listening can be disabled with `--listen=false`; DNS seed lookup can be disabled with `--dnsseed=false`. `--blocksonly` disables transaction relay while retaining block synchronization and local RPC/mempool operation. Block pruning follows Core's `--prune=1` manual mode or `--prune=<MiB>` automatic target mode (automatic targets must be at least 550 MiB); `pruneblockchain` is only available when pruning is enabled.

Use `--txindex` to enable confirmed transaction lookup without supplying a block hash to `getrawtransaction`; Core-style pruning and `--txindex` are mutually exclusive.

ZeroMQ topics can be enabled with the Core-style options, for example
`--zmqpubhashtx tcp://127.0.0.1:28332 --zmqpubsequence tcp://127.0.0.1:28333`.
`getzmqnotifications` reports the configured topic endpoints and high-water marks.
