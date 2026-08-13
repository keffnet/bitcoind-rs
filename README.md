# bitcoind-rs

`bitcoind-rs` is a wallet-free Bitcoin node and Electrum-compatible indexer written in Rust.

The project targets the consensus and network behavior of Bitcoin Core 31.1 while keeping the implementation modular:

- `chain`: chain selection, block persistence, UTXO state, and validation
- `mempool`: policy checks and transaction admission
- `p2p`: Bitcoin peer handshake and block/transaction propagation
- `rpc`: wallet-free JSON-RPC methods
- `electrum`: TCP JSON-RPC server with address/scripthash history and subscriptions

## Status

The implementation is an actively developed, wallet-free Core-compatible node subset. It includes:

- regtest, testnet, testnet4, signet, and mainnet chain parameters, proof-of-work/header checks, UTXO validation, libbitcoinconsensus script checks, reorgs, invalidation/reconsideration, compact filters, and durable block undo data;
- Bitcoin P2P handshake, header/block/transaction relay, compact blocks, BIP157 relay, peer controls, bans, dynamic connections, traffic counters, and ping measurements;
- mining templates and proposal validation, package-aware transaction selection, raw transaction submission, wallet-free raw signing, PSBT lifecycle, message-signing, and multisig RPCs, opt-in RBF, package submission, wallet-free descriptors (`addr`, `raw`, `pkh`, `wpkh`, `sh`, `wsh`, and `tr`), UTXO scans, and the implemented JSON-RPC/REST methods;
- an Electrum protocol server with header and scripthash subscriptions, history, balances, UTXOs, mempool queries, transaction retrieval, merkle proofs, broadcasts, and fee histograms.

It is not yet a drop-in replacement for every Bitcoin Core 31.1 behavior. In particular, the storage engine is append-only with JSON chain metadata rather than Core's production database, pruning is intentionally disabled, UTXO snapshot files use this implementation's JSON format, descriptor parsing is not full miniscript/checksum coverage, and Electrum indexing is in-process rather than a separate electrs database. Full mainnet deployment still requires broader Core test-vector, reorg, fuzz, and interoperability testing.

The node never creates, imports, or stores private keys. Wallet RPCs are intentionally not implemented.

## Running

```text
cargo run -- --network regtest --datadir ./data
```

The default configuration listens on `127.0.0.1:8333` for P2P, `127.0.0.1:8332` for JSON-RPC, and `127.0.0.1:30001` for Electrum. Select `--network regtest` when using the standard regtest ports in external tooling.

JSON-RPC uses the standard cookie file at `<datadir>/.cookie`; clients should send it as HTTP Basic authentication (`curl --user "$(cat data/.cookie)" ...`).

For the public signet, use `--network signet`. Custom BIP325 challenges can be supplied as script hex with `--signet-challenge <hex>`.
