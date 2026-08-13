# bitcoind-rs

`bitcoind-rs` is a wallet-free Bitcoin node and Electrum-compatible indexer written in Rust.

The project targets the consensus and network behavior of Bitcoin Core 31.1 while keeping the implementation modular:

- `chain`: chain selection, block persistence, UTXO state, and validation
- `mempool`: policy checks and transaction admission
- `p2p`: Bitcoin peer handshake and block/transaction propagation
- `rpc`: wallet-free JSON-RPC methods
- `electrum`: TCP JSON-RPC server with address/scripthash history and subscriptions

The node never creates, imports, or stores private keys. Wallet RPCs are intentionally not implemented.

## Status

This repository is being developed incrementally. Every subsystem is intended to be independently testable; do not use an early build for mainnet consensus until the full validation and reorg test suite is complete.

## Running

```text
cargo run -- --network regtest --datadir ./data
```

The default configuration listens on `127.0.0.1:18444` for P2P, `127.0.0.1:18443` for JSON-RPC, and `127.0.0.1:30001` for Electrum.

JSON-RPC uses the standard cookie file at `<datadir>/.cookie`; clients should send it as HTTP Basic authentication (`curl --user "$(cat data/.cookie)" ...`).
