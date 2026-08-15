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
- Bitcoin P2P handshake, header/block/transaction relay, compact blocks, BIP157 relay, optional BIP37 Bloom-filter relay and merkle blocks (`--peer-bloom-filters`), bounded peer-transaction orphan handling, Core-style whitelist permissions (`noban`, `forcerelay`, `relay`, `mempool`, `download`, `addr`, and `bloomfilter`), peer controls, bans, dynamic connections, traffic counters, and ping measurements;
- mining templates and proposal validation, package-aware transaction selection, raw transaction submission, wallet-free raw signing, PSBT lifecycle including descriptor-driven updates and transient descriptor-key signing, message-signing, and multisig RPCs, opt-in RBF, BIP431/TRUC topology and size policy, ephemeral-dust package checks, package submission, wallet-free descriptors (`addr`, `raw`, `pk`, `pkh`, `wpkh`, `combo`, `multi`, `sortedmulti`, `sh`, `wsh`, `tr`, and `rawtr`) with generic Miniscript v0 wrappers, multipath expansion, and checksum metadata, UTXO scans, and the implemented JSON-RPC/REST methods;
- an Electrum protocol server with header, legacy block-height, scripthash, scriptPubKey, and legacy address subscriptions, history, balances, UTXOs, mempool queries, transaction retrieval, merkle proofs, broadcasts, and fee histograms.
- Core-compatible ZeroMQ PUB topics (`hashtx`, `hashblock`, `rawtx`, `rawblock`, and `sequence`) with multipart message and per-topic sequence framing;
- optional BIP330 `sendtxrcncl` negotiation (`--tx-reconciliation`) with Core-compatible pre-`verack` wire framing;

It is not yet a drop-in replacement for every Bitcoin Core 31.1 behavior. In particular, the storage engine uses indexed append-only records with compact versioned binary chain metadata/snapshots and a lightweight JSON `peers.json` address table rather than Core's production database, manual pruning rewrites this implementation's block and undo stores while retaining active-chain transaction counts in a compact sidecar for chain statistics, external UTXO snapshots use Core's binary `utxo\xff` format and support historical active-chain `dumptxoutset` rollback by replay, while legacy internal JSON chainstate files remain readable and are migrated on write, and Electrum indexing is in-process rather than a separate electrs database. P2P synchronization includes headers-first validation, Core's low-work two-phase header presync/commitment protocol, bounded block requests, block-stall detection/backoff, and Core-style request timeouts. Strict `loadtxoutset` activation enforces the v31.1 hardcoded AssumeUTXO commitments, serves the snapshot-backed tip immediately, and validates an independent chainstate asynchronously with durable replay checkpoints and restart recovery; a mismatch promotes the independently replayed state and discards the snapshot. SOCKS5 proxy routing, typed BIP155 address-manager persistence/relay for IPv4, IPv6, Tor, I2P, and CJDNS, endpoint-aware `onlynet` filtering, numeric-IP whitelist permissions, permissioned `whitebind` listeners, and proxy-backed private broadcast connections are implemented. Mempool persistence uses Core's versioned binary `mempool.dat` format (including v1/v2 loading, v2 obfuscation, fee deltas, and unbroadcast metadata); legacy JSON pool files remain importable. Miniscript-backed taproot-tree derivation, PSBT leaf metadata, and transient-descriptor-key script-path signing/finalization are supported, but the broader wallet/policy satisfaction surface is not a complete wallet replacement. Full mainnet deployment still requires broader Core test-vector, reorg, fuzz, and interoperability testing.

The node never creates, imports, or stores private keys. A private extended key supplied directly in a descriptor RPC is used only for that request and is not retained. Wallet RPCs are intentionally not implemented.

## Running

```text
cargo run -- --network regtest --datadir ./data
```

The default configuration listens on `127.0.0.1:8333` for P2P, `127.0.0.1:8332` for JSON-RPC, and `127.0.0.1:30001` for Electrum. Select `--network regtest` when using the standard regtest ports in external tooling.

JSON-RPC uses the standard cookie file at `<datadir>/.cookie`; clients should send it as HTTP Basic authentication (`curl --user "$(cat data/.cookie)" ...`).

For the public signet, use `--network signet`. Custom BIP325 challenges can be supplied as script hex with `--signet-challenge <hex>`.

Bloom-filter peer relay is disabled by default, matching Core's default; enable it with `--peer-bloom-filters` when serving BIP37 clients.

Inbound P2P listening can be disabled with `--listen=false`; DNS seed lookup can be disabled with `--dnsseed=false`. As in Core, configuring `--proxy=<ip:port>` disables listening by default for privacy and routes outbound peer connections through an unauthenticated SOCKS5 proxy; use `--listen=true` or a `--whitebind` listener when local inbound connections are intended. Use `--onlynet=ipv4`, `--onlynet=ipv6`, `--onlynet=onion`, `--onlynet=i2p`, or `--onlynet=cjdns` to restrict address networks. ADDRv2 Tor and I2P endpoints require the configured SOCKS5 proxy for outbound connections; CJDNS endpoints use their IPv6 socket representation. `--privatebroadcast` changes `sendrawtransaction` to queue a validated transaction for three dedicated, short-lived IPv4/IPv6 connections through the configured SOCKS5 proxy; it remains out of the local mempool until received back from a peer, and `getprivatebroadcastinfo`/`abortprivatebroadcast` expose the queue. `--blocksonly` disables ordinary transaction relay while retaining block synchronization and local RPC/mempool operation; a peer matched by a whitelist rule with `relay` or `forcerelay` can still relay transactions. Whitelist rules use Core's `permissions@IP[/PREFIX]` form, for example `--whitelist=192.0.2.0/24` for the implicit incoming permissions (`noban`, `download`, and `mempool`, plus `relay` unless blocksonly is active), or `--whitelist=forcerelay,relay@198.51.100.7`. Add `in` or `out` to target connection direction, and use `--whitelistrelay=false` or `--whitelistforcerelay` to adjust implicit defaults. Permissioned inbound listeners use `--whitebind=PERMISSIONS@IP:PORT`, for example `--whitebind=noban,forcerelay@127.0.0.1:18444`; a whitebind listener is additive to the configured `--p2p` listener. Block pruning follows Core's `--prune=1` manual mode or `--prune=<MiB>` automatic target mode (automatic targets must be at least 550 MiB); `pruneblockchain` is only available when pruning is enabled.

`--peertimeout=<seconds>` controls the inactivity ping timeout (60 seconds by default); the automatic peer connection limit defaults to Core's 125 peers.

Use `--txindex` to enable confirmed transaction lookup without supplying a block hash to `getrawtransaction`; Core-style pruning and `--txindex` are mutually exclusive.

Use `--txospenderindex` to enable historical spender lookup for `gettxspendingprevout`; transaction lookup indexes are unavailable in prune mode.

`--maxmempool=<MB>` sets the transaction pool's byte limit (300 MB by default, or 5 MB in `--blocksonly` mode unless explicitly set); admission uses the existing package-aware eviction policy when the limit is reached.

`--mempoolexpiry=<hours>` controls automatic mempool expiration (336 hours by default, matching Core).

Mining policy follows Core's block-creation options: `--blockmaxweight` defaults to 4,000,000, `--blockreservedweight` defaults to 8,000, and `--blockmintxfee` defaults to 1 sat/kvB. These settings affect `getblocktemplate`, `generate*`, and `getmininginfo`.

Relay policy follows Core's fee and standardness switches: `--minrelaytxfee` and `--incrementalrelayfee` default to 100 sat/kvB, `--dustrelayfee` defaults to 3,000 sat/kvB, and `--permitbaremultisig`, `--datacarrier`, and `--datacarriersize` control the corresponding mempool policy checks.

`--coinstatsindex` persists incremental UTXO statistics and enables historical `gettxoutsetinfo` queries by block hash or height.

`--blockfilterindex=basic` enables the BIP157 basic compact-filter index, its RPC/REST methods, and compact-filter P2P service; it is disabled by default, matching Core.

`--reindex` and `--reindex-chainstate` rebuild this implementation's chain metadata and UTXO state from the durable block store on startup. The rebuild ignores the existing binary or legacy JSON chainstate/snapshot files and preserves the stored block records.

`--loadblock=<path>` imports one or more Core-style network-magic/length-framed block files at startup; each block still passes normal header, consensus, and chain-selection validation.

ZeroMQ topics can be enabled with the Core-style options, for example
`--zmqpubhashtx tcp://127.0.0.1:28332 --zmqpubsequence tcp://127.0.0.1:28333`.
`getzmqnotifications` reports the configured topic endpoints and high-water marks.
