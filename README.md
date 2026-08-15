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

It is not yet a drop-in replacement for every Bitcoin Core 31.1 behavior. In particular, the storage engine uses indexed append-only records with compact versioned binary chain metadata/snapshots and a lightweight JSON `peers.json` address table rather than Core's production database, manual pruning rewrites this implementation's block and undo stores while retaining active-chain transaction counts in a compact sidecar for chain statistics, external UTXO snapshots use Core's binary `utxo\xff` format and support historical active-chain `dumptxoutset` rollback by replay, while legacy internal JSON chainstate files remain readable and are migrated on write, and Electrum indexing is in-process rather than a separate electrs database. P2P synchronization includes headers-first validation, Core's low-work two-phase header presync/commitment protocol, bounded block requests, block-stall detection/backoff, and Core-style request timeouts. Strict `loadtxoutset` activation enforces the v31.1 hardcoded AssumeUTXO commitments, serves the snapshot-backed tip immediately, and validates an independent chainstate asynchronously with durable replay checkpoints and restart recovery; a mismatch promotes the independently replayed state and discards the snapshot. SOCKS5 proxy routing, native I2P SAM v3.1 transport, Core-compatible domain-form destination encoding, optional per-connection stream-isolation credentials via `--proxyrandomize`, typed BIP155 address-manager persistence/relay for IPv4, IPv6, Tor, I2P, and CJDNS, endpoint-aware `onlynet` filtering, numeric-IP whitelist permissions, permissioned `whitebind` listeners, and proxy-backed private broadcast connections are implemented. Mempool persistence uses Core's versioned binary `mempool.dat` format (including v1/v2 loading, v2 obfuscation, fee deltas, and unbroadcast metadata); legacy JSON pool files remain importable. Miniscript-backed taproot-tree derivation, PSBT leaf metadata, and transient-descriptor-key script-path signing/finalization are supported, but the broader wallet/policy satisfaction surface is not a complete wallet replacement. Full mainnet deployment still requires broader Core test-vector, reorg, fuzz, and interoperability testing.

The node never creates, imports, or stores Bitcoin wallet private keys. A private extended key supplied directly in a descriptor RPC is used only for that request and is not retained; the optional I2P transport stores only its SAM destination identity in `i2p_private_key`. Wallet RPCs are intentionally not implemented.

## Running

Automatic Tor onion listening is enabled whenever P2P listening is active. Disable it with --listenonion=false; --torcontrol selects the control service (127.0.0.1:9051 by default) and --torpassword enables password authentication. The controller supports NULL, SAFECOOKIE, and COOKIE authentication, publishes an Ed25519 v3 service with ADD_ONION, keeps the control connection alive, caches its identity in onion_v3_private_key, discovers Tor's SOCKS listener for onion outbound connections, and retries when Tor is unavailable. The generated Tor identity is a network-service key, not a Bitcoin wallet key.

```text
cargo run -- --network regtest --datadir ./data
```

The default configuration listens on the selected network’s loopback P2P and JSON-RPC ports (`8333`/`8332` on mainnet, `18333`/`18332` on testnet, `48333`/`48332` on testnet4, `38333`/`38332` on signet, and `18444`/`18443` on regtest), with Electrum on `127.0.0.1:30001`. Select a network with `--network=<name>` or Core-compatible `--mainnet`, `--testnet`, `--testnet4`, `--signet`, or `--regtest` aliases. `--port` changes the default loopback P2P port and `--rpcport` changes the default loopback RPC port; explicit `--p2p` and `--rpc` values override these defaults. Repeatable comma-delimited `--bind` and `--rpcbind` options expose multiple P2P or RPC listeners. As in Core, `--rpcbind` is honored only when at least one `--rpcallowip` rule is supplied; its port is optional and otherwise inherits `--rpcport`.

The default read-only configuration file is `<datadir>/bitcoin.conf`; use `--conf=<path>` for another file or `--noconf` to suppress config-file loading. Options are written as `name=value`, may be grouped under `[main]`, `[testnet]`, `[testnet4]`, `[signet]`, or `[regtest]`, and may include another file with `includeconf=<path>`. Command-line options take precedence.

JSON-RPC is enabled by default for this daemon and allows loopback clients using the standard cookie file at `<datadir>/.cookie`; clients should send it as HTTP Basic authentication (`curl --user "$(cat data/.cookie)" ...`). Use `--server=false` to disable the HTTP JSON-RPC listeners and cookie generation. Add repeatable `--rpcallowip=<ip[/prefix]>` rules for additional source networks, or use Core-style dotted IPv4 netmasks. `--rpcuser`/`--rpcpassword` enables plaintext credential authentication instead of the cookie, while repeatable `--rpcauth=USER:SALT$HASH` enables salted HMAC-SHA-256 credentials alongside cookie authentication. Use `--rpccookiefile=<path>` to relocate the generated cookie relative to the data directory, `--rpccookieperms=owner|group|all` to control Unix readability, or `--norpccookiefile` when alternate credentials are configured. Repeatable `--rpcwhitelist=USER:METHOD[,METHOD]` rules restrict authenticated users to named RPC methods; specifying any rule enables the Core default that users without a rule are denied, overridable with `--rpcwhitelistdefault=false`.

RPC request handling uses Core-compatible defaults of 16 worker slots, 64 queued requests, and a 30-second HTTP timeout. These can be tuned with `--rpcthreads`, `--rpcworkqueue`, and `--rpcservertimeout`.

For the public signet, use `--network signet`. Custom BIP325 challenges can be supplied as script hex with `--signet-challenge <hex>`.

Bloom-filter peer relay is disabled by default, matching Core's default; enable it with `--peer-bloom-filters` when serving BIP37 clients.

Inbound P2P listening can be disabled with `--listen=false`; DNS seed lookup can be disabled with `--dnsseed=false`. `--networkactive=false` starts with P2P activity disabled and can be reversed with `setnetworkactive`. `--discover=false` suppresses automatically advertised local addresses, while `--externalip=<ip[:port]>` adds a manually advertised address and disables discovery by default. `--dns=false` prevents direct DNS resolution of hostname peers; SOCKS5 domain routing remains available. As in Core, configuring `--proxy=<ip:port>` disables listening by default for privacy and routes routable outbound peer connections through SOCKS5; stream-isolation credentials are randomized by default and can be disabled with `--proxyrandomize=false`; use `--listen=true` or a `--whitebind` listener when local inbound connections are intended. BIP324 v2 transport is enabled by default and can be disabled with `--v2transport=false`; the advertised `P2P_V2` service bit and automatic/manual transport selection follow that setting. `--connect`, `--addnode`, and the `addnode` RPC accept numeric addresses with an optional network-default port and hostnames with an optional port; hostname peers are sent to SOCKS5 as domain targets when a proxy is configured. `--connect=0` or `--noconnect` disables automatic outbound connections while leaving inbound and manual RPC connections available. `--onlynet=ipv4`, `--onlynet=ipv6`, `--onlynet=onion`, `--onlynet=i2p`, or `--onlynet=cjdns` restrict automatic outbound address selection; inbound and manual connections are unaffected. CJDNS requires `--cjdnsreachable`. Tor endpoints use `--onion=<ip:port>` when supplied, otherwise the generic `--proxy`; I2P endpoints use `--i2psam=<ip:port>` with SAM v3.1 and fall back to SOCKS5 routing only when SAM is not configured; CJDNS endpoints use their IPv6 socket representation. `--i2pacceptincoming=false` disables the SAM inbound listener and uses transient I2P sessions for outbound connections. `--privatebroadcast` requires a SOCKS5 proxy and cannot be combined with `--connect`; it changes `sendrawtransaction` to queue a validated transaction for three dedicated, short-lived IPv4/IPv6 connections through that proxy. The transaction remains out of the local mempool until received back from a peer, and `getprivatebroadcastinfo`/`abortprivatebroadcast` expose the queue. `--blocksonly` disables ordinary transaction relay while retaining block synchronization and local RPC/mempool operation; a peer matched by a whitelist rule with `relay` or `forcerelay` can still relay transactions. Whitelist rules use Core's `permissions@IP[/PREFIX]` form, for example `--whitelist=192.0.2.0/24` for the implicit incoming permissions (`noban`, `download`, and `mempool`, plus `relay` unless blocksonly is active), or `--whitelist=forcerelay,relay@198.51.100.7`. Add `in` or `out` to target connection direction, and use `--whitelistrelay=false` or `--whitelistforcerelay` to adjust implicit defaults. Permissioned inbound listeners use `--whitebind=PERMISSIONS@IP:PORT`, for example `--whitebind=noban,forcerelay@127.0.0.1:18444`; a whitebind listener is additive to the configured `--p2p` listener. Block pruning follows Core's `--prune=1` manual mode or `--prune=<MiB>` automatic target mode (automatic targets must be at least 550 MiB); `pruneblockchain` is only available when pruning is enabled.

`--timeout=<milliseconds>` bounds each initial outbound TCP connection attempt (5,000 ms by default). `--peertimeout=<seconds>` controls the inactivity ping timeout (60 seconds by default); the automatic peer connection limit defaults to Core's 125 peers.
Repeatable `--uacomment=<comment>` values are appended to the BIP14 P2P user-agent string; comments use Core's safe character set and the complete string is capped at 256 bytes. `--startupnotify=<command>`, `--blocknotify=<command>`, and `--shutdownnotify=<command>` run asynchronously through the platform shell; `%s` in `--blocknotify` expands to the new active tip hash.
Compact-block reconstruction also retains a bounded FIFO of recent non-mempool transactions; tune it with `--blockreconstructionextratxn=<n>` (100 by default, `0` disables the extra cache).

`--forcednsseed` forces a DNS seed lookup even when persisted peer addresses are available; regular DNS seeding is deferred briefly in that case so the saved addresses are tried first. It cannot be combined with `--dnsseed=false`.

`--seednode=<host[:port]>` opens a one-shot address-fetch connection during startup; `--connect` takes precedence, matching Core's manual-connection modes.

Use `--txindex` to enable confirmed transaction lookup without supplying a block hash to `getrawtransaction`; Core-style pruning and `--txindex` are mutually exclusive.

Use `--blocksdir=<path>` to place the append-only block and undo records outside the data directory; relative paths are resolved beneath `--datadir`, while chainstate and indexes remain in the data directory.
Use `--minimumchainwork=<hex>` to override Core's assumed work floor; `0` disables the assumption.
`--assumevalid=<hex>` selects Core's externally verified block for conservative script-check skipping during synchronization; `0` disables it. Public-network defaults match Core v31.1, while custom Signet challenges disable the default.
`--maxtipage=<seconds>` controls the maximum tip age used to leave initial block download (24 hours by default).
For explicit startup integrity checks, `--checkblocks=<n>` selects the recent block depth (`0` means all available blocks) and `--checklevel=<0..4>` selects verification thoroughness; either option enables the check.
Debug consistency checks follow Core: `--checkmempool` and `--checkblockindex` default to `1` on regtest and `0` on public networks; set either option to an operation interval, or `0` to disable it.
`--checkaddrman=<n>` checks the persisted known/tried peer endpoint indexes every `n` address-manager mutations; it defaults to `0`, matching Core.
Use `--mocktime=<unix-seconds>` for deterministic regtest/replay startup; `0` restores the system clock.
Script verification uses bounded parallel workers; `--par=<n>` follows Core's convention (`0` autodetects, positive values select the total script-check thread budget, and negative values leave that many cores free).
`--stopatheight=<n>` requests a clean shutdown after the active chain reaches height `n`; `0` disables the limit, and an already-persisted tip at or above the target exits during startup.

Use `--txospenderindex` to enable historical spender lookup for `gettxspendingprevout`; transaction lookup indexes are unavailable in prune mode.

`--maxmempool=<MB>` sets the transaction pool's dynamic-memory limit (300 MB by default, or 5 MB in `--blocksonly` mode unless explicitly set); admission uses the existing package-aware eviction policy when the limit is reached.

`--maxuploadtarget=<size>` limits P2P upload bytes to the size of a rolling 24-hour cycle (`0M` by default, meaning unlimited). Lowercase suffixes use decimal units and uppercase suffixes use powers of 1024, matching Core; once the target is reached, historical blocks older than seven days and filtered blocks are withheld from peers without the `download` permission.

`--mempoolexpiry=<hours>` controls automatic mempool expiration (336 hours by default, matching Core).

Mining policy follows Core's block-creation options: `--blockmaxweight` defaults to 4,000,000, `--blockreservedweight` defaults to 8,000, and `--blockmintxfee` defaults to 1 sat/kvB. These settings affect `getblocktemplate`, `generate*`, and `getmininginfo`.

Relay policy follows Core's fee and standardness switches: `--minrelaytxfee` and `--incrementalrelayfee` default to 100 sat/kvB, `--dustrelayfee` defaults to 3,000 sat/kvB, and `--permitbaremultisig`, `--datacarrier`, and `--datacarriersize` control the corresponding mempool policy checks.
`--bytespersigop=<n>` sets the sigop-adjusted transaction weight multiplier used by relay and mining; it defaults to Core's 20 bytes per sigop.

`--coinstatsindex` persists incremental UTXO statistics and enables historical `gettxoutsetinfo` queries by block hash or height.

`--blockfilterindex=basic` enables the BIP157 basic compact-filter index, its RPC/REST methods, and compact-filter P2P service; it is disabled by default, matching Core.

`--reindex` and `--reindex-chainstate` rebuild this implementation's chain metadata and UTXO state from the durable block store on startup. The rebuild ignores the existing binary or legacy JSON chainstate/snapshot files and preserves the stored block records.

`--loadblock=<path>` imports one or more Core-style network-magic/length-framed block files at startup; each block still passes normal header, consensus, and chain-selection validation.

ZeroMQ topics can be enabled with the Core-style options, for example
`--zmqpubhashtx tcp://127.0.0.1:28332 --zmqpubsequence tcp://127.0.0.1:28333`.
`getzmqnotifications` reports the configured topic endpoints and high-water marks.
