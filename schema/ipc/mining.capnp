@0xc77d03df6a41b505;

using Common = import "common.capnp";
using Proxy = import "/mp/proxy.capnp";

const maxMoney :Int64 = 2100000000000000;
const maxDouble :Float64 = 1.7976931348623157e308;
const defaultBlockReservedWeight :UInt32 = 8000;
const defaultCoinbaseOutputMaxAdditionalSigops :UInt32 = 400;

interface Mining {
    isTestChain @0 (context :Proxy.Context) -> (result :Bool);
    isInitialBlockDownload @1 (context :Proxy.Context) -> (result :Bool);
    getTip @2 (context :Proxy.Context) -> (result :Common.BlockRef, hasResult :Bool);
    waitTipChanged @3 (context :Proxy.Context, currentTip :Data, timeout :Float64 = .maxDouble) -> (result :Common.BlockRef);
    createNewBlock @4 (context :Proxy.Context, options :BlockCreateOptions, cooldown :Bool = true) -> (result :BlockTemplate);
    checkBlock @5 (context :Proxy.Context, block :Data, options :BlockCheckOptions) -> (reason :Text, debug :Text, result :Bool);
    interrupt @6 () -> ();
}

interface BlockTemplate {
    destroy @0 (context :Proxy.Context) -> ();
    getBlockHeader @1 (context :Proxy.Context) -> (result :Data);
    getBlock @2 (context :Proxy.Context) -> (result :Data);
    getTxFees @3 (context :Proxy.Context) -> (result :List(Int64));
    getTxSigops @4 (context :Proxy.Context) -> (result :List(Int64));
    getCoinbaseTx @5 (context :Proxy.Context) -> (result :CoinbaseTx);
    getCoinbaseMerklePath @6 (context :Proxy.Context) -> (result :List(Data));
    submitSolution @7 (context :Proxy.Context, version :UInt32, timestamp :UInt32, nonce :UInt32, coinbase :Data) -> (result :Bool);
    waitNext @8 (context :Proxy.Context, options :BlockWaitOptions) -> (result :BlockTemplate);
    interruptWait @9 () -> ();
}

struct BlockCreateOptions {
    useMempool @0 :Bool = true;
    blockReservedWeight @1 :UInt64 = .defaultBlockReservedWeight;
    coinbaseOutputMaxAdditionalSigops @2 :UInt64 = .defaultCoinbaseOutputMaxAdditionalSigops;
}

struct BlockWaitOptions {
    timeout @0 :Float64 = .maxDouble;
    feeThreshold @1 :Int64 = .maxMoney;
}

struct BlockCheckOptions {
    checkMerkleRoot @0 :Bool = true;
    checkPow @1 :Bool = true;
}

struct CoinbaseTx {
    version @0 :UInt32;
    sequence @1 :UInt32;
    scriptSigPrefix @2 :Data;
    witness @3 :Data;
    blockRewardRemaining @4 :Int64;
    requiredOutputs @5 :List(Data);
    lockTime @6 :UInt32;
}
