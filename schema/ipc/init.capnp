@0xf2c5cfa319406aa6;

using Proxy = import "/mp/proxy.capnp";
using Echo = import "echo.capnp";
using Mining = import "mining.capnp";

interface Init {
    construct @0 (threadMap :Proxy.ThreadMap) -> (threadMap :Proxy.ThreadMap);
    makeEcho @1 (context :Proxy.Context) -> (result :Echo.Echo);
    makeMining @3 (context :Proxy.Context) -> (result :Mining.Mining);
    makeMiningOld2 @2 () -> ();
}
