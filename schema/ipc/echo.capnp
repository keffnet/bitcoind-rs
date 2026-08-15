@0x888b4f7f51e691f7;

using Proxy = import "/mp/proxy.capnp";

interface Echo {
    destroy @0 (context :Proxy.Context) -> ();
    echo @1 (context :Proxy.Context, echo :Text) -> (result :Text);
}
