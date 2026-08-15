@0xcc316e3f71a040fb;

interface ThreadMap {
    makeThread @0 (name :Text) -> (result :Thread);
}

interface Thread {
    getName @0 () -> (result :Text);
}

struct Context {
    thread @0 :Thread;
    callbackThread @1 :Thread;
}
