//! Process-wide clock used by consensus and regression-test RPCs.

use std::sync::atomic::{AtomicI64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static MOCK_TIME: AtomicI64 = AtomicI64::new(0);

/// Set the process clock used by Bitcoin time-sensitive code. A value of zero
/// restores the system clock, matching Core's `setmocktime` RPC.
pub fn set_mock_time(seconds: i64) {
    MOCK_TIME.store(seconds, Ordering::Relaxed);
}

/// Return the configured mock timestamp, or zero when the system clock is in use.
pub fn mock_time() -> i64 {
    MOCK_TIME.load(Ordering::Relaxed)
}

/// Return Unix time in seconds.
pub fn unix_time() -> u64 {
    let mock = mock_time();
    if mock > 0 {
        return mock as u64;
    }
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
}

/// Return Unix time in milliseconds.
pub fn unix_time_millis() -> u128 {
    let mock = mock_time();
    if mock > 0 {
        return (mock as u128).saturating_mul(1_000);
    }
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis()
}

/// Return Unix time as a signed value for wire timestamps.
pub fn unix_time_i64() -> i64 {
    i64::try_from(unix_time()).unwrap_or(i64::MAX)
}
