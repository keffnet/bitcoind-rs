//! Process-wide clock used by consensus and regression-test RPCs.

use std::sync::atomic::{AtomicI64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static MOCK_TIME: AtomicI64 = AtomicI64::new(0);

#[cfg(test)]
static MOCK_TIME_TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

#[cfg(test)]
pub(crate) struct MockTimeTestGuard {
    previous: i64,
    _lock: std::sync::MutexGuard<'static, ()>,
}

#[cfg(test)]
pub(crate) fn mock_time_test_guard() -> MockTimeTestGuard {
    let lock = MOCK_TIME_TEST_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    MockTimeTestGuard {
        previous: mock_time(),
        _lock: lock,
    }
}

#[cfg(test)]
impl Drop for MockTimeTestGuard {
    fn drop(&mut self) {
        set_mock_time(self.previous);
    }
}

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

/// Return the system Unix time in milliseconds without applying regtest
/// mocktime. Core's network-traffic RPCs use the system clock for this field,
/// even while consensus and peer timestamps use mocktime.
pub fn system_unix_time_millis() -> u128 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis()
}

/// Return Unix time as a signed value for wire timestamps.
pub fn unix_time_i64() -> i64 {
    i64::try_from(unix_time()).unwrap_or(i64::MAX)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn system_millis_ignores_mocktime() {
        let _guard = mock_time_test_guard();
        set_mock_time(1);
        let system = system_unix_time_millis();
        let mock = unix_time_millis();

        assert_eq!(mock, 1_000);
        assert!(system > mock);
    }
}
