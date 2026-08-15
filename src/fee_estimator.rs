//! Mempool-based fee estimation.
//!
//! Core's estimator is deliberately independent from wallet policy. It tracks
//! transactions as they enter and leave the mempool, groups them into fee
//! buckets, and keeps exponentially decaying confirmation statistics over
//! short, medium, and long horizons. This module follows that model while
//! using a compact versioned bincode snapshot for persistence.

use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::time::{Duration, SystemTime};

use anyhow::{Context, Result};
use bitcoin::{Transaction, Txid};
use serde::{Deserialize, Serialize};
use tracing::warn;

const CURRENT_FILE_VERSION: u32 = 1;
const MAX_FILE_AGE: Duration = Duration::from_secs(60 * 60 * 60);
const MIN_BUCKET_FEERATE: f64 = 1_000.0;
const MAX_BUCKET_FEERATE: f64 = 10_000_000.0;
const INF_BUCKET_FEERATE: f64 = 1e99;
const FEE_SPACING: f64 = 1.05;

const SHORT_BLOCK_PERIODS: usize = 12;
const SHORT_SCALE: u32 = 1;
const SHORT_DECAY: f64 = 0.962;
const MED_BLOCK_PERIODS: usize = 24;
const MED_SCALE: u32 = 2;
const MED_DECAY: f64 = 0.9952;
const LONG_BLOCK_PERIODS: usize = 42;
const LONG_SCALE: u32 = 24;
const LONG_DECAY: f64 = 0.99931;
const MAX_TRACKED_CONFIRMS: u32 = 1_008;

const HALF_SUCCESS_PCT: f64 = 0.60;
const SUCCESS_PCT: f64 = 0.85;
const DOUBLE_SUCCESS_PCT: f64 = 0.95;
const SUFFICIENT_FEETXS: f64 = 0.1;
const SUFFICIENT_TXS_SHORT: f64 = 0.5;

#[derive(Clone, Debug)]
pub(crate) struct EstimatorBucket {
    pub start: f64,
    pub end: f64,
    pub within_target: f64,
    pub total_confirmed: f64,
    pub in_mempool: f64,
    pub left_mempool: f64,
}

impl Default for EstimatorBucket {
    fn default() -> Self {
        Self {
            start: -1.0,
            end: -1.0,
            within_target: 0.0,
            total_confirmed: 0.0,
            in_mempool: 0.0,
            left_mempool: 0.0,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct RawFeeEstimate {
    pub feerate_sat_per_kvb: Option<u64>,
    pub pass: EstimatorBucket,
    pub fail: EstimatorBucket,
    pub decay: f64,
    pub scale: u32,
}

#[derive(Clone, Copy)]
enum Horizon {
    Short,
    Medium,
    Long,
}

#[derive(Clone, Debug)]
struct TrackedTransaction {
    entry_height: u32,
    bucket: usize,
    fee_rate_sat_per_kvb: f64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct PersistedStats {
    decay: f64,
    scale: u32,
    tx_count_average: Vec<f64>,
    confirmation_average: Vec<Vec<f64>>,
    failure_average: Vec<Vec<f64>>,
    fee_rate_average: Vec<f64>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct PersistedEstimator {
    version: u32,
    best_height: u32,
    first_recorded_height: u32,
    historical_first: u32,
    historical_best: u32,
    buckets: Vec<f64>,
    medium: PersistedStats,
    short: PersistedStats,
    long: PersistedStats,
}

#[derive(Clone)]
struct ConfirmStats {
    decay: f64,
    scale: u32,
    tx_count_average: Vec<f64>,
    confirmation_average: Vec<Vec<f64>>,
    failure_average: Vec<Vec<f64>>,
    fee_rate_average: Vec<f64>,
    unconfirmed: Vec<Vec<i32>>,
    old_unconfirmed: Vec<i32>,
}

impl ConfirmStats {
    fn new(buckets: usize, periods: usize, decay: f64, scale: u32) -> Self {
        let max_confirms = periods.saturating_mul(scale as usize);
        Self {
            decay,
            scale,
            tx_count_average: vec![0.0; buckets],
            confirmation_average: vec![vec![0.0; buckets]; periods],
            failure_average: vec![vec![0.0; buckets]; periods],
            fee_rate_average: vec![0.0; buckets],
            unconfirmed: vec![vec![0; buckets]; max_confirms.max(1)],
            old_unconfirmed: vec![0; buckets],
        }
    }

    fn from_persisted(value: PersistedStats, buckets: usize) -> Option<Self> {
        if !value.decay.is_finite()
            || !(0.0..1.0).contains(&value.decay)
            || value.scale == 0
            || value.tx_count_average.len() != buckets
            || value.fee_rate_average.len() != buckets
            || value.confirmation_average.is_empty()
            || value.confirmation_average.len() != value.failure_average.len()
            || value
                .confirmation_average
                .iter()
                .any(|row| row.len() != buckets)
            || value.failure_average.iter().any(|row| row.len() != buckets)
            || value
                .tx_count_average
                .iter()
                .chain(value.fee_rate_average.iter())
                .chain(value.confirmation_average.iter().flatten())
                .chain(value.failure_average.iter().flatten())
                .any(|number| !number.is_finite() || *number < 0.0)
        {
            return None;
        }
        let mut stats = Self {
            decay: value.decay,
            scale: value.scale,
            tx_count_average: value.tx_count_average,
            confirmation_average: value.confirmation_average,
            failure_average: value.failure_average,
            fee_rate_average: value.fee_rate_average,
            unconfirmed: Vec::new(),
            old_unconfirmed: vec![0; buckets],
        };
        stats.resize_unconfirmed_counters();
        Some(stats)
    }

    fn persisted(&self) -> PersistedStats {
        PersistedStats {
            decay: self.decay,
            scale: self.scale,
            tx_count_average: self.tx_count_average.clone(),
            confirmation_average: self.confirmation_average.clone(),
            failure_average: self.failure_average.clone(),
            fee_rate_average: self.fee_rate_average.clone(),
        }
    }

    fn resize_unconfirmed_counters(&mut self) {
        let max_confirms = self
            .confirmation_average
            .len()
            .saturating_mul(self.scale as usize)
            .max(1);
        self.unconfirmed = vec![vec![0; self.tx_count_average.len()]; max_confirms];
        self.old_unconfirmed = vec![0; self.tx_count_average.len()];
    }

    fn max_confirms(&self) -> u32 {
        self.confirmation_average
            .len()
            .saturating_mul(self.scale as usize)
            .try_into()
            .unwrap_or(u32::MAX)
    }

    fn bucket_index(buckets: &[f64], fee_rate: f64) -> usize {
        buckets
            .iter()
            .position(|boundary| fee_rate <= *boundary)
            .unwrap_or_else(|| buckets.len().saturating_sub(1))
    }

    fn clear_current(&mut self, height: u32) {
        let index = height as usize % self.unconfirmed.len();
        for bucket in 0..self.old_unconfirmed.len() {
            self.old_unconfirmed[bucket] =
                self.old_unconfirmed[bucket].saturating_add(self.unconfirmed[index][bucket]);
            self.unconfirmed[index][bucket] = 0;
        }
    }

    fn update_moving_averages(&mut self) {
        for bucket in 0..self.tx_count_average.len() {
            for period in 0..self.confirmation_average.len() {
                self.confirmation_average[period][bucket] *= self.decay;
                self.failure_average[period][bucket] *= self.decay;
            }
            self.tx_count_average[bucket] *= self.decay;
            self.fee_rate_average[bucket] *= self.decay;
        }
    }

    fn new_transaction(&mut self, buckets: &[f64], height: u32, fee_rate: f64) -> usize {
        let bucket = Self::bucket_index(buckets, fee_rate);
        let index = height as usize % self.unconfirmed.len();
        self.unconfirmed[index][bucket] = self.unconfirmed[index][bucket].saturating_add(1);
        bucket
    }

    fn record_confirmation(&mut self, buckets: &[f64], blocks_to_confirm: u32, fee_rate: f64) {
        if blocks_to_confirm == 0 {
            return;
        }
        let periods = blocks_to_confirm.saturating_add(self.scale.saturating_sub(1)) / self.scale;
        let bucket = Self::bucket_index(buckets, fee_rate);
        let start = periods.saturating_sub(1) as usize;
        for row in self.confirmation_average.iter_mut().skip(start) {
            row[bucket] += 1.0;
        }
        self.tx_count_average[bucket] += 1.0;
        self.fee_rate_average[bucket] += fee_rate;
    }

    fn remove_transaction(
        &mut self,
        entry_height: u32,
        best_height: u32,
        bucket: usize,
        in_block: bool,
    ) {
        let blocks_ago = best_height.saturating_sub(entry_height);
        if blocks_ago >= self.max_confirms() {
            self.old_unconfirmed[bucket] = self.old_unconfirmed[bucket].saturating_sub(1);
        } else {
            let index = entry_height as usize % self.unconfirmed.len();
            self.unconfirmed[index][bucket] = self.unconfirmed[index][bucket].saturating_sub(1);
        }
        if !in_block && blocks_ago >= self.scale {
            let periods = (blocks_ago / self.scale) as usize;
            let failure_periods = periods.min(self.failure_average.len());
            for row in self.failure_average.iter_mut().take(failure_periods) {
                row[bucket] += 1.0;
            }
        }
    }

    fn estimate(
        &self,
        buckets: &[f64],
        target: u32,
        sufficient_tx_value: f64,
        success_threshold: f64,
        best_height: u32,
    ) -> (Option<f64>, EstimatorBucket, EstimatorBucket) {
        if target == 0 || target > self.max_confirms() || !(0.0..=1.0).contains(&success_threshold)
        {
            return (None, EstimatorBucket::default(), EstimatorBucket::default());
        }
        let period_target = target.saturating_add(self.scale.saturating_sub(1)) / self.scale;
        let period_target = period_target.saturating_sub(1) as usize;
        let max_bucket = buckets.len().saturating_sub(1);
        let mut confirmed_within = 0.0;
        let mut total_confirmed = 0.0;
        let mut in_mempool = 0.0;
        let mut left_mempool = 0.0;
        let mut current_near = max_bucket;
        let mut current_far = max_bucket;
        let mut best_near = max_bucket;
        let mut best_far = max_bucket;
        let mut partial = 0.0;
        let mut found = false;
        let mut new_range = true;
        let mut passing = true;
        let mut pass = EstimatorBucket::default();
        let mut fail = EstimatorBucket::default();

        for bucket in (0..=max_bucket).rev() {
            if new_range {
                current_near = bucket;
                new_range = false;
            }
            current_far = bucket;
            confirmed_within += self.confirmation_average[period_target][bucket];
            partial += self.tx_count_average[bucket];
            total_confirmed += self.tx_count_average[bucket];
            left_mempool += self.failure_average[period_target][bucket];
            for confirmation in target..self.max_confirms() {
                let index =
                    best_height.saturating_sub(confirmation) as usize % self.unconfirmed.len();
                in_mempool += f64::from(self.unconfirmed[index][bucket]);
            }
            in_mempool += f64::from(self.old_unconfirmed[bucket]);
            if partial < sufficient_tx_value / (1.0 - self.decay) {
                continue;
            }
            partial = 0.0;
            let denominator = total_confirmed + left_mempool + in_mempool;
            let percentage = if denominator > 0.0 {
                confirmed_within / denominator
            } else {
                0.0
            };
            if percentage < success_threshold {
                if passing {
                    fail = Self::bucket_range(
                        buckets,
                        current_near,
                        current_far,
                        confirmed_within,
                        total_confirmed,
                        in_mempool,
                        left_mempool,
                    );
                    passing = false;
                }
                continue;
            }
            fail = EstimatorBucket::default();
            found = true;
            passing = true;
            pass.within_target = confirmed_within;
            confirmed_within = 0.0;
            pass.total_confirmed = total_confirmed;
            total_confirmed = 0.0;
            pass.in_mempool = in_mempool;
            in_mempool = 0.0;
            pass.left_mempool = left_mempool;
            left_mempool = 0.0;
            best_near = current_near;
            best_far = current_far;
            new_range = true;
        }

        let min_bucket = best_near.min(best_far);
        let max_bucket = best_near.max(best_far);
        let mut total_bucket_count = 0.0;
        for bucket in min_bucket..=max_bucket {
            total_bucket_count += self.tx_count_average[bucket];
        }
        let median = if found && total_bucket_count > 0.0 {
            let mut remaining = total_bucket_count / 2.0;
            let mut result = None;
            for bucket in min_bucket..=max_bucket {
                if self.tx_count_average[bucket] < remaining {
                    remaining -= self.tx_count_average[bucket];
                } else {
                    result = Some(self.fee_rate_average[bucket] / self.tx_count_average[bucket]);
                    break;
                }
            }
            pass.start = if min_bucket == 0 {
                0.0
            } else {
                buckets[min_bucket - 1]
            };
            pass.end = buckets[max_bucket];
            result
        } else {
            None
        };
        if passing && !new_range {
            fail = Self::bucket_range(
                buckets,
                current_near,
                current_far,
                confirmed_within,
                total_confirmed,
                in_mempool,
                left_mempool,
            );
        }
        (
            median.filter(|value| value.is_finite() && *value >= 0.0),
            pass,
            fail,
        )
    }

    fn bucket_range(
        buckets: &[f64],
        near: usize,
        far: usize,
        within_target: f64,
        total_confirmed: f64,
        in_mempool: f64,
        left_mempool: f64,
    ) -> EstimatorBucket {
        let min_bucket = near.min(far);
        let max_bucket = near.max(far);
        EstimatorBucket {
            start: if min_bucket == 0 {
                0.0
            } else {
                buckets[min_bucket - 1]
            },
            end: buckets[max_bucket],
            within_target,
            total_confirmed,
            in_mempool,
            left_mempool,
        }
    }
}

pub(crate) struct FeeEstimator {
    path: PathBuf,
    buckets: Vec<f64>,
    medium: ConfirmStats,
    short: ConfirmStats,
    long: ConfirmStats,
    best_height: u32,
    first_recorded_height: u32,
    historical_first: u32,
    historical_best: u32,
    tracked: HashMap<Txid, TrackedTransaction>,
}

impl FeeEstimator {
    pub(crate) fn new(path: PathBuf, best_height: u32, accept_stale: bool) -> Self {
        let buckets = default_buckets();
        let mut estimator = Self {
            medium: ConfirmStats::new(buckets.len(), MED_BLOCK_PERIODS, MED_DECAY, MED_SCALE),
            short: ConfirmStats::new(buckets.len(), SHORT_BLOCK_PERIODS, SHORT_DECAY, SHORT_SCALE),
            long: ConfirmStats::new(buckets.len(), LONG_BLOCK_PERIODS, LONG_DECAY, LONG_SCALE),
            path,
            buckets,
            best_height,
            first_recorded_height: 0,
            historical_first: 0,
            historical_best: 0,
            tracked: HashMap::new(),
        };
        estimator.load(accept_stale, best_height);
        estimator
    }

    fn load(&mut self, accept_stale: bool, current_height: u32) {
        let Ok(metadata) = fs::metadata(&self.path) else {
            return;
        };
        if let Ok(modified) = metadata.modified()
            && let Ok(age) = SystemTime::now().duration_since(modified)
            && age > MAX_FILE_AGE
            && !accept_stale
        {
            warn!(path = %self.path.display(), "fee estimates file is stale; ignoring it");
            return;
        }
        let Ok(bytes) = fs::read(&self.path) else {
            warn!(path = %self.path.display(), "unable to read fee estimates file");
            return;
        };
        let Ok(value) = bincode::deserialize::<PersistedEstimator>(&bytes) else {
            warn!(path = %self.path.display(), "unable to decode fee estimates file");
            return;
        };
        if value.version != CURRENT_FILE_VERSION
            || value.buckets.len() < 2
            || value.buckets.len() > 1_000
            || value
                .buckets
                .iter()
                .any(|bucket| !bucket.is_finite() || *bucket <= 0.0)
            || value.buckets.windows(2).any(|window| window[0] > window[1])
        {
            warn!(path = %self.path.display(), "fee estimates file has an unsupported format");
            return;
        }
        let buckets = value.buckets.len();
        let Some(medium) = ConfirmStats::from_persisted(value.medium, buckets) else {
            warn!(path = %self.path.display(), "fee estimates file has invalid medium statistics");
            return;
        };
        let Some(short) = ConfirmStats::from_persisted(value.short, buckets) else {
            warn!(path = %self.path.display(), "fee estimates file has invalid short statistics");
            return;
        };
        let Some(long) = ConfirmStats::from_persisted(value.long, buckets) else {
            warn!(path = %self.path.display(), "fee estimates file has invalid long statistics");
            return;
        };
        self.buckets = value.buckets;
        self.medium = medium;
        self.short = short;
        self.long = long;
        self.best_height = current_height;
        self.first_recorded_height = value.first_recorded_height;
        self.historical_first = value.historical_first;
        self.historical_best = value.historical_best;
    }

    pub(crate) fn track_mempool_entry(
        &mut self,
        txid: Txid,
        transaction: &Transaction,
        fee_sat: u64,
        vsize: u64,
        height: u32,
    ) {
        if vsize == 0 || height != self.best_height || self.tracked.contains_key(&txid) {
            return;
        }
        let fee_rate = (fee_sat as f64 * 1_000.0) / vsize as f64;
        if !fee_rate.is_finite() || fee_rate <= 0.0 || transaction.is_coinbase() {
            return;
        }
        let bucket = self.medium.new_transaction(&self.buckets, height, fee_rate);
        self.short.new_transaction(&self.buckets, height, fee_rate);
        self.long.new_transaction(&self.buckets, height, fee_rate);
        self.tracked.insert(
            txid,
            TrackedTransaction {
                entry_height: height,
                bucket,
                fee_rate_sat_per_kvb: fee_rate,
            },
        );
    }

    pub(crate) fn remove_from_mempool(&mut self, txid: &Txid) {
        let Some(tracked) = self.tracked.remove(txid) else {
            return;
        };
        self.medium.remove_transaction(
            tracked.entry_height,
            self.best_height,
            tracked.bucket,
            false,
        );
        self.short.remove_transaction(
            tracked.entry_height,
            self.best_height,
            tracked.bucket,
            false,
        );
        self.long.remove_transaction(
            tracked.entry_height,
            self.best_height,
            tracked.bucket,
            false,
        );
    }

    pub(crate) fn process_block(&mut self, height: u32, confirmed: &[Txid]) {
        if height <= self.best_height {
            return;
        }
        self.best_height = height;
        self.medium.clear_current(height);
        self.short.clear_current(height);
        self.long.clear_current(height);
        self.medium.update_moving_averages();
        self.short.update_moving_averages();
        self.long.update_moving_averages();
        let mut counted = 0u32;
        for txid in confirmed {
            let Some(tracked) = self.tracked.remove(txid) else {
                continue;
            };
            let blocks_to_confirm = height.saturating_sub(tracked.entry_height);
            self.medium
                .remove_transaction(tracked.entry_height, height, tracked.bucket, true);
            self.short
                .remove_transaction(tracked.entry_height, height, tracked.bucket, true);
            self.long
                .remove_transaction(tracked.entry_height, height, tracked.bucket, true);
            self.medium.record_confirmation(
                &self.buckets,
                blocks_to_confirm,
                tracked.fee_rate_sat_per_kvb,
            );
            self.short.record_confirmation(
                &self.buckets,
                blocks_to_confirm,
                tracked.fee_rate_sat_per_kvb,
            );
            self.long.record_confirmation(
                &self.buckets,
                blocks_to_confirm,
                tracked.fee_rate_sat_per_kvb,
            );
            counted = counted.saturating_add(1);
        }
        if self.first_recorded_height == 0 && counted > 0 {
            self.first_recorded_height = height;
        }
    }

    pub(crate) fn estimate_smart_fee(
        &self,
        requested_target: u32,
        conservative: bool,
    ) -> (Option<u64>, u32) {
        if requested_target == 0 || requested_target > MAX_TRACKED_CONFIRMS {
            return (None, requested_target);
        }
        let requested_target = requested_target.max(2);
        let mut target = requested_target;
        let max_usable = self.max_usable_estimate();
        if max_usable <= 1 {
            return (None, requested_target);
        }
        if target > max_usable {
            target = max_usable;
        }
        if target <= 1 {
            return (None, target);
        }
        let mut estimate = self
            .estimate_combined(target / 2, HALF_SUCCESS_PCT, true)
            .into_iter()
            .chain(self.estimate_combined(target, SUCCESS_PCT, true))
            .max_by(|left, right| left.total_cmp(right));
        if let Some(double) =
            self.estimate_combined(target.saturating_mul(2), DOUBLE_SUCCESS_PCT, !conservative)
        {
            estimate = Some(estimate.map_or(double, |current| current.max(double)));
        }
        if conservative && let Some(value) = self.estimate_conservative(target.saturating_mul(2)) {
            estimate = Some(estimate.map_or(value, |current| current.max(value)));
        }
        (estimate.map(|value| value.round().max(1.0) as u64), target)
    }

    pub(crate) fn raw_fee_estimates(
        &self,
        target: u32,
        threshold: f64,
    ) -> Vec<(&'static str, RawFeeEstimate)> {
        [
            ("short", Horizon::Short),
            ("medium", Horizon::Medium),
            ("long", Horizon::Long),
        ]
        .into_iter()
        .filter_map(|(name, horizon)| {
            let stats = self.stats(horizon);
            (target <= stats.max_confirms()).then(|| {
                let (rate, pass, fail) = stats.estimate(
                    &self.buckets,
                    target,
                    if matches!(horizon, Horizon::Short) {
                        SUFFICIENT_TXS_SHORT
                    } else {
                        SUFFICIENT_FEETXS
                    },
                    threshold,
                    self.best_height,
                );
                (
                    name,
                    RawFeeEstimate {
                        feerate_sat_per_kvb: rate.map(|value| value.round().max(1.0) as u64),
                        pass,
                        fail,
                        decay: stats.decay,
                        scale: stats.scale,
                    },
                )
            })
        })
        .collect()
    }

    fn stats(&self, horizon: Horizon) -> &ConfirmStats {
        match horizon {
            Horizon::Short => &self.short,
            Horizon::Medium => &self.medium,
            Horizon::Long => &self.long,
        }
    }

    fn estimate_combined(&self, target: u32, threshold: f64, shorter: bool) -> Option<f64> {
        if target == 0 {
            return None;
        }
        let (horizon, sufficient) = if target <= self.short.max_confirms() {
            (Horizon::Short, SUFFICIENT_TXS_SHORT)
        } else if target <= self.medium.max_confirms() {
            (Horizon::Medium, SUFFICIENT_FEETXS)
        } else if target <= self.long.max_confirms() {
            (Horizon::Long, SUFFICIENT_FEETXS)
        } else {
            return None;
        };
        let mut estimate = self
            .stats(horizon)
            .estimate(
                &self.buckets,
                target,
                sufficient,
                threshold,
                self.best_height,
            )
            .0;
        if shorter {
            for (shorter_horizon, max_target, sufficient) in [
                (
                    Horizon::Medium,
                    self.medium.max_confirms(),
                    SUFFICIENT_FEETXS,
                ),
                (
                    Horizon::Short,
                    self.short.max_confirms(),
                    SUFFICIENT_TXS_SHORT,
                ),
            ] {
                if target > max_target {
                    let candidate = self
                        .stats(shorter_horizon)
                        .estimate(
                            &self.buckets,
                            max_target,
                            sufficient,
                            threshold,
                            self.best_height,
                        )
                        .0;
                    if let Some(candidate) = candidate {
                        estimate =
                            Some(estimate.map_or(candidate, |current| current.max(candidate)));
                    }
                }
            }
        }
        estimate
    }

    fn estimate_conservative(&self, target: u32) -> Option<f64> {
        let mut estimate = if target <= self.short.max_confirms() {
            self.medium
                .estimate(
                    &self.buckets,
                    target,
                    SUFFICIENT_FEETXS,
                    DOUBLE_SUCCESS_PCT,
                    self.best_height,
                )
                .0
        } else {
            None
        };
        if target <= self.medium.max_confirms() {
            let candidate = self
                .long
                .estimate(
                    &self.buckets,
                    target,
                    SUFFICIENT_FEETXS,
                    DOUBLE_SUCCESS_PCT,
                    self.best_height,
                )
                .0;
            if let Some(candidate) = candidate {
                estimate = Some(estimate.map_or(candidate, |current| current.max(candidate)));
            }
        }
        estimate
    }

    fn max_usable_estimate(&self) -> u32 {
        let block_span = if self.first_recorded_height == 0 {
            0
        } else {
            self.best_height.saturating_sub(self.first_recorded_height)
        };
        let historical_span = self.historical_best.saturating_sub(self.historical_first);
        self.long
            .max_confirms()
            .min(block_span.max(historical_span) / 2)
    }

    pub(crate) fn flush(&mut self) -> Result<()> {
        let persisted = PersistedEstimator {
            version: CURRENT_FILE_VERSION,
            best_height: self.best_height,
            first_recorded_height: self.first_recorded_height,
            historical_first: self.historical_first,
            historical_best: self.historical_best,
            buckets: self.buckets.clone(),
            medium: self.medium.persisted(),
            short: self.short.persisted(),
            long: self.long.persisted(),
        };
        let bytes = bincode::serialize(&persisted).context("serializing fee estimates")?;
        let temp = self.path.with_file_name("fee_estimates.dat.tmp");
        fs::write(&temp, bytes).with_context(|| format!("writing {}", temp.display()))?;
        fs::rename(&temp, &self.path)
            .with_context(|| format!("replacing {}", self.path.display()))?;
        Ok(())
    }

    pub(crate) fn flush_unconfirmed(&mut self) {
        let txids = self.tracked.keys().copied().collect::<Vec<_>>();
        for txid in txids {
            self.remove_from_mempool(&txid);
        }
    }
}

fn default_buckets() -> Vec<f64> {
    let mut buckets = Vec::new();
    let mut boundary = MIN_BUCKET_FEERATE;
    while boundary <= MAX_BUCKET_FEERATE {
        buckets.push(boundary);
        boundary *= FEE_SPACING;
    }
    buckets.push(INF_BUCKET_FEERATE);
    buckets
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::absolute::LockTime;
    use bitcoin::transaction::Version;
    use bitcoin::{Amount, ScriptBuf, Transaction, TxOut};

    fn transaction(value: u64) -> Transaction {
        Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: Vec::new(),
            output: vec![TxOut {
                value: Amount::from_sat(value),
                script_pubkey: ScriptBuf::new(),
            }],
        }
    }

    #[test]
    fn confirmation_stats_record_success_and_failure_ranges() {
        let buckets = vec![1_000.0, 2_000.0, f64::INFINITY];
        let mut stats = ConfirmStats::new(buckets.len(), 2, 0.5, 1);
        let bucket = stats.new_transaction(&buckets, 0, 1_500.0);
        stats.clear_current(1);
        stats.update_moving_averages();
        stats.remove_transaction(0, 1, bucket, true);
        stats.record_confirmation(&buckets, 1, 1_500.0);

        let (rate, pass, fail) = stats.estimate(&buckets, 1, 0.1, 0.85, 1);
        assert_eq!(rate, Some(1_500.0));
        assert!(pass.within_target > 0.0);
        assert!(fail.start >= -1.0);
        assert!(fail.end >= -1.0);

        let bucket = stats.new_transaction(&buckets, 1, 1_500.0);
        stats.remove_transaction(1, 2, bucket, false);
        let (_, _, fail) = stats.estimate(&buckets, 1, 0.1, 0.99, 2);
        assert!(fail.left_mempool > 0.0 || fail.in_mempool > 0.0);
    }

    #[test]
    fn estimator_tracks_confirmations_and_round_trips_persistence() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("fee_estimates.dat");
        let mut estimator = FeeEstimator::new(path.clone(), 100, false);
        let mut txids = Vec::new();
        for value in 1..=20 {
            let transaction = transaction(value);
            let txid = transaction.compute_txid();
            txids.push(txid);
            estimator.track_mempool_entry(txid, &transaction, 100_000, 100, 100);
        }
        estimator.process_block(101, &txids);
        for height in 102..=105 {
            estimator.process_block(height, &[]);
        }

        let (rate, target) = estimator.estimate_smart_fee(2, false);
        assert_eq!(target, 2);
        assert!(rate.is_some());
        let raw = estimator.raw_fee_estimates(2, 0.85);
        assert_eq!(raw.len(), 3);
        assert!(
            raw.iter()
                .find(|(name, _)| *name == "short")
                .is_some_and(|(_, estimate)| estimate.feerate_sat_per_kvb.is_some())
        );

        estimator.flush().unwrap();
        let restored = FeeEstimator::new(path, 105, false);
        let (restored_rate, restored_target) = restored.estimate_smart_fee(2, false);
        assert_eq!(restored_target, 2);
        assert_eq!(restored_rate, rate);
    }
}
