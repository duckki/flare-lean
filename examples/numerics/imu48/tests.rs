use crate::imu_epoch::{self, assess, Decision, Error, Sample};
use crate::timestamp_alignment::{elapsed_seconds, TimingError};

fn samples(previous: u64, ticks: u64, acceleration: f64) -> Vec<Sample> {
    (1..=48).map(|i| Sample {
        timestamp: previous + i * ticks,
        acceleration,
    }).collect()
}

fn error(previous: u64, samples: &[Sample], threshold: f64) -> Error {
    match assess(previous, samples, threshold) {
        Err(error) => error,
        Ok(_) => panic!("expected an input error"),
    }
}

#[test]
fn successful_decisions_and_large_integer_epoch() {
    let previous = u64::MAX - 48 * 5_000_000;
    let xs = samples(previous, 5_000_000, 0.0);
    let below = assess(previous, &xs, 1.0).unwrap();
    assert_eq!(below.decision, Decision::Below);
    assert!((below.position - 0.12).abs() <= below.error_allowance);
    assert_eq!(assess(previous, &xs, -1.0).unwrap().decision, Decision::Above);
    assert_eq!(assess(previous, &xs, below.position).unwrap().decision, Decision::Uncertain);
    assert!(below.position.is_finite() && below.velocity.is_finite());
}

#[test]
fn strict_branch_endpoints() {
    let padding = imu_epoch::DECISION_PADDING;
    let next = f64::from_bits(padding.to_bits() + 1);
    assert_eq!(imu_epoch::classify(-padding, 0.0), Decision::Uncertain);
    assert_eq!(imu_epoch::classify(padding, 0.0), Decision::Uncertain);
    assert_eq!(imu_epoch::classify(-next, 0.0), Decision::Below);
    assert_eq!(imu_epoch::classify(next, 0.0), Decision::Above);
}

#[test]
fn size_gate_has_priority() {
    for size in [0, 47, 49] {
        let xs: Vec<_> = (0..size).map(|_| Sample {
            timestamp: 0, acceleration: f64::NAN,
        }).collect();
        assert_eq!(error(u64::MAX, &xs, f64::NAN), Error::WrongSize);
    }
}

#[test]
fn threshold_gate_has_priority_over_samples() {
    let xs = samples(0, 2_000_000, f64::NAN);
    for threshold in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY, 1.00001, -1.00001] {
        assert_eq!(error(0, &xs, threshold), Error::UnsupportedThreshold);
    }
}

#[test]
fn acceleration_gate_has_priority_over_timing() {
    for acceleration in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY, 4.00001, -4.00001] {
        let mut xs = samples(0, 2_000_000, 0.0);
        xs[0] = Sample { timestamp: 0, acceleration };
        assert_eq!(error(1, &xs, 0.0), Error::UnsupportedAcceleration);
    }
}

#[test]
fn integer_timing_rejection_and_inclusive_endpoints() {
    assert_eq!(elapsed_seconds(u64::MAX, 0), Err(TimingError::Reversed));
    for ticks in [0, 1_999_999, 5_000_001, u64::MAX] {
        assert_eq!(elapsed_seconds(0, ticks), Err(TimingError::OutsidePeriod));
    }
    for ticks in [2_000_000, 5_000_000] {
        assert!(elapsed_seconds(u64::MAX - ticks, u64::MAX).is_ok());
        assert!(assess(0, &samples(0, ticks, 0.0), 0.0).is_ok());
    }
}

#[test]
fn application_propagates_first_and_late_errors() {
    let mut xs = samples(1, 2_000_000, 0.0);
    xs[0].timestamp = 0;
    assert_eq!(error(1, &xs, 0.0), Error::Timing(TimingError::Reversed));
    xs = samples(0, 2_000_000, 0.0);
    xs[47].timestamp = xs[46].timestamp + 1_999_999;
    assert_eq!(error(0, &xs, 0.0), Error::Timing(TimingError::OutsidePeriod));
    xs[46].acceleration = f64::NAN;
    assert_eq!(error(0, &xs, 0.0), Error::UnsupportedAcceleration);
}

#[test]
fn zero_padding_diagnostic_would_make_a_false_strict_decision() {
    let xs = samples(0, 5_000_000, 0.0);
    let threshold = f64::from_bits(0.12_f64.to_bits() + 1);
    let output = assess(0, &xs, threshold).unwrap();
    // Exact displacement is 48 * (5_000_000 / 1e9) / 2 = 3/25.
    // The threshold is strictly above 3/25, but accumulated rounding crosses it.
    assert!(output.position - threshold > 0.0);
    assert_eq!(output.decision, Decision::Uncertain);
}
