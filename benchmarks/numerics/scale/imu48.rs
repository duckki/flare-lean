//! Mean-only IMU prediction with original integer nanoseconds and certified
//! arithmetic padding. Units: metres, seconds, metres/second, metres/second².
//! Physical sensor/model error is separate. Unsupported inputs are rejected.
use crate::timestamp_alignment::{elapsed_seconds, TimingError};

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Sample {
    pub timestamp: u64,
    pub acceleration: f64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    WrongSize,
    UnsupportedAcceleration,
    UnsupportedThreshold,
    Timing(TimingError),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Decision {
    Below,
    Above,
    Uncertain,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Assessment {
    pub position: f64,
    pub velocity: f64,
    pub error_allowance: f64,
    pub decision: Decision,
}

/// Exactly 48 * 2^-35 metres; a conservative arithmetic allowance.
pub const ERROR_ALLOWANCE: f64 = 1.3969838619232178e-09;
/// Exactly 2^-28 metres; also covers the rounded decision subtraction.
pub const DECISION_PADDING: f64 = 3.725290298461914e-9;

pub fn supported_acceleration(a: f64) -> bool {
    a.is_finite() && -4.0 <= a && a <= 4.0
}

pub fn supported_threshold(x: f64) -> bool {
    x.is_finite() && -1.0 <= x && x <= 1.0
}

/// Keep all eight operations separate: no reassociation or fused multiply-add.
pub fn step(position: f64, velocity: f64, acceleration: f64, dt: f64) -> (f64, f64) {
    let squared = dt * dt;
    let accelerated = squared * acceleration;
    let half = accelerated / 2.0;
    let translation = dt * velocity;
    let translated = position + translation;
    let next_position = translated + half;
    let velocity_increment = dt * acceleration;
    let next_velocity = velocity + velocity_increment;
    (next_position, next_velocity)
}

pub fn classify(position: f64, threshold: f64) -> Decision {
    let margin = position - threshold;
    if margin < -DECISION_PADDING {
        Decision::Below
    } else if DECISION_PADDING < margin {
        Decision::Above
    } else {
        Decision::Uncertain
    }
}

pub fn advance(previous: u64, sample: &Sample, state: (f64, f64)) -> Result<(f64, f64), Error> {
    if !supported_acceleration(sample.acceleration) {
        return Err(Error::UnsupportedAcceleration);
    }
    let seconds = match elapsed_seconds(previous, sample.timestamp) {
        Ok(seconds) => seconds,
        Err(error) => return Err(Error::Timing(error)),
    };
    Ok(step(state.0, state.1, sample.acceleration, seconds))
}

pub fn run_from(
    mut previous: u64,
    samples: &[Sample],
    mut state: (f64, f64),
) -> Result<(f64, f64), Error> {
    for sample in samples {
        state = advance(previous, sample, state)?;
        previous = sample.timestamp;
    }
    Ok(state)
}

/// The certificate covers exactly 48 events, starting from (0 m, 0.5 m/s).
/// The threshold is an original finite binary64 word in [-1,1] metres.
pub fn assess(previous: u64, samples: &[Sample], threshold: f64) -> Result<Assessment, Error> {
    if samples.len() != 48 {
        return Err(Error::WrongSize);
    }
    if !supported_threshold(threshold) {
        return Err(Error::UnsupportedThreshold);
    }
    let (position, velocity) = run_from(previous, samples, (0.0, 0.5))?;
    Ok(Assessment {
        position,
        velocity,
        error_allowance: ERROR_ALLOWANCE,
        decision: classify(position, threshold),
    })
}
