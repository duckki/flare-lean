//! A checked planar application of two independent scalar GHFilter APIs.
//! Position is in metres, velocity in metres/second. Gains and dt match the
//! source binding; the allowance covers arithmetic, not physical sensor error.
use crate::gh::GhFilter;

#[derive(Clone, Copy, Debug)]
pub struct Measurement {
    pub x: f64,
    pub y: f64,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    WrongSize,
    InvalidInitial,
    InvalidMeasurement,
    InvalidThreshold,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Decision { Below, Above, Uncertain }
#[derive(Clone, Copy, Debug)]
pub struct PlanarTracker {
    pub horizontal: GhFilter,
    pub vertical: GhFilter,
}
#[derive(Clone, Copy, Debug)]
pub struct Assessment {
    pub state: PlanarTracker,
    pub arithmetic_allowance: f64,
    pub decision: Decision,
}
pub const ARITHMETIC_ALLOWANCE: f64 = 9.313225746154785e-10;
pub const DECISION_PADDING: f64 = 3.725290298461914e-9;

pub fn supported_position(x: f64) -> bool { x.is_finite() && -10.0 <= x && x <= 10.0 }
pub fn supported_velocity(x: f64) -> bool { x.is_finite() && -2.0 <= x && x <= 2.0 }
pub fn supported_threshold(x: f64) -> bool { x.is_finite() && -20.0 <= x && x <= 20.0 }
impl PlanarTracker {
    pub fn new(x: f64, vx: f64, y: f64, vy: f64) -> Result<Self, Error> {
        if !supported_position(x) || !supported_velocity(vx)
            || !supported_position(y) || !supported_velocity(vy) {
            return Err(Error::InvalidInitial);
        }
        Ok(Self { horizontal: GhFilter::new(x, vx, 0.125, 0.5, 0.125),
                  vertical: GhFilter::new(y, vy, 0.125, 0.5, 0.125) })
    }
    /// Each scalar API preserves its stored gains when an override is supplied.
    /// A rejected measurement leaves both complete scalar states unchanged.
    pub fn update(&mut self, sample: Measurement, g: Option<f64>, h: Option<f64>)
        -> Result<(), Error> {
        if !supported_position(sample.x) || !supported_position(sample.y) {
            return Err(Error::InvalidMeasurement);
        }
        self.horizontal.update(sample.x, g, h);
        self.vertical.update(sample.y, g, h);
        Ok(())
    }
}

/// The reusable driver uses a slice loop. The application theorem specializes
/// its numerical accuracy to eight measurements, while its source bridge covers
/// the general loop and every rejection exit.
pub fn run_from(mut state: PlanarTracker, samples: &[Measurement]) -> Result<PlanarTracker, Error> {
    for sample in samples {
        state.update(*sample, None, None)?;
    }
    Ok(state)
}
pub fn classify(position: f64, threshold: f64) -> Decision {
    let margin = position - threshold;
    if margin < -DECISION_PADDING { Decision::Below }
    else if DECISION_PADDING < margin { Decision::Above }
    else { Decision::Uncertain }
}
pub fn assess(x: f64, vx: f64, y: f64, vy: f64, samples: &[Measurement], threshold: f64)
    -> Result<Assessment, Error> {
    if samples.len() != 8 { return Err(Error::WrongSize); }
    if !supported_threshold(threshold) { return Err(Error::InvalidThreshold); }
    let state = run_from(PlanarTracker::new(x, vx, y, vy)?, samples)?;
    let decision = classify(state.horizontal.x, threshold);
    Ok(Assessment { state, arithmetic_allowance: ARITHMETIC_ALLOWANCE, decision })
}
