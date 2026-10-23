//! Checked nanosecond intervals. Subtract original integer words before casting.
//! Error precedence and operation order match the native Lean timing kernel.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TimingError {
    Reversed,
    OutsidePeriod,
}

pub fn ticks_to_float(ticks: u64) -> f64 {
    ticks as f64
}

pub fn elapsed_seconds(previous: u64, current: u64) -> Result<f64, TimingError> {
    if current < previous {
        return Err(TimingError::Reversed);
    }
    let ticks = current - previous;
    if ticks < 2_000_000 || 5_000_000 < ticks {
        return Err(TimingError::OutsidePeriod);
    }
    Ok((ticks as f64) * 1.0e-9)
}
