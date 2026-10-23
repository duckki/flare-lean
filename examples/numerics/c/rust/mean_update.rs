fn correction(gain: f64, residual: f64) -> f64 {
    gain * residual
}

pub fn mean_update(prior: f64, gain: f64, residual: f64) -> f64 {
    prior + correction(gain, residual)
}
