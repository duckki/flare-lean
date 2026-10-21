def step(mean: float, variance: float, measurement: float, process_noise: float, measurement_noise: float):
    """One random-walk prediction and scalar Kalman measurement correction."""
    predicted_variance = variance + process_noise
    innovation_variance = predicted_variance + measurement_noise
    gain = predicted_variance / innovation_variance
    innovation = measurement - mean
    next_mean = mean + gain * innovation
    next_variance = (1.0 - gain) * predicted_variance
    return next_mean, next_variance
