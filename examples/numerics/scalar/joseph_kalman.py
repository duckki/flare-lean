def step(mean: float, variance: float, measurement: float, process_noise: float, measurement_noise: float):
    """A different source implementation with Joseph-form scalar covariance."""
    predicted_variance = variance + process_noise
    gain = predicted_variance / (predicted_variance + measurement_noise)
    next_mean = mean + gain * (measurement - mean)
    complement = 1.0 - gain
    next_variance = (complement * predicted_variance) * complement + (gain * measurement_noise) * gain
    return next_mean, next_variance
