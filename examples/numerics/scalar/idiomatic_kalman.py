def step(mean, variance, measurement, process_noise, measurement_noise) -> tuple[float, float]:
    """Scalar double inputs; annotations are optional and do not coerce inputs."""
    variance += process_noise
    gain: float = variance / (variance + measurement_noise)
    mean, variance = mean + gain * (measurement - mean), (1 - gain) * variance
    return mean, variance
