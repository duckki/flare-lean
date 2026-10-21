# Inputs are original Float64 values; no @fastmath or custom arithmetic methods.
function step(mean::Float64, variance::Float64, measurement::Float64,
              process_noise::Float64, measurement_noise::Float64)
    variance += process_noise
    gain = variance / (variance + measurement_noise)
    next_mean = mean + gain * (measurement - mean)
    next_variance = (1 - gain) * variance
    return (next_mean, next_variance)
end
