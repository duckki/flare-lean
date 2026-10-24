"""Binary32 storage boundaries around binary64 engineering computations."""
import numpy as np


def stored(x: float) -> float:
    return float(np.float32(x))


def calibrate(sample: float, gain: float, offset: float) -> float:
    quantized = float(np.float32(sample))
    adjusted = gain * quantized + offset
    return float(np.float32(adjusted))


def normalized_residual(measurement: float, prediction: float, scale: float) -> float:
    quantized = float(np.float32(measurement))
    residual = quantized - prediction
    return float(np.float32(residual / scale))


def storage_chain(x: float, correction: float) -> tuple[float, float]:
    first = stored(x)
    second = stored(first + correction)
    final = stored(second - correction)
    return second, final
