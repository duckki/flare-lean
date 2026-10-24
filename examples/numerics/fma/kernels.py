"""Explicitly fused binary64 kernels; ordinary operators retain separate rounding."""
import math


def calibrate(reading: float, gain: float, offset: float) -> float:
    return math.fma(reading, gain, offset)


def residual(x: float) -> float:
    return math.fma(x, x, -1.0)


def regularized_gain(x: float) -> float:
    denominator = math.fma(x, x, 1.0)
    return 1.0 / denominator


def fused_dot3(x0: float, w0: float, x1: float, w1: float,
               x2: float, w2: float) -> float:
    total = math.fma(x0, w0, 0.0)
    total = math.fma(x1, w1, total)
    return math.fma(x2, w2, total)


def reciprocal_calibrate(x: float, gain: float, offset: float) -> float:
    reciprocal = 1.0 / x
    return math.fma(reciprocal, gain, offset)
