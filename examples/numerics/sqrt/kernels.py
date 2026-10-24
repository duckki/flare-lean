"""Selected correctly rounded binary64 square-root applications."""
import math


def standard_deviation(variance: float) -> float:
    return math.sqrt(variance)


def regularized_norm(x: float, y: float) -> float:
    energy = x * x + y * y + 1.0
    return math.sqrt(energy)


def normalized_residual(residual: float, variance: float, noise: float) -> float:
    deviation = math.sqrt(variance + noise)
    return residual / deviation


def fused_norm(x: float, y: float) -> float:
    energy = math.fma(x, x, math.fma(y, y, 1.0))
    return math.sqrt(energy)


def nested_root(variance: float) -> float:
    return math.sqrt(math.sqrt(variance))
