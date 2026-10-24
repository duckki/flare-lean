"""Scalar gain with small positive variances; original binary64 operations."""


def gain(p: float, r: float) -> float:
    return p / (p + r)
