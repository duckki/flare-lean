def guarded_reciprocal(x: float) -> float:
    if x >= 0.5:
        return 1.0 / x
    else:
        return 0.0
