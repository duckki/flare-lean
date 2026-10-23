def gate(signal: float) -> float:
    shifted = signal + 1.0
    if shifted >= 1.0:
        return 1.0
    else:
        return 0.0
