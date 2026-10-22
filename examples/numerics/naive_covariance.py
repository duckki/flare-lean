def posterior_variance(p: float, r: float):
    gain = p / (p + r)
    return (1.0 - gain) * p
