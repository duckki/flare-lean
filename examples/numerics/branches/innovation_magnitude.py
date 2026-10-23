def innovation_magnitude(observation: float, prediction: float) -> float:
    residual = observation - prediction
    if residual >= 0.0:
        return residual
    else:
        return -residual
