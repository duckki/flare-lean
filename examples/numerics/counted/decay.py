def decay_step(x: float, y: float, bias: float) -> tuple[float, float]:
    return (x + bias) * 0.25, (y - bias) * 0.5


def decay(steps: int, x: float, y: float, bias: float) -> tuple[float, float]:
    for index in range(steps):
        x, y = decay_step(x, y, bias)
    return x, y
