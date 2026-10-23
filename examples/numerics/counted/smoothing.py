def smooth_step(x: float, y: float, observation: float) -> tuple[float, float]:
    return (x + observation) / 2.0, (y + observation) / 2.0


def smooth(x: float, y: float, observation: float, steps: int) -> tuple[float, float]:
    for _ in range(steps):
        x, y = smooth_step(x, y, observation)
    return x, y
