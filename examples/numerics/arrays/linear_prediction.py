"""Two-state linear prediction with explicit built-in binary64 list arithmetic."""
def dot(row: list[float], state: list[float]) -> float:
    total = 0.0
    for k in range(len(state)):
        total += row[k] * state[k]
    return total


def predict(transition: list[list[float]], state: list[float]) -> list[float]:
    assert len(transition) == 2
    assert len(state) == 2
    predicted = [0.0, 0.0]
    for i in range(2):
        assert len(transition[i]) == 2
        predicted[i] = dot(transition[i], state)
    return predicted
