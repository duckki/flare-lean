"""Compose small calibration matrices, using fresh independent output rows."""
def compose(left: list[list[float]], right: list[list[float]]) -> list[list[float]]:
    assert len(left) == 2
    assert len(right) == 2
    result = [[0.0, 0.0], [0.0, 0.0]]
    for i in range(2):
        assert len(left[i]) == 2
        assert len(right[i]) == 2
        for j in range(2):
            total = 0.0
            for k in range(2):
                total += left[i][k] * right[k][j]
            result[i][j] = total
    return result
