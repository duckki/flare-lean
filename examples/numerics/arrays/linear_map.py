"""Explicit dense matrix-vector application on built-in Python lists."""
def apply_linear(matrix: list[list[float]], vector: list[float]) -> list[float]:
    result = [0.0] * len(matrix)
    for i in range(len(matrix)):
        assert len(matrix[i]) == len(vector)
        for k in range(len(vector)):
            result[i] += matrix[i][k] * vector[k]
    return result
