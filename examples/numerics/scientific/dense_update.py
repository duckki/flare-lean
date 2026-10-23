import numpy as np


def product2(left, right):
    output = np.zeros((2, 2), dtype=np.float64)
    for i in range(2):
        for j in range(2):
            for k in range(2):
                output[i, j] = output[i, j] + left[i, k] * right[k, j]
    return output


def apply2(matrix, vector):
    output = np.zeros(2, dtype=np.float64)
    for i in range(2):
        for j in range(2):
            output[i] = output[i] + matrix[i, j] * vector[j]
    return output


def update(state, covariance, transition, process, measurement, noise):
    predicted = apply2(transition, state)
    propagated = product2(product2(transition, covariance), transition.T)
    prior = np.add(propagated, process)
    observation = np.array([1.0, 0.5], dtype=np.float64)
    projected = apply2(prior, observation)
    row_projection = apply2(prior.T, observation)
    innovation = observation[0] * projected[0] + observation[1] * projected[1] + noise
    gain = np.divide(projected, innovation)
    residual = measurement - (observation[0] * predicted[0] + observation[1] * predicted[1])
    posterior_state = np.add(predicted, np.multiply(gain, residual))
    posterior_covariance = np.subtract(prior, np.outer(gain, row_projection))
    return posterior_state, posterior_covariance
