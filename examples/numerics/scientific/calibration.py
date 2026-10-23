import numpy as np


def calibrate(values, gains, offsets):
    scaled = np.multiply(values, gains)
    return np.add(scaled, offsets)
