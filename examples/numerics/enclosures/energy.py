"""Separately rounded nonnegative energy factors; no reassociation or FMA."""

def square(x):
    return x * x


def quartic(x):
    squared = x * x
    return squared * squared


def regularized_gain(x):
    return 1.0 / (x * x + 1.0)
