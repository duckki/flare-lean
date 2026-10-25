"""Ordered products for typed summary and exact-operation inference."""


def power32(x):
    x = x * x
    x = x * x
    x = x * x
    x = x * x
    x = x * x
    return x

def power256(x):
    x = x * x
    x = x * x
    x = x * x
    x = x * x
    x = x * x
    x = x * x
    x = x * x
    x = x * x
    return x

def zero_product(x):
    return x * 0.0

def zero_energy(x):
    x = x * x
    return x * 0.0


def power4096(x):
    x = x * x
    x = x * x
    x = x * x
    x = x * x
    x = x * x
    x = x * x
    x = x * x
    x = x * x
    x = x * x
    x = x * x
    x = x * x
    x = x * x
    return x


def tiny_constants(x):
    y = 1e-300
    y = y * y
    y = y * y
    return y * y
