"""Shared ordered graph and scalar typing for deliberately restricted frontends."""
from dataclasses import asdict, dataclass
import math
import struct


class Unsupported(ValueError):
    pass


@dataclass(frozen=True)
class Node:
    name: str
    op: str
    args: tuple = ()
    bits: int | None = None


@dataclass(frozen=True)
class Program:
    language: str
    function: str
    inputs: tuple
    nodes: tuple
    outputs: tuple

    def record(self):
        return {"schema": "ordered-binary64-v1", **asdict(self)}


def word(value):
    return struct.unpack(">Q", struct.pack(">d", value))[0]


def number(bits):
    return struct.unpack(">d", struct.pack(">Q", bits))[0]


@dataclass(frozen=True)
class Scalar:
    ref: str | None = None
    integer: int | None = None


class Graph:
    def __init__(self, language, function, inputs):
        if not inputs or len(set(inputs)) != len(inputs):
            raise Unsupported('Expected distinct scalar input parameters')
        self.language = language
        self.function = function
        self.inputs = tuple(inputs)
        self.names = {name: Scalar(ref=f'a{i}') for i, name in enumerate(inputs)}
        self.nodes = []

    def emit(self, op, args=(), bits=None):
        node = Node(f'n{len(self.nodes)}', op, tuple(args), bits)
        self.nodes.append(node)
        return Scalar(ref=node.name)

    def literal(self, value):
        if type(value) is int:
            # Only exact integer-to-binary64 promotions are admitted. Do not
            # turn integer-only computations into floating-point operations.
            if abs(value) > 2**53:
                raise Unsupported('Integer literal exceeds exact binary64 promotion range')
            return Scalar(integer=value)
        if type(value) is not float or not math.isfinite(value):
            raise Unsupported('Only finite real binary64 literals are supported')
        return self.emit('constant', bits=word(value))

    def floating(self, value):
        if value.ref is None:
            return self.literal(float(value.integer)).ref
        return value.ref

    def unary(self, op, value):
        if value.integer is not None:
            return Scalar(integer=-value.integer if op == 'neg' else value.integer)
        return self.emit('neg', (value.ref,)) if op == 'neg' else value

    def binary(self, op, left, right):
        if left.integer is not None and right.integer is not None:
            raise Unsupported('Integer-only arithmetic is unsupported; explicitly use float literals in the source if intended')
        return self.emit(op, (self.floating(left), self.floating(right)))

    def finish(self, outputs):
        if not 1 <= len(outputs) <= 2:
            raise Unsupported('Expected one or two scalar outputs')
        if any(value.integer is not None for value in outputs):
            raise Unsupported('Integer outputs cannot be silently converted to binary64')
        return Program(self.language, self.function, self.inputs, tuple(self.nodes),
                       tuple(value.ref for value in outputs))
