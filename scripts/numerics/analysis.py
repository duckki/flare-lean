"""Propose untrusted exact-rational summaries; accepted bounds require Lean checking."""
from dataclasses import asdict, dataclass
from fractions import Fraction as Q

from .frontend import number


@dataclass(frozen=True)
class Bound:
    c: Q
    w: Q
    i: Q
    e: Q

    @property
    def cap(self):
        return abs(self.c) + self.w

    def record(self):
        return {k: str(v) for k, v in asdict(self).items()}


def up(x, exponent):
    grid = Q(2) ** exponent
    return -(-x // grid) * grid


def normalized(b):
    grid = Q(2) ** -20
    c = (b.c // grid) * grid
    return Bound(c, up(b.w + abs(b.c-c), -20), up(b.i, -20), up(b.e, -45))


def scale_normalized(b):
    """Outward rounding relative to the current scale, including error bounds."""
    cap = max(abs(b.c), b.w, b.i)
    exponent = cap.numerator.bit_length()-cap.denominator.bit_length() if cap else -1022
    grid = Q(2)**(exponent-40)
    centre = (b.c//grid)*grid
    return Bound(centre, up(b.w+abs(b.c-centre), exponent-40),
                 up(b.i, exponent-40), up(b.e, exponent-64))


def magnitude_exponent(x):
    n = max(-1022, x.numerator.bit_length() - x.denominator.bit_length())
    while Q(2) ** n < x:
        n += 1
    if n > 1022:
        raise ValueError("Magnitude exceeds the admitted finite-operation profile")
    return n


def analyze(program, domain, normalizer=normalized):
    summaries = {}
    for i, name in enumerate(program.inputs):
        lo, hi = map(Q, domain[name])
        summaries[f"a{i}"] = Bound((lo+hi)/2, (hi-lo)/2, max(abs(lo), abs(hi)), Q(0))
    steps = []
    for node in program.nodes:
        raw_ideal = None
        if node.op == "constant":
            c = Q.from_float(number(node.bits))
            result = Bound(c, Q(0), abs(c), Q(0))
            exponent = None
        elif node.op == "neg":
            a = summaries[node.args[0]]
            result = Bound(-a.c, a.w, a.i, a.e)
            exponent = None
        else:
            a, b = [summaries[x] for x in node.args]
            if node.op in ("add", "sub"):
                exponent = magnitude_exponent(a.cap+b.cap)
                rho = Q(2) ** (exponent-52)
                result = Bound(a.c+b.c if node.op == "add" else a.c-b.c,
                               a.w+b.w+rho, a.i+b.i, a.e+b.e+rho)
            elif node.op == "mul":
                exponent = magnitude_exponent(a.cap*b.cap)
                rho = Q(2) ** (exponent-52)
                result = Bound(a.c*b.c, a.w*b.cap+abs(a.c)*b.w+rho,
                               a.i*b.i, a.e*b.cap+a.i*b.e+rho)
            else:
                lower = b.c-b.w
                ideal_lower = lower-b.e
                if lower <= 0 or ideal_lower <= 0:
                    raise ValueError(f"{node.name}: cannot prove a positive native and exact denominator; refine the domain or use another analysis route")
                exponent = magnitude_exponent(a.cap/lower)
                rho = Q(2) ** (exponent-51)
                result = Bound(a.c/b.c, a.w/lower+abs(a.c)*b.w/(lower*b.c)+rho,
                    a.i/ideal_lower, a.e/lower+a.i*b.e/(lower*ideal_lower)+rho)
            raw_ideal = result.i
            result = normalizer(result)
            # Native range and accumulated error give another exact-magnitude
            # bound. Lean checks this refinement with native_ideal_refine.
            result = Bound(result.c,result.w,min(result.i,result.cap+result.e),result.e)
        summaries[node.name] = result
        steps.append({"node": node.name, "exponent": exponent, "summary": result.record(),
                      "raw_ideal":str(raw_ideal) if raw_ideal is not None else None,
                      "ideal_refinement":raw_ideal is not None and result.i<raw_ideal})
    return summaries, steps
