# FLARE

**Floating-point Library for Arithmetic, Rounding, and Error bounds.**

FLARE is a Lean proof library for floating-point arithmetic and numerical
linear algebra. It collects reusable definitions and AI-generated theorems,
together with the mathematics needed to establish their error bounds. Its
primary interface is the collection of statements that other Lean developments
can import and use. Lean checks the proofs; review establishes whether the
definitions, assumptions, and conclusions express the intended guarantee.

Repository: `flare-lean` · Lake package: `flare` · Lean namespace: `Flare`.

## Use the library

Import the full library with `import Flare`, or select a module and use its
theorems in your own proofs:

```lean
import Flare.Binary64.Nearest

#check Flare.Binary64.Nearest.add_error_nearest
#check Flare.Binary64.Nearest.div_error_nearest
```

## Build and check

Install [elan](https://github.com/leanprover/elan), Python 3.9 or newer, and Make,
then run:

```sh
lake exe cache get
make check
```

Lean and Mathlib are pinned to **v4.33.1**. The Lake manifest pins transitive
revisions. The axiom audit checks every FLARE theorem, including private
supporting lemmas, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
The layout check enforces dependency boundaries and entry-point coverage.
`make check` also runs Lean's normal and extra linters, source style checks,
an import-closure check, and the formatter check.

Format Lean sources with `make fmt` using
[leanfmt v0.4.1](https://github.com/duckki/leanfmt/tree/v0.4.1), pinned in Lake.
The line width is **100**, including comments (URLs are exempt from the style
limit). See [CONTRIBUTING.md](CONTRIBUTING.md) for individual check commands.

## What is proved

| Area | Representative results |
| --- | --- |
| Binary64 | Packing, bounded integer conversion, addition, subtraction, multiplication, division, nearest-rounding bounds, comparisons, signed-zero congruence, and square root |
| Dense matrices | Finite storage, multiplication accuracy, LDLᵀ factorization, successful positive-definite solves, substitution and residual bounds |
| Spectral algorithms | Jacobi convergence and spectral error, approximate PSD-check acceptance, and truncated pseudoinverse accuracy |
| Real analysis | Schur complements, conditioning, matrix norms, Gram residual transport, spectral gaps, and pseudoinverse perturbation |

These are theorems about specific operations **under explicit hypotheses**.
Scalar arithmetic includes overflow-domain bounds. Matrix results retain the
proved numerical profiles: for example, at most 32 terms for the dense product
bounds, at most 12 rows for the main solve/pseudoinverse results, and at most 18
rows for Jacobi success. The theorem statements give the complete assumptions.

Concrete algorithm definitions are included where theorems analyze them. They
identify the exact operations and arithmetic order covered by a guarantee.

NaNs and infinities have no real interpretation; both signed zeros mean real
zero. Some proof helpers totalize exceptional or missing values to zero, with
finiteness and representation premises stated separately. The numerical kernels
use native `Float`; they do not execute rational arithmetic or `Float.Model`.

## Organization

One Lake project contains one library, organized by the subjects of its
definitions and theorems:

| Directory | Contents | Allowed FLARE dependencies |
| --- | --- | --- |
| `Flare/Analysis/` | Pure real and discrete mathematics | Analysis |
| `Flare/Binary64/` | Native scalar semantics and error proofs | Analysis, Binary64 |
| `Flare/Binary64/Model/` | Exact model interpretations and supporting proofs | Analysis, Binary64 |
| `Flare/Matrix/` | Matrix accuracy and correctness theorems, storage relations, and the algorithms they analyze | Analysis, Binary64, Matrix |

The [architecture guide](docs/architecture.md) explains the dependency rules
and the proof-library design modeled on Mathlib.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for theorem review and validation.
The [Mathlib guide](docs/upstream/mathlib.md) describes potential contributions
of pure mathematical results. Contribution destinations do not determine
module namespaces; each proposed contribution needs a concrete upstream use.

## Documentation

- [Theorem guide and assurance boundaries](docs/reference.md)
- [Project layout and dependency rules](docs/architecture.md)
- [Source provenance](docs/provenance.md)
