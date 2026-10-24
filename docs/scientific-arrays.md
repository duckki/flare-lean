# Scientific collection verification

The closed scientific profile certifies selected NumPy and Julia APIs through
one typed collection model and the existing numerical checker. The
[skill reference](../skills/verify-numerics/references/scientific-arrays.md) is the
authoritative request/source/setup guide. Maintained
[examples](../examples/numerics/scientific/README.md) include calibration and a
complete two-state dense covariance prediction/correction.

Closed functions can also be selected from a full Python module with
`python_module: true`; see [source selection](automated-delivery.md#select-original-source-definitions)
for its isolation and caller-review premises.

## What is connected

The original source is admitted with explicit dtypes/shapes and operation order.
NumPy eager ufuncs remain collection primitives in the Lean model; explicit loops
retain their indexed read/update order. The scalar graph supplies numerical
obligations, rather than replacing the collection execution claim. A checked
`collection_equiv` bridge equates the collection model's flattened results to
that graph. Original NumPy/Julia executes separately for diagnostic word checks.

`Flare.Binary64.Collection.Tensor` stores dimensions and row-major cells.
`Workflow.Certificate.certificate` checks input dimensions/data sizes, source
access/count conditions, successful model execution, the number and shapes of
returned components, finite results, independent exact-reference accuracy and
budgets. `Workflow.Check` independently reconstructs this complete expected type
and audits its transitive axioms. A scalar-only replacement is rejected.

The exact reference uses independently supplied collection algebra; its matrix
products are Mathlib `Matrix` products. Source arithmetic retains its separate
rounding sites and accumulation schedule. Existing FLARE binary64 pipeline rules
carry every intermediate's error through the whole computation. The new core
module supplies collection definitions and size rules, not per-application error
lemmas or a foreign-proof importer.

Python integer literals and fixed integer expressions with magnitude at most
`2^53` can promote exactly when used in float64 arithmetic; indexing remains
integer-valued. This does not admit integer-array dtypes, arbitrary NumPy casts
or Julia integer promotion. Extra polynomial reference normalization is limited
to 32-node graphs; larger collection graphs retain structural proofs and sharing.

## Dense application

The retained update has two coupled state values and a full 2×2 covariance.
It predicts state, computes `F P Fᵀ + Q`, forms the innovation and gain for a
scalar observation, then corrects state and all four covariance entries.
The independent matrix reference and all six output budgets join one root.
The source's multiplication helpers use explicit ascending loops; it does not
invoke NumPy `matmul`/BLAS. The source file is the actual program certified,
not a rewrite presented as proof of an unsupported library call.

This is single-call arithmetic accuracy under the demonstration domain. It
assumes neither hidden covariance symmetry nor a reset of intermediate error.
Covariance positivity, conditioning, sensor/model validity and repeated-call
invariants are separate requirements. The larger four-state graph probes remain
analysis cases without source-program certificates.

## Implementation and runtime boundary

Selected NumPy operations were inspected in the pinned **2.4.0** implementation:

- [Real double arithmetic ufunc loops](https://github.com/numpy/numpy/blob/v2.4.0/numpy/_core/src/umath/loops_arithm_fp.dispatch.c.src): separate add/subtract/multiply/divide inner operations, with scalar/SIMD dispatch. Reduction paths differ and are excluded.
- [Double scalar arithmetic](https://github.com/numpy/numpy/blob/v2.4.0/numpy/_core/src/umath/scalarmath.c.src) for indexed loop operands, separate from the eager array ufunc route.
- [Array indexing](https://github.com/numpy/numpy/blob/v2.4.0/numpy/_core/src/multiarray/mapping.c) and [outer-product implementation](https://github.com/numpy/numpy/blob/v2.4.0/numpy/_core/numeric.py): the admitted ordinary-array indexing and eager multiplication path.
- Julia **1.11.7** uses ordinary typed vectors and [native Float64 arithmetic](https://github.com/JuliaLang/julia/blob/v1.11.7/base/float.jl), with explicit one-based loops and `--math-mode=ieee`.

These inspected implementations guide the admitted semantic contracts. Their C,
Julia runtime and compiler implementations are not formalized by this change.
Parser/source mapping, ordinary container representation, selected primitive
fidelity and compiler/hardware agreement remain trusted. Callers supply the
stated shape/dtype, finite binary64 data and nontrapping environment. Original-
source samples and runtime probes diagnose agreement; they do not prove those
implementation assumptions. NumPy extension/library identities participate in
freshness auditing. Replay needs neither NumPy nor Julia.

## Reusable Rust delivery

The retained calibration port preserves fixed-array parameters/return, a scalar
helper and its real production loop. The provider reconstructs those actual
arguments in a small extraction wrapper. Fresh Charon/Aeneas extraction and an
authored bridge prove indexing, counter increments and return correspondence;
that actual return joins the same typed numerical root. Debug/release diagnostics
also compare with original Python/NumPy or Julia. Proof expansion stays in the proof.

The current scientific retained-port route has at most two output cells. It is
not a general array-library translator or automatic proof generator. General
slice/state/error APIs retain the authored application route; further automation
remains on the [roadmap](roadmap.md).

## Validation

The maintained smoke/scale suite certifies and cold-replays two/eight-channel
calibration and the dense update. macOS ARM64 also exercises the original Julia
API and freshly extracted Rust port. Ubuntu ARM64 separately exercises NumPy
certification/replay and NumPy-to-Rust delivery with fresh extraction. The Linux
run reused an existing Lean/Aeneas installation and installed the pinned NumPy
runtime; it is not a new clean-machine bootstrap claim. Both routes preserve the
same source, reference, budgets and typed root checks.

The later [delivery evaluation](delivery-evaluation.md) additionally checks the
original NumPy quantile helper in clean-tool Linux and isolated macOS setups,
plus native macOS NumPy-to-Rust portable delivery/rechecking. It records which
installations were fresh and which tools were reused.

Controls cover dtype/broadcast/index/alias/schedule changes, Julia counter scope,
exact decimal reference parsing, false numerical references, altered runtime
libraries, weakened roots and a false Rust port. Tool setup failures remain
separate from proof rejection. See the [development commands](development.md#scientific-collection-regression-checks).
