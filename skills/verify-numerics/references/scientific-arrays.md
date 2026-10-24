# Scientific arrays: NumPy and Julia

Use `scientific_arrays` for a closed scientific API, separately from
`python_arrays` (built-in list products). Confirm the original library calls,
dtypes, shapes and engineering requirements; keep original source and its loops.
The provider admits Python with **NumPy 2.4.0** or **Julia 1.11.7** ordinary
`Vector{Float64}` functions. It uses the default `lean-flare` producer.

## Request and independent reference

Map every original parameter to its shape, with `[]` for a binary64 scalar:

```json
"scientific_arrays": {
  "values": [2],
  "gains": [2],
  "offsets": [2]
},
"specification": {
  "kind": "collections",
  "bindings": [],
  "outputs": ["values*gains+offsets"]
}
```

Each array cell has an original-input domain, for example `values_0` or
`covariance_0_1`. Output targets list all cells in API return order, then row-major
order within each array. The reference is independent exact real algebra, not
NumPy execution. It supports `+ - * /`, scalar broadcasting, matrix/vector `@`,
transpose `.T`, `outer(a,b)`, rational constants and rectangular list literals.
Bindings are ordered `[name, expression]` pairs; names must be fresh. Mathlib
matrix products interpret `@`. Return shapes must match the admitted source.

The maintained provider examples are in `examples/numerics/scientific/`:

- NumPy calibration uses eager multiply/add; an eight-channel request scales it.
- Julia calibration uses a typed scalar helper, fresh vector allocation and
  `for i in 1:length(values)` with ordinary one-based indexing.
- The two-state dense update propagates the entire covariance through
  `F P Fᵀ + Q`, then corrects state and every covariance entry for a scalar
  observation. Its exact reference uses matrix algebra, while its original
  source uses explicit ascending multiplication loops and NumPy operations.
  This covers arithmetic accuracy, not covariance positivity or physical validity.

Examples have conditional demonstration ranges/units/budgets. Obtain the actual
contract rather than treating them as engineering defaults. One invocation does
not establish a repeated-filter invariant or restart an incoming error budget.

Inspect the actual NumPy source without importing its runtime, for example:

```sh
python3 "$FLARE_ROOT/scripts/certify_numerics.py" inspect \
  --language python --source /path/to/calibration.py --function calibrate \
  --scientific-arrays '{"values":[2],"gains":[2],"offsets":[2]}'
```

Then use `plan` with a complete request. Numerical validation must reconstruct
the supplied independent reference; an unproved identity remains unresolved.

## Closed source forms

NumPy source imports exactly `numpy as np` and defines a closed call graph:

- Ordinary positional functions, local helpers, separately rounded `+ - * /`
  and eager `np.add`, `np.subtract`, `np.multiply`, `np.divide`.
- Identical array shapes or scalar broadcasting. NumPy row/column broadcasting,
  mixed dtypes, integer promotions and implicit casts need further support.
- `np.zeros(shape, dtype=np.float64)`, rectangular
  `np.array([...], dtype=np.float64)`, vector `np.outer` and read-only matrix `.T`.
- Explicit indexing of every dimension, fixed `range(size)` loops, initialized
  scalar locals and updates to fresh owned output arrays. Helpers borrow inputs
  for reading; input/view mutation and alias assignment are rejected. Taking
  `.T` also prevents later in-place changes to its source in this profile.
- Fresh arrays, or tuples of fresh arrays and binary64 scalars, as results.
  Returned views and aliased output components are rejected.

Julia source uses explicit `function`/`end`, `Float64`/`Vector{Float64}` positional
parameters, direct local helpers, scalar arithmetic, `zeros(Float64, length(v))`,
ordinary indexing, `for i in start:stop` and explicit returns. Bounds must resolve
to fixed ranges under the request; `1:length(v)` is admitted. Julia dotted/fused
broadcast, macros, custom arrays/dispatch and matrix APIs are separate obligations.
Diagnostics execute original Julia; the parser's internal AST is never its proxy.

Arrays have rank one/two for NumPy and rank one for Julia; each dimension is 1–8,
with at most 32 cells per array and 64 original input cells. There must be an array
input. Expansion is capped at 1,024 nodes, 10,000 visited statements, 16 helper
levels and fixed nonnegative loop ranges bounded by 32. Explicit floating
constants keep dtypes clear; integers are used only for indices/extents.

NumPy `matmul`, `dot`, `einsum`, reductions, BLAS/LAPACK, arbitrary slicing/strides,
`out=`, dtype changes and general library calls are excluded. Do not replace an
unsupported original call with a hand-written loop and claim equivalence. Such a
rewrite is a separate adaptation needing its own bridge and review.

## Lean guarantee and trust boundary

The generated model retains collection primitives, indexed reads/writes and the
bounded loops' execution order. `Flare.Binary64.Collection.Tensor` carries
explicit dimensions and row-major cells. The final root checks input dimensions
and storage sizes, source access/count conditions, successful model execution,
return component shapes/sizes, finite outputs, error against the independent
exact reference and every accepted budget. An independent checker reconstructs
that whole type and audits its transitive axioms.

Source parsing/library mapping and the actual NumPy/Julia implementation,
compiler/hardware fidelity and physical container representation remain trusted.
This is not a proof of NumPy's C internals, Julia's compiler or a BLAS backend.
Callers supply ordinary native-endian float64 ndarrays with the declared shapes
and C-contiguous input storage, or ordinary Julia vectors, plus binary64 scalars.
Custom subclasses, overrides, monkey-patching, nonfinite inputs and trapping
floating-error policies are outside this profile. Inputs are read-only and the
selected output allocations are fresh. Warning/status-flag behavior is not the
numerical contract.

Runtime admission records versions and NumPy extension/library file hashes.
Diagnostics compare actual source word results with the graph, check actual
return shapes/dtypes and diagnose input/output aliasing. These samples do not
prove universal compiler/library correspondence. Frozen-source replay recompiles
Lean and rederives the source model without NumPy, Julia, numerical producers,
Rust extractors or an LLM; only the compatible Lean proof libraries are needed.

## Setup and Rust delivery

Read [tool-setup.md](tool-setup.md#numpy-and-julia-runtimes) to obtain
missing runtimes in the announced shared user cache. NumPy needs Python 3.11+;
other CLI profiles retain their own lower requirement. Julia uses the existing
`source_runtime` selector. Build FLARE, then use normal `plan`, `run`, `audit`
and `replay` commands with agreed application artifact destinations.

For a requested Rust port, retain a production API using fixed arrays/scalars
and its actual loop. The provider reconstructs those fixed-array arguments in
an extraction wrapper, then flattens the return for the numerical checker.
This route currently admits at most two output cells and needs an authored
`rust_port` equivalence proof. General Rust API/proof generation is still future
work; the wrapper is not an automatic scientific-library translator.

The maintained calibration port preserves `[f64; 2]` arguments, a scalar helper,
an indexed production loop and `[f64; 2]` return. Its extracted bridge proves
successful indexing, counter increments and return correspondence. Only its
proof expands two iterations. A repeated-call horizon would be a separately
named driver calling the production API; keep that driver separate as in
[source-to-rust.md](source-to-rust.md).
