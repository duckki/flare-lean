# Verify explicit fused multiply-add

FLARE certifies restricted scalar Python kernels that call `math.fma(x, y, z)`.
The source keeps a ternary operation: its exact product and sum receive one final
binary64 rounding. Ordinary `x*y+z` keeps two rounding sites. The workflow never
inserts FMA into a separate schedule.

This is the first delivered arithmetic feature in
[roadmap milestone 13](roadmap.md#13-cover-more-arithmetic-models).
A [square-root source bridge](square-root.md) is also available. Mixed
binary32/binary64 remains planned.

## Select the profile

Use CPython 3.13 or 3.14 with `math.fma`. Select `python_math: true` in a numerical
request, or pass `--python-math` to `inspect`:

```sh
python3 scripts/certify_numerics.py inspect \
  --language python --source examples/numerics/fma/kernels.py \
  --function calibrate --python-math
python3 scripts/certify_numerics.py run \
  --request examples/numerics/fma/calibrate.json \
  --out .cache/numerics-generated/fma-calibration
python3 scripts/certify_numerics.py replay \
  --run .cache/numerics-generated/fma-calibration \
  --out .cache/numerics-generated/fma-calibration-replay
```

Those destinations are provider regression paths. For application verification,
confirm the verification directory and keep scratch/downloads in the skill's
agreed locations.

The profile admits one unaliased `import math`, ordinary scalar parameters,
assignments, local numerical helpers, fixed literal-tuple loops, and unshadowed
positional `math.fma` calls. It inherits finite binary64 literal/promotion rules
and permits at most 32 ordered graph nodes and one or two scalar outputs.
Non-FMA arithmetic retains the ordinary profile's rules. Unsupported imports,
casts, `math` functions beyond the selected FMA/square-root contracts, keyword
calls and shadowing are rejected.

Use `lean-flare` and Lean delivery. External producer routes, Rust delivery and
composition with the array/conditional/counted profiles need separate bridges.
This profile adds no new runtime/tool dependency to the Lake library.

## What Lean checks

`Flare.Binary64.Nearest.fma_error_nearest` proves finiteness and

```text
|value (a.fma b c) - (value a * value b + value c)|
  ≤ 2⁻⁵³ * (|value a * value b + value c| + 2⁻¹⁰²²)
```

for finite operands whose exact product-plus-sum has magnitude at most `2¹⁰⁰⁰`.
The proof follows Lean 4.35's actual `Float.Model.fma`: it aligns the exact
product and addend before one signed normalization, and handles signed zeros
and a zero addend. It reuses the existing proved rounding/sticky-bit argument.
No rounding law, finite-result condition or analyzer conclusion is an added axiom.
NaN/infinite operands and floating-point exception flags are outside this contract.

The scalar checker propagates incoming operand errors, the independent exact
reference and one rounding allowance per FMA. Its existing typed rational enclosure
engine checks ranges and polynomial correlations. Nonpolynomial predecessors,
such as a reciprocal, use compositional bounds without resetting their errors.
One `Workflow.Certificate.certificate` checks accuracy against the independent
specification, the engineering budget predicate and the root's axiom closure.

The frozen obligation and evidence record this arithmetic model:

```json
{
  "format": "binary64",
  "rounding": "nearest-even",
  "subnormals": "gradual",
  "fma": "explicit",
  "reassociation": false
}
```

The request may provide that same object explicitly. Calls to `math.sqrt` add
its separately declared function model; see the [square-root guide](square-root.md).
A mismatched format, rounding mode, implicit fusion or separate-only model is rejected. Ordinary
profiles retain their existing identities and `fma: false` model.

## Maintained examples and rejection controls

The [example family](../examples/numerics/fma/README.md) includes sensor calibration,
a cancellation residual, a fused three-term dot product, a positive regularized
reciprocal and calibration after an inexact reciprocal. Each has a checked Lean
root and producer/runtime-free replay.

The residual compares against `x*x-1` near one. Explicit FMA certifies the fixed
`10⁻²³` budget; the separate schedule retains its own source and the same budget,
and returns `budget_not_met`. That status describes the checked allowance; it
is not itself a Lean counterexample. Separate kernel-checked bit-pattern examples
in [Tests/PublicAPI.lean](../Tests/PublicAPI.lean) establish that `(1+2⁻²⁷)*(1-2⁻²⁷)-1` is `-2⁻⁵⁴` with
FMA and `+0` with separate arithmetic.

Controls reject wrong formats/models, shadowed/aliased imports, unsupported calls,
missing/unsupported runtimes and a runtime FMA that actually rounds twice.
Lean rejects zero rounding allowances and substituting a separate expression
under the FMA proof. Kernel computations also check negative zero and the smallest
subnormal, tie-to-even underflow and cancellation of a product that would
overflow if rounded separately. Existing ordinary scalar/array/loop regressions remain separate cases.

## Runtime boundary and replay

CPython documents `math.fma` as one final rounding of the exact product and sum.
See the [Python contract](https://docs.python.org/3.14/library/math.html#math.fma).
Source parsing, the mapping to Lean's primitive, CPython, its platform math library
and hardware fidelity remain explicit trust boundaries. FLARE does not prove the
CPython or platform C implementation.

Runtime admission records the Python executable, full version and the loaded
`math` extension's file hash. Preflight probes exercise cancellation, nearest
rounding, signed zero and subnormals; original-source/IR word comparisons are
sampled diagnostics. These do not establish universal implementation equivalence
or identify every dynamically linked platform library. A freshness audit checks
the recorded executable/extension identities. Frozen replay does not load that
runtime or rerun those diagnostics: it rebuilds the source-derived Lean model
and rechecks the saved numerical theorem and axiom closure.
