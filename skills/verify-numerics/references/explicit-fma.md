# Explicit Python FMA

Select `python_math: true` for ordinary scalar Python code containing unshadowed
`math.fma(x,y,z)` calls and one unaliased `import math`. Use CPython 3.13/3.14,
`lean-flare`, and Lean delivery. Run `inspect --python-math` before filling in
original finite input ranges, independent exact specifications, units and budgets.
If the current interpreter lacks this profile, obtain a compatible CPython in the
shared tool pool using [tool-setup.md](tool-setup.md), then invoke the provider
with that interpreter. Preserve the application's existing runtime configuration.

Each call is one ternary graph node and one final rounding. Ordinary `*` and `+`
retain separate rounding sites. Never silently fuse, unfuse or reassociate the
source or Rust port. An alternative schedule requires a separate reviewed artifact.
The frozen model records `fma: "explicit"`; ordinary/external-producer routes keep
`fma: false`. The selected [square-root bridge](square-root.md) can compose with FMA. Binary32
casts, other math functions, Rust extraction and arbitrary
composition with other source profiles are not admitted by this profile.

Lean checks the actual native FMA rounding law, finiteness, accumulated input
errors, exact-reference relation and numerical root. Runtime admission retains
CPython/math identities and sampled probes. Source mapping and platform/runtime
fidelity remain trusted; a successful diagnostic is not an implementation proof.
Cold replay uses saved Lean sources without executing Python or inference.

Use the cancellation residual as a schedule control, not as permission to optimize
a user's code. Its fused schedule certifies a `10⁻²³` budget; a separate request
with unchanged requirements has a checked `budget_not_met` result. This status
is not a counterexample certificate. Zero rounding allowances and substituting
separate arithmetic under the FMA proof must be rejected by Lean.

For the schema, proof assumptions, sample commands and retained cases, see
[the profile guide](../../../docs/explicit-fma.md) and
[the example family](../../../examples/numerics/fma/README.md).
Confirm application artifact locations using the main skill before creating them.
