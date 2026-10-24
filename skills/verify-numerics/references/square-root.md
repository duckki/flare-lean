# Square-root applications

Select `python_math: true` for ordinary scalar Python functions with unshadowed
`math.sqrt` calls and one unaliased `import math`. Explicit `math.fma` may compose
with sqrt; ordinary operators keep separate rounding. Use CPython 3.13/3.14,
`lean-flare` and Lean delivery. Obtain a missing compatible interpreter in the
shared tool pool using [tool-setup.md](tool-setup.md); preserve the application's
runtime configuration.

Use `inspect --python-math`, then provide original domains, units/budgets and an
independent exact specification using `sqrt(expr)`. Require finite native values
and prove nonnegative native and exact radicands. The function model is
`functions: {"sqrt": "ieee754-binary64-nearest-even"}` in the arithmetic object;
`fma` is `"explicit"` only when the source actually contains admitted FMA calls.
Other libm error contracts or binary32 types need separate bridges.

The checker proposes rational endpoints without host sqrt and proves their square
inequalities in Lean. It uses a positive-floor perturbation bound when available,
or a zero-inclusive squared-allowance bound otherwise. Keep accumulated errors
before and after the call. Near-zero bounds can be coarse; a domain gap or a
checked allowance above budget is not a numerical counterexample.

The selected CPython extension/platform is assumed to implement the declared
correctly rounded contract. Record executable/extension hashes and platform/version
metadata; preflight and source/IR samples are diagnostics. Do not claim that Lean
verified CPython/libm implementation correctness. Frozen replay rechecks the Lean
model and numerical root without invoking that runtime or inference.

See [the profile guide](../../../docs/arithmetic/square-root.md) and
[the application family](../../../examples/numerics/sqrt/README.md) for exact scope,
measurements, controls and reproducible commands. External producers and Rust
extraction do not yet have this function bridge.
