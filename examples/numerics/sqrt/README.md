# Square-root applications

These original scalar Python kernels use explicit `math.sqrt` calls and an
independent exact reference. Use the [square-root profile](../../../docs/arithmetic/square-root.md)
with CPython 3.13/3.14, `lean-flare` and Lean delivery.

| Request | Checked behavior | Expected result |
| --- | --- | --- |
| `standard_deviation.json` | Variance in `[0,16]`, including zero; finite root and absolute error ≤ `1e-12` | `certified` |
| `regularized_norm.json` | Rounded squares/additions, then root of regularized energy; positive-floor error propagation | `certified` |
| `normalized_residual.json` | Rounded variance/noise sum and root, then division; carries all incoming errors | `certified` |
| `fused_norm.json` | Explicit FMAs before square root; each primitive retains its rounding contract | `certified` |
| `nested_root.json` | Nested roots over `[0,16]`; zero-inclusive propagation, retained `1e-6` requirement | `certified` |
| `standard_deviation_tight.json` | Unchanged standard-deviation computation/domain with a `2^-60` requirement | `budget_not_met` |

The nested-root allowance is about `2.11e-8`; this is a coarse uniform bound near
zero. The tight variance request checks an allowance above its budget, rather
than proving an attained numerical failure. Negative variance is a separate
unresolved-domain control, never a successful certificate for exception-raising code.

Run and cold-replay the maintained family:

```sh
python3 scripts/benchmark_numerics.py \
  --case sqrt_standard_deviation --case sqrt_regularized_norm \
  --case sqrt_normalized_residual --case sqrt_fused_norm --case sqrt_nested_root \
  --case sqrt_standard_deviation_tight --replay \
  --out .cache/numerics-generated/sqrt-family
```

These paths are provider regression outputs. Application destinations follow
the skill's confirmed verification directory. Runtime/libm fidelity to the
selected correctly rounded primitive remains a declared trust boundary.
