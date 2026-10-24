# Explicit FMA kernels

These requests preserve each explicit `math.fma` rounding site and an independent
exact specification. Use CPython 3.13/3.14 and the `lean-flare` producer.
See the [profile and trust boundaries](../../../docs/explicit-fma.md).

| Request | Property | Expected result |
| --- | --- | --- |
| `calibrate.json` | Affine sensor calibration over readings, gains and offsets | `certified` |
| `residual.json` | Cancellation-sensitive `x*x-1` near one, absolute error ≤ `10⁻²³` | `certified` |
| `fused_dot3.json` | Three accumulated products; independent exact sum and incoming error propagation | `certified` |
| `regularized_gain.json` | Fused positive denominator followed by division | `certified` |
| `reciprocal_calibrate.json` | FMA after a rounded reciprocal; preserves its input error | `certified` |
| `separate_residual.json` | Separate `x*x-1` schedule, unchanged domain and `10⁻²³` budget | `budget_not_met` |

`budget_not_met` has a checked allowance above the request's limit. It is distinct
from a counterexample and from rejection of an invalid proof.

Run and cold-replay the family from the repository root:

```sh
python3 scripts/benchmark_numerics.py \
  --case fma_calibrate --case fma_residual --case fma_regularized_gain \
  --case fma_fused_dot3 --case fma_reciprocal_calibrate \
  --case fma_separate_residual --replay \
  --out .cache/numerics-generated/fma-family
```

The generated summary records each checked bound, budget outcome, stage time,
proof bytes and cold replay. These paths are ignored provider-regression outputs.
Application destinations follow the skill's confirmed verification directory.
