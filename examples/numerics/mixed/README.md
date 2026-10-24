# Mixed storage applications

These original Python kernels store selected intermediates as binary32, promote
exactly to binary64 and continue the original computation. Independent references
use the original inputs; storage never resets accumulated error.

| Request | Scope | Expected result |
| --- | --- | --- |
| `stored.json` | Binary32 quantization over `[-2,2]` | `certified` |
| `calibrate.json` | Stored sensor input, binary64 gain/offset, stored output | `certified` |
| `normalized_residual.json` | Stored measurement, residual and positive-scale division, stored result | `certified` |
| `storage_chain.json` | Scalar helper called three times, storage boundaries, two independent outputs | `certified` |
| `calibrate_tight.json` | Same calibration/domain, unchanged `1e-12` requirement | `budget_not_met` |

A checked allowance above budget is not a counterexample. The profile uses
CPython 3.13/3.14 and NumPy 2.4.0, whose runtime correspondence remains explicit.
It does not admit binary32 arithmetic or arbitrary mixed dtype promotions.

```sh
python3 scripts/benchmark_numerics.py \
  --case mixed_stored --case mixed_calibrate --case mixed_normalized_residual \
  --case mixed_storage_chain --case mixed_calibrate_tight --replay \
  --out .cache/numerics-generated/mixed-family
```

Application destinations follow the skill's confirmed verification directory.
See the [profile guide](../../../docs/arithmetic/mixed-precision.md) for exact scope and trust
boundaries, shared inference, model-backed conversions and rejection controls.
