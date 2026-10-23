# Scientific collection examples

One shared source/model/Lean route covers selected NumPy and Julia arrays.
All ranges, units and budgets are conditional demonstrations. Review the
[skill profile](../../../skills/verify-numerics/references/scientific-arrays.md)
for the source/runtime trust boundaries and excluded library paths.

| Request | Source/API | Guarantee |
| --- | --- | --- |
| `calibration_python.json` | NumPy eager elementwise multiply/add, two channels | Typed shapes, source execution, independent gain/offset reference, finite accurate output |
| `calibration8.json` | Same original function, eight channels | Larger collection/tuple/root and cold replay using the same machinery |
| `calibration_julia.json` | Typed vector API, local helper and `1:length` loop | Original one-based accesses, fresh output, numerical root and actual Julia diagnostics |
| `dense_update.json` | NumPy helpers with nested product loops, transpose, elementwise operations and outer product | State prediction, full dense covariance propagation and correction; two state values and all four covariance entries |
| `calibration_rust.json` | Julia calibration plus `rust/calibration.rs` | Actual reusable fixed-array API and real loop; freshly extracted return in the same Lean root |

## Dense update

The independent exact reference is:

```text
predicted = transition @ state
prior = transition @ covariance @ transition.T + process
observation = [1, 1/2]
projected = prior @ observation
row_projection = prior.T @ observation
innovation = observation @ projected + noise
gain = projected / innovation
residual = measurement - observation @ predicted
return predicted + gain*residual, prior - outer(gain, row_projection)
```

The source implements this update with explicit operation schedules. Matrix
products in the exact reference use Mathlib; native source products retain their
initial positive zero and ascending multiply/add loops. The covariance correction
uses `H P`, independently of `P Hᵀ`, so the arithmetic theorem needs no hidden
symmetry assumption. The demo domains keep the native and exact innovation
positive. Every intermediate's error carries forward; there is no reset at a
helper boundary. This is a single-call accuracy contract, not a positivity,
conditioning or physical-filter correctness theorem. Larger four-state exported
graphs remain separate analysis probes.

## Reproduce

After obtaining the pinned NumPy/runtime tools and building the provider:

```sh
python3 scripts/benchmark_numerics.py --case numpy_calibration \
  --case numpy_dense_update --replay \
  --out .cache/numerics-generated/new-scientific
python3 scripts/benchmark_numerics.py --suite scale \
  --case numpy_calibration8 --replay \
  --out .cache/numerics-generated/new-scientific-scale
python3 scripts/benchmark_numerics.py --case julia_vector_calibration \
  --case scientific_calibration_rust --replay \
  --tools /absolute/path/to/local-tools.json \
  --out .cache/numerics-generated/new-scientific-rust
```

These are provider regression paths; application artifacts follow confirmed
verification/Rust destinations. Optional local selectors supply Julia and
Charon/Aeneas. The retained Rust source remains reusable; extraction wrappers and
proof unrolling do not replace its production loop.

The core `Collection` definitions and generated source/exact bridges are checked
in Lean. NumPy/Julia internals and compilation remain trusted. Actual-source
word diagnostics are samples. Replay needs neither application runtime nor
extractor; Rust replay still needs the recorded compiled Aeneas model.
