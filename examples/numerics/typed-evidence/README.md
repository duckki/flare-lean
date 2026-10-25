# Typed product evidence

These requests use the original separately rounded binary64 products on finite
inputs in `[-1,1]`. The independent exact references and budgets are unchanged
between the baseline and typed-evidence comparison.

| Request | Checked result | Added capability |
| --- | --- | --- |
| `power32.json` | Degree-32 repeated square, error below `1e-13` | Compact local summaries beyond polynomial degree 16 |
| `power256.json` | Degree-256 repeated square, error below `1e-13` | Shared values stay shared; no expanded polynomial proof |
| `power4096.json` | Degree-4096 repeated square, error below `1e-12` | Scale case with 12 shared product operations |
| `tiny_constants.json` | Separately rounded tiny constant products | Outward summary rounding bounds rational evidence size |
| `power32_gappa.json` | Optional real Gappa candidate with the typed checker | Producer selection stays independent of checking |
| `zero_product.json` | Error exactly zero | Native multiplication by zero adds no rounding allowance |
| `zero_energy.json` | Error exactly zero after an intermediate rounded square | Earlier operations still require finite execution |

The zero requests use a positive engineering budget of `2^-1100`; the accepted
allowance is zero. Their proof reuses FLARE's existing exact native zero semantics.
The rule preserves incoming ideal-operand error, even when a native operand is
zero. It does not erase earlier errors by resetting the exact reference.

```sh
python3 scripts/benchmark_numerics.py --replay \
  --case typed_power32 --case typed_power256 \
  --case typed_zero_product --case typed_zero_energy \
  --out .cache/numerics-generated/typed-products
```

The admitted typed profile has at most 32 product/constant nodes and 4,096-bit
rational annotations. Summary proposals round outward with an exponent floor
of `-1200`, avoiding exponentially growing denominators for tiny constant chains. Other arithmetic
continues through the existing inference routes. See the
[integration evaluation](../../../docs/evaluation/numerical-integrations.md) for
measurements, rejected tool routes and rejection controls.

The larger product chain is in the scale suite:

```sh
python3 scripts/benchmark_numerics.py --suite scale --replay \
  --case typed_power4096 --out .cache/numerics-generated/typed-product-scale
```

With the pinned Gappa installation selected:

```sh
python3 scripts/benchmark_numerics.py --replay --case typed_power32_gappa \
  --tools /absolute/path/to/local-tools.json \
  --out .cache/numerics-generated/typed-gappa
```
