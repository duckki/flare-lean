# Four-state planar tracker and reusable Rust delivery

Two scalar FilterPy `GHFilter` instances track `(x, vx, y, vy)`. This is a
multi-module composition example with initialization, prediction, correction,
validation and a caller-visible threshold decision. It is not a full covariance
Kalman filter. The original scalar API and the added application have separate,
explicit specifications.

## What Lean checks

One root, `Workflow.Certificate.certificate`, combines:

- The original scalar constructor and update, all nine fields and both optional
  gain overrides, with the freshly extracted reusable Rust implementation.
- Two uses of the independently certified eight-update numerical component.
  Every final position/velocity is finite and has absolute arithmetic error at
  most `2^-30` m or m/s relative to the original-input exact recurrence.
- The real Rust slice loop, input admission and every error exit. Size precedes
  threshold, initialization and measurement checks. A rejected update leaves
  the original state unchanged in the extracted model.
- The separately rounded horizontal threshold comparison: `Below` and `Above`
  imply strict ordering of the exact reference. `Uncertain` confines that
  reference to `2^-28 + 2^-29` m from the threshold, including padding endpoints.

The application accepts exactly eight paired measurements. Positions and
measurements are finite in `[-10,10]` m, velocities in `[-2,2]` m/s and the
threshold in `[-20,20]` m. The numerical contract fixes `dt=1/8` second,
`g=1/2`, `h=1/8` and default update gains. The raw API correspondence also
covers explicit overrides; it does not extend the numerical guarantee to them.
The source API's finite nonzero divisor premise is satisfied throughout the
application because the stored `dt` remains `1/8`.

## Run and replay

Configure `rust_tools` as described in the skill's
[Rust application guide](../../../skills/verify-numerics/references/rust-applications.md).
`request.json` is the complete reviewed input. `axis.json` selects the original
scalar method; its exact reference and numerical limits are independent inputs.
Use new output directories beneath your agreed verification directory.

```sh
python3 "$FLARE_ROOT/scripts/certify_numerics.py" plan --request "$REQUEST"
python3 "$FLARE_ROOT/scripts/certify_numerics.py" run --request "$REQUEST" --out "$RUN"
python3 "$FLARE_ROOT/scripts/certify_numerics.py" audit --run "$RUN" --frozen
python3 "$FLARE_ROOT/scripts/certify_numerics.py" replay --run "$RUN" \
  --out "$REPLAY" --aeneas-lean-lib "$AENEAS_LEAN_LIB"
```

The run's `report.md` lists properties, scope, paths, trust boundaries and replay
commands. Transfer the whole frozen run, including `result.json`. Its `rust/`
is a standalone dependency-free crate with the real public API and loop;
`drivers/` holds optional verification diagnostics separately. Fresh replay
needs Lean, FLARE/Mathlib and the recorded compiled Aeneas model, but no
translator, Rust compiler, Python/NumPy runtime, bound producer or LLM.

To compare the exact selected original Python bodies against Rust, set optional
`rust_application.source_api.runtime` to a Python executable with NumPy. The
provider checks 128 constructors and 1,024 updates in debug and release,
comparing every field's binary64 word. These sampled diagnostics supplement
Lean's full-state correspondence proof. Rust unit tests also cover all decisions,
guard precedence, exceptional inputs and rejection without state mutation.

## Maintenance

Set optional `contract_cache` to an explicit shared proof cache. Compiled helper
keys include their entire local import closure and model/library identities.
The application root and independent root audit always compile afresh; replay
never reads this cache. Changed application modules invalidate affected helpers
while unchanged numerical component modules remain reusable. Components are
still freshly certified before being imported; reuse is not a claim that every
stage is skipped.

The maintenance regression increases padding from `2^-28` to `2^-27` in both
actual Rust and its reviewed model/contract, freshly extracts the changed crate
and checks the new root while reusing the unchanged axis proofs. A compatible
Rust runtime upgrade can be selected with `rust_runtime` (an explicit release);
extraction remains independently pinned. Runtime upgrade tests do not prove
compiler correctness.

## Source and trust

`source/gh_filter.py` is the unchanged FilterPy file at revision
`3b51149ebcff0401ff1e10bf08ffca7b6bbc4a33`; see `LICENSE-FilterPy` and the
[extraction manifest](../../../docs/extraction-manifest.json). The Rust scalar
port preserves that selected constructor/update; the planar composition is new.
The Python frontend is an explicit source-model trust boundary: ordinary fields,
built-in floats, the selected original bodies and nonzero finite divisors.
The constructor's NumPy `ndim` scalar branch is selected; array execution,
custom dispatch and unrelated module initialization are outside this profile.
Charon/Aeneas, their binary64 model, the Rust compiler and hardware retain the
trust boundaries stated in the report. Arithmetic certification excludes
physical sensor/model uncertainty.
