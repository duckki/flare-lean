# Closed C examples

These authored C fixtures exercise one reusable source/VC route. Domains and
units are conditional demonstration contracts; review real requirements before
using them in an application. The original functions remain in `updates.c`.

| Request | Original API | Checked behavior |
| --- | --- | --- |
| `mean_update.json` | Scalar function calling `correction` | Original operation order and independent exact update |
| `blend.json` | Two-cell mutable buffer, read-only observations, unsigned loop | Checked access/counter conditions, separation, final cells and heap frame, independent two-output reference |
| `calibrate.json` | Double plus a by-value `Calibration` struct | Flattened original fields, independent gain/offset reference |
| `dot2.json` | Two read-only buffers and scalar accumulator loop | Ordered reduction, unchanged heap; read-only regions may overlap |
| `mean_update_rust.json` | The same C function plus `rust/mean_update.rs` | Actual reusable Rust API/helper, fresh extraction and checked return correspondence |

```sh
python3 scripts/certify_numerics.py run \
  --request examples/numerics/c/blend.json \
  --out .cache/numerics-generated/new-c-blend
python3 scripts/certify_numerics.py replay \
  --run .cache/numerics-generated/new-c-blend \
  --out .cache/numerics-generated/new-c-blend-replay
```

These are provider regression paths. Application artifacts use agreed verification
and Rust destinations. C needs pinned pycparser and a compatible Clang/GCC;
Rust delivery additionally needs the configured Charon/Aeneas tools and Lean model.
The Rust correspondence template is materialized as Lean source by the provider;
it is outside the core Lake dependency graph.

The buffer root assumes live initialized aligned C double objects of adequate
extent, with required writable-region separation. Parsing, typed-cell mapping
and compiler/runtime fidelity remain trusted. The Lean model proves conditional
access/frame behavior; source samples and sanitizers are diagnostics. See the
[C profile](../../../skills/verify-numerics/references/c-source.md) and
[VC evaluation](../../../docs/c-verification.md) for scope and optional foreign
task export. Source ACSL is inspected by WP; JSON numerical budgets are checked
by FLARE and are not automatically ACSL contracts.
