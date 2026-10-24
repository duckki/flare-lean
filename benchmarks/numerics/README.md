# Numerical workflow benchmarks

`scenarios.json` is the maintained scenario list; requests and source kernels
live in `examples/numerics/`. These include reusable fixtures extracted from
Kalman experiments and FLARE's fixed-shape array examples, rather than the
paper or its frozen performance reports.
The [source attribution](../../docs/library/organization.md#source-attribution) identifies their source.

```sh
make numerics-check  # Adapter, installation, producer-gap and fresh Lean controls
make numerics-bench  # Default end-to-end cases, fresh ignored output directory
python3 scripts/benchmark_numerics.py --out /tmp/optional-numerics \
  --include-optional --tools /path/to/local-tools.json
```

Run the scripts from the provider root. Shared Lake caching is optional; see
[the development guide](../../docs/development.md#shared-build-cache). `make numerics-bench` writes to
`.cache/numerics-generated/bench-TIMESTAMP/`. A benchmark output directory must be new. Commands,
streams, accepted allowances, root theorems, failures and elapsed times are saved.
Warm checking time does not measure proof authoring or engineer effort.

CI also certifies and replays the exact [README examples](../../docs/numerical-verification.md#replay-the-readme-examples),
then uploads their sources, proofs and reports as `readme-evidence`.
`filterpy-gh-request.json` is the pinned eight-update request template; the
evidence generator binds `source.py` to the selected original FilterPy file.

| Scenario | Expected result | Scope |
| --- | --- | --- |
| Scalar and idiomatic Kalman | `certified` | Mean and variance, original inputs, independent exact equations |
| Joseph covariance | `certified` | Alternative operation schedule and two outputs |
| IMU prediction | `certified` | Scalar motion kernel, original Float time input |
| Four-stage mean update | `certified` | Residual, gain multiplication, add zero, add prior mean |
| Same mean update, `2^-51` target | `certified` | Reusable scalar inference, three gain intervals and the unchanged target |
| Tiny positive gain denominator | `certified` | Preserve native and exact positive floors with both variances in `[2^-54,2^-53]` |
| Array prediction / calibration / projection | `certified` | Built-in Python lists, checked shapes and original ascending product order, independent exact matrix expressions |
| Mean update through Gappa / FPTaylor | `certified` with optional producers | Lean validates the Gappa query bound or actual FPTaylor candidate |
| Shared square / quartic / regularized reciprocal | `certified` with selected producers | Gappa/FPTaylor share a proved power-aware rational enclosure engine; actual candidate targets and replay |
| Mixed storage / calibration / residual / repeated storage | `certified` with selected NumPy | Binary32 nearest/even narrowing, exact binary64 promotion, incoming storage/computation error; tight budget returns `budget_not_met` |
| Scalar covariance / cancellation witnesses | `counterexample` | Finite admissible input, actual output, independent exact reference and violated positivity/error requirement in one checked root; cold replay |
| ROS positivity search | `counterexample` with selected CBMC | Strict-positivity witness proposed from the original header's scalar graph, checked in Lean and replayed without CBMC |
| Square-root variance / norm / normalized residual / nested root | `certified` with CPython 3.13/3.14 | Correctly rounded primitive contract, checked radicand domains, endpoint proposals and incoming error; tight request returns `budget_not_met` |
| Explicit FMA calibration / residual / dot product / reciprocal composition | `certified` with CPython 3.13/3.14 | One native rounding per FMA, incoming errors and independent exact reference; separate residual keeps its budget and returns `budget_not_met` |
| Scalar conditional innovation / threshold gate | `certified` | All four native/exact flows with independent conditional references |
| Guarded reciprocal | `certified` | Direct input guard, local denominator premise, domain includes zero |
| Counted smoothing loop | `certified` | Original `range(count)` loop; one preserved invariant and independent exact recurrence |
| Threshold gate / innovation through PRECiSA | `certified` / `budget_not_met` with optional producer | Actual maximum stable/unstable candidate proved in Lean |
| Julia / MATLAB-compatible Kalman | `certified` with optional runtime | Same equations; actual Julia or explicitly selected MATLAB/Octave |
| NumPy calibration / dense update | `certified` with pinned NumPy | Eager operations/indexed loops; typed dimensions, fresh outputs, state plus every covariance entry against independent matrix algebra |
| Julia vector calibration | `certified` with optional Julia | Typed helpers, one-based loop and original-runtime diagnostics |
| Julia calibration → fixed-array Rust | `certified` with optional Julia/extraction tools | Actual reusable array API and production loop, extracted return in the typed root |
| C scalar / buffer / struct / read-only reduction | `certified` with pinned parser and Clang/GCC | Original source, access/counter conditions, heap frame, independent numerical references; three compiler modes |
| C mean update → reusable Rust | `certified` with optional extraction tools | Retained production function/helper and checked fresh extracted return |
| Rust mean update | `certified` with rustc | Original Rust source and source/IR diagnostics |
| Python Kalman → Rust IR probe | `certified` with optional extraction tools | Internal straight-line kernel: fresh Charon/Aeneas return plus debug/release diagnostics; not a reusable production port |
| Original Rust → extracted Rust model | `certified` with optional extraction tools | Original source retained, no port substitution |

Optional cases are excluded by default and marked separately in summaries.
CI additionally builds the pinned Gappa/FPTaylor versions and selects
`mean_update_gappa` / `mean_update_fptaylor`. See
[tool integration](../../docs/integration/tool-integration.md) for source setup, configuration,
adapter extension and the distinction between raw output and checked bounds.
CI also retains the [shared power/enclosure families](../../examples/numerics/enclosures/README.md)
through both real tools and replays their frozen proofs.
Explicitly selecting one requires its tools: absence is a failed prerequisite,
not a successful proof rejection. `--case NAME` can select individual scenarios.
A local tools file has `runtimes` keyed by `julia`, `matlab`, `c` or `rust`, each with
`kind` and `executable`; `rust_tools` has `charon`, `aeneas` and `lean_lib`.
`analysis_tools` maps Gappa/FPTaylor/PRECiSA to their executable and optional identity/data selections.
For `ros_angles_positivity_search`, use `search_tools.cbmc.path` with CBMC 6.11.0;
the benchmark runner preserves that witness-proposer selection.
Use absolute paths. This machine configuration is not a version attestation.

### Scientific array scenarios

The [scientific examples](../../examples/numerics/scientific/README.md) retain
NumPy calibration, a two-state dense update and a Julia vector API. The dense
case checks 82 native arithmetic operations and six outputs; the eight-channel
scale case checks 16 operations using the same original calibration function.
It exercises rank/shape, scalar broadcasting, fresh storage, nested helper loops,
transpose and outer product. The source does not use BLAS or NumPy reductions.
Mathlib matrix algebra supplies the independent dense reference.

Select `numpy_calibration` / `numpy_dense_update` with `--replay`, and
`numpy_calibration8` in the scale suite. `julia_vector_calibration` and
`scientific_calibration_rust` use optional runtime/extraction selectors. The Rust
port retains its fixed arrays and indexed loop. All routes share the typed root
and replay checker; NumPy/Julia/compiler implementations remain declared trust
boundaries. See the [profile](../../skills/verify-numerics/references/scientific-arrays.md)
for exact limits. Source/dtype/index/alias/schedule controls and weakened-root,
false-reference and runtime-library identity checks accompany positive roots.

### C source scenarios

Select `c_mean_update`, `c_blend`, `c_calibrate` and `c_dot2` with `--replay`.
Their [source and requests](../../examples/numerics/c/README.md) use one closed
C frontend, generated source conditions and the existing numerical validator.
The buffer roots add successful typed-heap execution and frame behavior under
region validity/separation; read-only regions may overlap. O0/O2/sanitized
original-source word checks are diagnostics. The optional `c_mean_update_rust`
case retains a reusable API/helper and authored extracted-return bridge.

Controls reject casts, alias escape, wrong loop bounds, unsigned wrapping in
floating expressions and out-of-bounds accesses. Lean rejects concrete overlap,
false references and weakened roots; replay rejects resealed source-condition
changes. Compiler admission, numerical producers and Rust extraction are disabled
in replay tests. See the [C guide](../../docs/sources/c-verification.md) for the physical
object/source/compiler boundaries and separate optional WP/Why3 task evaluation.

### Array source scenarios

The requests under `examples/numerics/arrays/` retain actual list indexing,
fresh buffer updates, local helpers and `range(size)` loops. The default suite
covers two-state prediction, a 2×2 calibration product, a three-term dot product
and the one-entry boundary. The scale suite adds a 4×4 matrix-vector prediction.
They use one adapter and typed array-root generator; no per-example numerical
lemma is supplied. See the [array guide](../../skills/verify-numerics/references/arrays.md).

Each root proves its input shape guard, fresh output shape, finite dense
execution with the same native entries and an error allowance against a real
matrix expression. Tests reject aliased rows, input mutation, bad shapes,
indices and native accumulation order. A false real specification fails in
Lean; the independent root checker rejects a resealed weakened statement.
All examples replay without a producer. These cases are separate from the
larger exported covariance/correction graphs, which remain analysis probes.

Fresh Lean tests require the baseline to certify first. Controls then check that:

- a wrong independent specification fails in Lean, not source admission;
- a false zero-error proposal for rounded addition is rejected in Lean;
- a runtime/model diagnostic mismatch prevents certification after a valid proof;
- a checked bound above budget remains `budget_not_met`;
- changed source/proof artifacts and changed authored proofs fail freshness;
- a resealed changed kernel fails comparison with frozen source/specification;
- removing the root and its inline audit still fails the independent root checker;
- an authored proof can certify, while an authored numerical axiom is rejected;
- saved proofs replay with producer/runtime entry points disabled.

Fast tests cover missing runtimes, unsupported source constructs, operation
order, literal words and signed zero, Rust mutation/typing, bounded process
cleanup, artifact retention and non-overwriting skill installation.

## A proved numerical failure

`provider/tests/numerics/test_numerics_counterexamples.py` maintains the README's standalone
naive scalar covariance update. At `p = 1`, `r = 2^-54`, its binary64 posterior
is zero while the exact posterior is `1 / (2^54 + 1) > 0`. The fast test compares
actual Python execution and the admitted model. `make numerics-check` also
checks and replays a Lean refutation with an axiom audit, then rejects a false
output claim. The [witness regressions](../../provider/tests/numerics/test_numerics_witnesses.py)
cover ordinary request/report/replay delivery, attained-error failures, domain
and reference checks, pair outputs, signed zeros/subnormals, runtime mismatch,
missing tools and independently rejected root/axiom tampering. The scenario
runner retains `covariance_counterexample` and `cancellation_counterexample` as
`counterexample` outcomes. See [the guide](../../docs/integration/counterexamples.md).

## Known analysis gaps and external fixtures

The fast compositional producer normalizes centers/radii/ideal magnitudes on a `2^-20`
grid and errors on a `2^-45` grid. It can then refine the ideal magnitude using
native range plus accumulated error; that refined value need not lie on the
coarser grid. Tests retain two limitations of that producer: a simple addition
allowance inflates from `2^-51` to `2^-45`, and `p/(p+r)` is unresolved for both
inputs in `[2^-54,2^-53]` after normalization loses a positive divisor floor.
The default workflow now tries reusable scalar inference for graphs of at most
32 IR nodes when a budget or divisor floor needs refinement. It uses relative
outward enclosures, nearest rounding, polynomial correlations and checked input
subdivision. The addition, tiny-gain and tight mean-update families now have
Lean certificates; large graphs still use the compositional producer.

`gappa/mean-update-tight.g`, its raw Coq trace and wrapper are preserved inputs
for comparison with Lean reconstruction. The reusable Lean route now establishes
the unchanged `2^-51` theorem without trusting that foreign trace.
Foreign checker tools are not required for default local tests. Gappa/FPTaylor
producer adapters retain output and validate the actual candidate conclusion;
their foreign proof traces are not imported. PRECiSA has a scalar/terminal-conditional
adapter; see the [conditional examples](../../examples/numerics/branches/README.md).
Further tools, full matrix/filter applications,
NumPy/BLAS mappings, general control flow and physical coverage need further work.

## Increasing scale

```sh
make numerics-scale
python3 scripts/benchmark_numerics.py --suite scale --case kalman_016 \
  --out /tmp/new-scale-case
```

The maintained scale suite is separate from the small smoke suite. It preserves
scalar helpers from the supplied Kalman worktree, wraps them in fixed-horizon
Python loops, and retains original larger assets as capability probes.

| Family | Sizes | What is measured |
| --- | --- | --- |
| Scalar Kalman loop | 1, 4, 8, 16, 48, 128 updates; 8 operations/update | Both mean and variance, helper calls, incoming state error, independent exact recurrence, Lean proof and budget stages |
| Counted smoothing / decay | 1, 16, 128, 1,024 calls; decay at 1,024 | Constant-size helper/invariant proof, nonzero incoming error, arbitrary-horizon theorem instantiated at the selected count |
| Shared smoothing pipeline | 4, 32, 64 blocks; 64, 512, 1,024 arithmetic operations | Shared function definition, distinct local contracts, caller-change reuse and cold replay |
| IMU motion loop | 1, 4, 16, 48 updates; 8 operations/update | Position and velocity with independent accelerations and shared original Float `dt`, complete-horizon Lean error proof |
| Original Rust IMU application (optional tools) | 48 events, integer time and decisions | Fresh multi-module extraction, complete admission/error behavior, arithmetic and exact-reference decision root; authored proof bundle and Lean-only replay |
| Planar GH tracker (optional tools) | Four states, two eight-update axes | Original scalar API/full-state correspondence, composed numerical allowances, validation and exact-reference decisions; reusable Rust crate |
| Original four-state graphs | 7,758 relative / 7,761 global operations, 46 stages | Frozen initialization, dense covariance propagation and correction-model analysis; candidates only |

Kalman profiles start at variance 1 m², process noise 1/8 m² and measurement
noise 1 m²; the initial mean and every independent measurement are in [-1,1] m.
The requested budgets stay 1e-4 m and 1e-6 m² across the whole family. These are
conditional scale fixtures, not measured sensor guarantees. IMU profiles start
at (0 m, 0.5 m/s), with independent accelerations in [-4,4] m/s² and a shared
original Float `dt` in [1/500,1/200] s. Their budgets are 1e-4 m and 1e-6 m/s.
The unchanged integer-time Rust application is checked through a separate
authored proof bundle, preserving its original slice loop and public API. The two graph fixtures are manual exports, not verified compilers.

Each run retains actual expanded arithmetic/node/input counts, per-stage times,
accepted versus proposed bounds, proposal time, Lean source size/module counts,
maximum reported check-process resident memory, full command records and
JSON/Markdown summaries. Memory is the maximum reported for completed children,
not an aggregate across simultaneously running processes.
The stage timeout is 120 seconds. A timeout is unresolved; any bound not yet
checked stays proposed. `candidate_only` has no Lean theorem and is never a
certification result. Expected admission/analysis gaps must match their stated
reason, rather than passing because of an unrelated parser/setup/proof error.
Warm local times are workload diagnostics, not a solver or agent ranking.
Use `--replay` to record cold saved-proof replay separately from fresh
certification and warm contract reuse. See the [scaling guide](../../docs/integration/scaling.md)
for focused commands, measured workloads and the distinction between lowered
graph size and repeated counted-loop work.

The 16/48-update Kalman cases now certify through helper-contract composition;
their resource-failure allowances have been removed. The 128-update case also
completes its Lean root, with a mean allowance above the original budget and a
variance allowance within budget. This is `budget_not_met`, not an observed
numerical failure. The two-million-heartbeat and 120-second per-stage limits are
unchanged. Shared native/exact helper definitions and local contracts keep
nonlinear trajectory expressions out of individual proof bodies.

Compiled local contracts can be reused explicitly across horizons:

```sh
python3 scripts/benchmark_numerics.py --suite scale \
  --contract-cache .cache/numerics-generated/contracts \
  --out .cache/numerics-generated/scale-composed
```

The first pass compiles the local modules. Later compatible callers reuse their
unchanged prefix contracts; the application root is still checked. Saved-proof
replay ignores this cache and recompiles all saved modules. A fresh replay may
take longer than a warm certification with reused contracts.

The reusable exact-magnitude refinement is checked by `native_ideal_refine`.
Proof generation restricts arithmetic facts and discards consumed bound facts;
these change proof construction, not the source algorithm, domain or requirement.
CI checks a smaller representative subset; the full scale target remains
available for performance and capability regression work.

### Complete Rust application

```sh
python3 scripts/benchmark_numerics.py --suite scale --case imu48_rust_application \
  --tools /path/to/local-tools.json --out .cache/numerics-generated/imu48-checked
FLARE_NUMERICS_RUST_TOOLS=/path/to/local-tools.json make numerics-check
```

The [bundle guide](../../skills/verify-numerics/references/rust-applications.md)
describes the reviewed contract, exact-reference bounds, rejection controls and
required cast patch. The root checks the actual `assess` API and its companion
integer timestamp module. Eight debug/release test cases are runtime diagnostics;
the universal Lean theorem supplies the proof. Frozen replay needs only the
matching Lean/Aeneas model imports, without extraction tools or a Rust compiler.

This scale case is optional because it needs Charon/Aeneas and its compiled Lean
model. Default CI validates its request; configured Rust-tool runs also certify,
replay and run the negative controls. Missing tools cannot satisfy a proof
rejection test. The provider retains those integration runs under
`.cache/numerics-generated/application-tests-*/`.

### Combined application and reusable Rust port

```sh
python3 scripts/benchmark_numerics.py --suite scale --case planar_tracker \
  --tools /path/to/local-tools.json --contract-cache .cache/numerics-generated/contracts \
  --out .cache/numerics-generated/planar-checked
FLARE_NUMERICS_RUST_TOOLS=/path/to/local-tools.json \
  FLARE_NUMERICS_RUST_UPGRADE=1.96.0 make numerics-check
```

See the [planar guide](../../examples/numerics/planar/README.md) for the finite
domains, all four error bounds, scalar API scope and report/replay commands.
The upgrade variable is optional and names an installed compatible Rust release.
The maintenance scenario changes padding in the actual Rust module and reviewed
model/contract, freshly extracts it and reuses unchanged imported axis proofs.
Constructor mismatches and altered imported source models must be rejected.
The tests retain runs under `.cache/numerics-generated/planar-tests-*/`.


## Public application delivery

[Held-out source cases](heldout/README.md) retain original Chemicals, NumPy and
ROS files, contracts, first attempts and needed provider extensions. The
`release_numerics.py` harness checks portable delivery, producer-free replay and
change-aware rechecking in addition to their numerical roots.
