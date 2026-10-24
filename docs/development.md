# Development guide

Install [Elan](https://github.com/leanprover/elan), Python 3.10 or newer, and Make.
Elan selects the Lean version from `lean-toolchain`. Lean and Mathlib are pinned
to **v4.35.0**; `lake-manifest.json` records transitive dependency revisions.
For agent-led application verification, start with the [user guide](../README.md):
the skill obtains missing tools as needed. This guide is for building and changing
FLARE itself.

## Build and check

From the FLARE checkout, build and run all required checks:

```sh
lake build Flare
make check
```

This builds the library, checks public and private theorem axioms, checks import
boundaries and coverage, runs the linters and their regression tests, and checks
formatting. Include the check results and any changed assumptions or runtime
behavior in the review.

### Shared build cache

Optionally, enable Lake's shared artifact pool before building on supported
toolchains, including Lean 4.35:

```sh
export LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
export MATHLIB_NO_CACHE_ON_UPDATE=1
```

Leave `LAKE_CACHE_DIR` unset to use the toolchain-specific pool. Bootstrap missing
Mathlib artifacts only when needed with
`lake exe cache get 'Flare.*' Tests/ProofAudit.lean Tests/PublicAPI.lean Lint.lean`,
then build with the cache variables above to register visited artifacts. Do not
repeat archive extraction in every worktree. Restored files can be hard links;
directory sizes alone do not establish duplicate storage.

CI uses a scoped cache download on its fresh runner instead of fetching all of Mathlib or
restoring a whole `.lake` cache. Select `Flare.*`, not just `Flare.lean`: Mathlib's
cache reader does not follow imports between downstream modules. FLARE's own
sources are built locally; cache misses for these downstream roots are expected.

### Formatting

[leanfmt](https://github.com/duckki/leanfmt/tree/v0.4.6) is pinned to **v0.4.6**.
Use a **100-column** width, matching Mathlib's line-length convention:

```sh
make fmt                  # Format all Lean sources, including untracked files
make fmt-check            # Check formatting without rewriting
```

Build the library before the first formatting run so the formatter can load
imports for custom syntax. To limit either command to changes against an
existing Git reference, use `python3 scripts/fmt.py --base REF`, with `--check`
for a check. The default checks the whole repository and needs no base branch.

Keep formatting exceptions narrow and explain them in a source comment.
The formatting wrapper restores a file and fails if the formatter changes its
non-whitespace content.

### Program specifications

Use `vcgen` for new verification-condition proofs. Lean 4.35 still marks this tactic
experimental, so modules using it explicitly set `experimental.vcgen` to `true`.
`Flare.Matrix.Specification` proves equivalences between the existing `Std.Do`
specifications and `Std.WP`, including exceptional outcomes. Apply these bridges when
updating an existing proof so its exported statement stays unchanged. Keep native
specification rules for private helpers local with `@[local spec]`.

### Linters

`lake lint` runs:

- Style checks adapted from
  [graphql-lean](https://github.com/duckki/GraphQL.lean/tree/41f1c4a240c30419c4ba0ffcdfeae612ee4d5810):
  100-column Lean code and comments (URLs exempt), 1,500-line Lean files, no tabs
  or trailing whitespace, modern `fun`/`<|` syntax, scoped diagnostic/resource
  options and `open Classical`, and no double underscores in declaration names.
- An incremental Lake build of `Flare` and `Lint.lean`, followed by
  `python3 scripts/check_layout.py` for layering.
- Import coverage using Lean's dependency reader, rooted at `Flare.lean`,
  `Tests/ProofAudit.lean`, `Tests/PublicAPI.lean`, and the lint executable. Nested
  and untracked Lean files are included; orphan files fail the check.
- Lean's normal and extra linters with warnings as errors, configured in
  `lakefile.toml` so they run during elaboration and reuse Lake's build cache.
  The proof audit and public-API client are elaborated separately with the same options;
  library files are not elaborated again after the build. Missing-documentation
  lint is disabled. Experimental Mathlib analyses enabled by `linter.all` are
  outside this check.

`schur_reflexive` retains its extracted `DecidableEq` parameter through a scoped
`unusedDecidableInType` exception. Review any removal of an existing hypothesis
as a separate API change.

For a quick text check, run `python3 scripts/lint.py --style-only`. Run the
tooling regression checks with
`python3 -m unittest discover -s provider/tests -t provider -p 'test_*.py'`.

The standalone commands `lake build`, `lake env lean Tests/ProofAudit.lean`,
and `python3 scripts/check_layout.py` remain available for focused validation.

Prepare a bounded, reviewable change. For agent-assisted work, commit only when
the user asks, then stop for review unless continuing was explicitly authorized.

## Work on the skill locally

For user installation from GitHub, follow the [README](../README.md#optional-installation).
When editing a FLARE checkout, the repository helper can instead link that
checkout's authoritative skill into an agent's skill directory:

```sh
python3 scripts/install_numerics_skill.py
```

It defaults to `$CODEX_HOME/skills` (or `~/.codex/skills`); pass `--dest DIR` for
another location. It preserves a different existing skill. Keep the checkout
available while using this development link. The helper installs neither the
toolchain nor the provider's dependencies.

## Numerical workflow changes

Maintain one skill at `skills/verify-numerics`, the provider CLI/adapters under
`provider/numerics`, stable CLI launchers under `scripts/`, and requests/source
fixtures under `examples/numerics`. Tool pins/setup recipes live in
`provider/manifests`, with hash-identified patches under `provider/patches`.
Python regressions live in `provider/tests/numerics` and `provider/tests/tooling`;
`unittest discover` uses `-t provider` to resolve the checked-out package without
installing it. Keep optional
external tools outside core Lake dependencies. Read
[the workflow guide](numerical-verification.md) for certification boundaries
and [the benchmark guide](../benchmarks/numerics/README.md) for scenarios.
The [tool integration guide](integration/tool-integration.md) describes adapter extension,
shared setup, versioned obligations/evidence and independent validation.

Finish `make check` or `lake build` before starting numerical certification or
replay in the same checkout. Those checks read compiled library artifacts;
rebuilding dependencies concurrently can invalidate their module imports.

Run `make numerics-check` for fresh Lean certification/replay and rejection
controls, and `make numerics-bench` for the default end-to-end scenarios. Use
`make numerics-scale` for increasing bounded-loop and larger-model workloads. CI
runs the smoke suite, a representative scale subset and the two README examples.
The scale subset includes 16/48/128-update Kalman and 16/48-update IMU checks,
plus compact loops and shared caller proofs with retained cold replay evidence;
resource failures are not accepted for the completed helper-composition cases.
It uploads the checked [README evidence](numerical-verification.md#replay-the-readme-examples)
after a fresh replay.
CI also builds the pinned Gappa/FPTaylor producers, checks external families and
retains their maintained benchmark evidence. For local real-producer tests, set
`FLARE_NUMERICS_ANALYSIS_TOOLS=/absolute/path/to/local-tools.json`; the file has
`analysis_tools` entries for both producers, as described in the integration guide.
The optional PRECiSA recipe and real producer tests use Linux; see the skill's
[setup guide](../skills/verify-numerics/references/tool-setup.md#precisa).
Set `FLARE_PRECISA` to its installed launcher for `make numerics-check`, or select
`branch_gate_precisa` / `branch_innovation_precisa` in the benchmark runner.
Default checks include conditional source/proof/rejection controls; real PRECiSA
setup and analyzer checks were exercised separately in an Ubuntu ARM64 VM.
CI also installs CBMC 6.11.0 and tests actual witness search plus Lean checking.
Locally, set `FLARE_CBMC` to the selected executable to enable these real-tool
tests. The [delivery guide](automated-delivery.md) covers its setup recipe and
`scripts/release_numerics.py`, which checks retained Python/NumPy/C++ cases,
counterexamples, portable bundles and change-aware rechecking. Platform evidence
and the independent engineer gate are in the [delivery evaluation](evaluation/delivery-evaluation.md).
Optional runtimes and Rust extraction are selected separately with local tool
paths. To run the fresh
explicit-port equivalence/replay and rejection tests, set
`FLARE_NUMERICS_RUST_TOOLS=/absolute/path/to/local-tools.json` for `make numerics-check`;
the file must contain the `rust_tools` selection described in the skill reference.
Keep provider regression commands, failures and evidence under ignored
`.cache/numerics-generated/`; do not check generated evidence or tool installations
into the library. Application verification uses the skill's confirmed artifact
locations and verification-local scratch; new reusable tool downloads use the
shared user cache. Candidate external bounds must become Lean proofs before acceptance.

For repeated helper/loop benchmarks, pass
`--contract-cache .cache/numerics-generated/contracts` to the benchmark runner.
This optional cache reuses compiled local contracts whose source, imported helper
and library/compiler identities still match. It preserves Lean's `.olean`,
`.olean.private` and `.olean.server` proof-module data. `proof-reuse.json` records
actual reuse; changed/corrupt entries are rebuilt. Replay always compiles saved
sources afresh and uses no compiled contract cache. Application runs select an
explicit `contract_cache` under their agreed verification directory instead.

Pass `--replay` to the benchmark runner to check each saved root again without
producers or compiled helper reuse and record its elapsed cost. The
[scaling guide](integration/scaling.md) gives focused counted-loop, shared-graph and
guard-local commands. Ordinary `make check` runs their fast admission/word tests;
`make numerics-check` additionally runs fresh proofs, replay and rejection controls.

Benchmark summaries record proposal/check times, Lean source bytes/module count,
reused modules and maximum reported check-process resident memory. Warm reuse
and fresh replay have different costs; retain both when comparing scalability.

## Rust application regression checks

With the tools from the skill's [setup guide](../skills/verify-numerics/references/tool-setup.md)
and a local `rust_tools` configuration, run:

```sh
FLARE_NUMERICS_RUST_TOOLS=/absolute/path/to/local-tools.json make numerics-check
python3 scripts/benchmark_numerics.py --suite scale --case imu48_rust_application \
  --tools /absolute/path/to/local-tools.json --out .cache/numerics-generated/new-imu48-run
```

These optional checks exercise fresh application extraction, the authored Lean
contract, all saved proof modules, replay, debug/release diagnostics and rejection
controls. The original crate files and proof templates live under
`examples/numerics/imu48` and `benchmarks/numerics/scale`. Templates use `.lean.txt`
to keep Aeneas outside the core Lake dependency graph; the provider materializes
and compiles them as `.lean` files. Format materialized templates with the pinned
`fmt --line-width 100` and their compiled imports on `LEAN_PATH`, preserve tokens,
then copy formatting back to the templates. `make fmt` handles core Lean files.

## C source regression checks

Install pinned pycparser 3.0 in Python or the shared user cache as described in
[tool setup](../skills/verify-numerics/references/tool-setup.md#c-parser-and-compiler).
CI installs it before `make check`. Clang/GCC and working address/undefined-
behavior sanitizers are required for original-source certification diagnostics;
frozen replay only needs the parser and Lean. Optional Frama-C/WP/Why3 task tools
are separate and are not required by the default suite.

```sh
make numerics-check
python3 scripts/benchmark_numerics.py --replay \
  --case c_mean_update --case c_blend --case c_calibrate --case c_dot2 \
  --out .cache/numerics-generated/new-c-suite
python3 scripts/benchmark_numerics.py --replay --case c_mean_update_rust \
  --tools /absolute/path/to/local-tools.json \
  --out .cache/numerics-generated/new-c-rust
```

The Rust case additionally needs the selected Charon/Aeneas tools/model. Tests
reject unsupported casts/alias escape/loop forms, false references, concrete
region overlap, resealed VCs, weakened roots and a changed Rust port. The actual
C functions run at O0/O2 and with ASan/UBSan. See the [C guide](sources/c-verification.md)
for supported syntax, typed-cell assumptions and optional task export.

## Scientific collection regression checks

Install NumPy 2.4.0 in the compatible Python environment or shared user cache;
see [tool setup](../skills/verify-numerics/references/tool-setup.md#numpy-and-julia-runtimes).
The NumPy route needs Python 3.11+. CI installs the pinned runtime before checks.
The Julia 1.11.7 and retained Rust cases use optional local tool selectors.

```sh
make numerics-check
python3 scripts/benchmark_numerics.py --case numpy_calibration \
  --case numpy_dense_update --replay \
  --out .cache/numerics-generated/new-scientific
python3 scripts/benchmark_numerics.py --suite scale --case numpy_calibration8 \
  --replay --out .cache/numerics-generated/new-scientific-scale
python3 scripts/benchmark_numerics.py --case julia_vector_calibration \
  --case scientific_calibration_rust --replay \
  --tools /absolute/path/to/local-tools.json \
  --out .cache/numerics-generated/new-scientific-rust
```

Tests reject dtype/cast/unsupported broadcast changes, input/view mutation,
invalid indices, altered native schedules, false references, changed runtime
libraries and a weakened shape/execution root. Cold replay disables producers,
NumPy/Julia admission and extraction. Rust source retains its actual API/loop;
only the authored proof expands the two-element iteration. See the
[scientific guide](sources/scientific-arrays.md) for implementation boundaries.

## Shared enclosure regression checks

The pure `Analysis.IntervalExpression` interpreter and checker reuse Mathlib's
interval soundness rules. `make check` audits their axioms and tests the exported
interface; `make numerics-check` exercises correlated powers, positive native
and exact denominator floors, corrupted rules/rewrites/leaf bounds, and frozen
replay. Real Gappa/FPTaylor selections additionally certify the square/quartic
family through the same engine and retain each tool's actual candidate.
See [proof evidence](integration/proof-evidence.md) for the supported vocabulary and commands.

## Explicit FMA regression checks

Use CPython 3.13/3.14 with `math.fma`; CI selects 3.14. The
[explicit-FMA profile](arithmetic/explicit-fma.md) uses the standard library and Lean, with
no additional analyzer. After the library build finishes, run:

```sh
FLARE_NUMERICS_INTEGRATION=1 python3 -m unittest discover -s provider/tests -t provider -p 'test_numerics_fma.py'
python3 scripts/benchmark_numerics.py \
  --case fma_calibrate --case fma_residual --case fma_regularized_gain \
  --case fma_fused_dot3 --case fma_reciprocal_calibrate \
  --case fma_separate_residual --replay \
  --out .cache/numerics-generated/fma-regression
```

The tests distinguish missing runtimes, unsupported models, invalid numerical
proofs and the separate schedule's checked allowance above budget. The public
Lean API tests also compute FMA/separate bit differences, signed zero, subnormal
ties and overflow cancellation in the kernel.

## Square-root regression checks

The [square-root profile](arithmetic/square-root.md) needs CPython 3.13/3.14 and no external
analyzer. After the library build finishes, run:

```sh
FLARE_NUMERICS_INTEGRATION=1 python3 -m unittest discover -s provider/tests -t provider -p 'test_numerics_sqrt.py'
python3 scripts/benchmark_numerics.py \
  --case sqrt_standard_deviation --case sqrt_regularized_norm \
  --case sqrt_normalized_residual --case sqrt_fused_norm --case sqrt_nested_root \
  --case sqrt_standard_deviation_tight --replay \
  --out .cache/numerics-generated/sqrt-regression
```

Controls include negative domains, incompatible function models, corrupt root
endpoints, missing incoming error, wrong native primitives/references, changed
platform/library identities, zero/subnormal domains and producer/runtime-free replay.

## Mixed-storage regression checks

The [mixed-storage profile](arithmetic/mixed-precision.md) uses CPython 3.13/3.14 and NumPy
2.4.0. After the library build finishes, run:

```sh
FLARE_NUMERICS_INTEGRATION=1 python3 -m unittest discover -s provider/tests -t provider -p 'test_numerics_mixed.py'
python3 scripts/benchmark_numerics.py \
  --case mixed_stored --case mixed_calibrate --case mixed_normalized_residual \
  --case mixed_storage_chain --case mixed_calibrate_tight --replay \
  --out .cache/numerics-generated/mixed-regression
```

Controls reject wrong storage/rounding/subnormal models, unpaired casts, hidden
promotions, lost storage allowances, substituted primitives and false references.
Zero/subnormal domains and producer/NumPy-free replay accompany the application
family. Public API tests compute ties, mantissa carry, signed zero and gradual
underflow in the kernel; exact widening is proved for every finite binary32 input.

## Counterexample regression checks

The [scalar witness route](integration/counterexamples.md) uses ordinary source-runtime
admission and no external analyzer. After the library build finishes, run:

```sh
FLARE_NUMERICS_INTEGRATION=1 python3 -m unittest discover -s provider/tests -t provider -p 'test_numerics_witnesses.py'
python3 scripts/benchmark_numerics.py \
  --case covariance_counterexample --case cancellation_counterexample --replay \
  --out .cache/numerics-generated/counterexample-regression
```

Controls reject satisfying/out-of-domain witnesses, false reference values,
changed native outputs, altered requirements, missing roots and extra axioms.
Pair outputs, signed zero and the smallest subnormal have retained cases. Cold
replay must not call witness proposal, source/model execution or producer adapters.
The README evidence generator and CI use this same delivery path for the Kalman
positivity example.


## Automated delivery regression

The [delivery guide](automated-delivery.md) covers matching skill/provider setup,
portable bundles and change-aware rechecking. The maintained public source cases
retain their first attempts and assistance in `benchmarks/numerics/heldout`.
Run `python3 scripts/release_numerics.py --out <new-regression-directory>` after
building the library. CI also installs pinned CBMC and exercises actual witness
search; set `FLARE_CBMC` to a selected 6.11.0 executable for the optional local
search integration test. These external tools remain outside Lake dependencies.
