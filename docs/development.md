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
`python3 -m unittest discover -s scripts -p 'test_*.py'`.

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
`scripts/`, and requests/source fixtures under `examples/numerics`. Keep optional
external tools outside core Lake dependencies. Read
[the workflow guide](numerical-verification.md) for certification boundaries
and [the benchmark guide](../benchmarks/numerics/README.md) for scenarios.
The [tool integration guide](tool-integration.md) describes adapter extension,
shared setup, versioned obligations/evidence and independent validation.

Run `make numerics-check` for fresh Lean certification/replay and rejection
controls, and `make numerics-bench` for the default end-to-end scenarios. Use
`make numerics-scale` for increasing bounded-loop and larger-model workloads. CI
runs the smoke suite, a representative scale subset and the two README examples.
The scale subset includes 16/48/128-update Kalman and 16/48-update IMU checks;
resource failures are not accepted for the completed helper-composition cases.
It uploads the checked [README evidence](numerical-verification.md#replay-the-readme-examples)
after a fresh replay.
CI also builds the pinned Gappa/FPTaylor producers, checks external families and
retains their maintained benchmark evidence. For local real-producer tests, set
`FLARE_NUMERICS_ANALYSIS_TOOLS=/absolute/path/to/local-tools.json`; the file has
`analysis_tools` entries for both producers, as described in the integration guide.
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

Benchmark summaries record proposal/check times, Lean source bytes/module count,
reused modules and maximum reported check-process resident memory. Warm reuse
and fresh replay have different costs; retain both when comparing scalability.
