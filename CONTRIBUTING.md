# Contributing to FLARE

FLARE welcomes reusable definitions and theorems, including AI-generated
contributions. A contribution should explain the mathematical statement and
its intended use so that a reviewer can assess it independently of the
proof-generation process.

The main contribution is a useful proof interface: clear definitions, suitable
hypotheses, and results that compose with other results. A contribution can
consist entirely of mathematics. Include concrete algorithm definitions when
they are the subject of a correctness or error theorem.

## Where work belongs

- `Flare/Analysis/`: real and discrete mathematics independent of native Float.
- `Flare/Binary64/`: native scalar semantics, rounding, and error bounds.
- `Flare/Matrix/`: matrix error and correctness theorems, storage relations,
  and the algorithms those theorems analyze.

Use content-specific module names and matching `Flare` namespaces. Shared type
methods may use their type's namespace. Add each library module to `Flare.lean`;
use direct module imports within the library. Keep one Lake package and one
`lean_lib`. See [the architecture](docs/architecture.md) for import boundaries.

Potential [Mathlib contributions](docs/upstream/mathlib.md) are tracked
separately from the library's source organization. Add another destination
only after identifying a concrete missing result that fits that project's
definitions and scope. Keep one authoritative implementation of each result
in its subject module.

## What to review

1. **Definitions and statement.** Explain the result, cite external mathematical
   definitions, and identify its intended numerical domain. Search Mathlib for
   existing results before adding a new formulation.
2. **Assumptions.** Make dimensions, finiteness, exceptional values, conditioning,
   and error constants explicit. Preserve existing assumptions when importing
   results; review generalizations and tighter bounds as separate changes.
3. **Connection to the subject.** A theorem should use the library's established
   definitions and compose with related results. For an algorithm theorem,
   identify the written implementation or a proved equivalent decomposition.
   A changed operation order needs a new justification.
4. **Proof dependencies.** No admitted proofs or additional axioms. The audit
   permits only `propext`, `Classical.choice`, and `Quot.sound`.
5. **Documentation.** Describe exported guarantees and their limits. For imported
   material, preserve attribution and update the [source record](docs/provenance.md).

AI generation does not establish novelty or upstream suitability. Lean checks
the proof of the stated proposition; human review must still assess that
proposition and its definitions.

## Validate a change

Use the pinned toolchain and dependency manifest. On a fresh checkout, first
run `lake exe cache get`. Then run from this repository:

```sh
make check
```

This builds the library, checks public and private theorem axioms, checks import
boundaries and coverage, runs the linters and their regression tests, and checks
formatting. Include the check results and any changed assumptions or runtime
behavior in the review.

### Formatting

[leanfmt](https://github.com/duckki/leanfmt/tree/v0.4.5) is pinned to **v0.4.5**.
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
The existing `mvcgen` exceptions use `-- leanfmt: off next`; these were
introduced for v0.4.1 alternative formatting and token-preservation failures. They still
undergo line-length checks and Lean elaboration. The formatting wrapper also
restores a file and fails if the formatter changes its non-whitespace content;
this guards against v0.4.1 dropping unparsed text after an indentation error.

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
  `Tests/ProofAudit.lean`, and the lint executable. Nested and untracked Lean
  files are included; orphan files fail the check.
- Lean's normal and extra linters with warnings as errors, configured in
  `lakefile.toml` so they run during elaboration and reuse Lake's build cache.
  `Tests/ProofAudit.lean` is elaborated once separately with the same options;
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
