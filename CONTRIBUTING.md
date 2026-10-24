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
- `Flare/FloatFormat/`: shared binary32/binary64 format, packing and rounding inference.
- `Flare/Binary32/`: model-backed binary32 storage conversions and mixed-storage bounds.
- `Flare/Binary64/`: native scalar semantics, rounding, and error bounds.
- `Flare/Matrix/`: matrix error and correctness theorems, storage relations,
  and the algorithms those theorems analyze.

Use content-specific module names and matching `Flare` namespaces. Shared type
methods may use their type's namespace. Add each library module to `Flare.lean`;
use direct module imports within the library. Keep one Lake package and one
`lean_lib`. See [the organization guide](docs/organization.md) for import boundaries.
Use `module`, `public import` for re-exports, and `@[expose] public section`
for the existing public API and unfoldable definitions. Keep private helper
specification rules local with `@[local spec]`.

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
   material, preserve attribution and update the [source manifest](docs/extraction-manifest.json).

AI generation does not establish novelty or upstream suitability. Lean checks
the proof of the stated proposition; human review must still assess that
proposition and its definitions.

## Results discovered during verification

After completing an engineer's verification task, the
[verify-numerics contribution workflow](skills/verify-numerics/references/contributing-results.md)
can propose newly proved reusable helpers. It checks existing FLARE and pinned
Mathlib declarations, searches only FLARE PRs for overlap, prepares and validates
a focused diff, and asks the user once before publishing a PR to FLARE.
Application certificates stay with the application; the contribution should
provide a useful library interface for later tasks.

## Validation and tooling

Follow the [development guide](docs/development.md) for prerequisites, builds,
shared caching, formatting, linters, proof audits and numerical workflow tests.
Include relevant check results and any changed assumptions in the review.
Prepare a bounded, reviewable change; commit only when requested, then stop for
review unless continuing was explicitly authorized.
