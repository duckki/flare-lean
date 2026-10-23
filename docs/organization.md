# Proved results and organization

FLARE is a proof library. Its main interface consists of definitions and
theorems that other Lean developments can import and compose. It uses one
Lake project, one `Flare` library, and subject-specific module trees.
Dependency boundaries keep mathematical results reusable and distinguish
native operations from their real interpretations.

## What is proved

| Area | Representative results |
| --- | --- |
| Binary64 | Packing, bounded integer conversion, addition, subtraction, multiplication, division, nearest-rounding bounds, comparisons, signed-zero congruence, exact ±1 multiplication, and positive square-root squared residuals |
| Dense matrices | Finite storage, multiplication accuracy, LDLᵀ factorization, successful positive-definite solves, substitution and residual bounds, and two-state rounded Gram word symmetry |
| Spectral algorithms | Jacobi convergence and spectral error, approximate PSD-check acceptance, and truncated pseudoinverse accuracy |
| Real analysis | Schur complements, conditioning, matrix norms, Gram residual transport, spectral gaps, pseudoinverse perturbation, entrywise propagation and positivity margins, error recurrences, and Householder Gram preservation |

These are theorems about specific operations **under explicit hypotheses**.
Scalar arithmetic includes overflow-domain bounds. Matrix results retain the
proved numerical profiles: for example, at most 32 terms for the dense product
bounds, at most 12 rows for the main solve/pseudoinverse results, and at most 18
rows for Jacobi success. The theorem statements give the complete assumptions.

Concrete algorithm definitions are included where theorems analyze them. They
identify the exact operations and arithmetic order covered by a guarantee.

NaNs and infinities have no real interpretation; both signed zeros mean real
zero. Some proof helpers totalize exceptional or missing values to zero, with
finiteness and representation premises stated separately. The numerical kernels
use native `Float`; they do not execute rational arithmetic or `Float.Model`.

See the [theorem guide](reference.md) for declarations and their precise
assumptions, and [using the library](using-library.md) for client setup. The
agent workflow can apply supported contracts to application code; this summary
does not imply automatic admission of arbitrary matrix or library calls.

## Repository layout

```text
flare-lean/
├── Flare.lean                   # Public import of the whole library
├── Flare/
│   ├── Analysis/                # Real and discrete mathematics
│   ├── Binary64/                # Native Float semantics and scalar bounds
│   │   └── Model/               # Exact model interpretations and proofs
│   └── Matrix/                  # Matrix correctness and its algorithm definitions
├── Tests/
│   ├── ProofAudit.lean          # Public and private theorem axiom audit
│   └── PublicAPI.lean           # Client import and exported-definition checks
├── Lint.lean                    # Lake lint executable, outside the library
├── docs/
│   ├── development.md           # Building, checking and changing FLARE
│   ├── using-library.md         # Importing FLARE from another Lean project
│   ├── organization.md          # Results, layout and source attribution
│   ├── numerical-verification.md # Workflow contracts and CLI
│   ├── tool-integration.md      # Adapter interfaces, evidence and validation
│   ├── roadmap.md               # Planned capabilities and completion criteria
│   ├── reference.md             # Theorem entry points and assumptions
│   ├── upstream/
│   │   └── mathlib.md           # Pure-mathematics contribution preparation
│   └── extraction-manifest.json # Source revisions, file hashes and extraction notes
├── scripts/
│   ├── certify_numerics.py      # Provider CLI for original-input Lean certificates
│   ├── numerics/               # Source adapters, proposals, Lean/Rust emission
│   ├── benchmark_numerics.py    # Maintained scenario runner
│   ├── check_layout.py          # Import and export boundary checks
│   ├── lint.py                  # Style, import-closure, and Lean lint driver
│   ├── fmt.py                   # leanfmt at width 100, with optional Git base
│   └── test_tooling.py          # Lint/format coverage regression tests
├── .github/workflows/ci.yml     # Build, audit, lint, and formatting checks
├── skills/verify-numerics/      # One authoritative engineer-facing agent skill
├── examples/numerics/           # Source kernels and request fixtures
├── benchmarks/numerics/         # Scenarios and external proof fixtures
├── tools/numerics/              # Optional extraction-tool revision records
├── .cache/numerics-generated/   # Provider regressions, local config and legacy tools
├── Makefile
├── CONTRIBUTING.md
├── AGENTS.md
├── README.md
├── lakefile.toml
├── lake-manifest.json
└── lean-toolchain
```

## Design model: Mathlib

[Mathlib](https://github.com/leanprover-community/mathlib4) is the primary
reference for FLARE's organization and use as a proof library. Its source
tree groups theories by subject and provides an umbrella import, supporting
tools, tests, and documentation generated from declarations.

FLARE applies that model to its focused numerical domain:

| Design principle | Application to FLARE |
| --- | --- |
| Organize theories by subject | `Analysis`, `Binary64`, and `Matrix`, with content-specific filenames |
| Make definitions and theorem statements the public interface | Prefer clear hypotheses and results that compose with existing declarations |
| Reuse established mathematical infrastructure | Use Mathlib definitions and lemmas before introducing local alternatives |
| Keep imports focused and layered | Pure mathematics remains independent of native binary64 and matrix algorithms |
| Make results discoverable | Maintain `Flare.lean`, module documentation, a theorem guide, and declaration docs |

Use Mathlib's [naming](https://leanprover-community.github.io/contribute/naming.html)
and [style](https://leanprover-community.github.io/contribute/style.html)
guidance where applicable, alongside FLARE's module and namespace rules.
The analogy concerns library design; it does not assert that every FLARE
result is general enough or otherwise suitable for inclusion in Mathlib.

Concrete algorithms belong in the library when a theorem analyzes them.
Their definitions fix the operation schedule covered by the proof. Reusability
does not require changing those definitions or weakening their assumptions:
review any mathematical generalization or implementation change separately.

The existing three module trees serve this proof-library organization. Keep
one package and one library, with potential upstream contributions recorded
separately from the source layout.

## Application verification tooling

The [numerical workflow](numerical-verification.md) adds an engineer-facing skill
and provider CLI beside the proof library. Python handles source admission,
tool invocation and artifact retention; Lean checks numerical obligations and
one root theorem. `Flare.Binary64.Pipeline` supplies reusable native/ideal
contracts without importing application or extraction-tool code.

Keep source adapters, proposal producers and optional Charon/Aeneas extraction
under `scripts/numerics`. Generated application models and proofs belong under
the verification directory confirmed with the user; application scratch goes in
that directory's `.cache/`. Confirm a separate destination for a requested Rust
delivery. Preserve its reusable API, state and loops, with a separate driver
function for a bounded repeated-call certificate.

FLARE's provider regression runs and local configuration use ignored
`.cache/numerics-generated/`. Existing local tools may remain there; new shared
tool downloads use a versioned user cache outside the checkout.
`tools/numerics/` contains only maintained revision records. External tool
results are untrusted candidates until reconstructed in Lean. Their installation
does not add a core Lake dependency.
Provider adapter modules expose shared [tool integration](tool-integration.md):
setup recipes, capabilities, execution, evidence and Lean validation. External
producer output remains untrusted until the numerical conclusion is checked.
`skills/verify-numerics` is the sole skill source. Standard GitHub/skills CLI
installers distribute that folder; the agent obtains the full provider
separately. The development installer links the local skill into an agent
directory for editing.

Maintained scenarios and source fixtures belong in `benchmarks/numerics` and
`examples/numerics`. They exercise current capabilities and known gaps; they do
not import an application's paper, session logs or historical roadmap.

## Dependency rules

The table lists allowed internal imports, including imports within the same
tree. Lean's `Init`/`Std` and Mathlib are the supported external import roots.

| Module tree | Allowed FLARE dependencies |
| --- | --- |
| `Flare.Analysis` | Analysis |
| `Flare.Binary64` (including Model) | Analysis, Binary64 |
| `Flare.Matrix` | Analysis, Binary64, Matrix |

Library modules import specific modules directly. `Flare.lean` imports all
library modules and is used by clients and the proof audit. Internal modules
must not import this public entry point. There are no per-directory import
aggregators.

Every library file uses Lean's `module` system. `public import` preserves the
existing re-exports, and `@[expose] public section` preserves the public names
and definition bodies that clients can unfold. Private helpers stay private;
specification rules for private helpers use `@[local spec]` so their attributes
do not leak into importing modules. A public theorem's statement may only refer
to public declarations.

`Tests/PublicAPI.lean` checks that a module-system client can import `Flare`,
access representative results, and unfold exported definitions. The proof audit
uses `import all` for every library module to load private proof data. The layout
check enforces complete audit coverage, and the audit rejects an empty private audit.

Matrix loop proofs use Lean 4.35's `vcgen` with explicit invariants. The
`Specification` module proves exact bridges from existing `Std.Do` contracts to
`Std.WP`, preserving both successful and exceptional postconditions. This lets
proof implementations migrate while existing theorem statements remain usable.
The tactic's experimental flag is enabled only in modules that use it.

Within `Matrix`, the runtime consists of `Error`, `Dense`, and `Operations`.
These modules may import one another and `Init`/`Std`; they must stay independent
of Mathlib, ghost values, and reasoning modules. `Value`, `Storage`, and
`OperationStorage` connect native arrays to mathematics. The other modules
establish numerical correctness. This is an import boundary within one library;
the Lake package itself depends on Mathlib.

`scripts/check_layout.py` enforces the allowed trees and import roots, runtime
isolation, and complete public entry-point coverage.

The `Lint.lean` executable delegates to `scripts/lint.py`; it adds no public
library. `lake lint` includes the proof audit and a Lean-derived dependency check
covering all repository Lean files. Normal and extra Lean linters run as part of
the incremental Lake build; only the audit is elaborated separately. `make check`
adds formatting and tooling regression checks. See
[the development guide](development.md) for details.

## Separating future contributions

Pure mathematical candidates stay in `Analysis`, where they can be assessed
without native Float dependencies. The [Mathlib guide](upstream/mathlib.md)
records candidate areas and how to turn a result into an upstream change.

Native scalar and matrix results stay in `Binary64` and `Matrix`. Add another
contribution destination when a concrete result fits that project's definitions
and scope. A shared subject area alone does not justify a contribution plan
or a reserved module tree.

Keep contribution status and upstream links in the destination guide. Move an
accepted result to an upstream import once the pinned dependency contains it,
retaining a compatibility lemma only when needed by clients.

## Documentation and generated files

Module documentation describes the current API. Durable source attribution
lives in the [source manifest](extraction-manifest.json) and the attribution
section below. Session handoffs, extraction logs, and application roadmaps are
not library documentation.

For generated documentation, use `doc-gen4` for declarations and `importGraph`
with Graphviz `dot` for module dependencies. Put the final site under
`docs-generated/doc-gen/` and the graph at `docs-generated/module-graph.svg`.
Keep tooling and intermediates under `docs-generated/.lake/` and
`docs-generated/.cache/`. The whole generated directory is ignored.

## Source attribution

The [extraction manifest](extraction-manifest.json) records source revisions,
original file SHA-256 hashes, destination paths and adaptation notes. FLARE is an
independent Lake package; no source-project checkout is needed to build or use it.

| Source | Recorded revision | Reused material |
| --- | --- | --- |
| `formal-demo` | `af1dd951770ee7d5b222331c31e0f3e885005681` | Initial scalar, matrix and analysis theorem collection |
| `kalman-filter` | `b5077c258988627ca81a02b0767b0a814ee1c8e9` | Entrywise propagation, positivity margins, residuals, error recurrences, Householder preservation, sign/sqrt bounds and two-state Gram symmetry |
| `kalman-filter-lean`, branch `paper` | `4d5330e176a6bf7059013b5689d7de9b07507ae4`, plus the file hashes recorded in the manifest | Numerical skill, adapters, graph/producer/emitters, pipeline contracts, tests, requests and frozen Gappa reconstruction inputs |
| Same `kalman-filter-lean` snapshot | Same revision and per-file hashes | Scalar Kalman/IMU helpers, unchanged Rust admission challenge and compressed four-state graph probes |

The workflow snapshot included uncommitted assets: its commit alone does not
identify the imported bytes. The manifest hashes identify the original sources,
not current FLARE files. Repeated destination paths mean that a module combines
material from multiple originals. The manifest's top-level toolchain fields
record the initial extraction environment; current build pins live in
`lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.

Extraction retained theorem assumptions, constants and native arithmetic order,
while adapting namespaces, imports and numerical error types. The pipeline
contracts reuse FLARE's existing arithmetic results; moving them establishes no
stronger bound. Fixed-horizon Python loop wrappers and independent recurrences
are explicit benchmark adaptations. The unchanged Rust source and large graphs
remain capability probes. Gappa's Coq proof is reconstruction material, not an
accepted Lean theorem.

The Kalman workflow source and FLARE use GPL-3.0. Application implementations,
paper reports and historical success claims are excluded from the library's
proof evidence. Source projects are neither modified nor required by this
extraction; application-specific bridges remain in their own projects. Preserve
attribution, update destinations when modules move, and add source records when
importing more results. Origin records establish neither mathematical novelty
nor upstream acceptance.
