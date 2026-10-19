# Project layout

FLARE is a proof library. Its main interface consists of definitions and
theorems that other Lean developments can import and compose. It uses one
Lake project, one `Flare` library, and subject-specific module trees.
Dependency boundaries keep mathematical results reusable and distinguish
native operations from their real interpretations.

```text
flare-lean/
├── Flare.lean                   # Public import of the whole library
├── Flare/
│   ├── Analysis/                # Real and discrete mathematics
│   ├── Binary64/                # Native Float semantics and scalar bounds
│   │   └── Model/               # Exact model interpretations and proofs
│   └── Matrix/                  # Matrix correctness and its algorithm definitions
├── Tests/
│   └── ProofAudit.lean          # Public and private theorem axiom audit
├── Lint.lean                    # Lake lint executable, outside the library
├── docs/
│   ├── architecture.md          # Layout and dependency policy
│   ├── reference.md             # Theorem entry points and assumptions
│   ├── upstream/
│   │   └── mathlib.md           # Pure-mathematics contribution preparation
│   ├── provenance.md           # How to read the source record
│   └── extraction-manifest.json # Initial source revision and file hashes
├── scripts/
│   ├── check_layout.py          # Import and export boundary checks
│   ├── lint.py                  # Style, import-closure, and Lean lint driver
│   ├── fmt.py                   # leanfmt at width 100, with optional Git base
│   └── test_tooling.py          # Lint/format coverage regression tests
├── .github/workflows/ci.yml     # Build, audit, lint, and formatting checks
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
[the contribution guide](../CONTRIBUTING.md) for details.

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
lives in the [provenance record](provenance.md). Session handoffs, extraction
logs, and application roadmaps are not library documentation.

For generated documentation, use `doc-gen4` for declarations and `importGraph`
with Graphviz `dot` for module dependencies. Put the final site under
`docs-generated/doc-gen/` and the graph at `docs-generated/module-graph.svg`.
Keep tooling and intermediates under `docs-generated/.lake/` and
`docs-generated/.cache/`. The whole generated directory is ignored.
