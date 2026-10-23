# Tool integration

FLARE separates source admission, numerical producers, source extractors and
Lean validation. Tool adapters share setup, bounded execution, evidence records,
the application root check and saved-proof replay.

## Available routes

Run `python3 scripts/certify_numerics.py capabilities` for the adapter records,
supported versions, arithmetic constraints and source-setup recipes.
Producer versions and setup sources are maintained in
[`tools/numerics/producers.json`](../tools/numerics/producers.json).

| Adapter | Role | Evidence and validation |
| --- | --- | --- |
| `lean-flare` | Producer | Compositional proposals, automatic scalar refinement or authored proofs; numerical claims checked in Lean |
| `gappa` | Producer | Reconstructs a successful Gappa 1.8.3 query's exact dyadic error conclusion in Lean; retains its Coq trace |
| `fptaylor` | Producer | Parses the pinned `0.9.4+dev` hexadecimal candidate and proves that exact bound in Lean |
| `rust-aeneas` | Extractor | Fresh Rust extraction and its actual return relation under the existing source-model trust boundaries |
| `lean-root` | Validator | Compiles proof modules, independently ascribes the expected root type and audits its transitive axioms |

External candidate conclusions now drive the Lean proof target. The FPTaylor
route must establish its parsed candidate itself; it cannot substitute a looser
engineering budget. The Gappa route reconstructs the exact queried dyadic bound.
Gappa's Coq trace is retained but is not imported or checked as a Coq proof.
Candidates that the reusable argument cannot establish remain unresolved.

Adapters can also emit a Lean proof module through the common validation
interface. This supports reusable translators and Lean inference procedures
without changing orchestration. The emitted accuracy declaration must have the
expected original-input type and its full dependencies pass the same axiom audit.
The current scalar validator is described below. Additional tools are a later
[roadmap milestone](roadmap.md#8-add-further-verification-tools).

## Reusable scalar validation

`scripts/numerics/scalar.py` proposes exact rational enclosures, local rounding
allowances, sparse polynomial rewrites and a bounded input subdivision. Lean
checks these using FLARE's actual binary64 nearest-rounding theorems, Mathlib's
`ring` normalization and `dyadic_interval` tactic. Generated case proofs also
establish that the subdivisions cover the original domain. Python inference and
external analyzers remain outside the proof's trusted assumptions.

The default producer tries this route when its compositional allowance misses a
budget or loses a positive divisor floor, for graphs of at most 32 IR nodes.
The external adapters use it directly to validate their candidate conclusions.
Search is bounded by 256 polynomial terms, degree 16 and 16 input boxes; exhausted search
does not establish a false requirement or permission to weaken a candidate.
Correlations through division currently use compositional bounds and require
positive native and exact denominator floors. Arithmetic magnitudes must be at
most `2^1000`. Exceptional values remain excluded by the finite-input contract.

The unchanged `mean_update_tight.json` now certifies at `2^-51`, with three gain
intervals. `tiny_gain.json` certifies `p/(p+r)` for both inputs in
`[2^-54,2^-53]`; no fixed absolute grid erases the divisor floor. Related input
scales, false zero bounds, incorrect rewrites and producer-free replay are tested.
No application-specific proof is supplied for these families.

## Helper and loop composition

The default `lean-flare` producer recognizes admitted Python helper chains in
two-state fold requests when the helper calls cover the ordered graph. It emits
one native/exact function definition per distinct helper body and a checked local
contract per reached input summary. Each contract takes separate native and exact
operands, their finiteness, ranges and incoming errors. No call resets that error.

The native and exact application models preserve those calls. Replay regenerates
the layout and helper definitions from the frozen source graph before checking
the saved proofs. Source parsing/model generation remains a declared boundary;
regrouping does not change arithmetic order. For a repeated helper, one checked
step identity connects its exact computation to the independent fold recurrence.
The public `foldl_contract` and `foldl_error_bound` rules additionally compose
supplied invariants/error recurrences for a parameterized horizon.

`model-layout.json` identifies call spans and wiring. `validation.json` lists the
standalone function/contract modules compiled before the application proof.
`analysis.json` records each helper's contract identity. An optional request field
`contract_cache` selects an explicit directory for compiled helper reuse; no shared
contract cache is created by default. Use the agreed verification directory's
`.cache/contracts/` for application work. `proof-reuse.json` reports actual reuse.
Cache keys bind exact module text, imported helper text, compiler configuration
and library identities; changed/corrupt entries are rebuilt. Like other Lean
build caches, it reuses previously compiled modules. Saved-proof replay always
recompiles the sources and requires neither this cache nor any numerical producer.

The automatic route currently covers bounded helper chains; arbitrary loop
invariants, mutation and collection operations need additional source/proof
support. Gappa/FPTaylor retain their scalar graph limits. A loose checked bound
remains `budget_not_met`, including the 128-update Kalman mean allowance.

## Select a producer

The request's `backend` remains `lean-flare`, the independent proof-generation
and checking path. Add a `producer` to select an external tool:

```json
{
  "producer": "fptaylor",
  "analysis_tools": {
    "fptaylor": {
      "executable": "/shared/tool-pool/fptaylor/source/fptaylor"
    }
  }
}
```

These fields extend the existing request; the source, domain, specification and
outputs are still required. `analysis_tools` selections optionally include an
executable `sha256` and a `base` directory for tool data/configuration. Otherwise
use `FLARE_GAPPA`, `FLARE_FPTAYLOR` or `PATH`. A missing executable, unsupported
version or changed selected hash has a distinct `failure_kind`.
For FPTaylor data, an explicit `base` takes precedence over `FPTAYLOR_BASE`,
followed by the executable's parent directory.

The common arithmetic model is separate binary64 operations, nearest/even,
gradual subnormals and no FMA or reassociation. An optional `arithmetic` object
must match the full model printed by `capabilities`. Gappa's initial exporter
requires dyadic domain endpoints. Both exporters preserve the ordered admitted
graph and use exact constants; Lean still checks its independent specification.

Run the maintained cases with configured tools:

```sh
python3 scripts/benchmark_numerics.py \
  --case mean_update_gappa --case mean_update_fptaylor \
  --tools /absolute/path/to/local-tools.json \
  --out .cache/numerics-generated/external-producers
```

The local tools file can contain `analysis_tools` alongside the existing
`rust_tools` and `runtimes` selections. These are provider regression paths;
application deliveries use the confirmed verification directory.

## Shared source setup

Reuse a compatible installation first. For a new installation, choose a versioned
user-cache directory and announce it before setup. The output directory must be
new; the setup service preserves existing installations.

```sh
python3 scripts/certify_numerics.py setup --tool gappa \
  --out /shared/tool-pool/gappa-1.8.3
python3 scripts/certify_numerics.py setup --tool fptaylor \
  --out /shared/tool-pool/fptaylor-b5a77cae
```

Setup fetches the adapter's pinned source, checks its revision or archive hash,
runs bounded build commands and saves `installation.json` and command logs.
Gappa needs C++, Flex/Bison, Boost headers and GMP/MPFR development files; its
release builds with the bundled `remake` tool. The FPTaylor
recipe uses its portable interval backend and needs OCaml 4, Num, Make and a C
compiler. Obtain missing prerequisites using the agent's tools and the platform's
documented installation route; preserve existing toolchains.

Use `--make-arg 'NAME=value'` for an explicit Make override, such as an isolated
compiler or Num include directory. Builds inherit the caller's environment;
on macOS an explicit `DEVELOPER_DIR` is preserved. Setup covers the two producer
recipes, while the existing [tool setup instructions](../skills/verify-numerics/references/tool-setup.md)
cover Lean and Charon/Aeneas. No setup action itself establishes a numerical proof.

## Evidence and replay

- `obligation.json` records the frozen source hash, ordered graph, original-input
  domain, independent specification, units/budgets and arithmetic semantics.
- `evidence.json` binds adapter roles, tool versions/hashes, raw evidence forms
  and validation details to that obligation's identity.
- `producer/` and `runs/` retain exact generated queries, foreign output, command
  streams and failures. FPTaylor candidates use hexadecimal upper values rather
  than rounded decimal display strings; its default configuration is also frozen
  under `tool-data/` and participates in freshness checking.
- `analysis.json` distinguishes the proposed conclusion from its independent
  derivation and records `accepted_bounds` only after Lean checking succeeds.
- `validation.json`, when present, identifies an adapter-generated Lean module.
  Final proofs remain under `lean/` with the expected root check.

Normal `audit` checks source/dependency/runtime and selected tool freshness.
`replay` binds the frozen obligation and recompiles the saved proof plus the root
type/axiom check. It performs no setup, tool admission or producer execution and
needs no original producer installation. Rust replay still needs its recorded
compiled Aeneas model. Existing pre-interface certificates retain their replay path.

## Add another tool

Add a provider module named `scripts/numerics/adapter_NAME.py` exporting an
`ADAPTERS` tuple. Discovery registers its capability records without edits to
the CLI, workflow, reports or replay implementation. Adapters are trusted provider
code; foreign output is parsed as data.

An adapter declares its name, role, evidence form, applicability check and
execution callback. It may provide a pinned source recipe for the shared setup
service. Producers return a `Proposal` and JSON evidence details:

- `summaries` and `steps` supply untrusted compositional annotations.
- `claims` maps IR output names to the exact allowances to be checked.
- An optional `lean_source` and `authored` declaration record supply a generated
  Lean accuracy argument instead of compositional annotation proofs. Its type
  must match those claims against `Workflow.reference`; the root also checks the
  independent specification and requested budgets.

Use the shared runner and tool admission services. Preserve tool-specific
payloads and version/model restrictions. New inference or arithmetic semantics
require their own soundness argument; existing evidence vocabularies can reuse
the validation interface. Keep mathematical support in FLARE's subject trees.

`make numerics-check` tests an additional adapter, generated Lean modules,
invalid selected claims, setup recipes and frozen-obligation mismatches. Set
`FLARE_NUMERICS_ANALYSIS_TOOLS=/absolute/path/to/local-tools.json` to additionally
run both real producers over addition, polynomial and division families and
replay their proofs with producer entry points disabled. CI builds the pinned
producers and runs these controls and the maintained external benchmarks.
