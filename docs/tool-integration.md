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
| `lean-flare` | Producer | Rational proposals or the existing authored-proof interface; numerical claims checked in Lean |
| `gappa` | Producer | Retains Gappa 1.8.3 Coq proof output; independently derives the requested budgets in Lean |
| `fptaylor` | Producer | Retains pinned FPTaylor `0.9.4+dev` numeric candidates; independently derives the requested budgets in Lean |
| `rust-aeneas` | Extractor | Fresh Rust extraction and its actual return relation under the existing source-model trust boundaries |
| `lean-root` | Validator | Compiles proof modules, independently ascribes the expected root type and audits its transitive axioms |

The initial external routes certify the **requested budgets**, using the existing
FLARE compositional derivation. Sharper foreign bounds remain candidates.
Gappa's Coq trace is retained as proof-bearing output but is not imported or
checked as a Coq proof. A foreign success cannot close a Lean premise; a requested
bound that the independent derivation cannot prove remains unresolved.

Adapters can also emit a Lean proof module through the common validation
interface. This supports reusable translators and Lean inference procedures
without changing orchestration. The emitted accuracy declaration must have the
expected original-input type and its full dependencies pass the same axiom audit.
Implementing sharper scalar inference is the next [roadmap milestone](roadmap.md).

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
