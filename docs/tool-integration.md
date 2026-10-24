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
| `precisa` | Producer | Reconstructs the maximum stable/unstable candidate from pinned PRECiSA `4.0.4`; checks divergent flows in Lean and retains PVS files |
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
The scalar and conditional validators are described below. Further tools follow the
[roadmap integration plan](roadmap.md#integration-strategy).

## Reusable scalar validation

`scripts/numerics/scalar.py` proposes exact rational enclosures, local rounding
allowances, sparse polynomial rewrites and a bounded input subdivision. Lean
checks these using FLARE's actual binary64 nearest-rounding theorems, Mathlib's
`ring` normalization and the proved `Analysis.IntervalExpression` inference
engine. Exact rational enclosure checks run in the Lean kernel; their soundness
reuses Mathlib's interval rules. Powers preserve nonnegative square floors.
Generated case proofs also
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

The [shared enclosure guide](proof-evidence.md) covers the typed rule vocabulary,
power/regularized-reciprocal families, unchanged external candidates, rejection
controls and measured coverage/cost comparison. Gappa and FPTaylor use this same
inference engine; their foreign traces remain untrusted evidence.

## Conditional validation and PRECiSA

The explicit `python_branches: true` profile admits one terminal scalar Python
conditional with an ordered guard, up to 32 arithmetic nodes and an independent
exact conditional reference. It uses the scalar arithmetic checker, then checks
all four native/exact branch combinations with finite-order bridges and real
inequalities. It never assumes branch stability. Both arms must satisfy arithmetic
premises on the whole domain. See the [profile guide](../skills/verify-numerics/references/conditionals.md)
for restrictions, including the current Lean-only delivery target.

The separate `python_branches: {"domains": "guard"}` mode proves agreement for
a direct original-input/literal comparison and derives branch-local domains.
Only reachable arms need arithmetic contracts. This closes the guarded reciprocal
on `[0,2]` without assuming an unconditional nonzero denominator. It currently
uses `lean-flare`, with no computed prefix or external-producer integration.

The PRECiSA adapter emits the admitted ordered PVS model with the pinned
`float_bounded_axiomatic@ieee754_double` import and runs absolute-error JSON
analysis without `--assume-stability`. Decimal input endpoints enclose the exact
request domain after PRECiSA's binary64 parsing. Constants retain their binary64
values. PRECiSA's input uncertainty model is a candidate-search boundary; the
final Lean theorem checks exact decoded original inputs and the independent
specification directly.

The exact binary64 values in `stableError` and `unstableError` determine the
maximum candidate. This becomes the proof target, even when it misses the
engineering budget. A null unstable field does not remove divergent cases.
PVS files are retained as foreign evidence, not checked/imported proof terms.
The threshold gate uses PRECiSA's one-unit unstable-flow candidate; ignoring it
or asserting stability fails Lean reconstruction. The continuous innovation
example retains PRECiSA's conservative roughly 40 m bound as `budget_not_met`,
while the default branch route proves the unchanged `10^-6` m allowance.
See the [examples and commands](../examples/numerics/branches/README.md).

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

The explicit `python_counted` route additionally admits a two-state
`range(count)` loop calling a scalar helper with fixed configuration. It proposes
a uniform native/exact invariant, checks initialization and step preservation,
and uses `foldl_contract` for all natural counts. The selected count is instantiated
at the root; helper definitions, contracts and the invariant proof body stay
constant across horizons. See the [scaling guide](scaling.md) for source-backed
1,024-call and 1,024-operation workloads, measurements and cold replay.
Arbitrary invariants, input streams, mutation and combinations with collection
profiles need additional source/proof support. Gappa/FPTaylor retain their scalar
graph limits. A loose checked bound
remains `budget_not_met`, including the 128-update Kalman mean allowance.

## Fixed-shape array source

The Python `python_arrays` profile supplies shapes independently of the source
and uses the existing `lean-flare` route. A restricted AST interpreter lowers
indexed reads, fresh output updates and fixed loops to a persistent Lean array
model and ordered scalar graph. Admission checks native dot-product order,
including its initial positive zero and each separate multiply/add.

The root quantifies over shaped arrays, proves the input shape guard and output
shape, and relates returned entries to `Matrix.Dense.multiply` through the
generic `Matrix.OrderedProduct.multiply_eq` theorem. The existing
`Matrix.Multiplication.multiply_accuracy` discharges successful finite dense
execution. The shared binary64 checker establishes each component allowance,
and real matrix expressions supply an independent reference. Thus this path
reuses matrix semantics and numerical validation without a per-application lemma.

Frozen replay regenerates the entire array model from the retained source,
then recompiles the proof and reconstructs its expected array root type. Wrong
shapes, aliasing, indices and accumulation order have admission controls; false
exact references and weakened roots have Lean rejection controls. This profile
does not extend the Gappa/FPTaylor source or Rust extraction subsets. See the
[array guide](../skills/verify-numerics/references/arrays.md) for configuration.

## C source conditions and optional foreign tasks

The [C route](c-verification.md) reuses `lean-flare` numerical validation and
adds source-derived access/counter proofs and an ordered typed-cell heap model.
The root proves execution, frame behavior, finiteness, accuracy and budgets under
the stated caller conditions. Physical C object validity and compiler/source
mapping remain declared boundaries. This route is a source frontend plus Lean
model/proof generation; it does not modify an external analyzer.

`scripts/export_c_vcs.py` separately retains Frama-C/WP 31.0 and Why3 1.8.2 tasks
from source ACSL. Their typed-memory/floating-point theories need further bridges
before foreign proof steps could discharge Lean obligations. The exporter does
not import proofs or translate JSON numerical contracts into ACSL. Its successful
status is `task_evidence_only`, regardless of solver verdicts. Normal C
certification/replay does not need these tools. See the C guide for the actual
evaluation and future integration boundary.

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
use `FLARE_GAPPA`, `FLARE_FPTAYLOR`, `FLARE_PRECISA` or `PATH`. A missing executable, unsupported
version or changed selected hash has a distinct `failure_kind`.
For FPTaylor data, an explicit `base` takes precedence over `FPTAYLOR_BASE`,
followed by the executable's parent directory.

The ordinary and external-producer arithmetic model is separate binary64
operations, nearest/even, gradual subnormals and no FMA or reassociation. An optional
`arithmetic` object must match the model printed by `capabilities`. The separate
[explicit-FMA Python profile](explicit-fma.md) uses `fma: "explicit"` with
`lean-flare` and Lean delivery; external producers retain their current admission.
Gappa's exporter requires dyadic domain endpoints. Both exporters preserve the
ordered admitted graph and use exact constants; Lean still checks its independent
specification.

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
python3 scripts/certify_numerics.py setup --tool precisa \
  --out /shared/tool-pool/precisa-2626ba1 --timeout 3600
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
on macOS an explicit `DEVELOPER_DIR` is preserved. The PRECiSA recipe requires
Linux, GHC 9.6.7, Cabal >=3.6.2.1 and C/C++ prerequisites; its
[setup guide](../skills/verify-numerics/references/tool-setup.md#precisa) describes
Ubuntu ARM64 setup. It builds the pinned Kodiak submodule and a hash-pinned
filib++ archive. The upstream executable has no version command; the installed
launcher reports recorded package/source identity. Admission checks the receipt,
native binary and backend library hashes. Setup covers these producer recipes,
while the [tool setup instructions](../skills/verify-numerics/references/tool-setup.md)
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

PRECiSA's build receipt is frozen under `tool-data/`. Native binary/backend
hashes participate in live freshness checking without copying the installation
into each certificate. Frozen replay needs no original binaries or libraries.

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

Set `FLARE_PRECISA=/absolute/path/to/precisa/install/bin/precisa` to additionally
run real conditional producer tests and producer-free replay. The maintained
recipe and actual analyzer/Lean path were tested in an isolated Ubuntu ARM64 VM.
Default CI runs conditional source/proof/rejection controls; it currently builds
only Gappa/FPTaylor as real external producers.
