# Roadmap: broader numerical verification

The demonstrated examples are the current baseline. Sharing FLARE and collecting
feedback proceed alongside this plan. Reported problems and new application
requests can change the order of later milestones.

The goal is one engineer-facing skill that verifies the original numerical code,
produces a reviewable Lean result, and optionally delivers a reusable verified
Rust port. Define completeness for each supported combination of source
constructs, arithmetic semantics, requested property and delivery target.

## Current baseline

- The FilterPy scalar `GHFilter.update` example has an eight-update error
  certificate. Its reusable Rust port was also certified and replayed in a
  clean Ubuntu ARM64 VM after installing the required tools.
- The naive scalar covariance example has a Lean counterexample to strict
  positivity, with an admissible input and a positive exact reference.
- The automatic path covers restricted scalar source, selected Python methods,
  local helpers and bounded loops. Authored Lean proofs can supply arguments
  beyond the automatic bound producer.
- Larger loops and the original Rust IMU API have checked scale fixtures.
  Four-state covariance/correction graphs remain analysis targets without a
  source-program certificate; see the [scale guide](../benchmarks/numerics/README.md#increasing-scale).

Each milestone must retain the original source, domain, reference and requirement.
Changing any of these creates a separately reviewed case. A completed capability
includes a checked Lean root, axiom audit, saved-proof replay and rejection tests.
Setup failures, proposed bounds and resource exhaustion remain distinct outcomes.

## Integration strategy

Build reusable verification capabilities through external tooling, evidence
importers and verified Lean implementations. New lemmas support the semantics
and soundness of those mechanisms. Success is measured by the class of requests
the machinery handles, rather than by the number of individual proofs added.

Use a common orchestration interface with tool-specific adapters and evidence
payloads. It must accommodate analyzers, proof-producing tools, source extractors
and Lean-native procedures; these have different roles and assurance boundaries.

| Shared interface | Responsibility |
| --- | --- |
| Obligation | Identify the original source/model, exact reference, domain, arithmetic semantics and requested conclusion |
| Capabilities and routing | Declare supported constructs, properties, arithmetic models, versions and evidence types; select compatible routes |
| Setup and execution | Obtain compatible tools, record identities, enforce resource limits and retain commands and failures |
| Evidence adapter | Preserve raw output and expose its tool-specific payload under a common provenance record |
| Lean validation | Import proof evidence, independently prove a candidate claim, or run a verified Lean inference procedure |
| Composition and delivery | Discharge caller premises, connect checked results to the application root, report outcomes and replay saved proofs |

A tool that emits a useful proof trace can have an adapter plus a Lean proof
importer or checker. A tool that emits bounds or hints can feed a reusable Lean
procedure that independently establishes the proposed claim. Where external
output is unsuitable, implement the needed inference algorithm in Lean and prove
its soundness. Choose between these routes by coverage, implementation effort,
maintenance and checking cost.

Keep exact semantic information and tool-specific evidence; a common envelope
does not make different arithmetic models equivalent. Existing adapters and
checkers should compose across tools that share an obligation kind. A new tool
using an existing proof vocabulary should need an adapter and capability record;
new semantics or inference rules also need their own soundness argument.

The core set for milestones 2–7 is Lean/Mathlib/FLARE, Gappa, FPTaylor and
Charon/Aeneas. Additional tools are milestone 8, after the numerical and source
capabilities below; they do not block completion with the core set.

The planned integrations below are explicit work items. A documented route is
not an implemented adapter, and invoking a tool does not import its reasoning.

| Tools | Current integration | Planned reusable capability | Milestones |
| --- | --- | --- | --- |
| Gappa | Query conclusion reconstructed by reusable scalar validation; Coq trace retained | Broaden supported reasoning and retain checked algebraic rewrites | 2–3 |
| FPTaylor | Parsed exact candidate is the Lean proof target | Extend coverage and useful hints through the same validator; reject unproved candidates | 2–3 |
| Charon/Aeneas | Existing Rust-to-Lean extraction and checked return relation, with declared translator/model trust | Extend source coverage and compose extracted APIs, loops and state with numerical contracts | 4–7 |
| PRECiSA/PVS | Documented route only | Admit branch/domain summaries and reconstruct or check them in Lean; preserve unstable-branch semantics | 8 |
| Why3, Frama-C/WP, VST | Documented routes only | Adapt supported source models and verification obligations; discharge their numerical and memory premises in Lean with explicit frontend boundaries | 8 |
| Coq/Flocq, VCFloat2, LAProof | Reference workflows only | Import a useful shared evidence vocabulary or reimplement its needed inference with Lean soundness proofs; do not treat a foreign theorem name as a Lean proof | 8 |
| Python, Julia, MATLAB/Octave, rustc | Restricted source admission and sampled runtime diagnostics | Extend source correspondence separately from proof evidence; retain interpreter/compiler assumptions and runtime distinctions | 4–7 |

For each family, first select a retained application obligation and inspect the
actual version's evidence and semantics. Then implement and test the adapter and
its Lean validation path, or record the concrete blocking gap. This is a coverage
plan, not a promise that every tool needs a distinct importer. Tools that share
an evidence vocabulary should reuse its checker. The architecture must support
adding tools without redesigning orchestration, reporting or replay.
Application-specific authored proofs remain available, while the planned
capability work prioritizes reusable automation.

## Sequence

| Milestone | User benefit | Concrete completion target |
| --- | --- | --- |
| 1. Feedback and reproducibility | Other engineers can reproduce the demonstrated workflows | Reported issues become portable cases; public examples replay from a matching checkout |
| 2. Shared tool integration | Reuse setup, routing, evidence handling and Lean validation across tools | Add distinct producer/evidence routes through the same workflow and replay boundary |
| 3. Reusable scalar reasoning | Smaller values and tighter budgets become practical | Automatically close the retained `2^-51` obligation and preserve small positive divisor bounds |
| 4. Composable loops and proofs | Longer computations reuse checked components | Resolve proof-resource failures in the 16/48-update Kalman cases; add induction over repeated calls |
| 5. Vectors and matrices | Verify code that operates on collections | Complete a small array-based application with a source bridge and a Lean error theorem |
| 6. Complete application behavior | Cover validation, branches, conversions and decisions | Verify the original 48-event Rust IMU application's success and error behavior |
| 7. Combined workflows and Rust delivery | Verify larger applications and preserve their APIs when porting | Complete a multi-module application using composed proofs and its actual Rust implementation |
| 8. Additional verification tools | Broaden coverage where another tool adds useful reasoning or source support | Add selected tools from the integration table through reusable Lean validation, driven by application gaps |

Milestone 2 supplies the shared integration boundary. Milestones 3 and 4 build
numerical and scaling capabilities through it. Milestones 5 and 6 can progress
independently once their needed foundations are available.
Rust correspondence and setup checks accompany each new source capability;
milestone 7 composes them into a larger delivery.

## 1. Turn feedback into reproducible workflows

### Deliver

- Maintain a capability table by source construct, property, arithmetic model,
  platform and Lean/Rust route. Distinguish demonstrated support from planned work.
- Convert feedback into minimal fixtures with frozen source, contract, provider
  and tool identities, commands, actual outcome and the precise failing stage.
  Include unfamiliar applications as well as regressions from the current demos.
- Keep copied-skill/provider compatibility explicit. Test setup without existing
  Lean or extraction tools, output-directory agreement, and saved-proof replay.
- Make the three engineering outcomes consistent across reports: requirement
  proved, counterexample proved, unresolved. Give the authored counterexample
  route a maintained delivery format alongside automatic error certificates.

### Completion criteria

Another engineer can reproduce both README examples from public instructions
and inspect their Lean roots. Every accepted feedback case has a repeatable test
or an explicitly recorded open obligation. Setup results name the tested platform
and tool route; a setup failure cannot count as a numerical rejection.

Record setup time, agent intervention and warm replay time separately. Use these
measurements to prioritize usability work without changing proof requirements.

## 2. Streamline integration across verification tools

The first shared layer is implemented in the
[tool integration guide](tool-integration.md): registered producer/extractor/
validator roles, source setup, versioned obligations/evidence and producer-free
replay. Gappa and FPTaylor exercise different output forms. Reusable scalar
validation now consumes their candidate conclusions: Gappa's successful query
radius or FPTaylor's exact parsed bound becomes the Lean proof target. Addition,
polynomial and division families exercise both routes and replay without the
producers. Corrupted bounds are rejected. This is independent reconstruction;
the retained Coq trace is not a checked/imported proof. The core set is sufficient
for this milestone; additional tools belong to milestone 8.

### Deliver

- Define versioned obligation, capability and evidence interfaces, reusing the
  current request, command-record and frozen-proof formats where they fit.
- Factor setup, invocation, resource limits and diagnostics into shared services.
  Tool-specific flags, parsers, model assumptions and extraction details stay
  in adapters. Declare compatibility and unsupported cases explicitly.
- Provide reusable Lean validation routes for proof evidence, candidate claims
  and extracted source models. Support both external inference with checked
  output and inference implemented with a soundness proof in Lean.
- Connect the existing `lean-flare` and Rust extraction paths to this interface.
  Add external producer integrations exercising both proof-bearing output and
  candidate-only output. Select the initial tools using retained fixtures and
  user requests.

### Completion criteria

At least two external producers with different evidence forms use the same
workflow to obtain Lean-checked application results, with their useful output
actually consumed by validation. Merely retaining a trace while independently
proving an unrelated requested allowance does not meet this criterion. Candidate
output is accepted only after an independent Lean argument closes that candidate
claim. A supported family of new inputs needs no handwritten numerical proof per
instance.

A further adapter using an existing obligation/evidence kind can be added without
changing core orchestration, reporting or replay. Unsupported rules and model
mismatches remain unresolved. Tests corrupt evidence, omit premises and change
tool versions, and check that rejection occurs at the appropriate boundary.
Saved-proof replay needs neither the producer nor its installation.

## 3. Close scalar gaps with reusable inference

Implemented for small scalar graphs through
[reusable scalar validation](tool-integration.md#reusable-scalar-validation).
The unchanged mean-update request certifies at `2^-51` with three gain intervals,
and the tiny-gain request preserves positive native/exact divisor floors.
Related input ranges and scales use the same engine; tests reject false bounds,
incorrect rewrites and arithmetic-model mismatches, and replay saved proofs
without inference or external producers. Search limits remain explicit. Larger
loops and proofs are milestone 4 rather than an extension of this scalar claim.

### Deliver

- Choose external integration or verified Lean inference for each missing class
  of reasoning. Address scale-aware outward bounds, positive native and exact
  divisor floors, and useful precision/correlation handling through these engines.
- Use the simple-addition inflation, tiny-denominator cases and frozen Gappa
  four-stage mean-update argument as acceptance cases. They are documented in
  the [benchmark guide](../benchmarks/numerics/README.md#known-analysis-gaps-and-external-fixtures).
- For the Gappa case, import its useful output or implement the relevant
  inference in Lean. Include rewrite validation and native binary64 semantics
  in the reusable checking path. Apply the same design choice to other tools.

### Completion criteria

The unchanged tight mean-update request certifies at `2^-51` and replays through
the reusable route. The small-denominator case obtains a checked bound without
an artificial zero lower bound from normalization. Run related kernels and
changed input ranges through the same machinery without adding per-case proofs.

Corrupt bounds, rewrite identities and rounding-model mismatches fail their
intended checks. Compare coverage, accepted bounds, proof time and maintenance
cost across available routes. Improving the current producer is one option;
another backend can supply the capability.

## 4. Compose proofs across loops and function boundaries

Implemented for admitted Python helper chains and two-state folds. Generated
models retain shared helper definitions, and each local contract accepts both
native and exact incoming state with its accumulated error. The exact step is
related to the independent recurrence once, then that identity rewrites the
fold. Scale-aware outward summaries preserve the 128-update divisor floors.

The unchanged 16/48-update Kalman cases certify; 128 updates reach a checked
`budget_not_met` result with the original budgets. IMU loops exercise the same
machinery. Optional content-keyed contract reuse preserves unchanged prefix
proofs across callers, while replay recompiles saved source without that cache.
Generic `foldl_contract` and `foldl_error_bound` rules support supplied invariants
and local error recurrences; the API checks instantiate them at 16, 48 and 128
steps. They do not infer missing invariants or admit unbounded source loops.

### Deliver

- Preserve shared expressions and function boundaries in generated models and
  proofs. Use reusable checked local contracts rather than expanding every
  repeated mathematical expression.
- Carry reached-domain invariants, finiteness, denominator floors and incoming
  state error across calls. Add an induction rule for a supplied loop invariant
  and error recurrence, supporting horizons expressed as a parameter.
- Reuse unchanged local proofs when a caller changes, while regenerating affected
  input wiring, reference equations and composition obligations.

### Completion criteria

The existing 16/48-update Kalman cases finish their Lean proof and budget stages
under the maintained resource limits, without treating resource failure as a
passing outcome. A checked bound above budget remains a valid diagnostic outcome.
The 128-update case reaches a checked numerical result after its denominator
obligations are discharged; it must retain the original engineering budgets.

Add a parameterized loop theorem and instantiate it at multiple horizons. Show
that an incorrect recurrence or reset of incoming state error is rejected.
Track proof construction, checking time, peak memory and artifact size across
the existing Kalman/IMU progression. Raising limits alone does not complete this
milestone.

## 5. Admit vectors and matrices from actual source

Implemented for fixed-shape built-in Python list products through the
[`python_arrays` profile](../skills/verify-numerics/references/arrays.md).
The same adapter and typed-root generator cover a two-state linear prediction,
calibration matrix composition, a three-term projection, a four-state linear
prediction and the one-entry boundary. Roots include input shape guards,
fresh output shape, successful finite dense execution and entrywise error
against independent real matrix expressions. The reusable ordered-product
bridge preserves the original ascending, separately rounded schedule.

Source-model regeneration and producer-free replay cover every example.
Wrong shapes, aliases, indices and order are rejected at admission; false
exact specifications and weakened roots are rejected in Lean. This scope does
not establish NumPy/BLAS correspondence, arbitrary mutable collections or an
automatic array Rust port. The original large covariance/correction graphs
remain intermediate analysis targets; they have no application certificate.

### Deliver

- Start with fixed-size vectors and small dense matrices: indexing, updates,
  shape checks, reductions, dot products and matrix multiplication with an
  explicit accumulation order. State aliasing and mutation conditions.
- Connect admitted source operations to existing `Flare.Matrix` algorithms and
  numerical theorems. Begin within their proved dimension and arithmetic profiles.
- Cover an array-based filtering or estimation example with an independent
  matrix recurrence. Reuse the four-state graphs as intermediate proof targets,
  then establish their connection to the actual source before claiming an
  application certificate.

### Completion criteria

One small array-based application has checked shape/domain conditions, finite
execution, an output error theorem and replay. A second use exercises the same
vector/matrix contracts outside that application. Wrong shapes, aliasing,
indexing and accumulation-order assumptions have rejection controls.

NumPy/BLAS calls need a bridge for the selected implementation and arithmetic
semantics. Existing theorems about FLARE's own matrix algorithms do not establish
that bridge. Add such calls to supported capabilities only when that obligation
has been discharged.

## 6. Cover validation, branches and decisions

Implemented through the reusable [Rust application proof-bundle interface](../skills/verify-numerics/references/rust-applications.md).
The original 48-event public API is freshly extracted with its companion timing
module. Authored source bridges and numerical proofs close one Lean root for all
input words: exact admission conditions, ordered rejection exits, finite success,
original-integer timing, the returned position allowance and strict decisions.
The uncertain branch has an explicit exact-reference neighborhood, including
rounding in the final subtraction. This is an authored-contract route; it does
not add arbitrary Rust APIs to the automatic scalar parser.

The provider freezes every selected crate/proof file, checks Charon's local
source identities, records tool/model hashes, independently applies the reviewed
contract to the extracted entry and audits the root's transitive axioms. Replay
compiles saved Lean sources without translators or Rust runtimes. Negative
controls reject weakened/axiom roots, changed timestamp arithmetic and inadequate
padding after source correspondence passes. Runtime cases cover branch endpoints,
all decisions, NaN/infinities, wrong sizes, late errors and full-width epochs.
The smaller scalar-loop fixture remains a separate regression.

### Deliver

- Admit the needed source modules, structs, slices, enums, results and state
  mutation. Include integer timestamps, subtraction and integer-to-float
  conversion in the numerical contract.
- Prove executable guards enforce the theorem's premises, including exceptional
  values, range/shape checks and integer overflow behavior. Cover error returns.
- Analyze floating-point branches and rounded decision arithmetic. Prove
  agreement with the exact reference when a checked margin permits it, and
  account explicitly for uncertain regions.
- Bring in the companion timestamp code needed by the retained `imu48.rs`
  fixture as a frozen compilable application, with source attribution.

### Completion criteria

The original 48-event Rust IMU API has a root theorem covering its input gate,
successful execution, arithmetic allowance and `Below`/`Above`/`Uncertain`
decisions. Its error outcomes are also specified and checked. Use the actual
timestamp path and public API; preserve the separate scalar-loop fixture as a
smaller regression.

Add cases at branch thresholds, invalid timestamps, nonfinite inputs and wrong
sizes. A deliberately inadequate decision padding must fail verification or
produce a checked counterexample when the property is false.

## 7. Complete a combined application and reusable Rust delivery

### Deliver

- Choose the application using feedback, with a proposed initial target of a
  multi-module four-state estimator combining initialization, prediction,
  correction, validation and a caller-visible decision.
- Compose source correspondence, checked numerical contracts, loop invariants
  and tool results into one application theorem. Include all numerical
  premises introduced by earlier stages.
- For a non-Rust input, generate and extract the actual reusable Rust port:
  constructors, state, methods, options, errors and loops. Keep verification
  drivers separate and prove the required API/state correspondence in Lean.
- Make the report identify which properties were proved, their runtime domain,
  trust boundaries, artifact locations, and run/replay commands. Exercise source
  changes and compatible tool upgrades as maintenance scenarios.

### Completion criteria

The original application and requested Rust delivery each have their required
Lean roots and replay successfully from frozen evidence in a clean setup.
API/state tests supplement the correspondence proof. At least one change to a
module or contract regenerates affected proofs and preserves reusable local
results. Another engineer reproduces the delivery from its report.

## 8. Add further verification tools

After milestones 3–7 with the core set, prioritize PRECiSA/PVS, Why3,
Frama-C/WP, VST, Coq/Flocq, VCFloat2 and LAProof using actual application gaps.
Inspect each selected version's source model and output before choosing an
importer, candidate checker or verified Lean implementation. Reuse existing
evidence vocabularies where possible.

A completed integration must use the tool's useful result in a checked Lean
application argument, replay without the producer, and reject corrupted evidence
and mismatched semantics. Tool installation or retaining an unchecked foreign
proof alone does not complete this milestone. No requirement to integrate every
listed tool delays the preceding milestones.

## Work that accompanies every milestone

- Prioritize reusable external tooling, evidence importers and verified Lean
  procedures. Add mathematical lemmas when needed for their soundness, semantic
  bridges or reusable contracts. Reuse FLARE/Mathlib before adding alternatives;
  keep results in the existing subject trees and track concrete upstream
  candidates in [the Mathlib guide](upstream/mathlib.md).
- Maintain one skill and one final Lean certification boundary. Optional tools
  remain outside core library dependencies. Importer rules need proved semantics,
  explicit version/model checks and rejection tests for unsupported evidence.
- Expand the benchmark matrix with useful proofs, genuine counterexamples and
  explicit open cases. Report these categories separately; successful rejection
  tests do not increase the count of verified applications.
- Keep platform/setup coverage and source-model/compiler/hardware trust
  boundaries visible. Measure agent assistance separately from proof replay.

After these milestones, prioritize additional capability packages from feedback:
binary32 and mixed precision, explicit FMA, elementary functions, sparse kernels,
and additional language/library adapters. Each package needs its own semantics,
reusable numerical contracts and application acceptance cases.
