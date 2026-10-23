# Roadmap: broader numerical verification

FLARE aims to give an engineer one reviewed contract, one final Lean theorem,
and, when requested, a reusable verified Rust implementation of the original
code. Broader applicability means covering more combinations of source constructs,
arithmetic semantics, properties and delivery targets with reusable machinery.

Prioritize external tooling, evidence import/checking and verified Lean inference.
Add mathematical lemmas for their soundness and semantic bridges. Measure progress
by applications and supported families, rather than theorem or adapter counts.
Feedback and retained application gaps can change the order below; they need not
delay implementing capabilities with clear acceptance cases.

## Current baseline

- Restricted scalar Python, Julia, MATLAB-compatible and Rust source has automatic
  admission and numerical validation. Python additionally has selected scalar
  methods, helpers, bounded loops and separate fixed-list array and terminal
  conditional profiles. A compact two-state counted-loop profile retains a
  uniform invariant across all natural counts, with selected roots through 1,024.
  These profiles do not yet compose arbitrarily.
- Closed C11 double APIs admit scalar helpers, by-value structs, fixed buffers
  and unsigned literal-count loops. Source-derived access/counter conditions and
  typed-cell heap execution join numerical accuracy in one Lean root. Scalar
  Rust delivery retains the real API; buffer delivery is currently Lean-only.
  Physical object validity and compiler/source mapping remain explicit premises
  and trust boundaries. See the [C guide](c-verification.md).
- Gappa, FPTaylor and PRECiSA supply candidate conclusions that are independently
  proved in Lean. Their retained Coq/PVS traces are not imported proofs. See
  [tool integration](tool-integration.md). Gappa and FPTaylor share a proved
  exact rational enclosure engine with power correlations and checked leaf
  premises. Square/quartic families and positive regularized denominators have
  maintained cases; foreign proof traces remain untrusted. See
  [shared proof evidence](proof-evidence.md).
- Charon/Aeneas supplies fresh Rust extraction. Reviewed bridges connect the
  actual extracted API to numerical contracts, including validation, integer
  timing, errors and decisions. General application bridges still need authored
  Lean proofs.
- The scalar FilterPy GH filter, Rust IMU API and multi-module
  [planar tracker](../examples/numerics/planar/README.md) have maintained certificates
  and reusable Rust delivery examples. The planar tracker composes two scalar
  filters; it is not a dense Kalman filter.
- Fixed-shape Python list products have checked shapes, execution order and
  entrywise error bounds. The separate [scientific profile](scientific-arrays.md)
  certifies selected NumPy eager operations and ordinary Julia vector APIs, with
  typed tensor dimensions/storage, source execution and independent exact
  collection algebra. A two-state dense covariance/correction checks all six
  outputs; a reusable fixed-array Rust calibration port retains its real loop.
  NumPy reductions, BLAS calls and fused Julia broadcast remain unsupported.
- The [conditional examples](../examples/numerics/branches/README.md) cover all four
  native/exact branch choices. The computed-guard profile validates both arms on
  the whole domain. A separate direct-input guard profile proves branch-local
  domains and denominator premises. Both support Lean delivery only.
- Source-backed shared pipelines reach 1,024 arithmetic operation instances with
  local contract reuse after a caller changes. Counted-loop proofs stay compact;
  frozen-source replay recompiles saved modules without producers or the helper
  cache. See the [scaling guide](scaling.md) for measurements and limits.
- The 16/48-update Kalman cases certify; 128 updates reach a checked
  `budget_not_met` result with unchanged budgets. Large covariance/correction
  graphs remain analysis probes without source-program certificates. See the
  [scale guide](../benchmarks/numerics/README.md#increasing-scale).
- The README's naive covariance example has an authored, replayable Lean
  counterexample. The automatic error-bound CLI has no counterexample status yet.

These are scoped capabilities, not support for arbitrary programs in each
language. Independent engineer reproduction remains a sharing follow-up; current
regressions and VM experiments establish automated reproduction of selected cases.

## Next priorities

1. **Broaden arithmetic models.** Add mixed binary32/binary64 semantics, explicit
   FMA and implementation-specific function contracts on retained applications.
2. **Broaden scientific code and automated delivery.** Extend actual library/API
   bridges where applications require them. Broaden Rust correspondence-proof
   generation, counterexamples, setup and maintenance.

Each milestone retains source, domain, independent reference and engineering
requirements. Changes to any of these create a separate reviewed case. Completion
requires a Lean root, axiom audit, frozen-source replay and rejection controls.
Setup failure, unsupported source, resource exhaustion, an unproved candidate and
a checked bound above budget remain distinct outcomes.

## Sequence

The next implementation milestone is 13.

| Milestone | User benefit | Concrete completion target |
| --- | --- | --- |
| 13. Precision and mathematical functions | Cover arithmetic used outside the current binary64 subset | Mixed binary32/binary64 and explicit FMA examples certify; selected elementary functions gain implementation-specific contracts |
| 14. Reliable automated delivery | Other engineers can use and maintain the workflow on unfamiliar code | Fresh-machine delivery, a first-class Lean counterexample path, and held-out applications pass the release criteria |

Milestone 13 progresses per arithmetic feature once its semantic bridge is ready.
Setup, counterexamples and maintenance work from 14 accompanies every milestone;
a separate integration test closes 14.

No milestone requires integrating every candidate tool or supporting a complete
source language before a useful closed profile can ship.

## Integration strategy

Keep common setup, version/model admission, routing, bounded execution, evidence
identities, composition and replay. Preserve each tool's actual payload and
arithmetic semantics. Select a source bridge, candidate reconstruction, proof
checker or verified Lean implementation after inspecting a pinned version's
output. An external success verdict never discharges a Lean premise by itself.

| Tool family | Current status | Next reusable capability | Milestones |
| --- | --- | --- | --- |
| Gappa / FPTaylor | Candidate reconstruction with shared proved rational enclosure/power inference | Tighter division correlations, larger composed obligations and lower evidence/checking cost | Future evidence work |
| PRECiSA/PVS | Implemented scalar/terminal-conditional candidate reconstruction using the common scalar proof path | External branch-local domains, incoming errors and callable summaries; retain unstable-flow obligations | Future evidence work |
| Charon/Aeneas | Implemented scalar/application/fixed-array extraction with authored bridges | Generate bridges for admitted structs, state, loops and result types; preserve actual APIs and separate drivers | 14 |
| Frama-C/WP / Why3 | Pinned source/ACSL/task export evaluated; no Lean proof importer | Translate selected application contracts and check useful typed-memory/FP evidence against the admitted source model | Future evidence work |
| CBMC | Proposed addition | Bounded integer/FP/memory counterexample candidates and execution paths, rechecked against the admitted source model in Lean | 14 |
| VST / Coq / Flocq / VCFloat2 / LAProof | Reference workflows; no Lean importer | Reuse suitable typed evidence or implement the needed inference and semantic bridges in Lean; select a numerical or memory obligation first | 13, future evidence work |

Frama-C/WP 31.0 and Why3 1.8.2 task output was inspected on the retained C API.
The [C guide](c-verification.md) describes the export utility and why the current
closed profile proves source-derived conditions directly in Lean. Task export
is not a Lean adapter or a translation of JSON numerical requirements into ACSL.
Useful foreign evidence checking still needs semantic bridges and a measured gap.
See the [Frama-C documentation](https://frama-c.com/index.html)
and [Why3 task/driver interface](https://why3.org/doc/manpages.html#the-prove-command).
CBMC supplies bounded C/C++ checking and counterexample paths; absence of a
bounded failure is not an unbounded-loop theorem or an imported Lean proof.
See its [official documentation](https://diffblue.github.io/cbmc/cprover_documentation.html).

Every new integration needs:

- A retained application gap, explicit source/arithmetic semantics and a supported
  version. Tool setup or invocation alone is not a completed integration.
- Useful output actually consumed by Lean validation. Candidate routes must prove
  the selected candidate itself; another producer's result is a separate attempt.
- Premises closed at the caller, including incoming error, memory/shape validity,
  finiteness and exceptional behavior where applicable.
- Frozen replay without producers or LLMs, plus controls for corrupted evidence,
  changed versions, wrong models and missing premises.

Use shared evidence vocabularies when appropriate. Do not build a separate generic
proof importer for every tool, or use a common envelope to erase semantic differences.

## Source language and library plan

A language name is insufficient to describe support. Track source constructs,
value types, library operations, semantics, automatic/authored proof coverage,
platform and Lean/Rust delivery separately in `capabilities` and regression cases.

| Source | Current supported profile | Next scope | Later scope / separate obligation |
| --- | --- | --- | --- |
| Python | Restricted scalar/method/loop/list/conditional profiles; separate NumPy 2.4.0 eager elementwise/indexed-loop/outer/transpose profile with typed roots | Compose profiles; selected scientific library calls, streams, state/configuration and broader collection contracts | Dynamic dispatch, arbitrary mutation and general Python/BLAS execution |
| Rust | Automatic scalar functions; extracted multi-module applications with authored bridges | Reusable bridge generation for admitted structs, slices, options/results, integer conversions and real loops | Unsafe code, FFI, concurrency and unrestricted traits/generics |
| Julia | Restricted Float64 scalar functions; separate Julia 1.11.7 typed Vector/helper/indexed-loop profile | Matrix APIs, selected broadcasting/reductions and more runtime versions | Multiple dispatch, fused broadcast and BLAS/LAPACK calls each need selected semantics and bridges |
| MATLAB / Octave | Restricted scalar function files and an explicitly selected runtime | Helpers, loops, indexing, shapes and reviewed array operations | MATLAB and Octave runtime/library correspondence remain separate claims |
| C | Closed C11 double helpers, by-value structs, fixed buffers and unsigned literal-count loops; Lean access/counter/execution roots | Header/preprocessor integration, larger mutable buffers and reusable Rust buffer bridges selected from real applications | Pointer-heavy APIs, allocation, lifetime/provenance and broader C semantics |
| C++ | Planned after the C route | A selected numeric API using supported value/container operations and an inspected frontend | Templates, exceptions, object lifetime and compiler/library behavior need their own coverage |
| Fortran | Deferred candidate | Select an actual array kernel and a suitable frontend after C/array contracts are reusable | Do not assume a C or LLVM-based route already establishes Fortran source correspondence |

A parser or sampled cross-language agreement is not a new source-equivalence
proof. Retain declared frontend/compiler/runtime trust boundaries. Exact dtype
promotions, integer overflow rules, indexing, aliasing, rounding and reduction
order belong to the bridge. A theorem about FLARE's matrix algorithm does not
verify an arbitrary NumPy, BLAS or LAPACK call.

## 13. Cover more arithmetic models

### Deliver

- Add explicit binary32 and mixed binary32/binary64 semantics, promotion/narrowing
  rules and reusable error propagation. Formats are independent capabilities;
  parsed source types or a tool's format flag do not establish their Lean bridge.
- Add explicit fused multiply-add as a distinct source operation and rounding
  contract. Keep existing separately rounded schedules intact. Unrequested
  reassociation or optimization remains outside the original-source claim.
- Prioritize square root, then selected elementary functions from application
  needs. Distinguish mathematical function bounds, rounded primitive semantics
  and a particular platform/library implementation. Connect any analyzer models
  through the appropriate contracts and exceptional-value domains.

### Completion criteria

An actual mixed-precision application and an explicit-FMA kernel have checked
source/rounding bridges and numerical roots. A selected function-using application
certifies against the specific primitive or implementation contract it executes.
Wrong formats, hidden FMA, casts, domains and library versions have negative
controls. Compare an alternative schedule only as a separate reviewed artifact.

## 14. Make automated delivery and maintenance routine

### Deliver

- Add a maintained counterexample request/result path alongside certification.
  Freeze an admissible witness, actual source-model execution, independent exact
  reference and violated requirement in one Lean root. Counterexample search may
  use external tools; a rejected proof or sampled failure is not that certificate.
- Route obligations using declared source/property/arithmetic capabilities and
  explicit resource limits. Retain every attempt, its actual accepted claim and
  failure stage. Alternative producers cannot silently change the requirement.
- Produce actionable unresolved reports with source locations, missing premises
  or unsupported features. Keep authored proof work separate from automatic
  coverage and replay time; measure engineer intervention on unfamiliar code.
- Exercise versioned setup, skill/provider compatibility, artifact-location
  agreement, portable proof bundles, verified Rust delivery and incremental
  rechecking after source/library/toolchain changes.

### Completion criteria

Maintain at least three held-out public application cases from different domains,
including a new source language and a scientific-array library. Preserve their
original sources and requirements; record needed assistance before incorporating
new regressions. An engineer reproduces a positive result and a Lean counterexample
from the report without session history.

Fresh-machine runs start with no Lean/analyzers/translators installed and obtain
only the selected route's tools. Test Linux x86-64 and ARM64 and the supported
macOS routes separately; a Linux VM does not establish native macOS tool support.
Cold replay needs no producers, translators, source execution or LLM, while retaining
required proof-library dependencies. A compatible change rechecks affected
results; an incompatible semantic change is reported instead of reusing stale
proofs. Publish coverage, setup/checking costs and known open obligations.

## Future considerations

Keep these recommendations for future iterations. They complement the planned
capabilities and do not require every new integration to wait for a separate
evaluation project.

- **Further evidence integration and cost.** Extend the shared enclosure engine
  with useful division/order/recurrence reasoning, external branch-local summaries
  and selected Frama-C/WP/Why3 typed-memory or numerical evidence. Inspect pinned
  Coq/Flocq, VCFloat2, LAProof or PVS output before choosing an importer or proved
  inference. Reduce repeated expression/proof bytes and check costs; the present
  power rules add coverage without a general speed or size improvement. Keep
  FPTaylor's unresolved regularized-reciprocal candidate and unchanged engineering
  budget as a correlation target. Recheck actual candidates, corrupt rules and
  side conditions, and preserve producer-free replay for every extension.
- **Further scaling and profile composition.** Extend the current
  [source-backed workloads](scaling.md) toward 10,000 arithmetic operations,
  array dimensions 2/4/8/16/32 and 1/4/16 composed components, where contracts
  permit. Add input streams, time-varying invariants, typed profile composition
  and source-local failure diagnostics. Measure source admission, inference,
  checking, cold replay, warm reuse, peak memory and proof bytes separately.
  Keep the 128-update Kalman budgets unchanged while improving correlation-aware
  inference. Larger exports alone do not establish source-program certification.
- **Broader collection/source support.** Extend the current closed NumPy/Julia
  profiles to selected reductions, richer broadcasting, views/strides and actual
  BLAS/LAPACK paths only with their dtype, schedule, aliasing and implementation
  contracts. Add MATLAB-compatible arrays and reusable Rust slice/state/error
  bridge generation from retained application gaps. Larger dense filters remain
  separate from the current two-state single-call certificate.
- **First-class counterexample delivery.** Extend the authored counterexample
  route into ordinary request/report/replay support, as proposed in milestone 14.
  Require an admissible witness and a Lean-checked violation of the original
  requirement; proof rejection and sampled failures remain different outcomes.
- **Held-out public applications.** Evaluate unfamiliar applications from several
  domains before turning them into regressions. Freeze source and requirements,
  record the first attempt and needed assistance, and include independent engineer
  reproduction. This tests applicability beyond examples used to develop FLARE.
- **End-to-end cost comparisons.** Extend the scaling scorecard across tools and
  source languages. Measure cold setup, analysis, Lean checking, cold replay and
  warm reuse separately, alongside peak memory and artifact size. Retain failed
  and resource-exhausted attempts so comparisons reflect actual coverage.
- **Engineer intervention.** Track clarification, manual source/contract work,
  authored Lean proofs and reusable adapter changes separately from automated
  execution. Use these records to prioritize improvements that reduce effort on
  new code; fast proof replay alone does not measure usability.

## Work that accompanies every milestone

- Keep one engineer-facing skill and one final Lean certification boundary.
  Optional tools remain outside core Lake dependencies. No admitted proofs or
  additional axioms; audit the final theorem's transitive dependencies.
- Extract reusable semantics, soundness arguments and compositional contracts.
  Check FLARE/Mathlib before adding alternatives; track concrete upstream work in
  [the Mathlib guide](upstream/mathlib.md).
- Retain original source, provenance, domains, exact references, units, requirements,
  arithmetic models, tool identities and assistance records. Preserve production
  APIs and loops; keep verification drivers separate from Rust delivery.
- Maintain positive results, genuine counterexamples, checked above-budget results
  and explicit unresolved cases. Rejection tests do not increase the verified
  application count. Physical/model premises remain distinct from arithmetic error.
- Keep setup, semantic coverage and compiler/runtime trust visible. Use cold
  producer-free replay and stale-evidence controls, even when warm proof caches
  or agent-authored proofs make development faster.
