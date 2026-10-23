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
  conditional profiles. These profiles do not yet compose arbitrarily.
- Gappa, FPTaylor and PRECiSA supply candidate conclusions that are independently
  proved in Lean. Their retained Coq/PVS traces are not imported proofs. See
  [tool integration](tool-integration.md).
- Charon/Aeneas supplies fresh Rust extraction. Reviewed bridges connect the
  actual extracted API to numerical contracts, including validation, integer
  timing, errors and decisions. General application bridges still need authored
  Lean proofs.
- The scalar FilterPy GH filter, Rust IMU API and multi-module
  [planar tracker](../examples/numerics/planar/README.md) have maintained certificates
  and reusable Rust delivery examples. The planar tracker composes two scalar
  filters; it is not a dense Kalman filter.
- Fixed-shape Python list products have checked shapes, execution order and
  entrywise error bounds. NumPy/BLAS calls have no source bridge yet.
- The [conditional examples](../examples/numerics/branches/README.md) cover all four
  native/exact branch choices. The profile currently validates both arms on the
  whole domain and supports Lean delivery only.
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

1. **Scale existing reasoning and compose source profiles.** Preserve sharing,
   local contracts and real loops; support branch-local premises and counted
   loops without expanding every iteration into a flat arithmetic graph.
2. **Add C and richer scientific code.** Start with a closed C profile and a
   verification-condition route, then bridge actual array/library operations in
   Python, Julia and MATLAB-compatible code. Broaden Rust API automation alongside
   these capabilities.
3. **Reduce repeated proof work and engineering effort.** Add reusable certificate
   checking where it helps, cover additional arithmetic models, and make genuine
   counterexamples, setup, maintenance and reporting part of ordinary delivery.

Each milestone retains source, domain, independent reference and engineering
requirements. Changes to any of these create a separate reviewed case. Completion
requires a Lean root, axiom audit, frozen-source replay and rejection controls.
Setup failure, unsupported source, resource exhaustion, an unproved candidate and
a checked bound above budget remain distinct outcomes.

## Sequence

The next implementation milestone is 9.

| Milestone | User benefit | Concrete completion target |
| --- | --- | --- |
| 9. Scale proofs and compose control flow | Larger existing programs need less expansion and manual proof work | A source-backed counted loop with a parameterized contract, a larger shared graph, and branch-local proofs all certify or reach checked numerical outcomes |
| 10. C source and verification conditions | Verify common embedded and numerical C code | Two actual C functions, including a loop/buffer case, obtain Lean application roots through a reusable source/VC route |
| 11. Scientific arrays and richer language APIs | Verify ordinary scientific code without hand-rewriting it | A fixed-shape NumPy application plus an idiomatic Julia or MATLAB-compatible application obtain source bridges and numerical roots |
| 12. Shared proof evidence and inference | More tool reasoning survives into Lean at lower checking cost | A reusable rule checker or verified inference engine consumes useful evidence across two tools and a family of applications |
| 13. Precision and mathematical functions | Cover arithmetic used outside the current binary64 subset | Mixed binary32/binary64 and explicit FMA examples certify; selected elementary functions gain implementation-specific contracts |
| 14. Reliable automated delivery | Other engineers can use and maintain the workflow on unfamiliar code | Fresh-machine delivery, a first-class Lean counterexample path, and held-out applications pass the release criteria |

Milestone 9 comes first. Milestone 10 can reuse existing scalar arithmetic while
9 develops compact loop proofs. Milestone 11 builds on 9's collection/loop
contracts; its library calls may also need 10 or 13 for C, FMA or precision bridges.
Milestone 12 starts with
a measured reconstruction bottleneck from any of these routes. Milestone 13 can
progress per arithmetic feature once its semantic bridge is ready. Setup,
counterexamples and maintenance work from 14 accompanies every milestone; a
separate final integration test closes 14.

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
| Gappa / FPTaylor | Implemented scalar candidate reconstruction | Shared algebraic/interval evidence, useful correlations and larger composed obligations | 9, 12 |
| PRECiSA/PVS | Implemented scalar/terminal-conditional candidate reconstruction | Branch-local domains, incoming errors and callable summaries; retain unstable-flow obligations | 9, 12 |
| Charon/Aeneas | Implemented Rust extraction with authored application bridges | Generate bridges for admitted structs, state, loops and result types; preserve actual APIs and separate drivers | 9, 11, 14 |
| Frama-C/WP / Why3 | Planned | C source contracts and exported verification tasks, connected to the original computation and reconstructed/checked in Lean | 10, 12 |
| CBMC | Proposed addition | Bounded integer/FP/memory counterexample candidates and execution paths, rechecked against the admitted source model in Lean | 10, 14 |
| VST / Coq / Flocq / VCFloat2 / LAProof | Reference workflows; no Lean importer | Reuse suitable typed evidence or implement the needed inference and semantic bridges in Lean; select a numerical or memory obligation first | 10, 12, 13 |

Frama-C/WP produces verification conditions from C contracts; Why3 can export
prover tasks through drivers. These are possible integration points, not existing
Lean adapters. See the [Frama-C documentation](https://frama-c.com/index.html)
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
| Python | Restricted scalar functions/helpers/loops, selected methods, fixed-list products, one terminal conditional | Compose these profiles; counted loops, branch-local arithmetic, state/configuration and fixed-shape NumPy calls | Dynamic dispatch, arbitrary mutation and general Python execution |
| Rust | Automatic scalar functions; extracted multi-module applications with authored bridges | Reusable bridge generation for admitted structs, slices, options/results, integer conversions and real loops | Unsafe code, FFI, concurrency and unrestricted traits/generics |
| Julia | Restricted Float64 scalar functions and tuple results | Typed scalar helpers, counted loops and explicit array/reduction schedules | Multiple dispatch, broadcasting and BLAS/LAPACK calls each need selected semantics and bridges |
| MATLAB / Octave | Restricted scalar function files and an explicitly selected runtime | Helpers, loops, indexing, shapes and reviewed array operations | MATLAB and Octave runtime/library correspondence remain separate claims |
| C | Planned | Explicit binary64 scalar functions, fixed buffers, structs, counted loops and contracts under a selected compiler/arithmetic profile | Pointer-heavy APIs, allocation and broader C semantics |
| C++ | Planned after the C route | A selected numeric API using supported value/container operations and an inspected frontend | Templates, exceptions, object lifetime and compiler/library behavior need their own coverage |
| Fortran | Deferred candidate | Select an actual array kernel and a suitable frontend after C/array contracts are reusable | Do not assume a C or LLVM-based route already establishes Fortran source correspondence |

A parser or sampled cross-language agreement is not a new source-equivalence
proof. Retain declared frontend/compiler/runtime trust boundaries. Exact dtype
promotions, integer overflow rules, indexing, aliasing, rounding and reduction
order belong to the bridge. A theorem about FLARE's matrix algorithm does not
verify an arbitrary NumPy, BLAS or LAPACK call.

## 9. Scale proofs and compose control flow

### Deliver

- Preserve shared expressions and helper boundaries through source models,
  inference and Lean checking. Generate local contracts and compact proof
  modules instead of repeatedly expanding transitive expressions.
- Compose the current scalar, method, array and conditional profiles through
  explicit typed contracts. Add source locations for unsupported constructs and
  failed obligations; a broader intermediate representation alone is not a proof.
- Prove branch-local domains and numerical premises. A safe division in one arm
  must not require a nonzero denominator in an unreachable arm. Use checked guard
  implications and local contracts to avoid enumerating every global path.
- Admit actual counted source loops with supplied or inferred invariants and
  incoming-error recurrences. Treat inferred invariants as candidates checked in
  Lean. Preserve the production loop and generate a separate verification driver.
- Improve correlations and allowance quality independently of proof speed. Keep
  the 128-update Kalman budgets unchanged while trying tighter reusable inference.
  An above-budget theorem is a numerical result, not evidence of an attained bug.

### Scaling scorecard

Measure source admission, inference, Lean checking, cold replay and warm reuse
separately. Record peak memory, proof/source bytes, unique operations, call edges,
path splits, authored proof work and final outcome on a pinned runner. Freeze
resource limits before comparing implementations; report all exhausted runs.

| Axis | Planned progression | What must be demonstrated |
| --- | --- | --- |
| Repeated calls | 1, 16, 128, 1,024 iterations | A parameterized loop proof whose body does not grow with the horizon; no reset of incoming error |
| Shared arithmetic graph | About 100, 1,000, 10,000 unique operations | Source-backed results, sharing retained, measured proof/checking growth |
| Array dimension | 2, 4, 8, 16, then 32 where contracts permit | Fixed accumulation order, valid shapes and honest dimension/algorithm limits |
| Module composition | 1, 4, 16 components | Local contract reuse; a caller edit invalidates affected dependents and preserves unrelated proofs |

These are proposed targets, including sizes beyond current frontend/theorem
limits; the progression continues across milestones 9–13. Raising an admission
limit alone does not meet them. Keep large exported
graphs marked as probes until the actual source bridge and application root exist.

### Completion criteria

A counted loop from actual source has a parameterized contract instantiated at
1, 16, 128 and 1,024 calls, with checked numerical outcomes under unchanged
requirements. A source-backed application with at least 1,000 unique arithmetic
operations completes within the recorded resource limits. A second family uses
the same mechanisms, including a branch-local denominator obligation.

Cold replay uses no producers or compiled helper cache. Maintenance tests change
one caller or component, preserve unaffected contracts and reject a false
recurrence, missing path or stale dependency. Publish the scorecard; do not infer
scaling from a larger timeout or a successful graph export.

## 10. Add C source and verification conditions

### Deliver

- Choose one retained C numerical API and a closed language profile. Start with
  explicit `double`, scalar helpers, fixed buffers, structs and counted loops.
  Record compiler options, floating-point contraction/rounding, integer widths,
  casts, aliasing and defined-behavior conditions.
- Evaluate Frama-C/WP and Why3 on its actual source/VC output. Reuse current scalar
  checking or add a supported evidence checker; preserve the link from every task
  to the selected source, contract and caller. Keep memory/undefined-behavior
  obligations alongside the numerical ones.
- Use CBMC where a bounded execution or counterexample search addresses a real
  gap. Reconstruct witnesses in Lean; leave unsupported positive proof evidence
  unresolved. VST/VCFloat2 remain alternative routes when their models fit better.
- Add optional reusable Rust delivery from the original C API, with separate
  drivers and checked state/return correspondence. An extracted arithmetic
  surrogate does not replace the production implementation.

### Completion criteria

Two C functions use one reusable route: a scalar kernel and a loop with fixed
buffer/state behavior. Each has an original-source bridge, closed numerical and
relevant memory/defined-behavior premises, a Lean root and replay. At least one
receives a verified Rust port when requested. Incorrect aliasing, casts, loop
bounds and operation order have rejection controls. A bounded witness, if used,
gets its own Lean counterexample root.

Broader C++, pointer-heavy C and Fortran are separate follow-ups selected from
applications; completing this profile does not silently admit them.

## 11. Verify scientific arrays and richer APIs

### Deliver

- Connect a fixed-shape NumPy application to selected dtype, shape, indexing,
  broadcasting/reduction and aliasing semantics. Start with operations whose
  execution schedules can be stated and checked. Inspect the actual library path.
- Generalize reusable array/loop contracts for Julia and MATLAB-compatible source;
  first select one of those languages using an application gap. Retain explicit
  runtime distinctions and close shape/indexing/state obligations at the caller.
- Verify a full dense covariance/correction application from its actual source,
  beyond the current independent-axis planar tracker. Connect existing exported
  graphs only after their source mapping is established. Reuse FLARE's matrix
  results where the algorithm, dimensions and operation order match.
- Broaden generated source bridges and Rust deliveries to preserve collections,
  configuration, state, errors and loops. Review solver/factorization adaptations
  separately from the original implementation's contract.

### Completion criteria

A NumPy application and an idiomatic Julia or MATLAB-compatible application have
source bridges and Lean application roots using reusable array contracts. Include
at least one application outside filtering. The dense covariance/correction case
has a source-program certificate rather than a candidate graph alone. Required
Rust deliveries preserve the real API and receive their own extracted roots.

Tests change shapes, dtype/promotions, aliasing, indices and reduction schedules.
A BLAS/LAPACK or parallel reduction path needs its own reviewed implementation
contract; an agreement sample or library name cannot supply that bridge.

## 12. Share proof evidence and verified inference

### Deliver

- Profile repeated reconstruction costs and missing reasoning in existing Gappa,
  FPTaylor and PRECiSA runs and the new C/array routes. Choose a useful common
  subset: for example interval, polynomial, order, rounding or recurrence rules.
- Implement typed evidence parsing with explicit semantic interpretations and
  Lean soundness proofs for every accepted rule, or implement the needed
  inference in Lean with proved soundness. Reuse existing math rather than adding
  application-specific bounds or manually copying foreign theorems.
- Connect useful output from at least two tools to that checker. Coq/Flocq,
  VCFloat2, LAProof and PVS may supply evidence or guide an implementation;
  inspecting their actual output precedes choosing an importer. Foreign theorem
  names, solver verdicts and unchecked transformation premises are insufficient.

### Completion criteria

Two tools and a family of applications use the same proved rule vocabulary or
inference engine. Compare accepted allowances, checking time, memory and proof
size against current reconstruction on unchanged requests. Show a measured
coverage or cost benefit. Corrupt a rule, rounding mode, rewrite and side condition;
all must fail the intended check. Saved Lean evidence replays without the tools.

A universal Coq/PVS/SMT proof importer is not required. Keep candidate
reconstruction where it is simpler and effective.

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
