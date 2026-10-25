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
  admission and numerical validation. Python additionally has closed original module selection, selected scalar
  methods, helpers, bounded loops and separate fixed-list array and terminal
  conditional profiles. A compact two-state counted-loop profile retains a
  uniform invariant across all natural counts, with selected roots through 1,024.
  These profiles do not yet compose arbitrarily.
- Closed C11 double APIs admit scalar helpers, by-value structs, fixed buffers
  and unsigned literal-count loops. Source-derived access/counter conditions and
  typed-cell heap execution join numerical accuracy in one Lean root. Scalar
  Rust delivery retains the real API; buffer delivery is currently Lean-only.
  Physical object validity and compiler/source mapping remain explicit premises
  and trust boundaries. See the [C guide](sources/c-verification.md).
- A separate [explicit-FMA Python profile](arithmetic/explicit-fma.md) certifies sensor
  calibration, cancellation residuals, fused accumulation and reciprocal/FMA
  composition with one final rounding per `math.fma`. Its native rounding proof,
  numerical roots and cold replay are checked. It currently uses `lean-flare`
  and Lean delivery. A [square-root source bridge](arithmetic/square-root.md) now certifies
  standard deviation, regularized norms, normalized residuals and nested roots
  with checked endpoint/perturbation rules and explicit runtime/libm contracts.
  A [mixed storage profile](arithmetic/mixed-precision.md) adds binary32 narrowing and exact
  promotion around binary64 computation, including repeated storage and division.
  Shared format/packing/rounding inference proves both widths. Binary32 arithmetic,
  arbitrary dtype promotions and additional elementary functions remain open.
- Gappa, FPTaylor and PRECiSA supply candidate conclusions that are independently
  proved in Lean. Their retained Coq/PVS traces are not imported proofs. See
  [tool integration](integration/tool-integration.md). Gappa and FPTaylor share a proved
  exact rational enclosure engine with power correlations and checked leaf
  premises. Square/quartic families and positive regularized denominators have
  maintained cases; foreign proof traces remain untrusted. See
  [shared proof evidence](integration/proof-evidence.md).
- A typed product-evidence path checks rational annotations against native
  semantics without expanding shared products into high-degree polynomials. It
  certifies degree-32/256 chains and exact-zero products, with incoming errors
  and gradual underflow retained. See the [examples](../examples/numerics/typed-evidence/README.md).
- Charon/Aeneas supplies fresh Rust extraction. Reviewed bridges connect the
  actual extracted API to numerical contracts, including validation, integer
  timing, errors and decisions. General application bridges still need authored
  Lean proofs.
- The scalar FilterPy GH filter, Rust IMU API and multi-module
  [planar tracker](../examples/numerics/planar/README.md) have maintained certificates
  and reusable Rust delivery examples. The planar tracker composes two scalar
  filters; it is not a dense Kalman filter.
- Fixed-shape Python list products have checked shapes, execution order and
  entrywise error bounds. The separate [scientific profile](sources/scientific-arrays.md)
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
  cache. See the [scaling guide](integration/scaling.md) for measurements and limits.
- The 16/48-update Kalman cases certify; 128 updates reach a checked
  `budget_not_met` result with unchanged budgets. Large covariance/correction
  graphs remain analysis probes without source-program certificates. See the
  [scale guide](../benchmarks/numerics/README.md#increasing-scale).
- The [counterexample request route](integration/counterexamples.md) checks supplied scalar
  witnesses for strict-positivity and attained-error failures. The README's
  covariance example uses its generated Lean root, report and cold replay;
  selected CBMC 6.11.0 search proposes strict-positivity witnesses that use the
  same Lean checker. Closed Python module and C++ header selections have retained
  public cases. Further properties/profiles remain open.

These are scoped capabilities, not support for arbitrary programs in each
language. Independent engineer reproduction remains a sharing follow-up; current
regressions and VM experiments establish automated reproduction of selected cases.

## Next priorities

1. **Extend reusable checked numerical inference.** Broaden typed operation
   evidence beyond products, retain tighter rounding/division correlations,
   try alternative checked backends for unproved candidates and reduce checking
   cost on larger shared graphs. The [integration decisions](evaluation/numerical-integrations.md)
   select native Lean annotation/exact-operation checking and reject the evaluated
   LeanCert/Daisy production routes for their tested scopes.
2. **Broaden arithmetic and scientific coverage.** Extend mixed precision beyond
   storage boundaries, add binary32 arithmetic and select further library/function
   contracts from retained applications.
3. **Broaden Rust correspondence-proof generation.** Generate further bridges
   from admitted source profiles while preserving real APIs and loops.

Each milestone retains source, domain, independent reference and engineering
requirements. Changes to any of these create a separate reviewed case. Completion
requires a Lean root, axiom audit, frozen-source replay and rejection controls.
Setup failure, unsupported source, resource exhaustion, an unproved candidate and
a checked bound above budget remain distinct outcomes.

The [delivery evaluation](evaluation/delivery-evaluation.md) records completed
automated setup, public application checks, counterexample delivery and
maintenance. Independent engineer reproduction is tracked below as a follow-up.

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
| [LeanCert Core](https://github.com/alerad/leancert) | Evaluated; direct checked-API backend rejected for the tested scalar/module scope | Revisit for a concrete transcendental gap after module compatibility and kernel checking are established | Future backend evaluation |
| [Daisy](https://github.com/malyzajko/daisy) | Conservative candidate controls passed; exact-input candidates unresolved; scalar production adapter rejected | Revisit tighter bounds after reusable rounding/correlation inference, or select a modular/array gap with its correspondence obligations | Future producer evaluation |
| [FloVer](https://github.com/Cactus-proj/FloVer) | Typed product annotations implemented natively in Lean; no foreign certificate importer | Extend the checked vocabulary and shared facts to selected additional operations; discharge every semantic premise | Future evidence coverage |
| [VCFloat2](https://github.com/VeriNum/vcfloat) | Compositional exact-zero multiplication inference implemented using FLARE proofs | Select further exact-operation rules, native binary32 arithmetic/casts or specified functions; prove their native bridges | Future inference coverage |
| PRECiSA/PVS | Implemented scalar/terminal-conditional candidate reconstruction using the common scalar proof path | External branch-local domains, incoming errors and callable summaries; retain unstable-flow obligations | Future evidence work |
| Charon/Aeneas | Implemented scalar/application/fixed-array extraction with authored bridges | Generate further bridges for admitted structs, state, loops and result types; preserve actual APIs and separate drivers | Future bridge coverage |
| Frama-C/WP / Why3 | Pinned source/ACSL/task export evaluated; no Lean proof importer | Translate selected application contracts and check useful typed-memory/FP evidence against the admitted source model | Future evidence work |
| CBMC | Pinned 6.11.0 scalar strict-positivity witness search and ordinary Lean rechecking | Further properties, bounded integer/memory paths and source profiles; never treat no-witness as a proof | Future counterexample work |
| VST / Coq / Flocq / LAProof | Reference workflows; no Lean importer | Reuse suitable typed evidence or implement the needed inference and semantic bridges in Lean; select a numerical or memory obligation first | Future evidence work |

Frama-C/WP 31.0 and Why3 1.8.2 task output was inspected on the retained C API.
The [C guide](sources/c-verification.md) describes the export utility and why the current
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

## Future integration evaluation protocol

- Select a retained application gap and pin the tool, dependencies, supported
  arithmetic model and work limits. Freeze source, domain, independent reference
  and engineering budget. When comparing proof backends, also fix the candidate
  bound; every producer's actual conclusion remains its own proof target.
- Prototype through the existing adapter and generated-Lean-module interface.
  Keep candidate production independently selectable from numerical proof
  checking, so producers can share a checked backend.
- Prove the translation from FLARE's obligation to the backend's semantics.
  Preserve shared variables, correlations, rounding sites and incoming error.
  An enclosure of a real function alone does not certify its rounded source
  implementation or a particular platform library call.
- Pin optional Lean proof dependencies and include their identities in evidence,
  replay and proof-cache keys. Keep one FLARE Lake project/library and retain
  `Workflow.Certificate.certificate` as the application completion boundary,
  including requested Rust correspondence and the transitive axiom audit.
- Measure new coverage, source admission, candidate generation, Lean checking,
  cold replay, warm reuse, memory and proof bytes against the existing route.
  Record setup requirements, manual proof/adapter work and failed attempts.
- Require producer-free frozen replay and rejection controls for changed
  source/contracts/models, false bounds, malformed evidence, missing premises
  and additional axioms. Record setup/resource failures separately from
  numerical failures.
- Accept a route when it provides a demonstrated capability gain or useful
  checking-cost improvement with justified dependency and maintenance costs.
  Reject it for the evaluated scope when it fails those criteria. Record the
  bounded experiment, measurements, decision and remaining limitations in
  `docs/evaluation/`; an incomplete experiment supports no adoption claim.

The [numerical integration evaluation](evaluation/numerical-integrations.md) records
the pinned LeanCert, Daisy, FloVer-style and VCFloat2-style trials, scoped decisions,
measurements and limits. Future evaluations should target an uncovered capability;
a foreign success verdict or another adapter alone is insufficient.

## Source language and library plan

A language name is insufficient to describe support. Track source constructs,
value types, library operations, semantics, automatic/authored proof coverage,
platform and Lean/Rust delivery separately in `capabilities` and regression cases.

| Source | Current supported profile | Next scope | Later scope / separate obligation |
| --- | --- | --- | --- |
| Python | Restricted scalar/method/loop/list/conditional profiles, including closed full-module selection; separate NumPy 2.4.0 eager collection and binary32-storage/binary64-computation profiles with typed roots | Compose profiles; selected scientific library calls, streams, state/configuration and broader collection contracts | Dynamic dispatch, arbitrary mutation and general Python/BLAS execution |
| Rust | Automatic scalar functions; extracted multi-module applications with authored bridges | Reusable bridge generation for admitted structs, slices, options/results, integer conversions and real loops | Unsafe code, FFI, concurrency and unrestricted traits/generics |
| Julia | Restricted Float64 scalar functions; separate Julia 1.11.7 typed Vector/helper/indexed-loop profile | Matrix APIs, selected broadcasting/reductions and more runtime versions | Multiple dispatch, fused broadcast and BLAS/LAPACK calls each need selected semantics and bridges |
| MATLAB / Octave | Restricted scalar function files and an explicitly selected runtime | Helpers, loops, indexing, shapes and reviewed array operations | MATLAB and Octave runtime/library correspondence remain separate claims |
| C | Closed C11 double helpers, by-value structs, fixed buffers and unsigned literal-count loops; Lean access/counter/execution roots | Header/preprocessor integration, larger mutable buffers and reusable Rust buffer bridges selected from real applications | Pointer-heavy APIs, allocation, lifetime/provenance and broader C semantics |
| C++ | Closed C++20 namespace-level by-value double header functions with explicit binary64 constants, actual-header diagnostics and Lean roots | More source/library operations selected from applications | Templates, objects, exceptions, memory, loops, general preprocessing and compiler/library behavior need their own bridges |
| Fortran | Deferred candidate | Select an actual array kernel and a suitable frontend after C/array contracts are reusable | Do not assume a C or LLVM-based route already establishes Fortran source correspondence |

A parser or sampled cross-language agreement is not a new source-equivalence
proof. Retain declared frontend/compiler/runtime trust boundaries. Exact dtype
promotions, integer overflow rules, indexing, aliasing, rounding and reduction
order belong to the bridge. A theorem about FLARE's matrix algorithm does not
verify an arbitrary NumPy, BLAS or LAPACK call.

## Further arithmetic coverage

- Extend binary32 storage to native binary32 arithmetic, independent typed API
  inputs/outputs, unpaired casts and specified promotion/narrowing rules. Keep
  rounding at every original source site; dtype names alone do not prove a bridge.
- Compose selected storage, FMA, root, array and conditional profiles only with
  checked source and numerical bridges. Preserve existing separately rounded
  schedules and exceptional-value domains.
- Broaden selected primitives to other source languages, Rust delivery and
  external-producer models when retained applications require them.
- Select further elementary functions from application gaps. Separate mathematical
  bounds, rounded primitive semantics and the actual platform implementation.

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
  [source-backed workloads](integration/scaling.md) toward 10,000 arithmetic operations,
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
- **Broader counterexample delivery.** Extend ordinary scalar witness delivery
  to further source profiles, properties and inspected external search evidence.
  Require an admissible witness and a Lean-checked violation of the original
  requirement; proof rejection and sampled failures remain different outcomes.
- **Held-out public applications.** Evaluate unfamiliar applications from several
  domains before turning them into regressions. Freeze source and requirements,
  record the first attempt and needed assistance, and include independent engineer
  reproduction. This tests applicability beyond examples used to develop FLARE.
- **Independent engineer reproduction.** Have an engineer reproduce one positive
  certificate and one Lean-checked counterexample from delivered bundles without
  session history. Record the actual results and needed assistance using the
  [reproduction handoff](evaluation/independent-reproduction.md). This is a
  follow-up to the completed automated delivery milestone; agent-only runs remain
  automated evidence.
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
  [the Mathlib guide](library/mathlib.md).
- Retain original source, provenance, domains, exact references, units, requirements,
  arithmetic models, tool identities and assistance records. Preserve production
  APIs and loops; keep verification drivers separate from Rust delivery.
- Maintain positive results, genuine counterexamples, checked above-budget results
  and explicit unresolved cases. Rejection tests do not increase the verified
  application count. Physical/model premises remain distinct from arithmetic error.
- Keep setup, semantic coverage and compiler/runtime trust visible. Use cold
  producer-free replay and stale-evidence controls, even when warm proof caches
  or agent-authored proofs make development faster.
