# Numerical application verification

FLARE hosts one engineer-facing [verify-numerics skill](../skills/verify-numerics/SKILL.md)
and its separately invocable [CLI](../scripts/certify_numerics.py). The proof
library remains one Lake project: reusable native contracts live in
`Flare.Binary64.Pipeline`, alongside the existing scalar and matrix results.
Optional analysis and extraction tools are provider tooling, not dependencies
of the core Lean library.

## Install and use

Start with the [skill user guide](../README.md) for a FilterPy example using
the skill's full GitHub URL, followed by optional installation. The agent can
read and follow the skill without registering it in a skill directory. Agents
obtain missing tools and build the provider as needed; reading or installing
the skill alone does not do either. For a manual provider build, follow the
[development guide](development.md). Shared Lake caching is optional; the CLI
inherits the caller's settings.

Standard GitHub/skills CLI installations can contain only the skill folder.
The agent locates or obtains a complete FLARE provider checkout separately and
keeps it in a shared user cache. The repository's
[development installer](development.md#work-on-the-skill-locally) instead links
an existing checkout. Neither method installs the Lean toolchain or builds FLARE
by itself; the skill directs the agent through that setup when first needed.

After agreeing on the verification directory, invoke the provider from any
application directory by absolute path:

```sh
export FLARE_ROOT=/absolute/path/to/flare-lean
export FLARE_VERIFICATION_DIR=/agreed/path/to/verification
python3 "$FLARE_ROOT/scripts/certify_numerics.py" capabilities
python3 "$FLARE_ROOT/scripts/certify_numerics.py" plan \
  --request "$FLARE_VERIFICATION_DIR/request.json"
python3 "$FLARE_ROOT/scripts/certify_numerics.py" run \
  --request "$FLARE_VERIFICATION_DIR/request.json" --out "$FLARE_VERIFICATION_DIR/certificate"
python3 "$FLARE_ROOT/scripts/certify_numerics.py" replay \
  --run "$FLARE_VERIFICATION_DIR/certificate" --out "$FLARE_VERIFICATION_DIR/replay"
```

[Request, runtime and optional Rust configuration](../skills/verify-numerics/references/source-to-rust.md)
are maintained with the skill. The default `lean` target needs no Rust tools.
The `rust-aeneas` target produces or retains Rust source, performs fresh
Charon/Aeneas extraction, and includes its actual return in the Lean theorem.
An explicit Rust port may supply a saved Lean equivalence proof; its actual
extracted return still has to equal the source kernel under the root's axiom audit.
`tools/numerics/aeneas-revisions.json` records the compatible experimental Float
fork. The skill's [tool-setup guide](../skills/verify-numerics/references/tool-setup.md)
directs agents to obtain/build missing tools and the compiled model in a shared
user cache, then check an extraction/proof preflight. There is no bundled
one-command bootstrap installer.

The agent confirms verification and Rust delivery locations before creating
application artifacts, reusing any paths already supplied by the user. Disposable
application work goes under the agreed verification directory's `.cache/`;
final proofs/certificates remain outside it. A requested Rust port preserves the
original API, state and loops. For repeated-call certificates, a separate loop
driver states the verification horizon; unrolling remains internal to the model
or proof. The CLI's automatic straight-line Rust emitter is a checker aid, not
that reusable delivery.

## What completion means

One named root, `Workflow.Certificate.certificate`, quantifies over the original
finite binary64 inputs and supplied domain. It proves output finiteness and
error against the independent exact specification, using only Lean-checked
numerical facts. A successful certificate includes a proved comparison with
each requested engineering budget. Rust delivery adds the actual extracted
return relation. A separate generated checker ascribes the expected root type
and audits its transitive axioms; only the standard project allowlist is accepted.

The parser/source-model mapping, runtime fidelity and hardware/compiler behavior
remain declared trust boundaries. Rust extraction adds Charon/Aeneas and its
Float model. Bit-pattern diagnostics compare actual source execution with the
model, and Rust debug/release when requested; samples do not prove interpreter
or compiler correctness. Input ranges and units require engineering review.
Physical/model uncertainty, arbitrary libraries, branches and unbounded
repeated-call invariants are outside the automatic certificate. Python local
helpers and bounded literal-tuple loops can be lowered and checked against an
independently specified exact two-state fold. Every intermediate error is carried
through the whole horizon. General dynamic iteration remains unsupported.

The separate `python_arrays` profile admits fixed-shape built-in list products:
matrix-vector prediction, dot products and dense matrix multiplication with
explicit ascending loops. The root quantifies over Lean array inputs, checks
the input shape guard, proves fresh output shape and finiteness, and connects
the actual operation order to `Matrix.Dense.multiply` through
`Matrix.OrderedProduct.multiply_eq`. Entrywise bounds use the same numerical
validator; an independent exact real matrix expression supplies the reference.
The [array workflow guide](../skills/verify-numerics/references/arrays.md) gives
the shape configuration, limits and maintained examples. Input lists are
read-only; NumPy/BLAS and automatic array Rust delivery need further bridges.

An explicit `python_method` binding also admits a narrow class-method subset:
two scalar state fields, fixed binary64 attributes, `None`-default gains and a
frozen observation horizon. The selected original body is lowered and used for
diagnostics. Initialization, construction and dispatch remain caller premises;
the report records the binding and this conditional scope. See the skill's
request reference for the admitted forms and configuration.

`result.json` distinguishes proposed and checked bounds. `certified` requires
the Lean root, runtime diagnostics and budgets. `budget_not_met` retains a
checked allowance that exceeds the request; it does not establish a numerical
bug. `unresolved` retains the failing stage and command logs. Missing runtimes,
analysis limitations, proof failures and timeouts require different remedies.

Saved-proof `replay` recompiles the frozen Lean sources and reconstructs the
source/specification and expected root check. It requires no producer, LLM,
source runtime or foreign checker. Rust replay still uses the compiled Aeneas
Lean model. The original run retains diagnostic evidence; replay preserves its
status and does not rerun diagnostics. `audit` checks identity/freshness only.
Artifacts are evidence records, not signed attestations or proof substitutes.
The CLI's `report.md` is part of the frozen evidence. Write any supplemental
engineering report outside the sealed run directories, under the agreed
verification directory, so adding reproduction commands or commentary does not
invalidate their recorded identities.

FLARE's maintained benchmark outputs and legacy local tool installations live
under ignored `.cache/numerics-generated/` in the provider checkout. This is not
an application-output default; new shared tool downloads use the user cache.
Moving saved runs preserves their frozen records;
historical logs still show their original paths. If the compiled Aeneas model
also moved, pass `replay --aeneas-lean-lib /new/path/to/compiled/model`. Replay
requires its file hashes to match the recorded model and records the selected
location without modifying the original evidence.

## FilterPy example

The [README walkthrough](../README.md#example-verify-a-filterpy-function) uses
FilterPy revision `3b51149ebcff0401ff1e10bf08ffca7b6bbc4a33`. It checks the actual
scalar `GHFilter.update` body over eight calls, with `dt = 0.125`, `g = 0.5`,
`h = 0.125` and omitted gain overrides. Initial position and each independent
measurement lie in `[-10, 10]` meters; initial velocity lies in `[-2, 2]`
meters/second. The reference is an independent real recurrence on those inputs.

Both Python and the reusable Rust port were certified and replayed with these
exact absolute allowances:

| Output | Checked allowance | Budget |
| --- | --- | --- |
| Position | `857/35184372088832` meters | `1e-6` meters |
| Velocity | `673/17592186044416` meters/second | `1e-6` meters/second |

The entry theorem is `Workflow.Certificate.certificate`. The README rounds the
bounds upward for display.

The Python certificate assumes ordinary scalar instances with the configured
fields; construction, module initialization and dynamic dispatch remain caller
premises. Source/model admission and runtime/compiler/hardware fidelity remain
trust boundaries. Rust adds Charon/Aeneas translation and its Float model. The
Rust bridge covers constructor and full update-state correspondence, including
optional gain behavior; a separate loop driver supplies the finite horizon.
Sampled API/state tests supplement that proof. Neither route certifies arrays,
arbitrary horizons or physical tracking accuracy.

## Kalman counterexample

The README's standalone `posterior_variance` is the scalar compact update
`(1 - p / (p + r)) * p`, with observation coefficient one. The failure fixture
comes from `cancellationChecks` in the source Kalman worktree's
`Kalman/Tests/FloatImplementations.lean`; its exact-positive reference is in
`Kalman/Tests/Specification.lean`. Source hashes and the scalar adaptation are
recorded in the [extraction manifest](extraction-manifest.json). This example
covers the displayed scalar snippet, without importing the full filter.

At original binary64 inputs `p = 1`, `r = 2^-54` (word
`0x3c90000000000000`), the snippet returns zero. The independent real posterior
is `p * r / (p + r) = 1 / (2^54 + 1) > 0`. These inputs satisfy the requested
ranges, so this refutes strict positivity on that domain.

The [maintained regression](../scripts/test_numerics_counterexamples.py) admits
[the actual Python snippet](../examples/numerics/naive_covariance.py), generates
its operation-ordered Lean kernel and proves `NaiveCovarianceFailure.failure`.
The root includes the finite input/domain conditions, zero interpreted native
output and positive exact reference. `decide +kernel` checks the closed native
execution; no `native_decide` or additional numerical axiom is used. Its
transitive axiom audit accepts only `propext`, `Classical.choice` and `Quot.sound`.
The regression also replays the saved source and rejects a false output claim.
The shared [authored argument](../scripts/numerics/counterexample.py) also supplies
the downloadable README evidence.

```sh
FLARE_NUMERICS_INTEGRATION=1 python3 -m unittest discover \
  -s scripts -p test_numerics_counterexamples.py -v
```

This is an authored Lean counterexample route, with a named refutation theorem
and an engineering report. The automatic error-bound CLI still reports
`certified`, `budget_not_met` or `unresolved`; it does not emit a counterexample
status or infer a bug from a rejected proof. The source/frontend and native
runtime trust boundaries described above still apply.

## Replay the README examples

Open a successful `main` run of
[Lean CI](https://github.com/duckki/flare-lean/actions/workflows/ci.yml) and download
the **readme-evidence** artifact from its Artifacts section. GitHub requires
[sign-in and repository read access](https://docs.github.com/en/actions/how-tos/manage-workflow-runs/download-workflow-artifacts).
The artifact is retained for 30 days; it can also be regenerated locally.

Extract it into a directory such as `/absolute/path/to/readme-evidence`. Its
`manifest.json` records the FLARE `provider_revision`, the pinned FilterPy
revision, dependency hashes and evidence-file hashes. Use a FLARE checkout at
that provider revision and [build it](development.md#build-and-check). Then,
from that checkout, check both saved proofs with one command:

```sh
python3 scripts/readme_evidence.py replay \
  --bundle /absolute/path/to/readme-evidence \
  --out .cache/numerics-generated/readme-replay
```

The output directory must be new and outside the frozen bundle. Success reports
`"status": "replayed"`, with `Workflow.Certificate.certificate` for FilterPy and
`NaiveCovarianceFailure.failure` for the counterexample. Replay verifies file
identities, checks that the saved source and contract match the examples, and
recompiles both Lean roots with their transitive axiom audits. It needs Python
and the built Lean library, without FilterPy dependencies or external numerical
tools. Original sampled runtime diagnostics stay in `filterpy/`; replay checks
the saved proofs rather than rerunning those diagnostics.

The bundle includes `filterpy/report.md`, `naive-covariance/report.md`, frozen
sources, Lean proofs, command logs and FilterPy's MIT license. It covers the
two Lean examples; optional Rust-port evidence is separate.

To generate fresh evidence from the pinned FilterPy checkout in the README:

```sh
python3 scripts/readme_evidence.py generate \
  --filterpy /absolute/path/to/filterpy \
  --out .cache/numerics-generated/readme-evidence
```

Generation checks source and license hashes, certifies the original scalar
method body, runs source/model diagnostics and checks the counterexample. CI
then runs the replay command above before uploading the bundle. The maintained
[request template](../benchmarks/numerics/filterpy-gh-request.json) supplies the
same eight-update contract; the generator binds its source to the selected checkout.

## Tool-assisted proofs

The automatic backend currently uses an untrusted rational producer plus FLARE
lemmas. A request can instead supply a saved authored Lean accuracy proof and
optional specification identity. This provides a path for reconstructing useful
external arguments without trusting a printed bound or foreign theorem. See
[Lean conversion](../skills/verify-numerics/references/lean-conversion.md).

Gappa and FPTaylor have [registered producer adapters](tool-integration.md) with
shared source setup, capability records, bounded execution and evidence tied to
the frozen source/contract. Their candidate conclusions feed reusable scalar
validation: Lean proves Gappa's queried dyadic bound or FPTaylor's actual parsed
bound. A looser engineering budget cannot replace an unproved candidate.
Gappa's Coq trace is retained rather than imported. An adapter may also generate
a Lean accuracy module for the same typed root check.

For graphs of at most 32 IR nodes, the default producer automatically tries
scalar refinement when compositional analysis misses a budget or loses a positive
divisor floor. Exact rational proposals, polynomial rewrites and input splits
are checked using native nearest-rounding theorems and Mathlib's interval tactic.
This closes the unchanged `2^-51` mean-update target and tiny-gain family. See the
[validator limits](tool-integration.md#reusable-scalar-validation).

PRECiSA and other tools can supply further adapters. Choose from the installed
version's supported arithmetic model, source constructs and output detail.
Coq/PVS/HOL success alone never closes a numerical Lean premise.

The [integration strategy](roadmap.md#integration-strategy) prioritizes shared tool
adapters, reusable evidence import/checking and verified Lean inference. Shared
orchestration and scalar reconstruction are implemented for the core set;
additional tools follow the loop, matrix and application milestones. Keep one
Lean completion boundary and add mathematical
support for those mechanisms and their semantic bridges.

## Maintained validation and next work

The [benchmark guide](../benchmarks/numerics/README.md) describes supported
scenarios, rejection controls and known limitations. CI runs default scenarios
and fresh Lean controls; optional Julia/Octave/Rust tools are tested separately.
These tests exercise the skill's executable path and packaging. They are not
an independent evaluation of agent behavior on new engineering tasks.

The [milestone plan](roadmap.md) defines the next capabilities and their
completion criteria: reproducible feedback cases, shared tool integration,
reusable scalar inference, composable loops, vectors/matrices, complete
application behavior and reusable Rust delivery. Keep the current scenarios as
baselines and use feedback to prioritize additional applications.

## Scaling beyond a single kernel

`make numerics-scale` exercises the maintained progression in
`benchmarks/numerics/scale.json`: 1/4/8/16/48/128 Kalman updates, 1/4/16/48 IMU
motion updates, the original 48-event Rust application proof bundle, and the original
relative/global four-state covariance/correction graphs (7,758/7,761 operations).
The [benchmark guide](../benchmarks/numerics/README.md) defines the domains,
capability boundaries and recorded proof-stage timings. CI runs a smaller subset.

The bounded Python fixtures preserve the source worktree's scalar helpers and
add explicit horizons with independent original observation inputs. The IMU loop
uses an original Float `dt` shared across its steps; it does not certify the
original UInt64 timestamp conversion, error-return branches or rounded decisions.
Those are checked separately by the [Rust application proof bundle](../skills/verify-numerics/references/rust-applications.md),
including all public API error exits and an exact-reference uncertain region.
Select its optional scale case with the configured Charon/Aeneas tools.
The large graph probes report untrusted candidates, without a Lean root or
universal source bridge. They are not equivalent to completed application proofs.

The producer now uses the already-proved `native_ideal_refine` rule when native
range plus accumulated error gives a smaller exact magnitude bound. Lean checks
every use. This avoids artificial growth in repeated covariance calculations;
large-graph normalization and lost correlations still limit useful bounds.
The scalar refinement route removes those particular grid losses for small
supported graphs. The helper-composition route preserves shared native/exact
functions and carries errors through larger Python folds. It certifies the
16/48-update Kalman cases; 128 updates reach a checked result above the mean
budget. See [helper composition](tool-integration.md#helper-and-loop-composition)
for limits, explicit contract reuse and fresh replay.
The nonlinear Kalman profiles use checked helper contracts rather than expanding
the entire trajectory inside each proof. Resource failures remain unresolved
and no longer match the completed 16/48-update scale cases.
