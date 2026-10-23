---
name: verify-numerics
description: "Verify numerical application code with a final Lean certificate, optionally producing a verified Rust port. Use for floating-point error bounds, source/model correspondence, composed guarantees and decision margins in Python, Julia, MATLAB-compatible or Rust code. Use this skill when formal numerical guarantees or a verified Rust port are requested. Simulation and parameter tuning alone do not require it."
---

# Verify numerical software

Deliver a reviewable guarantee: an original-input domain, an independent exact
reference, a checked numerical allowance in engineering units, and one Lean entry
theorem connecting these to the executable model. Use external tools when their
arithmetic model and libraries fit the obligation. Their output is a proposal
until the required argument is checked in Lean.

## Establish the contract

Inspect the actual source and caller. Record input types, initialization,
precision, operation order, rounding, FMA policy, subnormals, exceptional values
and branches. Establish engineering limits and units before choosing a solver
target. Reuse requirements already provided; ask only for missing information.
Sampled sensor ranges do not establish physical operating limits.

State the exact reference on the same original inputs. Carry incoming state
error across interfaces; do not restart from rounded gains or coefficients.
Distinguish equality of decoded real values from equality of words and signed
zero. Keep physical/model error separate from arithmetic error. Repeated calls
need reached-domain invariants and state-error propagation.

## Agree on artifact locations

Before creating application artifacts, confirm the verification directory and,
when generating a Rust delivery, the Rust destination with the user. A path
explicitly supplied or previously confirmed by the user already settles that
choice. Otherwise ask one concise question covering the missing locations;
suggest project-appropriate paths such as `verification/` and `rust/`, and name
any new top-level directories before creating them. Record the agreed paths in
the report and reproduction commands.

Keep requests, authored proofs, final certificates and replay evidence under the
agreed verification directory. Put disposable application experiments, extraction
preflights and superseded runs in its `.cache/` subdirectory, with an appropriate
ignore rule. Do not create a repository-root `.cache/` for application scratch
merely because it is ignored. Keep reusable downloaded tools in a shared user
cache outside the checkout; announce that location during setup. An ignored
directory is not automatically disposable: preserve frozen evidence and its
identities when organizing or cleaning up.

## Execute the workflow

Locate a complete FLARE provider checkout as `FLARE_ROOT`, checking for
`lean-toolchain`, `Flare/` and `scripts/certify_numerics.py`. Reuse a supplied
path or a checkout found by resolving the skill's symlink. Standard GitHub and
skills CLI installations may contain only the skill folder; their parent is
not necessarily the provider. If no complete checkout is available, obtain it
using [tool-setup.md](references/tool-setup.md) in the shared user cache.
Read
[source-to-rust.md](references/source-to-rust.md) for commands, request fields,
optional tool configuration and the closed source subsets. Build the provider
library, run `capabilities`, inspect the source and use `plan` to collect missing
ranges, units, budgets and exact specifications. Invoke the CLI by absolute path
so the application needs no FLARE-specific working directory or dependency.

Obtain missing tools yourself using the available download, package and build
tools; do not stop at a missing executable or hand routine installation back to
the user. Read [tool-setup.md](references/tool-setup.md) when dependencies are
missing: use compatible pinned sources or releases, install in user scope,
record identities and run an extraction/proof preflight. Respect actual network,
filesystem and installation permissions. Report a concrete setup failure if a
compatible installation cannot be completed; it is not a numerical proof failure.

The default `lean` target checks a numerical source model without requiring
Rust tools. Use `rust-aeneas` when the engineer requests a Rust delivery; for a
Rust input, retain the original source. Run into a fresh output directory and
inspect the root theorem, result, command logs and report.

Preserve the original implementation and arithmetic operation order. When a
narrow source-admission gap blocks the requested contract, add the reusable
frontend or semantic support and regression tests needed for that case, then
retry certification. Keep extensions within the requested scope and make the
mapping from actual source to executable model explicit. If support cannot be
completed, report the unresolved construct or obligation; do not substitute a
hand-rewritten surrogate and claim to have verified the original implementation.

For admitted Python helpers and bounded literal-tuple loops, specify an exact
two-state fold on the original inputs. Review the whole horizon's allowance;
intermediate state errors must carry forward. The provider's scale suite includes
Kalman/IMU horizons and larger unproved application/model probes. An analysis
candidate or a successful rejection test is not a completed certificate.

Read [tool-routes.md](references/tool-routes.md) to select producers per obligation.
Try a small version-specific preflight, retain failures, check option units and
set external process limits. Read [tool-integration.md](references/tool-integration.md)
for registered producer selection and shared source setup. The current Gappa and
FPTaylor routes retain external evidence and validate their candidate conclusions
through reusable Lean scalar inference. Accept a candidate only after its actual
bound is proved; do not substitute the user's looser budget. Foreign proof traces
remain untrusted evidence; a general foreign-proof importer is not implemented.
Use reusable adapters, evidence checking or verified inference when extending
support to a new class of obligations.

Read [lean-conversion.md](references/lean-conversion.md) for saved authored proofs.
Both an implemented converter and an LLM-authored Lean proof are acceptable when
Lean checks the full result. Do not leave numerical bounds, rewrite identities
or local finiteness as unproved premises in the final theorem. Read
[composition.md](references/composition.md) for local contracts, denominator
floors, state recurrences and branch margins when flat analysis is inadequate.

## Produce a reusable Rust port

When Rust is requested, preserve the original implementation's reusable API and
organization: functions or methods, state/configuration fields, initialization,
optional per-call overrides, mutation order and loops. Preserve fields that the
original leaves unchanged as well as those it updates. Keep the agreed numerical
operation order; do not replace a stateful method or loop with an unrolled
fixed-horizon arithmetic kernel for delivery.

For repeated-call certificates, generate a finite-horizon verification driver
as a separate function that calls the real production API in a loop. Proofs and
internal models may expand that horizon; the delivered API and driver retain
their structure. The CLI's automatic
straight-line IR emitter is a checker aid, not a substitute for this port. For
non-Rust input, use the explicit `rust_port` route in
[source-to-rust.md](references/source-to-rust.md)
to freeze and extract the actual implementation and driver, then prove their
connection to the numerical model in Lean. Include caller-visible state and
per-call option behavior in the correspondence argument; final output error
bounds alone do not cover those effects. Test API/state behavior separately
from the bounded driver. If extraction or its bridge remains unsupported, report
that gap without silently flattening the delivered program.

## Check and deliver

For successful error-bound certification, require `Workflow.Certificate.certificate`
to cover the original finite inputs,
independent exact specification, output finiteness and accepted allowances. A
successful budget must be proved in Lean. A Rust delivery also needs the actual
freshly extracted return relation. Audit the root's transitive axioms: only
`propext`, `Classical.choice` and `Quot.sound` are allowed. Preserve the declared
frontend, runtime, translation and compiler/hardware trust boundaries.

If the requested property is false, deliver a saved Lean counterexample with a
named root proving an input satisfies the stated domain, the executable model's
actual result, and violation of the required property against the independent
reference. Audit its transitive axioms and replay the saved proof. Use the
authored-proof guidance in [lean-conversion.md](references/lean-conversion.md);
the automatic error-bound CLI has no counterexample status. A proof rejection
or an upper bound above budget does not establish an attained failure.

Replay the saved Lean proof into a new directory without an analyzer, LLM or
foreign prover. `audit` checks identity/freshness; it does not check mathematics.
Use rejection controls for wrong specifications/bounds, changed source, removed
root theorems and additional axioms. Classify missing tools separately from proof
failure. A timeout is unresolved; a checked upper bound above budget does not
prove that the implementation attains that error.

Deliver a readable report naming the checked entry theorem, accepted error
bounds versus the engineering budget, assumptions and trust boundaries,
unresolved goals, artifact location, and reproducible run and replay commands.
Put this engineering report under the agreed verification directory, outside
sealed run directories; preserve the CLI's frozen `report.md` and other evidence.
Clearly distinguish Lean-checked results, untrusted candidates and sampled
diagnostics. Samples diagnose translation/runtime agreement; they are not
universal equivalence proofs or physical validation.
For comparisons, freeze source/domain/reference/target and assistance budget,
retain default failures and record proof/hint authoring separately from replay.
Read [evidence-records.md](references/evidence-records.md) for portable scorecards;
its audit helper checks records, not proofs. Accessibility claims need new-task
and engineer evaluation; passing regression scenarios alone does not establish
that the skill can solve arbitrary new applications.
