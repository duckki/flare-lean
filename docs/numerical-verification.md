# Numerical application verification

FLARE hosts one engineer-facing [verify-numerics skill](../skills/verify-numerics/SKILL.md)
and its separately invocable [CLI](../scripts/certify_numerics.py). The proof
library remains one Lake project: reusable native contracts live in
`Flare.Binary64.Pipeline`, alongside the existing scalar and matrix results.
Optional analysis and extraction tools are provider tooling, not dependencies
of the core Lean library.

## Install and use

Start with the [skill user guide](../README.md) for installation and an
agent-led FilterPy example. Agents can obtain missing tools and build the
provider; installing the skill alone does not do either. For a manual provider
build, follow the [development guide](development.md). Shared Lake caching is
optional; the CLI inherits the caller's settings.

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
through the whole horizon. Arrays and general dynamic iteration remain unsupported.

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

## Tool-assisted proofs

The automatic backend currently uses an untrusted rational producer plus FLARE
lemmas. A request can instead supply a saved authored Lean accuracy proof and
optional specification identity. This provides a path for reconstructing useful
external arguments without trusting a printed bound or foreign theorem. See
[Lean conversion](../skills/verify-numerics/references/lean-conversion.md).

Gappa, FPTaylor, PRECiSA and language-specific tools can help different local
obligations. Choose from the installed version's supported arithmetic model,
source constructs and output detail. No automatic external-output importer is
implemented. Coq/PVS/HOL success alone never closes a numerical Lean premise.

## Maintained validation and next work

The [benchmark guide](../benchmarks/numerics/README.md) describes supported
scenarios, rejection controls and known limitations. CI runs default scenarios
and fresh Lean controls; optional Julia/Octave/Rust tools are tested separately.
These tests exercise the skill's executable path and packaging. They are not
an independent evaluation of agent behavior on new engineering tasks.

Future work is organized around concrete checked results:

1. Reconstruct the frozen four-stage Gappa mean-update argument at `2^-51`
   through the authored-proof interface. Its current automatic allowance is
   `2^-43`; the foreign proof is not an existing FLARE result.
2. Extract recurring rules into a small versioned argument importer, or implement
   the same useful reasoning directly in Lean when that is simpler to maintain.
   Unsupported evidence must leave a goal unresolved. Prove native Float bridges.
3. Replace fixed absolute proposal grids with scale-aware proposals, preserving
   the original domains and checking outward rounding in Lean. Add FPTaylor
   candidate and PRECiSA branch cases only with completed Lean reconstruction.
4. Extend reusable error lemmas and admitted source semantics beyond fixed
   tuple loops to actual vector/matrix and dynamic repeated-call applications. Reuse the
   existing matrix/recurrence theorems, prove caller applicability, carry incoming
   errors and include requested decision margins.

Prefer the smallest useful checker/rule set over a general foreign-proof
translator. Keep one final Lean application theorem as the completion boundary.

## Scaling beyond a single kernel

`make numerics-scale` exercises the maintained progression in
`benchmarks/numerics/scale.json`: 1/4/8/16/48/128 Kalman updates, 1/4/16/48 IMU
motion updates, the original 48-event Rust admission challenge, and the original
relative/global four-state covariance/correction graphs (7,758/7,761 operations).
The [benchmark guide](../benchmarks/numerics/README.md) defines the domains,
capability boundaries and recorded proof-stage timings. CI runs a smaller subset.

The bounded Python fixtures preserve the source worktree's scalar helpers and
add explicit horizons with independent original observation inputs. The IMU loop
uses an original Float `dt` shared across its steps; it does not certify the
original UInt64 timestamp conversion, error-return branches or rounded decisions.
Those remain explicit obligations of the unchanged Rust application fixture.
The large graph probes report untrusted candidates, without a Lean root or
universal source bridge. They are not equivalent to completed application proofs.

The producer now uses the already-proved `native_ideal_refine` rule when native
range plus accumulated error gives a smaller exact magnitude bound. Lean checks
every use. This avoids artificial growth in repeated covariance calculations;
fixed normalization grids and lost correlations still limit useful bounds.
The 16/48-update nonlinear Kalman profiles also expose limits in expanded proof
construction; an unresolved proof has no accepted allowance. Named resource
allowances in the scale suite do not count as certification success.
