# Numerical integration decisions

The bounded evaluations accept **typed product annotations and exact-zero
inference implemented in Lean**. They reject the tested **LeanCert Core backend
and Daisy scalar production adapter**. These decisions concern the routes below;
they do not establish that a whole tool is unsuitable for other applications.

| Route | Decision | Evidence and limit |
| --- | --- | --- |
| LeanCert Core public checked APIs | Reject for the tested scalar/module scope | Kernel-checked real/addition controls pass; direct import into FLARE's module proofs fails, and all three tested interval backends lose the reciprocal's square correlation |
| Modern Daisy scalar candidate producer | Reject production adoption for this scope | Conservative candidate controls certify/replay; all four exact-input candidates remain unproved by the current reconstruction, with no added source coverage |
| FloVer-style typed range/error evidence | Accept product/constant subset | A small Lean checker validates local rational summaries against native operations; degree-32/256 shared product chains now certify |
| VCFloat2-style compositional exact operations | Accept exact-zero multiplication subset | Two source examples obtain zero error; the checked rule preserves incoming ideal error and finite execution |

The accepted implementation adds no external Lake dependency. It does not import
Coq/HOL4 proofs or claim that FloVer or VCFloat2 checked these Lean certificates.
Their published typed annotation/compositional workflows inform the design.
FLARE's existing native IEEE semantics supply the operation soundness proofs.

## Frozen contracts and scope

The [pins](../../provider/manifests/evaluation-tools.json),
[reproduction runner and controls](../../benchmarks/numerics/integrations/README.md)
and [compact measurements](../../benchmarks/numerics/integrations/results.json)
retain the tested scopes. These are local macOS ARM64 runs with Lean/Mathlib
4.35.0 and two Lean workers. Setup/build artifacts were already populated for
checking measurements. Isolated source-admission time, complete clean setup
cost and manual authoring time were not measured; missing metrics are explicit
in the result record. Single-run timings are observations, not general speed
claims or clean-machine setup measurements.

The reciprocal is the maintained `1/(x*x+1)` source on finite original binary64
inputs in `[-1,1]`, with nearest/even, gradual subnormals, separate operations,
independent exact reference and budget `2^-40`. FPTaylor reproduced its exact
candidate `4503874505277445/20282409603651670423947251286016`
(`0x1.0004000000005p-52`, about `2.22058e-16`). The existing reconstruction still
rejects that actual candidate; it is not replaced with the user's looser budget.

The product-chain and zero-operation cases extend the maintained square/quartic
family. Their [requests](../../examples/numerics/typed-evidence/README.md) hold
source, domain, independent reference and budget fixed between the earlier and
new inference paths. The separate quartic cost comparison also holds the actual
candidate fixed at `2^-40`.

## LeanCert Core

The evaluated [Core APIs](https://github.com/alerad/leancert/blob/f704278b3ed525ab5dc80b2ce9545c9b8047ec30/LeanCert/API/Bounds.lean)
share FLARE's Lean and Mathlib revisions. The trial built the selected API import
closure, rather than importing the full library or SDK. Frozen checker ASTs and
boxes prove an ordinary addition bound with `decide +kernel`; an interpretation
and box-membership proof connects it to the original real addition. A separate
control composes that bound with FLARE's native nearest/even addition theorem,
including finiteness and underflow. Its transitive axioms are exactly `propext`,
`Classical.choice`, and `Quot.sound`. Frozen source rechecks pass.

Rational, Affine and Dyadic evaluation of `x*x` over `[-1,1]` returns `[-1,1]`.
The following reciprocal check then reports a denominator enclosure containing
zero. Rational and Dyadic API rejection controls are checked in the kernel;
Affine's compiled evaluation reports the same result, but the retained Affine
kernel-reduction probe fails. That compiled result is a diagnostic, not a proof.
Restricting the input interval to `[0,1]` gives an ordinary real reciprocal
enclosure, but changes the contract and does not prove the rounded-source error.

The direct provider-module trial fails because Lean 4.35 cannot import the pinned
legacy `LeanCert.API.Bounds` module from a `module` proof. Porting the dependency
closure or changing FLARE's proof-module system is not justified by this scalar
result. No provider backend, SDK, default native trust mode or optional proof-cache
dependency was added. Transcendental functions, other proof algorithms and a
future module-compatible revision remain separate evaluations.

## Modern Daisy

The pinned analyzer was built with Temurin 24.0.2+12 and sbt 1.9.9. Z3 4.15.4
supports the bounded reciprocal subdivision. The trial uses Float64, interval
ranges, affine errors, no rewriting or precision tuning,
and at most three divisions/32 analysis runs for the reciprocal. Its small
exporter admits a single output and exact small integer constants/endpoints.

The [exact-output patch](../../provider/patches/daisy-exact-candidates.patch)
exports Daisy's internal numerator/denominator. Ordinary display output converts
to a rounded decimal and is not used as an exact candidate. The exported ordered
query, raw CSV, actual candidate and generated Lean accuracy module are frozen.
The first run used `--noInitialErrors`. Inspection of the pinned specification
phase showed that this flag still assigns default input-rounding allowances.
All four resulting conservative candidates—addition, polynomial, division and
the regularized reciprocal—finish at `Workflow.Certificate.certificate`, pass
the axiom audit and replay with producer calls blocked. FLARE proves these bounds
for its own original-input semantics; it does not assume Daisy's input model.

A second run matches FLARE's zero incoming error on original binary64 inputs:
the exporter supplies an explicit zero-error annotation for every parameter and
leaves initial-error tracking enabled. The tighter actual candidates are all
unresolved at the Lean accuracy module. Addition and division propose `2^-52`
and `2^-53`; FLARE's current relative-plus-underflow reconstruction is slightly
looser. Polynomial and reciprocal reconstruction also exceed Daisy's proposed
allowances. These are missing proofs, not established numerical violations.
No candidate is enlarged to manufacture a success.

The conservative reciprocal candidate is about `5.05151e-16`; the exact-input
candidate is about `3.25295e-16`. Neither result settles FPTaylor's still tighter
proof obligation. The selected contracts already certify through FLARE/Gappa.
Without reconstruction of the exact-input candidates, added source coverage or
a checking-cost advantage, another production analyzer stack is not justified. The evaluation adapter and patch are retained
for a future gap involving Daisy's modular/array analysis or optimization.
Modern Daisy is not treated as the old `certified` branch's FloVer exporter.

Setup attempts exposed an inaccessible Adoptium endpoint, a missing subdivision
solver, Daisy's working-directory `library/` requirement and the need for explicit
`Real` annotations on exported constant bindings. The resolved runs retain these
as setup/export issues, separate from numerical or Lean rejection. The default
unsplit reciprocal analysis also fails after losing the denominator floor.

## Typed evidence and compositional inference

[`CheckedBounds`](../../Flare/Binary64/CheckedBounds.lean) exposes rational
summaries, numeric checks and soundness for ordinary and exact-zero multiplication.
The summary records a native center/radius, ideal magnitude and accumulated error.
Every application requires already proved operand summaries. Kernel computation
checks the proposed inequalities; the soundness theorem uses FLARE's existing
native rounding/zero semantics and retains incoming error. No application lemma,
solver unsatisfiability assertion or unproved approximation premise is introduced.

The provider proposes at most 32 product/constant nodes, with one shared summary
per original operation and 4,096-bit rational annotations. An exponent floor of
`-1200` and outward recentering bound rational growth for tiny constant chains;
these proposals still need kernel-checked inequalities. This avoids expanded polynomial inference. It is a native
Lean implementation of the selected typed-evidence/compositional ideas from
[FloVer](https://github.com/Cactus-proj/FloVer/blob/2b846b7242db7435c97ba694393db47842b19860/coq/CertificateChecker.v)
and [VCFloat2](https://github.com/VeriNum/vcfloat/blob/a203b287a84b0e3c9bec136823b5622ebfde6ad6/vcfloat/Automate.v).
The historical FloVer producer/checker pair was not reproduced; no claims about
its Coq/HOL checker execution or a general certificate importer follow.

| Fixed request | Earlier route | Accepted route |
| --- | --- | --- |
| Degree-32 repeated square | Polynomial work limit | Certified and replayed below `1e-13` |
| Degree-256 repeated square | Polynomial work limit | Certified and replayed below `1e-13` |
| Zero product, budget `2^-1100` | Checked allowance exceeds budget | Certified and replayed with zero error |
| Rounded square then zero product, same budget | Checked allowance exceeds budget | Certified and replayed with zero error |

For the fixed-candidate quartic comparison, total generated Lean source falls
from **14,470 to 4,837 bytes**. The recorded check commands take **5.75 versus
4.68 seconds** in the local run, including environment/kernel/proof/root checks.
The implementation adds 124 Lean lines for the checked interface/soundness, a
bounded provider proposer/emitter, tests and evaluation scaffolding.
Manual authoring time and a complete clean-machine tool setup were not timed.
These observations support the small reusable subset; they do not establish a
speed improvement across applications. The additional degree-4096 scale case certifies 12 shared product operations
below `1e-12` and replays in about seven seconds. Fresh replay recompiles all generated
modules. There is no new compiled-helper cache to restore; warm artifact reuse
is not claimed for this checker.

The tests corrupt native ranges, accumulated errors, rounding allowances and
exactness rules; Lean must reject each at the accuracy module. Kernel controls
also reject discarded incoming error and a relative-only allowance that omits
gradual underflow. The existing source/contract/model freshness and extra-axiom
controls remain part of the provider regression suite. The primary comparison matrix requests Lean delivery. An additional degree-32
product control completes fresh Charon/Aeneas extraction, numerical accuracy and
Rust correspondence in the same final root and replays. This exercises the
existing Rust IR-probe route; production API ports retain their separate bridges.

The default producer selects typed evidence after a coarse budget miss. External
scalar producers currently reach it after a polynomial work-limit failure;
numerical misses alone retain the primary reconstruction. Broader backend
selection is future work.

The accepted scope excludes other arithmetic, native binary32 arithmetic,
Sterbenz rules and unspecified platform functions. Extend the common checked
vocabulary against a retained gap before adding a foreign parser or operation.
The [roadmap](../roadmap.md) tracks that work.

Parallel full-suite checking and four formatter workers caused memory contention
on the 16 GB evaluation host. The formatter workers were stopped, and the remaining
format check uses `FMT_JOBS=1`. This interrupted check is retained separately from
completed proof rejections and from the final validation record.

## Validation

- `make check FMT_JOBS=1`: passed; 258 fast tests with 90 optional integration
  skips, 79 library modules, 747 public/977 private theorem declarations audited,
  and Lean formatting at width 100.
- Full `make numerics-check` with installed Gappa/FPTaylor and Rust tools: 221
  tests passed with five optional skips. This run preceded the final bounded-rational
  proposer guard; all seven focused route tests passed again after that fix.
- Six maintained typed-evidence smoke cases certified and replayed, including
  tiny constants and a [real Gappa candidate](../../examples/numerics/typed-evidence/power32_gappa.json).
  The candidate remains the actual queried radius; capability metadata names
  the selected typed fallback.
- The degree-4096 scale case certified and replayed. Its generated accuracy
  module remains byte-identical after the proposer guard.
- The separate Rust extraction/root/replay control passed. LeanCert API positives
  and intended compatibility/reduction rejections, both Daisy input-error trials,
  and failed setup attempts remain recorded in the evaluation outputs.
