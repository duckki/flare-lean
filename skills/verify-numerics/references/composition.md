# Recover a large analysis with local contracts

Read this when a flat analyzer query stalls, repeats the same kernels or needs
to reuse existing guarantees. A successful direct query need not be rewritten.
Choose admitted analyzers and available libraries for the actual obligations.
In this skill's deliverable, local numerical claims and their composition must
all be checked in Lean; see [lean-conversion.md](lean-conversion.md).

## Automatic provider route

For admitted Python helper chains with a two-state fold request, the default
producer preserves helper definitions and generates local contracts on native
and exact incoming state. It checks finite execution, reached ranges, divisor
floors and carried errors, then proves the application against the independent
recurrence. This route closes the retained 16/48-update Kalman cases; 128 updates
have a checked allowance above the mean budget. Do not call that a numerical bug.

Review `model-layout.json`, per-helper identities in `analysis.json` and the
function/contract modules under `lean/Workflow/`. Frozen-source replay regenerates
the helper model and recompiles all saved proofs without inference or producers.
For a two-state source loop with fixed scalar configuration, the explicit
[counted-loop profile](counted-loops.md) proposes and checks a uniform invariant.
Its `foldl_contract` proof covers every natural horizon; the application root
instantiates the selected source count. Arbitrary invariants, input streams and
general loops need additional source/proof support. The library's parameterized
`foldl_contract` / `foldl_error_bound` rules can compose supplied local arguments.

For repeated work, an optional `contract_cache` request field can use the agreed
verification directory's `.cache/contracts/`. Announce the path; no shared cache
is created by default. Unchanged module text, helper dependencies and library/
compiler identities allow reuse across changed callers. Inspect
`proof-reuse.json`; replay deliberately bypasses this build cache.

## Pick the interface before the bound

Keep the original source, input interpretation, reference and engineering
target. Decomposition changes the proof strategy, not the requested problem.
Identify the values crossing each interface and the already accumulated errors
in those values. Include coefficients, timestamps, conversions and initializers,
not just the state estimate. An interface value may have a native word and an
exact reference that differ; both are needed by the next stage.

A local rounding theorem normally takes an arbitrary **real exact operation
on rounded operands**. Its argument need not itself be representable. Declaring
that argument as an already rounded input can accidentally analyze another
problem. Match nearest/even, subnormals, FMA and exceptions to the implementation.

## Carry a checked summary

One useful absolute summary is

`|n| ≤ N`, `|i| ≤ I`, `|n-i| ≤ E`,

where n is the rounded value and i its original-input exact reference. Other
signed, affine, interval or matrix summaries may retain useful correlations.
For absolute summaries, sound error propagation includes:

| Operation before its new rounding | Incoming error allowance |
|---|---|
| Addition/subtraction | E₁ + E₂ |
| Multiplication | E₁ N₂ + I₁ E₂ |
| Negation | E₁ |
| Division by an exact nonzero constant c | E₁ / abs(c) |

The multiplication expression follows the exact identity
`n₁*n₂-i₁*i₂ = (n₁-i₁)*n₂+i₁*(n₂-i₂)`; it is not a first-order approximation.
Add the local rounding allowance and derive the next magnitude premises.
General division needs separate denominator error and nonzero/lower-bound
arguments. Do not use the constant-divisor rule for a rounded computed gain.

A producer can propose summaries using exact rationals and outward grids. A
prover should check the inequalities and each local contract's caller premises.
Sampled ranges are diagnostics, not universal bounds for reached values.
Keep the producer untrusted where possible: its false annotations should
produce rejected proofs rather than new assumptions.

## Keep translation and simplification visible

Record the original node, operation order, operands, proposed summary and
theorem used. If an identity reduction helps, retain its alias ledger and
check equality for **both** rounded and exact computations before transferring
the error allowance. A nonexact constant computation cannot be folded into a
new exact input without carrying its error.

Some intermediate nodes become irrelevant only after a later zero/identity
reduction. They may still need definitions and representation proofs to justify
the earlier node equalities. Slicing the final optimized dependency alone can
leave a proof producer with missing aliases. Decoded equality can also ignore
a zero sign that bitwise correspondence must preserve.

Track the original caller separately. Bounds for a real rounding DAG do not
by themselves prove the native program's validation, successful finite
execution, memory behavior or compiler/hardware interpretation.

## Specialize fixed work when it helps

Identify which source computations actually depend on the quantified inputs.
A fixed schedule or initializer may make part of a pipeline constant. A producer
can propose its trace and a trusted proof kernel can check the closed operations
and guards directly. Prove independence from the remaining variable inputs and
compose with their parametric contracts before claiming a universal result.
One successful constant-input execution alone does not justify that claim.

Match the property to the need: a path used only for execution validity may
need finite-operation/shape/guard proofs rather than a second accuracy theorem.
Keep specialization premises explicit. A fixed covariance trace says nothing
about variable initialization, other schedules or covariance accuracy unless
those properties have separate proofs. This strategy is not specific to one
proof assistant; source semantics and available checking support determine
whether it is practical.

## Make the guarantee usable by its caller

Connect the numerical reference to compact equations an engineer can review.
A checked bound against a large generated arithmetic graph still leaves the
meaning of that graph to review. When practical, prove its relation to the
independently stated recurrence, preserving original inputs and alignment.
That identity does not validate a physical model or input units.

Expose executable admission checks for the premises that can be checked at
runtime: array shape, finite values, ranges and supported configuration. Prove
that acceptance matches the theorem's domain in the actual comparison model,
including exceptional values, signed zero and subnormals. Prove successful
execution for accepted inputs and the guarantee for every successful API
result. Unsupported data must not acquire a certificate through a fallback.

Return allowances in the quantity's units, with their native encoding checked.
If an exact radius is rounded for runtime use, prove outward coverage; if it
is exactly representable, prove that equality. Include any later arithmetic
used to form intervals or make decisions in its own error analysis. A returned
numerical allowance is not automatically a physical confidence interval.

## Compose tools without upgrading their assurance

An analyzer may propose a local allowance and a prover may compose it. The
composition theorem remains conditional until that allowance is justified at
the claimed trust level. If a second checker independently proves a looser
normalized contract, it validates that normalized contract, not every sharper
number printed by the analyzer. Name both roles. A completed primitive query
is not a completed whole-program analyzer result.

Distinguish replay cost from the effort to create the local lemmas, summary
scheme, hints and source relations. Reusing an established library is useful
engineering, but not evidence that the backend or agent developed the proof
from scratch. Preserve the unsuccessful flat inputs and budgets.

## Maintain and stop at the requested conclusion

After a horizon, rate or source change, regenerate the affected caller,
coefficient/reference wiring, reductions and composition obligations. Reuse
unchanged local theorems only within their original premises. For example,
a longer propagation loop may preserve a local binary64 rounding theorem
while requiring a new application certificate for the changed event list.

A relevant negative control can expose a fragile proof boundary: setting a
known nonexact coefficient's accumulated error to zero, or using an unsupported
local rounding radius, should not pass the checker. Such controls do not
fully validate the frontend or certify the original native program. A checker
error alone does not establish the intended negative claim: distinguish setup,
parser and reduction failures. Where practical, prove the negated contract and
audit its assumptions; do not label a computation axiom-free without checking.

When the allowance meets the target, report the remaining source/validity
boundary before tightening further. If it is too loose, distinguish actual
error from correlation loss in the summary; a richer summary or different
formulation may help. Keep the final engineering quantity and units separate
from the units of local arithmetic contracts.
