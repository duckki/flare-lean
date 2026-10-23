# Shared proof evidence and verified inference

Gappa and FPTaylor feed candidate error bounds to the same Lean inference engine.
The engine checks exact rational enclosures for typed real expressions and reuses
Mathlib's interval soundness rules. It preserves correlations such as `x*x ≥ 0`
without adding an application-specific theorem.

## What Lean checks

`Flare.Analysis.IntervalExpression` is pure mathematics, independent of native
binary64 semantics, source frontends and external tools.

| Evidence | Interpretation and check |
| --- | --- |
| Rational constant | Its exact cast to the reals |
| Bounded variable | A real value with proved lower/upper rational bounds |
| Addition, multiplication, negation | Mathlib's corresponding interval operation and soundness theorem |
| Natural power | Mathlib's sign/parity-aware enclosure; repeated factors retain one value |
| Proposed endpoints | `Expr.check` computes whether its enclosure fits; `Expr.check_sound` connects the Boolean result to the real claim |

Leaf premises come from the original input domain or an already checked local
rounding law. The provider proposes polynomial factorizations and rational
endpoints; `ring` checks the rewrite and `decide +kernel` checks the enclosure.
The original ordered native source model and rounding operations remain intact.
The final root still closes finiteness, source/reference correspondence, actual
candidate accuracy and engineering-budget obligations and audits transitive axioms.

This is a proved inference procedure over typed Lean evidence. It does not parse
or trust Coq/PVS proof traces, solver verdicts or an external tool's polynomial
rewrite. The retained foreign payload remains useful provenance and candidate
search evidence. No new external tool or core Lake dependency is introduced.

## Useful correlations

The [maintained examples](../examples/numerics/enclosures/README.md) include
squares, quartics and `1/(x*x+1)`. A naive product enclosure puts `x*x` in `[-1,1]`
when `x ∈ [-1,1]`; it then loses the denominator floor. Power enclosure proves
`x*x ∈ [0,1]`, and separately checked rounding allowances retain positive native
and exact floors. Gappa and the default producer can certify the unchanged
reciprocal request without an authored application proof.

Both Gappa and FPTaylor certify the square/quartic family through this same
checker. Each tool's actual output candidate remains the target. FPTaylor's
roughly `2.22e-16` reciprocal candidate remains unresolved: current reconstruction
produces a roughly `4.44e-16` allowance. A separate successful producer attempt
cannot turn that candidate into a checked result.

The scalar route retains its existing work limits: 32 IR nodes, 256 polynomial
terms, degree 16 and 16 domain boxes. The general Lean soundness theorem covers
arbitrary finite expression trees and natural powers; bounded provider search is
a separate implementation limit. Division still uses the established native/exact
positive-floor contract, outside the expression interpreter.

## Run and replay

Select the [example suite](../examples/numerics/enclosures/README.md) with
`benchmark_numerics.py --replay`. `--tools` supplies the pinned Gappa/FPTaylor
installations; normal setup is described in [tool integration](tool-integration.md).
The existing benchmark summary records accepted allowances, checking time,
maximum check-process resident memory and generated Lean source bytes.

`evidence.json` names the shared `rule_checker` and vocabulary. `analysis.json`
retains the proposed input boxes, rounding allowances and accepted conclusions;
typed expressions and their proofs are frozen under `lean/`. Cold replay
recompiles these sources without external producers, expression generation or
LLM assistance. Original pre-engine certificates keep their existing replay path.

`make numerics-check` includes corrupted operation rules, false polynomial
rewrites and invalid leaf bounds; they must fail in Lean before any allowance is
accepted. Arithmetic admission rejects a changed rounding mode before the
producer runs. Existing false-candidate, changed-source and additional-axiom
controls still apply.

## Coverage and cost

The comparison holds source, input domain, exact reference, arithmetic model and
requested budgets fixed. It compares the earlier scalar reconstruction with the
shared engine on addition, polynomial and division requests through each of the
two real producers, plus the regularized reciprocal. Measurements are local
macOS ARM64 checks with Lean 4.35.0 and existing library artifacts; setup and proof
authoring are excluded. They do not establish a general performance improvement.

| Measurement | Earlier reconstruction | Shared engine |
| --- | ---: | ---: |
| Certified requests in the eight-case comparison | 6 | 7 |
| Median accuracy-module check, six common successes | 1.53 s | 1.84 s |
| Maximum accuracy-module resident memory, same six | 907.9 MiB | 907.9 MiB |
| Total generated Lean source, same six | 63,075 bytes | 84,152 bytes |

All six previously checked output/budget records matched exactly. The added
success is Gappa's regularized reciprocal; FPTaylor's tighter candidate remains
unresolved. These are single-run cost observations, not a speed claim. This
change adds coverage and a reusable checked interface; reducing expression/proof
size and checking cost remains future work.
