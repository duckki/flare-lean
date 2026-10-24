# Run registered numerical producers

Read the provider's `capabilities` output for adapter roles, supported versions,
arithmetic constraints and setup recipes. The current external producers are
`gappa`, `fptaylor` and `precisa`; `lean-flare` remains the default producer and
independent checking path. `rust-aeneas` supplies extraction when requested.
CBMC 6.11.0 is a separate witness proposer; use
[counterexamples.md](counterexamples.md) for strict-positivity search and ordinary
Lean witness checking. Select it through `counterexample_search` and
`search_tools`, rather than the numerical `producer` field.

Add `"producer": "gappa"`, `"producer": "fptaylor"` or `"producer": "precisa"`
to an otherwise complete request. Configure `analysis_tools` as a map from tool name to `executable`,
optional expected `sha256`, and optional tool-data `base` directory. Environment
variables `FLARE_GAPPA` / `FLARE_FPTAYLOR` / `FLARE_PRECISA` and `PATH` are
fallbacks. Preserve source, domain, independent specification, units and requirements.

The external routes save proof-bearing or candidate output, then reconstruct the
**candidate conclusion** in Lean: the Gappa query's exact dyadic radius or the
actual FPTaylor hexadecimal bound, or PRECiSA's maximum stable/unstable bound.
They cannot substitute a looser budget. Failed Lean arguments remain unresolved. Gappa's Coq
trace is retained rather than imported; this is not a general foreign-proof importer.

The scalar validator uses nearest-rounding theorems, checked polynomial rewrites,
exact rational enclosure inference with checked powers and bounded domain
subdivision. It admits at most 32 IR nodes,
256 polynomial terms, degree 16 and 16 input boxes, with arithmetic magnitude at most
`2^1000` and positive native/exact divisor floors. The default producer also tries
it when compositional analysis loses a floor or misses a budget. Preserve the
original contract when search or proof checking fails. Review per-box domains,
rounding allowances and conclusions in `analysis.json`; saved proofs establish
that all cases cover the original domain.

For the closed [C profile](c-source.md), use its source-derived Lean conditions
and the default producer. Optional WP/Why3 task export is inspection evidence,
not registered producer output or an imported proof.

For terminal scalar Python conditionals, read [conditionals.md](conditionals.md).
PRECiSA's candidate is checked across all four native/exact flows, even if the
analyzer claims stability. PVS files are retained rather than imported. This
`python_branches: true` profile uses Lean delivery; both arms must satisfy
arithmetic premises on the full domain. The default branch producer attempts
the requested allowance.
The default producer also has an explicit guard-local profile for a direct
input/literal comparison; Lean proves guard agreement and local arithmetic
premises. External producers do not yet support that profile or compact counted
loops; use [counted-loops.md](counted-loops.md) for the latter's invariant route.

Reuse compatible tools. Otherwise obtain missing prerequisites and use the
shared source-setup service in the agreed versioned user cache:

```sh
python3 "$FLARE_ROOT/scripts/certify_numerics.py" setup --tool gappa \
  --out /shared/tool-pool/gappa-1.8.3
python3 "$FLARE_ROOT/scripts/certify_numerics.py" setup --tool fptaylor \
  --out /shared/tool-pool/fptaylor-b5a77cae
```

Gappa needs C++, Flex/Bison, Boost headers and GMP/MPFR development files; the
release uses bundled `remake`. The portable FPTaylor build
needs OCaml 4, Num, Make and C; use an isolated compiler/switch as necessary.
`--make-arg 'NAME=value'` passes a build override. Keep setup logs, source identities
and failures. Existing destinations are preserved. Tool setup is separate from
Lean/Rust setup in [tool-setup.md](tool-setup.md). The same guide covers the
Linux PRECiSA recipe, GHC/Cabal prerequisites and versioned launcher.

Run normal `plan`, `run`, `audit` and `replay` commands. Review `obligation.json`,
`evidence.json`, raw queries/output and `analysis.json` alongside the root proof.
Missing tools, unsupported versions and changed tool hashes have separate failure
kinds. Saved-proof replay uses neither setup nor producers.

For provider extensions, prefer another adapter, a reusable evidence checker or
verified inference over per-application numerical proof patches. An adapter can
emit a Lean proof module through the same typed root check. The
[provider integration guide](https://github.com/duckki/flare-lean/blob/main/docs/integration/tool-integration.md)
defines these interfaces and their tests.

## Shared enclosure inference

The Gappa and FPTaylor adapters use the same proved
`Flare.Analysis.IntervalExpression.Expr.check_sound` engine for rational
constants, bounded real leaves, addition, multiplication, negation and natural
powers. Leaf bounds are proved from the original input domain or a checked
rounding theorem; Python calculations never become premises. Polynomial
factorizations are checked separately by `ring`. Power inference can retain a
positive denominator floor in `1/(x*x+1)` across a domain spanning zero.

Keep the actual producer candidate as the target. FPTaylor's tighter candidate
for that reciprocal is below the current reconstruction's allowance and remains
unresolved; a successful Gappa/default route is a separate attempt.
Saved typed Lean expressions replay without the producer or inference script.
This is verified inference over retained candidate conclusions, not a Coq/PVS
proof-trace importer. See the provider's `docs/integration/proof-evidence.md` for maintained
cases, controls and measurements.
