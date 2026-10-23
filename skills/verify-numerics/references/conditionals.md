# Scalar conditionals and PRECiSA

Use `"python_branches": true` for an ordinary Python function ending in one
scalar `if`/`else`. An `if: return ...` followed by a final `return` is also
admitted. Use `inspect --python-branches` to inspect this profile.

The prefix supports the existing scalar assignments and separately rounded
`+ - * /`. The guard must be one `<`, `<=`, `>` or `>=` comparison; each arm
returns one scalar expression. Use floating literals for guard constants and
returned constants (`0.0`, rather than an integer result). The limit is 32
arithmetic nodes, excluding the selector. Helpers, loops, nested conditionals,
Boolean combinations, side effects and collections need a different route.
This profile currently supports the `lean` target with `lean-flare` or `precisa`.
It does not automatically generate a verified Rust conditional port.

Supply an independent exact conditional expression on the original input names:

```json
{
  "python_branches": true,
  "specification": ["1 if signal+1 >= 1 else 0"],
  "outputs": [{"name": "gate", "unit": "control", "limit": "1"}]
}
```

This extends a complete ordinary request with source, function and domain.
The specification's arithmetic is exact, so its branch can differ from the
native branch after rounding. The reusable Lean argument covers all four
combinations of native/exact choices, proves arithmetic finiteness and
denominator premises, and establishes equivalence to the independent specification.
Both arms are validated on the full domain, even though Python evaluates only
the selected arm. This conservative restriction can leave a safe branch-local
division unresolved. The generated arithmetic is pure; this treatment cannot
justify arbitrary side effects.

## Select PRECiSA when branch analysis is useful

The registered `precisa` producer uses PRECiSA package `4.0.4`, pinned source
`2626ba151a2915d7b148ff90ccfff5e1f764d948`. Obtain the maintained Linux installation
using [tool setup](tool-setup.md#precisa), then select its launcher using
`analysis_tools.precisa.executable`, `FLARE_PRECISA`, or `PATH`. The optional
`base` is the installation directory containing `precisa-build.json`.

The adapter emits an ordered PVS model and enclosing input intervals, runs
PRECiSA without a stability assumption, and retains its JSON and PVS files.
It reads `stableError` and `unstableError` as exact binary64 candidate values.
Their maximum becomes the actual Lean proof target. A missing unstable bound
does not remove divergent-flow obligations. Neither foreign PVS proofs nor
printed stability claims are trusted.

PRECiSA's input model can include half-ulp input uncertainty. FLARE's theorem
uses original binary64 inputs and their exact decoded real values. The external
model is used for candidate search; Lean independently checks the original
graph, domain and exact specification. A failed reconstruction is unresolved;
do not replace the candidate with the engineer's looser budget. The default
`lean-flare` branch route instead attempts the requested allowance directly.

The [conditional examples](https://github.com/duckki/flare-lean/tree/main/examples/numerics/branches)
include a threshold gate with zero stable-flow error but a one-unit unstable-flow
candidate. Ignoring the latter would give a false guarantee. The continuous
innovation-magnitude example certifies with the default procedure; its retained
PRECiSA run gives a checked allowance above the unchanged budget. Analyzer choice
can affect usefulness without changing Lean's proof boundary.

Use normal certification and saved-proof replay. Replay requires no PRECiSA,
Kodiak, Haskell compiler, original source runtime or LLM. It regenerates the
source model and checks the frozen Lean proof, root type and transitive axioms.
