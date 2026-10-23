# Scaling numerical source proofs

FLARE has two complementary composition routes: contracts for bounded helper
chains and one preserved invariant for a counted scalar loop. Both carry native
and exact state through calls, close numerical premises in Lean and retain the
original source. A sampled diagnostic is separate from the universal theorem.

## Maintained workloads

| Source/request | Work | Lean result |
| --- | --- | --- |
| `examples/numerics/counted/smoothing_*.json` | 1, 16, 128 and 1,024 calls to the original two-state smoothing helper | One invariant proof for all natural counts; the root instantiates the selected count |
| `examples/numerics/counted/decay_1024.json` | 1,024 calls to a different two-state decay helper; count is the first API argument | Same reusable source/invariant machinery |
| `examples/numerics/scale/shared_*.json` | 4, 32 or 64 four-stage two-channel smoothing blocks, with distinct original observations | 64, 512 or 1,024 arithmetic operation instances in the source graph, with shared helper definitions and local contracts |
| `examples/numerics/branches/guarded_reciprocal.json` | Input domain `[0,2]`, dividing only when `x >= 0.5` | Guard agreement and a positive denominator proved on the selected branch |

All source fixtures are maintained in FLARE. Smoothing/decay outputs have a
requested uniform `10^-6` m allowance per channel. The shared pipeline's exact
per-observation step is `(state+15*observation)/16`, proved equivalent to its four
separately rounded averaging stages. Initial channels range over `[-1,1]` m and
observations/bias over `[-1/4,1/4]` m. These are demonstration contracts, not
default physical operating limits.

The counted profile keeps six lowered nodes for the smoothing helper regardless
of count. At 1,024 calls it represents 4,096 arithmetic operation instances.
The larger shared graph contains 1,536 lowered nodes, including constants, and
1,024 arithmetic operations. Its checked proof uses one function module and 12
distinct local contract modules. These are different size measures; do not count
loop repetitions as additional unique helper definitions.

## Reproduce and measure

After building the provider, from its root:

```sh
python3 scripts/benchmark_numerics.py --suite scale \
  --case counted_smoothing_0001 --case counted_smoothing_0016 \
  --case counted_smoothing_0128 --case counted_smoothing_1024 \
  --case counted_decay_1024 \
  --contract-cache .cache/numerics-generated/scaling-contracts \
  --replay --out .cache/numerics-generated/scaling-counted

python3 scripts/benchmark_numerics.py --suite scale \
  --case shared_smoothing_0032 --case shared_smoothing_0064 \
  --contract-cache .cache/numerics-generated/shared-contracts \
  --replay --out .cache/numerics-generated/scaling-shared

python3 scripts/benchmark_numerics.py --case guarded_reciprocal \
  --replay --out .cache/numerics-generated/scaling-guard
```

Output directories must be new. These paths are provider regressions; application
artifacts and scratch use the engineer's confirmed verification directory.
Shared Lake caching is optional and follows [the development guide](development.md#shared-build-cache).

`summary.json` records proposal/check times, graph sizes, expanded counted-loop
work, Lean source bytes/module counts, reused modules and maximum reported check
process resident memory. `--replay` separately records elapsed cold replay and
retains its commands and streams. Replay recompiles saved proof modules with no
producer or compiled helper-cache reuse. Run time includes source diagnostics;
replay time does not. These costs do not measure proof-authoring effort.

### Local scorecard

Measured on macOS 26.7.1 ARM64 with Lean/Mathlib 4.35.0 and the commands above.
All seven cases certified within the unchanged two-million-heartbeat and
120-second per-stage limits, then replayed without producers or the compiled
helper cache. Other regressions ran concurrently, so timings are local workload
observations, not isolated speed comparisons.

| Workload | Lean check seconds | Cold replay seconds | Lean source KiB | Maximum check RSS GiB | Reused modules |
| --- | ---: | ---: | ---: | ---: | ---: |
| Smoothing, 1 call | 16.55 | 12.08 | 14.61 | 1.59 | 0 |
| Smoothing, 16 calls | 13.46 | 16.31 | 14.62 | 1.60 | 2 |
| Smoothing, 128 calls | 12.37 | 10.02 | 14.62 | 1.60 | 2 |
| Smoothing, 1,024 calls | 7.66 | 10.76 | 14.63 | 1.60 | 2 |
| Decay, 1,024 calls | 11.64 | 11.04 | 14.38 | 1.60 | 0 |
| Shared pipeline, 32 blocks / 512 operations | 34.58 | 30.96 | 236.25 | 0.91 | 0 |
| Shared pipeline, 64 blocks / 1,024 operations | 12.14 | 39.12 | 296.62 | 1.01 | 13 |

Check seconds sum the initial run's check-phase command times; reused modules
are absent from that sum. RSS is the maximum reported resident memory of a
completed check child, not total concurrent memory. Lean source size includes
the generated model, local contracts, application proof and root checker.
The smoothing invariant theorem is exactly 2,604 bytes at every tested count;
only the selected-count wrappers grow by a few digits. The 64-block caller reuses
one function and all 12 contracts from the 32-block caller. Cold replay compiles
all saved modules in both cases.

These cases use automatic provider proofs and independent fixture specifications;
no per-application Lean proof is supplied. Designing a new profile or specification
still requires review. The commands above retain JSON summaries, commands and
streams alongside fresh proof evidence. CI also runs the 1/1,024-call and
32/64-block cases with replay, retaining them in its numerical benchmark artifact.

Changing the bounded shared caller from 32 to 64 blocks retains its function and
existing local contracts. Changing a counted horizon retains both helper modules
and the parameterized invariant proof body. Contract keys bind module contents,
transitive imports and foundation/compiler identities. Fresh replay still checks
the saved source proof even when development used compiled contract reuse.

## Scope and rejection controls

The [counted-loop profile](../skills/verify-numerics/references/counted-loops.md)
currently handles two states, fixed scalar configuration, and one helper call per
`range(count)` iteration. It proposes a uniform invariant; general input streams,
time-varying recurrences and arbitrary combinations with array/branch profiles
remain open capabilities. The [guard-local profile](../skills/verify-numerics/references/conditionals.md#guard-local-arithmetic)
uses a direct input/literal comparison. Computed floating-point guards retain the
separate four-flow route and its full-domain arithmetic premises.

Tests reject incorrect exact recurrences, zero incoming-error assumptions,
unpreserved invariants, changed helper/arm models even after artifact hashes are
updated, wrong guards and missing denominator premises. An unreachable arm can
contain a division unsafe outside the theorem's domain; Lean must prove the arm
unreachable, and source diagnostics must evaluate only the selected arm.

These source-backed cases are separate from the large covariance/correction graph
probes. Those still have no source-program certificate. The 128-update Kalman case
retains its unchanged budgets and checked `budget_not_met` baseline; the new
counted-loop examples do not establish a tighter bound for that application.
Larger dimensions, 10,000-operation source graphs and broader source-profile
composition remain [roadmap work](roadmap.md).
