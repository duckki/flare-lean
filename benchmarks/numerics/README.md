# Numerical workflow benchmarks

`scenarios.json` is the maintained scenario list; requests and source kernels
live in `examples/numerics/`. These are reusable fixtures extracted from
Kalman experiments, not a copy of the paper or its frozen performance reports.
The [source attribution](../../docs/organization.md#source-attribution) identifies their source.

```sh
make numerics-check  # Adapter, installation, producer-gap and fresh Lean controls
make numerics-bench  # Default end-to-end cases, fresh ignored output directory
python3 scripts/benchmark_numerics.py --out /tmp/optional-numerics \
  --include-optional --tools /path/to/local-tools.json
```

Run the scripts from the provider root. Shared Lake caching is optional; see
[the development guide](../../docs/development.md#shared-build-cache). `make numerics-bench` writes to
`.cache/numerics-generated/bench-TIMESTAMP/`. A benchmark output directory must be new. Commands,
streams, accepted allowances, root theorems, failures and elapsed times are saved.
Warm checking time does not measure proof authoring or engineer effort.

CI also certifies and replays the exact [README examples](../../docs/numerical-verification.md#replay-the-readme-examples),
then uploads their sources, proofs and reports as `readme-evidence`.
`filterpy-gh-request.json` is the pinned eight-update request template; the
evidence generator binds `source.py` to the selected original FilterPy file.

| Scenario | Expected result | Scope |
| --- | --- | --- |
| Scalar and idiomatic Kalman | `certified` | Mean and variance, original inputs, independent exact equations |
| Joseph covariance | `certified` | Alternative operation schedule and two outputs |
| IMU prediction | `certified` | Scalar motion kernel, original Float time input |
| Four-stage mean update | `certified` | Residual, gain multiplication, add zero, add prior mean |
| Same mean update, `2^-51` target | `certified` | Reusable scalar inference, three gain intervals and the unchanged target |
| Tiny positive gain denominator | `certified` | Preserve native and exact positive floors with both variances in `[2^-54,2^-53]` |
| Mean update through Gappa / FPTaylor | `certified` with optional producers | Lean validates the Gappa query bound or actual FPTaylor candidate |
| Julia / MATLAB-compatible Kalman | `certified` with optional runtime | Same equations; actual Julia or explicitly selected MATLAB/Octave |
| Rust mean update | `certified` with rustc | Original Rust source and source/IR diagnostics |
| Python Kalman → Rust IR probe | `certified` with optional extraction tools | Internal straight-line kernel: fresh Charon/Aeneas return plus debug/release diagnostics; not a reusable production port |
| Original Rust → extracted Rust model | `certified` with optional extraction tools | Original source retained, no port substitution |

Optional cases are excluded by default and marked separately in summaries.
CI additionally builds the pinned Gappa/FPTaylor versions and selects
`mean_update_gappa` / `mean_update_fptaylor`. See
[tool integration](../../docs/tool-integration.md) for source setup, configuration,
adapter extension and the distinction between raw output and checked bounds.
Explicitly selecting one requires its tools: absence is a failed prerequisite,
not a successful proof rejection. `--case NAME` can select individual scenarios.
A local tools file has `runtimes` keyed by `julia`, `matlab` or `rust`, each with
`kind` and `executable`; `rust_tools` has `charon`, `aeneas` and `lean_lib`.
`analysis_tools` maps Gappa/FPTaylor to their executable and optional identity/data selections.
Use absolute paths. This machine configuration is not a version attestation.

Fresh Lean tests require the baseline to certify first. Controls then check that:

- a wrong independent specification fails in Lean, not source admission;
- a false zero-error proposal for rounded addition is rejected in Lean;
- a runtime/model diagnostic mismatch prevents certification after a valid proof;
- a checked bound above budget remains `budget_not_met`;
- changed source/proof artifacts and changed authored proofs fail freshness;
- a resealed changed kernel fails comparison with frozen source/specification;
- removing the root and its inline audit still fails the independent root checker;
- an authored proof can certify, while an authored numerical axiom is rejected;
- saved proofs replay with producer/runtime entry points disabled.

Fast tests cover missing runtimes, unsupported source constructs, operation
order, literal words and signed zero, Rust mutation/typing, bounded process
cleanup, artifact retention and non-overwriting skill installation.

## A proved numerical failure

`scripts/test_numerics_counterexamples.py` maintains the README's standalone
naive scalar covariance update. At `p = 1`, `r = 2^-54`, its binary64 posterior
is zero while the exact posterior is `1 / (2^54 + 1) > 0`. The fast test compares
actual Python execution and the admitted model. `make numerics-check` also
checks and replays a Lean refutation with an axiom audit, then rejects a false
output claim. This authored counterexample is separate from the error-bound
scenario runner's statuses. See [the worked example](../../docs/numerical-verification.md#kalman-counterexample).

## Known analysis gaps and external fixtures

The fast compositional producer normalizes centers/radii/ideal magnitudes on a `2^-20`
grid and errors on a `2^-45` grid. It can then refine the ideal magnitude using
native range plus accumulated error; that refined value need not lie on the
coarser grid. Tests retain two limitations of that producer: a simple addition
allowance inflates from `2^-51` to `2^-45`, and `p/(p+r)` is unresolved for both
inputs in `[2^-54,2^-53]` after normalization loses a positive divisor floor.
The default workflow now tries reusable scalar inference for graphs of at most
32 IR nodes when a budget or divisor floor needs refinement. It uses relative
outward enclosures, nearest rounding, polynomial correlations and checked input
subdivision. The addition, tiny-gain and tight mean-update families now have
Lean certificates; large graphs still use the compositional producer.

`gappa/mean-update-tight.g`, its raw Coq trace and wrapper are preserved inputs
for comparison with Lean reconstruction. The reusable Lean route now establishes
the unchanged `2^-51` theorem without trusting that foreign trace.
Foreign checker tools are not required for default local tests. Gappa/FPTaylor
producer adapters retain output and validate the actual candidate conclusion;
their foreign proof traces are not imported. PRECiSA is planned for milestone 8
and has no registered adapter.
Full matrix/filter applications,
NumPy/BLAS mappings, unstable branches and physical coverage need further work.

## Increasing scale

```sh
make numerics-scale
python3 scripts/benchmark_numerics.py --suite scale --case kalman_016 \
  --out /tmp/new-scale-case
```

The maintained scale suite is separate from the small smoke suite. It preserves
scalar helpers from the supplied Kalman worktree, wraps them in fixed-horizon
Python loops, and retains original larger assets as capability probes.

| Family | Sizes | What is measured |
| --- | --- | --- |
| Scalar Kalman loop | 1, 4, 8, 16, 48, 128 updates; 8 operations/update | Both mean and variance, helper calls, incoming state error, independent exact recurrence, Lean proof and budget stages |
| IMU motion loop | 1, 4, 16, 48 updates; 8 operations/update | Position and velocity with independent accelerations and shared original Float `dt`, complete-horizon Lean error proof |
| Original Rust IMU application | 48 events, integer time and decisions | Explicit source-admission gap; it is not reduced to the supported motion loop |
| Original four-state graphs | 7,758 relative / 7,761 global operations, 46 stages | Frozen initialization, dense covariance propagation and correction-model analysis; candidates only |

Kalman profiles start at variance 1 m², process noise 1/8 m² and measurement
noise 1 m²; the initial mean and every independent measurement are in [-1,1] m.
The requested budgets stay 1e-4 m and 1e-6 m² across the whole family. These are
conditional scale fixtures, not measured sensor guarantees. IMU profiles start
at (0 m, 0.5 m/s), with independent accelerations in [-4,4] m/s² and a shared
original Float `dt` in [1/500,1/200] s. Their budgets are 1e-4 m and 1e-6 m/s.
The unchanged original integer-time Rust application's broader obligations are
kept separate. The two graph fixtures are manual exports, not verified compilers.

Each run retains actual expanded arithmetic/node/input counts, per-stage times,
accepted versus proposed bounds, full command records and JSON/Markdown summaries.
The stage timeout is 120 seconds. A timeout is unresolved; any bound not yet
checked stays proposed. `candidate_only` has no Lean theorem and is never a
certification result. Expected admission/analysis gaps must match their stated
reason, rather than passing because of an unrelated parser/setup/proof error.
Warm local times are workload diagnostics, not a solver or agent ranking.

The named 16/48-update Kalman cases may report Lean proof resource exhaustion
instead of the intended certificate/budget outcome. Only a recorded wall timeout
or deterministic heartbeat limit at `lean-proof` matches this allowance. Wrong
statements, unsupported source or other proof errors do not. Summaries list
`resource_limited_cases` explicitly, and those runs retain proposed bounds only.
The compiler's generated proof uses a two-million-heartbeat limit; raising the
wall limit alone does not remove that independent limit. Larger nonlinear state
expressions need better sharing or modular proof composition.

The reusable exact-magnitude refinement is checked by `native_ideal_refine`.
Proof generation restricts arithmetic facts and discards consumed bound facts;
these change proof construction, not the source algorithm, domain or requirement.
CI checks a smaller representative subset; the full scale target remains
available for performance and capability regression work.
