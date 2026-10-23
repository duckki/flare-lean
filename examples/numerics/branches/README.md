# Conditional numerical code

These ordinary Python functions use the reusable
[`python_branches` profile](../../../skills/verify-numerics/references/conditionals.md).
The exact reference can select a different branch from native binary64 execution.
The `python_branches: true` cases retain all four native/exact flows in Lean.
The explicit guard-local case proves native/exact agreement for its direct input
comparison and checks arithmetic only on reachable branch domains.

| Request | Domain and reference | Expected result |
| --- | --- | --- |
| `innovation_magnitude.json` | Two finite measurements in `[-10,10]` m; exact absolute difference | `certified`: requested `10^-6` m allowance |
| `gate.json` | Finite signal in `[-2^-52,2^-52]`; exact indicator of `signal+1 >= 1` | `certified`: one-unit allowance |
| `gate_precisa.json` | Same source, domain, reference and budget | `certified`: actual PRECiSA maximum candidate `1` |
| `innovation_magnitude_precisa.json` | Same source, domain, reference and budget | `budget_not_met`: actual PRECiSA maximum candidate about `40` m |
| `guarded_reciprocal.json` | Finite input in `[0,2]`; exact `1/x` when `x >= 1/2`, otherwise zero | `certified`: local denominator premise and `10^-6` reciprocal-unit allowance |

The gate is intentionally discontinuous. At `signal = -2^-54`, the native sum
rounds to `1.0`, while the exact sum is below one. The gate results differ by
one unit. PRECiSA reports `stableError: 0` and `unstableError: 1`; the adapter
must prove the latter allowance in Lean. Tests replace it with zero or a false
stability claim and require Lean rejection. The certificate is an upper-bound
theorem; this concrete input explanation is not a separate saved Lean
counterexample certificate.

The innovation example illustrates a conservative analyzer result. PRECiSA's
unstable-flow estimate is much larger than the default Lean procedure needs.
The adapter proves PRECiSA's actual candidate and reports that it misses the
unchanged engineering budget. It does not attribute the default proof's tighter
allowance to PRECiSA.

## Reproduce

From the provider root, after `lake build Flare`:

```sh
python3 scripts/benchmark_numerics.py \
  --case branch_innovation --case branch_gate --case guarded_reciprocal --replay \
  --out .cache/numerics-generated/branches

# Optional Linux PRECiSA installation; see the setup guide for prerequisites.
export FLARE_PRECISA=/shared/tool-pool/precisa-2626ba1/install/bin/precisa
python3 scripts/benchmark_numerics.py \
  --case branch_gate_precisa --case branch_innovation_precisa \
  --out .cache/numerics-generated/branches-precisa
```

Each run retains source, independent request, ordered model, proposed/accepted
bounds, logs and `Workflow.Certificate.certificate`. Use normal
`replay --run ... --out ...` into a fresh directory for producer-free replay.
These are provider regression paths; applications use the confirmed verification
directory.

The pinned build and real producer/Lean runs were exercised on Ubuntu ARM64,
with frozen proof replay on macOS ARM64. This is candidate reconstruction,
not a PVS proof import. Source mapping and compiler/runtime correspondence remain
declared trust boundaries. The `true` profile requires safe finite scalar
arithmetic in both arms over the full domain. The default producer's explicit
`{"domains":"guard"}` profile proves local domains for a direct input/literal
guard. The reciprocal example therefore admits zero in the original domain
without executing or assuming safe division on the inactive arm. Arbitrary
control flow, dispatch and automatic Rust delivery remain outside these profiles.
