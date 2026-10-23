# Shared enclosure examples

`energy.py` preserves the original separately rounded multiplication schedule.
Its square and quartic functions are certified through both Gappa and FPTaylor;
the exact references are `x*x` and `(x*x)*(x*x)` on original binary64 inputs in
`[-1,1]`. Each producer's actual candidate becomes the Lean target.

`regularized_gain` computes `1/(x*x+1)`. The proof needs a positive native and
exact denominator across a domain spanning zero. The shared enclosure engine
retains nonnegative squares instead of multiplying unrelated interval factors.
The default producer and Gappa certify this example without an application proof.
FPTaylor's tighter reciprocal candidate remains beyond the current reconstruction;
its success verdict does not discharge that missing proof.

These are single-call arithmetic guarantees. The source, exact reference,
nearest/even binary64 model, gradual subnormals and engineering budgets remain
fixed. Normal source/runtime trust boundaries apply. No foreign proof trace or
unproved variable bound is a theorem premise.

```sh
python3 scripts/benchmark_numerics.py --replay \
  --case square_gappa --case quartic_gappa \
  --case square_fptaylor --case quartic_fptaylor \
  --case regularized_gain_lean --case regularized_gain_gappa \
  --tools /absolute/path/to/local-tools.json \
  --out .cache/numerics-generated/new-enclosure-suite
```

The [shared evidence guide](../../../docs/proof-evidence.md) describes the proved
rule vocabulary, rejection controls and coverage/cost comparison.
