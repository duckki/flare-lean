# Numerical integration evaluations

The [evaluation report](../../../docs/evaluation/numerical-integrations.md) records
four bounded decisions. Tool revisions and scopes are in
[`evaluation-tools.json`](../../../provider/manifests/evaluation-tools.json).
These scripts expose evaluation adapters; Daisy and LeanCert are not registered
production backends.

Build FLARE first as described in the [development guide](../../../docs/development.md).
Run the typed-summary and exact-zero comparison without external tools:

```sh
python3 benchmarks/numerics/integrations/evaluate.py typed \
  --out .cache/numerics-generated/new-typed-evaluation
```

The comparison holds the original requests fixed and disables the new route for
the baseline. A separate quartic comparison fixes the actual candidate as well.
Every success gets a frozen-source replay with producer/inference calls blocked.
The [provider regressions](../../../provider/tests/numerics/test_numerics_checked_bounds.py)
include corrupted ranges, errors, rounding allowances and exact-operation rules.
`CheckedControls.lean.txt` tests incoming error and gradual-underflow obligations.

## LeanCert Core

Clone LeanCert outside the checkout, check out the pinned revision, and supply
that clean source directory:

```sh
python3 benchmarks/numerics/integrations/evaluate.py leancert \
  --source /path/to/pinned/leancert \
  --out .cache/numerics-generated/new-leancert-evaluation
```

The runner checks the source revision and matching Mathlib dependency revisions,
then builds a scratch copy against FLARE's populated package/build cache.
`Probe.lean.txt` exercises checked APIs with explicit kernel computation.
`Composition.lean.txt` composes a real enclosure with FLARE native addition.
`ModuleBoundary.lean.txt` and `AffineKernel.lean.txt` must fail for their recorded
compatibility/reduction reasons. Rejected cases are never reported as certificates.

## Daisy

Use the pinned source, a supported Java 24 installation, sbt 1.9.9, and Z3 4.15.4
for subdivision. Apply the evaluation-only exact-candidate export patch and build
Daisy in its own source directory:

```sh
git apply /path/to/flare-lean/provider/patches/daisy-exact-candidates.patch
JAVA_HOME=/path/to/jdk24 PATH=/path/to/jdk24/bin:$PATH sbt compile script
```

The patch exports the internal rational numerator and denominator. The ordinary
rounded display and CSV output are not safe exact candidate inputs. Run:

```sh
python3 benchmarks/numerics/integrations/evaluate.py daisy \
  --source /path/to/pinned/patched/daisy \
  --java-bin /path/to/jdk/Contents/Home/bin \
  --z3-bin /path/to/z3/bin \
  --out .cache/numerics-generated/new-daisy-evaluation
```

The default trial supplies explicit zero input-error annotations to match original
binary64 inputs. `--input-errors conservative` reproduces the earlier
`--noInitialErrors` run, which still adds default input-rounding allowances in
the pinned Daisy version. The report retains both sets of actual candidates.

The small trial admits one scalar output, exact small integer constants/endpoints,
Float64 arithmetic, no optimization, and bounded subdivision for the reciprocal.
It freezes the ordered query, raw rational payload and generated Lean proof.
Daisy's Scala frontend also needs its `library/` files in the working directory;
the runner retains a copy beside each query. Tool absence, source extraction
failure, analysis failure and Lean rejection remain separate recorded stages.

Use a fresh output directory for each run. Logs and full certificates stay under
the ignored output directory; compact measurements are retained in
[`results.json`](results.json). Source downloads and their build products are not
vendored into FLARE.
