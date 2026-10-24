# Binary32 storage with binary64 computation

FLARE certifies a closed mixed-precision Python profile: explicit
`float(np.float32(x))` storage round trips inside ordinary binary64 computation.
The maintained applications include sensor calibration, normalized residuals and
repeated storage through a helper. Each retains the original source, independent
exact-real reference and engineering budget.

## Source and arithmetic contract

Use CPython 3.13/3.14, NumPy **2.4.0**, and `python_mixed: true`. The source has
exactly one `import numpy as np`. Parameters and returned scalar values are
built-in binary64 floats. Each paired conversion first rounds to binary32 and
then promotes that stored value exactly to binary64. Ordinary operations keep
their original order and separate binary64 rounding sites.

```python
import numpy as np


def calibrate(sample: float, gain: float, offset: float) -> float:
    quantized = float(np.float32(sample))
    adjusted = gain * quantized + offset
    return float(np.float32(adjusted))
```

The exact reference is `gain*sample+offset` on the original inputs. It does not
reset the reference to the quantized sample or another rounded intermediate.
This checks storage error, computation error and later storage together.

```sh
python3 scripts/certify_numerics.py inspect --language python \
  --source examples/numerics/mixed/kernels.py --function calibrate --python-mixed
python3 scripts/certify_numerics.py run \
  --request examples/numerics/mixed/calibrate.json \
  --out .cache/numerics-generated/mixed-calibrate
python3 scripts/certify_numerics.py replay \
  --run .cache/numerics-generated/mixed-calibrate \
  --out .cache/numerics-generated/mixed-calibrate-replay
```

These are ignored provider regression destinations. Application artifacts use
the skill's confirmed verification directory, with scratch in its `.cache/`.

The arithmetic object must match the admitted graph:

```json
{
  "format": "binary64",
  "rounding": "nearest-even",
  "subnormals": "gradual",
  "fma": false,
  "reassociation": false,
  "storage": "binary32",
  "conversion": "narrow-nearest-even-exact-widen"
}
```

Local scalar helpers and bounded literal-tuple loops are admitted within a
32-node graph. One or two scalar outputs are supported. The profile rejects
aliases, shadowed `np`/`float` calls, unpaired casts, implicit NumPy scalar
promotions, other dtypes, binary32 arithmetic and composition with the array,
conditional, counted-loop or Python math profiles. These need explicit bridges.
External-producer and Rust-delivery routes retain their existing admission;
installing a tool does not establish support for these cast semantics.

## What Lean proves

`Flare.FloatFormat` holds shared format selection, exact packing and rounding
inference for the pinned binary32 and binary64 models. Existing binary64
rounding declarations retain their statements and assumptions, with their proofs
instantiated from this shared engine.

`Binary32.Conversion.narrow` uses Lean's `Format.binary32` nearest/even rounding
and packing. `widen` pads the decoded binary32 mantissa into a canonical binary64
representation. `widen_exact` proves exact promotion for **every finite binary32
value**, including signed zero and subnormals.

For narrowing, a checked native magnitude at most `2^N`, with
`-126 ≤ N ≤ 126`, gives the conservative one-ulp allowance `2^(N-23)`.
The lower exponent floor covers gradual underflow; the upper bound proves finite
packing with margin from overflow. Values outside this admission can need a
stronger proof even when a particular cast would be finite. The bound is not a
claim that this much error is attained, nor a half-ulp estimate.

`Binary32.StorageBounds.native_roundTrip` adds that allowance to both the native
range and accumulated error. Later addition, multiplication, division and
storage continue carrying incoming error. The final Lean theorem checks the
independent reference, finite execution, engineering budget and transitive axiom
closure. Kernel tests cover ties, mantissa carry, signed zero, underflow and exact
promotion of the smallest subnormal.

The pinned Lean built-ins `Float.toFloat32` and `Float32.toFloat` are **opaque**.
FLARE's executable conversion definitions use the model directly; no theorem
about those opaque built-ins, compiler casts or an arbitrary runtime is assumed
as a Lean axiom.

## Runtime boundary and replay

[NumPy's scalar documentation](https://numpy.org/doc/2.4/reference/arrays.scalars.html)
describes its storage types. The selected NumPy conversion and CPython operations
are assumed to implement the declared IEEE contracts. Source mapping,
NumPy/CPython/compiler/hardware correspondence remain explicit trust boundaries;
Lean proves the model-backed conversions and numerical root.

Admission retains the executable, actual NumPy version and loaded library hashes,
plus OS/architecture/version metadata. Nearest/even, signed-zero and subnormal
probes and original-source/IR word comparisons are sampled diagnostics, rather
than universal implementation proofs. Diagnostics use nontrapping NumPy error
policy; floating status flags and warning/exception policy are outside the theorem.
The recorded identities are not a complete fingerprint of every linked platform
library.

Frozen replay reparses the saved source and recompiles saved Lean proofs without
loading NumPy, running producers or repeating inference. Live freshness auditing
checks recorded runtime identities; replay does not validate a changed runtime.

See the [maintained cases](../examples/numerics/mixed/README.md) for domains,
budgets and reproducible benchmark commands.
