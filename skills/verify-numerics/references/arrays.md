# Fixed-shape Python arrays

Use this profile for explicit matrix/vector products on built-in Python lists
of built-in binary64 floats. Inspect the original source; retain its loops,
indexing, accumulator initialization and separate multiply/add schedule.

## Select shapes and the exact reference

Set `python_arrays` to the original parameter names and their fixed dimensions:

```json
{
  "python_arrays": {"transition": [2, 2], "state": [2]},
  "specification": {"kind": "matrix", "expression": "transition @ state"},
  "target": "lean"
}
```

There are two input parameters: a rank-two left matrix and a rank-one vector
or rank-two right matrix. Inner sizes must match. Dimensions are 1–8, with at
most 32 output entries; these are admission limits, not a guarantee that every
request closes within resource limits. The selected function returns a fresh
vector or rectangular matrix. Matrices use nested lists and row-major output
order. A vector is interpreted as a one-column matrix in the exact reference.

Use `inspect` to obtain component names for the domain and output requirements:

```sh
python3 "$FLARE_ROOT/scripts/certify_numerics.py" inspect \
  --source application.py --function predict --language python \
  --python-arrays '{"transition":[2,2],"state":[2]}'
```

Provide exact rational ranges for each original component, such as
`transition_0_0` and `state_1`, and a name, engineering unit and error budget
for each returned component. Review the exact matrix expression independently.
Then use the ordinary `plan`, `run` and `replay` commands. Artifact destinations
follow the agreement in the main skill; this profile creates no new destination.

## Admitted source

- Ordinary positional functions and direct local helpers, with optional
  `float`, `list[float]` or nested-list annotations.
- Rectangular float-list literals, scalar-list repetition for fresh buffers,
  fixed indexing, and scalar updates to fresh local buffers.
- `range(size)` loops, where `size` is a statically known integer or `len` of
  an admitted list. Each loop has at most 32 iterations.
- Shape assertions of the form `assert len(array) == size`, with no message.
  Every assertion must follow from the requested shapes. Rank and every
  reached index are checked during admission.
- Each output follows the ascending dot-product schedule starting at `+0.0`:
  multiply a left/right entry, then add it to the accumulator, without FMA or
  reassociation. The profile checks this schedule, not just real equivalence.

Inputs and helper arguments are read-only. Local buffers must have fresh,
independent rows. Array alias assignment, repeated mutable rows, input writes,
negative or dynamic indices, slices, data-dependent branches, imports and
NumPy/BLAS calls are outside this profile. Input operands may share storage
because the admitted computation only reads them. Ordinary Python guards
beyond these shape assertions and their error behavior remain separate work.

## What the root establishes

The named root accepts shaped Lean arrays and the original component domains.
It proves the input shape guard, output shape, successful FLARE dense execution
with the same returned entries, output finiteness, and error relative to an
independent real matrix product. Its numerical premises and transitive axioms
are checked. The generic `Matrix.OrderedProduct.multiply_eq` bridge preserves
native operation order; `Matrix.Multiplication.multiply_accuracy` establishes
successful finite execution. Component allowances are checked by the shared
binary64 validator.

The restricted Python-to-Lean mapping and runtime/hardware fidelity remain
declared trust boundaries. Runtime samples compare original Python and graph
words, including signed zeros and subnormals. Replay regenerates the source
array model and independently checks the saved root without inference or a
producer. These guarantees do not transfer to NumPy, BLAS, a reordered reduction
or an array Rust port. Extend and check their bridges before claiming support.

Maintained requests under `examples/numerics/arrays/` cover two-state linear
prediction, calibration matrix composition, a three-term projection, a
four-state linear prediction and the one-entry boundary. They reuse the same
source adapter and proof machinery. The larger exported four-state covariance
graphs remain analysis probes; the new prediction source is a separate case.
