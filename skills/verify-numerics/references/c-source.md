# Closed C source verification

Use `language: "c"` for the admitted C11 binary64 profile. It uses the default
`lean-flare` producer and the same domain, independent specification and output
budgets as scalar requests. Inspect the actual source before selecting this
profile; a parser accepting C syntax is not evidence of semantic support.

## Source and requests

The profile admits:

- `double` scalar parameters, initialized locals, assignments, scalar returns,
  unary signs and separately rounded `+ - * /` in their original order.
- Direct calls to closed, nonrecursive scalar helpers taking/returning doubles.
- Named double-only structs passed by value. `config.gain` becomes the original
  input name `config_gain`; each field needs its own domain.
- `const double values[static N]` read-only parameters, with `N` from 1 to 8.
  A buffer's cells become input names `values_0`, `values_1`, etc.
- A `void` entry updating one one/two-cell `double state[restrict static N]`
  parameter, optionally with read-only buffers and scalar/value-struct arguments.
  Outputs are the final writable cells in ascending order. A double-returning
  entry may use read-only buffers, but cannot mutate them.
- `for (unsigned int i = 0; i < N; ++i)` with a literal count from 1 to 128,
  direct indexing and checked unsigned index offsets. Integer counters are not
  floating-point data. Decimal/octal signed-int literals can be promoted exactly
  in double contexts; integer-only arithmetic, unsigned arithmetic values and
  casts are rejected.

There are at most 32 scalar input cells, 512 graph nodes, 2,000 visited statements
and 16 helper levels. Limits are admission bounds, not scaling guarantees. Loops
remain in the original C source and diagnostics; internal proofs expand this
bounded profile. Includes/macros/preprocessing, pointer variables, pointer escape,
allocation, globals, external calls, casts, arbitrary conditionals, variable loop
bounds and general C/C++ are outside it. Do not delete constructs from the input
just to obtain a certificate for a different program.

The provider's `examples/numerics/c/` has complete requests. For example,
`blend` supplies five original-input ranges (`state_0`, `state_1`, `observation_0`,
`observation_1`, `gain`) and these independent references:

```json
"specification": [
  "state_0+gain*(observation_0-state_0)",
  "state_1+gain*(observation_1-state_1)"
]
```

Example units/ranges/budgets are conditional demonstrations; obtain the actual
engineering contract. Use `inspect --language c`, `plan`, `run` and `replay` as in
[source-to-rust.md](source-to-rust.md). Confirm artifact locations first.

## What the Lean root covers

`c-vcs.json` records source locations, buffer extents, accesses and unsigned loop
counts. Replay regenerates it from the frozen source and compares it exactly.
Lean checks every admitted access index and counter bound. For buffers it also
checks execution of an ordered load/store model over `Array Float`: under region
validity/separation, every access succeeds and the result equals the numerical
kernel. The final root includes this execution, finite accurate results, the
budget, unchanged heap size and unchanged cells outside the writable region.
A read-only entry returns the original heap, and its read-only regions may overlap.

These regions are abstract typed cells, not byte-addressed C memory. The caller
must supply live, initialized, correctly aligned double objects of the declared
extent and the required writable/read-only separation. `restrict` obligations
are explicit root premises. Lean proves consequences of those premises; it does
not discover pointer lifetime/provenance at an arbitrary C call site. Option-valued
loads/stores belong to the Lean model; the original C API gains no runtime guard.
Parsing, source-to-model mapping, typed-object representation and compiler/runtime
fidelity remain declared trust boundaries. This is not a formalization of all C
undefined behavior or a verified C compiler.

The selected platform must use binary64 double, 32-bit unsigned int, nearest/even,
gradual underflow, no excess precision, contraction or fast-math reassociation.
The actual original C file is compiled at `-O0`, `-O2` and with address/undefined-
behavior sanitizers. Static assertions and floating-point probes check this
runtime profile; diagnostic words must agree with the model across all three
modes. Samples and sanitizers are diagnostics, not universal compiler/memory
proofs. Floating-point status flags and traps are outside the contract.

## Setup and Rust

Read [tool-setup.md](tool-setup.md#c-parser-and-compiler) to obtain pinned
pycparser 3.0 and a compatible Clang/GCC. Replay reparses the frozen C, so it needs
that pure-Python parser and the Lean library, but no C compiler or foreign prover.

Scalar and by-value-struct entries can use a retained `rust_port` with fresh
Charon/Aeneas extraction and an authored equivalence proof. The maintained
`mean_update_rust.json` verifies a reusable function with its helper intact.
This is agent-written production Rust with a checked bridge, not a general C-to-
Rust translator. Buffer delivery currently supports Lean only; a Rust slice or
mutable API needs a separate reusable source/extraction bridge. Preserve the
actual API and loops; put any horizon driver in a separately named function.

## Optional foreign verification tasks

Frama-C/WP 31.0 and Why3 1.8.2 were inspected on this source profile. The provider's
`scripts/export_c_vcs.py` retains actual tasks, source ACSL, tool identities and
solver reports. It is an optional inspection utility, not a registered producer
or Lean proof importer. JSON numerical requests are retained for identity but
are not translated to ACSL, so WP verdicts do not compare the same numerical
target. The current route proves its own source-derived conditions and uses
FLARE's reusable arithmetic validation. See the provider's
[C guide](https://github.com/duckki/flare-lean/blob/main/docs/sources/c-verification.md).
