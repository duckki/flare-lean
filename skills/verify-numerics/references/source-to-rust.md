# Executable Lean verification and optional Rust delivery

FLARE is the provider: one skill, a Python CLI and reusable Lean contracts.
An application checkout supplies source and a request; it does not need a Kalman
checkout or changes to its package manifest. Build the provider with its pinned
Lean/Mathlib first. Python 3.10+ and Elan/Lake are required.

Confirm the application verification directory and any Rust destination before
creating them, unless the user has already supplied or confirmed those paths.
The paths below are placeholders for that agreement, not automatic defaults.

```sh
export FLARE_ROOT=/absolute/path/to/flare-lean
export FLARE_VERIFICATION_DIR=/agreed/path/to/verification
(cd "$FLARE_ROOT" && lake build Flare)
python3 "$FLARE_ROOT/scripts/certify_numerics.py" capabilities
python3 "$FLARE_ROOT/scripts/certify_numerics.py" inspect \
  --language python --source /path/to/kernel.py --function step
python3 "$FLARE_ROOT/scripts/certify_numerics.py" plan \
  --request "$FLARE_VERIFICATION_DIR/request.json"
python3 "$FLARE_ROOT/scripts/certify_numerics.py" run \
  --request "$FLARE_VERIFICATION_DIR/request.json" \
  --out "$FLARE_VERIFICATION_DIR/certificate"
python3 "$FLARE_ROOT/scripts/certify_numerics.py" audit \
  --run "$FLARE_VERIFICATION_DIR/certificate"
python3 "$FLARE_ROOT/scripts/certify_numerics.py" replay \
  --run "$FLARE_VERIFICATION_DIR/certificate" \
  --out "$FLARE_VERIFICATION_DIR/replay"
```

Run/replay destinations must be new. Keep disposable application work beneath
`$FLARE_VERIFICATION_DIR/.cache/`; retain final evidence outside that scratch
directory. A generated extraction crate inside a certificate is checker evidence;
it does not select the user's production Rust destination. Shared tool downloads
belong outside the checkout; see [tool-setup.md](tool-setup.md).

Shared Lake caching is optional; configure it as described in the provider's
`docs/development.md`. Commands inherit the caller's settings.

Requests use `schema: numerics-request-v1`. See the provider's
`examples/numerics/scalar_kalman.json` for a complete example.

| Field | Meaning |
| --- | --- |
| `language`, `source`, `function` | Explicit adapter; source path relative to the request |
| `domain` | Original input names mapped to inclusive rational-string `[lo, hi]` ranges; finite binary64 inputs are additional premises |
| `outputs` | One or two outputs in return order, each with `name`, `unit`, positive rational-string `limit` |
| `specification` | Independently reviewed exact expressions on original input names using rational/decimal constants and `+ - * /` |
| `backend` | `lean-flare` (default); independent numerical proof/checking path |
| `producer` | `lean-flare` (default), `gappa`, `fptaylor` or `precisa`; see `tool-integration.md` for evidence and validation roles |
| `analysis_tools` | Tool-name map with `executable`, optional expected `sha256` and optional tool-data `base` |
| `arithmetic` | Optional full model from `capabilities`; mismatched precision/rounding/FMA/subnormal semantics are rejected |
| `target` | `lean` (default) or `rust-aeneas` |
| `timeout_seconds` | Finite positive per-command limit, default 120 |
| `contract_cache` | Optional explicit directory for compiled helper-contract reuse; prefer the agreed verification directory's `.cache/contracts/`; replay always recompiles saved sources |
| `proof` | Optional saved Lean proof and bounds; see `lean-conversion.md` |
| `python_method` | Optional explicit state, fixed attributes and measurement horizon for a selected `Class.method`; see below |
| `python_branches` | Explicit terminal scalar Python conditional profile; see [conditionals.md](conditionals.md) |
| `rust_port` | Optional retained Rust implementation and checked equivalence module for `rust-aeneas`; see below |

Exact specification decimals are rationals; source literals mean their stored
binary64 words. A changed literal interpretation needs a proof. Example ranges
and budgets are conditional demonstration inputs, not engineering defaults.
Expression-list reference bridges use unfolding and ring normalization; fold
bridges use a shared step identity when helper composition applies, otherwise
definitional equality. Other identities can use a saved authored proof.

## Admitted source subsets

The scalar profiles select a numerical function with one or two scalar results,
finite constants, unary signs and separately rounded `+ - * /`, preserving
parentheses and operation order. Python also admits local helpers and fixed
tuple loops as described below. A separate [array profile](arrays.md) admits
fixed-shape built-in Python list products with explicit range loops and fresh
output storage. The separate [conditional profile](conditionals.md) admits one
terminal scalar Python branch and an exact conditional specification. In the
ordinary scalar profiles, external calls, arrays, dynamic loops, branches,
casts, fast-math and custom numeric objects are excluded. Source-language implementations remain trusted;
actual-runtime word diagnostics test samples independently of graph execution.

| Adapter | Forms | Runtime |
| --- | --- | --- |
| `python` | Positional/untyped or `float` parameters, scalar locals, tuple assignments, updating assignments, local numerical helpers, fixed literal-tuple loops, docstrings | CLI's Python with built-in floats |
| `julia` | Long/short functions, optional `::Float64` parameters, explicit/implicit returns, tuple results and updating assignments | Julia in IEEE mode, startup/history disabled, scratch depot |
| `matlab` | Function files with named outputs, optional `end`, semicolons, line continuations, scalar dot operators | MATLAB or GNU Octave, recorded explicitly |
| `rust` (automatic scalar profile) | One `pub fn`, named `f64` parameters, `f64` or `(f64, f64)` result, scalar `let`, `let mut`, shadowing, assignments, return/tail expression | `rustc` |

Python modules may contain a closed collection of numerical functions. Calls
are positional and direct; recursion, external functions, decorators, defaults,
global mutation and function-valued arguments remain unsupported. The selected
call graph is expanded into the same immutable arithmetic graph.

The scalar Python profile's `for` loops iterate a literal tuple of 1–128 values. The tuple
is evaluated before iteration, including when a loop body reassigns a name
used in that tuple. `break`, `continue`, loop `else`, returns inside loops,
`while`, `range`, arbitrary iterable inputs and container mutation are excluded.
Expansion is capped at 20,000 visited statements, 10,000 arithmetic/constant
nodes and helper depth 32. These are finite-horizon certificates; no theorem
for arbitrary horizons or generic Python interpreter is claimed.

For an independent recurrence, `specification` can be a two-state `fold` object:
`initial` lists two exact expressions on original inputs; `sequence` lists
original input names in order; `state` gives two fresh state names; `element`
names the current observation; and `step` lists two exact next-state equations.
See `examples/numerics/scale/kalman_004.json` for a complete example. This does
not reset error at a helper or iteration boundary. The generated proof connects
the whole lowered computation to the fold. Current automatic fold equivalence
uses definitional equality; other algebra can use an authored equivalence proof.

Scalar Python/Julia integer constants up to 2^53 are admitted only when promoted exactly
by a Float operand; integer-only computations and results are rejected. MATLAB
numerals have double type. Rust literals must use decimal floating syntax;
suffixes, hex literals, macros and block comments are outside this subset.
Runtime failures or word mismatches leave a run unresolved.

### Ordinary scalar instance methods

Select `function: "Filter.update"` and supply an explicit binding, for example:

```json
"python_method": {
  "state": {"x": "x0", "dx": "v0"},
  "constants": {"dt": 0.125, "g": 0.5, "h": 0.125},
  "sequence": ["z0", "z1"]
}
```

The domain names are the two initial-state inputs followed by the 1–128 distinct
measurement inputs. State attribute order must match the method's two scalar
return values. Constants are finite JSON floating-point numbers interpreted as
stored binary64 words, not exact decimal coefficients. They must stay immutable.
Use `plan` with this request; `inspect` selects standalone functions only.

The selected method takes `self`, one measurement and optional scalar gains
defaulting to `None`. Leading `if gain is None: gain = self.attribute` statements
must resolve every gain from the configured constants. The rest uses admitted
scalar arithmetic, locals and direct ordinary `self.attribute` reads/writes.
Each auxiliary attribute must be assigned before reading within the call; only
the two configured state attributes carry between calls. The adapter lowers the
selected original method AST and preserves its arithmetic order across the
frozen horizon. It rejects custom inheritance, descriptors, attribute hooks,
instance escape and general branches. Numeric error still accumulates across
all calls and is checked against an independent exact fold.

Module imports, initialization and the constructor are not executed. Diagnostics
execute the selected original method body on a plain scalar namespace. The
caller must establish that the selected body is the one invoked, with ordinary
attributes matching the binding and omitted optional gains. Construction,
monkey-patching, subclass dispatch and wider application behavior are outside
this conditional certificate. The report records these assumptions and the
fixed attributes' exact hexadecimal values.

For Julia/MATLAB/Rust, select an executable using:

```json
"source_runtime": {"kind": "julia", "executable": "/absolute/path/to/julia"}
```

Kinds are `julia`, `matlab`/`octave` or `rustc` respectively. Otherwise the CLI
searches PATH; MATLAB is preferred over Octave. An Octave test does not establish
MATLAB runtime behavior. Paths are passed as separate arguments. Interpreter
versions, executable hashes, commands and output streams are retained.

## Optional Rust extraction

For `rust-aeneas`, obtain a matching Charon/Aeneas tool pair and its compiled Lean
library using [tool-setup.md](tool-setup.md). Tested revision records live in
`tools/numerics/aeneas-revisions.json`; they describe the compatible experimental
Float fork, not evidence that an existing binary matches those revisions.
Requests configure:

```json
"rust_tools": {
  "charon": "/absolute/path/to/charon",
  "aeneas": "/absolute/path/to/aeneas",
  "lean_lib": "/absolute/path/to/aeneas/compiled/lean"
}
```

Alternatively set `FLARE_CHARON`, `FLARE_AENEAS`, `FLARE_AENEAS_LEAN_LIB`;
executables can also be found on PATH. `lean_lib` must contain `Aeneas.olean`.
Charon may require its sibling driver and the extraction nightly toolchain.
The delivered crate pins the runtime Rust version in `tools/numerics/rust-toolchain.toml`.

Without `rust_port`, the CLI emits an operation-ordered straight-line Rust kernel
from a non-Rust input. This is an internal checker/probe artifact. For a requested
Rust delivery, author the reusable port described below, preserving the original
API, state and control structure. Rust input is copied unchanged and wrapped for
extraction. Charon and Aeneas produce fresh Lean source;
`source_equiv` proves the extracted return equals the ordered Float kernel.
The final root theorem includes that actual return, its finiteness, accuracy
and budget. Debug/release native Rust outputs are compared with the actual
source runtime and graph on diagnostic words. No compiler or machine-code proof
is claimed; translation/runtime/Float-model fidelity remain declared boundaries.

### Retaining an independently written Rust port

A non-Rust source can supply a single-file Rust implementation instead of the generated
straight-line kernel. Select `rust-aeneas` and provide:

```json
"rust_port": {
  "source": "../rust/src/lib.rs",
  "function": "verification_horizon",
  "proof_source": "PortEquiv.lean",
  "equivalence": "Port.source_equiv"
}
```

Place the reusable implementation in the agreed Rust destination. Preserve its
original functions/methods, state and configuration, defaults, mutation order
and loops. For repeated-call certificates, add a separately named finite-horizon
driver function that invokes the production API in a loop; select that driver
as `rust_port.function`. For a single call, select the production entry directly.
The current single-file route can retain both the API and this separate function in
the same file. Do not duplicate the method's arithmetic in the driver or deliver
an unrolled body. Expansion belongs in the internal model or Lean proof.

The Rust function takes all original graph inputs in order and returns the same
one/two-output type. Both source paths are relative to the request. FLARE freezes
the Rust bytes and proof module, extracts that actual port, and requires the
named Lean theorem to prove `Generated.kernel args = .ok (kernel args)` for all
Float inputs without extra premises. The file is copied unchanged into the
extraction crate as `src/original.rs`. Structs, methods and loops can remain when
Charon/Aeneas supports their extraction; this does not extend the automatic
scalar Rust frontend. The saved module can import `Workflow.Kernel` and
`Workflow.Generated.Funs`; it is compiled as `Workflow.RustEquiv` before the main
proof. The root's axiom audit also covers this equivalence. A false bridge or an
additional axiom cannot supply a completed certificate.

The equivalence proof must discharge any loop termination, indexing and integer
overflow obligations needed for a successful return. Numerical analysis still
covers the whole original-input horizon.

Freshness checks include the live port/proof identities. Replay uses the frozen
Rust/proof assets and extracted Lean model without rerunning Charon or Aeneas.
Source/IR and Rust debug/release diagnostics remain required for certification.

## Results, replay and freshness

`run` freezes source, request and graph; admits the actual source runtime;
selects a producer and freezes its obligation/evidence (or loads an authored proof); checks Lean proofs and
an independently generated root-type/axiom checker; then runs word diagnostics.
Only checked bounds are recorded as `accepted_bounds`.
The external routes must prove their actual candidate conclusions in Lean;
unproved candidates remain unresolved. See [tool integration](tool-integration.md).

| Status | Interpretation |
| --- | --- |
| `needs_input` | Missing domain, specification or engineering output target |
| `unsupported_or_invalid_request` | Source/selector/schema outside admission |
| `unresolved` | Missing prerequisite, analysis gap, timeout, proof failure or diagnostic mismatch; inspect `failure_stage` and logs |
| `budget_not_met` | Lean checked the allowance and diagnostics passed, but at least one requested limit is tighter |
| `certified` | Lean root, diagnostics and all budgets passed under reported premises |
| `replayed` | Saved Lean sources checked again; `certificate_status` preserves the original run's status |

Review `report.md`, `result.json` and `lean/Workflow/Proof.lean`. The root is
`Workflow.Certificate.certificate`. `Workflow/Check.lean` independently ascribes
its expected type and audits its axiom closure. A Lean proof's numeric inputs
are premises; all numerical inequalities connecting them to the claimed result
must be discharged. Units are annotations, not a dimensional-analysis proof.

`audit` checks frozen artifacts and current source, authored proof, provider and
runtime/extraction executable identities and the Aeneas Lean model file hashes.
It does not validate every dynamic dependency or compiler driver.
`audit --frozen` checks artifact hashes only. Neither is a proof check or a
cryptographic signature of authorship.

`replay` checks saved Lean sources without rerunning analysis, source runtimes,
Rust extraction or an LLM. It reconstructs the kernel/specification from the
frozen request and source and regenerates the expected root check. It uses the
current provider's compatible Lean library; Rust replay also needs the compiled
Aeneas Lean model, but not Charon/Aeneas executables. Its model files must match
the recorded hashes. Keep original evidence with the replay: replay does not
rerun diagnostics or upgrade the original status.
If the model library moved, use `replay --aeneas-lean-lib /new/model/path`.
This selects a location for the same recorded model, checks its hashes, and
records the override in `replay.json`; frozen source and proof records stay intact.

The implemented producer supports positive native and ideal divisor floors.
Its fixed grids can inflate bounds or lose a tiny positive denominator. Failed
budgets are not observations of large actual error. Repeated calls, physical
coverage and covariance positivity need additional contracts and composition.

## Larger Rust APIs

Use the separate [Rust application proof-bundle route](rust-applications.md) for
modules, structs, slices, enums/results, integer timestamps and validation gates.
It uses the same CLI and tool configuration but replaces scalar domain/output
fields with a separately reviewed Lean contract and authored proof modules.
The 48-event IMU fixture covers the actual public API and all error outcomes;
this does not expand the automatic scalar parser's admitted subset.
