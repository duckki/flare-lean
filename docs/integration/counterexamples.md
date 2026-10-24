# Lean-checked counterexamples

A counterexample answers a universal requirement with one allowed input that
violates it. The CLI accepts an untrusted witness, proves its domain membership,
checks the ordered native execution and independent exact reference in Lean,
then checks the root's type and transitive axioms independently. Actual-source
execution at that witness supplies a separate runtime diagnostic.

This route produces `counterexample`, not `certified`. A satisfying witness,
failed proof, setup failure or timeout stays unresolved. An error allowance above
budget remains `budget_not_met`; it does not establish an attained failure.

## Request

Use the ordinary `numerics-request-v1` schema with a `counterexample` selection.
For the [README covariance source](../../examples/numerics/counterexamples/naive_covariance.py), the
[complete request](../../examples/numerics/counterexamples/naive_covariance.json) uses:

```json
{
  "outputs": [
    {"name": "posterior variance", "unit": "m²", "property": "strict_positive"}
  ],
  "counterexample": {
    "inputs": {"p": "0x3ff0000000000000", "r": "0x3c90000000000000"},
    "output": 0
  }
}
```

Input words contain exactly 16 lowercase hexadecimal digits after `0x`. They
preserve signed zeros and subnormals. `output` selects one output by its zero-based
index. All original inputs still need finite exact-rational domain ranges, and
every output needs an independent rational scalar reference, name and unit.

Two requirements are admitted:

| Output fields | Root proves at the selected witness |
| --- | --- |
| `"property": "strict_positive"` | The independent exact result is positive and the finite native result is nonpositive |
| `"limit": "<positive rational>"` | The attained absolute difference from the independent exact result strictly exceeds that limit |

Do not combine strict positivity with an error limit. Ordinary error-bound
requests keep their existing schema and behavior. The positivity witness route
does not yet provide automatic universal positivity proofs.

The witness can come from engineering analysis, an agent, a sample or a foreign
search tool. The CLI can validate supplied witnesses or use the selected CBMC
search route below. A search verdict cannot replace the Lean root.
Use a new run for each proposed witness; retain failed attempts and the original
requirement instead of loosening the budget until a different result succeeds.

## Run and replay

After agreeing application artifact locations, run from a built FLARE checkout:

```sh
python3 scripts/certify_numerics.py run \
  --request examples/numerics/counterexamples/naive_covariance.json \
  --out .cache/numerics-generated/covariance-failure
python3 scripts/certify_numerics.py replay \
  --run .cache/numerics-generated/covariance-failure \
  --out .cache/numerics-generated/covariance-failure-replay
```

These are repository regression paths. For an application use the agreed
verification directory, with scratch under its `.cache/`. Output directories
must be new.

Expected result:

```text
status: counterexample
p = 1, r = 1/18014398509481984
native posterior = 0
independent exact posterior = 1/18014398509481985 > 0
requirement: strictly positive — violated
Lean entry: Workflow.Counterexample.counterexample
```

The sealed run retains the original source, request, ordered graph, proposed
`witness.json`, Lean sources, command logs, runtime identity, witness diagnostics
and `report.md`. The root includes all input-domain conditions, the computed
native output tuple, finite outputs, every reported native/reference value and
the violated requirement. Only `propext`, `Classical.choice` and `Quot.sound` are
allowed in its axiom closure. No `native_decide` is used.

Cold replay parses the frozen source to reconstruct the kernel and reconstructs
the required root type from the request and untrusted witness record. It compiles
the saved proof into a new directory and regenerates the root check. It does not
evaluate the source or graph, search for witnesses, run a bound producer, invoke
a translator or consult an LLM. A resealed changed output, reference, domain or
missing theorem must still satisfy the reconstructed type and axiom audit.
`audit` checks file identities/freshness only; it is not replay.

## Supported scope and remaining boundaries

Closed scalar Python (including selected full-module definitions), C++ header,
Rust, Julia and MATLAB-compatible frontends can use this
path, subject to their existing source-runtime admission. Python, C++ and Rust have
maintained end-to-end witnesses; Julia/MATLAB routes need their corresponding
runtime and separate application evaluation. The graph has at most 32 nodes,
one or two finite outputs, separately rounded binary64 `+ - * /` and negation.
Selected scalar helpers and bounded literal-tuple expansion remain part of the
admitted graph. There is no new source-language parser or compiler proof here.

Array, branch, counted-invariant, C memory, FMA, square-root, mixed-storage and
Rust application profiles need separate counterexample bridges. Rust-port
delivery, exceptional outcomes and authored witness arguments are not admitted
by this automatic route. The standalone authored-proof route remains available
for properties outside this closed scope.

Frontend mapping and runtime/compiler/hardware fidelity remain trusted. The
actual-source witness diagnostic can reject a mismatch but does not prove source
equivalence on other inputs. Review units, domain, reference and physical premises
as for a positive certificate.

## CBMC witness search

For strict positivity, replace the supplied `counterexample` field with:

```json
"counterexample_search": {"tool": "cbmc", "output": 0},
"search_tools": {"cbmc": {"path": "/absolute/path/to/cbmc"}}
```

Keep the original domain, independent reference and selected output property.
Run/replay use the ordinary CLI. The admitted search route needs CBMC 6.11.0,
at most eight scalar inputs and 32 separately rounded binary64 nodes. It exports
a bounded C harness as an **unproved search aid**, retains the JSON trace and
extracts exact visible input-word assignments. The ordinary witness checker
then proves admissibility, actual model execution and the violation in Lean,
with separate original-source diagnostics. The certificate is in `witness-run/`.
Parent replay checks that this child preserved the original source/contract and
replays its root without CBMC. A search verdict is never imported as a proof.

`no_witness`, missing tools, unsupported versions, timeout and a candidate rejected
by Lean are unresolved outcomes. A successful bounded search with no failure is
not a positive numerical theorem. Search currently targets positivity only;
absolute-error search and further source/memory profiles need separate support.

A retained ROS header case finds a positive subnormal degree input whose computed
radians round to zero. This is a separate positivity contract; it does not change
the held-out accuracy case's frozen domain or error requirement. See
[delivery evaluation](../evaluation/delivery-evaluation.md) for evidence and
[CBMC's command interface](https://diffblue.github.io/cbmc/man/cbmc.html) for the
external tool's trace and floating-point options.
