# Counted Python loops with a compact invariant proof

Use `python_counted` for an ordinary Python API with one integer count parameter,
two scalar state arguments and optional fixed scalar configuration arguments:

```python
def run(x, y, observation, steps):
    for index in range(steps):
        x, y = step(x, y, observation)
    return x, y
```

The selected helper uses admitted scalar Python arithmetic and returns both new
states. The index is unused, arguments are positional, and configuration remains
fixed across calls. The helper receives every original float/state argument once;
argument permutation is supported. The body has at most 64 lowered scalar nodes.
Input streams, indexing, data-dependent loops, branch bodies and arbitrary state
mutation need additional source support. This route currently targets Lean with
`lean-flare`; it does not automatically deliver a Rust loop port.

Select the original count explicitly and supply an independent exact recurrence:

```json
{
  "python_counted": {"parameter": "steps", "iterations": 1024},
  "specification": {
    "kind": "iterate",
    "initial": ["x", "y"],
    "state": ["m", "p"],
    "step": ["(m+observation)/2", "(p+observation)/2"]
  }
}
```

This extends a complete request with source, function, original **float** input
domains and two output allowances/units. The count is a fixed nonnegative integer
configuration, not an additional floating input. Selected counts are bounded by
65,536 as a workflow resource limit; negative counts are outside this profile.
Use `inspect --python-counted '{"parameter":"steps","iterations":1024}'` to
inspect the source, then the usual `plan`, `run` and `replay` commands.

## What Lean checks

The provider retains one helper graph and models the actual range loop as a
compact repeated fold. It proposes a uniform native/exact state invariant from
the original domains and requested allowances. Lean proves initialization,
finite step execution, reached-state bounds, divisor floors and preservation of
the invariant. Local contracts accept separate native and exact incoming states
with their accumulated error; that error never resets to zero at a call.

The existing `foldl_contract` theorem composes the step for every natural horizon.
The final `Workflow.Certificate.certificate` instantiates the selected count and
relates the exact helper recurrence to the independent specification. The
parameterized proof body and step modules do not expand with the count. Source
mapping and compiler/runtime correspondence remain declared trust boundaries.

The allowance is a **checked uniform invariant bound**, not an inferred attained
worst-case error. A proposed invariant that fails initialization or preservation
leaves the request unresolved. This initial search is deliberately bounded; it
does not infer arbitrary time-varying invariants or certify every stable loop.
Do not weaken the original requirement or substitute a different implementation.

`analysis.json` records the proposed invariant and selected count. The saved
`Workflow.Counted.invariant` theorem is parameterized by the natural count;
function/step-contract modules are retained under `lean/Workflow/`. An optional
explicit `contract_cache` reuses unchanged helper modules across callers and
horizons. Keep an application's cache under its agreed verification directory.
Cold replay recompiles saved proofs without inference, producers or helper-cache
reuse, and regenerates the helper/model from frozen original source.

See the provider's [scaling guide](https://github.com/duckki/flare-lean/blob/main/docs/integration/scaling.md)
for smoothing and decay families, the larger shared source graph, measured costs
and rejection controls. Preserve production loops when generating a Rust port;
the existing explicit-port/application routes require their own source bridges.
