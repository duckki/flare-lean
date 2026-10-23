# Rust application proof bundles

Use `rust_application` when the original Rust API needs modules, structs, slices,
enums/results, checked integers or mutation beyond the scalar frontend. This
route runs Charon/Aeneas on a frozen crate and checks authored Lean bridges and
proofs. It does not infer an application specification automatically. The agent
must write/review that specification and discharge it in Lean.

## Request and contract

Start from the complete example at
`$FLARE_ROOT/examples/numerics/imu48/request.json`. Use schema
`numerics-request-v1`, `language: rust`, `target: rust-aeneas`, and the original
`source` and public `function`. The `rust_application` object has:

| Field | Meaning |
| --- | --- |
| `entry` | Crate-local path, such as `imu_epoch::assess`; ends with `function` |
| `files` | Map each destination `src/*.rs` to its original source file; include `src/lib.rs` and every companion module |
| `lean_modules` | Map each `Workflow.*` module name to a saved Lean source/template; include `Workflow.Contract` and `Workflow.Proof` |

File selections resolve relative to the request. The provider generates a
standalone dependency-free crate, pins its Rust toolchain, and extracts the
selected entry with its reachable callees. External crate dependencies need a
separate admission extension; do not silently stub or substitute them. Include
`#[cfg(test)]` modules in the files map for retained debug/release diagnostics.
The current route runs `cargo test --lib` in both modes after checking the root;
its test count is not a proof or a coverage claim.

`Workflow.Contract` defines `Statement`, a proposition parameterized by a
function with the public API's extracted type. Keep its numerical reference,
input validation, error behavior and uncertain outcomes independently reviewable.
It should import types and specification definitions, not the certificate or
extracted function bodies. `Workflow.Proof` exports
`Workflow.Certificate.certificate`. The provider independently checks:

```lean
example : Workflow.Contract.Statement Workflow.Generated.imu_epoch.assess :=
  Workflow.Certificate.certificate
```

The actual selected entry replaces `imu_epoch.assess`. It also rejects every
transitive root axiom except `propext`, `Classical.choice` and `Quot.sound`.
A theorem of `True`, an extra assumption or an axiom cannot close this check.
The authored contract still requires semantic review: a weak specification does
not become a useful engineering guarantee merely by being checked.

Generated `Workflow.Generated.Types/Funs` and `Workflow.Check` are reserved.
Freeze authored definitions/proofs alongside freshly emitted sources; never
edit the emitted functions to make a bridge compile. Files in FLARE's example
bundle use `.lean.txt` so optional Aeneas dependencies stay outside the core
Lake library. Each is materialized as its named `.lean` module in the run.
Use the pinned formatter at width 100 after compiling its imported modules.

## Execution and replay

Use the normal CLI commands and configured `rust_tools` or tool environment
variables from [tool setup](tool-setup.md#charonaeneas-and-its-lean-model):

```sh
python3 "$FLARE_ROOT/scripts/certify_numerics.py" plan --request "$REQUEST"
python3 "$FLARE_ROOT/scripts/certify_numerics.py" run --request "$REQUEST" --out "$NEW_RUN"
python3 "$FLARE_ROOT/scripts/certify_numerics.py" replay --run "$NEW_RUN" --out "$NEW_REPLAY"
```

Use the confirmed verification/Rust destinations and verification-local scratch
from the skill. Provider regressions use `.cache/numerics-generated/`.
Every crate/proof file, tool identity, extracted model, command and result is
retained and hashed. Charon's local source file names and contents must match
the frozen crate selection; implicit includes outside it are rejected. Freshness auditing checks original companion and contract
files too. Frozen replay recompiles all saved Lean modules and reconstructs the
root ascription/axiom audit, without Charon, Aeneas translation, rustc, producers
or an LLM. It needs the matching compiled Aeneas model, Lean and library imports;
`--aeneas-lean-lib` can relocate that model with matching hashes.

## Maintained 48-event example

The original public `assess` API remains a slice loop. The root proves:

- Exactly 48 samples, finite accelerations in `[-4,4]` m/s² and a finite
  threshold in `[-1,1]` m are precisely the successful admission conditions,
  together with increasing original UInt64 epochs separated by 2–5 million ns.
- The integer subtraction is safe before conversion, including epochs above
  `2^53`. The exact reference uses original integer differences divided by
  `10^9`, not rounded elapsed seconds or restarted rounded states.
- Successful position and velocity are finite. Position error is at most
  `48 * 2^-35` m, exactly the returned arithmetic allowance.
- `Below`/`Above` imply the corresponding strict exact-reference ordering.
  `Uncertain` implies exact distance at most
  `2^-28 + 2^-51 + 48 * 2^-35` m from the threshold. The subtraction used for
  the decision has its own rounding allowance.
- Wrong size, unsupported threshold, unsupported acceleration, reversed time
  and out-of-period errors are returned in the source's validation order.

The runtime cases include padding endpoints, all decisions, NaN/infinities,
wrong sizes, late failures and near-maximum UInt64 epochs. Regression controls
reject changed timestamp arithmetic, weakened/axiom roots and zero decision
padding in both the actual Rust source and its native Lean model. The padding
control must reach numerical proof rejection after fresh extraction and the
source bridge have passed. A runtime diagnostic also shows why zero padding
can cross a strict threshold; runtime sampling alone is not a Lean counterexample.
