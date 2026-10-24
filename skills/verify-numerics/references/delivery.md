# Select original definitions and deliver replayable results

`python_module: true` selects an undecorated closed top-level scalar function or
scientific function/helper closure from the retained full source. Original
selected definition lines are preserved. Runtime diagnostics execute those
definitions in isolation; module initialization, rebinding and dispatch require
caller review. Do not claim that unrelated module behavior was checked.

`language: "cpp"` with `cpp_module: {"constants":{"M_PI":"0x400921fb54442d18"}}`
admits a selected namespace-level by-value double C++20 function, at most 32
straight-line operations. Use the original qualified function name. Configured
constants are exact words checked by static assertions against the real header;
original-header diagnostics run at O0/O2. Parser/compiler fidelity is trusted.
Objects, templates, exceptions, memory, loops and general preprocessing require
further bridges. These selections currently use `lean-flare` and Lean delivery.

Use `pack --run <run> --out <archive>` to deliver frozen sources/evidence, then
`unpack --archive <archive> --out <new-run>` and `replay --run <new-run> --out
<new-replay>`. Hashes establish integrity only. Require fresh Lean replay, including
its independently reconstructed type and axiom audit. Rust replay also needs the
recorded compiled Aeneas model; translators and original source runtimes are not
needed. Keep all application artifacts under the agreed verification directory.

For complete current requests, `recheck --run <old-run> --request <current-request>
--out <new-directory>` checks compatibility, builds the provider and replays
compatible results. Changed source/contract/profile/toolchain returns
`needs_reverification`, requiring a new run. A changed runtime needs fresh
diagnostics; replay/recheck of frozen evidence does not validate a new runtime.
Authored proofs, Rust ports/crate files and nested contracts are compared by
content. A changed Aeneas proof model needs fresh verification; a matching one
can be relocated with `--aeneas-lean-lib`. Changed application source needs fresh
extraction; the existing component cache can reuse unaffected proof work.

Read the provider's [delivery guide](https://github.com/duckki/flare-lean/blob/main/docs/automated-delivery.md)
for complete commands and the retained public case scope. Independent engineer
reproduction needs that engineer's actual run; agent-operated checks do not count.
