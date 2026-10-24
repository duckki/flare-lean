# C source and verification conditions

FLARE's closed C11 profile connects original double-precision C functions to
ordered Lean execution and numerical contracts. Start with the
[skill profile](../../skills/verify-numerics/references/c-source.md) for admission,
request fields, caller premises and setup. The maintained
[examples](../../examples/numerics/c/README.md) cover scalar helpers, a buffer update,
a by-value struct and a read-only reduction.

## One root for execution and accuracy

The frontend lowers admitted source to an ordered scalar graph and, for buffers,
a load/store trace. It records literal access indices, extents, source lines and
32-bit unsigned loop counts in `c-vcs.json`. A generated `sourceConditions` proof
checks the static indices and counter bounds. Frozen replay rederives these
conditions rather than trusting a saved JSON success flag.

`Flare.Binary64.Memory` provides checked access to a finite heap of initialized
`Float` cells, region validity/separation and frame rules. The generated
`Workflow.sourceExec` preserves each load, arithmetic operation and store.
`source_equiv` proves successful execution equals the operation-ordered kernel
under the declared region conditions. The final
`Workflow.Certificate.certificate` includes this execution, numerical accuracy
against the independent reference, finiteness, budgets and heap frame behavior.
The independently generated `Workflow.Check` ascribes that whole expected type
and audits its transitive axioms. Replacing it with a scalar-only theorem fails.

The reusable numerical checker handles all examples; no application-specific
error lemma or new axiom is added. Scalar/value-struct Rust delivery uses the
existing retained-port route and fresh Charon/Aeneas extraction. Buffer roots
currently support Lean delivery only.

## Assurance boundary

The theorem concerns the admitted typed-cell model. Source parsing/mapping,
physical C object representation and compiler/runtime agreement remain trusted.
Callers establish live initialized aligned double objects, declared extents and
required separation. Read-only regions may overlap; the mutable region must be
separate from each other region. Thus the root proves conditional memory access
and frame properties, not arbitrary C call-site lifetime/provenance correctness.
The model's checked `Option` accesses add no runtime checks to the original C.

The selected target has binary64 doubles, 32-bit unsigned int, no excess precision,
nearest/even, gradual underflow and separate arithmetic operations. Original-source
diagnostics use `-fno-fast-math -ffp-contract=off -fexcess-precision=standard`,
`-O0`, `-O2` and address/undefined-behavior sanitizers. Reports retain compiler/SDK
identities, modes and probes. Diagnostic samples do not prove compiler correctness
or universal absence of undefined behavior; floating-point flags/traps are outside
the contract. See the [profile guide](../../skills/verify-numerics/references/c-source.md)
for exact limits and rejected syntax.

## Frama-C/WP and Why3 evaluation

The optional exporter was exercised with [Frama-C](https://frama-c.com/) **31.0
Gallium**, [Why3](https://why3.org/) **1.8.2** and Z3 on Ubuntu ARM64. It retains
actual WP `Typed+float` tasks, runtime-error obligations, source ACSL, prover
reports, versions and hashes:

```sh
python3 scripts/export_c_vcs.py \
  --request examples/numerics/c/mean_update.json \
  --request examples/numerics/c/blend.json \
  --out /absolute/new/task-directory
```

Read the [optional setup instructions](../../skills/verify-numerics/references/tool-setup.md#optional-c-verification-task-tools)
when tools are missing. The exporter pins these task interfaces and invokes
Why3's Z3 driver with a bounded prover timeout. Its `export.json` status is
`task_evidence_only`, with `lean_proof_imported: false`; an exporter success means
tasks were retained, regardless of prover verdicts. JSON numerical requirements
are not translated into ACSL. These are source/VC inspection tasks, not competing
certificates for the same numerical target.

The inspected tasks contain typed-memory theories and abstract floating-point
operations/finite predicates. A useful Lean importer would need semantic bridges
for those theories, contract translation and checked proof steps. An SMT success
flag or a translated task proposition supplies none of those. For this closed
profile, direct source-derived conditions plus the existing Lean arithmetic
checker give a reusable complete route within the stated boundary. Foreign
proof evidence checking remains a separate [roadmap](../roadmap.md) item. The
[CBMC adapter](../integration/counterexamples.md#cbmc-witness-search) searches a separate scalar
positivity profile; it does not establish C memory or access conditions.

## Regressions

The default numerical suite certifies and replays the scalar, buffer, struct and
read-only cases. Controls reject casts, alias escape, out-of-bounds indices and
unsupported loop counters. Lean rejects a concrete overlapping separation claim,
a false independent reference, corrupted/resealed conditions and a weakened root.
The optional Rust case rejects a changed port's false correspondence proof.
Replay tests disable producers, compiler admission and Rust extraction.

Original-source diagnostics were exercised with macOS ARM64 Clang 21 and Linux
ARM64 GCC 13, at all three compiler modes. Lean certification and Rust extraction
were exercised on macOS; GCC diagnostics alone are not a Linux Lean replay run.
Use [development commands](../development.md#c-source-regression-checks) to reproduce.
