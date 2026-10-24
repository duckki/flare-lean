# Setup, portable delivery and maintenance

Use the same reviewed source, domain, independent reference and requirements
through setup, checking, delivery and maintenance. A compatible tool invocation
or a saved success verdict cannot replace the final Lean root and axiom audit.

## Obtain only the selected tools

A skill-only installation needs a matching complete provider checkout or supplied
source bundle. `scripts/bootstrap_numerics.py` checks the skill hash when `--skill`
is supplied, pins Elan release assets and their published digests, installs the
provider's Lean version, and builds FLARE. It can obtain pinned NumPy/pycparser
wheels checked against official PyPI digests. Python, curl, Git, Make and a C/C++
compiler are base-OS prerequisites; the script does not install OS packages.

After agreeing artifact locations, choose a shared user tool pool outside both
the application and provider:

```sh
python3 "$FLARE_ROOT/scripts/bootstrap_numerics.py" \
  --provider "$FLARE_ROOT" --tools "$FLARE_TOOLS" \
  --out "$VERIFICATION/setup" --skill "$SKILL_DIR/SKILL.md" \
  --package numpy --package pycparser
```

Request only needed packages. `--shared-cache` opts into the shared Lake artifact
pool; omitting it preserves inherited cache preferences. Missing Mathlib artifacts
are explicitly bootstrapped once. `environment.json` records the environment for
later commands; apply its values in the calling process rather than changing shell
profiles. `bootstrap.json` and `runs/` preserve identities, setup costs and failed
stages. Choose a new tool/output destination for a new attempt.

`--require-clean` requires no verification tools on the recorded baseline PATH and
an empty selected tool pool. This establishes an isolated tool environment, not a fresh OS.
Record the VM/container/user environment separately. The base OS and its compiler,
SDK, network configuration and Python remain prerequisites.

Optional analyzers/translators remain separate. For the maintained CBMC 6.11.0
Ubuntu 24.04 x86-64/ARM64 assets, run:

```sh
python3 "$FLARE_ROOT/scripts/certify_numerics.py" setup \
  --tool cbmc --out "$FLARE_TOOLS/cbmc-6.11.0"
```

This verifies the official release digest and extracts into user scope with
`dpkg-deb`; it does not install a system package. Other OS distributions need a
compatible selected installation. See [counterexamples](integration/counterexamples.md).
Charon/Aeneas setup and proof-model identities follow the skill's
[tool guide](../skills/verify-numerics/references/tool-setup.md).

## Select original source definitions

Use these selectors when the original file contains more than the closed kernel:

| Request fields | Admitted source | Boundary |
| --- | --- | --- |
| `"python_module": true` | An undecorated top-level scalar function or scientific function/helper closure from a full Python module | Selected definitions execute in isolation; module initialization, rebinding and dynamic dispatch require caller review |
| `"language": "cpp"`, `"cpp_module": {"constants": {"M_PI": "0x400921fb54442d18"}}` | A namespace-level by-value double C++20 header function, with at most 32 straight-line operations | Explicit constant words, supported header guards/includes only; no objects, templates, exceptions, memory, loops or general preprocessing/library algorithms |

Keep the original source file and function name, including C++ namespace
qualification. Python selection preserves the original selected definition lines
and rejects rebinding of selected functions/helpers. NumPy module selection needs
an unshadowed `import numpy as np`. These profiles currently use `lean-flare`
and Lean delivery; they do not add external-producer, authored-proof or Rust-port
support to those source selections.

C++ diagnostics compile the original full header at O0/O2 with separate binary64
operations. Static assertions check the configured constants' types and words.
The selected-source/parser mapping and compiler/hardware fidelity remain trusted.
The header's unrelated functions are outside the numerical theorem. Both C and
C++ frozen replay require pycparser 3.0; C++ replay needs no compiler.
The [retained public cases](../benchmarks/numerics/heldout/README.md) show complete
requests and independent references, including the ROS reference's binary64 π.

## Portable evidence

After a completed root (`certified`, `counterexample` or `budget_not_met`), export
and import a frozen run:

```sh
python3 "$FLARE_ROOT/scripts/certify_numerics.py" pack \
  --run "$VERIFICATION/result" --out "$VERIFICATION/result.tar.gz"
python3 "$FLARE_ROOT/scripts/certify_numerics.py" unpack \
  --archive "$VERIFICATION/result.tar.gz" --out "$VERIFICATION/received"
python3 "$FLARE_ROOT/scripts/certify_numerics.py" replay \
  --run "$VERIFICATION/received" --out "$VERIFICATION/replayed"
```

Bundles retain original sources, requests, proof sources, evidence and command
receipts. They reject symlinks, traversal, duplicate paths, changed payloads and
oversized archives. Hashes detect corruption; they do not authenticate a sender
or certify a theorem. Unpacking performs an integrity audit only. Replay checks
the reconstructed root with the built proof-library dependencies. Rust bundles
also require the recorded compiled Aeneas Lean model, optionally relocated with
`--aeneas-lean-lib`; it is a proof dependency, not a translator.

Replay uses no producers, translators, source execution, witness search or LLM.
A relocated original source path or missing original executable does not block
frozen replay. Reports and logs retain their original paths as provenance.

## Change-aware rechecking

For a complete current request:

```sh
python3 "$FLARE_ROOT/scripts/certify_numerics.py" recheck \
  --run "$VERIFICATION/received" --request "$VERIFICATION/current-request.json" \
  --out "$VERIFICATION/rechecked"
```

Recheck compares original source bytes, requirements, profile selectors and the
reconstructed source model. Source/contract/profile or Lean-toolchain changes
produce `needs_reverification`, retaining the differences without reusing a stale
certificate. Compatible provider changes build FLARE, then reconstruct/check the
frozen root afresh. `recheck.json` lists changed dependencies; `replay/` contains
the new check. A proof rejected by the new library remains a rejected check.

Runtime/tool locations and resource budgets are operational settings. `recheck`
honors the current request's per-command timeout; standalone `replay --timeout`
can override only that execution limit while preserving the frozen contract.
Rejected rechecks retain an unresolved `recheck.json` and command logs. Rechecking
does not execute a new runtime; original diagnostics remain frozen historical
evidence. A new runtime/compiler claim needs fresh certification/diagnostics.
Authored proofs, retained Rust ports, crate files and nested component contracts
are compared by content rather than original path. A changed Aeneas proof model
requires fresh verification. An unchanged model can be relocated without its
translator. Changed application source needs a fresh extraction/run; the existing
component/contract proof cache reuses unaffected work. See [scaling](integration/scaling.md).

A CLI `run` rejected before source admission retains the original request,
`admission.json` and a report when its requested output directory is new. It also
retains the original source when readable and at most 2 MB. It has no checked root. Missing tools,
unsupported profiles, timeouts, rejected proofs, `budget_not_met` and checked
counterexamples remain distinct results. Select a new run for each attempt;
changing producer cannot silently change the requirement.

## Release evaluation and independent reproduction

The [retained public cases](../benchmarks/numerics/heldout/README.md) cover density
conversion, a scientific-array helper and a C++ robotics helper. Their original
sources/contracts and first attempts precede the reusable admission changes.
Run `scripts/release_numerics.py --out <new-directory>` on each selected platform
with its built provider. `release.json` records checking costs and bundle sizes;
setup receipts are separate from checking/replay costs. Supply `--tools <JSON>`
with an explicit `rust_tools` selection to include fresh extraction, portable
replay and rechecking of the retained array Rust API. It keeps its real loop.

For an independent engineer, deliver the matching provider revision/source bundle,
the positive/counterexample archives, their reports, and the commands above.
They should reproduce one positive root and one counterexample from those files
without session history. Record that person's result separately. Agent-driven
VM/container/native runs establish automated reproduction, not this human step.
The [independent reproduction checklist](evaluation/independent-reproduction.md)
provides the minimal paired handoff, commands and required results.

Current platform evidence and the independent reproduction follow-up are in
[the delivery evaluation](evaluation/delivery-evaluation.md). Full source-language support,
general C++ semantics and arbitrary NumPy/library calls are outside these cases.

## Reference equality and resource bounds

Small scalar rational references use bounded total-field case analysis, including
zero denominators; no new nonzero assumption escapes into the root. Additional
polynomial normalization for scientific references is limited to 32-node graphs.
Larger collection/matrix graphs retain their structural proof path and expression
sharing. A failed reference proof stays unresolved; it never licenses a changed
reference or engineering budget.
