# Automated delivery evaluation

The release checks retain unmodified Chemicals, NumPy and ROS sources, frozen
contracts, [first attempts and needed assistance](../benchmarks/numerics/heldout/README.md).
Their three positive certificates accompany the covariance failure and a separate
ROS underflow counterexample. Reports, command receipts and portable bundles are
retained under the ignored provider regression directory. Aggregate measurements
are in [delivery-results.json](../benchmarks/numerics/delivery-results.json).

## Completed platform checks

| Environment | Setup | Checked delivery |
| --- | --- | --- |
| Linux ARM64 | Fresh Ubuntu 24.04 container inside an ARM64 Linux VM; no host mounts or existing tools/caches | Three positives, two counterexamples, portable replay and rechecking |
| Linux x86-64 | Separate fresh Ubuntu 24.04 container under emulation in the ARM64 VM; no host mounts | Same five cases, portable replay and rechecking |
| Native macOS ARM64, isolated tool pool | Empty selected Elan/tool pool and restricted system PATH with no baseline verification executables | Three positives, covariance counterexample, portable replay and rechecking |
| Native macOS ARM64, existing tools | Existing Lean/NumPy/Charon/Aeneas installations | All five cases plus fresh retained-array Rust extraction, portable replay and rechecking |

The macOS isolated-tool test uses the existing OS, Python, compiler and SDK;
existing user caches remain available. It is not a fresh macOS VM. The x86-64 run
checks that toolchain/ABI route under emulation, not native x86 performance.
Optional Rust tools were existing native macOS installations, not new installs.
No result here claims macOS x86-64, Windows or every optional tool/platform route.

Both final Linux repetitions completed uninterrupted. Earlier interrupted setup
attempts and recovery commands are retained separately; they are excluded from
the complete setup totals below.

## Observed costs

Tool bootstrap, excluding base-OS prerequisite installation:

| Environment | Elapsed setup |
| --- | ---: |
| Fresh Linux ARM64 | 185.0 s |
| Fresh emulated Linux x86-64 | 335.6 s |
| Native macOS ARM64 isolated tool pool | 424.2 s |

Selected checking/replay measurements:

| Case / environment | Generation | Cold proof replay |
| --- | ---: | ---: |
| Chemicals density / Linux ARM64 | 2.6 s | 2.4 s |
| NumPy quantile helper / Linux ARM64 | 7.1 s | 6.0 s |
| ROS angle conversion / Linux ARM64 | 3.1 s | 2.6 s |
| Covariance counterexample / Linux ARM64 | 2.0 s | 2.0 s |
| ROS underflow counterexample / Linux ARM64 | 2.6 s | 1.8 s |
| Retained Rust array API / native macOS, existing tools | 28.8 s | 20.9 s |

These are observations, not controlled cross-platform performance comparisons.
Generation includes source diagnostics and, for Rust, fresh extraction. Replay
recompiles frozen proof sources without producers/translators/source execution;
proof-library dependencies remain required. JSON distinguishes wall time from
summed child-command time for older measurements. Peak RSS is a completed-child
maximum, not aggregate process-tree memory. Bundle sizes and individual stage
costs are retained with the results.

## Search, maintenance and rejection controls

The official CBMC 6.11.0 ARM64 release and maintained setup recipe were checked
against GitHub's published digest. Its scalar search uses the common adapter
session for version/model admission, tool identity and frozen-obligation evidence.
A positive subnormal ROS degree input rounds to zero radians: the ordinary Lean
witness checker and original compiled header agree on the violation. Parent
replay needs no CBMC. The original trace and witness are retained as regressions;
this positivity contract does not replace the held-out accuracy requirement.

Real-tool tests also check that no witness stays unresolved. Other controls cover
missing tools, malformed/ambiguous trace words, source rebinding, invalid C++
selectors, unsafe/corrupt bundles, changed source/contracts, rejected current
proofs and replay resource limits. Rechecking preserves requirements and freshly
checks compatible provider changes. A changed source/model/contract or toolchain
requires new verification. The retained Rust API keeps its production loop and
separate verification driver; its matching compiled Aeneas model is a proof
replay dependency, not a translator.

The broader regressions include the dense-array certificate, false-port rejection,
Gappa/FPTaylor replay, older frozen certificates and the 1,024-step/shared-contract
scale cases. Additional polynomial reference normalization is bounded to small
graphs; large matrix graphs retain their structural proof path and sharing.

## Remaining release gate

An independent engineer still needs to reproduce one positive certificate and
one counterexample from their delivered reports/bundles, without session history.
Agent-operated VM/container/native runs cannot satisfy that human step. The
[delivery guide](automated-delivery.md) provides the commands and prerequisites.

Broader NumPy APIs, general C++ semantics, additional counterexample properties,
Rust bridge generation and native binary32 arithmetic remain roadmap work. These
selected application checks do not establish whole-library or whole-language
coverage.
