# Documentation

Start with the [skill user guide](../README.md) to verify application code or
request a verified Rust port. The guides below cover setup, contracts and library
use; detailed documentation is grouped by subject.

## Guides

- [Verify application code](numerical-verification.md): requests, guarantees,
  trust boundaries and replaying the README examples.
- [Set up and deliver results](automated-delivery.md): tool setup, original-source
  selection, portable evidence and change-aware rechecking.
- [Use FLARE as a Lean library](using-library.md): dependencies, imports and theorem use.
- [Develop FLARE](development.md): build, format, test and change the provider or skill.
- [Roadmap](roadmap.md): remaining capabilities and completion criteria.

## Library

- [Proved results, organization and attribution](library/organization.md)
- [Theorem reference](library/reference.md)
- [Potential Mathlib contributions](library/mathlib.md)
- [Source extraction manifest](library/extraction-manifest.json)

## Source profiles

- [Scientific arrays: NumPy and Julia](sources/scientific-arrays.md)
- [C source, memory conditions and verification tasks](sources/c-verification.md)
- [Closed Python module and C++ header selection](automated-delivery.md#select-original-source-definitions)

## Floating-point arithmetic

- [Explicit fused multiply-add](arithmetic/explicit-fma.md)
- [Square-root contracts and error propagation](arithmetic/square-root.md)
- [Binary32 storage with binary64 computation](arithmetic/mixed-precision.md)

## Tool integration and proofs

- [Provider layout and Python tests](../provider/README.md)
- [Producers, witness search and Lean validation](integration/tool-integration.md)
- [Shared enclosure inference and proof evidence](integration/proof-evidence.md)
- [Lean-checked counterexamples](integration/counterexamples.md)
- [Counted loops, shared contracts and scaling](integration/scaling.md)

## Evaluation

- [Tested applications and platforms](evaluation/delivery-evaluation.md)
- [Maintained benchmarks](../benchmarks/numerics/README.md)

See [Contributing](../CONTRIBUTING.md) for review requirements and where new results belong.
