# Native binary64

Scalar semantics and error bounds for Lean's native `Float` operations.
`Value` defines direct optional real interpretations and a totalized ghost
value. `Model/` supplies exact rational interpretations and model-level proofs;
these are mathematical support for the native operations.

`Arithmetic.interpretation_eq` relates the direct-real and rational-backed
interpretations. `Nearest`, `Division`, `Sqrt`, `Order`, `Zero`, and `Congruence`
establish arithmetic bounds and properties of comparisons and signed zeros.
NaNs and infinities have no real interpretation. Finiteness and overflow-domain
assumptions remain explicit in theorems.

Modules may import Analysis and Binary64 modules, together with Lean's
`Init`/`Std` and Mathlib. They must remain independent of matrix algorithms
and future interoperability modules.

See the [theorem guide](../../docs/library/reference.md) for entry points and domains.
