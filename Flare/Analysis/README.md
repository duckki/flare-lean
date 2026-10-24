# Numerical analysis

Real and discrete mathematical support for the floating-point proofs: dyadic
bounds, Schur complements, conditioning, matrix norms, spectral estimates,
Gram residuals, and pseudoinverse perturbation.

Modules may import Mathlib and other Analysis modules. They must not import
Binary64, Matrix, or application projects. Existing theorem hypotheses and
fixed numerical profiles are preserved; this is not a claim that every result
is already expressed in an interface suitable for Mathlib.

See the [theorem guide](../../docs/library/reference.md) for entry points and the
[Mathlib contribution guide](../../docs/library/mathlib.md) for upstream work.
