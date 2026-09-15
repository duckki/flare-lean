# Floating-point matrices

Theorems about matrix representations, numerical accuracy, and successful
execution under explicit hypotheses. Concrete algorithms are included as the
subjects of these proofs.

`Value` is a mathematical interpretation. `Storage` and `OperationStorage`
prove representation properties; the other proof modules establish numerical
bounds for multiplication, factorization, solves, Jacobi, and pseudoinverses.

`Dense` contains row-major binary64 arithmetic and LDLᵀ kernels. `Operations`
provides the combined dense/spectral interface and the Jacobi eigensolver.
`Error` distinguishes dense failures from spectral failures; `Operations.adapt`
preserves the explicit error translation in the proved schedule.

Runtime modules must not import the interpretation or reasoning modules.

Dimension, conditioning, gap, finiteness, and rounding assumptions remain
explicit. PSD diagnostic acceptance is not an exact PSD certificate. These
proofs do not automatically apply to a different BLAS or language implementation.

See the [theorem guide](../../docs/reference.md) for entry points and limits.
