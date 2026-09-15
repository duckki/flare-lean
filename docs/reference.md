# Theorem guide and assurance boundaries

FLARE proves numerical guarantees under explicit hypotheses. This guide lists
useful entry points and explains their interpretations. The Lean declarations
are the complete contracts. Names below are relative to `Flare`.

## Numeric representations

- `Binary64.Value.modelToReal` interprets a finite `Float.Model` directly in ℝ.
- `Binary64.Value.toReal` interprets native `Float` through its logical model.
- `Binary64.Value.value` totalizes that optional value to zero for proof statements.
  Finiteness remains an explicit premise; zero fallback is not numerical recovery.
- `Binary64.Model.Value` supplies exact rational interpretations and a finite-value
  guard for model-level proofs. `Binary64.Arithmetic.interpretation_eq` proves
  agreement of direct-real and rational-backed model interpretations.
- `Matrix.Value.matrix` interprets row-major arrays. Missing entries are totalized
  to zero in this ghost interpretation. Individual theorems state their storage
  and numerical requirements; callers must respect the runtime interface.

NaNs and infinities have no real value. The two zero signs share a real value,
but semantic equality is not bit equality. The congruence and zero lemmas retain
this distinction.

The pinned Lean source is the definition of the logical machine operations:
[Float.Model in Lean 4.33.1](https://github.com/leanprover/lean4/tree/v4.33.1/src/lean/Init/Data/Float/Model).

## Useful theorem entry points

| Module | Entry points | Scope |
| --- | --- | --- |
| `Binary64.Nearest` | `add_error_nearest`, `sub_error_nearest`, `mul_error_nearest`, `div_error_nearest` | Finite operands; exact-result magnitude ≤ 2^1000; division also requires a nonzero interpreted divisor |
| `Binary64.Sqrt` | `sqrt_error_nearest` | Every finite nonnegative operand, including zero and positive subnormals |
| `Binary64.Order` | `compare_value`, `lt_iff`, `le_iff`, `beq_iff`, `abs_value`, `neg_value` | Real interpretation of finite native comparisons and unary operations |
| `Binary64.Model.NaturalConversion` | `ofNat_exact`, `nat_div_error_real` | Exact conversion below 2^53; bounded natural quotient with 0 < denominator and numerator ≤ denominator |
| `Matrix.Multiplication` | `multiply_accuracy`, `multiply_mass_accuracy`, `multiply_norm_accuracy` | Actual separately rounded multiply/add loops; inner dimension ≤ 32 and explicit magnitude or term-mass bounds |
| `Matrix.PositiveDefiniteFactorization` | `factor_accuracy`, `solveSPD_success` | Dimension ≤ 12; explicit SPD floor, entry bounds, and right-hand-side bounds |
| `Matrix.SolveAccuracy` | `solveSPD_residual`, `solveSPD_accuracy`, `solveSPD_mass_residual` | Residual and forward-error guarantees under the stated conditioning and factorization profiles |
| `Matrix.JacobiInitialization` | `jacobiEigen_success` | Finite symmetric arrays, 1–18 rows, entries bounded by 2^500; includes the iteration limit and final rescaling |
| `Matrix.JacobiOutput` | `jacobiEigen_spectral`, `jacobiEigen_spectral_sharp` | Backward spectral error and eigenvector bounds with explicit profile limits |
| `Matrix.Pseudoinverse` | `symmetricPseudoInverse_accuracy` | 1–12 rows, PSD real target, quarter-unit spectral gap, norm limit, and explicit matrix-formation error |
| `Matrix.PSDCheck` | `checkPSD_accepts_approximation` | Sufficient conditions for diagnostic acceptance, not a converse PSD certificate |
| `Analysis.PseudoinversePerturbation` | `difference_norm`, `projected_difference_norm` | Singular symmetric pseudoinverse perturbations, including range-projected estimates |

For the nearest scalar operations, the stated error is bounded by
`2^-53 * (abs(exact result) + 2^-1022)`. Square root has the relative bound
`2^-53 * sqrt(exact operand)`. These statements also conclude finiteness of the
computed result. Read the declarations for the precise hypotheses.

The concrete pseudoinverse theorem assumes `A` is PSD and
`A*A - (1/4) • A` is PSD, requires an input operator norm at most `2^20`, and
bounds formation error by `1.4e-11` times the input norm. It includes zero and
singular matrices. It is not a theorem for arbitrary ill-conditioned matrices
or an arbitrary eigenvalue threshold.

## Runtime correspondence

`Matrix.Operations` is the executable matrix interface, built on `Matrix.Dense`
and `Matrix.Error`. The dense and spectral error types are related by an
explicit adapter. The runtime uses native `Float` operations; rational and real
interpretations are proof support.

Some proof modules decompose loops into smaller passes. Theorems such as
`Matrix.Factorization.factor_eq` and `Matrix.JacobiIteration.jacobiEigen_eq`
connect those decompositions to the runtime. Changing a loop or its arithmetic
order requires re-establishing the corresponding guarantees.

The numerical proof is about Lean's logical interpretation of the written native
operations. It does not alone prove compiler/hardware agreement, a BLAS call,
or a Python/Rust port. A changed implementation needs a correspondence proof
or separately described testing evidence.

## Checking the library

`lake build` elaborates the full public import tree. `Tests/ProofAudit.lean`
checks every public and private FLARE theorem for extra axioms, including any
admitted proof or compiler-trust axiom. Only Lean's usual `propext`,
`Classical.choice`, and `Quot.sound` are allowed.

`scripts/check_layout.py` verifies the source import closure, ensures all library
modules are exposed by `Flare.lean`, keeps Analysis independent of floating-point
modules, and keeps the native matrix runtime free of ghost or proof dependencies.

`lake lint` runs these checks together with source style checks, Lean's normal
and extra linters, and import coverage for all Lean files. `make check` also
checks leanfmt output at width 100 and runs tooling regression tests.
