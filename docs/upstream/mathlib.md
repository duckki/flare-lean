# Mathlib contributions

`Flare/Analysis/` contains the pure mathematics supporting the numerical
library. It depends on Mathlib and other Analysis modules, so a candidate can
be studied independently of the native floating-point implementation.

## Candidate areas

These are areas for investigation, not claims that Mathlib lacks the results.
No upstream submission is recorded here yet.

| Area | FLARE modules | Preparation needed |
| --- | --- | --- |
| Dyadic estimates | `Analysis.Dyadic` | Compare the exponent-selection and scaling lemmas with existing power bounds |
| Indexed fold simulation | `Analysis.ErrorRecurrence.foldl_contract` | Compare with `List.foldl_rel` and `List.rel_foldl`; assess a useful interface for step-indexed invariants before proposing an upstream statement |
| Matrix conditioning | `Analysis.Conditioning`, `Analysis.SchurComplement`, `Analysis.LinearSolve` | Compare positive-definite and operator-norm APIs; identify reusable missing lemmas |
| Spectral estimates | `Analysis.SpectralGap`, `Analysis.SpectralPerturbation` | Compare spectral-theorem and norm infrastructure; retain the exact assumptions |
| Pseudoinverses | `Analysis.MoorePenrose`, `Analysis.PseudoinversePerturbation` | Reconcile definitions and symmetry hypotheses with upstream interfaces |
| Gram and Jacobi bounds | `Analysis.GramBounds`, `Analysis.Jacobi*` | Separate general inequalities from algorithm-specific or fixed-profile statements |

## Preparing a contribution

1. Search the pinned Mathlib checkout and current upstream for the statement,
   its ingredients, and the preferred definitions. Start with Mathlib's own
   [contribution guide](https://leanprover-community.github.io/contribute/index.html).
2. Identify the smallest useful statement and its dependencies. Any
   generalization or new formulation is a separate mathematical change.
3. Prepare an upstream branch using Mathlib's namespace, file placement, and
   style. Keep the working FLARE theorem in its subject module until the
   dependency migration is ready.
4. Record the exact declarations, upstream revision, preparation status, and
   eventual PR link here. Check definitions and assumptions in the upstream
   version as well as proof compilation.
5. Once a pinned Mathlib revision contains the accepted result, use it from
   FLARE and remove redundant local proof infrastructure.

There is no `Flare/Mathlib/` holding area: destination status belongs here,
while library modules remain organized by subject.

## Matrix-coordinate error and reflection interfaces

`Analysis.EntrywiseError` supplies a finite-matrix absolute comparison relation
and propagation through products, together with residual and spectral-margin
consequences. `Analysis.Householder` supplies the explicit coordinate action
and column-Gram identity for a unit-vector reflection. Mathlib already has
abstract reflection and norm infrastructure. An upstream proposal would need
to establish a useful connection to that infrastructure and avoid duplicating
its existing results; these local interfaces do not assert a novel theorem or
an accepted upstream contribution.
