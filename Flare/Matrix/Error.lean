module

public import Init.Data.Float.Float

/-! Error results for dense and spectral numerical operations. -/

@[expose] public section

namespace Flare.Matrix

/-- Errors emitted by dense arithmetic and LDLᵀ operations. -/
inductive DenseError where
  | nonpositivePivot
  | nonfiniteComputation
deriving DecidableEq, Repr

/-- Errors emitted by the combined dense and spectral interface. -/
inductive Error where
  | nonpositivePivot
  | nonfiniteComputation
  | eigenNotConverged
  | negativeEigenvalue
deriving DecidableEq, Repr

end Flare.Matrix
