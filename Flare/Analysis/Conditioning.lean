module

public import Flare.Analysis.LinearSolve
public import Flare.Analysis.SpectralPerturbation

/-! Inverse operator-norm bounds from a positive-definite lower bound. -/

@[expose] public section

namespace Flare.Analysis.Conditioning
open Matrix Flare.Analysis
open scoped Matrix.Norms.L2Operator

/-- A uniform SPD floor bounds the exact inverse in the Euclidean operator norm. -/
theorem inverse_norm_bound {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) (σ : ℝ)
    (hσ : 0 < σ) (hA : (A - σ • 1).PosSemidef)
    : ‖A⁻¹‖ ≤ 1 / σ := by
  have hpd := NumericalBounds.posDef_of_lower_bound A σ hσ hA
  let := hpd.isUnit.invertible
  rw [cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hh := LinearSolve.matrix_lower_bound A σ hσ hA (toEuclideanCLM (𝕜 := ℝ) A⁻¹ x)
  simp only [ofLp_toEuclideanCLM, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
    Matrix.one_mulVec, WithLp.toLp_ofLp] at hh
  calc
    _ ≤ ‖x‖ / σ := (le_div_iff₀ hσ).mpr (by linarith only [hh])
    _ = _ := by ring

end Flare.Analysis.Conditioning
