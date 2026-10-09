import Mathlib.Tactic

/-! Accumulation of certified local errors under a scalar step sensitivity.
No implementation or trajectory property is inferred from the recurrence. -/

namespace Flare.Analysis.ErrorRecurrence

noncomputable section

/-- Finite-horizon composition budget. L bounds sensitivity of each
step and δ its proved local error; neither is inferred here. -/
def accumulatedRadius (L δ initial : ℝ) : Nat → ℝ
  | 0 => initial
  | t + 1 => L * accumulatedRadius L δ initial t + δ

/-- Compose certified local radii once a step sensitivity and local error
bound have been established. Step sensitivity and local error are premises of this theorem. -/
theorem finite_horizon_bound (error : Nat → ℝ) (L δ initial : ℝ) (hL : 0 ≤ L)
    (h0 : error 0 ≤ initial) (hstep : ∀ t, error (t + 1) ≤ L * error t + δ)
    : ∀ t, error t ≤ accumulatedRadius L δ initial t := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
      exact (hstep t).trans (add_le_add (mul_le_mul_of_nonneg_left ih hL) (le_refl δ))

theorem nonexpansive_budget (L δ initial : ℝ) (hL : 0 ≤ L) (hL' : L ≤ 1)
    (hδ : 0 ≤ δ) (hinitial : 0 ≤ initial) (t : Nat)
    : accumulatedRadius L δ initial t ≤ initial + t * δ := by
  induction t with
  | zero => simp [accumulatedRadius]
  | succ t ih =>
      change L * accumulatedRadius L δ initial t + δ ≤ _
      have hbound := mul_le_mul_of_nonneg_left ih hL
      have hcoef := mul_le_mul_of_nonneg_right hL' (by positivity : 0 ≤ initial + (t : ℝ) * δ)
      simp only [one_mul] at hcoef
      simp only [Nat.cast_add, Nat.cast_one]
      linarith

end
end Flare.Analysis.ErrorRecurrence
