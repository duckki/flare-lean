import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Dyadic scale selection and conversion of absolute rounding allowances. -/

namespace Flare.Analysis.Dyadic

/-- Select a normal-range dyadic scale from the magnitude of a real result.
The normal underflow threshold also covers zero and subnormal results. -/
lemma bounded_exponent (x : ℝ) (hx : |x| ≤ (2 : ℝ)^(1000 : Int))
    : ∃ E : Int,
        -1022 ≤ E ∧ E ≤ 1000 ∧ |x| ≤ (2 : ℝ)^E ∧ (2 : ℝ)^E ≤ 2 * (|x| + (2 : ℝ)^(-1022 : Int)) := by
  let s := max ((2 : ℝ)^(-1022 : Int)) |x|
  have hmin : 0 < (2 : ℝ)^(-1022 : Int) := zpow_pos (by norm_num) _
  have hs : 0 < s := hmin.trans_le (le_max_left _ _)
  obtain ⟨N, hlo, hhi⟩ := exists_mem_Ioc_zpow hs (by norm_num : (1 : ℝ) < 2)
  have hsup : s ≤ (2 : ℝ)^(1000 : Int) := max_le
    (zpow_le_zpow_right₀ (by norm_num) (by norm_num)) hx
  have hN : N < 1000 := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp (hlo.trans_le hsup)
  have hN' : -1022 ≤ N + 1 := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
    ((le_max_left _ _).trans hhi)
  refine ⟨N + 1, hN', by omega, (le_max_right _ _).trans hhi, ?_⟩
  have hm : s ≤ |x| + (2 : ℝ)^(-1022 : Int) := max_le (by linarith [abs_nonneg x])
    (by linarith)
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  linarith

/-- Convert a dyadic absolute error allowance into a magnitude-scaled bound. -/
lemma scaled_error_bound (x : ℝ) (E p : Int) (hE : (2 : ℝ)^E ≤ 2 * (|x| + (2 : ℝ)^(-1022 : Int)))
    : (2 : ℝ)^(E - p) ≤ (2 : ℝ)^(1 - p) * (|x| + (2 : ℝ)^(-1022 : Int)) := by
  calc
    _ = (2 : ℝ)^E * (2 : ℝ)^(-p) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
    _ ≤ (2 * (|x| + (2 : ℝ)^(-1022 : Int))) * (2 : ℝ)^(-p) :=
      mul_le_mul_of_nonneg_right hE (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    _ = _ := by
      rw [show 1 - p = 1 + (-p) by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
      ring

end Flare.Analysis.Dyadic
