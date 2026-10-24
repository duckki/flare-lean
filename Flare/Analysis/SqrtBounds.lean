module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith

/-! Perturbation rules for exact square roots. These discharge the incoming-error
obligation when a rounded primitive is composed with an independent reference.
The squared-allowance rule includes zero; a positive floor gives a sharper rule. -/

@[expose] public section

namespace Flare.Analysis.SqrtBounds

/-- A squared error allowance controls square-root distance even at zero. -/
theorem difference_le_of_sq (x y d : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hd : 0 ≤ d) (herror : |x - y| ≤ d ^ 2)
    : |Real.sqrt x - Real.sqrt y| ≤ d := by
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy
  have hnx := Real.sqrt_nonneg x
  have hny := Real.sqrt_nonneg y
  have hsq : (Real.sqrt x - Real.sqrt y) ^ 2 ≤ |x - y| := by
    rcases le_total (Real.sqrt x) (Real.sqrt y) with h | h
    · rw [abs_of_nonpos (by nlinarith : x - y ≤ 0)]
      nlinarith [mul_nonneg hnx (sub_nonneg.mpr h)]
    · rw [abs_of_nonneg (by nlinarith : 0 ≤ x - y)]
      nlinarith [mul_nonneg hny (sub_nonneg.mpr h)]
  nlinarith [sq_abs (Real.sqrt x - Real.sqrt y), abs_nonneg (Real.sqrt x - Real.sqrt y)]

/-- A common positive square-root floor gives linear error propagation. -/
theorem difference_le_of_floor (x y e l : ℝ) (hl : 0 < l)
    (hx : l ^ 2 ≤ x) (hy : l ^ 2 ≤ y) (herror : |x - y| ≤ e)
    : |Real.sqrt x - Real.sqrt y| ≤ e / (2 * l) := by
  have hnx := Real.sqrt_nonneg x
  have hny := Real.sqrt_nonneg y
  have hsx := Real.sq_sqrt ((sq_nonneg l).trans hx)
  have hsy := Real.sq_sqrt ((sq_nonneg l).trans hy)
  have hxl := Real.le_sqrt_of_sq_le hx
  have hyl := Real.le_sqrt_of_sq_le hy
  have hid : |Real.sqrt x - Real.sqrt y| * (Real.sqrt x + Real.sqrt y) = |x - y| := by
    rw [← abs_of_nonneg (add_nonneg hnx hny), ← abs_mul]
    congr 1
    nlinarith
  apply (le_div_iff₀ (by linarith : 0 < 2 * l)).mpr
  calc
    |Real.sqrt x - Real.sqrt y| * (2 * l)
        ≤ |Real.sqrt x - Real.sqrt y| * (Real.sqrt x + Real.sqrt y) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ ≤ e := hid.le.trans herror

end Flare.Analysis.SqrtBounds
