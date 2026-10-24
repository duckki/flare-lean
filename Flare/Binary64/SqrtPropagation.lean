module

public import Flare.Analysis.SqrtBounds
public import Flare.Binary64.Pipeline
public import Flare.Binary64.Sqrt

/-! Composable bounds for the actual rounded binary64 square root. Proposed
rational endpoints and incoming-error bounds remain proof obligations. The native
rounding theorem discharges the primitive error, including zero and subnormals. -/

@[expose] public section

namespace Flare.Binary64.SqrtPropagation

open Flare.Binary64.Pipeline Flare.Binary64.Value

/-- Transfer checked root enclosures and an independent-reference perturbation
allowance to native bounds. Nonnegativity of the native result is also retained
for subsequent square roots, including those whose domain contains zero. -/
theorem native_sqrt {C W I E i l u j d rho : ℝ} {x : Float}
    (b : NativeBounds C W I E x i)
    (hl : 0 ≤ l) (hu : 0 ≤ u) (hj : 0 ≤ j)
    (hlo : l ^ 2 ≤ value x) (hup : value x ≤ u ^ 2)
    (hij : i ≤ j ^ 2)
    (hd : |Real.sqrt (value x) - Real.sqrt i| ≤ d)
    (hrho : (2 : ℝ) ^ (-53 : Int) * u ≤ rho)
    : NativeBounds ((l + u) / 2) ((u - l) / 2 + rho) j (d + rho) x.sqrt (Real.sqrt i)
      ∧ 0 ≤ value x.sqrt := by
  have hn := (sq_nonneg l).trans hlo
  have hround := Flare.Binary64.Sqrt.sqrt_error_nearest x b.finite hn
  have hlroot := (Real.le_sqrt hl hn).mpr hlo
  have huroot := (Real.sqrt_le_iff).mpr ⟨hu, hup⟩
  have hiroot := (Real.sqrt_le_iff).mpr ⟨hj, hij⟩
  have hraw : Bounds ((l + u) / 2) ((u - l) / 2) j d
      (Real.sqrt (value x)) (Real.sqrt i) := by
    refine ⟨?_, ?_, hd⟩
    · rw [abs_le]
      constructor <;> linarith
    · rwa [abs_of_nonneg (Real.sqrt_nonneg i)]
  refine ⟨⟨hround.1, rounded hraw (hround.2.trans ?_)⟩, ?_⟩
  · exact (mul_le_mul_of_nonneg_left huroot (by norm_num)).trans hrho
  · have hlo' := (abs_le.mp hround.2).1
    have hunit : (2 : ℝ) ^ (-53 : Int) ≤ 1 := by norm_num
    have hsmall := mul_le_mul_of_nonneg_right hunit (Real.sqrt_nonneg (value x))
    linarith

end Flare.Binary64.SqrtPropagation
