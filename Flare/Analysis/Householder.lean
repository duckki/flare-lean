import Mathlib.Tactic

/-! Exact normalized Householder action in matrix coordinates. Mathlib supplies
the abstract reflection infrastructure; this explicit finite-sum formulation
matches the reference used in native QR error analysis. The unit vector may be
obtained by any construction. -/

namespace Flare.Analysis.Householder

noncomputable section

def reflect {height width : Nat} (u : Fin height → ℝ) (a : Matrix (Fin height) (Fin width) ℝ)
    : Matrix (Fin height) (Fin width) ℝ :=
  fun i j => a i j - 2 * u i * ∑ k, u k * a k j

theorem unit_component_bound {height : Nat} (u : Fin height → ℝ)
    (hu : ∑ i, (u i) ^ 2 = 1) (i : Fin height)
    : |u i| ≤ 1 := by
  have hs : (u i)^2 ≤ ∑ k, (u k)^2 := Finset.single_le_sum
    (fun k _ => sq_nonneg (u k)) (Finset.mem_univ i)
  rw [hu] at hs
  nlinarith [sq_abs (u i), abs_nonneg (u i)]

/-- Any exactly unit vector defines a reflection preserving every column Gram,
independently of how that vector was obtained. -/
theorem reflect_gram {height width : Nat} (u : Fin height → ℝ)
    (a : Matrix (Fin height) (Fin width) ℝ) (hu : ∑ i, (u i) ^ 2 = 1)
    : (reflect u a).transpose * reflect u a = a.transpose * a := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, reflect]
  let dj := ∑ i, u i * a i j
  let dk := ∑ i, u i * a i k
  change (∑ i, (a i j - 2 * u i * dj) * (a i k - 2 * u i * dk)) = ∑ i, a i j * a i k
  calc
    _ = ∑ i,
          (a i j * a i k
            - 2 * dk * (u i * a i j)
            - 2 * dj * (u i * a i k)
            + 4 * dj * dk * (u i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hu]
      change (∑ i, a i j * a i k) - 2*dk*dj - 2*dj*dk + 4*dj*dk*1 = _
      ring

end
end Flare.Analysis.Householder
