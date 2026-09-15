import Flare.Analysis.Factorization
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Conditioned linear-solve estimates from componentwise residual bounds.
These lemmas absorb dependence on the computed solution's magnitude; they do
not assume an accurate numerical solver. -/

namespace Flare.Analysis.LinearSolve
open Matrix

private lemma sum_abs_le {n : Nat} (x : EuclideanSpace ℝ (Fin n))
    : (∑ i, |x i|) ≤ Real.sqrt n * ‖x‖ := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) (fun i : Fin n => |x i|) (fun _ => (1
    : ℝ))
  simp only [mul_one, sq_abs, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hh
  apply (sq_le_sq₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), EuclideanSpace.norm_sq_eq]
  simpa only [Real.norm_eq_abs, sq_abs, mul_comm] using hh

/-- A componentwise residual with a column-sum term gives a Euclidean bound
with one dimension factor, rather than a separate maximum bound per entry. -/
theorem componentwise_residual_norm {n : Nat} (r b x : EuclideanSpace ℝ (Fin n))
    (α c δ : ℝ) (hα : 0 ≤ α) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hr : ∀ i, |r i| ≤ α * |b i| + c * (∑ k, |x k|) + δ)
    : ‖r‖ ≤ α * ‖b‖ + n * c * ‖x‖ + Real.sqrt n * δ := by
  let S := ∑ k, |x k|
  let babs : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => |b i|)
  let z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => c * S + δ)
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcz : 0 ≤ c * S + δ := add_nonneg (mul_nonneg hc hS) hδ
  have hba : ‖babs‖ = ‖b‖ := by
    simp only [EuclideanSpace.norm_eq, babs, Real.norm_eq_abs, abs_abs]
  have hz : ‖z‖ = Real.sqrt n * (c * S + δ) := by
    simp only [EuclideanSpace.norm_eq, z, Real.norm_eq_abs, sq_abs,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq_eq_abs, abs_of_nonneg hcz]
  have hnorm : ‖r‖ ≤ ‖α • babs + z‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    apply Finset.sum_le_sum
    intro i _
    change (r i)^2 ≤ (α * |b i| + (c * S + δ))^2
    have hi : |r i| ≤ α * |b i| + (c * S + δ) := by simpa only [add_assoc] using hr i
    have hh := (sq_le_sq₀ (abs_nonneg _) (add_nonneg (mul_nonneg hα (abs_nonneg _)) hcz)).mpr hi
    simpa only [sq_abs] using hh
  have htri : ‖r‖ ≤ α * ‖b‖ + Real.sqrt n * (c * S + δ) := by
    have hh := hnorm.trans (norm_add_le (α • babs) z)
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hα, hba, hz] using hh
  have hsum := sum_abs_le x
  have hh := mul_le_mul_of_nonneg_left hsum (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hc)
  have hsqrt : (Real.sqrt (n : ℝ))^2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have heq : Real.sqrt (n : ℝ) * c * (Real.sqrt n * ‖x‖) = n * c * ‖x‖ := by
    calc
      _ = (Real.sqrt (n : ℝ)) ^ 2 * c * ‖x‖ := by ring
      _ = _ := by rw [hsqrt]
  rw [heq] at hh
  change Real.sqrt (n : ℝ) * c * S ≤ _ at hh
  linarith only [htri, hh]

/-- A positive matrix lower bound controls the norm of a vector by the norm
of its image. This is the conditioning fact used to absorb numerical residuals. -/
theorem matrix_lower_bound {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) (σ : ℝ)
    (hσ : 0 < σ) (hA : (A - σ • 1).PosSemidef) (x : EuclideanSpace ℝ (Fin n))
    : σ * ‖x‖ ≤ ‖WithLp.toLp 2 (A.mulVec x)‖ := by
  have hh := NumericalBounds.residual_squared_bound A σ hσ hA x
  apply (sq_le_sq₀ (mul_nonneg hσ.le (norm_nonneg _)) (norm_nonneg _)).mp
  simpa only [mul_pow, EuclideanSpace.norm_sq_eq, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]
    using hh

/-- Conditioning absorbs the output-dependent residual term. The conclusion
bounds both the computed solution and its distance from an exact solution. -/
theorem conditioned_solve_bounds {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ)
    (b x exact : EuclideanSpace ℝ (Fin n)) (σ α c δ : ℝ)
    (hσ : 0 < σ) (hA : (A - σ • 1).PosSemidef)
    (hα : 0 ≤ α) (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hgap : n * c < σ)
    (hexact : A.mulVec exact = b)
    (hr : ∀ i, |A.mulVec x i - b i| ≤ α * |b i| + c * (∑ k, |x k|) + δ)
    : ‖x‖ ≤ ((1 + α) * ‖b‖ + Real.sqrt n * δ) / (σ - n * c)
      ∧ ‖x - exact‖ ≤ (α * ‖b‖ + n * c * (‖b‖ / σ) + Real.sqrt n * δ) / (σ - n * c) := by
  let r : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (A.mulVec x) - b
  have hres := componentwise_residual_norm r b x α c δ hα hc hδ hr
  have hgap' : 0 < σ - n * c := sub_pos.mpr hgap
  have hnc : 0 ≤ (n : ℝ) * c := mul_nonneg (Nat.cast_nonneg _) hc
  have himage := matrix_lower_bound A σ hσ hA x
  have hsum : ‖WithLp.toLp 2 (A.mulVec x)‖ ≤ ‖r‖ + ‖b‖ := by
    have hh := norm_add_le r b
    simpa only [r, sub_add_cancel] using hh
  have hnorm : ‖x‖ ≤ ((1 + α) * ‖b‖ + Real.sqrt n * δ) / (σ - n * c) := by
    apply (le_div_iff₀ hgap').mpr
    nlinarith only [himage, hsum, hres]
  have hexactnorm : ‖exact‖ ≤ ‖b‖ / σ := by
    have hh := matrix_lower_bound A σ hσ hA exact
    rw [hexact] at hh
    apply (le_div_iff₀ hσ).mpr
    simpa only [WithLp.toLp_ofLp, mul_comm] using hh
  have herror_image : WithLp.toLp 2 (A.mulVec (x - exact)) = r := by
    apply WithLp.ofLp_injective 2
    change A.mulVec (x - exact) = A.mulVec x - b
    rw [Matrix.mulVec_sub, hexact]
  have he := matrix_lower_bound A σ hσ hA (x - exact)
  change σ * ‖x - exact‖ ≤ ‖WithLp.toLp 2 (A.mulVec (x.ofLp - exact.ofLp))‖ at he
  rw [herror_image] at he
  have hx : ‖x‖ ≤ ‖x - exact‖ + ‖exact‖ := by
    have hh := norm_add_le (x - exact) exact
    simpa only [sub_add_cancel] using hh
  have hx' := mul_le_mul_of_nonneg_left hx hnc
  have he' := mul_le_mul_of_nonneg_left hexactnorm hnc
  refine ⟨hnorm, (le_div_iff₀ hgap').mpr ?_⟩
  nlinarith only [he, hres, hx', he']

end Flare.Analysis.LinearSolve
