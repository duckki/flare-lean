import Flare.Analysis.SchurComplement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Real conditioning facts used to connect native linear algebra to its input
domain. These are numerical-analysis lemmas, not additional optimizer premises. -/

namespace Flare.Analysis.NumericalBounds
open Matrix

/-- A covariance bound and a known-noise floor bound every gain entry. This uses
only exact matrix inequalities; no native gain magnitude is assumed. -/
theorem gain_entry_bound {n o : Nat} (K : Matrix (Fin n) (Fin o) ℝ)
    (R : Matrix (Fin o) (Fin o) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hR : (R - (1 / 4 : ℝ) • 1).PosSemidef)
    (hB : (B - K * R * K.transpose).PosSemidef) (hb : ∀ i, B i i ≤ 4)
    : ∀ i j, |K i j| ≤ 4 := by
  have hcong := hR.mul_mul_conjTranspose_same K
  have hbound : (B - (1 / 4 : ℝ) • (K * K.transpose)).PosSemidef := by
    convert hB.add hcong using 1
    simp only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    abel
  intro i j
  have hdiag := hbound.diag_nonneg (i := i)
  have he : (K * K.transpose) i i = ∑ k, (K i k)^2 := by
    simp only [Matrix.mul_apply, transpose_apply, pow_two]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, he] at hdiag
  have hj : (K i j)^2 ≤ ∑ k, (K i k)^2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  have hs : |K i j|^2 = (K i j)^2 := sq_abs _
  nlinarith [hb i, abs_nonneg (K i j)]

/-- Exact Schur elimination preserves a uniform positive lower bound. This is
the mathematical reason that well-conditioned positive-definite input has safe
exact pivots. Float.PositiveDefiniteFactorization combines this lower bound with
the perturbation estimates for rounded elimination. -/
theorem schur_lower_bound {n m : Nat} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ) (α : ℝ)
    (hα : 0 ≤ α) (hA : A.PosDef)
    (hM : (fromBlocks A B B.transpose D - α • 1).PosSemidef)
    : (D - B.transpose * A⁻¹ * B - α • 1).PosSemidef := by
  have hupper := (PosSemidef.one (n := Fin n) (R := ℝ)).smul hα
  have hpad := hupper.mul_mul_conjTranspose_same
    (fromRows (1 : Matrix (Fin n) (Fin n) ℝ) (0 : Matrix (Fin m) (Fin n) ℝ))
  have hblock : (fromBlocks A B B.transpose (D - α • 1)).PosSemidef := by
    convert hM.add hpad using 1
    simp only [conjTranspose_eq_transpose_of_trivial, transpose_fromRows, transpose_one,
      transpose_zero, fromRows_mul, Matrix.one_mul, Matrix.zero_mul]
    ext (i | i) (j | j) <;> simp [fromBlocks, Matrix.one_apply]
  let := hA.isUnit.invertible
  have h :=
    (hA.fromBlocks₁₁ B (D - α • 1)).mp
      (by simpa only [conjTranspose_eq_transpose_of_trivial] using hblock)
  simpa only [conjTranspose_eq_transpose_of_trivial, sub_right_comm] using h

/-- Entrywise matrix error controls its quadratic form. The factor n is a
finite-dimensional bound, with no spectral computation or native premise. -/
lemma quadratic_perturbation_bound {n : Nat} (E : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hE : ∀ i j, |E i j| ≤ ε) (x : Fin n → ℝ)
    : |x ⬝ᵥ E.mulVec x| ≤ n * ε * ∑ i, (x i) ^ 2 := by
  have heq : x ⬝ᵥ E.mulVec x = ∑ i, ∑ j, x i * E i j * x j := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hentry : ∀ i j, |x i * E i j * x j| ≤ |x i| * ε * |x j| := by
    intro i j
    simp only [abs_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hE i j) (abs_nonneg _)) (abs_nonneg _)
  have hsum : |x ⬝ᵥ E.mulVec x| ≤ ε * (∑ i, |x i|)^2 := by
    rw [heq]
    calc
      _ ≤ ∑ i, |∑ j, x i * E i j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |x i * E i j * x j| :=
        Finset.sum_le_sum
          fun i _ =>
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |x i| * ε * |x j| :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
      _ = _ := by
        simp only [pow_two, Finset.mul_sum, mul_left_comm, mul_comm]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |x i|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sq_abs] at hcs
  have h := mul_le_mul_of_nonneg_left hcs hε
  have he : ε * ((∑ i, (x i)^2) * n) = n * ε * ∑ i, (x i)^2 := by ring
  rw [he] at h
  exact hsum.trans h

/-- A symmetric entrywise perturbation of size ε can lower a matrix's uniform
positive lower bound by at most nε. This quantifies the margin available to a
rounded factorization, instead of presuming that its pivots remain positive. -/
theorem perturbation_lower_bound {n : Nat} (A E : Matrix (Fin n) (Fin n) ℝ)
    (α ε : ℝ) (hε : 0 ≤ ε) (hA : (A - α • 1).PosSemidef)
    (hE : E.IsHermitian) (hb : ∀ i j, |E i j| ≤ ε)
    : (A + E - (α - n * ε) • 1).PosSemidef := by
  have hshift : (E + (n * ε) • 1).PosSemidef := by
    have hdiag := (PosSemidef.one (n := Fin n) (R := ℝ)).smul (mul_nonneg (Nat.cast_nonneg n) hε)
    apply PosSemidef.of_dotProduct_mulVec_nonneg (hE.add hdiag.isHermitian)
    intro x
    have h := (abs_le.mp (quadratic_perturbation_bound E ε hε hb x)).1
    rw [star_trivial, add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul]
    have hself : x ⬝ᵥ x = ∑ i, (x i)^2 := by simp only [dotProduct, pow_two]
    rw [hself]
    change 0 ≤ x ⬝ᵥ E.mulVec x + (n * ε) * ∑ i, (x i)^2
    linarith
  convert hA.add hshift using 1
  rw [sub_smul]
  abel

/-- The matrix lower bound is a lower bound on every quadratic form. -/
lemma quadratic_lower_bound {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (hA : (A - α • 1).PosSemidef) (x : Fin n → ℝ)
    : α * (∑ i, (x i) ^ 2) ≤ x ⬝ᵥ A.mulVec x := by
  have h := hA.dotProduct_mulVec_nonneg x
  rw [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul] at h
  have hself : x ⬝ᵥ x = ∑ i, (x i)^2 := by simp only [dotProduct, pow_two]
  rw [hself] at h
  change 0 ≤ x ⬝ᵥ A.mulVec x - α * ∑ i, (x i)^2 at h
  linarith

/-- A strictly positive uniform lower bound implies positive definiteness. -/
lemma posDef_of_lower_bound {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (hα : 0 < α) (hA : (A - α • 1).PosSemidef)
    : A.PosDef := by
  have hsym : A.IsHermitian := by
    convert hA.isHermitian.add ((PosSemidef.one (n := Fin n) (R := ℝ)).smul hα.le).isHermitian using
      1
    abel
  apply PosDef.of_dotProduct_mulVec_pos hsym
  intro x hx
  rw [star_trivial]
  have hp : 0 < ∑ i, (x i)^2 := by
    apply Finset.sum_pos'
    · intro i _; exact sq_nonneg _
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  exact (mul_pos hα hp).trans_le (quadratic_lower_bound A α hA x)

/-- A partial LDLᵀ factorization has the same exact Schur complement as block
elimination. Uniform conditioning therefore controls the next factor column. -/
theorem factor_schur_lower_bound {n m : Nat} (L D : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin m) (Fin m) ℝ) (α : ℝ)
    (hα : 0 < α) (hL : IsUnit L) (hD : D.PosDef)
    (hM
      : (fromBlocks (L * D * L.transpose) (L * D * C.transpose) (C * D * L.transpose) B
          - α • 1).PosSemidef)
    : (B - C * D * C.transpose - α • 1).PosSemidef := by
  let := hL.invertible
  let := hD.isUnit.invertible
  have hDt : D.transpose = D := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hD.isHermitian.eq
  have hA : (L * D * L.transpose).PosDef := posDef_of_lower_bound _ α hα (by
    convert hM.submatrix Sum.inl using 1
    ext i j
    simp [Matrix.one_apply])
  have hc : (L * D * C.transpose).transpose = C * D * L.transpose := by
    simp only [transpose_mul, transpose_transpose, hDt, Matrix.mul_assoc]
  have h := schur_lower_bound (L * D * L.transpose) (L * D * C.transpose) B α hα.le hA
    (by simpa only [hc] using hM)
  have he : (L * D * C.transpose).transpose * (L * D * L.transpose)⁻¹ *
      (L * D * C.transpose) = C * D * C.transpose := by
    rw [hc, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc, Matrix.inv_mul_cancel_left_of_invertible,
      Matrix.mul_inv_cancel_left_of_invertible]
  simpa only [he] using h

/-- A nonnegative diagonal factor can only reduce the uneliminated diagonals.
Together with `factor_schur_lower_bound`, this bounds the next pivot and column. -/
lemma factor_schur_diagonal_le {n m : Nat} (D : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin m) (Fin m) ℝ)
    (hD : D.PosSemidef) (i : Fin m)
    : (B - C * D * C.transpose) i i ≤ B i i := by
  have h := (hD.mul_mul_conjTranspose_same C).diag_nonneg (i := i)
  simp only [conjTranspose_eq_transpose_of_trivial] at h
  exact sub_le_self _ h

/-- Every two-coordinate restriction of a positive semidefinite matrix obeys
the scalar Cauchy inequality. In LDLᵀ this bounds a Schur residual by its pivots. -/
lemma entry_sq_le_diagonal_product {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (i j : Fin n)
    : (A i j) ^ 2 ≤ A i i * A j j := by
  have hsym : A j i = A i j := by
    have h := congr_fun (congr_fun hA.isHermitian.eq i) j
    simpa only [conjTranspose_apply, star_trivial] using h
  have hii := hA.diag_nonneg (i := i)
  by_cases hz : A i i = 0
  · have hzero : A.mulVec (Pi.single i 1) = 0 :=
      hA.dotProduct_mulVec_zero_iff.mp (by
        simp only [star_trivial, mulVec_single_one, single_one_dotProduct, col_apply, hz])
    have hij := congr_fun hzero j
    simp only [mulVec_single_one, col_apply, Pi.zero_apply, hsym] at hij
    simp [hz, hij]
  · have hii' : 0 < A i i := lt_of_le_of_ne hii (Ne.symm hz)
    have hq := hA.dotProduct_mulVec_nonneg
      (A i i • Pi.single j 1 - A i j • Pi.single i 1)
    simp only [star_trivial, mulVec_sub, mulVec_smul, mulVec_single_one,
      dotProduct_sub, sub_dotProduct, smul_dotProduct, dotProduct_smul,
      single_one_dotProduct, col_apply, hsym, smul_eq_mul] at hq
    have hfactor : A i i * ((A i i * A j j) - (A i j)^2) =
        A i i * (A i i * A j j - A i j * A i j) -
        A i j * (A i i * A i j - A i j * A i i) := by ring
    rw [← hfactor] at hq
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hii').mp hq)

/-- Residual control in squared Euclidean norm. With A ≽ αI and α > 0,
the solution error is at most the equation residual divided by α. -/
theorem residual_squared_bound {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ)
    (α : ℝ) (hα : 0 < α) (hA : (A - α • 1).PosSemidef) (x : Fin n → ℝ)
    : α ^ 2 * (∑ i, (x i) ^ 2) ≤ ∑ i, (A.mulVec x i) ^ 2 := by
  have hq := quadratic_lower_bound A α hA x
  have hx : 0 ≤ ∑ i, (x i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (A.mulVec x)
  change (x ⬝ᵥ A.mulVec x)^2 ≤ (∑ i, (x i)^2) * ∑ i, (A.mulVec x i)^2 at hcs
  have hqnonneg : 0 ≤ x ⬝ᵥ A.mulVec x := (mul_nonneg hα.le hx).trans hq
  have hsq : (α * ∑ i, (x i)^2)^2 ≤ (x ⬝ᵥ A.mulVec x)^2 :=
    sq_le_sq₀ (mul_nonneg hα.le hx) hqnonneg |>.mpr hq
  by_cases hz : ∑ i, (x i)^2 = 0
  · rw [hz, mul_zero]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  · have hp : 0 < ∑ i, (x i)^2 := lt_of_le_of_ne hx (Ne.symm hz)
    have h := hsq.trans hcs
    have he : (α * ∑ i, (x i)^2)^2 = (∑ i, (x i)^2) * (α^2 * ∑ i, (x i)^2) := by ring
    rw [he] at h
    exact (mul_le_mul_iff_right₀ hp).mp h

/-- The inverse of A ≽ αI has each entry bounded by 1/α. The proof uses exact
linear-system residuals; it does not assume accuracy of a computed inverse. -/
theorem inverse_entry_bound {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (hα : 0 < α) (hA : (A - α • 1).PosSemidef)
    : ∀ i j, |A⁻¹ i j| ≤ 1 / α := by
  have hpd := posDef_of_lower_bound A α hα hA
  have hinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (A.isUnit_iff_isUnit_det.mp hpd.isUnit)
  intro i j
  have heq : A.mulVec (fun k => A⁻¹ k j) = Pi.single j 1 := by
    ext k
    have hk := congr_fun (congr_fun hinv k) j
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply,
      Pi.single_apply, eq_comm] using hk
  have hr := residual_squared_bound A α hα hA (fun k => A⁻¹ k j)
  rw [heq] at hr
  have hh : ∑ k : Fin n, ((Pi.single j 1 : Fin n → ℝ) k)^2 = 1 := by simp [Pi.single_apply]
  rw [hh] at hr
  have hsq : (A⁻¹ i j)^2 ≤ ∑ k, (A⁻¹ k j)^2 :=
    Finset.single_le_sum (f := fun k : Fin n => (A⁻¹ k j)^2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  have hb := (mul_le_mul_of_nonneg_left hsq (sq_nonneg α)).trans hr
  apply (le_div_iff₀ hα).mpr
  have hs : |A⁻¹ i j|^2 = (A⁻¹ i j)^2 := sq_abs _
  nlinarith [abs_nonneg (A⁻¹ i j)]

/-- Entrywise solve error from an entrywise equation residual. This applies to
any approximate solution after its native residual has been bounded. It does
not assume that a native solve is accurate or that factorization succeeds. -/
theorem residual_entrywise_bound {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ)
    (α δ : ℝ) (hα : 0 < α) (hδ : 0 ≤ δ) (hA : (A - α • 1).PosSemidef)
    (computed exact rhs : Fin n → ℝ) (hexact : A.mulVec exact = rhs)
    (hres : ∀ i, |A.mulVec computed i - rhs i| ≤ δ)
    : ∀ i, |computed i - exact i| ≤ (n : ℝ) * δ / α := by
  let error := computed - exact
  have h := residual_squared_bound A α hα hA error
  have hmul : A.mulVec error = A.mulVec computed - rhs := by
    dsimp [error]
    rw [mulVec_sub, hexact]
  have hr : ∑ i, (A.mulVec error i)^2 ≤ n * δ^2 := by
    calc
      _ ≤ ∑ _i : Fin n, δ ^ 2 :=
        Finset.sum_le_sum
          fun i _ => by
            rw [hmul]
            simpa only [sq_abs, Pi.sub_apply] using (sq_le_sq₀ (abs_nonneg _) hδ).mpr (hres i)
      _ = _ := by simp
  intro i
  have hpos : 1 ≤ n := by have := i.isLt; omega
  have hpos' : (1 : ℝ) ≤ n := by exact_mod_cast hpos
  have hi : (error i)^2 ≤ ∑ j, (error j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hh := (mul_le_mul_of_nonneg_left hi (sq_nonneg α)).trans (h.trans hr)
  have hnonneg : 0 ≤ (n : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ
  have hscaled : α * |error i| ≤ (n : ℝ) * δ := by
    have hsq : |error i|^2 = (error i)^2 := sq_abs _
    have hnn : (n : ℝ) * δ^2 ≤ (n : ℝ)^2 * δ^2 :=
      mul_le_mul_of_nonneg_right (by nlinarith : (n : ℝ) ≤ (n : ℝ)^2) (sq_nonneg δ)
    nlinarith [abs_nonneg (error i)]
  apply (le_div_iff₀ hα).mpr
  simpa only [error, Pi.sub_apply, mul_comm] using hscaled

end Flare.Analysis.NumericalBounds
