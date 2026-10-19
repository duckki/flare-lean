module

public import Flare.Analysis.SpectralGap
public import Flare.Analysis.LinearSolve
public import Flare.Analysis.Conditioning

/-!
# Gram-matrix domination and residual transport

Real-arithmetic estimates for PSD sums, inverse-weighted products, and projected
solve residuals. Fixed numerical profiles remain explicit in the statements.
-/

@[expose] public section

namespace Flare.Analysis.GramBounds
open Matrix Flare.Analysis SpectralPerturbation Flare.Analysis.Conditioning
open scoped Matrix.Norms.L2Operator

/-- The known-noise floor gives a Gram domination for `R⁻¹ C`. Adding PSD
partial information preserves that domination, without any inverse of `T`. -/
theorem noise_information_domination {o m : Nat} (R : Matrix (Fin o) (Fin o) ℝ)
    (C : Matrix (Fin o) (Fin m) ℝ) (Y : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosDef) (hfloor : (R - (1 / 4 : ℝ) • 1).PosSemidef) (hY : Y.PosSemidef)
    : ((4 : ℝ) • (Y + C.transpose * R⁻¹ * C) - (R⁻¹ * C).transpose * (R⁻¹ * C)).PosSemidef := by
  let := hR.isUnit.invertible
  have hRi : (R⁻¹).transpose = R⁻¹ := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hR.inv.isHermitian
  have hr : ((4 : ℝ) • R⁻¹ - R⁻¹ * R⁻¹).PosSemidef := by
    have hh := (hfloor.mul_mul_conjTranspose_same R⁻¹).smul (by norm_num : (0 : ℝ) ≤ 4)
    convert hh using 1
    simp only [conjTranspose_eq_transpose_of_trivial, hRi, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.inv_mul_of_invertible,
        Matrix.one_mul]
    module
  have hc := hr.mul_mul_conjTranspose_same C.transpose
  convert (hY.smul (by norm_num : (0 : ℝ) ≤ 4)).add hc using 1
  simp only [conjTranspose_eq_transpose_of_trivial, transpose_transpose, transpose_mul, hRi,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, Matrix.mul_assoc]
  abel

/-- The stated positive-definite floor and spectral gap imply both the range
condition and the bound of four for the transported exact inverse. -/
theorem transport_bounds {o m : Nat} (R : Matrix (Fin o) (Fin o) ℝ)
    (C : Matrix (Fin o) (Fin m) ℝ) (Y X : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosDef) (hfloor : (R - (1 / 4 : ℝ) • 1).PosSemidef) (hY : Y.PosSemidef)
    (hgap
      : ((Y + C.transpose * R⁻¹ * C) * (Y + C.transpose * R⁻¹ * C)
          - (1 / 4 : ℝ) • (Y + C.transpose * R⁻¹ * C)).PosSemidef)
    (hX : MoorePenrose (Y + C.transpose * R⁻¹ * C) X)
    : (R⁻¹ * C) * ((Y + C.transpose * R⁻¹ * C) * X) = R⁻¹ * C ∧ ‖R⁻¹ * C * X‖ ≤ 4 := by
  have hT : (Y + C.transpose * R⁻¹ * C).PosSemidef :=
    hY.add
      (by
        simpa only [conjTranspose_eq_transpose_of_trivial, transpose_transpose]
          using hR.inv.posSemidef.mul_mul_conjTranspose_same C.transpose)
  have ht := PseudoinversePerturbation.dominated_transport _ X (R⁻¹ * C) 4 (by norm_num) hT hX
    (noise_information_domination R C Y hR hfloor hY)
  have hXn : ‖X‖ ≤ 4 := (SpectralGap.pseudoinverse_norm _ X (1 / 4) (by norm_num) hT hgap
    hX).trans_eq (by norm_num)
  refine ⟨ht.1, ?_⟩
  nlinarith only [ht.2, hXn, norm_nonneg (R⁻¹ * C * X)]

/-- The bounded input columns have norm below fourteen, uniformly over the
supported observation dimension. -/
theorem column_norm_bound {o k : Nat} (A : Matrix (Fin o) (Fin k) ℝ)
    (ho : o ≤ 12) (hA : ∀ i j, |A i j| ≤ 4) (j : Fin k)
    : ‖WithLp.toLp 2 (fun i => A i j)‖ ≤ 14 := by
  let v : EuclideanSpace ℝ (Fin o) := WithLp.toLp 2 (fun i => A i j)
  have hs : ‖v‖^2 ≤ o * 16 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)).mpr (hA i j))
    simpa only [v, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, show (4 : ℝ)^2 = 16 by norm_num] using hh
  have ho' : (o : ℝ) ≤ 12 := by exact_mod_cast ho
  change ‖v‖ ≤ 14
  nlinarith [norm_nonneg v]

/-- An inverse-weighted matrix product has entries bounded by 784. Using column norms
avoids a spurious second factor of the observation dimension. -/
theorem prepared_product_entry_bound {n o m : Nat} (H : Matrix (Fin o) (Fin n) ℝ)
    (R : Matrix (Fin o) (Fin o) ℝ) (C : Matrix (Fin o) (Fin m) ℝ)
    (ho : o ≤ 12) (hR : (R - (1 / 4 : ℝ) • 1).PosSemidef)
    (hH : ∀ i j, |H i j| ≤ 4) (hC : ∀ i j, |C i j| ≤ 4) (i : Fin n) (j : Fin m)
    : |(H.transpose * R⁻¹ * C) i j| ≤ 784 := by
  let hv : EuclideanSpace ℝ (Fin o) := WithLp.toLp 2 (fun k => H k i)
  let cv : EuclideanSpace ℝ (Fin o) := WithLp.toLp 2 (fun k => C k j)
  let rv : EuclideanSpace ℝ (Fin o) := WithLp.toLp 2 (R⁻¹.mulVec cv)
  have hn := inverse_norm_bound R (1 / 4) (by norm_num) hR
  have hr := l2_opNorm_mulVec R⁻¹ cv
  have hh : ‖hv‖ ≤ 14 := column_norm_bound H ho hH i
  have hc : ‖cv‖ ≤ 14 := column_norm_bound C ho hC j
  have hrv : ‖rv‖ ≤ 56 := by
    have hprod := mul_le_mul hn hc (norm_nonneg cv) (by norm_num : (0 : ℝ) ≤ 1 / (1 / 4))
    norm_num at hprod
    exact hr.trans hprod
  have hinner := abs_real_inner_le_norm hv rv
  have hid : (H.transpose * R⁻¹ * C) i j = inner ℝ hv rv := by
    rw [Matrix.mul_assoc, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
    rfl
  rw [hid]
  exact hinner.trans ((mul_le_mul hh hrv (norm_nonneg _) (by norm_num)).trans_eq (by norm_num))

/-- A PSD matrix with operator norm at most `M` satisfies `A² ≤ M A`.
This spectral estimate keeps the known-noise scale in Gram-matrix formation. -/
theorem square_le_norm_smul {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ)
    (M : ℝ) (hA : A.PosSemidef) (hM : ‖A‖ ≤ M)
    : (M • A - A * A).PosSemidef := by
  let e := Unitary.conjStarAlgAut ℝ _ hA.isHermitian.eigenvectorUnitary
  let D := diagonal hA.isHermitian.eigenvalues
  have he : A = e D := by
    simpa only [e, D, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq]
      using hA.isHermitian.spectral_theorem
  have hd : ‖hA.isHermitian.eigenvalues‖ = ‖A‖ := by
    rw [← l2_opNorm_diagonal]
    have hh : ‖e D‖ = ‖D‖ := by
      exact similarity_isometry
        (hA.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).transpose D
        (by simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
          (Unitary.star_mem hA.isHermitian.eigenvectorUnitary.property))
    exact hh.symm.trans (congrArg norm he.symm)
  have hD : (M • D - D * D).PosSemidef := by
    dsimp only [D]
    rw [diagonal_mul_diagonal, ← diagonal_smul, diagonal_sub]
    apply PosSemidef.diagonal
    intro i
    have hi : hA.isHermitian.eigenvalues i ≤ M :=
      (le_abs_self _).trans ((norm_le_pi_norm _ i).trans (hd.le.trans hM))
    change 0 ≤ M * hA.isHermitian.eigenvalues i - _
    nlinarith only [mul_nonneg (hA.eigenvalues_nonneg i) (sub_nonneg.mpr hi)]
  have hp : (e (M • D - D * D)).PosSemidef := by
    simpa only [e, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
      using hD.mul_mul_conjTranspose_same
        (hA.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  simpa only [map_sub, map_smul, map_mul, ← he] using hp

/-- The noise norm gives `CᵀC ≤ ‖R‖ T`, complementary to the inverse-noise
bound `FᵀF ≤ 4 T` for `F=R⁻¹C`. -/
theorem input_gram_domination {o m : Nat} (R : Matrix (Fin o) (Fin o) ℝ)
    (C : Matrix (Fin o) (Fin m) ℝ) (Y : Matrix (Fin m) (Fin m) ℝ)
    (M : ℝ) (hR : R.PosDef) (hY : Y.PosSemidef) (hM : ‖R‖ ≤ M)
    : (M • (Y + C.transpose * R⁻¹ * C) - C.transpose * C).PosSemidef := by
  let := hR.isUnit.invertible
  have hRi : (R⁻¹).transpose = R⁻¹ := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hR.inv.isHermitian
  have hi : (M • R⁻¹ - 1).PosSemidef := by
    have hh := (square_le_norm_smul R M hR.posSemidef hM).mul_mul_conjTranspose_same R⁻¹
    convert hh using 1
    simp only [conjTranspose_eq_transpose_of_trivial, hRi, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_inv_of_invertible,
      Matrix.mul_one, Matrix.inv_mul_of_invertible, Matrix.one_mul]
  have hh := hi.mul_mul_conjTranspose_same C.transpose
  have hm0 : 0 ≤ M := (norm_nonneg R).trans hM
  convert (hY.smul hm0).add hh using 1
  simp only [conjTranspose_eq_transpose_of_trivial, transpose_transpose,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    smul_add, Matrix.mul_assoc]
  abel

/-- Exact Gram error equals the solve residual projected through `R⁻¹C`.
Using this identity avoids charging the condition number a second time. -/
theorem cross_residual_identity {n o m : Nat} (R : Matrix (Fin o) (Fin o) ℝ)
    (H : Matrix (Fin o) (Fin n) ℝ) (C X : Matrix (Fin o) (Fin m) ℝ) (hR : R.PosDef)
    : H.transpose * X - H.transpose * R⁻¹ * C = (R⁻¹ * H).transpose * (R * X - C) := by
  let := hR.isUnit.invertible
  have hi : (R⁻¹).transpose = R⁻¹ := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hR.inv.isHermitian
  simp only [transpose_mul, hi, Matrix.mul_sub, Matrix.mul_assoc,
    ← Matrix.mul_assoc R⁻¹ R X, Matrix.inv_mul_of_invertible, Matrix.one_mul]

/-- Exact Gram error equals the solve residual projected through `R⁻¹C`.
Using this identity avoids charging the condition number a second time. -/
theorem gram_residual_identity {o m : Nat} (R : Matrix (Fin o) (Fin o) ℝ)
    (C X : Matrix (Fin o) (Fin m) ℝ) (hR : R.PosDef)
    : C.transpose * X - C.transpose * R⁻¹ * C = (R⁻¹ * C).transpose * (R * X - C) :=
  cross_residual_identity R C C X hR

/-- The public noise floor and entry-induced noise norm bound give the two
complementary scales used in native Gram formation. -/
theorem gram_operand_norms {o m : Nat} (R : Matrix (Fin o) (Fin o) ℝ)
    (C : Matrix (Fin o) (Fin m) ℝ) (Y : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosDef) (hfloor : (R - (1 / 4 : ℝ) • 1).PosSemidef)
    (hY : Y.PosSemidef) (hRn : ‖R‖ ≤ 48)
    : let T := Y + C.transpose * R⁻¹ * C
      ‖R⁻¹ * C‖ ^ 2 ≤ 4 * ‖T‖ ∧ ‖C‖ ^ 2 ≤ 48 * ‖T‖ ∧ ‖C‖ * ‖R⁻¹ * C‖ ≤ 14 * ‖T‖ := by
  let T := Y + C.transpose * R⁻¹ * C
  have hf := gram_norm_bound (R⁻¹ * C) ((4 : ℝ) • T)
    (noise_information_domination R C Y hR hfloor hY)
  have hc := gram_norm_bound C ((48 : ℝ) • T)
    (input_gram_domination R C Y 48 hR hY hRn)
  norm_num only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 48)] at hf hc
  refine ⟨hf, hc, ?_⟩
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow]
  have hh := mul_le_mul hc hf (sq_nonneg _) (by positivity : 0 ≤ 48 * ‖T‖)
  nlinarith only [hh, sq_nonneg ‖T‖]

/-- Zero total information forces both its PSD partial-information term and
the observation-correlation matrix to vanish. No positive-rank assumption is used. -/
theorem zero_information_operands {o m : Nat} (R : Matrix (Fin o) (Fin o) ℝ)
    (C : Matrix (Fin o) (Fin m) ℝ) (Y : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosDef) (hY : Y.PosSemidef) (hz : Y + C.transpose * R⁻¹ * C = 0)
    : Y = 0 ∧ C = 0 := by
  have hG : (C.transpose * R⁻¹ * C).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, transpose_transpose]
      using hR.inv.posSemidef.mul_mul_conjTranspose_same C.transpose
  have hYn := norm_le_of_psd_order Y (Y + C.transpose * R⁻¹ * C) hY (by
    convert hG using 1
    abel)
  rw [hz, norm_zero] at hYn
  have hCn := gram_norm_bound C (‖R‖ • (Y + C.transpose * R⁻¹ * C))
    (input_gram_domination R C Y ‖R‖ hR hY le_rfl)
  rw [hz, smul_zero, norm_zero] at hCn
  refine ⟨norm_eq_zero.mp (le_antisymm hYn (norm_nonneg Y)), norm_eq_zero.mp ?_⟩
  nlinarith only [hCn, norm_nonneg C]

end Flare.Analysis.GramBounds
