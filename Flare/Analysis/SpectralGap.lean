module

public import Flare.Analysis.JacobiNorms
public import Flare.Analysis.NumericalBounds
public import Flare.Analysis.MoorePenrose
public import Flare.Analysis.PseudoinversePerturbation

/-! Consequences of a positive spectral gap. A polynomial matrix inequality
gives rank-separation facts without assuming that a numerical eigensolver
or cutoff has selected the correct rank. -/

@[expose] public section

namespace Flare.Analysis.SpectralGap
open Matrix SpectralPerturbation JacobiNorms
open scoped Matrix.Norms.L2Operator

/-- Below half the positive spectral gap, an approximate eigenvalue is no
larger in magnitude than its eigen-equation residual. This includes negatives. -/
theorem residual_lower_bound {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) (α d : ℝ)
    (hA : A.PosSemidef) (hgap : (A * A - α • A).PosSemidef) (hd : d ≤ α / 2)
    (x : Fin n → ℝ)
    : d ^ 2 * (∑ i, (x i) ^ 2) ≤ ∑ i, (A.mulVec x i - d * x i) ^ 2 := by
  have hP : (A * A - (2 * d) • A).PosSemidef := by
    convert hgap.add (hA.smul (show 0 ≤ α - 2 * d by linarith only [hd])) using 1
    module
  have hsym : A.transpose = A := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hA.isHermitian
  have hdot := hP.dotProduct_mulVec_nonneg x
  rw [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul] at hdot
  have hAA : x ⬝ᵥ (A * A).mulVec x = ∑ i, (A.mulVec x i)^2 := by
    rw [← mulVec_mulVec, ← hsym, dotProduct_transpose_mulVec]
    simp only [dotProduct, pow_two, hsym]
  rw [hAA, smul_eq_mul] at hdot
  have he : (∑ i, (A.mulVec x i - d * x i)^2) =
      (∑ i, (A.mulVec x i)^2) - 2 * d * (x ⬝ᵥ A.mulVec x) + d^2 * ∑ i, (x i)^2 := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  linarith only [hdot]

/-- A nearby real diagonal representation separates small values from the
positive spectral range. A cutoff larger than ε removes all values below α/2. -/
theorem diagonal_separation {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (α ε : ℝ)
    (hA : A.PosSemidef) (hgap : (A * A - α • A).PosSemidef)
    (he : ‖A - diagonal d‖ ≤ ε) (j : Fin n) (hd : d j ≤ α / 2)
    : |d j| ≤ ε := by
  have hε := (norm_nonneg _).trans he
  have hres := residual_lower_bound A α (d j) hA hgap hd (Pi.single j 1)
  have hcol := column_energy_le_norm (A - diagonal d) j
  have herr := (sq_le_sq₀ (norm_nonneg _) hε).mpr he
  have henergy : ∑ i, (A.mulVec (Pi.single j 1) i - d j * (Pi.single j 1 : Fin n → ℝ) i)^2 =
      ∑ i, ((A - diagonal d) i j)^2 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hij : i = j
    · subst i; simp
    · simp [hij, Matrix.sub_apply]
  rw [henergy] at hres
  simp only [Pi.single_apply, ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0), Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, mul_one] at hres
  apply (sq_le_sq₀ (abs_nonneg _) hε).mp
  rw [sq_abs]
  exact hres.trans (hcol.trans herr)

/-- The polynomial spectral-gap assumption survives the exact orthogonal
change of coordinates used by the eigensolver's reference matrix. -/
theorem orthogonal_gap {n : Nat} (A W : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (hA : A.PosSemidef) (hgap : (A * A - α • A).PosSemidef)
    (hW : W ∈ unitary (Matrix (Fin n) (Fin n) ℝ))
    : (W.transpose * A * W).PosSemidef
      ∧ ((W.transpose * A * W) * (W.transpose * A * W) - α • (W.transpose * A * W)).PosSemidef := by
  have hWW : W * W.transpose = 1 := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hW.2
  have congruence (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef) :
      (W.transpose * M * W).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, transpose_transpose]
      using hM.mul_mul_conjTranspose_same W.transpose
  refine ⟨congruence A hA, ?_⟩
  have he : (W.transpose * A * W) * (W.transpose * A * W) - α • (W.transpose * A * W) =
      W.transpose * (A * A - α • A) * W := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc
      _ = W.transpose * A * (W * W.transpose) * A * W := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hWW]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [he]
  exact congruence _ hgap

/-- Apply the gap separation to a diagonal approximation in an exactly
orthogonal frame. This is the mathematical step needed for native rank cutoff. -/
theorem orthogonal_diagonal_separation {n : Nat} (A W : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (α ε : ℝ) (hA : A.PosSemidef) (hgap : (A * A - α • A).PosSemidef)
    (hW : W ∈ unitary (Matrix (Fin n) (Fin n) ℝ))
    (he : ‖diagonal d - W.transpose * A * W‖ ≤ ε) (j : Fin n) (hd : d j ≤ α / 2)
    : |d j| ≤ ε := by
  have hg := orthogonal_gap A W α hA hgap hW
  apply diagonal_separation _ d α ε hg.1 hg.2 _ j hd
  rwa [norm_sub_rev]

/-- Thresholding a separated diagonal spectrum produces a PSD matrix and its
exact pseudoinverse. Retained reciprocal magnitudes are bounded by 2/α, while
discarding entries perturbs the diagonal by at most the chosen cutoff. -/
theorem diagonal_truncation {n : Nat} (d : Fin n → ℝ) (α ε θ : ℝ)
    (hα : 0 < α) (hε : 0 ≤ ε) (hθ : ε ≤ θ)
    (hsep : ∀ j, d j ≤ α / 2 → |d j| ≤ ε)
    : let b := fun j => if θ < |d j| then d j else 0
      (diagonal b).PosSemidef
      ∧ Flare.Analysis.MoorePenrose (diagonal b) (diagonal (fun j => (b j)⁻¹))
      ∧ (diagonal (fun j => (b j)⁻¹)).PosSemidef
      ∧ ‖(diagonal (fun j => (b j)⁻¹) : Matrix (Fin n) (Fin n) ℝ)‖ ≤ 2 / α
      ∧ ‖diagonal b - diagonal d‖ ≤ θ := by
  let b := fun j => if θ < |d j| then d j else 0
  have hθ0 : 0 ≤ θ := hε.trans hθ
  have hkeep (j : Fin n) (hj : θ < |d j|) : α / 2 < d j :=
    lt_of_not_ge (fun hsmall => (not_lt_of_ge ((hsep j hsmall).trans hθ)) hj)
  have hb (j : Fin n) : 0 ≤ b j := by
    dsimp [b]
    split_ifs with hj
    · exact ((show 0 < α / 2 by positivity).trans (hkeep j hj)).le
    · exact le_rfl
  have hmp : Flare.Analysis.MoorePenrose (diagonal b) (diagonal (fun j => (b j)⁻¹)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [diagonal_mul_diagonal, mul_inv_mul_cancel]
    · simp only [diagonal_mul_diagonal, diagonal_eq_diagonal_iff]
      intro j
      by_cases hj : b j = 0 <;> simp [hj]
    · simp [diagonal_mul_diagonal]
    · simp [diagonal_mul_diagonal]
  refine ⟨.diagonal hb, hmp, .diagonal (fun j => inv_nonneg.mpr (hb j)), ?_, ?_⟩
  · rw [l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (show 0 ≤ 2 / α by positivity)).mpr
    intro j
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hb j))]
    dsimp [b]
    split_ifs with hj
    · have he := one_div_le_one_div_of_le (show 0 < α / 2 by positivity) (hkeep j hj).le
      simpa only [one_div, inv_div, inv_inv] using he
    · simp only [_root_.inv_zero]
      positivity
  · rw [diagonal_sub, l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg hθ0).mpr
    intro j
    change |b j - d j| ≤ θ
    dsimp [b]
    split_ifs with hj
    · simpa using hθ0
    · simpa only [zero_sub, abs_neg] using le_of_not_gt hj

/-- Lift thresholded diagonal values back through the exact orthogonal frame.
The result is a nearby PSD matrix with a bounded exact pseudoinverse. -/
theorem orthogonal_truncation {n : Nat} (A W : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (α ε θ : ℝ) (hα : 0 < α) (hθ : ε ≤ θ)
    (hA : A.PosSemidef) (hgap : (A * A - α • A).PosSemidef)
    (hW : W ∈ unitary (Matrix (Fin n) (Fin n) ℝ))
    (he : ‖diagonal d - W.transpose * A * W‖ ≤ ε)
    : let b := fun j => if θ < |d j| then d j else 0
      let B := W * diagonal b * W.transpose
      let Z := W * diagonal (fun j => (b j)⁻¹) * W.transpose
      B.PosSemidef
      ∧ Flare.Analysis.MoorePenrose B Z
      ∧ Z.PosSemidef
      ∧ ‖Z‖ ≤ 2 / α
      ∧ ‖B - A‖ ≤ ε + θ := by
  let b := fun j => if θ < |d j| then d j else 0
  have ht := diagonal_truncation d α ε θ hα ((norm_nonneg _).trans he) hθ
    (fun j hj => orthogonal_diagonal_separation A W d α ε hA hgap hW he j hj)
  let e := Unitary.conjStarAlgAut ℝ _ (⟨W, hW⟩ : unitary (Matrix (Fin n) (Fin n) ℝ))
  have hmp := MoorePenrose.map_moorePenrose e ht.2.1
  have hB : (W * diagonal b * W.transpose).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using ht.1.mul_mul_conjTranspose_same W
  have hZ : (W * diagonal (fun j => (b j)⁻¹) * W.transpose).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using ht.2.2.1.mul_mul_conjTranspose_same W
  have hWt : W.transpose ∈ unitary (Matrix (Fin n) (Fin n) ℝ) := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using Unitary.star_mem hW
  have hWW : W * W.transpose = 1 := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hW.2
  refine ⟨hB, ?_, hZ, ?_, ?_⟩
  · simpa only [e, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] using hmp
  · rw [CStarRing.norm_mul_mem_unitary _ hWt, CStarRing.norm_mem_unitary_mul _ hW]
    exact ht.2.2.2.1
  · have hid : W * diagonal b * W.transpose - A =
        W * (diagonal b - W.transpose * A * W) * W.transpose := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]
      have heq : W * (W.transpose * A * W) * W.transpose = A := by
        calc
          _ = (W * W.transpose) * A * (W * W.transpose) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hWW]; simp
      rw [heq]
    rw [hid, CStarRing.norm_mul_mem_unitary _ hWt, CStarRing.norm_mem_unitary_mul _ hW]
    exact ((norm_sub_le_norm_sub_add_norm_sub _ (diagonal d) _).trans
      (add_le_add ht.2.2.2.2 he)).trans_eq (add_comm _ _)

/-- The thresholded spectral construction approximates the source
pseudoinverse, with the conditioning factors visible in the error bound.
Native reciprocal and matrix-product rounding are separate obligations. -/
theorem orthogonal_truncation_accuracy {n : Nat} (A W X : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (α ε θ : ℝ) (hα : 0 < α) (hθ : ε ≤ θ)
    (hA : A.PosSemidef) (hgap : (A * A - α • A).PosSemidef)
    (hX : Flare.Analysis.MoorePenrose A X)
    (hW : W ∈ unitary (Matrix (Fin n) (Fin n) ℝ))
    (he : ‖diagonal d - W.transpose * A * W‖ ≤ ε)
    : let b := fun j => if θ < |d j| then d j else 0
      let Z := W * diagonal (fun j => (b j)⁻¹) * W.transpose
      ‖Z - X‖ ≤ (‖X‖ * (2 / α) + ‖X‖ ^ 2 + (2 / α) ^ 2) * (ε + θ) := by
  have ht := orthogonal_truncation A W d α ε θ hα hθ hA hgap hW he
  have hXpsd := MoorePenrose.posSemidef hA hX
  apply PseudoinversePerturbation.difference_norm A _ X _ ‖X‖ (2 / α) (ε + θ)
    (by simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hA.isHermitian)
    (by simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using ht.1.isHermitian)
    (by simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hXpsd.isHermitian)
    (by simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using ht.2.2.1.isHermitian)
    hX ht.2.1 le_rfl ht.2.2.2.1 ht.2.2.2.2

/-- The polynomial PSD gap is exactly the exclusion of positive eigenvalues
below `α`; zero eigenvalues remain legal. -/
theorem eigenvalues_gap {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (hA : A.PosSemidef) (hgap : (A * A - α • A).PosSemidef) (i : Fin n)
    : hA.isHermitian.eigenvalues i = 0 ∨ α ≤ hA.isHermitian.eigenvalues i := by
  let W : Matrix (Fin n) (Fin n) ℝ := hA.isHermitian.eigenvectorUnitary
  have hW : W ∈ unitary (Matrix (Fin n) (Fin n) ℝ) := hA.isHermitian.eigenvectorUnitary.property
  have hd : W.transpose * A * W = diagonal hA.isHermitian.eigenvalues := by
    simpa only [W, Unitary.conjStarAlgAut_star_apply, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq]
      using hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hg := (orthogonal_gap A W α hA hgap hW).2
  rw [hd] at hg
  have hi : 0 ≤ (hA.isHermitian.eigenvalues i)^2 - α * hA.isHermitian.eigenvalues i := by
    simpa only [diagonal_mul_diagonal, Matrix.sub_apply, diagonal_apply_eq, Matrix.smul_apply,
      smul_eq_mul, pow_two]
      using hg.diag_nonneg (i := i)
  by_cases hz : hA.isHermitian.eigenvalues i = 0
  · exact Or.inl hz
  · exact Or.inr (by nlinarith only [hi, lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm hz)])

/-- A PSD matrix with the polynomial gap is either exactly zero or has norm
at least the gap. This supplies the norm floor for nonzero native inversion. -/
theorem zero_or_norm_lower_bound {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (hA : A.PosSemidef) (hgap : (A * A - α • A).PosSemidef)
    : A = 0 ∨ α ≤ ‖A‖ := by
  let W : Matrix (Fin n) (Fin n) ℝ := hA.isHermitian.eigenvectorUnitary
  have hW : W ∈ unitary (Matrix (Fin n) (Fin n) ℝ) := hA.isHermitian.eigenvectorUnitary.property
  have hd : W.transpose * A * W = diagonal hA.isHermitian.eigenvalues := by
    simpa only [W, Unitary.conjStarAlgAut_star_apply, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq]
      using hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hnorm : ‖hA.isHermitian.eigenvalues‖ = ‖A‖ := by
    rw [← l2_opNorm_diagonal, ← hd, similarity_isometry W A hW]
  by_cases hz : A = 0
  · exact Or.inl hz
  · obtain ⟨i, hi⟩ : ∃ i, hA.isHermitian.eigenvalues i ≠ 0 := by
      by_contra h
      have he : hA.isHermitian.eigenvalues = 0 := funext fun i => by simpa using not_exists.mp h i
      apply hz
      apply norm_eq_zero.mp
      rw [← hnorm, he, norm_zero]
    apply Or.inr
    calc
      α ≤ hA.isHermitian.eigenvalues i := (eigenvalues_gap A α hA hgap i).resolve_left hi
      _ = |hA.isHermitian.eigenvalues i| := (abs_of_nonneg (hA.eigenvalues_nonneg i)).symm
      _ ≤ ‖hA.isHermitian.eigenvalues‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm hA.isHermitian.eigenvalues i
      _ = _ := hnorm

/-- The exact pseudoinverse has norm at most the reciprocal spectral gap.
The proof uses the source polynomial gap, not a numerical inverse premise. -/
theorem pseudoinverse_norm {n : Nat} (A X : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (hα : 0 < α) (hA : A.PosSemidef) (hgap : (A * A - α • A).PosSemidef)
    (hX : Flare.Analysis.MoorePenrose A X)
    : ‖X‖ ≤ 1 / α := by
  let e := Unitary.conjStarAlgAut ℝ _ hA.isHermitian.eigenvectorUnitary
  let d := hA.isHermitian.eigenvalues
  let D := diagonal d
  let Z := diagonal (fun i => (d i)⁻¹)
  have hDZ : Flare.Analysis.MoorePenrose D Z := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [D, Z, diagonal_mul_diagonal, mul_inv_mul_cancel]
    · simp only [D, Z, diagonal_mul_diagonal, diagonal_eq_diagonal_iff]
      intro i
      by_cases h : d i = 0 <;> simp [h]
    · simp [D, Z, diagonal_mul_diagonal]
    · simp [D, Z, diagonal_mul_diagonal]
  have he : A = e D := by
    simpa only [e, D, d, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq]
      using hA.isHermitian.spectral_theorem
  have hXeq : X = e Z := MoorePenrose.unique hX (he ▸ MoorePenrose.map_moorePenrose e hDZ)
  have hZ : ‖Z‖ ≤ 1 / α := by
    dsimp only [Z]
    rw [l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hA.eigenvalues_nonneg i)), one_div]
    rcases eigenvalues_gap A α hA hgap i with hz | hi
    · change (d i)⁻¹ ≤ α⁻¹
      rw [show d i = 0 from hz, _root_.inv_zero]
      positivity
    · exact inv_le_inv₀ (hα.trans_le hi) hα |>.mpr hi
  rw [hXeq]
  have hW : (hA.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) ∈ unitary _ :=
    hA.isHermitian.eigenvectorUnitary.property
  have hWt
      : (hA.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).transpose ∈ unitary _ := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using Unitary.star_mem hW
  simpa only [e, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial, CStarRing.norm_mul_mem_unitary _ hWt,
    CStarRing.norm_mem_unitary_mul _ hW]
    using hZ

/-- A small relative formation error preserves a nonzero norm floor. If the
source is zero, the relative error premise forces the formed matrix to be zero
as well; no separate rank assumption is introduced. -/
theorem formed_zero_or_norm_lower_bound {n : Nat} (A N : Matrix (Fin n) (Fin n) ℝ)
    (α ε : ℝ) (hε : 0 ≤ ε) (hε' : ε < 1)
    (hA : A.PosSemidef) (hgap : (A * A - α • A).PosSemidef)
    (he : ‖N - A‖ ≤ ε * ‖N‖)
    : N = 0 ∨ α / (1 + ε) ≤ ‖N‖ := by
  rcases zero_or_norm_lower_bound A α hA hgap with hz | hlo
  · left
    rw [hz, sub_zero] at he
    exact norm_eq_zero.mp (by nlinarith only [he, hε', norm_nonneg N])
  · right
    have ht := norm_le_norm_sub_add A N
    rw [norm_sub_rev] at ht
    have hupper := ht.trans (add_le_add he le_rfl)
    apply (div_le_iff₀ (by positivity : 0 < 1 + ε)).mpr
    nlinarith only [hlo, hupper]

end Flare.Analysis.SpectralGap
