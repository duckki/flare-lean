module

public import Flare.Analysis.JacobiNorms
public import Flare.Analysis.LinearSolve

/-! Frobenius estimates for rectangular numerical residuals. These proof-side
norms preserve column information when a residual is projected through a matrix;
they do not impose a maximum-entry estimate on every column. -/

@[expose] public section

namespace Flare.Analysis.MatrixError
open Matrix
open scoped Matrix.Norms.L2Operator

/-- Flattened Euclidean representation used only for residual estimates. -/
noncomputable def entries {n m : Nat} (A : Matrix (Fin n) (Fin m) ℝ)
    : EuclideanSpace ℝ (Fin n × Fin m) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

/-- The flattened norm is the Frobenius norm. -/
lemma entries_norm_sq {n m : Nat} (A : Matrix (Fin n) (Fin m) ℝ)
    : ‖entries A‖ ^ 2 = ∑ i, ∑ j, (A i j) ^ 2 := by
  simp only [entries, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs,
    Fintype.sum_prod_type]

lemma entries_add {n m : Nat} (A B : Matrix (Fin n) (Fin m) ℝ)
    : entries (A + B) = entries A + entries B :=
  rfl

lemma entries_sub {n m : Nat} (A B : Matrix (Fin n) (Fin m) ℝ)
    : entries (A - B) = entries A - entries B :=
  rfl

/-- The operator norm is bounded by the Frobenius norm, including rectangular
matrices and empty dimensions. -/
theorem norm_le_entries {n m : Nat} (A : Matrix (Fin n) (Fin m) ℝ) : ‖A‖ ≤ ‖entries A‖ := by
  rw [l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  change ‖WithLp.toLp 2 (A.mulVec x.ofLp)‖^2 ≤ (‖entries A‖ * ‖x‖)^2
  rw [mul_pow, entries_norm_sq]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) x.ofLp)
  rw [← Finset.sum_mul] at hs
  simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, mulVec, dotProduct] using hs

/-- A single dimension factor suffices for the squared Frobenius norm. -/
theorem entries_norm_le {n m : Nat} (A : Matrix (Fin n) (Fin m) ℝ)
    : ‖entries A‖ ≤ Real.sqrt m * ‖A‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [entries_norm_sq, Finset.sum_comm, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => JacobiNorms.column_energy_le_norm A j)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

/-- Multiplication on the left costs its operator norm, not its Frobenius norm. -/
theorem entries_mul_le {n m k : Nat} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin k) ℝ)
    : ‖entries (A * B)‖ ≤ ‖A‖ * ‖entries B‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [entries_norm_sq, mul_pow, entries_norm_sq]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => (B i j)^2), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    (l2_opNorm_mulVec A (WithLp.toLp 2 (fun i => B i j)))
  change ‖WithLp.toLp 2 (A.mulVec (fun i => B i j))‖^2 ≤
    (‖A‖ * ‖WithLp.toLp 2 (fun i => B i j)‖)^2 at hh
  simpa only [mul_pow, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, Matrix.mul_apply,
    mulVec, dotProduct]
    using hh

/-- Entrywise absolute domination transfers to the flattened norm. -/
theorem entries_norm_mono {n m : Nat} (A B : Matrix (Fin n) (Fin m) ℝ)
    (h : ∀ i j, |A i j| ≤ |B i j|)
    : ‖entries A‖ ≤ ‖entries B‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [entries_norm_sq]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr (h i j)

/-- Euclidean norms of the individual columns, as a real vector. -/
noncomputable def columnNorms {n m : Nat} (A : Matrix (Fin n) (Fin m) ℝ)
    : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun j => ‖WithLp.toLp 2 (fun i => A i j)‖)

lemma columnNorms_norm {n m : Nat} (A : Matrix (Fin n) (Fin m) ℝ)
    : ‖columnNorms A‖ = ‖entries A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [entries_norm_sq]
  simp only [columnNorms, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  exact Finset.sum_comm

/-- Columnwise norm domination supplies a Frobenius enclosure. -/
theorem entries_le_of_columns {n m : Nat} (A : Matrix (Fin n) (Fin m) ℝ)
    (v : EuclideanSpace ℝ (Fin m))
    (h : ∀ j, ‖WithLp.toLp 2 (fun i => A i j)‖ ≤ v j)
    : ‖entries A‖ ≤ ‖v‖ := by
  rw [← columnNorms_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  exact Finset.sum_le_sum fun j _ =>
    (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (h j))).mpr (h j)

/-- Componentwise solve residuals combine across all columns without an
additional maximum-entry dimension penalty. -/
theorem entries_residual_norm {n m : Nat} (R B X : Matrix (Fin n) (Fin m) ℝ)
    (α c δ : ℝ) (hα : 0 ≤ α) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (h : ∀ i j, |R i j| ≤ α * |B i j| + c * (∑ k, |X k j|) + δ)
    : ‖entries R‖ ≤ α * ‖entries B‖ + n * c * ‖entries X‖ + Real.sqrt m * Real.sqrt n * δ := by
  let z : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun _ => Real.sqrt n * δ)
  have hz : ‖z‖ = Real.sqrt m * Real.sqrt n * δ := by
    simp only [z, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq (by positivity)]
    ring
  have hh := entries_le_of_columns R (α • columnNorms B + (n * c) • columnNorms X + z)
    (fun j => LinearSolve.componentwise_residual_norm
      (WithLp.toLp 2 (fun i => R i j)) (WithLp.toLp 2 (fun i => B i j))
      (WithLp.toLp 2 (fun i => X i j)) α c δ hα hc hδ (fun i => h i j))
  have htri := hh.trans ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl))
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hα,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hc), columnNorms_norm, hz]
    using htri

lemma entries_smul {n m : Nat} (α : ℝ) (A : Matrix (Fin n) (Fin m) ℝ)
    : entries (α • A) = α • entries A :=
  rfl

lemma entries_abs_norm {n m : Nat} (A : Matrix (Fin n) (Fin m) ℝ)
    : ‖entries (fun i j => |A i j|)‖ = ‖entries A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [entries_norm_sq (fun (i : Fin n) (j : Fin m) => |A i j|), entries_norm_sq A]
  simp only [sq_abs]

lemma entries_const_norm {n m : Nat} (δ : ℝ) (hδ : 0 ≤ δ)
    : ‖entries (fun (_ : Fin n) (_ : Fin m) => δ)‖ = Real.sqrt n * Real.sqrt m * δ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [entries_norm_sq (fun (_ : Fin n) (_ : Fin m) => δ)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt (Nat.cast_nonneg m)]
  ring

/-- Absolute dot-product error estimates combine into a Frobenius bound.
This lemma is independent of the numerical implementation producing `E`. -/
theorem product_roundoff_norm {n k m : Nat} (A : Matrix (Fin n) (Fin k) ℝ)
    (B : Matrix (Fin k) (Fin m) ℝ) (E : Matrix (Fin n) (Fin m) ℝ) (ε η : ℝ)
    (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (he : ∀ i j, |E i j| ≤ ε * ((∑ t, |A i t * B t j|) + η))
    : ‖entries E‖ ≤ ε * (‖entries A‖ * ‖entries B‖ + Real.sqrt n * Real.sqrt m * η) := by
  let AA : Matrix (Fin n) (Fin k) ℝ := fun i j => |A i j|
  let BB : Matrix (Fin k) (Fin m) ℝ := fun i j => |B i j|
  let Z : Matrix (Fin n) (Fin m) ℝ := fun _ _ => η
  have hm : ‖entries E‖ ≤ ‖entries (ε • (AA * BB + Z))‖ := entries_norm_mono E _ (fun i j => by
    change |E i j| ≤ |ε * ((∑ t, |A i t| * |B t j|) + η)|
    simp only [← abs_mul, abs_of_nonneg (mul_nonneg hε
      (add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) hη))]
    exact he i j)
  rw [entries_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hε, entries_add] at hm
  apply hm.trans
  apply mul_le_mul_of_nonneg_left _ hε
  have hp := (entries_mul_le AA BB).trans
    (mul_le_mul_of_nonneg_right (norm_le_entries AA) (norm_nonneg (entries BB)))
  have ht := (norm_add_le (entries (AA * BB)) (entries Z)).trans (add_le_add hp le_rfl)
  simpa only [AA, BB, Z, entries_abs_norm, entries_const_norm η hη] using ht

/-- Copying one triangle has Frobenius amplification at most 1.42. The
symmetric reference is preserved exactly, so only the error is charged. -/
theorem mirror_error_norm {n : Nat} (A E N : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian)
    (hN : ∀ i j, N i j = if j.val ≤ i.val then (A + E) i j else (A + E) j i)
    : ‖entries (N - A)‖ ≤ (71 / 50 : ℝ) * ‖entries E‖ := by
  have hs : ∀ i j, A i j = A j i := fun i j => by
    have hh := congr_fun (congr_fun hA j) i
    simpa only [conjTranspose_apply, star_trivial] using hh
  have hentry (i j) : ((N - A) i j)^2 ≤ (E i j)^2 + (E j i)^2 := by
    rw [Matrix.sub_apply, hN]
    split
    · simp only [Matrix.add_apply, add_sub_cancel_left]
      nlinarith only [sq_nonneg (E j i)]
    · rw [Matrix.add_apply, hs j i, add_sub_cancel_left]
      nlinarith only [sq_nonneg (E i j)]
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => hentry i j
  have he : ‖entries (N - A)‖^2 ≤ 2 * ‖entries E‖^2 := by
    simpa only [entries_norm_sq, Finset.sum_add_distrib,
      Finset.sum_comm (f := fun i j => (E j i)^2), two_mul]
      using hh
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow]
  nlinarith only [he, sq_nonneg ‖entries E‖]

lemma entries_transpose_norm {n m : Nat} (A : Matrix (Fin n) (Fin m) ℝ)
    : ‖entries A.transpose‖ = ‖entries A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [entries_norm_sq, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- A bounded rectangle has the expected dimension-scaled Frobenius norm. -/
theorem entries_bound {n m : Nat} (A : Matrix (Fin n) (Fin m) ℝ) (M : ℝ)
    (hM : 0 ≤ M) (h : ∀ i j, |A i j| ≤ M)
    : ‖entries A‖ ≤ Real.sqrt n * Real.sqrt m * M := by
  have hh :=
    entries_norm_mono A (fun _ _ => M)
      (fun i j => by
        simpa only [abs_of_nonneg hM] using h i j)
  exact hh.trans_eq (entries_const_norm M hM)

/-- The source entry bound of four gives a Frobenius bound of 48 for every
rectangle with at most twelve rows and columns. -/
theorem bounded_rectangle {n m : Nat} (A : Matrix (Fin n) (Fin m) ℝ)
    (hn : n ≤ 12) (hm : m ≤ 12) (h : ∀ i j, |A i j| ≤ 4)
    : ‖entries A‖ ≤ 48 := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [entries_norm_sq]
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ =>
      (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)).mpr (h i j)
  simp only [sq_abs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hn' : (n : ℝ) ≤ 12 := by exact_mod_cast hn
  have hm' : (m : ℝ) ≤ 12 := by exact_mod_cast hm
  have hb := mul_le_mul hn' hm' (Nat.cast_nonneg m) (by norm_num : (0 : ℝ) ≤ 12)
  nlinarith only [hs, hb]

/-- The operator norm controls every real quadratic form. -/
theorem quadratic_norm_bound {n : Nat} (E : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    : |x ⬝ᵥ E.mulVec x| ≤ ‖E‖ * ∑ i, (x i) ^ 2 := by
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (E.mulVec x)
  have hh : |x ⬝ᵥ E.mulVec x| ≤ ‖v‖ * ‖w‖ := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, Real.norm_eq_abs,
      dotProduct_comm]
      using norm_inner_le_norm (𝕜 := ℝ) v w
  have he : ‖w‖ ≤ ‖E‖ * ‖v‖ := l2_opNorm_mulVec E v
  calc
    _ ≤ ‖v‖ * (‖E‖ * ‖v‖) := hh.trans (mul_le_mul_of_nonneg_left he (norm_nonneg v))
    _ = ‖E‖ * ‖v‖ ^ 2 := by ring
    _ = _ := by simp only [v, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]

/-- A Hermitian matrix lies above minus its operator norm times identity. -/
theorem add_identity_posSemidef {n : Nat} (E : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hE : E.IsHermitian) (he : ‖E‖ ≤ ε)
    : (E + ε • 1).PosSemidef := by
  have hε : 0 ≤ ε := (norm_nonneg E).trans he
  apply PosSemidef.of_dotProduct_mulVec_nonneg
    (hE.add ((PosSemidef.one (n := Fin n) (R := ℝ)).smul hε).isHermitian)
  intro x
  have hh := (quadratic_norm_bound E x).trans
    (mul_le_mul_of_nonneg_right he (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hlo := (abs_le.mp hh).1
  rw [star_trivial, add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul]
  have hself : x ⬝ᵥ x = ∑ i, (x i)^2 := by simp only [dotProduct, pow_two]
  rw [hself]
  change 0 ≤ x ⬝ᵥ E.mulVec x + ε * ∑ i, (x i)^2
  linarith only [hlo]

/-- Operator-norm perturbations preserve a matrix lower bound with no
extra dimension factor. -/
theorem perturbation_lower_bound_norm {n : Nat} (A E : Matrix (Fin n) (Fin n) ℝ)
    (σ ε : ℝ) (hA : (A - σ • 1).PosSemidef) (hE : E.IsHermitian) (he : ‖E‖ ≤ ε)
    : (A + E - (σ - ε) • 1).PosSemidef := by
  have hh := hA.add (add_identity_posSemidef E ε hE he)
  convert hh using 1
  module

/-- Frobenius energy is additive across a symmetric block matrix. Reindexing
the disjoint row/column sets into the native contiguous layout is exact. -/
theorem block_entries_norm_sq {n m : Nat} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ)
    : ‖entries ((fromBlocks A B B.transpose D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm)‖
        ^ 2
      = ‖entries A‖ ^ 2 + 2 * ‖entries B‖ ^ 2 + ‖entries D‖ ^ 2 := by
  rw [entries_norm_sq]
  rw [← (finSumFinEquiv (m := n) (n := m)).sum_comp]
  simp only [submatrix_apply, Equiv.symm_apply_apply]
  simp_rw [← (finSumFinEquiv (m := n) (n := m)).sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, transpose_apply,
    Finset.sum_add_distrib, entries_norm_sq]
  rw [Finset.sum_comm (f := fun i j => (B j i)^2)]
  ring

/-- The off-diagonal error is charged once with the square-root-of-two
Frobenius factor, rather than once for every row in the assembled matrix. -/
theorem block_error_norm {n m : Nat} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ)
    : ‖(fromBlocks A B B.transpose D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm‖
      ≤ ‖entries A‖ + (71 / 50 : ℝ) * ‖entries B‖ + ‖entries D‖ := by
  apply (norm_le_entries _).trans
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [block_entries_norm_sq]
  nlinarith only [norm_nonneg (entries A), norm_nonneg (entries B), norm_nonneg (entries D),
    mul_nonneg (norm_nonneg (entries A)) (norm_nonneg (entries B)),
    mul_nonneg (norm_nonneg (entries A)) (norm_nonneg (entries D)),
    mul_nonneg (norm_nonneg (entries B)) (norm_nonneg (entries D)), sq_nonneg ‖entries B‖]

end Flare.Analysis.MatrixError
