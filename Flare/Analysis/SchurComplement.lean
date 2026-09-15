import Flare.Analysis.MoorePenrose
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! Schur-complement and block-matrix inequalities, including singular blocks. -/

namespace Flare.Analysis.SchurComplement
open Matrix Flare.Analysis

lemma kernel_offDiagonal {n m : Nat}
    {A : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin m) ℝ}
    {D : Matrix (Fin m) (Fin m) ℝ}
    (h : (fromBlocks A B B.transpose D).PosSemidef)
    (v : Fin m → ℝ) (hv : D *ᵥ v = 0)
    : B *ᵥ v = 0 := by
  have hmul : fromBlocks A B B.transpose D *ᵥ Sum.elim 0 v = Sum.elim (B *ᵥ v) 0 := by
    rw [fromBlocks_mulVec]
    change Sum.elim (A *ᵥ 0 + B *ᵥ v) (B.transpose *ᵥ 0 + D *ᵥ v) = _
    simp only [mulVec_zero, zero_add, hv]
  have hm := (h.dotProduct_mulVec_zero_iff (Sum.elim 0 v)).mp (by
    rw [hmul, star_trivial, sumElim_dotProduct_sumElim]
    simp)
  rw [hmul] at hm
  exact congrArg (fun x => x ∘ Sum.inl) hm

/-- An identity off-diagonal block forces the lower diagonal block to be PD. -/
lemma identity_posDef {n : Nat} {A D : Matrix (Fin n) (Fin n) ℝ}
    (h : (fromBlocks A 1 1 D).PosSemidef)
    : D.PosDef := by
  have hD : D.PosSemidef := h.submatrix Sum.inr
  apply PosDef.of_dotProduct_mulVec_pos hD.isHermitian
  intro v hv
  refine lt_of_le_of_ne (hD.dotProduct_mulVec_nonneg v) ?_
  intro he
  have hdv := (hD.dotProduct_mulVec_zero_iff v).mp he.symm
  have hb := kernel_offDiagonal (A := A) (B := 1) (by simpa only [transpose_one] using h) v hdv
  exact hv (by simpa using hb)

-- Preserve the extracted DecidableEq parameter until an API change is reviewed separately.
set_option linter.extra.unusedDecidableInType false in
/-- Congruence gives a Schur inequality for any symmetric reflexive inverse.
The upper index type permits nested blocks in the reverse-feasibility proof. -/
lemma schur_reflexive {ι : Type*} [Fintype ι] [DecidableEq ι] {m : Nat}
    {A : Matrix ι ι ℝ} {B : Matrix ι (Fin m) ℝ}
    {D Z : Matrix (Fin m) (Fin m) ℝ}
    (h : (fromBlocks A B B.transpose D).PosSemidef)
    (hzt : Z.transpose = Z) (hz : Z * D * Z = Z)
    : (A - B * Z * B.transpose).PosSemidef := by
  have hZDZ : Z * (D * (Z * B.transpose)) = Z * B.transpose := by
    simpa only [Matrix.mul_assoc] using congrArg (· * B.transpose) hz
  have hc := h.mul_mul_conjTranspose_same (fromCols (1 : Matrix ι ι ℝ) (-B * Z))
  convert hc using 1
  simp only [conjTranspose_eq_transpose_of_trivial, transpose_fromCols, transpose_mul,
    transpose_neg, transpose_one, hzt, fromCols_mul_fromBlocks, fromCols_mul_fromRows,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.add_mul, Matrix.mul_assoc, hZDZ]
  abel

/-- The Schur inequality remains valid for a singular lower block. -/
lemma generalized_schur {n m : Nat}
    {A : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin m) ℝ}
    {D Z : Matrix (Fin m) (Fin m) ℝ}
    (h : (fromBlocks A B B.transpose D).PosSemidef) (hz : MoorePenrose D Z)
    : (A - B * Z * B.transpose).PosSemidef := by
  have hD : D.PosSemidef := h.submatrix Sum.inr
  have hzt : Z.transpose = Z := by
    simpa only [conjTranspose_eq_transpose_of_trivial]
      using (MoorePenrose.posSemidef hD hz).isHermitian.eq
  exact schur_reflexive h hzt hz.2.1

lemma lower_block {n m : Nat} {D : Matrix (Fin m) (Fin m) ℝ} (hD : D.PosSemidef)
    : (fromBlocks (0 : Matrix (Fin n) (Fin n) ℝ) 0 0 D).PosSemidef := by
  have h := hD.mul_mul_conjTranspose_same
    (fromRows (0 : Matrix (Fin n) (Fin m) ℝ) (1 : Matrix (Fin m) (Fin m) ℝ))
  simp only [conjTranspose_eq_transpose_of_trivial, transpose_fromRows, transpose_zero,
    transpose_one] at h
  rw [fromRows_mul, fromRows_mul_fromCols] at h
  simpa only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one] using h

lemma increase_lower {n m : Nat}
    {A : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin m) ℝ}
    {D E : Matrix (Fin m) (Fin m) ℝ}
    (h : (fromBlocks A B B.transpose D).PosSemidef) (hE : (E - D).PosSemidef)
    : (fromBlocks A B B.transpose E).PosSemidef := by
  convert h.add (lower_block (n := n) hE) using 1
  ext (i | i) (j | j) <;> simp [fromBlocks]

/-- A PSD block cannot couple to a null direction of its lower block. -/
lemma offDiagonal_projection {n m : Nat}
    {A : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin m) ℝ}
    {D Z : Matrix (Fin m) (Fin m) ℝ}
    (h : (fromBlocks A B B.transpose D).PosSemidef) (hz : MoorePenrose D Z)
    : B * Z * D = B := by
  apply Matrix.ext
  intro i j
  let v : Fin m → ℝ := fun k => (1 - Z * D) k j
  have hv : D *ᵥ v = 0 := by
    change (fun k => (D * (1 - Z * D)) k j) = 0
    simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hz.1, sub_self]
    rfl
  have hb := kernel_offDiagonal h v hv
  have he : (B - B * Z * D) i j = 0 := by
    have he := congrFun hb i
    change (B * ((1 : Matrix (Fin m) (Fin m) ℝ) - Z * D)) i j = 0 at he
    simpa only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc] using he
  exact sub_eq_zero.mp he |>.symm

/-- The least upper block compatible with a given lower block and coupling. -/
lemma pseudoinverse_block {n m : Nat}
    {A : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin m) ℝ}
    {D Z : Matrix (Fin m) (Fin m) ℝ}
    (h : (fromBlocks A B B.transpose D).PosSemidef) (hz : MoorePenrose D Z)
    : (fromBlocks (B * Z * B.transpose) B B.transpose D).PosSemidef := by
  have hD : D.PosSemidef := h.submatrix Sum.inr
  have hzt : Z.transpose = Z := by
    simpa only [conjTranspose_eq_transpose_of_trivial]
      using (MoorePenrose.posSemidef hD hz).isHermitian.eq
  have hbt := offDiagonal_projection h hz
  have hdt : D.transpose = D := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hD.isHermitian.eq
  have htb : D * Z * B.transpose = B.transpose := by
    have he := congrArg Matrix.transpose hbt
    simpa only [transpose_mul, hzt, hdt, Matrix.mul_assoc] using he
  have hc := hD.mul_mul_conjTranspose_same
    (fromRows (B * Z) (1 : Matrix (Fin m) (Fin m) ℝ))
  simp only [conjTranspose_eq_transpose_of_trivial, transpose_fromRows, transpose_mul,
    transpose_one, hzt] at hc
  rw [fromRows_mul, fromRows_mul_fromCols] at hc
  simpa only [Matrix.one_mul, Matrix.mul_one, hbt, ← Matrix.mul_assoc, htb] using hc

/-- Comparing a singular inverse with an invertible enlargement only on the
directions that the off-diagonal block can observe. -/
lemma inverse_comparison {n m : Nat}
    {A : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin m) ℝ}
    {D Z E : Matrix (Fin m) (Fin m) ℝ}
    (h : (fromBlocks A B B.transpose D).PosSemidef) (hz : MoorePenrose D Z)
    (hE : E.PosDef) (hle : (E - D).PosSemidef)
    : (B * Z * B.transpose - B * E⁻¹ * B.transpose).PosSemidef := by
  let := hE.isUnit.invertible
  have hs := hE.fromBlocks₂₂ (B * Z * B.transpose) B
  simp only [conjTranspose_eq_transpose_of_trivial] at hs
  exact hs.mp (increase_lower (pseudoinverse_block h hz) hle)

lemma covariance_contraction {n : Nat} {X R : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (hR : R.PosDef) (hle : (R⁻¹ - X).PosSemidef)
    : (X - X * R * X).PosSemidef := by
  have ht : X.transpose = X := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hX.isHermitian.eq
  have hb : (fromBlocks X X X.transpose X).PosSemidef := by
    have hc := hX.mul_mul_conjTranspose_same
      (fromRows (1 : Matrix (Fin n) (Fin n) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ))
    simp only [conjTranspose_eq_transpose_of_trivial, transpose_fromRows, transpose_one] at hc
    rw [fromRows_mul, fromRows_mul_fromCols] at hc
    simpa only [Matrix.one_mul, Matrix.mul_one, ht] using hc
  let := hR.isUnit.invertible
  let := hR.inv.isUnit.invertible
  have hs := hR.inv.fromBlocks₂₂ X X
  simpa only [conjTranspose_eq_transpose_of_trivial, inv_inv_of_invertible, ht]
    using hs.mp (by simpa only [conjTranspose_eq_transpose_of_trivial] using increase_lower hb hle)

end Flare.Analysis.SchurComplement
