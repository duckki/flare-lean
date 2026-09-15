import Flare.Analysis.NumericalBounds
import Mathlib.LinearAlgebra.Matrix.Block

/-! Conditioning of a partially computed LDLᵀ factorization. The completed
columns define a nearby symmetric matrix. Its Schur complement controls the next
pivot without assuming that the native factorization succeeds. -/

namespace Flare.Analysis.Factorization
open Matrix

/-- The rectangular matrix consisting of the completed factor columns. -/
def prefixColumns {N k : Nat} (L : Matrix (Fin N) (Fin N) ℝ) (hk : k ≤ N)
    : Matrix (Fin N) (Fin k) ℝ :=
  fun i j => L i ⟨j.val, lt_of_lt_of_le j.isLt hk⟩

/-- Exact Gram contribution of the stored factor prefix. -/
def prefixGram {N k : Nat} (L : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℝ) (hk : k ≤ N)
    : Matrix (Fin N) (Fin N) ℝ :=
  prefixColumns L hk
  * diagonal (fun j : Fin k => d ⟨j.val, lt_of_lt_of_le j.isLt hk⟩)
  * (prefixColumns L hk).transpose

/-- Replace completed rows/columns by their factor reconstruction. The trailing
principal block retains the original matrix entries. -/
def completedMatrix {N k : Nat} (A L : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℝ) (hk : k ≤ N)
    : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    if i.val < k ∨ j.val < k then prefixGram L d hk i j else A i j

lemma prefixGram_apply {N k : Nat} (L : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℝ)
    (hk : k ≤ N) (i j : Fin N)
    : prefixGram L d hk i j
      = ∑ t : Fin k,
          L i ⟨t.val, lt_of_lt_of_le t.isLt hk⟩
          * d ⟨t.val, lt_of_lt_of_le t.isLt hk⟩
          * L j ⟨t.val, lt_of_lt_of_le t.isLt hk⟩ := by
  simp [prefixGram, prefixColumns, Matrix.mul_apply, Matrix.diagonal]

lemma prefixGram_posSemidef {N k : Nat} (L : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℝ)
    (hk : k ≤ N) (hd : ∀ j : Fin N, j.val < k → 0 ≤ d j)
    : (prefixGram L d hk).PosSemidef := by
  have hD : (diagonal (fun j : Fin k => d ⟨j.val, lt_of_lt_of_le j.isLt hk⟩)).PosSemidef :=
    PosSemidef.diagonal (fun j => hd _ j.isLt)
  simpa only [prefixGram, conjTranspose_eq_transpose_of_trivial]
    using hD.mul_mul_conjTranspose_same (prefixColumns L hk)

/-- Uniform entrywise backward error on the completed columns preserves a
conditioning margin for the nearby completed matrix. -/
theorem completedMatrix_lower_bound {N k : Nat} (A L : Matrix (Fin N) (Fin N) ℝ)
    (d : Fin N → ℝ) (hk : k ≤ N) (hN : N ≤ 12)
    (hA : (A - (3 / 16 : ℝ) • 1).PosSemidef)
    (hd : ∀ j : Fin N, j.val < k → 0 ≤ d j)
    (herr
      : ∀ i j : Fin N,
          i.val < k ∨ j.val < k → |prefixGram L d hk i j - A i j| ≤ (2 : ℝ)^(-13 : Int))
    : (completedMatrix A L d hk - (5 / 32 : ℝ) • 1).PosSemidef := by
  have hAsym := (NumericalBounds.posDef_of_lower_bound A (3 / 16) (by norm_num) hA).isHermitian
  have hGsym := (prefixGram_posSemidef L d hk hd).isHermitian
  have hMsym : (completedMatrix A L d hk).IsHermitian := by
    apply IsHermitian.ext
    intro i j
    have ha := congr_fun (congr_fun hAsym.eq i) j
    have hg := congr_fun (congr_fun hGsym.eq i) j
    simp only [conjTranspose_apply, star_trivial] at ha hg
    simp only [completedMatrix, star_trivial]
    by_cases hij : i.val < k ∨ j.val < k
    · rw [if_pos hij, if_pos (Or.comm.mp hij)]
      exact hg
    · rw [if_neg hij, if_neg (fun h => hij (Or.comm.mp h))]
      exact ha
  have hE : ∀ i j : Fin N, |(completedMatrix A L d hk - A) i j| ≤ (2 : ℝ)^(-13 : Int) := by
    intro i j
    simp only [Matrix.sub_apply, completedMatrix]
    split
    · exact herr i j ‹_›
    · simp
  have h := NumericalBounds.perturbation_lower_bound A (completedMatrix A L d hk - A)
    (3 / 16) ((2 : ℝ)^(-13 : Int)) (by positivity) hA (hMsym.sub hAsym) hE
  have hN' : (N : ℝ) ≤ 12 := by exact_mod_cast hN
  have hm : 0 ≤ (3 / 16 : ℝ) - N * (2 : ℝ)^(-13 : Int) - 5 / 32 := by
    norm_num only [_root_.zpow_neg, zpow_ofNat, inv_pow, pow_succ, pow_zero]
    linarith
  have hpad := (PosSemidef.one (n := Fin N) (R := ℝ)).smul hm
  convert h.add hpad using 1
  simp only [sub_smul]
  abel

/-- Index into the trailing principal block after k completed columns. -/
def trailingIndex {N k : Nat} (hk : k ≤ N) (i : Fin (N - k)) : Fin N :=
  ⟨k + i.val, by omega⟩

/-- The next Schur block retains a positive margin when the completed factor
prefix has bounded backward error. Zero upper entries and unit diagonal are
structural facts about LDLᵀ storage; positive pivots are prefix invariants. -/
theorem prefix_schur_lower_bound {N k : Nat} (A L : Matrix (Fin N) (Fin N) ℝ)
    (d : Fin N → ℝ) (hk : k ≤ N) (hN : N ≤ 12)
    (hA : (A - (3 / 16 : ℝ) • 1).PosSemidef)
    (hd : ∀ j : Fin N, j.val < k → 0 < d j)
    (hunit : ∀ j : Fin N, j.val < k → L j j = 1)
    (htri : ∀ i j : Fin N, j.val < k → i.val < j.val → L i j = 0)
    (herr
      : ∀ i j : Fin N,
          i.val < k ∨ j.val < k → |prefixGram L d hk i j - A i j| ≤ (2 : ℝ)^(-13 : Int))
    : ((A - prefixGram L d hk).submatrix (trailingIndex hk) (trailingIndex hk)
        - (5 / 32 : ℝ) • 1).PosSemidef := by
  let e : Fin k ⊕ Fin (N - k) ≃ Fin N := finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hk))
  let P : Matrix (Fin k) (Fin k) ℝ := fun i j => L (e (.inl i)) (e (.inl j))
  let C : Matrix (Fin (N - k)) (Fin k) ℝ := fun i j => L (e (.inr i)) (e (.inl j))
  let D : Matrix (Fin k) (Fin k) ℝ := diagonal (fun j => d (e (.inl j)))
  let B : Matrix (Fin (N - k)) (Fin (N - k)) ℝ := A.submatrix (trailingIndex hk) (trailingIndex hk)
  have hleft (i : Fin k) : e (.inl i) = ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ := by rfl
  have hright (i : Fin (N - k)) : e (.inr i) = trailingIndex hk i := by rfl
  have hleft_lt (i : Fin k) : (e (.inl i)).val < k := i.isLt
  have hright_nlt (i : Fin (N - k)) : ¬(e (.inr i)).val < k := by
    change ¬k + i.val < k
    omega
  have hPdiag (i : Fin k) : P i i = 1 := hunit _ (hleft_lt i)
  have hP : IsUnit P := by
    apply P.isUnit_iff_isUnit_det.mpr
    have hpt : P.IsLowerTriangular := by
      intro i j hij
      exact htri _ _ (hleft_lt j) hij
    have hpdet : P.det = 1 := by rw [det_of_isLowerTriangular P hpt]; simp [hPdiag]
    rw [hpdet]
    exact isUnit_one
  have hD : D.PosDef := PosDef.diagonal (fun j => hd _ (hleft_lt j))
  have hblock : (completedMatrix A L d hk).submatrix e e =
      fromBlocks (P * D * P.transpose) (P * D * C.transpose) (C * D * P.transpose) B := by
    ext (i | i) (j | j)
    · change (if (e (.inl i)).val < k ∨ (e (.inl j)).val < k then _ else _) = _
      rw [if_pos (Or.inl (hleft_lt i))]
      rfl
    · change (if (e (.inl i)).val < k ∨ (e (.inr j)).val < k then _ else _) = _
      rw [if_pos (Or.inl (hleft_lt i))]
      rfl
    · change (if (e (.inr i)).val < k ∨ (e (.inl j)).val < k then _ else _) = _
      rw [if_pos (Or.inr (hleft_lt j))]
      rfl
    · change (if (e (.inr i)).val < k ∨ (e (.inr j)).val < k then _ else _) = _
      rw [if_neg (not_or_intro (hright_nlt i) (hright_nlt j))]
      rfl
  have hM := (completedMatrix_lower_bound A L d hk hN hA (fun j hj => (hd j hj).le) herr).submatrix
    e
  have hM' : (fromBlocks (P * D * P.transpose) (P * D * C.transpose) (C * D * P.transpose) B -
      (5 / 32 : ℝ) • 1).PosSemidef := by
    simpa only [submatrix_sub, submatrix_smul, Pi.sub_apply, Pi.smul_apply,
      submatrix_one_equiv, hblock]
      using hM
  have h := NumericalBounds.factor_schur_lower_bound P D C B (5 / 32) (by norm_num) hP hD hM'
  convert h using 1
  congr 1

/-- Scalar bounds needed by the next native column follow from the trailing
matrix lower bound and the original diagonal bounds. -/
theorem schur_column_bounds {N k : Nat} (A L : Matrix (Fin N) (Fin N) ℝ)
    (d : Fin N → ℝ) (hk : k ≤ N)
    (hd : ∀ j : Fin N, j.val < k → 0 ≤ d j)
    (hdiag : ∀ i : Fin N, A i i ≤ 1024)
    (hS
      : ((A - prefixGram L d hk).submatrix (trailingIndex hk) (trailingIndex hk)
          - (5 / 32 : ℝ) • 1).PosSemidef) (i j : Fin N) (hi : k ≤ i.val) (hj : k ≤ j.val)
    : (5 / 32 : ℝ) ≤ (A - prefixGram L d hk) j j
      ∧ ((A - prefixGram L d hk) i j)^2 ≤ 1024 * (A - prefixGram L d hk) j j := by
  let ii : Fin (N - k) := ⟨i.val - k, by omega⟩
  let jj : Fin (N - k) := ⟨j.val - k, by omega⟩
  have hii : trailingIndex hk ii = i := by apply Fin.ext; dsimp [trailingIndex, ii]; omega
  have hjj : trailingIndex hk jj = j := by apply Fin.ext; dsimp [trailingIndex, jj]; omega
  have hlo := hS.diag_nonneg (i := jj)
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    mul_one, submatrix_apply, hjj] at hlo
  have hpos : ((A - prefixGram L d hk).submatrix (trailingIndex hk) (trailingIndex hk)).PosSemidef
    := by
    convert hS.add ((PosSemidef.one (n := Fin (N - k)) (R := ℝ)).smul (by norm_num : (0 : ℝ) ≤ 5 /
      32)) using 1
    abel
  have hquad := NumericalBounds.entry_sq_le_diagonal_product _ hpos ii jj
  simp only [submatrix_apply, hii, hjj] at hquad
  have hupper : (A - prefixGram L d hk) i i ≤ 1024 :=
    (sub_le_self _ ((prefixGram_posSemidef L d hk hd).diag_nonneg (i := i))).trans (hdiag i)
  change 0 ≤ (A - prefixGram L d hk) j j - 5 / 32 at hlo
  exact ⟨by linarith, hquad.trans (mul_le_mul_of_nonneg_right hupper (by linarith))⟩

/-- Nonnegative LDLᵀ diagonal factors control the absolute mass of every
reconstruction sum by its two diagonal sums. This avoids estimating each
individual factor product by a worst-case entry bound. -/
theorem gram_mass_bound {n : Nat} (L : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hd : ∀ k, 0 ≤ d k)
    (hdiag : ∀ i, (L * diagonal d * L.transpose) i i ≤ M) (i j : Fin n)
    : (∑ k, |L i k * d k * L j k|) ≤ M := by
  have henergy (i : Fin n) : (∑ k, (L i k * Real.sqrt (d k))^2) =
      (L * diagonal d * L.transpose) i i := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, transpose_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow, Real.sq_sqrt (hd k)]
    ring
  have hnonneg (i : Fin n) : 0 ≤ (L * diagonal d * L.transpose) i i := by
    rw [← henergy]
    exact Finset.sum_nonneg fun k _ => sq_nonneg _
  have hterm (k : Fin n) : |L i k * d k * L j k| =
      |L i k * Real.sqrt (d k)| * |L j k * Real.sqrt (d k)| := by
    rw [← abs_mul]
    congr 1
    calc
      _ = L i k * L j k * (Real.sqrt (d k))^2 := by rw [Real.sq_sqrt (hd k)]; ring
      _ = _ := by ring
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun k => |L i k * Real.sqrt (d k)|) (fun k => |L j k * Real.sqrt (d k)|)
  simp only [← hterm, sq_abs, henergy] at hs
  apply (sq_le_sq₀ (Finset.sum_nonneg fun k _ => abs_nonneg _) hM).mp
  exact hs.trans ((mul_le_mul (hdiag i) (hdiag j) (hnonneg j) hM).trans_eq (by ring))

/-- Factorization and substitution residuals compose into the residual of
the original linear system, with explicit componentwise propagation. -/
theorem componentwise_solve_residual {n columns : Nat}
    (A L D : _root_.Matrix (Fin n) (Fin n) ℝ)
    (B Y X : _root_.Matrix (Fin n) (Fin columns) ℝ)
    (ε : ℝ) (F E : Fin n → Fin columns → ℝ)
    (hfactor : ∀ i k, |(L * D * L.transpose) i k - A i k| ≤ ε)
    (hF : ∀ i j, |(L * Y - B) i j| ≤ F i j)
    (hE : ∀ i j, |(D * L.transpose * X - Y) i j| ≤ E i j)
    : ∀ i j, |(A * X - B) i j| ≤ F i j + ∑ k, |L i k| * E k j + ε * ∑ k, |X k j| := by
  have he : A * X - B =
      (L * Y - B) + L * (D * L.transpose * X - Y) + (A - L * D * L.transpose) * X := by
    simp only [_root_.Matrix.mul_sub, _root_.Matrix.sub_mul, _root_.Matrix.mul_assoc]
    abel
  intro i j
  have hprod : |(L * (D * L.transpose * X - Y)) i j| ≤ ∑ k, |L i k| * E k j := by
    rw [_root_.Matrix.mul_apply]
    calc
      _ ≤ ∑ k, |L i k * (D * L.transpose * X - Y) k j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ :=
        Finset.sum_le_sum
          fun k _ => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hE k j) (abs_nonneg _)
  have hpert : |((A - L * D * L.transpose) * X) i j| ≤ ε * ∑ k, |X k j| := by
    rw [_root_.Matrix.mul_apply, Finset.mul_sum]
    calc
      _ ≤ ∑ k, |(A - L * D * L.transpose) i k * X k j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ :=
        Finset.sum_le_sum
          fun k _ => by
            rw [abs_mul, _root_.Matrix.sub_apply, abs_sub_comm]
            exact mul_le_mul_of_nonneg_right (hfactor i k) (abs_nonneg _)
  rw [he]
  change |(L * Y - B) i j + (L * (D * L.transpose * X - Y)) i j +
    ((A - L * D * L.transpose) * X) i j| ≤ _
  exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    (add_le_add (add_le_add (hF i j) hprod) hpert)

private lemma gram_transport_mass_bound {n columns : Nat}
    (L : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (X : Matrix (Fin n) (Fin columns) ℝ) (M : ℝ)
    (hd : ∀ k, 0 ≤ d k) (hmass : ∀ i t, (∑ k, |L i k * d k * L t k|) ≤ M)
    (i : Fin n) (j : Fin columns)
    : (∑ k, |L i k| * d k * ∑ t, |L t k * X t j|) ≤ M * ∑ t, |X t j| := by
  have hswap : (∑ k, |L i k| * d k * ∑ t, |L t k * X t j|) =
      ∑ t, (∑ k, |L i k * d k * L t k|) * |X t j| := by
    simp only [Finset.mul_sum, Finset.sum_mul, abs_mul, abs_of_nonneg (hd _)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hgram : (∑ k, |L i k| * d k * ∑ t, |L t k * X t j|) ≤ M * ∑ t, |X t j| := by
    rw [hswap, Finset.mul_sum]
    exact Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_right (hmass i t) (abs_nonneg _)
  exact hgram

/-- A backward-substitution residual bounds the forward intermediate after
weighting by the absolute lower factor. Reordering the sums exposes the Gram
mass, avoiding a separate large norm bound for each triangular factor. -/
theorem weighted_substitution_mass {n columns : Nat}
    (L : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (Y X : Matrix (Fin n) (Fin columns) ℝ) (β η M P : ℝ)
    (hβ : 0 ≤ β) (hη : 0 ≤ η) (hd : ∀ k, 0 ≤ d k)
    (hmass : ∀ i t, (∑ k, |L i k * d k * L t k|) ≤ M)
    (hp : ∀ i, (∑ k, |L i k| * d k) ≤ P)
    (hback
      : ∀ k j,
          |(diagonal d * L.transpose * X - Y) k j|
          ≤ β * (|Y k j| + d k * (∑ t, |L t k * X t j|) + d k * η))
    : ∀ i j, (1 - β) * (∑ k, |L i k * Y k j|) ≤ (1 + β) * M * (∑ t, |X t j|) + β * P * η := by
  have hrow (k : Fin n) (j : Fin columns) :
      (1 - β) * |Y k j| ≤ (1 + β) * d k * (∑ t, |L t k * X t j|) + β * d k * η := by
    have hprod : |(diagonal d * L.transpose * X) k j| ≤ d k * ∑ t, |L t k * X t j| := by
      rw [Matrix.mul_assoc, Matrix.diagonal_mul, abs_mul, abs_of_nonneg (hd k), Matrix.mul_apply]
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (hd k)
    have ht := abs_sub_le (Y k j) ((diagonal d * L.transpose * X) k j) 0
    simp only [sub_zero, abs_sub_comm (Y k j)] at ht
    have hb := hback k j
    change |(diagonal d * L.transpose * X) k j - Y k j| ≤ _ at hb
    nlinarith only [ht, hprod, hb]
  intro i j
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
    mul_le_mul_of_nonneg_left (hrow k j) (abs_nonneg (L i k)))
  have hgram := gram_transport_mass_bound L d X M hd hmass i j
  have hrearrange : (∑ k, |L i k| * ((1 + β) * d k * (∑ t, |L t k * X t j|) + β * d k * η)) =
      (1 + β) * (∑ k, |L i k| * d k * ∑ t, |L t k * X t j|) +
        β * (∑ k, |L i k| * d k) * η := by
    calc
      _ = ∑ k, ((1 + β) * (|L i k| * d k * ∑ t, |L t k * X t j|) + β * (|L i k| * d k) * η) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
  have hleft : (∑ k, |L i k| * ((1 - β) * |Y k j|)) =
      (1 - β) * ∑ k, |L i k * Y k j| := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [abs_mul]; ring
  rw [hleft, hrearrange] at hsum
  have hb := add_le_add
    (mul_le_mul_of_nonneg_left hgram (by linarith : 0 ≤ 1 + β))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hp i) hβ) hη)
  simpa only [mul_assoc] using hsum.trans hb

/-- Eliminate the forward intermediate from the composed solve residual.
The remaining bound depends on the input and final solution, the input-scaled
Gram mass, and rounding coefficients. This is the absorption step needed for
a uniform conditioned-solve estimate. -/
theorem solve_residual_mass {n columns : Nat}
    (A L : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (B Y X : Matrix (Fin n) (Fin columns) ℝ) (α β η M P ε : ℝ)
    (hα : 0 ≤ α) (hα' : α ≤ 1 / 4) (hβ : 0 ≤ β) (hβ' : β ≤ 1 / 4000)
    (hη : 0 ≤ η) (hM : 0 ≤ M) (hP : 0 ≤ P) (hd : ∀ k, 0 ≤ d k)
    (hmass : ∀ i t, (∑ k, |L i k * d k * L t k|) ≤ M)
    (hp : ∀ i, (∑ k, |L i k| * d k) ≤ P)
    (hfactor : ∀ i k, |(L * diagonal d * L.transpose) i k - A i k| ≤ ε)
    (hforward : ∀ i j, |(L * Y - B) i j| ≤ α * (|B i j| + ∑ k, |L i k * Y k j| + η))
    (hback
      : ∀ k j,
          |(diagonal d * L.transpose * X - Y) k j|
          ≤ β * (|Y k j| + d k * (∑ t, |L t k * X t j|) + d k * η))
    : ∀ i j,
        |(A * X - B) i j|
        ≤ α * |B i j|
          + (((1001 / 1000 : ℝ) * α + (2001 / 1000 : ℝ) * β) * M + ε) * (∑ t, |X t j|)
          + (α + 2 * β * P) * η := by
  have hres := componentwise_solve_residual A L (diagonal d) B Y X ε
    (fun i j => α * (|B i j| + ∑ k, |L i k * Y k j| + η))
    (fun k j => β * (|Y k j| + d k * (∑ t, |L t k * X t j|) + d k * η))
    hfactor hforward hback
  have hy := weighted_substitution_mass L d Y X β η M P hβ hη hd hmass hp hback
  intro i j
  let Z := ∑ k, |L i k * Y k j|
  let S := ∑ t, |X t j|
  let W := M * S
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hW : 0 ≤ W := mul_nonneg hM hS
  have hPη : 0 ≤ P * η := mul_nonneg hP hη
  have hZ : Z ≤ (1001 / 1000 : ℝ) * W + 2 * β * P * η := by
    have hh := hy i j
    rw [mul_assoc (1 + β) M] at hh
    change (1 - β) * Z ≤ (1 + β) * W + β * P * η at hh
    have hc : 1 + β ≤ (1 - β) * (1001 / 1000 : ℝ) := by linarith
    have hc' : β ≤ (1 - β) * (2 * β) := by nlinarith
    have hh' := add_le_add (mul_le_mul_of_nonneg_right hc hW)
      (mul_le_mul_of_nonneg_right hc' hPη)
    have hmul : (1 - β) * Z ≤ (1 - β) * ((1001 / 1000 : ℝ) * W + 2 * β * P * η) := by
      calc
        _ ≤ (1 + β) * W + β * (P * η) := by simpa only [mul_assoc] using hh
        _ ≤ _ := hh'.trans_eq (by ring)
    exact (mul_le_mul_iff_right₀ (by linarith : 0 < 1 - β)).mp hmul
  have hgram := gram_transport_mass_bound L d X M hd hmass i j
  have hbackmass : (∑ k, |L i k| * (β * (|Y k j| + d k * (∑ t, |L t k * X t j|) + d k * η))) ≤
      β * (Z + W + P * η) := by
    calc
      _ = β
          * ((∑ k, |L i k * Y k j|)
              + (∑ k, |L i k| * d k * ∑ t, |L t k * X t j|)
              + (∑ k, |L i k| * d k) * η) := by
        calc
          _ = ∑ k,
                (β * |L i k * Y k j|
                  + β * (|L i k| * d k * ∑ t, |L t k * X t j|)
                  + β * (|L i k| * d k) * η) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [abs_mul]
            ring
          _ = _ := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
            ring
      _ ≤ _ :=
        mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add le_rfl hgram) (mul_le_mul_of_nonneg_right (hp i) hη)) hβ
  have hsmall : 2 * (α + β) + 1 ≤ 2 := by linarith
  calc
    _ ≤ α * (|B i j| + Z + η) + β * (Z + W + P * η) + ε * S :=
      (hres i j).trans (add_le_add (add_le_add le_rfl hbackmass) le_rfl)
    _ = α * |B i j| + (α + β) * Z + β * W + ε * S + (α + β * P) * η := by ring
    _ ≤ α * |B i j|
        + (α + β) * ((1001 / 1000 : ℝ) * W + 2 * β * P * η)
        + β * W
        + ε * S
        + (α + β * P) * η := by
      gcongr
    _ = α * |B i j|
        + (((1001 / 1000 : ℝ) * α + (2001 / 1000 : ℝ) * β) * M + ε) * S
        + α * η
        + (2 * (α + β) + 1) * (β * P * η) := by
      dsimp [W]; ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hsmall (mul_nonneg (mul_nonneg hβ hP) hη)
      nlinarith only [hh]

end Flare.Analysis.Factorization
