import Flare.Matrix.Multiplication

/-! Finite execution and roundoff for the native matrix-formation helpers.
Lower-triangle copying is exact storage manipulation; its error is measured
against an explicitly symmetric real target. -/

namespace Flare.Matrix.MatrixFormation
open Flare.Matrix.Value Flare.Binary64.Value Flare.Matrix.Operations
open Flare.Binary64.Arithmetic
open scoped Matrix.Norms.L2Operator

/-- The two operations in `combine`, with an absolute-term mass allowance. -/
lemma combine_step (a b s : Float) (M : ℝ)
    (ha : a.isFinite = true) (hb : b.isFinite = true) (hs : s.isFinite = true)
    (hM : M ≤ (2 : ℝ) ^ (990 : Int)) (hη : (2 : ℝ) ^ (-1022 : Int) ≤ M)
    (hmass : |value a| + |value s * value b| ≤ M)
    : (s * b).isFinite = true
      ∧ (a + s * b).isFinite = true
      ∧ |value (a + s * b) - (value a + value s * value b)| ≤ (2 : ℝ) ^ (-48 : Int) * M := by
  have hM0 : 0 ≤ M := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hmass
  have hlim : 3 * M ≤ (2 : ℝ)^(1000 : Int) := by
    calc
      _ ≤ 4 * M := by linarith only [hM0]
      _ ≤ 4 * (2 : ℝ) ^ (990 : Int) := mul_le_mul_of_nonneg_left hM (by norm_num)
      _ = (2 : ℝ) ^ (992 : Int) := by
        rw [show (992 : Int) = 990 + 2 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num only [show (2 : ℝ)^(2 : Int) = 4 by norm_num]; ring
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hab : |value a| ≤ M := (le_add_of_nonneg_right (abs_nonneg _)).trans hmass
  have hprod : |value s * value b| ≤ M := (le_add_of_nonneg_left (abs_nonneg _)).trans hmass
  have hm := mul_error_relative s b hs hb
    (hprod.trans ((by linarith only [hM0] : M ≤ 3 * M).trans hlim))
  have hterm : |value (s * b)| ≤ 2 * M := by
    have hh := abs_sub_le (value (s * b)) (value s * value b) 0
    simp only [sub_zero] at hh
    have he := hm.2
    norm_num only [show (2 : ℝ)^(-51 : Int) = 1 / 2251799813685248 by norm_num] at he
    linarith
  have hh := add_error_relative a (s * b) ha hm.1
    ((abs_add_le _ _).trans ((by linarith only [hab, hterm] :
      |value a| + |value (s * b)| ≤ 3 * M).trans hlim))
  refine ⟨hm.1, hh.1, ?_⟩
  have heq : value (a + s * b) - (value a + value s * value b) =
      (value (a + s * b) - (value a + value (s * b))) +
      (value (s * b) - value s * value b) := by ring
  rw [heq]
  have htri := abs_add_le (value (a + s * b) - (value a + value (s * b)))
    (value (s * b) - value s * value b)
  have hmerr := hm.2
  have haerr := hh.2
  have hsum := abs_add_le (value a) (value (s * b))
  norm_num only [show (2 : ℝ)^(-51 : Int) = 1 / 2251799813685248 by norm_num,
    show (2 : ℝ)^(-48 : Int) = 1 / 281474976710656 by norm_num] at hmerr haerr ⊢
  linarith

/-- Actual checked addition/subtraction succeeds, with per-entry error relative
to its stored operands. The sign and both inputs may be rounded upstream values. -/
theorem combine_accuracy (a b : Array Float) (s : Float) (M : ℝ)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true) (hs : s.isFinite = true)
    (hM : M ≤ (2 : ℝ) ^ (990 : Int)) (hη : (2 : ℝ) ^ (-1022 : Int) ≤ M)
    (hmass : ∀ i, i < a.size → |value (a.getD i 0.0)| + |value s * value (b.getD i 0.0)| ≤ M)
    : ∃ r,
        combine a b s = .ok r
        ∧ r.size = a.size
        ∧ r.all Float.isFinite = true
        ∧ ∀ i,
            i < a.size
            → |value (r.getD i 0.0) - (value (a.getD i 0.0) + value s * value (b.getD i 0.0))|
              ≤ (2 : ℝ) ^ (-48 : Int) * M := by
  have hh (i : Nat) (hi : i < a.size) := combine_step (a.getD i 0.0) (b.getD i 0.0) s M
    (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ hb)
    hs hM hη (hmass i hi)
  have hmap : combine a b s = .ok ((Array.range a.size).map
      (fun i => a.getD i 0.0 + s * b.getD i 0.0)) := by
    apply Flare.Matrix.Multiplication.mapM_eq_ok_map
    intro i hi
    have hi' : i < a.size := by simpa using hi
    simp only [finite, (hh i hi').1, (hh i hi').2.1, ↓reduceIte, bind, Except.bind]
  refine ⟨_, hmap, by simp, ?_, ?_⟩
  · rw [Array.all_eq_true]
    intro i hi
    have hi' : i < a.size := by simpa using hi
    simpa only [Array.getElem_map, Array.getElem_range] using (hh i hi').2.1
  · intro i hi
    simpa [hi] using (hh i hi).2.2

/-- Matrix norms supply the mass bound for the actual native sum. -/
theorem combine_norm_accuracy (n : Nat) (a b : Array Float) (s : Float)
    (has : a.size = n * n) (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hs : s.isFinite = true)
    (hbound
      : ‖matrix n n a‖ + |value s| * ‖matrix n n b‖ + (2 : ℝ) ^ (-1022 : Int)
        ≤ (2 : ℝ) ^ (990 : Int))
    : ∃ r,
        combine a b s = .ok r
        ∧ r.size = n * n
        ∧ r.all Float.isFinite = true
        ∧ ∀ i j,
            |matrix n n r i j - (matrix n n a + value s • matrix n n b) i j|
            ≤ (2 : ℝ) ^ (-48 : Int)
              * (‖matrix n n a‖ + |value s| * ‖matrix n n b‖ + (2 : ℝ) ^ (-1022 : Int)) := by
  obtain ⟨r, hr, hrs, hrf, he⟩ := combine_accuracy a b s _ ha hb hs hbound
    (le_add_of_nonneg_left (by positivity)) (by
      intro k hk
      have hn : 0 < n := by rw [has] at hk; nlinarith only [hk]
      let i : Fin n := ⟨k / n, (Nat.div_lt_iff_lt_mul hn).mpr (has ▸ hk)⟩
      let j : Fin n := ⟨k % n, Nat.mod_lt _ hn⟩
      have hidx : i.val * n + j.val = k := Nat.div_add_mod' k n
      have hab := Flare.Analysis.SpectralPerturbation.entry_le_norm (matrix n n a) i j
      have hbb := Flare.Analysis.SpectralPerturbation.entry_le_norm (matrix n n b) i j
      change |value (a.getD (i.val * n + j.val) 0.0)| ≤ _ at hab
      change |value (b.getD (i.val * n + j.val) 0.0)| ≤ _ at hbb
      rw [hidx] at hab hbb
      rw [abs_mul]
      exact (add_le_add hab (mul_le_mul_of_nonneg_left hbb (abs_nonneg _))).trans
        (le_add_of_nonneg_right (by positivity)))
  refine ⟨r, hr, hrs.trans has, hrf, ?_⟩
  intro i j
  have hidx : i.val * n + j.val < a.size := by
    rw [has]
    have := Nat.mul_le_mul_right n i.isLt
    rw [Nat.succ_mul] at this
    omega
  exact he _ hidx

/-- Copying the lower triangle produces a finite symmetric matrix and preserves
an entrywise error bound against a symmetric target. No arithmetic is performed. -/
theorem mirrorLower_accuracy (n : Nat) (a : Array Float) (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (has : a.size = n * n) (ha : a.all Float.isFinite = true) (hA : A.IsHermitian)
    (hε : 0 ≤ ε) (he : ∀ i j, |matrix n n a i j - A i j| ≤ ε)
    : (mirrorLower n a).size = n * n
      ∧ (mirrorLower n a).all Float.isFinite = true
      ∧ (matrix n n (mirrorLower n a)).IsHermitian
      ∧ (∀ i j, |matrix n n (mirrorLower n a) i j - A i j| ≤ ε)
      ∧ ‖matrix n n (mirrorLower n a) - A‖ ≤ n * ε := by
  have hm : (mirrorLower n a).size = n * n ∧ (mirrorLower n a).all Float.isFinite = true ∧
      ∀ i j, i < n → j < n → entry n (mirrorLower n a) i j =
        if i < j then entry n a j i else entry n a i j :=
    Flare.Matrix.Storage.mirrorLower_spec n a ⟨has, ha⟩
  have hent (i j : Fin n) : matrix n n (mirrorLower n a) i j =
      if i.val < j.val then matrix n n a j i else matrix n n a i j := by
    change value (entry n (mirrorLower n a) i.val j.val) = _
    rw [hm.2.2 _ _ i.isLt j.isLt]
    split_ifs <;> rfl
  have herr (i j : Fin n) : |matrix n n (mirrorLower n a) i j - A i j| ≤ ε := by
    rw [hent]
    split_ifs with hij
    · have hsym : A i j = A j i := by
        have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j i) hA.eq
        simpa only [Matrix.conjTranspose_apply, star_trivial] using hh
      rw [hsym]
      exact he j i
    · exact he i j
  refine ⟨hm.1, hm.2.1, ?_, herr,
    Flare.Analysis.SpectralPerturbation.norm_le_entries _ _ hε herr⟩
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial, hent]
  split_ifs <;> first | rfl | (have : i = j := Fin.ext (by omega); subst j; rfl)

/-- Block assembly only copies stored entries, including the lower-left transpose. -/
theorem blocks_storage (n m : Nat) (a b d : Array Float)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hd : d.all Float.isFinite = true)
    : (blocks n m a b d).size = (n + m) * (n + m)
      ∧ (blocks n m a b d).all Float.isFinite = true := by
  refine ⟨by simp [blocks], ?_⟩
  rw [Array.all_eq_true]
  intro i hi
  simp only [blocks, Array.getElem_map, Array.getElem_range]
  split_ifs <;> first
    | exact Flare.Matrix.Storage.getD_finite _ _ ha
    | exact Flare.Matrix.Storage.getD_finite _ _ hb
    | exact Flare.Matrix.Storage.getD_finite _ _ hd

private theorem blocks_entry (n m : Nat) (a b d : Array Float) (i j : Fin (n + m))
    : matrix (n + m) (n + m) (blocks n m a b d) i j
      = if i.val < n then
          if j.val < n then value (entry n a i.val j.val) else value (entry m b i.val (j.val - n))
        else if j.val < n then
          value (entry m b j.val (i.val - n))
        else
          value (entry m d (i.val - n) (j.val - n)) := by
  have hk : 0 < n + m := Nat.zero_lt_of_lt i.isLt
  have hidx : i.val * (n + m) + j.val < (n + m) * (n + m) := by
    have := Nat.mul_le_mul_right (n + m) i.isLt
    rw [Nat.succ_mul] at this
    omega
  have hdiv : (i.val * (n + m) + j.val) / (n + m) = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
  have hmod : (i.val * (n + m) + j.val) % (n + m) = j.val := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  simp only [matrix, blocks, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_range, hidx, ↓reduceIte, Option.map_some, Option.getD_some, hdiv, hmod]
  split_ifs <;> rfl

/-- Exact real semantics of the native symmetric block layout, with Lean's
canonical sum/finite-index equivalence making the indexing interpretation explicit. -/
theorem blocks_matrix (n m : Nat) (a b d : Array Float)
    : matrix (n + m) (n + m) (blocks n m a b d)
      = (Matrix.fromBlocks (matrix n n a) (matrix n m b) (matrix n m b).transpose
          (matrix m m d)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := n) (n := m)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := n) (n := m)).surjective j
  rw [blocks_entry]
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp [finSumFinEquiv_apply_left, i.isLt, j.isLt, Matrix.submatrix_apply, matrix, entry,
            Flare.Matrix.Dense.entry]
      | inr j =>
          simp [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, i.isLt,
            Matrix.submatrix_apply, matrix, entry, Flare.Matrix.Dense.entry]
  | inr i =>
      cases j with
      | inl j =>
          simp [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, j.isLt,
            Matrix.submatrix_apply, matrix, entry, Flare.Matrix.Dense.entry]
      | inr j =>
          simp [finSumFinEquiv_apply_right, Matrix.submatrix_apply, matrix, entry,
            Flare.Matrix.Dense.entry]

/-- Block assembly preserves a common entrywise error allowance; the transposed
off-diagonal block uses the same stored entries and the same bound. -/
theorem blocks_accuracy (n m : Nat) (a b d : Array Float)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ)
    (ha : ∀ i j, |matrix n n a i j - A i j| ≤ ε)
    (hb : ∀ i j, |matrix n m b i j - B i j| ≤ ε)
    (hd : ∀ i j, |matrix m m d i j - D i j| ≤ ε)
    : ∀ i j,
        |matrix (n + m) (n + m) (blocks n m a b d) i j
          - (Matrix.fromBlocks A B B.transpose D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
              i j|
        ≤ ε := by
  rw [blocks_matrix]
  intro i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := n) (n := m)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := n) (n := m)).surjective j
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  cases i with
  | inl i =>
      cases j with
      | inl j => exact ha i j
      | inr j => exact hb i j
  | inr i =>
      cases j with
      | inl j => exact hb j i
      | inr j => exact hd i j

/-- A symmetric block layout is exactly symmetric whenever its diagonal blocks
are. This is independent of roundoff in their upstream construction. -/
theorem blocks_isHermitian (n m : Nat) (a b d : Array Float)
    (ha : (matrix n n a).IsHermitian) (hd : (matrix m m d).IsHermitian)
    : (matrix (n + m) (n + m) (blocks n m a b d)).IsHermitian := by
  rw [blocks_matrix]
  apply Matrix.IsHermitian.submatrix
  apply Matrix.IsHermitian.ext
  intro i j
  cases i <;> cases j <;> simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply, star_trivial]
  · exact ha.apply _ _
  · exact hd.apply _ _

/-- Native combination of real-zero arrays stays exactly zero. This handles
signed zero without identifying its two encodings. -/
theorem combine_zero (a b : Array Float) (s : Float)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true) (hs : s.isFinite = true)
    (ha0 : ∀ i, i < a.size → value (a.getD i 0.0) = 0)
    (hb0 : ∀ i, i < a.size → value (b.getD i 0.0) = 0)
    : ∃ r,
        combine a b s = .ok r
        ∧ r.size = a.size
        ∧ r.all Float.isFinite = true
        ∧ ∀ i, i < a.size → value (r.getD i 0.0) = 0 := by
  have hh (i : Nat) (hi : i < a.size) : (s * b.getD i 0.0).isFinite = true ∧
      (a.getD i 0.0 + s * b.getD i 0.0).isFinite = true ∧
      value (a.getD i 0.0 + s * b.getD i 0.0) = 0 := by
    have ht := Flare.Binary64.Zero.mul_zero s (b.getD i 0.0) hs
      (Flare.Matrix.Storage.getD_finite _ _ hb) (by rw [hb0 i hi, mul_zero])
    exact ⟨ht.1, Flare.Binary64.Zero.add_zero _ _ (Flare.Matrix.Storage.getD_finite _ _ ha)
      ht.1 (ha0 i hi) ht.2⟩
  have hmap : combine a b s = .ok ((Array.range a.size).map
      (fun i => a.getD i 0.0 + s * b.getD i 0.0)) := by
    apply Flare.Matrix.Multiplication.mapM_eq_ok_map
    intro i hi
    have hi' : i < a.size := by simpa using hi
    simp only [finite, (hh i hi').1, (hh i hi').2.1, ↓reduceIte, bind, Except.bind]
  refine ⟨_, hmap, by simp, ?_, ?_⟩
  · rw [Array.all_eq_true]
    intro i hi
    have hi' : i < a.size := by simpa using hi
    simpa only [Array.getElem_map, Array.getElem_range] using (hh i hi').2.1
  · intro i hi
    simpa [hi] using (hh i hi).2.2

/-- A common rounded scalar combination preserves exact real symmetry.
The proof accounts for equal finite values with different signed-zero encodings. -/
theorem combine_isHermitian (n : Nat) (a b : Array Float) (s : Float) (r : Array Float) (M : ℝ)
    (has : a.size = n * n) (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hs : s.isFinite = true) (hM : M ≤ (2 : ℝ) ^ (990 : Int)) (hη : (2 : ℝ) ^ (-1022 : Int) ≤ M)
    (hmass : ∀ i, i < a.size → |value (a.getD i 0.0)| + |value s * value (b.getD i 0.0)| ≤ M)
    (hA : (matrix n n a).IsHermitian) (hB : (matrix n n b).IsHermitian)
    (hr : combine a b s = .ok r)
    : (matrix n n r).IsHermitian := by
  have hstep (i : Nat) (hi : i < a.size) := combine_step (a.getD i 0.0) (b.getD i 0.0) s M
    (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ hb)
    hs hM hη (hmass i hi)
  have hmap : combine a b s = .ok ((Array.range a.size).map
      (fun i => a.getD i 0.0 + s * b.getD i 0.0)) := by
    apply Flare.Matrix.Multiplication.mapM_eq_ok_map
    intro i hi
    have hi' : i < a.size := by simpa using hi
    simp only [finite, (hstep i hi').1, (hstep i hi').2.1, ↓reduceIte, bind, Except.bind]
  have heq : r = (Array.range a.size).map (fun i => a.getD i 0.0 + s * b.getD i 0.0) :=
    Except.ok.inj (hr.symm.trans hmap)
  have hindex (i j : Fin n) : i.val * n + j.val < a.size := by
    rw [has]
    have hh := Nat.mul_le_mul_right n i.isLt
    rw [Nat.succ_mul] at hh
    omega
  have hentry (i j : Fin n) : matrix n n r i j =
      value (a.getD (i.val * n + j.val) 0.0 + s * b.getD (i.val * n + j.val) 0.0) := by
    simp [matrix, heq, hindex i j]
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial, hentry]
  apply (Flare.Binary64.Congruence.add_value_congr_left _ _ _
    (Flare.Matrix.Storage.getD_finite _ _ ha)
    (Flare.Matrix.Storage.getD_finite _ _ ha) (hstep _ (hindex j i)).1 (hA.apply i j)).trans
  apply Flare.Binary64.Congruence.add_value_congr_right _ _ _
    (Flare.Matrix.Storage.getD_finite _ _ ha) (hstep _ (hindex j i)).1 (hstep _ (hindex i j)).1
  exact Flare.Binary64.Congruence.mul_value_congr_right _ _ _ hs
    (Flare.Matrix.Storage.getD_finite _ _ hb) (Flare.Matrix.Storage.getD_finite _ _ hb)
    (hB.apply i j)

end Flare.Matrix.MatrixFormation
