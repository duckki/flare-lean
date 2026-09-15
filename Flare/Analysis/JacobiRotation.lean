import Flare.Analysis.Jacobi
import Mathlib.Data.Matrix.Basis

/-! Matrix identities for the plane rotations used in the Jacobi eigensolver.
These proof-side matrices connect the scalar update equations to orthogonal
similarity. Native binary64 coefficients require separate error bounds. -/

namespace Flare.Analysis.JacobiRotation
open Matrix

/-- The rotation mixes columns p and q as `(c*x-s*y, s*x+c*y)`.
Its coefficients need not be normalized in this definition. -/
noncomputable def plane {n : Nat} (p q : Fin n) (c s : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun i => if i = p ∨ i = q then c else 1) + single p q s - single q p s

/-- Right multiplication has exactly the column-pair schedule of the native
eigenvector update. All other columns are unchanged. -/
theorem mul_plane {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ)
    (p q : Fin n) (hpq : p ≠ q) (c s : ℝ) (i : Fin m) (j : Fin n)
    : (A * plane p q c s) i j
      = if j = p then
          c * A i p - s * A i q
        else if j = q then
          s * A i p + c * A i q
        else
          A i j := by
  by_cases hjp : j = p
  · subst j
    simp [plane, Matrix.mul_sub, Matrix.mul_add, mul_diagonal, hpq, mul_comm]
  · by_cases hjq : j = q
    · subst j
      simp [plane, Matrix.mul_sub, Matrix.mul_add, mul_diagonal, hpq.symm,
        mul_comm, add_comm]
    · simp [plane, Matrix.mul_sub, Matrix.mul_add, mul_diagonal, hjp, hjq]

/-- Left multiplication by the transpose applies the same pair schedule to
rows. This follows from the column identity, rather than a second scalar loop. -/
theorem transpose_plane_mul {m n : Nat} (A : Matrix (Fin n) (Fin m) ℝ)
    (p q : Fin n) (hpq : p ≠ q) (c s : ℝ) (i : Fin n) (j : Fin m)
    : ((plane p q c s).transpose * A) i j
      = if i = p then
          c * A p j - s * A q j
        else if i = q then
          s * A p j + c * A q j
        else
          A i j := by
  have h := mul_plane A.transpose p q hpq c s j i
  change (A.transpose * plane p q c s).transpose i j = _ at h
  rw [transpose_mul, transpose_transpose] at h
  exact h

/-- A normalized plane matrix is exactly orthogonal on both sides. -/
theorem plane_orthogonal {n : Nat} (p q : Fin n) (hpq : p ≠ q) (c s : ℝ) (hunit : c ^ 2 + s ^ 2 = 1)
    : (plane p q c s).transpose * plane p q c s = 1
      ∧ plane p q c s * (plane p q c s).transpose = 1 := by
  have hleft : (plane p q c s).transpose * plane p q c s = 1 := by
    ext i j
    rw [transpose_plane_mul _ p q hpq]
    by_cases hip : i = p <;> by_cases hiq : i = q <;>
      by_cases hjp : j = p <;> by_cases hjq : j = q
    all_goals subst_vars
    all_goals simp_all [plane, diagonal_apply, Matrix.one_apply, eq_comm]
    all_goals nlinarith
  exact ⟨hleft, mul_eq_one_comm.mp hleft⟩

/-- An exact similarity has the two pair updates and the unchanged exterior
block used by Jacobi. The pivot block is stated without assuming annihilation. -/
theorem similarity_entries {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ)
    (p q : Fin n) (hpq : p ≠ q) (c s : ℝ)
    (hA : ∀ i j, A i j = A j i)
    : let B := (plane p q c s).transpose * A * plane p q c s
      B p p = c ^ 2 * A p p - 2 * c * s * A p q + s ^ 2 * A q q
      ∧ B q q = s ^ 2 * A p p + 2 * c * s * A p q + c ^ 2 * A q q
      ∧ B p q = c * s * (A p p - A q q) + (c ^ 2 - s ^ 2) * A p q
      ∧ (∀ k, k ≠ p → k ≠ q → B k p = c * A k p - s * A k q ∧ B k q = s * A k p + c * A k q)
      ∧ (∀ i j, i ≠ p → i ≠ q → j ≠ p → j ≠ q → B i j = A i j) := by
  dsimp only
  have entries (i j : Fin n) := mul_plane ((plane p q c s).transpose * A) p q hpq c s i j
  simp_rw [transpose_plane_mul A p q hpq c s] at entries
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [entries]
    simp only [ite_true]
    rw [hA q p]
    ring
  · rw [entries]
    simp only [hpq.symm, if_false, ite_true]
    rw [hA q p]
    ring
  · rw [entries]
    simp only [hpq.symm, if_false, ite_true]
    rw [hA q p]
    ring
  · intro k hkp hkq
    simp [entries, hkp, hkq, hpq.symm]
  · intro i j hip hiq hjp hjq
    simp [entries, hip, hiq, hjp, hjq]

/-- The tangent's quadratic residual is precisely what remains in the pivot
block when the native diagonal shortcut is compared with an exact orthogonal
similarity. This identity does not require the tangent to be an exact root. -/
theorem pivot_residual (a b d t : ℝ)
    : let c := 1 / Real.sqrt (1 + t ^ 2)
      let s := t * c
      let r := b * t ^ 2 + (d - a) * t - b
      (c ^ 2 * a - 2 * c * s * b + s ^ 2 * d) - (a - t * b) = c ^ 2 * t * r
      ∧ (s ^ 2 * a + 2 * c * s * b + c ^ 2 * d) - (d + t * b) = -(c ^ 2 * t * r)
      ∧ c * s * (a - d) + (c ^ 2 - s ^ 2) * b = -(c ^ 2 * r) := by
  dsimp only
  have hu := Jacobi.rotation_unit t
  generalize (1 / Real.sqrt (1 + t ^ 2)) = c at *
  have hunit : c ^ 2 + t ^ 2 * c ^ 2 = 1 := by nlinarith [hu]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [congrArg (fun x : ℝ => x * (a - t * b)) hunit]
  · nlinarith [congrArg (fun x : ℝ => x * (d + t * b)) hunit]
  · ring

/-- Real symmetry is preserved by orthogonal similarity, independently of the
normalization of the matrix used for the congruence. -/
theorem similarity_symmetric {n : Nat} (A J : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, A i j = A j i)
    : ∀ i j, (J.transpose * A * J) i j = (J.transpose * A * J) j i := by
  have ht : A.transpose = A := Matrix.ext fun i j => hA j i
  have h : (J.transpose * A * J).transpose = J.transpose * A * J := by
    simp only [transpose_mul, transpose_transpose, ht, Matrix.mul_assoc]
  intro i j
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j i) h

/-- Entrywise error relative to an exact similarity. Pair/diagonal rounding
and the tangent residual are kept separate, allowing later bounds to exploit
the actual entries and pivots instead of a single worst-case constant. -/
theorem similarity_error {n : Nat} (A B : Matrix (Fin n) (Fin n) ℝ)
    (p q : Fin n) (hpq : p ≠ q) (t ε : ℝ) (ht : |t| ≤ 2) (hε : 0 ≤ ε)
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i)
    (hp : |B p p - (A p p - t * A p q)| ≤ ε)
    (hq : |B q q - (A q q + t * A p q)| ≤ ε)
    (hpivot : B p q = 0)
    (hpair
      : ∀ k,
          k ≠ p
          → k ≠ q
          → |B k p - ((1 / Real.sqrt (1 + t^2)) * A k p - (t / Real.sqrt (1 + t^2)) * A k q)| ≤ ε
            ∧ |B k q - ((t / Real.sqrt (1 + t^2)) * A k p + (1 / Real.sqrt (1 + t^2)) * A k q)| ≤ ε)
    (hexterior : ∀ i j, i ≠ p → i ≠ q → j ≠ p → j ≠ q → B i j = A i j)
    : let c := 1 / Real.sqrt (1 + t^2)
      let s := t * c
      let J := plane p q c s
      let r := A p q * t^2 + (A q q - A p p) * t - A p q
      ∀ i j, |B i j - (J.transpose * A * J) i j| ≤ ε + 2 * |r| := by
  dsimp only
  let c := 1 / Real.sqrt (1 + t^2)
  let s := t * c
  let J := plane p q c s
  let D := J.transpose * A * J
  let r := A p q * t^2 + (A q q - A p p) * t - A p q
  have hu : c^2 + s^2 = 1 := Jacobi.rotation_unit t
  have hc : |c^2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg c)]; nlinarith [sq_nonneg s]
  have hct : |c^2 * t * r| ≤ 2 * |r| := by
    simp only [abs_mul]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul hc ht (abs_nonneg _) (by norm_num))
      (abs_nonneg r)).trans_eq (by ring)
  have hcr : |c^2 * r| ≤ 2 * |r| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hc (abs_nonneg r)).trans (by linarith [abs_nonneg r])
  obtain ⟨hpp, hqq, hpq', hpair', hout⟩ := similarity_entries A p q hpq c s hA
  obtain ⟨hrp, hrq, hrpq⟩ := pivot_residual (A p p) (A p q) (A q q) t
  have hDp : |D p p - (A p p - t * A p q)| ≤ 2 * |r| := by
    change |(J.transpose * A * J) p p - _| ≤ _
    rw [hpp, hrp]
    exact hct
  have hDq : |D q q - (A q q + t * A p q)| ≤ 2 * |r| := by
    change |(J.transpose * A * J) q q - _| ≤ _
    rw [hqq, hrq, abs_neg]
    exact hct
  have hDpq : |D p q| ≤ 2 * |r| := by
    change |(J.transpose * A * J) p q| ≤ _
    rw [hpq', hrpq, abs_neg]
    exact hcr
  have hd : ∀ i j, D i j = D j i := similarity_symmetric A J hA
  have pair (k : Fin n) (hkp : k ≠ p) (hkq : k ≠ q) :
      |B k p - D k p| ≤ ε + 2 * |r| ∧ |B k q - D k q| ≤ ε + 2 * |r| := by
    obtain ⟨hP, hQ⟩ := hpair k hkp hkq
    have hE := hpair' k hkp hkq
    change D k p = c * A k p - s * A k q ∧ D k q = s * A k p + c * A k q at hE
    have he : s = t / Real.sqrt (1 + t^2) := by dsimp [s, c]; ring
    rw [hE.1, hE.2, he]
    exact ⟨hP.trans (by linarith [abs_nonneg r]), hQ.trans (by linarith [abs_nonneg r])⟩
  have diagP : |B p p - D p p| ≤ ε + 2 * |r| := by
    exact (abs_sub_le _ _ _).trans (add_le_add hp (by rwa [abs_sub_comm]))
  have diagQ : |B q q - D q q| ≤ ε + 2 * |r| := by
    exact (abs_sub_le _ _ _).trans (add_le_add hq (by rwa [abs_sub_comm]))
  have pivot : |B p q - D p q| ≤ ε + 2 * |r| := by
    rw [hpivot, zero_sub, abs_neg]
    exact hDpq.trans (by linarith)
  intro i j
  change |B i j - D i j| ≤ _
  by_cases hip : i = p
  · subst i
    by_cases hjp : j = p
    · subst j; exact diagP
    by_cases hjq : j = q
    · subst j; exact pivot
    rw [hB p j, hd p j]
    exact (pair j hjp hjq).1
  by_cases hiq : i = q
  · subst i
    by_cases hjp : j = p
    · subst j; rw [hB q p, hd q p]; exact pivot
    by_cases hjq : j = q
    · subst j; exact diagQ
    rw [hB q j, hd q j]
    exact (pair j hjp hjq).2
  by_cases hjp : j = p
  · subst j; exact (pair i hip hiq).1
  by_cases hjq : j = q
  · subst j; exact (pair i hip hiq).2
  change |B i j - (J.transpose * A * J) i j| ≤ _
  rw [hexterior i j hip hiq hjp hjq, hout i j hip hiq hjp hjq, sub_self, abs_zero]
  positivity

end Flare.Analysis.JacobiRotation
