module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real

/-! Exact pseudoinverses for symmetric, possibly singular real matrices.
The spectral construction supplies mathematical witnesses. -/

@[expose] public section

namespace Flare.Analysis

/-- The four Moore–Penrose equations for a square real matrix. -/
def MoorePenrose {m : Nat} (A Z : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  A * Z * A = A ∧ Z * A * Z = Z ∧ (A * Z).transpose = A * Z ∧ (Z * A).transpose = Z * A

end Flare.Analysis

namespace Flare.Analysis.MoorePenrose
open Matrix Flare.Analysis

/-- The four source equations determine a unique pseudoinverse. -/
theorem unique {m : Nat} {A X Y : Matrix (Fin m) (Fin m) ℝ}
    (hx : MoorePenrose A X) (hy : MoorePenrose A Y)
    : X = Y := by
  have hleft : A * X = A * Y := by
    calc
      A * X = (A * X).transpose := hx.2.2.1.symm
      _ = ((A * Y) * (A * X)).transpose := by rw [← mul_assoc, hy.1]
      _ = (A * X) * (A * Y) := by rw [transpose_mul, hx.2.2.1, hy.2.2.1]
      _ = A * Y := by rw [← mul_assoc, hx.1]
  have hright : X * A = Y * A := by
    calc
      X * A = (X * A).transpose := hx.2.2.2.symm
      _ = ((X * A) * (Y * A)).transpose := by rw [mul_assoc, ← mul_assoc A, hy.1]
      _ = (Y * A) * (X * A) := by rw [transpose_mul, hy.2.2.2, hx.2.2.2]
      _ = Y * A := by rw [mul_assoc, ← mul_assoc A, hx.1]
  calc
    X = X * A * X := hx.2.1.symm
    _ = X * A * Y := by rw [mul_assoc, hleft, ← mul_assoc]
    _ = Y := by rw [hright, hy.2.1]

/-- A star-algebra change of coordinates preserves all four source equations. -/
theorem map_moorePenrose {m : Nat}
    (e : Matrix (Fin m) (Fin m) ℝ ≃⋆ₐ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    {A Z : Matrix (Fin m) (Fin m) ℝ} (h : MoorePenrose A Z)
    : MoorePenrose (e A) (e Z) := by
  have ht (M : Matrix (Fin m) (Fin m) ℝ) : (e M).transpose = e M.transpose := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using (map_star e M).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [map_mul] using congrArg e h.1
  · simpa only [map_mul] using congrArg e h.2.1
  · rw [← map_mul, ht, h.2.2.1]
  · rw [← map_mul, ht, h.2.2.2]

set_option maxHeartbeats 800000 in
/-- Every PSD real matrix has a PSD Moore–Penrose inverse, including the zero
matrix. The construction inverts nonzero eigenvalues and maps zero to zero. -/
theorem exists_posSemidef {m : Nat} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.PosSemidef)
    : ∃ Z, MoorePenrose A Z ∧ Z.PosSemidef := by
  let e := Unitary.conjStarAlgAut ℝ _ hA.isHermitian.eigenvectorUnitary
  let D := diagonal hA.isHermitian.eigenvalues
  let Z := diagonal (fun i => (hA.isHermitian.eigenvalues i)⁻¹)
  have hAZ : MoorePenrose D Z := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [D, Z, diagonal_mul_diagonal, mul_inv_mul_cancel]
    · simp only [D, Z, diagonal_mul_diagonal, diagonal_eq_diagonal_iff]
      intro i
      by_cases h : hA.isHermitian.eigenvalues i = 0 <;> simp [h]
    · simp [D, Z, diagonal_mul_diagonal]
    · simp [D, Z, diagonal_mul_diagonal]
  have he : A = e D := by
    simpa only [e, D, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq]
      using hA.isHermitian.spectral_theorem
  refine ⟨e Z, he ▸ map_moorePenrose e hAZ, ?_⟩
  have hZ : Z.PosSemidef := .diagonal fun i => inv_nonneg.mpr (hA.eigenvalues_nonneg i)
  simpa only [e, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
    using hZ.mul_mul_conjTranspose_same
      (hA.isHermitian.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)

/-- Any witness satisfying the source equations inherits PSD and symmetry. -/
theorem posSemidef {m : Nat} {A Z : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) (hZ : MoorePenrose A Z)
    : Z.PosSemidef := by
  obtain ⟨W, hW, hw⟩ := exists_posSemidef hA
  exact unique hZ hW ▸ hw

end Flare.Analysis.MoorePenrose
