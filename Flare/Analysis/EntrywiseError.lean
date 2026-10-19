module

public import Flare.Analysis.NumericalBounds
public import Mathlib.Tactic

/-! Absolute entrywise matrix error, propagation through exact algebra, and
quantitative spectral margins. These bounds are independent of the algorithm
producing the error. Extracted from the Kalman case study with its hypotheses
and constants preserved; see docs/provenance.md. -/

@[expose] public section

namespace Flare.Analysis.EntrywiseError

open Matrix

noncomputable section

/-- Absolute entrywise comparison of two Real matrices. -/
def EntrywiseWithin {n m : Nat} (ε : ℝ) (a b : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  0 ≤ ε ∧ ∀ i j, |a i j - b i j| ≤ ε

theorem within_trans {n m : Nat} {a b c : Matrix (Fin n) (Fin m) ℝ} {ε δ : ℝ}
    (hab : EntrywiseWithin ε a b) (hbc : EntrywiseWithin δ b c)
    : EntrywiseWithin (ε + δ) a c := by
  refine ⟨add_nonneg hab.1 hbc.1, fun i j => ?_⟩
  exact (abs_sub_le (a i j) (b i j) (c i j)).trans (add_le_add (hab.2 i j) (hbc.2 i j))

theorem within_transpose {n m : Nat} {a b : Matrix (Fin n) (Fin m) ℝ} {ε : ℝ}
    (h : EntrywiseWithin ε a b)
    : EntrywiseWithin ε a.transpose b.transpose :=
  ⟨h.1, fun i j => h.2 j i⟩

theorem within_add {n m : Nat} {a b c d : Matrix (Fin n) (Fin m) ℝ} {ε δ : ℝ}
    (hab : EntrywiseWithin ε a b) (hcd : EntrywiseWithin δ c d)
    : EntrywiseWithin (ε + δ) (a + c) (b + d) := by
  refine ⟨add_nonneg hab.1 hcd.1, fun i j => ?_⟩
  change |(a i j + c i j) - (b i j + d i j)| ≤ _
  rw [show (a i j + c i j) - (b i j + d i j) = (a i j - b i j) + (c i j - d i j) by ring]
  exact (abs_add_le _ _).trans (add_le_add (hab.2 i j) (hcd.2 i j))

theorem within_sub {n m : Nat} {a b c d : Matrix (Fin n) (Fin m) ℝ} {ε δ : ℝ}
    (hab : EntrywiseWithin ε a b) (hcd : EntrywiseWithin δ c d)
    : EntrywiseWithin (ε + δ) (a - c) (b - d) := by
  refine ⟨add_nonneg hab.1 hcd.1, fun i j => ?_⟩
  change |(a i j - c i j) - (b i j - d i j)| ≤ _
  rw [show (a i j - c i j) - (b i j - d i j) = (a i j - b i j) - (c i j - d i j) by ring]
  exact (abs_sub _ _).trans (add_le_add (hab.2 i j) (hcd.2 i j))

theorem within_refl {n m : Nat} (a : Matrix (Fin n) (Fin m) ℝ) : EntrywiseWithin 0 a a := by
  simp [EntrywiseWithin]

theorem within_sym {n m : Nat} {a b : Matrix (Fin n) (Fin m) ℝ} {ε : ℝ} (h : EntrywiseWithin ε a b)
    : EntrywiseWithin ε b a :=
  ⟨h.1, fun i j => by simpa only [abs_sub_comm] using h.2 i j⟩

/-- Rounded operands and multiplication error remain separate. A and B
are magnitude bounds on the ideal operands, not on their differences. -/
theorem within_mul {n k m : Nat}
    {a a₀ : Matrix (Fin n) (Fin k) ℝ} {b b₀ : Matrix (Fin k) (Fin m) ℝ}
    {ε δ A B : ℝ} (ha : EntrywiseWithin ε a a₀) (hb : EntrywiseWithin δ b b₀)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha₀ : ∀ i j, |a₀ i j| ≤ A) (hb₀ : ∀ i j, |b₀ i j| ≤ B)
    : EntrywiseWithin (k * (ε * B + A * δ + ε * δ)) (a * b) (a₀ * b₀) := by
  have hε := ha.1
  have hδ := hb.1
  refine ⟨by positivity, fun i j => ?_⟩
  simp only [Matrix.mul_apply, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ t : Fin k, |a i t * b t j - a₀ i t * b₀ t j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin k, (ε * B + A * δ + ε * δ) := by
      apply Finset.sum_le_sum
      intro t _
      have he : a i t * b t j - a₀ i t * b₀ t j =
          (a i t - a₀ i t) * b₀ t j + a₀ i t * (b t j - b₀ t j) +
            (a i t - a₀ i t) * (b t j - b₀ t j) := by ring
      rw [he]
      apply ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      simp only [abs_mul]
      exact add_le_add (add_le_add
        (mul_le_mul (ha.2 i t) (hb₀ t j) (abs_nonneg _) ha.1)
        (mul_le_mul (ha₀ i t) (hb.2 t j) (abs_nonneg _) hA))
        (mul_le_mul (ha.2 i t) (hb.2 t j) (abs_nonneg _) ha.1)
    _ = _ := by simp; ring

theorem product_magnitude {n k m : Nat} (a : Matrix (Fin n) (Fin k) ℝ)
    (b : Matrix (Fin k) (Fin m) ℝ) (A B : ℝ)
    (ha : ∀ i j, |a i j| ≤ A) (hb : ∀ i j, |b i j| ≤ B)
    : ∀ i j, |(a * b) i j| ≤ k * A * B := by
  intro i j
  simp only [Matrix.mul_apply]
  calc
    _ ≤ ∑ t : Fin k, |a i t * b t j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin k, A * B :=
      Finset.sum_le_sum
        fun t _ => by
          rw [abs_mul]
          exact mul_le_mul (ha i t) (hb t j) (abs_nonneg _) ((abs_nonneg _).trans (ha i t))
    _ = _ := by simp [mul_assoc]

/-- Right multiplication by an exact operand only propagates left error. -/
theorem within_mul_right {n k m : Nat} {a a₀ : Matrix (Fin n) (Fin k) ℝ} {ε B : ℝ}
    (ha : EntrywiseWithin ε a a₀) (b : Matrix (Fin k) (Fin m) ℝ)
    (hB : 0 ≤ B) (hb : ∀ i j, |b i j| ≤ B)
    : EntrywiseWithin (k * ε * B) (a * b) (a₀ * b) := by
  have hε := ha.1
  refine ⟨by positivity, fun i j => ?_⟩
  simp only [Matrix.mul_apply, ← Finset.sum_sub_distrib, ← sub_mul]
  calc
    _ ≤ ∑ t : Fin k, |(a i t - a₀ i t) * b t j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin k, ε * B :=
      Finset.sum_le_sum
        fun t _ => by
          rw [abs_mul]
          exact mul_le_mul (ha.2 i t) (hb t j) (abs_nonneg _) ha.1
    _ = _ := by simp [mul_assoc]

/-- Exact diagonal support removes the inner-dimension factor when propagating
gain error through an exact right operand. -/
theorem within_diagonal_mul_right {n m : Nat}
    {a a₀ : Matrix (Fin n) (Fin n) ℝ} {ε B : ℝ}
    (ha : EntrywiseWithin ε a a₀)
    (hd : a = diagonal (fun i => a i i)) (hd₀ : a₀ = diagonal (fun i => a₀ i i))
    (b : Matrix (Fin n) (Fin m) ℝ) (hB : 0 ≤ B) (hb : ∀ i j, |b i j| ≤ B)
    : EntrywiseWithin (ε * B) (a * b) (a₀ * b) := by
  refine ⟨mul_nonneg ha.1 hB, fun i j => ?_⟩
  rw [hd, hd₀, diagonal_mul, diagonal_mul, ← sub_mul, abs_mul]
  exact mul_le_mul (ha.2 i i) (hb i j) (abs_nonneg _) ha.1

/-- Left multiplication by an exact operand only propagates right error. -/
theorem within_mul_left {n k m : Nat} {b b₀ : Matrix (Fin k) (Fin m) ℝ} {ε A : ℝ}
    (a : Matrix (Fin n) (Fin k) ℝ) (hb : EntrywiseWithin ε b b₀)
    (hA : 0 ≤ A) (ha : ∀ i j, |a i j| ≤ A)
    : EntrywiseWithin (k * A * ε) (a * b) (a * b₀) := by
  have h := within_transpose (within_mul_right (within_transpose hb) a.transpose hA
    (fun i j => ha j i))
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h
  convert h using 1
  ring

/-- An entrywise perturbation consumes at most `n * ε` of a uniform spectral
lower bound. The remaining lower bound may be zero or negative. -/
theorem lower_bound_of_error {n : Nat} (reference output : Matrix (Fin n) (Fin n) ℝ)
    (α ε : ℝ) (href : (reference - α • 1).PosSemidef)
    (hout : output.IsHermitian) (he : EntrywiseWithin ε output reference)
    : (output - (α - n * ε) • 1).PosSemidef := by
  have hrefsym : reference.IsHermitian := by
    have hid : (α • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := by
      simp [Matrix.IsHermitian]
    convert href.isHermitian.add hid using 1
    abel
  have hbound := Flare.Analysis.NumericalBounds.perturbation_lower_bound reference
    (output - reference) α ε he.1 href (hout.sub hrefsym) he.2
  convert hbound using 1
  abel

/-- Strict positivity of a symmetric rounded dense output requires an error
allowance smaller than the ideal covariance's uniform positivity margin. -/
theorem posDef_of_error_margin {n : Nat} (reference output : Matrix (Fin n) (Fin n) ℝ)
    (α ε : ℝ) (hmargin : n * ε < α) (href : (reference - α • 1).PosSemidef)
    (hout : output.IsHermitian) (he : EntrywiseWithin ε output reference)
    : output.PosDef := by
  have hb := lower_bound_of_error reference output α ε href hout he
  exact Flare.Analysis.NumericalBounds.posDef_of_lower_bound output _ (sub_pos.mpr hmargin) hb

/-- A right-hand linear-system residual bounds the solution against C S⁻¹. -/
theorem right_residual_accuracy {n m : Nat} (s : Matrix (Fin m) (Fin m) ℝ)
    (c k : Matrix (Fin n) (Fin m) ℝ) (α ρ : ℝ)
    (hα : 0 < α) (hs : (s - α • 1).PosSemidef)
    (he : EntrywiseWithin ρ (k * s) c)
    : EntrywiseWithin (m * ρ / α) k (c * s⁻¹) := by
  have hpd := Flare.Analysis.NumericalBounds.posDef_of_lower_bound s α hα hs
  have hst : s.transpose = s := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hpd.isHermitian.eq
  have hid : s⁻¹ * s = 1 := by
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit)
  have hex : (c * s⁻¹) * s = c := by rw [Matrix.mul_assoc, hid, Matrix.mul_one]
  have hρ := he.1
  have hsym (i j : Fin m) : s i j = s j i :=
    (congr_fun (congr_fun hst i) j).symm
  have hmul (x : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) (t : Fin m)
      : s.mulVec (fun u => x i u) t = (x * s) i t := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro u _
    rw [hsym t u, mul_comm]
  refine ⟨by positivity, fun i j => ?_⟩
  have heq : s.mulVec (fun t => (c * s⁻¹) i t) = fun t => c i t := by
    ext t
    rw [hmul, hex]
  apply Flare.Analysis.NumericalBounds.residual_entrywise_bound s α ρ hα he.1 hs
    (fun t => k i t) (fun t => (c * s⁻¹) i t) (fun t => c i t) heq _ j
  intro t
  rw [hmul]
  exact he.2 i t

end
end Flare.Analysis.EntrywiseError
