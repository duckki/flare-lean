module

public import Flare.Matrix.JacobiSpectral

/-! Sparse spectral-error accumulation along the actual native trajectory.
Stopped transitions contribute no pivot error. All state and energy premises
are derived from the same native scan and rotation used by the runtime. -/

@[expose] public section

namespace Flare.Matrix.JacobiAccumulation
open Flare.Matrix.Value Flare.Binary64.Value Flare.Matrix.Operations
open Flare.Binary64.Arithmetic Flare.Matrix.JacobiIteration
open Flare.Matrix.JacobiBounds Flare.Matrix.JacobiConvergence
open Flare.Analysis.JacobiEnergy Flare.Analysis.JacobiNorms
open Flare.Analysis.JacobiRotation Flare.Analysis.SpectralPerturbation
open scoped Matrix.Norms.L2Operator

/-- Magnitude of a pivot actually rotated. An already stopped trajectory
contributes zero to the accumulated tangent residual. -/
noncomputable def activePivot (n : Nat) (a : Array Float) : ℝ :=
  if (selectedPivot n a).magnitude ≤ (1.0e-14 : Float) then
    0
  else
    value (selectedPivot n a).magnitude

/-- The energy recurrence also holds on stopped transitions when their active
pivot is zero. This allows telescoping arbitrary bounded execution prefixes. -/
theorem advance_energy (n k : Nat) (a v : Array Float) (hn : n ≤ 18)
    (hk : k ≤ 32 * n * n) (h : State n k a v)
    : offEnergy (matrix n n (advance n a v).1)
      ≤ (1 + (2 : ℝ) ^ (-36 : Int)) * offEnergy (matrix n n a) - 2 * (activePivot n a) ^ 2 := by
  by_cases hstop : (selectedPivot n a).magnitude ≤ (1.0e-14 : Float)
  · simp only [advance, activePivot, hstop, ↓reduceIte, zero_pow (by decide : 2 ≠ 0), mul_zero,
    sub_zero]
    nlinarith only [mul_nonneg (show 0 ≤ (2 : ℝ)^(-36 : Int) by positivity)
      (offEnergy_nonneg (matrix n n a))]
  · simpa only [activePivot, hstop, ↓reduceIte] using ((advance_correct n k a v hn hk h).2 hstop).2

/-- Actual pivot magnitudes have a square-root-in-step-count sum bound. The
roundoff term uses the already proved bound on every native matrix energy. -/
theorem trajectory_pivot_sum (n : Nat) (a v : Array Float) (hn : n ≤ 18)
    (h : State n 0 a v) (k : Nat) (hk : k ≤ 32 * n * n)
    : (∑ i ∈ Finset.range k, |activePivot n (trajectory n a v i).1|) ^ 2
      ≤ k * (offEnergy (matrix n n a) + k * (2 : ℝ) ^ (-36 : Int) * 1024) / 2 := by
  apply pivot_magnitude_sum
    (fun i => offEnergy (matrix n n (trajectory n a v i).1))
    (fun i => activePivot n (trajectory n a v i).1) ((2 : ℝ) ^ (-36 : Int)) 1024 k
    (by positivity) (offEnergy_nonneg _)
  · intro i hi
    have hstate := trajectory_state n a v hn h i (by omega)
    exact (offEnergy_le_energy _).trans ((state_energy_bound n i _ _ hn (by omega) hstate).1)
  · intro i hi
    exact advance_energy n i _ _ hn (by omega) (trajectory_state n a v hn h i (by omega))

/-- The coarse vector enclosure already keeps every native trajectory prefix
within a small norm allowance of its exactly orthogonal reference. -/
theorem trajectory_vectors_norm_bound (n : Nat) (a v : Array Float) (hn : n ≤ 18)
    (h : State n 0 a v) (hV : matrix n n v = 1) (k : Nat) (hk : k ≤ 32 * n * n)
    : ‖matrix n n (trajectory n a v k).2‖ ≤ (1001 / 1000 : ℝ) := by
  by_cases hz : n = 0
  · subst n
    rw [show matrix 0 0 (trajectory 0 a v k).2 = 0 from Subsingleton.elim _ _, norm_zero]
    norm_num
  have : NeZero n := ⟨hz⟩
  obtain ⟨W, hW, _, hV'⟩ := JacobiSpectral.trajectory_backward_error n a v hn h hV k hk
  have hnR : (n : ℝ) ≤ 18 := by exact_mod_cast hn
  have hkN : k ≤ 10368 := by nlinarith only [hk, hn]
  have hkR : (k : ℝ) ≤ 10368 := by exact_mod_cast hkN
  have herr : (k : ℝ) * (n * ((2 : ℝ)^(-48 : Int) * 65)) ≤ (1 / 1000 : ℝ) := by
    exact (mul_le_mul hkR (mul_le_mul_of_nonneg_right hnR (by positivity)) (by positivity) (by
      norm_num)).trans
      (by norm_num)
  have ht := (norm_le_norm_sub_add (matrix n n (trajectory n a v k).2) W).trans
    (add_le_add (hV'.trans herr) (CStarRing.norm_of_mem_unitary hW).le)
  exact ht.trans_eq (by norm_num)

/-- A native trajectory transition has a sparse similarity bound and the
two-column eigenvector bound against the same exact orthogonal reference. -/
theorem advance_similarity (n k : Nat) (a v : Array Float) (hn : n ≤ 18)
    (hk : k ≤ 32 * n * n) (h : State n k a v)
    (hVnorm : ‖matrix n n v‖ ≤ (1001 / 1000 : ℝ))
    : ∃ J : Matrix (Fin n) (Fin n) ℝ,
        J ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
        ∧ ‖matrix n n (advance n a v).1 - J.transpose * matrix n n a * J‖
          ≤ 141 * (2 : ℝ) ^ (-53 : Int) * ‖matrix n n a‖
            + (64 * n + 13) * (2 : ℝ) ^ (-53 : Int) * (2 : ℝ) ^ (-1022 : Int)
            + 512 * (2 : ℝ) ^ (-53 : Int) * activePivot n a
        ∧ ‖matrix n n (advance n a v).2 - matrix n n v * J‖ ≤ 97 * (2 : ℝ) ^ (-53 : Int) := by
  by_cases hstop : (selectedPivot n a).magnitude ≤ (1.0e-14 : Float)
  · refine ⟨1, (unitary _).one_mem, ?_, ?_⟩ <;>
      simp only [advance, activePivot, hstop, ↓reduceIte, Matrix.transpose_one, Matrix.one_mul,
        Matrix.mul_one, sub_self, norm_zero, mul_zero, add_zero] <;> positivity
  have hs := selectedPivot_correct n a h.matrix_finite h.symmetric
  obtain ⟨hpq, hq, hpivot, hlt⟩ := selectedPivot_ready n a (selectedPivot n a) hs.2.1 hs.2.2.2.1
    hstop
  have hp := hpq.trans hq
  have hE := state_energy_bound n k a v hn hk h
  have hab := entries_of_energy n a hE.1
  have hvb := entries_of_energy n v hE.2
  obtain ⟨result, he, hr⟩ := rotate_step n (selectedPivot n a).row (selectedPivot n a).column a v
    hp hq (Nat.ne_of_lt hpq) h.matrix_size h.vectors_size h.matrix_finite h.vectors_finite hab hvb
      hlt
  have hnext : advance n a v = result := by simp only [advance, hstop, ↓reduceIte, he]
  rw [hnext]
  have herr := JacobiSpectral.rotation_similarity n (selectedPivot n a).row (selectedPivot n
    a).column a v result
    hp hq (Nat.ne_of_lt hpq) h.matrix_finite h.vectors_finite hab hvb h.symmetric hlt hr
  dsimp only at herr
  refine ⟨_, orthogonal_mem_unitary _ ⟨herr.1, herr.2.1⟩, ?_, ?_⟩
  · have hnew := JacobiSpectral.rotation_similarity_norm n (selectedPivot n a).row (selectedPivot n
    a).column
      a v result hn hp hq (Nat.ne_of_lt hpq) h.matrix_finite hab h.symmetric hlt hr
    have habs := (Flare.Binary64.Order.abs_value (entry n a (selectedPivot n a).row (selectedPivot n
      a).column)
      (Flare.Matrix.Storage.getD_finite _ _ h.matrix_finite)).2
    rw [activePivot, ite_eq_right hstop, hpivot, habs]
    exact hnew
  · have hv := JacobiSpectral.rotation_vectors_norm n (selectedPivot n a).row (selectedPivot n
    a).column
      a v result hp hq (Nat.ne_of_lt hpq) h.matrix_finite h.vectors_finite hab hvb hlt hr
    have hη : (2 : ℝ)^(-1022 : Int) ≤ (2 : ℝ)^(-64 : Int) :=
      zpow_le_zpow_right₀ (by norm_num) (by norm_num)
    have hnR : (n : ℝ) ≤ 18 := by exact_mod_cast hn
    apply hv.trans
    have h1 := mul_le_mul_of_nonneg_left hVnorm (by positivity : 0 ≤ 96 * (2 : ℝ)^(-53 : Int))
    have h2 : 48 * (n : ℝ) * (2 : ℝ)^(-53 : Int) * (2 : ℝ)^(-1022 : Int) ≤
        48 * 18 * (2 : ℝ)^(-53 : Int) * (2 : ℝ)^(-64 : Int) := by gcongr
    exact (add_le_add h1 h2).trans (by norm_num)

/-- Sparse local errors add over every permitted native trajectory prefix.
The pivot sum is the actual active-pivot sum bounded by trajectory_pivot_sum. -/
theorem trajectory_backward_error (n : Nat) (a v : Array Float) (hn : n ≤ 18)
    (h : State n 0 a v) (hV : matrix n n v = 1) (k : Nat) (hk : k ≤ 32 * n * n)
    : ∃ W : Matrix (Fin n) (Fin n) ℝ,
        W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
        ∧ ‖matrix n n (trajectory n a v k).1 - W.transpose * matrix n n a * W‖
          ≤ 141 * (2 : ℝ) ^ (-53 : Int)
              * (∑ i ∈ Finset.range k, ‖matrix n n (trajectory n a v i).1‖)
            + k * (64 * n + 13) * (2 : ℝ) ^ (-53 : Int) * (2 : ℝ) ^ (-1022 : Int)
            + 512
              * (2 : ℝ) ^ (-53 : Int)
              * (∑ i ∈ Finset.range k, |activePivot n (trajectory n a v i).1|)
        ∧ ‖matrix n n (trajectory n a v k).2 - W‖ ≤ k * (97 * (2 : ℝ) ^ (-53 : Int)) := by
  induction k with
  | zero => refine ⟨1, (unitary _).one_mem, ?_, ?_⟩ <;> simp [trajectory, hV]
  | succ k ih =>
      obtain ⟨W, hW, hA, hV'⟩ := ih (by omega)
      have hstate := trajectory_state n a v hn h k (by omega)
      obtain ⟨J, hJ, heA, heV⟩ := advance_similarity n k _ _ hn (by omega) hstate
        (trajectory_vectors_norm_bound n a v hn h hV k (by omega))
      have heA' := heA.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (le_abs_self (activePivot n (trajectory n a v k).1)) (by positivity)))
      refine ⟨W * J, (unitary _).mul_mem hW hJ, ?_, ?_⟩
      · have he : matrix n n (trajectory n a v (k + 1)).1 - (W * J).transpose * matrix n n a * (W *
        J) =
            (matrix n n (advance n (trajectory n a v k).1 (trajectory n a v k).2).1 -
              J.transpose * matrix n n (trajectory n a v k).1 * J) +
            J.transpose * (matrix n n (trajectory n a v k).1 - W.transpose * matrix n n a * W) * J
              := by
          simp only [trajectory, Matrix.transpose_mul, Matrix.mul_sub, Matrix.sub_mul,
            Matrix.mul_assoc]
          abel
        rw [he]
        have he' := (norm_add_le _ _).trans (add_le_add heA'
          ((similarity_isometry J _ hJ).le.trans hA))
        apply he'.trans_eq
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        push_cast
        ring
      · have he : matrix n n (trajectory n a v (k + 1)).2 - W * J =
            (matrix n n (advance n (trajectory n a v k).1 (trajectory n a v k).2).2 -
              matrix n n (trajectory n a v k).2 * J) + (matrix n n (trajectory n a v k).2 - W) * J
                := by
          simp only [trajectory, Matrix.sub_mul]
          abel
        rw [he]
        have he' := (norm_add_le _ _).trans (add_le_add heV
          ((CStarRing.norm_mul_mem_unitary _ hJ).le.trans hV'))
        exact he'.trans_eq (by push_cast; ring)

/-- The coarse enclosure already controls all intermediate operator norms
within a small relative allowance when normalization supplies a norm floor. -/
theorem trajectory_norm_bound (n : Nat) (a v : Array Float) (hn : n ≤ 18)
    (h : State n 0 a v) (hV : matrix n n v = 1) (hfloor : (1 / 2 : ℝ) ≤ ‖matrix n n a‖)
    (k : Nat) (hk : k ≤ 32 * n * n)
    : ‖matrix n n (trajectory n a v k).1‖ ≤ (1001 / 1000 : ℝ) * ‖matrix n n a‖ := by
  obtain ⟨W, hW, hA, _⟩ := JacobiSpectral.trajectory_backward_error n a v hn h hV k hk
  have htri := norm_sub_le_norm_sub_add_norm_sub (matrix n n (trajectory n a v k).1)
    (W.transpose * matrix n n a * W) 0
  simp only [sub_zero, similarity_isometry W _ hW] at htri
  have hn' : (n : ℝ) ≤ 18 := by exact_mod_cast hn
  have hkN : k ≤ 10368 := by nlinarith only [hk, hn]
  have hk' : (k : ℝ) ≤ 10368 := by exact_mod_cast hkN
  have he : (k : ℝ) * (n * (2 : ℝ)^(-33 : Int)) ≤ (1 / 40000 : ℝ) := by
    calc
      _ ≤ 10368 * (18 * (2 : ℝ) ^ (-33 : Int)) := by gcongr
      _ ≤ _ := by norm_num
  have hbound := htri.trans (add_le_add (hA.trans he) le_rfl)
  linarith only [hbound, hfloor]

/-- Energy decrease bounds the squared active-pivot sum relative to the
starting norm throughout the complete diagnostic dimension range. -/
theorem trajectory_pivot_sum_relative_squared (n : Nat) (a v : Array Float) (hn : n ≤ 18)
    (h : State n 0 a v) (hfloor : (1 / 2 : ℝ) ≤ ‖matrix n n a‖)
    (k : Nat) (hk : k ≤ 32 * n * n)
    : (∑ i ∈ Finset.range k, |activePivot n (trajectory n a v i).1|) ^ 2
      ≤ k * (n + 1) * ‖matrix n n a‖ ^ 2 / 2 := by
  have hkN : k ≤ 10368 := by nlinarith only [hk, hn]
  have hk' : (k : ℝ) ≤ 10368 := by exact_mod_cast hkN
  have henergy := (offEnergy_le_energy (matrix n n a)).trans (energy_le_norm (matrix n n a))
  have hround : (k : ℝ) * (2 : ℝ)^(-36 : Int) * 1024 ≤ ‖matrix n n a‖^2 := by
    calc
      _ ≤ 10368 * (2 : ℝ) ^ (-36 : Int) * 1024 := by gcongr
      _ ≤ 1 / 4 := by norm_num
      _ ≤ _ := by nlinarith only [hfloor]
  have hsum := trajectory_pivot_sum n a v hn h k hk
  apply hsum.trans
  calc
    _ ≤ (k : ℝ) * (n * ‖matrix n n a‖ ^ 2 + ‖matrix n n a‖ ^ 2) / 2 := by gcongr
    _ = _ := by ring

/-- On the pseudoinverse dimension range, all active pivots sum to at most
174 times the starting norm. This bound uses actual energy decrease. -/
theorem trajectory_pivot_sum_bound (n : Nat) (a v : Array Float) (hn : n ≤ 12)
    (h : State n 0 a v) (hfloor : (1 / 2 : ℝ) ≤ ‖matrix n n a‖)
    (k : Nat) (hk : k ≤ 32 * n * n)
    : (∑ i ∈ Finset.range k, |activePivot n (trajectory n a v i).1|) ≤ 174 * ‖matrix n n a‖ := by
  have hn' : (n : ℝ) ≤ 12 := by exact_mod_cast hn
  have hkN : k ≤ 4608 := by nlinarith only [hk, hn]
  have hk' : (k : ℝ) ≤ 4608 := by exact_mod_cast hkN
  have hsum := trajectory_pivot_sum_relative_squared n a v (by omega) h hfloor k hk
  apply (sq_le_sq₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)).mp
  apply hsum.trans
  calc
    _ ≤ 4608 * (12 + 1) * ‖matrix n n a‖ ^ 2 / 2 := by gcongr
    _ ≤ _ := by nlinarith only [sq_nonneg ‖matrix n n a‖]

/-- The active pivots of a diagnostic-size trajectory sum to at most
320 times its starting norm, including all eighteen-row execution prefixes. -/
theorem trajectory_pivot_sum_diagnostic (n : Nat) (a v : Array Float) (hn : n ≤ 18)
    (h : State n 0 a v) (hfloor : (1 / 2 : ℝ) ≤ ‖matrix n n a‖)
    (k : Nat) (hk : k ≤ 32 * n * n)
    : (∑ i ∈ Finset.range k, |activePivot n (trajectory n a v i).1|) ≤ 320 * ‖matrix n n a‖ := by
  have hn' : (n : ℝ) ≤ 18 := by exact_mod_cast hn
  have hkN : k ≤ 10368 := by nlinarith only [hk, hn]
  have hk' : (k : ℝ) ≤ 10368 := by exact_mod_cast hkN
  have hsum := trajectory_pivot_sum_relative_squared n a v (by omega) h hfloor k hk
  apply (sq_le_sq₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)).mp
  apply hsum.trans
  calc
    _ ≤ 10368 * (18 + 1) * ‖matrix n n a‖ ^ 2 / 2 := by gcongr
    _ ≤ _ := by nlinarith only [sq_nonneg ‖matrix n n a‖]

/-- Uniform native trajectory error for the pseudoinverse dimension range.
The norm floor is supplied by nonzero input normalization; intermediate success
and accuracy are consequences of the input state, not added assumptions. -/
private theorem trajectory_uniform_error_of_bounds (n : Nat) (a v : Array Float) (hn : n ≤ 18)
    (h : State n 0 a v) (hV : matrix n n v = 1) (hfloor : (1 / 2 : ℝ) ≤ ‖matrix n n a‖) (k : Nat)
    (hk : k ≤ 32 * n * n) (K P ε : ℝ) (hK : (k : ℝ) ≤ K)
    (hP : (∑ i ∈ Finset.range k, |activePivot n (trajectory n a v i).1|) ≤ P * ‖matrix n n a‖)
    (hsmall : K * (64 * n + 13) * (2 : ℝ) ^ (-1022 : Int) ≤ 1 / 2)
    (hcoef
      : 141 * (2 : ℝ) ^ (-53 : Int) * K * (1001 / 1000)
          + (2 : ℝ) ^ (-53 : Int)
          + 512 * (2 : ℝ) ^ (-53 : Int) * P
        ≤ ε)
    : ∃ W : Matrix (Fin n) (Fin n) ℝ,
        W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
        ∧ ‖matrix n n (trajectory n a v k).1 - W.transpose * matrix n n a * W‖ ≤ ε * ‖matrix n n a‖
        ∧ ‖matrix n n (trajectory n a v k).2 - W‖ ≤ k * (97 * (2 : ℝ) ^ (-53 : Int)) := by
  obtain ⟨W, hW, hA, hV'⟩ := trajectory_backward_error n a v (by omega) h hV k hk
  have hsum : (∑ i ∈ Finset.range k, ‖matrix n n (trajectory n a v i).1‖) ≤
      K * ((1001 / 1000 : ℝ) * ‖matrix n n a‖) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range k, (1001 / 1000 : ℝ) * ‖matrix n n a‖ :=
        Finset.sum_le_sum
          fun i hi =>
            trajectory_norm_bound n a v
              (by omega)
              h hV hfloor i
              (by have := Finset.mem_range.mp hi; omega)
      _ = k * ((1001 / 1000 : ℝ) * ‖matrix n n a‖) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hK (by positivity)
  have hsmall' : (k : ℝ) * (64 * n + 13) * (2 : ℝ)^(-1022 : Int) ≤ ‖matrix n n a‖ :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (by positivity)) (by
      positivity)).trans
      (hsmall.trans hfloor)
  have hround : (k : ℝ) * (64 * n + 13) * (2 : ℝ)^(-53 : Int) * (2 : ℝ)^(-1022 : Int) ≤
      (2 : ℝ)^(-53 : Int) * ‖matrix n n a‖ := by
    have he := mul_le_mul_of_nonneg_left hsmall' (show 0 ≤ (2 : ℝ)^(-53 : Int) by positivity)
    calc
      _ = (2 : ℝ) ^ (-53 : Int) * ((k : ℝ) * (64 * n + 13) * (2 : ℝ) ^ (-1022 : Int)) := by ring
      _ ≤ _ := he
  refine ⟨W, hW, ?_, hV'⟩
  apply hA.trans
  have he := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 ≤ 141 * (2 : ℝ)^(-53 : Int))) hround)
    (mul_le_mul_of_nonneg_left hP (by positivity : 0 ≤ 512 * (2 : ℝ)^(-53 : Int)))
  have hb := mul_le_mul_of_nonneg_right hcoef (norm_nonneg (matrix n n a))
  apply he.trans
  convert hb using 1; ring

theorem trajectory_uniform_error_sharp (n : Nat) (a v : Array Float) (hn : n ≤ 12)
    (h : State n 0 a v) (hV : matrix n n v = 1) (hfloor : (1 / 2 : ℝ) ≤ ‖matrix n n a‖)
    (k : Nat) (hk : k ≤ 32 * n * n)
    : ∃ W : Matrix (Fin n) (Fin n) ℝ,
        W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
        ∧ ‖matrix n n (trajectory n a v k).1 - W.transpose * matrix n n a * W‖
          ≤ (83 / 1000000000000 : ℝ) * ‖matrix n n a‖
        ∧ ‖matrix n n (trajectory n a v k).2 - W‖ ≤ k * (97 * (2 : ℝ) ^ (-53 : Int)) := by
  have hnR : (n : ℝ) ≤ 12 := by exact_mod_cast hn
  have hkN : k ≤ 4608 := by nlinarith only [hk, hn]
  apply trajectory_uniform_error_of_bounds n a v (by omega) h hV hfloor k hk 4608 174 _
    (by exact_mod_cast hkN) (trajectory_pivot_sum_bound n a v hn h hfloor k hk)
  · have hη : (2 : ℝ)^(-1022 : Int) ≤ (2 : ℝ)^(-64 : Int) := zpow_le_zpow_right₀ (by norm_num) (by
    norm_num)
    calc
      _ ≤ 4608 * (64 * 12 + 13) * (2 : ℝ) ^ (-64 : Int) := by gcongr
      _ ≤ _ := by norm_num
  · norm_num

theorem trajectory_uniform_error (n : Nat) (a v : Array Float) (hn : n ≤ 12)
    (h : State n 0 a v) (hV : matrix n n v = 1) (hfloor : (1 / 2 : ℝ) ≤ ‖matrix n n a‖)
    (k : Nat) (hk : k ≤ 32 * n * n)
    : ∃ W : Matrix (Fin n) (Fin n) ℝ,
        W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
        ∧ ‖matrix n n (trajectory n a v k).1 - W.transpose * matrix n n a * W‖
          ≤ 3 * (2 : ℝ) ^ (-35 : Int) * ‖matrix n n a‖
        ∧ ‖matrix n n (trajectory n a v k).2 - W‖ ≤ k * (97 * (2 : ℝ) ^ (-53 : Int)) := by
  obtain ⟨W, hW, he, hv⟩ := trajectory_uniform_error_sharp n a v hn h hV hfloor k hk
  refine ⟨W, hW, he.trans ?_, hv⟩
  exact mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _)

/-- Relative spectral enclosure for all native PSD-diagnostic dimensions.
The complete eighteen-row trajectory remains within 2⁻³² of its starting norm. -/
theorem trajectory_diagnostic_error (n : Nat) (a v : Array Float) (hn : n ≤ 18)
    (h : State n 0 a v) (hV : matrix n n v = 1) (hfloor : (1 / 2 : ℝ) ≤ ‖matrix n n a‖)
    (k : Nat) (hk : k ≤ 32 * n * n)
    : ∃ W : Matrix (Fin n) (Fin n) ℝ,
        W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
        ∧ ‖matrix n n (trajectory n a v k).1 - W.transpose * matrix n n a * W‖
          ≤ (2 : ℝ) ^ (-32 : Int) * ‖matrix n n a‖
        ∧ ‖matrix n n (trajectory n a v k).2 - W‖ ≤ k * (97 * (2 : ℝ) ^ (-53 : Int)) := by
  have hnR : (n : ℝ) ≤ 18 := by exact_mod_cast hn
  have hkN : k ≤ 10368 := by nlinarith only [hk, hn]
  apply trajectory_uniform_error_of_bounds n a v (by omega) h hV hfloor k hk 10368 320 _
    (by exact_mod_cast hkN) (trajectory_pivot_sum_diagnostic n a v hn h hfloor k hk)
  · have hη : (2 : ℝ)^(-1022 : Int) ≤ (2 : ℝ)^(-64 : Int) := zpow_le_zpow_right₀ (by norm_num) (by
    norm_num)
    calc
      _ ≤ 10368 * (64 * 18 + 13) * (2 : ℝ) ^ (-64 : Int) := by gcongr
      _ ≤ _ := by norm_num
  · norm_num

end Flare.Matrix.JacobiAccumulation
