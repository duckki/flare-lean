import Flare.Matrix.JacobiConvergence
import Flare.Binary64.Congruence

/-! Establish the native Jacobi invariant from the actual normalization and
identity construction, then compose the bounded-loop success theorem. -/

namespace Flare.Matrix.JacobiInitialization

open Flare.Matrix.Value Flare.Binary64.Value Flare.Matrix.Operations
open Flare.Binary64.Arithmetic Flare.Binary64.Order
open Flare.Matrix.JacobiIteration Flare.Matrix.JacobiBounds Flare.Matrix.JacobiConvergence
open Flare.Analysis.JacobiEnergy

theorem identity_size (n : Nat) : (identity n).size = n * n := by
  simp [Flare.Matrix.Operations.identity, Flare.Matrix.Dense.identity]

theorem identity_finite (n : Nat) : (identity n).all Float.isFinite = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < n * n := by simpa [identity_size] using hi
  simp only [Flare.Matrix.Operations.identity, Flare.Matrix.Dense.identity,
    Array.getElem_map, Array.getElem_range]
  split_ifs <;> decide

theorem identity_entry (n i j : Nat) (hi : i < n) (hj : j < n)
    : entry n (identity n) i j = if i = j then 1.0 else 0.0 := by
  have hn : 0 < n := by omega
  have hidx : i * n + j < n * n := by nlinarith
  have hdiv : (i * n + j) / n = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (i * n + j) % n = j := by simp [Nat.add_mod, Nat.mod_eq_of_lt hj]
  simp [Flare.Matrix.Operations.identity, Flare.Matrix.Dense.identity,
    Flare.Matrix.Operations.entry, Flare.Matrix.Dense.entry,
    hidx, hdiv, hmod]

/-- The native identity array denotes the exact real identity matrix. -/
theorem identity_matrix (n : Nat) : matrix n n (identity n) = 1 := by
  ext i j
  change value (entry n (identity n) i.val j.val) = _
  rw [identity_entry n i.val j.val i.isLt j.isLt]
  by_cases he : i = j
  · subst j; simp [one_value]
  · have hne : i.val ≠ j.val := Fin.val_ne_of_ne he
    simp [hne, he, zero_value]

private theorem identity_energy (n : Nat) : energy (matrix n n (identity n)) = n := by
  rw [identity_matrix]
  simp [energy, Matrix.one_apply]

private theorem energy_le_entries (n : Nat) (A : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hA : ∀ i j, |A i j| ≤ M)
    : energy A ≤ (n : ℝ) ^ 2 * M ^ 2 := by
  have hs : energy A ≤ ∑ _ : Fin n, ∑ _ : Fin n, M^2 := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have h := (sq_le_sq₀ (abs_nonneg (A i j)) hM).mpr (hA i j)
    simpa only [sq_abs] using h
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_two,
    mul_assoc]
    using hs

/-- Actual normalization initializes the full native iteration invariant and
the convergence theorem's off-diagonal energy bound. Symmetry is numerical,
including different encodings of equal signed-zero inputs. -/
theorem normalization_state (n : Nat) (input : Array Float) (hn : 1 ≤ n) (hn' : n ≤ 18)
    (hs : input.size = n * n) (hf : input.all Float.isFinite = true)
    (hsym : ∀ i j, i < n → j < n → value (entry n input i j) = value (entry n input j i))
    (hzero : (maxAbs input == 0.0) = false)
    : ∃ a,
        input.mapM (fun x => finite (x / maxAbs input)) = .ok a
        ∧ State n 0 a (identity n)
        ∧ offEnergy (matrix n n a) ≤ (1001 / 1000 : ℝ) * (n * (n - 1) : Nat) := by
  have hmag := Spectrum.maxAbs_correct input hf
  have hmpos := Spectrum.magnitude_positive input hf hzero
  have hdiv (i : Nat) (hi : i < input.size) := Flare.Binary64.Division.div_error (input.getD i 0.0)
    (maxAbs input) 0
    (Flare.Matrix.Storage.getD_finite _ _ hf) hmag.1 (ne_of_gt hmpos) (by norm_num) (by norm_num)
    (by simpa only [zpow_zero, abs_div, abs_of_pos hmpos] using (div_le_one hmpos).mpr (hmag.2.2 i
      hi))
  have hmap : input.mapM (fun x => finite (x / maxAbs input)) = .ok (input.map (· / maxAbs input))
    := by
    apply Flare.Matrix.Multiplication.mapM_eq_ok_map
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (by simpa using hx)
    have hfin : (input[i] / maxAbs input).isFinite = true := by simpa [hi] using (hdiv i hi).1
    simp only [finite, hfin, ↓reduceIte]
  obtain ⟨a, ha, hsize, hfinite, herror⟩ := Spectrum.normalization_accuracy input hf hzero
  have heq : a = input.map (· / maxAbs input) := Except.ok.inj (ha.symm.trans hmap)
  have hentry (i j : Nat) (hi : i < n) (hj : j < n) :
      entry n a i j = entry n input i j / maxAbs input := by
    have hidx : i * n + j < input.size := by rw [hs]; nlinarith
    rw [heq]
    simp [Flare.Matrix.Operations.entry, Flare.Matrix.Dense.entry, hidx]
  have hab : ∀ i j, i < n → j < n → |value (entry n a i j)| ≤ 1 + (2 : ℝ)^(-51 : Int) := by
    intro i j hi hj
    have hidx : i * n + j < input.size := by rw [hs]; nlinarith
    have he := herror (i * n + j) hidx
    have hq : |value (entry n input i j) / value (maxAbs input)| ≤ 1 := by
      rw [abs_div, abs_of_pos hmpos]
      exact (div_le_one hmpos).mpr (hmag.2.2 (i * n + j) hidx)
    have htri := abs_sub_le (value (entry n a i j)) (value (entry n input i j) / value (maxAbs
      input)) 0
    simp only [sub_zero] at htri
    change |value (entry n a i j) - value (entry n input i j) / value (maxAbs input)| ≤ _ at he
    exact htri.trans ((add_le_add he hq).trans_eq (by ring))
  have hsym' : ∀ i j, i < n → j < n → value (entry n a i j) = value (entry n a j i) := by
    intro i j hi hj
    rw [hentry i j hi hj, hentry j i hj hi]
    exact Flare.Binary64.Congruence.div_value_congr _ _ _ (Flare.Matrix.Storage.getD_finite _ _ hf)
      (Flare.Matrix.Storage.getD_finite _ _ hf) hmag.1 (ne_of_gt hmpos) (hsym i j hi hj)
  have hM : (1 + (2 : ℝ)^(-51 : Int))^2 ≤ (10001 / 10000 : ℝ) := by norm_num
  have hAE := energy_le_entries n (matrix n n a) (1 + (2 : ℝ)^(-51 : Int)) (by positivity)
    (fun i j => hab i.val j.val i.isLt j.isLt)
  have hOE := offEnergy_le_max (matrix n n a) (1 + (2 : ℝ)^(-51 : Int)) (by positivity)
    (fun i j _ => hab i.val j.val i.isLt j.isLt)
  have hnR : (n : ℝ) ≤ 18 := by exact_mod_cast hn'
  have hnR' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨a, ha, ⟨hsize.trans hs, hfinite, identity_size n, identity_finite n, hsym', ?_, ?_⟩, ?_⟩
  · simp only [Nat.cast_zero, zero_mul, add_zero]
    have hmul := mul_le_mul_of_nonneg_left hM (sq_nonneg (n : ℝ))
    exact (hAE.trans hmul).trans (by nlinarith only [hnR, hnR'])
  · simp [identity_energy]
  · rw [Nat.cast_mul, Nat.cast_sub hn, Nat.cast_one]
    have hmul := mul_le_mul_of_nonneg_left hM (show 0 ≤ (n : ℝ) * (n - 1) by nlinarith)
    exact (hOE.trans hmul).trans (by nlinarith only [hnR', sq_nonneg (n : ℝ)])

/-- The complete native eigensolver succeeds for finite symmetric matrices of
one to eighteen rows with entries bounded by `2⁵⁰⁰`. This includes zero input,
normalization, every pivot/rotation, the rotation cap and final rescaling.
It proves finite spectrum storage; spectral approximation is a separate claim. -/
theorem jacobiEigen_success (n : Nat) (input : Array Float) (hn : 1 ≤ n) (hn' : n ≤ 18)
    (hs : input.size = n * n) (hf : input.all Float.isFinite = true)
    (hsym : ∀ i j, i < n → j < n → value (entry n input i j) = value (entry n input j i))
    (hb : ∀ i, i < input.size → |value (input.getD i 0.0)| ≤ (2 : ℝ) ^ (500 : Int))
    : ∃ result, jacobiEigen n input = .ok result ∧ Stored n result := by
  by_cases hzero : (maxAbs input == 0.0) = true
  · refine ⟨⟨Array.replicate n 0.0, identity n⟩, ?_, ⟨by simp, ?_, identity_size n, identity_finite
    n⟩⟩
    · rw [jacobiEigen_eq, jacobiBySteps_eq]
      simp only [hzero, ↓reduceIte, pure, Except.pure]
    · rw [Array.all_eq_true]
      intro i hi
      simpa only [Array.getElem_replicate] using (show (0.0 : Float).isFinite = true by decide)
  · have hzero' : (maxAbs input == 0.0) = false := Bool.eq_false_iff.mpr hzero
    obtain ⟨a, hmap, hstate, hstart⟩ := normalization_state n input hn hn' hs hf hsym hzero'
    have hm := Spectrum.maxAbs_correct input hf
    have hmb : |value (maxAbs input)| ≤ (2 : ℝ)^(500 : Int) := by
      rw [abs_of_nonneg hm.2.1]
      exact Spectrum.maxAbs_le input _ hf (by positivity) hb
    obtain ⟨result, he, hstored⟩ := iterations_success n (maxAbs input) a (identity n)
      hn hn' hm.1 hmb hstate hstart
    refine ⟨result, ?_, hstored⟩
    rw [jacobiEigen_eq, jacobiBySteps_eq]
    simp only [hzero', Bool.false_eq_true, ↓reduceIte, hmap, bind, Except.bind]
    exact he

end Flare.Matrix.JacobiInitialization
