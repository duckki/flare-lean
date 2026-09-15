import Flare.Matrix.JacobiSpectral
import Flare.Matrix.JacobiInitialization
import Flare.Matrix.JacobiAccumulation

/-! Spectral enclosures for the native eigensolver's returned storage. These
compose the stopped trajectory with final eigenvalue rescaling. Separate
uniform bounds cover the pseudoinverse and covariance-diagnostic dimensions. -/

namespace Flare.Matrix.JacobiOutput
open Flare.Matrix.Value Flare.Binary64.Value Flare.Matrix.Operations
open Flare.Binary64.Arithmetic Flare.Binary64.Order
open Flare.Matrix.JacobiConvergence Flare.Matrix.JacobiBounds
open Flare.Matrix.JacobiSpectral Flare.Analysis.SpectralPerturbation
open scoped Matrix.Norms.L2Operator

/-- Real diagonal matrix represented by the returned native eigenvalue array. -/
noncomputable def spectrumDiagonal (n : Nat) (result : Spectrum) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => value (result.values.getD i.val 0.0))

/-- The actual stopping test bounds the remaining off-diagonal matrix in
operator norm. The bound uses the exact real value of the native threshold. -/
theorem stopped_diagonal_error (n : Nat) (a : Array Float)
    (ha : a.all Float.isFinite = true)
    (hsym : ∀ i j, i < n → j < n → value (entry n a i j) = value (entry n a j i))
    (hstop : (selectedPivot n a).magnitude ≤ (1.0e-14 : Float))
    : ‖matrix n n a - Matrix.diagonal (fun i => matrix n n a i i)‖
      ≤ n * value (1.0e-14 : Float) := by
  obtain ⟨pivot, he, hf, _, _, hmax⟩ := JacobiIteration.largestPivot_correct n a ha
  have hp : selectedPivot n a = pivot := by simp only [selectedPivot, he]
  rw [hp] at hstop
  have hm := (le_iff _ _ hf (by decide)).mp hstop
  have hε : 0 ≤ value (1.0e-14 : Float) :=
    (show 0 ≤ (2 : ℝ)^(-47 : Int) by positivity).trans Jacobi.stopping_threshold_bounds.1
  apply norm_le_entries _ _ hε
  intro i j
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.sub_apply, Matrix.diagonal_apply_eq, sub_self, abs_zero] using hε
  · simp only [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij, sub_zero]
    change |value (entry n a i.val j.val)| ≤ _
    by_cases hlt : i.val < j.val
    · exact (hmax i.val j.val hlt j.isLt).trans hm
    · rw [hsym i.val j.val i.isLt j.isLt]
      exact (hmax j.val i.val (by have hn := Fin.val_ne_of_ne hij; omega) i.isLt).trans hm

/-- Rescaling rounds each diagonal entry once. The final spectrum keeps the
trajectory's eigenvectors exactly. Underflow is retained explicitly. -/
theorem finish_rescaling (n : Nat) (magnitude : Float) (a v : Array Float)
    (hm : magnitude.isFinite = true) (hmb : |value magnitude| ≤ (2 : ℝ)^(500 : Int))
    (ha : a.all Float.isFinite = true)
    (hE : Flare.Analysis.JacobiEnergy.energy (matrix n n a) ≤ 1024) (hvs : v.size = n * n)
    (hv : v.all Float.isFinite = true)
    : ∃ result,
        finish n magnitude a v = .ok result
        ∧ Stored n result
        ∧ result.vectors = v
        ∧ ‖spectrumDiagonal n result
            - value magnitude • Matrix.diagonal (fun i => matrix n n a i i)‖
          ≤ (2 : ℝ)^(-51 : Int) * (32 * |value magnitude| + (2 : ℝ)^(-1022 : Int)) := by
  obtain ⟨result, he, hstored, hvec, hdiag⟩ := finish_entries n magnitude a v hm hmb ha hE hvs hv
  refine ⟨result, he, hstored, hvec, ?_⟩
  have hδ : 0 ≤ (2 : ℝ)^(-51 : Int) * (32 * |value magnitude| + (2 : ℝ)^(-1022 : Int)) := by
    positivity
  have hbound := entries_of_energy n a hE
  have herr (i : Fin n) :
      |value (result.values.getD i.val 0.0) - value magnitude * matrix n n a i i| ≤
        (2 : ℝ)^(-51 : Int) * (32 * |value magnitude| + (2 : ℝ)^(-1022 : Int)) := by
    have hprod : |value (entry n a i.val i.val) * value magnitude| ≤ 32 * |value magnitude| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hbound i.val i.val i.isLt i.isLt) (abs_nonneg _)
    have hlarge : 32 * |value magnitude| ≤ (2 : ℝ)^(1000 : Int) := by
      calc
        _ ≤ 32 * (2 : ℝ)^(500 : Int) := mul_le_mul_of_nonneg_left hmb (by norm_num)
        _ = (2 : ℝ)^(505 : Int) := by
          rw [show (505 : Int) = 5 + 500 by rfl, zpow_add₀ (by norm_num)]; norm_num
        _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
    have herr := (mul_error_relative (entry n a i.val i.val) magnitude
      (Flare.Matrix.Storage.getD_finite _ _ ha) hm (hprod.trans hlarge)).2
    rw [hdiag i.val i.isLt]
    change |value (entry n a i.val i.val * magnitude) - value magnitude * value (entry n a i.val
      i.val)| ≤ _
    rw [mul_comm (value magnitude)]
    exact herr.trans (mul_le_mul_of_nonneg_left (add_le_add hprod le_rfl) (by positivity))
  have heq : spectrumDiagonal n result - value magnitude • Matrix.diagonal (fun i => matrix n n a i
    i) =
      Matrix.diagonal (fun i => value (result.values.getD i.val 0.0) - value magnitude * matrix n n
        a i i) := by
    ext i j
    by_cases hij : i = j <;> simp [spectrumDiagonal, hij]
  rw [heq, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hδ).mpr (fun i => by simpa only [Real.norm_eq_abs] using herr i)

/-- The returned spectrum of the normalized loop has an orthogonal reference,
a diagonalization enclosure and an eigenvector enclosure. The rotation errors,
stopping tolerance and final multiplication error remain separate. -/
private theorem iterations_spectral_of_trajectory (n : Nat) (magnitude : Float) (a v : Array Float)
    (hn : 1 ≤ n) (hn' : n ≤ 18)
    (hm : magnitude.isFinite = true) (hmb : |value magnitude| ≤ (2 : ℝ)^(500 : Int))
    (hstate : State n 0 a v) (_hV : matrix n n v = 1)
    (hstart
      : Flare.Analysis.JacobiEnergy.offEnergy (matrix n n a)
        ≤ (1001 / 1000 : ℝ) * (n * (n - 1) : Nat))
    (δ δV : ℝ) (hδV : 0 ≤ δV)
    (htrajectory
      : ∀ k,
          k ≤ 32 * n * n
          → ∃ W : Matrix (Fin n) (Fin n) ℝ,
              W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
              ∧ ‖matrix n n (trajectory n a v k).1 - W.transpose * matrix n n a * W‖ ≤ δ
              ∧ ‖matrix n n (trajectory n a v k).2 - W‖ ≤ k * δV)
    : ∃ result,
        iterations n magnitude a v = .ok result
        ∧ Stored n result
        ∧ ∃ W : Matrix (Fin n) (Fin n) ℝ,
            W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
            ∧ ‖spectrumDiagonal n result - W.transpose * (value magnitude • matrix n n a) * W‖
              ≤ |value magnitude| * (δ + n * value (1.0e-14 : Float))
                + (2 : ℝ)^(-51 : Int) * (32 * |value magnitude| + (2 : ℝ)^(-1022 : Int))
            ∧ ‖matrix n n result.vectors - W‖ ≤ (32 * n * n : Nat) * δV := by
  obtain ⟨result, he, hstored, k, hk, hstop, hfinish⟩ := iterations_trace n magnitude a v hn hn' hm
    hmb hstate hstart
  have hcurrent := trajectory_state n a v hn' hstate k hk.le
  have hE := state_energy_bound n k _ _ hn' hk.le hcurrent
  obtain ⟨finished, hfinished, _, hvec, hscale⟩ := finish_rescaling n magnitude _ _ hm hmb
    hcurrent.matrix_finite hE.1 hcurrent.vectors_size hcurrent.vectors_finite
  rw [hfinish] at hfinished
  have hres : finished = result := (Except.ok.inj hfinished).symm
  subst finished
  obtain ⟨W, hW, hA', hV'⟩ := htrajectory k hk.le
  have hdiag := stopped_diagonal_error n _ hcurrent.matrix_finite hcurrent.symmetric hstop
  have hk' : (k : ℝ) ≤ (32 * n * n : Nat) := by exact_mod_cast hk.le
  have hV'' := hV'.trans (mul_le_mul_of_nonneg_right hk' hδV)
  refine ⟨result, he, hstored, W, hW, ?_, ?_⟩
  · let D := Matrix.diagonal (fun i => matrix n n (trajectory n a v k).1 i i)
    have hsum : ‖D - W.transpose * matrix n n a * W‖ ≤
        δ + n * value (1.0e-14 : Float) := by
      have hdiag' : ‖D - matrix n n (trajectory n a v k).1‖ ≤ n * value (1.0e-14 : Float) := by
        rw [norm_sub_rev]
        exact hdiag
      have h := (norm_sub_le_norm_sub_add_norm_sub D (matrix n n (trajectory n a v k).1) _).trans
        (add_le_add hdiag' hA')
      simpa only [add_comm] using h
    have hid : spectrumDiagonal n result - W.transpose * (value magnitude • matrix n n a) * W =
        (spectrumDiagonal n result - value magnitude • D) +
          value magnitude • (D - W.transpose * matrix n n a * W) := by
      simp only [smul_sub, Matrix.mul_smul, Matrix.smul_mul]
      abel
    rw [hid]
    have hscaled : ‖value magnitude • (D - W.transpose * matrix n n a * W)‖ ≤
        |value magnitude| * (δ + n * value (1.0e-14 : Float)) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    exact ((norm_add_le _ _).trans (add_le_add hscale hscaled)).trans_eq (by ring)
  · rw [hvec]
    exact hV''

/-- Coarse enclosure of the returned normalized spectrum. -/
theorem iterations_spectral (n : Nat) (magnitude : Float) (a v : Array Float)
    (hn : 1 ≤ n) (hn' : n ≤ 18)
    (hm : magnitude.isFinite = true) (hmb : |value magnitude| ≤ (2 : ℝ)^(500 : Int))
    (hstate : State n 0 a v) (hV : matrix n n v = 1)
    (hstart
      : Flare.Analysis.JacobiEnergy.offEnergy (matrix n n a)
        ≤ (1001 / 1000 : ℝ) * (n * (n - 1) : Nat))
    : ∃ result,
        iterations n magnitude a v = .ok result
        ∧ Stored n result
        ∧ ∃ W : Matrix (Fin n) (Fin n) ℝ,
            W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
            ∧ ‖spectrumDiagonal n result - W.transpose * (value magnitude • matrix n n a) * W‖
              ≤ |value magnitude|
                  * ((32 * n * n : Nat) * (n * (2 : ℝ)^(-33 : Int)) + n * value (1.0e-14 : Float))
                + (2 : ℝ)^(-51 : Int) * (32 * |value magnitude| + (2 : ℝ)^(-1022 : Int))
            ∧ ‖matrix n n result.vectors - W‖
              ≤ (32 * n * n : Nat) * (n * ((2 : ℝ)^(-48 : Int) * 65)) := by
  apply iterations_spectral_of_trajectory n magnitude a v hn hn' hm hmb hstate hV hstart _ _
    (by positivity)
  intro k hk
  obtain ⟨W, hW, hA, hV'⟩ := trajectory_backward_error n a v hn' hstate hV k hk
  refine ⟨W, hW, ?_, hV'⟩
  exact hA.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity))

/-- Sharper returned-spectrum enclosure on the pseudoinverse dimension range,
including the actual stopping test and native eigenvalue rescaling. -/
theorem iterations_spectral_uniform (n : Nat) (magnitude : Float) (a v : Array Float)
    (hn : 1 ≤ n) (hn' : n ≤ 12)
    (hm : magnitude.isFinite = true) (hmb : |value magnitude| ≤ (2 : ℝ)^(500 : Int))
    (hstate : State n 0 a v) (hV : matrix n n v = 1)
    (hstart
      : Flare.Analysis.JacobiEnergy.offEnergy (matrix n n a)
        ≤ (1001 / 1000 : ℝ) * (n * (n - 1) : Nat))
    (hfloor : (1 / 2 : ℝ) ≤ ‖matrix n n a‖)
    : ∃ result,
        iterations n magnitude a v = .ok result
        ∧ Stored n result
        ∧ ∃ W : Matrix (Fin n) (Fin n) ℝ,
            W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
            ∧ ‖spectrumDiagonal n result - W.transpose * (value magnitude • matrix n n a) * W‖
              ≤ |value magnitude|
                  * (3 * (2 : ℝ)^(-35 : Int) * ‖matrix n n a‖ + n * value (1.0e-14 : Float))
                + (2 : ℝ)^(-51 : Int) * (32 * |value magnitude| + (2 : ℝ)^(-1022 : Int))
            ∧ ‖matrix n n result.vectors - W‖
              ≤ (32 * n * n : Nat) * (97 * (2 : ℝ)^(-53 : Int)) := by
  apply iterations_spectral_of_trajectory n magnitude a v hn (by omega) hm hmb hstate hV hstart _ _
    (by positivity)
  intro k hk
  exact JacobiAccumulation.trajectory_uniform_error n a v hn' hstate hV hfloor k hk

/-- Native normalization, expressed as a backward error in the original input
scale. The normalized entries and their rescaling use real arithmetic here;
the final native rescaling is covered separately by finish_rescaling. -/
theorem normalization_rescaling (n : Nat) (input a : Array Float)
    (hs : input.size = n * n) (hf : input.all Float.isFinite = true)
    (hzero : (maxAbs input == 0.0) = false)
    (hmap : input.mapM (fun x => finite (x / maxAbs input)) = .ok a)
    : ‖value (maxAbs input) • matrix n n a - matrix n n input‖
      ≤ n * (|value (maxAbs input)| * (2 : ℝ)^(-51 : Int)) := by
  obtain ⟨normalized, he, _, _, herr⟩ := Spectrum.normalization_accuracy input hf hzero
  rw [hmap] at he
  have heq : normalized = a := (Except.ok.inj he).symm
  subst normalized
  have hm := Spectrum.magnitude_positive input hf hzero
  apply norm_le_entries _ _ (by positivity)
  intro i j
  have hidx : i.val * n + j.val < input.size := by rw [hs]; nlinarith [i.isLt, j.isLt]
  have hentry := herr (i.val * n + j.val) hidx
  change |matrix n n a i j - matrix n n input i j / value (maxAbs input)| ≤ _ at hentry
  have hid : value (maxAbs input) * matrix n n a i j - matrix n n input i j =
      value (maxAbs input) * (matrix n n a i j - matrix n n input i j / value (maxAbs input)) := by
    field_simp
  change |value (maxAbs input) * matrix n n a i j - matrix n n input i j| ≤ _
  rw [hid, abs_mul]
  exact mul_le_mul_of_nonneg_left hentry (abs_nonneg _)

/-- The native normalization scale is bounded by the input operator norm. -/
theorem magnitude_le_norm (n : Nat) (input : Array Float) (hn : 1 ≤ n)
    (hs : input.size = n * n) (hf : input.all Float.isFinite = true)
    : value (maxAbs input) ≤ ‖matrix n n input‖ := by
  apply Spectrum.maxAbs_le input _ hf (norm_nonneg _)
  intro i hi
  have hnp : 0 < n := by omega
  have hp : i / n < n := (Nat.div_lt_iff_lt_mul hnp).mpr (by simpa only [hs] using hi)
  have hq : i % n < n := Nat.mod_lt i hnp
  have he : i / n * n + i % n = i := by
    simpa only [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div i n
  have h := entry_le_norm (matrix n n input) ⟨i / n, hp⟩ ⟨i % n, hq⟩
  change |value (input.getD (i / n * n + i % n) 0.0)| ≤ _ at h
  rwa [he] at h

/-- A nonzero normalized input has operator norm at least one half, and its
rescaled norm differs from the original input norm by only normalization error.
This derives the floor needed by the uniform trajectory bound from input data. -/
theorem normalization_norm_bounds (n : Nat) (input a : Array Float) (hn : 1 ≤ n) (hn' : n ≤ 18)
    (hs : input.size = n * n) (hf : input.all Float.isFinite = true)
    (hzero : (maxAbs input == 0.0) = false)
    (hmap : input.mapM (fun x => finite (x / maxAbs input)) = .ok a)
    : (1 / 2 : ℝ) ≤ ‖matrix n n a‖
      ∧ value (maxAbs input) * ‖matrix n n a‖
        ≤ (1 + n * (2 : ℝ)^(-51 : Int)) * ‖matrix n n input‖ := by
  have hm := Spectrum.magnitude_positive input hf hzero
  have hscale := magnitude_le_norm n input hn hs hf
  have he := normalization_rescaling n input a hs hf hzero hmap
  rw [abs_of_pos hm] at he
  have htri := norm_sub_le_norm_sub_add_norm_sub (matrix n n input)
    (value (maxAbs input) • matrix n n a) 0
  have htri' := norm_sub_le_norm_sub_add_norm_sub (value (maxAbs input) • matrix n n a)
    (matrix n n input) 0
  simp only [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hm] at htri htri'
  rw [norm_sub_rev] at htri
  have hnorm := hscale.trans (htri.trans (add_le_add he le_rfl))
  have hnorm' := htri'.trans (add_le_add he le_rfl)
  refine ⟨?_, ?_⟩
  · have hnR : (n : ℝ) ≤ 18 := by exact_mod_cast hn'
    have hsmall : (n : ℝ) * (2 : ℝ)^(-51 : Int) ≤ 1 / 2 := by
      exact (mul_le_mul_of_nonneg_right hnR (by positivity)).trans (by norm_num)
    have hl : 1 ≤ (n : ℝ) * (2 : ℝ)^(-51 : Int) + ‖matrix n n a‖ := by
      apply (mul_le_mul_iff_right₀ hm).mp
      nlinarith only [hnorm]
    calc
      (1 / 2 : ℝ) = 1 - 1 / 2 := by norm_num
      _ ≤ 1 - (n : ℝ) * (2 : ℝ)^(-51 : Int) := sub_le_sub_left hsmall 1
      _ ≤ _ := sub_le_iff_le_add.mpr (by simpa only [add_comm] using hl)
  · have hb := mul_le_mul_of_nonneg_left hscale
      (show 0 ≤ (n : ℝ) * (2 : ℝ)^(-51 : Int) by positivity)
    nlinarith only [hnorm', hb]

/-- The returned native spectrum has an exact orthogonal reference and a
coarse backward-error enclosure relative to the original input matrix. This
includes zero input, normalization, every rotation, early return and rescaling.
The bound is not tight enough to prove the native rank threshold correct. -/
theorem jacobiEigen_spectral (n : Nat) (input : Array Float) (hn : 1 ≤ n) (hn' : n ≤ 18)
    (hs : input.size = n * n) (hf : input.all Float.isFinite = true)
    (hsym : ∀ i j, i < n → j < n → value (entry n input i j) = value (entry n input j i))
    (hb : ∀ i, i < input.size → |value (input.getD i 0.0)| ≤ (2 : ℝ)^(500 : Int))
    : ∃ result,
        jacobiEigen n input = .ok result
        ∧ Stored n result
        ∧ ∃ W : Matrix (Fin n) (Fin n) ℝ,
            W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
            ∧ ‖spectrumDiagonal n result - W.transpose * matrix n n input * W‖
              ≤ |value (maxAbs input)|
                  * ((32 * n * n : Nat) * (n * (2 : ℝ)^(-33 : Int))
                      + n * value (1.0e-14 : Float)
                      + (n + 32) * (2 : ℝ)^(-51 : Int))
                + (2 : ℝ)^(-51 : Int) * (2 : ℝ)^(-1022 : Int)
            ∧ ‖matrix n n result.vectors - W‖
              ≤ (32 * n * n : Nat) * (n * ((2 : ℝ)^(-48 : Int) * 65)) := by
  have hm := Spectrum.maxAbs_correct input hf
  by_cases hzero : (maxAbs input == 0.0) = true
  · obtain ⟨result, he, hstored⟩ := JacobiInitialization.jacobiEigen_success n input hn hn' hs hf
      hsym hb
    have heq : result = ⟨Array.replicate n 0.0, identity n⟩ := by
      have hresult := he
      rw [JacobiIteration.jacobiEigen_eq, jacobiBySteps_eq] at hresult
      simpa only [hzero, ↓reduceIte, pure, Except.pure, Except.ok.injEq] using hresult.symm
    subst result
    have hmzero : value (maxAbs input) = 0 := by
      simpa only [zero_value] using (beq_iff _ _ hm.1 (by decide)).mp hzero
    have hinput : matrix n n input = 0 := by
      ext i j
      have hidx : i.val * n + j.val < input.size := by rw [hs]; nlinarith [i.isLt, j.isLt]
      have hb' := hm.2.2 (i.val * n + j.val) hidx
      rw [hmzero] at hb'
      exact abs_nonpos_iff.mp hb'
    have hdiag : spectrumDiagonal n ⟨Array.replicate n 0.0, identity n⟩ = 0 := by
      ext i j
      simp [spectrumDiagonal, zero_value]
    refine ⟨_, he, hstored, 1, (unitary _).one_mem, ?_, ?_⟩
    · rw [hdiag, hinput, hmzero]
      simp only [Matrix.transpose_one, Matrix.one_mul, sub_self, norm_zero,
        abs_zero, zero_mul, zero_add]
      positivity
    · change ‖matrix n n (identity n) - 1‖ ≤ _
      rw [JacobiInitialization.identity_matrix, sub_self, norm_zero]
      positivity
  · have hz : (maxAbs input == 0.0) = false := Bool.eq_false_iff.mpr hzero
    obtain ⟨a, hmap, hstate, hstart⟩ := JacobiInitialization.normalization_state n input hn hn' hs
      hf hsym hz
    have hmb : |value (maxAbs input)| ≤ (2 : ℝ)^(500 : Int) := by
      rw [abs_of_nonneg hm.2.1]
      exact Spectrum.maxAbs_le input _ hf (by positivity) hb
    obtain ⟨result, he, hstored, W, hW, hA, hV⟩ := iterations_spectral n (maxAbs input) a (identity
      n)
      hn hn' hm.1 hmb hstate (JacobiInitialization.identity_matrix n) hstart
    refine ⟨result, ?_, hstored, W, hW, ?_, hV⟩
    · rw [JacobiIteration.jacobiEigen_eq, jacobiBySteps_eq]
      simp only [hz, Bool.false_eq_true, ↓reduceIte, hmap, bind, Except.bind]
      exact he
    · have hnorm := normalization_rescaling n input a hs hf hz hmap
      have hdiff : W.transpose * (value (maxAbs input) • matrix n n a) * W - W.transpose * matrix n
        n input * W =
          W.transpose * (value (maxAbs input) • matrix n n a - matrix n n input) * W := by
        simp only [Matrix.mul_sub, Matrix.sub_mul]
      have hsim : ‖W.transpose * (value (maxAbs input) • matrix n n a) * W - W.transpose * matrix n
        n input * W‖ ≤
          n * (|value (maxAbs input)| * (2 : ℝ)^(-51 : Int)) := by
        rw [hdiff, similarity_isometry W _ hW]
        exact hnorm
      exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hA hsim)).trans_eq (by
        ring)

private theorem jacobiEigen_spectral_of_trajectory (n : Nat) (input : Array Float) (hn : 1 ≤ n)
    (hn' : n ≤ 18) (hs : input.size = n * n) (hf : input.all Float.isFinite = true)
    (hsym : ∀ i j, i < n → j < n → value (entry n input i j) = value (entry n input j i))
    (hb : ∀ i, i < input.size → |value (input.getD i 0.0)| ≤ (2 : ℝ)^(500 : Int)) (δ ε : ℝ)
    (hδ : 0 ≤ δ)
    (hcoef
      : δ * (1 + n * (2 : ℝ)^(-51 : Int))
          + (n * value (1.0e-14 : Float) + (n + 32) * (2 : ℝ)^(-51 : Int))
        ≤ ε)
    (htrajectory
      : ∀ a v,
          State n 0 a v
          → matrix n n v = 1
          → (1 / 2 : ℝ) ≤ ‖matrix n n a‖
          → ∀ k,
              k ≤ 32 * n * n
              → ∃ W : Matrix (Fin n) (Fin n) ℝ,
                  W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
                  ∧ ‖matrix n n (trajectory n a v k).1 - W.transpose * matrix n n a * W‖
                    ≤ δ * ‖matrix n n a‖
                  ∧ ‖matrix n n (trajectory n a v k).2 - W‖ ≤ k * (97 * (2 : ℝ)^(-53 : Int)))
    : ∃ result,
        jacobiEigen n input = .ok result
        ∧ Stored n result
        ∧ ∃ W : Matrix (Fin n) (Fin n) ℝ,
            W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
            ∧ ‖spectrumDiagonal n result - W.transpose * matrix n n input * W‖
              ≤ ε * ‖matrix n n input‖ + (2 : ℝ)^(-51 : Int) * (2 : ℝ)^(-1022 : Int)
            ∧ ‖matrix n n result.vectors - W‖
              ≤ (32 * n * n : Nat) * (97 * (2 : ℝ)^(-53 : Int)) := by
  have hm := Spectrum.maxAbs_correct input hf
  by_cases hzero : (maxAbs input == 0.0) = true
  · obtain ⟨result, he, hstored⟩ := JacobiInitialization.jacobiEigen_success n input hn (by omega)
      hs hf hsym hb
    have heq : result = ⟨Array.replicate n 0.0, identity n⟩ := by
      have hresult := he
      rw [JacobiIteration.jacobiEigen_eq, jacobiBySteps_eq] at hresult
      simpa only [hzero, ↓reduceIte, pure, Except.pure, Except.ok.injEq] using hresult.symm
    subst result
    have hmzero : value (maxAbs input) = 0 := by
      simpa only [zero_value] using (beq_iff _ _ hm.1 (by decide)).mp hzero
    have hinput : matrix n n input = 0 := by
      ext i j
      have hidx : i.val * n + j.val < input.size := by rw [hs]; nlinarith [i.isLt, j.isLt]
      have hb' := hm.2.2 (i.val * n + j.val) hidx
      rw [hmzero] at hb'
      exact abs_nonpos_iff.mp hb'
    have hdiag : spectrumDiagonal n ⟨Array.replicate n 0.0, identity n⟩ = 0 := by
      ext i j
      simp [spectrumDiagonal, zero_value]
    refine ⟨_, he, hstored, 1, (unitary _).one_mem, ?_, ?_⟩
    · rw [hdiag, hinput]
      simp only [Matrix.transpose_one, Matrix.zero_mul, sub_self, norm_zero, mul_zero, zero_add]
      positivity
    · change ‖matrix n n (identity n) - 1‖ ≤ _
      rw [JacobiInitialization.identity_matrix, sub_self, norm_zero]
      positivity
  · have hz : (maxAbs input == 0.0) = false := Bool.eq_false_iff.mpr hzero
    obtain ⟨a, hmap, hstate, hstart⟩ := JacobiInitialization.normalization_state n input hn (by
      omega) hs hf hsym hz
    have hmpos := Spectrum.magnitude_positive input hf hz
    have hmb : |value (maxAbs input)| ≤ (2 : ℝ)^(500 : Int) := by
      rw [abs_of_pos hmpos]
      exact Spectrum.maxAbs_le input _ hf (by positivity) hb
    have hnorms := normalization_norm_bounds n input a hn (by omega) hs hf hz hmap
    obtain ⟨result, he, hstored, W, hW, hA, hV⟩ := iterations_spectral_of_trajectory n (maxAbs
      input) a (identity n)
      hn hn' hm.1 hmb hstate (JacobiInitialization.identity_matrix n) hstart
      (δ * ‖matrix n n a‖) (97 * (2 : ℝ)^(-53 : Int)) (by positivity)
      (htrajectory a (identity n) hstate (JacobiInitialization.identity_matrix n) hnorms.1)
    refine ⟨result, ?_, hstored, W, hW, ?_, hV⟩
    · rw [JacobiIteration.jacobiEigen_eq, jacobiBySteps_eq]
      simp only [hz, Bool.false_eq_true, ↓reduceIte, hmap, bind, Except.bind]
      exact he
    · have hnorm := normalization_rescaling n input a hs hf hz hmap
      have hsim : ‖W.transpose * (value (maxAbs input) • matrix n n a) * W - W.transpose * matrix n
        n input * W‖ ≤
          n * (|value (maxAbs input)| * (2 : ℝ)^(-51 : Int)) := by
        rw [show W.transpose * (value (maxAbs input) • matrix n n a) * W - W.transpose * matrix n n
          input * W =
          W.transpose * (value (maxAbs input) • matrix n n a - matrix n n input) * W by
            simp only [Matrix.mul_sub, Matrix.sub_mul], similarity_isometry W _ hW]
        exact hnorm
      have htri := (norm_sub_le_norm_sub_add_norm_sub (spectrumDiagonal n result)
        (W.transpose * (value (maxAbs input) • matrix n n a) * W) (W.transpose * matrix n n input *
          W)).trans
        (add_le_add hA hsim)
      rw [abs_of_pos hmpos] at htri
      have hscale := magnitude_le_norm n input hn hs hf
      have ht0 : 0 ≤ value (1.0e-14 : Float) :=
        (show 0 ≤ (2 : ℝ)^(-47 : Int) by positivity).trans Jacobi.stopping_threshold_bounds.1
      apply htri.trans
      calc
        _ = δ * (value (maxAbs input) * ‖matrix n n a‖)
            + value (maxAbs input) * (n * value (1.0e-14 : Float) + (n + 32) * (2 : ℝ)^(-51 : Int))
            + (2 : ℝ)^(-51 : Int) * (2 : ℝ)^(-1022 : Int) := by
          ring
        _ ≤ δ * ((1 + n * (2 : ℝ)^(-51 : Int)) * ‖matrix n n input‖)
            + ‖matrix n n input‖ * (n * value (1.0e-14 : Float) + (n + 32) * (2 : ℝ)^(-51 : Int))
            + (2 : ℝ)^(-51 : Int) * (2 : ℝ)^(-1022 : Int) :=
          add_le_add
            (add_le_add (mul_le_mul_of_nonneg_left hnorms.2 (by positivity))
              (mul_le_mul_of_nonneg_right hscale (by positivity)))
            le_rfl
        _ = (δ * (1 + n * (2 : ℝ)^(-51 : Int))
                + (n * value (1.0e-14 : Float) + (n + 32) * (2 : ℝ)^(-51 : Int)))
              * ‖matrix n n input‖
            + (2 : ℝ)^(-51 : Int) * (2 : ℝ)^(-1022 : Int) := by
          ring
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)) le_rfl

/-- A uniform enclosure for the actual returned spectrum on the pseudoinverse
dimension range. It includes zero input, normalization, all rotations, early
stopping and final binary64 rescaling. The absolute term covers underflow. -/
theorem jacobiEigen_spectral_sharp (n : Nat) (input : Array Float) (hn : 1 ≤ n) (hn' : n ≤ 12)
    (hs : input.size = n * n) (hf : input.all Float.isFinite = true)
    (hsym : ∀ i j, i < n → j < n → value (entry n input i j) = value (entry n input j i))
    (hb : ∀ i, i < input.size → |value (input.getD i 0.0)| ≤ (2 : ℝ)^(500 : Int))
    : ∃ result,
        jacobiEigen n input = .ok result
        ∧ Stored n result
        ∧ ∃ W : Matrix (Fin n) (Fin n) ℝ,
            W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
            ∧ ‖spectrumDiagonal n result - W.transpose * matrix n n input * W‖
              ≤ (84 / 1000000000000 : ℝ) * ‖matrix n n input‖
                + (2 : ℝ)^(-51 : Int) * (2 : ℝ)^(-1022 : Int)
            ∧ ‖matrix n n result.vectors - W‖
              ≤ (32 * n * n : Nat) * (97 * (2 : ℝ)^(-53 : Int)) := by
  apply jacobiEigen_spectral_of_trajectory n input hn (by omega) hs hf hsym hb
    ((83 / 1000000000000 : ℝ)) _ (by positivity)
  · have hnR : (n : ℝ) ≤ 12 := by exact_mod_cast hn'
    have ht : value (1.0e-14 : Float) ≤ (2 : ℝ)^(-46 : Int) := by
      change 6338253001141147 * (2 : ℝ)^(-99 : Int) ≤ (2 : ℝ)^(-46 : Int)
      norm_num
    have ht0 : 0 ≤ value (1.0e-14 : Float) :=
      (show 0 ≤ (2 : ℝ)^(-47 : Int) by positivity).trans Jacobi.stopping_threshold_bounds.1
    calc
      _ ≤ ((83 / 1000000000000 : ℝ)) * (1 + 12 * (2 : ℝ)^(-51 : Int))
          + (12 * (2 : ℝ)^(-46 : Int) + (12 + 32) * (2 : ℝ)^(-51 : Int)) := by
        gcongr
      _ ≤ _ := by norm_num
  · intro a v hstate hV hfloor k hk
    exact JacobiAccumulation.trajectory_uniform_error_sharp n a v hn' hstate hV hfloor k hk

theorem jacobiEigen_spectral_uniform (n : Nat) (input : Array Float) (hn : 1 ≤ n) (hn' : n ≤ 12)
    (hs : input.size = n * n) (hf : input.all Float.isFinite = true)
    (hsym : ∀ i j, i < n → j < n → value (entry n input i j) = value (entry n input j i))
    (hb : ∀ i, i < input.size → |value (input.getD i 0.0)| ≤ (2 : ℝ)^(500 : Int))
    : ∃ result,
        jacobiEigen n input = .ok result
        ∧ Stored n result
        ∧ ∃ W : Matrix (Fin n) (Fin n) ℝ,
            W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
            ∧ ‖spectrumDiagonal n result - W.transpose * matrix n n input * W‖
              ≤ (9 / 100000000000 : ℝ) * ‖matrix n n input‖
                + (2 : ℝ)^(-51 : Int) * (2 : ℝ)^(-1022 : Int)
            ∧ ‖matrix n n result.vectors - W‖
              ≤ (32 * n * n : Nat) * (97 * (2 : ℝ)^(-53 : Int)) := by
  obtain ⟨r, hr, hrs, W, hW, he, hv⟩ := jacobiEigen_spectral_sharp n input hn hn' hs hf hsym hb
  refine ⟨r, hr, hrs, W, hW, he.trans ?_, hv⟩
  exact add_le_add (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _)) le_rfl

/-- Uniform enclosure for every native covariance diagnostic dimension.
It covers zero input, normalization, all rotations and final rescaling up to
eighteen rows, with relative spectral error at most 2.4e-10 plus underflow. -/
theorem jacobiEigen_spectral_diagnostic (n : Nat) (input : Array Float) (hn : 1 ≤ n) (hn' : n ≤ 18)
    (hs : input.size = n * n) (hf : input.all Float.isFinite = true)
    (hsym : ∀ i j, i < n → j < n → value (entry n input i j) = value (entry n input j i))
    (hb : ∀ i, i < input.size → |value (input.getD i 0.0)| ≤ (2 : ℝ)^(500 : Int))
    : ∃ result,
        jacobiEigen n input = .ok result
        ∧ Stored n result
        ∧ ∃ W : Matrix (Fin n) (Fin n) ℝ,
            W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
            ∧ ‖spectrumDiagonal n result - W.transpose * matrix n n input * W‖
              ≤ (24 / 100000000000 : ℝ) * ‖matrix n n input‖
                + (2 : ℝ)^(-51 : Int) * (2 : ℝ)^(-1022 : Int)
            ∧ ‖matrix n n result.vectors - W‖
              ≤ (32 * n * n : Nat) * (97 * (2 : ℝ)^(-53 : Int)) := by
  apply jacobiEigen_spectral_of_trajectory n input hn (by omega) hs hf hsym hb ((2 : ℝ)^(-32 : Int))
    _ (by positivity)
  · have hnR : (n : ℝ) ≤ 18 := by exact_mod_cast hn'
    have ht : value (1.0e-14 : Float) ≤ (2 : ℝ)^(-46 : Int) := by
      change 6338253001141147 * (2 : ℝ)^(-99 : Int) ≤ (2 : ℝ)^(-46 : Int)
      norm_num
    have ht0 : 0 ≤ value (1.0e-14 : Float) :=
      (show 0 ≤ (2 : ℝ)^(-47 : Int) by positivity).trans Jacobi.stopping_threshold_bounds.1
    calc
      _ ≤ ((2 : ℝ)^(-32 : Int)) * (1 + 18 * (2 : ℝ)^(-51 : Int))
          + (18 * (2 : ℝ)^(-46 : Int) + (18 + 32) * (2 : ℝ)^(-51 : Int)) := by
        gcongr
      _ ≤ _ := by norm_num
  · intro a v hstate hV hfloor k hk
    exact JacobiAccumulation.trajectory_diagnostic_error n a v hn' hstate hV hfloor k hk

end Flare.Matrix.JacobiOutput
