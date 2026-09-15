import Flare.Analysis.MatrixError
import Flare.Analysis.NumericalBounds
import Flare.Matrix.JacobiOutput

/-! Completeness of the approximate positive-semidefiniteness diagnostic.
The proved acceptance conditions do not make diagnostic acceptance a
certificate of exact positive semidefiniteness. -/

namespace Flare.Matrix.PSDCheck
open Flare.Matrix.Value Flare.Binary64.Value Flare.Matrix.Operations
open Flare.Binary64.Arithmetic Flare.Binary64.Order
open Flare.Matrix.JacobiOutput Flare.Analysis.SpectralPerturbation
open scoped Matrix.Norms.L2Operator

/-- The native tolerance is finite and remains above nine billionths of its
selected real scale, including the rounding of the decimal literal and product. -/
theorem tolerance_lower_bound (m : Float) (hm : m.isFinite = true)
    (hmb : |value m| ≤ (2 : ℝ)^(500 : Int))
    : (1.0e-8 * max 1.0 m).isFinite = true
      ∧ (9 / 1000000000 : ℝ) * max 1 (value m) ≤ value (1.0e-8 * max 1.0 m) := by
  obtain ⟨hsf, hsv⟩ := max_value 1.0 m (by decide) hm
  rw [one_value] at hsv
  let s := max 1 (value m)
  have hs : (1 : ℝ) ≤ s := le_max_left _ _
  have hs0 : 0 ≤ s := by linarith
  have hsbound : s ≤ (2 : ℝ)^(500 : Int) := max_le
    (by simpa only [zpow_zero] using (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show (0 : Int) ≤ 500 by omega))) ((le_abs_self _).trans hmb)
  have hc0 : 0 ≤ value (1.0e-8 : Float) := by
    change 0 ≤ 6044629098073146 * (2 : ℝ)^(-79 : Int)
    positivity
  have hc1 : value (1.0e-8 : Float) ≤ 1 := by
    change 6044629098073146 * (2 : ℝ)^(-79 : Int) ≤ 1
    norm_num
  have hclo : (999 / 100000000000 : ℝ) ≤ value (1.0e-8 : Float) := by
    change (999 / 100000000000 : ℝ) ≤ 6044629098073146 * (2 : ℝ)^(-79 : Int)
    norm_num
  have hprod : |value (1.0e-8 : Float) * value (max 1.0 m)| ≤ (2 : ℝ)^(1000 : Int) := by
    rw [hsv, abs_of_nonneg (mul_nonneg hc0 hs0)]
    exact ((mul_le_mul_of_nonneg_right hc1 hs0).trans_eq (one_mul s)).trans
      (hsbound.trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)))
  obtain ⟨hf, he⟩ := mul_error_relative 1.0e-8 (max 1.0 m) (by decide) hsf hprod
  rw [hsv, abs_of_nonneg (mul_nonneg hc0 hs0)] at he
  have hη : (2 : ℝ)^(-1022 : Int) ≤ 1 :=
    (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (-1022 : Int) ≤ 0)).trans_eq (by
      norm_num)
  have he' : |value (1.0e-8 * max 1.0 m) - value (1.0e-8 : Float) * s| ≤
      2 * (2 : ℝ)^(-51 : Int) * s := by
    apply he.trans
    have hc := mul_le_mul_of_nonneg_right hc1 hs0
    norm_num only [show (2 : ℝ)^(-51 : Int) = 1 / 2251799813685248 by norm_num]
    linarith
  have hh := (abs_le.mp he').1
  have hc := mul_le_mul_of_nonneg_right hclo hs0
  refine ⟨hf, ?_⟩
  change (9 / 1000000000 : ℝ) * s ≤ _
  norm_num only [show (2 : ℝ)^(-51 : Int) = 1 / 2251799813685248 by norm_num] at hh
  linarith

/-- Native covariance checking accepts a symmetric input whose negative part
is at most `4e-9 * max(1,maxAbs(input))`. This is a completeness guarantee for
the diagnostic, not a converse claiming exact PSD from a passing check. -/
theorem checkPSD_accepts_nearPSD (n : Nat) (input : Array Float) (hn : 1 ≤ n) (hn' : n ≤ 18)
    (hs : input.size = n * n) (hf : input.all Float.isFinite = true)
    (hsym : ∀ i j, i < n → j < n → value (entry n input i j) = value (entry n input j i))
    (hb : ∀ i, i < input.size → |value (input.getD i 0.0)| ≤ (2 : ℝ)^(500 : Int))
    (hPSD
      : (matrix n n input + ((4 / 1000000000 : ℝ) * max 1 (value (maxAbs input))) • 1).PosSemidef)
    : checkPSD n input = .ok () := by
  obtain ⟨result, he, hstored, W, hW, herr, _⟩ := jacobiEigen_spectral_diagnostic n input hn hn' hs
    hf hsym hb
  have hm := Spectrum.maxAbs_correct input hf
  have hmhi : |value (maxAbs input)| ≤ (2 : ℝ)^(500 : Int) := by
    rw [abs_of_nonneg hm.2.1]
    exact Spectrum.maxAbs_le input _ hf (by positivity) hb
  obtain ⟨htf, htlo⟩ := tolerance_lower_bound (maxAbs input) hm.1 hmhi
  let s := max 1 (value (maxAbs input))
  have hs1 : (1 : ℝ) ≤ s := le_max_left _ _
  have hs0 : 0 ≤ s := by linarith
  have hnorm : ‖matrix n n input‖ ≤ n * s := by
    apply norm_le_entries _ _ hs0
    intro i j
    exact (hm.2.2 (i.val * n + j.val) (by rw [hs]; nlinarith [i.isLt, j.isLt])).trans (le_max_right
      _ _)
  have hnR : (n : ℝ) ≤ 18 := by exact_mod_cast hn'
  have hη : (2 : ℝ)^(-1022 : Int) ≤ 1 :=
    (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (-1022 : Int) ≤ 0)).trans_eq (by
      norm_num)
  have herr' : ‖spectrumDiagonal n result - W.transpose * matrix n n input * W‖ ≤
      (5 / 1000000000 : ℝ) * s := by
    apply herr.trans
    have hns := mul_le_mul_of_nonneg_right hnR hs0
    have hr := mul_le_mul_of_nonneg_left hη (by positivity : 0 ≤ (2 : ℝ)^(-51 : Int))
    norm_num only [show (2 : ℝ)^(-51 : Int) = 1 / 2251799813685248 by norm_num] at hr ⊢
    nlinarith only [hnorm, hns, hs1, hr]
  have hunit : W.transpose * W = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.star_mul_self_of_mem hW
  have hsim : (W.transpose * matrix n n input * W + ((4 / 1000000000 : ℝ) * s) • 1).PosSemidef := by
    have hh := hPSD.mul_mul_conjTranspose_same W.transpose
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hunit]
      using hh
  have hvalues : ∀ i : Fin n, -value (1.0e-8 * max 1.0 (maxAbs input)) ≤ value (result.values.getD
    i.val 0.0) := by
    intro i
    have hd := hsim.diag_nonneg (i := i)
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hd
    have hbnd := (entry_le_norm (spectrumDiagonal n result - W.transpose * matrix n n input * W) i
      i).trans herr'
    simp only [Matrix.sub_apply, spectrumDiagonal, Matrix.diagonal_apply_eq] at hbnd
    have hlo := (abs_le.mp hbnd).1
    change (9 / 1000000000 : ℝ) * s ≤ _ at htlo
    linarith only [hd, hlo, htlo]
  have hneg := neg_value (1.0e-8 * max 1.0 (maxAbs input)) htf
  have hall : result.values.all (fun x => -(1.0e-8 * max 1.0 (maxAbs input)) ≤ x) = true := by
    rw [Array.all_eq_true]
    intro i hi
    have hin : i < n := by rw [← hstored.values_size]; exact hi
    have hif := Array.all_eq_true.mp hstored.values_finite i hi
    have hv := hvalues ⟨i, hin⟩
    simp only [decide_eq_true_eq]
    exact (le_iff _ _ hneg.1 hif).mpr (by simpa [hneg.2, hi] using hv)
  simp only [checkPSD, he, finite, htf, ↓reduceIte, bind, Except.bind, hall]
  rfl

/-- Exact positive semidefinite inputs, including singular and zero matrices,
are accepted by the complete native diagnostic on its supported profile. -/
theorem checkPSD_accepts_psd (n : Nat) (input : Array Float) (hn : 1 ≤ n) (hn' : n ≤ 18)
    (hs : input.size = n * n) (hf : input.all Float.isFinite = true)
    (hsym : ∀ i j, i < n → j < n → value (entry n input i j) = value (entry n input j i))
    (hb : ∀ i, i < input.size → |value (input.getD i 0.0)| ≤ (2 : ℝ)^(500 : Int))
    (hPSD : (matrix n n input).PosSemidef)
    : checkPSD n input = .ok () := by
  apply checkPSD_accepts_nearPSD n input hn hn' hs hf hsym hb
  apply hPSD.add
  apply Matrix.PosSemidef.one.smul
  have hs : (1 : ℝ) ≤ max 1 (value (maxAbs input)) := le_max_left _ _
  positivity

/-- A proved entrywise formation error transfers exact PSD of the reference
matrix to acceptance of the actual native diagnostic. The margin is compared
with the diagnostic's own input scale, rather than an assumed solver result. -/
theorem checkPSD_accepts_approximation (n : Nat) (input : Array Float)
    (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (hn : 1 ≤ n) (hn' : n ≤ 18)
    (hs : input.size = n * n) (hf : input.all Float.isFinite = true)
    (hN : (matrix n n input).IsHermitian) (hA : A.PosSemidef) (hε : 0 ≤ ε)
    (he : ∀ i j, |matrix n n input i j - A i j| ≤ ε)
    (hb : ∀ i, i < input.size → |value (input.getD i 0.0)| ≤ (2 : ℝ)^(500 : Int))
    (hmargin : n * ε ≤ (4 / 1000000000 : ℝ) * max 1 (value (maxAbs input)))
    : checkPSD n input = .ok () := by
  refine checkPSD_accepts_nearPSD n input hn hn' hs hf ?_ hb ?_
  · intro i j hi hj
    have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M ⟨j, hj⟩ ⟨i, hi⟩) hN.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial, matrix, entry,
      Flare.Matrix.Dense.entry] using hh
  · have hnear := Flare.Analysis.NumericalBounds.perturbation_lower_bound A
      (matrix n n input - A) 0 ε hε (by simpa using hA) (hN.sub hA.isHermitian) he
    have hnear' : (matrix n n input + (n * ε) • 1).PosSemidef := by
      convert hnear using 1
      simp only [zero_sub, neg_smul, sub_neg_eq_add]
      abel
    have hgap := (Matrix.PosSemidef.one (n := Fin n) (R := ℝ)).smul (sub_nonneg.mpr hmargin)
    convert hnear'.add hgap using 1
    rw [sub_smul]
    abel

/-- The native PSD diagnostic accepts a symmetric approximation whose
operator-norm error is within its negative-eigenvalue allowance. This avoids
charging a dimension factor for a bound already measured in operator norm. -/
theorem checkPSD_accepts_norm_approximation (n : Nat) (input : Array Float)
    (A : Matrix (Fin n) (Fin n) ℝ) (hn : 1 ≤ n) (hn' : n ≤ 18)
    (hs : input.size = n * n) (hf : input.all Float.isFinite = true)
    (hsym : (matrix n n input).IsHermitian)
    (hb : ∀ i, i < input.size → |value (input.getD i 0.0)| ≤ (2 : ℝ)^(500 : Int))
    (hA : A.PosSemidef)
    (he : ‖matrix n n input - A‖ ≤ (4 / 1000000000 : ℝ) * max 1 (value (maxAbs input)))
    : checkPSD n input = .ok () := by
  refine checkPSD_accepts_nearPSD n input hn hn' hs hf ?_ hb ?_
  · intro i j hi hj
    have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M ⟨j, hj⟩ ⟨i, hi⟩) hsym
    simpa only [Matrix.conjTranspose_apply, star_trivial, matrix, entry,
      Flare.Matrix.Dense.entry] using hh
  · have hp := hA.add (Flare.Analysis.MatrixError.add_identity_posSemidef (matrix n n input - A)
      _ (hsym.sub hA.isHermitian) he)
    convert hp using 1
    abel

end Flare.Matrix.PSDCheck
