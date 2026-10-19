module

public import Flare.Matrix.MatrixFormation
public import Flare.Matrix.SolveAccuracy
public import Flare.Analysis.GramBounds

/-! Structured error estimates for the native known-noise Gram matrix. The
proofs retain Frobenius residuals and exact matrix identities before converting
to an operator-norm enclosure for pseudoinverse rank separation. -/

@[expose] public section

namespace Flare.Matrix.GramFormation
open Flare.Matrix.Value Flare.Binary64.Value Flare.Matrix.Operations
open Flare.Binary64.Arithmetic Flare.Analysis.MatrixError
open scoped Matrix.Norms.L2Operator

/-- The native product has a Frobenius error controlled by the input Frobenius
norms. Finite execution follows from a bound on the exact dot-product mass. -/
theorem multiply_frobenius_accuracy (rows inner columns : Nat) (a b : Array Float)
    (hinner : inner ≤ 32) (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hbound
      : ‖matrix rows inner a‖ * ‖matrix inner columns b‖ + (2 : ℝ) ^ (-1022 : Int)
        ≤ (2 : ℝ) ^ (990 : Int))
    : ∃ r,
        multiply rows inner columns a b = .ok r
        ∧ r.size = rows * columns
        ∧ r.all Float.isFinite = true
        ∧ ‖entries (matrix rows columns r - matrix rows inner a * matrix inner columns b)‖
          ≤ inner * (2 : ℝ) ^ (-50 : Int)
            * (‖entries (matrix rows inner a)‖ * ‖entries (matrix inner columns b)‖
                + Real.sqrt rows * Real.sqrt columns * (2 : ℝ) ^ (-1022 : Int)) := by
  let mass (i j : Nat) := (∑ k ∈ Finset.range inner,
    |value (entry inner a i k) * value (entry columns b k j)|) + (2 : ℝ)^(-1022 : Int)
  have hlim (i j : Nat) (hi : i < rows) (hj : j < columns) : mass i j ≤ (2 : ℝ)^(990 : Int) := by
    apply le_trans _ hbound
    apply add_le_add _ le_rfl
    rw [← Fin.sum_univ_eq_sum_range (fun k => |value (entry inner a i k) * value (entry columns b k
      j)|) inner]
    exact Flare.Analysis.JacobiNorms.product_mass_le_norm (matrix rows inner a) (matrix inner
      columns b) ⟨i, hi⟩ ⟨j, hj⟩
  obtain ⟨r, hr, hrs, hrf, he⟩ := Flare.Matrix.Multiplication.multiply_entrywise_accuracy rows inner
    columns a b mass
    hinner ha hb hlim (fun _ _ _ _ => le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => abs_nonneg
      _))
    (fun _ _ _ _ => le_add_of_nonneg_right (by positivity))
  refine ⟨r, hr, hrs, hrf, ?_⟩
  apply product_roundoff_norm (matrix rows inner a) (matrix inner columns b) _
    (inner * (2 : ℝ) ^ (-50 : Int)) ((2 : ℝ) ^ (-1022 : Int)) (by positivity) (by positivity)
  intro i j
  have hh := he i j
  dsimp only [mass] at hh
  rw [← Fin.sum_univ_eq_sum_range (fun k => |value (entry inner a i.val k) * value (entry columns b
    k j.val)|) inner] at hh
  exact hh

/-- Exact lower-triangle copying amplifies the Frobenius error by at most
1.42 and returns a finite symmetric matrix. -/
theorem mirrorLower_frobenius_accuracy (n : Nat) (a : Array Float)
    (A : Matrix (Fin n) (Fin n) ℝ) (has : a.size = n * n)
    (ha : a.all Float.isFinite = true) (hA : A.IsHermitian)
    : (mirrorLower n a).size = n * n
      ∧ (mirrorLower n a).all Float.isFinite = true
      ∧ (matrix n n (mirrorLower n a)).IsHermitian
      ∧ ‖entries (matrix n n (mirrorLower n a) - A)‖
        ≤ (71 / 50 : ℝ) * ‖entries (matrix n n a - A)‖ := by
  have hm : (mirrorLower n a).size = n * n ∧ (mirrorLower n a).all Float.isFinite = true ∧
      ∀ i j, i < n → j < n → entry n (mirrorLower n a) i j =
        if i < j then entry n a j i else entry n a i j :=
    Flare.Matrix.Storage.mirrorLower_spec n a ⟨has, ha⟩
  have hent (i j : Fin n) : matrix n n (mirrorLower n a) i j =
      if i.val < j.val then matrix n n a j i else matrix n n a i j := by
    change value (entry n (mirrorLower n a) i.val j.val) = _
    rw [hm.2.2 _ _ i.isLt j.isLt]
    split_ifs <;> rfl
  refine ⟨hm.1, hm.2.1, ?_, ?_⟩
  · apply _root_.Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial, hent]
    split_ifs <;> first | rfl | (have : i = j := Fin.ext (by omega); subst j; rfl)
  · apply mirror_error_norm A (matrix n n a - A) _ hA
    intro i j
    rw [hent, add_sub_cancel]
    split_ifs <;> first | rfl | omega

/-- The actual noise solve, product and lower-triangle copy form the Gram
coefficient with relative error at most `1.27e-11` against the total information
scale. No native-success or native-accuracy premise is required. -/
theorem known_noise_gram_accuracy (o m : Nat) (r c : Array Float)
    (Y : Matrix (Fin m) (Fin m) ℝ) (ho : o ≤ 12) (hm : m ≤ 12)
    (hr : r.all Float.isFinite = true) (hc : c.all Float.isFinite = true)
    (hR : (matrix o o r - (1 / 4 : ℝ) • 1).PosSemidef)
    (hrb : ∀ i j : Fin o, |matrix o o r i j| ≤ 4)
    (hcb : ∀ (i : Fin o) (k : Fin m), |matrix o m c i k| ≤ 4)
    (hY : Y.PosSemidef)
    : let R := matrix o o r
      let C := matrix o m c
      let G := C.transpose * R⁻¹ * C
      let T := Y + G
      ∃ x raw,
        solveSPD o m r c = .ok x
        ∧ multiply m o m (transpose o m c) x = .ok raw
        ∧ raw.size = m * m
        ∧ raw.all Float.isFinite = true
        ∧ (mirrorLower m raw).size = m * m
        ∧ (mirrorLower m raw).all Float.isFinite = true
        ∧ (matrix m m (mirrorLower m raw)).IsHermitian
        ∧ ‖matrix m m (mirrorLower m raw) - G‖
          ≤ (127 / 10000000000000 : ℝ) * ‖T‖ + (2 : ℝ) ^ (-980 : Int) := by
  dsimp only
  let R := matrix o o r
  let C := matrix o m c
  let F := R⁻¹ * C
  let G := C.transpose * R⁻¹ * C
  let T := Y + G
  let δ := (2 : ℝ)^(-1000 : Int)
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
  have hηδ : (2 : ℝ)^(-1022 : Int) ≤ δ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hm' : (m : ℝ) ≤ 12 := by exact_mod_cast hm
  have ho' : (o : ℝ) ≤ 12 := by exact_mod_cast ho
  have hc' (i : Fin o) (j : Fin m) : |C i j| ≤ 4 := hcb i j
  have hRn : ‖R‖ ≤ 48 := (norm_le_entries R).trans (bounded_rectangle R ho ho hrb)
  have hCnF : ‖entries C‖ ≤ 48 := bounded_rectangle C ho hm hc'
  have hCn : ‖C‖ ≤ 48 := (norm_le_entries C).trans hCnF
  have hRi : ‖R⁻¹‖ ≤ 4 := (Flare.Analysis.Conditioning.inverse_norm_bound R (1 / 4)
    (by norm_num) hR).trans_eq (by norm_num)
  have hFn : ‖F‖ ≤ 192 := (_root_.Matrix.l2_opNorm_mul _ _).trans
    ((mul_le_mul hRi hCn (norm_nonneg C) (by norm_num)).trans_eq (by norm_num))
  have hpd := Flare.Analysis.NumericalBounds.posDef_of_lower_bound R (1 / 4) (by norm_num) hR
  obtain ⟨hF2, _, hCF⟩ := Flare.Analysis.GramBounds.gram_operand_norms R C Y hpd hR hY hRn
  have hsqrt : Real.sqrt (m : ℝ) ≤ 7 / 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num; linarith⟩
  have hFnF : ‖entries F‖ ≤ (7 / 2 : ℝ) * ‖F‖ :=
    (entries_norm_le F).trans (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg F))
  have hCFrob : ‖entries C‖ * ‖entries F‖ ≤ 168 * ‖T‖ := by
    have hh := mul_le_mul (entries_norm_le C) (entries_norm_le F) (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg C))
    have hid : (Real.sqrt (m : ℝ) * ‖C‖) * (Real.sqrt m * ‖F‖) = m * (‖C‖ * ‖F‖) := by
      calc
        _ = (Real.sqrt (m : ℝ)) ^ 2 * (‖C‖ * ‖F‖) := by ring
        _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg m)]
    rw [hid] at hh
    exact hh.trans
      ((mul_le_mul_of_nonneg_left hCF (Nat.cast_nonneg m)).trans
        (by have ht := mul_le_mul_of_nonneg_right hm' (norm_nonneg T); nlinarith only [ht]))
  obtain ⟨x, hx, _, hxf, hXf, hEf⟩ := SolveAccuracy.noise_solve_frobenius o m 2 r c ho hm
    (by norm_num) (by norm_num) hr hc hR hrb (by
      intro i j hi hj
      exact (hc' ⟨i, hi⟩ ⟨j, hj⟩).trans_eq (by norm_num))
  let X := matrix o m x
  have hXn : ‖entries X‖ ≤ 674 := by
    have hh := (mul_le_mul_of_nonneg_left hFn (by norm_num : (0 : ℝ) ≤ 7 / 2))
    change ‖entries X‖ ≤ (1001 / 1000 : ℝ) * ‖entries F‖ + δ at hXf
    linarith only [hXf, hFnF, hh, hδ1]
  have hCX : ‖entries C‖ * ‖entries X‖ ≤ (1001 / 1000 : ℝ) * 168 * ‖T‖ + 48 * δ := by
    have hh := mul_le_mul_of_nonneg_left hXf (norm_nonneg (entries C))
    have hsmall := mul_le_mul_of_nonneg_right hCnF hδ0
    nlinarith only [hh, hCFrob, hsmall]
  have hCT := Flare.Matrix.Multiplication.transpose_matrix o m c hc
  have ht := Flare.Matrix.Multiplication.transpose_storage o m c hc
  have hlim
      : ‖matrix m o (transpose o m c)‖ * ‖X‖ + (2 : ℝ) ^ (-1022 : Int) ≤ (2 : ℝ) ^ (990 : Int) := by
    rw [hCT, Flare.Analysis.SpectralPerturbation.norm_transpose]
    have hprod := mul_le_mul hCn ((norm_le_entries X).trans hXn) (norm_nonneg X) (by norm_num : (0
      : ℝ) ≤ 48)
    calc
      _ ≤ (2 : ℝ) ^ (16 : Int) := by
        norm_num only [show (2 : ℝ)^(16 : Int) = 65536 by norm_num]
        linarith only [hprod, hηδ, hδ1]
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  obtain ⟨raw, hraw, hrs, hrf, he⟩ := multiply_frobenius_accuracy m o m (transpose o m c) x
    (by omega) ht.2.1 hxf hlim
  rw [hCT, entries_transpose_norm] at he
  have hsqrts : Real.sqrt (m : ℝ) * Real.sqrt m = m := by
    simpa only [pow_two] using Real.sq_sqrt (Nat.cast_nonneg m)
  rw [hsqrts] at he
  have hround : ‖entries (matrix m m raw - C.transpose * X)‖ ≤
      (18 / 10000000000000 : ℝ) * ‖T‖ + δ := by
    have ht0 : 0 ≤ ‖T‖ := norm_nonneg T
    have hmass := add_le_add hCX (mul_le_mul hm' hηδ (by positivity) (by norm_num : (0 : ℝ) ≤ 12))
    have hcoef : (o : ℝ) * (2 : ℝ)^(-50 : Int) ≤ 12 * (2 : ℝ)^(-50 : Int) :=
      mul_le_mul_of_nonneg_right ho' (by positivity)
    have hh := he.trans (mul_le_mul hcoef hmass
      (by positivity) (by positivity : 0 ≤ 12 * (2 : ℝ)^(-50 : Int)))
    norm_num only [show (2 : ℝ)^(-50 : Int) = 1 / 1125899906842624 by norm_num] at hh
    nlinarith only [hh, hδ0, ht0]
  have hsolve : ‖entries (C.transpose * X - G)‖ ≤
      (71 / 10000000000000 : ℝ) * ‖T‖ + 192 * δ := by
    rw [Flare.Analysis.GramBounds.gram_residual_identity R C X hpd]
    have he' := (entries_mul_le F.transpose (R * X - C)).trans
      (mul_le_mul_of_nonneg_left hEf (norm_nonneg F.transpose))
    rw [Flare.Analysis.SpectralPerturbation.norm_transpose] at he'
    have hscale := mul_le_mul_of_nonneg_left hFnF (norm_nonneg F)
    have hsmall := mul_le_mul_of_nonneg_right hFn hδ0
    change ‖entries (F.transpose * (R * X - C))‖ ≤ _
    nlinarith only [he', hscale, hsmall, hF2, norm_nonneg T]
  have hG : G.PosSemidef := by
    simpa only [G, _root_.Matrix.conjTranspose_eq_transpose_of_trivial,
      _root_.Matrix.transpose_transpose]
      using hpd.inv.posSemidef.mul_mul_conjTranspose_same C.transpose
  have hmcopy := mirrorLower_frobenius_accuracy m raw G hrs hrf hG.isHermitian
  refine ⟨x, raw, hx, hraw, hrs, hrf, hmcopy.1, hmcopy.2.1, hmcopy.2.2.1, ?_⟩
  have hsum : ‖entries (matrix m m raw - G)‖ ≤
      (89 / 10000000000000 : ℝ) * ‖T‖ + 193 * δ := by
    have hh := norm_sub_le_norm_sub_add_norm_sub (entries (matrix m m raw)) (entries (C.transpose *
      X)) (entries G)
    simp only [← entries_sub] at hh
    linarith only [hh, hround, hsolve]
  have hfinal := (norm_le_entries (matrix m m (mirrorLower m raw) - G)).trans hmcopy.2.2.2
  have htiny : 1024 * δ ≤ (2 : ℝ)^(-980 : Int) := by
    rw [show (-980 : Int) = -1000 + 20 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    change 1024 * δ ≤ δ * (2 : ℝ)^(20 : Int)
    norm_num only [show (2 : ℝ)^(20 : Int) = 1048576 by norm_num]
    linarith only [hδ0]
  change ‖matrix m m (mirrorLower m raw) - G‖ ≤ (127 / 10000000000000 : ℝ) * ‖T‖ + _
  nlinarith only [hfinal, hsum, htiny, hδ0, norm_nonneg T]

/-- Native HᵀR⁻¹C formation, scaled to the second LMI's magnitude. The
information-scale hypothesis is supplied by the already formed T block. -/
theorem known_noise_cross_accuracy (n o m : Nat) (h r c : Array Float)
    (Y : Matrix (Fin m) (Fin m) ℝ) (S : ℝ) (hn : n ≤ 6) (ho : o ≤ 12) (hm : m ≤ 12)
    (hh : h.all Float.isFinite = true) (hr : r.all Float.isFinite = true)
    (hc : c.all Float.isFinite = true) (hR : (matrix o o r - (1 / 4 : ℝ) • 1).PosSemidef)
    (hhb : ∀ i j, |matrix o n h i j| ≤ 4) (hrb : ∀ i j, |matrix o o r i j| ≤ 4)
    (hcb : ∀ i j, |matrix o m c i j| ≤ 4) (hY : Y.PosSemidef) (hS : 1 ≤ S)
    (hT : ‖Y + (matrix o m c).transpose * (matrix o o r)⁻¹ * matrix o m c‖ ≤ (12001 / 1000 : ℝ) * S)
    : ∃ x raw,
        solveSPD o m r c = .ok x
        ∧ multiply n o m (transpose o n h) x = .ok raw
        ∧ raw.size = n * m
        ∧ raw.all Float.isFinite = true
        ∧ ‖entries (matrix n m raw - (matrix o n h).transpose * (matrix o o r)⁻¹ * matrix o m c)‖
          ≤ (18 / 10000000000 : ℝ) * S + (2 : ℝ) ^ (-980 : Int) := by
  let H := matrix o n h
  let R := matrix o o r
  let C := matrix o m c
  let F := R⁻¹ * C
  let FH := R⁻¹ * H
  let δ := (2 : ℝ)^(-1000 : Int)
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
  have hηδ : (2 : ℝ)^(-1022 : Int) ≤ δ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hS0 : 0 ≤ S := by linarith only [hS]
  have hn' : (n : ℝ) ≤ 6 := by exact_mod_cast hn
  have ho' : (o : ℝ) ≤ 12 := by exact_mod_cast ho
  have hm' : (m : ℝ) ≤ 12 := by exact_mod_cast hm
  have hsn : Real.sqrt (n : ℝ) ≤ 5 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num; linarith⟩
  have hso : Real.sqrt (o : ℝ) ≤ 7 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num; linarith⟩
  have hsm : Real.sqrt (m : ℝ) ≤ 7 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num; linarith⟩
  have hHf : ‖entries H‖ ≤ 36 := by
    have he := entries_bound H 4 (by norm_num) hhb
    have hs := mul_le_mul hso hsn (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 7 / 2)
    linarith only [he, hs]
  have hHn : ‖H‖ ≤ 36 := (norm_le_entries H).trans hHf
  have hCf : ‖entries C‖ ≤ 48 := bounded_rectangle C ho hm hcb
  have hRn : ‖R‖ ≤ 48 := (norm_le_entries R).trans (bounded_rectangle R ho ho hrb)
  have hRi : ‖R⁻¹‖ ≤ 4 := (Flare.Analysis.Conditioning.inverse_norm_bound R (1 / 4)
    (by norm_num) hR).trans_eq (by norm_num)
  have hpd := Flare.Analysis.NumericalBounds.posDef_of_lower_bound R (1 / 4) (by norm_num) hR
  have hFH : ‖FH‖ ≤ 144 := (_root_.Matrix.l2_opNorm_mul _ _).trans
    ((mul_le_mul hRi hHn (norm_nonneg H) (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by norm_num))
  have hFn : ‖entries F‖ ≤ 192 := (entries_mul_le R⁻¹ C).trans
    ((mul_le_mul hRi hCf (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by norm_num))
  have hF2 := (Flare.Analysis.GramBounds.gram_operand_norms R C Y hpd hR hY hRn).1
  have hFS : ‖F‖ ≤ 7 * S := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    have hs : S ≤ S^2 := by nlinarith only [hS]
    nlinarith only [hF2, hT, hs, hS0]
  have hFfS : ‖entries F‖ ≤ (49 / 2 : ℝ) * S := by
    have he := (entries_norm_le F).trans (mul_le_mul hsm hFS (norm_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 7 / 2))
    nlinarith only [he]
  obtain ⟨x, hx, _, hxf, hX, hE⟩ := SolveAccuracy.noise_solve_frobenius o m 2 r c ho hm
    (by norm_num) (by norm_num) hr hc hR hrb (by
      intro i j hi hj
      exact (hcb ⟨i, hi⟩ ⟨j, hj⟩).trans_eq (by norm_num))
  let X := matrix o m x
  have hXn : ‖entries X‖ ≤ 194 := by linarith only [hX, hFn, hδ1]
  have hXS : ‖entries X‖ ≤ (1001 / 1000 : ℝ) * (49 / 2) * S + δ := by
    linarith only [hX, hFfS]
  have hES : ‖entries (R * X - C)‖ ≤ (501 / 1000000000000000 : ℝ) * (49 / 2) * S + δ := by
    linarith only [hE, hFfS]
  have htr := Flare.Matrix.Multiplication.transpose_storage o n h hh
  have htm := Flare.Matrix.Multiplication.transpose_matrix o n h hh
  have hlim
      : ‖matrix n o (transpose o n h)‖ * ‖X‖ + (2 : ℝ) ^ (-1022 : Int) ≤ (2 : ℝ) ^ (990 : Int) := by
    rw [htm, Flare.Analysis.SpectralPerturbation.norm_transpose]
    have hp := mul_le_mul hHn ((norm_le_entries X).trans hXn) (norm_nonneg X) (by norm_num : (0 :
      ℝ) ≤ 36)
    calc
      _ ≤ (2 : ℝ) ^ (16 : Int) := by
        norm_num only [show (2 : ℝ)^(16 : Int) = 65536 by norm_num]
        linarith only [hp, hηδ, hδ1]
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  obtain ⟨raw, heq, hrs, hrf, he⟩ := multiply_frobenius_accuracy n o m (transpose o n h) x
    (by omega) htr.2.1 hxf hlim
  rw [htm, entries_transpose_norm] at he
  have hround : ‖entries (matrix n m raw - H.transpose * X)‖ ≤
      (1 / 100000000000 : ℝ) * S + δ := by
    have hprod := mul_le_mul hHf hXS (norm_nonneg (entries X)) (by norm_num : (0 : ℝ) ≤ 36)
    have hs := mul_le_mul hsn hsm (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 5 / 2)
    have hη := mul_le_mul hs hηδ (by positivity) (by norm_num : (0 : ℝ) ≤ 5 / 2 * (7 / 2))
    have hcoef := mul_le_mul_of_nonneg_right ho' (by positivity : 0 ≤ (2 : ℝ)^(-50 : Int))
    have hb := he.trans (mul_le_mul hcoef (add_le_add hprod hη) (by positivity) (by positivity))
    norm_num only [show (2 : ℝ)^(-50 : Int) = 1 / 1125899906842624 by norm_num] at hb
    nlinarith only [hb, hS0, hδ0]
  have hsolve : ‖entries (H.transpose * X - H.transpose * R⁻¹ * C)‖ ≤
      (178 / 100000000000 : ℝ) * S + 144 * δ := by
    rw [Flare.Analysis.GramBounds.cross_residual_identity R H C X hpd]
    have hh := (entries_mul_le FH.transpose (R * X - C)).trans
      (mul_le_mul (by simpa only [Flare.Analysis.SpectralPerturbation.norm_transpose] using hFH)
        hES (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 144))
    nlinarith only [hh, hS0]
  refine ⟨x, raw, hx, heq, hrs, hrf, ?_⟩
  have ht := norm_sub_le_norm_sub_add_norm_sub (entries (matrix n m raw)) (entries (H.transpose *
    X))
    (entries (H.transpose * R⁻¹ * C))
  simp only [← entries_sub] at ht
  have htiny : 1024 * δ ≤ (2 : ℝ)^(-980 : Int) := by
    rw [show (-980 : Int) = -1000 + 20 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    change 1024 * δ ≤ δ * (2 : ℝ)^(20 : Int)
    norm_num only [show (2 : ℝ)^(20 : Int) = 1048576 by norm_num]
    linarith only [hδ0]
  nlinarith only [ht, hround, hsolve, htiny, hS0, hδ0]

end Flare.Matrix.GramFormation
