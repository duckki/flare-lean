import Flare.Analysis.JacobiEnergy
import Flare.Matrix.JacobiIteration
import Flare.Matrix.JacobiDiagonal

/-! Native Jacobi energy bounds obtained from the actual scan and rotation
equations. Local entry bounds remain explicit iteration-invariant obligations. -/

namespace Flare.Matrix.JacobiEnergy

open Flare.Matrix.Value Flare.Binary64.Value Flare.Matrix.Operations
open Flare.Binary64.Arithmetic Flare.Binary64.Order
open Flare.Matrix.JacobiIteration Flare.Analysis.JacobiEnergy

/-- The actual pivot scan supplies the maximum needed by the energy recurrence. -/
theorem largestPivot_energy (n : Nat) (a : Array Float) (ha : a.all Float.isFinite = true)
    (hsym : ∀ i j, i < n → j < n → value (entry n a i j) = value (entry n a j i))
    : ∃ pivot,
        largestPivot n a = .ok pivot
        ∧ pivot.magnitude.isFinite = true
        ∧ 0 ≤ value pivot.magnitude
        ∧ (pivot.magnitude = 0.0
            ∨ pivot.row < pivot.column
              ∧ pivot.column < n
              ∧ pivot.magnitude = (entry n a pivot.row pivot.column).abs)
        ∧ offEnergy (matrix n n a) ≤ (n : ℝ) * (n - 1) * (value pivot.magnitude)^2 := by
  obtain ⟨pivot, he, hf, hnonneg, hselected, hmax⟩ := largestPivot_correct n a ha
  refine ⟨pivot, he, hf, hnonneg, hselected, offEnergy_le_max _ _ hnonneg ?_⟩
  intro i j hij
  change |value (entry n a i.val j.val)| ≤ _
  by_cases hlt : i.val < j.val
  · exact hmax i.val j.val hlt j.isLt
  · rw [hsym i.val j.val i.isLt j.isLt]
    exact hmax j.val i.val (by have hne := Fin.val_ne_of_ne hij; omega) i.isLt

private theorem matrix_pair_energy (n p q : Nat) (a v : Array Float)
    (result : Array Float × Array Float) (hp : p < n) (hq : q < n)
    (ha : a.all Float.isFinite = true) (hab : ∀ i j, i < n → j < n → |value (entry n a i j)| ≤ 32)
    (h : RotationResult n p q a v result) (k : Fin n) (hk : k ∈ outside (⟨p, hp⟩ : Fin n) ⟨q, hq⟩)
    : |((matrix n n result.1) k ⟨p, hp⟩)^2
        + ((matrix n n result.1) k ⟨q, hq⟩)^2
        - (((matrix n n a) k ⟨p, hp⟩)^2 + ((matrix n n a) k ⟨q, hq⟩)^2)|
      ≤ (2 : ℝ)^(-40 : Int)
        * (((matrix n n a) k ⟨p, hp⟩)^2
            + ((matrix n n a) k ⟨q, hq⟩)^2
            + ((2 : ℝ)^(-1022 : Int))^2) := by
  have hk' := (mem_outside (⟨p, hp⟩ : Fin n) ⟨q, hq⟩ k).mp hk
  have hkp : k.val ≠ p := by intro he; exact hk'.1 (Fin.ext he)
  have hkq : k.val ≠ q := by intro he; exact hk'.2 (Fin.ext he)
  have he := h.matrix_pair k.val k.isLt hkp hkq
  have hη : (2 : ℝ)^(-1022 : Int) ≤ 1 :=
    (zpow_le_one_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr (by norm_num)
  have hbound : |value (entry n a k.val p)| + |value (entry n a k.val q)| +
      (2 : ℝ)^(-1022 : Int) ≤ (2 : ℝ)^(500 : Int) := by
    apply le_trans (b := 128) (by linarith [hab k.val p k.isLt hp, hab k.val q k.isLt hq])
    exact ((by norm_num : (128 : ℝ) ≤ (2 : ℝ)^(8 : Int))).trans
      (zpow_le_zpow_right₀ (by norm_num) (by norm_num))
  have hpair := Jacobi.pair_update_energy (pivotC n a p q) (pivotS n a p q)
    (entry n a k.val p) (entry n a k.val q) h.cosine_finite h.sine_finite
    (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ ha)
    h.cosine_bound h.sine_bound h.unit_error hbound
  change |(value (entry n result.1 k.val p))^2 + (value (entry n result.1 k.val q))^2 - _| ≤ _
  rw [he.1, he.2.2.1]
  exact hpair.2.2

/-- A native rotation obeys the matrix energy inequality with an explicit
underflow term, derived from its original input row pairs. -/
theorem rotation_offEnergy (n p q : Nat) (a v : Array Float) (result : Array Float × Array Float)
    (hp : p < n) (hq : q < n) (hpq : p ≠ q)
    (ha : a.all Float.isFinite = true)
    (hab : ∀ i j, i < n → j < n → |value (entry n a i j)| ≤ 32)
    (hsym : ∀ i j, i < n → j < n → value (entry n a i j) = value (entry n a j i))
    (h : RotationResult n p q a v result)
    : offEnergy (matrix n n result.1)
      ≤ (1 + (2 : ℝ)^(-40 : Int)) * offEnergy (matrix n n a)
        - 2 * (value (entry n a p q))^2
        + 2 * (2 : ℝ)^(-40 : Int) * n * ((2 : ℝ)^(-1022 : Int))^2 := by
  have hPQ : (⟨p, hp⟩ : Fin n) ≠ ⟨q, hq⟩ := by intro he; exact hpq (congrArg Fin.val he)
  apply offEnergy_step (matrix n n a) (matrix n n result.1) ⟨p, hp⟩ ⟨q, hq⟩
    ((2 : ℝ)^(-40 : Int)) ((2 : ℝ)^(-1022 : Int)) hPQ (by positivity)
    (fun i j => hsym i.val j.val i.isLt j.isLt)
    (fun i j => h.symmetric n p q a v result hsym i.val j.val i.isLt j.isLt)
  · change value (entry n result.1 p q) = 0
    rw [h.pivot_zero.1, zero_value]
  · exact matrix_pair_energy n p q a v result hp hq ha hab h
  · intro k hk l hl
    have hk' := (mem_outside (⟨p, hp⟩ : Fin n) ⟨q, hq⟩ k).mp hk
    have hl' := (mem_outside (⟨p, hp⟩ : Fin n) ⟨q, hq⟩ l).mp hl
    change value (entry n result.1 k.val l.val) = value (entry n a k.val l.val)
    rw [h.matrix_unchanged k.val l.val k.isLt l.isLt
      (fun he => hk'.1 (Fin.ext he)) (fun he => hk'.2 (Fin.ext he))
      (fun he => hl'.1 (Fin.ext he)) (fun he => hl'.2 (Fin.ext he))]

/-- Complete native matrix energy growth, including rounded diagonal transfer.
The absolute allowance controls magnitude growth rather than spectral error. -/
theorem rotation_total_energy (n p q : Nat) (a v : Array Float) (result : Array Float × Array Float)
    (hp : p < n) (hq : q < n) (hpq : p ≠ q)
    (ha : a.all Float.isFinite = true)
    (hab : ∀ i j, i < n → j < n → |value (entry n a i j)| ≤ 32)
    (hsym : ∀ i j, i < n → j < n → value (entry n a i j) = value (entry n a j i))
    (hstop : (1.0e-14 : Float) < (entry n a p q).abs)
    (h : RotationResult n p q a v result)
    : energy (matrix n n result.1)
      ≤ (1 + (2 : ℝ)^(-40 : Int)) * energy (matrix n n a)
        + (2 : ℝ)^(-28 : Int)
        + 2 * (2 : ℝ)^(-40 : Int) * n * ((2 : ℝ)^(-1022 : Int))^2 := by
  have hPQ : (⟨p, hp⟩ : Fin n) ≠ ⟨q, hq⟩ := by intro he; exact hpq (congrArg Fin.val he)
  apply energy_step (matrix n n a) (matrix n n result.1) ⟨p, hp⟩ ⟨q, hq⟩
    ((2 : ℝ)^(-28 : Int)) ((2 : ℝ)^(-40 : Int)) ((2 : ℝ)^(-1022 : Int)) hPQ (by positivity)
    (fun i j => hsym i.val j.val i.isLt j.isLt)
    (fun i j => h.symmetric n p q a v result hsym i.val j.val i.isLt j.isLt)
  · change value (entry n result.1 p q) = 0
    rw [h.pivot_zero.1, zero_value]
  · change |(value (entry n result.1 p p))^2 + (value (entry n result.1 q q))^2 - _| ≤ _
    rw [h.diagonal_p, h.diagonal_q]
    exact (JacobiDiagonal.diagonal_energy (entry n a p p) (entry n a p q) (entry n a q q)
      (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ ha)
      (Flare.Matrix.Storage.getD_finite _ _ ha) (hab p p hp hp) (hab p q hp hq) (hab q q hq hq)
        hstop).2.2
  · exact matrix_pair_energy n p q a v result hp hq ha hab h
  · intro k hk l hl
    have hk' := (mem_outside (⟨p, hp⟩ : Fin n) ⟨q, hq⟩ k).mp hk
    have hl' := (mem_outside (⟨p, hp⟩ : Fin n) ⟨q, hq⟩ l).mp hl
    change value (entry n result.1 k.val l.val) = value (entry n a k.val l.val)
    rw [h.matrix_unchanged k.val l.val k.isLt l.isLt
      (fun he => hk'.1 (Fin.ext he)) (fun he => hk'.2 (Fin.ext he))
      (fun he => hl'.1 (Fin.ext he)) (fun he => hl'.2 (Fin.ext he))]

/-- Above the actual stopping threshold, underflow is absorbed into the
relative energy allowance used by the proved convergence criterion. -/
theorem rotation_energy_step (n p q : Nat) (a v : Array Float) (result : Array Float × Array Float)
    (hn : n ≤ 18) (hp : p < n) (hq : q < n) (hpq : p ≠ q)
    (ha : a.all Float.isFinite = true)
    (hab : ∀ i j, i < n → j < n → |value (entry n a i j)| ≤ 32)
    (hsym : ∀ i j, i < n → j < n → value (entry n a i j) = value (entry n a j i))
    (hstop : (1.0e-14 : Float) < (entry n a p q).abs)
    (h : RotationResult n p q a v result)
    : offEnergy (matrix n n result.1)
      ≤ (1 + (2 : ℝ)^(-36 : Int)) * offEnergy (matrix n n a) - 2 * (value (entry n a p q))^2 := by
  have hs := rotation_offEnergy n p q a v result hp hq hpq ha hab hsym h
  have hbf := abs_value (entry n a p q) (Flare.Matrix.Storage.getD_finite _ _ ha)
  have hbp := (lt_iff (1.0e-14 : Float) (entry n a p q).abs (by decide) hbf.1).mp hstop
  rw [hbf.2] at hbp
  have hb : (2 : ℝ)^(-47 : Int) ≤ |value (entry n a p q)| :=
    Jacobi.stopping_threshold_bounds.1.trans hbp.le
  have hη : (2 : ℝ)^(-1022 : Int) ≤ (2 : ℝ)^(-50 : Int) :=
    zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hη0 : 0 ≤ (2 : ℝ)^(-1022 : Int) := by positivity
  have hηsq := (sq_le_sq₀ hη0 (by positivity : 0 ≤ (2 : ℝ)^(-50 : Int))).mpr hη
  have hbsq := (sq_le_sq₀ (by positivity : 0 ≤ (2 : ℝ)^(-47 : Int)) (abs_nonneg _)).mpr hb
  rw [sq_abs] at hbsq
  have hpivot := pivot_sq_le_offEnergy (matrix n n a) (⟨p, hp⟩ : Fin n) ⟨q, hq⟩
    (fun he => hpq (congrArg Fin.val he))
  change (value (entry n a p q))^2 ≤ _ at hpivot
  have hn' : (n : ℝ) ≤ 18 := by exact_mod_cast hn
  generalize hηdef : (2 : ℝ)^(-1022 : Int) = η at *
  have hsmall : 2 * (n : ℝ) * η^2 ≤ offEnergy (matrix n n a) := by
    have hmul := mul_le_mul_of_nonneg_right hn' (sq_nonneg η)
    norm_num only [zpow_neg, zpow_ofNat] at hηsq hbsq
    nlinarith
  have herr := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ (2 : ℝ)^(-40 : Int) by positivity)
  have hE := offEnergy_nonneg (matrix n n a)
  norm_num only [zpow_neg, zpow_ofNat] at hs herr ⊢
  nlinarith

/-- The native scan either meets its actual stopping test or selects a valid
pivot whose complete rotation succeeds and satisfies the convergence recurrence.
The bounds on current matrix/vector entries are local invariant premises. -/
theorem scan_rotation_progress (n : Nat) (a v : Array Float)
    (hn : n ≤ 18) (has : a.size = n * n) (hvs : v.size = n * n)
    (ha : a.all Float.isFinite = true) (hv : v.all Float.isFinite = true)
    (hab : ∀ i j, i < n → j < n → |value (entry n a i j)| ≤ 32)
    (hvb : ∀ i j, i < n → j < n → |value (entry n v i j)| ≤ 32)
    (hsym : ∀ i j, i < n → j < n → value (entry n a i j) = value (entry n a j i))
    : ∃ pivot,
        largestPivot n a = .ok pivot
        ∧ pivot.magnitude.isFinite = true
        ∧ 0 ≤ value pivot.magnitude
        ∧ offEnergy (matrix n n a) ≤ (n : ℝ) * (n - 1) * (value pivot.magnitude)^2
        ∧ (pivot.magnitude ≤ (1.0e-14 : Float)
            ∨ ∃ result,
                rotate n a v pivot.row pivot.column = .ok result
                ∧ RotationResult n pivot.row pivot.column a v result
                ∧ offEnergy (matrix n n result.1)
                  ≤ (1 + (2 : ℝ)^(-36 : Int)) * offEnergy (matrix n n a)
                    - 2 * (value pivot.magnitude)^2) := by
  obtain ⟨pivot, he, hf, hnonneg, hselected, henergy⟩ := largestPivot_energy n a ha hsym
  refine ⟨pivot, he, hf, hnonneg, henergy, ?_⟩
  by_cases hstop : pivot.magnitude ≤ (1.0e-14 : Float)
  · exact Or.inl hstop
  right
  have hlt : (1.0e-14 : Float) < pivot.magnitude := by
    apply (lt_iff _ _ (by decide) hf).mpr
    exact lt_of_not_ge (fun hle => hstop ((le_iff _ _ hf (by decide)).mpr hle))
  rcases hselected with hzero | ⟨hpq, hq, hpivot⟩
  · have ht := (lt_iff _ _ (by decide) hf).mp hlt
    rw [hzero, zero_value] at ht
    have hpos := Jacobi.stopping_threshold_bounds.1
    have hε : 0 < (2 : ℝ)^(-47 : Int) := by positivity
    linarith
  have hp : pivot.row < n := hpq.trans hq
  have hne : pivot.row ≠ pivot.column := Nat.ne_of_lt hpq
  have hstop' : (1.0e-14 : Float) < (entry n a pivot.row pivot.column).abs := by
    simpa only [hpivot] using hlt
  obtain ⟨result, hresult, hrot⟩ := rotate_step n pivot.row pivot.column a v hp hq hne has hvs ha hv
    hab hvb hstop'
  refine ⟨result, hresult, hrot, ?_⟩
  have henergy' := rotation_energy_step n pivot.row pivot.column a v result hn hp hq hne ha hab hsym
    hstop' hrot
  have habs := (abs_value (entry n a pivot.row pivot.column) (Flare.Matrix.Storage.getD_finite _ _
    ha)).2
  rw [hpivot, habs, sq_abs]
  exact henergy'

/-- The same native rotation controls the eigenvector array's total energy.
It follows the actual two-column writes, with no symmetry assumption on vectors. -/
theorem rotation_vector_energy (n p q : Nat) (a v : Array Float)
    (result : Array Float × Array Float) (hp : p < n) (hq : q < n) (hpq : p ≠ q)
    (hv : v.all Float.isFinite = true) (hvb : ∀ i j, i < n → j < n → |value (entry n v i j)| ≤ 32)
    (h : RotationResult n p q a v result)
    : energy (matrix n n result.2)
      ≤ (1 + (2 : ℝ)^(-40 : Int)) * energy (matrix n n v)
        + (2 : ℝ)^(-40 : Int) * n * ((2 : ℝ)^(-1022 : Int))^2 := by
  apply columnPair_energy_step (matrix n n v) (matrix n n result.2) ⟨p, hp⟩ ⟨q, hq⟩
    ((2 : ℝ)^(-40 : Int)) ((2 : ℝ)^(-1022 : Int))
    (fun he => hpq (congrArg Fin.val he)) (by positivity)
  · intro i
    have hη : (2 : ℝ)^(-1022 : Int) ≤ 1 :=
      (zpow_le_one_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr (by norm_num)
    have hbound : |value (entry n v i.val p)| + |value (entry n v i.val q)| +
        (2 : ℝ)^(-1022 : Int) ≤ (2 : ℝ)^(500 : Int) := by
      apply le_trans (b := 128) (by linarith [hvb i.val p i.isLt hp, hvb i.val q i.isLt hq])
      exact ((by norm_num : (128 : ℝ) ≤ (2 : ℝ)^(8 : Int))).trans
        (zpow_le_zpow_right₀ (by norm_num) (by norm_num))
    have hpair := Jacobi.pair_update_energy (pivotC n a p q) (pivotS n a p q)
      (entry n v i.val p) (entry n v i.val q) h.cosine_finite h.sine_finite
      (Flare.Matrix.Storage.getD_finite _ _ hv) (Flare.Matrix.Storage.getD_finite _ _ hv)
      h.cosine_bound h.sine_bound h.unit_error hbound
    change |(value (entry n result.2 i.val p))^2 + (value (entry n result.2 i.val q))^2 - _| ≤ _
    rw [(h.vectors_pair i.val i.isLt).1, (h.vectors_pair i.val i.isLt).2]
    exact hpair.2.2
  · intro i j hjp hjq
    change value (entry n result.2 i.val j.val) = value (entry n v i.val j.val)
    rw [h.vectors_unchanged i.val j.val i.isLt j.isLt
      (fun he => hjp (Fin.ext he)) (fun he => hjq (Fin.ext he))]

end Flare.Matrix.JacobiEnergy
