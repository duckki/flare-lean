import Flare.Binary64.Division
import Flare.Binary64.Order
import Flare.Matrix.Multiplication

/-! Native eigensolver normalization. The maximum-magnitude scan is exact, and
every division in the initial scaling succeeds with an explicit error bound.
Jacobi iteration and spectral accuracy require additional proofs. -/

namespace Flare.Matrix.Spectrum
open Flare.Matrix.Value Flare.Binary64.Value Flare.Matrix.Operations
open Flare.Binary64.Arithmetic Flare.Binary64.Division
open Flare.Binary64.Order

private lemma maxAbs_fold (xs : List Float) (s : Float)
    (hx : ∀ x ∈ xs, x.isFinite = true) (hs : s.isFinite = true)
    : (xs.foldl (fun a x => max a x.abs) s).isFinite = true
      ∧ value s ≤ value (xs.foldl (fun a x => max a x.abs) s)
      ∧ ∀ x ∈ xs, |value x| ≤ value (xs.foldl (fun a x => max a x.abs) s) := by
  induction xs generalizing s with
  | nil => exact ⟨hs, le_rfl, by simp⟩
  | cons x xs ih =>
      obtain ⟨hxf, hxv⟩ := abs_value x (hx x (by simp))
      obtain ⟨hmf, hmv⟩ := max_value s x.abs hs hxf
      obtain ⟨hrf, hrs, hrx⟩ := ih (max s x.abs) (fun y hy => hx y (by simp [hy])) hmf
      rw [hxv] at hmv
      rw [hmv] at hrs
      refine ⟨hrf, ?_, ?_⟩
      · exact (le_max_left _ _).trans hrs
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact (le_max_right _ _).trans hrs
        · exact hrx y hy

/-- `maxAbs` is finite, nonnegative, and bounds every input entry's magnitude.
The scan is exact even when entries are subnormal. -/
theorem maxAbs_correct (a : Array Float) (ha : a.all Float.isFinite = true)
    : (maxAbs a).isFinite = true
      ∧ 0 ≤ value (maxAbs a)
      ∧ ∀ i, i < a.size → |value (a.getD i 0.0)| ≤ value (maxAbs a) := by
  have hx : ∀ x ∈ a.toList, x.isFinite = true := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (by simpa using hx)
    exact (Array.all_eq_true.mp ha) i hi
  obtain ⟨hf, hs, hb⟩ := maxAbs_fold a.toList 0.0 hx (by decide)
  simp only [Array.foldl_toList] at hf hs hb
  change (maxAbs a).isFinite = true at hf
  change 0 ≤ value (maxAbs a) at hs
  refine ⟨hf, hs, ?_⟩
  intro i hi
  exact hb (a.getD i 0.0) (by simp [hi])

/-- A uniform finite input bound also bounds the selected normalization scale. -/
theorem maxAbs_le (a : Array Float) (M : ℝ) (ha : a.all Float.isFinite = true) (hM : 0 ≤ M)
    (hb : ∀ i, i < a.size → |value (a.getD i 0.0)| ≤ M)
    : value (maxAbs a) ≤ M := by
  have hfold (xs : List Float) (s : Float)
      (hx : ∀ x ∈ xs, x.isFinite = true ∧ |value x| ≤ M)
      (hs : s.isFinite = true) (hsv : value s ≤ M) :
      value (xs.foldl (fun a x => max a x.abs) s) ≤ M := by
    induction xs generalizing s with
    | nil => exact hsv
    | cons x xs ih =>
        have hxf := hx x (by simp)
        have hxa := abs_value x hxf.1
        have hm := max_value s x.abs hs hxa.1
        apply ih (max s x.abs) (fun y hy => hx y (by simp [hy])) hm.1
        rw [hm.2, hxa.2]
        exact max_le hsv hxf.2
  have h := hfold a.toList 0.0 (by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (by simpa using hx)
    exact ⟨(Array.all_eq_true.mp ha) i hi, by simpa [hi] using hb i hi⟩) (by decide) hM
  rw [Array.foldl_toList] at h
  change value (maxAbs a) ≤ M at h
  exact h

/-- A successful nonzero branch of the magnitude test gives a positive real
scale. IEEE equality is interpreted numerically, including both signed zeros. -/
theorem magnitude_positive (a : Array Float) (ha : a.all Float.isFinite = true)
    (hn : (maxAbs a == 0.0) = false)
    : 0 < value (maxAbs a) := by
  obtain ⟨hf, hs, _⟩ := maxAbs_correct a ha
  have hz : value (maxAbs a) ≠ 0 := by
    intro h
    have ht := (beq_iff (maxAbs a) 0.0 hf (by decide)).mpr h
    rw [hn] at ht
    contradiction
  exact lt_of_le_of_ne hs hz.symm

/-- The eigensolver's native input normalization always succeeds on finite,
nonzero input. Each result is within 2⁻⁵¹ of its exact scaled entry. This is a
proof of the actual `mapM` expression at the start of `jacobiEigen`. -/
theorem normalization_accuracy (a : Array Float) (ha : a.all Float.isFinite = true)
    (hn : (maxAbs a == 0.0) = false)
    : ∃ r,
        a.mapM (fun x => finite (x / maxAbs a)) = .ok r
        ∧ r.size = a.size
        ∧ r.all Float.isFinite = true
        ∧ ∀ i,
            i < a.size
            → |value (r.getD i 0.0) - value (a.getD i 0.0) / value (maxAbs a)|
              ≤ (2 : ℝ)^(-51 : Int) := by
  obtain ⟨hf, _, hb⟩ := maxAbs_correct a ha
  have hp := magnitude_positive a ha hn
  have he (i : Nat) (hi : i < a.size) :=
    div_error (a.getD i 0.0) (maxAbs a) 0
      (Flare.Matrix.Storage.getD_finite a i ha) hf (ne_of_gt hp) (by decide) (by decide)
      (by simpa only [zpow_zero, abs_div, abs_of_pos hp] using (div_le_one hp).mpr (hb i hi))
  have hmap : a.mapM (fun x => finite (x / maxAbs a)) = .ok (a.map (· / maxAbs a)) := by
    apply Flare.Matrix.Multiplication.mapM_eq_ok_map
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (by simpa using hx)
    have hfin : (a[i] / maxAbs a).isFinite = true := by simpa [hi] using (he i hi).1
    simp only [finite, hfin, ↓reduceIte]
  refine ⟨_, hmap, by simp, ?_, ?_⟩
  · rw [Array.all_eq_true]
    intro i hi
    have hi' : i < a.size := by simpa using hi
    simpa [hi'] using (he i hi').1
  · intro i hi
    simpa [hi] using (he i hi).2

end Flare.Matrix.Spectrum
