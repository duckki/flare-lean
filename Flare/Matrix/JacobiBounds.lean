module

public import Flare.Matrix.JacobiEnergy

/-! Iteration-wide magnitude invariants for native Jacobi. The energy allowances
are ghost proof quantities; no runtime bound or certificate is added. -/

@[expose] public section

namespace Flare.Matrix.JacobiBounds

open Flare.Matrix.Value Flare.Binary64.Value Flare.Matrix.Operations
open Flare.Matrix.JacobiIteration Flare.Matrix.JacobiEnergy
open Flare.Analysis.JacobiEnergy

/-- Finite storage, symmetry and slowly growing energy through the bounded
rotation sequence. The initial matrix allowance covers normalization rounding. -/
structure State (n step : Nat) (a v : Array Float) : Prop where
  matrix_size : a.size = n * n
  matrix_finite : a.all Float.isFinite = true
  vectors_size : v.size = n * n
  vectors_finite : v.all Float.isFinite = true
  symmetric : ∀ i j, i < n → j < n → value (entry n a i j) = value (entry n a j i)
  matrix_energy : energy (matrix n n a) ≤ (n : ℝ) ^ 2 + 1 / 4 + step * (2 : ℝ) ^ (-20 : Int)
  vectors_energy : energy (matrix n n v) ≤ (n : ℝ) + step * (2 : ℝ) ^ (-20 : Int)

/-- The energy invariant implies the local magnitude profile throughout the
entire runtime rotation allowance. -/
theorem state_energy_bound (n step : Nat) (a v : Array Float)
    (hn : n ≤ 18) (hstep : step ≤ 32 * n * n) (h : State n step a v)
    : energy (matrix n n a) ≤ 1024 ∧ energy (matrix n n v) ≤ 1024 := by
  have hstep' : step ≤ 10368 := hstep.trans (by nlinarith)
  have hstepR : (step : ℝ) ≤ 10368 := by exact_mod_cast hstep'
  have hnR : (n : ℝ) ≤ 18 := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha := h.matrix_energy
  have hv := h.vectors_energy
  norm_num only [zpow_neg, zpow_ofNat] at ha hv
  constructor <;> nlinarith

/-- Frobenius energy controls each stored, in-range entry. -/
theorem entries_of_energy (n : Nat) (a : Array Float) (h : energy (matrix n n a) ≤ 1024)
    : ∀ i j, i < n → j < n → |value (entry n a i j)| ≤ 32 := by
  intro i j hi hj
  have he := entry_sq_le_energy (matrix n n a) (⟨i, hi⟩ : Fin n) ⟨j, hj⟩
  change (value (entry n a i j))^2 ≤ _ at he
  nlinarith [sq_abs (value (entry n a i j)), abs_nonneg (value (entry n a i j))]

private lemma energy_allowance (n : Nat) (E E' : ℝ) (hn : n ≤ 18) (hE : E ≤ 1024)
    (h
      : E'
        ≤ (1 + (2 : ℝ) ^ (-40 : Int)) * E
          + (2 : ℝ) ^ (-28 : Int)
          + 2 * (2 : ℝ) ^ (-40 : Int) * n * ((2 : ℝ) ^ (-1022 : Int)) ^ 2)
    : E' ≤ E + (2 : ℝ) ^ (-20 : Int) := by
  have hη : (2 : ℝ)^(-1022 : Int) ≤ 1 :=
    (zpow_le_one_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr (by norm_num)
  have hη0 : 0 ≤ (2 : ℝ)^(-1022 : Int) := by positivity
  generalize hηdef : (2 : ℝ)^(-1022 : Int) = η at *
  have hηsq : η^2 ≤ 1 := by nlinarith
  have hnR : (n : ℝ) ≤ 18 := by exact_mod_cast hn
  have hterm : (n : ℝ) * η^2 ≤ 18 := by
    have hmul := mul_le_mul_of_nonneg_left hηsq (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith
  norm_num only [zpow_neg, zpow_ofNat] at h ⊢
  nlinarith

/-- Each successful pivot preserves the global energy invariant. Every local
entry bound and every finite-output premise is derived from that invariant. -/
theorem state_rotate (n step p q : Nat) (a v : Array Float)
    (hn : n ≤ 18) (hstep : step ≤ 32 * n * n) (hp : p < n) (hq : q < n) (hpq : p ≠ q)
    (h : State n step a v) (hstop : (1.0e-14 : Float) < (entry n a p q).abs)
    : ∃ result,
        rotate n a v p q = .ok result
        ∧ State n (step + 1) result.1 result.2
        ∧ offEnergy (matrix n n result.1)
          ≤ (1 + (2 : ℝ) ^ (-36 : Int)) * offEnergy (matrix n n a)
            - 2 * (value (entry n a p q)) ^ 2 := by
  have hE := state_energy_bound n step a v hn hstep h
  have ha := entries_of_energy n a hE.1
  have hv := entries_of_energy n v hE.2
  obtain ⟨result, he, hr⟩ := rotate_step n p q a v hp hq hpq h.matrix_size h.vectors_size
    h.matrix_finite h.vectors_finite ha hv hstop
  have hAE := rotation_total_energy n p q a v result hp hq hpq h.matrix_finite ha h.symmetric hstop
    hr
  have hVE := rotation_vector_energy n p q a v result hp hq hpq h.vectors_finite hv hr
  have hAM := energy_allowance n _ _ hn hE.1 hAE
  have hVM := energy_allowance n _ _ hn hE.2 (hVE.trans (by
    have hη : 0 ≤ (2 : ℝ)^(-1022 : Int) := by positivity
    have hε : 0 ≤ (2 : ℝ)^(-40 : Int) := by positivity
    have hδ : 0 ≤ (2 : ℝ)^(-28 : Int) := by positivity
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_nonneg (mul_nonneg hε hn0) (sq_nonneg ((2 : ℝ)^(-1022 : Int)))]))
  refine ⟨result, he, ⟨hr.matrix_size, hr.matrix_finite, hr.vectors_size, hr.vectors_finite,
    hr.symmetric n p q a v result h.symmetric, ?_, ?_⟩,
    rotation_energy_step n p q a v result hn hp hq hpq h.matrix_finite ha h.symmetric hstop hr⟩
  · calc
      _ ≤ energy (matrix n n a) + (2 : ℝ)^(-20 : Int) := hAM
      _ ≤ ((n : ℝ)^2 + 1 / 4 + step * (2 : ℝ)^(-20 : Int)) + (2 : ℝ)^(-20 : Int) :=
        add_le_add h.matrix_energy le_rfl
      _ = _ := by push_cast; ring
  · calc
      _ ≤ energy (matrix n n v) + (2 : ℝ)^(-20 : Int) := hVM
      _ ≤ ((n : ℝ) + step * (2 : ℝ)^(-20 : Int)) + (2 : ℝ)^(-20 : Int) :=
        add_le_add h.vectors_energy le_rfl
      _ = _ := by push_cast; ring

end Flare.Matrix.JacobiBounds
