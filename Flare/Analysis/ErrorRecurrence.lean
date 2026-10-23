module

public import Mathlib.Tactic

/-! Accumulation of certified local errors under a scalar step sensitivity.
No implementation or trajectory property is inferred from the recurrence. -/

@[expose] public section

namespace Flare.Analysis.ErrorRecurrence

noncomputable section

/-- Finite-horizon composition budget. L bounds sensitivity of each
step and δ its proved local error; neither is inferred here. -/
def accumulatedRadius (L δ initial : ℝ) : Nat → ℝ
  | 0 => initial
  | t + 1 => L * accumulatedRadius L δ initial t + δ

/-- Compose certified local radii once a step sensitivity and local error
bound have been established. Step sensitivity and local error are premises of this theorem. -/
theorem finite_horizon_bound (error : Nat → ℝ) (L δ initial : ℝ) (hL : 0 ≤ L)
    (h0 : error 0 ≤ initial) (hstep : ∀ t, error (t + 1) ≤ L * error t + δ)
    : ∀ t, error t ≤ accumulatedRadius L δ initial t := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
      exact (hstep t).trans (add_le_add (mul_le_mul_of_nonneg_left ih hL) (le_refl δ))

theorem nonexpansive_budget (L δ initial : ℝ) (hL : 0 ≤ L) (hL' : L ≤ 1)
    (hδ : 0 ≤ δ) (hinitial : 0 ≤ initial) (t : Nat)
    : accumulatedRadius L δ initial t ≤ initial + t * δ := by
  induction t with
  | zero => simp [accumulatedRadius]
  | succ t ih =>
      change L * accumulatedRadius L δ initial t + δ ≤ _
      have hbound := mul_le_mul_of_nonneg_left ih hL
      have hcoef := mul_le_mul_of_nonneg_right hL' (by positivity : 0 ≤ initial + (t : ℝ) * δ)
      simp only [one_mul] at hcoef
      simp only [Nat.cast_add, Nat.cast_one]
      linarith

/-- Compose a step-indexed simulation invariant over a bounded list. The relation
can include reached domains, finiteness and an accumulated numerical allowance.
Unlike a constant fold relation, each step may use a different invariant. -/
theorem foldl_contract {α σ τ : Type*} (native : σ → α → σ) (ideal : τ → α → τ)
    (R : Nat → σ → τ → Prop) (Input : α → Prop) (limit : Nat)
    (hstep : ∀ k < limit, ∀ x, Input x → ∀ n i, R k n i → R (k + 1) (native n x) (ideal i x))
    (xs : List α) (hxs : ∀ x ∈ xs, Input x) (start : Nat)
    (hsize : start + xs.length ≤ limit) (n : σ) (i : τ) (h0 : R start n i)
    : R (start + xs.length) (xs.foldl native n) (xs.foldl ideal i) := by
  induction xs generalizing start n i with
  | nil => simpa using h0
  | cons x xs ih =>
      have hx := hxs x (by simp)
      have htail : ∀ y ∈ xs, Input y := fun y hy => hxs y (by simp [hy])
      have hnext := hstep start (by simp only [List.length_cons] at hsize; omega) x hx n i h0
      have hsize' : start + 1 + xs.length ≤ limit := by
        simp only [List.length_cons] at hsize
        omega
      have h := ih htail (start + 1) hsize' _ _ hnext
      have heq : start + 1 + xs.length = start + (x :: xs).length := by
        simp only [List.length_cons]
        omega
      rw [heq] at h
      simpa only [List.foldl_cons] using h

/-- A local error recurrence and preserved domain invariant give a whole-fold
guarantee. Incoming error is propagated by `L`; it is never reset at a call. -/
theorem foldl_error_bound {α σ τ : Type*} (native : σ → α → σ) (ideal : τ → α → τ)
    (Inv : σ → τ → Prop) (Input : α → Prop) (error : σ → τ → ℝ)
    (L δ initial : ℝ) (hL : 0 ≤ L) (limit : Nat)
    (hstep
      : ∀ k < limit,
          ∀ x,
            Input x
            → ∀ n i,
                Inv n i
                → Inv (native n x) (ideal i x) ∧ error (native n x) (ideal i x) ≤ L * error n i + δ)
    (xs : List α) (hxs : ∀ x ∈ xs, Input x) (hsize : xs.length ≤ limit)
    (n : σ) (i : τ) (hInv : Inv n i) (h0 : error n i ≤ initial)
    : Inv (xs.foldl native n) (xs.foldl ideal i)
      ∧ error (xs.foldl native n) (xs.foldl ideal i) ≤ accumulatedRadius L δ initial xs.length := by
  have hlocal : ∀ k < limit, ∀ x, Input x → ∀ n i,
      (Inv n i ∧ error n i ≤ accumulatedRadius L δ initial k) →
      Inv (native n x) (ideal i x) ∧ error (native n x) (ideal i x) ≤
        accumulatedRadius L δ initial (k + 1) := by
    intro k hk x hx n i h
    obtain ⟨hInv', he⟩ := hstep k hk x hx n i h.1
    exact ⟨hInv', he.trans (add_le_add (mul_le_mul_of_nonneg_left h.2 hL) le_rfl)⟩
  simpa only [Nat.zero_add]
    using foldl_contract native ideal
      (fun k n i => Inv n i ∧ error n i ≤ accumulatedRadius L δ initial k)
      Input limit hlocal xs hxs 0 (by simpa using hsize) n i ⟨hInv, h0⟩

end
end Flare.Analysis.ErrorRecurrence
