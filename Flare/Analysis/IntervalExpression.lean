module

public import Mathlib.Tactic.Inclusion.Extension.Interval
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Basic.Real.Basic

/-! A small, typed expression language for kernel-checked rational enclosures.
Interval arithmetic reuses Mathlib's inclusion rules. Leaf bounds carry their
proofs; a computed enclosure is useful only through `Expr.check_sound`. This is
real arithmetic, independent of a source language or floating-point format. -/

@[expose] public section

namespace Flare.Analysis.IntervalExpression

open Inclusion

/-- A real variable together with proved, exact rational endpoint bounds. -/
structure Variable where
  lower : ℚ
  upper : ℚ
  value : ℝ
  bounds : (lower : ℝ) ≤ value ∧ value ≤ (upper : ℝ)

/-- Typed enclosure evidence. Powers retain repeated-variable correlations. -/
inductive Expr where
  | constant (value : ℚ)
  | atom (value : Variable)
  | add (left right : Expr)
  | mul (left right : Expr)
  | neg (arg : Expr)
  | pow (arg : Expr) (exponent : Nat)

/-- Interpret an expression in exact real arithmetic. -/
noncomputable def Expr.eval : Expr → ℝ
  | .constant q => q
  | .atom x => x.value
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval
  | .neg a => -a.eval
  | .pow a n => a.eval ^ n

/-- Compute a rational enclosure with Mathlib's verified interval operations. -/
def Expr.enclosure : Expr → Interval ℚ
  | .constant q => Interval.singleton q
  | .atom x => Interval.Icc x.lower x.upper
  | .add a b => a.enclosure.add b.enclosure
  | .mul a b => a.enclosure.mul b.enclosure
  | .neg a => a.enclosure.neg
  | .pow a n => a.enclosure.pow n

/-- Every expression value lies in its computed rational enclosure. -/
theorem Expr.enclosure_sound (e : Expr) : e.eval ∈ e.enclosure.map (Rat.castHom ℝ) := by
  induction e with
  | constant q => exact Interval.mem_map_singleton q _
  | atom x => exact Interval.mem_map_Icc _ x.bounds.1 x.bounds.2
  | add a b ha hb => exact Interval.add_mem (Rat.castHom ℝ).toAddMonoidHom ha hb
  | mul a b ha hb =>
      exact Interval.mul_mem Rat.castOrderEmbedding (by simp) (by simp) ha hb
  | neg a ha => exact Interval.neg_mem (Rat.castHom ℝ).toAddMonoidHom ha
  | pow a n ha =>
      exact Interval.pow_mem Rat.castOrderEmbedding (by simp) (by simp)
        (by simp) (fun q k => map_pow (Rat.castHom ℝ) q k) n ha

/-- Check that the computed, finite enclosure fits the proposed endpoints. -/
def Expr.check (e : Expr) (lower upper : ℚ) : Bool :=
  match e.enclosure.lb, e.enclosure.ub with
  | some lo, some hi => decide (lower ≤ lo ∧ hi ≤ upper)
  | _, _ => false

/-- Kernel computation of `check` discharges an exact real enclosure. -/
theorem Expr.check_sound {e : Expr} {lower upper : ℚ} (h : e.check lower upper = true)
    : (lower : ℝ) ≤ e.eval ∧ e.eval ≤ (upper : ℝ) := by
  have he := e.enclosure_sound
  cases hl : e.enclosure.lb with
  | bot => simp [Expr.check, hl] at h
  | coe lo =>
      cases hu : e.enclosure.ub with
      | top => simp [Expr.check, hu] at h
      | coe hi =>
          have hh : lower ≤ lo ∧ hi ≤ upper := by simpa [Expr.check, hl, hu] using h
          have hs : (lo : ℝ) ≤ e.eval ∧ e.eval ≤ (hi : ℝ) := by
            simpa [Interval.map, hl, hu] using he
          exact ⟨(Rat.cast_le.mpr hh.1).trans hs.1, hs.2.trans (Rat.cast_le.mpr hh.2)⟩

end Flare.Analysis.IntervalExpression
