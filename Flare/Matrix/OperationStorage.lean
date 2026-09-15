import Flare.Matrix.Operations
import Flare.Matrix.Value
import Flare.Matrix.Storage

/-! Shape and finiteness of successful elementwise numerical operations. -/

namespace Flare.Matrix.OperationStorage

open Std.Do Flare.Matrix.Value Flare.Matrix.Operations

set_option mvcgen.warning false

private theorem bind_ok {α β : Type} (x : Except Flare.Matrix.Error α)
    (f : α → Except Flare.Matrix.Error β) (b : β)
    : (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

private theorem successful {ε α : Type} {prog : Except ε α} {result : α}
    (P : α → Prop) (hs : ⦃⌜True⌝⦄ prog ⦃⇓? r => ⌜P r⌝⦄) (h : prog = .ok result)
    : P result := by
  rw [h] at hs
  exact hs True.intro

private theorem adapt_ok {α : Type} (p : Except Flare.Matrix.DenseError α) (r : α)
    : adapt p = .ok r ↔ p = .ok r := by
  cases p with
  | ok a => simp [adapt]
  | error e => cases e <;> simp [adapt]

@[spec]
theorem finite_spec (x : Float) : ⦃⌜True⌝⦄ finite x ⦃⇓? y => ⌜y.isFinite = true⌝⦄ := by
  mvcgen [finite]

private theorem push_storage (a : Array Float) (x : Float) (n : Nat)
    (ha : a.size = n ∧ a.all Float.isFinite = true) (hx : x.isFinite = true)
    : (a.push x).size = n + 1 ∧ (a.push x).all Float.isFinite = true := by
  refine ⟨by simpa only [Array.size_push] using congrArg (· + 1) ha.1, ?_⟩
  simpa only [← Array.all_toList, Array.toList_push, List.all_append,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    using And.intro ha.2 hx

@[spec]
theorem combine_spec (a b : Array Float) (s : Float)
    : ⦃⌜True⌝
      ⦄ combine a b s
      ⦃⇓? r => ⌜r.size = a.size ∧ r.all Float.isFinite = true⌝⦄ := by
  -- leanfmt 0.4.1 misindents the mvcgen alternatives below.
  -- leanfmt: off next
  mvcgen [combine, Array.mapM_eq_foldlM] invariants
  · ⇓? ⟨xs, r⟩ => ⌜r.size = xs.prefix.length ∧ r.all Float.isFinite = true⌝
  with
  | vc1 =>
    intros
    simpa only [List.length_append, List.length_singleton] using push_storage _ _ _ ‹_› ‹_›
  | vc4 => exact ⟨rfl, by simp⟩
  | vc5 => simpa only [Array.length_toList, Array.size_range] using And.intro

@[spec]
theorem scale_spec (a : Array Float) (s : Float)
    : ⦃⌜True⌝
      ⦄ scale a s
      ⦃⇓? r => ⌜r.size = a.size ∧ r.all Float.isFinite = true⌝⦄ := by
  -- leanfmt 0.4.1 misindents the mvcgen alternatives below.
  -- leanfmt: off next
  mvcgen [scale, Array.mapM_eq_foldlM] invariants
  · ⇓? ⟨xs, r⟩ => ⌜r.size = xs.prefix.length ∧ r.all Float.isFinite = true⌝
  with
  | vc1 =>
    intros
    simpa only [List.length_append, List.length_singleton] using push_storage _ _ _ ‹_› ‹_›
  | vc3 => exact ⟨rfl, by simp⟩
  | vc4 => simpa only [Array.length_toList] using And.intro

end Flare.Matrix.OperationStorage
