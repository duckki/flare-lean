module

public import Flare.Matrix.Operations
public import Flare.Matrix.Value
public import Flare.Matrix.Storage

/-! Shape and finiteness of successful elementwise numerical operations. -/

@[expose] public section

namespace Flare.Matrix.OperationStorage

open Std.Do Flare.Matrix.Value Flare.Matrix.Operations

set_option experimental.vcgen true

attribute [local instance] Std.Internal.Order.instPartialOrderProp
  Std.Internal.Order.instCompleteLatticeProp

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
  apply (Specification.except_iff _ _ _).mpr
  vcgen [finite] with finish

open scoped Std.WP in
/-- `vcgen` form of the checked scalar operation's success guarantee. -/
@[spec]
theorem finite_wp_spec (x : Float)
    : Std.WP.Triple (finite x) True (fun y => y.isFinite = true) (fun _ => True) :=
  (Specification.except_iff _ _ _).mp (finite_spec x)

open scoped Std.WP in
/-- A finite operand passes the check unchanged. -/
theorem finite_wp_exact (x : Float)
    : Std.WP.Triple (finite x) (x.isFinite = true) (fun y => y = x) (fun _ => False) := by
  vcgen [finite] with finish

private theorem push_storage (a : Array Float) (x : Float) (n : Nat)
    (ha : a.size = n ∧ a.all Float.isFinite = true) (hx : x.isFinite = true)
    : (a.push x).size = n + 1 ∧ (a.push x).all Float.isFinite = true := by
  refine ⟨by simpa only [Array.size_push] using congrArg (· + 1) ha.1, ?_⟩
  simpa only [← Array.all_toList, Array.toList_push, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true]
    using And.intro ha.2 hx

@[spec]
theorem combine_spec (a b : Array Float) (s : Float)
    : ⦃⌜True⌝
      ⦄ combine a b s
      ⦃⇓? r => ⌜r.size = a.size ∧ r.all Float.isFinite = true⌝⦄ := by
  apply (Specification.except_iff _ _ _).mpr
  vcgen [combine, Array.mapM_eq_foldlM] invariants
  · fun pref _ r => r.size = pref.length ∧ r.all Float.isFinite = true
  all_goals simp_all only [SPred.down_pure_nil, Array.length_toList, Array.size_range]
  all_goals first
  | (solve | trivial)
  | (solve |
    simpa only [List.length_append, List.length_singleton] using push_storage _ _ _ ‹_› ‹_›)
  | (solve |
    rename_i r hr
    refine ⟨True.intro, ?_⟩
    simpa only [← hr.1] using hr.2)
  | (solve | exact ⟨rfl, by simp⟩)

@[spec]
theorem scale_spec (a : Array Float) (s : Float)
    : ⦃⌜True⌝
      ⦄ scale a s
      ⦃⇓? r => ⌜r.size = a.size ∧ r.all Float.isFinite = true⌝⦄ := by
  apply (Specification.except_iff _ _ _).mpr
  vcgen [scale, Array.mapM_eq_foldlM] invariants
  · fun pref _ r => r.size = pref.length ∧ r.all Float.isFinite = true
  all_goals simp_all only [SPred.down_pure_nil, Array.length_toList]
  all_goals first
  | (solve | trivial)
  | (solve |
    simpa only [List.length_append, List.length_singleton] using push_storage _ _ _ ‹_› ‹_›)
  | (solve |
    rename_i r hr
    refine ⟨True.intro, ?_⟩
    simpa only [← hr.1] using hr.2)
  | (solve | exact ⟨rfl, by simp⟩)

end Flare.Matrix.OperationStorage
