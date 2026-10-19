module

public import Std.Tactic.Do
public import Std.WP.Triple.SpecLemmas

/-! Exact bridges from the existing matrix specifications to the `vcgen` proof framework. -/

@[expose] public section

namespace Flare.Matrix.Specification

open Std.Do
open scoped Std.WP

/-- A successful concrete result passes its value to the postcondition. -/
@[spec]
theorem except_ok {α ε : Type} (a : α) (post : α → Prop) (epost : ε → Prop)
    : Std.WP.Triple (Except.ok a : Except ε α) (post a) post epost :=
  ⟨id⟩

/-- A concrete exceptional result uses exactly its exceptional postcondition. -/
@[spec]
theorem except_error {α ε : Type} (e : ε) (post : α → Prop) (epost : ε → Prop)
    : Std.WP.Triple (Except.error e : Except ε α) (epost e) post epost :=
  ⟨id⟩

/-- The two specification frameworks agree on both successful and exceptional outcomes. -/
theorem except_iff {α ε : Type} (x : Except ε α)
    (P : Assertion (.except ε .pure)) (Q : PostCond α (.except ε .pure))
    : Std.Do.Triple x P Q
      ↔ Std.WP.Triple x P.down (fun a => (Q.1 a).down) (fun e => (Q.2.1 e).down) := by
  cases x with
  | ok a =>
      constructor
      · intro h; exact ⟨h⟩
      · intro h; exact h.le_wp
  | error e =>
      constructor
      · intro h; exact ⟨h⟩
      · intro h; exact h.le_wp

/-- The two specification frameworks agree on pure computations. -/
theorem id_iff {α : Type} (x : Id α) (P : Assertion .pure) (Q : PostCond α .pure)
    : Std.Do.Triple x P Q ↔ Std.WP.Triple x P.down (fun a => (Q.1 a).down) Std.WP.EStackEnd.mk := by
  constructor
  · intro h; exact ⟨h⟩
  · intro h; exact h.le_wp

end Flare.Matrix.Specification
