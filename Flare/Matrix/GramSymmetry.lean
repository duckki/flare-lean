module

public import Flare.Matrix.Multiplication

/-! Exact word symmetry of the separately rounded two-state dense Gram
schedule. Ascending accumulation and commutative native products give identical
off-diagonal words. No magnitude or positivity premise, symmetry repair, or
averaging is used. Success and finite input are explicit premises. -/

@[expose] public section

namespace Flare.Matrix.GramSymmetry

open Flare.Matrix.Dense Flare.Matrix.Value
open Flare.Binary64.Arithmetic

private def dot2 (a b c d : Float) : Except Flare.Matrix.DenseError Float := do
  let first ← Flare.Matrix.Dense.finite (a * b)
  let s ← Flare.Matrix.Dense.finite (0.0 + first)
  let second ← Flare.Matrix.Dense.finite (c * d)
  Flare.Matrix.Dense.finite (s + second)

private theorem dot2_comm (a b c d : Float) : dot2 a b c d = dot2 b a d c := by
  unfold dot2
  rw [native_mul_comm a b, native_mul_comm c d]

private theorem store_four (x y z w : Float)
    : ((((Array.replicate 4 0.0).setIfInBounds 0 x).setIfInBounds 1 y).setIfInBounds 2
        z).setIfInBounds
        3 w
      = #[x, y, z, w] := by
  rfl

private theorem multiply_two_schedule (a b : Array Float)
    : Flare.Matrix.Dense.multiply 2 2 2 a b
      = (do
          let x ← dot2 (entry 2 a 0 0) (entry 2 b 0 0) (entry 2 a 0 1) (entry 2 b 1 0)
          let y ← dot2 (entry 2 a 0 0) (entry 2 b 0 1) (entry 2 a 0 1) (entry 2 b 1 1)
          let z ← dot2 (entry 2 a 1 0) (entry 2 b 0 0) (entry 2 a 1 1) (entry 2 b 1 0)
          let w ← dot2 (entry 2 a 1 0) (entry 2 b 0 1) (entry 2 a 1 1) (entry 2 b 1 1)
          return #[x, y, z, w]) := by
  simp [Flare.Matrix.Dense.multiply, dot2, Std.Legacy.Range.forIn_eq_forIn_range',
    List.range', List.forIn_cons, List.forIn_nil, bind_assoc, entry, -bind_pure_comp,
    store_four]

/-- The separately computed off-diagonal words are identical on every
successful finite two-state Gram multiplication. No magnitude or PD premise
is needed, so this also covers gradual underflow. -/
theorem multiply_gram_two_symmetric (a r : Array Float)
    (ha : a.all Float.isFinite = true)
    (hr : multiply 2 2 2 a (transpose 2 2 a) = .ok r)
    : entry 2 r 0 1 = entry 2 r 1 0 := by
  have h := hr
  rw [multiply_two_schedule] at h
  have ht : ∀ i j, i < 2 → j < 2 → entry 2 (transpose 2 2 a) i j = entry 2 a j i :=
    (Flare.Matrix.Multiplication.transpose_storage 2 2 a ha).2.2
  rw [ht 0 0 (by decide) (by decide), ht 1 0 (by decide) (by decide),
    ht 0 1 (by decide) (by decide), ht 1 1 (by decide) (by decide)] at h
  rw [dot2_comm (entry 2 a 1 0) (entry 2 a 0 0) (entry 2 a 1 1) (entry 2 a 0 1)] at h
  cases hx : dot2 (entry 2 a 0 0) (entry 2 a 0 0) (entry 2 a 0 1) (entry 2 a 0 1) <;>
    cases hy : dot2 (entry 2 a 0 0) (entry 2 a 1 0) (entry 2 a 0 1) (entry 2 a 1 1) <;>
    cases hw : dot2 (entry 2 a 1 0) (entry 2 a 1 0) (entry 2 a 1 1) (entry 2 a 1 1) <;>
    simp_all [bind, Except.bind, pure, Except.pure, entry, Flare.Matrix.Dense.entry]
  subst r
  rfl

/-- Exact Real decoding of the successful rounded two-state Gram is Hermitian. -/
theorem multiply_gram_two_hermitian (a r : Array Float)
    (ha : a.all Float.isFinite = true)
    (hr : multiply 2 2 2 a (transpose 2 2 a) = .ok r)
    : (matrix 2 2 r).IsHermitian := by
  have hs := multiply_gram_two_symmetric a r ha hr
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  change Flare.Binary64.Value.value (entry 2 r j.val i.val) =
    Flare.Binary64.Value.value (entry 2 r i.val j.val)
  fin_cases i <;> fin_cases j <;> simp [hs]

end Flare.Matrix.GramSymmetry
