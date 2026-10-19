module

public import Flare.Binary64.Order

/-! Equal finite real values have the same unpacked binary64 representation,
apart from signed zero. This proves exact numerical congruences used to preserve
symmetry during native normalization, without asserting signed-zero bit equality. -/

@[expose] public section

namespace Flare.Binary64.Congruence

open Float.Model Float.Model.UnpackedFloat
open Flare.Binary64.Value Flare.Binary64.Order

private theorem unpacked_compare_eq (x y : UnpackedFloat)
    (hx : x.isFinite = true) (hy : y.isFinite = true) (hc : x.compare y = some .eq)
    : x = y ∨ (∃ s, x = .zero s) ∧ ∃ s, y = .zero s := by
  cases x with
  | notANumber => simp [UnpackedFloat.isFinite] at hx
  | infinity s => simp [UnpackedFloat.isFinite] at hx
  | zero sx =>
      cases y with
      | notANumber => simp [UnpackedFloat.isFinite] at hy
      | infinity s => simp [UnpackedFloat.isFinite] at hy
      | zero sy => exact Or.inr ⟨⟨sx, rfl⟩, ⟨sy, rfl⟩⟩
      | finite sy n f hn => cases sy <;> simp [UnpackedFloat.compare] at hc
  | finite sx m e hm =>
      cases y with
      | notANumber => simp [UnpackedFloat.isFinite] at hy
      | infinity s => simp [UnpackedFloat.isFinite] at hy
      | zero sy => cases sx <;> simp [UnpackedFloat.compare] at hc
      | finite sy n f hn =>
          have h : sx = sy ∧ e = f ∧ m = n := by
            cases sx <;> cases sy <;>
              simp_all [UnpackedFloat.compare, Ordering.swap_eq_eq, Ordering.then_eq_eq]
          rcases h with ⟨rfl, rfl, rfl⟩
          exact Or.inl rfl

/-- Equality of finite real interpretations implies equal unpacked values,
with exactly the expected exception for the two signed-zero encodings. -/
theorem unpack_eq_or_zero (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (he : value x = value y)
    : x.toModel.unpack = y.toModel.unpack
      ∨ (∃ s, x.toModel.unpack = .zero s) ∧ ∃ s, y.toModel.unpack = .zero s := by
  have hc := compare_value x y hx hy
  rw [he, compare_eq_iff_eq.mpr rfl] at hc
  exact unpacked_compare_eq x.toModel.unpack y.toModel.unpack hx hy hc

/-- Native division preserves equality of real values under a common finite,
nonzero divisor, including equal zero numerators with different signs. -/
theorem div_value_congr (x y z : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hz : z.isFinite = true) (hz0 : value z ≠ 0) (he : value x = value y)
    : value (x / z) = value (y / z) := by
  have hxy := unpack_eq_or_zero x y hx hy he
  change (Flare.Binary64.Value.modelToReal
      (Float.Model.pack (UnpackedFloat.div Format.binary64 x.toModel.unpack z.toModel.unpack))).getD
        0 =
    (Flare.Binary64.Value.modelToReal
      (Float.Model.pack (UnpackedFloat.div Format.binary64 y.toModel.unpack z.toModel.unpack))).getD
        0
  rcases hxy with hxy | ⟨⟨sx, hsx⟩, ⟨sy, hsy⟩⟩
  · rw [hxy]
  · change z.toModel.unpack.isFinite = true at hz
    cases hu : z.toModel.unpack with
    | notANumber => simp [hu, UnpackedFloat.isFinite] at hz
    | infinity s => simp [hu, UnpackedFloat.isFinite] at hz
    | zero sz =>
        apply False.elim
        apply hz0
        simp [value, Flare.Binary64.Value.modelToReal, hu]
    | finite sz m e hm =>
        rw [hsx, hsy]
        cases sx <;> cases sy <;> cases sz <;> simp only [UnpackedFloat.div] <;> rfl

/-- Equal finite first operands give equal real sums, including signed zero. -/
theorem add_value_congr_left (x y z : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hz : z.isFinite = true) (he : value x = value y)
    : value (x + z) = value (y + z) := by
  have hxy := unpack_eq_or_zero x y hx hy he
  change (Flare.Binary64.Value.modelToReal (Float.Model.pack
    (UnpackedFloat.add Format.binary64 x.toModel.unpack z.toModel.unpack))).getD 0 =
    (Flare.Binary64.Value.modelToReal (Float.Model.pack
      (UnpackedFloat.add Format.binary64 y.toModel.unpack z.toModel.unpack))).getD 0
  rcases hxy with hxy | ⟨⟨sx, hsx⟩, ⟨sy, hsy⟩⟩
  · rw [hxy]
  · rw [hsx, hsy]
    change z.toModel.unpack.isFinite = true at hz
    cases hu : z.toModel.unpack with
    | notANumber => simp [hu, UnpackedFloat.isFinite] at hz
    | infinity s => simp [hu, UnpackedFloat.isFinite] at hz
    | zero sz => cases sx <;> cases sy <;> cases sz <;> rfl
    | finite sz m e hm => simp only [UnpackedFloat.add]

/-- Equal finite second operands give equal real sums, including signed zero. -/
theorem add_value_congr_right (x y z : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hz : z.isFinite = true) (he : value y = value z)
    : value (x + y) = value (x + z) := by
  have hyz := unpack_eq_or_zero y z hy hz he
  change (Flare.Binary64.Value.modelToReal (Float.Model.pack
    (UnpackedFloat.add Format.binary64 x.toModel.unpack y.toModel.unpack))).getD 0 =
    (Flare.Binary64.Value.modelToReal (Float.Model.pack
      (UnpackedFloat.add Format.binary64 x.toModel.unpack z.toModel.unpack))).getD 0
  rcases hyz with hyz | ⟨⟨sy, hsy⟩, ⟨sz, hsz⟩⟩
  · rw [hyz]
  · rw [hsy, hsz]
    change x.toModel.unpack.isFinite = true at hx
    cases hu : x.toModel.unpack with
    | notANumber => simp [hu, UnpackedFloat.isFinite] at hx
    | infinity s => simp [hu, UnpackedFloat.isFinite] at hx
    | zero sx => cases sx <;> cases sy <;> cases sz <;> rfl
    | finite sx m e hm => simp only [UnpackedFloat.add]

/-- Multiplying equal finite real values by the same finite scalar preserves
real equality even when the two encodings represent different zero signs. -/
theorem mul_value_congr_right (x y z : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hz : z.isFinite = true) (he : value y = value z)
    : value (x * y) = value (x * z) := by
  have hyz := unpack_eq_or_zero y z hy hz he
  change (Flare.Binary64.Value.modelToReal (Float.Model.pack
    (UnpackedFloat.mul Format.binary64 x.toModel.unpack y.toModel.unpack))).getD 0 =
    (Flare.Binary64.Value.modelToReal (Float.Model.pack
      (UnpackedFloat.mul Format.binary64 x.toModel.unpack z.toModel.unpack))).getD 0
  rcases hyz with hyz | ⟨⟨sy, hsy⟩, ⟨sz, hsz⟩⟩
  · rw [hyz]
  · rw [hsy, hsz]
    change x.toModel.unpack.isFinite = true at hx
    cases hu : x.toModel.unpack with
    | notANumber => simp [hu, UnpackedFloat.isFinite] at hx
    | infinity s => simp [hu, UnpackedFloat.isFinite] at hx
    | zero sx => cases sx <;> cases sy <;> cases sz <;> rfl
    | finite sx m e hm =>
        cases sx <;> cases sy <;> cases sz <;> simp only [UnpackedFloat.mul] <;> rfl

end Flare.Binary64.Congruence
