module

public import Flare.Binary64.Congruence
public import Flare.Binary64.Nearest

/-! Exact zero behavior of native binary64 operations. These lemmas preserve
real zero without requiring the two signed-zero encodings to be identical. -/

@[expose] public section

namespace Flare.Binary64.Zero
open Float.Model Float.Model.UnpackedFloat
open Flare.Binary64.Value Flare.Binary64.Arithmetic

lemma unpack_zero (a : Float) (ha : a.isFinite = true) (hv : value a = 0)
    : ∃ s, a.toModel.unpack = .zero s := by
  rcases Flare.Binary64.Congruence.unpack_eq_or_zero a 0.0 ha (by decide) hv with h | ⟨h, _⟩
  · exact ⟨.positive, h⟩
  · exact h

/-- Adding either signed zero to either signed zero preserves real zero. -/
theorem add_zero (a b : Float) (ha : a.isFinite = true) (hb : b.isFinite = true)
    (ha0 : value a = 0) (hb0 : value b = 0)
    : (a + b).isFinite = true ∧ value (a + b) = 0 := by
  have hf := Flare.Binary64.Nearest.add_error_nearest a b ha hb (by rw [ha0, hb0]; simp)
  refine ⟨hf.1, ?_⟩
  obtain ⟨sa, hsa⟩ := unpack_zero a ha ha0
  obtain ⟨sb, hsb⟩ := unpack_zero b hb hb0
  change (Flare.Binary64.Value.modelToReal (Float.Model.pack
    (UnpackedFloat.add Format.binary64 a.toModel.unpack b.toModel.unpack))).getD 0 = 0
  rw [hsa, hsb]
  cases sa <;> cases sb <;> rfl

/-- Adding either signed zero to a finite operand introduces no numerical error.
The resulting zero sign is deliberately not specified. -/
theorem add_right_zero (a b : Float) (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hb0 : value b = 0)
    : (a + b).isFinite = true ∧ value (a + b) = value a := by
  obtain ⟨sb, hsb⟩ := unpack_zero b hb hb0
  have he : Flare.Binary64.Value.modelToReal (a + b).toModel =
      Flare.Binary64.Value.modelToReal a.toModel := by
    change Flare.Binary64.Value.modelToReal (Float.Model.pack
      (UnpackedFloat.add Format.binary64 a.toModel.unpack b.toModel.unpack)) = _
    rw [hsb]
    change a.toModel.unpack.isFinite = true at ha
    cases hua : a.toModel.unpack with
    | notANumber => simp [hua, UnpackedFloat.isFinite] at ha
    | infinity s => simp [hua, UnpackedFloat.isFinite] at ha
    | zero sa =>
        cases sa <;> cases sb <;> simp [UnpackedFloat.add,
          Flare.Binary64.Value.modelToReal, hua] <;> rfl
    | finite sa m e hm =>
        simp only [UnpackedFloat.add]
        rw [← hua, interpretation_eq, interpretation_eq]
        simp only [Flare.Binary64.Model.Value.toReal,
          Flare.Binary64.Model.Rounding.pack_unpack_rational]
  exact ⟨finite_of_value _ _ (he.trans (finite_value a ha)), by simp only [value, he]⟩

/-- A product with exact real value zero remains zero, including underflow
inputs and differing zero signs. -/
theorem mul_zero (a b : Float) (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hzero : value a * value b = 0)
    : (a * b).isFinite = true ∧ value (a * b) = 0 := by
  have hf := Flare.Binary64.Nearest.mul_error_nearest a b ha hb (by rw [hzero]; simp)
  refine ⟨hf.1, ?_⟩
  change (Flare.Binary64.Value.modelToReal (Float.Model.pack
    (UnpackedFloat.mul Format.binary64 a.toModel.unpack b.toModel.unpack))).getD 0 = 0
  rcases mul_eq_zero.mp hzero with ha0 | hb0
  · obtain ⟨sa, hsa⟩ := unpack_zero a ha ha0
    rw [hsa]
    change b.toModel.unpack.isFinite = true at hb
    cases hbu : b.toModel.unpack with
    | notANumber => simp [hbu, UnpackedFloat.isFinite] at hb
    | infinity s => simp [hbu, UnpackedFloat.isFinite] at hb
    | zero sb => cases sa <;> cases sb <;> rfl
    | finite sb m e hm => cases sa <;> cases sb <;> simp only [UnpackedFloat.mul] <;> rfl
  · obtain ⟨sb, hsb⟩ := unpack_zero b hb hb0
    rw [hsb]
    change a.toModel.unpack.isFinite = true at ha
    cases hau : a.toModel.unpack with
    | notANumber => simp [hau, UnpackedFloat.isFinite] at ha
    | infinity s => simp [hau, UnpackedFloat.isFinite] at ha
    | zero sa => cases sa <;> cases sb <;> rfl
    | finite sa m e hm => cases sa <;> cases sb <;> simp only [UnpackedFloat.mul] <;> rfl

/-- Zero divided by a finite nonzero denominator preserves real zero. -/
theorem div_zero (a b : Float) (ha : a.isFinite = true) (hb : b.isFinite = true)
    (ha0 : value a = 0) (hb0 : value b ≠ 0)
    : (a / b).isFinite = true ∧ value (a / b) = 0 := by
  have hf := Flare.Binary64.Nearest.div_error_nearest a b ha hb hb0 (by rw [ha0]; simp)
  refine ⟨hf.1, ?_⟩
  obtain ⟨sa, hsa⟩ := unpack_zero a ha ha0
  change (Flare.Binary64.Value.modelToReal (Float.Model.pack
    (UnpackedFloat.div Format.binary64 a.toModel.unpack b.toModel.unpack))).getD 0 = 0
  rw [hsa]
  change b.toModel.unpack.isFinite = true at hb
  cases hbu : b.toModel.unpack with
  | notANumber => simp [hbu, UnpackedFloat.isFinite] at hb
  | infinity s => simp [hbu, UnpackedFloat.isFinite] at hb
  | zero sb => exact (hb0 (by simp [value, Flare.Binary64.Value.modelToReal, hbu])).elim
  | finite sb m e hm => cases sa <;> cases sb <;> simp only [UnpackedFloat.div] <;> rfl

end Flare.Binary64.Zero
