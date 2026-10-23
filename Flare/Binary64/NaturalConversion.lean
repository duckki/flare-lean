module

public import Flare.Binary64.Model.NaturalConversion
public import Flare.Binary64.Arithmetic

/-! Native conversion wrappers for FLARE's exact bounded natural-number model.
Both lemmas preserve subtraction in the original integer representation. -/

@[expose] public section

namespace Flare.Binary64.NaturalConversion

open Flare.Binary64.Value Flare.Binary64.Arithmetic

/-- All unsigned integers strictly below 2^53 convert exactly to native
binary64, including zero. Native runtime/model agreement remains an execution
assumption shared with the imported FLARE operations. -/
theorem uint64_exact (n : UInt64) (hb : n.toNat < 2 ^ 53)
    : n.toFloat.isFinite = true ∧ value n.toFloat = (n.toNat : ℝ) := by
  have hr := Flare.Binary64.Model.NaturalConversion.ofNat_exact n.toNat hb
  have hm : n.toFloat.toModel = Float.Model.ofNat n.toNat := rfl
  have hv : Flare.Binary64.Value.modelToReal n.toFloat.toModel = some (n.toNat : ℝ) := by
    rw [interpretation_eq, hm]
    simp [Flare.Binary64.Model.Value.toReal, hr]
  exact ⟨finite_of_value _ _ hv, by simp [value, hv]⟩

/-- Subtract in the original integer representation before converting. -/
theorem uint64_difference_exact (previous current : UInt64) (horder : previous ≤ current)
    (hb : current.toNat - previous.toNat < 2 ^ 53)
    : (current - previous).toFloat.isFinite = true
      ∧ value (current - previous).toFloat = (current.toNat : ℝ) - previous.toNat := by
  have hd := UInt64.toNat_sub_of_le current previous horder
  have hn : previous.toNat ≤ current.toNat := horder
  simpa only [hd, Nat.cast_sub hn]
    using uint64_exact (current - previous) (by simpa only [hd] using hb)

end Flare.Binary64.NaturalConversion
