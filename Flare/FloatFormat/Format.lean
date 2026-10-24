module

public import Init.Data.Float.Model.Float32
public import Mathlib.Basic.Real.Basic

/-! The two IEEE storage formats supported by the pinned Lean model. Values are
interpreted through the shared unpacked representation; exceptional values have
no rational interpretation. Format selection is explicit at every rounding site. -/

@[expose] public section

namespace Flare.FloatFormat.Format

/-- Supported IEEE storage widths, independent of a source-language dtype tag. -/
inductive Width where
  | binary32
  | binary64
deriving DecidableEq

/-- The pinned Lean format specification for a storage width. -/
abbrev Width.spec : Width → Float.Model.Format
  | .binary32 => .binary32
  | .binary64 => .binary64

/-- Fraction bits, excluding the implicit leading bit. -/
abbrev Width.fraction (w : Width) : Nat := w.spec.mantissaBitsWithoutImplicit

/-- Least dyadic exponent, including subnormals. -/
abbrev Width.minimum (w : Width) : Int := w.spec.minExponent

/-- Largest dyadic exponent of a canonical normal mantissa. -/
abbrev Width.maximum : Width → Int
  | .binary32 => 104
  | .binary64 => 971

/-- Exact finite meaning shared by both packed models. -/
def unpackedToRational : Float.Model.UnpackedFloat → Option ℚ
  | .notANumber => none
  | .infinity _ => none
  | .zero _ => some 0
  | .finite s m e _ => some ((s.apply (m : Int) : ℚ) * (2 : ℚ) ^ e)

/-- Decode a format's stored bits through Lean's unpacker. -/
def toRational (w : Width) (bits : BitVec w.spec.numBits) : Option ℚ :=
  unpackedToRational (Float.Model.UnpackedFloat.unpack w.spec bits)

/-- Interpret packing in the selected format. Packing requires a canonical input;
rounding theorems prove that condition before using it. -/
def packedValue (w : Width) (v : Float.Model.UnpackedFloat) : Option ℚ :=
  toRational w (Float.Model.UnpackedFloat.pack w.spec v)

/-- The supported formats have a positive number of fraction bits. -/
theorem Width.fraction_pos (w : Width) : 0 < w.fraction := by
  cases w <;> decide

/-- Both storage formats have room between the least exponent and overflow. -/
theorem Width.exponent_room (w : Width) : w.minimum ≤ w.maximum - 1 := by
  cases w <;> decide

/-- Expose the selected precision to arithmetic simplification. -/
theorem Width.spec_fraction (w : Width) : w.spec.mantissaBitsWithoutImplicit = w.fraction := rfl

/-- Expose the selected subnormal floor to arithmetic simplification. -/
theorem Width.spec_minimum (w : Width) : w.spec.minExponent = w.minimum := rfl

/-- Both signs of stored zero have the same exact rational meaning. -/
@[simp]
theorem packedValue_zero (w : Width) (s : Float.Model.UnpackedFloat.Sign)
    : packedValue w (.zero s) = some 0 := by
  cases w <;> cases s <;> rfl

end Flare.FloatFormat.Format
