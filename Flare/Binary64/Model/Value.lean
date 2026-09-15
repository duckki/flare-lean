import Mathlib.Data.Real.Basic
import Init.Data.Float.Model.Float

/-!
# Exact rational and real meanings of binary64 model values

Interpret Lean's unpacked constructors at the pinned toolchain version. Rational
arithmetic is proof support and does not occur in the native numerical kernels.
Both signed zeros have numeric value zero; NaNs and infinities have no value.
-/

namespace Flare.Binary64.Model.Value

/-- interpret the external unpacked constructors as exact rationals when
finite. The zero constructor includes both signs; sentinels return `none`. -/
def unpackedToRational : Float.Model.UnpackedFloat → Option ℚ
  | .notANumber => none
  | .infinity _ => none
  | .zero _ => some 0
  | .finite sign mantissa exponent _ =>
      some ((sign.apply (mantissa : ℤ) : ℚ) * (2 : ℚ) ^ exponent)

/-- exact rational interpretation of a stored binary64 value, using the
pinned external decoder rather than a separately invented bit layout. -/
def toRational (value : Float.Model) : Option ℚ :=
  unpackedToRational value.unpack

/-- finite stored values embed exactly into the reals. This is not a
conversion from an arbitrary real value to a representable float. -/
def toReal (value : Float.Model) : Option ℝ :=
  (toRational value).map (fun q => (q : ℝ))

/-- interpretation of Lean `Float` through its logical model. Native runtime
agreement and CPython behavior remain separate external execution assumptions. -/
def floatToRational (value : Float) : Option ℚ :=
  toRational value.toModel

/-- Retain a finite model value; reject NaNs and infinities. -/
def finite (value : Float.Model) : Option Float.Model :=
  if value.isFinite then some value else none

end Flare.Binary64.Model.Value
