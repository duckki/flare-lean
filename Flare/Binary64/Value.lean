import Init.Data.Float.Float
import Mathlib.Basic.Real.Basic

/-!
# Real interpretation of binary64 values

Source: Lean v4.33.1, `Init/Data/Float/Model/Float.lean` and
`Init/Data/Float/Model/Unpacked/{Basic,Sign,Pack/Basic}.lean`.
<https://github.com/leanprover/lean4/tree/v4.33.1/src/lean/Init/Data/Float/Model>

Finite values mean a signed integer mantissa times an integer power of two.
Lean's unpacking supplies the representation details, including subnormals.
NaNs and infinities have no real interpretation. Both signed zeros mean real
zero; equality of interpreted values does not imply equality of stored bits.

These definitions are mathematical interpretations for specifications and
proofs. They do not implement an executable conversion to exact real numbers,
and they do not establish correspondence with another language's runtime.
-/

namespace Flare.Binary64.Value

/-- Exact real meaning of a finite `Float.Model`; `none` for NaN and infinity. -/
noncomputable def modelToReal (value : Float.Model) : Option ℝ :=
  match value.unpack with
  | .notANumber => none
  | .infinity _ => none
  | .zero _ => some 0
  | .finite sign mantissa exponent _ =>
      some ((sign.apply (mantissa : Int) : ℝ) * (2 : ℝ) ^ exponent)

/-- Real meaning of a native `Float` through Lean's logical binary64 model. -/
noncomputable def toReal (value : Float) : Option ℝ :=
  modelToReal value.toModel

/-- Totalized ghost value. Exceptional values map to zero only to simplify
statements; arithmetic theorems separately require finite operands. -/
noncomputable def value (x : Float) : ℝ :=
  (modelToReal x.toModel).getD 0

end Flare.Binary64.Value
