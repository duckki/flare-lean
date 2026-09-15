import Flare.Binary64.Value
import Mathlib.Data.Matrix.Basic

/-! Mathematical interpretation of row-major binary64 arrays. -/

namespace Flare.Matrix.Value
open Flare.Binary64.Value

/-- Ghost interpretation. Shape and finiteness are separate theorem premises;
missing entries and exceptional values are totalized to zero only here. -/
noncomputable def matrix (rows cols : Nat) (a : Array Float) : Matrix (Fin rows) (Fin cols) ℝ :=
  fun i j => value (a.getD (i.val * cols + j.val) 0.0)

end Flare.Matrix.Value
