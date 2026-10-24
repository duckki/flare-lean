module

public import Flare.Binary32.Conversion
public import Flare.Binary64.Pipeline

/-! Composable numerical bounds for binary32 storage between binary64 operations.
Storage adds its own checked allowance and retains all incoming reference error. -/

@[expose] public section

namespace Flare.Binary32.StorageBounds

open Flare.Binary64.Value Flare.Binary64.Arithmetic Flare.Binary64.Pipeline

/-- The model-backed storage round trip is finite and has its format's proved
absolute one-ulp allowance on the selected magnitude range. -/
theorem roundTrip_error (x : Float) (N : Int) (hf : x.isFinite = true)
    (hN : -126 ≤ N) (hN' : N ≤ 126) (hv : |value x| ≤ (2 : ℝ) ^ N)
    : (Conversion.roundTrip x).isFinite = true
      ∧ |value (Conversion.roundTrip x) - value x| ≤ (2 : ℝ) ^ (N - 23) := by
  obtain ⟨r, hr, hre⟩ := Flare.Binary64.Model.Arithmetic.rational_of_real x.toModel (value x)
    (by rw [← interpretation_eq]; exact finite_value x hf)
  have hvr : |r| ≤ (2 : ℚ) ^ N := by
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_abs, Rat.cast_zpow, Rat.cast_ofNat, hre] using hv
  obtain ⟨q, hq, he⟩ := Conversion.roundTrip_error x r N hr hN hN' hvr
  have heq : Flare.Binary64.Value.modelToReal (Conversion.roundTrip x).toModel = some (q : ℝ) := by
    rw [interpretation_eq]
    simp [Flare.Binary64.Model.Value.toReal, hq]
  refine ⟨finite_of_value _ _ heq, ?_⟩
  have he' := (Rat.cast_le (K := ℝ)).mpr he
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_zpow, Rat.cast_ofNat, hre, value, heq,
    Option.getD_some]
    using he'

/-- Retain the independent exact value while adding storage rounding error. -/
theorem native_roundTrip {C W I E i rho : ℝ} {x : Float}
    (b : NativeBounds C W I E x i) (N : Int)
    (hN : -126 ≤ N) (hN' : N ≤ 126)
    (hv : |C| + W ≤ (2 : ℝ) ^ N) (hrho : (2 : ℝ) ^ (N - 23) ≤ rho)
    : NativeBounds C (W + rho) I (E + rho) (Conversion.roundTrip x) i := by
  have h := roundTrip_error x N b.finite hN hN' ((native_bound b.bounds).trans hv)
  exact ⟨h.1, rounded b.bounds (h.2.trans hrho)⟩

end Flare.Binary32.StorageBounds
