module

public import Flare.Binary64.Pipeline
public import Flare.Binary64.Nearest
public import Flare.Binary64.Zero

/-! Typed, kernel-checked numerical summaries for ordered native operations.
Producers propose rational ranges and error allowances. These checks do not trust
those annotations: their soundness theorems retain the native operation, its
independent ideal operands, finiteness, incoming errors and gradual underflow. -/

@[expose] public section

namespace Flare.Binary64.CheckedBounds

open Flare.Binary64.Pipeline Flare.Binary64.Value

/-- A proposed centered native range, ideal magnitude and absolute error. -/
structure Summary where
  centre : ℚ
  radius : ℚ
  ideal : ℚ
  error : ℚ
deriving Repr, DecidableEq

/-- Meaning of a summary for one actual native value and its independent ideal. -/
def Summary.Holds (s : Summary) (n : Float) (i : ℝ) : Prop :=
  NativeBounds s.centre s.radius s.ideal s.error n i

/-- Absolute native magnitude obtained from a centered range. -/
def Summary.cap (s : Summary) : ℚ := |s.centre| + s.radius

/-- Check weakening of a previously justified summary. -/
def fits (a b : Summary) : Bool :=
  decide (a.radius + |a.centre - b.centre| ≤ b.radius ∧ a.ideal ≤ b.ideal ∧ a.error ≤ b.error)

/-- A successful numeric weakening preserves every part of the contract. -/
theorem fits_sound {a b : Summary} {n : Float} {i : ℝ} (h : a.Holds n i) (hc : fits a b = true)
    : b.Holds n i := by
  have hh : a.radius + |a.centre - b.centre| ≤ b.radius ∧
      a.ideal ≤ b.ideal ∧ a.error ≤ b.error := of_decide_eq_true hc
  apply native_weaken h
  · exact_mod_cast hh.1
  · exact_mod_cast hh.2.1
  · exact_mod_cast hh.2.2

/-- Summary before the final rounding of a multiplication. -/
def product (a b : Summary) : Summary :=
  ⟨
    a.centre * b.centre,
    a.radius * b.cap + |a.centre| * b.radius,
    a.ideal * b.ideal,
    a.error * b.cap + a.ideal * b.error
  ⟩

/-- Add a local rounding allowance without changing the independent ideal. -/
def rounded (s : Summary) (rho : ℚ) : Summary :=
  ⟨s.centre, s.radius + rho, s.ideal, s.error + rho⟩

/-- Rational form of the existing nearest/even law, including subnormal results. -/
def roundingCheck (cap rho : ℚ) : Bool :=
  decide
    (cap ≤ (2 : ℚ) ^ (1000 : Int) ∧ (2 : ℚ) ^ (-53 : Int) * (cap + (2 : ℚ) ^ (-1022 : Int)) ≤ rho)

/-- Check one multiplication annotation against the proved native rule. -/
def checkMul (a b result : Summary) (rho : ℚ) : Bool :=
  roundingCheck (a.cap * b.cap) rho && fits (rounded (product a b) rho) result

/-- A checked multiplication annotation proves finite execution and actual error. -/
theorem mul_sound {a b result : Summary} {n p : Float} {i j : ℝ} {rho : ℚ}
    (ha : a.Holds n i) (hb : b.Holds p j)
    (hc : checkMul a b result rho = true)
    : result.Holds (n * p) (i * j) := by
  simp only [checkMul, Bool.and_eq_true] at hc
  obtain ⟨hr, hw⟩ := hc
  have hr' : a.cap * b.cap ≤ (2 : ℚ) ^ (1000 : Int) ∧
      (2 : ℚ) ^ (-53 : Int) * (a.cap * b.cap + (2 : ℚ) ^ (-1022 : Int)) ≤ rho :=
    of_decide_eq_true hr
  have hm : |value n * value p| ≤ ((a.cap * b.cap : ℚ) : ℝ) := by
    simpa [Summary.cap] using abs_product (native_bound ha.bounds) (native_bound hb.bounds)
  have finite := Nearest.mul_error_nearest n p ha.finite hb.finite
    (hm.trans (by exact_mod_cast hr'.1))
  have herr : |value (n * p) - value n * value p| ≤ (rho : ℝ) := by
    apply finite.2.trans
    calc
      _ ≤ (2 : ℝ) ^ (-53 : Int) * (((a.cap * b.cap : ℚ) : ℝ) + (2 : ℝ) ^ (-1022 : Int)) :=
        mul_le_mul_of_nonneg_left (add_le_add hm le_rfl) (by positivity)
      _ ≤ _ := by
        have h := (Rat.cast_le (K := ℝ)).mpr hr'.2
        simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_zpow, Rat.cast_ofNat] using h
  apply fits_sound (a := rounded (product a b) rho) (hc := hw)
  refine ⟨finite.1, ?_⟩
  simpa [rounded, product, Summary.cap]
    using (Pipeline.rounded (mul_bounds ha.bounds hb.bounds) herr)

/-- Exact-zero multiplication is available only with a justified zero native cap. -/
def checkMulZero (a b result : Summary) : Bool :=
  decide (a.cap = 0 ∨ b.cap = 0) && fits (product a b) result

/-- Exact multiplication by zero retains any incoming ideal-operand error. -/
theorem mul_zero_sound {a b result : Summary} {n p : Float} {i j : ℝ}
    (ha : a.Holds n i) (hb : b.Holds p j)
    (hc : checkMulZero a b result = true)
    : result.Holds (n * p) (i * j) := by
  simp only [checkMulZero, Bool.and_eq_true] at hc
  obtain ⟨hz, hw⟩ := hc
  have hz' : a.cap = 0 ∨ b.cap = 0 := of_decide_eq_true hz
  have hzero : value n * value p = 0 := by
    rcases hz' with h | h
    · have hn := native_bound ha.bounds
      have hcap : |(a.centre : ℝ)| + a.radius = 0 := by exact_mod_cast h
      rw [hcap] at hn
      rw [abs_eq_zero.mp (le_antisymm hn (abs_nonneg _)), zero_mul]
    · have hp := native_bound hb.bounds
      have hcap : |(b.centre : ℝ)| + b.radius = 0 := by exact_mod_cast h
      rw [hcap] at hp
      rw [abs_eq_zero.mp (le_antisymm hp (abs_nonneg _)), mul_zero]
  have exact := Zero.mul_zero n p ha.finite hb.finite hzero
  apply fits_sound (a := product a b) (hc := hw)
  refine ⟨exact.1, ?_⟩
  have he : value (n * p) = value n * value p := exact.2.trans hzero.symm
  simpa [product, Summary.cap, he] using mul_bounds ha.bounds hb.bounds

end Flare.Binary64.CheckedBounds
