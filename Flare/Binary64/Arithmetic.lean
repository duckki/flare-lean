import Flare.Binary64.Value
import Flare.Binary64.Model.Arithmetic
import Flare.Analysis.Dyadic

/-!
# Native binary64 arithmetic bounds

The interpretation bridge identifies direct real values with the rational-backed
model semantics. All arithmetic bounds follow from Lean's Float.Model operations.
-/

open Flare.Analysis.Dyadic

namespace Flare.Binary64.Arithmetic
open Flare.Binary64.Value Flare.Analysis.Dyadic

lemma one_value : value (1.0 : Float) = 1 := by
  change (((2^52 : Nat) : ℝ) * (2 : ℝ)^(-52 : Int)) = 1
  norm_num

lemma zero_value : value (0.0 : Float) = 0 := rfl

lemma interpretation_eq (x : Float.Model)
    : Flare.Binary64.Value.modelToReal x = Flare.Binary64.Model.Value.toReal x := by
  unfold Flare.Binary64.Value.modelToReal Flare.Binary64.Model.Value.toReal
    Flare.Binary64.Model.Value.toRational
  cases x.unpack <;>
    simp [Flare.Binary64.Model.Value.unpackedToRational, Rat.cast_mul,
      Rat.cast_intCast, Rat.cast_zpow]

lemma finite_value (x : Float) (h : x.isFinite = true)
    : Flare.Binary64.Value.modelToReal x.toModel = some (value x) := by
  change x.toModel.unpack.isFinite = true at h
  unfold value Flare.Binary64.Value.modelToReal
  cases hx : x.toModel.unpack <;> simp_all [Float.Model.UnpackedFloat.isFinite]

lemma finite_of_value (x : Float) (y : ℝ) (h : Flare.Binary64.Value.modelToReal x.toModel = some y)
    : x.isFinite = true := by
  change x.toModel.unpack.isFinite = true
  unfold Flare.Binary64.Value.modelToReal at h
  cases hx : x.toModel.unpack <;> simp_all [Float.Model.UnpackedFloat.isFinite]

/-- Actual native multiplication is finite and obeys the proved model's one-ulp
bound whenever the exact product lies in the stated exponent range. -/
theorem mul_error (a b : Float) (N : Int)
    (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hv : |value a * value b| ≤ (2 : ℝ) ^ N)
    : (a * b).isFinite = true ∧ |value (a * b) - value a * value b| ≤ (2 : ℝ) ^ (N - 52) := by
  obtain ⟨q, hq, herr⟩ := Flare.Binary64.Model.Arithmetic.mul_error_real
    a.toModel b.toModel (value a) (value b) N
    (by rw [← interpretation_eq]; exact finite_value a ha)
    (by rw [← interpretation_eq]; exact finite_value b hb) hN hN' hv
  have he : Flare.Binary64.Value.modelToReal (a * b).toModel = some q := by
    rw [interpretation_eq]
    exact hq
  exact ⟨finite_of_value _ _ he, by simpa only [value, he, Option.getD_some] using herr⟩

/-- Native addition, including signed zero and subnormals, with an absolute
rounding bound established from Float.Model rather than assumed. -/
theorem add_error (a b : Float) (N : Int)
    (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hv : |value a + value b| ≤ (2 : ℝ) ^ N)
    : (a + b).isFinite = true ∧ |value (a + b) - (value a + value b)| ≤ (2 : ℝ) ^ (N - 52) := by
  obtain ⟨q, hq, herr⟩ := Flare.Binary64.Model.Arithmetic.add_error_real
    a.toModel b.toModel (value a) (value b) N
    (by rw [← interpretation_eq]; exact finite_value a ha)
    (by rw [← interpretation_eq]; exact finite_value b hb) hN hN' hv
  have he : Flare.Binary64.Value.modelToReal (a + b).toModel = some q := by
    rw [interpretation_eq]
    exact hq
  exact ⟨finite_of_value _ _ he, by simpa only [value, he, Option.getD_some] using herr⟩

/-- Native subtraction shares the model's finite one-ulp bound. -/
theorem sub_error (a b : Float) (N : Int)
    (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hv : |value a - value b| ≤ (2 : ℝ) ^ N)
    : (a - b).isFinite = true ∧ |value (a - b) - (value a - value b)| ≤ (2 : ℝ) ^ (N - 52) := by
  obtain ⟨q, hq, herr⟩ := Flare.Binary64.Model.Arithmetic.sub_error_real
    a.toModel b.toModel (value a) (value b) N
    (by rw [← interpretation_eq]; exact finite_value a ha)
    (by rw [← interpretation_eq]; exact finite_value b hb) hN hN' hv
  have he : Flare.Binary64.Value.modelToReal (a - b).toModel = some q := by
    rw [interpretation_eq]
    exact hq
  exact ⟨finite_of_value _ _ he, by simpa only [value, he, Option.getD_some] using herr⟩

/-- Native multiplication has a relative error bound plus a tiny absolute
underflow term. No positive lower bound on the exact result is required. -/
theorem mul_error_relative (a b : Float) (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hx : |value a * value b| ≤ (2 : ℝ) ^ (1000 : Int))
    : (a * b).isFinite = true
      ∧ |value (a * b) - value a * value b|
        ≤ (2 : ℝ) ^ (-51 : Int) * (|value a * value b| + (2 : ℝ) ^ (-1022 : Int)) := by
  obtain ⟨E, hE, hE', hv, hs⟩ := bounded_exponent (value a * value b) hx
  have h := mul_error a b E ha hb hE (by omega) hv
  exact ⟨h.1, h.2.trans (scaled_error_bound _ E 52 hs)⟩

/-- Native addition with magnitude-scaled rounding and an underflow allowance. -/
theorem add_error_relative (a b : Float) (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hx : |value a + value b| ≤ (2 : ℝ) ^ (1000 : Int))
    : (a + b).isFinite = true
      ∧ |value (a + b) - (value a + value b)|
        ≤ (2 : ℝ) ^ (-51 : Int) * (|value a + value b| + (2 : ℝ) ^ (-1022 : Int)) := by
  obtain ⟨E, hE, hE', hv, hs⟩ := bounded_exponent (value a + value b) hx
  have h := add_error a b E ha hb hE (by omega) hv
  exact ⟨h.1, h.2.trans (scaled_error_bound _ E 52 hs)⟩

/-- Native subtraction with magnitude-scaled rounding, including cancellation. -/
theorem sub_error_relative (a b : Float) (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hx : |value a - value b| ≤ (2 : ℝ) ^ (1000 : Int))
    : (a - b).isFinite = true
      ∧ |value (a - b) - (value a - value b)|
        ≤ (2 : ℝ) ^ (-51 : Int) * (|value a - value b| + (2 : ℝ) ^ (-1022 : Int)) := by
  obtain ⟨E, hE, hE', hv, hs⟩ := bounded_exponent (value a - value b) hx
  have h := sub_error a b E ha hb hE (by omega) hv
  exact ⟨h.1, h.2.trans (scaled_error_bound _ E 52 hs)⟩

end Flare.Binary64.Arithmetic
