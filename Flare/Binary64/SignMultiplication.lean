import Flare.Binary64.Order
import Flare.Binary64.Model.Rounding

/-! Exact real interpretation of native multiplication by ±1 over the entire
finite binary64 domain, including signed zeros, gradual underflow, and largest
finite values. These are statements about Lean's logical native model. -/

namespace Flare.Binary64.SignMultiplication

open Float.Model Float.Model.UnpackedFloat
open Flare.Binary64.Value Flare.Binary64.Arithmetic
open Flare.Binary64.Model.Rounding

private theorem repeat_shift {α : Type} (f : α → α) (k : Nat) (a : α)
    : Nat.repeat f (k + 1) a = Nat.repeat f k (f a) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => change f (Nat.repeat f (k+1) a) = f (Nat.repeat f k (f a)); rw [ih]

private theorem exact_shift (m k : Nat)
    : (ExtendedMantissa.ofMantissaAndAccuracy (m * 2 ^ k) .exact >>> k)
      = ExtendedMantissa.ofMantissaAndAccuracy m .exact := by
  induction k with
  | zero => simp [HShiftRight.hShiftRight, Nat.repeat, ExtendedMantissa.ofMantissaAndAccuracy]
  | succ k ih =>
      rw [pow_succ, ← mul_assoc]
      change (Nat.repeat ExtendedMantissa.shiftRightOne (k+1) ⟨m * 2^k * 2, false, false⟩) = _
      rw [repeat_shift]
      have hs
          : ExtendedMantissa.shiftRightOne ⟨m * 2 ^ k * 2, false, false⟩
            = ⟨m * 2 ^ k,false,false⟩ := by
        simp [ExtendedMantissa.shiftRightOne]
      rw [hs]
      exact ih

private theorem canonical_shift (m : Nat) (e : Int) (hm : m < 2 ^ 53) (he : -1074 ≤ e)
    : shiftToTargetExponent Format.binary64 m e .exact
      = (ExtendedMantissa.ofMantissaAndAccuracy m .exact,e) := by
  have hl : m.log2 ≤ 52 := by
    by_cases hz : m = 0
    · subst m; decide
    · have := (Nat.log2_lt hz).mpr hm
      omega
  have ht : Format.binary64.targetExponent (totalExponent m e) ≤ e := by
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
    omega
  have hs : (Format.binary64.targetExponent (totalExponent m e)-e).toNat = 0 := by omega
  simp [shiftToTargetExponent, shiftToExponent, hs, HShiftRight.hShiftRight, Nat.repeat]

private theorem scaled_log (m k : Nat) (hm : 0 < m) : (m * 2 ^ k).log2 = m.log2 + k := by
  apply (Nat.log2_eq_iff (by positivity : m * 2 ^ k ≠ 0)).mpr
  constructor
  · rw [pow_add]
    exact Nat.mul_le_mul_right _ (Nat.log2_self_le hm.ne')
  · rw [show m.log2+k+1=(m.log2+1)+k by omega, pow_add]
    exact Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (by positivity)

private theorem round_unit_product (s : Sign) (m : Nat) (e : Int) (hp : 0 < m)
    (hm : m < 2 ^ 53) (he : -1074 ≤ e) (hc : m.log2 = 52 ∨ e = -1074)
    : roundWithAccuracy Format.binary64 s (m * 2 ^ 52) (e - 52) .exact = .finite s m e hp := by
  have ht : Format.binary64.targetExponent (totalExponent (m*2^52) (e-52)) = e := by
    rw [totalExponent, scaled_log m 52 hp]
    simp only [Format.targetExponent, Format.mantissaBits, Format.minExponent]
    have hl : m.log2 ≤ 52 := by
      have := (Nat.log2_lt hp.ne').mpr hm
      omega
    rcases hc with hc | hc <;> omega
  have hs
      : shiftToTargetExponent Format.binary64 (m*2^52) (e-52) .exact
        = (ExtendedMantissa.ofMantissaAndAccuracy m .exact,e) := by
    simp only [shiftToTargetExponent, ht, shiftToExponent,
      show (e-(e-52)).toNat = 52 by omega]
    rw [exact_shift]
    congr 1
    omega
  unfold roundWithAccuracy
  rw [hs]
  dsimp only [ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.roundedMantissa,
    ExtendedMantissa.accuracy, Accuracy.roundToNearestEven]
  rw [canonical_shift m e hm he]
  split
  · rename_i h
    change m = 0 at h
    omega
  · rfl

private theorem pack_finite_value (x : Float.Model) (s s' : Sign) (m : Nat) (e : Int)
    (hm : 0 < m) (hu : x.unpack = .finite s m e hm)
    : Flare.Binary64.Value.modelToReal (Float.Model.pack (.finite s' m e hm))
      = some ((s'.apply (m : Int) : ℝ) * (2 : ℝ) ^ e) := by
  obtain ⟨hmb, he, he', hc⟩ := unpack_finite_shape x s m e hm hu
  unfold Flare.Binary64.Value.modelToReal
  rcases hc with hlog | heq
  · rw [Flare.Binary64.Model.Conversion.unpack_pack_normal s' m e hm hlog he he']
  · subst e
    by_cases hsmall : m < 2^52
    · rw [unpack_pack_subnormal s' m hm hsmall]
    · rw [Flare.Binary64.Model.Conversion.unpack_pack_normal s' m (-1074) hm
        ((Nat.log2_eq_iff (Nat.ne_of_gt hm)).mpr ⟨by omega, hmb⟩) (by omega) (by omega)]

private theorem mul_unit (a x : Float) (s : Sign)
    (ha : a.toModel.unpack = .finite s (2 ^ 52) (-52) (by decide)) (hx : x.isFinite = true)
    : (a * x).isFinite = true ∧ value (a * x) = (s.apply 1 : ℝ) * value x := by
  change x.toModel.unpack.isFinite = true at hx
  cases hu : x.toModel.unpack with
  | notANumber => simp [hu, UnpackedFloat.isFinite] at hx
  | infinity t => simp [hu, UnpackedFloat.isFinite] at hx
  | zero t =>
      have hv : value x = 0 := by simp [value, Flare.Binary64.Value.modelToReal, hu]
      have hq : Flare.Binary64.Value.modelToReal (a*x).toModel = some 0 := by
        change Flare.Binary64.Value.modelToReal
          (pack (UnpackedFloat.mul Format.binary64 a.toModel.unpack x.toModel.unpack)) = _
        rw [ha, hu]
        simp only [UnpackedFloat.mul]
        cases s*t <;> rfl
      exact ⟨finite_of_value _ _ hq, by rw [hv]; simp [value, hq]⟩
  | finite t m e hp =>
      obtain ⟨hm, he, _, hc⟩ := unpack_finite_shape x.toModel t m e hp hu
      have hq : Flare.Binary64.Value.modelToReal (a*x).toModel
          = some (((s*t).apply (m : Int) : ℝ) * (2 : ℝ)^e) := by
        change Flare.Binary64.Value.modelToReal
          (pack (UnpackedFloat.mul Format.binary64 a.toModel.unpack x.toModel.unpack)) = _
        rw [ha, hu]
        simp only [UnpackedFloat.mul]
        rw [mul_comm (2^52) m, show (-52 : Int)+e=e-52 by omega,
          round_unit_product (s*t) m e hp hm he hc]
        exact pack_finite_value x.toModel t (s*t) m e hp hu
      refine ⟨finite_of_value _ _ hq, ?_⟩
      have hv : value x = (t.apply (m : Int) : ℝ) * (2 : ℝ)^e := by
        simp [value, Flare.Binary64.Value.modelToReal, hu]
      rw [hv]
      cases s <;> cases t <;> simp [value, hq, Sign.apply]

/-- Multiplication by +1 is exact for every finite native binary64 value,
including signed zero, subnormal values and the largest finite values. -/
theorem one_mul_value (x : Float) (hx : x.isFinite = true)
    : ((1.0 : Float) * x).isFinite = true ∧ value ((1.0 : Float) * x) = value x := by
  simpa only [Sign.apply, Int.cast_one, one_mul] using mul_unit 1.0 x .positive (by rfl) hx

/-- Multiplication by -1 is exact over the same full finite domain. -/
theorem neg_one_mul_value (x : Float) (hx : x.isFinite = true)
    : ((-1.0 : Float) * x).isFinite = true ∧ value ((-1.0 : Float) * x) = -value x := by
  simpa only [Sign.apply, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
    using mul_unit (-1.0) x .negative (by rfl) hx

end Flare.Binary64.SignMultiplication
