module

public import Flare.Binary64.Arithmetic

/-! Exact rounding identities reused in sharper native error estimates. The
binary64 model's canonical mantissa and accuracy flag determine the rounded
value, including a carry; no floating-point accuracy premise is introduced. -/

@[expose] public section

namespace Flare.Binary64.Rounding
open Float.Model Float.Model.UnpackedFloat

/-- A canonical normal-range mantissa needs no initial right shift. Its
accuracy flag determines the rounded value exactly, including mantissa carry. -/
theorem round_canonical_value (s : Sign) (m : Nat) (e : Int) (a : Accuracy)
    (hm : m.log2 = 52) (he : -1074 ≤ e) (he' : e ≤ 970)
    : Flare.Binary64.Model.Value.toRational
        (Float.Model.pack (roundWithAccuracy Format.binary64 s m e a))
      = some ((s.apply (a.roundToNearestEven m : Int) : Rat) * (2 : Rat) ^ e) := by
  have ht : Format.binary64.targetExponent (totalExponent m e) = e := by
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent, hm]
    omega
  have hshift : shiftToTargetExponent Format.binary64 m e a =
      (ExtendedMantissa.ofMantissaAndAccuracy m a, e) := by
    simp only [shiftToTargetExponent, ht, shiftToExponent, sub_self, Int.toNat_zero,
      HShiftRight.hShiftRight, Nat.repeat, Nat.cast_zero, add_zero]
  have hround : (ExtendedMantissa.ofMantissaAndAccuracy m a).roundedMantissa = a.roundToNearestEven
    m := by
    cases a with
    | exact => rfl
    | inexact o => cases o <;> rfl
  have h := Flare.Binary64.Model.Rounding.round_rational_value s m e a (Or.inl hm.ge)
    (by rw [hshift]; exact he')
  simpa only [hshift, hround] using h

/-- Proof interpretation of the round/sticky bits. The represented rational
lies in the indicated subinterval above the stored integer mantissa. -/
def MantissaRep (em : ExtendedMantissa) (x : Rat) : Prop :=
  match em.roundBit, em.stickyBit with
  | false, false => x = em.mantissa
  | false, true => (em.mantissa : Rat) < x ∧ x < em.mantissa + 1 / 2
  | true, false => x = em.mantissa + 1 / 2
  | true, true => (em.mantissa : Rat) + 1 / 2 < x ∧ x < em.mantissa + 1

/-- The native right shift preserves the precise residual-bit interpretation.
This proves the meaning of the sticky-bit update rather than assuming it. -/
theorem shiftRightOne_rep (em : ExtendedMantissa) (x : Rat) (h : MantissaRep em x)
    : MantissaRep em.shiftRightOne (x / 2) := by
  rcases em with ⟨m, r, s⟩
  have he : (m : Rat) = 2 * ((m / 2 : Nat) : Rat) + (m % 2 : Nat) := by
    exact_mod_cast (Nat.div_add_mod m 2).symm
  have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hm with hm | hm
  all_goals
    rw [hm] at he
    cases r <;> cases s <;>
      norm_num [MantissaRep, ExtendedMantissa.shiftRightOne, hm,
        show ((1 : Nat) != 0) = true by decide] at h he ⊢
  all_goals first | linarith | (constructor <;> linarith)

/-- Round-to-nearest-even is within half an ulp of the value represented by
its mantissa and residual bits, including ties and a mantissa carry. -/
theorem roundedMantissa_nearest (em : ExtendedMantissa) (x : Rat) (h : MantissaRep em x)
    : |(em.roundedMantissa : Rat) - x| ≤ 1 / 2 := by
  rcases em with ⟨m, r, s⟩
  have hm : m % 2 ≤ 1 := by omega
  have hm0 : (0 : Rat) ≤ (m % 2 : Nat) := by positivity
  have hm1 : ((m % 2 : Nat) : Rat) ≤ 1 := by exact_mod_cast hm
  cases r <;> cases s <;>
    simp only [MantissaRep, ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
      Accuracy.roundToNearestEven, Nat.cast_add, Nat.cast_one] at h ⊢ <;>
    rw [abs_le] <;> constructor <;> first | linarith [h.1, h.2] | linarith

/-- Repeated native right shifts retain the represented exact mantissa value
at the shifted scale. -/
theorem shift_rep (em : ExtendedMantissa) (x : Rat) (k : Nat) (h : MantissaRep em x)
    : MantissaRep (em >>> k) (x / (2 : Rat) ^ k) := by
  induction k with
  | zero => simpa only [HShiftRight.hShiftRight, Nat.repeat, pow_zero, div_one] using h
  | succ k ih =>
      have hh := shiftRightOne_rep (em >>> k) (x / (2 : Rat)^k) ih
      change MantissaRep (em >>> (k + 1)) _ at hh
      simpa only [pow_succ, div_div] using hh

/-- The actual shift-and-round sequence on an exact integer mantissa has a
half-ulp error, including any number of discarded bits and gradual underflow. -/
theorem shift_rounded_nearest (m k : Nat)
    : |(((ExtendedMantissa.ofMantissaAndAccuracy m .exact >>> k).roundedMantissa : Nat) : Rat)
        - (m : Rat) / (2 : Rat) ^ k|
      ≤ 1 / 2 :=
  roundedMantissa_nearest _ _
    (shift_rep _ _ k
      (show MantissaRep (ExtendedMantissa.ofMantissaAndAccuracy m .exact) (m : Rat) from rfl))

/-- Packing the model's shifted mantissa preserves its half-ulp nearest-rounding
bound. The represented value may include a fractional tail, as in division. -/
theorem roundWithAccuracy_nearest (s : Sign) (m : Nat) (e : Int) (a : Accuracy) (x : Rat)
    (hc : 52 ≤ m.log2 ∨ e ≤ -1074)
    (he : (shiftToTargetExponent Format.binary64 m e a).2 ≤ 970)
    (hrep : MantissaRep (ExtendedMantissa.ofMantissaAndAccuracy m a) x)
    : ∃ q,
        Flare.Binary64.Model.Value.toRational
            (Float.Model.pack (roundWithAccuracy Format.binary64 s m e a))
          = some q
        ∧ |q - (s.apply 1 : Rat) * x * (2 : Rat) ^ e|
          ≤ (1 / 2 : Rat) * (2 : Rat) ^ ((shiftToTargetExponent Format.binary64 m e a).2) := by
  let k := (Format.binary64.targetExponent (totalExponent m e) - e).toNat
  let em := ExtendedMantissa.ofMantissaAndAccuracy m a >>> k
  have hshift : shiftToTargetExponent Format.binary64 m e a = (em, e + (k : Int)) := rfl
  have hq := Flare.Binary64.Model.Rounding.round_rational_value s m e a hc he
  rw [hshift] at hq ⊢
  have hnearest := roundedMantissa_nearest em (x / (2 : Rat)^k) (shift_rep _ x k hrep)
  have hscale : x / (2 : Rat)^k * (2 : Rat)^(e + (k : Int)) = x * (2 : Rat)^e := by
    rw [zpow_add₀ (by norm_num : (2 : Rat) ≠ 0), zpow_natCast]
    field_simp
  have herror : |(em.roundedMantissa : Rat) * (2 : Rat)^(e + (k : Int)) - x * (2 : Rat)^e| ≤
      (1 / 2 : Rat) * (2 : Rat)^(e + (k : Int)) := by
    rw [← hscale, ← sub_mul, abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : Rat) < 2) _)]
    exact mul_le_mul_of_nonneg_right hnearest (zpow_pos (by norm_num : (0 : Rat) < 2) _).le
  refine ⟨_, hq, ?_⟩
  cases s with
  | positive => simpa only [Sign.apply, Int.cast_natCast, Int.cast_one, one_mul] using herror
  | negative =>
      simp only [Sign.apply, Int.cast_neg, Int.cast_natCast, Int.cast_one, neg_one_mul]
      simp only [neg_mul, neg_sub_neg]
      rw [abs_sub_comm]
      exact herror

lemma mantissaRep_lower (em : ExtendedMantissa) (x : Rat) (h : MantissaRep em x)
    : (em.mantissa : Rat) ≤ x := by
  rcases em with ⟨m, r, s⟩
  cases r <;> cases s <;> simp only [MantissaRep] at h <;> dsimp only <;> linarith

private lemma first_exponent_target (m : Nat) (e : Int) (a : Accuracy)
    (hc : 52 ≤ m.log2 ∨ e ≤ -1074)
    : (shiftToTargetExponent Format.binary64 m e a).2 = max ((m.log2 : Int) + e - 52) (-1074) := by
  simp only [shiftToTargetExponent, shiftToExponent, Format.targetExponent, totalExponent,
    Format.mantissaBits, Format.minExponent]
  norm_num
  omega

private lemma nearest_scale_bound (m : Nat) (e : Int) (x : Rat)
    (hc : 52 ≤ m.log2 ∨ e ≤ -1074) (hx : (m : Rat) ≤ x)
    : (1 / 2 : Rat) * (2 : Rat) ^ (max ((m.log2 : Int) + e - 52) (-1074))
      ≤ (2 : Rat) ^ (-53 : Int) * (x * (2 : Rat) ^ e + (2 : Rat) ^ (-1022 : Int)) := by
  have hx0 : 0 ≤ x := (Nat.cast_nonneg m).trans hx
  have hη : (1 / 2 : Rat) * (2 : Rat)^(-1074 : Int) =
      (2 : Rat)^(-53 : Int) * (2 : Rat)^(-1022 : Int) := by
    rw [show (1 / 2 : Rat) = (2 : Rat)^(-1 : Int) by norm_num,
      ← zpow_add₀ (by norm_num : (2 : Rat) ≠ 0), ← zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
    congr 1
  by_cases ht : (m.log2 : Int) + e - 52 ≤ -1074
  · rw [max_eq_right ht, hη]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (mul_nonneg hx0 (zpow_pos (by norm_num :
      (0 : Rat) < 2) _).le)) (by positivity)
  · rw [max_eq_left (le_of_not_ge ht)]
    have hm : m ≠ 0 := by
      intro hm
      subst m
      simp only [Nat.log2_zero, Nat.cast_zero] at hc ht
      omega
    have hlog : (2 : Rat)^m.log2 ≤ x := (show (2 : Rat)^m.log2 ≤ (m : Rat) by
      exact_mod_cast Nat.log2_self_le hm).trans hx
    have hp : (1 / 2 : Rat) * (2 : Rat)^((m.log2 : Int) + e - 52) =
        (2 : Rat)^(-53 : Int) * ((2 : Rat)^m.log2 * (2 : Rat)^e) := by
      rw [show (1 / 2 : Rat) = (2 : Rat)^(-1 : Int) by norm_num,
        ← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : Rat) ≠ 0),
        ← zpow_add₀ (by norm_num : (2 : Rat) ≠ 0), ← zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
      congr 1
      omega
    rw [hp]
    exact mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_right hlog (zpow_pos (by norm_num : (0 : Rat) < 2) _).le).trans
        (le_add_of_nonneg_right (zpow_pos (by norm_num : (0 : Rat) < 2) _).le))
      (by positivity)

/-- The actual packed rounding operation has the binary64 unit-roundoff bound
`u (|x·2^e| + 2^-1022)`, where `u = 2^-53`. Residual-bit consistency supplies
the fractional input tail, and the magnitude bound proves finite packing. -/
theorem roundWithAccuracy_relative_nearest (s : Sign) (m : Nat) (e : Int) (a : Accuracy) (x : Rat)
    (hc : 52 ≤ m.log2 ∨ e ≤ -1074)
    (hrep : MantissaRep (ExtendedMantissa.ofMantissaAndAccuracy m a) x)
    (hbound : x * (2 : Rat) ^ e ≤ (2 : Rat) ^ (1000 : Int))
    : ∃ q,
        Flare.Binary64.Model.Value.toRational
            (Float.Model.pack (roundWithAccuracy Format.binary64 s m e a))
          = some q
        ∧ |q - (s.apply 1 : Rat) * x * (2 : Rat) ^ e|
          ≤ (2 : Rat) ^ (-53 : Int) * (x * (2 : Rat) ^ e + (2 : Rat) ^ (-1022 : Int)) := by
  have hx : (m : Rat) ≤ x := by
    have hh := mantissaRep_lower _ x hrep
    cases a with
    | exact => exact hh
    | inexact o => cases o <;> exact hh
  have he : (shiftToTargetExponent Format.binary64 m e a).2 ≤ 970 := by
    rw [first_exponent_target m e a hc]
    apply max_le _ (by norm_num)
    by_cases hm : m = 0
    · subst m
      simp only [Nat.log2_zero] at hc
      simp only [Nat.log2_zero, Nat.cast_zero]
      omega
    · have hlog : (2 : Rat)^((m.log2 : Int) + e) ≤ (2 : Rat)^(1000 : Int) := by
        rw [zpow_add₀ (by norm_num : (2 : Rat) ≠ 0), zpow_natCast]
        apply le_trans _ hbound
        exact mul_le_mul_of_nonneg_right
          ((show (2 : Rat)^m.log2 ≤ (m : Rat) by exact_mod_cast Nat.log2_self_le hm).trans hx)
          (zpow_pos (by norm_num : (0 : Rat) < 2) _).le
      have hexp := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : Rat) < 2)).mp hlog
      omega
  obtain ⟨q, hq, herr⟩ := roundWithAccuracy_nearest s m e a x hc he hrep
  refine ⟨q, hq, herr.trans ?_⟩
  rw [first_exponent_target m e a hc]
  exact nearest_scale_bound m e x hc hx

/-- The model's exponent-decreasing wrapper preserves the nearest-rounding
bound for an exact positive integer mantissa. -/
theorem round_relative_nearest (s : Sign) (m : Nat) (e : Int) (hm : 0 < m)
    (hbound : (m : Rat) * (2 : Rat) ^ e ≤ (2 : Rat) ^ (1000 : Int))
    : ∃ q,
        Flare.Binary64.Model.Value.toRational (Float.Model.pack (round Format.binary64 s m e))
          = some q
        ∧ |q - (s.apply 1 : Rat) * (m : Rat) * (2 : Rat) ^ e|
          ≤ (2 : Rat) ^ (-53 : Int) * ((m : Rat) * (2 : Rat) ^ e + (2 : Rat) ^ (-1022 : Int)) := by
  let t := Format.binary64.targetExponent (totalExponent m e)
  let k := (e - t).toNat
  have ht : t = max ((m.log2 : Int) + e - 52) (-1074) := by
    dsimp [t, Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
    omega
  have hlog : (m <<< k).log2 = m.log2 + k :=
    Flare.Binary64.Model.Conversion.log2_shift m k hm
  have hc : 52 ≤ (m <<< k).log2 ∨ e - (k : Int) ≤ -1074 := by
    rw [hlog]
    dsimp [k]
    omega
  have hvalue := Flare.Binary64.Model.Rounding.decrease_preserves_value m k e
  obtain ⟨q, hq, herr⟩ := roundWithAccuracy_relative_nearest s (m <<< k) (e - (k : Int)) .exact
    ((m <<< k : Nat) : Rat) hc rfl (by rw [hvalue]; exact hbound)
  refine ⟨q, ?_, ?_⟩
  · simpa only [UnpackedFloat.round, decreaseExponent] using hq
  · simpa only [mul_assoc, hvalue] using herr

/-- Exact signed normalization, including either signed-zero branch, has the
binary64 unit-roundoff bound without presuming correctly rounded arithmetic. -/
theorem normalize_relative_nearest (m : Int) (e : Int) (zs : Sign)
    (hbound : |(m : Rat) * (2 : Rat) ^ e| ≤ (2 : Rat) ^ (1000 : Int))
    : ∃ q,
        Flare.Binary64.Model.Value.toRational
            (Float.Model.pack (UnpackedFloat.normalize Format.binary64 m e zs))
          = some q
        ∧ |q - (m : Rat) * (2 : Rat) ^ e|
          ≤ (2 : Rat) ^ (-53 : Int)
            * (|(m : Rat) * (2 : Rat) ^ e| + (2 : Rat) ^ (-1022 : Int)) := by
  by_cases hz : m = 0
  · subst m
    refine ⟨0, ?_, ?_⟩
    · simp only [UnpackedFloat.normalize, show compare (0 : Int) 0 = Ordering.eq by decide]
      cases zs <;> rfl
    · simp only [Int.cast_zero, zero_mul, sub_self, abs_zero, zero_add]
      exact mul_nonneg (by norm_num) (by norm_num)
  have hp : 0 < (2 : Rat)^e := zpow_pos (by norm_num : (0 : Rat) < 2) _
  by_cases hn : m < 0
  · have hm : ((-m).toNat : Int) = -m := by omega
    have hcast : ((-m).toNat : Rat) = -(m : Rat) := by exact_mod_cast hm
    have hmag : ((-m).toNat : Rat) * (2 : Rat)^e = |(m : Rat) * (2 : Rat)^e| := by
      rw [hcast, abs_mul, abs_of_nonpos (by exact_mod_cast hn.le : (m : Rat) ≤ 0), abs_of_pos hp]
    obtain ⟨q, hq, herr⟩ := round_relative_nearest .negative (-m).toNat e (by omega)
      (by rw [hmag]; exact hbound)
    refine ⟨q, ?_, ?_⟩
    · unfold UnpackedFloat.normalize
      rw [Int.compare_eq_lt.mpr hn]
      exact hq
    · rw [hmag] at herr
      simpa only [Sign.apply, Int.cast_neg, Int.cast_one, neg_one_mul, hcast, neg_neg] using herr
  · have hm : (m.toNat : Int) = m := by omega
    have hcast : (m.toNat : Rat) = (m : Rat) := by exact_mod_cast hm
    have hmag : (m.toNat : Rat) * (2 : Rat)^e = |(m : Rat) * (2 : Rat)^e| := by
      rw [hcast, abs_mul, abs_of_nonneg (by exact_mod_cast (by omega : 0 ≤ m) : (0 : Rat) ≤ m),
        abs_of_pos hp]
    obtain ⟨q, hq, herr⟩ := round_relative_nearest .positive m.toNat e (by omega)
      (by rw [hmag]; exact hbound)
    refine ⟨q, ?_, ?_⟩
    · unfold UnpackedFloat.normalize
      rw [Int.compare_eq_gt.mpr (by omega)]
      exact hq
    · rw [hmag] at herr
      simpa only [Sign.apply, Int.cast_one, one_mul, hcast] using herr

end Flare.Binary64.Rounding
