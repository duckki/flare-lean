module

public import Mathlib.Tactic.Ring
public import Flare.FloatFormat.Packing
public import Mathlib.Tactic.Linarith

/-!
# Shared binary32 and binary64 rounding bounds

These proofs interpret the pinned model's mantissa shifting, carry, packing, and
normalization code as exact rational arithmetic. The bound is deliberately a full
ulp, so it does not require assuming a nearest-rounding theorem. The magnitude
hypotheses keep the packed result finite; subnormal outputs and signed zeros are
covered. No native-decide axiom or hypothetical rounding law is used.
-/

open Float.Model Float.Model.UnpackedFloat
@[expose] public section

namespace Flare.FloatFormat.Rounding

open Flare.FloatFormat.Format

open Flare.FloatFormat.Packing

private theorem shift_mantissa (em : ExtendedMantissa) (k : Nat)
    : (em >>> k).mantissa = em.mantissa / 2 ^ k := by
  induction k generalizing em with
  | zero => simp [HShiftRight.hShiftRight, Nat.repeat]
  | succ k ih =>
      change (Nat.repeat ExtendedMantissa.shiftRightOne (k + 1) em).mantissa = _
      change ((em >>> k).mantissa / 2) = _
      rw [ih]
      simp [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

private theorem rounded_mantissa_bounds (em : ExtendedMantissa)
    : em.mantissa ≤ em.roundedMantissa ∧ em.roundedMantissa ≤ em.mantissa + 1 := by
  rcases em with ⟨m, r, s⟩
  cases r <;> cases s <;>
    simp [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
      Accuracy.roundToNearestEven]
  omega

private theorem shift_floor_bound (w : Width) (m : Nat) (s : Nat) (hs : m.log2 ≤ w.fraction + s)
    : m / 2 ^ s < 2 ^ (w.fraction + 1) := by
  apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ s)).mpr
  have h := Nat.lt_log2_self (n := m)
  have hp : 2^(m.log2 + 1) ≤ 2^((w.fraction + 1)+s) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [← Nat.pow_add]
  exact lt_of_lt_of_le h hp

private theorem shift_floor_normal (w : Width) (m s : Nat) (hm : m ≠ 0)
    (hs : m.log2 = w.fraction + s)
    : 2 ^ w.fraction ≤ m / 2 ^ s := by
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ s)).mpr
  rw [← Nat.pow_add, ← hs]
  exact Nat.log2_self_le hm

private theorem target_shift_bounds (w : Width) (m : Nat) (e : Int)
    : let t := w.spec.targetExponent (totalExponent m e)
      let k := (t - e).toNat
      (w.minimum : Int) ≤ e + k ∧ m.log2 ≤ w.fraction + k := by
  simp only [Float.Model.Format.targetExponent, totalExponent,
    Float.Model.Format.mantissaBits, Width.spec_fraction, Width.spec_minimum]
  norm_num
  omega

private theorem shift_small_identity (w : Width) (m : Nat) (e : Int) (hm : m < 2 ^ (w.fraction + 1))
    (he : w.minimum ≤ e)
    : shiftToTargetExponent w.spec m e .exact = (ExtendedMantissa.mk m false false, e) := by
  have hk : m.log2 ≤ w.fraction := by
    by_cases h : m = 0
    · simp [h]
    · have := (Nat.log2_lt h).mpr hm; omega
  have ht : w.spec.targetExponent (totalExponent m e) ≤ e := by
    simp only [Float.Model.Format.targetExponent, totalExponent,
      Float.Model.Format.mantissaBits, Width.spec_fraction, Width.spec_minimum]
    omega
  have hs : (w.spec.targetExponent (totalExponent m e) - e).toNat = 0 := by omega
  simp [shiftToTargetExponent, shiftToExponent, hs, HShiftRight.hShiftRight,
    Nat.repeat, ExtendedMantissa.ofMantissaAndAccuracy]

private theorem shift_overflow_identity (w : Width) (e : Int) (he : w.minimum ≤ e)
    : shiftToTargetExponent w.spec (2 ^ (w.fraction + 1)) e .exact
      = (ExtendedMantissa.mk (2 ^ w.fraction) false false, e + 1) := by
  have ht : w.spec.targetExponent (totalExponent (2^(w.fraction + 1)) e) = e + 1 := by
    simp only [Float.Model.Format.targetExponent, totalExponent, Nat.log2_two_pow,
      Float.Model.Format.mantissaBits, Width.spec_fraction, Width.spec_minimum]
    norm_num
    omega
  unfold shiftToTargetExponent
  rw [ht]
  simp [shiftToExponent,
    HShiftRight.hShiftRight, Nat.repeat, ExtendedMantissa.ofMantissaAndAccuracy,
    ExtendedMantissa.shiftRightOne, pow_succ]

private theorem round_eq_firstRounded (w : Width) (s : Sign) (m : Nat) (e : Int) (a : Accuracy)
    : let first := shiftToTargetExponent w.spec m e a
      let r := first.1.roundedMantissa
      roundWithAccuracy w.spec s m e a
      = if h : r = 0 then
          .zero s
        else if r < 2 ^ (w.fraction + 1) then
          .finite s r first.2 (Nat.pos_of_ne_zero h)
        else
          .finite s (2 ^ w.fraction) (first.2 + 1) (by positivity) := by
  dsimp only
  have hshift := target_shift_bounds w m e
  dsimp only at hshift
  have hf : (shiftToTargetExponent w.spec m e a).1.mantissa =
      m / 2^((w.spec.targetExponent (totalExponent m e) - e).toNat) := by
    simp [shiftToTargetExponent, shiftToExponent, shift_mantissa,
      ExtendedMantissa.ofMantissaAndAccuracy]
    cases a with
    | exact => rfl
    | inexact o => cases o <;> rfl
  have hb := rounded_mantissa_bounds (shiftToTargetExponent w.spec m e a).1
  have he : w.minimum ≤ (shiftToTargetExponent w.spec m e a).2 := hshift.1
  have hr : (shiftToTargetExponent w.spec m e a).1.roundedMantissa ≤ 2^(w.fraction + 1) := by
    rw [hf] at hb
    have := shift_floor_bound w m _ hshift.2
    omega
  generalize hfirst : shiftToTargetExponent w.spec m e a = first at *
  rcases first with ⟨em, e₁⟩
  rw [roundWithAccuracy, hfirst]
  dsimp only at *
  by_cases hz : em.roundedMantissa = 0
  · rw [hz, shift_small_identity w 0 e₁ (by positivity) he]
    rfl
  by_cases hsmall : em.roundedMantissa < 2^(w.fraction + 1)
  · rw [shift_small_identity w _ _ hsmall he]
    simp only [hz, hsmall, ↓reduceDIte, ↓reduceIte]
  · have hmax : em.roundedMantissa = 2^(w.fraction + 1) := by omega
    rw [hmax, shift_overflow_identity w _ he]
    dsimp only
    simp

private theorem first_floor (w : Width) (m : Nat) (e : Int) (a : Accuracy)
    : (shiftToTargetExponent w.spec m e a).1.mantissa
      = m / 2 ^ ((w.spec.targetExponent (totalExponent m e) - e).toNat) := by
  simp [shiftToTargetExponent, shiftToExponent, shift_mantissa,
    ExtendedMantissa.ofMantissaAndAccuracy]
  cases a with
  | exact => rfl
  | inexact o => cases o <;> rfl

private theorem first_canonical (w : Width) (m : Nat) (e : Int) (a : Accuracy)
    (hc : w.fraction ≤ m.log2 ∨ e ≤ w.minimum)
    : 2 ^ w.fraction ≤ (shiftToTargetExponent w.spec m e a).1.roundedMantissa
      ∨ (shiftToTargetExponent w.spec m e a).2 = w.minimum := by
  let t := w.spec.targetExponent (totalExponent m e)
  let k := (t - e).toNat
  have ht : t = max ((m.log2 : Int) + e - w.fraction) (w.minimum) := by
    change max ((m.log2 : Int) + 1 + e - (1 + w.fraction)) w.minimum = _
    omega
  have het : e ≤ t := by omega
  have he' : e + (k : Int) = t := by dsimp [k]; omega
  by_cases hmin : t = w.minimum
  · right
    change e + (k : Int) = w.minimum
    omega
  · left
    have hlog : w.fraction ≤ m.log2 := by omega
    have hm : m ≠ 0 := by
      intro h
      have hp := w.fraction_pos
      simp [h] at hlog
      omega
    have hk : m.log2 = w.fraction + k := by dsimp [k]; omega
    have hl := shift_floor_normal w m k hm hk
    have hr := rounded_mantissa_bounds (shiftToTargetExponent w.spec m e a).1
    rw [first_floor w] at hr
    exact le_trans hl hr.1

/-- Exact packed value after the first rounded mantissa, including a carry
into the next binade. The exponent bound excludes overflow. -/
theorem round_rational_value (w : Width) (s : Sign) (m : Nat) (e : Int) (a : Accuracy)
    (hc : w.fraction ≤ m.log2 ∨ e ≤ w.minimum)
    (he : (shiftToTargetExponent w.spec m e a).2 ≤ (w.maximum - 1))
    : packedValue w (roundWithAccuracy w.spec s m e a)
      = some
          (((s.apply ((shiftToTargetExponent w.spec m e a).1.roundedMantissa : Int)) : Rat)
            * (2 : Rat) ^ ((shiftToTargetExponent w.spec m e a).2)) := by
  have hl : w.minimum ≤ (shiftToTargetExponent w.spec m e a).2 := (target_shift_bounds w m e).1
  have hc' := first_canonical w m e a hc
  rw [round_eq_firstRounded w]
  by_cases hz : (shiftToTargetExponent w.spec m e a).1.roundedMantissa = 0
  · simp only [hz, ↓reduceDIte]
    cases s <;> simp [Sign.apply]
  by_cases hn : (shiftToTargetExponent w.spec m e a).1.roundedMantissa < 2^(w.fraction + 1)
  · simp only [hz, hn, ↓reduceDIte, ↓reduceIte]
    unfold packedValue toRational
    rcases hc' with hc' | hc'
    · rw [unpack_pack_normal w _ _ _ _ ((Nat.log2_eq_iff hz).mpr ⟨hc', hn⟩) hl (by omega)]
      rfl
    · by_cases hb : 2^w.fraction ≤ (shiftToTargetExponent w.spec m e a).1.roundedMantissa
      · rw [unpack_pack_normal w _ _ _ _ ((Nat.log2_eq_iff hz).mpr ⟨hb, hn⟩) hl (by omega)]
        rfl
      · simp only [hc']
        rw [unpack_pack_subnormal w _ _ _ (by omega)]
        rfl
  · have hr : (shiftToTargetExponent w.spec m e a).1.roundedMantissa = 2^(w.fraction + 1) := by
      have h := rounded_mantissa_bounds (shiftToTargetExponent w.spec m e a).1
      rw [first_floor w] at h
      have h' := shift_floor_bound w m _ (target_shift_bounds w m e).2
      omega
    simp only [hz, hn, ↓reduceDIte, ↓reduceIte]
    unfold packedValue toRational
    rw [unpack_pack_normal w _ _ _ _ Nat.log2_two_pow (by omega) (by omega)]
    simp only [unpackedToRational, hr]
    cases s <;> simp only [Sign.apply, Int.cast_neg, Int.cast_natCast]
    all_goals rw [zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
    all_goals norm_num; ring

private theorem floor_round_error (m r k : Nat) (hr : m / 2 ^ k ≤ r ∧ r ≤ m / 2 ^ k + 1)
    : |(r : Rat) * (2 : Rat) ^ k - (m : Rat)| ≤ (2 : Rat) ^ k := by
  have hd : 0 < 2^k := Nat.two_pow_pos k
  have hlo := Nat.div_mul_le_self m (2^k)
  have hhi : m < (m / 2^k + 1) * 2^k := by
    have hmod := Nat.mod_lt m hd
    have heq := Nat.mod_add_div m (2^k)
    nlinarith
  have h₁ : r * 2^k ≤ m + 2^k := by nlinarith [hr.2]
  have h₂ : m ≤ r * 2^k + 2^k := by nlinarith [hr.1]
  have h₁' : (r : Rat) * 2^k ≤ (m : Rat) + 2^k := by exact_mod_cast h₁
  have h₂' : (m : Rat) ≤ (r : Rat) * 2^k + 2^k := by exact_mod_cast h₂
  rw [abs_le]
  constructor <;> linarith

private theorem dyadic_round_error (m r k : Nat) (e : Int) (hr : m / 2 ^ k ≤ r ∧ r ≤ m / 2 ^ k + 1)
    : |(r : Rat) * (2 : Rat) ^ (e + (k : Int)) - (m : Rat) * (2 : Rat) ^ e|
      ≤ (2 : Rat) ^ (e + (k : Int)) := by
  have h := floor_round_error m r k hr
  have hp : 0 ≤ (2 : Rat)^e := le_of_lt (zpow_pos (by norm_num : (0 : Rat) < 2) e)
  have hmul := mul_le_mul_of_nonneg_right h hp
  rw [zpow_add₀ (by norm_num : (2 : Rat) ≠ 0), zpow_natCast]
  have he : (r : Rat) * ((2 : Rat)^e * (2 : Rat)^k) - (m : Rat) * (2 : Rat)^e =
      ((r : Rat) * (2 : Rat)^k - (m : Rat)) * (2 : Rat)^e := by ring
  rw [he, abs_mul, abs_of_nonneg hp]
  simpa only [mul_comm] using hmul

private theorem round_error (w : Width) (s : Sign) (m : Nat) (e : Int) (a : Accuracy)
    (hc : w.fraction ≤ m.log2 ∨ e ≤ w.minimum)
    (he : (shiftToTargetExponent w.spec m e a).2 ≤ (w.maximum - 1))
    : ∃ q,
        packedValue w (roundWithAccuracy w.spec s m e a) = some q
        ∧ |q - (s.apply (m : Int) : Rat) * (2 : Rat) ^ e|
          ≤ (2 : Rat) ^ ((shiftToTargetExponent w.spec m e a).2) := by
  rw [round_rational_value w s m e a hc he]
  refine ⟨_, rfl, ?_⟩
  have hr := rounded_mantissa_bounds (shiftToTargetExponent w.spec m e a).1
  rw [first_floor w] at hr
  have h := dyadic_round_error m _ _ e hr
  have hs : (shiftToTargetExponent w.spec m e a).2 =
      e + (w.spec.targetExponent (totalExponent m e) - e).toNat := rfl
  rw [hs]
  cases s <;> simpa only [Sign.apply, Int.cast_neg, Int.cast_natCast,
    neg_mul, neg_sub_neg, abs_sub_comm] using h

private theorem target_le_of_value_le (w : Width) (m : Nat) (e N : Int) (hm : 0 < m)
    (hN : (w.minimum + w.fraction) ≤ N) (hv : (m : Rat) * (2 : Rat) ^ e ≤ (2 : Rat) ^ N)
    : w.spec.targetExponent (totalExponent m e) ≤ N - w.fraction := by
  have hl : (2 : Rat)^m.log2 ≤ (m : Rat) := by
    exact_mod_cast Nat.log2_self_le (Nat.ne_of_gt hm)
  have hp : 0 ≤ (2 : Rat)^e := le_of_lt (zpow_pos (by norm_num : (0 : Rat) < 2) e)
  have h := le_trans (mul_le_mul_of_nonneg_right hl hp) hv
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)] at h
  have hexp := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : Rat) < 2)).mp h
  simp only [Float.Model.Format.targetExponent, totalExponent,
    Float.Model.Format.mantissaBits, Width.spec_fraction, Width.spec_minimum]
  norm_num
  omega

private theorem first_exponent_eq_target (w : Width) (m : Nat) (e : Int) (a : Accuracy)
    (hc : w.fraction ≤ m.log2 ∨ e ≤ w.minimum)
    : (shiftToTargetExponent w.spec m e a).2 = w.spec.targetExponent (totalExponent m e) := by
  change e + (w.spec.targetExponent (totalExponent m e) - e).toNat = _
  simp only [Float.Model.Format.targetExponent, totalExponent,
    Float.Model.Format.mantissaBits, Width.spec_fraction, Width.spec_minimum]
  norm_num
  omega

theorem decrease_preserves_value (m k : Nat) (e : Int)
    : ((m <<< k : Nat) : Rat) * (2 : Rat) ^ (e - (k : Int)) = (m : Rat) * (2 : Rat) ^ e := by
  rw [Nat.shiftLeft_eq]
  push_cast
  rw [← zpow_natCast, mul_assoc, ← zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
  have he : (k : Int) + (e - (k : Int)) = e := by omega
  rw [he]

theorem round_direct_error (w : Width) (s : Sign) (m : Nat) (e N : Int)
    (hm : 0 < m) (hN : (w.minimum + w.fraction) ≤ N) (hN' : N ≤ (w.maximum + w.fraction - 1))
    (hv : (m : Rat) * (2 : Rat) ^ e ≤ (2 : Rat) ^ N)
    : ∃ q,
        packedValue w (round w.spec s m e) = some q
        ∧ |q - (s.apply (m : Int) : Rat) * (2 : Rat) ^ e| ≤ (2 : Rat) ^ (N - w.fraction) := by
  let t := w.spec.targetExponent (totalExponent m e)
  let k := (e - t).toNat
  have ht : t = max ((m.log2 : Int) + e - w.fraction) (w.minimum) := by
    change max ((m.log2 : Int) + 1 + e - (1 + w.fraction)) w.minimum = _
    omega
  have hlog : (m <<< k).log2 = m.log2 + k := log2_shift m k hm
  have hc : w.fraction ≤ (m <<< k).log2 ∨ e - (k : Int) ≤ w.minimum := by
    rw [hlog]
    dsimp [k]
    omega
  have htotal : totalExponent (m <<< k) (e - (k : Int)) = totalExponent m e := by
    simp only [totalExponent, hlog, Nat.cast_add]
    omega
  have hb := target_le_of_value_le w m e N hm hN hv
  have hexp : (shiftToTargetExponent w.spec (m <<< k) (e - (k : Int)) .exact).2 = t := by
    rw [first_exponent_eq_target w _ _ _ hc, htotal]
  obtain ⟨q, hq, herror⟩ := round_error w s (m <<< k) (e - (k : Int)) .exact hc
    (by rw [hexp]; dsimp [t]; omega)
  refine ⟨q, ?_, ?_⟩
  · simpa only [round, decreaseExponent] using hq
  · have hvalue := decrease_preserves_value m k e
    have hs : (s.apply ((m <<< k : Nat) : Int) : Rat) * (2 : Rat)^(e - (k : Int)) =
        (s.apply (m : Int) : Rat) * (2 : Rat)^e := by
      cases s with
      | positive => simpa only [Sign.apply, Int.cast_natCast] using hvalue
      | negative =>
          simpa only [Sign.apply, Int.cast_neg, Int.cast_natCast, neg_mul] using congrArg Neg.neg
            hvalue
    rw [hs, hexp] at herror
    exact le_trans herror (zpow_le_zpow_right₀ (by norm_num : (1 : Rat) ≤ 2) hb)

theorem round_with_accuracy_error (w : Width) (s : Sign) (m : Nat) (e N : Int) (a : Accuracy)
    (hm : 0 < m) (hc : w.fraction ≤ m.log2 ∨ e ≤ w.minimum)
    (hN : (w.minimum + w.fraction) ≤ N) (hN' : N ≤ (w.maximum + w.fraction - 1))
    (hv : (m : Rat) * (2 : Rat) ^ e ≤ (2 : Rat) ^ N)
    : ∃ q,
        packedValue w (roundWithAccuracy w.spec s m e a) = some q
        ∧ |q - (s.apply (m : Int) : Rat) * (2 : Rat) ^ e| ≤ (2 : Rat) ^ (N - w.fraction) := by
  have ht := target_le_of_value_le w m e N hm hN hv
  have he := first_exponent_eq_target w m e a hc
  obtain ⟨q, hq, herror⟩ := round_error w s m e a hc (by rw [he]; omega)
  refine ⟨q, hq, le_trans herror ?_⟩
  rw [he]
  exact zpow_le_zpow_right₀ (by norm_num : (1 : Rat) ≤ 2) ht

/-- Rounding a zero truncated mantissa still accounts for its accuracy flag.
This case occurs when division underflows before the final rounding step. -/
theorem round_zero_with_accuracy_error (w : Width) (s : Sign) (e N : Int) (a : Accuracy)
    (he : e ≤ w.minimum) (hN : (w.minimum + w.fraction) ≤ N)
    : ∃ q,
        packedValue w (roundWithAccuracy w.spec s 0 e a) = some q
        ∧ |q| ≤ (2 : Rat) ^ (N - w.fraction) := by
  have ht : (shiftToTargetExponent w.spec 0 e a).2 = w.minimum := by
    rw [first_exponent_eq_target w _ _ _ (Or.inr he)]
    change max ((0 : Int) + 1 + e - (1 + w.fraction)) w.minimum = w.minimum
    exact max_eq_right (by omega)
  obtain ⟨q, hq, herr⟩ := round_error w s 0 e a (Or.inr he) (by rw [ht]; exact w.exponent_room)
  refine ⟨q, hq, ?_⟩
  have herr' : |q| ≤ (2 : Rat)^(w.minimum : Int) := by
    cases s <;> simpa [Sign.apply, ht] using herr
  exact herr'.trans (zpow_le_zpow_right₀ (by norm_num) (by omega))

theorem normalize_error (w : Width) (m : Int) (e N : Int) (zs : Sign)
    (hN : (w.minimum + w.fraction) ≤ N) (hN' : N ≤ (w.maximum + w.fraction - 1))
    (hv : |(m : Rat) * (2 : Rat) ^ e| ≤ (2 : Rat) ^ N)
    : ∃ q,
        packedValue w (UnpackedFloat.normalize w.spec m e zs) = some q
        ∧ |q - (m : Rat) * (2 : Rat) ^ e| ≤ (2 : Rat) ^ (N - w.fraction) := by
  by_cases hz : m = 0
  · subst m
    refine ⟨0, ?_, ?_⟩
    · simp only [UnpackedFloat.normalize, show compare (0 : Int) 0 = Ordering.eq by decide]
      exact packedValue_zero w zs
    · simp only [Int.cast_zero, zero_mul, sub_self, abs_zero]
      exact le_of_lt (zpow_pos (by norm_num : (0 : Rat) < 2) _)
  have hp : 0 < (2 : Rat)^e := zpow_pos (by norm_num : (0 : Rat) < 2) e
  by_cases hn : m < 0
  · have hn' : 0 < (-m).toNat := by omega
    have hm : ((-m).toNat : Int) = -m := by omega
    have hv' : ((-m).toNat : Rat) * (2 : Rat)^e ≤ (2 : Rat)^N := by
      have hcast : ((-m).toNat : Rat) = -(m : Rat) := by exact_mod_cast hm
      rw [hcast]
      have hneg : (m : Rat) ≤ 0 := by exact_mod_cast le_of_lt hn
      simpa only [abs_mul, abs_of_nonpos hneg, abs_of_pos hp] using hv
    obtain ⟨q, hq, he⟩ := round_direct_error w .negative (-m).toNat e N hn' hN hN' hv'
    refine ⟨q, ?_, ?_⟩
    · unfold UnpackedFloat.normalize
      rw [Int.compare_eq_lt.mpr hn]
      exact hq
    · simpa only [Sign.apply, hm, neg_neg] using he
  · have hn' : 0 < m.toNat := by omega
    have hm : (m.toNat : Int) = m := by omega
    have hv' : (m.toNat : Rat) * (2 : Rat)^e ≤ (2 : Rat)^N := by
      have hcast : (m.toNat : Rat) = (m : Rat) := by exact_mod_cast hm
      rw [hcast]
      have hpos : 0 ≤ (m : Rat) := by exact_mod_cast (by omega : 0 ≤ m)
      simpa only [abs_mul, abs_of_nonneg hpos, abs_of_pos hp] using hv
    obtain ⟨q, hq, he⟩ := round_direct_error w .positive m.toNat e N hn' hN hN' hv'
    refine ⟨q, ?_, ?_⟩
    · unfold UnpackedFloat.normalize
      rw [Int.compare_eq_gt.mpr (by omega)]
      exact hq
    · simpa only [Sign.apply, hm] using he

end Flare.FloatFormat.Rounding
