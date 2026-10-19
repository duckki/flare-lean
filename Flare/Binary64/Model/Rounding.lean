module

public import Mathlib.Tactic.Ring
public import Flare.Binary64.Model.Conversion
public import Mathlib.Tactic.Linarith

/-!
# Concrete binary64 rounding bounds

These proofs interpret the pinned model's mantissa shifting, carry, packing, and
normalization code as exact rational arithmetic. The bound is deliberately a full
ulp, so it does not require assuming a nearest-rounding theorem. The magnitude
hypotheses keep the packed result finite; subnormal outputs and signed zeros are
covered. No native-decide axiom or hypothetical rounding law is used.
-/

open Float.Model Float.Model.UnpackedFloat
@[expose] public section

namespace Flare.Binary64.Model.Rounding
open Flare.Binary64.Model.Conversion

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

private theorem shift_floor_bound (m : Nat) (s : Nat) (hs : m.log2 ≤ 52 + s)
    : m / 2 ^ s < 2 ^ 53 := by
  apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ s)).mpr
  have h := Nat.lt_log2_self (n := m)
  have hp : 2^(m.log2 + 1) ≤ 2^(53+s) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [← Nat.pow_add]
  exact lt_of_lt_of_le h hp

private theorem shift_floor_normal (m s : Nat) (hm : m ≠ 0) (hs : m.log2 = 52 + s)
    : 2 ^ 52 ≤ m / 2 ^ s := by
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ s)).mpr
  rw [← Nat.pow_add, ← hs]
  exact Nat.log2_self_le hm

private theorem target_shift_bounds (m : Nat) (e : Int)
    : let t := Format.binary64.targetExponent (totalExponent m e)
      let k := (t - e).toNat
      (-1074 : Int) ≤ e + k ∧ m.log2 ≤ 52 + k := by
  simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
  norm_num
  omega

private theorem shift_small_identity (m : Nat) (e : Int) (hm : m < 2 ^ 53) (he : -1074 ≤ e)
    : shiftToTargetExponent Format.binary64 m e .exact
      = (ExtendedMantissa.mk m false false, e) := by
  have hk : m.log2 ≤ 52 := by
    by_cases h : m = 0
    · simp [h]
    · have := (Nat.log2_lt h).mpr hm; omega
  have ht : Format.binary64.targetExponent (totalExponent m e) ≤ e := by
    simp [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
    omega
  have hs : (Format.binary64.targetExponent (totalExponent m e) - e).toNat = 0 := by omega
  simp [shiftToTargetExponent, shiftToExponent, hs, HShiftRight.hShiftRight,
    Nat.repeat, ExtendedMantissa.ofMantissaAndAccuracy]

private theorem shift_overflow_identity (e : Int) (he : -1074 ≤ e)
    : shiftToTargetExponent Format.binary64 (2 ^ 53) e .exact
      = (ExtendedMantissa.mk (2 ^ 52) false false, e + 1) := by
  have ht : Format.binary64.targetExponent (totalExponent (2^53) e) = e + 1 := by
    simp only [Format.targetExponent, totalExponent, Nat.log2_two_pow,
      Format.mantissaBits, Format.minExponent]
    norm_num
    omega
  unfold shiftToTargetExponent
  rw [ht]
  simp [shiftToExponent,
    HShiftRight.hShiftRight, Nat.repeat, ExtendedMantissa.ofMantissaAndAccuracy,
    ExtendedMantissa.shiftRightOne]

private theorem round_eq_firstRounded (s : Sign) (m : Nat) (e : Int) (a : Accuracy)
    : let first := shiftToTargetExponent Format.binary64 m e a
      let r := first.1.roundedMantissa
      roundWithAccuracy Format.binary64 s m e a
      = if h : r = 0 then
          .zero s
        else if r < 2 ^ 53 then
          .finite s r first.2 (Nat.pos_of_ne_zero h)
        else
          .finite s (2 ^ 52) (first.2 + 1) (by decide) := by
  dsimp only
  have hshift := target_shift_bounds m e
  dsimp only at hshift
  have hf : (shiftToTargetExponent Format.binary64 m e a).1.mantissa =
      m / 2^((Format.binary64.targetExponent (totalExponent m e) - e).toNat) := by
    simp [shiftToTargetExponent, shiftToExponent, shift_mantissa,
      ExtendedMantissa.ofMantissaAndAccuracy]
    cases a with
    | exact => rfl
    | inexact o => cases o <;> rfl
  have hb := rounded_mantissa_bounds (shiftToTargetExponent Format.binary64 m e a).1
  have he : -1074 ≤ (shiftToTargetExponent Format.binary64 m e a).2 := hshift.1
  have hr : (shiftToTargetExponent Format.binary64 m e a).1.roundedMantissa ≤ 2^53 := by
    rw [hf] at hb
    have := shift_floor_bound m _ hshift.2
    omega
  generalize hfirst : shiftToTargetExponent Format.binary64 m e a = first at *
  rcases first with ⟨em, e₁⟩
  rw [roundWithAccuracy, hfirst]
  dsimp only at *
  by_cases hz : em.roundedMantissa = 0
  · rw [hz, shift_small_identity 0 e₁ (by decide) he]
    rfl
  by_cases hsmall : em.roundedMantissa < 2^53
  · rw [shift_small_identity _ _ hsmall he]
    simp only [hz, hsmall, ↓reduceDIte, ↓reduceIte]
  · have hmax : em.roundedMantissa = 2^53 := by omega
    rw [hmax, shift_overflow_identity _ he]
    rfl

theorem unpack_pack_subnormal (s : Sign) (m : Nat) (hp : 0 < m) (hm : m < 2 ^ 52)
    : (Float.Model.pack (.finite s m (-1074) hp)).unpack = .finite s m (-1074) hp := by
  have hk : m.log2 < 52 := (Nat.log2_lt (Nat.ne_of_gt hp)).mpr hm
  have hne : (BitVec.ofNat 52 m) ≠ 0#52 := by
    intro h
    have hb := congrArg BitVec.toNat h
    change m % 2^52 = 0 at hb
    rw [Nat.mod_eq_of_lt hm] at hb
    omega
  unfold Float.Model.unpack Float.Model.pack
  simp only [UnpackedFloat.pack, Format.exponentBias, Format.binary64, Format.mantissaBits]
  norm_num
  simp only [show m.log2 ≠ 52 by omega, ↓reduceIte,
    UnpackedFloat.unpack, unpackExponent_packComponents,
    unpackMantissa_packComponents, unpackSign_components]
  simp only [hne, ↓reduceIte, ↓reduceDIte]
  have hnat : (BitVec.ofNat 52 m).toNat = m := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  simp only [hnat]
  cases s <;> rfl

private theorem first_floor (m : Nat) (e : Int) (a : Accuracy)
    : (shiftToTargetExponent Format.binary64 m e a).1.mantissa
      = m / 2 ^ ((Format.binary64.targetExponent (totalExponent m e) - e).toNat) := by
  simp [shiftToTargetExponent, shiftToExponent, shift_mantissa,
    ExtendedMantissa.ofMantissaAndAccuracy]
  cases a with
  | exact => rfl
  | inexact o => cases o <;> rfl

private theorem first_canonical (m : Nat) (e : Int) (a : Accuracy) (hc : 52 ≤ m.log2 ∨ e ≤ -1074)
    : 2 ^ 52 ≤ (shiftToTargetExponent Format.binary64 m e a).1.roundedMantissa
      ∨ (shiftToTargetExponent Format.binary64 m e a).2 = -1074 := by
  let t := Format.binary64.targetExponent (totalExponent m e)
  let k := (t - e).toNat
  have ht : t = max ((m.log2 : Int) + e - 52) (-1074) := by
    dsimp [t, Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
    omega
  have het : e ≤ t := by omega
  have he' : e + (k : Int) = t := by dsimp [k]; omega
  by_cases hmin : t = -1074
  · right
    change e + (k : Int) = -1074
    omega
  · left
    have hlog : 52 ≤ m.log2 := by omega
    have hm : m ≠ 0 := by intro h; simp [h] at hlog
    have hk : m.log2 = 52 + k := by dsimp [k]; omega
    have hl := shift_floor_normal m k hm hk
    have hr := rounded_mantissa_bounds (shiftToTargetExponent Format.binary64 m e a).1
    rw [first_floor] at hr
    exact le_trans hl hr.1

/-- Exact packed value after the first rounded mantissa, including a carry
into the next binade. The exponent bound excludes overflow. -/
theorem round_rational_value (s : Sign) (m : Nat) (e : Int) (a : Accuracy)
    (hc : 52 ≤ m.log2 ∨ e ≤ -1074)
    (he : (shiftToTargetExponent Format.binary64 m e a).2 ≤ 970)
    : Flare.Binary64.Model.Value.toRational
        (Float.Model.pack (roundWithAccuracy Format.binary64 s m e a))
      = some
          (((s.apply ((shiftToTargetExponent Format.binary64 m e a).1.roundedMantissa : Int)) : Rat)
            * (2 : Rat) ^ ((shiftToTargetExponent Format.binary64 m e a).2)) := by
  have hl : -1074 ≤ (shiftToTargetExponent Format.binary64 m e a).2 := (target_shift_bounds m e).1
  have hc' := first_canonical m e a hc
  rw [round_eq_firstRounded]
  by_cases hz : (shiftToTargetExponent Format.binary64 m e a).1.roundedMantissa = 0
  · simp only [hz, ↓reduceDIte]
    cases s <;> change some (0 : Rat) = _ <;> simp [Sign.apply]
  by_cases hn : (shiftToTargetExponent Format.binary64 m e a).1.roundedMantissa < 2^53
  · simp only [hz, hn, ↓reduceDIte, ↓reduceIte]
    unfold Flare.Binary64.Model.Value.toRational
    rcases hc' with hc' | hc'
    · rw [unpack_pack_normal _ _ _ _ ((Nat.log2_eq_iff hz).mpr ⟨hc', hn⟩) hl (by omega)]
      rfl
    · by_cases hb : 2^52 ≤ (shiftToTargetExponent Format.binary64 m e a).1.roundedMantissa
      · rw [unpack_pack_normal _ _ _ _ ((Nat.log2_eq_iff hz).mpr ⟨hb, hn⟩) hl (by omega)]
        rfl
      · simp only [hc']
        rw [unpack_pack_subnormal _ _ _ (by omega)]
        rfl
  · have hr : (shiftToTargetExponent Format.binary64 m e a).1.roundedMantissa = 2^53 := by
      have h := rounded_mantissa_bounds (shiftToTargetExponent Format.binary64 m e a).1
      rw [first_floor] at h
      have h' := shift_floor_bound m _ (target_shift_bounds m e).2
      omega
    simp only [hz, hn, ↓reduceDIte, ↓reduceIte]
    unfold Flare.Binary64.Model.Value.toRational
    rw [unpack_pack_normal _ _ _ _ Nat.log2_two_pow (by omega) (by omega)]
    simp only [Flare.Binary64.Model.Value.unpackedToRational, hr]
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

private theorem round_error (s : Sign) (m : Nat) (e : Int) (a : Accuracy)
    (hc : 52 ≤ m.log2 ∨ e ≤ -1074)
    (he : (shiftToTargetExponent Format.binary64 m e a).2 ≤ 970)
    : ∃ q,
        Flare.Binary64.Model.Value.toRational
            (Float.Model.pack (roundWithAccuracy Format.binary64 s m e a))
          = some q
        ∧ |q - (s.apply (m : Int) : Rat) * (2 : Rat) ^ e|
          ≤ (2 : Rat) ^ ((shiftToTargetExponent Format.binary64 m e a).2) := by
  rw [round_rational_value s m e a hc he]
  refine ⟨_, rfl, ?_⟩
  have hr := rounded_mantissa_bounds (shiftToTargetExponent Format.binary64 m e a).1
  rw [first_floor] at hr
  have h := dyadic_round_error m _ _ e hr
  have hs : (shiftToTargetExponent Format.binary64 m e a).2 =
      e + (Format.binary64.targetExponent (totalExponent m e) - e).toNat := rfl
  rw [hs]
  cases s <;> simpa only [Sign.apply, Int.cast_neg, Int.cast_natCast,
    neg_mul, neg_sub_neg, abs_sub_comm] using h

theorem unpack_finite_shape (v : Float.Model) (s : Sign) (m : Nat) (e : Int)
    (hp : 0 < m) (hu : v.unpack = .finite s m e hp)
    : m < 2 ^ 53 ∧ -1074 ≤ e ∧ e ≤ 971 ∧ (m.log2 = 52 ∨ e = -1074) := by
  unfold Float.Model.unpack UnpackedFloat.unpack at hu
  dsimp only at hu
  split at hu
  · split at hu <;> cases hu
  · rename_i hninf
    split at hu
    · rename_i hzero
      split at hu
      · cases hu
      · cases hu
        have hb := (unpackMantissa (spec := Format.binary64) v.toBits.toBitVec).isLt
        simp only [hzero, BitVec.toNat_ofNat] at *
        norm_num [Format.exponentBias, Format.mantissaBits] at *
        omega
    · rename_i hnzero
      cases hu
      have hb := (unpackMantissa (spec := Format.binary64) v.toBits.toBitVec).isLt
      have he := (unpackExponent (spec := Format.binary64) v.toBits.toBitVec).isLt
      have he0 : (unpackExponent (spec := Format.binary64) v.toBits.toBitVec).toNat ≠ 0 := by
        intro h
        apply hnzero
        exact BitVec.eq_of_toNat_eq h
      have hemax : (unpackExponent (spec := Format.binary64) v.toBits.toBitVec).toNat ≠ 2047 := by
        intro h
        apply hninf
        exact BitVec.eq_of_toNat_eq h
      have hm : (1#1 ++ unpackMantissa (spec := Format.binary64) v.toBits.toBitVec).toNat =
          2^52 + (unpackMantissa (spec := Format.binary64) v.toBits.toBitVec).toNat := by
        simp only [BitVec.toNat_append]
        rw [← Nat.shiftLeft_add_eq_or_of_lt hb]
        rfl
      rw [hm]
      have hlog : (2^52 + (unpackMantissa (spec := Format.binary64) v.toBits.toBitVec).toNat).log2 =
        52 := by
        apply (Nat.log2_eq_iff (by omega)).mpr
        constructor <;> omega
      change (unpackMantissa (spec := Format.binary64) v.toBits.toBitVec).toNat < 2^52 at hb
      change (unpackExponent (spec := Format.binary64) v.toBits.toBitVec).toNat < 2^11 at he
      change 2^52 + (unpackMantissa (spec := Format.binary64) v.toBits.toBitVec).toNat < 2^53 ∧
        -1074 ≤ ((unpackExponent (spec := Format.binary64) v.toBits.toBitVec).toNat : Int) - 1075 ∧
        ((unpackExponent (spec := Format.binary64) v.toBits.toBitVec).toNat : Int) - 1075 ≤ 971 ∧ _
      exact ⟨by omega, by omega, by omega, Or.inl hlog⟩

private theorem target_le_of_value_le (m : Nat) (e N : Int) (hm : 0 < m)
    (hN : -1022 ≤ N) (hv : (m : Rat) * (2 : Rat) ^ e ≤ (2 : Rat) ^ N)
    : Format.binary64.targetExponent (totalExponent m e) ≤ N - 52 := by
  have hl : (2 : Rat)^m.log2 ≤ (m : Rat) := by
    exact_mod_cast Nat.log2_self_le (Nat.ne_of_gt hm)
  have hp : 0 ≤ (2 : Rat)^e := le_of_lt (zpow_pos (by norm_num : (0 : Rat) < 2) e)
  have h := le_trans (mul_le_mul_of_nonneg_right hl hp) hv
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)] at h
  have hexp := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : Rat) < 2)).mp h
  simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
  norm_num
  omega

private theorem first_exponent_eq_target (m : Nat) (e : Int) (a : Accuracy)
    (hc : 52 ≤ m.log2 ∨ e ≤ -1074)
    : (shiftToTargetExponent Format.binary64 m e a).2
      = Format.binary64.targetExponent (totalExponent m e) := by
  change e + (Format.binary64.targetExponent (totalExponent m e) - e).toNat = _
  simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
  norm_num
  omega

theorem decrease_preserves_value (m k : Nat) (e : Int)
    : ((m <<< k : Nat) : Rat) * (2 : Rat) ^ (e - (k : Int)) = (m : Rat) * (2 : Rat) ^ e := by
  rw [Nat.shiftLeft_eq]
  push_cast
  rw [← zpow_natCast, mul_assoc, ← zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
  have he : (k : Int) + (e - (k : Int)) = e := by omega
  rw [he]

theorem round_direct_error (s : Sign) (m : Nat) (e N : Int)
    (hm : 0 < m) (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hv : (m : Rat) * (2 : Rat) ^ e ≤ (2 : Rat) ^ N)
    : ∃ q,
        Flare.Binary64.Model.Value.toRational (Float.Model.pack (round Format.binary64 s m e))
          = some q
        ∧ |q - (s.apply (m : Int) : Rat) * (2 : Rat) ^ e| ≤ (2 : Rat) ^ (N - 52) := by
  let t := Format.binary64.targetExponent (totalExponent m e)
  let k := (e - t).toNat
  have ht : t = max ((m.log2 : Int) + e - 52) (-1074) := by
    dsimp [t, Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
    omega
  have hlog : (m <<< k).log2 = m.log2 + k := log2_shift m k hm
  have hc : 52 ≤ (m <<< k).log2 ∨ e - (k : Int) ≤ -1074 := by
    rw [hlog]
    dsimp [k]
    omega
  have htotal : totalExponent (m <<< k) (e - (k : Int)) = totalExponent m e := by
    simp only [totalExponent, hlog, Nat.cast_add]
    omega
  have hb := target_le_of_value_le m e N hm hN hv
  have hexp : (shiftToTargetExponent Format.binary64 (m <<< k) (e - (k : Int)) .exact).2 = t := by
    rw [first_exponent_eq_target _ _ _ hc, htotal]
  obtain ⟨q, hq, herror⟩ := round_error s (m <<< k) (e - (k : Int)) .exact hc
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

theorem round_with_accuracy_error (s : Sign) (m : Nat) (e N : Int) (a : Accuracy)
    (hm : 0 < m) (hc : 52 ≤ m.log2 ∨ e ≤ -1074)
    (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hv : (m : Rat) * (2 : Rat) ^ e ≤ (2 : Rat) ^ N)
    : ∃ q,
        Flare.Binary64.Model.Value.toRational
            (Float.Model.pack (roundWithAccuracy Format.binary64 s m e a))
          = some q
        ∧ |q - (s.apply (m : Int) : Rat) * (2 : Rat) ^ e| ≤ (2 : Rat) ^ (N - 52) := by
  have ht := target_le_of_value_le m e N hm hN hv
  have he := first_exponent_eq_target m e a hc
  obtain ⟨q, hq, herror⟩ := round_error s m e a hc (by rw [he]; omega)
  refine ⟨q, hq, le_trans herror ?_⟩
  rw [he]
  exact zpow_le_zpow_right₀ (by norm_num : (1 : Rat) ≤ 2) ht

/-- Rounding a zero truncated mantissa still accounts for its accuracy flag.
This case occurs when division underflows before the final rounding step. -/
theorem round_zero_with_accuracy_error (s : Sign) (e N : Int) (a : Accuracy)
    (he : e ≤ -1074) (hN : -1022 ≤ N)
    : ∃ q,
        Flare.Binary64.Model.Value.toRational
            (Float.Model.pack (roundWithAccuracy Format.binary64 s 0 e a))
          = some q
        ∧ |q| ≤ (2 : Rat) ^ (N - 52) := by
  have ht : (shiftToTargetExponent Format.binary64 0 e a).2 = -1074 := by
    rw [first_exponent_eq_target _ _ _ (Or.inr he)]
    simp [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
    omega
  obtain ⟨q, hq, herr⟩ := round_error s 0 e a (Or.inr he) (by rw [ht]; norm_num)
  refine ⟨q, hq, ?_⟩
  have herr' : |q| ≤ (2 : Rat)^(-1074 : Int) := by
    cases s <;> simpa [Sign.apply, ht] using herr
  exact herr'.trans (zpow_le_zpow_right₀ (by norm_num) (by omega))

theorem normalize_error (m : Int) (e N : Int) (zs : Sign)
    (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hv : |(m : Rat) * (2 : Rat) ^ e| ≤ (2 : Rat) ^ N)
    : ∃ q,
        Flare.Binary64.Model.Value.toRational
            (Float.Model.pack (UnpackedFloat.normalize Format.binary64 m e zs))
          = some q
        ∧ |q - (m : Rat) * (2 : Rat) ^ e| ≤ (2 : Rat) ^ (N - 52) := by
  by_cases hz : m = 0
  · subst m
    refine ⟨0, ?_, ?_⟩
    · simp only [UnpackedFloat.normalize, show compare (0 : Int) 0 = Ordering.eq by decide]
      cases zs <;> rfl
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
    obtain ⟨q, hq, he⟩ := round_direct_error .negative (-m).toNat e N hn' hN hN' hv'
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
    obtain ⟨q, hq, he⟩ := round_direct_error .positive m.toNat e N hn' hN hN' hv'
    refine ⟨q, ?_, ?_⟩
    · unfold UnpackedFloat.normalize
      rw [Int.compare_eq_gt.mpr (by omega)]
      exact hq
    · simpa only [Sign.apply, hm] using he

theorem pack_unpack_rational (v : Float.Model)
    : Flare.Binary64.Model.Value.toRational (Float.Model.pack v.unpack)
      = Flare.Binary64.Model.Value.toRational v := by
  cases hu : v.unpack with
  | notANumber =>
      unfold Flare.Binary64.Model.Value.toRational; rw [hu]; rfl
  | infinity s =>
      unfold Flare.Binary64.Model.Value.toRational; rw [hu]; cases s <;> rfl
  | zero s =>
      unfold Flare.Binary64.Model.Value.toRational; rw [hu]; cases s <;> rfl
  | finite s m e hp =>
      have ⟨hb, he, he', hc⟩ := unpack_finite_shape v s m e hp hu
      unfold Flare.Binary64.Model.Value.toRational
      rw [hu]
      rcases hc with hc | hc
      · rw [unpack_pack_normal s m e hp hc he he']
      · subst e
        by_cases hm : m < 2^52
        · rw [unpack_pack_subnormal s m hp hm]
        · rw [unpack_pack_normal s m (-1074) hp
            ((Nat.log2_eq_iff (Nat.ne_of_gt hp)).mpr ⟨by omega, hb⟩) he he']

theorem finite_of_rational (v : Float.Model) (q : Rat)
    (h : Flare.Binary64.Model.Value.toRational v = some q)
    : v.isFinite = true := by
  unfold Flare.Binary64.Model.Value.toRational at h
  change v.unpack.isFinite = true
  cases hu : v.unpack <;> simp_all [Flare.Binary64.Model.Value.unpackedToRational,
    UnpackedFloat.isFinite]

end Flare.Binary64.Model.Rounding
