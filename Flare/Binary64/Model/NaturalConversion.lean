module

public import Mathlib.Tactic.Ring
public import Flare.Binary64.Model.Arithmetic

/-! Exact bounded natural-number conversion and division. These bounds follow
from Float.Model.divCore and its rounding implementation. Model operations
remain outside the native numerical kernels. -/

open Float.Model Float.Model.UnpackedFloat
open Flare.Binary64.Model.Rounding
@[expose] public section

namespace Flare.Binary64.Model.NaturalConversion
open Flare.Binary64.Model.Arithmetic Flare.Binary64.Model.Conversion

private theorem round_nat_exact (s : Sign) (n : Nat) (hn : 0 < n) (hb : n < 2 ^ 53)
    : round Format.binary64 s n 0
      = .finite s (n <<< (52 - n.log2)) ((n.log2 : Int) - 52) (Nat.shiftLeft_pos_iff.mpr hn) := by
  have hk : n.log2 < 53 := (Nat.log2_lt (Nat.ne_of_gt hn)).mpr hb
  have ht : Format.binary64.targetExponent (totalExponent n 0) = (n.log2 : Int) - 52 := by
    simp [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
    omega
  have hs : (0 - ((n.log2 : Int) - 52)).toNat = 52 - n.log2 := by omega
  have he : (0 : Int) - (52 - n.log2 : Nat) = (n.log2 : Int) - 52 := by omega
  have hm : (n <<< (52 - n.log2)).log2 = 52 := by rw [log2_shift n _ hn]; omega
  rw [round, ht, decreaseExponent, hs]
  dsimp only
  rw [he, shiftTarget_exact s _ _ hm (by omega)]
  simp [Nat.ne_of_gt (Nat.shiftLeft_pos_iff.mpr hn)]

theorem ofNat_unpack (n : Nat) (hn : 0 < n) (hb : n < 2 ^ 53)
    : (Float.Model.ofNat n).unpack
      = .finite .positive (n <<< (52 - n.log2)) ((n.log2 : Int) - 52)
          (Nat.shiftLeft_pos_iff.mpr hn) := by
  have hk : n.log2 < 53 := (Nat.log2_lt (Nat.ne_of_gt hn)).mpr hb
  unfold Float.Model.ofNat UnpackedFloat.ofNat UnpackedFloat.ofInt UnpackedFloat.normalize
  rw [Int.compare_eq_gt.mpr (by omega)]
  simp only [Int.toNat_natCast, round_nat_exact _ n hn hb]
  exact unpack_pack_normal _ _ _ _
    (by rw [log2_shift n _ hn]; omega)
    (by omega)
    (by omega)

theorem ofNat_exact (n : Nat) (hb : n < 2 ^ 53)
    : Flare.Binary64.Model.Value.toRational (Float.Model.ofNat n) = some (n : Rat) := by
  by_cases hn : n = 0
  · subst n; rfl
  · have hn := Nat.pos_of_ne_zero hn
    have hk : n.log2 < 53 := (Nat.log2_lt (Nat.ne_of_gt hn)).mpr hb
    unfold Flare.Binary64.Model.Value.toRational
    rw [ofNat_unpack n hn hb]
    change some (((n <<< (52 - n.log2) : Nat) : Rat) * (2 : Rat)^((n.log2 : Int) - 52)) = _
    have h := decrease_preserves_value n (52 - n.log2) 0
    have he : (0 : Int) - ((52 - n.log2 : Nat) : Int) = (n.log2 : Int) - 52 := by omega
    rw [he] at h
    simpa using congrArg some h

private theorem divCore_normal (m n : Nat) (e f : Int)
    (hm : m.log2 = 52) (hn : n.log2 = 52) (he : -52 ≤ e) (hf : f ≤ 0)
    : divCore Format.binary64 m e n f
      = ((m <<< 53) / n, e - f - 53, accuracyOfFraction ((m <<< 53) % n) n) := by
  have ht
      : Format.binary64.targetExponent (totalExponent m e - totalExponent n f) = e - f - 53 := by
    simp [Format.targetExponent, totalExponent, hm, hn, Format.mantissaBits, Format.minExponent]
    omega
  simp [divCore, ht]

/-- The division used for time normalization: positive exact integers with numerator
at most denominator. The conservative error includes quotient truncation and final rounding. -/
theorem nat_div_error (n d : Nat) (hd : 0 < d) (hnd : n ≤ d) (hb : d < 2 ^ 53)
    : ∃ q,
        Flare.Binary64.Model.Value.toRational (Float.Model.ofNat n / Float.Model.ofNat d) = some q
        ∧ |q - (n : Rat) / (d : Rat)| ≤ (2 : Rat) ^ (-51 : Int) := by
  by_cases hn : n = 0
  · subst n
    refine ⟨0, ?_, by norm_num⟩
    change Flare.Binary64.Model.Value.toRational (Float.Model.pack (UnpackedFloat.div
      Format.binary64
      (Float.Model.ofNat 0).unpack (Float.Model.ofNat d).unpack)) = _
    rw [ofNat_unpack d hd hb]
    change Flare.Binary64.Model.Value.toRational (Float.Model.pack (UnpackedFloat.div
      Format.binary64
      (.zero .positive) _)) = _
    simp only [UnpackedFloat.div]
    rfl
  · have hn := Nat.pos_of_ne_zero hn
    have hnb : n < 2^53 := lt_of_le_of_lt hnd hb
    have hnlog : n.log2 < 53 := (Nat.log2_lt (Nat.ne_of_gt hn)).mpr hnb
    have hdlog : d.log2 < 53 := (Nat.log2_lt (Nat.ne_of_gt hd)).mpr hb
    let m := n <<< (52 - n.log2)
    let k := d <<< (52 - d.log2)
    let e : Int := (n.log2 : Int) - (d.log2 : Int) - 53
    let p := (m <<< 53) / k
    have hmpos : 0 < m := Nat.shiftLeft_pos_iff.mpr hn
    have hkpos : 0 < k := Nat.shiftLeft_pos_iff.mpr hd
    have hmlog : m.log2 = 52 := by dsimp [m]; rw [log2_shift n _ hn]; omega
    have hklog : k.log2 = 52 := by dsimp [k]; rw [log2_shift d _ hd]; omega
    have hmb := (Nat.log2_eq_iff (Nat.ne_of_gt hmpos)).mp hmlog
    have hkb := (Nat.log2_eq_iff (Nat.ne_of_gt hkpos)).mp hklog
    have hplow : 2^52 ≤ p := by
      apply (Nat.le_div_iff_mul_le hkpos).mpr
      rw [Nat.shiftLeft_eq]
      exact le_trans (Nat.mul_le_mul_left _ (le_of_lt hkb.2)) (Nat.mul_le_mul_right _ hmb.1)
    have hppos : 0 < p := by omega
    have hpe : 52 ≤ p.log2 := (Nat.le_log2 (Nat.ne_of_gt hppos)).mpr hplow
    have he : e ≤ -53 := by
      have : n.log2 ≤ d.log2 := (Nat.le_log2 (Nat.ne_of_gt hd)).mpr
        (le_trans ((Nat.le_log2 (Nat.ne_of_gt hn)).mp (le_refl _)) hnd)
      dsimp [e]
      omega
    have hexact : ((m <<< 53 : Nat) : Rat) * (2 : Rat)^e / (k : Rat) = (n : Rat) / (d : Rat) := by
      have hm := decrease_preserves_value n (52 - n.log2) 0
      have hk := decrease_preserves_value d (52 - d.log2) 0
      have hmexp : (0 : Int) - ((52 - n.log2 : Nat) : Int) = (n.log2 : Int) - 52 := by omega
      have hkexp : (0 : Int) - ((52 - d.log2 : Nat) : Int) = (d.log2 : Int) - 52 := by omega
      rw [hmexp] at hm
      rw [hkexp] at hk
      simp only [zpow_zero, mul_one] at hm hk
      rw [Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      have hz : (2 : Rat) ≠ 0 := by norm_num
      have hpowers : (2 : Rat)^(53 : Nat) * (2 : Rat)^e =
          (2 : Rat)^((n.log2 : Int) - 52) / (2 : Rat)^((d.log2 : Int) - 52) := by
        rw [← zpow_natCast (2 : Rat) 53, ← zpow_add₀ hz, ← zpow_sub₀ hz]
        congr 1
        dsimp [e]
        omega
      rw [mul_assoc, hpowers, ← hm, ← hk]
      ring
    have hfloor : (p : Rat) * (2 : Rat)^e ≤ (n : Rat) / (d : Rat) ∧
        (n : Rat) / (d : Rat) ≤ ((p : Rat) + 1) * (2 : Rat)^e := by
      have hlow : p * k ≤ m <<< 53 := Nat.div_mul_le_self _ _
      have hhigh : m <<< 53 < (p + 1) * k := by
        simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ (m <<< 53) hkpos
      have hkR : (0 : Rat) < k := by exact_mod_cast hkpos
      have hep := le_of_lt (zpow_pos (by norm_num : (0 : Rat) < 2) e)
      have hlowR : (p : Rat) * k ≤ (m <<< 53 : Nat) := by exact_mod_cast hlow
      have hhighR : ((m <<< 53 : Nat) : Rat) ≤ ((p : Rat) + 1) * k := by
        exact_mod_cast le_of_lt hhigh
      rw [← hexact]
      constructor
      · apply (le_div_iff₀ hkR).mpr
        simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_right hlowR hep
      · apply (div_le_iff₀ hkR).mpr
        simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_right hhighR hep
    have hle : (n : Rat) / (d : Rat) ≤ 1 := by
      apply (div_le_one (by exact_mod_cast hd)).mpr
      exact_mod_cast hnd
    obtain ⟨q, hq, herr⟩ := round_with_accuracy_error .positive p e 0
      (accuracyOfFraction ((m <<< 53) % k) k) hppos (Or.inl hpe) (by norm_num) (by norm_num)
      (by simpa using le_trans hfloor.1 hle)
    refine ⟨q, ?_, ?_⟩
    · change Flare.Binary64.Model.Value.toRational (Float.Model.pack (UnpackedFloat.div
      Format.binary64
        (Float.Model.ofNat n).unpack (Float.Model.ofNat d).unpack)) = _
      rw [ofNat_unpack n hn hnb, ofNat_unpack d hd hb]
      simp only [UnpackedFloat.div]
      rw [divCore_normal _ _ ((n.log2 : Int) - 52) ((d.log2 : Int) - 52) hmlog hklog (by omega) (by
        omega)]
      have heq : (n.log2 : Int) - 52 - ((d.log2 : Int) - 52) - 53 = e := by dsimp [e]; omega
      rw [heq]
      dsimp only
      exact hq
    · have hep : (2 : Rat)^e ≤ (2 : Rat)^(-53 : Int) :=
        zpow_le_zpow_right₀ (by norm_num) he
      simp only [Sign.apply, Int.cast_natCast] at herr
      have htriangle := abs_sub_le q ((p : Rat) * (2 : Rat)^e) ((n : Rat) / (d : Rat))
      have hrem : |(p : Rat) * (2 : Rat)^e - (n : Rat) / (d : Rat)| ≤ (2 : Rat)^e := by
        rw [abs_of_nonpos (by linarith only [hfloor.1])]
        nlinarith only [hfloor.2]
      norm_num at herr hep ⊢
      linarith only [htriangle, hrem, herr, hep]

/-- Real-valued form of the bounded tick division theorem. -/
theorem nat_div_error_real (n d : Nat) (hd : 0 < d) (hnd : n ≤ d) (hb : d < 2 ^ 53)
    : ∃ q : ℝ,
        Flare.Binary64.Model.Value.toReal (Float.Model.ofNat n / Float.Model.ofNat d) = some q
        ∧ |q - (n : ℝ) / (d : ℝ)| ≤ (2 : ℝ) ^ (-51 : Int) := by
  obtain ⟨q, hq, herr⟩ := nat_div_error n d hd hnd hb
  refine ⟨(q : ℝ), by simp [Flare.Binary64.Model.Value.toReal, hq], ?_⟩
  have hcast := (Rat.cast_le (K := ℝ)).mpr herr
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_zpow,
    Rat.cast_ofNat]
    using hcast

end Flare.Binary64.Model.NaturalConversion
