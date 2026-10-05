import Flare.Binary64.Model.Value
import Mathlib.Tactic.NormNum
import Std.Tactic.BVDecide

open Float.Model
open Float.Model.UnpackedFloat

/-!
# Binary64 packing and bounded signed conversion

Kernel-checked facts about Lean's normalization and packing code, including
normal finite values and the bounded Int32-to-Float conversion expression.
-/

namespace Flare.Binary64.Model.Conversion
theorem log2_shift (n k : Nat) (hn : 0 < n) : (n <<< k).log2 = n.log2 + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h : n <<< k ≠ 0 := Nat.ne_of_gt (Nat.shiftLeft_pos_iff.mpr hn)
      have heq : n <<< (k + 1) = 2 * (n <<< k) := by
        simp [Nat.shiftLeft_eq, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
      rw [heq, Nat.log2_two_mul h, ih]
      omega

theorem shiftTarget_exact (s : Sign) (m : Nat) (e : Int) (hm : m.log2 = 52) (he : -1074 ≤ e)
    : roundWithAccuracy Format.binary64 s m e .exact
      = if h : m = 0 then .zero s else .finite s m e (Nat.pos_of_ne_zero h) := by
  have ht : Format.binary64.targetExponent (totalExponent m e) = e := by
    simp [Format.targetExponent, totalExponent, Format.mantissaBits,
      Format.minExponent, hm, max_eq_left he]
  simp [roundWithAccuracy, shiftToTargetExponent, ht, shiftToExponent,
    ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.roundedMantissa,
    ExtendedMantissa.accuracy, Accuracy.roundToNearestEven, HShiftRight.hShiftRight,
    Nat.repeat]

private theorem round_small (s : Sign) (n : Nat) (hn : 0 < n) (hb : n < 2 ^ 32)
    : round Format.binary64 s n 0
      = .finite s (n <<< (52 - n.log2)) ((n.log2 : Int) - 52) (Nat.shiftLeft_pos_iff.mpr hn) := by
  have hk : n.log2 < 32 := (Nat.log2_lt (Nat.ne_of_gt hn)).mpr hb
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

theorem unpackSign_components (s : Sign) (e : BitVec 11) (m : BitVec 52)
    : unpackSign (packComponents Format.binary64 s e m) = s.toBitVec := by
  cases s <;> simp [unpackSign, packComponents, Sign.toBitVec] <;> bv_decide

theorem unpack_pack_normal (s : Sign) (m : Nat) (e : Int)
    (hp : 0 < m) (hm : m.log2 = 52) (he : -1074 ≤ e) (he' : e ≤ 971)
    : (Float.Model.pack (.finite s m e hp)).unpack = .finite s m e hp := by
  have hbounds := (Nat.log2_eq_iff (Nat.ne_of_gt hp)).mp hm
  have hepos : 0 < (e + 1075).toNat := by omega
  have helim : (e + 1075).toNat < 2047 := by omega
  have hne : (BitVec.ofNat 11 (e + 1075).toNat) ≠ 0#11 := by
    intro h
    have hb := congrArg BitVec.toNat h
    change (e + 1075).toNat % 2048 = 0 at hb
    omega
  have hni : (BitVec.ofNat 11 (e + 1075).toNat) ≠ -1#11 := by
    intro h
    have hb := congrArg BitVec.toNat h
    change (e + 1075).toNat % 2048 = 2047 at hb
    omega
  have hexp : (((BitVec.ofNat 11 (e + 1075).toNat).toNat : Nat) : Int) - 1075 = e := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hmant : (1#1 ++ BitVec.ofNat 52 m).toNat = m := by
    simp only [BitVec.toNat_append, BitVec.toNat_ofNat]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide))]
    norm_num at hbounds ⊢
    omega
  unfold Float.Model.unpack Float.Model.pack
  simp only [UnpackedFloat.pack, Format.exponentBias,
    Format.binary64, Format.mantissaBits, hm]
  norm_num
  simp only [show e + 1023 + 52 = e + 1075 by omega,
    show ¬2047 ≤ (e + 1075).toNat by omega, ↓reduceIte]
  simp only [UnpackedFloat.unpack, unpackExponent_packComponents,
    unpackMantissa_packComponents, unpackSign_components, hne, hni, ↓reduceIte]
  change UnpackedFloat.finite (Sign.ofBitVec s.toBitVec) (1#1 ++ BitVec.ofNat 52 m).toNat
    ((BitVec.ofNat 11 (e + 1075).toNat).toNat - 1075) _ = _
  simp only [hexp, hmant]
  cases s <;> rfl

private theorem model_ofNat_small (n : Nat) (hn : 0 < n) (hb : n < 2 ^ 32)
    : Float.Model.ofNat n
      = Float.Model.pack
          (.finite .positive (n <<< (52 - n.log2)) ((n.log2 : Int) - 52)
            (Nat.shiftLeft_pos_iff.mpr hn)) := by
  unfold Float.Model.ofNat UnpackedFloat.ofNat UnpackedFloat.ofInt UnpackedFloat.normalize
  rw [Int.compare_eq_gt.mpr (by omega)]
  simp only [Int.toNat_natCast, round_small _ n hn hb]

private theorem model_ofInt_neg_small (n : Nat) (hn : 0 < n) (hb : n < 2 ^ 32)
    : Float.Model.ofInt (-(n : Int)) = -Float.Model.ofNat n := by
  have hk : n.log2 < 32 := (Nat.log2_lt (Nat.ne_of_gt hn)).mpr hb
  rw [model_ofNat_small n hn hb]
  change Float.Model.pack (UnpackedFloat.ofInt Format.binary64 (-(n : Int))) =
    Float.Model.pack ((Float.Model.pack _).unpack.neg)
  rw [unpack_pack_normal _ _ _ _ (by rw [log2_shift n _ hn]; omega) (by omega) (by omega)]
  unfold UnpackedFloat.ofInt UnpackedFloat.normalize
  rw [Int.compare_eq_lt.mpr (by omega)]
  simp only [Int.neg_neg, Int.toNat_natCast, round_small _ n hn hb]
  rfl

private theorem magnitude_toNat (q : Int32) (hq : q < 0)
    : ((-(q + 1)).toUInt32 + 1).toNat = (-q.toInt).toNat := by
  have hq' : q.toInt < 0 := Int32.lt_iff_toInt_lt.mp hq
  have hbound := q.toUInt32.toNat_lt
  have hint := BitVec.toInt_eq_toNat_cond q.toBitVec
  change q.toInt = if 2 * q.toUInt32.toNat < 4294967296 then
    (q.toUInt32.toNat : Int) else (q.toUInt32.toNat : Int) - 4294967296 at hint
  have hn : 0 < q.toUInt32.toNat := by split at hint <;> omega
  have hi : q.toInt = (q.toUInt32.toNat : Int) - 4294967296 := by split at hint <;> omega
  have hw : (-(q + 1)).toUInt32 + 1 = -q.toUInt32 := by
    simp only [Int32.toUInt32_neg, Int32.toUInt32_add]
    bv_decide
  rw [hw, UInt32.toNat_neg]
  change (4294967296 - q.toUInt32.toNat) % 4294967296 = _
  omega

theorem model_signedConversion (q : Int32)
    : (if q < 0 then -((-(q + 1)).toUInt32 + 1).toFloat else q.toUInt32.toFloat).toModel
      = Float.Model.ofInt32 q := by
  split
  next hq =>
    change -Float.Model.ofNat ((-(q + 1)).toUInt32 + 1).toNat = Float.Model.ofInt q.toInt
    rw [magnitude_toNat q hq]
    have hq' : q.toInt < 0 := Int32.lt_iff_toInt_lt.mp hq
    have hlo := q.le_toInt
    have hn : 0 < (-q.toInt).toNat := by omega
    have hb : (-q.toInt).toNat < 2^32 := by omega
    have he : q.toInt = -((-q.toInt).toNat : Int) := by omega
    conv_rhs => rw [he]
    exact (model_ofInt_neg_small _ hn hb).symm
  next hq =>
    change Float.Model.ofInt (q.toUInt32.toNat : Int) = Float.Model.ofInt q.toInt
    congr 1
    have h : 0 ≤ q := by
      apply Int32.le_iff_toInt_le.mpr
      have hq' : ¬ q.toInt < 0 := fun h => hq (Int32.lt_iff_toInt_lt.mpr h)
      change 0 ≤ q.toInt
      omega
    rw [Int32.toNat_toUInt32_of_le h, Int32.toInt_eq_toNatClampNeg h]

end Flare.Binary64.Model.Conversion
