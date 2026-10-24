module

public import Flare.FloatFormat.Format
public import Mathlib.Tactic.NormNum
public import Std.Tactic.BVDecide

/-! Exact packing and canonical finite shapes for binary32 and binary64. The
width-dependent bit-vector facts are isolated here; rounding inference is shared. -/

@[expose] public section

namespace Flare.FloatFormat.Packing

open Flare.FloatFormat.Format

open Float.Model Float.Model.UnpackedFloat

theorem log2_shift (n k : Nat) (hn : 0 < n) : (n <<< k).log2 = n.log2 + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h : n <<< k ≠ 0 := Nat.ne_of_gt (Nat.shiftLeft_pos_iff.mpr hn)
      have heq : n <<< (k + 1) = 2 * (n <<< k) := by
        simp [Nat.shiftLeft_eq, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
      rw [heq, Nat.log2_two_mul h, ih]
      omega

private theorem unpackSign_components32 (s : Sign) (e : BitVec 8) (m : BitVec 23)
    : unpackSign (packComponents Float.Model.Format.binary32 s e m) = s.toBitVec := by
  cases s <;> simp [unpackSign, packComponents, Sign.toBitVec] <;> bv_decide

private theorem unpack_pack_normal32 (s : Sign) (m : Nat) (e : Int)
    (hp : 0 < m) (hm : m.log2 = 23) (he : -149 ≤ e) (he' : e ≤ 104)
    : (Float32.Model.pack (.finite s m e hp)).unpack = .finite s m e hp := by
  have hbounds := (Nat.log2_eq_iff (Nat.ne_of_gt hp)).mp hm
  have hepos : 0 < (e + 150).toNat := by omega
  have helim : (e + 150).toNat < 255 := by omega
  have hne : (BitVec.ofNat 8 (e + 150).toNat) ≠ 0#8 := by
    intro h
    have hb := congrArg BitVec.toNat h
    change (e + 150).toNat % 256 = 0 at hb
    omega
  have hni : (BitVec.ofNat 8 (e + 150).toNat) ≠ -1#8 := by
    intro h
    have hb := congrArg BitVec.toNat h
    change (e + 150).toNat % 256 = 255 at hb
    omega
  have hexp : (((BitVec.ofNat 8 (e + 150).toNat).toNat : Nat) : Int) - 150 = e := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hmant : (1#1 ++ BitVec.ofNat 23 m).toNat = m := by
    simp only [BitVec.toNat_append, BitVec.toNat_ofNat]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide))]
    norm_num at hbounds ⊢
    omega
  unfold Float32.Model.unpack Float32.Model.pack
  simp only [UnpackedFloat.pack, Float.Model.Format.exponentBias,
    Float.Model.Format.binary32, Float.Model.Format.mantissaBits, hm]
  norm_num
  simp only [show e + 127 + 23 = e + 150 by omega,
    show ¬255 ≤ (e + 150).toNat by omega, ↓reduceIte]
  simp only [UnpackedFloat.unpack, unpackExponent_packComponents,
    unpackMantissa_packComponents, unpackSign_components32, hne, hni, ↓reduceIte]
  change UnpackedFloat.finite (Sign.ofBitVec s.toBitVec) (1#1 ++ BitVec.ofNat 23 m).toNat
    ((BitVec.ofNat 8 (e + 150).toNat).toNat - 150) _ = _
  simp only [hexp, hmant]
  cases s <;> rfl

private theorem unpack_pack_subnormal32 (s : Sign) (m : Nat) (hp : 0 < m) (hm : m < 2 ^ 23)
    : (Float32.Model.pack (.finite s m (-149) hp)).unpack = .finite s m (-149) hp := by
  have hk : m.log2 < 23 := (Nat.log2_lt (Nat.ne_of_gt hp)).mpr hm
  have hne : (BitVec.ofNat 23 m) ≠ 0#23 := by
    intro h
    have hb := congrArg BitVec.toNat h
    change m % 2^23 = 0 at hb
    rw [Nat.mod_eq_of_lt hm] at hb
    omega
  unfold Float32.Model.unpack Float32.Model.pack
  simp only [UnpackedFloat.pack, Float.Model.Format.exponentBias,
    Float.Model.Format.binary32, Float.Model.Format.mantissaBits]
  norm_num
  simp only [show m.log2 ≠ 23 by omega, ↓reduceIte,
    UnpackedFloat.unpack, unpackExponent_packComponents,
    unpackMantissa_packComponents, unpackSign_components32]
  simp only [hne, ↓reduceIte, ↓reduceDIte]
  have hnat : (BitVec.ofNat 23 m).toNat = m := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  simp only [hnat]
  cases s <;> rfl

private theorem unpack_finite_shape32 (v : BitVec 32) (s : Sign) (m : Nat) (e : Int)
    (hp : 0 < m) (hu : UnpackedFloat.unpack Float.Model.Format.binary32 v = .finite s m e hp)
    : m < 2 ^ 24 ∧ -149 ≤ e ∧ e ≤ 104 ∧ (m.log2 = 23 ∨ e = -149) := by
  unfold UnpackedFloat.unpack at hu
  dsimp only at hu
  split at hu
  · split at hu <;> cases hu
  · rename_i hninf
    split at hu
    · rename_i hzero
      split at hu
      · cases hu
      · cases hu
        have hb := (unpackMantissa (spec := Float.Model.Format.binary32) v).isLt
        simp only [hzero, BitVec.toNat_ofNat] at *
        norm_num [Float.Model.Format.exponentBias, Float.Model.Format.mantissaBits] at *
        omega
    · rename_i hnzero
      cases hu
      have hb := (unpackMantissa (spec := Float.Model.Format.binary32) v).isLt
      have he := (unpackExponent (spec := Float.Model.Format.binary32) v).isLt
      have he0 : (unpackExponent (spec := Float.Model.Format.binary32) v).toNat ≠ 0 := by
        intro h
        apply hnzero
        exact BitVec.eq_of_toNat_eq h
      have hemax : (unpackExponent (spec := Float.Model.Format.binary32) v).toNat ≠ 255 := by
        intro h
        apply hninf
        exact BitVec.eq_of_toNat_eq h
      have hm : (1#1 ++ unpackMantissa (spec := Float.Model.Format.binary32) v).toNat =
          2^23 + (unpackMantissa (spec := Float.Model.Format.binary32) v).toNat := by
        simp only [BitVec.toNat_append]
        rw [← Nat.shiftLeft_add_eq_or_of_lt hb]
        rfl
      rw [hm]
      have hlog : (2^23 + (unpackMantissa (spec := Float.Model.Format.binary32) v).toNat).log2 =
        23 := by
        apply (Nat.log2_eq_iff (by omega)).mpr
        constructor <;> omega
      change (unpackMantissa (spec := Float.Model.Format.binary32) v).toNat < 2^23 at hb
      change (unpackExponent (spec := Float.Model.Format.binary32) v).toNat < 2^8 at he
      change 2^23 + (unpackMantissa (spec := Float.Model.Format.binary32) v).toNat < 2^24 ∧
        -149 ≤ ((unpackExponent (spec := Float.Model.Format.binary32) v).toNat : Int) - 150 ∧
        ((unpackExponent (spec := Float.Model.Format.binary32) v).toNat : Int) - 150 ≤ 104 ∧ _
      exact ⟨by omega, by omega, by omega, Or.inl hlog⟩

private theorem unpackSign_components64 (s : Sign) (e : BitVec 11) (m : BitVec 52)
    : unpackSign (packComponents Float.Model.Format.binary64 s e m) = s.toBitVec := by
  cases s <;> simp [unpackSign, packComponents, Sign.toBitVec] <;> bv_decide

private theorem unpack_pack_normal64 (s : Sign) (m : Nat) (e : Int)
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
  simp only [UnpackedFloat.pack, Float.Model.Format.exponentBias,
    Float.Model.Format.binary64, Float.Model.Format.mantissaBits, hm]
  norm_num
  simp only [show e + 1023 + 52 = e + 1075 by omega,
    show ¬2047 ≤ (e + 1075).toNat by omega, ↓reduceIte]
  simp only [UnpackedFloat.unpack, unpackExponent_packComponents,
    unpackMantissa_packComponents, unpackSign_components64, hne, hni, ↓reduceIte]
  change UnpackedFloat.finite (Sign.ofBitVec s.toBitVec) (1#1 ++ BitVec.ofNat 52 m).toNat
    ((BitVec.ofNat 11 (e + 1075).toNat).toNat - 1075) _ = _
  simp only [hexp, hmant]
  cases s <;> rfl

private theorem unpack_pack_subnormal64 (s : Sign) (m : Nat) (hp : 0 < m) (hm : m < 2 ^ 52)
    : (Float.Model.pack (.finite s m (-1074) hp)).unpack = .finite s m (-1074) hp := by
  have hk : m.log2 < 52 := (Nat.log2_lt (Nat.ne_of_gt hp)).mpr hm
  have hne : (BitVec.ofNat 52 m) ≠ 0#52 := by
    intro h
    have hb := congrArg BitVec.toNat h
    change m % 2^52 = 0 at hb
    rw [Nat.mod_eq_of_lt hm] at hb
    omega
  unfold Float.Model.unpack Float.Model.pack
  simp only [UnpackedFloat.pack, Float.Model.Format.exponentBias,
    Float.Model.Format.binary64, Float.Model.Format.mantissaBits]
  norm_num
  simp only [show m.log2 ≠ 52 by omega, ↓reduceIte,
    UnpackedFloat.unpack, unpackExponent_packComponents,
    unpackMantissa_packComponents, unpackSign_components64]
  simp only [hne, ↓reduceIte, ↓reduceDIte]
  have hnat : (BitVec.ofNat 52 m).toNat = m := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  simp only [hnat]
  cases s <;> rfl

private theorem unpack_finite_shape64 (v : BitVec 64) (s : Sign) (m : Nat) (e : Int)
    (hp : 0 < m) (hu : UnpackedFloat.unpack Float.Model.Format.binary64 v = .finite s m e hp)
    : m < 2 ^ 53 ∧ -1074 ≤ e ∧ e ≤ 971 ∧ (m.log2 = 52 ∨ e = -1074) := by
  unfold UnpackedFloat.unpack at hu
  dsimp only at hu
  split at hu
  · split at hu <;> cases hu
  · rename_i hninf
    split at hu
    · rename_i hzero
      split at hu
      · cases hu
      · cases hu
        have hb := (unpackMantissa (spec := Float.Model.Format.binary64) v).isLt
        simp only [hzero, BitVec.toNat_ofNat] at *
        norm_num [Float.Model.Format.exponentBias, Float.Model.Format.mantissaBits] at *
        omega
    · rename_i hnzero
      cases hu
      have hb := (unpackMantissa (spec := Float.Model.Format.binary64) v).isLt
      have he := (unpackExponent (spec := Float.Model.Format.binary64) v).isLt
      have he0 : (unpackExponent (spec := Float.Model.Format.binary64) v).toNat ≠ 0 := by
        intro h
        apply hnzero
        exact BitVec.eq_of_toNat_eq h
      have hemax : (unpackExponent (spec := Float.Model.Format.binary64) v).toNat ≠ 2047 := by
        intro h
        apply hninf
        exact BitVec.eq_of_toNat_eq h
      have hm : (1#1 ++ unpackMantissa (spec := Float.Model.Format.binary64) v).toNat =
          2^52 + (unpackMantissa (spec := Float.Model.Format.binary64) v).toNat := by
        simp only [BitVec.toNat_append]
        rw [← Nat.shiftLeft_add_eq_or_of_lt hb]
        rfl
      rw [hm]
      have hlog : (2^52 + (unpackMantissa (spec := Float.Model.Format.binary64) v).toNat).log2 =
        52 := by
        apply (Nat.log2_eq_iff (by omega)).mpr
        constructor <;> omega
      change (unpackMantissa (spec := Float.Model.Format.binary64) v).toNat < 2^52 at hb
      change (unpackExponent (spec := Float.Model.Format.binary64) v).toNat < 2^11 at he
      change 2^52 + (unpackMantissa (spec := Float.Model.Format.binary64) v).toNat < 2^53 ∧
        -1074 ≤ ((unpackExponent (spec := Float.Model.Format.binary64) v).toNat : Int) - 1075 ∧
        ((unpackExponent (spec := Float.Model.Format.binary64) v).toNat : Int) - 1075 ≤ 971 ∧ _
      exact ⟨by omega, by omega, by omega, Or.inl hlog⟩

/-- The sign field survives packing in either supported width. -/
theorem unpackSign_components (w : Width) (s : Sign)
    (e : BitVec w.spec.exponentBits) (m : BitVec w.fraction)
    : unpackSign (packComponents w.spec s e m) = s.toBitVec := by
  cases w
  · exact unpackSign_components32 s e m
  · exact unpackSign_components64 s e m

/-- Packing a canonical normal value preserves every component. -/
theorem unpack_pack_normal (w : Width) (s : Sign) (m : Nat) (e : Int)
    (hp : 0 < m) (hm : m.log2 = w.fraction)
    (he : w.minimum ≤ e) (he' : e ≤ w.maximum)
    : unpack w.spec (pack w.spec (.finite s m e hp)) = .finite s m e hp := by
  cases w
  · exact unpack_pack_normal32 s m e hp hm he he'
  · exact unpack_pack_normal64 s m e hp hm he he'

/-- Packing a positive subnormal preserves its integer mantissa. -/
theorem unpack_pack_subnormal (w : Width) (s : Sign) (m : Nat)
    (hp : 0 < m) (hm : m < 2 ^ w.fraction)
    : unpack w.spec (pack w.spec (.finite s m w.minimum hp)) = .finite s m w.minimum hp := by
  cases w
  · exact unpack_pack_subnormal32 s m hp hm
  · exact unpack_pack_subnormal64 s m hp hm

/-- Every decoded finite nonzero value has a canonical mantissa and exponent. -/
theorem unpack_finite_shape (w : Width) (bits : BitVec w.spec.numBits)
    (s : Sign) (m : Nat) (e : Int) (hp : 0 < m)
    (hu : unpack w.spec bits = .finite s m e hp)
    : m < 2 ^ (w.fraction + 1)
      ∧ w.minimum ≤ e
      ∧ e ≤ w.maximum
      ∧ (m.log2 = w.fraction ∨ e = w.minimum) := by
  cases w
  · exact unpack_finite_shape32 bits s m e hp hu
  · exact unpack_finite_shape64 bits s m e hp hu

end Flare.FloatFormat.Packing
