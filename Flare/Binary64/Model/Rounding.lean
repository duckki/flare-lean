module

public import Flare.Binary64.Model.Conversion
public import Flare.FloatFormat.Rounding

/-! Binary64 instances of the shared IEEE packing and rounding inference.
The exported statements retain their original assumptions and allowances. -/

@[expose] public section

namespace Flare.Binary64.Model.Rounding

open Float.Model Float.Model.UnpackedFloat
open Flare.Binary64.Model.Conversion

theorem unpack_pack_subnormal (s : Sign) (m : Nat) (hp : 0 < m) (hm : m < 2 ^ 52)
    : (Float.Model.pack (.finite s m (-1074) hp)).unpack = .finite s m (-1074) hp :=
  Flare.FloatFormat.Packing.unpack_pack_subnormal .binary64 s m hp hm

theorem round_rational_value (s : Sign) (m : Nat) (e : Int) (a : Accuracy)
    (hc : 52 ≤ m.log2 ∨ e ≤ -1074)
    (he : (shiftToTargetExponent Format.binary64 m e a).2 ≤ 970)
    : Flare.Binary64.Model.Value.toRational
        (Float.Model.pack (roundWithAccuracy Format.binary64 s m e a))
      = some
          (((s.apply ((shiftToTargetExponent Format.binary64 m e a).1.roundedMantissa : Int)) : Rat)
            * (2 : Rat) ^ ((shiftToTargetExponent Format.binary64 m e a).2)) :=
  Flare.FloatFormat.Rounding.round_rational_value .binary64 s m e a hc he

theorem unpack_finite_shape (v : Float.Model) (s : Sign) (m : Nat) (e : Int)
    (hp : 0 < m) (hu : v.unpack = .finite s m e hp)
    : m < 2 ^ 53 ∧ -1074 ≤ e ∧ e ≤ 971 ∧ (m.log2 = 52 ∨ e = -1074) :=
  Flare.FloatFormat.Packing.unpack_finite_shape .binary64 v.toBits.toBitVec s m e hp hu

theorem decrease_preserves_value (m k : Nat) (e : Int)
    : ((m <<< k : Nat) : Rat) * (2 : Rat) ^ (e - (k : Int)) = (m : Rat) * (2 : Rat) ^ e :=
  Flare.FloatFormat.Rounding.decrease_preserves_value m k e

theorem round_direct_error (s : Sign) (m : Nat) (e N : Int)
    (hm : 0 < m) (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hv : (m : Rat) * (2 : Rat) ^ e ≤ (2 : Rat) ^ N)
    : ∃ q,
        Flare.Binary64.Model.Value.toRational (Float.Model.pack (round Format.binary64 s m e))
          = some q
        ∧ |q - (s.apply (m : Int) : Rat) * (2 : Rat) ^ e| ≤ (2 : Rat) ^ (N - 52) :=
  Flare.FloatFormat.Rounding.round_direct_error .binary64 s m e N hm hN hN' hv

theorem round_with_accuracy_error (s : Sign) (m : Nat) (e N : Int) (a : Accuracy)
    (hm : 0 < m) (hc : 52 ≤ m.log2 ∨ e ≤ -1074)
    (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hv : (m : Rat) * (2 : Rat) ^ e ≤ (2 : Rat) ^ N)
    : ∃ q,
        Flare.Binary64.Model.Value.toRational
            (Float.Model.pack (roundWithAccuracy Format.binary64 s m e a))
          = some q
        ∧ |q - (s.apply (m : Int) : Rat) * (2 : Rat) ^ e| ≤ (2 : Rat) ^ (N - 52) :=
  Flare.FloatFormat.Rounding.round_with_accuracy_error .binary64 s m e N a hm hc hN hN' hv

theorem round_zero_with_accuracy_error (s : Sign) (e N : Int) (a : Accuracy)
    (he : e ≤ -1074) (hN : -1022 ≤ N)
    : ∃ q,
        Flare.Binary64.Model.Value.toRational
            (Float.Model.pack (roundWithAccuracy Format.binary64 s 0 e a))
          = some q
        ∧ |q| ≤ (2 : Rat) ^ (N - 52) :=
  Flare.FloatFormat.Rounding.round_zero_with_accuracy_error .binary64 s e N a he hN

theorem normalize_error (m : Int) (e N : Int) (zs : Sign)
    (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hv : |(m : Rat) * (2 : Rat) ^ e| ≤ (2 : Rat) ^ N)
    : ∃ q,
        Flare.Binary64.Model.Value.toRational
            (Float.Model.pack (UnpackedFloat.normalize Format.binary64 m e zs))
          = some q
        ∧ |q - (m : Rat) * (2 : Rat) ^ e| ≤ (2 : Rat) ^ (N - 52) :=
  Flare.FloatFormat.Rounding.normalize_error .binary64 m e N zs hN hN' hv

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
