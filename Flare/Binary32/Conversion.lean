module

public import Init.Data.Float.Float32
public import Flare.Binary64.Arithmetic
public import Flare.FloatFormat.Rounding

/-! Model-backed binary32 storage conversions. Lean's native `Float.toFloat32`
and `Float32.toFloat` are opaque at the pinned version; these executable functions
use the pinned rounding/packing definitions instead. Source-language casts map to
this model through an explicit runtime/source correspondence boundary. -/

@[expose] public section

namespace Flare.Binary32.Conversion

open Float.Model Float.Model.UnpackedFloat
open Flare.FloatFormat Flare.FloatFormat.Format

/-- Exact finite meaning of a native binary32 value; sentinels have no value. -/
def toRational (x : Float32) : Option ℚ :=
  unpackedToRational x.toModel.unpack

/-- Round a binary64 value to binary32 using the pinned nearest/even model. -/
def narrow (x : Float) : Float32 :=
  .ofModel
    (.pack
      (match x.toModel.unpack with
        | .finite s m e _ => round .binary32 s m e
        | v => v))

/-- Embed every finite binary32 value exactly in binary64 by padding its mantissa.
NaN/infinity and signed zero retain their corresponding model constructors. -/
def widen (x : Float32) : Float :=
  .ofModel
    (.pack
      (match x.toModel.unpack with
        | .finite s m e hp =>
            let k := 52 - m.log2
            .finite s (m <<< k) (e - (k : Int)) (Nat.shiftLeft_pos_iff.mpr hp)
        | v => v))

/-- Binary32 storage followed by exact binary64 promotion. -/
def roundTrip (x : Float) : Float := widen (narrow x)

/-- Promotion loses no finite binary32 value, including every subnormal. -/
theorem widen_exact (x : Float32) (q : ℚ) (hq : toRational x = some q)
    : Flare.Binary64.Model.Value.toRational (widen x).toModel = some q := by
  cases hu : x.toModel.unpack with
  | notANumber => simp [toRational, hu, unpackedToRational] at hq
  | infinity s => simp [toRational, hu, unpackedToRational] at hq
  | zero s =>
      have hzero : q = 0 := by simpa [toRational, hu, unpackedToRational] using hq.symm
      subst q
      simp only [widen, hu]
      cases s <;> rfl
  | finite s m e hp =>
      have ⟨hm, he, he', _⟩ := Packing.unpack_finite_shape .binary32
        x.toModel.toBits.toBitVec s m e hp hu
      change m < 2 ^ 24 at hm
      have hk : m.log2 ≤ 23 := by
        have h := (Nat.log2_lt (Nat.ne_of_gt hp)).mpr hm
        omega
      let k := 52 - m.log2
      have hlog : (m <<< k).log2 = 52 := by
        rw [Packing.log2_shift m k hp]
        dsimp [k]
        omega
      have hlo : -1074 ≤ e - (k : Int) := by
        dsimp [k]
        change -149 ≤ e at he
        omega
      have hhi : e - (k : Int) ≤ 971 := by
        change e ≤ 104 at he'
        omega
      have hpack := Flare.Binary64.Model.Conversion.unpack_pack_normal s (m <<< k)
        (e - (k : Int)) (Nat.shiftLeft_pos_iff.mpr hp) hlog hlo hhi
      change unpackedToRational (Float.Model.unpack (Float.Model.pack _)) = some q
      simp only [hu]
      rw [hpack]
      have hvalue := Rounding.decrease_preserves_value m k e
      have hmeaning : (s.apply (m : Int) : ℚ) * (2 : ℚ) ^ e = q := by
        simpa [toRational, hu, unpackedToRational] using hq
      apply congrArg some
      rw [← hmeaning]
      cases s
      · simpa only [Sign.apply, Int.cast_neg, Int.cast_natCast, neg_mul]
          using congrArg Neg.neg hvalue
      · simpa only [Sign.apply, Int.cast_natCast] using hvalue

/-- Narrowing has a model-derived one-ulp allowance below the selected magnitude.
The normal exponent floor makes the allowance cover gradual underflow as well. -/
theorem narrow_error (x : Float) (r : ℚ) (N : Int)
    (hr : Flare.Binary64.Model.Value.toRational x.toModel = some r)
    (hN : -126 ≤ N) (hN' : N ≤ 126) (hv : |r| ≤ (2 : ℚ) ^ N)
    : ∃ q, toRational (narrow x) = some q ∧ |q - r| ≤ (2 : ℚ) ^ (N - 23) := by
  cases hu : x.toModel.unpack with
  | notANumber =>
      simp [Flare.Binary64.Model.Value.toRational, hu,
        Flare.Binary64.Model.Value.unpackedToRational] at hr
  | infinity s =>
      simp [Flare.Binary64.Model.Value.toRational, hu,
        Flare.Binary64.Model.Value.unpackedToRational] at hr
  | zero s =>
      have hz : r = 0 := by
        simpa [Flare.Binary64.Model.Value.toRational, hu,
          Flare.Binary64.Model.Value.unpackedToRational]
          using hr.symm
      subst r
      refine ⟨
        0,
        ?_,
        by simp only [sub_self, abs_zero]; exact (zpow_pos (by norm_num : (0 : ℚ) < 2) (N - 23)).le
      ⟩
      change packedValue .binary32 (match x.toModel.unpack with
        | .finite s m e _ => round .binary32 s m e
        | v => v) = some 0
      rw [hu]
      exact packedValue_zero .binary32 s
  | finite s m e hp =>
      have hmeaning : (s.apply (m : Int) : ℚ) * (2 : ℚ) ^ e = r := by
        simpa [Flare.Binary64.Model.Value.toRational, hu,
          Flare.Binary64.Model.Value.unpackedToRational]
          using hr
      have hmag : (m : ℚ) * (2 : ℚ) ^ e = |r| := by
        rw [← hmeaning, abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℚ) < 2) _)]
        cases s <;> simp [Sign.apply]
      obtain ⟨q, hq, herr⟩ := Rounding.round_direct_error .binary32 s m e N hp hN hN'
        (by rw [hmag]; exact hv)
      refine ⟨q, ?_, ?_⟩
      · change packedValue .binary32 _ = some q
        simpa only [narrow, hu] using hq
      · change |q - (s.apply (m : Int) : ℚ) * (2 : ℚ) ^ e| ≤ (2 : ℚ) ^ (N - 23) at herr
        simpa only [hmeaning] using herr

/-- A storage round trip retains the binary32 narrowing allowance exactly. -/
theorem roundTrip_error (x : Float) (r : ℚ) (N : Int)
    (hr : Flare.Binary64.Model.Value.toRational x.toModel = some r)
    (hN : -126 ≤ N) (hN' : N ≤ 126) (hv : |r| ≤ (2 : ℚ) ^ N)
    : ∃ q,
        Flare.Binary64.Model.Value.toRational (roundTrip x).toModel = some q
        ∧ |q - r| ≤ (2 : ℚ) ^ (N - 23) := by
  obtain ⟨q, hq, he⟩ := narrow_error x r N hr hN hN' hv
  exact ⟨q, widen_exact (narrow x) q hq, he⟩

end Flare.Binary32.Conversion
