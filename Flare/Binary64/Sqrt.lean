import Flare.Binary64.Arithmetic
import Flare.Binary64.Rounding
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Sqrt

/-! Accuracy of the actual binary64 square-root model used by Jacobi.
The proof follows `sqrtCore`'s integer square root and `roundWithAccuracy`.
It includes subnormal inputs; a positive binary64 square root is normal.
-/

namespace Flare.Binary64.Sqrt
open Float.Model Float.Model.UnpackedFloat
open Flare.Binary64.Value Flare.Binary64.Arithmetic
open Flare.Binary64.Model.Rounding

private lemma core_shape (m : Nat) (e : Int) (hm : 0 < m) (hmb : m < 2^53)
    (he : -1074 ≤ e) (he' : e ≤ 971)
    : (let t := ((m.log2 : Int) + e + 2) / 2 - 53;
        let shifted := m <<< (e - 2 * t).toNat;
        let root := Nat.sqrt shifted;
        -589 ≤ t
        ∧ t ≤ 459
        ∧ e - 2 * t ≥ 0
        ∧ root.log2 = 52
        ∧ sqrtCore Format.binary64 m e
          = (
            root,
            t,
            if shifted - root * root = 0 then
              .exact
            else
              .inexact (if shifted - root * root ≤ root then .lt else .gt)
          )) := by
  dsimp only
  have hlog : m.log2 ≤ 52 := by
    have := (Nat.log2_lt (Nat.ne_of_gt hm)).mpr hmb
    omega
  let t := ((m.log2 : Int) + e + 2) / 2 - 53
  have ht : -589 ≤ t ∧ t ≤ 459 ∧ 0 ≤ e - 2 * t := by dsimp [t]; omega
  have ht' : min (e / 2) (Format.binary64.targetExponent ((totalExponent m e + 1) / 2)) = t := by
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
    dsimp [t]
    omega
  have hshift : (m <<< (e - 2 * t).toNat).log2 = m.log2 + (e - 2 * t).toNat :=
    Flare.Binary64.Model.Conversion.log2_shift m _ hm
  have hshiftpos : 0 < m <<< (e - 2 * t).toNat := Nat.shiftLeft_pos_iff.mpr hm
  have hshiftlog : 104 ≤ (m <<< (e - 2 * t).toNat).log2 ∧
      (m <<< (e - 2 * t).toNat).log2 ≤ 105 := by
    rw [hshift]
    dsimp [t]
    omega
  have hlow : 2^104 ≤ m <<< (e - 2 * t).toNat :=
    (Nat.le_log2 (Nat.ne_of_gt hshiftpos)).mp hshiftlog.1
  have hhigh : m <<< (e - 2 * t).toNat < 2^106 :=
    (Nat.log2_lt (Nat.ne_of_gt hshiftpos)).mp (by omega)
  have hrlo : 2^52 ≤ Nat.sqrt (m <<< (e - 2 * t).toNat) := Nat.le_sqrt.mpr (by
    convert hlow using 1; norm_num)
  have hrhi : Nat.sqrt (m <<< (e - 2 * t).toNat) < 2^53 := Nat.sqrt_lt.mpr (by
    convert hhigh using 1; norm_num)
  refine ⟨ht.1, ht.2.1, ht.2.2, ?_, ?_⟩
  · exact (Nat.log2_eq_iff (Nat.ne_of_gt (Nat.sqrt_pos.mpr hshiftpos))).mpr ⟨hrlo, hrhi⟩
  · unfold sqrtCore
    have ht'' : min (e.ediv 2) (Format.binary64.targetExponent
        ((totalExponent m e + 1).ediv 2)) = t := ht'
    rw [ht'']

private lemma integer_root_rounding (z : Nat)
    : let r := Nat.sqrt z
      let acc :=
        if z - r * r = 0 then
          Accuracy.exact
        else
          Accuracy.inexact (if z - r * r ≤ r then .lt else .gt)
      |(acc.roundToNearestEven r : ℝ) - Real.sqrt (z : ℝ)| ≤ 1 / 2 := by
  let r := Nat.sqrt z
  let d := z - r * r
  have hlow : r^2 ≤ z := Nat.sqrt_le' z
  have hhigh : z < (r + 1)^2 := Nat.lt_succ_sqrt' z
  have hz : (z : ℝ) = (r : ℝ)^2 + (d : ℝ) := by
    have he : z = r^2 + d := by dsimp [d]; rw [pow_two] at hlow ⊢; omega
    exact_mod_cast he
  have hs : (Real.sqrt (z : ℝ))^2 = (z : ℝ) := Real.sq_sqrt (Nat.cast_nonneg z)
  have hs0 := Real.sqrt_nonneg (z : ℝ)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hlow' : (r : ℝ)^2 ≤ (z : ℝ) := by exact_mod_cast hlow
  have hhigh' : (z : ℝ) < ((r : ℝ) + 1)^2 := by exact_mod_cast hhigh
  dsimp only
  change |((if d = 0 then Accuracy.exact else Accuracy.inexact (if d ≤ r then .lt else
    .gt)).roundToNearestEven r : ℝ) - _| ≤ _
  by_cases hd : d = 0
  · simp only [hd, ite_true, Accuracy.roundToNearestEven]
    rw [abs_le]
    have hd' : (d : ℝ) = 0 := by exact_mod_cast hd
    constructor <;> nlinarith
  by_cases hdr : d ≤ r
  · simp only [hd, if_false, hdr, ite_true, Accuracy.roundToNearestEven]
    have hd' : (d : ℝ) ≤ r := by exact_mod_cast hdr
    rw [abs_le]
    constructor <;> nlinarith
  · simp only [hd, hdr, if_false, Accuracy.roundToNearestEven, Nat.cast_add, Nat.cast_one]
    have hd' : (r : ℝ) + 1 ≤ d := by exact_mod_cast (show r + 1 ≤ d by omega)
    rw [abs_le]
    constructor <;> nlinarith

private lemma positive_error (x : Float.Model) (m : Nat) (e : Int) (hm : 0 < m)
    (hu : x.unpack = .finite .positive m e hm)
    : ∃ q : ℝ,
        Flare.Binary64.Value.modelToReal x.sqrt = some q
        ∧ |q - Real.sqrt ((m : ℝ) * (2 : ℝ)^e)|
          ≤ (2 : ℝ)^(-53 : Int) * Real.sqrt ((m : ℝ) * (2 : ℝ)^e) := by
  obtain ⟨hmb, he, he', _⟩ := unpack_finite_shape x .positive m e hm hu
  let t := ((m.log2 : Int) + e + 2) / 2 - 53
  let shifted := m <<< (e - 2 * t).toNat
  let root := Nat.sqrt shifted
  obtain ⟨ht, ht', hshift, hrootlog, hcore⟩ := core_shape m e hm hmb he he'
  have hroot : 0 < root := by
    apply Nat.sqrt_pos.mpr
    exact Nat.shiftLeft_pos_iff.mpr hm
  have hrange := (Nat.log2_eq_iff (Nat.ne_of_gt hroot)).mp hrootlog
  have hδ : 0 < (2 : ℝ)^t := zpow_pos (by norm_num) _
  have hx : 0 ≤ (m : ℝ) * (2 : ℝ)^e :=
    mul_nonneg (Nat.cast_nonneg m) (zpow_pos (by norm_num) _).le
  have hscaled : (shifted : ℝ) * ((2 : ℝ)^t)^2 = (m : ℝ) * (2 : ℝ)^e := by
    have h := decrease_preserves_value m (e - 2 * t).toNat e
    have hcast := congrArg (fun q : Rat => (q : ℝ)) h
    have heq : e - ((e - 2 * t).toNat : Int) = 2 * t := by omega
    simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_zpow, Rat.cast_ofNat, heq] at hcast
    have hpow : (2 : ℝ)^(2 * t) = ((2 : ℝ)^t)^2 := by
      rw [mul_comm (2 : Int) t, zpow_mul, zpow_ofNat]
    simpa only [hpow] using hcast
  have hfloor : (root : ℝ) * (2 : ℝ)^t ≤ Real.sqrt ((m : ℝ) * (2 : ℝ)^e) ∧
      Real.sqrt ((m : ℝ) * (2 : ℝ)^e) ≤ ((root : ℝ) + 1) * (2 : ℝ)^t := by
    have hl : (root : ℝ)^2 ≤ (shifted : ℝ) := by exact_mod_cast Nat.sqrt_le' shifted
    have hh : (shifted : ℝ) < ((root : ℝ) + 1)^2 := by
      exact_mod_cast Nat.lt_succ_sqrt' shifted
    have hlo := mul_le_mul_of_nonneg_right hl (sq_nonneg ((2 : ℝ)^t))
    have hhi := mul_lt_mul_of_pos_right hh (sq_pos_of_pos hδ)
    rw [hscaled] at hlo hhi
    have hsq := Real.sq_sqrt hx
    have hnonneg := Real.sqrt_nonneg ((m : ℝ) * (2 : ℝ)^e)
    constructor <;> nlinarith [mul_nonneg (Nat.cast_nonneg root) hδ.le]
  let acc := if shifted - root * root = 0 then Accuracy.exact
    else Accuracy.inexact (if shifted - root * root ≤ root then .lt else .gt)
  have hq := Flare.Binary64.Rounding.round_canonical_value .positive root t acc hrootlog (by omega)
    (by omega)
  refine ⟨(acc.roundToNearestEven root : ℝ) * (2 : ℝ)^t, ?_, ?_⟩
  · rw [interpretation_eq]
    change Flare.Binary64.Model.Value.toReal
      (Float.Model.pack (UnpackedFloat.sqrt Format.binary64 x.unpack)) = _
    rw [hu]
    simp only [UnpackedFloat.sqrt, hcore]
    change Flare.Binary64.Model.Value.toReal
      (Float.Model.pack (roundWithAccuracy Format.binary64 .positive root t acc)) = _
    simp [Flare.Binary64.Model.Value.toReal, hq, Sign.apply]
  · have hscaledRoot : Real.sqrt (shifted : ℝ) * (2 : ℝ)^t = Real.sqrt ((m : ℝ) * (2 : ℝ)^e) := by
      have hs1 := Real.sq_sqrt (Nat.cast_nonneg shifted)
      have hs2 := Real.sq_sqrt hx
      have hnonneg := mul_nonneg (Real.sqrt_nonneg (shifted : ℝ)) hδ.le
      nlinarith [Real.sqrt_nonneg ((m : ℝ) * (2 : ℝ)^e)]
    have herr := integer_root_rounding shifted
    change |(acc.roundToNearestEven root : ℝ) - Real.sqrt (shifted : ℝ)| ≤ 1 / 2 at herr
    have herror : |(acc.roundToNearestEven root : ℝ) * (2 : ℝ)^t -
        Real.sqrt ((m : ℝ) * (2 : ℝ)^e)| ≤ (1 / 2) * (2 : ℝ)^t := by
      rw [← hscaledRoot, ← sub_mul, abs_mul, abs_of_pos hδ]
      exact mul_le_mul_of_nonneg_right herr hδ.le
    have hrlo : (2^52 : ℝ) ≤ (root : ℝ) := by exact_mod_cast hrange.1
    have hrootlo := mul_le_mul_of_nonneg_right hrlo hδ.le
    apply herror.trans
    calc
      (1 / 2 : ℝ) * (2 : ℝ)^t = (2 : ℝ)^(-53 : Int) * ((2^52 : ℝ) * (2 : ℝ)^t) := by norm_num; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hrootlo.trans hfloor.1) (by positivity)

/-- Native square root is rounded within half a spacing unit, yielding the
standard binary64 `2⁻⁵³` relative bound. The proof follows integer-root rounding,
including its carry case, signed zero and positive subnormal inputs. -/
theorem sqrt_error_nearest (x : Float) (hx : x.isFinite = true) (hn : 0 ≤ value x)
    : x.sqrt.isFinite = true
      ∧ |value x.sqrt - Real.sqrt (value x)| ≤ (2 : ℝ)^(-53 : Int) * Real.sqrt (value x) := by
  change x.toModel.unpack.isFinite = true at hx
  cases hu : x.toModel.unpack with
  | notANumber => simp [hu, UnpackedFloat.isFinite] at hx
  | infinity s => simp [hu, UnpackedFloat.isFinite] at hx
  | zero s =>
      have hv : value x = 0 := by simp [value, Flare.Binary64.Value.modelToReal, hu]
      have hq : Flare.Binary64.Value.modelToReal x.sqrt.toModel = some 0 := by
        change Flare.Binary64.Value.modelToReal
          (Float.Model.pack (UnpackedFloat.sqrt Format.binary64 x.toModel.unpack)) = _
        rw [hu]
        cases s <;> rfl
      exact ⟨finite_of_value _ _ hq, by rw [hv]; simp [value, hq]⟩
  | finite s m e hm =>
      cases s with
      | negative =>
          have hv : value x = -((m : ℝ) * (2 : ℝ)^e) := by
            simp [value, Flare.Binary64.Value.modelToReal, hu, Sign.apply]
          rw [hv] at hn
          have hp : 0 < (m : ℝ) * (2 : ℝ)^e :=
            mul_pos (Nat.cast_pos.mpr hm) (zpow_pos (by norm_num) _)
          linarith
      | positive =>
          obtain ⟨q, hq, herr⟩ := positive_error x.toModel m e hm hu
          have hv : value x = (m : ℝ) * (2 : ℝ)^e := by
            simp [value, Flare.Binary64.Value.modelToReal, hu, Sign.apply]
          have hq' : Flare.Binary64.Value.modelToReal x.sqrt.toModel = some q := hq
          exact ⟨
            finite_of_value _ _ hq',
            by rw [hv]; simpa only [value, hq', Option.getD_some] using herr
          ⟩

/-- A finite nonnegative native binary64 has a finite square root with relative
error at most 2⁻⁵⁰. This convenient allowance follows from the sharper nearest
rounding theorem and includes signed zero and positive subnormal inputs. -/
theorem sqrt_error (x : Float) (hx : x.isFinite = true) (hn : 0 ≤ value x)
    : x.sqrt.isFinite = true
      ∧ |value x.sqrt - Real.sqrt (value x)| ≤ (2 : ℝ)^(-50 : Int) * Real.sqrt (value x) := by
  have h := sqrt_error_nearest x hx hn
  exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _))⟩

end Flare.Binary64.Sqrt
