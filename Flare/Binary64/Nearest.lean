import Flare.Binary64.Rounding
import Flare.Binary64.Division

/-! Unit-roundoff bounds for actual native binary64 arithmetic. The model's
round/sticky-bit semantics are proved in Flare.Binary64.Rounding; the operation case
analysis is shared with the existing absolute-error proofs. -/

namespace Flare.Binary64.Nearest
open Float.Model Float.Model.UnpackedFloat
open Flare.Binary64.Value Flare.Binary64.Arithmetic
open Flare.Binary64.Rounding

/-- Nearest rounding of the actual model addition, including cancellation. -/
theorem model_add_nearest (a b : Float.Model) (x y : Rat)
    (ha : Flare.Binary64.Model.Value.toRational a = some x)
    (hb : Flare.Binary64.Model.Value.toRational b = some y)
    (hbound : |x + y| ≤ (2 : Rat)^(1000 : Int))
    : ∃ q,
        Flare.Binary64.Model.Value.toRational (a + b) = some q
        ∧ |q - (x + y)| ≤ (2 : Rat)^(-53 : Int) * (|x + y| + (2 : Rat)^(-1022 : Int)) := by
  apply Flare.Binary64.Model.Arithmetic.add_error_of_normalize a b x y _ ha hb
    (mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (by norm_num)))
  intro m e hvalue
  obtain ⟨q, hq, herr⟩ := normalize_relative_nearest m e .positive (by rw [hvalue]; exact hbound)
  exact ⟨q, hq, by simpa only [hvalue] using herr⟩

/-- Nearest rounding of the actual model subtraction, including signed zero. -/
theorem model_sub_nearest (a b : Float.Model) (x y : Rat)
    (ha : Flare.Binary64.Model.Value.toRational a = some x)
    (hb : Flare.Binary64.Model.Value.toRational b = some y)
    (hbound : |x - y| ≤ (2 : Rat)^(1000 : Int))
    : ∃ q,
        Flare.Binary64.Model.Value.toRational (a - b) = some q
        ∧ |q - (x - y)| ≤ (2 : Rat)^(-53 : Int) * (|x - y| + (2 : Rat)^(-1022 : Int)) := by
  apply Flare.Binary64.Model.Arithmetic.sub_error_of_normalize a b x y _ ha hb
    (mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (by norm_num)))
  intro m e hvalue
  obtain ⟨q, hq, herr⟩ := normalize_relative_nearest m e .positive (by rw [hvalue]; exact hbound)
  exact ⟨q, hq, by simpa only [hvalue] using herr⟩

/-- Nearest rounding of the actual model multiplication, including underflow. -/
theorem model_mul_nearest (a b : Float.Model) (x y : Rat)
    (ha : Flare.Binary64.Model.Value.toRational a = some x)
    (hb : Flare.Binary64.Model.Value.toRational b = some y)
    (hbound : |x * y| ≤ (2 : Rat)^(1000 : Int))
    : ∃ q,
        Flare.Binary64.Model.Value.toRational (a * b) = some q
        ∧ |q - x * y| ≤ (2 : Rat)^(-53 : Int) * (|x * y| + (2 : Rat)^(-1022 : Int)) := by
  apply Flare.Binary64.Model.Arithmetic.mul_error_of_round a b x y _ ha hb
    (mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (by norm_num)))
  intro s m e _ hc hvalue
  have hs : (s.apply 1 : Rat) * (m : Rat) = (s.apply (m : Int) : Rat) := by
    cases s <;> simp [Sign.apply]
  have habs : |x * y| = (m : Rat) * (2 : Rat)^e := by
    rw [← hvalue]
    have hp := (zpow_pos (by norm_num : (0 : Rat) < 2) e).le
    cases s <;> simp [Sign.apply, abs_mul, abs_of_nonneg hp]
  obtain ⟨q, hq, herr⟩ := roundWithAccuracy_relative_nearest s m e .exact (m : Rat) hc rfl
    (by rw [← habs]; exact hbound)
  rw [hs, hvalue, ← habs] at herr
  exact ⟨q, hq, herr⟩

private lemma native_rational (a : Float) (ha : a.isFinite = true)
    : ∃ x : Rat, Flare.Binary64.Model.Value.toRational a.toModel = some x ∧ (x : ℝ) = value a := by
  apply Flare.Binary64.Model.Arithmetic.rational_of_real
  rw [← interpretation_eq]
  exact finite_value a ha

private lemma native_bound (r : Float) (target ε : ℝ)
    (h
      : ∃ q : Rat,
          Flare.Binary64.Model.Value.toRational r.toModel = some q ∧ |(q : ℝ) - target| ≤ ε)
    : r.isFinite = true ∧ |value r - target| ≤ ε := by
  obtain ⟨q, hq, herr⟩ := h
  have he : Flare.Binary64.Value.modelToReal r.toModel = some (q : ℝ) := by
    rw [interpretation_eq]
    simp [Flare.Binary64.Model.Value.toReal, hq]
  exact ⟨finite_of_value r _ he, by simpa only [value, he, Option.getD_some] using herr⟩

/-- Actual native addition has error at most u times result magnitude plus the
normal-underflow allowance, with u = 2⁻⁵³. -/
theorem add_error_nearest (a b : Float) (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hbound : |value a + value b| ≤ (2 : ℝ)^(1000 : Int))
    : (a + b).isFinite = true
      ∧ |value (a + b) - (value a + value b)|
        ≤ (2 : ℝ)^(-53 : Int) * (|value a + value b| + (2 : ℝ)^(-1022 : Int)) := by
  obtain ⟨x, hx, hxr⟩ := native_rational a ha
  obtain ⟨y, hy, hyr⟩ := native_rational b hb
  have hxy : |x + y| ≤ (2 : Rat)^(1000 : Int) := by
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_abs, Rat.cast_add, Rat.cast_zpow, Rat.cast_ofNat, hxr, hyr] using hbound
  obtain ⟨q, hq, herr⟩ := model_add_nearest a.toModel b.toModel x y hx hy hxy
  apply native_bound
  refine ⟨q, hq, ?_⟩
  have hh := (Rat.cast_le (K := ℝ)).mpr herr
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_zpow,
    Rat.cast_ofNat, hxr, hyr]
    using hh

/-- Actual native subtraction has the unit-roundoff bound, even on cancellation. -/
theorem sub_error_nearest (a b : Float) (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hbound : |value a - value b| ≤ (2 : ℝ)^(1000 : Int))
    : (a - b).isFinite = true
      ∧ |value (a - b) - (value a - value b)|
        ≤ (2 : ℝ)^(-53 : Int) * (|value a - value b| + (2 : ℝ)^(-1022 : Int)) := by
  obtain ⟨x, hx, hxr⟩ := native_rational a ha
  obtain ⟨y, hy, hyr⟩ := native_rational b hb
  have hxy : |x - y| ≤ (2 : Rat)^(1000 : Int) := by
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_zpow, Rat.cast_ofNat, hxr, hyr] using hbound
  obtain ⟨q, hq, herr⟩ := model_sub_nearest a.toModel b.toModel x y hx hy hxy
  apply native_bound
  refine ⟨q, hq, ?_⟩
  have hh := (Rat.cast_le (K := ℝ)).mpr herr
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_zpow,
    Rat.cast_ofNat, hxr, hyr]
    using hh

/-- Actual native multiplication has the unit-roundoff bound, including subnormal
inputs and results. No mathematical rounding law is an assumption. -/
theorem mul_error_nearest (a b : Float) (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hbound : |value a * value b| ≤ (2 : ℝ)^(1000 : Int))
    : (a * b).isFinite = true
      ∧ |value (a * b) - value a * value b|
        ≤ (2 : ℝ)^(-53 : Int) * (|value a * value b| + (2 : ℝ)^(-1022 : Int)) := by
  obtain ⟨x, hx, hxr⟩ := native_rational a ha
  obtain ⟨y, hy, hyr⟩ := native_rational b hb
  have hxy : |x * y| ≤ (2 : Rat)^(1000 : Int) := by
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_abs, Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat, hxr, hyr] using hbound
  obtain ⟨q, hq, herr⟩ := model_mul_nearest a.toModel b.toModel x y hx hy hxy
  apply native_bound
  refine ⟨q, hq, ?_⟩
  have hh := (Rat.cast_le (K := ℝ)).mpr herr
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_zpow,
    Rat.cast_ofNat, hxr, hyr]
    using hh

/-- The quotient-core accuracy flag represents the exact rational quotient,
including the discarded integer remainder. -/
theorem quotient_rep (num den : Nat) (hd : 0 < den)
    : MantissaRep
        (ExtendedMantissa.ofMantissaAndAccuracy (num / den) (accuracyOfFraction (num % den) den))
        ((num : Rat) / (den : Rat)) := by
  have hdR : (0 : Rat) < den := by exact_mod_cast hd
  have hr : ((num % den : Nat) : Rat) < den := by exact_mod_cast Nat.mod_lt num hd
  have hid : (num : Rat) = (num / den : Nat) * (den : Rat) + (num % den : Nat) := by
    exact_mod_cast (Nat.div_add_mod' num den).symm
  have hvalue : (num : Rat) / (den : Rat) = (num / den : Nat) + (num % den : Nat) / (den : Rat) :=
    by
    apply (div_eq_iff hdR.ne').mpr
    rw [add_mul, div_mul_cancel₀ _ hdR.ne']
    exact hid
  have hr1 : ((num % den : Nat) : Rat) / den < 1 := (div_lt_one hdR).mpr hr
  by_cases hz : num % den = 0
  · simp only [accuracyOfFraction, hz, ↓reduceIte, ExtendedMantissa.ofMantissaAndAccuracy,
    MantissaRep]
    simpa only [hz, Nat.cast_zero, zero_div, add_zero] using hvalue
  · have hr0 : (0 : Rat) < (num % den : Nat) := by exact_mod_cast (Nat.pos_of_ne_zero hz)
    have hfrac0 := div_pos hr0 hdR
    simp only [accuracyOfFraction, hz, ↓reduceIte]
    rcases lt_trichotomy (2 * (num % den)) den with hlt | heq | hgt
    · rw [Nat.compare_eq_lt.mpr hlt]
      change (num / den : Nat) < (num : Rat) / den ∧ (num : Rat) / den < (num / den : Nat) + 1 / 2
      have hh : (2 : Rat) * (num % den : Nat) < den := by exact_mod_cast hlt
      have hhalf : ((num % den : Nat) : Rat) / den < 1 / 2 :=
        (div_lt_iff₀ hdR).mpr (by linarith only [hh])
      constructor <;> linarith only [hvalue, hfrac0, hhalf]
    · rw [Nat.compare_eq_eq.mpr heq]
      change (num : Rat) / den = (num / den : Nat) + 1 / 2
      have hh : (2 : Rat) * (num % den : Nat) = den := by exact_mod_cast heq
      have hhalf : ((num % den : Nat) : Rat) / den = 1 / 2 :=
        (div_eq_iff hdR.ne').mpr (by linarith only [hh])
      rw [hvalue, hhalf]
    · rw [Nat.compare_eq_gt.mpr hgt]
      change (num / den : Nat) + (1 / 2 : Rat) < (num : Rat) / den ∧
        (num : Rat) / den < (num / den : Nat) + 1
      have hh : (den : Rat) < 2 * (num % den : Nat) := by exact_mod_cast hgt
      have hhalf : (1 / 2 : Rat) < (num % den : Nat) / (den : Rat) :=
        (lt_div_iff₀ hdR).mpr (by linarith only [hh])
      constructor <;> linarith only [hvalue, hr1, hhalf]

/-- The actual quotient core and its rounding carry the full fractional tail
into nearest rounding, so no additional truncation error is charged. -/
theorem finite_div_nearest (s : Sign) (m n : Nat) (e f : Int) (hm : 0 < m) (hn : 0 < n)
    (hbound : (m : Rat) * (2 : Rat)^e / ((n : Rat) * (2 : Rat)^f) ≤ (2 : Rat)^(1000 : Int))
    : ∃ q,
        Flare.Binary64.Model.Value.toRational
            (Float.Model.pack
              (let (p, t, acc) := divCore Format.binary64 m e n f;
                roundWithAccuracy Format.binary64 s p t acc))
          = some q
        ∧ |q - (s.apply (m : Int) : Rat) * (2 : Rat)^e / ((n : Rat) * (2 : Rat)^f)|
          ≤ (2 : Rat)^(-53 : Int)
            * ((m : Rat) * (2 : Rat)^e / ((n : Rat) * (2 : Rat)^f) + (2 : Rat)^(-1022 : Int)) := by
  let t := min (e - f) (max ((m.log2 : Int) - n.log2 + e - f - 53) (-1074))
  let shifted := m <<< (e - f - t).toNat
  let p := shifted / n
  let acc := accuracyOfFraction (shifted % n) n
  have hc := (Flare.Binary64.Division.quotient_core_bounds m n e f 1000 hm hn (by norm_num)
    hbound).2.1
  change 52 ≤ p.log2 ∨ t ≤ -1074 at hc
  have hcore : divCore Format.binary64 m e n f = (p, t, acc) := by
    have heq : Format.binary64.targetExponent (totalExponent m e - totalExponent n f) =
        max ((m.log2 : Int) - n.log2 + e - f - 53) (-1074) := by
      simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
      apply congrArg (fun z : Int => max z (-1074))
      omega
    simp only [divCore, heq]
    rfl
  have hscale : ((shifted : Rat) / (n : Rat)) * (2 : Rat)^t =
      (m : Rat) * (2 : Rat)^e / ((n : Rat) * (2 : Rat)^f) := by
    have h := Flare.Binary64.Model.Rounding.decrease_preserves_value m (e - f - t).toNat (e - f)
    have ht : e - f - ((e - f - t).toNat : Int) = t := by dsimp only [t]; omega
    rw [ht, zpow_sub₀ (by norm_num : (2 : Rat) ≠ 0)] at h
    change (shifted : Rat) * (2 : Rat)^t = _ at h
    calc
      _ = ((shifted : Rat) * (2 : Rat)^t) / n := by ring
      _ = _ := by rw [h]; ring
  obtain ⟨q, hq, herr⟩ := roundWithAccuracy_relative_nearest s p t acc ((shifted : Rat) / n)
    hc (quotient_rep shifted n hn) (by rw [hscale]; exact hbound)
  refine ⟨q, by rw [hcore]; exact hq, ?_⟩
  have hsign : (s.apply 1 : Rat) * ((shifted : Rat) / n) * (2 : Rat)^t =
      (s.apply (m : Int) : Rat) * (2 : Rat)^e / ((n : Rat) * (2 : Rat)^f) := by
    rw [mul_assoc, hscale]
    cases s <;> simp [Sign.apply, mul_div_assoc, neg_div, neg_mul]
  rw [hsign, hscale] at herr
  exact herr

/-- Nearest rounding of model division for either sign and any finite nonzero denominator. -/
theorem model_div_nearest (a b : Float.Model) (x y : Rat)
    (ha : Flare.Binary64.Model.Value.toRational a = some x)
    (hb : Flare.Binary64.Model.Value.toRational b = some y) (hy : y ≠ 0)
    (hbound : |x / y| ≤ (2 : Rat)^(1000 : Int))
    : ∃ q,
        Flare.Binary64.Model.Value.toRational (a / b) = some q
        ∧ |q - x / y| ≤ (2 : Rat)^(-53 : Int) * (|x / y| + (2 : Rat)^(-1022 : Int)) := by
  apply Flare.Binary64.Division.model_div_error_of_core a b x y _ ha hb hy
    (mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (by norm_num)))
  intro s m n e f hm hn heq
  have hmag : (m : Rat) * (2 : Rat)^e / ((n : Rat) * (2 : Rat)^f) = |x / y| := by
    rw [← heq]
    cases s <;> simp [Sign.apply, abs_div, abs_mul,
      abs_of_pos (zpow_pos (by norm_num : (0 : Rat) < 2) _)]
  obtain ⟨q, hq, herr⟩ := finite_div_nearest s m n e f hm hn (by rw [hmag]; exact hbound)
  exact ⟨q, hq, by rwa [heq, hmag] at herr⟩

/-- Actual native division has the unit-roundoff bound, including quotient
underflow and signed zero. The finite denominator's real value must be nonzero. -/
theorem div_error_nearest (a b : Float) (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hb0 : value b ≠ 0) (hbound : |value a / value b| ≤ (2 : ℝ)^(1000 : Int))
    : (a / b).isFinite = true
      ∧ |value (a / b) - value a / value b|
        ≤ (2 : ℝ)^(-53 : Int) * (|value a / value b| + (2 : ℝ)^(-1022 : Int)) := by
  obtain ⟨x, hx, hxr⟩ := native_rational a ha
  obtain ⟨y, hy, hyr⟩ := native_rational b hb
  have hy0 : y ≠ 0 := by intro h; apply hb0; rw [← hyr, h]; norm_num
  have hxy : |x / y| ≤ (2 : Rat)^(1000 : Int) := by
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_zpow, Rat.cast_ofNat, hxr, hyr] using hbound
  obtain ⟨q, hq, herr⟩ := model_div_nearest a.toModel b.toModel x y hx hy hy0 hxy
  apply native_bound
  refine ⟨q, hq, ?_⟩
  have hh := (Rat.cast_le (K := ℝ)).mpr herr
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_zpow,
    Rat.cast_ofNat, hxr, hyr]
    using hh

end Flare.Binary64.Nearest
