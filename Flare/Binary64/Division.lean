import Flare.Binary64.Arithmetic

/-! Native binary64 division, derived from the model's integer quotient and
rounding operations. The absolute bound includes quotient truncation, signed
zeros and underflow, without requiring normal operands or a normal result. -/

open Flare.Analysis.Dyadic

namespace Flare.Binary64.Division
open Float.Model Float.Model.UnpackedFloat
open Flare.Binary64.Value Flare.Binary64.Arithmetic
open Flare.Binary64.Model.Rounding

lemma quotient_core_bounds (m n : Nat) (e f N : Int)
    (hm : 0 < m) (hn : 0 < n) (hN : -1022 ≤ N)
    (hv : (m : Rat) * (2 : Rat) ^ e / ((n : Rat) * (2 : Rat) ^ f) ≤ (2 : Rat) ^ N)
    : (let t := min (e - f) (max ((m.log2 : Int) - n.log2 + e - f - 53) (-1074));
        let shifted := m <<< (e - f - t).toNat;
        let p := shifted / n;
        t ≤ N - 52
        ∧ (52 ≤ p.log2 ∨ t ≤ -1074)
        ∧ (p : Rat) * (2 : Rat) ^ t ≤ (m : Rat) * (2 : Rat) ^ e / ((n : Rat) * (2 : Rat) ^ f)
        ∧ (m : Rat) * (2 : Rat) ^ e / ((n : Rat) * (2 : Rat) ^ f)
          ≤ ((p : Rat) + 1) * (2 : Rat) ^ t) := by
  dsimp only
  let t := min (e - f) (max ((m.log2 : Int) - n.log2 + e - f - 53) (-1074))
  let shifted := m <<< (e - f - t).toNat
  let p := shifted / n
  have hz : (2 : Rat) ≠ 0 := by norm_num
  have hp (k : Int) : 0 < (2 : Rat)^k := zpow_pos (by norm_num) _
  have hnR : (0 : Rat) < n := Nat.cast_pos.mpr hn
  have hlo : (2 : Rat)^m.log2 ≤ m := by exact_mod_cast Nat.log2_self_le (Nat.ne_of_gt hm)
  have hhi : (n : Rat) < (2 : Rat)^(n.log2 + 1) := by exact_mod_cast Nat.lt_log2_self (n := n)
  have hlogbound : (m.log2 : Int) - n.log2 + e - f ≤ N := by
    have hnum : 0 < (2 : Rat)^m.log2 * (2 : Rat)^e := mul_pos (by positivity) (hp e)
    have hd := mul_lt_mul_of_pos_right hhi (hp f)
    have hl := div_lt_div_of_pos_left hnum (mul_pos hnR (hp f)) hd
    have hu := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlo (hp e).le)
      (mul_pos hnR (hp f)).le
    have h := lt_of_lt_of_le hl (hu.trans hv)
    have heq : (2 : Rat)^m.log2 * (2 : Rat)^e /
        ((2 : Rat)^(n.log2 + 1) * (2 : Rat)^f) =
        (2 : Rat)^((m.log2 : Int) - n.log2 + e - f - 1) := by
      rw [← zpow_natCast (2 : Rat) m.log2, ← zpow_natCast (2 : Rat) (n.log2 + 1),
        ← zpow_add₀ hz, ← zpow_add₀ hz, ← zpow_sub₀ hz]
      congr 1
      push_cast
      ring
    rw [heq] at h
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : Rat) < 2)).mp h
    omega
  have ht : t ≤ N - 52 := by dsimp [t]; omega
  have hshift : 0 ≤ e - f - t := by dsimp [t]; omega
  have hcanonical : 52 ≤ p.log2 ∨ t ≤ -1074 := by
    by_cases htlow : t ≤ -1074
    · exact Or.inr htlow
    have ht' : t ≤ (m.log2 : Int) - n.log2 + e - f - 53 := by dsimp [t] at *; omega
    have hlog : shifted.log2 = m.log2 + (e - f - t).toNat :=
      Flare.Binary64.Model.Conversion.log2_shift m _ hm
    have hsp : 0 < shifted := Nat.shiftLeft_pos_iff.mpr hm
    have hlarge : 2^(n.log2 + 53) ≤ shifted :=
      (Nat.le_log2 (Nat.ne_of_gt hsp)).mp (by omega)
    have hnsmall : n ≤ 2^(n.log2 + 1) := Nat.lt_log2_self.le
    have hplow : 2^52 ≤ p := by
      apply (Nat.le_div_iff_mul_le hn).mpr
      have h := Nat.mul_le_mul_left (2^52) hnsmall
      have heq : 2^52 * 2^(n.log2 + 1) = 2^(n.log2 + 53) := by
        rw [← pow_add]
        congr 1
        omega
      rw [heq] at h
      exact h.trans hlarge
    exact Or.inl ((Nat.le_log2 (by omega : p ≠ 0)).mpr hplow)
  have hexact : (shifted : Rat) * (2 : Rat)^t / (n : Rat) =
      (m : Rat) * (2 : Rat)^e / ((n : Rat) * (2 : Rat)^f) := by
    have hd := decrease_preserves_value m (e - f - t).toNat (e - f)
    have heq : e - f - ((e - f - t).toNat : Int) = t := by omega
    rw [heq, zpow_sub₀ hz] at hd
    rw [hd]
    ring
  have hlow : (p : Rat) * n ≤ (shifted : Rat) := by exact_mod_cast Nat.div_mul_le_self shifted n
  have hhigh : (shifted : Rat) ≤ ((p : Rat) + 1) * n := by
    have h : shifted < (p + 1) * n := by
      simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ shifted hn
    exact_mod_cast h.le
  refine ⟨ht, hcanonical, ?_, ?_⟩
  · rw [← hexact]
    apply (le_div_iff₀ hnR).mpr
    simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_right hlow (hp t).le
  · rw [← hexact]
    apply (div_le_iff₀ hnR).mpr
    simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_right hhigh (hp t).le

private lemma finite_div_error (s : Sign) (m n : Nat) (e f N : Int)
    (hm : 0 < m) (hn : 0 < n) (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hv : (m : Rat) * (2 : Rat) ^ e / ((n : Rat) * (2 : Rat) ^ f) ≤ (2 : Rat) ^ N)
    : ∃ q,
        Flare.Binary64.Model.Value.toRational
            (Float.Model.pack
              (let (p, t, a) := divCore Format.binary64 m e n f;
                roundWithAccuracy Format.binary64 s p t a))
          = some q
        ∧ |q - (s.apply (m : Int) : Rat) * (2 : Rat) ^ e / ((n : Rat) * (2 : Rat) ^ f)|
          ≤ (2 : Rat) ^ (N - 51) := by
  let t := min (e - f) (max ((m.log2 : Int) - n.log2 + e - f - 53) (-1074))
  let shifted := m <<< (e - f - t).toNat
  let p := shifted / n
  let acc := accuracyOfFraction (shifted % n) n
  obtain ⟨ht, hc, hlo, hhi⟩ := quotient_core_bounds m n e f N hm hn hN hv
  change t ≤ N - 52 at ht
  change 52 ≤ p.log2 ∨ t ≤ -1074 at hc
  change (p : Rat) * (2 : Rat)^t ≤ _ at hlo
  change _ ≤ ((p : Rat) + 1) * (2 : Rat)^t at hhi
  have hround : ∃ q, Flare.Binary64.Model.Value.toRational
      (Float.Model.pack (roundWithAccuracy Format.binary64 s p t acc)) = some q ∧
      |q - (s.apply (p : Int) : Rat) * (2 : Rat)^t| ≤ (2 : Rat)^(N - 52) := by
    by_cases hp : p = 0
    · have he : t ≤ -1074 := by simp only [hp, Nat.log2_zero] at hc; omega
      obtain ⟨q, hq, he⟩ := round_zero_with_accuracy_error s t N acc he hN
      refine ⟨q, by simpa only [hp] using hq, ?_⟩
      cases s <;> simpa only [hp, Nat.cast_zero, Sign.apply, Int.cast_zero, neg_zero,
        zero_mul, sub_zero] using he
    · exact round_with_accuracy_error s p t N acc (Nat.pos_of_ne_zero hp) hc hN hN' (hlo.trans hv)
  obtain ⟨q, hq, herr⟩ := hround
  have hcore : divCore Format.binary64 m e n f = (p, t, acc) := by
    have heq : Format.binary64.targetExponent (totalExponent m e - totalExponent n f) =
        max ((m.log2 : Int) - n.log2 + e - f - 53) (-1074) := by
      simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
      congr 1
      omega
    simp only [divCore, heq]
    rfl
  refine ⟨q, by rw [hcore]; exact hq, ?_⟩
  have hrem : |(p : Rat) * (2 : Rat)^t -
      (m : Rat) * (2 : Rat)^e / ((n : Rat) * (2 : Rat)^f)| ≤ (2 : Rat)^t := by
    rw [abs_of_nonpos (by linarith only [hlo])]
    nlinarith only [hhi]
  have hrem' : |(s.apply (p : Int) : Rat) * (2 : Rat)^t -
      (s.apply (m : Int) : Rat) * (2 : Rat)^e / ((n : Rat) * (2 : Rat)^f)| ≤ (2 : Rat)^t := by
    cases s <;> simpa only [Sign.apply, Int.cast_neg, Int.cast_natCast, neg_mul,
      neg_div, neg_sub_neg, abs_sub_comm] using hrem
  have htri := abs_sub_le q ((s.apply (p : Int) : Rat) * (2 : Rat)^t)
    ((s.apply (m : Int) : Rat) * (2 : Rat)^e / ((n : Rat) * (2 : Rat)^f))
  have he := zpow_le_zpow_right₀ (by norm_num : (1 : Rat) ≤ 2) ht
  have hp : (2 : Rat)^(N - 51) = 2 * (2 : Rat)^(N - 52) := by
    rw [show N - 51 = N - 52 + 1 by omega, zpow_add₀ (by norm_num : (2 : Rat) ≠ 0), zpow_one]
    ring
  rw [hp]
  linarith only [htri, herr, hrem', he]

/-- Shared model-division case analysis. A proved quotient-core allowance
supplies the finite branch; signs and zero operands are handled exactly. -/
theorem model_div_error_of_core (a b : Float.Model) (av bv ε : Rat)
    (ha : Flare.Binary64.Model.Value.toRational a = some av)
    (hb : Flare.Binary64.Model.Value.toRational b = some bv)
    (hbv : bv ≠ 0) (hpos : 0 ≤ ε)
    (hcore
      : ∀ (s : Sign) (m n : Nat) (e f : Int),
          0 < m
          → 0 < n
          → (s.apply (m : Int) : Rat) * (2 : Rat) ^ e / ((n : Rat) * (2 : Rat) ^ f) = av / bv
          → ∃ q,
              Flare.Binary64.Model.Value.toRational
                  (Float.Model.pack
                    (let (p, t, acc) := divCore Format.binary64 m e n f;
                      roundWithAccuracy Format.binary64 s p t acc))
                = some q
              ∧ |q - av / bv| ≤ ε)
    : ∃ q, Flare.Binary64.Model.Value.toRational (a / b) = some q ∧ |q - av / bv| ≤ ε := by
  unfold Flare.Binary64.Model.Value.toRational at ha hb
  cases hu : b.unpack with
  | notANumber => simp [hu, Flare.Binary64.Model.Value.unpackedToRational] at hb
  | infinity s => simp [hu, Flare.Binary64.Model.Value.unpackedToRational] at hb
  | zero s =>
      simp [hu, Flare.Binary64.Model.Value.unpackedToRational] at hb; exact (hbv hb.symm).elim
  | finite sb n f hn =>
      have hbval : bv = (sb.apply (n : Int) : Rat) * (2 : Rat)^f := by
        simpa only [hu, Flare.Binary64.Model.Value.unpackedToRational, Option.some.injEq]
          using hb.symm
      cases hu' : a.unpack with
      | notANumber => simp [hu', Flare.Binary64.Model.Value.unpackedToRational] at ha
      | infinity s => simp [hu', Flare.Binary64.Model.Value.unpackedToRational] at ha
      | zero sa =>
          have hav : av = 0 := by
            simpa only [hu', Flare.Binary64.Model.Value.unpackedToRational, Option.some.injEq]
              using ha.symm
          refine ⟨0, ?_, ?_⟩
          · change Flare.Binary64.Model.Value.toRational
              (Float.Model.pack (UnpackedFloat.div Format.binary64 a.unpack b.unpack)) = _
            rw [hu', hu]
            simp only [UnpackedFloat.div]
            cases sa / sb <;> rfl
          · simp only [hav, zero_div, sub_self, abs_zero]
            exact hpos
      | finite sa m e hm =>
          have haval : av = (sa.apply (m : Int) : Rat) * (2 : Rat)^e := by
            simpa only [hu', Flare.Binary64.Model.Value.unpackedToRational, Option.some.injEq]
              using ha.symm
          have heq : ((sa / sb).apply (m : Int) : Rat) * (2 : Rat)^e /
              ((n : Rat) * (2 : Rat)^f) = av / bv := by
            rw [haval, hbval]
            cases sa <;> cases sb
            · rw [show (Sign.negative / Sign.negative) = Sign.positive from rfl]
              simp [Sign.apply, neg_mul, neg_div, div_neg]
            · rw [show (Sign.negative / Sign.positive) = Sign.negative from rfl]
              simp [Sign.apply, neg_mul, neg_div]
            · rw [show (Sign.positive / Sign.negative) = Sign.negative from rfl]
              simp [Sign.apply, neg_mul, neg_div, div_neg]
            · rw [show (Sign.positive / Sign.positive) = Sign.positive from rfl]
              simp only [Sign.apply, Int.cast_natCast]
          obtain ⟨q, hq, herr⟩ := hcore (sa / sb) m n e f hm hn heq
          refine ⟨q, ?_, herr⟩
          change Flare.Binary64.Model.Value.toRational
            (Float.Model.pack (UnpackedFloat.div Format.binary64 a.unpack b.unpack)) = _
          rw [hu', hu]
          exact hq

private lemma model_div_error (a b : Float.Model) (av bv : Rat) (N : Int)
    (ha : Flare.Binary64.Model.Value.toRational a = some av)
    (hb : Flare.Binary64.Model.Value.toRational b = some bv)
    (hbv : bv ≠ 0) (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hv : |av / bv| ≤ (2 : Rat) ^ N)
    : ∃ q,
        Flare.Binary64.Model.Value.toRational (a / b) = some q
        ∧ |q - av / bv| ≤ (2 : Rat) ^ (N - 51) := by
  apply model_div_error_of_core a b av bv _ ha hb hbv (zpow_pos (by norm_num : (0 : Rat) < 2) _).le
  intro s m n e f hm hn heq
  have hmag : (m : Rat) * (2 : Rat)^e / ((n : Rat) * (2 : Rat)^f) = |av / bv| := by
    rw [← heq]
    cases s <;> simp [Sign.apply, abs_div, abs_mul,
      abs_of_pos (zpow_pos (by norm_num : (0 : Rat) < 2) _)]
  obtain ⟨q, hq, herr⟩ := finite_div_error s m n e f N hm hn hN hN' (by rw [hmag]; exact hv)
  exact ⟨q, hq, by rwa [heq] at herr⟩

private lemma finite_rational (x : Float) (hx : x.isFinite = true)
    : ∃ q, Flare.Binary64.Model.Value.toRational x.toModel = some q ∧ value x = (q : ℝ) := by
  have hv := finite_value x hx
  rw [interpretation_eq] at hv
  unfold Flare.Binary64.Model.Value.toReal at hv
  cases hq : Flare.Binary64.Model.Value.toRational x.toModel with
  | none => simp [hq] at hv
  | some q => exact ⟨q, rfl, by simpa [hq] using hv.symm⟩

/-- Division by a finite nonzero binary64 operand is finite when the exact
quotient is bounded by 2ᴺ, and has absolute error at most 2ᴺ⁻⁵¹. This includes
both operand signs, signed zero, and gradual underflow. -/
theorem div_error (a b : Float) (N : Int)
    (ha : a.isFinite = true) (hb : b.isFinite = true) (hbv : value b ≠ 0)
    (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hv : |value a / value b| ≤ (2 : ℝ) ^ N)
    : (a / b).isFinite = true ∧ |value (a / b) - value a / value b| ≤ (2 : ℝ) ^ (N - 51) := by
  obtain ⟨av, hav, hva⟩ := finite_rational a ha
  obtain ⟨bv, hbv', hvb⟩ := finite_rational b hb
  have hbn : bv ≠ 0 := by intro h; simp [hvb, h] at hbv
  have hbound : |av / bv| ≤ (2 : Rat)^N := by
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_zpow, Rat.cast_ofNat, ← hva, ← hvb] using hv
  obtain ⟨q, hq, herr⟩ := model_div_error a.toModel b.toModel av bv N hav hbv' hbn hN hN' hbound
  have he : Flare.Binary64.Value.modelToReal (a / b).toModel = some (q : ℝ) := by
    rw [interpretation_eq]
    change Flare.Binary64.Model.Value.toReal (a.toModel / b.toModel) = _
    simp [Flare.Binary64.Model.Value.toReal, hq]
  refine ⟨finite_of_value _ _ he, ?_⟩
  have herr' := (Rat.cast_le (K := ℝ)).mpr herr
  rw [hva, hvb]
  simpa only [value, he, Option.getD_some, Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_zpow,
    Rat.cast_ofNat]
    using herr'

/-- Native division with magnitude-scaled error and an absolute underflow
allowance. The denominator is finite and nonzero in the real interpretation. -/
theorem div_error_relative (a b : Float) (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hb0 : value b ≠ 0) (hx : |value a / value b| ≤ (2 : ℝ) ^ (1000 : Int))
    : (a / b).isFinite = true
      ∧ |value (a / b) - value a / value b|
        ≤ (2 : ℝ) ^ (-50 : Int) * (|value a / value b| + (2 : ℝ) ^ (-1022 : Int)) := by
  obtain ⟨E, hE, hE', hv, hs⟩ := bounded_exponent (value a / value b) hx
  have h := div_error a b E ha hb hb0 hE (by omega) hv
  exact ⟨h.1, h.2.trans (scaled_error_bound _ E 51 hs)⟩

end Flare.Binary64.Division
