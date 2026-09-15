import Mathlib.Tactic.Ring
import Flare.Binary64.Model.Rounding

/-! Finite addition, subtraction, and multiplication bounds for the pinned binary64
model. Exact rational interpretations occur only in these proofs. Each operation
constructs a finite result and bounds its error from exact arithmetic. -/

open Float.Model Float.Model.UnpackedFloat
open Flare.Binary64.Model.Rounding
namespace Flare.Binary64.Model.Arithmetic
open Flare.Binary64.Model.Conversion

private theorem unpack_cases (v : Float.Model) (x : Rat)
    (h : Flare.Binary64.Model.Value.toRational v = some x)
    : (∃ s, v.unpack = .zero s ∧ x = 0)
      ∨ ∃ s m e,
        ∃ hp : 0 < m,
          v.unpack = .finite s m e hp ∧ x = (s.apply (m : Int) : Rat) * (2 : Rat) ^ e := by
  cases hu : v.unpack with
  | notANumber =>
      simp [Flare.Binary64.Model.Value.toRational, hu,
        Flare.Binary64.Model.Value.unpackedToRational] at h
  | infinity s =>
      simp [Flare.Binary64.Model.Value.toRational, hu,
        Flare.Binary64.Model.Value.unpackedToRational] at h
  | zero s =>
      left
      refine ⟨s, rfl, ?_⟩
      simpa [Flare.Binary64.Model.Value.toRational, hu,
        Flare.Binary64.Model.Value.unpackedToRational] using h.symm
  | finite s m e hp =>
      right
      refine ⟨s, m, e, hp, rfl, ?_⟩
      simpa [Flare.Binary64.Model.Value.toRational, hu,
        Flare.Binary64.Model.Value.unpackedToRational] using h.symm

private theorem aligned_value (s : Sign) (m : Nat) (e target : Int) (ht : target ≤ e)
    : (s.apply ((decreaseExponent m e target).1 : Int) : Rat) * (2 : Rat) ^ target
      = (s.apply (m : Int) : Rat) * (2 : Rat) ^ e := by
  have h := decrease_preserves_value m (e - target).toNat e
  have he : e - ((e - target).toNat : Int) = target := by omega
  rw [he] at h
  change (s.apply ((m <<< (e - target).toNat : Nat) : Int) : Rat) * (2 : Rat)^target = _
  cases s with
  | positive => simpa only [Sign.apply, Int.cast_natCast] using h
  | negative =>
      simpa only [Sign.apply, Int.cast_neg, Int.cast_natCast, neg_mul] using congrArg Neg.neg h

/-- Addition transfers any proved signed-normalization error allowance to the
actual model operation, including its exact signed-zero branches. -/
theorem add_error_of_normalize (a b : Float.Model) (x y ε : Rat)
    (ha : Flare.Binary64.Model.Value.toRational a = some x)
    (hb : Flare.Binary64.Model.Value.toRational b = some y) (hpos : 0 ≤ ε)
    (hround
      : ∀ (m e : Int),
          (m : Rat) * (2 : Rat) ^ e = x + y
          → ∃ q,
              Flare.Binary64.Model.Value.toRational
                  (Float.Model.pack (UnpackedFloat.normalize Format.binary64 m e .positive))
                = some q
              ∧ |q - (x + y)| ≤ ε)
    : ∃ q, Flare.Binary64.Model.Value.toRational (a + b) = some q ∧ |q - (x + y)| ≤ ε := by
  rcases unpack_cases a x ha with ⟨sa, hua, rfl⟩ | ⟨sa, ma, ea, hma, hua, rfl⟩
  · rcases unpack_cases b y hb with ⟨sb, hub, rfl⟩ | ⟨sb, mb, eb, hmb, hub, rfl⟩
    · refine ⟨0, ?_, by simpa using hpos⟩
      change Flare.Binary64.Model.Value.toRational (Float.Model.pack (UnpackedFloat.add
        Format.binary64 a.unpack b.unpack)) = _
      rw [hua, hub]
      cases sa <;> cases sb <;> rfl
    · refine ⟨(sb.apply (mb : Int) : Rat) * (2 : Rat)^eb, ?_, by simpa using hpos⟩
      change Flare.Binary64.Model.Value.toRational (Float.Model.pack (UnpackedFloat.add
        Format.binary64 a.unpack b.unpack)) = _
      rw [hua, hub]
      change Flare.Binary64.Model.Value.toRational (Float.Model.pack (.finite sb mb eb hmb)) = _
      rw [← hub, pack_unpack_rational]
      exact hb
  · rcases unpack_cases b y hb with ⟨sb, hub, rfl⟩ | ⟨sb, mb, eb, hmb, hub, rfl⟩
    · refine ⟨(sa.apply (ma : Int) : Rat) * (2 : Rat)^ea, ?_, by simpa using hpos⟩
      change Flare.Binary64.Model.Value.toRational (Float.Model.pack (UnpackedFloat.add
        Format.binary64 a.unpack b.unpack)) = _
      rw [hua, hub]
      change Flare.Binary64.Model.Value.toRational (Float.Model.pack (.finite sa ma ea hma)) = _
      rw [← hua, pack_unpack_rational]
      exact ha
    · let e := min ea eb
      let m := sa.apply ((decreaseExponent ma ea e).1 : Int) + sb.apply ((decreaseExponent mb eb
        e).1 : Int)
      have hx := aligned_value sa ma ea e (min_le_left _ _)
      have hy := aligned_value sb mb eb e (min_le_right _ _)
      have hvalue
          : (m : Rat) * (2 : Rat) ^ e
            = (sa.apply (ma : Int) : Rat) * (2 : Rat) ^ ea
              + (sb.apply (mb : Int) : Rat) * (2 : Rat) ^ eb := by
        dsimp only [m]
        rw [Int.cast_add, add_mul, hx, hy]
      obtain ⟨q, hq, herr⟩ := hround m e hvalue
      refine ⟨q, ?_, ?_⟩
      · change Flare.Binary64.Model.Value.toRational (Float.Model.pack (UnpackedFloat.add
        Format.binary64 a.unpack b.unpack)) = _
        rw [hua, hub]
        exact hq
      · exact herr

/-- Finite arithmetic with the model-derived absolute one-ulp allowance. -/
theorem add_error (a b : Float.Model) (x y : Rat) (N : Int)
    (ha : Flare.Binary64.Model.Value.toRational a = some x)
    (hb : Flare.Binary64.Model.Value.toRational b = some y) (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hv : |x + y| ≤ (2 : Rat) ^ N)
    : ∃ q,
        Flare.Binary64.Model.Value.toRational (a + b) = some q
        ∧ |q - (x + y)| ≤ (2 : Rat) ^ (N - 52) := by
  apply add_error_of_normalize a b x y _ ha hb (zpow_pos (by norm_num : (0 : Rat) < 2) _).le
  intro m e hvalue
  obtain ⟨q, hq, herr⟩ := normalize_error m e N .positive hN hN' (by rw [hvalue]; exact hv)
  exact ⟨q, hq, by simpa only [hvalue] using herr⟩

private theorem pack_changed_sign (v : Float.Model) (s t : Sign) (m : Nat) (e : Int)
    (hp : 0 < m) (hu : v.unpack = .finite s m e hp)
    : Flare.Binary64.Model.Value.toRational (Float.Model.pack (.finite t m e hp))
      = some ((t.apply (m : Int) : Rat) * (2 : Rat) ^ e) := by
  obtain ⟨hm, he, he', hc⟩ := unpack_finite_shape v s m e hp hu
  unfold Flare.Binary64.Model.Value.toRational
  rcases hc with hc | rfl
  · rw [Flare.Binary64.Model.Conversion.unpack_pack_normal t m e hp hc he he']
    rfl
  · by_cases hs : m < 2^52
    · rw [unpack_pack_subnormal t m hp hs]; rfl
    · rw [Flare.Binary64.Model.Conversion.unpack_pack_normal t m (-1074) hp
        ((Nat.log2_eq_iff (Nat.ne_of_gt hp)).mpr ⟨by omega, hm⟩) (by omega) (by omega)]
      rfl

/-- Subtraction transfers a signed-normalization allowance to the actual model
operation, including its exact signed-zero and sign-changing branches. -/
theorem sub_error_of_normalize (a b : Float.Model) (x y ε : Rat)
    (ha : Flare.Binary64.Model.Value.toRational a = some x)
    (hb : Flare.Binary64.Model.Value.toRational b = some y) (hpos : 0 ≤ ε)
    (hround
      : ∀ (m e : Int),
          (m : Rat) * (2 : Rat) ^ e = x - y
          → ∃ q,
              Flare.Binary64.Model.Value.toRational
                  (Float.Model.pack (UnpackedFloat.normalize Format.binary64 m e .positive))
                = some q
              ∧ |q - (x - y)| ≤ ε)
    : ∃ q, Flare.Binary64.Model.Value.toRational (a - b) = some q ∧ |q - (x - y)| ≤ ε := by
  rcases unpack_cases a x ha with ⟨sa, hua, rfl⟩ | ⟨sa, ma, ea, hma, hua, rfl⟩
  · rcases unpack_cases b y hb with ⟨sb, hub, rfl⟩ | ⟨sb, mb, eb, hmb, hub, rfl⟩
    · refine ⟨0, ?_, by simpa using hpos⟩
      change Flare.Binary64.Model.Value.toRational (Float.Model.pack (UnpackedFloat.sub
        Format.binary64 a.unpack b.unpack)) = _
      rw [hua, hub]
      cases sa <;> cases sb <;> rfl
    · refine ⟨-((sb.apply (mb : Int) : Rat) * (2 : Rat)^eb), ?_, by simpa using hpos⟩
      change Flare.Binary64.Model.Value.toRational (Float.Model.pack (UnpackedFloat.sub
        Format.binary64 a.unpack b.unpack)) = _
      rw [hua, hub]
      change Flare.Binary64.Model.Value.toRational (Float.Model.pack (.finite (-sb) mb eb hmb)) = _
      rw [pack_changed_sign b sb (-sb) mb eb hmb hub]
      cases sb <;> simp [Sign.apply]
  · rcases unpack_cases b y hb with ⟨sb, hub, rfl⟩ | ⟨sb, mb, eb, hmb, hub, rfl⟩
    · refine ⟨(sa.apply (ma : Int) : Rat) * (2 : Rat)^ea, ?_, by simpa using hpos⟩
      change Flare.Binary64.Model.Value.toRational (Float.Model.pack (UnpackedFloat.sub
        Format.binary64 a.unpack b.unpack)) = _
      rw [hua, hub]
      change Flare.Binary64.Model.Value.toRational (Float.Model.pack (.finite sa ma ea hma)) = _
      rw [← hua, pack_unpack_rational]
      exact ha
    · let e := min ea eb
      let m := sa.apply ((decreaseExponent ma ea e).1 : Int) - sb.apply ((decreaseExponent mb eb
        e).1 : Int)
      have hx := aligned_value sa ma ea e (min_le_left _ _)
      have hy := aligned_value sb mb eb e (min_le_right _ _)
      have hvalue
          : (m : Rat) * (2 : Rat) ^ e
            = (sa.apply (ma : Int) : Rat) * (2 : Rat) ^ ea
              - (sb.apply (mb : Int) : Rat) * (2 : Rat) ^ eb := by
        dsimp only [m]
        rw [Int.cast_sub, sub_mul, hx, hy]
      obtain ⟨q, hq, herr⟩ := hround m e hvalue
      refine ⟨q, ?_, ?_⟩
      · change Flare.Binary64.Model.Value.toRational (Float.Model.pack (UnpackedFloat.sub
        Format.binary64 a.unpack b.unpack)) = _
        rw [hua, hub]
        exact hq
      · exact herr

/-- Finite arithmetic with the model-derived absolute one-ulp allowance. -/
theorem sub_error (a b : Float.Model) (x y : Rat) (N : Int)
    (ha : Flare.Binary64.Model.Value.toRational a = some x)
    (hb : Flare.Binary64.Model.Value.toRational b = some y) (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hv : |x - y| ≤ (2 : Rat) ^ N)
    : ∃ q,
        Flare.Binary64.Model.Value.toRational (a - b) = some q
        ∧ |q - (x - y)| ≤ (2 : Rat) ^ (N - 52) := by
  apply sub_error_of_normalize a b x y _ ha hb (zpow_pos (by norm_num : (0 : Rat) < 2) _).le
  intro m e hvalue
  obtain ⟨q, hq, herr⟩ := normalize_error m e N .positive hN hN' (by rw [hvalue]; exact hv)
  exact ⟨q, hq, by simpa only [hvalue] using herr⟩

/-- Multiplication transfers a proved mantissa-rounding allowance to the model
operation. Canonical operand shapes establish the rounding preconditions. -/
theorem mul_error_of_round (a b : Float.Model) (x y ε : Rat)
    (ha : Flare.Binary64.Model.Value.toRational a = some x)
    (hb : Flare.Binary64.Model.Value.toRational b = some y) (hpos : 0 ≤ ε)
    (hround
      : ∀ (s : Sign) (m : Nat) (e : Int),
          0 < m
          → (52 ≤ m.log2 ∨ e ≤ -1074)
          → (s.apply (m : Int) : Rat) * (2 : Rat) ^ e = x * y
          → ∃ q,
              Flare.Binary64.Model.Value.toRational
                  (Float.Model.pack (roundWithAccuracy Format.binary64 s m e .exact))
                = some q
              ∧ |q - x * y| ≤ ε)
    : ∃ q, Flare.Binary64.Model.Value.toRational (a * b) = some q ∧ |q - x * y| ≤ ε := by
  rcases unpack_cases a x ha with ⟨sa, hua, rfl⟩ | ⟨sa, ma, ea, hma, hua, rfl⟩
  · rcases unpack_cases b y hb with ⟨sb, hub, rfl⟩ | ⟨sb, mb, eb, hmb, hub, rfl⟩
    · refine ⟨0, ?_, by simpa using hpos⟩
      change Flare.Binary64.Model.Value.toRational (Float.Model.pack (UnpackedFloat.mul
        Format.binary64 a.unpack b.unpack)) = _
      rw [hua, hub]
      simp only [UnpackedFloat.mul]
      cases sa <;> cases sb <;> rfl
    · refine ⟨0, ?_, by simpa using hpos⟩
      change Flare.Binary64.Model.Value.toRational (Float.Model.pack (UnpackedFloat.mul
        Format.binary64 a.unpack b.unpack)) = _
      rw [hua, hub]
      simp only [UnpackedFloat.mul]
      cases sa <;> cases sb <;> rfl
  · rcases unpack_cases b y hb with ⟨sb, hub, rfl⟩ | ⟨sb, mb, eb, hmb, hub, rfl⟩
    · refine ⟨0, ?_, by simpa using hpos⟩
      change Flare.Binary64.Model.Value.toRational (Float.Model.pack (UnpackedFloat.mul
        Format.binary64 a.unpack b.unpack)) = _
      rw [hua, hub]
      simp only [UnpackedFloat.mul]
      cases sa <;> cases sb <;> rfl
    · obtain ⟨_, _, _, hca⟩ := unpack_finite_shape a sa ma ea hma hua
      obtain ⟨_, _, _, hcb⟩ := unpack_finite_shape b sb mb eb hmb hub
      have hc : 52 ≤ (ma * mb).log2 ∨ ea + eb ≤ -1074 := by
        rcases hca with hca | hca
        · left
          apply (Nat.le_log2 (Nat.ne_of_gt (Nat.mul_pos hma hmb))).mpr
          have ht := (Nat.log2_eq_iff (Nat.ne_of_gt hma)).mp hca
          have := Nat.mul_le_mul_left ma (show 1 ≤ mb by omega)
          omega
        · rcases hcb with hcb | hcb
          · left
            apply (Nat.le_log2 (Nat.ne_of_gt (Nat.mul_pos hma hmb))).mpr
            have ht := (Nat.log2_eq_iff (Nat.ne_of_gt hmb)).mp hcb
            have := Nat.mul_le_mul_right mb (show 1 ≤ ma by omega)
            omega
          · right; omega
      have hvalue : (((sa * sb).apply (ma * mb : Nat) : Int) : Rat) * (2 : Rat)^(ea + eb) =
          ((sa.apply (ma : Int) : Rat) * (2 : Rat)^ea) * ((sb.apply (mb : Int) : Rat) * (2 :
            Rat)^eb) := by
        rw [zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
        cases sa <;> cases sb <;> simp [Sign.apply] <;> ring
      obtain ⟨q, hq, herr⟩ := hround (sa * sb) (ma * mb) (ea + eb)
        (Nat.mul_pos hma hmb) hc hvalue
      refine ⟨q, ?_, ?_⟩
      · change Flare.Binary64.Model.Value.toRational (Float.Model.pack (UnpackedFloat.mul
        Format.binary64 a.unpack b.unpack)) = _
        rw [hua, hub]
        exact hq
      · exact herr

/-- Finite multiplication with the model-derived absolute one-ulp allowance. -/
theorem mul_error (a b : Float.Model) (x y : Rat) (N : Int)
    (ha : Flare.Binary64.Model.Value.toRational a = some x)
    (hb : Flare.Binary64.Model.Value.toRational b = some y) (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hv : |x * y| ≤ (2 : Rat) ^ N)
    : ∃ q,
        Flare.Binary64.Model.Value.toRational (a * b) = some q
        ∧ |q - (x * y)| ≤ (2 : Rat) ^ (N - 52) := by
  apply mul_error_of_round a b x y _ ha hb (zpow_pos (by norm_num : (0 : Rat) < 2) _).le
  intro s m e hm hc hvalue
  have habs : |(s.apply (m : Int) : Rat) * (2 : Rat)^e| = (m : Rat) * (2 : Rat)^e := by
    have hp := le_of_lt (zpow_pos (by norm_num : (0 : Rat) < 2) e)
    cases s <;> simp [Sign.apply, abs_mul, abs_of_nonneg hp]
  obtain ⟨q, hq, herr⟩ := round_with_accuracy_error s m e N .exact hm hc hN hN'
    (by rw [← habs, hvalue]; exact hv)
  exact ⟨q, hq, by simpa only [hvalue] using herr⟩

/-- A finite real interpretation comes from the exact stored rational. -/
theorem rational_of_real (v : Float.Model) (x : ℝ)
    (h : Flare.Binary64.Model.Value.toReal v = some x)
    : ∃ q, Flare.Binary64.Model.Value.toRational v = some q ∧ (q : ℝ) = x := by
  unfold Flare.Binary64.Model.Value.toReal at h
  cases hq : Flare.Binary64.Model.Value.toRational v with
  | none => simp [hq] at h
  | some q => exact ⟨q, rfl, by simpa [hq] using h⟩

theorem finite_of_real (v : Float.Model) (x : ℝ) (h : Flare.Binary64.Model.Value.toReal v = some x)
    : Flare.Binary64.Model.Value.finite v = some v := by
  obtain ⟨q, hq, _⟩ := rational_of_real v x h
  simp [Flare.Binary64.Model.Value.finite, finite_of_rational v q hq]

/-- Real-valued form of the concrete binary64 add bound. -/
theorem add_error_real (a b : Float.Model) (x y : ℝ) (N : Int)
    (ha : Flare.Binary64.Model.Value.toReal a = some x)
    (hb : Flare.Binary64.Model.Value.toReal b = some y) (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hv : |x + y| ≤ (2 : ℝ) ^ N)
    : ∃ q : ℝ,
        Flare.Binary64.Model.Value.toReal (a + b) = some q
        ∧ |q - (x + y)| ≤ (2 : ℝ) ^ (N - 52) := by
  obtain ⟨u, hu, rfl⟩ := rational_of_real a x ha
  obtain ⟨v, hv', rfl⟩ := rational_of_real b y hb
  have hbound : |u + v| ≤ (2 : Rat)^N := by
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_abs, Rat.cast_add, Rat.cast_zpow, Rat.cast_ofNat] using hv
  obtain ⟨q, hq, herr⟩ := add_error a b u v N hu hv' hN hN' hbound
  refine ⟨(q : ℝ), by simp [Flare.Binary64.Model.Value.toReal, hq], ?_⟩
  have hcast := (Rat.cast_le (K := ℝ)).mpr herr
  simpa only [Rat.cast_abs, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat]
    using hcast

/-- Real-valued form of the concrete binary64 sub bound. -/
theorem sub_error_real (a b : Float.Model) (x y : ℝ) (N : Int)
    (ha : Flare.Binary64.Model.Value.toReal a = some x)
    (hb : Flare.Binary64.Model.Value.toReal b = some y) (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hv : |x - y| ≤ (2 : ℝ) ^ N)
    : ∃ q : ℝ,
        Flare.Binary64.Model.Value.toReal (a - b) = some q
        ∧ |q - (x - y)| ≤ (2 : ℝ) ^ (N - 52) := by
  obtain ⟨u, hu, rfl⟩ := rational_of_real a x ha
  obtain ⟨v, hv', rfl⟩ := rational_of_real b y hb
  have hbound : |u - v| ≤ (2 : Rat)^N := by
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_zpow, Rat.cast_ofNat] using hv
  obtain ⟨q, hq, herr⟩ := sub_error a b u v N hu hv' hN hN' hbound
  refine ⟨(q : ℝ), by simp [Flare.Binary64.Model.Value.toReal, hq], ?_⟩
  have hcast := (Rat.cast_le (K := ℝ)).mpr herr
  simpa only [Rat.cast_abs, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat]
    using hcast

/-- Real-valued form of the concrete binary64 mul bound. -/
theorem mul_error_real (a b : Float.Model) (x y : ℝ) (N : Int)
    (ha : Flare.Binary64.Model.Value.toReal a = some x)
    (hb : Flare.Binary64.Model.Value.toReal b = some y) (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hv : |x * y| ≤ (2 : ℝ) ^ N)
    : ∃ q : ℝ,
        Flare.Binary64.Model.Value.toReal (a * b) = some q
        ∧ |q - (x * y)| ≤ (2 : ℝ) ^ (N - 52) := by
  obtain ⟨u, hu, rfl⟩ := rational_of_real a x ha
  obtain ⟨v, hv', rfl⟩ := rational_of_real b y hb
  have hbound : |u * v| ≤ (2 : Rat)^N := by
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_abs, Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat] using hv
  obtain ⟨q, hq, herr⟩ := mul_error a b u v N hu hv' hN hN' hbound
  refine ⟨(q : ℝ), by simp [Flare.Binary64.Model.Value.toReal, hq], ?_⟩
  have hcast := (Rat.cast_le (K := ℝ)).mpr herr
  simpa only [Rat.cast_abs, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat]
    using hcast

end Flare.Binary64.Model.Arithmetic
