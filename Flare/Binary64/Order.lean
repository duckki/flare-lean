import Flare.Binary64.Arithmetic
import Mathlib.Order.Compare

/-! Exact order and sign operations for finite native binary64 values.
These results connect executable guards to the real interpretation, including
signed zero and the transition between subnormal and normal representations. -/

namespace Flare.Binary64.Order
open Float.Model Float.Model.UnpackedFloat
open Flare.Binary64.Value Flare.Binary64.Arithmetic
open Flare.Binary64.Model.Rounding

private lemma exponent_lt (m n : Nat) (e f : Int) (hn : 0 < n)
    (hm : m < 2^53) (he : -1074 ≤ e) (hnc : n.log2 = 52 ∨ f = -1074) (hef : e < f)
    : (m : ℝ) * (2 : ℝ)^e < (n : ℝ) * (2 : ℝ)^f := by
  have hnlog : n.log2 = 52 := by rcases hnc with h | h; exact h; omega
  have hnb : 2^52 ≤ n := ((Nat.log2_eq_iff (Nat.ne_of_gt hn)).mp hnlog).1
  have hmlt : (m : ℝ) < (2 : ℝ)^53 := by exact_mod_cast hm
  have hnle : (2 : ℝ)^52 ≤ (n : ℝ) := by exact_mod_cast hnb
  have hpow : (2 : ℝ)^53 * (2 : ℝ)^e ≤ (2 : ℝ)^52 * (2 : ℝ)^f := by
    rw [← zpow_natCast (2 : ℝ) 53, ← zpow_natCast (2 : ℝ) 52,
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  exact (mul_lt_mul_of_pos_right hmlt (zpow_pos (by norm_num) _)).trans_le
    (hpow.trans (mul_le_mul_of_nonneg_right hnle (zpow_pos (by norm_num) _).le))

private lemma compare_magnitudes (m n : Nat) (e f : Int) (hm : 0 < m) (hn : 0 < n)
    (hmb : m < 2^53) (hnb : n < 2^53) (he : -1074 ≤ e) (hf : -1074 ≤ f)
    (hmc : m.log2 = 52 ∨ e = -1074) (hnc : n.log2 = 52 ∨ f = -1074)
    : ((compare e f).then (compare m n)).Compares ((m : ℝ) * (2 : ℝ)^e) ((n : ℝ) * (2 : ℝ)^f) := by
  rcases lt_trichotomy e f with hef | hef | hef
  · rw [Int.compare_eq_lt.mpr hef]
    exact exponent_lt m n e f hn hmb he hnc hef
  · subst f
    rw [Int.compare_eq_eq.mpr rfl]
    rcases lt_trichotomy m n with hmn | hmn | hmn
    · rw [Nat.compare_eq_lt.mpr hmn]
      exact mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hmn) (zpow_pos (by norm_num) _)
    · rw [Nat.compare_eq_eq.mpr hmn]
      exact congrArg (fun k : Nat => (k : ℝ) * (2 : ℝ)^e) hmn
    · rw [Nat.compare_eq_gt.mpr hmn]
      exact mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hmn) (zpow_pos (by norm_num) _)
  · rw [Int.compare_eq_gt.mpr hef]
    exact exponent_lt n m f e hm hnb hf hmc hef

private lemma compares_neg (o : Ordering) (a b : ℝ) (h : o.Compares a b)
    : o.swap.Compares (-a) (-b) := by
  cases o <;> simp_all [Ordering.Compares, Ordering.swap]

/-- Finite native comparisons agree with the real ordering. Canonical unpacked
mantissas justify the model's lexicographic exponent/mantissa comparison. -/
theorem compare_value (a b : Float) (ha : a.isFinite = true) (hb : b.isFinite = true)
    : Float.Model.compare a.toModel b.toModel = some (compare (value a) (value b)) := by
  change a.toModel.unpack.isFinite = true at ha
  change b.toModel.unpack.isFinite = true at hb
  unfold Float.Model.compare
  cases hu : a.toModel.unpack with
  | notANumber => simp [hu, UnpackedFloat.isFinite] at ha
  | infinity s => simp [hu, UnpackedFloat.isFinite] at ha
  | zero sa =>
      have hav : value a = 0 := by simp [value, Flare.Binary64.Value.modelToReal, hu]
      rw [hav]
      cases hu' : b.toModel.unpack with
      | notANumber => simp [hu', UnpackedFloat.isFinite] at hb
      | infinity s => simp [hu', UnpackedFloat.isFinite] at hb
      | zero sb =>
          have hbv : value b = 0 := by simp [value, Flare.Binary64.Value.modelToReal, hu']
          rw [hbv, compare_eq_iff_eq.mpr rfl]
          rfl
      | finite sb n f hn =>
          have hpos : 0 < (n : ℝ) * (2 : ℝ)^f := mul_pos (Nat.cast_pos.mpr hn) (zpow_pos (by
            norm_num) _)
          cases sb with
          | positive =>
              have hbv : value b = (n : ℝ) * (2 : ℝ)^f := by
                simp [value, Flare.Binary64.Value.modelToReal, hu', Sign.apply]
              rw [hbv, compare_lt_iff_lt.mpr hpos]
              rfl
          | negative =>
              have hbv : value b = -((n : ℝ) * (2 : ℝ)^f) := by
                simp [value, Flare.Binary64.Value.modelToReal, hu', Sign.apply]
              rw [hbv, compare_gt_iff_gt.mpr (by linarith : -((n : ℝ) * (2 : ℝ)^f) < 0)]
              rfl
  | finite sa m e hm =>
      obtain ⟨hmb, he, _, hmc⟩ := unpack_finite_shape a.toModel sa m e hm hu
      have hpos : 0 < (m : ℝ) * (2 : ℝ)^e := mul_pos (Nat.cast_pos.mpr hm) (zpow_pos (by norm_num)
        _)
      cases hu' : b.toModel.unpack with
      | notANumber => simp [hu', UnpackedFloat.isFinite] at hb
      | infinity s => simp [hu', UnpackedFloat.isFinite] at hb
      | zero sb =>
          have hbv : value b = 0 := by simp [value, Flare.Binary64.Value.modelToReal, hu']
          rw [hbv]
          cases sa with
          | positive =>
              have hav : value a = (m : ℝ) * (2 : ℝ)^e := by
                simp [value, Flare.Binary64.Value.modelToReal, hu, Sign.apply]
              rw [hav, compare_gt_iff_gt.mpr hpos]
              rfl
          | negative =>
              have hav : value a = -((m : ℝ) * (2 : ℝ)^e) := by
                simp [value, Flare.Binary64.Value.modelToReal, hu, Sign.apply]
              rw [hav, compare_lt_iff_lt.mpr (by linarith : -((m : ℝ) * (2 : ℝ)^e) < 0)]
              rfl
      | finite sb n f hn =>
          obtain ⟨hnb, hf, _, hnc⟩ := unpack_finite_shape b.toModel sb n f hn hu'
          have hpos' : 0 < (n : ℝ) * (2 : ℝ)^f := mul_pos (Nat.cast_pos.mpr hn) (zpow_pos (by
            norm_num) _)
          have hcmp := compare_magnitudes m n e f hm hn hmb hnb he hf hmc hnc
          have hav : value a = (sa.apply (m : Int) : ℝ) * (2 : ℝ)^e := by
            simp [value, Flare.Binary64.Value.modelToReal, hu]
          have hbv : value b = (sb.apply (n : Int) : ℝ) * (2 : ℝ)^f := by
            simp [value, Flare.Binary64.Value.modelToReal, hu']
          rw [hav, hbv]
          cases sa <;> cases sb <;> simp only [UnpackedFloat.compare, Sign.apply, Int.cast_neg,
            Int.cast_natCast, neg_mul]
          · exact congrArg some ((compare_iff _ _).mpr (compares_neg _ _ _ hcmp)).symm
          · rw [compare_lt_iff_lt.mpr (by linarith : -((m : ℝ) * (2 : ℝ)^e) < (n : ℝ) * (2 : ℝ)^f)]
          · rw [compare_gt_iff_gt.mpr (by linarith : -((n : ℝ) * (2 : ℝ)^f) < (m : ℝ) * (2 : ℝ)^e)]
          · exact congrArg some ((compare_iff _ _).mpr hcmp).symm

/-- A finite native strict-comparison guard has exactly its real meaning. -/
theorem lt_iff (a b : Float) (ha : a.isFinite = true) (hb : b.isFinite = true)
    : a < b ↔ value a < value b := by
  change Float.lt a b = true ↔ _
  simp only [Float.lt, decide_eq_true_eq]
  change (Float.Model.compare a.toModel b.toModel == some .lt) = true ↔ _
  rw [compare_value a b ha hb]
  simp only [beq_iff_eq, Option.some.injEq, compare_lt_iff_lt]

/-- A finite native non-strict-comparison guard has exactly its real meaning. -/
theorem le_iff (a b : Float) (ha : a.isFinite = true) (hb : b.isFinite = true)
    : a ≤ b ↔ value a ≤ value b := by
  change Float.le a b = true ↔ _
  simp only [Float.le, decide_eq_true_eq]
  change (Float.Model.compare a.toModel b.toModel).any Ordering.isLE = true ↔ _
  rw [compare_value a b ha hb]
  have h := compare_le_iff_le (a := value a) (b := value b)
  cases hc : compare (value a) (value b) <;> simpa [hc] using h

/-- IEEE equality of finite operands is equality of their real values; this
identifies the two signed zeros without asserting bit equality. -/
theorem beq_iff (a b : Float) (ha : a.isFinite = true) (hb : b.isFinite = true)
    : (a == b) = true ↔ value a = value b := by
  change (Float.Model.compare a.toModel b.toModel == some .eq) = true ↔ _
  rw [compare_value a b ha hb]
  simp only [beq_iff_eq, Option.some.injEq, compare_eq_iff_eq]

/-- Selecting the maximum of finite operands is an exact operation. -/
theorem max_value (a b : Float) (ha : a.isFinite = true) (hb : b.isFinite = true)
    : (max a b).isFinite = true ∧ value (max a b) = max (value a) (value b) := by
  change (if a ≤ b then b else a).isFinite = true ∧
    value (if a ≤ b then b else a) = max (value a) (value b)
  by_cases h : a ≤ b
  · rw [if_pos h, max_eq_right ((le_iff a b ha hb).mp h)]
    exact ⟨hb, rfl⟩
  · have h' : value b ≤ value a := le_of_not_ge (fun hh => h ((le_iff a b ha hb).mpr hh))
    rw [if_neg h, max_eq_left h']
    exact ⟨ha, rfl⟩

private lemma pack_finite_value (x : Float.Model) (s s' : Sign) (m : Nat) (e : Int)
    (hm : 0 < m) (hu : x.unpack = .finite s m e hm)
    : Flare.Binary64.Value.modelToReal (Float.Model.pack (.finite s' m e hm))
      = some ((s'.apply (m : Int) : ℝ) * (2 : ℝ)^e) := by
  obtain ⟨hmb, he, he', hc⟩ := unpack_finite_shape x s m e hm hu
  unfold Flare.Binary64.Value.modelToReal
  rcases hc with hlog | heq
  · rw [Flare.Binary64.Model.Conversion.unpack_pack_normal s' m e hm hlog he he']
  · subst e
    by_cases hsmall : m < 2^52
    · rw [unpack_pack_subnormal s' m hm hsmall]
    · rw [Flare.Binary64.Model.Conversion.unpack_pack_normal s' m (-1074) hm
        ((Nat.log2_eq_iff (Nat.ne_of_gt hm)).mpr ⟨by omega, hmb⟩) (by omega) (by omega)]

/-- Absolute value is finite and exact; it introduces no rounding. -/
theorem abs_value (x : Float) (hx : x.isFinite = true)
    : x.abs.isFinite = true ∧ value x.abs = |value x| := by
  change x.toModel.unpack.isFinite = true at hx
  cases hu : x.toModel.unpack with
  | notANumber => simp [hu, UnpackedFloat.isFinite] at hx
  | infinity s => simp [hu, UnpackedFloat.isFinite] at hx
  | zero s =>
      have hv : value x = 0 := by simp [value, Flare.Binary64.Value.modelToReal, hu]
      have hq : Flare.Binary64.Value.modelToReal x.abs.toModel = some 0 := by
        change Flare.Binary64.Value.modelToReal
          (Float.Model.pack (UnpackedFloat.abs x.toModel.unpack)) = _
        rw [hu]
        simp only [UnpackedFloat.abs]
        rfl
      exact ⟨finite_of_value _ _ hq, by rw [hv]; simp [value, hq]⟩
  | finite s m e hm =>
      have hq : Flare.Binary64.Value.modelToReal x.abs.toModel = some ((m : ℝ) * (2 : ℝ)^e) := by
        change Flare.Binary64.Value.modelToReal
          (Float.Model.pack (UnpackedFloat.abs x.toModel.unpack)) = _
        rw [hu]
        exact pack_finite_value x.toModel s .positive m e hm hu
      refine ⟨finite_of_value _ _ hq, ?_⟩
      have hv : value x = (s.apply (m : Int) : ℝ) * (2 : ℝ)^e := by
        simp [value, Flare.Binary64.Value.modelToReal, hu]
      rw [hv]
      cases s <;> simp [value, hq, Sign.apply, abs_mul,
        abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]

/-- Negation is finite and exact; signed zero has real value zero. -/
theorem neg_value (x : Float) (hx : x.isFinite = true)
    : (-x).isFinite = true ∧ value (-x) = -value x := by
  change x.toModel.unpack.isFinite = true at hx
  cases hu : x.toModel.unpack with
  | notANumber => simp [hu, UnpackedFloat.isFinite] at hx
  | infinity s => simp [hu, UnpackedFloat.isFinite] at hx
  | zero s =>
      have hv : value x = 0 := by simp [value, Flare.Binary64.Value.modelToReal, hu]
      have hq : Flare.Binary64.Value.modelToReal (-x).toModel = some 0 := by
        change Flare.Binary64.Value.modelToReal
          (Float.Model.pack (UnpackedFloat.neg x.toModel.unpack)) = _
        rw [hu]
        simp only [UnpackedFloat.neg]
        cases -s <;> rfl
      exact ⟨finite_of_value _ _ hq, by rw [hv]; simp [value, hq]⟩
  | finite s m e hm =>
      have hq : Flare.Binary64.Value.modelToReal (-x).toModel =
          some (((-s).apply (m : Int) : ℝ) * (2 : ℝ)^e) := by
        change Flare.Binary64.Value.modelToReal
          (Float.Model.pack (UnpackedFloat.neg x.toModel.unpack)) = _
        rw [hu]
        exact pack_finite_value x.toModel s (-s) m e hm hu
      refine ⟨finite_of_value _ _ hq, ?_⟩
      have hv : value x = (s.apply (m : Int) : ℝ) * (2 : ℝ)^e := by
        simp [value, Flare.Binary64.Value.modelToReal, hu]
      have hs : (-s).apply (m : Int) = -(s.apply (m : Int)) := by
        cases s
        · change (m : Int) = -(-(m : Int))
          exact (neg_neg _).symm
        · rfl
      rw [hv]
      simp only [value, hq, Option.getD_some, hs, Int.cast_neg, neg_mul]

end Flare.Binary64.Order
