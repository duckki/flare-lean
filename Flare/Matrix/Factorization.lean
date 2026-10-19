module

public import Flare.Binary64.Nearest
public import Flare.Binary64.Division
public import Flare.Binary64.Order
public import Flare.Matrix.Multiplication
public import Flare.Analysis.NumericalBounds

/-! Rounded sums used by the native LDLᵀ factorization. Each term executes two
multiplications followed by subtraction, matching the factorization kernel.
Residual and column execution have local error/success theorems.
`PositiveDefiniteFactorization` supplies the outer induction from input bounds. -/

@[expose] public section

namespace Flare.Matrix.Factorization
open Flare.Matrix.Value Flare.Binary64.Value Flare.Binary64.Arithmetic
open Flare.Matrix.Dense Std.Do

set_option experimental.vcgen true

attribute [local instance] Std.Internal.Order.instPartialOrderProp
  Std.Internal.Order.instCompleteLatticeProp

private lemma power_sub (E k : Int) : (2 : ℝ) ^ (E - k) = (2 : ℝ) ^ E / (2 : ℝ) ^ k :=
  zpow_sub₀ (by norm_num) _ _

/-- A rounded LDLᵀ term (l*d)*r is finite with a bound for both roundings.
The exponent choices include gradual underflow and zero-valued factors. -/
lemma gram_term (L D : Int) (l d r : Float)
    (hL : 0 ≤ L) (hD : 0 ≤ D) (hE : 2 * L + D ≤ 1000)
    (hl : l.isFinite = true) (hd : d.isFinite = true) (hr : r.isFinite = true)
    (hlb : |value l| ≤ (2 : ℝ) ^ L) (hdb : |value d| ≤ (2 : ℝ) ^ D)
    (hrb : |value r| ≤ (2 : ℝ) ^ L)
    : (l * d).isFinite = true
      ∧ ((l * d) * r).isFinite = true
      ∧ |value ((l * d) * r) - value l * value d * value r| ≤ (2 : ℝ) ^ (2 * L + D - 50) := by
  have hpL : 0 < (2 : ℝ)^L := zpow_pos (by norm_num) _
  have hpD : 0 < (2 : ℝ)^D := zpow_pos (by norm_num) _
  have hprod : |value l * value d| ≤ (2 : ℝ)^(L + D) := by
    rw [abs_mul, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    exact mul_le_mul hlb hdb (abs_nonneg _) hpL.le
  have hm := mul_error l d (L + D) hl hd (by omega) (by omega) hprod
  have hfirst : |value (l * d)| ≤ 2 * (2 : ℝ)^(L + D) := by
    have h := abs_sub_le (value (l * d)) (value l * value d) 0
    simp only [sub_zero] at h
    rw [power_sub] at hm
    norm_num only [zpow_ofNat, pow_succ, pow_zero] at hm
    nlinarith [hm.2, zpow_pos (by norm_num : (0 : ℝ) < 2) (L + D)]
  have hsecond : |value (l * d) * value r| ≤ (2 : ℝ)^(2 * L + D + 1) := by
    rw [abs_mul]
    calc
      _ ≤ (2 * (2 : ℝ) ^ (L + D)) * (2 : ℝ) ^ L :=
        mul_le_mul hfirst hrb (abs_nonneg _)
          (mul_nonneg (by norm_num) (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _))
      _ = (2 : ℝ) ^ ((L + D) + L) * (2 : ℝ) ^ (1 : Int) := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (L + D) L]
        norm_num only [zpow_one]
        ring
      _ = _ := by rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; omega
  have hm' := mul_error (l * d) r (2 * L + D + 1) hm.1 hr (by omega) (by omega) hsecond
  refine ⟨hm.1, hm'.1, ?_⟩
  have hprop : |value (l * d) * value r - value l * value d * value r| ≤
      (2 : ℝ)^(2 * L + D - 52) := by
    rw [← sub_mul, abs_mul]
    calc
      _ ≤ (2 : ℝ) ^ (L + D - 52) * (2 : ℝ) ^ L :=
        mul_le_mul hm.2 hrb (abs_nonneg _) (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      _ = _ := by rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; omega
  have htri := abs_sub_le (value ((l * d) * r)) (value (l * d) * value r)
    (value l * value d * value r)
  rw [show 2 * L + D + 1 - 52 = 2 * L + D - 51 by omega] at hm'
  simp only [power_sub] at hprop hm' ⊢
  norm_num only [zpow_ofNat, pow_succ, pow_zero] at hprop hm' ⊢
  nlinarith [hm'.2, zpow_pos (by norm_num : (0 : ℝ) < 2) (2 * L + D)]

/-- Two rounded multiplications, with error proportional to the actual
absolute Gram term. The additive allowance covers gradual underflow. -/
lemma gram_term_relative (l d r : Float)
    (hl : l.isFinite = true) (hd : d.isFinite = true) (hr : r.isFinite = true)
    (hlb : |value l| ≤ 128) (hdb : |value d| ≤ 2048) (hrb : |value r| ≤ 128)
    : (l * d).isFinite = true
      ∧ ((l * d) * r).isFinite = true
      ∧ |value ((l * d) * r) - value l * value d * value r|
        ≤ 3 * (2 : ℝ) ^ (-53 : Int) * |value l * value d * value r|
          + 256 * (2 : ℝ) ^ (-53 : Int) * (2 : ℝ) ^ (-1022 : Int) := by
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  have hη : 0 ≤ η := zpow_nonneg (by norm_num) _
  have hη' : η ≤ 1 := by dsimp [η]; exact (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show
    (-1022 : Int) ≤ 0 by omega)).trans (by norm_num)
  have hab : |value l * value d| ≤ (2 : ℝ)^(18 : Int) := by
    rw [abs_mul]; norm_num
    nlinarith [mul_le_mul hlb hdb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 128)]
  have hm := Flare.Binary64.Nearest.mul_error_nearest l d hl hd
    (hab.trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)))
  have hfirst : |value (l * d)| ≤ (2 : ℝ)^(19 : Int) := by
    have ht := abs_sub_le (value (l * d)) (value l * value d) 0
    simp only [sub_zero] at ht
    have he := hm.2
    change _ ≤ (2 : ℝ)^(-53 : Int) * (|value l * value d| + η) at he
    norm_num only [show (2 : ℝ)^(-53 : Int) = 1 / 9007199254740992 by norm_num] at he
    norm_num only [show (2 : ℝ)^(18 : Int) = 262144 by norm_num] at hab
    norm_num; linarith
  have hsecond : |value (l * d) * value r| ≤ (2 : ℝ)^(26 : Int) := by
    rw [abs_mul]
    calc
      _ ≤ (2 : ℝ) ^ (19 : Int) * 128 := mul_le_mul hfirst hrb (abs_nonneg _) (by positivity)
      _ = _ := by norm_num
  have hm' := Flare.Binary64.Nearest.mul_error_nearest (l * d) r hm.1 hr
    (hsecond.trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)))
  have hprop : |value (l * d) * value r - value l * value d * value r| ≤
      (2 : ℝ)^(-53 : Int) * |value l * value d * value r| +
        128 * (2 : ℝ)^(-53 : Int) * η := by
    rw [← sub_mul, abs_mul]
    calc
      _ ≤ ((2 : ℝ) ^ (-53 : Int) * (|value l * value d| + η)) * |value r| :=
        mul_le_mul_of_nonneg_right hm.2 (abs_nonneg _)
      _ ≤ _ := by
        simp only [abs_mul]
        norm_num only [show (2 : ℝ)^(-53 : Int) = 1 / 9007199254740992 by norm_num]
        nlinarith [mul_le_mul_of_nonneg_left hrb hη]
  have hprod := abs_sub_le (value (l * d) * value r) (value l * value d * value r) 0
  simp only [sub_zero] at hprod
  have ht := abs_sub_le (value ((l * d) * r)) (value (l * d) * value r)
    (value l * value d * value r)
  refine ⟨hm.1, hm'.1, ?_⟩
  have he := hm'.2
  change _ ≤ (2 : ℝ)^(-53 : Int) * (|value (l * d) * value r| + η) at he
  change _ ≤ 3 * (2 : ℝ)^(-53 : Int) * |value l * value d * value r| +
    256 * (2 : ℝ)^(-53 : Int) * η
  norm_num only [show (2 : ℝ)^(-53 : Int) = 1 / 9007199254740992 by norm_num] at he hprop ⊢
  nlinarith [abs_nonneg (value l * value d * value r)]

/-- Subtract one LDLᵀ term from a running accumulator. The exact target is the
corresponding real prefix sum of the supplied Float factors, not an ideal factor. -/
lemma gram_step (L D : Int) (k : Nat) (l d r s : Float) (exact : ℝ)
    (hL : 0 ≤ L) (hD : 0 ≤ D) (hE : 2 * L + D ≤ 1000) (hk : k ≤ 11)
    (hl : l.isFinite = true) (hd : d.isFinite = true) (hr : r.isFinite = true)
    (hs : s.isFinite = true)
    (hlb : |value l| ≤ (2 : ℝ) ^ L) (hdb : |value d| ≤ (2 : ℝ) ^ D)
    (hrb : |value r| ≤ (2 : ℝ) ^ L)
    (hexact : |exact| ≤ (k + 1 : Nat) * (2 : ℝ) ^ (2 * L + D))
    (herr : |value s - exact| ≤ k * (2 : ℝ) ^ (2 * L + D - 44))
    : (l * d).isFinite = true
      ∧ ((l * d) * r).isFinite = true
      ∧ (s - (l * d) * r).isFinite = true
      ∧ |value (s - (l * d) * r) - (exact - value l * value d * value r)|
        ≤ (k + 1 : Nat) * (2 : ℝ) ^ (2 * L + D - 44) := by
  let E := 2 * L + D
  have hp : 0 < (2 : ℝ)^E := zpow_pos (by norm_num) _
  have hk' : (k : ℝ) ≤ 11 := by exact_mod_cast hk
  have ht := gram_term L D l d r hL hD hE hl hd hr hlb hdb hrb
  have hreal : |value l * value d * value r| ≤ (2 : ℝ)^E := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ ((2 : ℝ) ^ L * (2 : ℝ) ^ D) * (2 : ℝ) ^ L :=
        mul_le_mul (mul_le_mul hlb hdb (abs_nonneg _) (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _))
          hrb (abs_nonneg _)
          (mul_nonneg (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
            (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _))
      _ = _ := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 1
        dsimp [E]
        omega
  have hterm : |value ((l * d) * r)| ≤ 2 * (2 : ℝ)^E := by
    have h := abs_sub_le (value ((l * d) * r)) (value l * value d * value r) 0
    simp only [sub_zero] at h
    have he := ht.2.2
    change |value ((l * d) * r) - value l * value d * value r| ≤ (2 : ℝ)^(E - 50) at he
    rw [power_sub] at he
    norm_num only [zpow_ofNat, pow_succ, pow_zero] at he
    nlinarith
  have hsbound : |value s| ≤ 13 * (2 : ℝ)^E := by
    have h := abs_sub_le (value s) exact 0
    simp only [sub_zero] at h
    change |value s - exact| ≤ k * (2 : ℝ)^(E - 44) at herr
    change |exact| ≤ (k + 1 : Nat) * (2 : ℝ)^E at hexact
    rw [power_sub] at herr
    norm_num only [zpow_ofNat, pow_succ, pow_zero] at herr
    simp only [Nat.cast_add, Nat.cast_one] at hexact
    nlinarith
  have hsub := sub_error s ((l * d) * r) (E + 4) hs ht.2.1 (by dsimp [E]; omega)
    (by dsimp [E]; omega) (by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num only [zpow_ofNat, pow_succ, pow_zero]
      linarith [abs_sub (value s) (value ((l * d) * r))])
  refine ⟨ht.1, ht.2.1, hsub.1, ?_⟩
  have h1 := abs_sub_le (value (s - (l * d) * r)) (value s - value ((l * d) * r))
    (exact - value l * value d * value r)
  have h2 : |(value s - value ((l * d) * r)) - (exact - value l * value d * value r)| ≤
      |value s - exact| + |value ((l * d) * r) - value l * value d * value r| := by
    have he : (value s - value ((l * d) * r)) - (exact - value l * value d * value r) =
        (value s - exact) - (value ((l * d) * r) - value l * value d * value r) := by ring
    rw [he]
    exact abs_sub _ _
  have h3 := ht.2.2
  change |value ((l * d) * r) - value l * value d * value r| ≤ (2 : ℝ)^(E - 50) at h3
  change |value s - exact| ≤ k * (2 : ℝ)^(E - 44) at herr
  change _ ≤ (k + 1 : Nat) * (2 : ℝ)^(E - 44)
  rw [show E + 4 - 52 = E - 48 by omega] at hsub
  simp only [power_sub, Nat.cast_add, Nat.cast_one] at herr hsub h3 ⊢
  norm_num only [zpow_ofNat, pow_succ, pow_zero] at herr hsub h3 ⊢
  nlinarith [hsub.2]

private noncomputable def residualBudget (k : Nat) (mass : ℝ) : ℝ :=
  (1001 / 1000 : ℝ) * (k + 4) * (2 : ℝ) ^ (-53 : Int) * mass

/-- One native Gram-residual step with a growing absolute term mass. The
small budget slack absorbs second-order rounding and subnormal errors. -/
lemma gram_step_relative (k : Nat) (l d r s : Float) (exact mass : ℝ)
    (hk : k ≤ 11) (hl : l.isFinite = true) (hd : d.isFinite = true)
    (hr : r.isFinite = true) (hs : s.isFinite = true)
    (hlb : |value l| ≤ 128) (hdb : |value d| ≤ 2048) (hrb : |value r| ≤ 128)
    (hmass : mass + |value l * value d * value r| ≤ (2 : ℝ) ^ (50 : Int))
    (hη : (2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int) ≤ mass)
    (hexact : |exact| ≤ mass)
    (herr : |value s - exact| ≤ (1001 / 1000 : ℝ) * (k + 4) * (2 : ℝ) ^ (-53 : Int) * mass)
    : (l * d).isFinite = true
      ∧ ((l * d) * r).isFinite = true
      ∧ (s - (l * d) * r).isFinite = true
      ∧ |value (s - (l * d) * r) - (exact - value l * value d * value r)|
        ≤ (1001 / 1000 : ℝ)
          * ((k + 1 : Nat) + 4)
          * (2 : ℝ) ^ (-53 : Int)
          * (mass + |value l * value d * value r|) := by
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  let t := |value l * value d * value r|
  have hη0 : 0 ≤ η := zpow_nonneg (by norm_num) _
  have ht0 : 0 ≤ t := abs_nonneg _
  have hm0 : 0 ≤ mass := (abs_nonneg _).trans hexact
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hk' : (k : ℝ) ≤ 11 := by exact_mod_cast hk
  have hkm := mul_le_mul_of_nonneg_right hk' hm0
  have hkt := mul_nonneg hk0 ht0
  have ht := gram_term_relative l d r hl hd hr hlb hdb hrb
  have hte := ht.2.2
  change _ ≤ 3 * (2 : ℝ)^(-53 : Int) * t + 256 * (2 : ℝ)^(-53 : Int) * η at hte
  change (2 : ℝ)^(20 : Int) * η ≤ mass at hη
  norm_num only [show (2 : ℝ)^(20 : Int) = 1048576 by norm_num] at hη
  have hsbound : |value s| ≤ 2 * mass := by
    have h := abs_sub_le (value s) exact 0
    simp only [sub_zero] at h
    norm_num only [show (2 : ℝ)^(-53 : Int) = 1 / 9007199254740992 by norm_num] at herr
    nlinarith
  have htbound : |value ((l * d) * r)| ≤ 2 * t + mass := by
    have h := abs_sub_le (value ((l * d) * r)) (value l * value d * value r) 0
    simp only [sub_zero] at h
    change _ ≤ _ + t at h
    norm_num only [show (2 : ℝ)^(-53 : Int) = 1 / 9007199254740992 by norm_num] at hte
    nlinarith
  have hlim : |value s - value ((l * d) * r)| ≤ (2 : ℝ)^(1000 : Int) := by
    calc
      _ ≤ |value s| + |value ((l * d) * r)| := abs_sub _ _
      _ ≤ 4 * (mass + t) := by linarith
      _ ≤ 4 * (2 : ℝ) ^ (50 : Int) := mul_le_mul_of_nonneg_left hmass (by norm_num)
      _ = (2 : ℝ) ^ (52 : Int) := by norm_num
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hsub := Flare.Binary64.Nearest.sub_error_nearest s ((l * d) * r) hs ht.2.1 hlim
  refine ⟨ht.1, ht.2.1, hsub.1, ?_⟩
  have he : |(value s - value ((l * d) * r)) - (exact - value l * value d * value r)| ≤
      |value s - exact| + |value ((l * d) * r) - value l * value d * value r| := by
    have heq : (value s - value ((l * d) * r)) - (exact - value l * value d * value r) =
        (value s - exact) - (value ((l * d) * r) - value l * value d * value r) := by ring
    rw [heq]
    exact abs_sub _ _
  have hreal : |exact - value l * value d * value r| ≤ mass + t :=
    (abs_sub _ _).trans (add_le_add hexact le_rfl)
  have hactual := abs_sub_le (value s - value ((l * d) * r))
    (exact - value l * value d * value r) 0
  simp only [sub_zero] at hactual
  have htotal := abs_sub_le (value (s - (l * d) * r))
    (value s - value ((l * d) * r)) (exact - value l * value d * value r)
  have he' := hsub.2
  change _ ≤ (2 : ℝ)^(-53 : Int) * (|value s - value ((l * d) * r)| + η) at he'
  change _ ≤ (1001 / 1000 : ℝ) * ((k + 1 : Nat) + 4) * (2 : ℝ)^(-53 : Int) * (mass + t)
  norm_num only [show (2 : ℝ)^(-53 : Int) = 1 / 9007199254740992 by norm_num,
    Nat.cast_add, Nat.cast_one] at he' hte herr ⊢
  nlinarith

/-- Dividing a rounded residual by its stored pivot preserves a small
backward error after multiplication by that same pivot. -/
lemma gram_quotient_backward (k : Nat) (r d : Float) (exact mass : ℝ)
    (hk : k ≤ 11) (hr : r.isFinite = true) (hd : d.isFinite = true)
    (hdlo : (1 / 8 : ℝ) ≤ value d) (hdhi : value d ≤ 2048)
    (hmass : mass ≤ 4096) (hη : (2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int) ≤ mass)
    (hexact : |exact| ≤ mass)
    (herr : |value r - exact| ≤ (1001 / 1000 : ℝ) * (k + 4) * (2 : ℝ) ^ (-53 : Int) * mass)
    : (r / d).isFinite = true
      ∧ |value (r / d) * value d - exact|
        ≤ (1002 / 1000 : ℝ) * (k + 6) * (2 : ℝ) ^ (-53 : Int) * mass := by
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  have hη0 : 0 ≤ η := zpow_nonneg (by norm_num) _
  have hm0 : 0 ≤ mass := (abs_nonneg _).trans hexact
  have hk' : (k : ℝ) ≤ 11 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hkm := mul_le_mul_of_nonneg_right hk' hm0
  have hdk : 0 < value d := by linarith
  have htri := abs_sub_le (value r) exact 0
  simp only [sub_zero] at htri
  have hrb : |value r| ≤ 2 * mass := by
    norm_num only [show (2 : ℝ)^(-53 : Int) = 1 / 9007199254740992 by norm_num] at herr
    nlinarith
  have hq : |value r / value d| ≤ (2 : ℝ)^(1000 : Int) := by
    rw [abs_div, abs_of_pos hdk]
    calc
      _ ≤ 65536 := (div_le_iff₀ hdk).mpr (by linarith)
      _ = (2 : ℝ) ^ (16 : Int) := by norm_num
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hdv := Flare.Binary64.Nearest.div_error_nearest r d hr hd hdk.ne' hq
  refine ⟨hdv.1, ?_⟩
  have he := mul_le_mul_of_nonneg_right hdv.2 (abs_nonneg (value d))
  rw [← abs_mul] at he
  have heq : (value (r / d) - value r / value d) * value d = value (r / d) * value d - value r := by
    rw [sub_mul, div_mul_cancel₀ _ hdk.ne']
  rw [heq, abs_div, abs_of_pos hdk] at he
  have hrhs : (2 : ℝ)^(-53 : Int) * (|value r| / value d + η) * value d =
      (2 : ℝ)^(-53 : Int) * (|value r| + value d * η) := by field_simp
  change _ ≤ (2 : ℝ)^(-53 : Int) * (|value r| / value d + η) * value d at he
  rw [hrhs] at he
  have htotal := abs_sub_le (value (r / d) * value d) (value r) exact
  have hdη := mul_le_mul_of_nonneg_right hdhi hη0
  change (2 : ℝ)^(20 : Int) * η ≤ mass at hη
  norm_num only [show (2 : ℝ)^(20 : Int) = 1048576 by norm_num] at hη
  have hkm0 := mul_nonneg hk0 hm0
  norm_num only [show (2 : ℝ)^(-53 : Int) = 1 / 9007199254740992 by norm_num] at he herr ⊢
  nlinarith

/-- Proof-side extraction of either LDLᵀ residual loop. The diagonal pivot uses
identical row indices. `factor_eq` connects this extraction to the runtime. -/
def gramResidual (n upto : Nat) (lower diagonal : Array Float) (initial : Float) (i j : Nat)
    : Except Flare.Matrix.DenseError Float := do
  let mut s := initial
  for k in [:upto] do
    let product ← finite (entry n lower i k * diagonal.getD k 0.0)
    let term ← finite (product * entry n lower j k)
    s ← finite (s - term)
  return s

/-- A residual reads only the completed columns. Writes to its current column
cannot change its arithmetic or its exceptional-value checks. -/
lemma gramResidual_congr (n upto : Nat) (lower diagonal lower' diagonal' : Array Float)
    (initial : Float) (i j : Nat)
    (hl : ∀ k, k < upto → entry n lower i k = entry n lower' i k)
    (hd : ∀ k, k < upto → diagonal.getD k 0.0 = diagonal'.getD k 0.0)
    (hr : ∀ k, k < upto → entry n lower j k = entry n lower' j k)
    : gramResidual n upto lower diagonal initial i j
      = gramResidual n upto lower' diagonal' initial i j := by
  unfold gramResidual
  simp only [bind_pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one, ← List.range_eq_range']
  simp only [← forIn'_eq_forIn]
  apply List.forIn'_congr rfl rfl
  intro k hk s
  have hk' := List.mem_range.mp hk
  simp only [hl k hk', hd k hk', hr k hk']

/-- Proof-side extraction of the native column loop. -/
def factorColumn (n j : Nat) (a : Array Float) (f : Factor)
    : Except Flare.Matrix.DenseError Factor := do
  let pivot ← gramResidual n j f.lower f.diagonal (entry n a j j) j j
  unless 0.0 < pivot do
    throw .nonpositivePivot
  let diagonal := f.diagonal.set! j pivot
  let mut lower := f.lower.set! (j * n + j) 1.0
  for i in [j + 1:n] do
    let residual ← gramResidual n j lower diagonal (entry n a i j) i j
    let value ← finite (residual / pivot)
    lower := lower.set! (i * n + j) value
  return ⟨lower, diagonal⟩

/-- The native factorization expressed using its column and residual loops.
This is proof tooling; runtime callers still execute `Matrix.factor`. -/
def factorByResidual (n : Nat) (a : Array Float) : Except Flare.Matrix.DenseError Factor := do
  let mut lower := Array.replicate (n * n) 0.0
  let mut diagonal := Array.replicate n 0.0
  for j in [:n] do
    let f ← factorColumn n j a ⟨lower, diagonal⟩
    lower := f.lower
    diagonal := f.diagonal
  return ⟨lower, diagonal⟩

universe u v

private lemma bind_if {ε : Type u} {α β : Type v} (p : Prop) [Decidable p] (x y : Except ε α)
    (f : α → Except ε β)
    : (if p then x else y) >>= f = if p then x >>= f else y >>= f := by split <;> rfl

/-- Extracting the residual loops preserves the complete native operation
schedule, including every finite check and the positive-pivot rejection. -/
theorem factor_eq (n : Nat) (a : Array Float) : factor n a = factorByResidual n a := by
  unfold factor factorByResidual factorColumn gramResidual
  simp only [bind_assoc, pure_bind, bind_if]

private noncomputable def gramPrefix (n k : Nat) (lower diagonal : Array Float)
    (initial : Float) (i j : Nat)
    : ℝ :=
  value initial
  - ∑ t ∈ Finset.range k,
      value (entry n lower i t) * value (diagonal.getD t 0.0) * value (entry n lower j t)

private def ResidualState (n : Nat) (lower diagonal : Array Float) (initial : Float)
    (i j : Nat) (budget : Nat → ℝ) (k : Nat) (s : Float)
    : Prop :=
  s.isFinite = true ∧ |value s - gramPrefix n k lower diagonal initial i j| ≤ budget k

private lemma gramPrefix_bound (n k : Nat) (lower diagonal : Array Float)
    (initial : Float) (i j : Nat) (L D : Int)
    (hinit : |value initial| ≤ (2 : ℝ) ^ (2 * L + D))
    (hl : ∀ t, t < k → |value (entry n lower i t)| ≤ (2 : ℝ) ^ L)
    (hd : ∀ t, t < k → |value (diagonal.getD t 0.0)| ≤ (2 : ℝ) ^ D)
    (hr : ∀ t, t < k → |value (entry n lower j t)| ≤ (2 : ℝ) ^ L)
    : |gramPrefix n k lower diagonal initial i j| ≤ (k + 1 : Nat) * (2 : ℝ) ^ (2 * L + D) := by
  have hterm (t : Nat) (ht : t < k) : |value (entry n lower i t) * value (diagonal.getD t 0.0) *
      value (entry n lower j t)| ≤ (2 : ℝ)^(2 * L + D) := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ ((2 : ℝ) ^ L * (2 : ℝ) ^ D) * (2 : ℝ) ^ L :=
        mul_le_mul
          (mul_le_mul (hl t ht) (hd t ht) (abs_nonneg _)
            (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)) (hr t ht) (abs_nonneg _)
          (mul_nonneg (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
            (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _))
      _ = _ := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 1
        omega
  unfold gramPrefix
  calc
    _ ≤ |value initial|
        + |∑ t ∈ Finset.range k,
            value (entry n lower i t) * value (diagonal.getD t 0.0) * value (entry n lower j t)| :=
      abs_sub _ _
    _ ≤ (2 : ℝ) ^ (2 * L + D) + ∑ _t ∈ Finset.range k, (2 : ℝ) ^ (2 * L + D) :=
      add_le_add hinit
        ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun t ht => hterm t (Finset.mem_range.mp ht)))
    _ = _ := by simp; ring

private theorem gramResidual_triple_of_step (n upto : Nat) (lower diagonal : Array Float)
    (initial : Float) (i j : Nat) (budget : Nat → ℝ)
    (hinit : initial.isFinite = true) (hzero : 0 ≤ budget 0)
    (step
      : ∀ k s,
          k < upto
          → ResidualState n lower diagonal initial i j budget k s
          → (entry n lower i k * diagonal.getD k 0.0).isFinite = true
            ∧ ((entry n lower i k * diagonal.getD k 0.0) * entry n lower j k).isFinite = true
            ∧ (s - (entry n lower i k * diagonal.getD k 0.0) * entry n lower j k).isFinite = true
            ∧ |value (s - (entry n lower i k * diagonal.getD k 0.0) * entry n lower j k)
                - (gramPrefix n k lower diagonal initial i j
                    - value (entry n lower i k)
                      * value (diagonal.getD k 0.0)
                      * value (entry n lower j k))|
              ≤ budget (k + 1))
    : ⦃⌜True⌝
      ⦄ gramResidual n upto lower diagonal initial i j
      ⦃⇓ s => ⌜ResidualState n lower diagonal initial i j budget upto s⌝⦄ := by
  unfold gramResidual
  apply (Specification.except_iff _ _ _).mpr
  vcgen [-Flare.Matrix.Storage.finite_wp_spec, Flare.Matrix.Storage.finite_wp_exact]
    invariants
      | inv1 => fun xs _ s => ResidualState n lower diagonal initial i j budget xs.length s
  all_goals simp_all only [SPred.down_pure_nil]
  all_goals subst_vars
  all_goals first
  | (solve |
    rename_i pref k suff hlist s hs
    have hk' := Flare.Matrix.Storage.forIn_range_current hlist
    have hh := step k s hk'.2 (by simpa only [hk'.1] using hs)
    first
    | exact hh.1
    | exact hh.2.1
    | exact hh.2.2.1
    | refine ⟨hh.2.2.1, ?_⟩
      have he : gramPrefix n (k + 1) lower diagonal initial i j =
          gramPrefix n k lower diagonal initial i j -
            value (entry n lower i k) * value (diagonal.getD k 0.0) * value (entry n lower j k)
              := by
        simp only [gramPrefix, Finset.sum_range_succ]
        ring
      simpa only [List.length_append, List.length_singleton, ← hk'.1, he] using hh.2.2.2)
  | (solve |
    exact ⟨hinit, by simpa [gramPrefix] using hzero⟩)
  | (solve |
    rename_i s hs
    simpa using hs)

private theorem gramResidual_triple (n upto : Nat) (lower diagonal : Array Float)
    (initial : Float) (i j : Nat) (L D : Int)
    (hL : 0 ≤ L) (hD : 0 ≤ D) (hE : 2 * L + D ≤ 1000) (hk : upto ≤ 12)
    (hfinite : lower.all Float.isFinite = true) (hdiag : diagonal.all Float.isFinite = true)
    (hinit : initial.isFinite = true) (hib : |value initial| ≤ (2 : ℝ) ^ (2 * L + D))
    (hl : ∀ t, t < upto → |value (entry n lower i t)| ≤ (2 : ℝ) ^ L)
    (hd : ∀ t, t < upto → |value (diagonal.getD t 0.0)| ≤ (2 : ℝ) ^ D)
    (hr : ∀ t, t < upto → |value (entry n lower j t)| ≤ (2 : ℝ) ^ L)
    : ⦃⌜True⌝
      ⦄ gramResidual n upto lower diagonal initial i j
      ⦃
        ⇓ s
          =>
              ⌜
                ResidualState n lower diagonal initial i j (fun k => k * (2 : ℝ) ^ (2 * L + D - 44))
                  upto s
                ⌝
        ⦄ := by
  have step (k : Nat) (s : Float) (hku : k < upto)
      (hs : ResidualState n lower diagonal initial i j (fun k => k * (2 : ℝ)^(2 * L + D - 44)) k s)
        :=
    gram_step L D k (entry n lower i k) (diagonal.getD k 0.0) (entry n lower j k) s
      (gramPrefix n k lower diagonal initial i j) hL hD hE (by omega)
      (Flare.Matrix.Storage.getD_finite _ _ hfinite)
      (Flare.Matrix.Storage.getD_finite _ _ hdiag)
      (Flare.Matrix.Storage.getD_finite _ _ hfinite) hs.1 (hl k hku) (hd k hku) (hr k hku)
      (gramPrefix_bound n k lower diagonal initial i j L D hib (fun t ht => hl t (by omega))
        (fun t ht => hd t (by omega)) (fun t ht => hr t (by omega))) hs.2
  exact gramResidual_triple_of_step n upto lower diagonal initial i j _ hinit (by simp) step

/-- The actual residual arithmetic succeeds and has an explicit absolute error
bound from the supplied finite factor entries. The bound covers all loop terms. -/
theorem gramResidual_accuracy (n upto : Nat) (lower diagonal : Array Float)
    (initial : Float) (i j : Nat) (L D : Int)
    (hL : 0 ≤ L) (hD : 0 ≤ D) (hE : 2 * L + D ≤ 1000) (hk : upto ≤ 12)
    (hfinite : lower.all Float.isFinite = true) (hdiag : diagonal.all Float.isFinite = true)
    (hinit : initial.isFinite = true) (hib : |value initial| ≤ (2 : ℝ) ^ (2 * L + D))
    (hl : ∀ t, t < upto → |value (entry n lower i t)| ≤ (2 : ℝ) ^ L)
    (hd : ∀ t, t < upto → |value (diagonal.getD t 0.0)| ≤ (2 : ℝ) ^ D)
    (hr : ∀ t, t < upto → |value (entry n lower j t)| ≤ (2 : ℝ) ^ L)
    : ∃ s,
        gramResidual n upto lower diagonal initial i j = .ok s
        ∧ s.isFinite = true
        ∧ |value s
            - (value initial
                - ∑ t ∈ Finset.range upto,
                    value (entry n lower i t)
                    * value (diagonal.getD t 0.0)
                    * value (entry n lower j t))|
          ≤ upto * (2 : ℝ) ^ (2 * L + D - 44) := by
  have h := gramResidual_triple n upto lower diagonal initial i j L D
    hL hD hE hk hfinite hdiag hinit hib hl hd hr
  cases he : gramResidual n upto lower diagonal initial i j with
  | error e =>
      rw [he] at h; exact False.elim (h True.intro)
  | ok s =>
      rw [he] at h
      exact ⟨s, rfl, h True.intro⟩

/-- Native residual error measured against the accumulated absolute term mass.
Unlike a per-term maximum, this bound exploits the energy bound of an LDLᵀ
factor and charges product rounding only once for each actual term. -/
theorem gramResidual_relative_accuracy (n upto : Nat) (lower diagonal : Array Float)
    (initial : Float) (i j : Nat) (hk : upto ≤ 12)
    (hfinite : lower.all Float.isFinite = true) (hdiag : diagonal.all Float.isFinite = true)
    (hinit : initial.isFinite = true) (hib : |value initial| ≤ 1024)
    (hl : ∀ t, t < upto → |value (entry n lower i t)| ≤ 128)
    (hd : ∀ t, t < upto → |value (diagonal.getD t 0.0)| ≤ 2048)
    (hr : ∀ t, t < upto → |value (entry n lower j t)| ≤ 128)
    : ∃ s,
        gramResidual n upto lower diagonal initial i j = .ok s
        ∧ s.isFinite = true
        ∧ |value s
            - (value initial
                - ∑ t ∈ Finset.range upto,
                    value (entry n lower i t)
                    * value (diagonal.getD t 0.0)
                    * value (entry n lower j t))|
          ≤ (1001 / 1000 : ℝ) * (upto + 4) * (2 : ℝ) ^ (-53 : Int)
            * (|value initial|
                + ∑ t ∈ Finset.range upto,
                    |value (entry n lower i t)
                      * value (diagonal.getD t 0.0)
                      * value (entry n lower j t)|
                + (2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int)) := by
  let term (t : Nat) := value (entry n lower i t) * value (diagonal.getD t 0.0) *
    value (entry n lower j t)
  let mass (k : Nat) := |value initial| + ∑ t ∈ Finset.range k, |term t| +
    (2 : ℝ)^(20 : Int) * (2 : ℝ)^(-1022 : Int)
  have hmass0 (k : Nat) : (2 : ℝ)^(20 : Int) * (2 : ℝ)^(-1022 : Int) ≤ mass k := by
    dsimp [mass]
    linarith [abs_nonneg (value initial), Finset.sum_nonneg (fun t (_ : t ∈ Finset.range k) =>
      abs_nonneg (term t))]
  have hmass_succ (k : Nat) : mass (k + 1) = mass k + |term k| := by
    simp only [mass, Finset.sum_range_succ]; ring
  have hbound (k : Nat) (hku : k ≤ upto) : mass k ≤ (2 : ℝ)^(50 : Int) := by
    have ht (t : Nat) (ht : t ∈ Finset.range k) : |term t| ≤ (33554432 : ℝ) := by
      have ht' : t < upto := lt_of_lt_of_le (Finset.mem_range.mp ht) hku
      dsimp [term]; rw [abs_mul, abs_mul]
      exact (mul_le_mul (mul_le_mul (hl t ht') (hd t ht') (abs_nonneg _)
        (by norm_num)) (hr t ht') (abs_nonneg _) (by norm_num)).trans (by norm_num)
    have hsum := Finset.sum_le_sum ht
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hk' : (k : ℝ) ≤ 12 := by exact_mod_cast hku.trans hk
    have hη : (2 : ℝ)^(-1022 : Int) ≤ 1 := (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show
      (-1022 : Int) ≤ 0 by omega)).trans (by norm_num)
    dsimp only [mass]
    norm_num only [show (2 : ℝ)^(20 : Int) = 1048576 by norm_num,
      show (2 : ℝ)^(50 : Int) = 1125899906842624 by norm_num]
    linarith
  have hprefix (k : Nat) : |gramPrefix n k lower diagonal initial i j| ≤ mass k := by
    dsimp only [gramPrefix, mass]
    calc
      _ ≤ |value initial| + |∑ t ∈ Finset.range k, term t| := abs_sub _ _
      _ ≤ |value initial| + ∑ t ∈ Finset.range k, |term t| :=
        add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  let budget (k : Nat) := residualBudget k (mass k)
  have hzero : 0 ≤ budget 0 := by
    dsimp [budget, residualBudget]
    exact mul_nonneg (by positivity) ((by positivity : 0 ≤ (2 : ℝ)^(20 : Int) * (2 : ℝ)^(-1022 :
      Int)).trans (hmass0 0))
  have step (k : Nat) (s : Float) (hku : k < upto)
      (hs : ResidualState n lower diagonal initial i j budget k s) :=
    gram_step_relative k (entry n lower i k) (diagonal.getD k 0.0) (entry n lower j k) s
      (gramPrefix n k lower diagonal initial i j) (mass k) (by omega)
      (Flare.Matrix.Storage.getD_finite _ _ hfinite)
      (Flare.Matrix.Storage.getD_finite _ _ hdiag)
      (Flare.Matrix.Storage.getD_finite _ _ hfinite) hs.1
      (hl k hku) (hd k hku) (hr k hku)
      (by rw [← hmass_succ]; exact hbound (k + 1) (by omega)) (hmass0 k) (hprefix k) hs.2
  have h := gramResidual_triple_of_step n upto lower diagonal initial i j budget hinit hzero
    (fun k s hku hs => by
      have hh := step k s hku hs
      refine ⟨hh.1, hh.2.1, hh.2.2.1, ?_⟩
      simpa only [budget, residualBudget, hmass_succ, term] using hh.2.2.2)
  cases he : gramResidual n upto lower diagonal initial i j with
  | error e =>
      rw [he] at h; exact False.elim (h True.intro)
  | ok s =>
      rw [he] at h
      exact ⟨s, rfl, h True.intro⟩

/-- Exact residual of the stored factor prefix. This is a proof interpretation
of the current Float factors, not an independently executed factorization. -/
noncomputable def schurResidual (n upto : Nat) (a lower diagonal : Array Float)
    : _root_.Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    value (entry n a i.val j.val)
    - ∑ k ∈ Finset.range upto,
        value (entry n lower i.val k) * value (diagonal.getD k 0.0) * value (entry n lower j.val k)

/-- Finite bounded factors make every native Schur-residual evaluation succeed.
The local error is at most 2⁻¹⁴ for up to twelve terms, including underflow. -/
theorem schurResidual_accuracy (n upto : Nat) (a lower diagonal : Array Float)
    (hn : upto ≤ 12) (ha : a.all Float.isFinite = true)
    (hl : lower.all Float.isFinite = true) (hd : diagonal.all Float.isFinite = true)
    (hab : ∀ i j : Fin n, |value (entry n a i.val j.val)| ≤ 1024)
    (hlb : ∀ i : Fin n, ∀ k, k < upto → |value (entry n lower i.val k)| ≤ 128)
    (hdb : ∀ k, k < upto → |value (diagonal.getD k 0.0)| ≤ 2048) (i j : Fin n)
    : ∃ s,
        gramResidual n upto lower diagonal (entry n a i.val j.val) i.val j.val = .ok s
        ∧ s.isFinite = true
        ∧ |value s - schurResidual n upto a lower diagonal i j| ≤ (2 : ℝ) ^ (-14 : Int) := by
  obtain ⟨s, he, hf, herr⟩ := gramResidual_accuracy n upto lower diagonal
    (entry n a i.val j.val) i.val j.val 7 11 (by norm_num) (by norm_num) (by norm_num) hn hl hd
    (Flare.Matrix.Storage.getD_finite _ _ ha) ((hab i j).trans (by norm_num))
    (by simpa only [show (2 : ℝ)^(7 : Int) = 128 by norm_num] using hlb i)
    (by simpa only [show (2 : ℝ)^(11 : Int) = 2048 by norm_num] using hdb)
    (by simpa only [show (2 : ℝ)^(7 : Int) = 128 by norm_num] using hlb j)
  refine ⟨s, he, hf, herr.trans ?_⟩
  have hk : (upto : ℝ) ≤ 12 := by exact_mod_cast hn
  norm_num only [zpow_neg, zpow_ofNat, inv_pow, pow_succ, pow_zero]
  linarith

/-- With nonnegative stored pivots, subtraction of the prefix Gram matrix
cannot increase a Schur diagonal. -/
lemma schurResidual_diagonal_le (n upto : Nat) (a lower diagonal : Array Float)
    (hd : ∀ k, k < upto → 0 ≤ value (diagonal.getD k 0.0)) (i : Fin n)
    : schurResidual n upto a lower diagonal i i ≤ value (entry n a i.val i.val) := by
  apply sub_le_self
  apply Finset.sum_nonneg
  intro k hk
  have he : value (entry n lower i.val k) * value (diagonal.getD k 0.0) *
      value (entry n lower i.val k) = value (diagonal.getD k 0.0) * (value (entry n lower i.val
        k))^2 := by ring
  rw [he]
  exact mul_nonneg (hd k (Finset.mem_range.mp hk)) (sq_nonneg _)

/-- A safely conditioned exact Schur pivot tolerates the error from its native
residual loop. The runtime comparison is proved true through binary64 order. -/
theorem pivot_positive (pivot : Float) (exact : ℝ)
    (hf : pivot.isFinite = true) (hlo : (5 / 32 : ℝ) ≤ exact) (hhi : exact ≤ 1024)
    (he : |value pivot - exact| ≤ (2 : ℝ) ^ (-10 : Int))
    : 0.0 < pivot ∧ (1 / 8 : ℝ) ≤ value pivot ∧ |value pivot| ≤ 2048 := by
  have hε : (2 : ℝ)^(-10 : Int) = 1 / 1024 := by norm_num
  rw [hε] at he
  have h := abs_le.mp he
  have hp : 0 < value pivot := by linarith
  refine ⟨?_, by linarith, ?_⟩
  · apply (Flare.Binary64.Order.lt_iff 0.0 pivot (by decide) hf).mpr
    exact hp
  · rw [abs_of_pos hp]
    linarith

/-- The rounded off-diagonal factor remains bounded and has a small backward
error. The exact residual's quadratic bound comes from the positive semidefinite
Schur complement; it does not presume a bound on the computed quotient. -/
theorem column_division (residual pivot : Float) (exactResidual exactPivot : ℝ)
    (hr : residual.isFinite = true) (hp : pivot.isFinite = true)
    (hlo : (5 / 32 : ℝ) ≤ exactPivot) (hhi : exactPivot ≤ 1024)
    (hsq : exactResidual ^ 2 ≤ 1024 * exactPivot)
    (her : |value residual - exactResidual| ≤ (2 : ℝ) ^ (-14 : Int))
    (hep : |value pivot - exactPivot| ≤ (2 : ℝ) ^ (-14 : Int))
    : (residual / pivot).isFinite = true
      ∧ |value (residual / pivot)| ≤ 128
      ∧ |value (residual / pivot) * value pivot - exactResidual| ≤ (2 : ℝ) ^ (-13 : Int) := by
  have hε : (2 : ℝ)^(-14 : Int) ≤ (2 : ℝ)^(-10 : Int) := by norm_num
  have hpb := pivot_positive pivot exactPivot hp hlo hhi (hep.trans hε)
  have hpp : 0 < value pivot := by linarith [hpb.2.1]
  have hpabs : |value pivot| = value pivot := abs_of_pos hpp
  have hrb : |exactResidual| ≤ 96 * exactPivot := by
    have hsq' : |exactResidual|^2 = exactResidual^2 := sq_abs _
    have hxp : 0 ≤ exactPivot := by linarith
    have haux : 1024 * exactPivot ≤ (96 * exactPivot)^2 := by nlinarith
    nlinarith [abs_nonneg exactResidual]
  have her' := abs_le.mp her
  have hep' := abs_le.mp hep
  norm_num only [zpow_neg, zpow_ofNat, inv_pow, pow_succ, pow_zero] at her' hep'
  have hquot : |value residual / value pivot| ≤ 100 := by
    rw [abs_div, hpabs]
    apply (div_le_iff₀ hpp).mpr
    have htri := abs_sub_le (value residual) exactResidual 0
    simp only [sub_zero] at htri
    have herr := her
    norm_num only [zpow_neg, zpow_ofNat, inv_pow, pow_succ, pow_zero] at herr
    nlinarith
  have hdiv := Flare.Binary64.Division.div_error residual pivot 7 hr hp hpp.ne'
    (by norm_num) (by norm_num) (hquot.trans (by norm_num))
  refine ⟨hdiv.1, ?_, ?_⟩
  · have htri := abs_sub_le (value (residual / pivot)) (value residual / value pivot) 0
    simp only [sub_zero] at htri
    norm_num only [show (7 : Int) - 51 = -44 by omega, zpow_neg, zpow_ofNat,
      inv_pow, pow_succ, pow_zero] at hdiv
    linarith [hdiv.2]
  · have hid : value (residual / pivot) * value pivot - value residual =
        (value (residual / pivot) - value residual / value pivot) * value pivot := by
      field_simp
    have hback : |value (residual / pivot) * value pivot - value residual| ≤
        (2 : ℝ)^(-44 : Int) * 2048 := by
      rw [hid, abs_mul]
      exact mul_le_mul hdiv.2 hpb.2.2 (abs_nonneg _) (by positivity)
    have htri := abs_sub_le (value (residual / pivot) * value pivot) (value residual) exactResidual
    have hh := htri.trans (add_le_add hback her)
    exact hh.trans (by norm_num)

private def ColumnStorage (n j : Nat) (original a : Array Float) : Prop :=
  a.size = n * n
  ∧ a.all Float.isFinite = true
  ∧ ∀ i k, i < n → k < n → k ≠ j → entry n a i k = entry n original i k

private lemma columnStorage_set (n j : Nat) (original a : Array Float) (i : Nat) (x : Float)
    (h : ColumnStorage n j original a) (hi : i < n) (hj : j < n) (hx : x.isFinite = true)
    : ColumnStorage n j original (a.set! (i * n + j) x) := by
  refine ⟨(Array.size_set! ..).trans h.1, Flare.Matrix.Storage.all_set _ _ _ h.2.1 hx, ?_⟩
  intro r k hr hk hkj
  rw [Flare.Matrix.Storage.entry_set n a i j r k x h.1 hi hj hk,
    ite_eq_right (fun he => hkj he.2)]
  exact h.2.2 r k hr hk hkj

private def fillColumn (n j : Nat) (a diagonal : Array Float) (pivot : Float)
    (xs : List Nat) (lower : Array Float)
    : Except Flare.Matrix.DenseError (Array Float) :=
  xs.foldlM
    (fun lower i => do
      let residual ← gramResidual n j lower diagonal (entry n a i j) i j
      let value ← finite (residual / pivot)
      return lower.set! (i * n + j) value)
    lower

private lemma fillColumn_success (n j : Nat) (a original diagonal : Array Float) (pivot : Float)
    (P : Nat → Float → Prop) (xs : List Nat) (lower : Array Float) (hj : j < n)
    (hxs : ∀ i ∈ xs, j < i ∧ i < n) (hstart : ColumnStorage n j original lower)
    (hstep
      : ∀ i,
          j < i
          → i < n
          → ∀ l,
              ColumnStorage n j original l
              → ∃ x,
                  (do
                    let residual ← gramResidual n j l diagonal (entry n a i j) i j
                    finite (residual / pivot))
                    = .ok x
                  ∧ x.isFinite = true
                  ∧ P i x)
    : ∃ result,
        fillColumn n j a diagonal pivot xs lower = .ok result
        ∧ ColumnStorage n j original result
        ∧ (∀ i ∈ xs, P i (entry n result i j))
        ∧ (∀ i, i < n → i ∉ xs → entry n result i j = entry n lower i j) := by
  induction xs generalizing lower with
  | nil => exact ⟨lower, rfl, hstart, by simp, by simp⟩
  | cons i xs ih =>
      obtain ⟨hji, hin⟩ := hxs i (by simp)
      obtain ⟨x, hx, hxf, hxp⟩ := hstep i hji hin lower hstart
      have hnext := columnStorage_set n j original lower i x hstart hin hj hxf
      obtain ⟨result, he, hs, hvalues, hsame⟩ := ih (lower.set! (i * n + j) x)
        (fun k hk => hxs k (by simp [hk])) hnext
      refine ⟨result, ?_, hs, ?_, ?_⟩
      · unfold fillColumn at he ⊢
        rw [List.foldlM_cons]
        have hcall : (do
            let residual ← gramResidual n j lower diagonal (entry n a i j) i j
            let value ← finite (residual / pivot)
            pure (lower.set! (i * n + j) value)) = .ok (lower.set! (i * n + j) x) := by
          have hh := congrArg (fun q : Except Flare.Matrix.DenseError Float =>
            q >>= fun v => Except.ok (lower.set! (i * n + j) v)) hx
          simp only [bind_assoc] at hh
          simpa only [bind, Except.bind, pure, Except.pure] using hh
        rw [hcall]
        exact he
      · intro k hk
        by_cases hmem : k ∈ xs
        · exact hvalues k hmem
        · have hki : k = i := (List.mem_cons.mp hk).resolve_right hmem
          subst k
          rw [hsame i hin hmem, Flare.Matrix.Storage.entry_set n lower i j i j x hstart.1 hin hj hj,
            ite_eq_left ⟨rfl, rfl⟩]
          exact hxp
      · intro k hk hnot
        have hki : k ≠ i := fun he => hnot (by simp [he])
        have hmem : k ∉ xs := fun he => hnot (by simp [he])
        rw [hsame k hk hmem, Flare.Matrix.Storage.entry_set n lower i j k j x hstart.1 hin hj hj,
          ite_eq_right (fun he => hki he.1)]

private lemma factorColumn_eq (n j : Nat) (a : Array Float) (f : Factor)
    : factorColumn n j a f
      = (do
          let pivot ← gramResidual n j f.lower f.diagonal (entry n a j j) j j
          unless 0.0 < pivot do
            throw .nonpositivePivot
          let lower ←
            fillColumn n j a (f.diagonal.set! j pivot) pivot
              (List.range' (j + 1) (n - (j + 1))) (f.lower.set! (j * n + j) 1.0)
          return ⟨lower, f.diagonal.set! j pivot⟩) := by
  unfold factorColumn fillColumn
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_one_sub_one, Nat.div_one]
  simp only [← map_eq_pure_bind, ← map_bind, List.forIn_yield_eq_foldlM]

/-- One complete native LDLᵀ column succeeds with a bounded backward error
when its exact Schur pivot has a margin and its residuals satisfy the PSD
quadratic bound. All previous columns are preserved. These are local induction
hypotheses on the stored prefix; the full factorization must establish them. -/
theorem factorColumn_accuracy (n : Nat) (j : Fin n) (a : Array Float) (f : Factor)
    (hn : n ≤ 12) (ha : a.all Float.isFinite = true)
    (hls : f.lower.size = n * n) (hds : f.diagonal.size = n)
    (hl : f.lower.all Float.isFinite = true) (hd : f.diagonal.all Float.isFinite = true)
    (hab : ∀ i k : Fin n, |value (entry n a i.val k.val)| ≤ 1024)
    (hlb : ∀ i : Fin n, ∀ k, k < j.val → |value (entry n f.lower i.val k)| ≤ 128)
    (hdb : ∀ k, k < j.val → |value (f.diagonal.getD k 0.0)| ≤ 2048)
    (hdp : ∀ k, k < j.val → 0 ≤ value (f.diagonal.getD k 0.0))
    (hlo : (5 / 32 : ℝ) ≤ schurResidual n j.val a f.lower f.diagonal j j)
    (hsq
      : ∀ i : Fin n,
          j.val < i.val
          → (schurResidual n j.val a f.lower f.diagonal i j) ^ 2
            ≤ 1024 * schurResidual n j.val a f.lower f.diagonal j j)
    : ∃ result,
        factorColumn n j.val a f = .ok result
        ∧ result.lower.size = n * n
        ∧ result.diagonal.size = n
        ∧ result.lower.all Float.isFinite = true
        ∧ result.diagonal.all Float.isFinite = true
        ∧ entry n result.lower j.val j.val = 1.0
        ∧ (1 / 8 : ℝ) ≤ value (result.diagonal.getD j.val 0.0)
        ∧ |value (result.diagonal.getD j.val 0.0)| ≤ 2048
        ∧ |value (result.diagonal.getD j.val 0.0) - schurResidual n j.val a f.lower f.diagonal j j|
          ≤ (2 : ℝ) ^ (-14 : Int)
        ∧ gramResidual n j.val f.lower f.diagonal (entry n a j.val j.val) j.val j.val
          = .ok (result.diagonal.getD j.val 0.0)
        ∧ (∀ i k : Fin n, k ≠ j → entry n result.lower i.val k.val = entry n f.lower i.val k.val)
        ∧ (∀ i : Fin n,
            i.val < j.val → entry n result.lower i.val j.val = entry n f.lower i.val j.val)
        ∧ (∀ k, k ≠ j.val → result.diagonal.getD k 0.0 = f.diagonal.getD k 0.0)
        ∧ (∀ i : Fin n,
            j.val < i.val
            → |value (entry n result.lower i.val j.val)| ≤ 128
              ∧ |value (entry n result.lower i.val j.val) * value (result.diagonal.getD j.val 0.0)
                  - schurResidual n j.val a f.lower f.diagonal i j|
                ≤ (2 : ℝ) ^ (-13 : Int)
              ∧ ∃ r,
                  gramResidual n j.val f.lower f.diagonal (entry n a i.val j.val) i.val j.val
                    = .ok r
                  ∧ entry n result.lower i.val j.val = r / result.diagonal.getD j.val 0.0) := by
  have residual (i : Fin n) := schurResidual_accuracy n j.val a f.lower f.diagonal
    (by omega) ha hl hd hab hlb hdb i j
  obtain ⟨pivot, hpivot, hpf, hpe⟩ := residual j
  have hhi : schurResidual n j.val a f.lower f.diagonal j j ≤ 1024 :=
    (schurResidual_diagonal_le n j.val a f.lower f.diagonal hdp j).trans
      ((le_abs_self _).trans (hab j j))
  have hpositive := pivot_positive pivot _ hpf hlo hhi (hpe.trans (by norm_num))
  let diagonal := f.diagonal.set! j.val pivot
  have hdiag : diagonal.getD j.val 0.0 = pivot := by
    simp [diagonal, Array.set!_eq_setIfInBounds, show j.val < f.diagonal.size by omega]
  have hdiag_other (k : Nat) (hk : k ≠ j.val) : diagonal.getD k 0.0 = f.diagonal.getD k 0.0 := by
    simp only [diagonal, Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_ne hk.symm]
  have hstart : ColumnStorage n j.val f.lower (f.lower.set! (j.val * n + j.val) 1.0) :=
    columnStorage_set n j.val f.lower f.lower j.val 1.0 ⟨hls, hl, by intros; rfl⟩
      j.isLt j.isLt (by decide)
  let P (i : Nat) (x : Float) := |value x| ≤ 128 ∧
    |value x * value pivot - gramPrefix n j.val f.lower f.diagonal (entry n a i j.val) i j.val| ≤
      (2 : ℝ)^(-13 : Int) ∧
      ∃ r, gramResidual n j.val f.lower f.diagonal (entry n a i j.val) i j.val = .ok r ∧ x = r /
        pivot
  have hstep (i : Nat) (hji : j.val < i) (hin : i < n) (l : Array Float)
      (hs : ColumnStorage n j.val f.lower l) :
      ∃ x, (do
        let r ← gramResidual n j.val l diagonal (entry n a i j.val) i j.val
        finite (r / pivot)) = .ok x ∧ x.isFinite = true ∧ P i x := by
    have he := gramResidual_congr n j.val l diagonal f.lower f.diagonal (entry n a i j.val) i j.val
      (fun k hk => hs.2.2 i k hin (by omega) (by omega))
      (fun k hk => hdiag_other k (by omega))
      (fun k hk => hs.2.2 j.val k j.isLt (by omega) (by omega))
    obtain ⟨r, hr, hrf, hre⟩ := residual ⟨i, hin⟩
    have hdiv := column_division r pivot _ _ hrf hpf hlo hhi (hsq ⟨i, hin⟩ hji) hre hpe
    refine ⟨r / pivot, ?_, hdiv.1, hdiv.2.1, hdiv.2.2, r, hr, rfl⟩
    rw [he, hr]
    change finite (r / pivot) = .ok (r / pivot)
    simp only [finite, hdiv.1, ↓reduceIte]
  obtain ⟨lower, he, hs, hvalues, hsame⟩ := fillColumn_success n j.val a f.lower diagonal pivot P
    (List.range' (j.val + 1) (n - (j.val + 1))) (f.lower.set! (j.val * n + j.val) 1.0)
    j.isLt (by intro i hi; simp only [List.mem_range'] at hi; omega) hstart hstep
  refine ⟨⟨lower, diagonal⟩, ?_, hs.1, (Array.size_set! ..).trans hds, hs.2.1,
    Flare.Matrix.Storage.all_set _ _ _ hd hpf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hdiag_other, ?_⟩
  · rw [factorColumn_eq, hpivot]
    dsimp only [diagonal] at he
    simp only [bind, Except.bind, hpositive.1, ↓reduceIte, he]
    rfl
  · rw [hsame j.val j.isLt (by simp),
      Flare.Matrix.Storage.entry_set n f.lower j.val j.val j.val j.val 1.0 hls j.isLt j.isLt j.isLt]
    simp
  · simpa only [hdiag] using hpositive.2.1
  · simpa only [hdiag] using hpositive.2.2
  · simpa only [hdiag] using hpe
  · simpa only [hdiag] using hpivot
  · intro i k hk
    exact hs.2.2 i.val k.val i.isLt k.isLt (fun he => hk (Fin.ext he))
  · intro i hi
    rw [hsame i.val i.isLt (by
      simp only [List.mem_range']
      rintro ⟨k, _, he⟩
      omega), Flare.Matrix.Storage.entry_set n f.lower j.val j.val i.val j.val 1.0
        hls j.isLt j.isLt j.isLt, ite_eq_right (by omega)]
  · intro i hi
    have hv := hvalues i.val (by
      rw [List.mem_range']
      refine ⟨i.val - (j.val + 1), ?_, ?_⟩ <;> have := i.isLt <;> omega)
    simpa only [hdiag, P, gramPrefix, schurResidual] using hv

end Flare.Matrix.Factorization
