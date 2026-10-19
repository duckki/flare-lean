module

public import Flare.Analysis.NumericalBounds
public import Mathlib.Analysis.Real.Sqrt

/-! Exact identities for Jacobi plane rotations. These real-arithmetic identities
provide the reference for separately rounded native rotation operations;
spectral accuracy requires the corresponding floating-point bounds. -/

@[expose] public section

namespace Flare.Analysis.Jacobi

/-- Real interpretation of the sign choice in the native rotation formula.
In particular, the zero branch chooses positive one. -/
noncomputable def tangent (τ : ℝ) : ℝ :=
  (if τ < 0 then -1 else 1) / (|τ| + Real.sqrt (1 + τ ^ 2))

/-- The stable tangent formula is defined for every real τ, has magnitude at
most one, and solves the quadratic needed to annihilate the selected pivot. -/
theorem tangent_properties (τ : ℝ)
    : 0 < |τ| + Real.sqrt (1 + τ ^ 2)
      ∧ |tangent τ| ≤ 1
      ∧ tangent τ ^ 2 + 2 * τ * tangent τ = 1 := by
  have hpos : 0 < 1 + τ ^ 2 := by nlinarith [sq_nonneg τ]
  have hspos := Real.sqrt_pos.mpr hpos
  have hs := Real.sq_sqrt hpos.le
  have hsone : 1 ≤ Real.sqrt (1 + τ ^ 2) := by
    nlinarith [sq_nonneg τ]
  have hd : 0 < |τ| + Real.sqrt (1 + τ ^ 2) :=
    add_pos_of_nonneg_of_pos (abs_nonneg τ) hspos
  refine ⟨hd, ?_, ?_⟩
  · unfold tangent
    rw [abs_div, abs_of_pos hd]
    have he : |(if τ < 0 then -1 else 1 : ℝ)| = 1 := by split <;> norm_num
    rw [he]
    exact (div_le_one hd).mpr (by linarith [abs_nonneg τ])
  · unfold tangent
    split_ifs with hτ
    · rw [abs_of_neg hτ] at hd ⊢
      field_simp [ne_of_gt hd]
      nlinarith
    · rw [abs_of_nonneg (le_of_not_gt hτ)] at hd ⊢
      field_simp [ne_of_gt hd]
      nlinarith

/-- The cosine and sine computed from an exact tangent form a unit rotation. -/
theorem rotation_unit (t : ℝ)
    : let c := 1 / Real.sqrt (1 + t ^ 2)
      let s := t * c
      c ^ 2 + s ^ 2 = 1 := by
  have hp : 0 < 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hs := Real.sq_sqrt hp.le
  have hz := ne_of_gt (Real.sqrt_pos.mpr hp)
  dsimp only
  field_simp
  nlinarith

/-- Exact annihilation of the off-diagonal entry, including equal diagonals.
The diagonal updates `a - t*b` and `d + t*b` used by the native schedule are
the diagonal entries of that same orthogonal similarity transformation. -/
theorem pivot_rotation (a b d : ℝ) (hb : b ≠ 0)
    : let t := tangent ((d - a) / (2 * b))
      let c := 1 / Real.sqrt (1 + t ^ 2)
      let s := t * c
      c ^ 2 + s ^ 2 = 1
      ∧ c * s * (a - d) + (c ^ 2 - s ^ 2) * b = 0
      ∧ c ^ 2 * a - 2 * c * s * b + s ^ 2 * d = a - t * b
      ∧ s ^ 2 * a + 2 * c * s * b + c ^ 2 * d = d + t * b := by
  dsimp only
  let t := tangent ((d - a) / (2 * b))
  let c := 1 / Real.sqrt (1 + t ^ 2)
  have ht := (tangent_properties ((d - a) / (2 * b))).2.2
  have he : b * t ^ 2 + (d - a) * t = b := by
    dsimp [t]
    field_simp at ht
    nlinarith
  have hu := rotation_unit t
  change c ^ 2 + (t * c) ^ 2 = 1 at hu
  change c ^ 2 + (t * c) ^ 2 = 1 ∧ _
  refine ⟨hu, ?_, ?_, ?_⟩
  all_goals nlinarith [congrArg (fun u : ℝ => u * c ^ 2) he,
    congrArg (fun u : ℝ => u * t * c ^ 2) he,
    congrArg (fun u : ℝ => u * a) hu, congrArg (fun u : ℝ => u * d) hu,
    congrArg (fun u : ℝ => u * (t * b)) hu]

/-- The two diagonal updates preserve trace and absorb exactly twice the
squared pivot into their squared magnitude. -/
theorem pivot_energy (a b d : ℝ) (hb : b ≠ 0)
    : let t := tangent ((d - a) / (2 * b))
      (a - t * b) + (d + t * b) = a + d
      ∧ (a - t * b) ^ 2 + (d + t * b) ^ 2 = a ^ 2 + d ^ 2 + 2 * b ^ 2 := by
  dsimp only
  let t := tangent ((d - a) / (2 * b))
  have ht := (tangent_properties ((d - a) / (2 * b))).2.2
  have he : b * t ^ 2 + (d - a) * t = b := by
    dsimp [t]
    field_simp at ht
    nlinarith
  constructor
  · ring
  · nlinarith [congrArg (fun u : ℝ => u * b) he]

/-- Each other off-diagonal pair preserves its squared magnitude under an
exact unit rotation. Thus only the two selected pivot entries are removed
from the full off-diagonal squared norm. -/
theorem pair_energy (c s x y : ℝ) (hunit : c ^ 2 + s ^ 2 = 1)
    : (c * x - s * y) ^ 2 + (s * x + c * y) ^ 2 = x ^ 2 + y ^ 2 := by
  nlinarith [congrArg (fun u : ℝ => u * (x ^ 2 + y ^ 2)) hunit]

/-- Positive square root does not amplify relative input error. The perturbed
input need only be nonnegative; no differentiability or lower bound away from
zero is required. This is used when composing multiplication, addition and the
native square-root model in a Jacobi parameter. -/
theorem sqrt_relative_perturbation (a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hε : 0 ≤ ε) (herr : |b - a| ≤ ε * a)
    : |Real.sqrt b - Real.sqrt a| ≤ ε * Real.sqrt a := by
  have hsa := Real.sqrt_pos.mpr ha
  have hsb := Real.sqrt_nonneg b
  have ha2 := Real.sq_sqrt ha.le
  have hb2 := Real.sq_sqrt hb
  have he : |Real.sqrt b - Real.sqrt a| * (Real.sqrt b + Real.sqrt a) = |b - a| := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ Real.sqrt b + Real.sqrt a), ← abs_mul]
    congr 1
    nlinarith
  have h := mul_le_mul_of_nonneg_left (by linarith : Real.sqrt a ≤ Real.sqrt b + Real.sqrt a)
    (abs_nonneg (Real.sqrt b - Real.sqrt a))
  rw [he] at h
  have h' := h.trans herr
  rw [← ha2] at h'
  nlinarith

/-- Perturbing a positive denominator by at most half its value keeps division
safe and bounds the relative error of its reciprocal. -/
theorem reciprocal_relative_perturbation (a b ε : ℝ) (ha : 0 < a)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) (herr : |b - a| ≤ ε * a)
    : a / 2 ≤ b ∧ 0 < b ∧ |1 / b - 1 / a| ≤ 2 * ε / a := by
  have he := abs_le.mp herr
  have hl : a / 2 ≤ b := by nlinarith
  have hb : 0 < b := by linarith
  refine ⟨hl, hb, ?_⟩
  have hid : 1 / b - 1 / a = (a - b) / (a * b) := by field_simp
  rw [hid, abs_div, abs_mul, abs_of_pos ha, abs_of_pos hb, abs_sub_comm]
  apply (div_le_iff₀ (mul_pos ha hb)).mpr
  calc
    |b - a| ≤ ε * a := herr
    _ ≤ 2 * ε * b := by nlinarith
    _ = (2 * ε / a) * (a * b) := by field_simp

/-- A sharper square-root perturbation rule. The caller supplies a radius δ
whose squared lower endpoint covers the input error ε. Near zero error this
retains the square root's factor of one half. -/
theorem sqrt_relative_sharp (a b ε δ : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (hεδ : ε ≤ 2 * δ - δ ^ 2)
    (herr : |b - a| ≤ ε * a)
    : |Real.sqrt b - Real.sqrt a| ≤ δ * Real.sqrt a := by
  have hs := Real.sq_sqrt ha.le
  have ht := Real.sq_sqrt hb
  have hs0 := Real.sqrt_pos.mpr ha
  have ht0 := Real.sqrt_nonneg b
  have he := abs_le.mp herr
  have hεa := mul_le_mul_of_nonneg_right hεδ ha.le
  have hlo : (1 - δ) * Real.sqrt a ≤ Real.sqrt b := by
    have hnonneg : 0 ≤ (1 - δ) * Real.sqrt a := mul_nonneg (by linarith) hs0.le
    have hsq : ((1 - δ) * Real.sqrt a)^2 ≤ (Real.sqrt b)^2 := by
      rw [mul_pow, hs, ht]
      nlinarith
    exact (sq_le_sq₀ hnonneg ht0).mp hsq
  have hhi : Real.sqrt b ≤ (1 + δ) * Real.sqrt a := by
    have hnonneg : 0 ≤ (1 + δ) * Real.sqrt a := by positivity
    have hsq : (Real.sqrt b)^2 ≤ ((1 + δ) * Real.sqrt a)^2 := by
      rw [mul_pow, hs, ht]
      nlinarith [mul_nonneg (sq_nonneg δ) ha.le]
    exact (sq_le_sq₀ ht0 hnonneg).mp hsq
  rw [abs_le]
  constructor <;> nlinarith

/-- A sharper reciprocal perturbation rule. Choosing δ just above ε avoids
the factor-of-two allowance used by the coarse magnitude invariant. -/
theorem reciprocal_relative_sharp (a b ε δ : ℝ) (ha : 0 < a)
    (hε' : ε < 1) (hδ : 0 ≤ δ) (hεδ : ε ≤ δ * (1 - ε))
    (herr : |b - a| ≤ ε * a)
    : 0 < b ∧ |1 / b - 1 / a| ≤ δ / a := by
  have he := abs_le.mp herr
  have hb : 0 < b := by nlinarith [mul_pos (by linarith : 0 < 1 - ε) ha]
  refine ⟨hb, ?_⟩
  have hid : 1 / b - 1 / a = (a - b) / (a * b) := by field_simp
  rw [hid, abs_div, abs_mul, abs_of_pos ha, abs_of_pos hb, abs_sub_comm]
  apply (div_le_iff₀ (mul_pos ha hb)).mpr
  calc
    |b - a| ≤ ε * a := herr
    _ ≤ δ * (1 - ε) * a := mul_le_mul_of_nonneg_right hεδ ha.le
    _ ≤ δ * b := by nlinarith [mul_le_mul_of_nonneg_left he.1 hδ]
    _ = (δ / a) * (a * b) := by field_simp

/-- Rounding a square and then adding one has a small relative error measured
against `1 + x²`, including when the square is tiny. Here u is binary64's unit
roundoff; the primitive error budgets are four units plus underflow. -/
theorem square_add_error (x₂ p q u η : ℝ) (hx : 0 ≤ x₂)
    (hu : 0 ≤ u) (hu' : u ≤ 1 / 1000) (hη' : η ≤ u)
    (hp : |p - x₂| ≤ 4 * u * (x₂ + η))
    (hq : |q - (1 + p)| ≤ 4 * u * (|1 + p| + η))
    : |q - (1 + x₂)| ≤ 9 * u * (1 + x₂) := by
  have hp' : |p - x₂| ≤ 4 * u * (x₂ + u) := hp.trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hη') (by positivity))
  have hsum : |1 + p| ≤ 1 + x₂ + 4 * u * (x₂ + u) := by
    have he : 1 + p = (1 + x₂) + (p - x₂) := by ring
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add (by rw [abs_of_nonneg (by positivity)]) hp')
  have hq' := hq.trans (mul_le_mul_of_nonneg_left (add_le_add hsum hη') (by positivity))
  have hid : |(1 + p) - (1 + x₂)| = |p - x₂| := by congr 1; ring
  have ht := abs_sub_le q (1 + p) (1 + x₂)
  rw [hid] at ht
  apply (ht.trans (add_le_add hq' hp')).trans
  have hu2 : u^2 ≤ u / 1000 := by nlinarith [mul_le_mul_of_nonneg_left hu' hu]
  have hu3 : u^3 ≤ u / 1000000 := by
    nlinarith [mul_le_mul_of_nonneg_left hu2 hu, mul_le_mul_of_nonneg_left hu' hu]
  nlinarith [mul_le_mul_of_nonneg_right hu2 hx]

private lemma square_perturbation (x y M δ : ℝ) (hM : 0 ≤ M)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (hx : |x| ≤ 2 * M) (he : |y - x| ≤ δ * M)
    : |y ^ 2 - x ^ 2| ≤ 5 * δ * M ^ 2 := by
  have hy : |y| ≤ 3 * M := by
    have h := abs_sub_le y x 0
    simp only [sub_zero] at h
    nlinarith [mul_le_mul_of_nonneg_right hδ' hM]
  have hsum : |y + x| ≤ 5 * M := (abs_add_le y x).trans (by linarith)
  have hid : y ^ 2 - x ^ 2 = (y - x) * (y + x) := by ring
  rw [hid, abs_mul]
  have h := mul_le_mul he hsum (abs_nonneg _) (mul_nonneg hδ hM)
  apply h.trans_eq
  ring

/-- Energy error of a perturbed rotation pair. The coefficient normalization
defect and the arithmetic error are separate, so either can be established by
an independent numerical implementation. -/
theorem pair_energy_perturbation (c s x y p q M δ ε : ℝ)
    (hM : |x| + |y| ≤ M) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1)
    (hc : |c| ≤ 2) (hs : |s| ≤ 2) (hunit : |c ^ 2 + s ^ 2 - 1| ≤ ε)
    (hp : |p - (c * x - s * y)| ≤ δ * M)
    (hq : |q - (s * x + c * y)| ≤ δ * M)
    : |p ^ 2 + q ^ 2 - (x ^ 2 + y ^ 2)| ≤ ε * (x ^ 2 + y ^ 2) + 10 * δ * M ^ 2 := by
  have hM0 : 0 ≤ M := (add_nonneg (abs_nonneg x) (abs_nonneg y)).trans hM
  have hprod (a b : ℝ) (ha : |a| ≤ 2) : |a * b| ≤ 2 * |b| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ha (abs_nonneg b)
  have hpx : |c * x - s * y| ≤ 2 * M :=
    (abs_sub _ _).trans ((add_le_add (hprod c x hc) (hprod s y hs)).trans (by linarith))
  have hqx : |s * x + c * y| ≤ 2 * M :=
    (abs_add_le _ _).trans ((add_le_add (hprod s x hs) (hprod c y hc)).trans (by linarith))
  have heP := square_perturbation _ p M δ hM0 hδ hδ' hpx hp
  have heQ := square_perturbation _ q M δ hM0 hδ hδ' hqx hq
  have he : (c * x - s * y) ^ 2 + (s * x + c * y) ^ 2 - (x ^ 2 + y ^ 2) =
      (c ^ 2 + s ^ 2 - 1) * (x ^ 2 + y ^ 2) := by ring
  have hu : |(c * x - s * y) ^ 2 + (s * x + c * y) ^ 2 - (x ^ 2 + y ^ 2)| ≤
      ε * (x ^ 2 + y ^ 2) := by
    rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ x ^ 2 + y ^ 2)]
    exact mul_le_mul_of_nonneg_right hunit (by positivity)
  have hid : p ^ 2 + q ^ 2 - (x ^ 2 + y ^ 2) =
      (p ^ 2 - (c * x - s * y) ^ 2) + (q ^ 2 - (s * x + c * y) ^ 2) +
        ((c * x - s * y) ^ 2 + (s * x + c * y) ^ 2 - (x ^ 2 + y ^ 2)) := by ring
  rw [hid]
  have h := (abs_add_le ((p ^ 2 - (c * x - s * y) ^ 2) + (q ^ 2 - (s * x + c * y) ^ 2))
    ((c * x - s * y) ^ 2 + (s * x + c * y) ^ 2 - (x ^ 2 + y ^ 2))).trans
      (add_le_add (abs_add_le _ _) le_rfl)
  exact (h.trans (add_le_add (add_le_add heP heQ) hu)).trans_eq (by ring)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 400 in
private lemma contraction_profile (n : Nat) (hn : 2 ≤ n) (hn' : n ≤ 18)
    : let D := n * (n - 1)
      let ρ : ℝ := 1 + 2 ^ (-36 : Int) - 2 / D
      0 ≤ ρ
      ∧ ρ ≤ 1
      ∧ ρ ^ D ≤ 5 / 37
      ∧ 32 * D ≤ 31 * n * n
      ∧ (D : ℝ) ≤ (17 / 18 : ℝ) * (n * n : Nat) := by
  interval_cases n <;> norm_num

/-- A largest-pivot energy recurrence reaches the stopping scale within the
runtime's `32*n²` rotation allowance. The recurrence permits a relative energy
increase of 2⁻³⁶ per step before eliminating the pivot. Float.JacobiConvergence
establishes the recurrence hypotheses for the native array loop.
The threshold 9.9e-15 lies below the runtime's binary64 `1e-14` threshold. -/
theorem energy_convergence (n : Nat) (E pivot : Nat → ℝ)
    (hn : 2 ≤ n) (hn' : n ≤ 18)
    (hE : ∀ k, k ≤ 32 * n * n → 0 ≤ E k)
    (hstart : E 0 ≤ (1001 / 1000 : ℝ) * (n * (n - 1) : Nat))
    (hlargest : ∀ k, k < 32 * n * n → E k ≤ (n * (n - 1) : Nat) * (pivot k) ^ 2)
    (hstep
      : ∀ k,
          k < 32 * n * n
          → (99 / 10000000000000000 : ℝ) < pivot k
          → E (k + 1) ≤ (1 + (2 : ℝ) ^ (-36 : Int)) * E k - 2 * (pivot k) ^ 2)
    : ∃ k, k < 32 * n * n ∧ pivot k ≤ (99 / 10000000000000000 : ℝ) := by
  by_contra hnone
  have hp : ∀ k, k < 32 * n * n → (99 / 10000000000000000 : ℝ) < pivot k := by
    intro k hk
    exact lt_of_not_ge (fun h => hnone ⟨k, hk, h⟩)
  let D := n * (n - 1)
  let ρ : ℝ := 1 + 2^(-36 : Int) - 2 / D
  let N := n * n
  let δ : ℝ := 99 / 10000000000000000
  have hn0 : 0 < n := by omega
  have hN : 0 < N := Nat.mul_pos hn0 hn0
  have hD : 0 < (D : ℝ) := Nat.cast_pos.mpr (Nat.mul_pos hn0 (by omega))
  obtain ⟨hρ, hρ', hblock, hcount, hratio⟩ := contraction_profile n hn hn'
  change 0 ≤ ρ at hρ
  change ρ ≤ 1 at hρ'
  change ρ ^ D ≤ 5 / 37 at hblock
  have hcontract (k : Nat) (hk : k < 32 * n * n) : E (k + 1) ≤ ρ * E k := by
    have hdom := hlargest k hk
    have he : 2 / (D : ℝ) * E k ≤ 2 * (pivot k)^2 := by
      change E k ≤ (D : ℝ) * (pivot k)^2 at hdom
      calc
        _ ≤ 2 / (D : ℝ) * ((D : ℝ) * (pivot k) ^ 2) :=
          mul_le_mul_of_nonneg_left hdom (by positivity)
        _ = _ := by field_simp
    have h := hstep k hk (hp k hk)
    calc
      _ ≤ (1 + (2 : ℝ) ^ (-36 : Int)) * E k - 2 * (pivot k) ^ 2 := h
      _ ≤ (1 + (2 : ℝ) ^ (-36 : Int)) * E k - (2 / D) * E k := sub_le_sub_left he _
      _ = _ := by dsimp [ρ]; ring
  have hpower : ∀ k, k ≤ 32 * n * n → E k ≤ ρ ^ k * E 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        intro hk
        have h := (hcontract k (by omega)).trans
          (mul_le_mul_of_nonneg_left (ih (by omega)) hρ)
        apply h.trans_eq
        rw [pow_succ]
        ring
  have hpow : ρ ^ (31 * n * n) ≤ (5 / 37 : ℝ)^32 := by
    calc
      _ ≤ ρ ^ (32 * D) := pow_le_pow_of_le_one hρ hρ' hcount
      _ = (ρ ^ D) ^ 32 := by rw [mul_comm 32 D, pow_mul]
      _ ≤ _ := pow_le_pow_left₀ (pow_nonneg hρ _) hblock 32
  have hsmall : E (31 * N) < (3 / 2 : ℝ) * N * δ^2 := by
    have h0 := hE 0 (by omega)
    have h := (hpower (31 * n * n) (by simp only [Nat.mul_assoc]; omega)).trans
      (mul_le_mul_of_nonneg_right hpow h0)
    have h' := mul_le_mul_of_nonneg_left hstart (by positivity : 0 ≤ (5 / 37 : ℝ)^32)
    have h'' := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ (5 / 37 : ℝ)^32 * (1001 /
      1000))
    have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hc : (5 / 37 : ℝ)^32 * (1001 / 1000) * (17 / 18) < (3 / 2 : ℝ) * δ^2 := by
      norm_num [δ]
    have hh := mul_lt_mul_of_pos_right hc hN0
    rw [Nat.mul_assoc 31 n n] at h
    change E (31 * N) ≤ _ at h
    change _ ≤ _ * (17 / 18 * (N : ℝ)) at h''
    nlinarith
  have hNbound : (N : ℝ) ≤ 324 := by
    have : N ≤ 324 := by dsimp [N]; nlinarith
    exact_mod_cast this
  have htail : ∀ k, k ≤ N → E (31 * N + k) ≤ E (31 * N) - (3 / 2 : ℝ) * k * δ^2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        intro hk
        have hki : 31 * N + k < 32 * n * n := by
          simp only [N, Nat.mul_assoc] at hk ⊢
          omega
        have hi := ih (by omega)
        have hnonneg : 0 ≤ (3 / 2 : ℝ) * k * δ^2 := by positivity
        have hcurrent : E (31 * N + k) < (3 / 2 : ℝ) * N * δ^2 := by linarith
        have hround : (2 : ℝ)^(-36 : Int) * E (31 * N + k) ≤ δ^2 / 2 := by
          have h := mul_le_mul_of_nonneg_left hcurrent.le (by positivity : 0 ≤ (2 : ℝ)^(-36 : Int))
          have hh := mul_le_mul_of_nonneg_right hNbound (by positivity : 0 ≤ (3 / 2 : ℝ) * (2 :
            ℝ)^(-36 : Int) * δ^2)
          norm_num only [zpow_neg, zpow_ofNat] at h hh
          nlinarith [sq_nonneg δ]
        have hpk := hp _ hki
        have hp2 : δ^2 ≤ (pivot (31 * N + k))^2 := by
          change δ < _ at hpk
          have : 0 ≤ δ := by norm_num [δ]
          nlinarith
        have hs := hstep _ hki hpk
        rw [Nat.cast_succ]
        have hind : 31 * N + (k + 1) = (31 * N + k) + 1 := by omega
        rw [hind]
        norm_num only [zpow_neg, zpow_ofNat] at hround hs
        norm_num [δ] at hi hp2 ⊢
        nlinarith only [hs, hi, hround, hp2]
  have hfinal := htail N le_rfl
  have hnonneg := hE (32 * n * n) le_rfl
  have he : 31 * N + N = 32 * n * n := by dsimp [N]; ring
  rw [he] at hfinal
  linarith

end Flare.Analysis.Jacobi
