module

public import Flare.Binary64.Nearest
public import Flare.Matrix.LinearSolve

/-! Reusable error analysis for the separately rounded product/subtraction loop
used by triangular substitution. All real quantities here are proof-only.
The runtime continues to use native Float arrays and arithmetic. -/

@[expose] public section

namespace Flare.Matrix.Substitution
open Flare.Matrix.Value Flare.Binary64.Value Flare.Binary64.Arithmetic
open Flare.Matrix.Dense Std.Do

set_option experimental.vcgen true

attribute [local instance] Std.Internal.Order.instPartialOrderProp
  Std.Internal.Order.instCompleteLatticeProp

/-- Proof-side extraction of a native subtract-products loop, with arbitrary
index order. This is the common arithmetic schedule of both substitution passes. -/
def subtractProducts (indices : List Nat) (left right : Nat → Float) (initial : Float)
    : Except Flare.Matrix.DenseError Float := do
  let mut s := initial
  for k in indices do
    let term ← finite (left k * right k)
    s ← finite (s - term)
  return s

private lemma subtract_step (a b s : Float) (exact M : ℝ) (k : Nat)
    (ha : a.isFinite = true) (hb : b.isFinite = true) (hs : s.isFinite = true)
    (hk : k ≤ 31) (hM : M ≤ (2 : ℝ) ^ (990 : Int))
    (hη : (2 : ℝ) ^ (-1022 : Int) ≤ M)
    (ht : |value a * value b| ≤ M) (he : |exact| ≤ M)
    (herr : |value s - exact| ≤ k * (2 : ℝ) ^ (-48 : Int) * M)
    : (a * b).isFinite = true
      ∧ (s - a * b).isFinite = true
      ∧ |value (s - a * b) - (exact - value a * value b)|
        ≤ (k + 1 : Nat) * (2 : ℝ) ^ (-48 : Int) * M := by
  have hM0 : 0 ≤ M := (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _).trans hη
  have hk' : (k : ℝ) ≤ 31 := by exact_mod_cast hk
  have hsbound : |value s| ≤ 2 * M := by
    have hh := abs_sub_le (value s) exact 0
    simp only [sub_zero] at hh
    have hkm := mul_le_mul_of_nonneg_right hk' hM0
    norm_num at herr
    nlinarith
  have hlim : 4 * M ≤ (2 : ℝ)^(1000 : Int) := by
    calc
      _ ≤ 4 * (2 : ℝ) ^ (990 : Int) := mul_le_mul_of_nonneg_left hM (by norm_num)
      _ = (2 : ℝ) ^ (992 : Int) := by
        rw [show (992 : Int) = 990 + 2 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        rw [show (2 : ℝ)^(2 : Int) = 4 by norm_num]; ring
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hm := Flare.Binary64.Nearest.mul_error_nearest a b ha hb
    (ht.trans ((by linarith only [hM0] : M ≤ 4 * M).trans hlim))
  have hprod : |value (a * b)| ≤ 2 * M := by
    have hh := abs_sub_le (value (a * b)) (value a * value b) 0
    simp only [sub_zero] at hh
    have he' := hm.2
    norm_num only [show (2 : ℝ)^(-53 : Int) = 1 / 9007199254740992 by norm_num] at he'
    nlinarith
  have hh := Flare.Binary64.Nearest.sub_error_nearest s (a * b) hs hm.1
    ((abs_sub _ _).trans (by linarith only [hsbound, hprod, hlim]))
  refine ⟨hm.1, hh.1, ?_⟩
  have heq : value (s - a * b) - (exact - value a * value b) =
      (value (s - a * b) - (value s - value (a * b))) +
      (value s - exact) - (value (a * b) - value a * value b) := by ring
  rw [heq]
  have htri := (abs_sub
    ((value (s - a * b) - (value s - value (a * b))) + (value s - exact))
    (value (a * b) - value a * value b)).trans
    (add_le_add (abs_add_le _ _) le_rfl)
  have hmerr := hm.2
  have hserr := hh.2
  have hsub := abs_sub (value s) (value (a * b))
  simp only [Nat.cast_add, Nat.cast_one] at ⊢
  norm_num only [show (2 : ℝ)^(-53 : Int) = 1 / 9007199254740992 by norm_num,
    show (2 : ℝ)^(-48 : Int) = 1 / 281474976710656 by norm_num] at hmerr hserr herr ⊢
  linarith

/-- A native product/subtraction step with a growing absolute term mass.
The offset allows the same recurrence to start from an exact input or from a
rounded division. No lower bound on individual products is needed. -/
lemma subtract_mass_step (a b s : Float) (exact mass : ℝ) (k offset : Nat)
    (ha : a.isFinite = true) (hb : b.isFinite = true) (hs : s.isFinite = true)
    (hk : k ≤ 31) (hoff : 2 ≤ offset) (hoff' : offset ≤ 4)
    (hM : mass + |value a * value b| ≤ (2 : ℝ) ^ (990 : Int))
    (hη : (2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int) ≤ mass)
    (he : |exact| ≤ mass)
    (herr : |value s - exact| ≤ (1001 / 1000 : ℝ) * (k + offset) * (2 : ℝ) ^ (-53 : Int) * mass)
    : (a * b).isFinite = true
      ∧ (s - a * b).isFinite = true
      ∧ |value (s - a * b) - (exact - value a * value b)|
        ≤ (1001 / 1000 : ℝ)
          * ((k + 1 : Nat) + offset)
          * (2 : ℝ) ^ (-53 : Int)
          * (mass + |value a * value b|) := by
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  let t := |value a * value b|
  have hη0 : 0 ≤ η := zpow_nonneg (by norm_num) _
  have ht0 : 0 ≤ t := abs_nonneg _
  have hm0 : 0 ≤ mass := (abs_nonneg _).trans he
  have hk' : (k : ℝ) ≤ 31 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hoff0 : (2 : ℝ) ≤ offset := by exact_mod_cast hoff
  have hoffhi : (offset : ℝ) ≤ 4 := by exact_mod_cast hoff'
  have hkm := mul_le_mul_of_nonneg_right hk' hm0
  have hom := mul_le_mul_of_nonneg_right hoffhi hm0
  have hkt := mul_nonneg hk0 ht0
  have hot := mul_le_mul_of_nonneg_right hoff0 ht0
  change (2 : ℝ)^(20 : Int) * η ≤ mass at hη
  norm_num only [show (2 : ℝ)^(20 : Int) = 1048576 by norm_num] at hη
  have hlim : 4 * (mass + t) ≤ (2 : ℝ)^(1000 : Int) := by
    calc
      _ ≤ 4 * (2 : ℝ) ^ (990 : Int) := mul_le_mul_of_nonneg_left hM (by norm_num)
      _ = (2 : ℝ) ^ (992 : Int) := by
        rw [show (992 : Int) = 990 + 2 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        rw [show (2 : ℝ)^(2 : Int) = 4 by norm_num]; ring
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hm := Flare.Binary64.Nearest.mul_error_nearest a b ha hb
    ((show t ≤ 4 * (mass + t) by linarith only [hm0, ht0]).trans hlim)
  have hme := hm.2
  change _ ≤ (2 : ℝ)^(-53 : Int) * (t + η) at hme
  have hsbound : |value s| ≤ 2 * mass := by
    have h := abs_sub_le (value s) exact 0
    simp only [sub_zero] at h
    norm_num only [show (2 : ℝ)^(-53 : Int) = 1 / 9007199254740992 by norm_num] at herr
    nlinarith
  have hprod : |value (a * b)| ≤ 2 * t + mass := by
    have h := abs_sub_le (value (a * b)) (value a * value b) 0
    simp only [sub_zero] at h
    change _ ≤ _ + t at h
    norm_num only [show (2 : ℝ)^(-53 : Int) = 1 / 9007199254740992 by norm_num] at hme
    nlinarith
  have hsub := Flare.Binary64.Nearest.sub_error_nearest s (a * b) hs hm.1
    ((abs_sub _ _).trans ((show |value s| + |value (a * b)| ≤ 4 * (mass + t) by
      linarith only [hsbound, hprod, hm0, ht0]).trans hlim))
  refine ⟨hm.1, hsub.1, ?_⟩
  have hdiff : |(value s - value (a * b)) - (exact - value a * value b)| ≤
      |value s - exact| + |value (a * b) - value a * value b| := by
    have heq : (value s - value (a * b)) - (exact - value a * value b) =
        (value s - exact) - (value (a * b) - value a * value b) := by ring
    rw [heq]; exact abs_sub _ _
  have hreal : |exact - value a * value b| ≤ mass + t :=
    (abs_sub _ _).trans (add_le_add he le_rfl)
  have hactual := abs_sub_le (value s - value (a * b)) (exact - value a * value b) 0
  simp only [sub_zero] at hactual
  have htotal := abs_sub_le (value (s - a * b)) (value s - value (a * b))
    (exact - value a * value b)
  have hse := hsub.2
  change _ ≤ (2 : ℝ)^(-53 : Int) * (|value s - value (a * b)| + η) at hse
  change _ ≤ (1001 / 1000 : ℝ) * ((k + 1 : Nat) + offset) * (2 : ℝ)^(-53 : Int) * (mass + t)
  norm_num only [show (2 : ℝ)^(-53 : Int) = 1 / 9007199254740992 by norm_num,
    Nat.cast_add, Nat.cast_one] at hse hme herr ⊢
  nlinarith

private noncomputable def productSum (indices : List Nat) (left right : Nat → Float) : ℝ :=
  (indices.map (fun k => value (left k) * value (right k))).sum

private noncomputable def productMass (indices : List Nat) (left right : Nat → Float) : ℝ :=
  (indices.map (fun k => |value (left k) * value (right k)|)).sum

private lemma productMass_nonneg (indices : List Nat) (left right : Nat → Float)
    : 0 ≤ productMass indices left right := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
  exact abs_nonneg _

private lemma productSum_bound (indices : List Nat) (left right : Nat → Float)
    : |productSum indices left right| ≤ productMass indices left right := by
  induction indices with
  | nil => simp [productSum, productMass]
  | cons k ks ih =>
      simpa only [productSum, productMass, List.map_cons, List.sum_cons]
        using (abs_add_le (value (left k) * value (right k)) (productSum ks left right)).trans
          (add_le_add le_rfl ih)

private theorem subtractProducts_triple_of_step (indices : List Nat) (left right : Nat → Float)
    (initial : Float) (target : ℝ) (budget : List Nat → ℝ)
    (hi : initial.isFinite = true) (hzero : |value initial - target| ≤ budget [])
    (step
      : ∀ pref k suff s,
          indices = pref ++ k :: suff
          → s.isFinite = true ∧ |value s - (target - productSum pref left right)| ≤ budget pref
          → (left k * right k).isFinite = true
            ∧ (s - left k * right k).isFinite = true
            ∧ |value (s - left k * right k)
                - (target - productSum pref left right - value (left k) * value (right k))|
              ≤ budget (pref ++ [k]))
    : ⦃⌜True⌝
      ⦄ subtractProducts indices left right initial
      ⦃
        ⇓ s
          =>
              ⌜
                s.isFinite = true
                ∧ |value s - (target - productSum indices left right)| ≤ budget indices
                ⌝
        ⦄ := by
  unfold subtractProducts
  apply (Specification.except_iff _ _ _).mpr
  vcgen [-Flare.Matrix.Storage.finite_wp_spec, Flare.Matrix.Storage.finite_wp_exact] invariants
  | inv1 => fun xs _ s => s.isFinite = true ∧
      |value s - (target - productSum xs left right)| ≤ budget xs
  all_goals simp_all only [SPred.down_pure_nil]
  all_goals subst_vars
  case vc1 => exact ⟨True.intro, by simpa [productSum] using hzero⟩
  case vc2 => trivial
  case vc3 | vc5 | vc7 =>
    rename_i pref k suff s hs
    have hh := step pref k suff s rfl hs
    first
    | exact hh.1
    | exact hh.2.1
    | refine ⟨hh.2.1, ?_⟩
      simpa only [productSum, List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton, sub_sub] using hh.2.2

private theorem subtractProducts_triple (indices : List Nat) (left right : Nat → Float)
    (initial : Float) (M : ℝ) (hlen : indices.length ≤ 32)
    (hi : initial.isFinite = true)
    (hl : ∀ k ∈ indices, (left k).isFinite = true)
    (hr : ∀ k ∈ indices, (right k).isFinite = true)
    (hM : M ≤ (2 : ℝ) ^ (990 : Int))
    (hmass : |value initial| + productMass indices left right + (2 : ℝ) ^ (-1022 : Int) ≤ M)
    : ⦃⌜True⌝
      ⦄ subtractProducts indices left right initial
      ⦃
        ⇓ s
          =>
              ⌜
                s.isFinite = true
                ∧ |value s - (value initial - productSum indices left right)|
                  ≤ indices.length * (2 : ℝ) ^ (-48 : Int) * M
                ⌝
        ⦄ := by
  have hη : (2 : ℝ)^(-1022 : Int) ≤ M := by
    linarith [abs_nonneg (value initial), productMass_nonneg indices left right]
  apply subtractProducts_triple_of_step indices left right initial (value initial)
    (fun pref => pref.length * (2 : ℝ) ^ (-48 : Int) * M) hi (by simp)
  intro pref k suff s heq hs
  subst indices
  let indices := pref ++ k :: suff
  have heq : indices = pref ++ k :: suff := rfl
  have hmem : k ∈ indices := by simp [heq]
  have hpref : productMass pref left right ≤ productMass indices left right := by
    rw [heq]
    simp only [productMass, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    change productMass pref left right ≤ productMass pref left right +
      (|value (left k) * value (right k)| + productMass suff left right)
    linarith [abs_nonneg (value (left k) * value (right k)), productMass_nonneg suff left right]
  have ht : |value (left k) * value (right k)| ≤ M := by
    have hh := hmass
    change |value initial| + productMass indices left right + (2 : ℝ)^(-1022 : Int) ≤ M at hh
    rw [heq] at hh
    simp only [productMass, List.map_append, List.sum_append, List.map_cons, List.sum_cons] at hh
    change |value initial| + (productMass pref left right +
      (|value (left k) * value (right k)| + productMass suff left right)) +
        (2 : ℝ)^(-1022 : Int) ≤ M at hh
    linarith [abs_nonneg (value initial), productMass_nonneg pref left right,
      productMass_nonneg suff left right, zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-1022 : Int)]
  have hp : |value initial - productSum pref left right| ≤ M := by
    have hh := productSum_bound pref left right
    linarith [abs_sub (value initial) (productSum pref left right),
      zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-1022 : Int)]
  have hk : pref.length ≤ 31 := by simp only [List.length_append, List.length_cons] at hlen; omega
  have hh := subtract_step (left k) (right k) s _ M pref.length
    (hl k hmem) (hr k hmem) hs.1 hk hM hη ht hp hs.2
  exact ⟨hh.1, hh.2.1, by simpa only [List.length_append, List.length_singleton] using hh.2.2⟩

/-- A sharp residual bound for the complete native row loop, including a
possibly rounded initial value. The target and all masses are ghost reals.
The two substitution passes instantiate the offset as two and four. -/
theorem subtractProducts_mass_accuracy (indices : List Nat) (left right : Nat → Float)
    (initial : Float) (target : ℝ) (offset : Nat) (hlen : indices.length ≤ 32)
    (hoff : 2 ≤ offset) (hoff' : offset ≤ 4)
    (hi : initial.isFinite = true)
    (hl : ∀ k ∈ indices, (left k).isFinite = true)
    (hr : ∀ k ∈ indices, (right k).isFinite = true)
    (hM
      : |target|
          + (indices.map (fun k => |value (left k) * value (right k)|)).sum
          + (2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int)
        ≤ (2 : ℝ) ^ (990 : Int))
    (hinit
      : |value initial - target|
        ≤ (1001 / 1000 : ℝ)
          * offset
          * (2 : ℝ) ^ (-53 : Int)
          * (|target| + (2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int)))
    : ∃ s,
        subtractProducts indices left right initial = .ok s
        ∧ s.isFinite = true
        ∧ |value s - (target - (indices.map (fun k => value (left k) * value (right k))).sum)|
          ≤ (1001 / 1000 : ℝ) * (indices.length + offset) * (2 : ℝ) ^ (-53 : Int)
            * (|target|
                + (indices.map (fun k => |value (left k) * value (right k)|)).sum
                + (2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int)) := by
  let mass (pref : List Nat) := |target| + productMass pref left right +
    (2 : ℝ)^(20 : Int) * (2 : ℝ)^(-1022 : Int)
  let budget (pref : List Nat) :=
    (1001 / 1000 : ℝ) * (pref.length + offset) * (2 : ℝ)^(-53 : Int) * mass pref
  have hm0 (pref : List Nat) : (2 : ℝ)^(20 : Int) * (2 : ℝ)^(-1022 : Int) ≤ mass pref := by
    dsimp [mass]; linarith [abs_nonneg target, productMass_nonneg pref left right]
  have hstep (pref : List Nat) (k : Nat) :
      mass (pref ++ [k]) = mass pref + |value (left k) * value (right k)| := by
    simp only [mass, productMass, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton]
    ring
  have h :=
    subtractProducts_triple_of_step indices left right initial target budget hi
      (by simpa [budget, mass, productMass] using hinit)
      (by
        intro pref k suff s heq hs
        have hmem : k ∈ indices := by simp [heq]
        have hk : pref.length ≤ 31 := by
          rw [heq] at hlen; simp only [List.length_append, List.length_cons] at hlen; omega
        have hmass : mass pref + |value (left k) * value (right k)| ≤ (2 : ℝ)^(990 : Int) := by
          have hh := hM
          change mass indices ≤ _ at hh
          rw [heq] at hh
          simp only [mass, productMass, List.map_append, List.sum_append,
            List.map_cons, List.sum_cons] at hh ⊢
          have htail := productMass_nonneg suff left right
          dsimp only [productMass] at htail
          linarith
        have hprefix : |target - productSum pref left right| ≤ mass pref := by
          calc
            _ ≤ |target| + |productSum pref left right| := abs_sub _ _
            _ ≤ |target| + productMass pref left right := add_le_add le_rfl (productSum_bound _ _ _)
            _ ≤ _ := le_add_of_nonneg_right (by positivity)
        have hh := subtract_mass_step (left k) (right k) s (target - productSum pref left right)
          (mass pref) pref.length offset (hl k hmem) (hr k hmem) hs.1 hk hoff hoff' hmass
          (hm0 pref) hprefix hs.2
        exact ⟨
          hh.1,
          hh.2.1,
          by simpa only [budget, List.length_append, List.length_singleton, hstep] using hh.2.2
        ⟩)
  cases he : subtractProducts indices left right initial with
  | error e =>
      rw [he] at h; exact False.elim (h True.intro)
  | ok s =>
      rw [he] at h; exact ⟨s, rfl, h True.intro⟩

/-- A complete native subtract-products loop succeeds and has a relative error
bound with an explicit underflow allowance in M. Indices may repeat and need
not be ascending. M bounds the absolute input plus the sum of absolute exact
products, so cancellation does not invalidate the estimate. -/
theorem subtractProducts_accuracy (indices : List Nat) (left right : Nat → Float)
    (initial : Float) (M : ℝ) (hlen : indices.length ≤ 32)
    (hi : initial.isFinite = true)
    (hl : ∀ k ∈ indices, (left k).isFinite = true)
    (hr : ∀ k ∈ indices, (right k).isFinite = true)
    (hM : M ≤ (2 : ℝ) ^ (990 : Int))
    (hmass
      : |value initial|
          + (indices.map (fun k => |value (left k) * value (right k)|)).sum
          + (2 : ℝ) ^ (-1022 : Int)
        ≤ M)
    : ∃ s,
        subtractProducts indices left right initial = .ok s
        ∧ s.isFinite = true
        ∧ |value s
            - (value initial - (indices.map (fun k => value (left k) * value (right k))).sum)|
          ≤ indices.length * (2 : ℝ) ^ (-48 : Int) * M := by
  have h := subtractProducts_triple indices left right initial M hlen hi hl hr hM hmass
  cases he : subtractProducts indices left right initial with
  | error e =>
      rw [he] at h; exact False.elim (h True.intro)
  | ok s =>
      rw [he] at h; exact ⟨s, rfl, h True.intro⟩

/-- Replacing operands outside the visited indices cannot change execution. -/
lemma subtractProducts_congr (indices : List Nat) (left right left' right' : Nat → Float)
    (initial : Float) (hl : ∀ k ∈ indices, left k = left' k)
    (hr : ∀ k ∈ indices, right k = right' k)
    : subtractProducts indices left right initial
      = subtractProducts indices left' right' initial := by
  unfold subtractProducts
  simp only [bind_pure, ← forIn'_eq_forIn]
  apply List.forIn'_congr rfl rfl
  intro k hk s
  simp only [hl k hk, hr k hk]

@[local spec]
private lemma subtractProducts_result (indices : List Nat)
    (left right : Nat → Float) (initial : Float)
    : ⦃⌜True⌝
      ⦄ subtractProducts indices left right initial
      ⦃⇓? s => ⌜subtractProducts indices left right initial = .ok s⌝⦄ := by
  generalize he : subtractProducts indices left right initial = result
  cases result with
  | error e => exact fun _ => True.intro
  | ok value => exact fun _ => rfl

open scoped Std.WP in
@[local spec]
private theorem subtractProducts_wp_result (indices : List Nat)
    (left right : Nat → Float) (initial : Float)
    : Std.WP.Triple (subtractProducts indices left right initial) True
        (fun s => subtractProducts indices left right initial = .ok s) (fun _ => True) :=
  (Specification.except_iff _ _ _).mp (subtractProducts_result indices left right initial)

/-- The forward pass expressed using the reusable product/subtraction loop. -/
def forwardByProducts (n columns : Nat) (f : Factor) (b : Array Float)
    : Except Flare.Matrix.DenseError (Array Float) := do
  let mut r := Array.replicate (n * columns) 0.0
  for i in [:n] do
    for j in [:columns] do
      let s ←
        subtractProducts (List.range i) (fun k => entry n f.lower i k)
          (fun k => entry columns r k j) (entry columns b i j)
      r := r.set! (i * columns + j) s
  return r

/-- The extracted loop preserves every multiplication, subtraction and finite
check of the native forward pass. -/
theorem forward_eq (n columns : Nat) (f : Factor) (b : Array Float)
    : LinearSolve.forward n columns f b = forwardByProducts n columns f b := by
  unfold LinearSolve.forward forwardByProducts subtractProducts
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one, ← List.range_eq_range']
  simp only [bind_assoc, pure_bind]

private def ForwardEquations (n columns : Nat) (f : Factor) (b : Array Float)
    (i j : Nat) (r : Array Float)
    : Prop :=
  r.size = n * columns
  ∧ ∀ a c,
      a < n
      → c < columns
      → a < i ∨ a = i ∧ c < j
      → subtractProducts (List.range a) (fun k => entry n f.lower a k)
          (fun k => entry columns r k c) (entry columns b a c)
        = .ok (entry columns r a c)

private lemma forward_write (n columns : Nat) (f : Factor) (b r : Array Float)
    (i j : Nat) (s : Float) (hi : i < n) (hj : j < columns)
    (hr : ForwardEquations n columns f b i j r)
    (hs
      : subtractProducts (List.range i) (fun k => entry n f.lower i k)
          (fun k => entry columns r k j) (entry columns b i j)
        = .ok s)
    : ForwardEquations n columns f b i (j + 1) (r.set! (i * columns + j) s) := by
  refine ⟨(Array.size_set! ..).trans hr.1, ?_⟩
  intro a c ha hc hac
  have reads (hrow : a ≤ i) :
      subtractProducts (List.range a) (fun k => entry n f.lower a k)
        (fun k => entry columns (r.set! (i * columns + j) s) k c) (entry columns b a c) =
      subtractProducts (List.range a) (fun k => entry n f.lower a k)
        (fun k => entry columns r k c) (entry columns b a c) := by
    apply subtractProducts_congr _ _ _ _ _ _ (by intros; rfl)
    intro k hk
    have hk' := List.mem_range.mp hk
    rw [Flare.Matrix.Storage.entry_set columns r i j k c s hr.1 hi hj hc]
    simp [show k ≠ i by omega]
  rw [reads (by omega)]
  rw [Flare.Matrix.Storage.entry_set columns r i j a c s hr.1 hi hj hc]
  split
  · rename_i he
    obtain ⟨rfl, rfl⟩ := he
    exact hs
  · apply hr.2 a c ha hc
    omega

private theorem forward_equations_triple (n columns : Nat) (f : Factor) (b : Array Float)
    : ⦃⌜True⌝
      ⦄ forwardByProducts n columns f b
      ⦃⇓? r => ⌜ForwardEquations n columns f b n 0 r⌝⦄ := by
  unfold forwardByProducts
  apply (Specification.except_iff _ _ _).mpr
  vcgen
    invariants
      | inv1 => fun xs _ r => ForwardEquations n columns f b xs.length 0 r
      | inv2 pref i suff hi initial hs =>
        fun xs _ r => ForwardEquations n columns f b i xs.length r
  all_goals simp_all only [SPred.down_pure_nil]
  case vc1 => simp [ForwardEquations, r]
  case vc2 =>
    rename_i r hr
    simpa [Std.Legacy.Range.size] using hr
  case vc3 =>
    rename_i pref i suff hlist current hcurrent
    simpa only [(Flare.Matrix.Storage.forIn_range_current hlist).1, List.length_nil] using hcurrent
  case vc4 =>
    rename_i pref i suff hlist initial hinit current hcurrent
    have hr' : ForwardEquations n columns f b i columns current := by
      simpa [Std.Legacy.Range.size] using hcurrent
    refine ⟨hr'.1, ?_⟩
    intro a c ha hc hac
    apply hr'.2 a c ha hc
    have hstep := (Flare.Matrix.Storage.forIn_range_current hlist).1
    simp only [List.length_append, List.length_singleton] at hac
    omega
  case vc5 => trivial
  case vc6 =>
    rename_i prefI i suffI hi initial hinit prefJ j suffJ hj current hcurrent hs
    have hj' := Flare.Matrix.Storage.forIn_range_current hj
    have hh := forward_write n columns f b current i j s
      (Flare.Matrix.Storage.forIn_range_current hi).2 hj'.2
      (by simpa only [hj'.1] using hcurrent) hs
    simpa only [List.length_append, List.length_singleton, ← hj'.1] using hh

/-- Each stored forward-substitution entry is exactly the result of its native
row loop, reading the final array's earlier rows. This proves the data-flow
connection needed to reuse the loop error theorem. -/
theorem forward_equations (n columns : Nat) (f : Factor) (b y : Array Float)
    (hy : LinearSolve.forward n columns f b = .ok y)
    : ∀ i j,
        i < n
        → j < columns
        → subtractProducts (List.range i) (fun k => entry n f.lower i k)
            (fun k => entry columns y k j) (entry columns b i j)
          = .ok (entry columns y i j) := by
  have h := forward_equations_triple n columns f b
  rw [← forward_eq, hy] at h
  intro i j hi hj
  exact (h True.intro).2 i j hi hj (Or.inl hi)

/-- Native forward substitution returns a finite array and obeys a componentwise
row-residual bound. The error is relative to the absolute input/product mass,
including an underflow allowance. No computed result or successful run is assumed. -/
theorem forward_accuracy (n columns : Nat) (B : Int) (f : Factor) (b : Array Float)
    (hn : n ≤ 12) (hB : 0 ≤ B) (hB' : B ≤ 512)
    (hl : f.lower.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hlb : ∀ i k, i < n → k < i → |value (entry n f.lower i k)| ≤ 128)
    (hbb : ∀ i j, i < n → j < columns → |value (entry columns b i j)| ≤ (2 : ℝ) ^ B)
    : ∃ y,
        LinearSolve.forward n columns f b = .ok y
        ∧ y.size = n * columns
        ∧ y.all Float.isFinite = true
        ∧ (∀ i j, i < n → j < columns → |value (entry columns y i j)| ≤ (2 : ℝ) ^ (B + 96))
        ∧ ∀ i j,
            i < n
            → j < columns
            → |value (entry columns y i j)
                - (value (entry columns b i j)
                    - ∑ k ∈ Finset.range i,
                        value (entry n f.lower i k) * value (entry columns y k j))|
              ≤ i * (2 : ℝ) ^ (-48 : Int)
                * (|value (entry columns b i j)|
                    + ∑ k ∈ Finset.range i,
                        |value (entry n f.lower i k) * value (entry columns y k j)|
                    + (2 : ℝ) ^ (-1022 : Int)) := by
  obtain ⟨y, hy, hys, hyf, hyb⟩ :=
    LinearSolve.forward_success n columns B f b hn hB hB' hl hb hlb hbb
  refine ⟨y, hy, hys, hyf, hyb, ?_⟩
  intro i j hi hj
  let left := fun k => entry n f.lower i k
  let right := fun k => entry columns y k j
  let initial := entry columns b i j
  let M := |value initial| + productMass (List.range i) left right + (2 : ℝ)^(-1022 : Int)
  have hterm : ∀ k ∈ List.range i, |value (left k) * value (right k)| ≤ (2 : ℝ)^(615 : Int) := by
    intro k hk
    have hk' := List.mem_range.mp hk
    have h1 := hlb i k hi hk'
    have h2 := (hyb k j (by omega) hj).trans
      (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : B + 96 ≤ 608))
    change |value (entry n f.lower i k) * value (entry columns y k j)| ≤ _
    rw [abs_mul]
    calc
      _ ≤ 128 * (2 : ℝ) ^ (608 : Int) := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ = _ := by
        rw [show (615 : Int) = 608 + 7 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        rw [show (2 : ℝ)^(7 : Int) = 128 by norm_num]
        ring
  have hmass : productMass (List.range i) left right ≤ i * (2 : ℝ)^(615 : Int) := by
    unfold productMass
    calc
      _ ≤ ((List.range i).map (fun _ => (2 : ℝ) ^ (615 : Int))).sum := List.sum_le_sum hterm
      _ = _ := by simp
  have hinit : |value initial| ≤ (2 : ℝ)^(615 : Int) :=
    (hbb i j hi hj).trans (zpow_le_zpow_right₀ (by norm_num) (by omega))
  have hη : (2 : ℝ)^(-1022 : Int) ≤ (2 : ℝ)^(615 : Int) :=
    zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hM : M ≤ (2 : ℝ)^(990 : Int) := by
    have hi' : (i : ℝ) ≤ 12 := by exact_mod_cast (by omega : i ≤ 12)
    have hm := mul_le_mul_of_nonneg_right hi' (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (615 : Int))
    calc
      M ≤ (2 : ℝ) ^ (615 : Int) + 12 * (2 : ℝ) ^ (615 : Int) + (2 : ℝ) ^ (615 : Int) :=
        add_le_add (add_le_add hinit (hmass.trans hm)) hη
      _ = 14 * (2 : ℝ) ^ (615 : Int) := by ring
      _ ≤ 16 * (2 : ℝ) ^ (615 : Int) :=
        mul_le_mul_of_nonneg_right (by norm_num) (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      _ = (2 : ℝ) ^ (619 : Int) := by
        rw [show (619 : Int) = 615 + 4 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        rw [show (2 : ℝ)^(4 : Int) = 16 by norm_num]
        ring
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  obtain ⟨s, hs, _, herr⟩ := subtractProducts_accuracy (List.range i) left right initial M
    (by simp; omega) (Flare.Matrix.Storage.getD_finite _ _ hb)
    (fun _ _ => Flare.Matrix.Storage.getD_finite _ _ hl)
    (fun _ _ => Flare.Matrix.Storage.getD_finite _ _ hyf) hM (le_refl _)
  have he := forward_equations n columns f b y hy i j hi hj
  change subtractProducts (List.range i) left right initial = .ok (entry columns y i j) at he
  rw [he] at hs
  cases hs
  simpa only [M, productMass, left, right, initial, List.length_range,
    ← List.sum_toFinset _ (List.nodup_range (n := i)), List.toFinset_range]
    using herr

/-- The back-substitution row starts with a checked rounded division and then
runs exactly the same product/subtraction loop as forward substitution. -/
def divideSubtractProducts (indices : List Nat) (left right : Nat → Float)
    (numerator denominator : Float)
    : Except Flare.Matrix.DenseError Float := do
  let initial ← finite (numerator / denominator)
  subtractProducts indices left right initial

/-- The division-initialized native row loop has the same mass-scaled error
recurrence as the forward loop, with two additional units for division error. -/
theorem divideSubtractProducts_mass_accuracy (indices : List Nat) (left right : Nat → Float)
    (numerator denominator : Float) (hlen : indices.length ≤ 32)
    (hn : numerator.isFinite = true) (hd : denominator.isFinite = true)
    (hd0 : value denominator ≠ 0)
    (hl : ∀ k ∈ indices, (left k).isFinite = true)
    (hr : ∀ k ∈ indices, (right k).isFinite = true)
    (hM
      : |value numerator / value denominator|
          + (indices.map (fun k => |value (left k) * value (right k)|)).sum
          + (2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int)
        ≤ (2 : ℝ) ^ (990 : Int))
    : ∃ s,
        divideSubtractProducts indices left right numerator denominator = .ok s
        ∧ s.isFinite = true
        ∧ |value s
            - (value numerator / value denominator
                - (indices.map (fun k => value (left k) * value (right k))).sum)|
          ≤ (1001 / 1000 : ℝ) * (indices.length + 4) * (2 : ℝ) ^ (-53 : Int)
            * (|value numerator / value denominator|
                + (indices.map (fun k => |value (left k) * value (right k)|)).sum
                + (2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int)) := by
  have hq : |value numerator / value denominator| ≤ (2 : ℝ)^(990 : Int) := by
    apply le_trans _ hM
    change _ ≤ _ + productMass indices left right + _
    linarith [productMass_nonneg indices left right,
      mul_nonneg (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (20 : Int))
        (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-1022 : Int))]
  have hdv := Flare.Binary64.Nearest.div_error_nearest numerator denominator hn hd hd0
    (hq.trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)))
  have hinit : |value (numerator / denominator) - value numerator / value denominator| ≤
      (1001 / 1000 : ℝ) * (4 : Nat) * (2 : ℝ)^(-53 : Int) *
        (|value numerator / value denominator| + (2 : ℝ)^(20 : Int) * (2 : ℝ)^(-1022 : Int)) := by
    apply hdv.2.trans
    norm_num only [show (2 : ℝ)^(-53 : Int) = 1 / 9007199254740992 by norm_num,
      show (2 : ℝ)^(20 : Int) = 1048576 by norm_num, Nat.cast_ofNat]
    nlinarith [abs_nonneg (value numerator / value denominator),
      zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-1022 : Int)]
  obtain ⟨s, hs, hsf, hse⟩ := subtractProducts_mass_accuracy indices left right
    (numerator / denominator) (value numerator / value denominator) 4 hlen (by omega) (by omega)
    hdv.1 hl hr hM hinit
  refine ⟨s, ?_, hsf, hse⟩
  simp only [divideSubtractProducts, finite, hdv.1, ↓reduceIte, bind, Except.bind]
  exact hs

/-- Reuse the loop theorem after native division. The mass bound uses the exact
real quotient, not the rounded initial value. The additional rounding and
underflow error is absorbed into one extra term in the error allowance. -/
theorem divideSubtractProducts_accuracy (indices : List Nat) (left right : Nat → Float)
    (numerator denominator : Float) (M : ℝ) (hlen : indices.length ≤ 32)
    (hn : numerator.isFinite = true) (hd : denominator.isFinite = true)
    (hd0 : value denominator ≠ 0)
    (hl : ∀ k ∈ indices, (left k).isFinite = true)
    (hr : ∀ k ∈ indices, (right k).isFinite = true)
    (hM : M ≤ (2 : ℝ) ^ (980 : Int))
    (hmass
      : |value numerator / value denominator|
          + (indices.map (fun k => |value (left k) * value (right k)|)).sum
          + (2 : ℝ) ^ (-1022 : Int)
        ≤ M)
    : ∃ s,
        divideSubtractProducts indices left right numerator denominator = .ok s
        ∧ s.isFinite = true
        ∧ |value s
            - (value numerator / value denominator
                - (indices.map (fun k => value (left k) * value (right k))).sum)|
          ≤ (indices.length + 1 : Nat) * (2 : ℝ) ^ (-47 : Int) * M := by
  have hmass0 := productMass_nonneg indices left right
  change 0 ≤ (indices.map (fun k => |value (left k) * value (right k)|)).sum at hmass0
  have hη0 := zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-1022 : Int)
  have hM0 : 0 ≤ M := by linarith [abs_nonneg (value numerator / value denominator)]
  have hq : |value numerator / value denominator| ≤ M := by linarith
  have hround := Flare.Binary64.Nearest.div_error_nearest numerator denominator hn hd hd0
    (hq.trans (hM.trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num))))
  have herr : |value (numerator / denominator) - value numerator / value denominator| ≤
      (2 : ℝ)^(-53 : Int) * M := hround.2.trans
    (mul_le_mul_of_nonneg_left (by linarith) (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _))
  have hsmall : (2 : ℝ)^(-53 : Int) * M ≤ M := by
    exact (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ)^(-53 : Int) ≤ 1) hM0).trans_eq
      (one_mul _)
  have hmass' : |value (numerator / denominator)| +
      (indices.map (fun k => |value (left k) * value (right k)|)).sum +
        (2 : ℝ)^(-1022 : Int) ≤ 2 * M := by
    have ht := abs_sub_le (value (numerator / denominator)) (value numerator / value denominator) 0
    simp only [sub_zero] at ht
    linarith
  have hM' : 2 * M ≤ (2 : ℝ)^(990 : Int) := by
    calc
      _ ≤ 2 * (2 : ℝ) ^ (980 : Int) := mul_le_mul_of_nonneg_left hM (by norm_num)
      _ = (2 : ℝ) ^ (981 : Int) := by
        rw [show (981 : Int) = 980 + 1 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
        ring
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  obtain ⟨s, hs, hsf, hse⟩ := subtractProducts_accuracy indices left right (numerator / denominator)
    (2 * M) hlen hround.1 hl hr hM' hmass'
  refine ⟨s, ?_, hsf, ?_⟩
  · simp only [divideSubtractProducts, finite, hround.1, ↓reduceIte, bind, Except.bind]
    exact hs
  · let S := (indices.map (fun k => value (left k) * value (right k))).sum
    have heq : value s - (value numerator / value denominator - S) =
        (value s - (value (numerator / denominator) - S)) +
          (value (numerator / denominator) - value numerator / value denominator) := by ring
    change |value s - (value numerator / value denominator - S)| ≤ _
    rw [heq]
    have ht := abs_add_le (value s - (value (numerator / denominator) - S))
      (value (numerator / denominator) - value numerator / value denominator)
    change |value s - (value (numerator / denominator) - S)| ≤
      indices.length * (2 : ℝ)^(-48 : Int) * (2 * M) at hse
    simp only [Nat.cast_add, Nat.cast_one]
    norm_num only [show (2 : ℝ)^(-53 : Int) = 1 / 9007199254740992 by norm_num,
      show (2 : ℝ)^(-48 : Int) = 1 / 281474976710656 by norm_num,
      show (2 : ℝ)^(-47 : Int) = 1 / 140737488355328 by norm_num] at herr hse ⊢
    linarith

/-- The backward pass expressed using the same verified row-loop building block. -/
def backwardByProducts (n columns : Nat) (f : Factor) (y : Array Float)
    : Except Flare.Matrix.DenseError (Array Float) := do
  let mut r := Array.replicate (n * columns) 0.0
  for step in [:n] do
    let i := n - 1 - step
    for j in [:columns] do
      let s ←
        divideSubtractProducts (List.range' (i + 1) (n - (i + 1)))
          (fun k => entry n f.lower k i) (fun k => entry columns r k j)
          (entry columns y i j) (f.diagonal.getD i 0.0)
      r := r.set! (i * columns + j) s
  return r

/-- Every arithmetic operation and finite check in the native backward pass
matches the division-initialized row loop analyzed above. -/
theorem backward_eq (n columns : Nat) (f : Factor) (y : Array Float)
    : LinearSolve.backward n columns f y = backwardByProducts n columns f y := by
  unfold LinearSolve.backward backwardByProducts divideSubtractProducts subtractProducts
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one, ← List.range_eq_range']
  simp only [bind_assoc, pure_bind]

/-- Both halves of the actual native solve use the shared row-loop arithmetic.
This is equality of execution schedules, not an assumed solver contract. -/
theorem solve_eq (n columns : Nat) (f : Factor) (b : Array Float)
    : solve n columns f b
      = (do
          backwardByProducts n columns f (← forwardByProducts n columns f b)) := by
  rw [LinearSolve.solve_split, forward_eq]
  simp only [backward_eq]

/-- The initialized row loop only depends on entries at the visited indices. -/
lemma divideSubtractProducts_congr (indices : List Nat) (left right left' right' : Nat → Float)
    (numerator denominator : Float) (hl : ∀ k ∈ indices, left k = left' k)
    (hr : ∀ k ∈ indices, right k = right' k)
    : divideSubtractProducts indices left right numerator denominator
      = divideSubtractProducts indices left' right' numerator denominator := by
  unfold divideSubtractProducts
  simp only [subtractProducts_congr indices left right left' right' _ hl hr]

@[local spec]
private lemma divideSubtractProducts_result (indices : List Nat)
    (left right : Nat → Float) (numerator denominator : Float)
    : ⦃⌜True⌝
      ⦄ divideSubtractProducts indices left right numerator denominator
      ⦃⇓? s => ⌜divideSubtractProducts indices left right numerator denominator = .ok s⌝⦄ := by
  generalize he : divideSubtractProducts indices left right numerator denominator = result
  cases result with
  | error e => exact fun _ => True.intro
  | ok value => exact fun _ => rfl

open scoped Std.WP in
@[local spec]
private theorem divideSubtractProducts_wp_result (indices : List Nat)
    (left right : Nat → Float) (numerator denominator : Float)
    : Std.WP.Triple (divideSubtractProducts indices left right numerator denominator) True
        (fun s => divideSubtractProducts indices left right numerator denominator = .ok s)
        (fun _ => True) :=
  (Specification.except_iff _ _ _).mp
    (divideSubtractProducts_result indices left right numerator denominator)

private def BackwardEquations (n columns : Nat) (f : Factor) (y : Array Float)
    (step j : Nat) (r : Array Float)
    : Prop :=
  r.size = n * columns
  ∧ ∀ a c,
      a < n
      → c < columns
      → n - 1 - a < step ∨ n - 1 - a = step ∧ c < j
      → divideSubtractProducts (List.range' (a + 1) (n - (a + 1)))
          (fun k => entry n f.lower k a) (fun k => entry columns r k c)
          (entry columns y a c) (f.diagonal.getD a 0.0)
        = .ok (entry columns r a c)

private lemma backward_write (n columns : Nat) (f : Factor) (y r : Array Float)
    (step j : Nat) (s : Float) (ht : step < n) (hj : j < columns)
    (hr : BackwardEquations n columns f y step j r)
    (hs
      : divideSubtractProducts (List.range' (n - 1 - step + 1) (n - (n - 1 - step + 1)))
          (fun k => entry n f.lower k (n - 1 - step)) (fun k => entry columns r k j)
          (entry columns y (n - 1 - step) j) (f.diagonal.getD (n - 1 - step) 0.0)
        = .ok s)
    : BackwardEquations n columns f y step (j + 1) (r.set! ((n - 1 - step) * columns + j) s) := by
  let i := n - 1 - step
  have hi : i < n := by dsimp [i]; omega
  refine ⟨(Array.size_set! ..).trans hr.1, ?_⟩
  intro a c ha hc hac
  have hai : i ≤ a := by dsimp [i]; omega
  have reads :
      divideSubtractProducts (List.range' (a + 1) (n - (a + 1)))
        (fun k => entry n f.lower k a) (fun k => entry columns (r.set! (i * columns + j) s) k c)
        (entry columns y a c) (f.diagonal.getD a 0.0) =
      divideSubtractProducts (List.range' (a + 1) (n - (a + 1)))
        (fun k => entry n f.lower k a) (fun k => entry columns r k c)
        (entry columns y a c) (f.diagonal.getD a 0.0) := by
    apply divideSubtractProducts_congr _ _ _ _ _ _ _ (by intros; rfl)
    intro k hk
    obtain ⟨t, _, hkt⟩ := List.mem_range'.mp hk
    have hki : k ≠ i := by omega
    rw [Flare.Matrix.Storage.entry_set columns r i j k c s hr.1 hi hj hc]
    simp [hki]
  change divideSubtractProducts _ _
    (fun k => entry columns (r.set! (i * columns + j) s) k c) _ _ = _
  rw [reads, Flare.Matrix.Storage.entry_set columns r i j a c s hr.1 hi hj hc]
  split
  · rename_i he
    obtain ⟨rfl, rfl⟩ := he
    exact hs
  · apply hr.2 a c ha hc
    dsimp [i] at *
    omega

private theorem backward_equations_triple (n columns : Nat) (f : Factor) (y : Array Float)
    : ⦃⌜True⌝
      ⦄ backwardByProducts n columns f y
      ⦃⇓? r => ⌜BackwardEquations n columns f y n 0 r⌝⦄ := by
  unfold backwardByProducts
  apply (Specification.except_iff _ _ _).mpr
  vcgen
    invariants
      | inv1 => fun xs _ r => BackwardEquations n columns f y xs.length 0 r
      | inv2 pref t suff ht initial hs =>
        fun xs _ r => BackwardEquations n columns f y t xs.length r
  all_goals simp_all only [SPred.down_pure_nil]
  case vc1 => simp [BackwardEquations, r]
  case vc2 =>
    rename_i r hr
    simpa [Std.Legacy.Range.size] using hr
  case vc3 =>
    rename_i pref t suff hlist current hcurrent
    simpa only [(Flare.Matrix.Storage.forIn_range_current hlist).1, List.length_nil] using hcurrent
  case vc4 =>
    rename_i pref t suff hlist initial hinit current hcurrent
    have hr' : BackwardEquations n columns f y t columns current := by
      simpa [Std.Legacy.Range.size] using hcurrent
    refine ⟨hr'.1, ?_⟩
    intro a c ha hc hac
    apply hr'.2 a c ha hc
    have hstep := (Flare.Matrix.Storage.forIn_range_current hlist).1
    simp only [List.length_append, List.length_singleton] at hac
    omega
  case vc5 => trivial
  case vc6 =>
    rename_i prefI t suffI hi initial hinit prefJ j suffJ hj current hcurrent hs
    have hj' := Flare.Matrix.Storage.forIn_range_current hj
    have hh := backward_write n columns f y current t j s
      (Flare.Matrix.Storage.forIn_range_current hi).2 hj'.2
      (by simpa only [hj'.1] using hcurrent) hs
    simpa only [List.length_append, List.length_singleton, ← hj'.1] using hh

/-- Stored backward entries are the actual native row-loop outputs reading
later rows of the final result. Every array write preserves those dependencies. -/
theorem backward_equations (n columns : Nat) (f : Factor) (y r : Array Float)
    (hr : LinearSolve.backward n columns f y = .ok r)
    : ∀ i j,
        i < n
        → j < columns
        → divideSubtractProducts (List.range' (i + 1) (n - (i + 1)))
            (fun k => entry n f.lower k i) (fun k => entry columns r k j)
            (entry columns y i j) (f.diagonal.getD i 0.0)
          = .ok (entry columns r i j) := by
  have h := backward_equations_triple n columns f y
  rw [← backward_eq, hr] at h
  intro i j hi hj
  exact (h True.intro).2 i j hi hj (Or.inl (by omega))

/-- Native backward substitution succeeds and satisfies a componentwise residual
bound against the exact quotient of the supplied Float values. The forward-pass
magnitude profile suffices; neither successful execution nor accuracy is assumed. -/
theorem backward_accuracy (n columns : Nat) (B : Int) (f : Factor) (y : Array Float)
    (hn : n ≤ 12) (hB : 0 ≤ B) (hB' : B ≤ 512)
    (hl : f.lower.all Float.isFinite = true) (hd : f.diagonal.all Float.isFinite = true)
    (hy : y.all Float.isFinite = true)
    (hlb : ∀ i k, i < n → k < i → |value (entry n f.lower i k)| ≤ 128)
    (hdb : ∀ i, i < n → (1 / 8 : ℝ) ≤ value (f.diagonal.getD i 0.0))
    (hyb : ∀ i j, i < n → j < columns → |value (entry columns y i j)| ≤ (2 : ℝ) ^ (B + 96))
    : ∃ r,
        LinearSolve.backward n columns f y = .ok r
        ∧ r.size = n * columns
        ∧ r.all Float.isFinite = true
        ∧ (∀ i j, i < n → j < columns → |value (entry columns r i j)| ≤ (2 : ℝ) ^ (B + 232))
        ∧ ∀ i j,
            i < n
            → j < columns
            → |value (entry columns r i j)
                - (value (entry columns y i j) / value (f.diagonal.getD i 0.0)
                    - ∑ k ∈ Finset.Ico (i + 1) n,
                        value (entry n f.lower k i) * value (entry columns r k j))|
              ≤ (n - i : Nat) * (2 : ℝ) ^ (-47 : Int)
                * (|value (entry columns y i j) / value (f.diagonal.getD i 0.0)|
                    + ∑ k ∈ Finset.Ico (i + 1) n,
                        |value (entry n f.lower k i) * value (entry columns r k j)|
                    + (2 : ℝ) ^ (-1022 : Int)) := by
  obtain ⟨r, hr, hrs, hrf, hrb⟩ :=
    LinearSolve.backward_success n columns B f y hn hB hB' hl hd hy hlb hdb hyb
  refine ⟨r, hr, hrs, hrf, hrb, ?_⟩
  intro i j hi hj
  let indices := List.range' (i + 1) (n - (i + 1))
  let left := fun k => entry n f.lower k i
  let right := fun k => entry columns r k j
  let numerator := entry columns y i j
  let denominator := f.diagonal.getD i 0.0
  let M :=
    |value numerator / value denominator| + productMass indices left right + (2 : ℝ)^(-1022 : Int)
  have hdp : 0 < value denominator := by have := hdb i hi; dsimp [denominator]; linarith
  have hterm : ∀ k ∈ indices, |value (left k) * value (right k)| ≤ (2 : ℝ)^(751 : Int) := by
    intro k hk
    obtain ⟨t, ht, hkt⟩ := List.mem_range'.mp hk
    have hki : i < k := by omega
    have hkn : k < n := by omega
    have h1 := hlb k i hkn hki
    have h2 := (hrb k j hkn hj).trans
      (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : B + 232 ≤ 744))
    change |value (entry n f.lower k i) * value (entry columns r k j)| ≤ _
    rw [abs_mul]
    calc
      _ ≤ 128 * (2 : ℝ) ^ (744 : Int) := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ = _ := by
        rw [show (751 : Int) = 744 + 7 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        rw [show (2 : ℝ)^(7 : Int) = 128 by norm_num]
        ring
  have hmass : productMass indices left right ≤ 12 * (2 : ℝ)^(751 : Int) := by
    have hlen : (indices.length : ℝ) ≤ 12 := by
      dsimp [indices]; simp only [List.length_range']; exact_mod_cast (by omega : n - (i + 1) ≤ 12)
    calc
      _ ≤ (indices.map (fun _ => (2 : ℝ) ^ (751 : Int))).sum := List.sum_le_sum hterm
      _ = indices.length * (2 : ℝ) ^ (751 : Int) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hlen (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have hq : |value numerator / value denominator| ≤ (2 : ℝ)^(751 : Int) := by
    have hy' := (hyb i j hi hj).trans
      (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : B + 96 ≤ 608))
    rw [abs_div, abs_of_pos hdp]
    calc
      _ ≤ 8 * (2 : ℝ) ^ (608 : Int) := by
        apply (div_le_iff₀ hdp).mpr
        have hm := mul_le_mul_of_nonneg_left (hdb i hi)
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8)
            (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (608 : Int)))
        change |value numerator| ≤ (2 : ℝ)^(608 : Int) at hy'
        change 8 * (2 : ℝ)^(608 : Int) * (1 / 8) ≤ 8 * (2 : ℝ)^(608 : Int) * value denominator at hm
        calc
          _ ≤ (2 : ℝ) ^ (608 : Int) := hy'
          _ = 8 * (2 : ℝ) ^ (608 : Int) * (1 / 8) := by ring
          _ ≤ _ := hm
      _ = (2 : ℝ) ^ (611 : Int) := by
        rw [show (611 : Int) = 608 + 3 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        rw [show (2 : ℝ)^(3 : Int) = 8 by norm_num]
        ring
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hη : (2 : ℝ)^(-1022 : Int) ≤ (2 : ℝ)^(751 : Int) :=
    zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hM : M ≤ (2 : ℝ)^(980 : Int) := by
    calc
      M ≤ (2 : ℝ) ^ (751 : Int) + 12 * (2 : ℝ) ^ (751 : Int) + (2 : ℝ) ^ (751 : Int) :=
        add_le_add (add_le_add hq hmass) hη
      _ = 14 * (2 : ℝ) ^ (751 : Int) := by ring
      _ ≤ 16 * (2 : ℝ) ^ (751 : Int) :=
        mul_le_mul_of_nonneg_right (by norm_num) (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      _ = (2 : ℝ) ^ (755 : Int) := by
        rw [show (755 : Int) = 751 + 4 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        rw [show (2 : ℝ)^(4 : Int) = 16 by norm_num]
        ring
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  obtain ⟨s, hs, _, herr⟩ :=
    divideSubtractProducts_accuracy indices left right numerator denominator M
    (by dsimp [indices]; simp only [List.length_range']; omega)
    (Flare.Matrix.Storage.getD_finite _ _ hy) (Flare.Matrix.Storage.getD_finite _ _ hd)
    (ne_of_gt hdp) (fun _ _ => Flare.Matrix.Storage.getD_finite _ _ hl)
    (fun _ _ => Flare.Matrix.Storage.getD_finite _ _ hrf) hM (le_refl _)
  have he := backward_equations n columns f y r hr i j hi hj
  change divideSubtractProducts indices left right numerator denominator =
    .ok (entry columns r i j) at he
  rw [he] at hs
  cases hs
  have hfinset : indices.toFinset = Finset.Ico (i + 1) n := by
    rw [List.toFinset_range'_1, Nat.add_sub_of_le (by omega : i + 1 ≤ n)]
  have hlen : indices.length + 1 = n - i := by
    dsimp [indices]; simp only [List.length_range']; omega
  have hnodup : indices.Nodup := List.nodup_range'
  simpa only [M, productMass, left, right, numerator, denominator, hlen,
    ← List.sum_toFinset _ hnodup, hfinset]
    using herr

private lemma product_magnitude (l x : ℝ) (hl : |l| ≤ 128) (hx : |x| ≤ (2 : ℝ) ^ (800 : Int))
    : |l * x| ≤ (2 : ℝ) ^ (900 : Int) := by
  rw [abs_mul]
  calc
    _ ≤ 128 * (2 : ℝ) ^ (800 : Int) := mul_le_mul hl hx (abs_nonneg _) (by norm_num)
    _ = (2 : ℝ) ^ (807 : Int) := by
      rw [show (807 : Int) = 800 + 7 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      rw [show (2 : ℝ)^(7 : Int) = 128 by norm_num]; ring
    _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)

private lemma row_mass_bound (indices : List Nat) (left right : Nat → Float) (target : ℝ)
    (hlen : indices.length ≤ 32) (hi : |target| ≤ (2 : ℝ) ^ (900 : Int))
    (ht : ∀ k ∈ indices, |value (left k) * value (right k)| ≤ (2 : ℝ) ^ (900 : Int))
    : |target|
        + (indices.map (fun k => |value (left k) * value (right k)|)).sum
        + (2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int)
      ≤ (2 : ℝ) ^ (990 : Int) := by
  have hsum : (indices.map (fun k => |value (left k) * value (right k)|)).sum ≤
      32 * (2 : ℝ)^(900 : Int) := by
    have hn : (indices.length : ℝ) ≤ 32 := by exact_mod_cast hlen
    calc
      _ ≤ (indices.map (fun _ => (2 : ℝ) ^ (900 : Int))).sum := List.sum_le_sum ht
      _ = indices.length * (2 : ℝ) ^ (900 : Int) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hn (by positivity)
  have hη : (2 : ℝ)^(20 : Int) * (2 : ℝ)^(-1022 : Int) ≤ (2 : ℝ)^(900 : Int) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    exact zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  calc
    _ ≤ (2 : ℝ) ^ (900 : Int) + 32 * (2 : ℝ) ^ (900 : Int) + (2 : ℝ) ^ (900 : Int) :=
      add_le_add (add_le_add hi hsum) hη
    _ ≤ 64 * (2 : ℝ) ^ (900 : Int) := by
      calc
        _ = 34 * (2 : ℝ) ^ (900 : Int) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = (2 : ℝ) ^ (906 : Int) := by
      rw [show (906 : Int) = 900 + 6 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      rw [show (2 : ℝ)^(6 : Int) = 64 by norm_num]; ring
    _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)

/-- Complete forward substitution with a mass-scaled rounding bound.
Successful native execution and finite stored values remain conclusions. -/
theorem forward_mass_accuracy (n columns : Nat) (B : Int) (f : Factor) (b : Array Float)
    (hn : n ≤ 12) (hB : 0 ≤ B) (hB' : B ≤ 512)
    (hl : f.lower.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hlb : ∀ i k, i < n → k < i → |value (entry n f.lower i k)| ≤ 128)
    (hbb : ∀ i j, i < n → j < columns → |value (entry columns b i j)| ≤ (2 : ℝ) ^ B)
    : ∃ y,
        LinearSolve.forward n columns f b = .ok y
        ∧ y.size = n * columns
        ∧ y.all Float.isFinite = true
        ∧ (∀ i j, i < n → j < columns → |value (entry columns y i j)| ≤ (2 : ℝ) ^ (B + 96))
        ∧ ∀ i j,
            i < n
            → j < columns
            → |value (entry columns y i j)
                - (value (entry columns b i j)
                    - ∑ k ∈ Finset.range i,
                        value (entry n f.lower i k) * value (entry columns y k j))|
              ≤ (1001 / 1000 : ℝ) * (i + 2) * (2 : ℝ) ^ (-53 : Int)
                * (|value (entry columns b i j)|
                    + ∑ k ∈ Finset.range i,
                        |value (entry n f.lower i k) * value (entry columns y k j)|
                    + (2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int)) := by
  obtain ⟨y, hy, hys, hyf, hyb⟩ :=
    LinearSolve.forward_success n columns B f b hn hB hB' hl hb hlb hbb
  refine ⟨y, hy, hys, hyf, hyb, ?_⟩
  intro i j hi hj
  let left := fun k => entry n f.lower i k
  let right := fun k => entry columns y k j
  let initial := entry columns b i j
  have hlen : (List.range i).length ≤ 32 := by simp; omega
  have hM := row_mass_bound (List.range i) left right (value initial) hlen
    ((hbb i j hi hj).trans (zpow_le_zpow_right₀ (by norm_num) (by omega))) (by
      intro k hk
      have hk' := List.mem_range.mp hk
      exact product_magnitude _ _ (hlb i k hi hk') ((hyb k j (by omega) hj).trans
        (zpow_le_zpow_right₀ (by norm_num) (by omega : B + 96 ≤ 800))))
  obtain ⟨r, hr, _, herr⟩ := subtractProducts_mass_accuracy (List.range i) left right initial
    (value initial) 2 hlen (by omega) (by omega) (Flare.Matrix.Storage.getD_finite _ _ hb)
    (fun _ _ => Flare.Matrix.Storage.getD_finite _ _ hl)
    (fun _ _ => Flare.Matrix.Storage.getD_finite _ _ hyf) hM (by
      rw [sub_self, abs_zero]; positivity)
  have he := forward_equations n columns f b y hy i j hi hj
  change subtractProducts (List.range i) left right initial = .ok (entry columns y i j) at he
  have hre : r = entry columns y i j := Except.ok.inj (hr.symm.trans he)
  subst r
  simpa only [left, right, initial, List.length_range, Nat.cast_ofNat,
    ← List.sum_toFinset _ (List.nodup_range (n := i)), List.toFinset_range]
    using herr

/-- Complete backward substitution, including the rounded pivot division,
with a mass-scaled residual bound against its stored operands. -/
theorem backward_mass_accuracy (n columns : Nat) (B : Int) (f : Factor) (y : Array Float)
    (hn : n ≤ 12) (hB : 0 ≤ B) (hB' : B ≤ 512)
    (hl : f.lower.all Float.isFinite = true) (hd : f.diagonal.all Float.isFinite = true)
    (hy : y.all Float.isFinite = true)
    (hlb : ∀ i k, i < n → k < i → |value (entry n f.lower i k)| ≤ 128)
    (hdb : ∀ i, i < n → (1 / 8 : ℝ) ≤ value (f.diagonal.getD i 0.0))
    (hyb : ∀ i j, i < n → j < columns → |value (entry columns y i j)| ≤ (2 : ℝ) ^ (B + 96))
    : ∃ r,
        LinearSolve.backward n columns f y = .ok r
        ∧ r.size = n * columns
        ∧ r.all Float.isFinite = true
        ∧ (∀ i j, i < n → j < columns → |value (entry columns r i j)| ≤ (2 : ℝ) ^ (B + 232))
        ∧ ∀ i j,
            i < n
            → j < columns
            → |value (entry columns r i j)
                - (value (entry columns y i j) / value (f.diagonal.getD i 0.0)
                    - ∑ k ∈ Finset.Ico (i + 1) n,
                        value (entry n f.lower k i) * value (entry columns r k j))|
              ≤ (1001 / 1000 : ℝ) * ((n - i : Nat) + 3) * (2 : ℝ) ^ (-53 : Int)
                * (|value (entry columns y i j) / value (f.diagonal.getD i 0.0)|
                    + ∑ k ∈ Finset.Ico (i + 1) n,
                        |value (entry n f.lower k i) * value (entry columns r k j)|
                    + (2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int)) := by
  obtain ⟨r, hr, hrs, hrf, hrb⟩ :=
    LinearSolve.backward_success n columns B f y hn hB hB' hl hd hy hlb hdb hyb
  refine ⟨r, hr, hrs, hrf, hrb, ?_⟩
  intro i j hi hj
  let indices := List.range' (i + 1) (n - (i + 1))
  let left := fun k => entry n f.lower k i
  let right := fun k => entry columns r k j
  let numerator := entry columns y i j
  let denominator := f.diagonal.getD i 0.0
  have hdp : 0 < value denominator := by have := hdb i hi; dsimp [denominator]; linarith
  have hlen : indices.length ≤ 32 := by dsimp [indices]; simp only [List.length_range']; omega
  have hq : |value numerator / value denominator| ≤ (2 : ℝ)^(900 : Int) := by
    have hy' : |value numerator| ≤ (2 : ℝ)^(800 : Int) := (hyb i j hi hj).trans
      (zpow_le_zpow_right₀ (by norm_num) (by omega))
    rw [abs_div, abs_of_pos hdp]
    calc
      _ ≤ 8 * (2 : ℝ) ^ (800 : Int) := by
        apply (div_le_iff₀ hdp).mpr
        have hh := mul_le_mul_of_nonneg_left (hdb i hi)
          (by positivity : 0 ≤ 8 * (2 : ℝ)^(800 : Int))
        change 8 * (2 : ℝ)^(800 : Int) * (1 / 8) ≤ 8 * (2 : ℝ)^(800 : Int) * value denominator at hh
        nlinarith only [hh, hy']
      _ = (2 : ℝ) ^ (803 : Int) := by
        rw [show (803 : Int) = 800 + 3 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        rw [show (2 : ℝ)^(3 : Int) = 8 by norm_num]; ring
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hM := row_mass_bound indices left right (value numerator / value denominator) hlen hq (by
    intro k hk
    obtain ⟨t, ht, hkt⟩ := List.mem_range'.mp hk
    have hki : i < k := by omega
    have hkn : k < n := by omega
    exact product_magnitude _ _ (hlb k i hkn hki) ((hrb k j hkn hj).trans
      (zpow_le_zpow_right₀ (by norm_num) (by omega : B + 232 ≤ 800))))
  obtain ⟨x, hx, _, herr⟩ :=
    divideSubtractProducts_mass_accuracy indices left right numerator denominator hlen
    (Flare.Matrix.Storage.getD_finite _ _ hy) (Flare.Matrix.Storage.getD_finite _ _ hd)
    hdp.ne' (fun _ _ => Flare.Matrix.Storage.getD_finite _ _ hl)
    (fun _ _ => Flare.Matrix.Storage.getD_finite _ _ hrf) hM
  have he := backward_equations n columns f y r hr i j hi hj
  change divideSubtractProducts indices left right numerator denominator =
    .ok (entry columns r i j) at he
  have hxe : x = entry columns r i j := Except.ok.inj (hx.symm.trans he)
  subst x
  have hfinset : indices.toFinset = Finset.Ico (i + 1) n := by
    rw [List.toFinset_range'_1, Nat.add_sub_of_le (by omega : i + 1 ≤ n)]
  have hlength : (indices.length : ℝ) + 4 = (n - i : Nat) + 3 := by
    have hh : indices.length + 4 = n - i + 3 := by
      dsimp [indices]; simp only [List.length_range']; omega
    exact_mod_cast hh
  have hnodup : indices.Nodup := List.nodup_range'
  simpa only [left, right, numerator, denominator, hlength, ← List.sum_toFinset _ hnodup, hfinset]
    using herr

end Flare.Matrix.Substitution
