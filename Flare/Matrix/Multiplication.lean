import Flare.Binary64.Zero
import Flare.Matrix.OperationStorage
import Flare.Analysis.JacobiNorms

/-! Native dense multiplication: finite execution and forward error relative to
the exact real product of the supplied binary64 arrays. These lemmas analyze the
actual ascending, separately rounded multiply/add loop in Dense.
-/

namespace Flare.Matrix.Multiplication
open Flare.Matrix.Value Flare.Binary64.Value Flare.Binary64.Arithmetic
open Std.Do Flare.Matrix.Dense
open scoped Matrix.Norms.L2Operator

set_option mvcgen.warning false

/-- Lift elementwise successful evaluation to an actual array map. -/
lemma mapM_eq_ok_map {α β ε : Type} (a : Array α) (f : α → Except ε β)
    (g : α → β) (h : ∀ x ∈ a.toList, f x = .ok (g x))
    : a.mapM f = .ok (a.map g) := by
  rw [Array.mapM_eq_mapM_toList]
  have hl (l : List α) (h : ∀ x ∈ l, f x = .ok (g x)) :
      l.mapM f = .ok (l.map g) := by
    induction l with
    | nil => rfl
    | cons x xs ih =>
        rw [List.mapM_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]
        rfl
  rw [hl a.toList h]
  simp only [Except.map, Functor.map]
  congr 1
  apply Array.toList_inj.mp
  simp

private lemma power_sub (E k : Int) : (2 : ℝ)^(E - k) = (2 : ℝ)^E / (2 : ℝ)^k :=
  zpow_sub₀ (by norm_num) _ _

/-- One dot-product step, including successful finite multiplication and addition.
The exponent bounds magnitudes of exact terms, not the individual operands. -/
lemma dot_step (E : Int) (k : Nat) (a b s : Float) (prefixSum : ℝ)
    (hE : 0 ≤ E) (hE' : E ≤ 1016) (hk : k ≤ 31)
    (ha : a.isFinite = true) (hb : b.isFinite = true) (hs : s.isFinite = true)
    (ht : |value a * value b| ≤ (2 : ℝ)^E)
    (hp : |prefixSum| ≤ k * (2 : ℝ)^E)
    (herr : |value s - prefixSum| ≤ k * (2 : ℝ)^(E - 45))
    : (a * b).isFinite = true
      ∧ (s + a * b).isFinite = true
      ∧ |value (s + a * b) - (prefixSum + value a * value b)|
        ≤ (k + 1 : Nat) * (2 : ℝ)^(E - 45) := by
  have hr : 0 < (2 : ℝ)^E := zpow_pos (by norm_num) _
  have hk' : (k : ℝ) ≤ 31 := by exact_mod_cast hk
  have hm := mul_error a b E ha hb (by omega) (by omega) ht
  have hsbound : |value s| ≤ 32 * (2 : ℝ)^E := by
    have htri := abs_add_le (value s - prefixSum) prefixSum
    rw [sub_add_cancel] at htri
    rw [power_sub] at herr
    norm_num only [zpow_ofNat, pow_succ, pow_zero] at herr
    have hkr := mul_le_mul_of_nonneg_right hk' hr.le
    nlinarith
  have htbound : |value (a * b)| ≤ 2 * (2 : ℝ)^E := by
    have htri := abs_add_le (value (a * b) - value a * value b) (value a * value b)
    rw [sub_add_cancel] at htri
    rw [power_sub] at hm
    norm_num only [zpow_ofNat, pow_succ, pow_zero] at hm
    linarith [hm.2]
  have ha' := add_error s (a * b) (E + 6) hs hm.1 (by omega) (by omega) (by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num only [zpow_ofNat, pow_succ, pow_zero]
    linarith [abs_add_le (value s) (value (a * b))])
  refine ⟨hm.1, ha'.1, ?_⟩
  have htri := abs_add_le
    (value (s + a * b) - (value s + value (a * b)))
    ((value (a * b) - value a * value b) + (value s - prefixSum))
  have htri' := abs_add_le (value (a * b) - value a * value b) (value s - prefixSum)
  have he : value (s + a * b) - (value s + value (a * b)) +
      (value (a * b) - value a * value b + (value s - prefixSum)) =
      value (s + a * b) - (prefixSum + value a * value b) := by ring
  rw [he] at htri
  have hexp : E + 6 - 52 = E - 46 := by omega
  rw [hexp] at ha'
  simp only [power_sub, Nat.cast_add, Nat.cast_one] at hm ha' herr ⊢
  norm_num only [zpow_ofNat, pow_succ, pow_zero] at hm ha' herr ⊢
  nlinarith [hm.2, ha'.2]

/-- A dot-product step controlled by the total absolute term mass. This
keeps cancellation separate from roundoff and includes gradual underflow. -/
lemma dot_relative_step (a b s : Float) (exact M : ℝ) (k : Nat)
    (ha : a.isFinite = true) (hb : b.isFinite = true) (hs : s.isFinite = true)
    (hk : k ≤ 31) (hM : M ≤ (2 : ℝ)^(990 : Int))
    (hη : (2 : ℝ)^(-1022 : Int) ≤ M)
    (ht : |value a * value b| ≤ M) (he : |exact| ≤ M)
    (herr : |value s - exact| ≤ k * (2 : ℝ)^(-48 : Int) * M)
    : (a * b).isFinite = true
      ∧ (s + a * b).isFinite = true
      ∧ |value (s + a * b) - (exact + value a * value b)|
        ≤ (k + 1 : Nat) * (2 : ℝ)^(-48 : Int) * M := by
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
      _ ≤ 4 * (2 : ℝ)^(990 : Int) := mul_le_mul_of_nonneg_left hM (by norm_num)
      _ = (2 : ℝ)^(992 : Int) := by
        rw [show (992 : Int) = 990 + 2 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        rw [show (2 : ℝ)^(2 : Int) = 4 by norm_num]; ring
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hm := mul_error_relative a b ha hb (ht.trans ((by linarith only [hM0] : M ≤ 4 * M).trans
    hlim))
  have hprod : |value (a * b)| ≤ 2 * M := by
    have hh := abs_sub_le (value (a * b)) (value a * value b) 0
    simp only [sub_zero] at hh
    have he' := hm.2
    norm_num only [show (2 : ℝ)^(-51 : Int) = 1 / 2251799813685248 by norm_num] at he'
    nlinarith
  have hadd := add_error_relative s (a * b) hs hm.1
    ((abs_add_le _ _).trans (by linarith only [hsbound, hprod, hlim]))
  refine ⟨hm.1, hadd.1, ?_⟩
  have heq : value (s + a * b) - (exact + value a * value b) =
      (value (s + a * b) - (value s + value (a * b))) +
      (value (a * b) - value a * value b) + (value s - exact) := by ring
  rw [heq]
  have htri := (abs_add_le
    ((value (s + a * b) - (value s + value (a * b))) + (value (a * b) - value a * value b))
    (value s - exact)).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hmerr := hm.2
  have haerr := hadd.2
  have habs := abs_add_le (value s) (value (a * b))
  simp only [Nat.cast_add, Nat.cast_one]
  norm_num only [show (2 : ℝ)^(-51 : Int) = 1 / 2251799813685248 by norm_num,
    show (2 : ℝ)^(-48 : Int) = 1 / 281474976710656 by norm_num] at hmerr haerr herr ⊢
  linarith

/-- A dot-product step controlled by the total absolute term mass. This
keeps cancellation separate from roundoff and includes gradual underflow. -/
lemma dot_nearest_step (a b s : Float) (exact M : ℝ) (k : Nat)
    (ha : a.isFinite = true) (hb : b.isFinite = true) (hs : s.isFinite = true)
    (hk : k ≤ 31) (hM : M ≤ (2 : ℝ)^(990 : Int))
    (hη : (2 : ℝ)^(-1022 : Int) ≤ M)
    (ht : |value a * value b| ≤ M) (he : |exact| ≤ M)
    (herr : |value s - exact| ≤ k * (2 : ℝ)^(-50 : Int) * M)
    : (a * b).isFinite = true
      ∧ (s + a * b).isFinite = true
      ∧ |value (s + a * b) - (exact + value a * value b)|
        ≤ (k + 1 : Nat) * (2 : ℝ)^(-50 : Int) * M := by
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
      _ ≤ 4 * (2 : ℝ)^(990 : Int) := mul_le_mul_of_nonneg_left hM (by norm_num)
      _ = (2 : ℝ)^(992 : Int) := by
        rw [show (992 : Int) = 990 + 2 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        rw [show (2 : ℝ)^(2 : Int) = 4 by norm_num]; ring
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hm := Flare.Binary64.Nearest.mul_error_nearest a b ha hb (ht.trans ((by linarith only [hM0] :
    M ≤ 4 * M).trans hlim))
  have hprod : |value (a * b)| ≤ 2 * M := by
    have hh := abs_sub_le (value (a * b)) (value a * value b) 0
    simp only [sub_zero] at hh
    have he' := hm.2
    norm_num only [show (2 : ℝ)^(-53 : Int) = 1 / 9007199254740992 by norm_num] at he'
    nlinarith
  have hadd := Flare.Binary64.Nearest.add_error_nearest s (a * b) hs hm.1
    ((abs_add_le _ _).trans (by linarith only [hsbound, hprod, hlim]))
  refine ⟨hm.1, hadd.1, ?_⟩
  have heq : value (s + a * b) - (exact + value a * value b) =
      (value (s + a * b) - (value s + value (a * b))) +
      (value (a * b) - value a * value b) + (value s - exact) := by ring
  rw [heq]
  have htri := (abs_add_le
    ((value (s + a * b) - (value s + value (a * b))) + (value (a * b) - value a * value b))
    (value s - exact)).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hmerr := hm.2
  have haerr := hadd.2
  have habs := abs_add_le (value s) (value (a * b))
  simp only [Nat.cast_add, Nat.cast_one]
  norm_num only [show (2 : ℝ)^(-53 : Int) = 1 / 9007199254740992 by norm_num,
    show (2 : ℝ)^(-50 : Int) = 1 / 1125899906842624 by norm_num] at hmerr haerr herr ⊢
  linarith

private noncomputable def prefixProduct (inner columns : Nat) (a b : Array Float) (i j k : Nat)
    : ℝ :=
  ∑ t ∈ Finset.range k, value (entry inner a i t) * value (entry columns b t j)

private def DotState (inner columns : Nat) (a b : Array Float) (i j : Nat)
    (δ : ℝ) (k : Nat) (s : Float)
    : Prop :=
  s.isFinite = true ∧ |value s - prefixProduct inner columns a b i j k| ≤ k * δ

private lemma prefixProduct_bound (inner columns : Nat) (a b : Array Float) (i j k : Nat)
    (E : Int) (hk : k ≤ inner)
    (ht : ∀ t, t < inner → |value (entry inner a i t) * value (entry columns b t j)| ≤ (2 : ℝ)^E)
    : |prefixProduct inner columns a b i j k| ≤ k * (2 : ℝ)^E := by
  unfold prefixProduct
  calc
    _ ≤ ∑ t ∈ Finset.range k, |value (entry inner a i t) * value (entry columns b t j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ Finset.range k, (2 : ℝ)^E := Finset.sum_le_sum fun t ht' => ht t (by
      have := Finset.mem_range.mp ht'; omega)
    _ = _ := by simp

private lemma dot_start (inner columns : Nat) (a b : Array Float) (i j : Nat) (δ : ℝ)
    : DotState inner columns a b i j δ 0 0.0 := by
  have hz : value (0.0 : Float) = 0 := rfl
  simp [DotState, prefixProduct, hz]

private lemma dot_update (inner columns : Nat) (a b : Array Float) (i j k : Nat)
    (E : Int) (s : Float) (hE : 0 ≤ E) (hE' : E ≤ 1016) (hinner : inner ≤ 32)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true) (hk : k < inner)
    (ht : ∀ t, t < inner → |value (entry inner a i t) * value (entry columns b t j)| ≤ (2 : ℝ)^E)
    (hs : DotState inner columns a b i j ((2 : ℝ)^(E - 45)) k s)
    : (entry inner a i k * entry columns b k j).isFinite = true
      ∧ (s + entry inner a i k * entry columns b k j).isFinite = true
      ∧ DotState inner columns a b i j ((2 : ℝ)^(E - 45)) (k + 1)
          (s + entry inner a i k * entry columns b k j) := by
  have hh := dot_step E k (entry inner a i k) (entry columns b k j) s
    (prefixProduct inner columns a b i j k) hE hE' (by omega)
    (Flare.Matrix.Storage.getD_finite a _ ha)
    (Flare.Matrix.Storage.getD_finite b _ hb) hs.1 (ht k hk)
    (prefixProduct_bound inner columns a b i j k E (by omega) ht) hs.2
  refine ⟨hh.1, hh.2.1, hh.2.1, ?_⟩
  simpa only [prefixProduct, Finset.sum_range_succ] using hh.2.2

private def ProductState (rows inner columns : Nat) (a b : Array Float) (δ : Nat → Nat → ℝ)
    (row column : Nat) (result : Array Float)
    : Prop :=
  result.size = rows * columns
  ∧ result.all Float.isFinite = true
  ∧ ∀ i j,
      i < rows
      → j < columns
      → i < row ∨ i = row ∧ j < column
      → |value (entry columns result i j) - prefixProduct inner columns a b i j inner|
        ≤ inner * δ i j

private lemma product_start (rows inner columns : Nat) (a b : Array Float) (δ : Nat → Nat → ℝ)
    : ProductState rows inner columns a b δ 0 0 (Array.replicate (rows * columns) 0.0) := by
  refine ⟨(Flare.Matrix.Storage.replicate_storage _).1,
    (Flare.Matrix.Storage.replicate_storage _).2, ?_⟩
  intros
  omega

private lemma product_update (rows inner columns : Nat) (a b result : Array Float)
    (δ : Nat → Nat → ℝ) (i j : Nat) (s : Float) (hi : i < rows) (hj : j < columns)
    (hs : ProductState rows inner columns a b δ i j result)
    (hd : DotState inner columns a b i j (δ i j) inner s)
    : ProductState rows inner columns a b δ i (j + 1) (result.set! (i * columns + j) s) := by
  refine ⟨(Array.size_set! ..).trans hs.1,
    Flare.Matrix.Storage.all_set _ _ _ hs.2.1 hd.1, ?_⟩
  intro r c hr hc hrc
  have hidx : i * columns + j < result.size := by
    rw [hs.1]
    have h := Nat.mul_le_mul_right columns (show i + 1 ≤ rows by omega)
    rw [Nat.add_mul] at h
    omega
  by_cases he : r = i ∧ c = j
  · rcases he with ⟨rfl, rfl⟩
    simpa [entry, Array.set!_eq_setIfInBounds, hidx] using hd.2
  · have hne : i * columns + j ≠ r * columns + c := fun h =>
      he ((Flare.Matrix.Storage.flat_index_eq hc hj).mp h.symm)
    have hv := hs.2.2 r c hr hc (by omega)
    simpa only [entry, Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_ne hne] using hv

private lemma product_row (rows inner columns : Nat) (a b result : Array Float)
    (δ : Nat → Nat → ℝ) (i : Nat) (hs : ProductState rows inner columns a b δ i columns result)
    : ProductState rows inner columns a b δ (i + 1) 0 result := by
  refine ⟨hs.1, hs.2.1, ?_⟩
  intro r c hr hc hrc
  exact hs.2.2 r c hr hc (by omega)

@[spec]
private theorem finite_exact (x : Float) : ⦃⌜x.isFinite = true⌝⦄ finite x ⦃⇓ y => ⌜y = x⌝⦄ := by
  unfold finite
  mvcgen; simp_all

private theorem multiply_triple_of_step (rows inner columns : Nat) (a b : Array Float)
    (δ : Nat → Nat → ℝ)
    (step
      : ∀ i j k s,
          i < rows
          → j < columns
          → k < inner
          → DotState inner columns a b i j (δ i j) k s
          → (entry inner a i k * entry columns b k j).isFinite = true
            ∧ (s + entry inner a i k * entry columns b k j).isFinite = true
            ∧ DotState inner columns a b i j (δ i j) (k + 1)
                (s + entry inner a i k * entry columns b k j))
    : ⦃⌜True⌝
      ⦄ Flare.Matrix.Dense.multiply rows inner columns a b
      ⦃⇓ r => ⌜ProductState rows inner columns a b δ rows 0 r⌝⦄ := by
  have range_length (n : Nat) : [:n].toList.length = n := by simp [Std.Legacy.Range.toList]
  unfold Flare.Matrix.Dense.multiply
  -- leanfmt 0.4.1 cannot preserve the grouped mvcgen alternatives below.
  -- leanfmt: off next
  mvcgen [-Flare.Matrix.Storage.finite_spec, finite_exact] invariants
  | inv1 => ⇓ ⟨xs, r⟩ => ⌜ProductState rows inner columns a b δ xs.prefix.length 0 r⌝
  | inv2 pref i suff hi result hs =>
    ⇓ ⟨xs, r⟩ => ⌜ProductState rows inner columns a b δ i xs.prefix.length r⌝
  | inv3 pref i suff hi initial hs pref' j suff' hj result hs' =>
    ⇓ ⟨xs, s⟩ => ⌜DotState inner columns a b i j (δ i j) xs.prefix.length s⌝
  with
  | vc1 | vc2 | vc3 =>
    subst_vars
    rename_i prefI i suffI hi initial hinit prefJ j suffJ hj result hresult prefK k suffK hk s hs
    have hk' := Flare.Matrix.Storage.range_current hk
    have hh := step i j k s (Flare.Matrix.Storage.range_current hi).2
      (Flare.Matrix.Storage.range_current hj).2 hk'.2 (by simpa only [hk'.1] using hs)
    first
    | exact hh.1
    | exact hh.2.1
    | simpa only [List.length_append, List.length_singleton, ← hk'.1] using hh.2.2
  | vc4 => exact dot_start ..
  | vc5 =>
    rename_i prefI i suffI hi initial hinit prefJ j suffJ hj result hresult s hs
    have hj' := Flare.Matrix.Storage.range_current hj
    simpa only [List.length_append, List.length_singleton, ← hj'.1] using
      product_update rows inner columns a b result δ i j s
        (Flare.Matrix.Storage.range_current hi).2 hj'.2
        (by simpa only [hj'.1] using hresult) (by simpa only [range_length] using hs)
  | vc7 =>
    rename_i pref i suff hi result hs
    simpa only [(Flare.Matrix.Storage.range_current hi).1, List.length_nil] using hs
  | vc8 =>
    rename_i pref i suff hi initial hinit result hs
    simpa only [List.length_append, List.length_singleton, ← (Flare.Matrix.Storage.range_current
      hi).1] using
      product_row rows inner columns a b result δ i (by simpa only [range_length] using hs)
  | vc10 => exact product_start ..
  | vc11 =>
    rename_i result hs
    simpa only [range_length] using hs

private theorem multiply_triple (rows inner columns : Nat) (a b : Array Float) (E : Int)
    (hE : 0 ≤ E) (hE' : E ≤ 1016) (hinner : inner ≤ 32)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (ht
      : ∀ i j k,
          i < rows
          → j < columns
          → k < inner
          → |value (entry inner a i k) * value (entry columns b k j)| ≤ (2 : ℝ)^E)
    : ⦃⌜True⌝
      ⦄ Flare.Matrix.Dense.multiply rows inner columns a b
      ⦃⇓ r => ⌜ProductState rows inner columns a b (fun _ _ => (2 : ℝ)^(E - 45)) rows 0 r⌝⦄ := by
  apply multiply_triple_of_step rows inner columns a b (fun _ _ => (2 : ℝ)^(E - 45))
  intro i j k s hi hj hk hs
  exact dot_update inner columns a b i j k E s hE hE' hinner ha hb hk
    (fun t ht' => ht i j t hi hj ht') hs

/-- The actual native matrix product succeeds and approximates the exact product
of its decoded inputs. With at most 32 terms and each exact term bounded by 2ᴱ,
the entrywise error is at most `inner * 2^(E-45)`. Finiteness is proved for all
intermediate operations; no successful native return is assumed. -/
theorem multiply_accuracy (rows inner columns : Nat) (a b : Array Float) (E : Int)
    (hE : 0 ≤ E) (hE' : E ≤ 1016) (hinner : inner ≤ 32)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (ht
      : ∀ i j k,
          i < rows
          → j < columns
          → k < inner
          → |value (entry inner a i k) * value (entry columns b k j)| ≤ (2 : ℝ)^E)
    : ∃ r,
        Flare.Matrix.Operations.multiply rows inner columns a b = .ok r
        ∧ r.size = rows * columns
        ∧ r.all Float.isFinite = true
        ∧ ∀ i j,
            |matrix rows columns r i j - (matrix rows inner a * matrix inner columns b) i j|
            ≤ inner * (2 : ℝ)^(E - 45) := by
  have hproof := multiply_triple rows inner columns a b E hE hE' hinner ha hb ht
  cases he : Flare.Matrix.Dense.multiply rows inner columns a b with
  | error e =>
      rw [he] at hproof
      exact False.elim (hproof True.intro)
  | ok r =>
      rw [he] at hproof
      have hs := hproof True.intro
      refine ⟨
        r,
        by simp only [Flare.Matrix.Operations.multiply, he,
          Flare.Matrix.Operations.adapt],
        hs.1,
        hs.2.1,
        ?_
      ⟩
      intro i j
      have hh := hs.2.2 i.val j.val i.isLt j.isLt (Or.inl i.isLt)
      have href : prefixProduct inner columns a b i.val j.val inner =
          (matrix rows inner a * matrix inner columns b) i j := by
        simp only [prefixProduct, Matrix.mul_apply, matrix, entry]
        exact (Fin.sum_univ_eq_sum_range (fun k => value (a.getD (i.val * inner + k) 0.0) *
          value (b.getD (k * columns + j.val) 0.0)) inner).symm
      rw [href] at hh
      exact hh

/-- Native dense multiplication with error controlled by the absolute mass of
each exact dot product. This sharper bound uses the same executable schedule
and the same loop invariant proof as `multiply_accuracy`. -/
theorem multiply_mass_accuracy (rows inner columns : Nat) (a b : Array Float) (M : ℝ)
    (hinner : inner ≤ 32) (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hM : M ≤ (2 : ℝ)^(990 : Int)) (hη : (2 : ℝ)^(-1022 : Int) ≤ M)
    (hmass
      : ∀ i j,
          i < rows
          → j < columns
          → (∑ k ∈ Finset.range inner, |value (entry inner a i k) * value (entry columns b k j)|)
            ≤ M)
    : ∃ r,
        Flare.Matrix.Operations.multiply rows inner columns a b = .ok r
        ∧ r.size = rows * columns
        ∧ r.all Float.isFinite = true
        ∧ ∀ i j,
            |matrix rows columns r i j - (matrix rows inner a * matrix inner columns b) i j|
            ≤ inner * (2 : ℝ)^(-48 : Int) * M := by
  have hproof : ⦃⌜True⌝⦄ Flare.Matrix.Dense.multiply rows inner columns a b
      ⦃⇓ r => ⌜ProductState rows inner columns a b (fun _ _ => (2 : ℝ)^(-48 : Int) * M) rows 0 r⌝⦄
        := by
    apply multiply_triple_of_step
    intro i j k s hi hj hk hs
    have htotal := hmass i j hi hj
    have hterm : |value (entry inner a i k) * value (entry columns b k j)| ≤ M :=
      (Finset.single_le_sum (fun t _ => abs_nonneg _) (Finset.mem_range.mpr hk)).trans htotal
    have hp : |prefixProduct inner columns a b i j k| ≤ M := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk.le)
        (by intro t _ _; exact abs_nonneg _)).trans htotal
    have hh := dot_relative_step (entry inner a i k) (entry columns b k j) s
      (prefixProduct inner columns a b i j k) M k
      (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ hb)
      hs.1 (by omega) hM hη hterm hp (by simpa only [mul_assoc] using hs.2)
    refine ⟨hh.1, hh.2.1, hh.2.1, ?_⟩
    simpa only [prefixProduct, Finset.sum_range_succ, mul_assoc] using hh.2.2
  cases he : Flare.Matrix.Dense.multiply rows inner columns a b with
  | error e =>
      rw [he] at hproof
      exact False.elim (hproof True.intro)
  | ok r =>
      rw [he] at hproof
      have hs := hproof True.intro
      refine ⟨
        r,
        by simp only [Flare.Matrix.Operations.multiply, he,
          Flare.Matrix.Operations.adapt],
        hs.1,
        hs.2.1,
        ?_
      ⟩
      intro i j
      have hh := hs.2.2 i.val j.val i.isLt j.isLt (Or.inl i.isLt)
      have href : prefixProduct inner columns a b i.val j.val inner =
          (matrix rows inner a * matrix inner columns b) i j := by
        simp only [prefixProduct, Matrix.mul_apply, matrix, entry]
        exact (Fin.sum_univ_eq_sum_range (fun k => value (a.getD (i.val * inner + k) 0.0) *
          value (b.getD (k * columns + j.val) 0.0)) inner).symm
      rw [href] at hh
      rw [mul_assoc]
      exact hh

/-- Native dense multiplication with error controlled by the absolute mass of
each exact dot product. This sharper bound uses the same executable schedule
and the same loop invariant proof as `multiply_accuracy`. -/
theorem multiply_entrywise_accuracy (rows inner columns : Nat) (a b : Array Float)
    (M : Nat → Nat → ℝ) (hinner : inner ≤ 32) (ha : a.all Float.isFinite = true)
    (hb : b.all Float.isFinite = true)
    (hM : ∀ i j, i < rows → j < columns → M i j ≤ (2 : ℝ)^(990 : Int))
    (hη : ∀ i j, i < rows → j < columns → (2 : ℝ)^(-1022 : Int) ≤ M i j)
    (hmass
      : ∀ i j,
          i < rows
          → j < columns
          → (∑ k ∈ Finset.range inner, |value (entry inner a i k) * value (entry columns b k j)|)
            ≤ M i j)
    : ∃ r,
        Flare.Matrix.Operations.multiply rows inner columns a b = .ok r
        ∧ r.size = rows * columns
        ∧ r.all Float.isFinite = true
        ∧ ∀ i j,
            |matrix rows columns r i j - (matrix rows inner a * matrix inner columns b) i j|
            ≤ inner * (2 : ℝ)^(-50 : Int) * M i.val j.val := by
  have hproof : ⦃⌜True⌝⦄ Flare.Matrix.Dense.multiply rows inner columns a b
      ⦃⇓ r => ⌜ProductState rows inner columns a b (fun i j => (2 : ℝ)^(-50 : Int) * M i j) rows 0
        r⌝⦄ := by
    apply multiply_triple_of_step
    intro i j k s hi hj hk hs
    have htotal := hmass i j hi hj
    have hterm : |value (entry inner a i k) * value (entry columns b k j)| ≤ M i j :=
      (Finset.single_le_sum (fun t _ => abs_nonneg _) (Finset.mem_range.mpr hk)).trans htotal
    have hp : |prefixProduct inner columns a b i j k| ≤ M i j := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk.le)
        (by intro t _ _; exact abs_nonneg _)).trans htotal
    have hh := dot_nearest_step (entry inner a i k) (entry columns b k j) s
      (prefixProduct inner columns a b i j k) (M i j) k
      (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ hb)
      hs.1 (by omega) (hM i j hi hj) (hη i j hi hj) hterm hp (by simpa only [mul_assoc] using hs.2)
    refine ⟨hh.1, hh.2.1, hh.2.1, ?_⟩
    simpa only [prefixProduct, Finset.sum_range_succ, mul_assoc] using hh.2.2
  cases he : Flare.Matrix.Dense.multiply rows inner columns a b with
  | error e =>
      rw [he] at hproof
      exact False.elim (hproof True.intro)
  | ok r =>
      rw [he] at hproof
      have hs := hproof True.intro
      refine ⟨
        r,
        by simp only [Flare.Matrix.Operations.multiply, he,
          Flare.Matrix.Operations.adapt],
        hs.1,
        hs.2.1,
        ?_
      ⟩
      intro i j
      have hh := hs.2.2 i.val j.val i.isLt j.isLt (Or.inl i.isLt)
      have href : prefixProduct inner columns a b i.val j.val inner =
          (matrix rows inner a * matrix inner columns b) i j := by
        simp only [prefixProduct, Matrix.mul_apply, matrix, entry]
        exact (Fin.sum_univ_eq_sum_range (fun k => value (a.getD (i.val * inner + k) 0.0) *
          value (b.getD (k * columns + j.val) 0.0)) inner).symm
      rw [href] at hh
      rw [mul_assoc]
      exact hh

/-- Operator norms supply the absolute-mass premise for the actual native
product. This is a forward-error bound relative to the stored matrix inputs,
with an explicit underflow term and no presumed successful execution. -/
theorem multiply_norm_accuracy (rows inner columns : Nat) (a b : Array Float)
    (hinner : inner ≤ 32) (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hbound
      : ‖matrix rows inner a‖ * ‖matrix inner columns b‖ + (2 : ℝ)^(-1022 : Int)
        ≤ (2 : ℝ)^(990 : Int))
    : ∃ r,
        Flare.Matrix.Operations.multiply rows inner columns a b = .ok r
        ∧ r.size = rows * columns
        ∧ r.all Float.isFinite = true
        ∧ ∀ i j,
            |matrix rows columns r i j - (matrix rows inner a * matrix inner columns b) i j|
            ≤ inner
              * (2 : ℝ)^(-48 : Int)
              * (‖matrix rows inner a‖ * ‖matrix inner columns b‖ + (2 : ℝ)^(-1022 : Int)) := by
  apply multiply_mass_accuracy rows inner columns a b _ hinner ha hb hbound
    (le_add_of_nonneg_left (by positivity))
  intro i j hi hj
  rw [← Fin.sum_univ_eq_sum_range (fun k => |value (entry inner a i k) * value (entry columns b k
    j)|) inner]
  exact (Flare.Analysis.JacobiNorms.product_mass_le_norm (matrix rows inner a)
          (matrix inner columns b) ⟨i, hi⟩ ⟨j, hj⟩).trans
    (le_add_of_nonneg_right (by positivity))

/-- Native transposition only reindexes finite inputs. Its real interpretation
is exactly matrix transpose, including rectangular and empty shapes. -/
theorem transpose_storage (rows columns : Nat) (a : Array Float) (ha : a.all Float.isFinite = true)
    : (transpose rows columns a).size = rows * columns
      ∧ (transpose rows columns a).all Float.isFinite = true
      ∧ ∀ i j,
          i < columns
          → j < rows
          → entry rows (transpose rows columns a) i j = entry columns a j i := by
  refine ⟨by simp [transpose], ?_, ?_⟩
  · rw [Array.all_eq_true]
    intro i hi
    simp only [transpose, Array.getElem_map, Array.getElem_range]
    exact Flare.Matrix.Storage.getD_finite _ _ ha
  · intro i j hi hj
    have hr : 0 < rows := by omega
    have hidx : i * rows + j < rows * columns := by nlinarith
    have hdiv : (i * rows + j) / rows = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hr, Nat.div_eq_of_lt hj, Nat.zero_add]
    have hmod : (i * rows + j) % rows = j := by simp [Nat.add_mod, Nat.mod_eq_of_lt hj]
    simp [transpose, entry, hidx, hdiv, hmod]

/-- Exact real semantics of the native transpose helper. -/
theorem transpose_matrix (rows columns : Nat) (a : Array Float) (ha : a.all Float.isFinite = true)
    : matrix columns rows (transpose rows columns a) = (matrix rows columns a).transpose := by
  ext i j
  change value (entry rows (transpose rows columns a) i.val j.val) = value (entry columns a j.val
    i.val)
  rw [(transpose_storage rows columns a ha).2.2 i.val j.val i.isLt j.isLt]

/-- If every exact scalar product vanishes, the native matrix product is
exactly real zero. This includes signed zeros and imposes no positive mass floor. -/
theorem multiply_zero (rows inner columns : Nat) (a b : Array Float)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hz
      : ∀ i j k,
          i < rows
          → j < columns
          → k < inner
          → value (entry inner a i k) * value (entry columns b k j) = 0)
    : ∃ r,
        Flare.Matrix.Operations.multiply rows inner columns a b = .ok r
        ∧ r.size = rows * columns
        ∧ r.all Float.isFinite = true
        ∧ matrix rows columns r = 0 := by
  have hp (i j k) (hi : i < rows) (hj : j < columns) (hk : k ≤ inner) :
      prefixProduct inner columns a b i j k = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    exact hz i j t hi hj (lt_of_lt_of_le (Finset.mem_range.mp ht) hk)
  have hproof : ⦃⌜True⌝⦄ Flare.Matrix.Dense.multiply rows inner columns a b
      ⦃⇓ r => ⌜ProductState rows inner columns a b (fun _ _ => 0) rows 0 r⌝⦄ := by
    apply multiply_triple_of_step
    intro i j k s hi hj hk hs
    have hs0 : value s = 0 := by
      have hh := hs.2
      simpa only [hp i j k hi hj hk.le, sub_zero, mul_zero, abs_nonpos_iff] using hh
    have ht := Flare.Binary64.Zero.mul_zero (entry inner a i k) (entry columns b k j)
      (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ hb)
      (hz i j k hi hj hk)
    have hh := Flare.Binary64.Zero.add_zero s _ hs.1 ht.1 hs0 ht.2
    refine ⟨ht.1, hh.1, hh.1, ?_⟩
    simp only [hp i j (k + 1) hi hj (by omega), hh.2, sub_self, abs_zero, mul_zero, le_refl]
  cases he : Flare.Matrix.Dense.multiply rows inner columns a b with
  | error e => rw [he] at hproof; exact False.elim (hproof True.intro)
  | ok r =>
      rw [he] at hproof
      have hs := hproof True.intro
      refine ⟨
        r,
        by simp only [Flare.Matrix.Operations.multiply, he,
          Flare.Matrix.Operations.adapt],
        hs.1,
        hs.2.1,
        ?_
      ⟩
      ext i j
      have hh := hs.2.2 i.val j.val i.isLt j.isLt (Or.inl i.isLt)
      change value (entry columns r i.val j.val) = 0
      simpa only [hp i.val j.val inner i.isLt j.isLt le_rfl, sub_zero, mul_zero, abs_nonpos_iff]
        using hh

end Flare.Matrix.Multiplication
