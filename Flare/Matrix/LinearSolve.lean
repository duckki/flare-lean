module

public import Flare.Binary64.Division
public import Flare.Matrix.Multiplication

/-! Native triangular substitution used by the LDLᵀ solve. Proof-only loop
extractions compose to the runtime schedule by proved monadic equalities. Bounds on supplied
factors are local hypotheses, discharged from matrix input bounds in
`PositiveDefiniteFactorization`. Solution accuracy is a separate obligation. -/

@[expose] public section

namespace Flare.Matrix.LinearSolve
open Flare.Matrix.Value Flare.Binary64.Value Flare.Binary64.Arithmetic
open Flare.Binary64.Division
open Flare.Matrix.Dense Std.Do

set_option experimental.vcgen true

attribute [local instance] Std.Internal.Order.instPartialOrderProp
  Std.Internal.Order.instCompleteLatticeProp

/-- Proof-side extraction of the native forward substitution pass. -/
def forward (n columns : Nat) (f : Factor) (b : Array Float)
    : Except Flare.Matrix.DenseError (Array Float) := do
  let mut result := Array.replicate (n * columns) 0.0
  for i in [:n] do
    for j in [:columns] do
      let mut s := entry columns b i j
      for k in [:i] do
        let term ← finite (entry n f.lower i k * entry columns result k j)
        s ← finite (s - term)
      result := result.set! (i * columns + j) s
  return result

/-- Proof-side extraction of the native backward substitution pass. -/
def backward (n columns : Nat) (f : Factor) (y : Array Float)
    : Except Flare.Matrix.DenseError (Array Float) := do
  let mut result := Array.replicate (n * columns) 0.0
  for step in [:n] do
    let i := n - 1 - step
    for j in [:columns] do
      let mut s ← finite (entry columns y i j / f.diagonal.getD i 0.0)
      for k in [i + 1:n] do
        let term ← finite (entry n f.lower k i * entry columns result k j)
        s ← finite (s - term)
      result := result.set! (i * columns + j) s
  return result

/-- Both extracted passes have exactly the runtime solve's operation schedule. -/
lemma solve_split (n columns : Nat) (f : Factor) (b : Array Float)
    : solve n columns f b
      = (do
          backward n columns f (← forward n columns f b)) := by
  unfold solve forward backward
  simp only [bind_assoc, pure_bind]

private lemma zpow_shift (E k : Int) : (2 : ℝ) ^ (E + k) = (2 : ℝ) ^ E * (2 : ℝ) ^ k :=
  zpow_add₀ (by norm_num) _ _

/-- A forward-substitution step cannot overflow on the stated operand bounds.
The two arithmetic operations are separately rounded, as in the runtime. -/
lemma forward_step (E : Int) (s l y : Float) (hE : 0 ≤ E) (hE' : E ≤ 1000)
    (hs : s.isFinite = true) (hl : l.isFinite = true) (hy : y.isFinite = true)
    (hsb : |value s| ≤ (2 : ℝ) ^ E) (hlb : |value l| ≤ 128) (hyb : |value y| ≤ (2 : ℝ) ^ E)
    : (l * y).isFinite = true
      ∧ (s - l * y).isFinite = true
      ∧ |value (s - l * y)| ≤ (2 : ℝ) ^ (E + 8) := by
  have hp : 0 < (2 : ℝ)^E := zpow_pos (by norm_num) _
  have ht : |value l * value y| ≤ 128 * (2 : ℝ)^E := by
    rw [abs_mul]
    exact mul_le_mul hlb hyb (abs_nonneg _) (by norm_num)
  have hm := mul_error l y (E + 7) hl hy (by omega) (by omega)
    (by rw [zpow_shift]; norm_num only [zpow_ofNat, pow_succ, pow_zero]; linarith)
  have hterm : |value (l * y)| ≤ 129 * (2 : ℝ)^E := by
    have htri := abs_sub_le (value (l * y)) (value l * value y) 0
    simp only [sub_zero] at htri
    have heq : E + 7 - 52 = E + (-45) := by omega
    rw [heq, zpow_shift] at hm
    norm_num only [zpow_neg, zpow_ofNat, inv_pow, pow_succ, pow_zero] at hm
    linarith [hm.2]
  have hadd := sub_error s (l * y) (E + 8) hs hm.1 (by omega) (by omega) (by
    rw [zpow_shift]
    norm_num only [zpow_ofNat, pow_succ, pow_zero]
    linarith [abs_sub (value s) (value (l * y))])
  refine ⟨hm.1, hadd.1, ?_⟩
  have heq : E + 8 - 52 = E + (-44) := by omega
  rw [heq, zpow_shift] at hadd
  rw [zpow_shift]
  norm_num only [zpow_neg, zpow_ofNat, inv_pow, pow_succ, pow_zero] at hadd ⊢
  have htri := abs_sub_le (value (s - l * y)) (value s - value (l * y)) 0
  simp only [sub_zero] at htri
  linarith [hadd.2, abs_sub (value s) (value (l * y))]

private def Stored (n columns : Nat) (done : Nat → Nat → Prop) (bound : Nat → ℝ) (r : Array Float)
    : Prop :=
  r.size = n * columns
  ∧ r.all Float.isFinite = true
  ∧ ∀ i j, i < n → j < columns → done i j → |value (entry columns r i j)| ≤ bound i

private lemma stored_set (n columns : Nat) (r : Array Float)
    (done next : Nat → Nat → Prop) (bound : Nat → ℝ) (i j : Nat) (x : Float)
    (hi : i < n) (hj : j < columns) (hr : Stored n columns done bound r)
    (hx : x.isFinite = true) (hb : |value x| ≤ bound i)
    (hnext : ∀ a b, a < n → b < columns → next a b → (a = i ∧ b = j) ∨ done a b)
    : Stored n columns next bound (r.set! (i * columns + j) x) := by
  refine ⟨(Array.size_set! ..).trans hr.1, Flare.Matrix.Storage.all_set _ _ _ hr.2.1 hx, ?_⟩
  intro a b ha hb' hd
  have hi' : i * columns + j < r.size := by
    rw [hr.1]
    have h := Nat.mul_le_mul_right columns (show i + 1 ≤ n by omega)
    rw [Nat.add_mul] at h
    omega
  by_cases he : a = i ∧ b = j
  · rcases he with ⟨rfl, rfl⟩
    simpa [entry, Array.set!_eq_setIfInBounds, hi'] using hb
  · have hn : i * columns + j ≠ a * columns + b := fun h =>
      he ((Flare.Matrix.Storage.flat_index_eq hb' hj).mp h.symm)
    have hh := hr.2.2 a b ha hb' ((hnext a b ha hb' hd).resolve_left he)
    simpa only [entry, Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_ne hn] using hh

private def ForwardState (n columns : Nat) (B : Int) (i j : Nat) (r : Array Float) : Prop :=
  Stored n columns (fun a b => a < i ∨ a = i ∧ b < j) (fun a => (2 : ℝ) ^ (B + 8 * ((a : Int) + 1)))
    r

private def ForwardAccumulator (B : Int) (k : Nat) (s : Float) : Prop :=
  s.isFinite = true ∧ |value s| ≤ (2 : ℝ) ^ (B + 8 * ((k : Int) + 1))

private lemma range_length (n : Nat) : (ForIn.toList [:n]).length = n := by
  simp

private theorem forward_triple (n columns : Nat) (B : Int) (f : Factor) (b : Array Float)
    (hn : n ≤ 12) (hB : 0 ≤ B) (hB' : B ≤ 512)
    (hl : f.lower.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hlb : ∀ i k, i < n → k < i → |value (entry n f.lower i k)| ≤ 128)
    (hbb : ∀ i j, i < n → j < columns → |value (entry columns b i j)| ≤ (2 : ℝ) ^ B)
    : ⦃⌜True⌝⦄ forward n columns f b ⦃⇓ r => ⌜ForwardState n columns B n 0 r⌝⦄ := by
  have step (i j k : Nat) (r : Array Float) (s : Float) (hi : i < n) (hj : j < columns)
      (hk : k < i) (hr : ForwardState n columns B i j r) (hs : ForwardAccumulator B k s) :
      (entry n f.lower i k * entry columns r k j).isFinite = true ∧
      (s - entry n f.lower i k * entry columns r k j).isFinite = true ∧
      ForwardAccumulator B (k + 1) (s - entry n f.lower i k * entry columns r k j) := by
    have hh := forward_step (B + 8 * ((k : Int) + 1)) s (entry n f.lower i k) (entry columns r k j)
      (by omega) (by omega) hs.1 (Flare.Matrix.Storage.getD_finite _ _ hl)
      (Flare.Matrix.Storage.getD_finite _ _ hr.2.1) hs.2 (hlb i k hi hk)
      (hr.2.2 k j (by omega) hj (Or.inl hk))
    refine ⟨hh.1, hh.2.1, hh.2.1, ?_⟩
    convert hh.2.2 using 2
    push_cast
    ring
  unfold forward
  apply (Specification.except_iff _ _ _).mpr
  vcgen [-Flare.Matrix.Storage.finite_wp_spec, Flare.Matrix.Storage.finite_wp_exact]
    invariants
      | inv1 => fun xs _ r => ForwardState n columns B xs.length 0 r
      | inv2 pref i suff hi result hs =>
        fun xs _ r => ForwardState n columns B i xs.length r
      | inv3 pref i suff hi initial hs pref' j suff' hj result hs' =>
        fun xs _ s => ForwardAccumulator B xs.length s
  all_goals simp_all only [SPred.down_pure_nil]
  all_goals subst_vars
  case vc7 | vc9 | vc11 =>
    rename_i prefI i suffI hi initial hinit prefJ j suffJ hj current hcurrent prefK k suffK
      hk s hs
    have hk' := Flare.Matrix.Storage.forIn_range_current hk
    have hh := step i j k current s (Flare.Matrix.Storage.forIn_range_current hi).2
      (Flare.Matrix.Storage.forIn_range_current hj).2 hk'.2
      (by simpa only [(Flare.Matrix.Storage.forIn_range_current hj).1] using hcurrent)
      (by simpa only [hk'.1] using hs)
    first
    | exact hh.1
    | exact hh.2.1
    | simpa only [List.length_append, List.length_singleton, ← hk'.1] using hh.2.2
  case vc5 =>
    rename_i prefI i suffI hi initial hinit prefJ j suffJ hj current hcurrent
    refine ⟨Flare.Matrix.Storage.getD_finite _ _ hb, ?_⟩
    have hh := hbb i j (Flare.Matrix.Storage.forIn_range_current hi).2
      (Flare.Matrix.Storage.forIn_range_current hj).2
    change |value (entry columns b i j)| ≤ (2 : ℝ)^(B + 8 * ((0 : Int) + 1))
    exact hh.trans (zpow_le_zpow_right₀ (by norm_num) (by omega))
  case vc6 =>
    rename_i prefI i suffI hi initial hinit prefJ j suffJ hj current hcurrent s hs
    have hj' := Flare.Matrix.Storage.forIn_range_current hj
    have hs' : ForwardAccumulator B i s := by simpa only [range_length] using hs
    have hh := stored_set n columns current _ (fun a b => a < i ∨ a = i ∧ b < j + 1) _ i j s
      (Flare.Matrix.Storage.forIn_range_current hi).2 hj'.2 hcurrent hs'.1 hs'.2
      (fun a b ha hb hnext => by omega)
    simpa only [ForwardState, List.length_append, List.length_singleton, ← hj'.1] using hh
  case vc3 =>
    rename_i pref i suff hi r hr
    simpa only [(Flare.Matrix.Storage.forIn_range_current hi).1, List.length_nil] using hr
  case vc4 =>
    rename_i pref i suff hi initial hinit r hr
    have hr' : ForwardState n columns B i columns r := by simpa only [range_length] using hr
    refine ⟨hr'.1, hr'.2.1, ?_⟩
    intro a b ha hb hd
    apply hr'.2.2 a b ha hb
    have hi' := (Flare.Matrix.Storage.forIn_range_current hi).1
    simp only [List.length_append, List.length_singleton] at hd
    omega
  case vc1 =>
    refine ⟨(Flare.Matrix.Storage.replicate_storage _).1,
      (Flare.Matrix.Storage.replicate_storage _).2, ?_⟩
    intros
    simp_all
  case vc2 =>
    rename_i r hr
    simpa only [range_length] using hr

/-- Back substitution subtracts at most twelve terms. This bound preserves
finiteness while allowing the solved rows to be larger than the right-hand side. -/
lemma backward_step (E : Int) (k : Nat) (s l x : Float) (hE : 0 ≤ E) (hE' : E ≤ 1000)
    (hk : k ≤ 11) (hs : s.isFinite = true) (hl : l.isFinite = true) (hx : x.isFinite = true)
    (hsb : |value s| ≤ (1 + 130 * k) * (2 : ℝ) ^ E)
    (hlb : |value l| ≤ 128) (hxb : |value x| ≤ (2 : ℝ) ^ E)
    : (l * x).isFinite = true
      ∧ (s - l * x).isFinite = true
      ∧ |value (s - l * x)| ≤ (1 + 130 * (k + 1 : Nat)) * (2 : ℝ) ^ E := by
  have hp : 0 < (2 : ℝ)^E := zpow_pos (by norm_num) _
  have hk' : (k : ℝ) ≤ 11 := by exact_mod_cast hk
  have ht : |value l * value x| ≤ 128 * (2 : ℝ)^E := by
    rw [abs_mul]
    exact mul_le_mul hlb hxb (abs_nonneg _) (by norm_num)
  have hm := mul_error l x (E + 7) hl hx (by omega) (by omega)
    (by rw [zpow_shift]; norm_num only [zpow_ofNat, pow_succ, pow_zero]; linarith)
  have hterm : |value (l * x)| ≤ 129 * (2 : ℝ)^E := by
    have htri := abs_sub_le (value (l * x)) (value l * value x) 0
    simp only [sub_zero] at htri
    rw [show E + 7 - 52 = E + (-45) by omega, zpow_shift] at hm
    norm_num only [zpow_neg, zpow_ofNat, inv_pow, pow_succ, pow_zero] at hm
    linarith [hm.2]
  have hadd := sub_error s (l * x) (E + 11) hs hm.1 (by omega) (by omega) (by
    rw [zpow_shift]
    norm_num only [zpow_ofNat, pow_succ, pow_zero]
    nlinarith [abs_sub (value s) (value (l * x))])
  refine ⟨hm.1, hadd.1, ?_⟩
  rw [show E + 11 - 52 = E + (-41) by omega, zpow_shift] at hadd
  norm_num only [zpow_neg, zpow_ofNat, inv_pow, pow_succ, pow_zero] at hadd
  have htri := abs_sub_le (value (s - l * x)) (value s - value (l * x)) 0
  simp only [sub_zero, Nat.cast_add, Nat.cast_one] at htri ⊢
  nlinarith [hadd.2, abs_sub (value s) (value (l * x))]

private lemma divide_start (B : Int) (hB : 0 ≤ B) (hB' : B ≤ 512) (y d : Float)
    (hy : y.isFinite = true) (hd : d.isFinite = true)
    (hyb : |value y| ≤ (2 : ℝ) ^ (B + 96)) (hdb : (1 / 8 : ℝ) ≤ value d)
    : (y / d).isFinite = true ∧ |value (y / d)| ≤ (2 : ℝ) ^ (B + 100) := by
  have hdp : 0 < value d := by linarith
  have hq : |value y / value d| ≤ (2 : ℝ)^(B + 99) := by
    rw [abs_div, abs_of_pos hdp]
    apply (div_le_iff₀ hdp).mpr
    rw [zpow_shift] at hyb ⊢
    norm_num only [zpow_ofNat, pow_succ, pow_zero] at hyb ⊢
    nlinarith [zpow_pos (by norm_num : (0 : ℝ) < 2) B]
  have hdiv := div_error y d (B + 99) hy hd (ne_of_gt hdp) (by omega) (by omega) hq
  refine ⟨hdiv.1, ?_⟩
  have htri := abs_sub_le (value (y / d)) (value y / value d) 0
  simp only [sub_zero] at htri
  have hround : |value (y / d) - value y / value d| ≤ (2 : ℝ)^(B + 99) :=
    hdiv.2.trans (zpow_le_zpow_right₀ (by norm_num) (by omega))
  rw [show B + 100 = (B + 99) + 1 by omega, zpow_shift]
  norm_num only [zpow_one]
  linarith

private def BackwardState (n columns : Nat) (B : Int) (step j : Nat) (r : Array Float) : Prop :=
  Stored n columns (fun a b => n - 1 - a < step ∨ n - 1 - a = step ∧ b < j)
    (fun a => (2 : ℝ) ^ (B + 100 + 11 * ((n : Int) - a))) r

private def BackwardAccumulator (B : Int) (step k : Nat) (s : Float) : Prop :=
  s.isFinite = true ∧ |value s| ≤ (1 + 130 * k) * (2 : ℝ) ^ (B + 100 + 11 * (step : Int))

private lemma range_from_current {a n k : Nat} {pref suff : List Nat}
    (h : ForIn.toList [a:n] = pref ++ k :: suff)
    : k = a + pref.length ∧ k < n := by
  have hlist : List.range' a (n - a) = pref ++ k :: suff := by simpa [Std.Legacy.Range.size] using h
  have hlen := congrArg List.length hlist
  simp only [List.length_range', List.length_append, List.length_cons] at hlen
  have he := congrArg (fun xs => xs[pref.length]?) hlist
  simp [show pref.length < n - a by omega] at he
  omega

private theorem backward_triple (n columns : Nat) (B : Int) (f : Factor) (y : Array Float)
    (hn : n ≤ 12) (hB : 0 ≤ B) (hB' : B ≤ 512)
    (hl : f.lower.all Float.isFinite = true) (hd : f.diagonal.all Float.isFinite = true)
    (hy : y.all Float.isFinite = true)
    (hlb : ∀ i k, i < n → k < i → |value (entry n f.lower i k)| ≤ 128)
    (hdb : ∀ i, i < n → (1 / 8 : ℝ) ≤ value (f.diagonal.getD i 0.0))
    (hyb : ∀ i j, i < n → j < columns → |value (entry columns y i j)| ≤ (2 : ℝ) ^ (B + 96))
    : ⦃⌜True⌝⦄ backward n columns f y ⦃⇓ r => ⌜BackwardState n columns B n 0 r⌝⦄ := by
  have start (step j : Nat) (hs : step < n) (hj : j < columns) :
      (entry columns y (n - 1 - step) j / f.diagonal.getD (n - 1 - step) 0.0).isFinite = true ∧
      BackwardAccumulator B step 0
        (entry columns y (n - 1 - step) j / f.diagonal.getD (n - 1 - step) 0.0) := by
    have hi : n - 1 - step < n := by omega
    have hh := divide_start B hB hB' (entry columns y (n - 1 - step) j) (f.diagonal.getD (n - 1 -
      step) 0.0)
      (Flare.Matrix.Storage.getD_finite _ _ hy) (Flare.Matrix.Storage.getD_finite _ _ hd)
      (hyb _ _ hi hj) (hdb _ hi)
    refine ⟨hh.1, hh.1, ?_⟩
    change |value (entry columns y (n - 1 - step) j / f.diagonal.getD (n - 1 - step) 0.0)| ≤
      (1 + 130 * (0 : Nat)) * (2 : ℝ)^(B + 100 + 11 * (step : Int))
    simp only [Nat.cast_zero, mul_zero, add_zero, one_mul]
    calc
      _ ≤ (2 : ℝ) ^ (B + 100) := hh.2
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have step (t j k count : Nat) (r : Array Float) (s : Float) (ht : t < n) (hj : j < columns)
      (hk : k < n) (hik : n - 1 - t < k) (hcount : count ≤ 11)
      (hr : BackwardState n columns B t j r) (hs : BackwardAccumulator B t count s) :
      (entry n f.lower k (n - 1 - t) * entry columns r k j).isFinite = true ∧
      (s - entry n f.lower k (n - 1 - t) * entry columns r k j).isFinite = true ∧
      BackwardAccumulator B t (count + 1)
        (s - entry n f.lower k (n - 1 - t) * entry columns r k j) := by
    have hxb : |value (entry columns r k j)| ≤ (2 : ℝ)^(B + 100 + 11 * (t : Int)) :=
      (hr.2.2 k j hk hj (Or.inl (by omega))).trans
        (zpow_le_zpow_right₀ (by norm_num) (by omega))
    have hh := backward_step (B + 100 + 11 * (t : Int)) count s (entry n f.lower k (n - 1 - t))
      (entry columns r k j) (by omega) (by omega) hcount hs.1
      (Flare.Matrix.Storage.getD_finite _ _ hl) (Flare.Matrix.Storage.getD_finite _ _ hr.2.1)
      hs.2 (hlb _ _ hk hik) hxb
    exact ⟨hh.1, hh.2.1, hh.2.1, hh.2.2⟩
  unfold backward
  apply (Specification.except_iff _ _ _).mpr
  vcgen [-Flare.Matrix.Storage.finite_wp_spec, Flare.Matrix.Storage.finite_wp_exact]
    invariants
      | inv1 => fun xs _ r => BackwardState n columns B xs.length 0 r
      | inv2 pref t suff ht result hs =>
        fun xs _ r => BackwardState n columns B t xs.length r
      | inv3 pref t suff ht initial hs pref' j suff' hj result hs' heq =>
        fun xs _ s => BackwardAccumulator B t xs.length s
  all_goals simp_all only [SPred.down_pure_nil]
  all_goals subst_vars
  case vc5 | vc7 =>
    rename_i prefT t suffT ht initial hinit prefJ j suffJ hj r hr
    have hh := start t j (Flare.Matrix.Storage.forIn_range_current ht).2
      (Flare.Matrix.Storage.forIn_range_current hj).2
    first | exact hh.1 | exact hh.2
  case vc9 | vc11 | vc13 =>
    rename_i prefT t suffT ht initial hinit prefJ j suffJ hj current hcurrent prefK k suffK hk s
      hs
    have ht' := Flare.Matrix.Storage.forIn_range_current ht
    have hk' := range_from_current hk
    have hi : i = n - 1 - t := rfl
    have hh := step t j k prefK.length current s ht'.2
      (Flare.Matrix.Storage.forIn_range_current hj).2 hk'.2 (by omega) (by omega)
      (by simpa only [(Flare.Matrix.Storage.forIn_range_current hj).1] using hcurrent) hs
    first
    | exact hh.1
    | exact hh.2.1
    | simpa only [List.length_append, List.length_singleton] using hh.2.2
  case vc8 =>
    rename_i prefT t suffT ht initial hinit prefJ j suffJ hj current hcurrent s hs
    have ht' := Flare.Matrix.Storage.forIn_range_current ht
    have hj' := Flare.Matrix.Storage.forIn_range_current hj
    have hi : i = n - 1 - t := rfl
    have hlen : (ForIn.toList [i + 1:n]).length = n - (i + 1) := by simp [Std.Legacy.Range.size]
    have hsb : |value s| ≤ (2 : ℝ)^(B + 100 + 11 * ((n : Int) - i)) := by
      have h := hs.2
      rw [hlen] at h
      have he : B + 100 + 11 * ((n : Int) - i) = (B + 100 + 11 * (t : Int)) + 11 := by omega
      rw [he, zpow_shift]
      norm_num only [zpow_ofNat, pow_succ, pow_zero]
      have hk : ((n - (i + 1) : Nat) : ℝ) ≤ 11 := by exact_mod_cast (by omega : n - (i + 1) ≤
        11)
      nlinarith [zpow_pos (by norm_num : (0 : ℝ) < 2) (B + 100 + 11 * (t : Int))]
    have hh := stored_set n columns current _
      (fun a b => n - 1 - a < t ∨ n - 1 - a = t ∧ b < j + 1) _ i j s
      (by omega) hj'.2 hcurrent hs.1 hsb (fun a b ha hb hd => by omega)
    simpa only [BackwardState, List.length_append, List.length_singleton, ← hj'.1] using hh
  case vc3 =>
    rename_i pref t suff ht r hr
    simpa only [(Flare.Matrix.Storage.forIn_range_current ht).1, List.length_nil] using hr
  case vc4 =>
    rename_i pref t suff ht initial hinit r hr
    have hr' : BackwardState n columns B t columns r := by simpa only [range_length] using hr
    refine ⟨hr'.1, hr'.2.1, ?_⟩
    intro a b ha hb hd
    apply hr'.2.2 a b ha hb
    have ht' := (Flare.Matrix.Storage.forIn_range_current ht).1
    simp only [List.length_append, List.length_singleton] at hd
    omega
  case vc1 =>
    refine ⟨(Flare.Matrix.Storage.replicate_storage _).1,
      (Flare.Matrix.Storage.replicate_storage _).2, ?_⟩
    intros
    simp_all
  case vc2 =>
    rename_i r hr
    simpa only [range_length] using hr

/-- The complete native forward pass succeeds under the substitution input
bounds. This exposes its intermediate result for compositional error analysis. -/
theorem forward_success (n columns : Nat) (B : Int) (f : Factor) (b : Array Float)
    (hn : n ≤ 12) (hB : 0 ≤ B) (hB' : B ≤ 512)
    (hl : f.lower.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hlb : ∀ i k, i < n → k < i → |value (entry n f.lower i k)| ≤ 128)
    (hbb : ∀ i j, i < n → j < columns → |value (entry columns b i j)| ≤ (2 : ℝ) ^ B)
    : ∃ y,
        forward n columns f b = .ok y
        ∧ y.size = n * columns
        ∧ y.all Float.isFinite = true
        ∧ ∀ i j, i < n → j < columns → |value (entry columns y i j)| ≤ (2 : ℝ) ^ (B + 96) := by
  have h := forward_triple n columns B f b hn hB hB' hl hb hlb hbb
  cases he : forward n columns f b with
  | error e =>
      rw [he] at h; exact False.elim (h True.intro)
  | ok y =>
      rw [he] at h
      have hy := h True.intro
      refine ⟨y, rfl, hy.1, hy.2.1, ?_⟩
      intro i j hi hj
      exact (hy.2.2 i j hi hj (Or.inl hi)).trans (zpow_le_zpow_right₀ (by norm_num) (by omega))

/-- Native backward substitution succeeds for the finite intermediate values
produced by the forward pass, with the same coarse overflow-avoidance bound. -/
theorem backward_success (n columns : Nat) (B : Int) (f : Factor) (y : Array Float)
    (hn : n ≤ 12) (hB : 0 ≤ B) (hB' : B ≤ 512)
    (hl : f.lower.all Float.isFinite = true) (hd : f.diagonal.all Float.isFinite = true)
    (hy : y.all Float.isFinite = true)
    (hlb : ∀ i k, i < n → k < i → |value (entry n f.lower i k)| ≤ 128)
    (hdb : ∀ i, i < n → (1 / 8 : ℝ) ≤ value (f.diagonal.getD i 0.0))
    (hyb : ∀ i j, i < n → j < columns → |value (entry columns y i j)| ≤ (2 : ℝ) ^ (B + 96))
    : ∃ r,
        backward n columns f y = .ok r
        ∧ r.size = n * columns
        ∧ r.all Float.isFinite = true
        ∧ ∀ i j, i < n → j < columns → |value (entry columns r i j)| ≤ (2 : ℝ) ^ (B + 232) := by
  have h := backward_triple n columns B f y hn hB hB' hl hd hy hlb hdb hyb
  cases he : backward n columns f y with
  | error e =>
      rw [he] at h; exact False.elim (h True.intro)
  | ok r =>
      rw [he] at h
      have hr := h True.intro
      refine ⟨r, rfl, hr.1, hr.2.1, ?_⟩
      intro i j hi hj
      exact (hr.2.2 i j hi hj (Or.inl (by omega))).trans
        (zpow_le_zpow_right₀ (by norm_num) (by omega))

/-- Given finite factors with strict-lower entries bounded by 128, pivots at
least one eighth, at most twelve rows, and right-hand-side entries bounded by
2ᴮ for 0 ≤ B ≤ 512, the actual native substitution returns a finite, correctly shaped result.
These are sufficient factor-domain hypotheses, not assertions that factorization
has produced such factors. No successful execution is assumed. -/
theorem solve_success (n columns : Nat) (B : Int) (f : Factor) (b : Array Float)
    (hn : n ≤ 12) (hB : 0 ≤ B) (hB' : B ≤ 512) (hl : f.lower.all Float.isFinite = true)
    (hd : f.diagonal.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hlb : ∀ i k, i < n → k < i → |value (entry n f.lower i k)| ≤ 128)
    (hdb : ∀ i, i < n → (1 / 8 : ℝ) ≤ value (f.diagonal.getD i 0.0))
    (hbb : ∀ i j, i < n → j < columns → |value (entry columns b i j)| ≤ (2 : ℝ) ^ B)
    : ∃ r,
        solve n columns f b = .ok r
        ∧ r.size = n * columns
        ∧ r.all Float.isFinite = true
        ∧ ∀ i j, i < n → j < columns → |value (entry columns r i j)| ≤ (2 : ℝ) ^ (B + 232) := by
  obtain ⟨y, hy, _, hyf, hyb⟩ := forward_success n columns B f b hn hB hB' hl hb hlb hbb
  obtain ⟨r, hr, hrs, hrf, hrb⟩ := backward_success n columns B f y hn hB hB' hl hd hyf hlb hdb hyb
  refine ⟨r, ?_, hrs, hrf, hrb⟩
  rw [solve_split, hy]
  exact hr

end Flare.Matrix.LinearSolve
