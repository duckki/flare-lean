import Flare.Matrix.Factorization
import Flare.Analysis.Factorization
import Flare.Matrix.LinearSolve

/-! Native LDLᵀ prefix invariants and the connection between its local column
theorem and the conditioning of the original input matrix. -/

namespace Flare.Matrix.PositiveDefiniteFactorization
open Flare.Matrix.Value Flare.Binary64.Value
open Flare.Matrix.Dense
open Flare.Binary64.Arithmetic
open Std.Do

set_option mvcgen.warning false
-- Retain the established VC engine while using Lean 4.35.
set_option linter.deprecated.syntax false

private noncomputable def gram (n k : Nat) (f : Factor) : _root_.Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    ∑ t ∈ Finset.range k,
      value (entry n f.lower i.val t)
      * value (f.diagonal.getD t 0.0)
      * value (entry n f.lower j.val t)

private lemma real_prefix_eq (n k : Nat) (f : Factor) (hk : k ≤ n)
    : Flare.Analysis.Factorization.prefixGram (matrix n n f.lower)
        (fun j => value (f.diagonal.getD j.val 0.0)) hk
      = gram n k f := by
  ext i j
  rw [Flare.Analysis.Factorization.prefixGram_apply]
  exact Fin.sum_univ_eq_sum_range (fun t =>
    value (entry n f.lower i.val t) * value (f.diagonal.getD t 0.0) * value (entry n f.lower j.val
      t)) k

private lemma schur_eq (n k : Nat) (a : Array Float) (f : Factor)
    : Factorization.schurResidual n k a f.lower f.diagonal = matrix n n a - gram n k f :=
  rfl

private structure Prefix (n k : Nat) (a : Array Float) (f : Factor) : Prop where
  processed_le : k ≤ n
  lower_size : f.lower.size = n * n
  diagonal_size : f.diagonal.size = n
  lower_finite : f.lower.all Float.isFinite = true
  diagonal_finite : f.diagonal.all Float.isFinite = true
  zero_entries : ∀ i j : Fin n, i.val < j.val ∨ k ≤ j.val → entry n f.lower i.val j.val = 0.0
  unit_diagonal : ∀ j : Fin n, j.val < k → entry n f.lower j.val j.val = 1.0
  lower_bound : ∀ i j : Fin n, j.val < k → |value (entry n f.lower i.val j.val)| ≤ 128
  pivot_lower : ∀ j : Fin n, j.val < k → (1 / 8 : ℝ) ≤ value (f.diagonal.getD j.val 0.0)
  pivot_upper : ∀ j : Fin n, j.val < k → |value (f.diagonal.getD j.val 0.0)| ≤ 2048
  backward_error
    : ∀ i j : Fin n,
        i.val < k ∨ j.val < k → |gram n k f i j - matrix n n a i j| ≤ (2 : ℝ) ^ (-13 : Int)
  pivot_equation
    : ∀ j : Fin n,
        j.val < k
        → Factorization.gramResidual n j.val f.lower f.diagonal (entry n a j.val j.val) j.val j.val
          = .ok (f.diagonal.getD j.val 0.0)
  column_equation
    : ∀ i j : Fin n,
        j.val < k
        → j.val < i.val
        → ∃ r,
            Factorization.gramResidual n j.val f.lower f.diagonal (entry n a i.val j.val) i.val
                j.val
              = .ok r
            ∧ entry n f.lower i.val j.val = r / f.diagonal.getD j.val 0.0

private lemma prefix_schur_bounds (n k : Nat) (a : Array Float) (f : Factor)
    (hn : n ≤ 12) (hA : (matrix n n a - (3 / 16 : ℝ) • 1).PosSemidef)
    (ha : ∀ i j : Fin n, |value (entry n a i.val j.val)| ≤ 1024)
    (h : Prefix n k a f) (i j : Fin n) (hi : k ≤ i.val) (hj : k ≤ j.val)
    : (5 / 32 : ℝ) ≤ Factorization.schurResidual n k a f.lower f.diagonal j j
      ∧ (Factorization.schurResidual n k a f.lower f.diagonal i j) ^ 2
        ≤ 1024 * Factorization.schurResidual n k a f.lower f.diagonal j j := by
  have hp (j : Fin n) (hj : j.val < k) : 0 < value (f.diagonal.getD j.val 0.0) := by
    linarith [h.pivot_lower j hj]
  have hS := Flare.Analysis.Factorization.prefix_schur_lower_bound (matrix n n a) (matrix n n
    f.lower)
    (fun j => value (f.diagonal.getD j.val 0.0)) h.processed_le hn hA hp
    (by
      intro j hj
      change value (entry n f.lower j.val j.val) = 1
      rw [h.unit_diagonal j hj]
      exact one_value)
    (by
      intro i j _ hij
      change value (entry n f.lower i.val j.val) = 0
      rw [h.zero_entries i j (Or.inl hij)]
      rfl)
    (by simpa only [real_prefix_eq] using h.backward_error)
  have hb := Flare.Analysis.Factorization.schur_column_bounds (matrix n n a) (matrix n n f.lower)
    (fun j => value (f.diagonal.getD j.val 0.0)) h.processed_le (fun j hj => (hp j hj).le)
    (fun i => (le_abs_self _).trans (ha i i)) hS i j hi hj
  simpa only [real_prefix_eq, schur_eq] using hb

private lemma gram_symm (n k : Nat) (f : Factor) (i j : Fin n)
    : gram n k f j i = gram n k f i j := by
  unfold gram
  apply Finset.sum_congr rfl
  intro t _
  ring

private theorem column_progress (n k : Nat) (a : Array Float) (f : Factor)
    (hn : n ≤ 12) (hk : k < n) (haf : a.all Float.isFinite = true)
    (hA : (matrix n n a - (3 / 16 : ℝ) • 1).PosSemidef)
    (ha : ∀ i j : Fin n, |value (entry n a i.val j.val)| ≤ 1024)
    (h : Prefix n k a f)
    : ∃ result, Factorization.factorColumn n k a f = .ok result ∧ Prefix n (k + 1) a result := by
  let j : Fin n := ⟨k, hk⟩
  have hp (t : Nat) (ht : t < k) : 0 ≤ value (f.diagonal.getD t 0.0) := by
    have hh := h.pivot_lower ⟨t, by omega⟩ ht
    linarith
  have hb := prefix_schur_bounds n k a f hn hA ha h j j (by rfl) (by rfl)
  obtain ⟨result, he, hls, hds, hlf, hdf, hunit, hpl, hpu, hpe, hpeq, hother, habove, hdother, hcol⟩
    :=
    Factorization.factorColumn_accuracy n j a f hn haf h.lower_size h.diagonal_size h.lower_finite
      h.diagonal_finite ha
      (fun i t ht => h.lower_bound i ⟨t, by omega⟩ ht)
      (fun t ht => h.pivot_upper ⟨t, by omega⟩ ht) hp hb.1
      (fun i hi => (prefix_schur_bounds n k a f hn hA ha h i j (by dsimp [j] at hi; omega) (by
        rfl)).2)
  have hzero (i t : Fin n) (hit : i.val < t.val ∨ k + 1 ≤ t.val) :
      entry n result.lower i.val t.val = 0.0 := by
    by_cases ht : t = j
    · subst t
      rw [habove i (by dsimp [j] at hit ⊢; omega)]
      exact h.zero_entries i j (Or.inr (by rfl))
    · rw [hother i t ht]
      exact h.zero_entries i t (by omega)
  have hg (i t : Fin n) : gram n k result i t = gram n k f i t := by
    unfold gram
    apply Finset.sum_congr rfl
    intro u hu
    have hu' := Finset.mem_range.mp hu
    have huf : (⟨u, by omega⟩ : Fin n) ≠ j := by
      intro heq; have := congrArg Fin.val heq; dsimp [j] at this; omega
    rw [hother i ⟨u, by omega⟩ huf, hother t ⟨u, by omega⟩ huf, hdother u (by dsimp [j]; omega)]
  have hgs (i t : Fin n) : gram n (k + 1) result i t = gram n k f i t +
      value (entry n result.lower i.val k) * value (result.diagonal.getD k 0.0) *
        value (entry n result.lower t.val k) := by
    unfold gram
    rw [Finset.sum_range_succ]
    change gram n k result i t + _ = _
    rw [hg]
    rfl
  have hcurrent (i : Fin n) (hi : k ≤ i.val) :
      |gram n (k + 1) result i j - matrix n n a i j| ≤ (2 : ℝ)^(-13 : Int) := by
    rw [hgs]
    change |gram n k f i j + value (entry n result.lower i.val k) * value (result.diagonal.getD k
      0.0) *
      value (entry n result.lower j.val j.val) - matrix n n a i j| ≤ _
    rw [hunit, one_value, mul_one]
    have hid : gram n k f i j + value (entry n result.lower i.val k) * value (result.diagonal.getD k
      0.0) -
        matrix n n a i j = value (entry n result.lower i.val k) * value (result.diagonal.getD k 0.0)
          -
          Factorization.schurResidual n k a f.lower f.diagonal i j := by
      rw [schur_eq]
      change _ = _ - (matrix n n a i j - gram n k f i j)
      ring
    rw [hid]
    by_cases hij : i = j
    · subst i
      change |value (entry n result.lower j.val j.val) * value (result.diagonal.getD k 0.0) - _| ≤ _
      rw [hunit, one_value, one_mul]
      exact hpe.trans (by norm_num)
    · exact (hcol i (by
        dsimp [j]; have := i.isLt; have hne : i.val ≠ k := fun he => hij (Fin.ext he); omega)).2.1
  have hres (i t : Fin n) (ht : t.val ≤ k)
      : Factorization.gramResidual n t.val result.lower result.diagonal (entry n a i.val t.val)
          i.val t.val
        = Factorization.gramResidual n t.val f.lower f.diagonal (entry n a i.val t.val) i.val
            t.val := by
    apply Factorization.gramResidual_congr
    · intro u hu
      exact hother i ⟨u, by omega⟩ (fun he => by
        have := congrArg Fin.val he; dsimp [j] at this; omega)
    · intro u hu
      exact hdother u (by dsimp [j]; omega)
    · intro u hu
      exact hother t ⟨u, by omega⟩ (fun he => by
        have := congrArg Fin.val he; dsimp [j] at this; omega)
  refine ⟨result, he, ⟨by omega, hls, hds, hlf, hdf, hzero, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro t ht
    by_cases htj : t = j
    · simpa only [htj] using hunit
    · rw [hother t t htj]
      apply h.unit_diagonal t
      have hne : t.val ≠ k := fun he => htj (Fin.ext he)
      omega
  · intro i t ht
    by_cases htj : t = j
    · subst t
      by_cases hij : i = j
      · subst i
        rw [hunit, one_value]
        norm_num
      · by_cases hi : i.val < k
        · rw [hzero i j (Or.inl hi), show value (0.0 : Float) = 0 by rfl]
          norm_num
        · exact (hcol i (by dsimp [j]; have hne : i.val ≠ k := fun he => hij (Fin.ext he); omega)).1
    · rw [hother i t htj]
      apply h.lower_bound i t
      have hne : t.val ≠ k := fun he => htj (Fin.ext he)
      omega
  · intro t ht
    by_cases htj : t = j
    · simpa only [htj] using hpl
    · rw [hdother t.val (fun he => htj (Fin.ext he))]
      apply h.pivot_lower t
      have hne : t.val ≠ k := fun he => htj (Fin.ext he)
      omega
  · intro t ht
    by_cases htj : t = j
    · simpa only [htj] using hpu
    · rw [hdother t.val (fun he => htj (Fin.ext he))]
      apply h.pivot_upper t
      have hne : t.val ≠ k := fun he => htj (Fin.ext he)
      omega
  · intro i t hit
    by_cases hold : i.val < k ∨ t.val < k
    · rw [hgs]
      rcases hold with hi | ht
      · rw [hzero i j (Or.inl hi), show value (0.0 : Float) = 0 by rfl, zero_mul, zero_mul,
        add_zero]
        exact h.backward_error i t (Or.inl hi)
      · rw [hzero t j (Or.inl ht), show value (0.0 : Float) = 0 by rfl, mul_zero, add_zero]
        exact h.backward_error i t (Or.inr ht)
    · have hi : k ≤ i.val := by omega
      have ht : k ≤ t.val := by omega
      by_cases htj : t = j
      · simpa only [htj] using hcurrent i hi
      · have hij : i = j := by
          apply Fin.ext; dsimp [j]; have hne : t.val ≠ k := fun he => htj (Fin.ext he); omega
        subst i
        have hs := (Flare.Analysis.NumericalBounds.posDef_of_lower_bound (matrix n n a) (3 / 16) (by
          norm_num) hA).isHermitian
        have heq := congr_fun (congr_fun hs.eq t) j
        simp only [_root_.Matrix.conjTranspose_apply, star_trivial] at heq
        rw [gram_symm n (k + 1) result t j, heq]
        exact hcurrent t ht
  · intro t ht
    by_cases htj : t = j
    · subst t
      exact (hres j j (by rfl)).trans hpeq
    · have hne : t.val ≠ k := fun he => htj (Fin.ext he)
      rw [hres t t (by omega), hdother t.val hne]
      exact h.pivot_equation t (by omega)
  · intro i t ht hit
    by_cases htj : t = j
    · subst t
      obtain ⟨r, hr, hx⟩ := (hcol i hit).2.2
      exact ⟨r, (hres i j (by rfl)).trans hr, hx⟩
    · have hne : t.val ≠ k := fun he => htj (Fin.ext he)
      obtain ⟨r, hr, hx⟩ := h.column_equation i t (by omega) hit
      refine ⟨r, (hres i t (by omega)).trans hr, ?_⟩
      rw [hother i t htj, hdother t.val hne]
      exact hx

private lemma prefix_start (n : Nat) (a : Array Float)
    : Prefix n 0 a ⟨Array.replicate (n * n) 0.0, Array.replicate n 0.0⟩ := by
  refine ⟨
    by omega,
    by simp,
    by simp,
    (Flare.Matrix.Storage.replicate_storage _).2,
    (Flare.Matrix.Storage.replicate_storage _).2,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_
  ⟩
  · intro i j _
    simp [entry, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  all_goals intros; simp_all

@[spec]
private theorem column_spec (n k : Nat) (a : Array Float) (f : Factor)
    (hn : n ≤ 12) (haf : a.all Float.isFinite = true)
    (hA : (matrix n n a - (3 / 16 : ℝ) • 1).PosSemidef)
    (ha : ∀ i j : Fin n, |value (entry n a i.val j.val)| ≤ 1024)
    : ⦃⌜k < n ∧ Prefix n k a f⌝
      ⦄ Factorization.factorColumn n k a f
      ⦃⇓ result => ⌜Prefix n (k + 1) a result⌝⦄ := by
  intro ⟨hk, h⟩
  obtain ⟨r, he, hr⟩ := column_progress n k a f hn hk haf hA ha h
  simp only [he]
  exact hr

private theorem factor_triple (n : Nat) (a : Array Float)
    (hn : n ≤ 12) (haf : a.all Float.isFinite = true)
    (hA : (matrix n n a - (3 / 16 : ℝ) • 1).PosSemidef)
    (ha : ∀ i j : Fin n, |value (entry n a i.val j.val)| ≤ 1024)
    : ⦃⌜True⌝⦄ Factorization.factorByResidual n a ⦃⇓ f => ⌜Prefix n n a f⌝⦄ := by
  unfold Factorization.factorByResidual
  mvcgen [column_spec]
    invariants
      | inv1 => ⇓ ⟨xs, lower, diagonal⟩ => ⌜Prefix n xs.prefix.length a ⟨lower, diagonal⟩⌝
    with
      | vc5 =>
        rename_i pref k suff hlist pair hp
        have hk := Flare.Matrix.Storage.range_current hlist
        exact ⟨hk.2, by simpa only [hk.1] using hp⟩
      | vc6 =>
        rename_i pref k suff hlist pair hp f hf
        have hk := Flare.Matrix.Storage.range_current hlist
        simpa only [List.length_append, List.length_singleton, ← hk.1] using hf
                                                                                | vc7 => exact
                                                                                  prefix_start n a
      | vc8 =>
        rename_i pair h
        simpa [Std.Legacy.Range.toList] using h

/-- Native LDLᵀ factorization succeeds on a bounded, uniformly positive-definite
matrix. Every pivot, factor entry, arithmetic result and storage write is
covered; successful execution and bounded computed factors are conclusions.
The absolute entrywise LDLᵀ reconstruction error is at most 2⁻¹³. -/
theorem factor_accuracy (n : Nat) (a : Array Float) (hn : n ≤ 12)
    (haf : a.all Float.isFinite = true)
    (hA : (matrix n n a - (3 / 16 : ℝ) • 1).PosSemidef)
    (ha : ∀ i j : Fin n, |value (entry n a i.val j.val)| ≤ 1024)
    : ∃ f,
        factor n a = .ok f
        ∧ f.lower.size = n * n
        ∧ f.diagonal.size = n
        ∧ f.lower.all Float.isFinite = true
        ∧ f.diagonal.all Float.isFinite = true
        ∧ (∀ i j : Fin n, i.val < j.val → entry n f.lower i.val j.val = 0.0)
        ∧ (∀ j : Fin n, entry n f.lower j.val j.val = 1.0)
        ∧ (∀ i j : Fin n, |value (entry n f.lower i.val j.val)| ≤ 128)
        ∧ (∀ j : Fin n,
            (1 / 8 : ℝ) ≤ value (f.diagonal.getD j.val 0.0)
            ∧ |value (f.diagonal.getD j.val 0.0)| ≤ 2048)
        ∧ (∀ i j : Fin n,
            |(matrix n n f.lower
                * _root_.Matrix.diagonal (fun t : Fin n => value (f.diagonal.getD t.val 0.0))
                * (matrix n n f.lower).transpose)
                i j
              - matrix n n a i j|
            ≤ (2 : ℝ) ^ (-13 : Int)) := by
  have h := factor_triple n a hn haf hA ha
  cases he : Factorization.factorByResidual n a with
  | error e =>
      rw [he] at h; exact False.elim (h True.intro)
  | ok f =>
      rw [he] at h
      have hf := h True.intro
      refine ⟨
        f,
        by rw [Factorization.factor_eq, he],
        hf.lower_size,
        hf.diagonal_size,
        hf.lower_finite,
        hf.diagonal_finite,
        (fun i j hij => hf.zero_entries i j (Or.inl hij)),
        (fun j => hf.unit_diagonal j j.isLt),
        (fun i j => hf.lower_bound i j j.isLt),
        (fun j => ⟨hf.pivot_lower j j.isLt, hf.pivot_upper j j.isLt⟩),
        ?_
      ⟩
      intro i j
      have heq := real_prefix_eq n n f (Nat.le_refl _)
      have hb := hf.backward_error i j (Or.inl i.isLt)
      rw [← heq] at hb
      exact hb

/-- The completed native factors have an absolute Gram-sum bound inherited
from input diagonals and the proved backward error. It applies to every row
pair and keeps the individual factor products out of the error budget. -/
theorem factor_gram_mass (n : Nat) (a : Array Float) (f : Factor) (M : ℝ)
    (hn : n ≤ 12) (hM : 0 ≤ M) (hM' : M ≤ 1024)
    (haf : a.all Float.isFinite = true)
    (hA : (matrix n n a - (3 / 16 : ℝ) • 1).PosSemidef)
    (ha : ∀ i j : Fin n, |value (entry n a i.val j.val)| ≤ M)
    (he : factor n a = .ok f)
    : ∀ i j : Fin n,
        (∑ k : Fin n,
          |value (entry n f.lower i.val k.val)
            * value (f.diagonal.getD k.val 0.0)
            * value (entry n f.lower j.val k.val)|)
        ≤ M + (2 : ℝ) ^ (-13 : Int) := by
  obtain ⟨f', hf', _, _, _, _, _, _, _, hd, herror⟩ := factor_accuracy n a hn haf hA
    (fun i j => (ha i j).trans hM')
  have hff : f' = f := Except.ok.inj (hf'.symm.trans he)
  subst f'
  intro i j
  apply Flare.Analysis.Factorization.gram_mass_bound (matrix n n f.lower)
    (fun k : Fin n => value (f.diagonal.getD k.val 0.0)) (M + (2 : ℝ) ^ (-13 : Int)) (by positivity)
    (fun k => (by norm_num : (0 : ℝ) ≤ 1 / 8).trans (hd k).1) _ i j
  intro k
  have he' := (abs_le.mp (herror k k)).2
  have hb := (le_abs_self (value (entry n a k.val k.val))).trans (ha k k)
  change _ ≤ M + _
  change _ - value (entry n a k.val k.val) ≤ _ at he'
  linarith only [he', hb]

/-- Every completed factor entry retains its actual native residual equation,
read against the final factor arrays. This enables sharper residual analysis
without re-proving factorization success or assuming ideal factor entries. -/
theorem factor_equations (n : Nat) (a : Array Float) (f : Factor) (hn : n ≤ 12)
    (haf : a.all Float.isFinite = true)
    (hA : (matrix n n a - (3 / 16 : ℝ) • 1).PosSemidef)
    (ha : ∀ i j : Fin n, |value (entry n a i.val j.val)| ≤ 1024)
    (he : factor n a = .ok f)
    : (∀ j : Fin n,
        Factorization.gramResidual n j.val f.lower f.diagonal (entry n a j.val j.val) j.val j.val
        = .ok (f.diagonal.getD j.val 0.0))
      ∧ (∀ i j : Fin n,
          j.val < i.val
          → ∃ r,
              Factorization.gramResidual n j.val f.lower f.diagonal (entry n a i.val j.val) i.val
                  j.val
                = .ok r
              ∧ entry n f.lower i.val j.val = r / f.diagonal.getD j.val 0.0) := by
  have h := factor_triple n a hn haf hA ha
  rw [Factorization.factor_eq] at he
  rw [he] at h
  have hf := h True.intro
  exact ⟨fun j => hf.pivot_equation j j.isLt, fun i j hij => hf.column_equation i j j.isLt hij⟩

/-- Sharper backward error for the actual stored LDLᵀ factors. The input
entry bound controls the absolute Gram mass, so the result scales with the
matrix rather than the coarse bounds used to prove absence of overflow. -/
theorem factor_backward_error (n : Nat) (a : Array Float) (f : Factor) (M : ℝ)
    (hn : n ≤ 12) (hM : 0 ≤ M) (hM' : M ≤ 1024)
    (haf : a.all Float.isFinite = true)
    (hA : (matrix n n a - (3 / 16 : ℝ) • 1).PosSemidef)
    (ha : ∀ i j : Fin n, |value (entry n a i.val j.val)| ≤ M)
    (he : factor n a = .ok f)
    : ∀ i j : Fin n,
        |(matrix n n f.lower
            * _root_.Matrix.diagonal (fun t : Fin n => value (f.diagonal.getD t.val 0.0))
            * (matrix n n f.lower).transpose)
            i j
          - matrix n n a i j|
        ≤ (1002 / 1000 : ℝ)
          * (n + 5)
          * (2 : ℝ) ^ (-53 : Int)
          * (2 * M + (2 : ℝ) ^ (-13 : Int) + (2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int)) := by
  obtain ⟨f', hf', _, _, hlf, hdf, hz, hu, hlb, hdb, _⟩ :=
    factor_accuracy n a hn haf hA (fun i j => (ha i j).trans hM')
  have hff : f' = f := Except.ok.inj (hf'.symm.trans he)
  subst f'
  obtain ⟨hpivot, hcolumn⟩ := factor_equations n a f hn haf hA (fun i j => (ha i j).trans hM') he
  have hmass := factor_gram_mass n a f M hn hM hM' haf hA ha he
  let mass := 2 * M + (2 : ℝ)^(-13 : Int) + (2 : ℝ)^(20 : Int) * (2 : ℝ)^(-1022 : Int)
  have hm0 : 0 ≤ mass := by dsimp [mass]; positivity
  have hmη : (2 : ℝ)^(20 : Int) * (2 : ℝ)^(-1022 : Int) ≤ mass := by
    dsimp [mass]; linarith [zpow_pos (by norm_num : (0 : ℝ) < 2) (-13 : Int)]
  have hmhi : mass ≤ 4096 := by
    have hη : (2 : ℝ)^(-1022 : Int) ≤ (2 : ℝ)^(-20 : Int) :=
      zpow_le_zpow_right₀ (by norm_num) (by norm_num)
    have h := mul_le_mul_of_nonneg_left hη (by positivity : 0 ≤ (2 : ℝ)^(20 : Int))
    have heq : (2 : ℝ)^(20 : Int) * (2 : ℝ)^(-20 : Int) = 1 := by norm_num
    rw [heq] at h
    dsimp [mass]; norm_num only [show (2 : ℝ)^(-13 : Int) = 1 / 8192 by norm_num]; linarith
  have hsum (i j : Fin n) : (∑ t ∈ Finset.range j.val,
      |value (entry n f.lower i.val t) * value (f.diagonal.getD t 0.0) * value (entry n f.lower
        j.val t)|) ≤
      M + (2 : ℝ)^(-13 : Int) := by
    apply le_trans _ (hmass i j)
    rw [Fin.sum_univ_eq_sum_range (fun t =>
      |value (entry n f.lower i.val t) * value (f.diagonal.getD t 0.0) * value (entry n f.lower
        j.val t)|)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_of_lt j.isLt))
      (fun _ _ _ => abs_nonneg _)
  have hres (i j : Fin n) : ∃ r,
      Factorization.gramResidual n j.val f.lower f.diagonal (entry n a i.val j.val) i.val j.val =
        .ok r ∧
      r.isFinite = true ∧ |value r - Factorization.schurResidual n j.val a f.lower f.diagonal i j| ≤
        (1001 / 1000 : ℝ) * (j.val + 4) * (2 : ℝ)^(-53 : Int) * mass := by
    obtain ⟨r, hr, hrf, herr⟩ := Factorization.gramResidual_relative_accuracy n j.val f.lower
      f.diagonal
      (entry n a i.val j.val) i.val j.val (by omega) hlf hdf
      (Flare.Matrix.Storage.getD_finite _ _ haf) ((ha i j).trans hM')
      (fun t ht => hlb i ⟨t, by omega⟩) (fun t ht => (hdb ⟨t, by omega⟩).2)
      (fun t ht => hlb j ⟨t, by omega⟩)
    refine ⟨r, hr, hrf, herr.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    dsimp [mass]
    linarith only [ha i j, hsum i j]
  have hschur (i j : Fin n) : |Factorization.schurResidual n j.val a f.lower f.diagonal i j| ≤ mass
    := by
    dsimp [Factorization.schurResidual]
    calc
      _ ≤ |value (entry n a i.val j.val)|
          + |∑ t ∈ Finset.range j.val,
              value (entry n f.lower i.val t)
              * value (f.diagonal.getD t 0.0)
              * value (entry n f.lower j.val t)| :=
        abs_sub _ _
      _ ≤ |value (entry n a i.val j.val)|
          + ∑ t ∈ Finset.range j.val,
              |value (entry n f.lower i.val t)
                * value (f.diagonal.getD t 0.0)
                * value (entry n f.lower j.val t)| :=
        add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ mass := by
        dsimp [mass]; linarith [ha i j, hsum i j, zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-1022 :
          Int)]
  have hclose (i j : Fin n) : gram n n f i j = gram n j.val f i j +
      value (entry n f.lower i.val j.val) * value (f.diagonal.getD j.val 0.0) := by
    have htruncate : gram n n f i j = gram n (j.val + 1) f i j := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k hkn hkj
      have hk : k < n := Finset.mem_range.mp hkn
      have hjk : j.val < k := by simp only [Finset.mem_range] at hkj; omega
      rw [hz j ⟨k, hk⟩ hjk, zero_value, mul_zero]
    rw [htruncate]
    dsimp only [gram]
    rw [Finset.sum_range_succ, hu j, one_value, mul_one]
  have hbound (i j : Fin n) (hij : j.val ≤ i.val) : |gram n n f i j - matrix n n a i j| ≤
      (1002 / 1000 : ℝ) * (n + 5) * (2 : ℝ)^(-53 : Int) * mass := by
    obtain ⟨r, hr, hrf, herr⟩ := hres i j
    have hid : gram n n f i j - matrix n n a i j =
        value (entry n f.lower i.val j.val) * value (f.diagonal.getD j.val 0.0) -
          Factorization.schurResidual n j.val a f.lower f.diagonal i j := by
      rw [hclose, schur_eq]
      change _ = _ - (matrix n n a i j - gram n j.val f i j)
      ring
    rw [hid]
    have hj : (j.val : ℝ) + 1 ≤ n := by exact_mod_cast j.isLt
    have hcoeff : (1002 / 1000 : ℝ) * (j.val + 6) * (2 : ℝ)^(-53 : Int) * mass ≤
        (1002 / 1000 : ℝ) * (n + 5) * (2 : ℝ)^(-53 : Int) * mass := by
      apply mul_le_mul_of_nonneg_right _ hm0
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    by_cases heq : i = j
    · subst i
      have hrp : r = f.diagonal.getD j.val 0.0 := Except.ok.inj (hr.symm.trans (hpivot j))
      rw [hu j, one_value, one_mul, ← hrp]
      apply herr.trans (le_trans _ hcoeff)
      apply mul_le_mul_of_nonneg_right _ hm0
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
      linarith
    · obtain ⟨r', hr', hquot⟩ := hcolumn i j (by have := Fin.val_ne_of_ne heq; omega)
      have hrr : r' = r := Except.ok.inj (hr'.symm.trans hr)
      subst r'
      rw [hquot]
      exact (Factorization.gram_quotient_backward j.val r (f.diagonal.getD j.val 0.0)
        (Factorization.schurResidual n j.val a f.lower f.diagonal i j) mass (by omega) hrf
        (Flare.Matrix.Storage.getD_finite _ _ hdf) (hdb j).1
        ((le_abs_self _).trans (hdb j).2) hmhi hmη (hschur i j) herr).2.trans hcoeff
  have hAsym := (Flare.Analysis.NumericalBounds.posDef_of_lower_bound (matrix n n a) (3 / 16) (by
    norm_num) hA).isHermitian
  intro i j
  have heq := real_prefix_eq n n f (Nat.le_refl _)
  change |Flare.Analysis.Factorization.prefixGram (matrix n n f.lower)
    (fun t : Fin n => value (f.diagonal.getD t.val 0.0)) (Nat.le_refl n) i j - matrix n n a i j| ≤ _
  rw [heq]
  by_cases hij : j.val ≤ i.val
  · exact hbound i j hij
  · have hs := congr_fun (congr_fun hAsym.eq j) i
    simp only [_root_.Matrix.conjTranspose_apply, star_trivial] at hs
    rw [← gram_symm n n f i j, hs]
    exact hbound j i (by omega)

/-- The complete positive-definite solve, including factorization and both
substitution passes, succeeds on this input profile. The large output bound
establishes absence of overflow; it is not a forward-error budget. -/
theorem solveSPD_success (n columns : Nat) (B : Int) (a b : Array Float)
    (hn : n ≤ 12) (hB : 0 ≤ B) (hB' : B ≤ 512)
    (haf : a.all Float.isFinite = true) (hbf : b.all Float.isFinite = true)
    (hA : (matrix n n a - (3 / 16 : ℝ) • 1).PosSemidef)
    (ha : ∀ i j : Fin n, |value (entry n a i.val j.val)| ≤ 1024)
    (hb : ∀ i j, i < n → j < columns → |value (entry columns b i j)| ≤ (2 : ℝ) ^ B)
    : ∃ r,
        Flare.Matrix.Operations.solveSPD n columns a b = .ok r
        ∧ r.size = n * columns
        ∧ r.all Float.isFinite = true
        ∧ ∀ i j, i < n → j < columns → |value (entry columns r i j)| ≤ (2 : ℝ) ^ (B + 232) := by
  obtain ⟨f, hf, _, _, hl, hd, _, _, hlb, hdb, _⟩ := factor_accuracy n a hn haf hA ha
  obtain ⟨r, hr, hs, hrf, hbound⟩ := LinearSolve.solve_success n columns B f b hn hB hB' hl hd hbf
    (fun i k hi hk => hlb ⟨i, hi⟩ ⟨k, by omega⟩) (fun i hi => (hdb ⟨i, hi⟩).1) hb
  refine ⟨r, ?_, hs, hrf, hbound⟩
  simp only [Flare.Matrix.Operations.solveSPD, solveSPD, hf, bind, Except.bind, hr,
    Flare.Matrix.Operations.adapt]

end Flare.Matrix.PositiveDefiniteFactorization
