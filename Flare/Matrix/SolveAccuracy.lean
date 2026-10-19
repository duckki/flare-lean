module

public import Flare.Analysis.MatrixError
public import Flare.Analysis.Conditioning
public import Flare.Matrix.Substitution
public import Flare.Matrix.PositiveDefiniteFactorization

/-! Compose the actual LDLᵀ factorization and substitution errors into a
linear-system residual and a posteriori solution-error enclosure. All error
enclosures are ghost real expressions; the numerical implementation carries no
runtime certificates. A uniform gain-design budget requires further bounds. -/

@[expose] public section

namespace Flare.Matrix.SolveAccuracy
open Flare.Matrix.Value Flare.Binary64.Value Flare.Binary64.Arithmetic
open Flare.Matrix.Dense

/-- Forward row rounding allowance, expressed using stored operand magnitudes. -/
noncomputable def forwardBound (n columns : Nat) (f : Factor) (b y : Array Float) (i j : Nat) : ℝ :=
  i * (2 : ℝ) ^ (-48 : Int)
  * (|value (entry columns b i j)|
      + ∑ k ∈ Finset.range i, |value (entry n f.lower i k) * value (entry columns y k j)|
      + (2 : ℝ) ^ (-1022 : Int))

/-- Backward row allowance after multiplication by the diagonal pivot. The
quotient is canceled exactly in this ghost bound, avoiding amplification by an
unnecessary inverse-pivot estimate. -/
noncomputable def backwardBound (n columns : Nat) (f : Factor) (y x : Array Float) (i j : Nat)
    : ℝ :=
  (n - i : Nat) * (2 : ℝ) ^ (-47 : Int)
  * (|value (entry columns y i j)|
      + |value (f.diagonal.getD i 0.0)|
        * ∑ k ∈ Finset.Ico (i + 1) n, |value (entry n f.lower k i) * value (entry columns x k j)|
      + |value (f.diagonal.getD i 0.0)| * (2 : ℝ) ^ (-1022 : Int))

/-- Combined substitution allowance plus the proved factorization error
2⁻¹³ times the absolute column sum of the computed solution. -/
noncomputable def residualBound (n columns : Nat) (f : Factor) (b y x : Array Float)
    (i : Fin n) (j : Fin columns)
    : ℝ :=
  forwardBound n columns f b y i.val j.val
  + ∑ k : Fin n, |matrix n n f.lower i k| * backwardBound n columns f y x k.val j.val
  + (2 : ℝ) ^ (-13 : Int) * ∑ k : Fin n, |matrix n columns x k j|

private lemma lower_sum (n i : Nat) (hi : i ≤ n) (f : Nat → ℝ)
    : (∑ k : Fin n, if k.val < i then f k.val else 0) = ∑ k ∈ Finset.range i, f k := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < i then f k else 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

private lemma upper_sum (n i : Nat) (f : Nat → ℝ)
    : (∑ k : Fin n, if i < k.val then f k.val else 0) = ∑ k ∈ Finset.Ico (i + 1) n, f k := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if i < k then f k else 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

private lemma lower_product (n columns : Nat) (f : Factor) (y : Array Float)
    (hz : ∀ i j : Fin n, i.val < j.val → entry n f.lower i.val j.val = 0.0)
    (hu : ∀ i : Fin n, entry n f.lower i.val i.val = 1.0) (i : Fin n) (j : Fin columns)
    : (matrix n n f.lower * matrix n columns y) i j
      = value (entry columns y i.val j.val)
        + ∑ k ∈ Finset.range i.val,
            value (entry n f.lower i.val k) * value (entry columns y k j.val) := by
  rw [_root_.Matrix.mul_apply]
  have he (k : Fin n) : matrix n n f.lower i k * matrix n columns y k j =
      (if k = i then value (entry columns y i.val j.val) else 0) +
      (if k.val < i.val then value (entry n f.lower i.val k.val) * value (entry columns y k.val
        j.val) else 0) := by
    change value (entry n f.lower i.val k.val) * value (entry columns y k.val j.val) = _
    by_cases hki : k = i
    · subst k; simp [hu, one_value]
    · by_cases hlt : k.val < i.val
      · simp [hki, hlt]
      · have hik : i.val < k.val := by have := Fin.val_ne_of_ne hki; omega
        simp [hki, hlt, hz i k hik, zero_value]
  simp_rw [he]
  rw [Finset.sum_add_distrib, lower_sum n i.val (Nat.le_of_lt i.isLt)
    (fun k => value (entry n f.lower i.val k) * value (entry columns y k j.val))]
  simp

private lemma upper_product (n columns : Nat) (f : Factor) (x : Array Float)
    (hz : ∀ i j : Fin n, i.val < j.val → entry n f.lower i.val j.val = 0.0)
    (hu : ∀ i : Fin n, entry n f.lower i.val i.val = 1.0) (i : Fin n) (j : Fin columns)
    : ((matrix n n f.lower).transpose * matrix n columns x) i j
      = value (entry columns x i.val j.val)
        + ∑ k ∈ Finset.Ico (i.val + 1) n,
            value (entry n f.lower k i.val) * value (entry columns x k j.val) := by
  rw [_root_.Matrix.mul_apply]
  have he (k : Fin n) : (matrix n n f.lower).transpose i k * matrix n columns x k j =
      (if k = i then value (entry columns x i.val j.val) else 0) +
      (if i.val < k.val then value (entry n f.lower k.val i.val) * value (entry columns x k.val
        j.val) else 0) := by
    change value (entry n f.lower k.val i.val) * value (entry columns x k.val j.val) = _
    by_cases hki : k = i
    · subst k; simp [hu, one_value]
    · by_cases hlt : i.val < k.val
      · simp [hki, hlt]
      · have hik : k.val < i.val := by have := Fin.val_ne_of_ne hki; omega
        simp [hki, hlt, hz k i hik, zero_value]
  simp_rw [he]
  rw [Finset.sum_add_distrib, upper_sum n i.val
    (fun k => value (entry n f.lower k i.val) * value (entry columns x k j.val))]
  simp

private lemma backward_scaled_bound (n columns : Nat) (f : Factor) (y x : Array Float)
    (i j : Nat) (δ η : ℝ) (hd : value (f.diagonal.getD i 0.0) ≠ 0)
    (hb
      : |value (entry columns x i j)
          - (value (entry columns y i j) / value (f.diagonal.getD i 0.0)
              - ∑ k ∈ Finset.Ico (i + 1) n,
                  value (entry n f.lower k i) * value (entry columns x k j))|
        ≤ δ
          * (|value (entry columns y i j) / value (f.diagonal.getD i 0.0)|
              + ∑ k ∈ Finset.Ico (i + 1) n,
                  |value (entry n f.lower k i) * value (entry columns x k j)|
              + η))
    : |value (f.diagonal.getD i 0.0)
          * (value (entry columns x i j)
              + ∑ k ∈ Finset.Ico (i + 1) n,
                  value (entry n f.lower k i) * value (entry columns x k j))
        - value (entry columns y i j)|
      ≤ δ
        * (|value (entry columns y i j)|
            + |value (f.diagonal.getD i 0.0)|
              * ∑ k ∈ Finset.Ico (i + 1) n,
                  |value (entry n f.lower k i) * value (entry columns x k j)|
            + |value (f.diagonal.getD i 0.0)| * η) := by
  have h := mul_le_mul_of_nonneg_left hb (abs_nonneg (value (f.diagonal.getD i 0.0)))
  rw [← abs_mul] at h
  have heq : value (f.diagonal.getD i 0.0) *
      (value (entry columns x i j) - (value (entry columns y i j) / value (f.diagonal.getD i 0.0) -
        ∑ k ∈ Finset.Ico (i + 1) n, value (entry n f.lower k i) * value (entry columns x k j))) =
      value (f.diagonal.getD i 0.0) * (value (entry columns x i j) +
        ∑ k ∈ Finset.Ico (i + 1) n, value (entry n f.lower k i) * value (entry columns x k j)) -
          value (entry columns y i j) := by field_simp; ring
  rw [heq] at h
  apply h.trans_eq
  rw [abs_div]
  field_simp

private lemma backward_scaled (n columns : Nat) (f : Factor) (y x : Array Float)
    (i j : Nat) (hd : value (f.diagonal.getD i 0.0) ≠ 0)
    (hb
      : |value (entry columns x i j)
          - (value (entry columns y i j) / value (f.diagonal.getD i 0.0)
              - ∑ k ∈ Finset.Ico (i + 1) n,
                  value (entry n f.lower k i) * value (entry columns x k j))|
        ≤ (n - i : Nat) * (2 : ℝ) ^ (-47 : Int)
          * (|value (entry columns y i j) / value (f.diagonal.getD i 0.0)|
              + ∑ k ∈ Finset.Ico (i + 1) n,
                  |value (entry n f.lower k i) * value (entry columns x k j)|
              + (2 : ℝ) ^ (-1022 : Int)))
    : |value (f.diagonal.getD i 0.0)
          * (value (entry columns x i j)
              + ∑ k ∈ Finset.Ico (i + 1) n,
                  value (entry n f.lower k i) * value (entry columns x k j))
        - value (entry columns y i j)|
      ≤ backwardBound n columns f y x i j := by
  exact backward_scaled_bound n columns f y x i j _ _ hd hb

/-- The complete native SPD solve succeeds on the factorization input profile.
Its equation residual is bounded by the combined rounding/factorization allowance
computed from ghost interpretations of the actual intermediate arrays. There is
no assumed native success, residual accuracy or bounded computed factor. -/
theorem solveSPD_residual (n columns : Nat) (B : Int) (a b : Array Float)
    (hn : n ≤ 12) (hB : 0 ≤ B) (hB' : B ≤ 512)
    (haf : a.all Float.isFinite = true) (hbf : b.all Float.isFinite = true)
    (hA : (matrix n n a - (3 / 16 : ℝ) • 1).PosSemidef)
    (ha : ∀ i j : Fin n, |value (entry n a i.val j.val)| ≤ 1024)
    (hb : ∀ i j, i < n → j < columns → |value (entry columns b i j)| ≤ (2 : ℝ) ^ B)
    : ∃ f y x,
        factor n a = .ok f
        ∧ LinearSolve.forward n columns f b = .ok y
        ∧ LinearSolve.backward n columns f y = .ok x
        ∧ Flare.Matrix.Operations.solveSPD n columns a b = .ok x
        ∧ x.size = n * columns
        ∧ x.all Float.isFinite = true
        ∧ ∀ i j,
            |(matrix n n a * matrix n columns x - matrix n columns b) i j|
            ≤ residualBound n columns f b y x i j := by
  obtain ⟨f, hf, _, _, hlf, hdf, hz, hu, hlb, hdb, hfactor⟩ :=
    PositiveDefiniteFactorization.factor_accuracy n a hn haf hA ha
  have hlower : ∀ i k, i < n → k < i → |value (entry n f.lower i k)| ≤ 128 :=
    fun i k hi hk => hlb ⟨i, hi⟩ ⟨k, by omega⟩
  have hdiag : ∀ i, i < n → (1 / 8 : ℝ) ≤ value (f.diagonal.getD i 0.0) :=
    fun i hi => (hdb ⟨i, hi⟩).1
  obtain ⟨y, hy, _, hyf, hyb, hforward⟩ :=
    Substitution.forward_accuracy n columns B f b hn hB hB' hlf hbf hlower hb
  obtain ⟨x, hx, hxs, hxf, _, hbackward⟩ :=
    Substitution.backward_accuracy n columns B f y hn hB hB' hlf hdf hyf hlower hdiag hyb
  have hsolve : solve n columns f b = .ok x := by rw [LinearSolve.solve_split, hy]; exact hx
  refine ⟨f, y, x, hf, hy, hx, ?_, hxs, hxf, ?_⟩
  · simp only [Flare.Matrix.Operations.solveSPD, solveSPD, hf, bind, Except.bind, hsolve,
      Flare.Matrix.Operations.adapt]
  · apply Flare.Analysis.Factorization.componentwise_solve_residual (matrix n n a) (matrix n n
    f.lower)
      (_root_.Matrix.diagonal (fun k : Fin n => value (f.diagonal.getD k.val 0.0)))
      (matrix n columns b) (matrix n columns y) (matrix n columns x) ((2 : ℝ)^(-13 : Int))
      (fun i j => forwardBound n columns f b y i.val j.val)
      (fun i j => backwardBound n columns f y x i.val j.val) hfactor
    · intro i j
      rw [_root_.Matrix.sub_apply, lower_product n columns f y hz hu i j]
      have h := hforward i.val j.val i.isLt j.isLt
      change |value (entry columns y i.val j.val) - (value (entry columns b i.val j.val) -
        ∑ k ∈ Finset.range i.val, value (entry n f.lower i.val k) * value (entry columns y k
          j.val))| ≤
          forwardBound n columns f b y i.val j.val at h
      change |value (entry columns y i.val j.val) +
        (∑ k ∈ Finset.range i.val, value (entry n f.lower i.val k) * value (entry columns y k
          j.val)) -
          value (entry columns b i.val j.val)| ≤ _
      convert h using 1
      congr 1
      ring
    · intro i j
      have hd0 : value (f.diagonal.getD i.val 0.0) ≠ 0 := by
        have := hdiag i.val i.isLt
        linarith
      have h := backward_scaled n columns f y x i.val j.val hd0 (hbackward i.val j.val i.isLt
        j.isLt)
      rw [_root_.Matrix.sub_apply, _root_.Matrix.mul_assoc, _root_.Matrix.diagonal_mul,
        upper_product n columns f x hz hu i j]
      exact h

/-- A posteriori solution-error enclosure for the complete native SPD solve.
The bound uses actual intermediate magnitudes and the input's proved conditioning.
Proofs.Float.Gain separately derives a uniform bound for the composed gain. -/
theorem solveSPD_accuracy (n columns : Nat) (B : Int) (a b : Array Float)
    (hn : n ≤ 12) (hB : 0 ≤ B) (hB' : B ≤ 512)
    (haf : a.all Float.isFinite = true) (hbf : b.all Float.isFinite = true)
    (hA : (matrix n n a - (3 / 16 : ℝ) • 1).PosSemidef)
    (ha : ∀ i j : Fin n, |value (entry n a i.val j.val)| ≤ 1024)
    (hb : ∀ i j, i < n → j < columns → |value (entry columns b i j)| ≤ (2 : ℝ) ^ B)
    : ∃ f y x,
        factor n a = .ok f
        ∧ LinearSolve.forward n columns f b = .ok y
        ∧ LinearSolve.backward n columns f y = .ok x
        ∧ Flare.Matrix.Operations.solveSPD n columns a b = .ok x
        ∧ x.size = n * columns
        ∧ x.all Float.isFinite = true
        ∧ ∀ i j,
            |matrix n columns x i j - ((matrix n n a)⁻¹ * matrix n columns b) i j|
            ≤ n * (∑ k : Fin n, residualBound n columns f b y x k j) / (3 / 16 : ℝ) := by
  obtain ⟨f, y, x, hf, hy, hx, hsolve, hxs, hxf, hres⟩ :=
    solveSPD_residual n columns B a b hn hB hB' haf hbf hA ha hb
  refine ⟨f, y, x, hf, hy, hx, hsolve, hxs, hxf, ?_⟩
  have hpd := Flare.Analysis.NumericalBounds.posDef_of_lower_bound (matrix n n a) (3 / 16) (by
    norm_num) hA
  have hinv : matrix n n a * (matrix n n a)⁻¹ = 1 :=
    _root_.Matrix.mul_nonsing_inv _ ((_root_.Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit)
  intro i j
  let δ := ∑ k : Fin n, residualBound n columns f b y x k j
  have hnonneg (k : Fin n) : 0 ≤ residualBound n columns f b y x k j := (abs_nonneg _).trans (hres k
    j)
  have hδ : 0 ≤ δ := Finset.sum_nonneg (fun k _ => hnonneg k)
  have hbound (k : Fin n) : residualBound n columns f b y x k j ≤ δ :=
    Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ k)
  have hexact : (matrix n n a).mulVec (fun k => ((matrix n n a)⁻¹ * matrix n columns b) k j) =
      fun k => matrix n columns b k j := by
    have heq : matrix n n a * ((matrix n n a)⁻¹ * matrix n columns b) = matrix n columns b := by
      rw [← _root_.Matrix.mul_assoc, hinv, _root_.Matrix.one_mul]
    ext k
    exact congr_fun (congr_fun heq k) j
  have h := Flare.Analysis.NumericalBounds.residual_entrywise_bound (matrix n n a) (3 / 16) δ
    (by norm_num) hδ hA (fun k => matrix n columns x k j)
    (fun k => ((matrix n n a)⁻¹ * matrix n columns b) k j) (fun k => matrix n columns b k j) hexact
    (fun k => (hres k j).trans (hbound k)) i
  exact h

/-- Sharp entrywise reconstruction allowance for the stored factors. -/
noncomputable def factorMassBound (n : Nat) (M : ℝ) : ℝ :=
  (1002 / 1000 : ℝ)
  * (n + 5)
  * (2 : ℝ) ^ (-53 : Int)
  * (2 * M + (2 : ℝ) ^ (-13 : Int) + (2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int))

/-- Forward row allowance from the growing absolute product mass. -/
noncomputable def forwardMassBound (n columns : Nat) (f : Factor) (b y : Array Float) (i j : Nat)
    : ℝ :=
  (1001 / 1000 : ℝ) * (i + 2) * (2 : ℝ) ^ (-53 : Int)
  * (|value (entry columns b i j)|
      + ∑ k ∈ Finset.range i, |value (entry n f.lower i k) * value (entry columns y k j)|
      + (2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int))

/-- Sharp backward row allowance after canceling the exact quotient by its
stored pivot. All quantities are proof-side real interpretations. -/
noncomputable def backwardMassBound (n columns : Nat) (f : Factor) (y x : Array Float) (i j : Nat)
    : ℝ :=
  (1001 / 1000 : ℝ) * ((n - i : Nat) + 3) * (2 : ℝ) ^ (-53 : Int)
  * (|value (entry columns y i j)|
      + |value (f.diagonal.getD i 0.0)|
        * ∑ k ∈ Finset.Ico (i + 1) n, |value (entry n f.lower k i) * value (entry columns x k j)|
      + |value (f.diagonal.getD i 0.0)| * ((2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int)))

/-- Combined componentwise residual allowance using the sharper factorization
and substitution estimates. It contains no runtime certificate computation. -/
noncomputable def residualMassBound (n columns : Nat) (M : ℝ) (f : Factor) (b y x : Array Float)
    (i : Fin n) (j : Fin columns)
    : ℝ :=
  forwardMassBound n columns f b y i.val j.val
  + ∑ k : Fin n, |matrix n n f.lower i k| * backwardMassBound n columns f y x k.val j.val
  + factorMassBound n M * ∑ k : Fin n, |matrix n columns x k j|

/-- The complete native SPD solve succeeds and its equation residual obeys
the mass-scaled factor and substitution budget. Actual intermediate arrays are
linked to their execution; no native accuracy or success is assumed. -/
theorem solveSPD_mass_residual (n columns : Nat) (B : Int) (a b : Array Float) (M : ℝ)
    (hn : n ≤ 12) (hM : 0 ≤ M) (hM' : M ≤ 1024) (hB : 0 ≤ B) (hB' : B ≤ 512)
    (haf : a.all Float.isFinite = true) (hbf : b.all Float.isFinite = true)
    (hA : (matrix n n a - (3 / 16 : ℝ) • 1).PosSemidef)
    (ha : ∀ i j : Fin n, |value (entry n a i.val j.val)| ≤ M)
    (hb : ∀ i j, i < n → j < columns → |value (entry columns b i j)| ≤ (2 : ℝ) ^ B)
    : ∃ f y x,
        factor n a = .ok f
        ∧ LinearSolve.forward n columns f b = .ok y
        ∧ LinearSolve.backward n columns f y = .ok x
        ∧ Flare.Matrix.Operations.solveSPD n columns a b = .ok x
        ∧ x.size = n * columns
        ∧ x.all Float.isFinite = true
        ∧ ∀ i j,
            |(matrix n n a * matrix n columns x - matrix n columns b) i j|
            ≤ residualMassBound n columns M f b y x i j := by
  obtain ⟨f, hf, _, _, hlf, hdf, hz, hu, hlb, hdb, _⟩ :=
    PositiveDefiniteFactorization.factor_accuracy n a hn haf hA (fun i j => (ha i j).trans hM')
  have hfactor := PositiveDefiniteFactorization.factor_backward_error n a f M hn hM hM' haf hA ha hf
  have hlower : ∀ i k, i < n → k < i → |value (entry n f.lower i k)| ≤ 128 :=
    fun i k hi hk => hlb ⟨i, hi⟩ ⟨k, by omega⟩
  have hdiag : ∀ i, i < n → (1 / 8 : ℝ) ≤ value (f.diagonal.getD i 0.0) :=
    fun i hi => (hdb ⟨i, hi⟩).1
  obtain ⟨y, hy, _, hyf, hyb, hforward⟩ :=
    Substitution.forward_mass_accuracy n columns B f b hn hB hB' hlf hbf hlower hb
  obtain ⟨x, hx, hxs, hxf, _, hbackward⟩ :=
    Substitution.backward_mass_accuracy n columns B f y hn hB hB' hlf hdf hyf hlower hdiag hyb
  have hsolve : solve n columns f b = .ok x := by rw [LinearSolve.solve_split, hy]; exact hx
  refine ⟨f, y, x, hf, hy, hx, ?_, hxs, hxf, ?_⟩
  · simp only [Flare.Matrix.Operations.solveSPD, solveSPD, hf, bind, Except.bind, hsolve,
      Flare.Matrix.Operations.adapt]
  · apply Flare.Analysis.Factorization.componentwise_solve_residual (matrix n n a) (matrix n n
    f.lower)
      (_root_.Matrix.diagonal (fun k : Fin n => value (f.diagonal.getD k.val 0.0)))
      (matrix n columns b) (matrix n columns y) (matrix n columns x) (factorMassBound n M)
      (fun i j => forwardMassBound n columns f b y i.val j.val)
      (fun i j => backwardMassBound n columns f y x i.val j.val) hfactor
    · intro i j
      rw [_root_.Matrix.sub_apply, lower_product n columns f y hz hu i j]
      have h := hforward i.val j.val i.isLt j.isLt
      change |value (entry columns y i.val j.val) - (value (entry columns b i.val j.val) -
        ∑ k ∈ Finset.range i.val, value (entry n f.lower i.val k) * value (entry columns y k
          j.val))| ≤
          forwardMassBound n columns f b y i.val j.val at h
      change |value (entry columns y i.val j.val) +
        (∑ k ∈ Finset.range i.val, value (entry n f.lower i.val k) * value (entry columns y k
          j.val)) -
          value (entry columns b i.val j.val)| ≤ _
      convert h using 1
      congr 1
      ring
    · intro i j
      have hd0 : value (f.diagonal.getD i.val 0.0) ≠ 0 := by
        have := hdiag i.val i.isLt
        linarith
      have h := backward_scaled_bound n columns f y x i.val j.val _ _ hd0 (hbackward i.val j.val
        i.isLt j.isLt)
      rw [_root_.Matrix.sub_apply, _root_.Matrix.mul_assoc, _root_.Matrix.diagonal_mul,
        upper_product n columns f x hz hu i j]
      exact h

set_option maxHeartbeats 800000 in
/-- The complete native solve has a residual bound depending only on its
input and final output magnitudes. The forward intermediate is eliminated
using the absolute Gram mass, rather than an overflow-only value bound. -/
theorem solveSPD_reduced_residual (n columns : Nat) (B : Int) (a b : Array Float) (M : ℝ)
    (hn : n ≤ 12) (hM : 0 ≤ M) (hM' : M ≤ 1024) (hB : 0 ≤ B) (hB' : B ≤ 512)
    (haf : a.all Float.isFinite = true) (hbf : b.all Float.isFinite = true)
    (hA : (matrix n n a - (3 / 16 : ℝ) • 1).PosSemidef)
    (ha : ∀ i j : Fin n, |value (entry n a i.val j.val)| ≤ M)
    (hb : ∀ i j, i < n → j < columns → |value (entry columns b i j)| ≤ (2 : ℝ) ^ B)
    : ∃ x,
        Flare.Matrix.Operations.solveSPD n columns a b = .ok x
        ∧ x.size = n * columns
        ∧ x.all Float.isFinite = true
        ∧ let α := (1001 / 1000 : ℝ) * (n + 1) * (2 : ℝ) ^ (-53 : Int)
          let β := (1001 / 1000 : ℝ) * (n + 3) * (2 : ℝ) ^ (-53 : Int)
          ∀ i j,
            |(matrix n n a * matrix n columns x - matrix n columns b) i j|
            ≤ α * |matrix n columns b i j|
              + (((1001 / 1000 : ℝ) * α + (2001 / 1000 : ℝ) * β) * (M + (2 : ℝ) ^ (-13 : Int))
                  + factorMassBound n M)
                * (∑ t : Fin n, |matrix n columns x t j|)
              + (α + 2 * β * (n * 128 * 2048))
                * ((2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int)) := by
  obtain ⟨f, hf, _, _, hlf, hdf, hz, hu, hlb, hdb, _⟩ :=
    PositiveDefiniteFactorization.factor_accuracy n a hn haf hA (fun i j => (ha i j).trans hM')
  have hfactor := PositiveDefiniteFactorization.factor_backward_error n a f M hn hM hM' haf hA ha hf
  have hlower : ∀ i k, i < n → k < i → |value (entry n f.lower i k)| ≤ 128 :=
    fun i k hi hk => hlb ⟨i, hi⟩ ⟨k, by omega⟩
  have hdiag : ∀ i, i < n → (1 / 8 : ℝ) ≤ value (f.diagonal.getD i 0.0) :=
    fun i hi => (hdb ⟨i, hi⟩).1
  obtain ⟨y, hy, _, hyf, hyb, hforward⟩ :=
    Substitution.forward_mass_accuracy n columns B f b hn hB hB' hlf hbf hlower hb
  obtain ⟨x, hx, hxs, hxf, _, hbackward⟩ :=
    Substitution.backward_mass_accuracy n columns B f y hn hB hB' hlf hdf hyf hlower hdiag hyb
  have hsolve : solve n columns f b = .ok x := by rw [LinearSolve.solve_split, hy]; exact hx
  refine ⟨x, ?_, hxs, hxf, ?_⟩
  · simp only [Flare.Matrix.Operations.solveSPD, solveSPD, hf, bind, Except.bind, hsolve,
      Flare.Matrix.Operations.adapt]
  let α := (1001 / 1000 : ℝ) * (n + 1) * (2 : ℝ)^(-53 : Int)
  let β := (1001 / 1000 : ℝ) * (n + 3) * (2 : ℝ)^(-53 : Int)
  have hn' : (n : ℝ) ≤ 12 := by exact_mod_cast hn
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hα' : α ≤ 1 / 4 := by dsimp [α]; norm_num; linarith
  have hβ' : β ≤ 1 / 4000 := by dsimp [β]; norm_num; linarith
  have hdp (k : Fin n) : 0 ≤ value (f.diagonal.getD k.val 0.0) := by linarith [(hdb k).1]
  have hprefix (i : Fin n) (j : Fin columns) :
      (∑ k ∈ Finset.range i.val, |value (entry n f.lower i.val k) * value (entry columns y k
        j.val)|) ≤
        ∑ k : Fin n, |matrix n n f.lower i k * matrix n columns y k j| := by
    change _ ≤ ∑ k : Fin n, |value (entry n f.lower i.val k.val) * value (entry columns y k.val
      j.val)|
    rw [Fin.sum_univ_eq_sum_range (fun k => |value (entry n f.lower i.val k) * value (entry columns
      y k j.val)|)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono i.isLt.le) (fun _ _ _ =>
      abs_nonneg _)
  have hupper (i : Fin n) (j : Fin columns) :
      (∑ k ∈ Finset.Ico (i.val + 1) n, |value (entry n f.lower k i.val) * value (entry columns x k
        j.val)|) ≤
        ∑ k : Fin n, |matrix n n f.lower k i * matrix n columns x k j| := by
    change _ ≤ ∑ k : Fin n, |value (entry n f.lower k.val i.val) * value (entry columns x k.val
      j.val)|
    rw [Fin.sum_univ_eq_sum_range (fun k => |value (entry n f.lower k i.val) * value (entry columns
      x k j.val)|)]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro k hk; exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2) (fun _ _ _ => abs_nonneg
        _)
  have hp : ∀ i : Fin n, (∑ k : Fin n, |matrix n n f.lower i k| * value (f.diagonal.getD k.val 0.0))
    ≤
      (n : ℝ) * 128 * 2048 := by
    intro i
    have hbnd (k : Fin n) : |matrix n n f.lower i k| * value (f.diagonal.getD k.val 0.0) ≤ 128 *
      2048 :=
      mul_le_mul (hlb i k) ((le_abs_self _).trans (hdb k).2) (hdp k) (by norm_num)
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hbnd k)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
      using hh
  apply Flare.Analysis.Factorization.solve_residual_mass (matrix n n a) (matrix n n f.lower)
    (fun k : Fin n => value (f.diagonal.getD k.val 0.0)) (matrix n columns b) (matrix n columns y)
    (matrix n columns x) α β ((2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int))
    (M + (2 : ℝ) ^ (-13 : Int)) (n * 128 * 2048) (factorMassBound n M) hα hα' hβ hβ' (by positivity)
    (by positivity) (by positivity) hdp
    (PositiveDefiniteFactorization.factor_gram_mass n a f M hn hM hM' haf hA ha hf) hp hfactor
  · intro i j
    have hh := hforward i.val j.val i.isLt j.isLt
    rw [_root_.Matrix.sub_apply, lower_product n columns f y hz hu i j]
    have heq : value (entry columns y i.val j.val) +
        (∑ k ∈ Finset.range i.val, value (entry n f.lower i.val k) * value (entry columns y k
          j.val)) -
          value (entry columns b i.val j.val) =
        value (entry columns y i.val j.val) - (value (entry columns b i.val j.val) -
          ∑ k ∈ Finset.range i.val, value (entry n f.lower i.val k) * value (entry columns y k
            j.val)) := by ring
    change |value (entry columns y i.val j.val) +
      (∑ k ∈ Finset.range i.val, value (entry n f.lower i.val k) * value (entry columns y k j.val))
        -
        value (entry columns b i.val j.val)| ≤ _
    rw [heq]
    apply hh.trans
    have hcoeff : (1001 / 1000 : ℝ) * (i.val + 2) * (2 : ℝ)^(-53 : Int) ≤ α := by
      dsimp [α]
      have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      linarith
    exact mul_le_mul hcoeff (add_le_add (add_le_add le_rfl (hprefix i j)) le_rfl) (by positivity) hα
  · intro i j
    have hd0 : value (f.diagonal.getD i.val 0.0) ≠ 0 := by linarith [(hdb i).1]
    have hh := backward_scaled_bound n columns f y x i.val j.val _ _ hd0
      (hbackward i.val j.val i.isLt j.isLt)
    rw [_root_.Matrix.sub_apply, _root_.Matrix.mul_assoc, _root_.Matrix.diagonal_mul,
      upper_product n columns f x hz hu i j]
    apply hh.trans
    have hcoeff : (1001 / 1000 : ℝ) * ((n - i.val : Nat) + 3) * (2 : ℝ)^(-53 : Int) ≤ β := by
      dsimp [β]
      have hi : ((n - i.val : Nat) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n i.val
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      linarith
    simp only [abs_of_nonneg (hdp i)]
    exact mul_le_mul hcoeff
      (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hupper i j) (hdp i))) le_rfl)
      (add_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg (hdp i)
        (Finset.sum_nonneg fun _ _ => abs_nonneg _)))
          (mul_nonneg (hdp i) (by positivity))) hβ

private lemma noise_residual_coefficients (n : Nat) (hn : n ≤ 12)
    : let α := (1001 / 1000 : ℝ) * (n + 1) * (2 : ℝ) ^ (-53 : Int)
      let β := (1001 / 1000 : ℝ) * (n + 3) * (2 : ℝ) ^ (-53 : Int)
      α ≤ 3 / 2000000000000000
      ∧ ((1001 / 1000 : ℝ) * α + (2001 / 1000 : ℝ) * β) * (4 + (2 : ℝ) ^ (-13 : Int))
          + factorMassBound n 4
        ≤ 71 / 2000000000000000
      ∧ (α + 2 * β * (n * 128 * 2048)) * ((2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int))
        ≤ (2 : ℝ) ^ (-1022 : Int) := by
  dsimp only
  let α := (1001 / 1000 : ℝ) * (n + 1) * (2 : ℝ)^(-53 : Int)
  let β := (1001 / 1000 : ℝ) * (n + 3) * (2 : ℝ)^(-53 : Int)
  have hn' : (n : ℝ) ≤ 12 := by exact_mod_cast hn
  have hα : α ≤ 3 / 2000000000000000 := by dsimp [α]; norm_num; linarith
  have hβ : β ≤ 7 / 4000000000000000 := by dsimp [β]; norm_num; linarith
  have hη : (2 : ℝ)^(20 : Int) * (2 : ℝ)^(-1022 : Int) ≤ (2 : ℝ)^(-20 : Int) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    exact zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hf : factorMassBound n 4 ≤ 61 / 4000000000000000 := by
    unfold factorMassBound
    calc
      _ ≤ (1002 / 1000 : ℝ)
          * (12 + 5)
          * (2 : ℝ) ^ (-53 : Int)
          * (2 * 4 + (2 : ℝ) ^ (-13 : Int) + (2 : ℝ) ^ (-20 : Int)) := by
        gcongr
      _ ≤ _ := by norm_num
  refine ⟨hα, ?_, ?_⟩
  · change ((1001 / 1000 : ℝ) * α + (2001 / 1000 : ℝ) * β) * (4 + (2 : ℝ)^(-13 : Int)) + _ ≤ _
    norm_num only [show (2 : ℝ)^(-13 : Int) = 1 / 8192 by norm_num]
    linarith
  · have hcoef : α + 2 * β * (n * 128 * 2048) ≤
        (3 / 2000000000000000 : ℝ) + 2 * (7 / 4000000000000000) * (12 * 128 * 2048) := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      have hβ0 : 0 ≤ β := by dsimp [β]; positivity
      gcongr
    change (α + 2 * β * (n * 128 * 2048)) * _ ≤ _
    calc
      _ ≤ ((3 / 2000000000000000 : ℝ) + 2 * (7 / 4000000000000000) * (12 * 128 * 2048))
          * ((2 : ℝ) ^ (20 : Int) * (2 : ℝ) ^ (-1022 : Int)) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ _ := by
        rw [← mul_assoc]
        exact (mul_le_mul_of_nonneg_right
                (by norm_num
                  : ((3 / 2000000000000000 : ℝ) + 2 * (7 / 4000000000000000) * (12 * 128 * 2048))
                      * (2 : ℝ) ^ (20 : Int)
                    ≤ 1)
                (by positivity)).trans_eq
          (one_mul _)

/-- Uniform accuracy for the fixed-profile positive-definite solve. On `R ≥ I/4`, entries bounded
by four, and at most twelve rows, the actual native result has columnwise
Euclidean error at most `8e-12` times the input column norm plus underflow. -/
theorem noise_solve_nearest_accuracy (n columns : Nat) (B : Int) (a b : Array Float)
    (hn : n ≤ 12) (hB : 0 ≤ B) (hB' : B ≤ 512)
    (haf : a.all Float.isFinite = true) (hbf : b.all Float.isFinite = true)
    (hA : (matrix n n a - (1 / 4 : ℝ) • 1).PosSemidef)
    (ha : ∀ i j : Fin n, |value (entry n a i.val j.val)| ≤ 4)
    (hb : ∀ i j, i < n → j < columns → |value (entry columns b i j)| ≤ (2 : ℝ) ^ B)
    : ∃ x,
        Flare.Matrix.Operations.solveSPD n columns a b = .ok x
        ∧ x.size = n * columns
        ∧ x.all Float.isFinite = true
        ∧ ∀ j : Fin columns,
            ‖WithLp.toLp 2
              (fun i : Fin n =>
                matrix n columns x i j - ((matrix n n a)⁻¹ * matrix n columns b) i j)‖
            ≤ (8 / 1000000000000 : ℝ) * ‖WithLp.toLp 2 (fun i : Fin n => matrix n columns b i j)‖
              + (2 : ℝ) ^ (-1000 : Int) := by
  have hweak : (matrix n n a - (3 / 16 : ℝ) • 1).PosSemidef := by
    have hh := hA.add ((_root_.Matrix.PosSemidef.one (n := Fin n) (R := ℝ)).smul (by norm_num : (0 :
      ℝ) ≤ 1 / 16))
    convert hh using 1
    module
  obtain ⟨x, hx, hxs, hxf, hres⟩ := solveSPD_reduced_residual n columns B a b 4 hn (by norm_num)
    (by norm_num) hB hB' haf hbf hweak ha hb
  refine ⟨x, hx, hxs, hxf, ?_⟩
  have hcoeff := noise_residual_coefficients n hn
  obtain ⟨hα, hc, hδ⟩ := hcoeff
  have hn' : (n : ℝ) ≤ 12 := by exact_mod_cast hn
  have hgap : (n : ℝ) * (71 / 2000000000000000) < 1 / 4 := by linarith
  have hden : (6 / 25 : ℝ) ≤ 1 / 4 - n * (71 / 2000000000000000) := by linarith
  have hpd := Flare.Analysis.NumericalBounds.posDef_of_lower_bound (matrix n n a) (1 / 4) (by
    norm_num) hA
  have hinv : matrix n n a * (matrix n n a)⁻¹ = 1 :=
    _root_.Matrix.mul_nonsing_inv _ ((_root_.Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit)
  have heq : matrix n n a * ((matrix n n a)⁻¹ * matrix n columns b) = matrix n columns b := by
    rw [← _root_.Matrix.mul_assoc, hinv, _root_.Matrix.one_mul]
  intro j
  let bv : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => matrix n columns b i j)
  let xv : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => matrix n columns x i j)
  let exact : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => ((matrix n n a)⁻¹ * matrix n
    columns b) i j)
  have hexact : (matrix n n a).mulVec exact = bv := by
    funext i
    exact congr_fun (congr_fun heq i) j
  have hr (i : Fin n) : |(matrix n n a).mulVec xv i - bv i| ≤
      (3 / 2000000000000000 : ℝ) * |bv i| + (71 / 2000000000000000 : ℝ) * (∑ k, |xv k|) +
        (2 : ℝ)^(-1022 : Int) := by
    exact (hres i j).trans (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right hα (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun _ _ => abs_nonneg _))) hδ)
  have hh := Flare.Analysis.LinearSolve.conditioned_solve_bounds (matrix n n a) bv xv exact (1 / 4)
    (3 / 2000000000000000) (71 / 2000000000000000) ((2 : ℝ)^(-1022 : Int))
    (by norm_num) hA (by norm_num) (by norm_num) (by positivity) hgap hexact hr
  change ‖xv - exact‖ ≤ (8 / 1000000000000 : ℝ) * ‖bv‖ + (2 : ℝ)^(-1000 : Int)
  apply hh.2.trans
  apply (div_le_iff₀ (sub_pos.mpr hgap)).mpr
  have hsqrt : Real.sqrt (n : ℝ) ≤ 4 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num; linarith⟩
  have hnb := mul_le_mul_of_nonneg_right hn' (norm_nonneg bv)
  have hη0 : 0 ≤ (2 : ℝ)^(-1022 : Int) := by positivity
  have hsqη := mul_le_mul_of_nonneg_right hsqrt hη0
  have hnum : (3 / 2000000000000000 : ℝ) * ‖bv‖ +
      n * (71 / 2000000000000000) * (‖bv‖ / (1 / 4)) + Real.sqrt n * (2 : ℝ)^(-1022 : Int) ≤
        (7 / 4000000000000 : ℝ) * ‖bv‖ + 4 * (2 : ℝ)^(-1022 : Int) := by
    norm_num only [div_div, div_one]
    nlinarith only [hnb, hsqη, norm_nonneg bv]
  have hηsmall : 4 * (2 : ℝ)^(-1022 : Int) ≤ (6 / 25 : ℝ) * (2 : ℝ)^(-1000 : Int) := by
    rw [show (-1022 : Int) = -1000 - 22 by omega, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have hh := mul_le_mul_of_nonneg_right (by norm_num : (4 : ℝ) / (2 : ℝ)^(22 : Int) ≤ 6 / 25)
      (by positivity : 0 ≤ (2 : ℝ)^(-1000 : Int))
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh
  have htarget : (7 / 4000000000000 : ℝ) * ‖bv‖ + 4 * (2 : ℝ)^(-1022 : Int) ≤
      ((8 / 1000000000000 : ℝ) * ‖bv‖ + (2 : ℝ)^(-1000 : Int)) * (6 / 25) := by
    nlinarith only [hηsmall, norm_nonneg bv]
  exact hnum.trans (htarget.trans (mul_le_mul_of_nonneg_left hden (by positivity)))

/-- Uniform accuracy for the fixed-profile positive-definite solve. On `R ≥ I/4`, entries bounded
by four, and at most twelve rows, the actual native result has columnwise
Euclidean error at most `3e-11` times the input column norm plus underflow. -/
theorem noise_solve_accuracy (n columns : Nat) (B : Int) (a b : Array Float)
    (hn : n ≤ 12) (hB : 0 ≤ B) (hB' : B ≤ 512)
    (haf : a.all Float.isFinite = true) (hbf : b.all Float.isFinite = true)
    (hA : (matrix n n a - (1 / 4 : ℝ) • 1).PosSemidef)
    (ha : ∀ i j : Fin n, |value (entry n a i.val j.val)| ≤ 4)
    (hb : ∀ i j, i < n → j < columns → |value (entry columns b i j)| ≤ (2 : ℝ) ^ B)
    : ∃ x,
        Flare.Matrix.Operations.solveSPD n columns a b = .ok x
        ∧ x.size = n * columns
        ∧ x.all Float.isFinite = true
        ∧ ∀ j : Fin columns,
            ‖WithLp.toLp 2
              (fun i : Fin n =>
                matrix n columns x i j - ((matrix n n a)⁻¹ * matrix n columns b) i j)‖
            ≤ (3 / 100000000000 : ℝ) * ‖WithLp.toLp 2 (fun i : Fin n => matrix n columns b i j)‖
              + (2 : ℝ) ^ (-1000 : Int) := by
  obtain ⟨x, hx, hxs, hxf, he⟩ :=
    noise_solve_nearest_accuracy n columns B a b hn hB hB' haf hbf hA ha hb
  refine ⟨x, hx, hxs, hxf, fun j => (he j).trans ?_⟩
  exact add_le_add
    (mul_le_mul_of_nonneg_right
      (by norm_num : (8 / 1000000000000 : ℝ) ≤ 3 / 100000000000)
      (norm_nonneg (WithLp.toLp 2 (fun i : Fin n => matrix n columns b i j))))
    le_rfl

open scoped Matrix.Norms.L2Operator

/-- The complete known-noise solve has a small Frobenius residual relative to
its exact solution. Keeping that solution scale is essential when forming the
Gram term `CᵀR⁻¹C`; the right-hand-side scale can be much larger. -/
theorem noise_solve_frobenius (n columns : Nat) (B : Int) (a b : Array Float)
    (hn : n ≤ 12) (hcolumns : columns ≤ 12) (hB : 0 ≤ B) (hB' : B ≤ 512)
    (haf : a.all Float.isFinite = true) (hbf : b.all Float.isFinite = true)
    (hA : (matrix n n a - (1 / 4 : ℝ) • 1).PosSemidef)
    (ha : ∀ i j : Fin n, |value (entry n a i.val j.val)| ≤ 4)
    (hb : ∀ i j, i < n → j < columns → |value (entry columns b i j)| ≤ (2 : ℝ) ^ B)
    : let F := (matrix n n a)⁻¹ * matrix n columns b
      ∃ x,
        Flare.Matrix.Operations.solveSPD n columns a b = .ok x
        ∧ x.size = n * columns
        ∧ x.all Float.isFinite = true
        ∧ ‖Flare.Analysis.MatrixError.entries (matrix n columns x)‖
          ≤ (1001 / 1000 : ℝ) * ‖Flare.Analysis.MatrixError.entries F‖ + (2 : ℝ) ^ (-1000 : Int)
        ∧ ‖Flare.Analysis.MatrixError.entries
            (matrix n n a * matrix n columns x - matrix n columns b)‖
          ≤ (501 / 1000000000000000 : ℝ) * ‖Flare.Analysis.MatrixError.entries F‖
            + (2 : ℝ) ^ (-1000 : Int) := by
  dsimp only
  have hweak : (matrix n n a - (3 / 16 : ℝ) • 1).PosSemidef := by
    have hh := hA.add ((_root_.Matrix.PosSemidef.one (n := Fin n) (R := ℝ)).smul (by norm_num : (0 :
      ℝ) ≤ 1 / 16))
    convert hh using 1
    module
  obtain ⟨x, hx, hxs, hxf, hres⟩ := solveSPD_reduced_residual n columns B a b 4 hn
    (by norm_num) (by norm_num) hB hB' haf hbf hweak ha hb
  let A := matrix n n a
  let C := matrix n columns b
  let X := matrix n columns x
  let F := A⁻¹ * C
  let E := A * X - C
  have hn' : (n : ℝ) ≤ 12 := by exact_mod_cast hn
  have hAn : ‖A‖ ≤ 48 := by
    have hh := Flare.Analysis.SpectralPerturbation.norm_le_entries A 4 (by norm_num) ha
    linarith only [hh, hn']
  have hAi : ‖A⁻¹‖ ≤ 4 :=
    (Flare.Analysis.Conditioning.inverse_norm_bound A (1 / 4) (by norm_num) hA).trans_eq (by
      norm_num)
  have hpd := Flare.Analysis.NumericalBounds.posDef_of_lower_bound A (1 / 4) (by norm_num) hA
  let := hpd.isUnit.invertible
  have hCF : C = A * F := by dsimp [F]; rw [← _root_.Matrix.mul_assoc,
    _root_.Matrix.mul_inv_of_invertible, _root_.Matrix.one_mul]
  have hXE : X - F = A⁻¹ * E := by
    dsimp only [F, E]
    rw [_root_.Matrix.mul_sub, ← _root_.Matrix.mul_assoc, _root_.Matrix.inv_mul_of_invertible,
      _root_.Matrix.one_mul]
  have hCn
      : ‖Flare.Analysis.MatrixError.entries C‖ ≤ 48 * ‖Flare.Analysis.MatrixError.entries F‖ := by
    rw [hCF]
    exact (Flare.Analysis.MatrixError.entries_mul_le A F).trans
      (mul_le_mul_of_nonneg_right hAn (norm_nonneg _))
  have hXn : ‖Flare.Analysis.MatrixError.entries X‖ ≤ ‖Flare.Analysis.MatrixError.entries F‖ + 4 *
    ‖Flare.Analysis.MatrixError.entries E‖ := by
    have ht := norm_sub_le_norm_sub_add_norm_sub (Flare.Analysis.MatrixError.entries X)
      (Flare.Analysis.MatrixError.entries F) 0
    simp only [sub_zero] at ht
    rw [← Flare.Analysis.MatrixError.entries_sub, hXE] at ht
    have he := (Flare.Analysis.MatrixError.entries_mul_le A⁻¹ E).trans
      (mul_le_mul_of_nonneg_right hAi (norm_nonneg _))
    linarith only [ht, he]
  obtain ⟨hα, hc, hδ⟩ := noise_residual_coefficients n hn
  have hr (i j) : |E i j| ≤ (3 / 2000000000000000 : ℝ) * |C i j| +
      (71 / 2000000000000000 : ℝ) * (∑ k, |X k j|) + (2 : ℝ)^(-1022 : Int) :=
    (hres i j).trans (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right hα (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun _ _ => abs_nonneg _))) hδ)
  have hh := Flare.Analysis.MatrixError.entries_residual_norm E C X
    (3 / 2000000000000000) (71 / 2000000000000000) ((2 : ℝ)^(-1022 : Int))
    (by norm_num) (by norm_num) (by positivity) hr
  have hsqrtN : Real.sqrt (n : ℝ) ≤ 4 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num; linarith⟩
  have hsqrtC : Real.sqrt (columns : ℝ) ≤ 4 := by
    have hc' : (columns : ℝ) ≤ 12 := by exact_mod_cast hcolumns
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num; linarith⟩
  have hη := mul_le_mul_of_nonneg_right
    (mul_le_mul hsqrtC hsqrtN (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 4))
    (by positivity : 0 ≤ (2 : ℝ)^(-1022 : Int))
  have hnX := mul_le_mul_of_nonneg_right hn' (norm_nonneg (Flare.Analysis.MatrixError.entries X))
  have hraw : ‖Flare.Analysis.MatrixError.entries E‖ ≤
      (498 / 1000000000000000 : ℝ) * ‖Flare.Analysis.MatrixError.entries F‖ +
        (1704 / 1000000000000000 : ℝ) * ‖Flare.Analysis.MatrixError.entries E‖ + 16 * (2 : ℝ)^(-1022
          : Int) := by
    nlinarith only [hh, hCn, hXn, hη, hnX]
  have htiny : 128 * (2 : ℝ)^(-1022 : Int) ≤ (2 : ℝ)^(-1000 : Int) := by
    rw [show (-1000 : Int) = -1022 + 22 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    nlinarith only [zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-1022 : Int),
      show (2 : ℝ)^(22 : Int) = 4194304 by norm_num]
  have hEn : ‖Flare.Analysis.MatrixError.entries E‖ ≤
      (501 / 1000000000000000 : ℝ) * ‖Flare.Analysis.MatrixError.entries F‖ + 32 * (2 : ℝ)^(-1022 :
        Int) := by
    nlinarith only [hraw, norm_nonneg (Flare.Analysis.MatrixError.entries F),
      zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-1022 : Int)]
  refine ⟨x, hx, hxs, hxf, ?_, ?_⟩
  · change ‖Flare.Analysis.MatrixError.entries X‖ ≤ (1001 / 1000 : ℝ) *
    ‖Flare.Analysis.MatrixError.entries F‖ + _
    nlinarith only [hXn, hEn, htiny, norm_nonneg (Flare.Analysis.MatrixError.entries F)]
  · change ‖Flare.Analysis.MatrixError.entries E‖ ≤ (501 / 1000000000000000 : ℝ) *
    ‖Flare.Analysis.MatrixError.entries F‖ + _
    have hη0 : 0 ≤ (2 : ℝ)^(-1022 : Int) := by positivity
    linarith only [hEn, htiny, hη0]

end Flare.Matrix.SolveAccuracy
