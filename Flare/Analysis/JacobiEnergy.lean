import Flare.Analysis.Jacobi

/-! Matrix energy identities for the project Jacobi iteration. These proof-side
sums connect entrywise native rotation facts to the convergence criterion. -/

namespace Flare.Analysis.JacobiEnergy

open scoped BigOperators

/-- Squared Frobenius norm, used as a ghost bound on stored matrix entries. -/
noncomputable def energy {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

/-- Squared off-diagonal Frobenius norm; both symmetric copies are counted. -/
noncomputable def offEnergy {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else A i j ^ 2

/-- Indices outside the selected two-dimensional pivot block. -/
def outside {n : Nat} (p q : Fin n) : Finset (Fin n) :=
  (Finset.univ.erase p).erase q

theorem mem_outside {n : Nat} (p q k : Fin n) : k ∈ outside p q ↔ k ≠ p ∧ k ≠ q := by
  simp [outside, and_comm]

private theorem sum_split_pair {n : Nat} (f : Fin n → ℝ) (p q : Fin n) (hpq : p ≠ q)
    : ∑ i, f i = f p + f q + ∑ k ∈ outside p q, f k := by
  have hp := Finset.sum_erase_add Finset.univ f (Finset.mem_univ p)
  have hq := Finset.sum_erase_add (Finset.univ.erase p) f (by simp [Ne.symm hpq] : q ∈
    Finset.univ.erase p)
  dsimp only [outside]
  linarith

private theorem symmetric_sum_split {n : Nat} (F : Fin n → Fin n → ℝ) (p q : Fin n)
    (hpq : p ≠ q) (hF : ∀ i j, F i j = F j i)
    : ∑ i, ∑ j, F i j
      = F p p
        + 2 * F p q
        + F q q
        + 2 * (∑ k ∈ outside p q, (F k p + F k q))
        + ∑ k ∈ outside p q, ∑ l ∈ outside p q, F k l := by
  rw [sum_split_pair (fun i => ∑ j, F i j) p q hpq]
  simp_rw [sum_split_pair (F _) p q hpq]
  rw [hF q p]
  have hP : ∑ k ∈ outside p q, F p k = ∑ k ∈ outside p q, F k p :=
    Finset.sum_congr rfl (fun k _ => hF p k)
  have hQ : ∑ k ∈ outside p q, F q k = ∑ k ∈ outside p q, F k q :=
    Finset.sum_congr rfl (fun k _ => hF q k)
  simp only [hP, hQ, Finset.sum_add_distrib]
  ring

/-- The matrix energy separates into its pivot block, affected row pairs and
untouched block. Symmetry is the only mathematical premise. -/
theorem energy_split {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n)
    (hpq : p ≠ q) (hA : ∀ i j, A i j = A j i)
    : energy A
      = A p p ^ 2
        + 2 * A p q ^ 2
        + A q q ^ 2
        + 2 * (∑ k ∈ outside p q, (A k p ^ 2 + A k q ^ 2))
        + ∑ k ∈ outside p q, ∑ l ∈ outside p q, A k l ^ 2 :=
  symmetric_sum_split (fun i j => A i j ^ 2) p q hpq (fun i j => congrArg (· ^ 2) (hA i j))

/-- Off-diagonal energy has the same decomposition without diagonal entries. -/
theorem offEnergy_split {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n)
    (hpq : p ≠ q) (hA : ∀ i j, A i j = A j i)
    : offEnergy A
      = 2 * A p q ^ 2
        + 2 * (∑ k ∈ outside p q, (A k p ^ 2 + A k q ^ 2))
        + ∑ k ∈ outside p q, ∑ l ∈ outside p q, if k = l then 0 else A k l ^ 2 := by
  have h := symmetric_sum_split (fun i j => if i = j then 0 else A i j ^ 2) p q hpq (by
    intro i j
    by_cases hij : i = j
    · subst j; rfl
    · simp [hij, Ne.symm hij, hA i j])
  have hpair : (∑ k ∈ outside p q, ((if k = p then 0 else A k p ^ 2) +
      (if k = q then 0 else A k q ^ 2))) = ∑ k ∈ outside p q, (A k p ^ 2 + A k q ^ 2) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := (mem_outside p q k).mp hk
    simp [hk'.1, hk'.2]
  simpa only [offEnergy, ite_true, if_neg hpq, zero_add, add_zero, hpair] using h

theorem energy_nonneg {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ energy A := by
  unfold energy; positivity

theorem offEnergy_nonneg {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ offEnergy A := by
  unfold offEnergy
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity

theorem entry_sq_le_energy {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
    : A i j ^ 2 ≤ energy A := by
  apply le_trans (Finset.single_le_sum (fun k _ => sq_nonneg (A i k)) (Finset.mem_univ j))
  exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg (A k l))
    (Finset.mem_univ i)

theorem pivot_sq_le_offEnergy {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) (hpq : p ≠ q)
    : A p q ^ 2 ≤ offEnergy A := by
  have hrow := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => if p = j then (0 : ℝ) else A p j ^ 2)
    (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ q)
  simp only [if_neg hpq] at hrow
  apply hrow.trans
  unfold offEnergy
  exact Finset.single_le_sum (f := fun i => ∑ j, if i = j then (0 : ℝ) else A i j ^ 2)
    (fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity) (Finset.mem_univ p)

theorem offEnergy_le_energy {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) : offEnergy A ≤ energy A := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _; split_ifs <;> first | rfl | positivity

/-- A largest off-diagonal magnitude bounds the entire off-diagonal energy.
This counts exactly `n(n-1)` entries, including both symmetric copies. -/
theorem offEnergy_le_max {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ)
    (hr : 0 ≤ r) (hA : ∀ i j, i ≠ j → |A i j| ≤ r)
    : offEnergy A ≤ (n : ℝ) * (n - 1) * r ^ 2 := by
  have hrow (i : Fin n) : (∑ j, if i = j then 0 else r ^ 2) = ((n : ℝ) - 1) * r ^ 2 := by
    have h := Finset.sum_erase_add Finset.univ (fun _ : Fin n => r ^ 2) (Finset.mem_univ i)
    have he : (∑ j, if i = j then 0 else r ^ 2) = ∑ j ∈ Finset.univ.erase i, r ^ 2 := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
      have hz := Finset.sum_ite (s := (Finset.univ : Finset (Fin n))) (p := fun j => i = j)
        (fun _ => (0 : ℝ)) (fun _ => r ^ 2)
      simp only [Finset.sum_const_zero, zero_add] at hz
      rw [hz]
      have hset : Finset.filter (fun j => ¬i = j) Finset.univ = Finset.univ.erase i := by
        ext j; simp [ne_comm]
      rw [hset, Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    rw [he]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h ⊢
    linarith
  calc
    offEnergy A ≤ ∑ i, ∑ j, if i = j then 0 else r ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hij
      · rfl
      · exact (sq_abs (A i j)) ▸ (sq_le_sq₀ (abs_nonneg _) hr).mpr (hA i j hij)
    _ = _ := by
      simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Pairwise rounded energy bounds imply the full off-diagonal energy step.
The diagonal updates do not occur in this theorem: only pivot annihilation,
the affected pairs and preservation of the untouched block are needed. -/
theorem offEnergy_step {n : Nat} (A B : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n)
    (ε η : ℝ) (hpq : p ≠ q) (hε : 0 ≤ ε)
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i)
    (hpivot : B p q = 0)
    (hpair
      : ∀ k ∈ outside p q,
          |(B k p ^ 2 + B k q ^ 2) - (A k p ^ 2 + A k q ^ 2)| ≤ ε * (A k p ^ 2 + A k q ^ 2 + η ^ 2))
    (hrest : ∀ k ∈ outside p q, ∀ l ∈ outside p q, B k l = A k l)
    : offEnergy B ≤ (1 + ε) * offEnergy A - 2 * A p q ^ 2 + 2 * ε * n * η ^ 2 := by
  let s := outside p q
  let pairsA := ∑ k ∈ s, (A k p ^ 2 + A k q ^ 2)
  let pairsB := ∑ k ∈ s, (B k p ^ 2 + B k q ^ 2)
  let rest := ∑ k ∈ s, ∑ l ∈ s, if k = l then (0 : ℝ) else A k l ^ 2
  have hrest0 : 0 ≤ rest := by
    apply Finset.sum_nonneg
    intro k _
    apply Finset.sum_nonneg
    intro l _; split_ifs <;> positivity
  have hrest' : (∑ k ∈ s, ∑ l ∈ s, if k = l then (0 : ℝ) else B k l ^ 2) = rest := by
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    rw [hrest k hk l hl]
  have hpair' : pairsB ≤ (1 + ε) * pairsA + ε * n * η ^ 2 := by
    have hsum := Finset.sum_le_sum (s := s) (f := fun k => B k p ^ 2 + B k q ^ 2)
      (g := fun k => (1 + ε) * (A k p ^ 2 + A k q ^ 2) + ε * η ^ 2) (by
        intro k hk
        have hk' := (abs_le.mp (hpair k hk)).2
        nlinarith)
    have hcard : (s.card : ℝ) ≤ n := by
      exact_mod_cast (show s.card ≤ n by simpa using Finset.card_le_card (Finset.subset_univ s))
    dsimp only [pairsA, pairsB]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hsum ⊢
    have hc := mul_le_mul_of_nonneg_right hcard (mul_nonneg hε (sq_nonneg η))
    nlinarith
  have hEA := offEnergy_split A p q hpq hA
  have hEB := offEnergy_split B p q hpq hB
  change offEnergy A = 2 * A p q ^ 2 + 2 * pairsA + rest at hEA
  change offEnergy B = 2 * B p q ^ 2 + 2 * pairsB + _ at hEB
  rw [hpivot, hrest'] at hEB
  nlinarith [mul_nonneg hε hrest0, mul_nonneg hε (sq_nonneg (A p q))]

/-- A two-column update with pairwise norm error controls the full matrix
energy, without a symmetry premise. This applies to the eigenvector array. -/
theorem columnPair_energy_step {n : Nat} (A B : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n)
    (ε η : ℝ) (hpq : p ≠ q) (hε : 0 ≤ ε)
    (hpair
      : ∀ i,
          |(B i p ^ 2 + B i q ^ 2) - (A i p ^ 2 + A i q ^ 2)| ≤ ε * (A i p ^ 2 + A i q ^ 2 + η ^ 2))
    (hrest : ∀ i j, j ≠ p → j ≠ q → B i j = A i j)
    : energy B ≤ (1 + ε) * energy A + ε * n * η ^ 2 := by
  have hrow (i : Fin n) : ∑ j, B i j ^ 2 ≤ (1 + ε) * (∑ j, A i j ^ 2) + ε * η ^ 2 := by
    have hA := sum_split_pair (fun j => A i j ^ 2) p q hpq
    have hB := sum_split_pair (fun j => B i j ^ 2) p q hpq
    have hR : (∑ j ∈ outside p q, B i j ^ 2) = ∑ j ∈ outside p q, A i j ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := (mem_outside p q j).mp hj
      rw [hrest i j hj'.1 hj'.2]
    rw [hR] at hB
    have hR0 : 0 ≤ ∑ j ∈ outside p q, A i j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hpair' := (abs_le.mp (hpair i)).2
    nlinarith [mul_nonneg hε hR0]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hs
  dsimp only [energy]
  nlinarith

/-- A diagonal transfer bound and pairwise errors control the complete
symmetric matrix's energy, including the zeroed pivot block. -/
theorem energy_step {n : Nat} (A B : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n)
    (δ ε η : ℝ) (hpq : p ≠ q) (hε : 0 ≤ ε)
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i)
    (hpivot : B p q = 0)
    (hdiag : |B p p ^ 2 + B q q ^ 2 - (A p p ^ 2 + A q q ^ 2 + 2 * A p q ^ 2)| ≤ δ)
    (hpair
      : ∀ k ∈ outside p q,
          |(B k p ^ 2 + B k q ^ 2) - (A k p ^ 2 + A k q ^ 2)| ≤ ε * (A k p ^ 2 + A k q ^ 2 + η ^ 2))
    (hrest : ∀ k ∈ outside p q, ∀ l ∈ outside p q, B k l = A k l)
    : energy B ≤ (1 + ε) * energy A + δ + 2 * ε * n * η ^ 2 := by
  let s := outside p q
  let pairsA := ∑ k ∈ s, (A k p ^ 2 + A k q ^ 2)
  let pairsB := ∑ k ∈ s, (B k p ^ 2 + B k q ^ 2)
  let rest := ∑ k ∈ s, ∑ l ∈ s, A k l ^ 2
  have hrest0 : 0 ≤ rest := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _
  have hrest' : (∑ k ∈ s, ∑ l ∈ s, B k l ^ 2) = rest := by
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    rw [hrest k hk l hl]
  have hpair' : pairsB ≤ (1 + ε) * pairsA + ε * n * η ^ 2 := by
    have hsum := Finset.sum_le_sum (s := s) (f := fun k => B k p ^ 2 + B k q ^ 2)
      (g := fun k => (1 + ε) * (A k p ^ 2 + A k q ^ 2) + ε * η ^ 2) (by
        intro k hk
        have hk' := (abs_le.mp (hpair k hk)).2
        nlinarith)
    have hcard : (s.card : ℝ) ≤ n := by
      exact_mod_cast (show s.card ≤ n by simpa using Finset.card_le_card (Finset.subset_univ s))
    dsimp only [pairsA, pairsB]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hsum ⊢
    have hc := mul_le_mul_of_nonneg_right hcard (mul_nonneg hε (sq_nonneg η))
    nlinarith
  have hEA := energy_split A p q hpq hA
  have hEB := energy_split B p q hpq hB
  change energy A = A p p ^ 2 + 2 * A p q ^ 2 + A q q ^ 2 + 2 * pairsA + rest at hEA
  change energy B = B p p ^ 2 + 2 * B p q ^ 2 + B q q ^ 2 + 2 * pairsB + _ at hEB
  rw [hpivot, hrest'] at hEB
  have hd := (abs_le.mp hdiag).2
  nlinarith [mul_nonneg hε hrest0, mul_nonneg hε (sq_nonneg (A p p)),
    mul_nonneg hε (sq_nonneg (A p q)), mul_nonneg hε (sq_nonneg (A q q))]

end Flare.Analysis.JacobiEnergy
