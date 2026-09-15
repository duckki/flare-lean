import Flare.Analysis.SpectralPerturbation
import Flare.Analysis.JacobiEnergy

/-! Euclidean operator-norm bounds for the sparse errors of a Jacobi rotation.
These proof-side estimates preserve the affected-column structure instead of
charging a dense entrywise bound for every matrix entry. -/

namespace Flare.Analysis.JacobiNorms
open Matrix JacobiEnergy SpectralPerturbation
open scoped Matrix.Norms.L2Operator

/-- Squared Frobenius energy bounds the Euclidean operator norm. -/
theorem norm_le_of_energy_le {n : Nat} (E : Matrix (Fin n) (Fin n) ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hE : energy E ≤ C^2)
    : ‖E‖ ≤ C := by
  rw [cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (E i) x.ofLp)
  rw [← Finset.sum_mul] at hsum
  have h := hsum.trans (mul_le_mul_of_nonneg_right hE
    (Finset.sum_nonneg fun j _ => sq_nonneg (x.ofLp j)))
  simpa only [mul_pow, EuclideanSpace.norm_sq_eq, ofLp_toEuclideanCLM, mulVec, dotProduct,
    Real.norm_eq_abs, sq_abs] using h

/-- A column's squared Euclidean norm is bounded by the squared matrix norm. -/
theorem column_energy_le_norm {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n)
    : ∑ i, (A i j)^2 ≤ ‖A‖^2 := by
  let x : EuclideanSpace ℝ (Fin n) := PiLp.single 2 j 1
  have hop := l2_opNorm_mulVec A x
  have hx : ‖x‖ = 1 := by simp [x]
  rw [hx, mul_one] at hop
  have h := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hop
  simpa [EuclideanSpace.norm_sq_eq, x, mulVec, dotProduct] using h

/-- The absolute mass of a matrix-product entry is bounded by the product
of operator norms. Cauchy--Schwarz accounts for the whole row and column. -/
theorem product_mass_le_norm {rows inner columns : Nat}
    (A : Matrix (Fin rows) (Fin inner) ℝ) (B : Matrix (Fin inner) (Fin columns) ℝ)
    (i : Fin rows) (j : Fin columns)
    : (∑ k, |A i k * B k j|) ≤ ‖A‖ * ‖B‖ := by
  have ha := column_energy_le_norm A.transpose i
  rw [norm_transpose] at ha
  have hb := column_energy_le_norm B j
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => |A i k|) (fun k => |B k j|)
  simp only [sq_abs, ← abs_mul] at hs
  apply (sq_le_sq₀ (Finset.sum_nonneg fun k _ => abs_nonneg _) (by positivity)).mp
  rw [mul_pow]
  exact hs.trans (mul_le_mul ha hb (Finset.sum_nonneg fun k _ => sq_nonneg _) (sq_nonneg _))

/-- Frobenius energy costs at most one dimension factor relative to the
operator norm, independently of the chosen coordinate basis. -/
theorem energy_le_norm {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) : energy A ≤ n * ‖A‖^2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => column_energy_le_norm A j)
  rw [energy, Finset.sum_comm]
  simpa only [Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using h

/-- The magnitudes of two input columns, with an underflow term in every row,
have a Euclidean bound without a dimension factor on the matrix norm. -/
theorem pair_magnitude_energy {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ)
    (p q : Fin n) (η : ℝ) (hη : 0 ≤ η)
    : ∑ i, (|A i p| + |A i q| + η)^2 ≤ (2 * ‖A‖ + n * η)^2 := by
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => |A i p|)
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => |A i q|)
  let z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => η)
  have hx : ‖x‖ ≤ ‖A‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa [x, EuclideanSpace.norm_sq_eq] using column_energy_le_norm A p
  have hy : ‖y‖ ≤ ‖A‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa [y, EuclideanSpace.norm_sq_eq] using column_energy_le_norm A q
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by have := p.isLt; omega)
  have hz : ‖z‖ ≤ n * η := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    simp only [z, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs,
      sq_abs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith only [hn] : (n : ℝ) ≤ (n : ℝ)^2) (sq_nonneg η)
  have h := (norm_add_le (x + y) z).trans (add_le_add ((norm_add_le x y).trans (add_le_add hx hy))
    hz)
  have h' : ‖x + y + z‖ ≤ 2 * ‖A‖ + n * η := h.trans_eq (by ring)
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr h'
  simpa [EuclideanSpace.norm_sq_eq, x, y, z] using hs

/-- A two-column error has a Frobenius bound with no leading dimension
factor. This applies to eigenvector updates without symmetry assumptions. -/
theorem two_column_error {n : Nat} (A E : Matrix (Fin n) (Fin n) ℝ)
    (p q : Fin n) (hpq : p ≠ q) (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hpair : ∀ i, |E i p| ≤ ε * (|A i p| + |A i q| + η) ∧ |E i q| ≤ ε * (|A i p| + |A i q| + η))
    (hzero : ∀ i j, j ≠ p → j ≠ q → E i j = 0)
    : ‖E‖ ≤ (3 / 2 : ℝ) * ε * (2 * ‖A‖ + n * η) := by
  apply norm_le_of_energy_le E _ (by positivity)
  have hrow (i : Fin n) : ∑ j, (E i j)^2 = (E i p)^2 + (E i q)^2 := by
    rw [← Finset.sum_subset (by intro j _; exact Finset.mem_univ j : ({p, q} : Finset (Fin n)) ⊆
      Finset.univ)]
    · simp [hpq]
    · intro j _ hj
      have hj' : j ≠ p ∧ j ≠ q := by simpa using hj
      rw [hzero i j hj'.1 hj'.2]
      norm_num
  have henergy : energy E ≤ 2 * ε^2 * ∑ i, (|A i p| + |A i q| + η)^2 := by
    rw [energy]
    simp only [hrow]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h1 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hpair i).1
    have h2 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hpair i).2
    simp only [sq_abs, mul_pow] at h1 h2
    nlinarith only [h1, h2]
  have hs := mul_le_mul_of_nonneg_left (pair_magnitude_energy A p q η hη)
    (by positivity : 0 ≤ 2 * ε^2)
  apply (henergy.trans hs).trans
  nlinarith only [sq_nonneg (ε * (2 * ‖A‖ + n * η))]

/-- A symmetric error supported on the affected row pairs, with a zero pivot
block, has a dimension-free leading operator-norm bound. -/
theorem symmetric_pair_error {n : Nat} (A E : Matrix (Fin n) (Fin n) ℝ)
    (p q : Fin n) (hpq : p ≠ q) (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hsym : ∀ i j, E i j = E j i)
    (hpp : E p p = 0) (hpq0 : E p q = 0) (hqq : E q q = 0)
    (hpair
      : ∀ k,
          k ≠ p
          → k ≠ q
          → |E k p| ≤ ε * (|A k p| + |A k q| + η) ∧ |E k q| ≤ ε * (|A k p| + |A k q| + η))
    (hzero : ∀ i j, i ≠ p → i ≠ q → j ≠ p → j ≠ q → E i j = 0)
    : ‖E‖ ≤ 2 * ε * (2 * ‖A‖ + n * η) := by
  apply norm_le_of_energy_le E _ (by positivity)
  rw [energy_split E p q hpq hsym, hpp, hpq0, hqq]
  have hout : (∑ i ∈ outside p q, ∑ j ∈ outside p q, E i j ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hi' := (mem_outside p q i).mp hi
    have hj' := (mem_outside p q j).mp hj
    rw [hzero i j hi'.1 hi'.2 hj'.1 hj'.2, zero_pow (by decide)]
  rw [hout]
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, add_zero]
  have hpairSq : ∑ k ∈ outside p q, (E k p ^ 2 + E k q ^ 2) ≤
      2 * ε^2 * ∑ k, (|A k p| + |A k q| + η)^2 := by
    calc
      _ ≤ ∑ k ∈ outside p q, 2 * ε^2 * (|A k p| + |A k q| + η)^2 := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := (mem_outside p q k).mp hk
        have he := hpair k hk'.1 hk'.2
        have h1 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr he.1
        have h2 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr he.2
        rw [sq_abs] at h1 h2
        nlinarith only [h1, h2]
      _ ≤ ∑ k, 2 * ε^2 * (|A k p| + |A k q| + η)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
      _ = _ := by rw [Finset.mul_sum]
  have he := mul_le_mul_of_nonneg_left hpairSq (by norm_num : (0 : ℝ) ≤ 2)
  apply he.trans
  have hs := mul_le_mul_of_nonneg_left (pair_magnitude_energy A p q η hη)
    (show 0 ≤ 4 * ε^2 by positivity)
  nlinarith only [hs]

/-- A symmetric error confined to the two-by-two pivot block costs at most
twice its entry bound, regardless of the surrounding matrix dimension. -/
theorem pivot_block_error {n : Nat} (E : Matrix (Fin n) (Fin n) ℝ)
    (p q : Fin n) (hpq : p ≠ q) (r : ℝ) (hr : 0 ≤ r)
    (hsym : ∀ i j, E i j = E j i)
    (hpp : |E p p| ≤ r) (hpq0 : |E p q| ≤ r) (hqq : |E q q| ≤ r)
    (hzero : ∀ i j, (i ≠ p ∧ i ≠ q) ∨ (j ≠ p ∧ j ≠ q) → E i j = 0)
    : ‖E‖ ≤ 2 * r := by
  apply norm_le_of_energy_le E _ (by positivity)
  rw [energy_split E p q hpq hsym]
  have hpair : (∑ k ∈ outside p q, (E k p ^ 2 + E k q ^ 2)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := (mem_outside p q k).mp hk
    rw [hzero k p (Or.inl hk'), hzero k q (Or.inl hk')]
    norm_num
  have hout : (∑ i ∈ outside p q, ∑ j ∈ outside p q, E i j ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j _
    rw [hzero i j (Or.inl ((mem_outside p q i).mp hi)), zero_pow (by decide)]
  rw [hpair, hout]
  have h1 := (sq_le_sq₀ (abs_nonneg _) hr).mpr hpp
  have h2 := (sq_le_sq₀ (abs_nonneg _) hr).mpr hpq0
  have h3 := (sq_le_sq₀ (abs_nonneg _) hr).mpr hqq
  simp only [sq_abs] at h1 h2 h3
  nlinarith only [h1, h2, h3]

/-- Split a rotation error into affected row pairs, two diagonal roundings,
and a residual pivot block. The leading constants do not grow with dimension. -/
theorem rotation_error {n : Nat} (A E : Matrix (Fin n) (Fin n) ℝ)
    (p q : Fin n) (hpq : p ≠ q) (ε η δ r α β : ℝ)
    (hε : 0 ≤ ε) (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (hsym : ∀ i j, E i j = E j i)
    (hα : |α| ≤ δ) (hβ : |β| ≤ δ)
    (hpp : |E p p - α| ≤ r) (hqq : |E q q - β| ≤ r) (hpq0 : |E p q| ≤ r)
    (hpair
      : ∀ k,
          k ≠ p
          → k ≠ q
          → |E k p| ≤ ε * (|A k p| + |A k q| + η) ∧ |E k q| ≤ ε * (|A k p| + |A k q| + η))
    (hzero : ∀ i j, i ≠ p → i ≠ q → j ≠ p → j ≠ q → E i j = 0)
    : ‖E‖ ≤ 2 * ε * (2 * ‖A‖ + n * η) + δ + 2 * r := by
  let F : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    if (i = p ∨ i = q) ∧ (j = p ∨ j = q) then 0 else E i j
  let G : Matrix (Fin n) (Fin n) ℝ := diagonal (fun i => if i = p then α else if i = q then β else
    0)
  let R := E - F - G
  have hFsym : ∀ i j, F i j = F j i := by
    intro i j
    simp only [F, and_comm, hsym i j]
  have hF : ‖F‖ ≤ 2 * ε * (2 * ‖A‖ + n * η) := by
    apply symmetric_pair_error A F p q hpq ε η hε hη hFsym
      (by simp [F]) (by simp [F]) (by simp [F])
    · intro k hkp hkq
      simpa [F, hkp, hkq] using hpair k hkp hkq
    · intro i j hip hiq hjp hjq
      simpa [F, hip, hiq] using hzero i j hip hiq hjp hjq
  have hGsym : ∀ i j, G i j = G j i := by
    intro i j
    by_cases hij : i = j
    · subst j; rfl
    · simp [G, diagonal_apply_ne _ hij, diagonal_apply_ne _ (Ne.symm hij)]
  have hG : ‖G‖ ≤ δ := by
    rw [l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg hδ).mpr
    intro i
    simp only [Real.norm_eq_abs]
    split_ifs <;> first | exact hα | exact hβ | simpa using hδ
  have hR : ‖R‖ ≤ 2 * r := by
    apply pivot_block_error R p q hpq r hr
    · intro i j
      simp only [R, Matrix.sub_apply, hsym i j, hFsym i j, hGsym i j]
    · change |E p p - F p p - G p p| ≤ r
      simpa [F, G] using hpp
    · change |E p q - F p q - G p q| ≤ r
      simpa [F, G, hpq] using hpq0
    · change |E q q - F q q - G q q| ≤ r
      simpa [F, G, hpq.symm] using hqq
    · intro i j hout
      change E i j - F i j - G i j = 0
      rcases hout with ⟨hip, hiq⟩ | ⟨hjp, hjq⟩
      · by_cases hij : i = j
        · subst j; simp [F, G, hip, hiq]
        · simp [F, G, hip, hiq, diagonal_apply_ne _ hij]
      · by_cases hij : i = j
        · subst j; simp [F, G, hjp, hjq]
        · simp [F, G, hjp, hjq, diagonal_apply_ne _ hij]
  have he : E = F + G + R := by dsimp [R]; abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hF hG)) hR)

/-- A complete approximate Jacobi update has an operator-norm error controlled
by its pair-rounding scale, diagonal-rounding bound and tangent residual. -/
theorem similarity_error_norm {n : Nat} (A B : Matrix (Fin n) (Fin n) ℝ)
    (p q : Fin n) (hpq : p ≠ q) (t ε η δ : ℝ)
    (hε : 0 ≤ ε) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i)
    (hp : |B p p - (A p p - t * A p q)| ≤ δ)
    (hq : |B q q - (A q q + t * A p q)| ≤ δ)
    (hpivot : B p q = 0)
    (hpair
      : ∀ k,
          k ≠ p
          → k ≠ q
          → |B k p - ((1 / Real.sqrt (1 + t^2)) * A k p - (t / Real.sqrt (1 + t^2)) * A k q)|
              ≤ ε * (|A k p| + |A k q| + η)
            ∧ |B k q - ((t / Real.sqrt (1 + t^2)) * A k p + (1 / Real.sqrt (1 + t^2)) * A k q)|
              ≤ ε * (|A k p| + |A k q| + η))
    (hexterior : ∀ i j, i ≠ p → i ≠ q → j ≠ p → j ≠ q → B i j = A i j)
    : let c := 1 / Real.sqrt (1 + t^2)
      let J := JacobiRotation.plane p q c (t * c)
      let r := A p q * t^2 + (A q q - A p p) * t - A p q
      ‖B - J.transpose * A * J‖ ≤ 2 * ε * (2 * ‖A‖ + n * η) + δ + 2 * |r| := by
  let c := 1 / Real.sqrt (1 + t^2)
  let s := t * c
  let J := JacobiRotation.plane p q c s
  let D := J.transpose * A * J
  let r := A p q * t^2 + (A q q - A p p) * t - A p q
  have hu : c^2 + s^2 = 1 := Jacobi.rotation_unit t
  have hc : |c^2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg c)]; nlinarith [sq_nonneg s]
  have hcs : |c * s| ≤ 1 := by
    have h1 := sq_nonneg (c - s)
    have h2 := sq_nonneg (c + s)
    exact abs_le.mpr ⟨by nlinarith only [h1, hu], by nlinarith only [h2, hu]⟩
  have hct : |c^2 * t * r| ≤ |r| := by
    have he : c^2 * t = c * s := by dsimp [s]; ring
    rw [he, abs_mul]
    exact (mul_le_mul_of_nonneg_right hcs (abs_nonneg r)).trans_eq (one_mul _)
  have hcr : |c^2 * r| ≤ |r| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hc (abs_nonneg r)).trans_eq (one_mul _)
  obtain ⟨hpp, hqq, hpq', hpair', hout⟩ := JacobiRotation.similarity_entries A p q hpq c s hA
  obtain ⟨hrp, hrq, hrpq⟩ := JacobiRotation.pivot_residual (A p p) (A p q) (A q q) t
  have hDsym : ∀ i j, D i j = D j i := JacobiRotation.similarity_symmetric A J hA
  apply rotation_error A (B - D) p q hpq ε η δ |r|
    (B p p - (A p p - t * A p q)) (B q q - (A q q + t * A p q))
    hε hη hδ (abs_nonneg r) (fun i j => by simp only [Matrix.sub_apply, hB i j, hDsym i j]) hp hq
  · have he : (B - D) p p - (B p p - (A p p - t * A p q)) =
        -(D p p - (A p p - t * A p q)) := by simp only [Matrix.sub_apply]; ring
    rw [he, abs_neg]
    change |(J.transpose * A * J) p p - _| ≤ _
    rw [hpp, hrp]
    exact hct
  · have he : (B - D) q q - (B q q - (A q q + t * A p q)) =
        -(D q q - (A q q + t * A p q)) := by simp only [Matrix.sub_apply]; ring
    rw [he, abs_neg]
    change |(J.transpose * A * J) q q - _| ≤ _
    rw [hqq, hrq, abs_neg]
    exact hct
  · change |B p q - (J.transpose * A * J) p q| ≤ _
    rw [hpivot, zero_sub, abs_neg, hpq', hrpq, abs_neg]
    exact hcr
  · intro k hkp hkq
    have he := hpair' k hkp hkq
    change D k p = _ ∧ D k q = _ at he
    change |B k p - D k p| ≤ _ ∧ |B k q - D k q| ≤ _
    rw [he.1, he.2]
    simpa only [s, c, mul_one_div] using hpair k hkp hkq
  · intro i j hip hiq hjp hjq
    change B i j - (J.transpose * A * J) i j = 0
    rw [hexterior i j hip hiq hjp hjq, hout i j hip hiq hjp hjq, sub_self]

/-- Telescoping the energy recurrence bounds the total squared pivot size,
including a multiplicative roundoff allowance at each step. -/
theorem pivot_energy_sum (E b : Nat → ℝ) (ε : ℝ) (k : Nat)
    (hstep : ∀ i, i < k → E (i + 1) ≤ (1 + ε) * E i - 2 * (b i)^2)
    : 2 * (∑ i ∈ Finset.range k, (b i)^2) + E k ≤ E 0 + ε * ∑ i ∈ Finset.range k, E i := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hprev := ih (fun i hi => hstep i (by omega))
      have hnext := hstep k (by omega)
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      nlinarith only [hprev, hnext]

/-- Cauchy--Schwarz converts the energy decrease into a bound on the sum of
pivot magnitudes, which is the quantity needed for tangent-error accumulation. -/
theorem pivot_magnitude_sum (E b : Nat → ℝ) (ε M : ℝ) (k : Nat)
    (hε : 0 ≤ ε) (hend : 0 ≤ E k) (hM : ∀ i, i < k → E i ≤ M)
    (hstep : ∀ i, i < k → E (i + 1) ≤ (1 + ε) * E i - 2 * (b i)^2)
    : (∑ i ∈ Finset.range k, |b i|)^2 ≤ k * (E 0 + k * ε * M) / 2 := by
  have henergy := pivot_energy_sum E b ε k hstep
  have hsum : ∑ i ∈ Finset.range k, E i ≤ k * M := by
    simpa using Finset.sum_le_sum (s := Finset.range k) (fun i hi => hM i (Finset.mem_range.mp hi))
  have hbound := mul_le_mul_of_nonneg_left hsum hε
  have hsq : (∑ i ∈ Finset.range k, (b i)^2) ≤ (E 0 + k * ε * M) / 2 := by
    nlinarith only [henergy, hbound, hend]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range k) (fun _ => (1 : ℝ)) (fun i => |b i|)
  simp only [one_mul, one_pow, sq_abs, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    at hcs
  exact (hcs.trans (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg k))).trans_eq (by ring)

end Flare.Analysis.JacobiNorms
