module

public import Flare.Analysis.JacobiRotation
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.PosDef

/-! Accumulation of local spectral errors in the Euclidean operator norm.
Mathlib's C⋆-algebra norm identities provide exact invariance under orthogonal
multiplication; error bounds therefore add across rotations without an
artificial dimension factor at every iteration. -/

@[expose] public section

namespace Flare.Analysis.SpectralPerturbation
open Matrix
open scoped Matrix.Norms.L2Operator

/-- A uniform entrywise error gives an operator-norm error with one factor of
the dimension. This bridge is applied to local errors, not to each accumulated
similarity transformation. -/
theorem norm_le_entries {n : Nat} (E : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hE : ∀ i j, |E i j| ≤ ε)
    : ‖E‖ ≤ n * ε := by
  rw [cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hrow (i : Fin n) : ∑ j, (E i j)^2 ≤ n * ε^2 := by
    calc
      _ ≤ ∑ _j : Fin n, ε ^ 2 :=
        Finset.sum_le_sum
          fun j _ => by
            have h := (sq_le_sq₀ (abs_nonneg _) hε).mpr (hE i j)
            simpa only [sq_abs] using h
      _ = _ := by simp
  have hrow' (i : Fin n) : (∑ j, E i j * x.ofLp j)^2 ≤
      (n * ε^2) * ∑ j, (x.ofLp j)^2 := by
    exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (E i) x.ofLp).trans
      (mul_le_mul_of_nonneg_right (hrow i) (Finset.sum_nonneg fun j _ => sq_nonneg _))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow' i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  simp only [mul_pow, EuclideanSpace.norm_sq_eq, ofLp_toEuclideanCLM, mulVec, dotProduct,
    Real.norm_eq_abs, sq_abs]
  convert hsum using 1
  ring

/-- Every entry is bounded by the Euclidean operator norm. -/
theorem entry_le_norm {m n : Nat} (E : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n)
    : |E i j| ≤ ‖E‖ := by
  let x : EuclideanSpace ℝ (Fin n) := PiLp.single 2 j 1
  let y : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (E.mulVec x.ofLp)
  have hcoord := PiLp.norm_apply_le y i
  have hop : ‖y‖ ≤ ‖E‖ * ‖x‖ := l2_opNorm_mulVec E x
  have hx : ‖x‖ = 1 := by simp [x]
  rw [hx, mul_one] at hop
  have he : y.ofLp i = E i j := by simp [y, x, mulVec, dotProduct]
  rw [he, Real.norm_eq_abs] at hcoord
  exact hcoord.trans hop

/-- Bridge real orthogonality to Mathlib's unitary matrix norm theory. -/
theorem orthogonal_mem_unitary {n : Nat} (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : J.transpose * J = 1 ∧ J * J.transpose = 1)
    : J ∈ unitary (Matrix (Fin n) (Fin n) ℝ) := by
  simpa only [Unitary.mem_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    using hJ

/-- Transpose preserves the Euclidean operator norm on real matrices. -/
theorem norm_transpose {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) : ‖A.transpose‖ = ‖A‖ := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using l2_opNorm_conjTranspose A

/-- Orthogonal similarity preserves the norm of an error matrix exactly. -/
theorem similarity_isometry {n : Nat} (J E : Matrix (Fin n) (Fin n) ℝ)
    (hJ : J ∈ unitary (Matrix (Fin n) (Fin n) ℝ))
    : ‖J.transpose * E * J‖ = ‖E‖ := by
  rw [CStarRing.norm_mul_mem_unitary _ hJ]
  simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    using CStarRing.norm_mem_unitary_mul E (Unitary.star_mem hJ)

/-- Product of the exact reference rotations, in native execution order. -/
noncomputable def product {n : Nat} (J : Nat → Matrix (Fin n) (Fin n) ℝ)
    : Nat → Matrix (Fin n) (Fin n) ℝ
  | 0 => 1
  | k + 1 => product J k * J k

/-- A finite product of reference rotations is itself exactly orthogonal. -/
theorem product_unitary {n : Nat} (J : Nat → Matrix (Fin n) (Fin n) ℝ) (k : Nat)
    (hJ : ∀ i, i < k → J i ∈ unitary (Matrix (Fin n) (Fin n) ℝ))
    : product J k ∈ unitary (Matrix (Fin n) (Fin n) ℝ) := by
  induction k with
  | zero => exact (unitary _).one_mem
  | succ k ih => exact (unitary _).mul_mem (ih fun i hi => hJ i (by omega)) (hJ k (by omega))

/-- Local similarity errors add through the full rotation sequence. -/
theorem accumulate_similarity {n : Nat} (A J : Nat → Matrix (Fin n) (Fin n) ℝ)
    (δ : Nat → ℝ) (k : Nat)
    (hJ : ∀ i, i < k → J i ∈ unitary (Matrix (Fin n) (Fin n) ℝ))
    (hstep : ∀ i, i < k → ‖A (i + 1) - (J i).transpose * A i * J i‖ ≤ δ i)
    : ‖A k - (product J k).transpose * A 0 * product J k‖ ≤ ∑ i ∈ Finset.range k, δ i := by
  induction k with
  | zero => simp [product]
  | succ k ih =>
      have hi := ih (fun i hi => hJ i (by omega)) (fun i hi => hstep i (by omega))
      have he : A (k + 1) - (product J (k + 1)).transpose * A 0 * product J (k + 1) =
          (A (k + 1) - (J k).transpose * A k * J k) +
          (J k).transpose * (A k - (product J k).transpose * A 0 * product J k) * J k := by
        simp only [product, transpose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
        abel
      rw [he]
      have h := (norm_add_le _ _).trans (add_le_add (hstep k (by omega))
        ((similarity_isometry (J k) _ (hJ k (by omega))).le.trans hi))
      simpa only [Finset.sum_range_succ, add_comm] using h

/-- Rounded eigenvector updates accumulate distance from the same exact
orthogonal product. The initial eigenvector matrix is identity. -/
theorem accumulate_vectors {n : Nat} (V J : Nat → Matrix (Fin n) (Fin n) ℝ)
    (δ : Nat → ℝ) (k : Nat) (hV : V 0 = 1)
    (hJ : ∀ i, i < k → J i ∈ unitary (Matrix (Fin n) (Fin n) ℝ))
    (hstep : ∀ i, i < k → ‖V (i + 1) - V i * J i‖ ≤ δ i)
    : ‖V k - product J k‖ ≤ ∑ i ∈ Finset.range k, δ i := by
  induction k with
  | zero => simp [product, hV]
  | succ k ih =>
      have hi := ih (fun i hi => hJ i (by omega)) (fun i hi => hstep i (by omega))
      have he : V (k + 1) - product J (k + 1) =
          (V (k + 1) - V k * J k) + (V k - product J k) * J k := by
        simp only [product, Matrix.sub_mul]
        abel
      rw [he]
      have h := (norm_add_le _ _).trans (add_le_add (hstep k (by omega))
        ((CStarRing.norm_mul_mem_unitary _ (hJ k (by omega))).le.trans hi))
      simpa only [Finset.sum_range_succ, add_comm] using h

/-- Proximity to an exactly orthogonal matrix gives an explicit orthogonality
defect for the rounded eigenvectors. No exact native orthogonality is assumed. -/
theorem orthogonality_error {n : Nat} (V W : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hW : W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)) (hε : ‖V - W‖ ≤ ε)
    : ‖V.transpose * V - 1‖ ≤ ε ^ 2 + 2 * ε := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hWW : W.transpose * W = 1 := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hW.1
  have hWT : W.transpose ∈ unitary (Matrix (Fin n) (Fin n) ℝ) := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using Unitary.star_mem hW
  have he : V.transpose * V - 1 =
      (V - W).transpose * (V - W) + (V - W).transpose * W + W.transpose * (V - W) := by
    simp only [transpose_sub, Matrix.mul_sub, Matrix.sub_mul, hWW]
    abel
  have hsq : ‖(V - W).transpose * (V - W)‖ ≤ ε^2 := by
    apply (norm_mul_le _ _).trans
    rw [norm_transpose, pow_two]
    exact mul_le_mul hε hε (norm_nonneg _) hε0
  have hright : ‖(V - W).transpose * W‖ ≤ ε := by
    rw [CStarRing.norm_mul_mem_unitary _ hW, norm_transpose]
    exact hε
  have hleft : ‖W.transpose * (V - W)‖ ≤ ε := by
    rw [CStarRing.norm_mem_unitary_mul _ hWT]
    exact hε
  rw [he]
  exact ((norm_add_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (add_le_add hsq hright)) hleft)).trans_eq
    (by ring)

/-- Similarity error, eigenvector error and the remaining off-diagonal matrix
give an enclosure of the eigen-equation residual. D may be any chosen diagonal
approximation; this result does not assume that native eigenvalues are exact. -/
theorem eigen_residual {n : Nat} (A T D V W : Matrix (Fin n) (Fin n) ℝ)
    (εA εV εD : ℝ) (hW : W ∈ unitary (Matrix (Fin n) (Fin n) ℝ))
    (hA : ‖T - W.transpose * A * W‖ ≤ εA)
    (hV : ‖V - W‖ ≤ εV) (hD : ‖T - D‖ ≤ εD)
    : ‖A * V - V * D‖ ≤ (‖A‖ + ‖D‖) * εV + εA + εD := by
  have hWW : W * W.transpose = 1 := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hW.2
  have hmid : ‖A * W - W * D‖ ≤ εA + εD := by
    have he : A * W - W * D = W * ((W.transpose * A * W - T) + (T - D)) := by
      simp only [Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc, hWW, Matrix.one_mul]
      abel
    rw [he, CStarRing.norm_mem_unitary_mul _ hW]
    exact (norm_add_le _ _).trans (add_le_add (by rwa [norm_sub_rev]) hD)
  have he : A * V - V * D = A * (V - W) + (A * W - W * D) + (W - V) * D := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hl : ‖A * (V - W)‖ ≤ ‖A‖ * εV :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hV (norm_nonneg _))
  have hr : ‖(W - V) * D‖ ≤ εV * ‖D‖ := by
    apply (norm_mul_le _ _).trans
    rw [norm_sub_rev]
    exact mul_le_mul_of_nonneg_right hV (norm_nonneg _)
  rw [he]
  exact ((norm_add_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (add_le_add hl hmid)) hr)).trans_eq
    (by ring)

/-- Spectral reconstruction using rounded vectors differs from the exactly
orthogonal reconstruction by a quadratic frame-error bound. -/
theorem reconstruction_frame_error {n : Nat} (V W R : Matrix (Fin n) (Fin n) ℝ)
    (δ : ℝ) (hW : W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)) (hδ : ‖V - W‖ ≤ δ)
    : ‖V * R * V.transpose - W * R * W.transpose‖ ≤ ‖R‖ * (δ ^ 2 + 2 * δ) := by
  have hδ0 := (norm_nonneg (V - W)).trans hδ
  have hWT : W.transpose ∈ unitary (Matrix (Fin n) (Fin n) ℝ) := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using Unitary.star_mem hW
  have he : V * R * V.transpose - W * R * W.transpose =
      (V - W) * R * (V - W).transpose + (V - W) * R * W.transpose +
      W * R * (V - W).transpose := by
    simp only [transpose_sub, Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hleft : ‖(V - W) * R‖ ≤ δ * ‖R‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hδ (norm_nonneg _))
  have hquad : ‖(V - W) * R * (V - W).transpose‖ ≤ δ * ‖R‖ * δ := by
    apply (norm_mul_le _ _).trans
    rw [norm_transpose]
    exact mul_le_mul hleft hδ (norm_nonneg _) (by positivity)
  have hl : ‖(V - W) * R * W.transpose‖ ≤ δ * ‖R‖ := by
    rw [CStarRing.norm_mul_mem_unitary _ hWT]
    exact hleft
  have hr : ‖W * R * (V - W).transpose‖ ≤ ‖R‖ * δ := by
    rw [Matrix.mul_assoc, CStarRing.norm_mem_unitary_mul _ hW]
    apply (norm_mul_le _ _).trans
    rw [norm_transpose]
    exact mul_le_mul_of_nonneg_left hδ (norm_nonneg _)
  rw [he]
  exact ((norm_add_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (add_le_add hquad hl)) hr)).trans_eq
    (by ring)

/-- Right multiplication by an orthogonal matrix preserves the rectangular
operator norm, including empty matrix dimensions. -/
theorem right_unitary_isometry {m n : Nat} (F : Matrix (Fin m) (Fin n) ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : W ∈ unitary (Matrix (Fin n) (Fin n) ℝ))
    : ‖F * W‖ = ‖F‖ := by
  by_cases hn : n = 0
  · subst n
    rw [show F = 0 from Subsingleton.elim _ _, Matrix.zero_mul]
  have : NeZero n := ⟨hn⟩
  have hWt : W.transpose ∈ unitary (Matrix (Fin n) (Fin n) ℝ) := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using Unitary.star_mem hW
  have hWW : W * W.transpose = 1 := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hW.2
  have hback : F * W * W.transpose = F := by rw [Matrix.mul_assoc, hWW, Matrix.mul_one]
  apply le_antisymm
  · simpa only [CStarRing.norm_of_mem_unitary hW, mul_one] using l2_opNorm_mul F W
  · have hh := l2_opNorm_mul (F * W) W.transpose
    simpa only [hback, CStarRing.norm_of_mem_unitary hWt, mul_one] using hh

/-- Propagating vector-rounding through a covariance factor uses `F Z` in the
linear terms. Only the quadratic term pays the full squared norm of `F`.
Here `Z = W R Wᵀ`, with an exactly orthogonal reference and symmetric `R`. -/
theorem projected_frame_error {m n : Nat} (F : Matrix (Fin m) (Fin n) ℝ)
    (V W R : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ)
    (hW : W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)) (hR : R.transpose = R)
    (hδ : ‖V - W‖ ≤ δ)
    : ‖F * (V * R * V.transpose - W * R * W.transpose) * F.transpose‖
      ≤ ‖F‖ ^ 2 * ‖R‖ * δ ^ 2 + 2 * ‖F‖ * ‖F * (W * R * W.transpose)‖ * δ := by
  have hδ0 := (norm_nonneg _).trans hδ
  let E := F * (V - W)
  let G := F * W
  let Z := W * R * W.transpose
  have hE : ‖E‖ ≤ ‖F‖ * δ := (l2_opNorm_mul _ _).trans
    (mul_le_mul_of_nonneg_left hδ (norm_nonneg _))
  have hWW : W.transpose * W = 1 := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hW.1
  have hback : (F * Z) * W = G * R := by
    dsimp [Z, G]
    simp only [Matrix.mul_assoc, hWW, Matrix.mul_one]
  have hGR : ‖G * R‖ = ‖F * Z‖ := by
    rw [← hback, right_unitary_isometry _ W hW]
  have htranspose : (G * R).transpose = R * G.transpose := by rw [transpose_mul, hR]
  have hid : F * (V * R * V.transpose - W * R * W.transpose) * F.transpose =
      E * R * E.transpose + E * R * G.transpose + G * R * E.transpose := by
    simp only [E, G, transpose_mul, transpose_sub, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc]
    abel
  have hquad : ‖E * R * E.transpose‖ ≤ (‖F‖ * δ) * ‖R‖ * (‖F‖ * δ) := by
    apply (l2_opNorm_mul _ _).trans
    rw [norm_transpose]
    exact mul_le_mul ((l2_opNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_right hE (norm_nonneg _))) hE (norm_nonneg _) (by positivity)
  have hl : ‖E * R * G.transpose‖ ≤ (‖F‖ * δ) * ‖F * Z‖ := by
    rw [Matrix.mul_assoc, ← htranspose]
    apply (l2_opNorm_mul _ _).trans
    rw [norm_transpose, hGR]
    exact mul_le_mul_of_nonneg_right hE (norm_nonneg _)
  have hr : ‖G * R * E.transpose‖ ≤ ‖F * Z‖ * (‖F‖ * δ) := by
    apply (l2_opNorm_mul _ _).trans
    rw [norm_transpose, hGR]
    exact mul_le_mul_of_nonneg_left hE (norm_nonneg _)
  rw [hid]
  exact ((norm_add_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (add_le_add hquad hl)) hr)).trans_eq
    (by ring)

/-- PSD order is monotone for the real Euclidean operator norm. The argument
uses Mathlib's exact spectral basis and works without complexifying matrices. -/
theorem norm_le_of_psd_order {n : Nat} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hAB : (B - A).PosSemidef)
    : ‖A‖ ≤ ‖B‖ := by
  let W : Matrix (Fin n) (Fin n) ℝ := hA.isHermitian.eigenvectorUnitary
  have hW : W ∈ unitary (Matrix (Fin n) (Fin n) ℝ) := hA.isHermitian.eigenvectorUnitary.property
  have hd : W.transpose * A * W = diagonal hA.isHermitian.eigenvalues := by
    simpa only [W, Unitary.conjStarAlgAut_star_apply, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq]
      using hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hnorm : ‖hA.isHermitian.eigenvalues‖ = ‖A‖ := by
    rw [← l2_opNorm_diagonal, ← hd, similarity_isometry W A hW]
  rw [← hnorm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg B)).mpr
  intro i
  have hh : (W.transpose * B * W - diagonal hA.isHermitian.eigenvalues).PosSemidef := by
    have ht := hAB.mul_mul_conjTranspose_same W.transpose
    simpa only [conjTranspose_eq_transpose_of_trivial, transpose_transpose,
      Matrix.mul_sub, Matrix.sub_mul, hd] using ht
  have hi := hh.diag_nonneg (i := i)
  simp only [Matrix.sub_apply, diagonal_apply_eq] at hi
  rw [Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i)]
  exact (show hA.isHermitian.eigenvalues i ≤ (W.transpose * B * W) i i by linarith only [hi]).trans
    ((le_abs_self _).trans ((entry_le_norm _ i i).trans_eq (similarity_isometry W B hW)))

/-- A PSD Gram domination bounds the norm of a rectangular matrix directly,
without replacing it by a dimension-dependent entrywise estimate. -/
theorem gram_norm_bound {m n : Nat} (F : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (h : (B - F.transpose * F).PosSemidef)
    : ‖F‖ ^ 2 ≤ ‖B‖ := by
  have hpsd : (F.transpose * F).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self F
  have hn := norm_le_of_psd_order _ B hpsd h
  have he : ‖F.transpose * F‖ = ‖F‖ * ‖F‖ := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using l2_opNorm_conjTranspose_mul_self F
  simpa only [he, pow_two] using hn

end Flare.Analysis.SpectralPerturbation
