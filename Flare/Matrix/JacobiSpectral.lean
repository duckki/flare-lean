import Flare.Analysis.SpectralPerturbation
import Flare.Analysis.JacobiNorms
import Flare.Matrix.JacobiIteration
import Flare.Matrix.JacobiPrecision
import Flare.Matrix.JacobiDiagonal
import Flare.Matrix.JacobiConvergence

/-! Spectral error bookkeeping for the actual Jacobi rotation. The exact
comparison uses the real normalization of the computed tangent, so its plane
matrix is orthogonal even though the native cosine and sine are rounded. -/

namespace Flare.Matrix.JacobiSpectral
open Flare.Matrix.Value Flare.Binary64.Value Flare.Matrix.Operations
open Flare.Binary64.Arithmetic Flare.Matrix.JacobiIteration
open Flare.Analysis.JacobiRotation
open Flare.Analysis.SpectralPerturbation
open Flare.Matrix.JacobiConvergence Flare.Matrix.JacobiBounds
open scoped Matrix.Norms.L2Operator

/-- Native cosine and sine approximate an exactly normalized real pair.
This strengthens the norm-defect bound with an explicit orthogonal reference. -/
theorem coefficients_reference (t : Float) (ht : t.isFinite = true) (htb : |value t| ≤ 2)
    : let c := 1.0 / (1.0 + t * t).sqrt
      let s := t * c
      let c₀ := 1 / Real.sqrt (1 + (value t) ^ 2)
      let s₀ := value t * c₀
      |value c - c₀| ≤ (2 : ℝ) ^ (-46 : Int) ∧ |value s - s₀| ≤ (2 : ℝ) ^ (-44 : Int) := by
  have h := JacobiPrecision.coefficients_precision t ht htb
  have ha : 1 ≤ Real.sqrt (1 + (value t)^2) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + (value t)^2 by positivity)
    have hs0 := Real.sqrt_nonneg (1 + (value t)^2)
    nlinarith [sq_nonneg (value t)]
  refine ⟨(h.2.2.1.trans (div_le_self (by positivity) ha)).trans (by norm_num), ?_⟩
  simpa only [mul_one_div]
    using h.2.2.2.1.trans (by norm_num : 22 * (2 : ℝ) ^ (-53 : Int) ≤ (2 : ℝ) ^ (-44 : Int))

/-- One native pair update is close to multiplication by the exact orthogonal
reference. The underflow allowance is included in M. -/
theorem pair_reference (t x y : Float) (M : ℝ)
    (ht : t.isFinite = true) (htb : |value t| ≤ 2)
    (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hM : |value x| + |value y| + (2 : ℝ) ^ (-1022 : Int) ≤ M)
    (hM' : M ≤ (2 : ℝ) ^ (500 : Int))
    : let c := 1.0 / (1.0 + t * t).sqrt
      let s := t * c
      let c₀ := 1 / Real.sqrt (1 + (value t) ^ 2)
      let s₀ := value t * c₀
      |value (c * x - s * y) - (c₀ * value x - s₀ * value y)| ≤ (2 : ℝ) ^ (-48 : Int) * M
      ∧ |value (s * x + c * y) - (s₀ * value x + c₀ * value y)| ≤ (2 : ℝ) ^ (-48 : Int) * M := by
  have h := JacobiPrecision.pair_precision t x y M ht htb hx hy hM hM'
  simpa only [mul_one_div] using h

private theorem bounded_pair (n p q : Nat) (a : Array Float) (t : Float)
    (ha : a.all Float.isFinite = true)
    (hab : ∀ i j, i < n → j < n → |value (entry n a i j)| ≤ 32)
    (hp : p < n) (hq : q < n) (ht : t.isFinite = true) (htb : |value t| ≤ 2)
    (k : Fin n)
    : let c := 1.0 / (1.0 + t * t).sqrt
      let s := t * c
      let c₀ := 1 / Real.sqrt (1 + (value t) ^ 2)
      let s₀ := value t * c₀
      |value (pairP n p q c s a k.val)
          - (c₀ * value (entry n a k.val p) - s₀ * value (entry n a k.val q))|
        ≤ (2 : ℝ) ^ (-48 : Int) * 65
      ∧ |value (pairQ n p q c s a k.val)
          - (s₀ * value (entry n a k.val p) + c₀ * value (entry n a k.val q))|
        ≤ (2 : ℝ) ^ (-48 : Int) * 65 := by
  have hη : (2 : ℝ)^(-1022 : Int) ≤ 1 :=
    (zpow_le_one_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr (by norm_num)
  exact pair_reference t (entry n a k.val p) (entry n a k.val q) 65 ht htb
    (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ ha)
    (by linarith [hab k.val p k.isLt hp, hab k.val q k.isLt hq])
    (((by norm_num : (65 : ℝ) ≤ (2 : ℝ) ^ (7 : Int))).trans
      (zpow_le_zpow_right₀ (by norm_num) (by norm_num)))

/-- A complete native rotation is an entrywise perturbation of an exact
orthogonal similarity, and its eigenvector update is a perturbation of the
same right multiplication. The tangent residual remains explicit. -/
theorem rotation_similarity (n p q : Nat) (a v : Array Float) (result : Array Float × Array Float)
    (hp : p < n) (hq : q < n) (hpq : p ≠ q)
    (ha : a.all Float.isFinite = true) (hv : v.all Float.isFinite = true)
    (hab : ∀ i j, i < n → j < n → |value (entry n a i j)| ≤ 32)
    (hvb : ∀ i j, i < n → j < n → |value (entry n v i j)| ≤ 32)
    (hsym : ∀ i j, i < n → j < n → value (entry n a i j) = value (entry n a j i))
    (hstop : (1.0e-14 : Float) < (entry n a p q).abs)
    (h : RotationResult n p q a v result)
    : let t := value (pivotT n a p q)
      let c := 1 / Real.sqrt (1 + t ^ 2)
      let J := plane (⟨p, hp⟩ : Fin n) ⟨q, hq⟩ c (t * c)
      let r :=
        value (entry n a p q) * t ^ 2
        + (value (entry n a q q) - value (entry n a p p)) * t
        - value (entry n a p q)
      J.transpose * J = 1
      ∧ J * J.transpose = 1
      ∧ (∀ i j,
          |matrix n n result.1 i j - (J.transpose * matrix n n a * J) i j|
          ≤ (2 : ℝ) ^ (-48 : Int) * 65 + 2 * |r|)
      ∧ ∀ i j, |matrix n n result.2 i j - (matrix n n v * J) i j| ≤ (2 : ℝ) ^ (-48 : Int) * 65 := by
  let P : Fin n := ⟨p, hp⟩
  let Q : Fin n := ⟨q, hq⟩
  have hPQ : P ≠ Q := by intro he; exact hpq (congrArg Fin.val he)
  have hparams := Jacobi.pivot_rotation_parameters (entry n a p p) (entry n a p q) (entry n a q q)
    (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ ha)
    (Flare.Matrix.Storage.getD_finite _ _ ha) (hab p p hp hp) (hab p q hp hq) (hab q q hq hq) hstop
  have ht : (pivotT n a p q).isFinite = true := hparams.2.1
  have htb : |value (pivotT n a p q)| ≤ 2 := hparams.2.2.2.2.1
  let t := value (pivotT n a p q)
  let c := 1 / Real.sqrt (1 + t^2)
  let s := t * c
  let J := plane P Q c s
  have hJ := plane_orthogonal P Q hPQ c s (Flare.Analysis.Jacobi.rotation_unit t)
  refine ⟨hJ.1, hJ.2, ?_, ?_⟩
  · apply similarity_error (matrix n n a) (matrix n n result.1) P Q hPQ t
      ((2 : ℝ)^(-48 : Int) * 65) htb (by positivity)
      (fun i j => hsym i.val j.val i.isLt j.isLt)
      (fun i j => h.symmetric n p q a v result hsym i.val j.val i.isLt j.isLt)
    · have hd := diagonal_updates (entry n a p p) (entry n a p q) (entry n a q q) (pivotT n a p q)
        (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ ha)
        (Flare.Matrix.Storage.getD_finite _ _ ha) ht (hab p p hp hp) (hab p q hp hq) (hab q q hq hq)
          htb
      change |value (entry n result.1 p p) - _| ≤ _
      rw [h.diagonal_p]
      exact hd.2.2.1.trans (by norm_num)
    · have hd := diagonal_updates (entry n a p p) (entry n a p q) (entry n a q q) (pivotT n a p q)
        (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ ha)
        (Flare.Matrix.Storage.getD_finite _ _ ha) ht (hab p p hp hp) (hab p q hp hq) (hab q q hq hq)
          htb
      change |value (entry n result.1 q q) - _| ≤ _
      rw [h.diagonal_q]
      exact hd.2.2.2.trans (by norm_num)
    · change value (entry n result.1 p q) = 0
      rw [h.pivot_zero.1, zero_value]
    · intro k hkp hkq
      have hkp' : k.val ≠ p := by intro he; exact hkp (Fin.ext he)
      have hkq' : k.val ≠ q := by intro he; exact hkq (Fin.ext he)
      have he := h.matrix_pair k.val k.isLt hkp' hkq'
      have hb := bounded_pair n p q a (pivotT n a p q) ha hab hp hq ht htb k
      change |value (entry n result.1 k.val p) - _| ≤ _ ∧ |value (entry n result.1 k.val q) - _| ≤ _
      rw [he.1, he.2.2.1]
      simp only [div_eq_mul_inv, one_mul] at hb ⊢
      exact hb
    · intro i j hip hiq hjp hjq
      change value (entry n result.1 i.val j.val) = value (entry n a i.val j.val)
      rw [h.matrix_unchanged i.val j.val i.isLt j.isLt
        (fun he => hip (Fin.ext he)) (fun he => hiq (Fin.ext he))
        (fun he => hjp (Fin.ext he)) (fun he => hjq (Fin.ext he))]
  · intro i j
    change |matrix n n result.2 i j - (matrix n n v * J) i j| ≤ _
    rw [mul_plane _ P Q hPQ]
    have hb := bounded_pair n p q v (pivotT n a p q) hv hvb hp hq ht htb i
    have he := h.vectors_pair i.val i.isLt
    by_cases hjp : j = P
    · subst j
      simp only [ite_true]
      change |value (entry n result.2 i.val p) - _| ≤ _
      rw [he.1]
      exact hb.1
    by_cases hjq : j = Q
    · subst j
      simp only [hjp, ite_false, ite_true]
      change |value (entry n result.2 i.val q) - _| ≤ _
      rw [he.2]
      exact hb.2
    simp only [hjp, hjq, ite_false]
    change |value (entry n result.2 i.val j.val) - value (entry n v i.val j.val)| ≤ _
    rw [h.vectors_unchanged i.val j.val i.isLt j.isLt
      (fun he => hjp (Fin.ext he)) (fun he => hjq (Fin.ext he)), sub_self, abs_zero]
    positivity

/-- One complete native rotation has a sparse operator-norm error bound.
The pivot residual retains its pivot magnitude for energy-based accumulation. -/
theorem rotation_similarity_norm (n p q : Nat) (a v : Array Float)
    (result : Array Float × Array Float) (hn : n ≤ 18) (hp : p < n) (hq : q < n) (hpq : p ≠ q)
    (ha : a.all Float.isFinite = true) (hab : ∀ i j, i < n → j < n → |value (entry n a i j)| ≤ 32)
    (hsym : ∀ i j, i < n → j < n → value (entry n a i j) = value (entry n a j i))
    (hstop : (1.0e-14 : Float) < (entry n a p q).abs) (h : RotationResult n p q a v result)
    : let t := value (pivotT n a p q)
      let c := 1 / Real.sqrt (1 + t ^ 2)
      let J := plane (⟨p, hp⟩ : Fin n) ⟨q, hq⟩ c (t * c)
      let u : ℝ := (2 : ℝ) ^ (-53 : Int)
      ‖matrix n n result.1 - J.transpose * matrix n n a * J‖
      ≤ 141 * u * ‖matrix n n a‖
        + (64 * n + 13) * u * (2 : ℝ) ^ (-1022 : Int)
        + 512 * u * |value (entry n a p q)| := by
  let P : Fin n := ⟨p, hp⟩
  let Q : Fin n := ⟨q, hq⟩
  let A := matrix n n a
  let B := matrix n n result.1
  let u : ℝ := (2 : ℝ)^(-53 : Int)
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  have hPQ : P ≠ Q := by intro he; exact hpq (congrArg Fin.val he)
  have hη : 0 ≤ η := by positivity
  have hη1 : η ≤ 1 := (zpow_le_one_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr (by norm_num)
  have hAnorm : ‖A‖ ≤ 576 := by
    have h := norm_le_entries A 32 (by norm_num) (fun i j => hab i.val j.val i.isLt j.isLt)
    have hn' : (n : ℝ) ≤ 18 := by exact_mod_cast hn
    exact h.trans (by nlinarith only [hn'])
  have hlarge : (577 : ℝ) ≤ (2 : ℝ)^(500 : Int) :=
    (by norm_num : (577 : ℝ) ≤ (2 : ℝ)^(10 : Int)).trans
      (zpow_le_zpow_right₀ (by norm_num) (by norm_num))
  have hM : ‖A‖ + η ≤ (2 : ℝ)^(500 : Int) :=
    (add_le_add hAnorm hη1).trans
      (by simpa only [show (576 : ℝ) + 1 = 577 by norm_num] using hlarge)
  have habs := Flare.Binary64.Order.abs_value (entry n a p q) (Flare.Matrix.Storage.getD_finite _ _
    ha)
  have hbp := (Flare.Binary64.Order.lt_iff (1.0e-14 : Float) _ (by decide) habs.1).mp hstop
  rw [habs.2] at hbp
  have hparams := Jacobi.pivot_parameter_bounded (entry n a p p) (entry n a p q) (entry n a q q)
    (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ ha)
    (Flare.Matrix.Storage.getD_finite _ _ ha) (hab p p hp hp) (hab p q hp hq) (hab q q hq hq)
    (Jacobi.stopping_threshold_bounds.1.trans hbp.le)
  have ht := JacobiPrecision.tangent_precision _ hparams.2.2.2.1 hparams.2.2.2.2
  have htf : (pivotT n a p q).isFinite = true := ht.1
  have htb : |value (pivotT n a p q)| ≤ 1 + 22 * u := ht.2.2
  have ht2 : |value (pivotT n a p q)| ≤ 2 := htb.trans (by norm_num [u])
  have hdiag := JacobiPrecision.diagonal_precision (entry n a p p) (entry n a p q) (entry n a q q)
    (pivotT n a p q) (‖A‖ + η)
    (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ ha)
    (Flare.Matrix.Storage.getD_finite _ _ ha) htf htb
    (add_le_add (entry_le_norm A P P) le_rfl) (add_le_add (entry_le_norm A P Q) le_rfl)
    (add_le_add (entry_le_norm A Q Q) le_rfl) hM
  have hres := JacobiDiagonal.pivot_polynomial_relative (entry n a p p) (entry n a p q) (entry n a q
    q)
    (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ ha)
    (Flare.Matrix.Storage.getD_finite _ _ ha) (hab p p hp hp) (hab p q hp hq) (hab q q hq hq) hstop
  have hs := Flare.Analysis.JacobiNorms.similarity_error_norm A B P Q hPQ (value (pivotT n a p q))
    ((2 : ℝ)^(-48 : Int)) η (13 * u * (‖A‖ + η)) (by positivity) hη (by positivity)
    (fun i j => hsym i.val j.val i.isLt j.isLt)
    (fun i j => h.symmetric n p q a v result hsym i.val j.val i.isLt j.isLt)
    (by change |value (entry n result.1 p p) - _| ≤ _; rw [h.diagonal_p]; exact hdiag.2.2.1)
    (by change |value (entry n result.1 q q) - _| ≤ _; rw [h.diagonal_q]; exact hdiag.2.2.2)
    (by change value (entry n result.1 p q) = 0; rw [h.pivot_zero.1, zero_value])
    (by
      intro k hkp hkq
      have hkp' : k.val ≠ p := fun he => hkp (Fin.ext he)
      have hkq' : k.val ≠ q := fun he => hkq (Fin.ext he)
      have he := h.matrix_pair k.val k.isLt hkp' hkq'
      have hb := pair_reference (pivotT n a p q) (entry n a k.val p) (entry n a k.val q)
        (|value (entry n a k.val p)| + |value (entry n a k.val q)| + η)
        htf ht2 (Flare.Matrix.Storage.getD_finite _ _ ha)
        (Flare.Matrix.Storage.getD_finite _ _ ha) le_rfl (by
          apply le_trans (b := 65) _ ((by norm_num : (65 : ℝ) ≤ 577).trans hlarge)
          linarith only [hab k.val p k.isLt hp, hab k.val q k.isLt hq, hη1])
      change |value (entry n result.1 k.val p) - _| ≤ _ ∧ |value (entry n result.1 k.val q) - _| ≤ _
      rw [he.1, he.2.2.1]
      simp only [mul_one_div] at hb
      exact hb)
    (by
      intro i j hip hiq hjp hjq
      change value (entry n result.1 i.val j.val) = value (entry n a i.val j.val)
      rw [h.matrix_unchanged i.val j.val i.isLt j.isLt
        (fun he => hip (Fin.ext he)) (fun he => hiq (Fin.ext he))
        (fun he => hjp (Fin.ext he)) (fun he => hjq (Fin.ext he))])
  apply hs.trans
  have hres' : |A P Q * (value (pivotT n a p q))^2 + (A Q Q - A P P) * value (pivotT n a p q) - A P
    Q| ≤
      256 * u * |value (entry n a p q)| := hres
  have hbound := add_le_add (le_refl (2 * (2 : ℝ)^(-48 : Int) * (2 * ‖A‖ + n * η) + 13 * u * (‖A‖ +
    η)))
    (mul_le_mul_of_nonneg_left hres' (by norm_num : (0 : ℝ) ≤ 2))
  have he : 2 * (2 : ℝ)^(-48 : Int) * (2 * ‖A‖ + n * η) + 13 * u * (‖A‖ + η) +
      2 * (256 * u * |value (entry n a p q)|) =
      141 * u * ‖A‖ + (64 * n + 13) * u * η + 512 * u * |value (entry n a p q)| := by
    rw [show (2 : ℝ)^(-48 : Int) = 32 * u by norm_num [u]]
    ring
  exact hbound.trans_eq he

/-- Native eigenvector updates only perturb two columns. Their operator-norm
error scales with the vector-matrix norm, without a leading dimension factor. -/
theorem rotation_vectors_norm (n p q : Nat) (a v : Array Float) (result : Array Float × Array Float)
    (hp : p < n) (hq : q < n) (hpq : p ≠ q)
    (ha : a.all Float.isFinite = true) (hv : v.all Float.isFinite = true)
    (hab : ∀ i j, i < n → j < n → |value (entry n a i j)| ≤ 32)
    (hvb : ∀ i j, i < n → j < n → |value (entry n v i j)| ≤ 32)
    (hstop : (1.0e-14 : Float) < (entry n a p q).abs)
    (h : RotationResult n p q a v result)
    : let t := value (pivotT n a p q)
      let c := 1 / Real.sqrt (1 + t ^ 2)
      let J := plane (⟨p, hp⟩ : Fin n) ⟨q, hq⟩ c (t * c)
      ‖matrix n n result.2 - matrix n n v * J‖
      ≤ 96 * (2 : ℝ) ^ (-53 : Int) * ‖matrix n n v‖
        + 48 * n * (2 : ℝ) ^ (-53 : Int) * (2 : ℝ) ^ (-1022 : Int) := by
  let P : Fin n := ⟨p, hp⟩
  let Q : Fin n := ⟨q, hq⟩
  have hPQ : P ≠ Q := fun he => hpq (congrArg Fin.val he)
  let η := (2 : ℝ)^(-1022 : Int)
  have hη : η ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
  have hparams := Jacobi.pivot_rotation_parameters (entry n a p p) (entry n a p q) (entry n a q q)
    (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ ha)
    (Flare.Matrix.Storage.getD_finite _ _ ha) (hab p p hp hp) (hab p q hp hq) (hab q q hq hq) hstop
  have ht : (pivotT n a p q).isFinite = true := hparams.2.1
  have htb : |value (pivotT n a p q)| ≤ 2 := hparams.2.2.2.2.1
  let t := value (pivotT n a p q)
  let c := 1 / Real.sqrt (1 + t^2)
  let J := plane P Q c (t * c)
  have hpair (i : Fin n) := pair_reference (pivotT n a p q) (entry n v i.val p) (entry n v i.val q)
    (|value (entry n v i.val p)| + |value (entry n v i.val q)| + η) ht htb
    (Flare.Matrix.Storage.getD_finite _ _ hv) (Flare.Matrix.Storage.getD_finite _ _ hv)
    le_rfl (by
      apply le_trans (b := 65) (by linarith only [hvb i.val p i.isLt hp, hvb i.val q i.isLt hq, hη])
      exact ((by norm_num : (65 : ℝ) ≤ (2 : ℝ)^(7 : Int))).trans
        (zpow_le_zpow_right₀ (by norm_num) (by norm_num)))
  have herror := Flare.Analysis.JacobiNorms.two_column_error (matrix n n v)
    (matrix n n result.2 - matrix n n v * J) P Q hPQ ((2 : ℝ)^(-48 : Int)) η (by positivity) (by
      positivity)
    (by
      intro i
      have he := h.vectors_pair i.val i.isLt
      simp only [Matrix.sub_apply, J, mul_plane _ P Q hPQ, ite_true, hPQ.symm, ite_false]
      change |value (entry n result.2 i.val p) - _| ≤ _ ∧ |value (entry n result.2 i.val q) - _| ≤ _
      rw [he.1, he.2]
      exact hpair i)
    (by
      intro i j hjp hjq
      simp only [Matrix.sub_apply, J, mul_plane _ P Q hPQ, hjp, hjq, ite_false]
      change value (entry n result.2 i.val j.val) - value (entry n v i.val j.val) = 0
      rw [h.vectors_unchanged i.val j.val i.isLt j.isLt
        (fun he => hjp (Fin.ext he)) (fun he => hjq (Fin.ext he)), sub_self])
  apply herror.trans_eq
  rw [show (2 : ℝ)^(-48 : Int) = 32 * (2 : ℝ)^(-53 : Int) by norm_num]
  ring

/-- One actual trajectory transition has an exact orthogonal reference and
operator-norm error bounds. The stopping transition uses identity. These
uniform constants are coarse enclosures, not a rank-cutoff guarantee. -/
theorem advance_similarity (n k : Nat) (a v : Array Float) (hn : n ≤ 18)
    (hk : k ≤ 32 * n * n) (h : State n k a v)
    : ∃ J : Matrix (Fin n) (Fin n) ℝ,
        J ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
        ∧ ‖matrix n n (advance n a v).1 - J.transpose * matrix n n a * J‖
          ≤ n * (2 : ℝ) ^ (-33 : Int)
        ∧ ‖matrix n n (advance n a v).2 - matrix n n v * J‖ ≤ n * ((2 : ℝ) ^ (-48 : Int) * 65) := by
  by_cases hstop : (selectedPivot n a).magnitude ≤ (1.0e-14 : Float)
  · refine ⟨1, (unitary _).one_mem, ?_, ?_⟩ <;>
      simp only [advance, hstop, ↓reduceIte, Matrix.transpose_one, Matrix.one_mul,
        Matrix.mul_one, sub_self, norm_zero] <;> positivity
  have hs := selectedPivot_correct n a h.matrix_finite h.symmetric
  obtain ⟨hpq, hq, _, hlt⟩ := selectedPivot_ready n a (selectedPivot n a) hs.2.1 hs.2.2.2.1 hstop
  have hp := hpq.trans hq
  have hE := state_energy_bound n k a v hn hk h
  have hab := entries_of_energy n a hE.1
  have hvb := entries_of_energy n v hE.2
  obtain ⟨result, he, hr⟩ := rotate_step n (selectedPivot n a).row (selectedPivot n a).column a v
    hp hq (Nat.ne_of_lt hpq) h.matrix_size h.vectors_size h.matrix_finite h.vectors_finite hab hvb
      hlt
  have hnext : advance n a v = result := by simp only [advance, hstop, ↓reduceIte, he]
  rw [hnext]
  have herr := rotation_similarity n (selectedPivot n a).row (selectedPivot n a).column a v result
    hp hq (Nat.ne_of_lt hpq) h.matrix_finite h.vectors_finite hab hvb h.symmetric hlt hr
  dsimp only at herr
  refine ⟨_, orthogonal_mem_unitary _ ⟨herr.1, herr.2.1⟩, ?_, ?_⟩
  · apply norm_le_entries _ ((2 : ℝ)^(-33 : Int)) (by positivity)
    intro i j
    have hb := JacobiDiagonal.pivot_polynomial_residual
      (entry n a (selectedPivot n a).row (selectedPivot n a).row)
      (entry n a (selectedPivot n a).row (selectedPivot n a).column)
      (entry n a (selectedPivot n a).column (selectedPivot n a).column)
      (Flare.Matrix.Storage.getD_finite _ _ h.matrix_finite)
      (Flare.Matrix.Storage.getD_finite _ _ h.matrix_finite)
      (Flare.Matrix.Storage.getD_finite _ _ h.matrix_finite)
      (hab _ _ hp hp) (hab _ _ hp hq) (hab _ _ hq hq) hlt
    change |value (entry n a (selectedPivot n a).row (selectedPivot n a).column) *
      (value (pivotT n a (selectedPivot n a).row (selectedPivot n a).column))^2 +
      (value (entry n a (selectedPivot n a).column (selectedPivot n a).column) -
        value (entry n a (selectedPivot n a).row (selectedPivot n a).row)) *
      value (pivotT n a (selectedPivot n a).row (selectedPivot n a).column) -
      value (entry n a (selectedPivot n a).row (selectedPivot n a).column)| ≤ (2 : ℝ)^(-35 : Int)
      at hb
    apply (herr.2.2.1 i j).trans
    have hbound := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at hbound ⊢
    linarith only [hbound]
  · exact norm_le_entries _ _ (by positivity) herr.2.2.2

/-- Every bounded native trajectory prefix stays close to an exact orthogonal
similarity of its starting matrix and to that same orthogonal eigenvector
product. All intermediate success and magnitude facts come from State. -/
theorem trajectory_backward_error (n : Nat) (a v : Array Float) (hn : n ≤ 18)
    (h : State n 0 a v) (hV : matrix n n v = 1) (k : Nat) (hk : k ≤ 32 * n * n)
    : ∃ W : Matrix (Fin n) (Fin n) ℝ,
        W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
        ∧ ‖matrix n n (trajectory n a v k).1 - W.transpose * matrix n n a * W‖
          ≤ k * (n * (2 : ℝ) ^ (-33 : Int))
        ∧ ‖matrix n n (trajectory n a v k).2 - W‖ ≤ k * (n * ((2 : ℝ) ^ (-48 : Int) * 65)) := by
  induction k with
  | zero => refine ⟨1, (unitary _).one_mem, ?_, ?_⟩ <;> simp [trajectory, hV]
  | succ k ih =>
      obtain ⟨W, hW, hA, hV'⟩ := ih (by omega)
      have hstate := trajectory_state n a v hn h k (by omega)
      obtain ⟨J, hJ, heA, heV⟩ := advance_similarity n k _ _ hn (by omega) hstate
      refine ⟨W * J, (unitary _).mul_mem hW hJ, ?_, ?_⟩
      · have he : matrix n n (trajectory n a v (k + 1)).1 - (W * J).transpose * matrix n n a * (W *
        J) =
            (matrix n n (advance n (trajectory n a v k).1 (trajectory n a v k).2).1 -
              J.transpose * matrix n n (trajectory n a v k).1 * J) +
            J.transpose * (matrix n n (trajectory n a v k).1 - W.transpose * matrix n n a * W) * J
              := by
          simp only [trajectory, Matrix.transpose_mul, Matrix.mul_sub, Matrix.sub_mul,
            Matrix.mul_assoc]
          abel
        rw [he]
        have he' := (norm_add_le _ _).trans (add_le_add heA
          ((similarity_isometry J _ hJ).le.trans hA))
        exact he'.trans_eq (by push_cast; ring)
      · have he : matrix n n (trajectory n a v (k + 1)).2 - W * J =
            (matrix n n (advance n (trajectory n a v k).1 (trajectory n a v k).2).2 -
              matrix n n (trajectory n a v k).2 * J) +
            (matrix n n (trajectory n a v k).2 - W) * J := by
          simp only [trajectory, Matrix.sub_mul]
          abel
        rw [he]
        have he' := (norm_add_le _ _).trans (add_le_add heV
          ((CStarRing.norm_mul_mem_unitary _ hJ).le.trans hV'))
        exact he'.trans_eq (by push_cast; ring)

end Flare.Matrix.JacobiSpectral
