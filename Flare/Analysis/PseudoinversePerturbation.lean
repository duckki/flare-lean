import Flare.Analysis.MoorePenrose
import Flare.Analysis.SpectralPerturbation

/-! Perturbation identities for symmetric Moore–Penrose inverses. Singular
matrices are handled through their orthogonal projections, without assuming
ordinary invertibility. -/

namespace Flare.Analysis.PseudoinversePerturbation
open Matrix Flare.Analysis SpectralPerturbation
open scoped Matrix.Norms.L2Operator

/-- A symmetric idempotent is a contraction in the Euclidean operator norm. -/
theorem projection_norm_le_one {n : Nat} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.transpose = P) (hPP : P * P = P)
    : ‖P‖ ≤ 1 := by
  have he : ‖star P * P‖ = ‖P‖ * ‖P‖ := CStarRing.norm_star_mul_self
  simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, hP, hPP] at he
  nlinarith only [he, norm_nonneg P]

/-- Symmetric matrices commute with their symmetric pseudoinverses. -/
theorem commute {n : Nat} (A X : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.transpose = A) (hX : X.transpose = X) (hAX : MoorePenrose A X)
    : A * X = X * A := by
  have he := hAX.2.2.1
  rw [transpose_mul, hA, hX] at he
  exact he.symm

/-- The nullspace projection accompanying a symmetric pseudoinverse has norm
at most one, including zero matrices and empty dimensions. -/
theorem complementary_projection_norm {n : Nat} (A X : Matrix (Fin n) (Fin n) ℝ)
    (hAX : MoorePenrose A X)
    : ‖1 - A * X‖ ≤ 1 := by
  have hPP : (A * X) * (A * X) = A * X := by rw [← mul_assoc, hAX.1]
  apply projection_norm_le_one
  · rw [transpose_sub, transpose_one, hAX.2.2.1]
  · calc
      _ = 1 - A * X - A * X + (A * X) * (A * X) := by noncomm_ring
      _ = _ := by rw [hPP]; abel

/-- Exact perturbation identity for symmetric pseudoinverses. The two
projection terms account for nullspaces; no equal-rank hypothesis is required. -/
theorem difference_identity {n : Nat} (A B X Y : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.transpose = A) (hB : B.transpose = B)
    (hX : X.transpose = X) (hY : Y.transpose = Y)
    (hAX : MoorePenrose A X) (hBY : MoorePenrose B Y)
    : Y - X
      = Y * (A - B) * X + (Y * Y) * (B - A) * (1 - A * X) + (1 - Y * B) * (B - A) * (X * X) := by
  have hcommA := commute A X hA hX hAX
  have hcommB := commute B Y hB hY hBY
  have hAAX : A * (A * X) = A := by rw [hcommA, ← mul_assoc, hAX.1]
  have hAXX : A * (X * X) = X := by rw [← mul_assoc, hcommA, hAX.2.1]
  have hYYB : Y * Y * B = Y := by rw [mul_assoc, ← hcommB, ← mul_assoc, hBY.2.1]
  have hYBB : Y * B * B = B := by rw [← hcommB, hBY.1]
  have hAk : A * (1 - A * X) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hAAX, sub_self]
  have hkB : (1 - Y * B) * B = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hYBB, sub_self]
  have hsecond : (Y * Y) * (B - A) * (1 - A * X) = Y * (1 - A * X) := by
    rw [mul_assoc, Matrix.sub_mul, hAk, sub_zero, ← mul_assoc, hYYB]
  have hthird : (1 - Y * B) * (B - A) * (X * X) = -((1 - Y * B) * X) := by
    rw [Matrix.mul_sub, hkB, zero_sub, Matrix.neg_mul, mul_assoc, hAXX]
  rw [hsecond, hthird]
  noncomm_ring

/-- A norm bound for the exact pseudoinverse perturbation. The inverse norms
are explicit: cutoff correctness must justify them for a computed truncation. -/
theorem difference_norm {n : Nat} (A B X Y : Matrix (Fin n) (Fin n) ℝ) (L M ε : ℝ)
    (hA : A.transpose = A) (hB : B.transpose = B)
    (hX : X.transpose = X) (hY : Y.transpose = Y)
    (hAX : MoorePenrose A X) (hBY : MoorePenrose B Y)
    (hL : ‖X‖ ≤ L) (hM : ‖Y‖ ≤ M) (he : ‖B - A‖ ≤ ε)
    : ‖Y - X‖ ≤ (L * M + L ^ 2 + M ^ 2) * ε := by
  have hL0 := (norm_nonneg X).trans hL
  have hM0 := (norm_nonneg Y).trans hM
  have hε0 := (norm_nonneg (B - A)).trans he
  have hBA := commute B Y hB hY hBY
  have hPX := complementary_projection_norm A X hAX
  have hPY : ‖1 - Y * B‖ ≤ 1 := by rw [← hBA]; exact complementary_projection_norm B Y hBY
  have h1 : ‖Y * (A - B) * X‖ ≤ M * ε * L := by
    apply (norm_mul_le _ _).trans
    apply mul_le_mul _ hL (norm_nonneg _) (by positivity)
    apply (norm_mul_le _ _).trans
    rw [norm_sub_rev]
    exact mul_le_mul hM he (norm_nonneg _) hM0
  have hYY : ‖Y * Y‖ ≤ M^2 := by
    exact ((norm_mul_le _ _).trans (mul_le_mul hM hM (norm_nonneg _) hM0)).trans_eq (by ring)
  have hXX : ‖X * X‖ ≤ L^2 := by
    exact ((norm_mul_le _ _).trans (mul_le_mul hL hL (norm_nonneg _) hL0)).trans_eq (by ring)
  have h2 : ‖(Y * Y) * (B - A) * (1 - A * X)‖ ≤ M^2 * ε := by
    calc
      _ ≤ ‖(Y * Y) * (B - A)‖ * ‖1 - A * X‖ := norm_mul_le _ _
      _ ≤ (M ^ 2 * ε) * 1 :=
        mul_le_mul
          ((norm_mul_le _ _).trans (mul_le_mul hYY he (norm_nonneg _) (sq_nonneg M))) hPX
          (norm_nonneg _) (by positivity)
      _ = _ := mul_one _
  have h3 : ‖(1 - Y * B) * (B - A) * (X * X)‖ ≤ ε * L^2 := by
    calc
      _ ≤ ‖(1 - Y * B) * (B - A)‖ * ‖X * X‖ := norm_mul_le _ _
      _ ≤ (1 * ε) * L ^ 2 :=
        mul_le_mul
          ((norm_mul_le _ _).trans (mul_le_mul hPY he (norm_nonneg _) (by norm_num))) hXX
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  rw [difference_identity A B X Y hA hB hX hY hAX hBY]
  exact ((norm_add_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)).trans_eq
    (by ring)

/-- When the application only observes the range of `A`, its product with a
nearby pseudoinverse is controlled by `F X`, rather than the larger `F` norm. -/
theorem transported_inverse_norm {m n : Nat} (A B X Y : Matrix (Fin n) (Fin n) ℝ)
    (F : Matrix (Fin m) (Fin n) ℝ) (q M ε : ℝ)
    (hA : A.transpose = A) (hX : X.transpose = X) (hAX : MoorePenrose A X)
    (hBY : MoorePenrose B Y) (hF : F * (A * X) = F)
    (hq : ‖F * X‖ ≤ q) (hM : ‖Y‖ ≤ M) (he : ‖A - B‖ ≤ ε)
    : ‖F * Y‖ ≤ q * (1 + ε * M) := by
  have hq0 := (norm_nonneg _).trans hq
  have hM0 := (norm_nonneg _).trans hM
  have he0 := (norm_nonneg _).trans he
  have hFXA : F * X * A = F := by rw [Matrix.mul_assoc, ← commute A X hA hX hAX, hF]
  have hP : ‖B * Y‖ ≤ 1 := projection_norm_le_one _ hBY.2.2.1 (by rw [← mul_assoc, hBY.1])
  have hid : F * Y = (F * X) * (A - B) * Y + (F * X) * (B * Y) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hFXA, Matrix.mul_assoc]
    abel
  have h1 : ‖(F * X) * (A - B) * Y‖ ≤ q * ε * M := by
    apply (l2_opNorm_mul _ _).trans
    exact mul_le_mul ((l2_opNorm_mul _ _).trans (mul_le_mul hq he (norm_nonneg _) hq0))
      hM (norm_nonneg _) (by positivity)
  have h2 : ‖(F * X) * (B * Y)‖ ≤ q := by
    exact ((l2_opNorm_mul _ _).trans (mul_le_mul hq hP (norm_nonneg _) hq0)).trans_eq (mul_one q)
  rw [hid]
  exact ((norm_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)

/-- Range-aware bound for a pseudoinverse difference projected through `F`. The
nullspace projection in the Moore--Penrose identity contributes only a quadratic
error after projection through `F`; singular matrices remain permitted. -/
theorem projected_difference_norm {m n : Nat} (A B X Y : Matrix (Fin n) (Fin n) ℝ)
    (F : Matrix (Fin m) (Fin n) ℝ) (q L M ε : ℝ)
    (hA : A.transpose = A) (hB : B.transpose = B)
    (hX : X.transpose = X) (hY : Y.transpose = Y)
    (hAX : MoorePenrose A X) (hBY : MoorePenrose B Y)
    (hF : F * (A * X) = F) (hq : ‖F * X‖ ≤ q)
    (hL : ‖X‖ ≤ L) (hM : ‖Y‖ ≤ M) (he : ‖A - B‖ ≤ ε)
    : ‖F * (Y - X) * F.transpose‖ ≤ q ^ 2 * ε * (1 + (M + L) * ε) := by
  have hq0 := (norm_nonneg _).trans hq
  have hL0 := (norm_nonneg _).trans hL
  have hM0 := (norm_nonneg _).trans hM
  have he0 := (norm_nonneg _).trans he
  have hcommA := commute A X hA hX hAX
  have hcommB := commute B Y hB hY hBY
  have hFXA : F * X * A = F := by rw [Matrix.mul_assoc, ← hcommA, hF]
  have hXT : ‖X * F.transpose‖ ≤ q := by
    have ht : (F * X).transpose = X * F.transpose := by rw [transpose_mul, hX]
    rw [← ht]
    exact (l2_opNorm_conjTranspose (F * X)).le.trans (by
      simpa only [conjTranspose_eq_transpose_of_trivial] using hq)
  have hkernel : (1 - A * X) * F.transpose = 0 := by
    have hf : F * (1 - A * X) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hF, sub_self]
    have ht := congrArg Matrix.transpose hf
    simpa only [transpose_mul, transpose_sub, transpose_one, hAX.2.2.1, transpose_zero] using ht
  let P := 1 - Y * B
  have hP : ‖P‖ ≤ 1 := by
    dsimp [P]
    rw [← hcommB]
    exact complementary_projection_norm B Y hBY
  have hBP : B * P = 0 := by
    dsimp [P]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hBY.1, sub_self]
  have hFP : F * P = (F * X) * (A - B) * P := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, hBP, sub_zero, ← Matrix.mul_assoc, hFXA]
  have hFPnorm : ‖F * P‖ ≤ q * ε := by
    rw [hFP]
    exact ((l2_opNorm_mul _ _).trans (mul_le_mul
      ((l2_opNorm_mul _ _).trans (mul_le_mul hq he (norm_nonneg _) hq0))
      hP (norm_nonneg _) (by positivity))).trans_eq (mul_one _)
  have hXXT : ‖(X * X) * F.transpose‖ ≤ L * q := by
    rw [Matrix.mul_assoc]
    exact (l2_opNorm_mul _ _).trans (mul_le_mul hL hXT (norm_nonneg _) hL0)
  have hFY := transported_inverse_norm A B X Y F q M ε hA hX hAX hBY hF hq hM he
  have hid : F * (Y - X) * F.transpose =
      (F * Y) * (A - B) * (X * F.transpose) +
      (F * P) * (B - A) * ((X * X) * F.transpose) := by
    rw [difference_identity A B X Y hA hB hX hY hAX hBY]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hkernel, Matrix.mul_zero, add_zero,
      P]
  have h1 : ‖(F * Y) * (A - B) * (X * F.transpose)‖ ≤ (q * (1 + ε * M)) * ε * q := by
    apply (l2_opNorm_mul _ _).trans
    exact mul_le_mul ((l2_opNorm_mul _ _).trans (mul_le_mul hFY he (norm_nonneg _) (by positivity)))
      hXT (norm_nonneg _) (by positivity)
  have h2 : ‖(F * P) * (B - A) * ((X * X) * F.transpose)‖ ≤ (q * ε) * ε * (L * q) := by
    apply (l2_opNorm_mul _ _).trans
    apply mul_le_mul _ hXXT (norm_nonneg _) (by positivity)
    apply (l2_opNorm_mul _ _).trans
    rw [norm_sub_rev]
    exact mul_le_mul hFPnorm he (norm_nonneg _) (by positivity)
  rw [hid]
  exact ((norm_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)

/-- A Gram domination supplies both application premises used by the sharper
pseudoinverse bound: annihilation of the source nullspace and a bound on `F X`.
These follow from PSD structure, rather than assumptions about a numerical solve. -/
theorem dominated_transport {m n : Nat} (A X : Matrix (Fin n) (Fin n) ℝ)
    (F : Matrix (Fin m) (Fin n) ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hA : A.PosSemidef) (hAX : MoorePenrose A X)
    (hdom : (β • A - F.transpose * F).PosSemidef)
    : F * (A * X) = F ∧ ‖F * X‖ ^ 2 ≤ β * ‖X‖ := by
  have hXpsd := Flare.Analysis.MoorePenrose.posSemidef hA hAX
  have hAsym : A.transpose = A := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hA.isHermitian
  have hXsym : X.transpose = X := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hXpsd.isHermitian
  have hcomm := commute A X hAsym hXsym hAX
  let P := 1 - A * X
  have hAP : A * P = 0 := by
    dsimp [P]
    rw [Matrix.mul_sub, Matrix.mul_one, hcomm, ← Matrix.mul_assoc, hAX.1, sub_self]
  have hnull : (-(F * P).transpose * (F * P)).PosSemidef := by
    have hh := hdom.mul_mul_conjTranspose_same P.transpose
    simpa only [conjTranspose_eq_transpose_of_trivial, transpose_transpose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
      hAP, Matrix.mul_zero, smul_zero, zero_sub, transpose_mul, Matrix.neg_mul] using hh
  have hFP : F * P = 0 := by
    have hg := gram_norm_bound (F * P) 0 (by simpa only [zero_sub, Matrix.neg_mul] using hnull)
    rw [norm_zero] at hg
    exact norm_eq_zero.mp (by nlinarith only [hg, norm_nonneg (F * P)])
  have hrange : F * (A * X) = F := by
    dsimp [P] at hFP
    rw [Matrix.mul_sub, Matrix.mul_one] at hFP
    exact (sub_eq_zero.mp hFP).symm
  refine ⟨hrange, ?_⟩
  have hgram : (β • X - (F * X).transpose * (F * X)).PosSemidef := by
    have hh := hdom.mul_mul_conjTranspose_same X
    simpa only [conjTranspose_eq_transpose_of_trivial, hXsym, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hAX.2.1, transpose_mul] using hh
  have hg := gram_norm_bound (F * X) (β • X) hgram
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ] using hg

end Flare.Analysis.PseudoinversePerturbation
