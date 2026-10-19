module

public import Flare.Analysis.Jacobi

/-! Perturbation identities used to bound the diagonal part of a native Jacobi
rotation. All arithmetic here is ghost real arithmetic for numerical analysis. -/

@[expose] public section

namespace Flare.Analysis.JacobiDiagonal

/-- A quotient's residual retains the numerator and pivot scales. In
particular, this estimate does not replace a small pivot by a global bound. -/
theorem scaled_quotient_relative (u v b τ δ ε η : ℝ)
    (hb : b ≠ 0) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) (_hη : 0 ≤ η)
    (hv : |v - 2 * b| ≤ δ * |b|)
    (hτ : |τ - u / v| ≤ ε * (|u / v| + η))
    : |2 * b * τ - u| ≤ (δ + 2 * ε) * |u| + 2 * ε * |b| * η := by
  have hbp : 0 < |b| := abs_pos.mpr hb
  have hvl : |b| ≤ |v| := by
    have ht := abs_sub_le (2 * b) v 0
    simp only [sub_zero, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_sub_comm (2 * b) v] at ht
    nlinarith [mul_le_mul_of_nonneg_right hδ1 (abs_nonneg b)]
  have hvp : 0 < |v| := hbp.trans_le hvl
  have hv0 : v ≠ 0 := abs_pos.mp hvp
  have hbq : |b| * |u / v| ≤ |u| := by
    rw [abs_div, ← mul_div_assoc]
    apply (div_le_iff₀ hvp).mpr
    nlinarith [mul_le_mul_of_nonneg_right hvl (abs_nonneg u)]
  have he : |2 * b * (τ - u / v)| ≤ 2 * ε * (|u| + |b| * η) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ 2 * |b| * (ε * (|u / v| + η)) :=
        mul_le_mul_of_nonneg_left hτ (by positivity)
      _ = 2 * ε * (|b| * |u / v| + |b| * η) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hbq le_rfl) (by positivity)
  have hd : |(2 * b - v) * (u / v)| ≤ δ * |u| := by
    rw [abs_mul, abs_sub_comm (2 * b) v]
    calc
      _ ≤ δ * |b| * |u / v| := mul_le_mul_of_nonneg_right hv (abs_nonneg _)
      _ = δ * (|b| * |u / v|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbq hδ
  have hid : 2 * b * τ - u = 2 * b * (τ - u / v) + (2 * b - v) * (u / v) := by
    field_simp
    ring
  rw [hid]
  exact ((abs_add_le _ _).trans (add_le_add he hd)).trans_eq (by ring)

/-- The stable tangent cancels a large pivot parameter. Its scaled perturbation
keeps the product bounded even when the parameter itself is large. -/
theorem tangent_product_bound (τ t ε : ℝ) (hε : 0 ≤ ε)
    (he : |t - Jacobi.tangent τ| ≤ ε / (|τ| + Real.sqrt (1 + τ ^ 2)))
    : |τ * t| ≤ 1 / 2 + ε := by
  have hp := Jacobi.tangent_properties τ
  have hsq : (Jacobi.tangent τ)^2 ≤ 1 := by
    nlinarith [sq_abs (Jacobi.tangent τ), abs_nonneg (Jacobi.tangent τ), hp.2.1]
  have ht0 : |τ * Jacobi.tangent τ| ≤ 1 / 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [hp.2.2, sq_nonneg (Jacobi.tangent τ)]
  have hD : |τ| ≤ |τ| + Real.sqrt (1 + τ^2) := by
    linarith [Real.sqrt_nonneg (1 + τ^2)]
  have hpert : |τ * (t - Jacobi.tangent τ)| ≤ ε := by
    rw [abs_mul]
    calc
      _ ≤ |τ| * (ε / (|τ| + Real.sqrt (1 + τ ^ 2))) :=
        mul_le_mul_of_nonneg_left he (abs_nonneg _)
      _ ≤ (|τ| + Real.sqrt (1 + τ ^ 2)) * (ε / (|τ| + Real.sqrt (1 + τ ^ 2))) :=
        mul_le_mul_of_nonneg_right hD (div_nonneg hε hp.1.le)
      _ = _ := by field_simp
  rw [show τ * t = τ * Jacobi.tangent τ + τ * (t - Jacobi.tangent τ) by ring]
  exact (abs_add_le _ _).trans (add_le_add ht0 hpert)

/-- Relative parameter error and a denominator-scaled tangent error produce a
pivot-proportional residual. The small coefficient lets us absorb the diagonal
difference without assuming that the pivot parameter is small. -/
theorem pivot_residual_relative (a b d τ t u : ℝ)
    (hu : 0 ≤ u) (hu' : u ≤ 1 / 10000) (ht : |t| ≤ 2)
    (hprod : |τ * t| ≤ 1 / 2 + 22 * u)
    (hquad : |t ^ 2 + 2 * τ * t - 1| ≤ 110 * u)
    (hparam : |2 * b * τ - (d - a)| ≤ 32 * u * |d - a| + u * |b|)
    : |(d - a) * t| ≤ 2 * |b| ∧ |b * t ^ 2 + (d - a) * t - b| ≤ 256 * u * |b| := by
  have hscaled : |(2 * b * τ - (d - a)) * t| ≤
      32 * u * |(d - a) * t| + 2 * u * |b| := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (32 * u * |d - a| + u * |b|) * |t| :=
        mul_le_mul_of_nonneg_right hparam (abs_nonneg t)
      _ = 32 * u * (|d - a| * |t|) + u * |b| * |t| := by ring
      _ ≤ _ :=
        add_le_add le_rfl
          (by nlinarith [mul_le_mul_of_nonneg_left ht (show 0 ≤ u * |b| by positivity)])
  have hleading : |2 * b * τ * t| ≤ (1 + 44 * u) * |b| := by
    rw [show 2 * b * τ * t = 2 * b * (τ * t) by ring, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact (mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 2 * |b|)).trans_eq (by ring)
  have hdiag : |(d - a) * t| ≤ 2 * |b| := by
    have he : (d - a) * t = 2 * b * τ * t - (2 * b * τ - (d - a)) * t := by ring
    have h := abs_sub (2 * b * τ * t) ((2 * b * τ - (d - a)) * t)
    rw [← he] at h
    have hx := h.trans (add_le_add hleading hscaled)
    have huX := mul_le_mul_of_nonneg_right hu' (abs_nonneg ((d - a) * t))
    have huB := mul_le_mul_of_nonneg_right hu' (abs_nonneg b)
    nlinarith only [hx, huX, huB, abs_nonneg b]
  refine ⟨hdiag, ?_⟩
  have hid : b * t^2 + (d - a) * t - b =
      b * (t^2 + 2 * τ * t - 1) - (2 * b * τ - (d - a)) * t := by ring
  rw [hid]
  apply (abs_sub _ _).trans
  have hfirst : |b * (t^2 + 2 * τ * t - 1)| ≤ 110 * u * |b| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hquad (abs_nonneg b)).trans_eq (by ring)
  have hsecond := hscaled.trans (add_le_add (mul_le_mul_of_nonneg_left hdiag (by positivity))
    le_rfl)
  exact (add_le_add hfirst hsecond).trans (by nlinarith only [mul_nonneg hu (abs_nonneg b)])

/-- A relative quotient error controls its residual after multiplication by
the original pivot. This avoids a large absolute bound on the quotient itself. -/
theorem scaled_quotient_error (u v b τ δ ε η : ℝ)
    (hb : b ≠ 0) (hu : |u| ≤ 128) (hbb : |b| ≤ 32)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hv : |v - 2 * b| ≤ δ * |b|)
    (hτ : |τ - u / v| ≤ ε * (|u / v| + η))
    : |2 * b * τ - u| ≤ 288 * δ + 224 * ε := by
  have hbp : 0 < |b| := abs_pos.mpr hb
  have hvl : |b| ≤ |v| := by
    have ht := abs_sub_le (2 * b) v 0
    simp only [sub_zero, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_sub_comm (2 * b) v]
      at ht
    nlinarith
  have hvu : |v| ≤ 3 * |b| := by
    have ht := abs_sub_le v (2 * b) 0
    simp only [sub_zero, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ht
    nlinarith
  have hvp : 0 < |v| := hbp.trans_le hvl
  have hv0 : v ≠ 0 := abs_pos.mp hvp
  have hbq : |b| * |u / v| ≤ |u| := by
    rw [abs_div, ← mul_div_assoc]
    apply (div_le_iff₀ hvp).mpr
    nlinarith [mul_le_mul_of_nonneg_right hvl (abs_nonneg u)]
  have hvq : |v| * |u / v| = |u| := by rw [abs_div]; field_simp
  have hbe : |b * (τ - u / v)| ≤ ε * (|u| + |b| * η) := by
    rw [abs_mul]
    have he := mul_le_mul_of_nonneg_left hτ (abs_nonneg b)
    nlinarith [mul_le_mul_of_nonneg_left hbq hε]
  have hbt : |b * τ| ≤ 288 := by
    have hterm : |b| * η ≤ 32 := by nlinarith [abs_nonneg b]
    have hbq' : |b * (u / v)| ≤ 128 := by rw [abs_mul]; exact hbq.trans hu
    have hbe' : |b * (τ - u / v)| ≤ 160 := by
      apply hbe.trans
      nlinarith [abs_nonneg u]
    have ht' := abs_sub_le (b * τ) (b * (u / v)) 0
    rw [show b * τ - b * (u / v) = b * (τ - u / v) by ring] at ht'
    simp only [sub_zero] at ht'
    linarith
  have hve : |v * (τ - u / v)| ≤ 224 * ε := by
    rw [abs_mul]
    have he := mul_le_mul_of_nonneg_left hτ (abs_nonneg v)
    have hterm : |v| * η ≤ 96 := by nlinarith [abs_nonneg v]
    have heq : |v| * (ε * (|u / v| + η)) = ε * (|u| + |v| * η) := by
      calc
        _ = ε * (|v| * |u / v| + |v| * η) := by ring
        _ = _ := by rw [hvq]
    rw [heq] at he
    nlinarith
  have hfirst : |(2 * b - v) * τ| ≤ 288 * δ := by
    rw [abs_mul, abs_sub_comm (2 * b) v]
    have h1 := mul_le_mul_of_nonneg_right hv (abs_nonneg τ)
    have h2 := mul_le_mul_of_nonneg_left hbt hδ
    rw [abs_mul] at h2
    nlinarith
  have hid : 2 * b * τ - u = (2 * b - v) * τ + v * (τ - u / v) := by
    field_simp; ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hfirst hve)

/-- The stable tangent's denominator-scaled error gives a uniformly small
quadratic residual even when the pivot parameter is large. -/
theorem tangent_residual (τ t ε : ℝ) (hε : 0 ≤ ε) (ht : |t| ≤ 2)
    (he : |t - Jacobi.tangent τ| ≤ ε / (|τ| + Real.sqrt (1 + τ ^ 2)))
    : |t ^ 2 + 2 * τ * t - 1| ≤ 5 * ε := by
  have hprops := Jacobi.tangent_properties τ
  have hs1 : 1 ≤ Real.sqrt (1 + τ ^ 2) := by
    have hs := Real.sq_sqrt (by nlinarith [sq_nonneg τ] : 0 ≤ 1 + τ ^ 2)
    nlinarith [Real.sqrt_nonneg (1 + τ ^ 2), sq_nonneg τ]
  have hfactor : |t + Jacobi.tangent τ + 2 * τ| ≤ 5 * (|τ| + Real.sqrt (1 + τ ^ 2)) := by
    have htri := abs_add_le (t + Jacobi.tangent τ) (2 * τ)
    have htri' := abs_add_le t (Jacobi.tangent τ)
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at htri
    nlinarith [abs_nonneg τ, hprops.2.1]
  have hid : t ^ 2 + 2 * τ * t - 1 = (t - Jacobi.tangent τ) * (t + Jacobi.tangent τ + 2 * τ) := by
    nlinarith [hprops.2.2]
  rw [hid, abs_mul]
  have hmul := mul_le_mul he hfactor (abs_nonneg _) (div_nonneg hε hprops.1.le)
  apply hmul.trans
  have hd : |τ| + Real.sqrt (1 + τ ^ 2) ≠ 0 := ne_of_gt hprops.1
  field_simp
  rfl

/-- The errors in the pivot parameter and stable tangent compose into the
quadratic identity used by the diagonal energy update. -/
theorem pivot_polynomial_error (a b d τ t δ ε : ℝ)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hb : |b| ≤ 32) (ht : |t| ≤ 2)
    (hτ : |2 * b * τ - (d - a)| ≤ δ)
    (he : |t - Jacobi.tangent τ| ≤ ε / (|τ| + Real.sqrt (1 + τ ^ 2)))
    : |b * t ^ 2 + (d - a) * t - b| ≤ 160 * ε + 2 * δ := by
  have hquad := tangent_residual τ t ε hε ht he
  have hid : b * t ^ 2 + (d - a) * t - b =
      b * (t ^ 2 + 2 * τ * t - 1) - (2 * b * τ - (d - a)) * t := by ring
  rw [hid]
  apply (abs_sub _ _).trans
  have h1 := mul_le_mul hb hquad (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 32)
  have h2 := mul_le_mul hτ ht (abs_nonneg _) hδ
  rw [abs_mul, abs_mul]
  nlinarith

/-- Rounded diagonal writes transfer the pivot's squared energy up to a bound
on the quadratic residual and the two final arithmetic errors. -/
theorem diagonal_energy_error (a b d t A D δ ε : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ha : |a| ≤ 32) (hb : |b| ≤ 32) (hd : |d| ≤ 32) (ht : |t| ≤ 2)
    (hquad : |b * t ^ 2 + (d - a) * t - b| ≤ δ)
    (hA : |A - (a - t * b)| ≤ ε) (hD : |D - (d + t * b)| ≤ ε)
    : |A ^ 2 + D ^ 2 - (a ^ 2 + d ^ 2 + 2 * b ^ 2)| ≤ 64 * δ + 386 * ε := by
  have htb : |t * b| ≤ 64 := by rw [abs_mul]; nlinarith [abs_nonneg t, abs_nonneg b]
  have hap : |a - t * b| ≤ 96 := (abs_sub _ _).trans (by linarith)
  have hdp : |d + t * b| ≤ 96 := (abs_add_le _ _).trans (by linarith)
  have hab : |A| ≤ 97 := by
    have h := abs_sub_le A (a - t * b) 0
    simp only [sub_zero] at h
    linarith
  have hdb : |D| ≤ 97 := by
    have h := abs_sub_le D (d + t * b) 0
    simp only [sub_zero] at h
    linarith
  have hAe : |A ^ 2 - (a - t * b)^2| ≤ 193 * ε := by
    rw [sq_sub_sq, abs_mul]
    have hsum : |A + (a - t * b)| ≤ 193 := (abs_add_le _ _).trans (by linarith)
    have h := mul_le_mul hA hsum (abs_nonneg _) hε
    nlinarith
  have hDe : |D ^ 2 - (d + t * b)^2| ≤ 193 * ε := by
    rw [sq_sub_sq, abs_mul]
    have hsum : |D + (d + t * b)| ≤ 193 := (abs_add_le _ _).trans (by linarith)
    have h := mul_le_mul hD hsum (abs_nonneg _) hε
    nlinarith
  have hQ : |2 * b * (b * t ^ 2 + (d - a) * t - b)| ≤ 64 * δ := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h := mul_le_mul hb hquad (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 32)
    nlinarith
  have hid : A ^ 2 + D ^ 2 - (a ^ 2 + d ^ 2 + 2 * b ^ 2) =
      (A ^ 2 - (a - t * b)^2) + (D ^ 2 - (d + t * b)^2) +
        2 * b * (b * t ^ 2 + (d - a) * t - b) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hAe hDe)) hQ)
  |>.trans (by ring_nf; rfl)

end Flare.Analysis.JacobiDiagonal
