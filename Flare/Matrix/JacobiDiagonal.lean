import Flare.Analysis.JacobiDiagonal
import Flare.Matrix.JacobiIteration
import Flare.Matrix.JacobiPrecision

/-! Diagonal-rounding bounds for the native Jacobi pivot. These supply the
local energy estimate used to control iteration-wide magnitudes. -/

namespace Flare.Matrix.JacobiDiagonal

open Flare.Matrix.Value Flare.Binary64.Value
open Flare.Binary64.Arithmetic Flare.Binary64.Order

/-- The actual quotient residual retains the diagonal-difference scale and
an underflow allowance proportional to the selected pivot. -/
theorem pivot_parameter_relative (a b d : Float)
    (ha : a.isFinite = true) (hb : b.isFinite = true) (hd : d.isFinite = true)
    (hab : |value a| ≤ 32) (hbb : |value b| ≤ 32) (hdb : |value d| ≤ 32)
    (hbp : (2 : ℝ) ^ (-47 : Int) ≤ |value b|)
    : let u : ℝ := (2 : ℝ) ^ (-53 : Int)
      let τ := (d - a) / (2.0 * b)
      |2 * value b * value τ - (value d - value a)|
      ≤ 32 * u * |value d - value a| + u * |value b| := by
  let u : ℝ := (2 : ℝ)^(-53 : Int)
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  have hu : 0 ≤ u := by positivity
  have hη : η ≤ u * |value b| := by
    calc
      _ ≤ (2 : ℝ) ^ (-100 : Int) := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
      _ = u * (2 : ℝ) ^ (-47 : Int) := by dsimp [u]; rw [← zpow_add₀ (by norm_num)]; rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left hbp hu
  have htwo : value (2.0 : Float) = 2 := by
    change (((2^52 : Nat) : ℝ) * (2 : ℝ)^(-51 : Int)) = 2
    norm_num
  have hu4 : (2 : ℝ)^(-51 : Int) = 4 * u := by norm_num [u]
  have hu8 : (2 : ℝ)^(-50 : Int) = 8 * u := by norm_num [u]
  have hp : 0 < |value b| := (zpow_pos (by norm_num) _).trans_le hbp
  have hlarge : (64 : ℝ) ≤ (2 : ℝ)^(1000 : Int) := by
    exact (by norm_num : (64 : ℝ) ≤ (2 : ℝ)^(6 : Int)).trans
      (zpow_le_zpow_right₀ (by norm_num) (by norm_num))
  obtain ⟨hnf, hne⟩ := sub_error_relative d a hd ha (by
    apply (abs_sub _ _).trans
    exact (add_le_add hdb hab).trans ((by norm_num : (32 : ℝ) + 32 ≤ 64).trans hlarge))
  rw [hu4] at hne
  have hnb : |value (d - a)| ≤ |value d - value a| + 4 * u * (|value d - value a| + η) := by
    have h := abs_sub_le (value (d - a)) (value d - value a) 0
    simp only [sub_zero] at h
    exact (h.trans (add_le_add hne le_rfl)).trans_eq (by ring)
  have hnb128 : |value (d - a)| ≤ 128 := by
    have hΔ : |value d - value a| ≤ 64 := (abs_sub _ _).trans (by linarith only [hab, hdb])
    have hη1 : η ≤ 1 := hη.trans (by norm_num [u]; nlinarith only [hbb])
    apply hnb.trans
    have he := add_le_add hΔ (mul_le_mul_of_nonneg_left (add_le_add hΔ hη1) (by positivity : 0 ≤ 4 *
      u))
    exact he.trans (by norm_num [u])
  obtain ⟨hdf, hde⟩ := mul_error_relative 2.0 b (by decide) hb (by
    rw [htwo, abs_mul]
    exact (mul_le_mul_of_nonneg_left hbb (abs_nonneg (2 : ℝ))).trans
      ((by norm_num : |(2 : ℝ)| * 32 ≤ 64).trans hlarge))
  rw [htwo, hu4, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hde
  have hde' : |value (2.0 * b) - 2 * value b| ≤ 9 * u * |value b| := by
    apply hde.trans
    have he := mul_le_mul_of_nonneg_left (add_le_add (le_refl (2 * |value b|)) hη) (show 0 ≤ 4 * u
      by positivity)
    exact he.trans (by norm_num [u]; nlinarith only [abs_nonneg (value b)])
  have hdl : |value b| ≤ |value (2.0 * b)| := by
    have h := abs_sub_le (2 * value b) (value (2.0 * b)) 0
    simp only [sub_zero, abs_sub_comm (2 * value b) (value (2.0 * b)), abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
    norm_num [u] at hde'
    nlinarith only [h, hde', abs_nonneg (value b)]
  have hdpos : 0 < |value (2.0 * b)| := hp.trans_le hdl
  have hquot : |value (d - a) / value (2.0 * b)| ≤ (2 : ℝ)^(54 : Int) := by
    rw [abs_div]
    apply (div_le_iff₀ hdpos).mpr
    calc
      _ ≤ 128 := hnb128
      _ = (2 : ℝ) ^ (54 : Int) * (2 : ℝ) ^ (-47 : Int) := by norm_num
      _ ≤ (2 : ℝ) ^ (54 : Int) * |value b| := mul_le_mul_of_nonneg_left hbp (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hdl (by positivity)
  have hτ := Flare.Binary64.Division.div_error_relative (d - a) (2.0 * b) hnf hdf (abs_pos.mp hdpos)
    (hquot.trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)))
  rw [hu8] at hτ
  have hres := Flare.Analysis.JacobiDiagonal.scaled_quotient_relative (value (d - a)) (value (2.0 *
    b)) (value b)
    (value ((d - a) / (2.0 * b))) (9 * u) (8 * u) η (abs_pos.mp hp)
    (by positivity) (by norm_num [u]) (by positivity) (by positivity) hde' hτ.2
  have htri := (abs_sub_le (2 * value b * value ((d - a) / (2.0 * b)))
    (value (d - a)) (value d - value a)).trans (add_le_add hres hne)
  apply htri.trans
  change (9 * u + 2 * (8 * u)) * |value (d - a)| + 2 * (8 * u) * |value b| * η +
      4 * u * (|value d - value a| + η) ≤ _
  calc
    _ ≤ (9 * u + 2 * (8 * u))
          * (|value d - value a| + 4 * u * (|value d - value a| + u * |value b|))
        + 2 * (8 * u) * |value b| * (u * |value b|)
        + 4 * u * (|value d - value a| + u * |value b|) := by
      gcongr
      exact hnb.trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl hη) (by positivity)))
    _ ≤ _ := by
      have hB2 := mul_le_mul_of_nonneg_right hbb (abs_nonneg (value b))
      norm_num [u]
      nlinarith only [hB2, abs_nonneg (value b), abs_nonneg (value d - value a)]

/-- The complete native tangent schedule has a pivot-proportional polynomial
residual. This sharper estimate is used for spectral accuracy. -/
theorem pivot_polynomial_relative (a b d : Float)
    (ha : a.isFinite = true) (hb : b.isFinite = true) (hd : d.isFinite = true)
    (hab : |value a| ≤ 32) (hbb : |value b| ≤ 32) (hdb : |value d| ≤ 32)
    (hstop : (1.0e-14 : Float) < b.abs)
    : let τ := (d - a) / (2.0 * b)
      let t := (if τ < 0.0 then (-1.0 : Float) else 1.0) / (τ.abs + (1.0 + τ * τ).sqrt)
      |value b * (value t) ^ 2 + (value d - value a) * value t - value b|
      ≤ 256 * (2 : ℝ) ^ (-53 : Int) * |value b| := by
  have habs := abs_value b hb
  have hbp := (lt_iff (1.0e-14 : Float) b.abs (by decide) habs.1).mp hstop
  rw [habs.2] at hbp
  have hbscale := Jacobi.stopping_threshold_bounds.1.trans hbp.le
  have hparams := Jacobi.pivot_parameter_bounded a b d ha hb hd hab hbb hdb hbscale
  have ht := JacobiPrecision.tangent_precision ((d - a) / (2.0 * b)) hparams.2.2.2.1 hparams.2.2.2.2
  have ht2 := ht.2.2.trans (by norm_num : 1 + 22 * (2 : ℝ)^(-53 : Int) ≤ 2)
  have hprod := Flare.Analysis.JacobiDiagonal.tangent_product_bound _ _ _ (by positivity) ht.2.1
  have hquad := Flare.Analysis.JacobiDiagonal.tangent_residual _ _ _ (by positivity) ht2 ht.2.1
  have hquad' : |(_ : ℝ)^2 + 2 * value ((d - a) / (2.0 * b)) * _ - 1| ≤
      110 * (2 : ℝ)^(-53 : Int) := hquad.trans_eq (by ring)
  exact (Flare.Analysis.JacobiDiagonal.pivot_residual_relative (value a) (value b) (value d) _ _ _
          (by positivity) (by norm_num) ht2 hprod hquad'
          (pivot_parameter_relative a b d ha hb hd hab hbb hdb hbscale)).2

/-- The rounded pivot parameter satisfies a small scaled residual. A small
pivot may produce a large parameter; the residual remains uniformly controlled. -/
theorem pivot_parameter_residual (a b d : Float)
    (ha : a.isFinite = true) (hb : b.isFinite = true) (hd : d.isFinite = true)
    (hab : |value a| ≤ 32) (hbb : |value b| ≤ 32) (hdb : |value d| ≤ 32)
    (hbp : (2 : ℝ) ^ (-47 : Int) ≤ |value b|)
    : let τ := (d - a) / (2.0 * b)
      |2 * value b * value τ - (value d - value a)| ≤ (2 : ℝ) ^ (-38 : Int) := by
  have h := pivot_parameter_relative a b d ha hb hd hab hbb hdb hbp
  have hΔ : |value d - value a| ≤ 64 := (abs_sub _ _).trans (by linarith only [hab, hdb])
  exact h.trans
    ((add_le_add (mul_le_mul_of_nonneg_left hΔ (by positivity))
        (mul_le_mul_of_nonneg_left hbb (by positivity))).trans
      (by norm_num))

/-- The actual native tangent satisfies the diagonal update's quadratic
identity up to a uniform residual, derived from input bounds and stopping test. -/
theorem pivot_polynomial_residual (a b d : Float)
    (ha : a.isFinite = true) (hb : b.isFinite = true) (hd : d.isFinite = true)
    (hab : |value a| ≤ 32) (hbb : |value b| ≤ 32) (hdb : |value d| ≤ 32)
    (hstop : (1.0e-14 : Float) < b.abs)
    : let τ := (d - a) / (2.0 * b)
      let t := (if τ < 0.0 then (-1.0 : Float) else 1.0) / (τ.abs + (1.0 + τ * τ).sqrt)
      |value b * (value t) ^ 2 + (value d - value a) * value t - value b|
      ≤ (2 : ℝ) ^ (-35 : Int) := by
  exact (pivot_polynomial_relative a b d ha hb hd hab hbb hdb hstop).trans
    ((mul_le_mul_of_nonneg_left hbb (by positivity)).trans (by norm_num))

/-- The actual two diagonal writes transfer twice the squared pivot energy,
up to an absolute `2⁻²⁸` allowance. This coarse allowance is used to maintain
bounded iterates, separately from the spectral-accuracy proof. -/
theorem diagonal_energy (a b d : Float)
    (ha : a.isFinite = true) (hb : b.isFinite = true) (hd : d.isFinite = true)
    (hab : |value a| ≤ 32) (hbb : |value b| ≤ 32) (hdb : |value d| ≤ 32)
    (hstop : (1.0e-14 : Float) < b.abs)
    : let τ := (d - a) / (2.0 * b)
      let t := (if τ < 0.0 then (-1.0 : Float) else 1.0) / (τ.abs + (1.0 + τ * τ).sqrt)
      (a - t * b).isFinite = true
      ∧ (d + t * b).isFinite = true
      ∧ |(value (a - t * b)) ^ 2
          + (value (d + t * b)) ^ 2
          - ((value a) ^ 2 + (value d) ^ 2 + 2 * (value b) ^ 2)|
        ≤ (2 : ℝ) ^ (-28 : Int) := by
  have hparams := Jacobi.pivot_rotation_parameters a b d ha hb hd hab hbb hdb hstop
  have hquad := pivot_polynomial_residual a b d ha hb hd hab hbb hdb hstop
  have hdiag := JacobiIteration.diagonal_updates a b d _ ha hb hd hparams.2.1 hab hbb hdb
    hparams.2.2.2.2.1
  refine ⟨hdiag.1, hdiag.2.1, ?_⟩
  have he := Flare.Analysis.JacobiDiagonal.diagonal_energy_error (value a) (value b) (value d) _ _ _
    ((2 : ℝ)^(-35 : Int)) ((2 : ℝ)^(-43 : Int)) (by positivity) (by norm_num)
    hab hbb hdb hparams.2.2.2.2.1 hquad hdiag.2.2.1 hdiag.2.2.2
  exact he.trans (by norm_num)

end Flare.Matrix.JacobiDiagonal
