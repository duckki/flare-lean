import Flare.Matrix.Jacobi

/-! Tighter error estimates for the native Jacobi parameters. These preserve
the runtime expressions and use nearest-square-root rounding, with explicit
relative error and underflow terms, to reduce spectral error allowances. -/

namespace Flare.Matrix.JacobiPrecision
open Flare.Matrix.Value Flare.Binary64.Value Flare.Binary64.Arithmetic

/-- Both Jacobi square-root expressions satisfy a seven-unit relative bound,
including the large pivot parameter used by the stable tangent formula. -/
theorem root_precision (x : Float) (hx : x.isFinite = true) (hxb : |value x| ≤ (2 : ℝ) ^ (60 : Int))
    : (1.0 + x * x).sqrt.isFinite = true
      ∧ |value (1.0 + x * x).sqrt - Real.sqrt (1 + (value x) ^ 2)|
        ≤ 7 * (2 : ℝ) ^ (-53 : Int) * Real.sqrt (1 + (value x) ^ 2) := by
  let u : ℝ := (2 : ℝ)^(-53 : Int)
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  have hu : 0 ≤ u := by positivity
  have hu' : u ≤ 1 / 1000 := by norm_num [u]
  have hηu : η ≤ u := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hη1 : η ≤ 1 := hηu.trans (by norm_num [u])
  have hu4 : (2 : ℝ)^(-51 : Int) = 4 * u := by norm_num [u]
  have hxsq : (value x)^2 ≤ (2 : ℝ)^(120 : Int) := by
    have h := (sq_le_sq₀ (abs_nonneg (value x)) (show 0 ≤ (2 : ℝ)^(60 : Int) by positivity)).mpr hxb
    norm_num only [sq_abs, zpow_ofNat] at h ⊢
    convert h using 1
  have hprod : |value x * value x| ≤ (2 : ℝ)^(120 : Int) := by
    rw [← pow_two, abs_of_nonneg (sq_nonneg _)]; exact hxsq
  obtain ⟨hpf, hp⟩ := mul_error_relative x x hx hx
    (hprod.trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)))
  have hp' : |value (x * x) - (value x)^2| ≤ 4 * u * ((value x)^2 + η) := by
    simpa only [← pow_two, abs_of_nonneg (sq_nonneg (value x)), hu4] using hp
  have hpb : |value (x * x)| ≤ (2 : ℝ)^(121 : Int) := by
    have h := abs_sub_le (value (x * x)) ((value x)^2) 0
    simp only [sub_zero, abs_of_nonneg (sq_nonneg (value x))] at h
    have he := hp'.trans (mul_le_mul_of_nonneg_left (add_le_add hxsq hη1) (by positivity))
    norm_num [u] at he hxsq ⊢
    linarith
  have hsum : |value (1.0 : Float) + value (x * x)| ≤ (2 : ℝ)^(122 : Int) := by
    rw [one_value]
    exact (abs_add_le _ _).trans ((add_le_add (by norm_num : |(1 : ℝ)| ≤ 1) hpb).trans (by
      norm_num))
  obtain ⟨hqf, hq⟩ := add_error_relative 1.0 (x * x) (by decide) hpf
    (hsum.trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)))
  rw [one_value, hu4] at hq
  have hq' := Flare.Analysis.Jacobi.square_add_error ((value x)^2) (value (x * x))
    (value (1.0 + x * x)) u η (sq_nonneg _) hu hu' hηu hp' hq
  have hpositive := (Jacobi.root_one_add_square_accuracy x hx hxb).2.2.1
  have hpert := Flare.Analysis.Jacobi.sqrt_relative_sharp (1 + (value x)^2) (value (1.0 + x * x))
    (9 * u) (5 * u) (by positivity) hpositive.le (by positivity) (by norm_num [u])
    (by norm_num [u]) hq'
  have hsqrt := Flare.Binary64.Sqrt.sqrt_error_nearest (1.0 + x * x) hqf hpositive.le
  refine ⟨hsqrt.1, ?_⟩
  have hs : Real.sqrt (value (1.0 + x * x)) ≤
      (1 + 5 * u) * Real.sqrt (1 + (value x)^2) := by
    have h := (abs_le.mp hpert).2
    nlinarith only [h]
  have hsround := hsqrt.2.trans (mul_le_mul_of_nonneg_left hs hu)
  have h := (abs_sub_le (value (1.0 + x * x).sqrt) (Real.sqrt (value (1.0 + x * x)))
    (Real.sqrt (1 + (value x)^2))).trans (add_le_add hsround hpert)
  apply h.trans
  change u * ((1 + 5 * u) * Real.sqrt (1 + (value x)^2)) + 5 * u * Real.sqrt (1 + (value x)^2) ≤ _
  have hnonneg := Real.sqrt_nonneg (1 + (value x)^2)
  norm_num [u]
  nlinarith

/-- Specialization of the relative denominator bound to the computed tangent. -/
theorem root_small_precision (x : Float) (hx : x.isFinite = true) (hxb : |value x| ≤ 2)
    : (1.0 + x * x).sqrt.isFinite = true
      ∧ |value (1.0 + x * x).sqrt - Real.sqrt (1 + (value x) ^ 2)|
        ≤ 7 * (2 : ℝ) ^ (-53 : Int) * Real.sqrt (1 + (value x) ^ 2) :=
  root_precision x hx (hxb.trans (by norm_num))

/-- Rounded division of a unit-magnitude numerator by an approximate positive
denominator. A k-unit relative denominator error costs at most k+10 units in
the quotient, retaining the reciprocal scale. -/
theorem unit_div_precision (v b : Float) (a k : ℝ)
    (hv : v.isFinite = true) (hb : b.isFinite = true) (hvunit : |value v| = 1)
    (ha : 1 ≤ a) (ha' : a ≤ (2 : ℝ) ^ (64 : Int)) (hk : 0 ≤ k) (hk' : k ≤ 32)
    (he : |value b - a| ≤ k * (2 : ℝ) ^ (-53 : Int) * a)
    : (v / b).isFinite = true
      ∧ |value (v / b) - value v / a| ≤ (k + 10) * (2 : ℝ) ^ (-53 : Int) / a := by
  let u : ℝ := (2 : ℝ)^(-53 : Int)
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  have hu : 0 ≤ u := by positivity
  have ha0 : 0 < a := by linarith only [ha]
  have hk2 : k^2 ≤ 1024 := by nlinarith only [hk, hk']
  have hku : k * u < 1 := by norm_num [u]; linarith only [hk']
  have hrecipBudget : k * u ≤ ((k + 1) * u) * (1 - k * u) := by
    norm_num [u]
    nlinarith only [hk2, hk']
  obtain ⟨hb0, hrecip⟩ := Flare.Analysis.Jacobi.reciprocal_relative_sharp a (value b) (k * u) ((k +
    1) * u)
    ha0 hku (by positivity) hrecipBudget he
  have hbound : 1 / value b ≤ (1 + (k + 1) * u) / a := by
    have h := (abs_le.mp hrecip).2
    rw [add_div]
    linarith only [h]
  have hquot : |value v / value b| ≤ 2 := by
    rw [abs_div, hvunit, abs_of_pos hb0]
    apply hbound.trans
    apply (div_le_iff₀ ha0).mpr
    norm_num [u]
    linarith only [ha, hk']
  have hlarge : (2 : ℝ) ≤ (2 : ℝ)^(1000 : Int) := by
    simpa only [zpow_one]
      using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 : Int) ≤ 1000)
  obtain ⟨hf, herr⟩ := Flare.Binary64.Division.div_error_relative v b hv hb (ne_of_gt hb0)
    (hquot.trans hlarge)
  rw [abs_div, hvunit, abs_of_pos hb0] at herr
  have hηscale : η ≤ u / a := by
    apply (le_div_iff₀ ha0).mpr
    calc
      _ ≤ η * (2 : ℝ) ^ (64 : Int) := mul_le_mul_of_nonneg_left ha' (by positivity)
      _ = (2 : ℝ) ^ (-958 : Int) := by dsimp [η]; rw [← zpow_add₀ (by norm_num)]; rfl
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hu8 : (2 : ℝ)^(-50 : Int) = 8 * u := by norm_num [u]
  rw [hu8] at herr
  have hround : |value (v / b) - value v / value b| ≤ 9 * u / a := by
    apply herr.trans
    calc
      _ ≤ 8 * u * ((1 + (k + 1) * u) / a + u / a) :=
        mul_le_mul_of_nonneg_left (add_le_add hbound hηscale) (by positivity)
      _ = (8 * u * (1 + (k + 2) * u)) / a := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num [u]; linarith only [hk']) ha0.le
  have hperturb : |value v / value b - value v / a| ≤ (k + 1) * u / a := by
    rw [show value v / value b - value v / a = value v * (1 / value b - 1 / a) by ring,
      abs_mul, hvunit, one_mul]
    exact hrecip
  refine ⟨hf, ?_⟩
  exact ((abs_sub_le _ _ _).trans (add_le_add hround hperturb)).trans_eq (by ring)

/-- The computed cosine and sine approximate an exact unit rotation within
17 and 22 unit roundoffs respectively. The cosine error retains its reciprocal
scale, which avoids multiplying the sine error by the tangent magnitude. -/
theorem coefficients_precision (t : Float) (ht : t.isFinite = true) (htb : |value t| ≤ 2)
    : let u : ℝ := (2 : ℝ) ^ (-53 : Int)
      let a := Real.sqrt (1 + (value t) ^ 2)
      let c := 1.0 / (1.0 + t * t).sqrt
      let s := t * c
      c.isFinite = true
      ∧ s.isFinite = true
      ∧ |value c - 1 / a| ≤ 17 * u / a
      ∧ |value s - value t / a| ≤ 22 * u
      ∧ |value c| ≤ 1 + 22 * u
      ∧ |value s| ≤ 1 + 22 * u := by
  let u : ℝ := (2 : ℝ)^(-53 : Int)
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  let a := Real.sqrt (1 + (value t)^2)
  let r := (1.0 + t * t).sqrt
  let c := 1.0 / r
  have hu : 0 ≤ u := by positivity
  have hηu : η ≤ u := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have ha2 : a^2 = 1 + (value t)^2 := Real.sq_sqrt (by positivity)
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have ha : 1 ≤ a := by nlinarith [sq_nonneg (value t)]
  have ha' : a ≤ 3 := by nlinarith [sq_abs (value t), abs_nonneg (value t)]
  have hta : |value t| ≤ a := by nlinarith [sq_abs (value t), abs_nonneg (value t)]
  obtain ⟨hrf, hr⟩ := root_small_precision t ht htb
  obtain ⟨hcf, hce⟩ := unit_div_precision 1.0 r a 7 (by decide) hrf
    (by rw [one_value]; norm_num) ha (ha'.trans (by norm_num)) (by norm_num) (by norm_num) hr
  rw [one_value] at hce
  rw [show (7 : ℝ) + 10 = 17 by norm_num] at hce
  change |value c - 1 / a| ≤ 17 * u / a at hce
  have hlarge : (2 : ℝ) ≤ (2 : ℝ)^(1000 : Int) := by
    simpa only [zpow_one]
      using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 : Int) ≤ 1000)
  have hce' : |value c - 1 / a| ≤ 17 * u :=
    hce.trans (div_le_self (by positivity) ha)
  have htcerr : |value t * value c - value t / a| ≤ 17 * u := by
    rw [show value t * value c - value t / a = value t * (value c - 1 / a) by ring, abs_mul]
    calc
      _ ≤ |value t| * (17 * u / a) := mul_le_mul_of_nonneg_left hce (abs_nonneg _)
      _ ≤ a * (17 * u / a) := mul_le_mul_of_nonneg_right hta (by positivity)
      _ = _ := by field_simp
  have hta' : |value t / a| ≤ 1 := by
    rw [abs_div, abs_of_pos ha0]
    exact (div_le_one ha0).mpr hta
  have htc : |value t * value c| ≤ 1 + 17 * u := by
    have h := abs_sub_le (value t * value c) (value t / a) 0
    simp only [sub_zero] at h
    exact (h.trans (add_le_add htcerr hta')).trans_eq (by ring)
  obtain ⟨hsf, hs⟩ := mul_error_relative t c ht hcf
    (htc.trans ((by norm_num [u] : 1 + 17 * u ≤ 2).trans hlarge))
  have hu4 : (2 : ℝ)^(-51 : Int) = 4 * u := by norm_num [u]
  rw [hu4] at hs
  have hsround : |value (t * c) - value t * value c| ≤ 5 * u :=
    hs.trans ((mul_le_mul_of_nonneg_left (add_le_add htc hηu) (by positivity)).trans (by norm_num
      [u]))
  have hse : |value (t * c) - value t / a| ≤ 22 * u := by
    exact ((abs_sub_le _ _ _).trans (add_le_add hsround htcerr)).trans_eq (by ring)
  refine ⟨hcf, hsf, hce, hse, ?_, ?_⟩
  · have h := abs_sub_le (value c) (1 / a) 0
    rw [sub_zero, sub_zero, abs_of_pos (one_div_pos.mpr ha0)] at h
    have hunit : 1 / a ≤ 1 := (div_le_one ha0).mpr ha
    change |value c| ≤ 1 + 22 * u
    exact (h.trans (add_le_add hce' hunit)).trans (by nlinarith only [hu])
  · have h := abs_sub_le (value (t * c)) (value t / a) 0
    simp only [sub_zero] at h
    change |value (t * c)| ≤ 1 + 22 * u
    exact (h.trans (add_le_add hse hta')).trans_eq (by ring)

/-- The native stable tangent is within 22 unit roundoffs divided by its
positive denominator. This scale is essential for small rotations when the
pivot parameter is large; the sign convention includes zero. -/
theorem tangent_precision (τ : Float) (hτ : τ.isFinite = true)
    (hτb : |value τ| ≤ (2 : ℝ) ^ (60 : Int))
    : let D := |value τ| + Real.sqrt (1 + (value τ) ^ 2)
      let t := (if τ < 0.0 then (-1.0 : Float) else 1.0) / (τ.abs + (1.0 + τ * τ).sqrt)
      t.isFinite = true
      ∧ |value t - Flare.Analysis.Jacobi.tangent (value τ)| ≤ 22 * (2 : ℝ) ^ (-53 : Int) / D
      ∧ |value t| ≤ 1 + 22 * (2 : ℝ) ^ (-53 : Int) := by
  let u : ℝ := (2 : ℝ)^(-53 : Int)
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  let r := (1.0 + τ * τ).sqrt
  let D := |value τ| + Real.sqrt (1 + (value τ)^2)
  let v : Float := if τ < 0.0 then -1.0 else 1.0
  have hu : 0 ≤ u := by positivity
  have hηu : η ≤ u := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hroot := root_precision τ hτ hτb
  have hrootOne : 1 ≤ Real.sqrt (1 + (value τ)^2) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + (value τ)^2 by positivity)
    have hs0 := Real.sqrt_nonneg (1 + (value τ)^2)
    nlinarith [sq_nonneg (value τ)]
  have hD : 1 ≤ D := by dsimp [D]; linarith [abs_nonneg (value τ)]
  have hD0 : 0 < D := by linarith only [hD]
  have hrootBound : Real.sqrt (1 + (value τ)^2) ≤ (2 : ℝ)^(61 : Int) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + (value τ)^2 by positivity)
    have hb := (sq_le_sq₀ (abs_nonneg (value τ)) (show 0 ≤ (2 : ℝ)^(60 : Int) by positivity)).mpr
      hτb
    rw [sq_abs] at hb
    norm_num at hb ⊢
    nlinarith only [hs, hb]
  have hDb : D ≤ (2 : ℝ)^(63 : Int) := by
    dsimp [D]
    norm_num at hτb hrootBound ⊢
    linarith only [hτb, hrootBound]
  have hr : |value r - Real.sqrt (1 + (value τ)^2)| ≤ 7 * u * D :=
    hroot.2.trans (mul_le_mul_of_nonneg_left
      (show Real.sqrt (1 + (value τ)^2) ≤ D by dsimp [D]; linarith [abs_nonneg (value τ)]) (by
        positivity))
  obtain ⟨habsf, habs⟩ := Flare.Binary64.Order.abs_value τ hτ
  have hsum : |value τ.abs + value r| ≤ (1 + 7 * u) * D := by
    rw [habs]
    have he : |value τ| + value r = D + (value r - Real.sqrt (1 + (value τ)^2)) := by
      dsimp [D]; ring
    rw [he]
    exact ((abs_add_le _ _).trans (add_le_add (by rw [abs_of_pos hD0]) hr)).trans_eq (by ring)
  have hlarge : |value τ.abs + value r| ≤ (2 : ℝ)^(1000 : Int) := by
    calc
      _ ≤ 2 * D := hsum.trans (mul_le_mul_of_nonneg_right (by norm_num [u]) hD0.le)
      _ ≤ 2 * (2 : ℝ) ^ (63 : Int) := mul_le_mul_of_nonneg_left hDb (by norm_num)
      _ = (2 : ℝ) ^ (64 : Int) := by norm_num
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  obtain ⟨hbf, hb⟩ := add_error_relative τ.abs r habsf hroot.1 hlarge
  have hu4 : (2 : ℝ)^(-51 : Int) = 4 * u := by norm_num [u]
  rw [hu4] at hb
  have hηD : η ≤ u * D := hηu.trans (by nlinarith [mul_le_mul_of_nonneg_left hD hu])
  have hb' : |value (τ.abs + r) - (value τ.abs + value r)| ≤ 5 * u * D := by
    apply hb.trans
    calc
      _ ≤ 4 * u * ((1 + 7 * u) * D + u * D) :=
        mul_le_mul_of_nonneg_left (add_le_add hsum hηD) (by positivity)
      _ ≤ _ := by norm_num [u]; nlinarith only [hD0]
  have hden : |value (τ.abs + r) - D| ≤ 12 * u * D := by
    have he : |(value τ.abs + value r) - D| = |value r - Real.sqrt (1 + (value τ)^2)| := by
      rw [habs]
      dsimp [D]
      congr 1
      ring
    have h := abs_sub_le (value (τ.abs + r)) (value τ.abs + value r) D
    rw [he] at h
    exact (h.trans (add_le_add hb' hr)).trans_eq (by ring)
  have hvf : v.isFinite = true := by dsimp [v]; split <;> decide
  have hneg : value (-1.0 : Float) = -1 := by
    simpa only [one_value] using (Flare.Binary64.Order.neg_value 1.0 (by decide)).2
  have hvunit : |value v| = 1 := by dsimp [v]; split <;> simp [hneg, one_value]
  obtain ⟨htf, ht⟩ := unit_div_precision v (τ.abs + r) D 12 hvf hbf hvunit hD
    (hDb.trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num))) (by norm_num) (by norm_num) hden
  have hvreal : value v = if value τ < 0 then -1 else 1 := by
    have hcmp := Flare.Binary64.Order.lt_iff τ 0.0 hτ (by decide)
    rw [zero_value] at hcmp
    dsimp [v]
    split_ifs with hlt hlt' hlt' <;> simp_all [one_value]
  rw [hvreal] at ht
  change |value (v / (τ.abs + r)) - Flare.Analysis.Jacobi.tangent (value τ)| ≤ (12 + 10) * u / D
    at ht
  have ht' : |value (v / (τ.abs + r)) - Flare.Analysis.Jacobi.tangent (value τ)| ≤ 22 * u / D := by
    convert ht using 1
    norm_num
  refine ⟨htf, ht', ?_⟩
  have hunit := (Flare.Analysis.Jacobi.tangent_properties (value τ)).2.1
  have he := ht'.trans (div_le_self (by positivity) hD)
  have h := abs_sub_le (value (v / (τ.abs + r))) (Flare.Analysis.Jacobi.tangent (value τ)) 0
  simp only [sub_zero] at h
  exact (h.trans (add_le_add he hunit)).trans_eq (by ring)

/-- The two diagonal shortcuts have thirteen-unit absolute error relative to
their exact expressions. M bounds each input magnitude plus underflow. -/
theorem diagonal_precision (a b d t : Float) (M : ℝ)
    (ha : a.isFinite = true) (hb : b.isFinite = true) (hd : d.isFinite = true)
    (ht : t.isFinite = true) (htb : |value t| ≤ 1 + 22 * (2 : ℝ) ^ (-53 : Int))
    (haM : |value a| + (2 : ℝ) ^ (-1022 : Int) ≤ M)
    (hbM : |value b| + (2 : ℝ) ^ (-1022 : Int) ≤ M)
    (hdM : |value d| + (2 : ℝ) ^ (-1022 : Int) ≤ M)
    (hM : M ≤ (2 : ℝ) ^ (500 : Int))
    : (a - t * b).isFinite = true
      ∧ (d + t * b).isFinite = true
      ∧ |value (a - t * b) - (value a - value t * value b)| ≤ 13 * (2 : ℝ) ^ (-53 : Int) * M
      ∧ |value (d + t * b) - (value d + value t * value b)| ≤ 13 * (2 : ℝ) ^ (-53 : Int) * M := by
  let u : ℝ := (2 : ℝ)^(-53 : Int)
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  let E := 4 * u * (1 + 22 * u) * M
  have hu : 0 ≤ u := by positivity
  have hη : 0 ≤ η := by positivity
  have hM0 : 0 ≤ M := (add_nonneg (abs_nonneg _) hη).trans hbM
  have hu4 : (2 : ℝ)^(-51 : Int) = 4 * u := by norm_num [u]
  have hprod : |value t * value b| + η ≤ (1 + 22 * u) * M := by
    rw [abs_mul]
    calc
      _ ≤ (1 + 22 * u) * |value b| + η :=
        add_le_add (mul_le_mul_of_nonneg_right htb (abs_nonneg _)) le_rfl
      _ ≤ (1 + 22 * u) * (|value b| + η) := by nlinarith only [mul_nonneg hu hη]
      _ ≤ _ := mul_le_mul_of_nonneg_left hbM (by positivity)
  have h4M : 4 * M ≤ (2 : ℝ)^(1000 : Int) := by
    calc
      _ ≤ 4 * (2 : ℝ) ^ (500 : Int) := mul_le_mul_of_nonneg_left hM (by norm_num)
      _ = (2 : ℝ) ^ (502 : Int) := by
        rw [show (4 : ℝ) = (2 : ℝ)^(2 : Int) by norm_num, ← zpow_add₀ (by norm_num)]
        rfl
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hprodLarge : |value t * value b| ≤ (2 : ℝ)^(1000 : Int) := by
    have h := (le_add_of_nonneg_right hη).trans hprod
    exact h.trans ((mul_le_mul_of_nonneg_right (by norm_num [u] : 1 + 22 * u ≤ 4) hM0).trans h4M)
  obtain ⟨hpf, hp⟩ := mul_error_relative t b ht hb hprodLarge
  rw [hu4] at hp
  have hp' : |value (t * b) - value t * value b| ≤ E :=
    (hp.trans (mul_le_mul_of_nonneg_left hprod (by positivity))).trans_eq (by dsimp [E]; ring)
  have hpb : |value (t * b)| ≤ (1 + 22 * u) * M + E := by
    have h := abs_sub_le (value (t * b)) (value t * value b) 0
    simp only [sub_zero] at h
    exact (h.trans (add_le_add hp' ((le_add_of_nonneg_right hη).trans hprod))).trans_eq (by ring)
  have hsuma : |value a - value (t * b)| + η ≤ (2 + 22 * u) * M + E := by
    have h := add_le_add (abs_sub (value a) (value (t * b))) (le_refl η)
    have he := add_le_add haM hpb
    linarith only [h, he]
  have hsumd : |value d + value (t * b)| + η ≤ (2 + 22 * u) * M + E := by
    have h := add_le_add (abs_add_le (value d) (value (t * b))) (le_refl η)
    have he := add_le_add hdM hpb
    linarith only [h, he]
  have hsumLarge : (2 + 22 * u) * M + E ≤ (2 : ℝ)^(1000 : Int) := by
    apply le_trans (b := 4 * M) _ h4M
    dsimp [E]
    norm_num [u]
    nlinarith only [hM0]
  obtain ⟨haf, hae⟩ := sub_error_relative a (t * b) ha hpf
    (((le_add_of_nonneg_right hη).trans hsuma).trans hsumLarge)
  obtain ⟨hdf, hde⟩ := add_error_relative d (t * b) hd hpf
    (((le_add_of_nonneg_right hη).trans hsumd).trans hsumLarge)
  rw [hu4] at hae hde
  have hae' := hae.trans (mul_le_mul_of_nonneg_left hsuma (by positivity : 0 ≤ 4 * u))
  have hde' := hde.trans (mul_le_mul_of_nonneg_left hsumd (by positivity : 0 ≤ 4 * u))
  have hbound : 4 * u * ((2 + 22 * u) * M + E) + E ≤ 13 * u * M := by
    dsimp [E]
    norm_num [u]
    nlinarith only [hM0]
  refine ⟨haf, hdf, ?_, ?_⟩
  · have he : |(value a - value (t * b)) - (value a - value t * value b)| ≤ E := by
      rw [show (value a - value (t * b)) - (value a - value t * value b) =
        -(value (t * b) - value t * value b) by ring, abs_neg]
      exact hp'
    exact ((abs_sub_le _ _ _).trans (add_le_add hae' he)).trans hbound
  · have he : |(value d + value (t * b)) - (value d + value t * value b)| ≤ E := by
      rw [show (value d + value (t * b)) - (value d + value t * value b) =
        value (t * b) - value t * value b by ring]
      exact hp'
    exact ((abs_sub_le _ _ _).trans (add_le_add hde' he)).trans hbound

/-- Both native pair updates approximate the same exactly orthogonal rotation
within 32 unit roundoffs times the pair's input magnitude plus underflow.
The proof retains the shared input magnitude across both products and the
final addition/subtraction instead of bounding every term by the whole pair. -/
theorem pair_precision (t x y : Float) (M : ℝ)
    (ht : t.isFinite = true) (htb : |value t| ≤ 2)
    (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hM : |value x| + |value y| + (2 : ℝ) ^ (-1022 : Int) ≤ M)
    (hM' : M ≤ (2 : ℝ) ^ (500 : Int))
    : let c := 1.0 / (1.0 + t * t).sqrt
      let s := t * c
      let a := Real.sqrt (1 + (value t) ^ 2)
      |value (c * x - s * y) - ((1 / a) * value x - (value t / a) * value y)|
        ≤ (2 : ℝ) ^ (-48 : Int) * M
      ∧ |value (s * x + c * y) - ((value t / a) * value x + (1 / a) * value y)|
        ≤ (2 : ℝ) ^ (-48 : Int) * M := by
  let u : ℝ := (2 : ℝ)^(-53 : Int)
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  let X := |value x| + |value y|
  let E := 4 * u * ((1 + 22 * u) * X + 2 * η)
  let a := Real.sqrt (1 + (value t)^2)
  let c := 1.0 / (1.0 + t * t).sqrt
  let s := t * c
  have hu : 0 ≤ u := by positivity
  have hη : 0 ≤ η := by positivity
  have hX : 0 ≤ X := by positivity
  have hM0 : 0 ≤ M := (add_nonneg hX hη).trans hM
  have hXM : X ≤ M := by change X + η ≤ M at hM; linarith only [hM, hη]
  have hηM : η ≤ M := by change X + η ≤ M at hM; linarith only [hM, hX]
  have hlarge : 2 * M ≤ (2 : ℝ)^(1000 : Int) := by
    calc
      _ ≤ 2 * (2 : ℝ) ^ (500 : Int) := mul_le_mul_of_nonneg_left hM' (by norm_num)
      _ = (2 : ℝ) ^ (501 : Int) := by
        rw [show (501 : Int) = 1 + 500 by rfl, zpow_add₀ (by norm_num), zpow_one]
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hcoeff : 1 + 22 * u ≤ 2 := by norm_num [u]
  obtain ⟨hcf, hsf, hc, hs, hcb, hsb⟩ := coefficients_precision t ht htb
  have hu4 : (2 : ℝ)^(-51 : Int) = 4 * u := by norm_num [u]
  have term (b z : Float) (hbf : b.isFinite = true) (hzf : z.isFinite = true)
      (hbb : |value b| ≤ 1 + 22 * u) (hzb : |value z| ≤ M) :
      (b * z).isFinite = true ∧
      |value (b * z) - value b * value z| ≤ 4 * u * ((1 + 22 * u) * |value z| + η) := by
    have hprod : |value b * value z| ≤ (1 + 22 * u) * |value z| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hbb (abs_nonneg _)
    have hpM : |value b * value z| ≤ 2 * M :=
      hprod.trans (mul_le_mul hcoeff hzb (abs_nonneg _) (by norm_num))
    obtain ⟨hf, herr⟩ := mul_error_relative b z hbf hzf (hpM.trans hlarge)
    rw [hu4] at herr
    exact ⟨hf, herr.trans (mul_le_mul_of_nonneg_left (add_le_add hprod le_rfl) (by positivity))⟩
  have hxm : |value x| ≤ M := (le_add_of_nonneg_right (abs_nonneg (value y))).trans hXM
  have hym : |value y| ≤ M := (le_add_of_nonneg_left (abs_nonneg (value x))).trans hXM
  obtain ⟨hcxf, hcx⟩ := term c x hcf hx hcb hxm
  obtain ⟨hsyf, hsy⟩ := term s y hsf hy hsb hym
  obtain ⟨hsxf, hsx⟩ := term s x hsf hx hsb hxm
  obtain ⟨hcyf, hcy⟩ := term c y hcf hy hcb hym
  have sum_error (p q bp bq : Float)
      (hp : |value p - value bp * value x| ≤ 4 * u * ((1 + 22 * u) * |value x| + η))
      (hq : |value q - value bq * value y| ≤ 4 * u * ((1 + 22 * u) * |value y| + η)) :
      |value p - value bp * value x| + |value q - value bq * value y| ≤ E := by
    exact (add_le_add hp hq).trans_eq (by dsimp [E, X]; ring)
  have hpError := sum_error (c * x) (s * y) c s hcx hsy
  have hqError := sum_error (s * x) (c * y) s c hsx hcy
  have pair_magnitude (p q bp bq : Float)
      (hp : |value bp| ≤ 1 + 22 * u) (hq : |value bq| ≤ 1 + 22 * u)
      (herr : |value p - value bp * value x| + |value q - value bq * value y| ≤ E) :
      |value p| + |value q| ≤ (1 + 22 * u) * X + E := by
    have hP := abs_sub_le (value p) (value bp * value x) 0
    have hQ := abs_sub_le (value q) (value bq * value y) 0
    simp only [sub_zero, abs_mul] at hP hQ
    have hb := add_le_add (mul_le_mul_of_nonneg_right hp (abs_nonneg (value x)))
      (mul_le_mul_of_nonneg_right hq (abs_nonneg (value y)))
    have he : (1 + 22 * u) * |value x| + (1 + 22 * u) * |value y| = (1 + 22 * u) * X := by
      dsimp [X]; ring
    rw [he] at hb
    linarith only [hP, hQ, hb, herr]
  have hpm := pair_magnitude (c * x) (s * y) c s hcb hsb hpError
  have hqm := pair_magnitude (s * x) (c * y) s c hsb hcb hqError
  have hmagBound : (1 + 22 * u) * X + E ≤ 2 * M := by
    have hX' := mul_le_mul_of_nonneg_left hXM (show 0 ≤ 1 + 22 * u by positivity)
    have hη' := mul_le_mul_of_nonneg_left hηM (show (0 : ℝ) ≤ 2 by norm_num)
    have hE := mul_le_mul_of_nonneg_left (add_le_add hX' hη') (show 0 ≤ 4 * u by positivity)
    apply (add_le_add hX' hE).trans
    norm_num [u]
    nlinarith only [hM0]
  obtain ⟨_, hpRound⟩ := sub_error_relative (c * x) (s * y) hcxf hsyf
    (((abs_sub _ _).trans hpm).trans (hmagBound.trans hlarge))
  obtain ⟨_, hqRound⟩ := add_error_relative (s * x) (c * y) hsxf hcyf
    (((abs_add_le _ _).trans hqm).trans (hmagBound.trans hlarge))
  rw [hu4] at hpRound hqRound
  have hpRound' := hpRound.trans (mul_le_mul_of_nonneg_left
    (add_le_add ((abs_sub _ _).trans hpm) le_rfl) (show 0 ≤ 4 * u by positivity))
  have hqRound' := hqRound.trans (mul_le_mul_of_nonneg_left
    (add_le_add ((abs_add_le _ _).trans hqm) le_rfl) (show 0 ≤ 4 * u by positivity))
  have hce : |value c - 1 / a| ≤ 22 * u := by
    have ha : 1 ≤ a := by
      have hsq := Real.sq_sqrt (show 0 ≤ 1 + (value t)^2 by positivity)
      have hpos := Real.sqrt_nonneg (1 + (value t)^2)
      nlinarith [sq_nonneg (value t)]
    exact (hc.trans (div_le_self (by positivity) ha)).trans (by nlinarith only [hu])
  have coefficient (b b₀ z : ℝ) (hb : |b - b₀| ≤ 22 * u) :
      |b * z - b₀ * z| ≤ 22 * u * |z| := by
    rw [← sub_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have hcX := coefficient (value c) (1 / a) (value x) hce
  have hsY := coefficient (value s) (value t / a) (value y) hs
  have hsX := coefficient (value s) (value t / a) (value x) hs
  have hcY := coefficient (value c) (1 / a) (value y) hce
  have hps
      : |(value (c * x) - value (s * y)) - ((1 / a) * value x - (value t / a) * value y)|
        ≤ E + 22 * u * X := by
    have he
        : (value (c * x) - value (s * y)) - ((1 / a) * value x - (value t / a) * value y)
          = ((value (c * x) - value c * value x) - (value (s * y) - value s * value y))
            + ((value c * value x - (1 / a) * value x)
                - (value s * value y - (value t / a) * value y)) := by
      ring
    rw [he]
    exact ((abs_add_le _ _).trans
            (add_le_add ((abs_sub _ _).trans hpError)
              ((abs_sub _ _).trans (add_le_add hcX hsY)))).trans_eq
      (by dsimp [X]; ring)
  have hqs
      : |(value (s * x) + value (c * y)) - ((value t / a) * value x + (1 / a) * value y)|
        ≤ E + 22 * u * X := by
    have he
        : (value (s * x) + value (c * y)) - ((value t / a) * value x + (1 / a) * value y)
          = ((value (s * x) - value s * value x) + (value (c * y) - value c * value y))
            + ((value s * value x - (value t / a) * value x)
                + (value c * value y - (1 / a) * value y)) := by
      ring
    rw [he]
    exact ((abs_add_le _ _).trans
            (add_le_add ((abs_add_le _ _).trans hqError)
              ((abs_add_le _ _).trans (add_le_add hsX hcY)))).trans_eq
      (by dsimp [X]; ring)
  have hbudget
      : 4 * u * ((1 + 22 * u) * X + E + η) + (E + 22 * u * X) ≤ (2 : ℝ) ^ (-48 : Int) * M := by
    have hsmall : 4 * u * ((1 + 22 * u) * X + E + η) + (E + 22 * u * X) ≤
        (2 : ℝ)^(-48 : Int) * (X + η) := by
      dsimp only [E]
      norm_num [u]
      nlinarith only [hX, hη]
    exact hsmall.trans (mul_le_mul_of_nonneg_left hM (by positivity))
  constructor
  · exact ((abs_sub_le _ _ _).trans (add_le_add hpRound' hps)).trans hbudget
  · exact ((abs_sub_le _ _ _).trans (add_le_add hqRound' hqs)).trans hbudget

end Flare.Matrix.JacobiPrecision
