import Flare.Matrix.Spectrum
import Flare.Binary64.Sqrt
import Flare.Analysis.Jacobi

/-! Error bounds for the actual scalar expressions in the native Jacobi
iteration. These lemmas cover both the matrix-entry and eigenvector updates.
JacobiIteration connects them to the native loops; the Jacobi convergence and
spectral bounds support the pseudoinverse proof. -/

namespace Flare.Matrix.Jacobi
open Flare.Matrix.Value Flare.Binary64.Value Flare.Binary64.Arithmetic

private lemma sub_propagation (a b targetA targetB ea eb er : ℝ)
    (ha : |a - targetA| ≤ ea) (hb : |b - targetB| ≤ eb)
    (r : ℝ) (hr : |r - (a - b)| ≤ er)
    : |r - (targetA - targetB)| ≤ er + ea + eb := by
  have he : (a - b) - (targetA - targetB) = (a - targetA) - (b - targetB) := by ring
  have h := abs_sub_le r (a - b) (targetA - targetB)
  rw [he] at h
  linarith [abs_sub (a - targetA) (b - targetB)]

private lemma add_propagation (a b targetA targetB ea eb er : ℝ)
    (ha : |a - targetA| ≤ ea) (hb : |b - targetB| ≤ eb)
    (r : ℝ) (hr : |r - (a + b)| ≤ er)
    : |r - (targetA + targetB)| ≤ er + ea + eb := by
  have he : (a + b) - (targetA + targetB) = (a - targetA) + (b - targetB) := by ring
  have h := abs_sub_le r (a + b) (targetA + targetB)
  rw [he] at h
  linarith [abs_add_le (a - targetA) (b - targetB)]

/-- Both rounded multiply/add expressions in a Jacobi pair update succeed.
The bound is relative to the magnitudes of the two updated entries, with an
explicit underflow allowance. It does not depend on the diagonal magnitude of
the entire matrix, which is essential when off-diagonal entries become small. -/
theorem pair_update_accuracy (c s x y : Float) (M : ℝ)
    (hc : c.isFinite = true) (hs : s.isFinite = true)
    (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hcb : |value c| ≤ 2) (hsb : |value s| ≤ 2)
    (hM : |value x| + |value y| + (2 : ℝ)^(-1022 : Int) ≤ M)
    (hM' : M ≤ (2 : ℝ)^(500 : Int))
    : (c * x - s * y).isFinite = true
      ∧ (s * x + c * y).isFinite = true
      ∧ |value (c * x - s * y) - (value c * value x - value s * value y)| ≤ (2 : ℝ)^(-47 : Int) * M
      ∧ |value (s * x + c * y) - (value s * value x + value c * value y)|
        ≤ (2 : ℝ)^(-47 : Int) * M := by
  let u : ℝ := (2 : ℝ)^(-51 : Int)
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  have hu : 0 ≤ u := zpow_nonneg (by norm_num) _
  have hη : 0 ≤ η := zpow_nonneg (by norm_num) _
  have hηM : η ≤ M := by dsimp [η]; linarith [abs_nonneg (value x), abs_nonneg (value y)]
  have hM0 : 0 ≤ M := hη.trans hηM
  have hxm : |value x| ≤ M := by linarith [abs_nonneg (value y)]
  have hym : |value y| ≤ M := by linarith [abs_nonneg (value x)]
  have hbig : 4 * M ≤ (2 : ℝ)^(1000 : Int) := by
    calc
      _ ≤ 4 * (2 : ℝ)^(500 : Int) := mul_le_mul_of_nonneg_left hM' (by norm_num)
      _ = (2 : ℝ)^(502 : Int) := by
        rw [show (502 : Int) = 2 + 500 by rfl, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have term (a b : Float) (haf : a.isFinite = true) (hbf : b.isFinite = true)
      (hab : |value a| ≤ 2) (hbb : |value b| ≤ M) :
      (a * b).isFinite = true ∧
        |value (a * b) - value a * value b| ≤ 3 * u * M ∧
        |value (a * b)| ≤ 3 * M := by
    have he : |value a * value b| ≤ 2 * M := by
      rw [abs_mul]
      exact mul_le_mul hab hbb (abs_nonneg _) (by norm_num)
    obtain ⟨hf, herr⟩ := mul_error_relative a b haf hbf (he.trans ((mul_le_mul_of_nonneg_right (by
      norm_num : (2 : ℝ) ≤ 4) hM0).trans hbig))
    have hb : |value (a * b) - value a * value b| ≤ 3 * u * M := by
      apply herr.trans
      change u * (|value a * value b| + η) ≤ _
      nlinarith [mul_le_mul_of_nonneg_left he hu, mul_le_mul_of_nonneg_left hηM hu]
    refine ⟨hf, hb, ?_⟩
    have htri := abs_sub_le (value (a * b)) (value a * value b) 0
    simp only [sub_zero] at htri
    norm_num [u] at hb
    linarith
  obtain ⟨hcx, hecx, hbcx⟩ := term c x hc hx hcb hxm
  obtain ⟨hsy, hesy, hbsy⟩ := term s y hs hy hsb hym
  obtain ⟨hsx, hesx, hbsx⟩ := term s x hs hx hsb hxm
  obtain ⟨hcy,hecy,hbcy⟩ := term c y hc hy hcb hym
  have pair_bound (a b v w : Float)
      (hev : |value a - value v * value x| ≤ 3 * u * M)
      (hew : |value b - value w * value y| ≤ 3 * u * M)
      (hv : |value v| ≤ 2) (hw : |value w| ≤ 2) :
      |value a| + |value b| ≤ 3 * M := by
    have ha := abs_sub_le (value a) (value v * value x) 0
    have hb := abs_sub_le (value b) (value w * value y) 0
    simp only [sub_zero] at ha hb
    have hva : |value v * value x| ≤ 2 * |value x| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hv (abs_nonneg _)
    have hwa : |value w * value y| ≤ 2 * |value y| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hw (abs_nonneg _)
    norm_num [u] at hev hew
    linarith
  have hpair := pair_bound (c * x) (s * y) c s hecx hesy hcb hsb
  have hpair' := pair_bound (s * x) (c * y) s c hesx hecy hsb hcb
  have hsubb := (abs_sub (value (c * x)) (value (s * y))).trans hpair
  have haddb := (abs_add_le (value (s * x)) (value (c * y))).trans hpair'
  obtain ⟨hsubf, hsub⟩ := sub_error_relative (c * x) (s * y) hcx hsy (hsubb.trans
    ((mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 4) hM0).trans hbig))
  obtain ⟨haddf, hadd⟩ := add_error_relative (s * x) (c * y) hsx hcy (haddb.trans
    ((mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 4) hM0).trans hbig))
  have hsub' : |value (c * x - s * y) - (value (c * x) - value (s * y))| ≤ 4 * u * M := by
    apply hsub.trans
    change u * (_ + η) ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hsubb hu, mul_le_mul_of_nonneg_left hηM hu]
  have hadd' : |value (s * x + c * y) - (value (s * x) + value (c * y))| ≤ 4 * u * M := by
    apply hadd.trans
    change u * (_ + η) ≤ _
    nlinarith [mul_le_mul_of_nonneg_left haddb hu, mul_le_mul_of_nonneg_left hηM hu]
  refine ⟨hsubf, haddf, ?_, ?_⟩
  · have h := sub_propagation _ _ _ _ _ _ _ hecx hesy _ hsub'
    apply h.trans
    norm_num [u]
    linarith
  · have h := add_propagation _ _ _ _ _ _ _ hesx hecy _ hadd'
    apply h.trans
    norm_num [u]
    linarith

/-- Both occurrences of `sqrt (1 + x*x)` in the Jacobi parameter calculation
succeed and have relative error at most 2⁻⁴⁸ against the corresponding real
expression. The proof includes the two arithmetic roundings before square root. -/
theorem root_one_add_square_accuracy (x : Float) (hx : x.isFinite = true)
    (hxb : |value x| ≤ (2 : ℝ)^(60 : Int))
    : (1.0 + x * x).isFinite = true
      ∧ (1.0 + x * x).sqrt.isFinite = true
      ∧ 0 < value (1.0 + x * x)
      ∧ |value (1.0 + x * x).sqrt - Real.sqrt (1 + (value x)^2)|
        ≤ (2 : ℝ)^(-48 : Int) * Real.sqrt (1 + (value x)^2) := by
  let β := 1 + (value x)^2
  let u : ℝ := (2 : ℝ)^(-51 : Int)
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  have hu : 0 ≤ u := zpow_nonneg (by norm_num) _
  have hη : 0 ≤ η := zpow_nonneg (by norm_num) _
  have hη1 : η ≤ 1 := by
    dsimp [η]
    exact (zpow_le_one_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr (by norm_num)
  have hβ : 1 ≤ β := by dsimp [β]; nlinarith [sq_nonneg (value x)]
  have hβpos : 0 < β := by linarith
  have hβbound : β ≤ (2 : ℝ)^(122 : Int) := by
    have h := (sq_le_sq₀ (abs_nonneg (value x)) (by positivity : 0 ≤ (2 : ℝ)^(60 : Int))).mpr hxb
    rw [sq_abs] at h
    norm_num [β] at h ⊢
    linarith
  have hlimit : (2 : ℝ)^(124 : Int) ≤ (2 : ℝ)^(1000 : Int) :=
    zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  obtain ⟨hxf, herrx⟩ := mul_error_relative x x hx hx (by
    rw [← pow_two, abs_of_nonneg (sq_nonneg _)]
    apply le_trans (b := (2 : ℝ)^(124 : Int)) _ hlimit
    norm_num [β] at hβbound ⊢
    linarith)
  have herrx' : |value (x * x) - (value x)^2| ≤ u * β := by
    rw [← pow_two] at herrx
    apply herrx.trans
    rw [abs_of_nonneg (sq_nonneg _)]
    change u * ((value x)^2 + η) ≤ u * β
    exact mul_le_mul_of_nonneg_left (by dsimp [β]; linarith) hu
  have hq : |value 1.0 + value (x * x)| ≤ 2 * β := by
    rw [one_value]
    have he : (1 : ℝ) + value (x * x) = β + (value (x * x) - (value x)^2) := by dsimp [β]; ring
    rw [he]
    have h := abs_add_le β (value (x * x) - (value x)^2)
    rw [abs_of_pos hβpos] at h
    norm_num [u] at herrx'
    linarith
  obtain ⟨hqf, herrq⟩ := add_error_relative 1.0 (x * x) (by decide) hxf (hq.trans (by
    apply le_trans (b := (2 : ℝ)^(124 : Int)) _ hlimit
    norm_num at hβbound ⊢
    linarith))
  have herrq' : |value (1.0 + x * x) - (1 + value (x * x))| ≤ 3 * u * β := by
    rw [one_value] at herrq hq
    apply herrq.trans
    change u * (_ + η) ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hq hu,
      mul_le_mul_of_nonneg_left (hη1.trans hβ) hu]
  have herrβ : |value (1.0 + x * x) - β| ≤ (2 : ℝ)^(-49 : Int) * β := by
    have he : |(1 + value (x * x)) - β| = |value (x * x) - (value x)^2| := by
      dsimp [β]
      congr 1
      ring
    have h := abs_sub_le (value (1.0 + x * x)) (1 + value (x * x)) β
    rw [he] at h
    norm_num [u] at herrx' herrq' ⊢
    linarith
  have hqpos : 0 < value (1.0 + x * x) := by
    have h := (abs_le.mp herrβ).1
    norm_num at h
    linarith
  have hroot := Flare.Analysis.Jacobi.sqrt_relative_perturbation β (value (1.0 + x * x))
    ((2 : ℝ)^(-49 : Int)) hβpos hqpos.le (by positivity) herrβ
  obtain ⟨hrf, herrr⟩ := Flare.Binary64.Sqrt.sqrt_error (1.0 + x * x) hqf hqpos.le
  have hro : Real.sqrt (value (1.0 + x * x)) ≤ 2 * Real.sqrt β := by
    have h := (abs_le.mp hroot).2
    norm_num at h
    linarith [Real.sqrt_nonneg β]
  refine ⟨hqf, hrf, hqpos, ?_⟩
  change |value (1.0 + x * x).sqrt - Real.sqrt β| ≤ _
  have h := abs_sub_le (value (1.0 + x * x).sqrt) (Real.sqrt (value (1.0 + x * x))) (Real.sqrt β)
  have he := mul_le_mul_of_nonneg_left hro (by positivity : 0 ≤ (2 : ℝ)^(-50 : Int))
  norm_num at herrr hroot he ⊢
  linarith

/-- Division of a signed unit by a rounded positive denominator. The error is
relative to the ideal reciprocal, even for large denominators. This includes
the native division rounding, rather than just perturbing an exact division. -/
theorem unit_div_accuracy (v b : Float) (a ε : ℝ)
    (hv : v.isFinite = true) (hb : b.isFinite = true) (hunit : |value v| = 1)
    (ha : 1 ≤ a) (ha' : a ≤ (2 : ℝ)^(500 : Int))
    (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) (herr : |value b - a| ≤ ε * a)
    : (v / b).isFinite = true
      ∧ 0 < value b
      ∧ |value (v / b) - value v / a| ≤ (2 * ε + 3 * (2 : ℝ)^(-50 : Int)) / a := by
  have ha0 : 0 < a := by linarith
  obtain ⟨hl, hb0, hrec⟩ := Flare.Analysis.Jacobi.reciprocal_relative_perturbation
    a (value b) ε ha0 hε hε' herr
  have hrecb : 1 / value b ≤ 2 / a := by
    apply (div_le_div_iff₀ hb0 ha0).mpr
    linarith
  have hη : (2 : ℝ)^(-1022 : Int) ≤ 1 / a := by
    apply (le_div_iff₀ ha0).mpr
    calc
      _ ≤ (2 : ℝ)^(-1022 : Int) * (2 : ℝ)^(500 : Int) :=
        mul_le_mul_of_nonneg_left ha' (by positivity)
      _ = (2 : ℝ)^(-522 : Int) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num
      _ ≤ 1 := (zpow_le_one_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr (by norm_num)
  have hvb : |value v / value b| = 1 / value b := by
    rw [abs_div, hunit, abs_of_pos hb0]
  have hlarge : (2 : ℝ) ≤ (2 : ℝ)^(1000 : Int) := by
    simpa only [zpow_one]
      using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 : Int) ≤ 1000)
  obtain ⟨hf, hd⟩ := Flare.Binary64.Division.div_error_relative v b hv hb (ne_of_gt hb0) (by
    rw [hvb]
    exact hrecb.trans ((by apply (div_le_iff₀ ha0).mpr; linarith : 2 / a ≤ 2).trans hlarge))
  have hde : |value (v / b) - value v / value b| ≤ 3 * (2 : ℝ)^(-50 : Int) / a := by
    apply hd.trans
    rw [hvb]
    calc
      _ ≤ (2 : ℝ)^(-50 : Int) * (2 / a + 1 / a) :=
        mul_le_mul_of_nonneg_left (add_le_add hrecb hη) (by positivity)
      _ = _ := by ring
  have hre : |value v / value b - value v / a| ≤ 2 * ε / a := by
    have he : value v / value b - value v / a = value v * (1 / value b - 1 / a) := by ring
    rw [he, abs_mul, hunit, one_mul]
    exact hrec
  refine ⟨hf, hb0, ?_⟩
  have h := (abs_sub_le (value (v / b)) (value v / value b) (value v / a)).trans
    (add_le_add hde hre)
  apply h.trans_eq
  ring

/-- The native stable tangent calculation is finite and close to the exact
formula, including its sign choice when τ is zero. The relative reciprocal
bound remains useful when τ is large and the rotation is correspondingly tiny. -/
theorem tangent_accuracy (τ : Float) (hτ : τ.isFinite = true) (hτb : |value τ| ≤ (2 : ℝ)^(60 : Int))
    : let t := (if τ < 0.0 then (-1.0 : Float) else 1.0) / (τ.abs + (1.0 + τ * τ).sqrt)
      t.isFinite = true
      ∧ |value t - Flare.Analysis.Jacobi.tangent (value τ)|
        ≤ (2 : ℝ)^(-45 : Int) / (|value τ| + Real.sqrt (1 + (value τ)^2)) := by
  let r := (1.0 + τ * τ).sqrt
  let D := |value τ| + Real.sqrt (1 + (value τ)^2)
  let v : Float := if τ < 0.0 then -1.0 else 1.0
  have hroot := root_one_add_square_accuracy τ hτ hτb
  have hrs : 0 ≤ Real.sqrt (1 + (value τ)^2) := Real.sqrt_nonneg _
  have hrs1 : 1 ≤ Real.sqrt (1 + (value τ)^2) := by
    have hs := Real.sq_sqrt (by nlinarith [sq_nonneg (value τ)] : 0 ≤ 1 + (value τ)^2)
    nlinarith [sq_nonneg (value τ)]
  have hD : 1 ≤ D := by dsimp [D]; linarith [abs_nonneg (value τ)]
  have hD0 : 0 < D := by linarith
  have hrbound : Real.sqrt (1 + (value τ)^2) ≤ (2 : ℝ)^(61 : Int) := by
    have hb := (sq_le_sq₀ (abs_nonneg (value τ)) (by positivity : 0 ≤ (2 : ℝ)^(60 : Int))).mpr hτb
    rw [sq_abs] at hb
    have hs := Real.sq_sqrt (by nlinarith [sq_nonneg (value τ)] : 0 ≤ 1 + (value τ)^2)
    norm_num at hb ⊢
    nlinarith
  have hDb : D ≤ (2 : ℝ)^(63 : Int) := by
    dsimp [D]
    norm_num at hτb hrbound ⊢
    linarith
  obtain ⟨haf, hav⟩ := Flare.Binary64.Order.abs_value τ hτ
  have her : |value r - Real.sqrt (1 + (value τ)^2)| ≤ (2 : ℝ)^(-48 : Int) * D :=
    hroot.2.2.2.trans (mul_le_mul_of_nonneg_left
      (by dsimp [D]; linarith [abs_nonneg (value τ)]) (by positivity))
  have hsum : |value τ.abs + value r| ≤ 2 * D := by
    rw [hav]
    have he : |value τ| + value r = D + (value r - Real.sqrt (1 + (value τ)^2)) := by
      dsimp [D]; ring
    rw [he]
    have h := abs_add_le D (value r - Real.sqrt (1 + (value τ)^2))
    rw [abs_of_pos hD0] at h
    norm_num at her
    linarith
  obtain ⟨hdf, hd⟩ := add_error_relative τ.abs r haf hroot.2.1 (hsum.trans (by
    apply le_trans (b := (2 : ℝ)^(65 : Int)) _
      (zpow_le_zpow_right₀ (by norm_num) (by norm_num))
    norm_num at hDb ⊢
    linarith))
  have hη : (2 : ℝ)^(-1022 : Int) ≤ D := by
    apply le_trans (b := 1) _ hD
    exact (zpow_le_one_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr (by norm_num)
  have hd' : |value (τ.abs + r) - D| ≤ (2 : ℝ)^(-47 : Int) * D := by
    have he : |(value τ.abs + value r) - D| = |value r - Real.sqrt (1 + (value τ)^2)| := by
      rw [hav]
      dsimp [D]
      congr 1
      ring
    have h := abs_sub_le (value (τ.abs + r)) (value τ.abs + value r) D
    rw [he] at h
    have herrd : |value (τ.abs + r) - (value τ.abs + value r)| ≤
        3 * (2 : ℝ)^(-51 : Int) * D := by
      apply hd.trans
      calc
        _ ≤ (2 : ℝ)^(-51 : Int) * (2 * D + D) :=
          mul_le_mul_of_nonneg_left (add_le_add hsum hη) (by positivity)
        _ = _ := by ring
    norm_num at herrd her ⊢
    linarith
  have hvf : v.isFinite = true := by dsimp [v]; split <;> decide
  have hneg : value (-1.0 : Float) = -1 := by
    simpa only [one_value] using (Flare.Binary64.Order.neg_value 1.0 (by decide)).2
  have hvunit : |value v| = 1 := by dsimp [v]; split <;> simp [hneg, one_value]
  obtain ⟨htf, _, ht⟩ := unit_div_accuracy v (τ.abs + r) D ((2 : ℝ)^(-47 : Int)) hvf hdf
    hvunit hD (hDb.trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num))) (by positivity)
      (by norm_num) hd'
  have hvreal : value v = if value τ < 0 then -1 else 1 := by
    have hcmp := Flare.Binary64.Order.lt_iff τ 0.0 hτ (by decide)
    rw [zero_value] at hcmp
    dsimp [v]
    split_ifs with hlt hlt' hlt' <;> simp_all [one_value]
  change (v / (τ.abs + r)).isFinite = true ∧ _
  refine ⟨htf, ?_⟩
  change |value (v / (τ.abs + r)) - Flare.Analysis.Jacobi.tangent (value τ)| ≤ _
  rw [hvreal] at ht
  change |value (v / (τ.abs + r)) - Flare.Analysis.Jacobi.tangent (value τ)| ≤ _ at ht
  apply ht.trans
  exact div_le_div_of_nonneg_right (by norm_num) hD0.le

/-- Native cosine/sine construction from a bounded tangent succeeds. Both
coefficients are bounded by two, and their squared norm differs from one by at
most 2⁻⁴³. The intermediate reciprocal and final multiplication are included. -/
theorem rotation_coefficients_accuracy (t : Float) (ht : t.isFinite = true) (htb : |value t| ≤ 2)
    : let c := 1.0 / (1.0 + t * t).sqrt
      let s := t * c
      c.isFinite = true
      ∧ s.isFinite = true
      ∧ |value c| ≤ 2
      ∧ |value s| ≤ 2
      ∧ |(value c)^2 + (value s)^2 - 1| ≤ (2 : ℝ)^(-43 : Int) := by
  let a := Real.sqrt (1 + (value t)^2)
  let r := (1.0 + t * t).sqrt
  let c := 1.0 / r
  let s := t * c
  have ha2 : a ^ 2 = 1 + (value t)^2 := Real.sq_sqrt (by positivity)
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have ha : 1 ≤ a := by nlinarith [sq_nonneg (value t)]
  have ha' : a ≤ 3 := by
    have hsq := (sq_le_sq₀ (abs_nonneg (value t)) (by norm_num : (0 : ℝ) ≤ 2)).mpr htb
    rw [sq_abs] at hsq
    nlinarith
  have htlarge : |value t| ≤ (2 : ℝ)^(60 : Int) := htb.trans (by norm_num)
  have hroot := root_one_add_square_accuracy t ht htlarge
  obtain ⟨hcf, _, hcerr⟩ := unit_div_accuracy 1.0 r a ((2 : ℝ)^(-48 : Int)) (by decide)
    hroot.2.1 (by rw [one_value]; norm_num) ha
      (ha'.trans ((by norm_num : (3 : ℝ) ≤ (2 : ℝ)^(2 : Int)).trans
        (zpow_le_zpow_right₀ (by norm_num) (by norm_num)))) (by positivity) (by norm_num)
          hroot.2.2.2
  rw [one_value] at hcerr
  have hce : |value c - 1 / a| ≤ (2 : ℝ)^(-46 : Int) / a :=
    hcerr.trans (div_le_div_of_nonneg_right (by norm_num) ha0.le)
  have hscaled : |a * value c - 1| ≤ (2 : ℝ)^(-46 : Int) := by
    have h := mul_le_mul_of_nonneg_left hce ha0.le
    rw [show a * |value c - 1 / a| = |a * (value c - 1 / a)| by
      rw [abs_mul, abs_of_pos ha0]] at h
    have he : a * (value c - 1 / a) = a * value c - 1 := by field_simp
    rw [he] at h
    apply h.trans_eq
    field_simp
  have hcb : |value c| ≤ 2 := by
    have h := abs_sub_le (value c) (1 / a) 0
    simp only [sub_zero, abs_of_pos (one_div_pos.mpr ha0)] at h
    have hr : 1 / a ≤ 1 := (div_le_one ha0).mpr ha
    have he : (2 : ℝ)^(-46 : Int) / a ≤ (2 : ℝ)^(-46 : Int) := by
      apply (div_le_iff₀ ha0).mpr
      nlinarith [mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ (2 : ℝ)^(-46 : Int))]
    norm_num only [zpow_neg, zpow_ofNat] at hce he
    linarith
  have hta : |value t| ≤ a := by nlinarith [sq_abs (value t), abs_nonneg (value t)]
  have htc : |value t * value c| ≤ 1 + (2 : ℝ)^(-46 : Int) := by
    have h := abs_sub_le (a * value c) 1 0
    norm_num only [sub_zero, abs_one] at h
    have hprod := mul_le_mul_of_nonneg_right hta (abs_nonneg (value c))
    rw [← abs_of_pos ha0, ← abs_mul, ← abs_mul] at hprod
    linarith
  obtain ⟨hsf, hsround⟩ := mul_error_relative t c ht hcf (htc.trans (by
    apply le_trans (b := 2) (by norm_num)
    simpa only [zpow_one] using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1 : Int) ≤ 1000)))
  have hη : (2 : ℝ)^(-1022 : Int) ≤ 1 :=
    (zpow_le_one_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr (by norm_num)
  have hse : |value s - value t * value c| ≤ (2 : ℝ)^(-49 : Int) := by
    apply hsround.trans
    calc
      _ ≤ (2 : ℝ)^(-51 : Int) * (1 + (2 : ℝ)^(-46 : Int) + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add htc hη) (by positivity)
      _ ≤ _ := by norm_num
  have hsb : |value s| ≤ 2 := by
    have h := abs_sub_le (value s) (value t * value c) 0
    simp only [sub_zero] at h
    norm_num only [zpow_neg, zpow_ofNat] at htc hse
    linarith
  have hnormc : |(a * value c)^2 - 1| ≤ 3 * (2 : ℝ)^(-46 : Int) := by
    have h := abs_sub_le (a * value c) 1 0
    norm_num only [sub_zero, abs_one] at h
    have hplus : |a * value c + 1| ≤ 3 := by
      have hh := abs_add_le (a * value c) 1
      norm_num only [zpow_neg, zpow_ofNat, abs_one] at hh hscaled
      linarith
    have he : (a * value c)^2 - 1 = (a * value c - 1) * (a * value c + 1) := by ring
    rw [he, abs_mul]
    have he := mul_le_mul hscaled hplus (abs_nonneg _) (by positivity)
    nlinarith
  have hnorms : |(value s)^2 - (value t * value c)^2| ≤ 4 * (2 : ℝ)^(-49 : Int) := by
    have he : (value s)^2 - (value t * value c)^2 =
        (value s - value t * value c) * (value s + value t * value c) := by ring
    rw [he, abs_mul]
    have hsum : |value s + value t * value c| ≤ 4 := by
      have h := abs_add_le (value s) (value t * value c)
      norm_num only [zpow_neg, zpow_ofNat] at htc
      linarith
    have he := mul_le_mul hse hsum (abs_nonneg _) (by positivity)
    nlinarith
  change c.isFinite = true ∧ s.isFinite = true ∧ _
  refine ⟨hcf, hsf, hcb, hsb, ?_⟩
  have he : (value c)^2 + (value s)^2 - 1 =
      ((a * value c)^2 - 1) + ((value s)^2 - (value t * value c)^2) := by
    nlinarith [congrArg (fun z : ℝ => z * (value c)^2) ha2]
  rw [he]
  have h := abs_add_le ((a * value c)^2 - 1) ((value s)^2 - (value t * value c)^2)
  norm_num at hnormc hnorms ⊢
  linarith

/-- The complete native tangent/cosine/sine schedule has finite, bounded
outputs and an explicit orthogonality defect. Its only numerical premise is a
bound on the supplied τ; no computed-coefficient bound is assumed. -/
theorem rotation_parameters_accuracy (τ : Float) (hτ : τ.isFinite = true)
    (hτb : |value τ| ≤ (2 : ℝ)^(60 : Int))
    : let t := (if τ < 0.0 then (-1.0 : Float) else 1.0) / (τ.abs + (1.0 + τ * τ).sqrt)
      let c := 1.0 / (1.0 + t * t).sqrt
      let s := t * c
      t.isFinite = true
      ∧ c.isFinite = true
      ∧ s.isFinite = true
      ∧ |value t| ≤ 2
      ∧ |value c| ≤ 2
      ∧ |value s| ≤ 2
      ∧ |(value c)^2 + (value s)^2 - 1| ≤ (2 : ℝ)^(-43 : Int) := by
  dsimp only
  let t := (if τ < 0.0 then (-1.0 : Float) else 1.0) / (τ.abs + (1.0 + τ * τ).sqrt)
  have ht := tangent_accuracy τ hτ hτb
  have hideal := Flare.Analysis.Jacobi.tangent_properties (value τ)
  have hsqrt : 1 ≤ Real.sqrt (1 + (value τ)^2) := by
    have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 + (value τ)^2)
    nlinarith [sq_nonneg (value τ), Real.sqrt_nonneg (1 + (value τ)^2)]
  have hD : 1 ≤ |value τ| + Real.sqrt (1 + (value τ)^2) := by linarith [abs_nonneg (value τ)]
  have hb : |value t| ≤ 2 := by
    have h := abs_sub_le (value t) (Flare.Analysis.Jacobi.tangent (value τ)) 0
    simp only [sub_zero] at h
    have he : (2 : ℝ)^(-45 : Int) / (|value τ| + Real.sqrt (1 + (value τ)^2)) ≤ 1 :=
      (div_le_one hideal.1).mpr (by norm_num; linarith)
    linarith [ht.2, hideal.2.1]
  have hcs := rotation_coefficients_accuracy t ht.1 hb
  exact ⟨ht.1, hcs.1, hcs.2.1, hb, hcs.2.2⟩

/-- Squared-norm error for a complete native pair update, with the proved
coefficient defect as a hypothesis. The bound scales with the updated entries,
including an explicit squared-underflow term; it does not add a fixed error
floor proportional to the matrix diagonal at each Jacobi iteration. -/
theorem pair_update_energy (c s x y : Float)
    (hc : c.isFinite = true) (hs : s.isFinite = true)
    (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hcb : |value c| ≤ 2) (hsb : |value s| ≤ 2)
    (hunit : |(value c)^2 + (value s)^2 - 1| ≤ (2 : ℝ)^(-43 : Int))
    (hsize : |value x| + |value y| + (2 : ℝ)^(-1022 : Int) ≤ (2 : ℝ)^(500 : Int))
    : (c * x - s * y).isFinite = true
      ∧ (s * x + c * y).isFinite = true
      ∧ |(value (c * x - s * y))^2 + (value (s * x + c * y))^2 - ((value x)^2 + (value y)^2)|
        ≤ (2 : ℝ)^(-40 : Int) * ((value x)^2 + (value y)^2 + ((2 : ℝ)^(-1022 : Int))^2) := by
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  let M := |value x| + |value y| + η
  have hη : 0 ≤ η := zpow_nonneg (by norm_num) _
  obtain ⟨hp, hq, hep, heq⟩ := pair_update_accuracy c s x y M hc hs hx hy hcb hsb le_rfl hsize
  have h := Flare.Analysis.Jacobi.pair_energy_perturbation (value c) (value s) (value x) (value y)
    (value (c * x - s * y)) (value (s * x + c * y)) M
      ((2 : ℝ)^(-47 : Int)) ((2 : ℝ)^(-43 : Int))
      (by dsimp [M]; linarith) (by positivity) (by norm_num) hcb hsb hunit hep heq
  have hM : M ^ 2 ≤ 3 * ((value x)^2 + (value y)^2 + η^2) := by
    dsimp [M]
    nlinarith [sq_nonneg (|value x| - |value y|), sq_nonneg (|value x| - η),
      sq_nonneg (|value y| - η), sq_abs (value x), sq_abs (value y)]
  refine ⟨hp, hq, h.trans ?_⟩
  have he := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 10 * (2 : ℝ)^(-47 : Int))
  change _ ≤ (2 : ℝ)^(-40 : Int) * ((value x)^2 + (value y)^2 + η^2)
  norm_num only [zpow_neg, zpow_ofNat] at he ⊢
  nlinarith [sq_nonneg (value x), sq_nonneg (value y), sq_nonneg η]

/-- A normalized Jacobi pivot above the stopping scale gives a finite τ within
the parameter theorem's domain. The subtraction, multiplication by two and
division are all actual native operations; nonzero division is a conclusion. -/
theorem pivot_parameter_bounded (a b d : Float)
    (ha : a.isFinite = true) (hb : b.isFinite = true) (hd : d.isFinite = true)
    (hab : |value a| ≤ 32) (hbb : |value b| ≤ 32) (hdb : |value d| ≤ 32)
    (hbp : (2 : ℝ)^(-47 : Int) ≤ |value b|)
    : (d - a).isFinite = true
      ∧ (2.0 * b).isFinite = true
      ∧ value (2.0 * b) ≠ 0
      ∧ ((d - a) / (2.0 * b)).isFinite = true
      ∧ |value ((d - a) / (2.0 * b))| ≤ (2 : ℝ)^(60 : Int) := by
  have htwo : value (2.0 : Float) = 2 := by
    change (((2^52 : Nat) : ℝ) * (2 : ℝ)^(-51 : Int)) = 2
    norm_num
  have hp : 0 < |value b| := (zpow_pos (by norm_num) _).trans_le hbp
  have hη : (2 : ℝ)^(-1022 : Int) ≤ |value b| :=
    (zpow_le_zpow_right₀ (by norm_num) (by norm_num : (-1022 : Int) ≤ -47)).trans hbp
  obtain ⟨hnf, hne⟩ := sub_error d a 6 hd ha (by norm_num) (by norm_num) (by
    have h := abs_sub (value d) (value a)
    norm_num
    linarith)
  have hnb : |value (d - a)| ≤ 128 := by
    have h := abs_sub_le (value (d - a)) (value d - value a) 0
    simp only [sub_zero] at h
    norm_num at hne
    linarith [abs_sub (value d) (value a)]
  obtain ⟨hdf, hde⟩ := mul_error_relative 2.0 b (by decide) hb (by
    rw [htwo, abs_mul]
    apply le_trans (b := (2 : ℝ)^(6 : Int)) _
      (zpow_le_zpow_right₀ (by norm_num) (by norm_num))
    norm_num
    linarith)
  rw [htwo] at hde
  have hde' : |value (2.0 * b) - 2 * value b| ≤ (2 : ℝ)^(-49 : Int) * |value b| := by
    apply hde.trans
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ (2 : ℝ)^(-51 : Int) * (2 * |value b| + |value b|) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hη) (by positivity)
      _ ≤ _ := by norm_num; linarith [abs_nonneg (value b)]
  have hdl : |value b| ≤ |value (2.0 * b)| := by
    have h := abs_sub_le (2 * value b) (value (2.0 * b)) 0
    simp only [sub_zero] at h
    rw [abs_sub_comm (2 * value b) (value (2.0 * b)), abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
    norm_num only [zpow_neg, zpow_ofNat] at hde'
    linarith
  have hdpos : 0 < |value (2.0 * b)| := hp.trans_le hdl
  have hdne : value (2.0 * b) ≠ 0 := abs_pos.mp hdpos
  have hquot : |value (d - a) / value (2.0 * b)| ≤ (2 : ℝ)^(54 : Int) := by
    rw [abs_div]
    apply (div_le_iff₀ hdpos).mpr
    calc
      _ ≤ 128 := hnb
      _ = (2 : ℝ)^(54 : Int) * (2 : ℝ)^(-47 : Int) := by norm_num
      _ ≤ (2 : ℝ)^(54 : Int) * |value b| := mul_le_mul_of_nonneg_left hbp (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hdl (by positivity)
  obtain ⟨htf, hte⟩ := Flare.Binary64.Division.div_error (d - a) (2.0 * b) 54 hnf hdf hdne
    (by norm_num) (by norm_num) hquot
  refine ⟨hnf, hdf, hdne, htf, ?_⟩
  have h := abs_sub_le (value ((d - a) / (2.0 * b))) (value (d - a) / value (2.0 * b)) 0
  simp only [sub_zero] at h
  norm_num only [zpow_ofNat] at hquot
  norm_num at hte ⊢
  linarith

/-- Exact comparison of the runtime stopping literal with the two real scales
used by the parameter and bounded-iteration proofs. No decimal-to-real equality
is assumed for a binary64 literal. -/
theorem stopping_threshold_bounds
    : (2 : ℝ)^(-47 : Int) ≤ value (1.0e-14 : Float)
      ∧ (99 / 10000000000000000 : ℝ) ≤ value (1.0e-14 : Float) := by
  change (2 : ℝ)^(-47 : Int) ≤ 6338253001141147 * (2 : ℝ)^(-99 : Int) ∧
    (99 / 10000000000000000 : ℝ) ≤ 6338253001141147 * (2 : ℝ)^(-99 : Int)
  norm_num

/-- Above the actual native stopping threshold, the full scalar parameter
schedule succeeds on bounded normalized matrix entries. It derives the bounds
needed by the native pair-update and energy theorems. This does not assume any
previously computed τ, tangent, cosine or sine is finite or accurate. -/
theorem pivot_rotation_parameters (a b d : Float)
    (ha : a.isFinite = true) (hb : b.isFinite = true) (hd : d.isFinite = true)
    (hab : |value a| ≤ 32) (hbb : |value b| ≤ 32) (hdb : |value d| ≤ 32)
    (hstop : (1.0e-14 : Float) < b.abs)
    : let τ := (d - a) / (2.0 * b)
      let t := (if τ < 0.0 then (-1.0 : Float) else 1.0) / (τ.abs + (1.0 + τ * τ).sqrt)
      let c := 1.0 / (1.0 + t * t).sqrt
      let s := t * c
      τ.isFinite = true
      ∧ t.isFinite = true
      ∧ c.isFinite = true
      ∧ s.isFinite = true
      ∧ |value t| ≤ 2
      ∧ |value c| ≤ 2
      ∧ |value s| ≤ 2
      ∧ |(value c)^2 + (value s)^2 - 1| ≤ (2 : ℝ)^(-43 : Int) := by
  have hbf := Flare.Binary64.Order.abs_value b hb
  have hp := (Flare.Binary64.Order.lt_iff 1.0e-14 b.abs (by decide) hbf.1).mp hstop
  rw [hbf.2] at hp
  have hτ := pivot_parameter_bounded a b d ha hb hd hab hbb hdb
    (stopping_threshold_bounds.1.trans hp.le)
  have hparams := rotation_parameters_accuracy ((d - a) / (2.0 * b)) hτ.2.2.2.1 hτ.2.2.2.2
  exact ⟨hτ.2.2.2.1, hparams⟩

end Flare.Matrix.Jacobi
