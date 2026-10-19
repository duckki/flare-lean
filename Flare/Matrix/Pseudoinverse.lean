import Flare.Matrix.JacobiOutput
import Flare.Analysis.SpectralGap

/-! Numerical bounds for the native symmetric pseudoinverse. These connect
the actual cutoff, reciprocal and reconstruction schedule to the real spectral
truncation lemmas, keeping each required conditioning premise explicit. -/

namespace Flare.Matrix.Pseudoinverse
open Flare.Matrix.Value Flare.Binary64.Value Flare.Matrix.Operations
open Flare.Binary64.Arithmetic Flare.Binary64.Order
open Flare.Matrix.JacobiOutput Flare.Analysis.SpectralPerturbation
open scoped Matrix.Norms.L2Operator
open Std.Do
set_option mvcgen.warning false
-- Retain the established VC engine while using Lean 4.35.
set_option linter.deprecated.syntax false

/-- The actual binary64 cutoff is close to its intended relative scale on
the bounded, non-negligible spectral magnitudes in the stated numerical profile. -/
theorem cutoff_precision (m : Float) (hm : m.isFinite = true)
    (hmlo : (1 / 16 : ℝ) ≤ value m) (hmhi : value m ≤ (2 : ℝ) ^ (30 : Int))
    : (1.0e-10 * m).isFinite = true
      ∧ (999 / 10000000000000 : ℝ) * value m ≤ value (1.0e-10 * m)
      ∧ value (1.0e-10 * m) ≤ (1001 / 10000000000000 : ℝ) * value m := by
  let u : ℝ := (2 : ℝ)^(-53 : Int)
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  have hu : 0 ≤ u := by positivity
  have hm0 : 0 < value m := by linarith only [hmlo]
  have hliteral : value (1.0e-10 : Float) = 7737125245533627 * (2 : ℝ)^(-86 : Int) := by
    change 7737125245533627 * (2 : ℝ)^(-86 : Int) = _
    rfl
  have hc0 : 0 ≤ value (1.0e-10 : Float) := by rw [hliteral]; positivity
  have hc1 : value (1.0e-10 : Float) ≤ 1 := by rw [hliteral]; norm_num
  have hη : η ≤ u * value m := by
    calc
      _ ≤ (2 : ℝ) ^ (-57 : Int) := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
      _ = u * (1 / 16 : ℝ) := by norm_num [u]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmlo hu
  have hprod : |value (1.0e-10 : Float) * value m| ≤ (2 : ℝ)^(1000 : Int) := by
    rw [abs_of_nonneg (mul_nonneg hc0 hm0.le)]
    calc
      _ ≤ 1 * value m := mul_le_mul_of_nonneg_right hc1 hm0.le
      _ ≤ (2 : ℝ) ^ (30 : Int) := by simpa only [one_mul] using hmhi
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  obtain ⟨hf, he⟩ := mul_error_relative 1.0e-10 m (by decide) hm hprod
  rw [abs_of_nonneg (mul_nonneg hc0 hm0.le), show (2 : ℝ)^(-51 : Int) = 4 * u by norm_num [u]] at he
  have he' := he.trans (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl (value (1.0e-10 : Float) * value m)) hη) (by positivity : 0 ≤ 4 * u))
  have heL := (abs_le.mp he').1
  have heU := (abs_le.mp he').2
  rw [hliteral] at heL heU
  norm_num [u] at heL heU
  refine ⟨hf, ?_, ?_⟩ <;> nlinarith only [heL, heU, hm0]

/-- Inverting a retained eigenvalue above one eighth is finite and has a
65-unit absolute roundoff bound. Its native result has magnitude at most nine. -/
theorem reciprocal_precision (x : Float) (hx : x.isFinite = true) (hlo : (1 / 8 : ℝ) ≤ value x)
    : (1.0 / x).isFinite = true
      ∧ |value (1.0 / x) - 1 / value x| ≤ 65 * (2 : ℝ) ^ (-53 : Int)
      ∧ |value (1.0 / x)| ≤ 9 := by
  have hxp : 0 < value x := by linarith only [hlo]
  have hquot : |value (1.0 : Float) / value x| ≤ 8 := by
    rw [one_value, abs_of_pos (one_div_pos.mpr hxp)]
    apply (div_le_iff₀ hxp).mpr
    linarith only [hlo]
  have hlarge : (8 : ℝ) ≤ (2 : ℝ)^(1000 : Int) :=
    (by norm_num : (8 : ℝ) ≤ (2 : ℝ)^(3 : Int)).trans
      (zpow_le_zpow_right₀ (by norm_num) (by norm_num))
  obtain ⟨hf, he⟩ := Flare.Binary64.Division.div_error_relative 1.0 x (by decide) hx (ne_of_gt hxp)
    (hquot.trans hlarge)
  have hη : (2 : ℝ)^(-1022 : Int) ≤ (1 / 8 : ℝ) := by
    exact (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (-1022 : Int) ≤
      -3)).trans_eq (by norm_num)
  have herr := he.trans (mul_le_mul_of_nonneg_left (add_le_add hquot hη) (by positivity))
  rw [one_value] at herr hquot
  have herr' : |value (1.0 / x) - 1 / value x| ≤ 65 * (2 : ℝ)^(-53 : Int) :=
    herr.trans_eq (by norm_num)
  refine ⟨hf, herr', ?_⟩
  have h := abs_sub_le (value (1.0 / x)) (1 / value x) 0
  simp only [sub_zero] at h
  exact (h.trans (add_le_add herr' hquot)).trans (by norm_num)

/-- The actual native branch agrees with thresholding the real values. Under
the retained-value lower bound, both the invert and discard branches are safe. -/
theorem reciprocal_if_precision (cutoff x : Float) (hc : cutoff.isFinite = true)
    (hx : x.isFinite = true) (hretain : value cutoff < |value x| → (1 / 8 : ℝ) ≤ value x)
    : let r := if cutoff < x.abs then 1.0 / x else 0.0
      r.isFinite = true
      ∧ |value r - (if value cutoff < |value x| then 1 / value x else 0)|
        ≤ 65 * (2 : ℝ) ^ (-53 : Int)
      ∧ |value r| ≤ 9 := by
  have habs := abs_value x hx
  have hcmp := lt_iff cutoff x.abs hc habs.1
  rw [habs.2] at hcmp
  by_cases h : cutoff < x.abs
  · have hr := hcmp.mp h
    simpa only [h, hr, ↓reduceIte] using reciprocal_precision x hx (hretain hr)
  · have hr : ¬value cutoff < |value x| := fun hr => h (hcmp.mpr hr)
    simp only [h, hr, ↓reduceIte, zero_value, sub_self, abs_zero]
    exact ⟨by decide, by positivity, by norm_num⟩

/-- The native maximum absolute returned eigenvalue is exactly the operator
norm of its real diagonal matrix; the scan performs no rounding arithmetic. -/
theorem spectrum_magnitude_eq_norm (n : Nat) (s : Spectrum)
    (hs : s.values.size = n) (hf : s.values.all Float.isFinite = true)
    : value (maxAbs s.values) = ‖spectrumDiagonal n s‖ := by
  rw [spectrumDiagonal, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply Spectrum.maxAbs_le _ _ hf (norm_nonneg _)
    intro i hi
    have hi' : i < n := by omega
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm
      (fun j : Fin n => value (s.values.getD j.val 0.0)) ⟨i, hi'⟩
  · have hm := Spectrum.maxAbs_correct s.values hf
    apply (pi_norm_le_iff_of_nonneg hm.2.1).mpr
    intro j
    simpa only [Real.norm_eq_abs] using hm.2.2 j.val (by have := j.isLt; omega)

/-- A returned-spectrum enclosure controls the actual native cutoff in the
original matrix scale, including the rounding of the cutoff multiplication. -/
theorem cutoff_from_spectral_enclosure (n : Nat) (A W : Matrix (Fin n) (Fin n) ℝ) (s : Spectrum)
    (hs : JacobiConvergence.Stored n s)
    (hW : W ∈ unitary (Matrix (Fin n) (Fin n) ℝ))
    (he
      : ‖spectrumDiagonal n s - W.transpose * A * W‖
        ≤ (9 / 100000000000 : ℝ) * ‖A‖ + (2 : ℝ) ^ (-51 : Int) * (2 : ℝ) ^ (-1022 : Int))
    (hlo : (1 / 8 : ℝ) ≤ ‖A‖) (hhi : ‖A‖ ≤ (2 : ℝ) ^ (20 : Int))
    : let cutoff := 1.0e-10 * maxAbs s.values
      cutoff.isFinite = true
      ∧ (99 / 1000000000000 : ℝ) * ‖A‖ ≤ value cutoff
      ∧ value cutoff ≤ (101 / 1000000000000 : ℝ) * ‖A‖ := by
  have hmag := spectrum_magnitude_eq_norm n s hs.values_size hs.values_finite
  have hnorm := abs_norm_sub_norm_le (spectrumDiagonal n s) (W.transpose * A * W)
  rw [similarity_isometry W A hW, ← hmag] at hnorm
  have hmerr := hnorm.trans he
  have htiny : (2 : ℝ)^(-51 : Int) * (2 : ℝ)^(-1022 : Int) ≤ (2 : ℝ)^(-64 : Int) := by
    rw [← zpow_add₀ (by norm_num)]
    exact zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hsmall : (2 : ℝ)^(-51 : Int) * (2 : ℝ)^(-1022 : Int) ≤ (1 / 100000 : ℝ) * ‖A‖ :=
    htiny.trans ((by norm_num : (2 : ℝ)^(-64 : Int) ≤ (1 / 100000 : ℝ) * (1 / 8)).trans
      (mul_le_mul_of_nonneg_left hlo (by norm_num)))
  have herr : |value (maxAbs s.values) - ‖A‖| ≤ (1 / 1000 : ℝ) * ‖A‖ := by
    exact hmerr.trans ((add_le_add le_rfl hsmall).trans (by nlinarith only [norm_nonneg A]))
  have hml : (999 / 1000 : ℝ) * ‖A‖ ≤ value (maxAbs s.values) := by
    nlinarith only [(abs_le.mp herr).1]
  have hmu : value (maxAbs s.values) ≤ (1001 / 1000 : ℝ) * ‖A‖ := by
    nlinarith only [(abs_le.mp herr).2]
  have hscaleLo : (1 / 16 : ℝ) ≤ value (maxAbs s.values) := by
    have he := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 999 / 1000)
    nlinarith only [he, hml]
  have hscaleHi : value (maxAbs s.values) ≤ (2 : ℝ)^(30 : Int) :=
    hmu.trans ((mul_le_mul_of_nonneg_left hhi (by norm_num)).trans (by norm_num))
  have hc := cutoff_precision (maxAbs s.values) (Spectrum.maxAbs_correct _ hs.values_finite).1
    hscaleLo hscaleHi
  refine ⟨hc.1, ?_, ?_⟩
  · have he := mul_le_mul_of_nonneg_left hml (by norm_num : (0 : ℝ) ≤ 999 / 10000000000000)
    have hb := he.trans hc.2.1
    nlinarith only [hb, norm_nonneg A]
  · have he := hc.2.2.trans (mul_le_mul_of_nonneg_left hmu (by norm_num))
    nlinarith only [he, norm_nonneg A]

/-- The actual reciprocal array map succeeds and stores the values analyzed
by the scalar branch theorem, with no assumption about its returned array. -/
theorem reciprocals_success (cutoff : Float) (xs : Array Float)
    (hc : cutoff.isFinite = true) (hx : xs.all Float.isFinite = true)
    (hretain
      : ∀ i,
          i < xs.size
          → value cutoff < |value (xs.getD i 0.0)|
          → (1 / 8 : ℝ) ≤ value (xs.getD i 0.0))
    : ∃ rs,
        xs.mapM (fun x => if cutoff < x.abs then finite (1.0 / x) else pure 0.0) = .ok rs
        ∧ rs.size = xs.size
        ∧ rs.all Float.isFinite = true
        ∧ ∀ i,
            i < xs.size
            → |value (rs.getD i 0.0)
                  - (if value cutoff < |value (xs.getD i 0.0)| then
                        1 / value (xs.getD i 0.0)
                      else
                        0)|
                ≤ 65 * (2 : ℝ) ^ (-53 : Int)
              ∧ |value (rs.getD i 0.0)| ≤ 9 := by
  let g := fun x : Float => if cutoff < x.abs then 1.0 / x else 0.0
  have hg (i : Nat) (hi : i < xs.size) := reciprocal_if_precision cutoff (xs.getD i 0.0)
    hc (Flare.Matrix.Storage.getD_finite _ _ hx) (hretain i hi)
  have he : xs.mapM (fun x => if cutoff < x.abs then finite (1.0 / x) else pure 0.0) = .ok (xs.map
    g) := by
    apply Flare.Matrix.Multiplication.mapM_eq_ok_map
    intro x hmem
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (by simpa using hmem)
    have hfin : (g xs[i]).isFinite = true := by simpa [g, hi] using (hg i hi).1
    dsimp [g] at hfin ⊢
    split_ifs with hbranch
    · rw [ite_eq_left hbranch] at hfin
      simp only [finite, hfin, ↓reduceIte]
    · rfl
  refine ⟨xs.map g, he, Array.size_map .., ?_, ?_⟩
  · rw [Array.all_eq_true]
    intro i hi
    have hi' : i < xs.size := by simpa only [Array.size_map] using hi
    simpa [g, hi'] using (hg i hi').1
  · intro i hi
    have hentry : (xs.map g).getD i 0.0 = g (xs.getD i 0.0) := by simp [hi]
    rw [hentry]
    exact (hg i hi).2

/-- Proof decomposition of the runtime's row-major eigenvector scaling loop.
Every product reads the original vectors and the corresponding reciprocal. -/
def scaleColumns (n : Nat) (vectors reciprocals : Array Float)
    : Except Flare.Matrix.Error (Array Float) := do
  let mut scaled := vectors
  for i in [:n] do
    for j in [:n] do
      let value ← finite (entry n vectors i j * reciprocals.getD j 0.0)
      scaled := scaled.set! (i * n + j) value
  return scaled

private def ScaleState (n : Nat) (vectors reciprocals : Array Float) (row column : Nat)
    (result : Array Float)
    : Prop :=
  result.size = n * n
  ∧ result.all Float.isFinite = true
  ∧ ∀ i j,
      i < n
      → j < n
      → i < row ∨ i = row ∧ j < column
      → entry n result i j = entry n vectors i j * reciprocals.getD j 0.0

private theorem scale_update (n i j : Nat) (vectors reciprocals result : Array Float)
    (hi : i < n) (hj : j < n) (hs : ScaleState n vectors reciprocals i j result)
    (hf : (entry n vectors i j * reciprocals.getD j 0.0).isFinite = true)
    : ScaleState n vectors reciprocals i (j + 1)
        (result.set! (i * n + j) (entry n vectors i j * reciprocals.getD j 0.0)) := by
  refine ⟨(Array.size_set! ..).trans hs.1, Flare.Matrix.Storage.all_set _ _ _ hs.2.1 hf, ?_⟩
  intro r c hr hc hrc
  have hidx : i * n + j < result.size := by rw [hs.1]; nlinarith
  by_cases he : r = i ∧ c = j
  · rcases he with ⟨rfl, rfl⟩
    simp [entry, Flare.Matrix.Dense.entry, Array.set!_eq_setIfInBounds, hidx]
  · have hne : i * n + j ≠ r * n + c := fun heq =>
      he ((Flare.Matrix.Storage.flat_index_eq hc hj).mp heq.symm)
    have hv := hs.2.2 r c hr hc (by omega)
    simpa only [entry, Flare.Matrix.Dense.entry, Array.set!_eq_setIfInBounds,
      Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne hne] using hv

@[spec]
private theorem finite_exact (x : Float) : ⦃⌜x.isFinite = true⌝⦄ finite x ⦃⇓ y => ⌜y = x⌝⦄ := by
  unfold finite
  mvcgen
  simp_all

private theorem scaleColumns_triple (n : Nat) (vectors reciprocals : Array Float)
    (hs : vectors.size = n * n) (hf : vectors.all Float.isFinite = true)
    (hproducts
      : ∀ i j, i < n → j < n → (entry n vectors i j * reciprocals.getD j 0.0).isFinite = true)
    : ⦃⌜True⌝
      ⦄ scaleColumns n vectors reciprocals
      ⦃⇓ r => ⌜ScaleState n vectors reciprocals n 0 r⌝⦄ := by
  have range_length (n : Nat) : [:n].toList.length = n := by simp [Std.Legacy.Range.toList]
  unfold scaleColumns
  mvcgen [-Flare.Matrix.OperationStorage.finite_spec, finite_exact]
    invariants
      | inv1 => ⇓ ⟨xs, r⟩ => ⌜ScaleState n vectors reciprocals xs.prefix.length 0 r⌝
      | inv2 pref i suff hi result hs =>
          ⇓ ⟨xs, r⟩ => ⌜ScaleState n vectors reciprocals i xs.prefix.length r⌝
    with
      | vc1 =>
        rename_i prefI i suffI hi initial hinit prefJ j suffJ hj result hresult
        exact hproducts i j (Flare.Matrix.Storage.range_current hi).2
          (Flare.Matrix.Storage.range_current hj).2
      | vc2 =>
        subst_vars
        rename_i prefI i suffI hi initial hinit prefJ j suffJ hj result hresult
        have hi' := Flare.Matrix.Storage.range_current hi
        have hj' := Flare.Matrix.Storage.range_current hj
        simpa only [List.length_append, List.length_singleton, ← hj'.1]
          using scale_update n i j vectors reciprocals result hi'.2 hj'.2
            (by simpa only [hj'.1] using hresult) (hproducts i j hi'.2 hj'.2)
      | vc3 =>
        rename_i pref i suff hi result hresult
        simpa only [(Flare.Matrix.Storage.range_current hi).1, List.length_nil] using hresult
      | vc4 =>
        rename_i pref i suff hi initial hinit result hresult
        have hstate : ScaleState n vectors reciprocals i n result := by
          simpa only [range_length] using hresult
        refine ⟨hstate.1, hstate.2.1, ?_⟩
        intro r c hr hc hrc
        apply hstate.2.2 r c hr hc
        have hi' := (Flare.Matrix.Storage.range_current hi).1
        simp only [List.length_append, List.length_singleton] at hrc
        omega
      | vc6 =>
        refine ⟨hs, hf, ?_⟩
        intros
        simp only [List.length_nil] at *
        omega
      | vc7 =>
        rename_i result hresult
        simpa only [range_length] using hresult

/-- The scaling loop succeeds on bounded vectors and reciprocals, with exact
stored-product equations and one-rounding error bounds for every entry. -/
theorem scaleColumns_success (n : Nat) (vectors reciprocals : Array Float)
    (hs : vectors.size = n * n) (hv : vectors.all Float.isFinite = true)
    (hr : reciprocals.all Float.isFinite = true)
    (hvb : ∀ i j, i < n → j < n → |value (entry n vectors i j)| ≤ 2)
    (hrb : ∀ j, j < n → |value (reciprocals.getD j 0.0)| ≤ 9)
    : ∃ result,
        scaleColumns n vectors reciprocals = .ok result
        ∧ result.size = n * n
        ∧ result.all Float.isFinite = true
        ∧ ∀ i j,
            i < n
            → j < n
            → entry n result i j = entry n vectors i j * reciprocals.getD j 0.0
              ∧ |value (entry n result i j)
                  - value (entry n vectors i j) * value (reciprocals.getD j 0.0)|
                ≤ (2 : ℝ) ^ (-47 : Int)
              ∧ |value (entry n result i j)| ≤ 19 := by
  have hprod (i j : Nat) (hi : i < n) (hj : j < n) :
      |value (entry n vectors i j) * value (reciprocals.getD j 0.0)| ≤ 18 := by
    rw [abs_mul]
    exact (mul_le_mul (hvb i j hi hj) (hrb j hj) (abs_nonneg _) (by norm_num)).trans_eq (by
      norm_num)
  have hround (i j : Nat) (hi : i < n) (hj : j < n) := mul_error (entry n vectors i j)
    (reciprocals.getD j 0.0) 5
    (Flare.Matrix.Storage.getD_finite _ _ hv) (Flare.Matrix.Storage.getD_finite _ _ hr)
    (by norm_num) (by norm_num) ((hprod i j hi hj).trans (by norm_num))
  have hproof := scaleColumns_triple n vectors reciprocals hs hv (fun i j hi hj => (hround i j hi
    hj).1)
  cases he : scaleColumns n vectors reciprocals with
  | error e =>
      rw [he] at hproof; exact False.elim (hproof True.intro)
  | ok result =>
      rw [he] at hproof
      have hstate := hproof True.intro
      refine ⟨result, rfl, hstate.1, hstate.2.1, ?_⟩
      intro i j hi hj
      have hentry := hstate.2.2 i j hi hj (Or.inl hi)
      have herr : |value (entry n vectors i j * reciprocals.getD j 0.0) -
          value (entry n vectors i j) * value (reciprocals.getD j 0.0)| ≤ (2 : ℝ)^(-47 : Int) :=
        (hround i j hi hj).2
      refine ⟨hentry, by rwa [hentry], ?_⟩
      rw [hentry]
      have htri := abs_sub_le (value (entry n vectors i j * reciprocals.getD j 0.0))
        (value (entry n vectors i j) * value (reciprocals.getD j 0.0)) 0
      simp only [sub_zero] at htri
      exact (htri.trans (add_le_add herr (hprod i j hi hj))).trans (by norm_num)

/-- Proof decomposition of the operations after native eigendecomposition. -/
def fromSpectrum (n : Nat) (e : Spectrum) : Except Flare.Matrix.Error (Array Float) := do
  let cutoff ← finite (1.0e-10 * maxAbs e.values)
  let reciprocals ←
    e.values.mapM
      fun x =>
        if cutoff < x.abs then finite (1.0 / x) else pure 0.0
  let scaled ← scaleColumns n e.vectors reciprocals
  return mirrorLower n (← multiply n n n scaled (transpose n n e.vectors))

/-- The proof decomposition is the actual runtime pseudoinverse schedule. -/
theorem symmetricPseudoInverse_eq (n : Nat) (a : Array Float)
    : symmetricPseudoInverse n a
      = (do
          let e ← jacobiEigen n a
          fromSpectrum n e) := by
  simp only [symmetricPseudoInverse, fromSpectrum, scaleColumns, bind_assoc, pure_bind]

/-- The complete native post-eigendecomposition kernel succeeds and is close
to the exact spectral reconstruction using the stored vectors and thresholded
real reciprocals. This includes reciprocal rounding, scaling, multiplication
and the final lower-triangle copy. -/
theorem fromSpectrum_accuracy (n : Nat) (e : Spectrum) (hn : n ≤ 12)
    (hs : JacobiConvergence.Stored n e)
    (hc : (1.0e-10 * maxAbs e.values).isFinite = true)
    (hVnorm : ‖matrix n n e.vectors‖ ≤ (1001 / 1000 : ℝ))
    (hretain
      : ∀ j,
          j < n
          → value (1.0e-10 * maxAbs e.values) < |value (e.values.getD j 0.0)|
          → (1 / 8 : ℝ) ≤ value (e.values.getD j 0.0))
    : let r :=
        fun j : Fin n =>
          if value (1.0e-10 * maxAbs e.values) < |value (e.values.getD j.val 0.0)| then
            1 / value (e.values.getD j.val 0.0)
          else
            0
      let V := matrix n n e.vectors
      ∃ result,
        fromSpectrum n e = .ok result
        ∧ result.size = n * n
        ∧ result.all Float.isFinite = true
        ∧ ∀ i j,
            |matrix n n result i j - (V * Matrix.diagonal r * V.transpose) i j|
            ≤ n * (2 : ℝ) ^ (-43 : Int) := by
  have hvb (i j : Nat) (hi : i < n) (hj : j < n) : |value (entry n e.vectors i j)| ≤ 2 :=
    (entry_le_norm (matrix n n e.vectors) ⟨i, hi⟩ ⟨j, hj⟩).trans (hVnorm.trans (by norm_num))
  have hvalues := hs.values_size
  let cutoff := 1.0e-10 * maxAbs e.values
  let r := fun j : Fin n => if value cutoff < |value (e.values.getD j.val 0.0)|
    then 1 / value (e.values.getD j.val 0.0) else 0
  let V := matrix n n e.vectors
  let R := Matrix.diagonal r
  obtain ⟨rs, hrec, hrs, hrf, hr⟩ := reciprocals_success cutoff e.values hc hs.values_finite
    (fun j hj => hretain j (by omega))
  obtain ⟨scaled, hscale, hss, hsf, hsentries⟩ := scaleColumns_success n e.vectors rs
    hs.vectors_size
    hs.vectors_finite hrf hvb (fun j hj => (hr j (by omega)).2)
  have htranspose := Flare.Matrix.Multiplication.transpose_storage n n e.vectors hs.vectors_finite
  have htrans : matrix n n (transpose n n e.vectors) = V.transpose :=
    Flare.Matrix.Multiplication.transpose_matrix n n e.vectors hs.vectors_finite
  have hscaled (i j : Fin n) : |matrix n n scaled i j - (V * R) i j| ≤ (2 : ℝ)^(-45 : Int) := by
    have hrj := (hr j.val (by have := j.isLt; omega)).1
    have hij := (hsentries i.val j.val i.isLt j.isLt).2.1
    have hcoeff : |value (entry n e.vectors i.val j.val) * (value (rs.getD j.val 0.0) - r j)| ≤
        2 * (65 * (2 : ℝ)^(-53 : Int)) := by
      rw [abs_mul]
      exact mul_le_mul (hvb i.val j.val i.isLt j.isLt) hrj (abs_nonneg _) (by norm_num)
    have htarget : (V * R) i j = value (entry n e.vectors i.val j.val) * r j := by
      simp only [R, Matrix.mul_diagonal]
      rfl
    rw [htarget]
    have hid : matrix n n scaled i j - value (entry n e.vectors i.val j.val) * r j =
        (value (entry n scaled i.val j.val) - value (entry n e.vectors i.val j.val) * value (rs.getD
          j.val 0.0)) +
        value (entry n e.vectors i.val j.val) * (value (rs.getD j.val 0.0) - r j) := by
      change value (entry n scaled i.val j.val) - _ = _
      ring
    rw [hid]
    exact ((abs_add_le _ _).trans (add_le_add hij hcoeff)).trans (by norm_num)
  have hRnorm : ‖R‖ ≤ 8 := by
    change ‖Matrix.diagonal r‖ ≤ 8
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro j
    rw [Real.norm_eq_abs]
    by_cases hj : value cutoff < |value (e.values.getD j.val 0.0)|
    · have hret := hretain j.val j.isLt hj
      have hpos : 0 < value (e.values.getD j.val 0.0) := by linarith only [hret]
      simp only [r, ite_eq_left hj]
      rw [abs_of_pos (one_div_pos.mpr hpos)]
      apply (div_le_iff₀ hpos).mpr
      linarith only [hret]
    · simp only [r, ite_eq_right hj, abs_zero]
      norm_num
  have hscaledNorm : ‖matrix n n scaled‖ ≤ (81 / 10 : ℝ) := by
    have he := norm_le_entries (matrix n n scaled - V * R) ((2 : ℝ)^(-45 : Int)) (by positivity)
      hscaled
    have hm := (Matrix.l2_opNorm_mul V R).trans (mul_le_mul hVnorm hRnorm (norm_nonneg _) (by
      norm_num))
    have ht := (norm_le_norm_sub_add (matrix n n scaled) (V * R)).trans (add_le_add he hm)
    have hnR : (n : ℝ) ≤ 12 := by exact_mod_cast hn
    apply ht.trans
    exact (add_le_add (mul_le_mul_of_nonneg_right hnR (by positivity)) le_rfl).trans (by norm_num)
  obtain ⟨product, hproduct, hps, hpf, hp⟩ := Flare.Matrix.Multiplication.multiply_mass_accuracy n n
    n scaled
    (transpose n n e.vectors) 9 (by omega) hsf htranspose.2.1
    (((by norm_num : (9 : ℝ) ≤ (2 : ℝ)^(4 : Int))).trans (zpow_le_zpow_right₀ (by norm_num) (by
      norm_num)))
    (((zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (-1022 : Int) ≤ 0))).trans
      (by norm_num))
    (by
      intro i j hi hj
      rw [← Fin.sum_univ_eq_sum_range (fun k =>
        |value (entry n scaled i k) * value (entry n (transpose n n e.vectors) k j)|) n]
      apply (Flare.Analysis.JacobiNorms.product_mass_le_norm (matrix n n scaled)
        (matrix n n (transpose n n e.vectors)) ⟨i, hi⟩ ⟨j, hj⟩).trans
      rw [htrans, norm_transpose]
      exact (mul_le_mul hscaledNorm hVnorm (norm_nonneg _) (by norm_num)).trans (by norm_num))
  rw [htrans] at hp
  have herror (i j : Fin n) : |matrix n n product i j - (V * R * V.transpose) i j| ≤ n * (2 :
    ℝ)^(-43 : Int) := by
    have hmul
        : |((matrix n n scaled - V * R) * V.transpose) i j| ≤ n * (2 * (2 : ℝ) ^ (-45 : Int)) := by
      rw [Matrix.mul_apply]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc
        _ ≤ ∑ _k : Fin n, (2 : ℝ) ^ (-45 : Int) * 2 := by
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul]
          exact mul_le_mul (hscaled i k) (hvb j.val k.val j.isLt k.isLt) (abs_nonneg _)
            (by positivity)
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
    have hid : matrix n n product i j - (V * R * V.transpose) i j =
        (matrix n n product i j - (matrix n n scaled * V.transpose) i j) +
        ((matrix n n scaled - V * R) * V.transpose) i j := by
      simp only [Matrix.sub_mul, Matrix.sub_apply]
      ring
    rw [hid]
    exact ((abs_add_le _ _).trans (add_le_add (hp i j) hmul)).trans (by
      norm_num
      nlinarith only [Nat.cast_nonneg (α := ℝ) n])
  have hmir : (mirrorLower n product).size = n * n ∧
      (mirrorLower n product).all Float.isFinite = true ∧
      ∀ i j, i < n → j < n → entry n (mirrorLower n product) i j =
        if i < j then entry n product j i else entry n product i j :=
    Flare.Matrix.Storage.mirrorLower_spec n product ⟨hps, hpf⟩
  refine ⟨mirrorLower n product, ?_, hmir.1, hmir.2.1, ?_⟩
  · have hcOk : finite cutoff = .ok cutoff := by simp only [finite, cutoff, hc, ↓reduceIte]
    unfold fromSpectrum
    change (do
      let c ← finite cutoff
      let rs ← e.values.mapM (fun (x : Float) => if c < x.abs then finite (1.0 / x) else pure 0.0)
      let scaled ← scaleColumns n e.vectors rs
      let product ← multiply n n n scaled (transpose n n e.vectors)
      pure (mirrorLower n product)) = .ok (mirrorLower n product)
    rw [hcOk]
    simp only [Except.bind, bind, hrec, hscale, hproduct]
    rfl
  · intro i j
    have hsym : (V * R * V.transpose) i j = (V * R * V.transpose) j i := by
      have ht : (V * R * V.transpose).transpose = V * R * V.transpose := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, R, Matrix.diagonal_transpose,
          Matrix.mul_assoc]
      exact congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j i) ht
    change |value (entry n (mirrorLower n product) i.val j.val) - (V * R * V.transpose) i j| ≤ _
    rw [hmir.2.2 i.val j.val i.isLt j.isLt]
    split_ifs with hij
    · rw [hsym]
      exact herror j i
    · exact herror i j

/-- Complete native spectral inversion is close to a PSD Moore--Penrose
inverse of a nearby matrix. The formation-error premise is explicit and must be
discharged for the supplied native input and real target. Zero target eigenvalues are
allowed; the native input norm floor excludes only the all-zero matrix here. -/
theorem symmetricPseudoInverse_spectral_reconstruction (n : Nat) (input : Array Float)
    (A : Matrix (Fin n) (Fin n) ℝ) (hn : 1 ≤ n) (hn' : n ≤ 12)
    (hs : input.size = n * n) (hf : input.all Float.isFinite = true)
    (hsym : ∀ i j, i < n → j < n → value (entry n input i j) = value (entry n input j i))
    (hb : ∀ i, i < input.size → |value (input.getD i 0.0)| ≤ (2 : ℝ) ^ (500 : Int))
    (hlo : (1 / 8 : ℝ) ≤ ‖matrix n n input‖) (hhi : ‖matrix n n input‖ ≤ (2 : ℝ) ^ (20 : Int))
    (hA : A.PosSemidef) (hgap : (A * A - (1 / 4 : ℝ) • A).PosSemidef)
    (hform : ‖matrix n n input - A‖ ≤ (14 / 1000000000000 : ℝ) * ‖matrix n n input‖)
    : let δ := (32 * n * n : Nat) * (97 * (2 : ℝ) ^ (-53 : Int))
      ∃ result,
        symmetricPseudoInverse n input = .ok result
        ∧ result.size = n * n
        ∧ result.all Float.isFinite = true
        ∧ ∃ B Z : Matrix (Fin n) (Fin n) ℝ,
            B.PosSemidef
            ∧ Flare.Analysis.MoorePenrose B Z
            ∧ Z.PosSemidef
            ∧ ‖Z‖ ≤ 8
            ∧ ‖B - A‖ ≤ (2 / 10000000000 : ℝ) * ‖matrix n n input‖
            ∧ ∃ V W D : Matrix (Fin n) (Fin n) ℝ,
                W ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
                ∧ D.transpose = D
                ∧ ‖D‖ ≤ 8
                ∧ Z = W * D * W.transpose
                ∧ ‖V - W‖ ≤ δ
                ∧ ‖matrix n n result - V * D * V.transpose‖
                  ≤ (n : ℝ) ^ 2 * (2 : ℝ) ^ (-43 : Int) := by
  have : NeZero n := ⟨by omega⟩
  let N := matrix n n input
  let ε := (985 / 10000000000000 : ℝ) * ‖N‖
  let δ := (32 * n * n : Nat) * (97 * (2 : ℝ)^(-53 : Int))
  obtain ⟨e, he, hstored, W, hW, hspec, hV⟩ := jacobiEigen_spectral_sharp n input hn hn' hs hf hsym
    hb
  let d := fun j : Fin n => value (e.values.getD j.val 0.0)
  let θ := value (1.0e-10 * maxAbs e.values)
  let b := fun j => if θ < |d j| then d j else 0
  let R := Matrix.diagonal (fun j => (b j)⁻¹)
  let Z := W * R * W.transpose
  have hspec' : ‖spectrumDiagonal n e - W.transpose * N * W‖ ≤
      (9 / 100000000000 : ℝ) * ‖N‖ + (2 : ℝ)^(-51 : Int) * (2 : ℝ)^(-1022 : Int) :=
    hspec.trans (add_le_add (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg N)) le_rfl)
  have hc := cutoff_from_spectral_enclosure n N W e hstored hW hspec' hlo hhi
  have htiny : (2 : ℝ)^(-51 : Int) * (2 : ℝ)^(-1022 : Int) ≤
      (5 / 10000000000000 : ℝ) * ‖N‖ := by
    have hη : (2 : ℝ)^(-1022 : Int) ≤ 1 := by
      exact zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
    exact (mul_le_mul_of_nonneg_left hη (by positivity)).trans
      ((by norm_num : (2 : ℝ)^(-51 : Int) * 1 ≤ (5 / 10000000000000 : ℝ) * (1 / 8)).trans
        (mul_le_mul_of_nonneg_left hlo (by norm_num)))
  have htotal : ‖Matrix.diagonal d - W.transpose * A * W‖ ≤ ε := by
    have hid : Matrix.diagonal d - W.transpose * A * W =
        (spectrumDiagonal n e - W.transpose * N * W) + W.transpose * (N - A) * W := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]
      change spectrumDiagonal n e - _ = _
      abel
    rw [hid]
    have herror := (norm_add_le _ _).trans (add_le_add hspec
      ((similarity_isometry W (N - A) hW).le.trans hform))
    exact herror.trans (by dsimp [ε]; linarith only [htiny])
  have hεθ : ε ≤ θ := by
    apply le_trans _ hc.2.1
    dsimp [ε]
    exact mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg N)
  have hretain (j : Nat) (hj : j < n) (hkeep : θ < |value (e.values.getD j 0.0)|) :
      (1 / 8 : ℝ) ≤ value (e.values.getD j 0.0) := by
    by_contra hnot
    have hsmall := Flare.Analysis.SpectralGap.orthogonal_diagonal_separation A W d
      (1 / 4) ε hA hgap hW htotal ⟨j, hj⟩ (by dsimp [d]; linarith only [not_le.mp hnot])
    exact (not_lt_of_ge (hsmall.trans hεθ)) hkeep
  have hδ : δ ≤ 1 / 1000 := by
    have hnat : (32 * n * n : Nat) ≤ 4608 := by nlinarith
    have h1 : ((32 * n * n : Nat) : ℝ) ≤ 4608 := by exact_mod_cast hnat
    exact (mul_le_mul_of_nonneg_right h1 (by positivity)).trans
      (by norm_num)
  have hnormV : ‖matrix n n e.vectors‖ ≤ (1001 / 1000 : ℝ) := by
    have hh := (norm_le_norm_sub_add (matrix n n e.vectors) W).trans
      (add_le_add hV (CStarRing.norm_of_mem_unitary hW).le)
    exact hh.trans (by change δ + 1 ≤ 1001 / 1000; linarith only [hδ])
  obtain ⟨result, hresult, hrs, hrf, hr⟩ := fromSpectrum_accuracy n e hn' hstored hc.1 hnormV
    hretain
  have hR : Matrix.diagonal (fun j : Fin n => if θ < |d j| then 1 / d j else 0) = R := by
    congr 1
    funext j
    dsimp [b]
    split_ifs <;> simp only [one_div, _root_.inv_zero]
  change ∀ i j, |matrix n n result i j -
    (matrix n n e.vectors * Matrix.diagonal (fun j => if θ < |d j| then 1 / d j else 0) *
      (matrix n n e.vectors).transpose) i j| ≤ n * (2 : ℝ)^(-43 : Int) at hr
  rw [hR] at hr
  have hnround : ‖matrix n n result - matrix n n e.vectors * R * (matrix n n e.vectors).transpose‖ ≤
      (n : ℝ)^2 * (2 : ℝ)^(-43 : Int) := by
    exact (norm_le_entries _ _ (by positivity) hr).trans_eq (by ring)
  have htrunc := Flare.Analysis.SpectralGap.orthogonal_truncation A W d (1 / 4) ε θ
    (by norm_num) hεθ hA hgap hW htotal
  have hRnorm : ‖R‖ ≤ 8 := by
    have ht := Flare.Analysis.SpectralGap.diagonal_truncation d (1 / 4) ε θ (by norm_num)
      (by dsimp [ε]; positivity) hεθ
      (fun j hj => Flare.Analysis.SpectralGap.orthogonal_diagonal_separation A W d (1 / 4) ε hA hgap
        hW htotal j hj)
    exact ht.2.2.2.1.trans_eq (by norm_num)
  refine ⟨
    result,
    ?_,
    hrs,
    hrf,
    W * Matrix.diagonal b * W.transpose,
    Z,
    htrunc.1,
    htrunc.2.1,
    htrunc.2.2.1,
    htrunc.2.2.2.1.trans_eq (by norm_num),
    ?_,
    ?_
  ⟩
  · rw [symmetricPseudoInverse_eq, he]
    exact hresult
  · apply htrunc.2.2.2.2.trans
    have hθ := hc.2.2
    change ε + θ ≤ _
    dsimp [ε]
    nlinarith only [hθ, norm_nonneg N]
  · exact ⟨matrix n n e.vectors, W, R, hW, Matrix.diagonal_transpose _, hRnorm, rfl, hV, hnround⟩

/-- Native inverse reconstruction around the nearby PSD reference. The
spectral representation is exposed separately for range-aware propagation. -/
theorem symmetricPseudoInverse_backward_error (n : Nat) (input : Array Float)
    (A : Matrix (Fin n) (Fin n) ℝ) (hn : 1 ≤ n) (hn' : n ≤ 12)
    (hs : input.size = n * n) (hf : input.all Float.isFinite = true)
    (hsym : ∀ i j, i < n → j < n → value (entry n input i j) = value (entry n input j i))
    (hb : ∀ i, i < input.size → |value (input.getD i 0.0)| ≤ (2 : ℝ) ^ (500 : Int))
    (hlo : (1 / 8 : ℝ) ≤ ‖matrix n n input‖) (hhi : ‖matrix n n input‖ ≤ (2 : ℝ) ^ (20 : Int))
    (hA : A.PosSemidef) (hgap : (A * A - (1 / 4 : ℝ) • A).PosSemidef)
    (hform : ‖matrix n n input - A‖ ≤ (14 / 1000000000000 : ℝ) * ‖matrix n n input‖)
    : let δ := (32 * n * n : Nat) * (97 * (2 : ℝ) ^ (-53 : Int))
      ∃ result,
        symmetricPseudoInverse n input = .ok result
        ∧ result.size = n * n
        ∧ result.all Float.isFinite = true
        ∧ ∃ B Z : Matrix (Fin n) (Fin n) ℝ,
            B.PosSemidef
            ∧ Flare.Analysis.MoorePenrose B Z
            ∧ Z.PosSemidef
            ∧ ‖Z‖ ≤ 8
            ∧ ‖B - A‖ ≤ (2 / 10000000000 : ℝ) * ‖matrix n n input‖
            ∧ ‖matrix n n result - Z‖
              ≤ (n : ℝ) ^ 2 * (2 : ℝ) ^ (-43 : Int) + 8 * (δ ^ 2 + 2 * δ) := by
  obtain ⟨result, hr, hrs, hrf, B, Z, hB, hBZ, hZ, hZn, hBA, V, W, D, hW, _, hDn, hZeq, hV, hround⟩
    :=
    symmetricPseudoInverse_spectral_reconstruction n input A hn hn' hs hf hsym hb hlo hhi hA hgap
      hform
  refine ⟨result, hr, hrs, hrf, B, Z, hB, hBZ, hZ, hZn, hBA, ?_⟩
  rw [hZeq]
  have hframe := reconstruction_frame_error V W D _ hW hV
  apply (norm_sub_le_norm_sub_add_norm_sub _ (V * D * V.transpose) (W * D * W.transpose)).trans
  exact add_le_add hround (hframe.trans (mul_le_mul_of_nonneg_right hDn (by positivity)))

/-- The all-zero information matrix takes the zero-spectrum branch and still
has native success and a rounding enclosure. No positive spectral magnitude
or matrix-norm floor is imposed on this branch. -/
theorem symmetricPseudoInverse_zero (n : Nat) (input : Array Float) (hn : 1 ≤ n) (hn' : n ≤ 12)
    (hs : input.size = n * n) (hf : input.all Float.isFinite = true)
    (hzero : matrix n n input = 0)
    : ∃ result,
        symmetricPseudoInverse n input = .ok result
        ∧ result.size = n * n
        ∧ result.all Float.isFinite = true
        ∧ ‖matrix n n result‖ ≤ (n : ℝ) ^ 2 * (2 : ℝ) ^ (-43 : Int) := by
  have hentry (i j : Nat) (hi : i < n) (hj : j < n) : value (entry n input i j) = 0 :=
    congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A ⟨i, hi⟩ ⟨j, hj⟩) hzero
  have hflat (i : Nat) (hi : i < input.size) : value (input.getD i 0.0) = 0 := by
    have hdiv : i / n < n := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    have hmod : i % n < n := Nat.mod_lt _ (by omega)
    have he := hentry (i / n) (i % n) hdiv hmod
    change value (input.getD (i / n * n + i % n) 0.0) = 0 at he
    rw [show i / n * n + i % n = i by
      simpa only [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div i n] at he
    exact he
  have hmax : value (maxAbs input) = 0 := le_antisymm
    (Spectrum.maxAbs_le input 0 hf le_rfl (by intro i hi; rw [hflat i hi, abs_zero]))
    (Spectrum.maxAbs_correct input hf).2.1
  have htest : (maxAbs input == 0.0) = true :=
    (beq_iff _ _ (Spectrum.maxAbs_correct input hf).1 (by decide)).mpr hmax
  obtain ⟨e, he, hstored⟩ := JacobiInitialization.jacobiEigen_success n input hn (by omega) hs hf
    (fun i j hi hj => (hentry i j hi hj).trans (hentry j i hj hi).symm)
    (by intro i hi; rw [hflat i hi, abs_zero]; positivity)
  have heq : e = ⟨Array.replicate n 0.0, identity n⟩ := by
    have hresult := he
    rw [JacobiIteration.jacobiEigen_eq, JacobiConvergence.jacobiBySteps_eq] at hresult
    simpa only [htest, ↓reduceIte, pure, Except.pure, Except.ok.injEq] using hresult.symm
  subst e
  have hmaxRep (k : Nat) : maxAbs (Array.replicate k 0.0) = 0.0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
        simp only [maxAbs, Array.replicate_succ, Array.foldl_push] at ih ⊢
        rw [ih]
        decide
  have hc : (1.0e-10 * maxAbs (Array.replicate n 0.0)).isFinite = true := by rw [hmaxRep]; decide
  have hθ : value (1.0e-10 * maxAbs (Array.replicate n 0.0)) = 0 := by
    rw [hmaxRep]
    exact zero_value
  have hnormV : ‖matrix n n (identity n)‖ ≤ (1001 / 1000 : ℝ) := by
    have : NeZero n := ⟨by omega⟩
    rw [JacobiInitialization.identity_matrix]
    norm_num
  obtain ⟨result, hresult, hrs, hrf, hr⟩ := fromSpectrum_accuracy n
    ⟨Array.replicate n 0.0, identity n⟩ hn' hstored hc hnormV (by
      intro j hj hkeep
      simp [hθ, hj, zero_value] at hkeep)
  have hR : Matrix.diagonal (fun j : Fin n =>
      if value (1.0e-10 * maxAbs (Array.replicate n 0.0)) < |value ((Array.replicate n 0.0).getD
        j.val 0.0)|
      then 1 / value ((Array.replicate n 0.0).getD j.val 0.0) else 0) = (0 : Matrix (Fin n) (Fin n)
        ℝ) := by
    simp [hθ, zero_value]
  dsimp only at hr
  rw [hR] at hr
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply, sub_zero] at hr
  refine ⟨result, ?_, hrs, hrf, ?_⟩
  · rw [symmetricPseudoInverse_eq, he]
    exact hresult
  · exact (norm_le_entries _ _ (by positivity) hr).trans_eq (by ring)

/-- Native pseudoinverse success and forward error from a PSD source with the
stated spectral gap and an explicit relative matrix-formation bound. This
includes zero and singular matrices, and derives both the norm floor and exact
inverse conditioning instead of assuming them separately. -/
theorem symmetricPseudoInverse_accuracy (n : Nat) (input : Array Float)
    (A : Matrix (Fin n) (Fin n) ℝ) (hn : 1 ≤ n) (hn' : n ≤ 12)
    (hs : input.size = n * n) (hf : input.all Float.isFinite = true)
    (hsym : ∀ i j, i < n → j < n → value (entry n input i j) = value (entry n input j i))
    (hhi : ‖matrix n n input‖ ≤ (2 : ℝ) ^ (20 : Int))
    (hA : A.PosSemidef) (hgap : (A * A - (1 / 4 : ℝ) • A).PosSemidef)
    (hform : ‖matrix n n input - A‖ ≤ (14 / 1000000000000 : ℝ) * ‖matrix n n input‖)
    : let δ := (32 * n * n : Nat) * (97 * (2 : ℝ) ^ (-53 : Int))
      ∃ result,
        symmetricPseudoInverse n input = .ok result
        ∧ result.size = n * n
        ∧ result.all Float.isFinite = true
        ∧ ∀ X : Matrix (Fin n) (Fin n) ℝ,
            Flare.Analysis.MoorePenrose A X
            → ‖matrix n n result - X‖
              ≤ (n : ℝ) ^ 2 * (2 : ℝ) ^ (-43 : Int)
                + 8 * (δ ^ 2 + 2 * δ)
                + 112 * ((2 / 10000000000 : ℝ) * ‖matrix n n input‖) := by
  let N := matrix n n input
  let δ := (32 * n * n : Nat) * (97 * (2 : ℝ)^(-53 : Int))
  rcases Flare.Analysis.SpectralGap.formed_zero_or_norm_lower_bound A N (1 / 4)
    (14 / 1000000000000) (by norm_num) (by norm_num) hA hgap hform with hzero | hfloor
  · obtain ⟨result, he, hrs, hrf, hr⟩ := symmetricPseudoInverse_zero n input hn hn' hs hf hzero
    have hA0 : A = 0 := by
      have hh := hform
      change ‖N - A‖ ≤ _ * ‖N‖ at hh
      rw [hzero, zero_sub, norm_neg, norm_zero, mul_zero] at hh
      exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg A))
    refine ⟨result, he, hrs, hrf, ?_⟩
    intro X hX
    have hX0 : X = 0 := by
      have hh := hX.2.1
      rw [hA0, Matrix.mul_zero, Matrix.zero_mul] at hh
      exact hh.symm
    rw [hX0, sub_zero]
    apply hr.trans
    have hp : 0 ≤ 8 * (δ^2 + 2 * δ) + 112 * ((2 / 10000000000 : ℝ) * ‖N‖) := by positivity
    simpa only [add_assoc] using le_add_of_nonneg_right (a := (n : ℝ)^2 * (2 : ℝ)^(-43 : Int)) hp
  · have hlo : (1 / 8 : ℝ) ≤ ‖N‖ := (by norm_num : (1 / 8 : ℝ) ≤ (1 / 4) / (1 + 14 /
    1000000000000)).trans hfloor
    have hb (i : Nat) (hi : i < input.size) : |value (input.getD i 0.0)| ≤ (2 : ℝ)^(500 : Int) := by
      have hdiv : i / n < n := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
      have hmod : i % n < n := Nat.mod_lt _ (by omega)
      have he := entry_le_norm N ⟨i / n, hdiv⟩ ⟨i % n, hmod⟩
      change |value (input.getD (i / n * n + i % n) 0.0)| ≤ ‖N‖ at he
      rw [show i / n * n + i % n = i by
        simpa only [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div i n] at he
      exact (he.trans hhi).trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num))
    obtain ⟨result, he, hrs, hrf, B, Z, hB, hBZ, hZ, hZn, hBA, hr⟩ :=
      symmetricPseudoInverse_backward_error n input A hn hn' hs hf hsym hb hlo hhi hA hgap hform
    refine ⟨result, he, hrs, hrf, ?_⟩
    intro X hX
    have hXn : ‖X‖ ≤ 4 := (Flare.Analysis.SpectralGap.pseudoinverse_norm A X (1 / 4)
      (by norm_num) hA hgap hX).trans_eq (by norm_num)
    have hXpsd := Flare.Analysis.MoorePenrose.posSemidef hA hX
    have hdiff :=
      Flare.Analysis.PseudoinversePerturbation.difference_norm A B X Z
        4 8 ((2 / 10000000000 : ℝ) * ‖N‖)
        (by
          simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
            using hA.isHermitian)
        (by
          simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
            using hB.isHermitian)
        (by
          simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
            using hXpsd.isHermitian)
        (by
          simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
            using hZ.isHermitian)
        hX hBZ hXn hZn hBA
    have hdiff' : ‖Z - X‖ ≤ 112 * ((2 / 10000000000 : ℝ) * ‖N‖) := hdiff.trans_eq (by ring)
    exact (norm_sub_le_norm_sub_add_norm_sub _ Z X).trans (add_le_add hr hdiff')

end Flare.Matrix.Pseudoinverse
