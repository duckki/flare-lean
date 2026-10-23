module

import Flare

/-! A module-system client can use the public entry point and unfold exported definitions. -/

example (x : Float) : Flare.Binary64.Value.toReal x = Flare.Binary64.Value.modelToReal x.toModel :=
  rfl

example (columns : Nat) (a : Array Float) (row column : Nat)
    : Flare.Matrix.Dense.entry columns a row column = a.getD (row * columns + column) 0.0 :=
  rfl

#check Flare.Analysis.PseudoinversePerturbation.difference_norm
#check Flare.Binary64.Nearest.add_error_nearest
#check Flare.Matrix.Pseudoinverse.symmetricPseudoInverse_accuracy

open Std.Do in
example (x : Float) : ⦃⌜True⌝⦄ Flare.Matrix.Dense.finite x ⦃⇓? y => ⌜y.isFinite = true⌝⦄ :=
  Flare.Matrix.Storage.finite_spec x

-- A local additive allowance must be carried through every iteration.
private theorem biased_fold_bound (xs : List ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    : |xs.foldl (fun n x => n + x + δ) 0 - xs.foldl (fun i x => i + x) 0| ≤ xs.length * δ := by
  have h := Flare.Analysis.ErrorRecurrence.foldl_error_bound
    (fun n x : ℝ => n + x + δ) (fun i x : ℝ => i + x)
    (fun _ _ => True) (fun _ => True) (fun n i => |n - i|)
    1 δ 0 (by norm_num) xs.length ?_ xs (by simp) (by omega) 0 0 trivial (by simp)
  · have hb := Flare.Analysis.ErrorRecurrence.nonexpansive_budget 1 δ 0
      (by norm_num) (by norm_num) hδ (by norm_num) xs.length
    exact h.2.trans (by simpa using hb)
  · intro k hk x hx n i hi
    refine ⟨trivial, ?_⟩
    have he : n + x + δ - (i + x) = (n - i) + δ := by ring
    simpa only [he, abs_of_nonneg hδ, one_mul] using abs_add_le (n - i) δ

example (δ : ℝ) (hδ : 0 ≤ δ)
    : |(List.replicate 16 (1 : ℝ)).foldl (fun n x => n + x + δ) 0
        - (List.replicate 16 (1 : ℝ)).foldl (fun i x => i + x) 0|
      ≤ 16 * δ := by
  simpa using biased_fold_bound (List.replicate 16 1) δ hδ

example (δ : ℝ) (hδ : 0 ≤ δ)
    : |(List.replicate 48 (1 : ℝ)).foldl (fun n x => n + x + δ) 0
        - (List.replicate 48 (1 : ℝ)).foldl (fun i x => i + x) 0|
      ≤ 48 * δ := by
  simpa using biased_fold_bound (List.replicate 48 1) δ hδ

example (δ : ℝ) (hδ : 0 ≤ δ)
    : |(List.replicate 128 (1 : ℝ)).foldl (fun n x => n + x + δ) 0
        - (List.replicate 128 (1 : ℝ)).foldl (fun i x => i + x) 0|
      ≤ 128 * δ := by
  simpa using biased_fold_bound (List.replicate 128 1) δ hδ

example (rows inner columns : Nat) (a b result : Array Float)
    (h : Flare.Matrix.Dense.multiply rows inner columns a b = .ok result)
    : result = Flare.Matrix.OrderedProduct.product rows inner columns a b :=
  Flare.Matrix.OrderedProduct.multiply_eq rows inner columns a b result h
