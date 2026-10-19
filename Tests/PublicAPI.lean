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
