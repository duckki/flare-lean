module

import all Flare.Analysis.Conditioning
import all Flare.Analysis.Dyadic
import all Flare.Analysis.EntrywiseError
import all Flare.Analysis.ErrorRecurrence
import all Flare.Analysis.Factorization
import all Flare.Analysis.GramBounds
import all Flare.Analysis.Householder
import all Flare.Analysis.Jacobi
import all Flare.Analysis.JacobiDiagonal
import all Flare.Analysis.JacobiEnergy
import all Flare.Analysis.JacobiNorms
import all Flare.Analysis.JacobiRotation
import all Flare.Analysis.LinearSolve
import all Flare.Analysis.MatrixError
import all Flare.Analysis.MoorePenrose
import all Flare.Analysis.NumericalBounds
import all Flare.Analysis.PseudoinversePerturbation
import all Flare.Analysis.SchurComplement
import all Flare.Analysis.SpectralGap
import all Flare.Analysis.SpectralPerturbation
import all Flare.Binary64.Arithmetic
import all Flare.Binary64.Congruence
import all Flare.Binary64.Division
import all Flare.Binary64.Memory
import all Flare.Binary64.Model.Arithmetic
import all Flare.Binary64.Model.Conversion
import all Flare.Binary64.Model.NaturalConversion
import all Flare.Binary64.Model.Rounding
import all Flare.Binary64.Model.Value
import all Flare.Binary64.Nearest
import all Flare.Binary64.NaturalConversion
import all Flare.Binary64.Order
import all Flare.Binary64.Pipeline
import all Flare.Binary64.Rounding
import all Flare.Binary64.SignMultiplication
import all Flare.Binary64.Sqrt
import all Flare.Binary64.Value
import all Flare.Binary64.Zero
import all Flare.Matrix.Dense
import all Flare.Matrix.Error
import all Flare.Matrix.Factorization
import all Flare.Matrix.GramFormation
import all Flare.Matrix.GramSymmetry
import all Flare.Matrix.Jacobi
import all Flare.Matrix.JacobiAccumulation
import all Flare.Matrix.JacobiBounds
import all Flare.Matrix.JacobiConvergence
import all Flare.Matrix.JacobiDiagonal
import all Flare.Matrix.JacobiEnergy
import all Flare.Matrix.JacobiInitialization
import all Flare.Matrix.JacobiIteration
import all Flare.Matrix.JacobiOutput
import all Flare.Matrix.JacobiPrecision
import all Flare.Matrix.JacobiSpectral
import all Flare.Matrix.LinearSolve
import all Flare.Matrix.MatrixFormation
import all Flare.Matrix.Multiplication
import all Flare.Matrix.OperationStorage
import all Flare.Matrix.Operations
import all Flare.Matrix.OrderedProduct
import all Flare.Matrix.PSDCheck
import all Flare.Matrix.PositiveDefiniteFactorization
import all Flare.Matrix.Pseudoinverse
import all Flare.Matrix.SolveAccuracy
import all Flare.Matrix.Spectrum
import all Flare.Matrix.Specification
import all Flare.Matrix.Storage
import all Flare.Matrix.Substitution
import all Flare.Matrix.Value
meta import Lean.Util.CollectAxioms
meta import Lean.Elab.Command

/-! Audit every FLARE theorem, including private supporting lemmas. -/

set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut publicCount : Nat := 0
  let mut privateCount : Nat := 0
  for (name, info) in env.constants.toList do
    let userName := (Lean.privateToUserName? name).getD name
    if (`Flare).isPrefixOf userName then
      match info with
      | .axiomInfo _ => throwError "FLARE declares an axiom: {name}"
      | .thmInfo _ =>
        for axiomName in ← Lean.collectAxioms name do
          unless allowed.contains axiomName do
            throwError "Unexpected axiom {axiomName} in {name}"
        if name == userName then
          publicCount := publicCount + 1
        else
          privateCount := privateCount + 1
      | _ => pure ()
  unless publicCount > 0 do
    throwError "No FLARE theorems found; the audit would be empty."
  unless privateCount > 0 do
    throwError "No private FLARE theorems found; the audit would be incomplete."
  Lean.logInfo (m!"Audited {publicCount} public and {privateCount} private FLARE "
    ++ m!"theorem declarations (including generated declarations); "
    ++ m!"only propext, Classical.choice, "
    ++ m!"and Quot.sound are permitted.")
