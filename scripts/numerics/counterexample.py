"""The maintained scalar covariance counterexample, emitted from its admitted source.

This is a specific authored proof, not an automatic counterexample finder.
"""
from .emit import kernel_source
from .frontend import parse


# The generated kernel retains the Python source's operation order. This saved
# argument proves an admissible witness and its exact reference, then audits the root.
ARGUMENT = '''
namespace NaiveCovarianceFailure

open Flare.Binary64.Value

def noise : Float := Float.ofBits 0x3c90000000000000

def inDomain (p r : Float) : Prop :=
  p.isFinite = true ∧ r.isFinite = true ∧
  1 ≤ value p ∧ value p ≤ 2 ∧
  1 / (2 : ℝ) ^ 54 ≤ value r ∧ value r ≤ 1 / (2 : ℝ) ^ 53

theorem noise_value : value noise = 1 / (2 : ℝ) ^ 54 := by
  change (4503599627370496 : ℝ) * (2 : ℝ) ^ (-106 : Int) = _
  norm_num

theorem valid_input : inDomain 1.0 noise := by
  unfold inDomain
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  rw [Flare.Binary64.Arithmetic.one_value, noise_value]
  norm_num

theorem rounded_zero : Workflow.kernel 1.0 noise = 0.0 := by
  decide +kernel

theorem exact_value :
    Workflow.specification (value (1.0 : Float)) (value noise)
      = 1 / ((2 : ℝ) ^ 54 + 1) := by
  unfold Workflow.specification
  rw [Flare.Binary64.Arithmetic.one_value, noise_value]
  norm_num

theorem failure : inDomain 1.0 noise ∧
    value (Workflow.kernel 1.0 noise) = 0 ∧
    0 < Workflow.specification (value (1.0 : Float)) (value noise) := by
  refine ⟨valid_input, ?_, ?_⟩
  · rw [rounded_zero, Flare.Binary64.Arithmetic.zero_value]
  · rw [exact_value]
    positivity

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in ← Lean.collectAxioms ``failure do
    unless allowed.contains axiomName do
      throwError "Unexpected counterexample axiom: {axiomName}"
  Lean.logInfo "Checked NaiveCovarianceFailure.failure and its transitive axioms."

end NaiveCovarianceFailure
'''


def certificate_source(source):
    program = parse('python', source, 'posterior_variance')
    source = kernel_source(program, ['p * r / (p + r)'])
    imports = '''public import Flare.Binary64.Arithmetic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
meta import Lean.Util.CollectAxioms
meta import Lean.Elab.Command'''
    source = source.replace('public import Flare.Binary64.Value', imports)
    return source + '\nset_option maxRecDepth 10000\n' + ARGUMENT
