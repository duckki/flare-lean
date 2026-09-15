import Flare
import Lean.Util.CollectAxioms

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
  Lean.logInfo (m!"Audited {publicCount} public and {privateCount} private FLARE "
    ++ m!"theorem declarations (including generated declarations); "
    ++ m!"only propext, Classical.choice, "
    ++ m!"and Quot.sound are permitted.")
