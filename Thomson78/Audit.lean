import Thomson78
import Thomson78.AnalysisAudit
import Thomson78.EightGeometryAxioms
import Lean.Util.CollectAxioms

/-! Inspect every public theorem in the project namespace, including auxiliary
theorems. This command audits dependencies; it does not construct proofs. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Thomson78).isPrefixOf name then
      if let .thmInfo _ := info then
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Unexpected axiom {ax} in {name}"
        logInfo m!"AUDIT {name}: {axioms}"
        count := count + 1
  logInfo m!"AUDIT_OK: {count} project theorems; only propext, Classical.choice, Quot.sound."
