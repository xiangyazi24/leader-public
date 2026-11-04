import Leader.Wu.Protocol.Repairs

/-!
The production writers do not themselves test that the old payload is empty.
The Start stage tests emptiness only when setting a new `produce` state.
An inherited `produce` state can therefore overwrite an occupied payload.
This is a stage-level scope check, not a full-host reachability claim or a
runtime lower bound. A lineage-loss proof must count such an overwrite as a
new generation event, or derive the absence of `produce` on its reachable cut.
-/

set_option autoImplicit false

namespace BirthGenerationOverwriteAudit

open PPLL PPLLRepair

/-- A present terminal payload can be replaced by the actual emission row.
No arbitrary auxiliary field is constrained. -/
theorem emit_overwrites_present (l r : AgentState 2) :
    let old := { r with label := (1 : Fin 2), state := .produce, path := .some 1 0, bit := true }
    old.path ≠ .bot ∧
      (genSigSaturatedEmit (by decide) l old).2.path = .some 1 1 ∧
      (genSigSaturatedEmit (by decide) l old).2.path ≠ old.path := by
  simp [genSigSaturatedEmit]

/-- Start does not sanitize an inherited production state. The full GEN
suffix after WAIT therefore has the same occupied-payload overwrite. -/
theorem after_wait_overwrites_present (l r : AgentState 2) :
    let left := { l with leader := true, label := (0 : Fin 2), state := .none }
    let right := { r with label := (1 : Fin 2), state := .produce, path := .some 1 0, bit := true }
    right.path ≠ .bot ∧
      (genSigSaturatedAfterWait (by decide) left right).2.path = .some 1 1 ∧
      (genSigSaturatedAfterWait (by decide) left right).2.path ≠ right.path := by
  simp [genSigSaturatedAfterWait, genSigSaturatedStart, genSigSaturatedEmit,
    genSigSaturatedPropagate, genSigSaturatedFinish]

end BirthGenerationOverwriteAudit

#print axioms BirthGenerationOverwriteAudit.emit_overwrites_present
#print axioms BirthGenerationOverwriteAudit.after_wait_overwrites_present
