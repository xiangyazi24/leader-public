import Leader.Wu.Safety.NoCheckBirthRepair
import Leader.Wu.Safety.ConcreteProtocolProperties

set_option autoImplicit false
set_option Elab.async false

namespace ZZEliminateFrame

open PPLL PPLLRepair PPLLVerify PPLLNoCheckBirthRepair

/-!
# Public re-export of the `eliminateLeadersNoCollision` label frame

`Leader/Wu/Birth/LeaderlessFixedLabelFrames.lean` proves

  `leaderless_edgewiseFixed_forces_successor_labels`

with exactly one remaining hypothesis, `hEliminate`, which is verbatim the
statement below.  A proof already exists in the repository, but it is
`private` at `Leader/Wu/Safety/NoCheckBirthLeaderFrames.lean:291-296`, so no downstream
module can discharge the hypothesis with it.  That module also carries a
twelve-module import chain that has never compiled end to end.

This file re-proves the frame publicly against the defining module
`Leader/Wu/Protocol/Repairs.lean:289`, so the F3 conclusion becomes unconditional.
-/

theorem eliminateLeadersNoCollision_labels_eq
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollision hψ l r).1.label = l.label ∧
      (eliminateLeadersNoCollision hψ l r).2.label = r.label := by
  simp [eliminateLeadersNoCollision]

#print axioms eliminateLeadersNoCollision_labels_eq

end ZZEliminateFrame
