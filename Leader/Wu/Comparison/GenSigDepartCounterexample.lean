import Leader.Wu.Birth.LeaderlessEscapeCleanBotRepairs

set_option autoImplicit false
set_option Elab.async false

namespace ZZStep2C

open PPLL PPLLRepair

/-!
WAIT local frames.

These deliberately project one field at a time and discharge the nested
conditionals by `split + rfl`.  In particular, there is no whole-row
`simp [wait]`.
-/

private theorem h2 : 0 < 2 := by decide

def badL : AgentState 2 :=
  { BoundedAgentState.erase Q16405.s with
      leader := false,
      label := (0 : Fin 2),
      path := PathInfo.bot,
      wait := false,
      state := MainState.none,
      reset := false,
      carry := false,
      count := 0,
      h_field := false }

def badR : AgentState 2 :=
  { BoundedAgentState.erase Q16405.s with
      leader := false,
      label := (1 : Fin 2),
      path := PathInfo.some 1 0,
      wait := true,
      state := MainState.done,
      reset := false,
      carry := false,
      count := 0,
      h_field := false }

theorem badL_has_requested_hypotheses :
    badL.leader = false ∧
    badL.label = (0 : Fin 2) ∧
    badL.path = PathInfo.bot ∧
    badL.wait = false ∧
    badL.state ≠ MainState.done := by
  decide +kernel

/--
Exact full-stage result.

Trace:
  WAIT preserves the relevant left fields;
  source-start makes badL produce;
  badR already has state=done and a non-bottom path, so it stays done;
  backward completion makes badL done;
  label-zero finish immediately makes badL depart.
-/
theorem repairedA_full_stage_is_depart :
    (ZZRepairAll8.genSigRepairedA h2 2 badL badR).1.state =
      MainState.depart := by
  decide +kernel

/-- The original Algorithm-4 `genSig` has the same counterexample. -/
theorem original_genSig_full_stage_is_depart :
    (genSig h2 2 badL badR).1.state = MainState.depart := by
  decide +kernel

/-- Hence the requested stronger universal final-output theorem is false. -/
theorem requested_full_statement_false :
    ¬ (∀ (u r : AgentState 2),
        u.leader = false →
        u.label = (0 : Fin 2) →
        u.path = PathInfo.bot →
        u.wait = false →
        u.state ≠ MainState.done →
        (ZZRepairAll8.genSigRepairedA h2 2 u r).1.state =
          MainState.produce) := by
  intro H
  have hh := badL_has_requested_hypotheses
  have hout := H badL badR
    hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2
  rw [repairedA_full_stage_is_depart] at hout
  cases hout

#print axioms ZZStep2C.badL_has_requested_hypotheses
#print axioms ZZStep2C.repairedA_full_stage_is_depart
#print axioms ZZStep2C.original_genSig_full_stage_is_depart
#print axioms ZZStep2C.requested_full_statement_false

end ZZStep2C
