import Leader.Wu.Birth.StepAgreementStagesCore

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthB1ResetStepAgreementStages

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
open BirthArrivalCaptureRepair BirthSingleUseReleaseRepair BirthGenerationDone

variable {psi : Nat}

private theorem capture1_frame (l r : AgentState psi) :
    stepPair (captureStep1 l r) = stepPair (l, r) := by
  unfold captureStep1 stepPair stepView
  repeat (first | rfl | split)

private theorem move1_frame (l r : AgentState psi) :
    stepPair (sigMoveStep1 l r) = stepPair (l, r) := by
  unfold sigMoveStep1 stepPair stepView
  repeat (first | rfl | split)

private theorem move2_frame (l r : AgentState psi) :
    stepPair (sigMoveStep2 l r) = stepPair (l, r) := by
  unfold sigMoveStep2 stepPair stepView
  repeat (first | rfl | split)

private theorem move3_frame (l r : AgentState psi) :
    stepPair (sigMoveStep3 l r) = stepPair (l, r) := by
  unfold sigMoveStep3 stepPair stepView
  repeat (first | rfl | split)

private theorem move4_frame (l r : AgentState psi) :
    stepPair (sigMoveStep4 l r) = stepPair (l, r) := by
  unfold sigMoveStep4 stepPair stepView
  repeat (first | rfl | split)

private theorem move5_frame (l r : AgentState psi) :
    stepPair (sigMoveStep5 l r) = stepPair (l, r) := by
  unfold sigMoveStep5 stepPair stepView
  repeat (first | rfl | split)

private theorem holdDone1_frame (l r : AgentState psi) :
    stepPair (holdDoneStep1 l r) = stepPair (l, r) := by
  unfold holdDoneStep1
  split
  · rfl
  · exact capture1_frame l r

private theorem controlTransfers_frame (l r : AgentState psi) :
    stepPair (controlTransfers l r) = stepPair (l, r) := by
  unfold controlTransfers
  dsimp only
  rw [move5_frame, move4_frame, move3_frame, move2_frame]

private theorem doneTransfers_frame (l r : AgentState psi) :
    stepPair (doneTransfers l r) = stepPair (l, r) := by
  unfold doneTransfers
  dsimp only
  rw [controlTransfers_frame, holdDone1_frame]

private theorem sigMoveTransfers_frame (l r : AgentState psi) :
    stepPair (sigMoveTransfers l r) = stepPair (l, r) := by
  unfold sigMoveTransfers
  dsimp only
  rw [move5_frame, move4_frame, move3_frame, move2_frame, move1_frame]

private theorem preclear_frame (hpsi : 0 < psi) (l r : AgentState psi) :
    stepPair (sigMoveLeaderPreclear hpsi l r) = stepPair (l, r) := by
  unfold sigMoveLeaderPreclear clearIfLeader clearComparisonSignal stepPair stepView
  dsimp only
  repeat (first | rfl | split)

private theorem leaderWall_frame (l r : AgentState psi) :
    stepPair (comparisonLeaderWall l r) = stepPair (l, r) := by
  unfold comparisonLeaderWall clearComparisonSignal stepPair stepView
  dsimp only
  repeat (first | rfl | split)

private theorem applyControl_fields_one_unfold
    (hpsi : 0 < psi) (u : AgentState psi) :
    (sigMoveApplyControl hpsi u).leader = u.leader ∧
      (sigMoveApplyControl hpsi u).reset_cmd = u.reset_cmd ∧
      (sigMoveApplyControl hpsi u).echo = u.echo := by
  cases hp : u.path2 with
  | none =>
      simp only [sigMoveApplyControl, hp]
      exact ⟨trivial, trivial, trivial⟩
  | some p =>
      by_cases h1 :
        u.label = (⟨psi - 1, by omega⟩ : Fin psi) ∧
          (p.action = 3 ∨ p.action = 4)
      <;> by_cases h2 :
        u.label = (⟨psi - 1, by omega⟩ : Fin psi) ∧ p.action = 5
      <;> by_cases h3 :
        u.label = (⟨0, hpsi⟩ : Fin psi) ∧ p.action = 6
      <;> simp [sigMoveApplyControl, hp, h1, h2, h3]

private theorem applyControl_view
    (hpsi : 0 < psi) (u : AgentState psi) :
    stepView (sigMoveApplyControl hpsi u) = stepView u := by
  have hl : (sigMoveApplyControl hpsi u).leader = u.leader := by
    exact (applyControl_fields_one_unfold hpsi u).1
  have hz : (sigMoveApplyControl hpsi u).reset_cmd = u.reset_cmd := by
    exact (applyControl_fields_one_unfold hpsi u).2.1
  have he : (sigMoveApplyControl hpsi u).echo = u.echo := by
    exact (applyControl_fields_one_unfold hpsi u).2.2
  unfold stepView
  rw [StepView.mk.injEq]
  exact ⟨hl, hz, he⟩

private theorem controlTail_frame (hpsi : 0 < psi) (l r : AgentState psi) :
    stepPair (sigMoveControlTail hpsi l r) = stepPair (l, r) := by
  have hl : stepView (sigMoveApplyControl hpsi l) = stepView l := by
    exact applyControl_view hpsi l
  have hr : stepView (sigMoveApplyControl hpsi r) = stepView r := by
    exact applyControl_view hpsi r
  unfold sigMoveControlTail
  simp only []
  split
  · split
    · unfold stepPair
      exact Prod.ext hl hr
    · unfold stepPair
      exact Prod.ext hl hr
  · unfold stepPair
    exact Prod.ext hl hr

private theorem clearRelease_view
    (hpsi : 0 < psi) (u : AgentState psi) :
    stepView (clearTerminalRelease hpsi u) = stepView u := by
  unfold clearTerminalRelease
  repeat (first | rfl | split)

private theorem singleUseTail_frame (hpsi : 0 < psi) (l r : AgentState psi) :
    stepPair (singleUseControlTail hpsi l r) = stepPair (l, r) := by
  calc
    stepPair (singleUseControlTail hpsi l r) =
        stepPair
          (clearTerminalRelease hpsi (sigMoveControlTail hpsi l r).1,
            clearTerminalRelease hpsi (sigMoveControlTail hpsi l r).2) := by
      exact congrArg stepPair (singleUseControlTail_eq_clear hpsi l r)
    _ = stepPair (sigMoveControlTail hpsi l r) := by
      unfold stepPair
      exact Prod.ext
        (clearRelease_view hpsi (sigMoveControlTail hpsi l r).1)
        (clearRelease_view hpsi (sigMoveControlTail hpsi l r).2)
    _ = stepPair (l, r) := controlTail_frame hpsi l r

private theorem b1_done_frame (hpsi : 0 < psi) (l r : AgentState psi) :
    stepPair (doneCaptureSigMove hpsi l r) = stepPair (l, r) := by
  unfold doneCaptureSigMove
  dsimp only
  rw [singleUseTail_frame, leaderWall_frame, doneTransfers_frame, preclear_frame]

private theorem wall_before_control_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    stepPair (sigMoveLeaderBeforeControl hpsi l r) = stepPair (l, r) := by
  unfold sigMoveLeaderBeforeControl
  dsimp only
  rw [leaderWall_frame, sigMoveTransfers_frame, preclear_frame]

private theorem wall_done_frame (hpsi : 0 < psi) (l r : AgentState psi) :
    stepPair (sigMoveLeaderWall hpsi l r) = stepPair (l, r) := by
  unfold sigMoveLeaderWall
  dsimp only
  rw [controlTail_frame, wall_before_control_frame]

/-- DONE uses the same leader/reset/echo action as the wall-aware SIGMOVE. -/
theorem done_stage (hpsi : 0 < psi) (l r : AgentState psi) :
    stepPair (doneCaptureSigMove hpsi l r) =
      stepPair (sigMoveLeaderWall hpsi l r) :=
  (b1_done_frame hpsi l r).trans (wall_done_frame hpsi l r).symm

end BirthB1ResetStepAgreementStages

#print axioms BirthB1ResetStepAgreementStages.done_stage
