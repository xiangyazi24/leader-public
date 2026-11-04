import Leader.Wu.Birth.StepAgreementStagesCore

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthB1ResetStepAgreementStages

open PPLL PPLLRepair PPLLWallSweepRepair
open BirthShortWait

variable {psi : Nat}

private def suppressTail
    (hpsi : 0 < psi) (l r : AgentState psi) :
    AgentState psi × AgentState psi :=
  let q2 := suppressSigTerminal hpsi l r
  let q3 := suppressSigEcho q2.1 q2.2
  suppressSigFinish q3.1 q3.2

private theorem suppress_tail_right_count_leader
    (hpsi : 0 < psi) (l r : AgentState psi) :
    (suppressTail hpsi l { r with count := 0 }).1.leader =
        (suppressTail hpsi l r).1.leader ∧
      (suppressTail hpsi l { r with count := 0 }).2.leader =
        (suppressTail hpsi l r).2.leader := by
  unfold suppressTail suppressSigTerminal suppressSigEcho suppressSigFinish
  dsimp only
  repeat (first | constructor | rfl | split)

private theorem suppress_tail_right_count_reset_cmd
    (hpsi : 0 < psi) (l r : AgentState psi) :
    (suppressTail hpsi l { r with count := 0 }).1.reset_cmd =
        (suppressTail hpsi l r).1.reset_cmd ∧
      (suppressTail hpsi l { r with count := 0 }).2.reset_cmd =
        (suppressTail hpsi l r).2.reset_cmd := by
  unfold suppressTail suppressSigTerminal suppressSigEcho suppressSigFinish
  dsimp only
  repeat (first | constructor | rfl | split)

private theorem suppress_tail_right_count_echo
    (hpsi : 0 < psi) (l r : AgentState psi) :
    (suppressTail hpsi l { r with count := 0 }).1.echo =
        (suppressTail hpsi l r).1.echo ∧
      (suppressTail hpsi l { r with count := 0 }).2.echo =
        (suppressTail hpsi l r).2.echo := by
  unfold suppressTail suppressSigTerminal suppressSigEcho suppressSigFinish
  dsimp only
  repeat (first | constructor | rfl | split)

private theorem suppress_tail_right_count_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    stepPair (suppressTail hpsi l { r with count := 0 }) =
      stepPair (suppressTail hpsi l r) := by
  have hl := suppress_tail_right_count_leader hpsi l r
  have hz := suppress_tail_right_count_reset_cmd hpsi l r
  have he := suppress_tail_right_count_echo hpsi l r
  unfold stepPair stepView
  apply Prod.ext
  · rw [StepView.mk.injEq]
    exact ⟨hl.1, hz.1, he.1⟩
  · rw [StepView.mk.injEq]
    exact ⟨hl.2, hz.2, he.2⟩

private theorem short_count_tail_frame
    (hpsi : 0 < psi) (h2 : 2 <= psi) (l r : AgentState psi) :
    let q := shortCountReset (by decide : 0 < 2) h2 l r
    stepPair (suppressTail hpsi q.1 q.2) =
      stepPair (suppressTail hpsi l r) := by
  unfold shortCountReset
  split
  · exact suppress_tail_right_count_frame hpsi l r
  · rfl

/-- The width-two count insertion in SUPPRESS is invisible to the wall frame. -/
theorem suppress_stage
    (hpsi : 0 < psi) (h2 : 2 <= psi) (l r : AgentState psi) :
    stepPair
        (suppressSigResetKillWidth hpsi (by decide : 0 < 2) h2 l r) =
      stepPair (suppressSigResetKill hpsi l r) := by
  change
    stepPair
        (suppressTail hpsi
          (shortCountReset (by decide : 0 < 2) h2
            (suppressPrefix l r).1 (suppressPrefix l r).2).1
          (shortCountReset (by decide : 0 < 2) h2
            (suppressPrefix l r).1 (suppressPrefix l r).2).2) =
      stepPair
        (suppressTail hpsi (suppressPrefix l r).1 (suppressPrefix l r).2)
  exact short_count_tail_frame hpsi h2
    (suppressPrefix l r).1 (suppressPrefix l r).2

end BirthB1ResetStepAgreementStages

#print axioms BirthB1ResetStepAgreementStages.suppress_stage
