import Leader.Wu.Birth.StepAgreementStagesCore


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace BirthB1ResetStepAgreementStages


open PPLL PPLLRepair PPLLWallSweepRepair
open BirthShortWait BirthShortWaitTerminalEntryRepair


variable {psi : Nat}


private theorem wait_false_projection (u : AgentState psi) :
    ({ u with wait := false }).wait = false := by
  rfl


private theorem prepare_frame (hpsi : 0 < psi) (l r : AgentState psi) :
    stepPair (waitSaturatedPrepare hpsi l r) = stepPair (l, r) := by
  unfold waitSaturatedPrepare stepPair stepView
  repeat (first | rfl | split)


private theorem inactive_frame (h2 : 2 ≤ psi) (l r : AgentState psi) :
    stepPair (terminalInactiveClear (by decide : 0 < 2) h2 l r) =
      stepPair (l, r) := by
  unfold terminalInactiveClear stepPair stepView
  repeat (first | rfl | split)


private theorem width_carry_frame
    (h2 : 2 ≤ psi) (kappa : Nat) (l r : AgentState psi) :
    stepPair (waitWidthCarry (by decide : 0 < 2) h2 kappa l r) =
      stepPair (l, r) := by
  unfold waitWidthCarry stepPair stepView
  repeat (first | rfl | split)


private theorem width_reset_frame (h2 : 2 ≤ psi) (l r : AgentState psi) :
    stepPair (waitWidthReset (by decide : 0 < 2) h2 l r) =
      stepPair (l, r) := by
  unfold waitWidthReset stepPair stepView
  repeat (first | rfl | split)


private theorem width_finish_frame
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (kappa : Nat)
    (l r : AgentState psi) :
    stepPair (waitWidthFinish hpsi (by decide : 0 < 2) h2 kappa l r) =
      stepPair (l, r) := by
  unfold waitWidthFinish
  split
  · let r0 : AgentState psi := { r with wait := false }
    have hwait : r0.wait = false := by
      exact wait_false_projection r
    change stepPair
      (if r0.wait = false ∧
          l.label ≠ (⟨psi - 1, by omega⟩ : Fin psi) then
        ({ l with wait := false }, { r0 with wait := true })
      else (l, r0)) = stepPair (l, r)
    rw [hwait]
    split <;> rfl
  · change stepPair
      (if r.wait = false ∧
          l.label ≠ (⟨psi - 1, by omega⟩ : Fin psi) then
        ({ l with wait := false }, { r with wait := true })
      else (l, r)) = stepPair (l, r)
    split <;> rfl


private theorem wall_carry_frame
    (hpsi : 0 < psi) (kappa : Nat) (l r : AgentState psi) :
    stepPair (waitSaturatedCarry hpsi kappa l r) = stepPair (l, r) := by
  unfold waitSaturatedCarry stepPair stepView
  repeat (first | rfl | split)


private theorem wall_reset_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    stepPair (waitSaturatedReset hpsi l r) = stepPair (l, r) := by
  unfold waitSaturatedReset stepPair stepView
  repeat (first | rfl | split)


private theorem wall_finish_frame
    (hpsi : 0 < psi) (kappa : Nat) (l r : AgentState psi) :
    stepPair (waitSaturatedFinish hpsi kappa l r) = stepPair (l, r) := by
  unfold waitSaturatedFinish
  split
  · let r0 : AgentState psi := { r with wait := false }
    have hwait : r0.wait = false := by
      exact wait_false_projection r
    change stepPair
      (if r0.wait = false ∧
          l.label ≠ (⟨psi - 1, by omega⟩ : Fin psi) then
        ({ l with wait := false }, { r0 with wait := true })
      else (l, r0)) = stepPair (l, r)
    rw [hwait]
    split <;> rfl
  · change stepPair
      (if r.wait = false ∧
          l.label ≠ (⟨psi - 1, by omega⟩ : Fin psi) then
        ({ l with wait := false }, { r with wait := true })
      else (l, r)) = stepPair (l, r)
    split <;> rfl


private theorem b1_wait_frame
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (kappa : Nat)
    (l r : AgentState psi) :
    stepPair (waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r) =
      stepPair (l, r) := by
  let q0 := waitSaturatedPrepare hpsi l r
  let qc := terminalInactiveClear (by decide : 0 < 2) h2 q0.1 q0.2
  let q1 := waitWidthCarry (by decide : 0 < 2) h2 kappa qc.1 qc.2
  let q2 := waitWidthReset (by decide : 0 < 2) h2 q1.1 q1.2
  change stepPair
      (waitWidthFinish hpsi (by decide : 0 < 2) h2 kappa q2.1 q2.2) =
    stepPair (l, r)
  calc
    _ = stepPair q2 := width_finish_frame hpsi h2 kappa q2.1 q2.2
    _ = stepPair q1 := width_reset_frame h2 q1.1 q1.2
    _ = stepPair qc := width_carry_frame h2 kappa qc.1 qc.2
    _ = stepPair q0 := inactive_frame h2 q0.1 q0.2
    _ = stepPair (l, r) := prepare_frame hpsi l r


private theorem wall_wait_frame
    (hpsi : 0 < psi) (kappa : Nat) (l r : AgentState psi) :
    stepPair (waitSaturated hpsi kappa l r) = stepPair (l, r) := by
  let q0 := waitSaturatedPrepare hpsi l r
  let q1 := waitSaturatedCarry hpsi kappa q0.1 q0.2
  let q2 := waitSaturatedReset hpsi q1.1 q1.2
  change stepPair (waitSaturatedFinish hpsi kappa q2.1 q2.2) =
    stepPair (l, r)
  calc
    _ = stepPair q2 := wall_finish_frame hpsi kappa q2.1 q2.2
    _ = stepPair q1 := wall_reset_frame hpsi q1.1 q1.2
    _ = stepPair q0 := wall_carry_frame hpsi kappa q0.1 q0.2
    _ = stepPair (l, r) := prepare_frame hpsi l r


private theorem shortened_wait_frame
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (kappa : Nat)
    (l r : AgentState psi) :
    stepPair (waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r) =
      stepPair (waitSaturated hpsi kappa l r) :=
  (b1_wait_frame hpsi h2 kappa l r).trans
    (wall_wait_frame hpsi kappa l r).symm


theorem shortened_wait_leader
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (kappa : Nat)
    (l r : AgentState psi) :
    (waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r).1.leader =
        (waitSaturated hpsi kappa l r).1.leader ∧
      (waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r).2.leader =
        (waitSaturated hpsi kappa l r).2.leader := by
  have h :
      stepPair (waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r) =
        stepPair (waitSaturated hpsi kappa l r) := by
    exact shortened_wait_frame hpsi h2 kappa l r
  exact ⟨congrArg (fun q => q.1.leader) h,
    congrArg (fun q => q.2.leader) h⟩


theorem shortened_wait_reset_cmd
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (kappa : Nat)
    (l r : AgentState psi) :
    (waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r).1.reset_cmd =
        (waitSaturated hpsi kappa l r).1.reset_cmd ∧
      (waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r).2.reset_cmd =
        (waitSaturated hpsi kappa l r).2.reset_cmd := by
  have h :
      stepPair (waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r) =
        stepPair (waitSaturated hpsi kappa l r) := by
    exact shortened_wait_frame hpsi h2 kappa l r
  exact ⟨congrArg (fun q => q.1.reset) h,
    congrArg (fun q => q.2.reset) h⟩


theorem shortened_wait_echo
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (kappa : Nat)
    (l r : AgentState psi) :
    (waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r).1.echo =
        (waitSaturated hpsi kappa l r).1.echo ∧
      (waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r).2.echo =
        (waitSaturated hpsi kappa l r).2.echo := by
  have h :
      stepPair (waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r) =
        stepPair (waitSaturated hpsi kappa l r) := by
    exact shortened_wait_frame hpsi h2 kappa l r
  exact ⟨congrArg (fun q => q.1.echo) h,
    congrArg (fun q => q.2.echo) h⟩


theorem shortened_wait_stage
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (kappa : Nat)
    (l r : AgentState psi) :
    stepPair (waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r) =
      stepPair (waitSaturated hpsi kappa l r) := by
  have hl := shortened_wait_leader hpsi h2 kappa l r
  have hz := shortened_wait_reset_cmd hpsi h2 kappa l r
  have he := shortened_wait_echo hpsi h2 kappa l r
  unfold stepPair stepView
  apply Prod.ext
  · rw [StepView.mk.injEq]
    exact ⟨hl.1, hz.1, he.1⟩
  · rw [StepView.mk.injEq]
    exact ⟨hl.2, hz.2, he.2⟩


end BirthB1ResetStepAgreementStages


#print axioms BirthB1ResetStepAgreementStages.shortened_wait_leader
#print axioms BirthB1ResetStepAgreementStages.shortened_wait_reset_cmd
#print axioms BirthB1ResetStepAgreementStages.shortened_wait_echo
#print axioms BirthB1ResetStepAgreementStages.shortened_wait_stage
