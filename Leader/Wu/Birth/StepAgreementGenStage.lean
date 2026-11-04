import Leader.Wu.Birth.StepAgreementStagesCore

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthB1ResetStepAgreementStages

open PPLL PPLLRepair
open BirthGenerationControlRepair

variable {psi : Nat}

private theorem gen_start_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    stepPair (genSigSaturatedStart hpsi l r) = stepPair (l, r) := by
  unfold stepPair stepView
  apply Prod.ext <;> rw [StepView.mk.injEq]
  all_goals
    unfold genSigSaturatedStart
    dsimp only
    repeat (first | rfl | constructor | split)

private theorem gen_clean_emit_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    stepPair (genCleanEmit hpsi l r) = stepPair (l, r) := by
  unfold stepPair stepView
  apply Prod.ext <;> rw [StepView.mk.injEq]
  all_goals
    unfold genCleanEmit
    dsimp only
    repeat (first | rfl | constructor | split)

private theorem gen_clean_propagate_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    stepPair (genCleanPropagate hpsi l r) = stepPair (l, r) := by
  unfold stepPair stepView
  apply Prod.ext <;> rw [StepView.mk.injEq]
  all_goals
    unfold genCleanPropagate
    dsimp only
    repeat (first | rfl | constructor | split)

private theorem gen_wall_emit_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    stepPair (genSigSaturatedEmit hpsi l r) = stepPair (l, r) := by
  unfold stepPair stepView
  apply Prod.ext <;> rw [StepView.mk.injEq]
  all_goals
    unfold genSigSaturatedEmit
    dsimp only
    repeat (first | rfl | constructor | split)

private theorem gen_wall_propagate_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    stepPair (genSigSaturatedPropagate hpsi l r) = stepPair (l, r) := by
  unfold stepPair stepView
  apply Prod.ext <;> rw [StepView.mk.injEq]
  all_goals
    unfold genSigSaturatedPropagate
    dsimp only
    repeat (first | rfl | constructor | split)

private theorem gen_finish_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    stepPair (genSigSaturatedFinish hpsi l r) = stepPair (l, r) := by
  unfold stepPair stepView
  apply Prod.ext <;> rw [StepView.mk.injEq]
  all_goals
    unfold genSigSaturatedFinish
    dsimp only
    repeat (first | rfl | constructor | split)

private theorem b1_gen_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    stepPair (genCleanAfterWait hpsi l r) = stepPair (l, r) := by
  let q0 := genSigSaturatedStart hpsi l r
  let q1 := genCleanEmit hpsi q0.1 q0.2
  let q2 := genCleanPropagate hpsi q1.1 q1.2
  change stepPair (genSigSaturatedFinish hpsi q2.1 q2.2) = stepPair (l, r)
  exact (gen_finish_frame hpsi q2.1 q2.2).trans
    ((gen_clean_propagate_frame hpsi q1.1 q1.2).trans
      ((gen_clean_emit_frame hpsi q0.1 q0.2).trans
        (gen_start_frame hpsi l r)))

private theorem wall_gen_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    stepPair (genSigSaturatedAfterWait hpsi l r) = stepPair (l, r) := by
  let q0 := genSigSaturatedStart hpsi l r
  let q1 := genSigSaturatedEmit hpsi q0.1 q0.2
  let q2 := genSigSaturatedPropagate hpsi q1.1 q1.2
  change stepPair (genSigSaturatedFinish hpsi q2.1 q2.2) = stepPair (l, r)
  exact (gen_finish_frame hpsi q2.1 q2.2).trans
    ((gen_wall_propagate_frame hpsi q1.1 q1.2).trans
      ((gen_wall_emit_frame hpsi q0.1 q0.2).trans
        (gen_start_frame hpsi l r)))

/-- The shortened GEN and wall GEN stages have the same observed fields. -/
theorem gen_stage (hpsi : 0 < psi) (l r : AgentState psi) :
    stepPair (genCleanAfterWait hpsi l r) =
      stepPair (genSigSaturatedAfterWait hpsi l r) := by
  have h : stepPair (genCleanAfterWait hpsi l r) =
      stepPair (genSigSaturatedAfterWait hpsi l r) :=
    (b1_gen_frame hpsi l r).trans (wall_gen_frame hpsi l r).symm
  have hl :
      (genCleanAfterWait hpsi l r).1.leader =
        (genSigSaturatedAfterWait hpsi l r).1.leader ∧
      (genCleanAfterWait hpsi l r).2.leader =
        (genSigSaturatedAfterWait hpsi l r).2.leader := by
    exact ⟨congrArg (fun q => q.1.leader) h,
      congrArg (fun q => q.2.leader) h⟩
  have hz :
      (genCleanAfterWait hpsi l r).1.reset_cmd =
        (genSigSaturatedAfterWait hpsi l r).1.reset_cmd ∧
      (genCleanAfterWait hpsi l r).2.reset_cmd =
        (genSigSaturatedAfterWait hpsi l r).2.reset_cmd := by
    exact ⟨congrArg (fun q => q.1.reset) h,
      congrArg (fun q => q.2.reset) h⟩
  have he :
      (genCleanAfterWait hpsi l r).1.echo =
        (genSigSaturatedAfterWait hpsi l r).1.echo ∧
      (genCleanAfterWait hpsi l r).2.echo =
        (genSigSaturatedAfterWait hpsi l r).2.echo := by
    exact ⟨congrArg (fun q => q.1.echo) h,
      congrArg (fun q => q.2.echo) h⟩
  unfold stepPair stepView
  apply Prod.ext
  · rw [StepView.mk.injEq]
    exact ⟨hl.1, hz.1, he.1⟩
  · rw [StepView.mk.injEq]
    exact ⟨hl.2, hz.2, he.2⟩

end BirthB1ResetStepAgreementStages

#print axioms BirthB1ResetStepAgreementStages.gen_stage
