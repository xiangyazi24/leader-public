import Leader.Wu.Elimination.SinkBoundedKernel
import Leader.Wu.Elimination.SinkTwoGapDeletionWired

/-!
# Exact elimination cost and probability on the finite carrier

The actual local row is `LDSinkBoundedKernel.boundedKernel`.  Here its bounded
configuration process stops precisely when the same tagged leader deletion
occurs as in `physicalBlockStep`.  The audit's `APhase` is an observer only:
the finite process stores no such per-agent field, and erasure relates it to
every audit phase with the same configuration.

Exact success, failure, active-leaf and active-interaction numerators agree
at every horizon.  Consequently every established audit bound transfers to
this finite elimination process without changing its scheduler or clock.
Other dispatcher families and their interference still require their own
physical row proofs.
-/

namespace LDSinkBoundedStopping

open LDSinkBoundedKernel LDSinkGapCleanup LDTwoGapFrame
open LDSinkTwoGapNoResetKernel LDSinkTwoGapDeletionWired
open FiniteUniformStoppingTree

set_option autoImplicit false

noncomputable section

/-- Only the bounded physical cells occur in this process state. -/
abbrev BConfig (n ψ κ : Nat) := Fin n → BoundedAgentState ψ κ

/-- Execute one finite K2 interaction and stop exactly on `NoResetSuccess`.
Reabsorptions are ordinary active continuations, not successful leaves. -/
def boundedBlockStep {n ψ κ : Nat} (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : BConfig n ψ κ) (e : Fin n) : StopNode (BConfig n ψ κ) := by
  classical
  exact
    let C' := boundedStep hψ F.attack C e
    if NoResetSuccess F (eraseConfig C') then .success else .active C'

/-- Same terminal outcome, or exactly the same configuration after erasure.
There is no constraint on the audit phase because the physical row does not
read it. -/
def Related {n ψ κ : Nat} :
    StopNode (BConfig n ψ κ) → StopNode (AState n ψ) → Prop
  | .active C, .active a => a.conf = eraseConfig C
  | .success, .success => True
  | .failure, .failure => True
  | _, _ => False

/-- Relation preservation follows from the concrete finite-row erasure and
the existing physical normal form; it is not a carried simulation premise. -/
theorem related_step {n ψ κ : Nat} (hψ : 0 < ψ) (F : TwoGapFrame n)
    (u : StopNode (BConfig n ψ κ)) (v : StopNode (AState n ψ))
    (h : Related u v) (e : Fin n) :
    Related (stepNode (boundedBlockStep hψ F) u e)
      (stepNode (physicalBlockStep hψ F) v e) := by
  classical
  cases u with
  | success => cases v <;> simp_all [Related, stepNode]
  | failure => cases v <;> simp_all [Related, stepNode]
  | active C =>
    cases v with
    | success => exact h.elim
    | failure => exact h.elim
    | active a =>
      change a.conf = eraseConfig C at h
      have hp : attemptStepConf hψ F a e =
          eraseConfig (boundedStep hψ F.attack C e) := by
        rw [attemptStepConf_eq_sinkStepC, h, erase_boundedStep]
      simp only [stepNode, boundedBlockStep, physicalBlockStep_normal_form, hp]
      split
      · trivial
      · change (postState hψ F a e).conf =
          eraseConfig (boundedStep hψ F.attack C e)
        exact hp

private theorem related_treeWeight {n ψ κ : Nat}
    (hψ : 0 < ψ) (F : TwoGapFrame n)
    (wb : StopNode (BConfig n ψ κ) → Nat) (wa : StopNode (AState n ψ) → Nat)
    (hw : ∀ u v, Related u v → wb u = wa v)
    (u : StopNode (BConfig n ψ κ)) (v : StopNode (AState n ψ))
    (h : Related u v) (T : Nat) :
    treeWeight (boundedBlockStep hψ F) wb u T =
      treeWeight (physicalBlockStep hψ F) wa v T := by
  induction T generalizing u v with
  | zero => exact hw u v h
  | succ T ih =>
    simp only [treeWeight]
    exact ofFn_sum_eq _ _ (fun e => ih _ _ (related_step hψ F u v h e))

/-- Exactly the same successful scheduler words are counted on both carriers. -/
theorem successCount_eq {n ψ κ : Nat} (hψ : 0 < ψ) (F : TwoGapFrame n)
    (u : StopNode (BConfig n ψ κ)) (v : StopNode (AState n ψ))
    (h : Related u v) (T : Nat) :
    successCount (boundedBlockStep hψ F) u T =
      successCount (physicalBlockStep hψ F) v T := by
  apply related_treeWeight hψ F successWeight successWeight ?_ u v h T
  intro x y hxy
  cases x <;> cases y <;> simp_all [Related, successWeight]

/-- Terminal failure counts agree as well; absorption is reactivated in both
processes and cannot be mistaken for leader-election success. -/
theorem failureCount_eq {n ψ κ : Nat} (hψ : 0 < ψ) (F : TwoGapFrame n)
    (u : StopNode (BConfig n ψ κ)) (v : StopNode (AState n ψ))
    (h : Related u v) (T : Nat) :
    failureCount (boundedBlockStep hψ F) u T =
      failureCount (physicalBlockStep hψ F) v T := by
  apply related_treeWeight hψ F failureWeight failureWeight ?_ u v h T
  intro x y hxy
  cases x <;> cases y <;> simp_all [Related, failureWeight]

/-- The finite and audit processes have the same unfinished-word numerator. -/
theorem activeCount_eq {n ψ κ : Nat} (hψ : 0 < ψ) (F : TwoGapFrame n)
    (u : StopNode (BConfig n ψ κ)) (v : StopNode (AState n ψ))
    (h : Related u v) (T : Nat) :
    activeCount (boundedBlockStep hψ F) u T =
      activeCount (physicalBlockStep hψ F) v T := by
  apply related_treeWeight hψ F activeWeight activeWeight ?_ u v h T
  intro x y hxy
  cases x <;> cases y <;> simp_all [Related, activeWeight]

/-- Every active physical interaction is charged exactly once on both sides.
This equality is stronger than a transfer of an upper bound. -/
theorem activeCost_eq {n ψ κ : Nat} (hψ : 0 < ψ) (F : TwoGapFrame n)
    (u : StopNode (BConfig n ψ κ)) (v : StopNode (AState n ψ))
    (h : Related u v) (T : Nat) :
    truncatedActiveCostNumerator (boundedBlockStep hψ F) u T =
      truncatedActiveCostNumerator (physicalBlockStep hψ F) v T := by
  induction T generalizing u v with
  | zero => rfl
  | succ T ih =>
    cases u with
    | success => cases v <;> simp_all [Related, truncatedActiveCostNumerator]
    | failure => cases v <;> simp_all [Related, truncatedActiveCostNumerator]
    | active C =>
      cases v with
      | success => exact h.elim
      | failure => exact h.elim
      | active a =>
        simp only [truncatedActiveCostNumerator]
        apply congrArg (n ^ (T + 1) + ·)
        apply ofFn_sum_eq
        intro e
        exact ih _ _ (related_step hψ F (.active C) (.active a) h e)

/-- Exact same-carrier runtime and probability transfer for arbitrary finite
inputs and arbitrary audit phase.  The two numeric premises are the actual
audit bounds being transferred, not further implementation obligations. -/
theorem transfer_cost_and_success {n ψ κ : Nat}
    (hψ : 0 < ψ) (F : TwoGapFrame n) (C : BConfig n ψ κ) (phase : APhase)
    (T budget denominator : Nat)
    (hc : truncatedActiveCostNumerator (physicalBlockStep hψ F)
      (.active ⟨eraseConfig C, phase⟩) T ≤ n ^ T * budget)
    (hs : n ^ T ≤ denominator * successCount (physicalBlockStep hψ F)
      (.active ⟨eraseConfig C, phase⟩) T) :
    truncatedActiveCostNumerator (boundedBlockStep hψ F) (.active C) T ≤
      n ^ T * budget ∧
    n ^ T ≤ denominator * successCount (boundedBlockStep hψ F) (.active C) T := by
  have hr : Related (.active C) (.active (⟨eraseConfig C, phase⟩ : AState n ψ)) := rfl
  rw [activeCost_eq hψ F _ _ hr, successCount_eq hψ F _ _ hr]
  exact ⟨hc, hs⟩

end
end LDSinkBoundedStopping

#print axioms LDSinkBoundedStopping.related_step
#print axioms LDSinkBoundedStopping.successCount_eq
#print axioms LDSinkBoundedStopping.activeCost_eq
#print axioms LDSinkBoundedStopping.transfer_cost_and_success
