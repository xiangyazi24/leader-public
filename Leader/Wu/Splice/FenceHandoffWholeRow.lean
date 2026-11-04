import Leader.Wu.Splice.FenceHandoffTable
import Leader.Wu.Splice.OrdinaryHostBirthSafe
import Leader.Wu.Splice.OrdinaryHostDeletionSafe

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceV10bWholeRow

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair BirthShortDoneTerminalBirthSources
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table
open B9SpliceControllerR1TableV2
open B9SpliceControllerR1TableV3
open B9SpliceControllerV3Safety
open B9SpliceControllerR1TableV4
open B9SpliceControllerV4Safety
open B9SpliceControllerR1TableV6
open B9SpliceControllerR1TableV7
open B9SpliceControllerR1TableV8
open B9SpliceControllerR1TableV9
open B9SpliceControllerR1TableV10b
open B9SpliceV8OrdinaryHost

variable {n psi width kappa tau : Nat}

/-- The requested target, with exactly the birth-case `hleft` hypothesis. -/
def StepV10bWholeRowStatement
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (hleft : forall (l r : R1AgentStateV6 psi kappa tau),
      OrdinaryNeutralPairV8 l r ->
      rowV8 hpsi hwidth hle l r =
        ordinaryHostWriteV7 hpsi hwidth hle l r ->
      (BirthShortDoneTerminalHost.row hpsi hwidth hle
        l.carrier.splice.base r.carrier.splice.base).1.core.core.leader = false ->
      (BirthShortDoneTerminalHost.row hpsi hwidth hle
        l.carrier.splice.base r.carrier.splice.base).1.core.core.label =
        l.carrier.splice.base.core.core.label) : Prop :=
  forall (C : R1ConfigV6 n psi kappa tau) (e : Fin n),
    SpliceSafeV7 (kappa := kappa) (tau := tau) hpsi ring C ->
    SpliceSafeV7 (kappa := kappa) (tau := tau) hpsi ring
      (stepV10b (kappa := kappa) (tau := tau)
        hpsi hwidth hle ring C e)

/-- Exact first inherited controller branch not covered by the theorem list. -/
def MoveAcquireFrontSelectedV10b
    (hpsi : 0 < psi)
    (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  ¬ HostFenceAdvanceGuardV10b (kappa := kappa) (tau := tau) hpsi l r /\
  ¬ HostFenceBusyFrontGuardV9 (kappa := kappa) (tau := tau) hpsi l r /\
  ¬ RightStalePredecessorHoldGuardV8 (kappa := kappa) (tau := tau) l r /\
  ¬ HostFenceShapeV7 (kappa := kappa) (tau := tau) l /\
  ¬ HostFenceShapeV7 (kappa := kappa) (tau := tau) r /\
  MoveAcquireFrontGuardV6 (kappa := kappa) (tau := tau) hpsi l r

/-- This is the missing full-safety theorem needed before whole-row assembly can
pass the first inherited V6 controller row. -/
def MoveAcquireFrontBranchStatementV10b
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) : Prop :=
  forall (C : R1ConfigV6 n psi kappa tau) (e : Fin n),
    SpliceSafeV7 (kappa := kappa) (tau := tau) hpsi ring C ->
    MoveAcquireFrontSelectedV10b (kappa := kappa) (tau := tau) hpsi
      (C e) (C (ring.rightNeighbor e)) ->
    SpliceSafeV7 (kappa := kappa) (tau := tau) hpsi ring
      (stepV10b (kappa := kappa) (tau := tau)
        hpsi hwidth hle ring C e)

/-! Closed decidability for the literal two-site witness. -/

private instance instDecidableHostFenceShape
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (HostFenceShapeV7 u) := by
  unfold HostFenceShapeV7
  infer_instance

private instance instDecidableTicketShape
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (TicketShapeV7 u) := by
  unfold TicketShapeV7 HostFenceShapeV7 ReservedFrontHoldGuard
  infer_instance

private instance instDecidablePreparedDanger
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring (projectV6 C) e) := by
  unfold PreparedDangerAt PreparedBarrierAt projectV6
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidableProtected
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (ProtectedSpliceEdgeV7 ring C e) := by
  unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3
    HostFenceShapeV7 ReservedFrontHoldGuard projectV6
  dsimp only
  infer_instance

private instance instDecidableProvenance
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) :
    Decidable (ProvenanceSafeV7 ring C) := by
  unfold ProvenanceSafeV7
  infer_instance

private instance instDecidableSpliceSafe
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) :
    Decidable (SpliceSafeV7 hpsi ring C) := by
  unfold SpliceSafeV7
  infer_instance

private instance instDecidableLocalBarrier
    (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (LocalPreparedBarrier hpsi l.carrier r.carrier) := by
  unfold LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidableAdvance
    (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (HostFenceAdvanceGuardV10b hpsi l r) := by
  unfold HostFenceAdvanceGuardV10b HostFenceTargetClearV7
  infer_instance

private instance instDecidableBusy
    (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (HostFenceBusyFrontGuardV9 hpsi l r) := by
  unfold HostFenceBusyFrontGuardV9 ReservedFrontHoldGuard
  infer_instance

private instance instDecidableStale
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (RightStalePredecessorHoldGuardV8 l r) := by
  unfold RightStalePredecessorHoldGuardV8
  infer_instance

private instance instDecidableAcquire
    (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (MoveAcquireFrontGuardV6 hpsi l r) := by
  unfold MoveAcquireFrontGuardV6 ReservedFrontHoldGuard
  infer_instance

private instance instDecidableSelected
    (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (MoveAcquireFrontSelectedV10b hpsi l r) := by
  unfold MoveAcquireFrontSelectedV10b
  infer_instance

private theorem hOne : 0 < 1 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hOneTwo : 1 <= 2 := by decide
private def ring2 : DirectedRing 2 := ⟨hTwo⟩

/-- Smallest possible non-self-loop fixture: two aligned follower fronts, with
site 0 carrying the authenticated acquisition ticket. -/
def moveAcquireFrontStart2V10b : R1ConfigV6 2 2 0 0 := fun i =>
  if i = (0 : Fin 2) then
    setTicketV6
      (liftAgentV6
        (B9SpliceR2AttackRerun.xcell false 0 false .front true)) true
  else
    liftAgentV6
      (B9SpliceR2AttackRerun.xcell false 1 false .front true)

/-- The missing branch is genuinely live under `SpliceSafeV7`.  The final
conjunct also records that this literal witness is not itself a counterexample. -/
theorem moveAcquireFront_uncovered_fixture_v10b :
    SpliceSafeV7 (kappa := 0) (tau := 0)
      hTwo ring2 moveAcquireFrontStart2V10b /\
    MoveAcquireFrontSelectedV10b (kappa := 0) (tau := 0) hTwo
      (moveAcquireFrontStart2V10b (0 : Fin 2))
      (moveAcquireFrontStart2V10b (1 : Fin 2)) /\
    rowV10b (kappa := 0) (tau := 0) hTwo hOne hOneTwo
      (moveAcquireFrontStart2V10b (0 : Fin 2))
      (moveAcquireFrontStart2V10b (1 : Fin 2)) =
        moveAcquireFrontWriteV6
          (moveAcquireFrontStart2V10b (0 : Fin 2))
          (moveAcquireFrontStart2V10b (1 : Fin 2)) /\
    SpliceSafeV7 (kappa := 0) (tau := 0) hTwo ring2
      (stepV10b (kappa := 0) (tau := 0) hTwo hOne hOneTwo
        ring2 moveAcquireFrontStart2V10b (0 : Fin 2)) := by
  decide

end B9SpliceV10bWholeRow

#print axioms B9SpliceV10bWholeRow.moveAcquireFront_uncovered_fixture_v10b
