import Leader.Wu.Splice.ProvenanceTicketTable
import Leader.Wu.Birth.PPrimeRearmThenBirthRingSix


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9SpliceControllerV6Safety


open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table
open B9SpliceControllerR1TableV2
open B9SpliceControllerR1TableV3
open B9SpliceControllerV3Safety
open B9SpliceControllerR1TableV4
open B9SpliceControllerV4Safety
open B9SpliceControllerR1TableV6


variable {n psi width kappa tau : Nat}


/-! ## Closed decidability for the counterexample -/


private instance q11703DecidablePreparedDanger
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring C e) := by
  unfold PreparedDangerAt PreparedBarrierAt
  dsimp only
  unfold isBarrier
  infer_instance


private instance q11703DecidableProtected
    (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) (e : Fin n) :
    Decidable (R1ProtectedSpliceEdgeV3 ring C e) := by
  unfold R1ProtectedSpliceEdgeV3 ReservedFrontHoldGuard
  dsimp only
  infer_instance


private instance q11703DecidableSpliceSafeBase
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) :
    Decidable (SpliceSafeR1V3 hpsi ring C) := by
  unfold SpliceSafeR1V3
  infer_instance


private instance q11703DecidableTicketShape
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (TicketShapeV6 u) := by
  unfold TicketShapeV6 ReservedFrontHoldGuard
  infer_instance


private instance q11703DecidableProvenanceSafe
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) :
    Decidable (ProvenanceSafeV6 ring C) := by
  unfold ProvenanceSafeV6
  infer_instance


private instance q11703DecidableSpliceSafeV6
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) :
    Decidable (SpliceSafeR1V6 hpsi ring C) := by
  unfold SpliceSafeR1V6
  infer_instance


/-! ## The inherited three-site physical collision, lifted to v6 -/


private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hTwoLe : 2 <= 2 := by decide


private def ring3 : DirectedRing 3 := ⟨hThree⟩
private def e0 : Fin 3 := 0
private def e1 : Fin 3 := 1


private def neutralCarrierV6
    (b : ExpiringAgentState 2 1 1) : R1AgentStateV4 2 1 1 :=
  { splice := { base := b, spliceRole := .none }
    repairPending := false }


private def neutralV6
    (b : ExpiringAgentState 2 1 1) : R1AgentStateV6 2 1 1 :=
  liftAgentV6 (neutralCarrierV6 b)


/-- Controller-neutral lift of the already-certified physical start:
site 0 is the surviving leader, site 1 is the echo-bearing follower, and
site 2 is the aligned label-1 follower. -/
def ordinaryHostStartV6 : R1ConfigV6 3 2 1 1 :=
  fun i => neutralV6 (Q11541PPrimeReachability.strongStart i)


def ordinaryHostAfterV6 : R1ConfigV6 3 2 1 1 :=
  stepV6 hTwo hTwo hTwoLe ring3 ordinaryHostStartV6 e0


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- Smallest inherited literal failure: the pre-state satisfies the complete
v6 safety predicate; the served row is exactly the ordinary-host branch; after
that row edge 1 is a prepared danger with no V3 ownership certificate, hence
the complete v6 safety predicate is false. -/
theorem ordinaryHost_counterexample_v6 :
    SpliceSafeR1V6 hTwo ring3 ordinaryHostStartV6 /\
    rowV6 hTwo hTwo hTwoLe
        (ordinaryHostStartV6 e0)
        (ordinaryHostStartV6 (ring3.rightNeighbor e0)) =
      ordinaryHostWriteV6 hTwo hTwo hTwoLe
        (ordinaryHostStartV6 e0)
        (ordinaryHostStartV6 (ring3.rightNeighbor e0)) /\
    PreparedDangerAt hTwo ring3
      (projectV6 ordinaryHostAfterV6) e1 /\
    ¬ R1ProtectedSpliceEdgeV3 ring3
      (projectV6 ordinaryHostAfterV6) e1 /\
    ¬ SpliceSafeR1V6 hTwo ring3 ordinaryHostAfterV6 := by
  decide


/-! ## Named obligations: both are false -/


/-- The branch-local statement that would be needed to close the inherited
ordinary-host row.  It is intentionally a named Prop rather than a status. -/
def OrdinaryHostPreservesSpliceSafeR1V6 : Prop :=
  forall (n psi width kappa tau : Nat)
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n),
    rowV6 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
        ordinaryHostWriteV6 hpsi hwidth hle
          (C e) (C (ring.rightNeighbor e)) ->
    SpliceSafeR1V6 hpsi ring C ->
    SpliceSafeR1V6 hpsi ring
      (stepV6 hpsi hwidth hle ring C e)


theorem ordinaryHostPreservesSpliceSafeR1V6_false :
    ¬ OrdinaryHostPreservesSpliceSafeR1V6 := by
  intro h
  have hout := h 3 2 2 1 1 hTwo hTwo hTwoLe
    ring3 ordinaryHostStartV6 e0
    ordinaryHost_counterexample_v6.2.1
    ordinaryHost_counterexample_v6.1
  exact ordinaryHost_counterexample_v6.2.2.2.2 hout


/-- The requested whole-step B9 safety gate, left as a named Prop because the
executable v6 table does not satisfy it. -/
def StepV6PreservesSpliceSafeR1V6 : Prop :=
  forall (n psi width kappa tau : Nat)
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n),
    SpliceSafeR1V6 hpsi ring C ->
    SpliceSafeR1V6 hpsi ring
      (stepV6 hpsi hwidth hle ring C e)


theorem stepV6PreservesSpliceSafeR1V6_false :
    ¬ StepV6PreservesSpliceSafeR1V6 := by
  intro h
  have hout := h 3 2 2 1 1 hTwo hTwo hTwoLe
    ring3 ordinaryHostStartV6 e0
    ordinaryHost_counterexample_v6.1
  exact ordinaryHost_counterexample_v6.2.2.2.2 hout


end B9SpliceControllerV6Safety


#print axioms B9SpliceControllerV6Safety.ordinaryHost_counterexample_v6
#print axioms B9SpliceControllerV6Safety.ordinaryHostPreservesSpliceSafeR1V6_false
#print axioms B9SpliceControllerV6Safety.stepV6PreservesSpliceSafeR1V6_false
