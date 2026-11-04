import Leader.Wu.Splice.BusyFrontTable

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceV9StrictRank

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9

variable {n psi width kappa tau : Nat}

/-! Local decidability for the closed safety check. -/
private instance instDecidableHostFenceShapeRank
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (HostFenceShapeV7 u) := by
  unfold HostFenceShapeV7
  infer_instance

private instance instDecidableTicketShapeRank
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (TicketShapeV7 u) := by
  unfold TicketShapeV7 HostFenceShapeV7 ReservedFrontHoldGuard
  infer_instance

private instance instDecidablePreparedDangerRank
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring (projectV6 C) e) := by
  unfold PreparedDangerAt PreparedBarrierAt projectV6
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidableProtectedSpliceEdgeRank
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (ProtectedSpliceEdgeV7 ring C e) := by
  unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3
    HostFenceShapeV7 ReservedFrontHoldGuard projectV6
  dsimp only
  infer_instance

private instance instDecidableProvenanceSafeRank
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) :
    Decidable (ProvenanceSafeV7 ring C) := by
  unfold ProvenanceSafeV7
  infer_instance

private instance instDecidableSpliceSafeRank
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) :
    Decidable (SpliceSafeV7 hpsi ring C) := by
  unfold SpliceSafeV7
  infer_instance

private theorem hOne : 0 < 1 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hOneThree : 1 <= 3 := by decide

private def ring1 : DirectedRing 1 := ⟨hOne⟩
private def ring2 : DirectedRing 2 := ⟨hTwo⟩

/-- Reuse the public two-site psi=3 physical fixture, but erase its old
controller and install exactly one host-fence ticket at site zero.
The physical labels are 0 at site zero and 2 at site one. -/
def advanceFlatStart : R1ConfigV6 2 3 0 0 := fun i =>
  if i = (0 : Fin 2) then
    setTicketV6
      (clearControlV6
        (B9SpliceControllerR1TableV6.moveAcquireAbortStart2V6 i)) true
  else
    clearControlV6
      (B9SpliceControllerR1TableV6.moveAcquireAbortStart2V6 i)

/-- The offending non-stuttering V9 service. -/
def advanceFlatAfter : R1ConfigV6 2 3 0 0 :=
  stepV9 hThree hOne hOneThree ring2 advanceFlatStart (0 : Fin 2)

/-- Literal input geometry and controller state. -/
theorem advanceFlat_literal_shape :
    (advanceFlatStart (0 : Fin 2)).carrier.splice.base.core.core.leader = false ∧
    (advanceFlatStart (1 : Fin 2)).carrier.splice.base.core.core.leader = false ∧
    (advanceFlatStart (0 : Fin 2)).carrier.splice.base.core.core.label =
      (0 : Fin 3) ∧
    (advanceFlatStart (1 : Fin 2)).carrier.splice.base.core.core.label =
      (2 : Fin 3) ∧
    role (advanceFlatStart (0 : Fin 2)).carrier = .none ∧
    (advanceFlatStart (0 : Fin 2)).carrier.repairPending = false ∧
    (advanceFlatStart (0 : Fin 2)).acquireTicket = true ∧
    role (advanceFlatStart (1 : Fin 2)).carrier = .none ∧
    (advanceFlatStart (1 : Fin 2)).carrier.repairPending = false ∧
    (advanceFlatStart (1 : Fin 2)).acquireTicket = false := by
  decide

/-- The counterexample starts inside the required V7 safety invariant. -/
theorem advanceFlat_safe :
    SpliceSafeV7 hThree ring2 advanceFlatStart := by
  decide

/-- V9 really selects the inherited HOST-FENCE-LEFT / ADVANCE row. -/
theorem advanceFlat_selects_fenceAdvance :
    rowV9 hThree hOne hOneThree
        (advanceFlatStart (0 : Fin 2))
        (advanceFlatStart (1 : Fin 2)) =
      hostFenceLeftAdvanceWriteV7 hThree
        (advanceFlatStart (0 : Fin 2))
        (advanceFlatStart (1 : Fin 2)) := by
  decide

/-- The selected row is not a stutter. -/
theorem advanceFlat_changes :
    ∃ i : Fin 2, advanceFlatAfter i != advanceFlatStart i := by
  refine ⟨(0 : Fin 2), ?_⟩
  decide

/-- Both rank components, hence the composite rank, are exactly flat. -/
theorem advanceFlat_rank_values :
    controllerPotentialV6 advanceFlatStart = 1 ∧
    controllerPotentialV6 advanceFlatAfter = 1 ∧
    fencePotentialV9 hThree ring2 advanceFlatStart = 2 ∧
    fencePotentialV9 hThree ring2 advanceFlatAfter = 2 ∧
    compositeRankV9 hThree ring2 advanceFlatStart = 7 ∧
    compositeRankV9 hThree ring2 advanceFlatAfter = 7 := by
  decide

theorem advanceFlat_rank_equal :
    compositeRankV9 hThree ring2 advanceFlatAfter =
      compositeRankV9 hThree ring2 advanceFlatStart := by
  decide

/-- A one-site ring cannot furnish a smaller non-stuttering counterexample. -/
theorem singleton_stepV9_stutters
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (C : R1ConfigV6 1 psi kappa tau) (e : Fin 1) :
    stepV9 hpsi hwidth hle ring1 C e = C := by
  have hself : ring1.rightNeighbor e = e := Subsingleton.elim _ _
  simp [stepV9, hself]

/-- Therefore the requested global strict-rank proposition is false. -/
theorem not_V9StrictRank :
    ¬ V9StrictRank (kappa := 0) (tau := 0)
      hThree hOne hOneThree ring2 := by
  intro h
  unfold V9StrictRank at h
  have hchange :
      ∃ i : Fin 2,
        stepV9 hThree hOne hOneThree ring2 advanceFlatStart
            (0 : Fin 2) i != advanceFlatStart i := by
    simpa only [advanceFlatAfter] using advanceFlat_changes
  have hdrop :=
    h advanceFlatStart advanceFlat_safe (0 : Fin 2) hchange
  change compositeRankV9 hThree ring2 advanceFlatAfter <
    compositeRankV9 hThree ring2 advanceFlatStart at hdrop
  rw [advanceFlat_rank_equal] at hdrop
  exact (Nat.lt_irrefl _ hdrop)

end B9SpliceV9StrictRank

#print axioms B9SpliceV9StrictRank.advanceFlat_literal_shape
#print axioms B9SpliceV9StrictRank.advanceFlat_safe
#print axioms B9SpliceV9StrictRank.advanceFlat_selects_fenceAdvance
#print axioms B9SpliceV9StrictRank.advanceFlat_rank_values
#print axioms B9SpliceV9StrictRank.singleton_stepV9_stutters
#print axioms B9SpliceV9StrictRank.not_V9StrictRank
