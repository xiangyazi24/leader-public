import Leader.Wu.Splice.OrphanScrubPotential
import Leader.Wu.Splice.HostFenceTable


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9SpliceScrubSafetyV6


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7
open B9SpliceOrphanScrubV6


variable {n psi kappa tau : Nat}


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


private instance instDecidableOrphan
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (OrphanReservedFrontGuardV3 l.carrier r.carrier) := by
  unfold OrphanReservedFrontGuardV3 ReservedFrontHoldGuard
  infer_instance


private theorem hTwo : 0 < (2 : Nat) := by decide
private theorem hThree : 0 < (3 : Nat) := by decide


private def ring2 : DirectedRing 2 := ⟨hTwo⟩
private def e0 : Fin 2 := 0
private def e1 : Fin 2 := 1


private def C : R1ConfigV6 2 3 0 0 :=
  orphanReservedFrontStart2V6


private def D : R1ConfigV6 2 3 0 0 :=
  orphanReservedFrontScrubAtV6 ring2 C e0


/-- The existing orphan fixture is V7-safe and the served edge is exactly the
orphan-reservation edge `0 -> 1`. -/
theorem orphan_scrub_fixture_pre :
    ring2.rightNeighbor e0 = e1 /\
    SpliceSafeV7 hThree ring2 C /\
    OrphanReservedFrontGuardV3
      (C e0).carrier (C (ring2.rightNeighbor e0)).carrier := by
  decide


/-- The scrubbed site is the left endpoint of the opposite edge `1 -> 0`.
That edge is dangerous before and after the scrub; the reservation is its old
certificate and clearing it destroys `ProtectedSpliceEdgeV7`. -/
theorem orphan_scrub_fixture_outgoing_certificate_lost :
    ring2.rightNeighbor e1 = e0 /\
    PreparedDangerAt hThree ring2 (projectV6 C) e1 /\
    ProtectedSpliceEdgeV7 ring2 C e1 /\
    PreparedDangerAt hThree ring2 (projectV6 D) e1 /\
    ¬ ProtectedSpliceEdgeV7 ring2 D e1 := by
  decide


/-- Hence the proposed productive scrub is not safety-preserving. -/
theorem orphan_scrub_fixture_not_spliceSafeV7 :
    ¬ SpliceSafeV7 hThree ring2 D := by
  intro hs
  exact orphan_scrub_fixture_outgoing_certificate_lost.2.2.2.2
    (hs.1 e1 orphan_scrub_fixture_outgoing_certificate_lost.2.2.2.1)


/-- Direct refutation of the unconditional preservation statement requested
for the scrub branch. -/
theorem orphanReservedFrontScrub_preserves_spliceSafeV7_false :
    ¬ (forall (n psi kappa tau : Nat) (hpsi : 0 < psi)
        (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n),
      SpliceSafeV7 hpsi ring C ->
      OrphanReservedFrontGuardV3
        (C e).carrier (C (ring.rightNeighbor e)).carrier ->
      SpliceSafeV7 hpsi ring
        (orphanReservedFrontScrubAtV6 ring C e)) := by
  intro h
  have hout := h 2 3 0 0 hThree ring2 C e0
    orphan_scrub_fixture_pre.2.1
    orphan_scrub_fixture_pre.2.2
  exact orphan_scrub_fixture_not_spliceSafeV7 hout


end B9SpliceScrubSafetyV6


#print axioms B9SpliceScrubSafetyV6.orphan_scrub_fixture_pre
#print axioms B9SpliceScrubSafetyV6.orphan_scrub_fixture_outgoing_certificate_lost
#print axioms B9SpliceScrubSafetyV6.orphan_scrub_fixture_not_spliceSafeV7
#print axioms B9SpliceScrubSafetyV6.orphanReservedFrontScrub_preserves_spliceSafeV7_false
