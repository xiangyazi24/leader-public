import Leader.Wu.Splice.FenceHandoffTable
import Leader.Wu.Splice.OrphanScrubPotential


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9SpliceControllerR1TableV11


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources Q11593SpliceControllerDesign
open B9SpliceControllerR1Table
open B9SpliceControllerR1TableV2
open B9SpliceControllerR1TableV3
open B9SpliceControllerR1TableV6
open B9SpliceControllerR1TableV7
open B9SpliceControllerR1TableV8
open B9SpliceControllerR1TableV9
open B9SpliceControllerR1TableV10b
open B9SpliceOrphanScrubV6


variable {n psi width kappa tau : Nat}


/-- V11 keeps the V10b row chain and replaces only the orphan reserved-front
branch by the proposed scrub writer. -/
def rowV11
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  if HostFenceAdvanceGuardV10b hpsi l r then
    hostFenceHandoffWriteV10b l r
  else rowV9 hpsi hwidth hle l r


/-- V11 step uses the same edge update shape as V10b. The changed orphan
semantics live in the inherited row branch replacement. -/
def stepV11
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n) : R1ConfigV6 n psi kappa tau :=
  let j := ring.rightNeighbor e
  if j = e then C
  else
    let q := rowV11 hpsi hwidth hle (C e) (C j)
    fun i => if i = e then q.1 else if i = j then q.2 else C i


/-- The V11 orphan scrub strictly decreases controller potential. -/
theorem stepV11_orphanReservedFront_controllerPotential_drop
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n)
    (h : OrphanReservedFrontGuardV3
      (C e).carrier (C (ring.rightNeighbor e)).carrier) :
    controllerPotentialV6
        (orphanReservedFrontScrubAtV6 ring C e) <
      controllerPotentialV6 C := by
  exact orphanReservedFront_scrub_controllerPotential_drop_v6 ring C e h


end B9SpliceControllerR1TableV11


#print axioms B9SpliceControllerR1TableV11.stepV11_orphanReservedFront_controllerPotential_drop
