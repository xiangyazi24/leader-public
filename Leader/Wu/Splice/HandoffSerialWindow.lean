import Leader.Wu.Splice.ZeroRefreshBlockMass
import Leader.Wu.Splice.ProvenanceTicketTable
import Leader.Wu.Splice.OneServiceBridge

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceBranchWindowMerge

open FiniteUniformStoppingTree
open BirthB1DrainCoupling
open B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV10b
open B9SpliceV10cLiveness
open B9SpliceBlockDrainMass B9SpliceOneServiceBridge

variable {n psi width kappa tau : Nat}

/-- The handoff branch alone: one V10c handoff followed by the certified V6
service drop, together with the unchanged 1/16 serial scheduler mass on the
physical window W = 4*n. -/
theorem handoff_serial_window
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (hn : 3 <= n) :
    let W := 4 * n
    let c : Nat := 16
    forall
      (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
      (p : ThreePortSerialCount.Ports n) (ha : p.a = e)
      (hne : ring.rightNeighbor e ≠ e)
      (hg : HostFenceAdvanceGuardV10b
        hpsi (C e) (C (ring.rightNeighbor e))),
      p.a = e /\
      (let H := stepV10c hpsi hwidth hle ring C e
       controllerPotentialV6 (stepV6 hpsi hwidth hle ring H e) <
         controllerPotentialV6 H) /\
      n ^ W <= c *
        successCount (samePortSerialStep p) (.active false) W := by
  dsimp only
  intro C e p ha hne hg
  exact handoff_serial_branch
    hpsi hwidth hle ring C e p hn ha hne hg

#print axioms handoff_serial_window


end B9SpliceBranchWindowMerge
