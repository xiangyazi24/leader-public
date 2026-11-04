import Leader.Wu.Splice.CheckXSupplier
import Leader.Wu.Splice.StaleHoldTable
import Leader.Wu.Splice.HostBarrierHole

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9CheckRouteGate

open PPLL PPLLRepair PPLLResearchFormulation
open BirthPhaseCohortDesign
open B9CheckStructuralCensus B9CheckGlobalWitnessCensus
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV3
open B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
open B9SpliceControllerR1TableV8 B9CheckXSupplierDesign
open B9HostBarrierHole B9SpliceControllerR1TableV2

variable {n psi kappa tau : Nat}

/-- The old acquisition ticket is the true ticket on a reserved front. -/
def AcquisitionTicketShapeV9
    (u : R1AgentStateV6 psi kappa tau) : Prop :=
  ReservedFrontHoldGuard u.carrier /\ u.acquireTicket = true

/-- `(none,true,false)` cannot be V7's `(none,false,true)` fence. -/
theorem route_gate_disjoint_host_fence
    (u : R1AgentStateV6 psi kappa tau)
    (hg : RouteWriterGateShape u) :
    ¬ HostFenceShapeV7 u := by
  intro hf
  have hbad : (true : Bool) = false :=
    hf.2.2.symm.trans hg.2.2
  cases hbad

/-- A route gate never carries the V6/V7 acquisition ticket. -/
theorem route_gate_disjoint_acquisition_ticket
    (u : R1AgentStateV6 psi kappa tau)
    (hg : RouteWriterGateShape u) :
    ¬ AcquisitionTicketShapeV9 u := by
  intro ha
  have hbad : (true : Bool) = false :=
    ha.2.symm.trans hg.2.2
  cases hbad

/-- Physical configuration actually controlled by an X-supplier state. -/
def xPhysical
    (S : XSupplierConfig n psi kappa tau) :
    BirthPhaseCohortDesign.FC n psi kappa tau :=
  fun i => (S i).splice.carrier.splice.base

/-- This is the type-correct preservation target for a future closed V9 step.
Unlike the current `CrossedIDRewriteX`, it mentions the gated controller. -/
def CrossedIDRewriteForXSupplierStep
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n)
    (step : XSupplierConfig n psi kappa tau -> Fin n ->
      XSupplierConfig n psi kappa tau) : Prop :=
  forall (S : XSupplierConfig n psi kappa tau) (e : Fin n),
    crossed_id_survival_bound hpsi h2 ring (xPhysical S) ->
    crossed_id_survival_bound hpsi h2 ring (xPhysical (step S e))

/-- The adopted design alias still points definitionally to the old target. -/
theorem mechanism_crossed_id_target_is_old_step
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) :
    MechanismSuppliesCrossedIDRewriteX
        (kappa := kappa) (tau := tau) hpsi h2 ring <->
      CrossedIDRewriteX
        (kappa := kappa) (tau := tau) hpsi h2 ring := by
  rfl

#print axioms B9CheckRouteGate.route_gate_disjoint_host_fence
#print axioms B9CheckRouteGate.route_gate_disjoint_acquisition_ticket
#print axioms B9CheckRouteGate.mechanism_crossed_id_target_is_old_step

end B9CheckRouteGate
