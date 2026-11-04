import Leader.Wu.Splice.ZeroRefreshTable
import Leader.Wu.Birth.DrainCoupling


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9SpliceBlockDrainMass


open FiniteUniformStoppingTree FixedSpanRenewalPayload
open B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
open B9SpliceControllerR1TableV10b B9SpliceV10cLiveness
open BirthB1ResetDrainParallel BirthB1DrainCoupling


variable {n psi width kappa tau : Nat}


def runV10c
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (u : List (Fin n)) : R1ConfigV6 n psi kappa tau :=
  u.foldl (stepV10c hpsi hwidth hle ring) C


def LiveNonClearV10c
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) : Prop :=
  SpliceSafeV7 hpsi ring C /\ ¬ RolesClearV7 C


def ControllerProductiveServiceV10c
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n) : Prop :=
  controllerPotentialV6 (stepV10c hpsi hwidth hle ring C e) <
      controllerPotentialV6 C \/
    RolesClearV7 (stepV10c hpsi hwidth hle ring C e)


def blockNextV10c
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (i : Fin (n ^ (2 * n))) : R1ConfigV6 n psi kappa tau :=
  runV10c hpsi hwidth hle ring C (rawWord n (2 * n) i)


def BlockProductiveV10c
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (i : Fin (n ^ (2 * n))) : Prop :=
  controllerPotentialV6 (blockNextV10c hpsi hwidth hle ring C i) <
      controllerPotentialV6 C \/
    RolesClearV7 (blockNextV10c hpsi hwidth hle ring C i)


theorem controller_potential_budget (C : R1ConfigV6 n psi kappa tau) :
    controllerPotentialV6 C <= 8 * n :=
  controllerPotentialV6_le_eight_mul C


/-- Existing main theorem showing why the handoff family is not yet a
one-service certificate: the proved strict drop is on the following V6 service. -/
theorem handoff_second_service_drop
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hg : HostFenceAdvanceGuardV10b hpsi (C e) (C (ring.rightNeighbor e))) :
    let H := stepV10b hpsi hwidth hle ring C e
    controllerPotentialV6 (stepV6 hpsi hwidth hle ring H e) <
      controllerPotentialV6 H := by
  exact handoff_next_v6_service_drops hpsi hwidth hle ring C e hne hg


#print axioms controller_potential_budget
#print axioms handoff_second_service_drop


end B9SpliceBlockDrainMass
