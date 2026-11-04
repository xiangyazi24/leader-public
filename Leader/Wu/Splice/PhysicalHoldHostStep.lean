import Leader.Wu.Splice.PhysicalHoldTransparency
import Leader.Wu.Birth.CountStepReduction

set_option autoImplicit false

/-! # A physical V10e service is one step of the physical host protocol

The physical projection of a configuration is the family of bases.  When a V10e service is
physical at `e` and leaves every other base unchanged, the projection after the service is
exactly the physical host step (the B7 protocol step) at `e` of the projection before. -/

namespace B9SpliceV10ePhysicalIsB7Step

open PPLL PPLLDomain PPLLResearchFormulation PPLLExpiringComparisonRepair
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6
  B9SpliceTableV10e B9SpliceV10eTransparency

variable {n psi width kappa tau : Nat}

def physicalProj (C : R1ConfigV6 n psi kappa tau) : Fin n → ExpiringAgentState psi kappa tau :=
  fun i => (C i).carrier.splice.base

theorem physicalService_is_hostStep
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C D : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hphys : PhysicalServiceAt hpsi hwidth hle ring C D e)
    (hother : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e →
      (D i).carrier.splice.base = (C i).carrier.splice.base) :
    physicalProj D = BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring (physicalProj C) e := by
  funext k
  unfold BirthShortDoneTerminalConsumer.step
  have h := BirthB1CountStepReduction.step_apply
    (BirthShortDoneTerminalConsumer.protocol hpsi hwidth hle kappa tau) ring
    (physicalProj C : (BirthShortDoneTerminalConsumer.protocol hpsi hwidth hle kappa tau).Configuration n) e k
  rw [h]
  unfold PhysicalServiceAt at hphys
  dsimp only at hphys
  by_cases hk : k = e
  · subst hk
    simp only [eq_self_iff_true, if_true]
    exact hphys.1
  · simp only [hk, if_false]
    by_cases hj : k = ring.rightNeighbor e
    · subst hj
      simp only [eq_self_iff_true, if_true]
      exact hphys.2
    · simp only [hj, if_false]
      exact hother k hk hj

/-- The physical hold leaves every other base unchanged. -/
theorem physicalHoldAt_other_base (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    (physicalHoldAt hpsi hwidth hle ring C e i).carrier.splice.base = (C i).carrier.splice.base := by
  simp [physicalHoldAt, hi, hj]

theorem physicalFenceAt_other_base (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    (physicalFenceAt hpsi hwidth hle ring C e i).carrier.splice.base = (C i).carrier.splice.base := by
  simp [physicalFenceAt, hi, hj]

/-- The physical hold at `e` projects to the host step at `e`. -/
theorem physicalHold_projects_to_hostStep
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    physicalProj (physicalHoldAt hpsi hwidth hle ring C e) =
      BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring (physicalProj C) e :=
  physicalService_is_hostStep hpsi hwidth hle ring C _ e
    (physicalHold_is_physical hpsi hwidth hle ring C e hne)
    (fun i hi hj => physicalHoldAt_other_base hpsi hwidth hle ring C e i hi hj)

theorem physicalFence_projects_to_hostStep
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    physicalProj (physicalFenceAt hpsi hwidth hle ring C e) =
      BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring (physicalProj C) e :=
  physicalService_is_hostStep hpsi hwidth hle ring C _ e
    (physicalFence_is_physical hpsi hwidth hle ring C e hne)
    (fun i hi hj => physicalFenceAt_other_base hpsi hwidth hle ring C e i hi hj)

end B9SpliceV10ePhysicalIsB7Step
