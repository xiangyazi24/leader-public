import Leader.Wu.Splice.HoldRepairProjection
import Leader.Wu.Splice.PhysicalHoldHostStep

set_option autoImplicit false
set_option Elab.async false

/-! # V10j projected onto the host: host steps, stutters and K2-invisible relabels

For every configuration and every served edge, with or without leaders:
* a physical V10j service projects to one host step of `BirthShortDoneTerminalConsumer.step`
  (`project_physical`);
* a non-physical V10j service leaves the K2 observation (`ExpiringK2Projection.observe`: leader, shield, bullet
  and signal of every cell) unchanged (`observe_nonphysical`), because it either keeps both bases or is a
  MOVE-COMMIT relabel, which changes only label, probe and phase.
So the K2 elimination layer sees a composed V10j run exactly as the host run along its physical services. -/

namespace B9SpliceV10jK2Observation

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6
  B9SpliceTableV10j B9SpliceV10hControllerRowsSafe B9SpliceV10eTransparency B9SpliceV10ePhysicalIsB7Step
  B9SpliceV10jRowProgress B9SpliceV10jProjection

variable {n psi width kappa tau : Nat}

theorem stepV10j_other (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n)
    (h1 : i ≠ e) (h2 : i ≠ ring.rightNeighbor e) : stepV10j hpsi hwidth hle ring C e i = C i := by
  classical
  unfold stepV10j
  by_cases hself : ring.rightNeighbor e = e
  · rw [if_pos hself]
  · rw [if_neg hself]; exact writeAt_other ring C e _ i h1 h2

/-- A physical V10j service is one host step on the projection. -/
theorem project_physical (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hphys : PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e) :
    physicalProj (stepV10j hpsi hwidth hle ring C e) =
      BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring (physicalProj C) e :=
  physicalService_is_hostStep hpsi hwidth hle ring C _ e hphys
    (fun i h1 h2 => by rw [stepV10j_other hpsi hwidth hle ring C e i h1 h2])

/-- The K2 observation of a relabelled cell is unchanged. -/
theorem observeCell_relabel (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) :
    ExpiringK2Projection.observeCell (repairResponder hpsi l.carrier r.carrier).splice.base =
      ExpiringK2Projection.observeCell r.carrier.splice.base := rfl

/-- A non-physical V10j service leaves the K2 observation unchanged. -/
theorem observe_nonphysical (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hnp : ¬ PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e) :
    ExpiringK2Projection.observe (physicalProj (stepV10j hpsi hwidth hle ring C e)) =
      ExpiringK2Projection.observe (physicalProj C) := by
  classical
  funext i
  unfold ExpiringK2Projection.observe physicalProj
  by_cases hself : ring.rightNeighbor e = e
  · unfold stepV10j; rw [if_pos hself]
  have hstep : stepV10j hpsi hwidth hle ring C e =
      writeAt ring C e (rowV10j hpsi hwidth hle (C e) (C (ring.rightNeighbor e))) := by
    unfold stepV10j; rw [if_neg hself]
  have hrow : ¬ PhysRow hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
      (rowV10j hpsi hwidth hle (C e) (C (ring.rightNeighbor e))) := by
    intro hp
    apply hnp
    rw [hstep]
    have hw := B9SpliceV10jGlobalProgress.physical_of_row hpsi hwidth hle ring C e hself
      (C e, C (ring.rightNeighbor e)) (rowV10j hpsi hwidth hle (C e) (C (ring.rightNeighbor e))) hp
    rw [B9SpliceV10hWholeStepSafe.writeAt_self] at hw
    exact hw
  have key : ExpiringK2Projection.observeCell (rowV10j hpsi hwidth hle (C e) (C (ring.rightNeighbor e))).1.carrier.splice.base =
        ExpiringK2Projection.observeCell (C e).carrier.splice.base ∧
      ExpiringK2Projection.observeCell (rowV10j hpsi hwidth hle (C e) (C (ring.rightNeighbor e))).2.carrier.splice.base =
        ExpiringK2Projection.observeCell (C (ring.rightNeighbor e)).carrier.splice.base := by
    rcases rowV10j_trichotomy hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) with ⟨h1, h2⟩ | hp | ⟨h1, h2⟩
    · rw [h1, h2]; exact ⟨rfl, rfl⟩
    · exact absurd hp hrow
    · rw [h1, h2]; exact ⟨rfl, observeCell_relabel hpsi _ _⟩
  rw [hstep]
  by_cases hie : i = e
  · rw [hie, writeAt_e]; exact key.1
  · by_cases hij : i = ring.rightNeighbor e
    · rw [hij, writeAt_j ring C e _ hself]; exact key.2
    · rw [writeAt_other ring C e _ i hie hij]

end B9SpliceV10jK2Observation
