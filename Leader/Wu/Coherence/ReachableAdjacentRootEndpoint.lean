import Leader.Wu.Coherence.ReachableFootprintCovered

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableAdjacentRoot2

open PPLL PPLLResearchFormulation
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure2 R2CoherenceV31OpenNoHazard
open R2CoherenceV31ReachableAdjacentRoot
open R2CoherenceV31ReachableReleaseOwner2

variable {n kappa tau : Nat}

private theorem root_before_of_label_eq
    {C D : FC n 2 kappa tau} (p : Fin n)
    (hLab : (raw (D p)).label = (raw (C p)).label)
    (hRoot : atRootB (D p) = true) :
    atRootB (C p) = true := by
  have hv := congrArg Fin.val hLab
  unfold atRootB at hRoot ⊢
  simpa [hv] using hRoot

/-- Exact missing R2-row export after the source census.

The hypothesis `MainClearV3 (C p)` gives `state=.none`, `path=.bot` and all
auxiliary main carriers empty.  `openNoHazard` already exports preservation of
`path`; the underlying CHECK/compare rows cannot create a comparison result or
`path2` from `.bot`.  What is not currently exported is the complete bundled
`MainClearV3` conclusion for a serviced endpoint. -/
def OpenNoHazardAdjacentRootEndpointMainClearPsi2V31
    (ring : DirectedRing n) : Prop :=
  forall (C : FC n 2 kappa tau) (e p : Fin n),
    MainClearV3 (C p) ->
    atRootB (C p) = true ->
    atRootB (C (ring.rightNeighbor p)) = true ->
    branchAtV3 (by decide : 0 < 2) (by decide : 2 <= 2)
      (C e) (C (ring.rightNeighbor e)) = .openNoHazard ->
    (p = e ∨ p = ring.rightNeighbor e) ->
      MainClearV3
        (stepV3 (by decide : 0 < 2) (by decide : 2 <= 2) ring C e p)

/-- The exact adjacent-root preservation residual reduces to the endpoint
R2-row fact above.  Labels are globally framed; an adjacent-root predecessor
outside the serviced pair is literally unchanged. -/
theorem openNoHazardAdjacentRootMainClear_of_endpoint
    (ring : DirectedRing n)
    (hEndpoint : OpenNoHazardAdjacentRootEndpointMainClearPsi2V31
      (kappa := kappa) (tau := tau) ring) :
    OpenNoHazardAdjacentRootMainClearPreservationPsi2V31
      (kappa := kappa) (tau := tau) ring := by
  intro C e hAdj hb
  let D := stepV3 (by decide : 0 < 2) (by decide : 2 <= 2) ring C e
  have hLab : forall x : Fin n, (raw (D x)).label = (raw (C x)).label := by
    intro x
    simpa [D] using
      stepV3_labels_eq_or_held (by decide : 0 < 2) (by decide : 2 <= 2)
        ring C e x
  intro p hRootD hNextRootD
  have hRootC := root_before_of_label_eq p (hLab p) hRootD
  have hNextRootC := root_before_of_label_eq (ring.rightNeighbor p)
    (hLab (ring.rightNeighbor p)) hNextRootD
  have hClearC := hAdj p hRootC hNextRootC
  by_cases hpe : p = e
  · exact hEndpoint C e p hClearC hRootC hNextRootC hb (Or.inl hpe)
  · by_cases hpr : p = ring.rightNeighbor e
    · exact hEndpoint C e p hClearC hRootC hNextRootC hb (Or.inr hpr)
    · change MainClearV3 (D p)
      rw [show D p = C p by
        simp [D, stepV3, protocolV3, PopulationProtocol.step, hpe, hpr]]
      exact hClearC

/-- General entrance remains producer-side: quarantine only changes control.
The probe's `[0,1,0]` fixture satisfies this because its extra root is a
literal clean R2 cell, but `BirthEntranceV31` does not export that global fact. -/
def BirthAdjacentRootMainClearProducerLeafPsi2V31
    (ring : DirectedRing n) : Prop :=
  BirthAdjacentRootPredecessorMainClearPsi2V31
    (kappa := kappa) (tau := tau) ring

end R2CoherenceV31ReachableAdjacentRoot2
