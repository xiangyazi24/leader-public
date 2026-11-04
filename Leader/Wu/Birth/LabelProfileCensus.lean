import Leader.Wu.Coherence.CarrierSimulationComponents
import Leader.Wu.Coherence.ReachableAdjacentRootEndpoint
import Leader.Wu.Entrance.AdmissionCollarClear

set_option autoImplicit false
set_option Elab.async false

namespace BirthLabelProfileCensus

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open B6LocalReverseFill B6EntranceV2 B6EntranceAdmissionR1
open R2CoherenceV31 R2CoherenceV31BirthQuarantine
open R2CoherenceV31ReachableRootSpacing2
open R2CoherenceV31ReachableAdjacentRoot
open R2CoherenceV31ReachableAdjacentRoot2 R2CoherenceV31ReachableReleaseOwner2

variable {n psi kappa tau : Nat}

/-- Internal B6/R1 words literally preserve labels outside the selected core. -/
theorem r1_core_internal_outside_label
    {ring : DirectedRing n}
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (X : Workspace ring psi)
    (C : PConfig n (Phys psi psi (16 * psi)))
    (w : List (Fin n))
    (hCore : InternalWord X.core.J w)
    (i : Fin n) (hi : support X.core.J i = false) :
    (B6Sanitation.rawCell
      ((runHost
        (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
        ring w C) i)).label =
      (B6Sanitation.rawCell (C i)).label := by
  rw [r1_core_internal_collar_site_unchanged
    hpsi h2 X C w hCore i hi]

/-- Label-only way to make the ψ=2 adjacent-root physical obligation vacuous. -/
def NoAdjacentRootsPsi2V31
    (ring : DirectedRing n) (C : FC n 2 kappa tau) : Prop :=
  ∀ p : Fin n,
    atRootB (C p) = true →
      atRootB (C (ring.rightNeighbor p)) = false

/-- No adjacent roots is sufficient for the current adjacent-root consumer. -/
theorem adjacentRootMainClear_of_noAdjacentRoots
    (ring : DirectedRing n) (C : FC n 2 kappa tau)
    (hNo : NoAdjacentRootsPsi2V31 ring C) :
    AdjacentRootPredecessorMainClearPsi2V31 ring C := by
  intro p hp hq
  have hf := hNo p hp
  rw [hq] at hf
  cases hf

/-- Exact optional producer theorem if one wants a label-only ψ=2 discharge. -/
def BirthNoAdjacentRootsPsi2V31
    (ring : DirectedRing n) : Prop :=
  ∀ Q : FC n 2 kappa tau,
    BirthEntranceV1 (by decide : 0 < 2) (by decide : 2 ≤ 2) ring Q →
      NoAdjacentRootsPsi2V31 ring Q

/-- Reduction from the optional label theorem to the installed producer leaf. -/
theorem birthAdjacentRoot_of_noAdjacentRoots
    (ring : DirectedRing n)
    (hNo : BirthNoAdjacentRootsPsi2V31
      (kappa := kappa) (tau := tau) ring) :
    BirthAdjacentRootMainClearProducerLeafPsi2V31
      (kappa := kappa) (tau := tau) ring := by
  unfold BirthAdjacentRootMainClearProducerLeafPsi2V31
    BirthAdjacentRootPredecessorMainClearPsi2V31
  intro Q hBirth
  exact adjacentRootMainClear_of_noAdjacentRoots ring Q (hNo Q hBirth)


namespace BirthLabelProfileCensus

open R2CoherenceV31FinalSimulation5
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C

variable {n psi kappa tau : Nat}

/-- This is the actual general-ψ admitted label contract: edge geometry only. -/
abbrev AdmittedWeakLabelProfileV31
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  C1FinalV31AdmittedElectionGeometryResidual
    (kappa := kappa) (tau := tau) hpsi h2 ring

/-- Full whole-ring linearity is strictly stronger and should remain separate. -/
abbrev AdmittedWholeRingLinearityV31
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  C1FinalV31AdmittedLabelProfileResidual
    (kappa := kappa) (tau := tau) hpsi h2 ring

/-- Fresh-seek birth needs no whole-ring label profile after RootSpacing2. -/
theorem freshSeek_birth_anchoring_free
    (ring : DirectedRing n) (C : FC n psi kappa tau) :
    R2CoherenceV31ReachableRootSpacing.PendingOwnerWindowAnchoredV31
      ring (quarantineInitV31 C) := by
  exact pendingOwnerWindowAnchored_quarantineInit ring C

end BirthLabelProfileCensus
