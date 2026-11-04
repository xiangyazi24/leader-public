import Leader.Wu.Coherence.ReachableSoundFresh
import Leader.Wu.Coherence.ReachableSoundParametric
import Leader.Wu.Coherence.ReachableSeekRootCases
import Leader.Wu.Coherence.ReachableScrubLNewPending
import Leader.Wu.Coherence.ReachableOpenRIncomingSeek

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableFreshBranches3

open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard3
open R2CoherenceV31MainClearTruth
open R2CoherenceV31MainClearTruth.WeakFreshnessLayer
open R2CoherenceV31FreshnessClear
open R2CoherenceV31ReachableSoundFresh
open R2CoherenceV31ReachableSoundParametric

variable {n ψ κ τ : Nat}

/-! Parts 1 and 2 (commit/sealed/sweep and release/openHazard/mixed) are still
quarantine-shaped on their other tabs.  They will be re-stated with the same
`ReachableFromV31 E` interface before the Fresh induction is assembled. -/

def StepPreservesBranchFreshV31P
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (b : BranchV3) : Prop :=
  ∀ C e, ElectionGeometryV31 ring C →
    ReachableFromV31 E hψ h2 ring C →
    ReachablePhaseFactsFreshV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = b →
      ReachablePhaseFactsFreshV31 ring (stepV3 hψ h2 ring C e)

abbrev StepPreservesV31_seek_freshP (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchFreshV31P E hψ h2 ring .seek
abbrev StepPreservesV31_scrubL_freshP (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchFreshV31P E hψ h2 ring .scrubL
abbrev StepPreservesV31_openR_freshP (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchFreshV31P E hψ h2 ring .openR

theorem electionGeometry_of_freshParametricTrace
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (hBase : EntranceGeometryV31Parametric E ring)
    (C : FC n ψ κ τ) (hReach : ReachableFromV31 E hψ h2 ring C) :
    ElectionGeometryV31 ring C := by
  exact electionGeometry_of_reachableFromV31 E hψ h2 ring hBase
    (R2CoherenceV31Closure2.electionGeometryStepV31
      (κ := κ) (τ := τ) hψ h2 ring) C hReach

theorem freshComponent_false_of_freshnessClear_branch3
    (u : Cell ψ κ τ) (k : Nat) (hc : FreshnessClearV31 u)
    (hf : R2Coherence.freshComponent (eraseCellV3 u) k) : False := by
  exact freshComponent_false_of_freshnessClear u k hc hf

/-- Fresh analogue of the old Plus3 prefix, only for sequencing SCRUBL tails. -/
def ReachablePhaseFactsFreshP3V31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ReachablePhaseFactsV31 ring C ∧
  ScrubLIncomingOpenRFreshV31 ring C ∧
  SweepOpenROverlapFreshV31 ring C ∧
  SweepOpenROverlapFreshWideV31 ring C

def SeekSFreshPreservationV31P
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ C e, ElectionGeometryV31 ring C →
    ReachableFromV31 E hψ h2 ring C →
    ReachablePhaseFactsFreshV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek →
      SeekIncomingSweepOpenROverlapFreshWideV31 ring
        (stepV3 hψ h2 ring C e)

def SeekStrongR2FreshPreservationV31P
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ C e, ElectionGeometryV31 ring C →
    ReachableFromV31 E hψ h2 ring C →
    ReachablePhaseFactsFreshV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek →
      R2CoherenceV31FreshnessClear.SweepPendingOpenRFootprintOwnedV31F ring
        (stepV3 hψ h2 ring C e)

def ScrubLP8FreshPreservationV31P
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ C e, ElectionGeometryV31 ring C → ReachableFromV31 E hψ h2 ring C →
    ReachablePhaseFactsFreshV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL →
    ScrubLIncomingOpenRFreshV31 ring (stepV3 hψ h2 ring C e) →
      SweepOpenROverlapFreshV31 ring (stepV3 hψ h2 ring C e)

def ScrubLP9FreshPreservationV31P
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ C e, ElectionGeometryV31 ring C → ReachableFromV31 E hψ h2 ring C →
    ReachablePhaseFactsFreshV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL →
    ScrubLIncomingOpenRFreshV31 ring (stepV3 hψ h2 ring C e) →
    SweepOpenROverlapFreshV31 ring (stepV3 hψ h2 ring C e) →
      SweepOpenROverlapFreshWideV31 ring (stepV3 hψ h2 ring C e)

def ScrubLSFreshPreservationV31P
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ C e, ElectionGeometryV31 ring C → ReachableFromV31 E hψ h2 ring C →
    ReachablePhaseFactsFreshV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL →
    ReachablePhaseFactsFreshP3V31 ring (stepV3 hψ h2 ring C e) →
      SeekIncomingSweepOpenROverlapFreshWideV31 ring
        (stepV3 hψ h2 ring C e)

def ScrubLStrongR2FreshPreservationV31P
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ C e, ElectionGeometryV31 ring C → ReachableFromV31 E hψ h2 ring C →
    ReachablePhaseFactsFreshV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL →
    ReachablePhaseFactsFreshP3V31 ring (stepV3 hψ h2 ring C e) →
    SeekIncomingSweepOpenROverlapFreshWideV31 ring
      (stepV3 hψ h2 ring C e) →
      R2CoherenceV31FreshnessClear.SweepPendingOpenRFootprintOwnedV31F ring
        (stepV3 hψ h2 ring C e)

/-- Fresh S-source corresponding to OpenR4's bad-new-seek predecessor-root seam. -/
def OpenRSFreshSourceV31P
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ C e pred owner, ElectionGeometryV31 ring C →
    ReachableFromV31 E hψ h2 ring C → ReachablePhaseFactsFreshV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR →
    successorB (C e) (C (ring.rightNeighbor e)) = false →
    ring.rightNeighbor pred = e →
    let D := stepV3 hψ h2 ring C e
    PendingOpenROwnerV31 ring D owner → atRootB (D e) = false →
    atRootB (D pred) = true →
      SweepOpenRSafeFreshV31 ring D owner e ∧
      ∀ d : Fin (ψ - (raw (D pred)).label.val),
        SweepOpenRSafeFreshV31 ring D owner (R2Coherence.fwd ring pred d.val)

def OpenRR1FreshPreservationV31P
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ C e, ElectionGeometryV31 ring C → ReachableFromV31 E hψ h2 ring C →
    ReachablePhaseFactsFreshV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR →
      OpenRForwardFreshnessClearV31 ring (stepV3 hψ h2 ring C e)

def OpenRStrongR2FreshPreservationV31P
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ C e, ElectionGeometryV31 ring C → ReachableFromV31 E hψ h2 ring C →
    ReachablePhaseFactsFreshV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR →
      R2CoherenceV31FreshnessClear.SweepPendingOpenRFootprintOwnedV31F ring (stepV3 hψ h2 ring C e)

/-- Import-bound replay residuals.  These are proof-interface seams, not new
protocol invariants.  If the old private frame helpers are moved into this file,
their `freshFalse*` uses are replaced by
`freshComponent_false_of_freshnessClear_branch3`. -/
def SeekFreshPrivateReplayV31P
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  SeekSFreshPreservationV31P E hψ h2 ring →
  SeekStrongR2FreshPreservationV31P E hψ h2 ring →
    StepPreservesV31_seek_freshP E hψ h2 ring

def ScrubLFreshPrivateReplayV31P
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ScrubLP8FreshPreservationV31P E hψ h2 ring →
  ScrubLP9FreshPreservationV31P E hψ h2 ring →
  ScrubLSFreshPreservationV31P E hψ h2 ring →
  ScrubLStrongR2FreshPreservationV31P E hψ h2 ring →
    StepPreservesV31_scrubL_freshP E hψ h2 ring

def OpenRFreshPrivateReplayV31P
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  OpenRSFreshSourceV31P E hψ h2 ring →
  OpenRR1FreshPreservationV31P E hψ h2 ring →
  OpenRStrongR2FreshPreservationV31P E hψ h2 ring →
    StepPreservesV31_openR_freshP E hψ h2 ring

theorem seekStep_reachable_fresh_of_residuals
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (hS : SeekSFreshPreservationV31P E hψ h2 ring)
    (hR2 : SeekStrongR2FreshPreservationV31P E hψ h2 ring)
    (hReplay : SeekFreshPrivateReplayV31P E hψ h2 ring) :
    StepPreservesV31_seek_freshP E hψ h2 ring := hReplay hS hR2

theorem scrubLStep_reachable_fresh_of_residuals
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (hP8 : ScrubLP8FreshPreservationV31P E hψ h2 ring)
    (hP9 : ScrubLP9FreshPreservationV31P E hψ h2 ring)
    (hS : ScrubLSFreshPreservationV31P E hψ h2 ring)
    (hR2 : ScrubLStrongR2FreshPreservationV31P E hψ h2 ring)
    (hReplay : ScrubLFreshPrivateReplayV31P E hψ h2 ring) :
    StepPreservesV31_scrubL_freshP E hψ h2 ring :=
  hReplay hP8 hP9 hS hR2

theorem openRStep_reachable_fresh_of_residuals
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (hS : OpenRSFreshSourceV31P E hψ h2 ring)
    (hR1 : OpenRR1FreshPreservationV31P E hψ h2 ring)
    (hR2 : OpenRStrongR2FreshPreservationV31P E hψ h2 ring)
    (hReplay : OpenRFreshPrivateReplayV31P E hψ h2 ring) :
    StepPreservesV31_openR_freshP E hψ h2 ring := hReplay hS hR1 hR2

end R2CoherenceV31ReachableFreshBranches3
