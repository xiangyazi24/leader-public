import Leader.Wu.Coherence.ReachableSeekRootCases
import Leader.Wu.Coherence.ReachableCoverForeignPrefix
import Leader.Wu.Coherence.OpenRCoherence
import Leader.Wu.Coherence.ReachableSoundFreshInstances
import Leader.Wu.Coherence.ReachableSweepOwnerFootprint


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31FreshResidualLedger


open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableAdjacentRoot
open R2CoherenceV31ReachableFreshBranches1
open R2CoherenceV31ReachableFreshBranches2
open R2CoherenceV31ReachableFreshBranches3
open R2CoherenceV31ReachableSoundFreshInstances
open R2CoherenceV31ReachableSweepFresh
open R2CoherenceV31ReachableSweepFresh2
open R2CoherenceV31FreshnessClear
open R2CoherenceV31OpenNoHazardClose
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31ReachableSoundFresh


variable {n ψ κ τ : Nat}


theorem openRR1Fresh_of_installed
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (r : DirectedRing n) :
    OpenRR1FreshPreservationV31P E hψ h2 r := by
  intro C e _ _ hF hb
  exact R2CoherenceV31ReachableOpenRTail.openRForwardFreshnessClear_openR_step
      hψ h2 r C e hF.2.2.2.2.2.1 hb


theorem openRR2Fresh_of_installed
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (r : DirectedRing n) :
    OpenRStrongR2FreshPreservationV31P E hψ h2 r := by
  intro C e _ _ hF hb
  have hOld : R2CoherenceV31StrongR2Route.SweepPendingOpenRFootprintOwnedV31F r C := by
    simpa [R2CoherenceV31StrongR2Route.SweepPendingOpenRFootprintOwnedV31F,
      R2CoherenceV31FreshnessClear.SweepPendingOpenRFootprintOwnedV31F]
      using hF.2.2.2.2.2.2
  have hNew := R2CoherenceV31StrongR2Route.sweepPendingOpenRFootprintOwnedV31F_openR_step
      hψ h2 r C e hOld hb
  simpa [R2CoherenceV31StrongR2Route.SweepPendingOpenRFootprintOwnedV31F,
    R2CoherenceV31FreshnessClear.SweepPendingOpenRFootprintOwnedV31F]
    using hNew


def freshResidualLedgerOpenCount : Nat := 22


theorem reachableSoundFresh_of_ledger
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (hCover : PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 r)
    (hCurrent : ReachableCurrentOpenRSweepFootprintFreshV31
      (κ := κ) (τ := τ) hψ h2 r)
    (seekS : SeekSFreshPreservationV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (seekR2 : SeekStrongR2FreshPreservationV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (seekReplay : SeekFreshPrivateReplayV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (rel7 : ReleaseP7FreshV31 (κ := κ) (τ := τ) hψ h2 r)
    (rel8 : ReleaseP8FreshV31 (κ := κ) (τ := τ) hψ h2 r)
    (rel9 : ReleaseP9FreshV31 (κ := κ) (τ := τ) hψ h2 r)
    (relS : ReleaseSFreshV31 (κ := κ) (τ := τ) hψ h2 r)
    (relR2 : ReleaseR2FreshV31 (κ := κ) (τ := τ) hψ h2 r)
    (scr8 : ScrubLP8FreshPreservationV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (scr9 : ScrubLP9FreshPreservationV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (scrS : ScrubLSFreshPreservationV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (scrR2 : ScrubLStrongR2FreshPreservationV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (scrReplay : ScrubLFreshPrivateReplayV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (orS : OpenRSFreshSourceV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (orReplay : OpenRFreshPrivateReplayV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (haz : OpenHazardFreshSeekPrepaidFreshV31
      (κ := κ) (τ := τ) hψ h2 r)
    (onh : SanitizedR2NewEqualFreshChainOriginNoMainMutation
      (κ := κ) (τ := τ) hψ (by decide : 0 < 2) h2)
    (mixS : MixedSFreshV31 (κ := κ) (τ := τ) hψ h2 r)
    (mixR1 : MixedR1FreshV31 (κ := κ) (τ := τ) hψ h2 r)
    (mixR2 : MixedR2FreshV31 (κ := κ) (τ := τ) hψ h2 r) :
    ∀ C : FC n ψ κ τ, ReachableFromQuarantineV31 hψ h2 r C →
      ReachablePhaseFactsFreshV31 r C := by
  have swSafe := sweepCurrentOpenRServedSafeFresh_of_footprintFresh
    hψ h2 r
    (sweepCurrentOpenRServedFootprintFresh_of_reachableInvariant
      hψ h2 r hCurrent)
  have swTail := sweepStrongTailPreservationFresh_of_cover
    hψ h2 r hCover
  have orR1 := openRR1Fresh_of_installed
    (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r
  have orR2 := openRR2Fresh_of_installed
    (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r
  exact R2CoherenceV31ReachableSoundFreshInstances.reachableSoundFresh_of_installed
      hψ h2 r seekS seekR2 seekReplay swSafe swTail
      rel7 rel8 rel9 relS relR2 scr8 scr9 scrS scrR2 scrReplay
      orS orR1 orR2 orReplay haz onh mixS mixR1 mixR2


end R2CoherenceV31FreshResidualLedger
