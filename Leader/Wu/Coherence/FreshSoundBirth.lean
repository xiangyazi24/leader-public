import Leader.Wu.Coherence.FreshBranchesBirth
import Leader.Wu.Coherence.FreshCoverSoundness
import Leader.Wu.Coherence.ReachableSoundFreshInstances

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31FreshBranchesBirthAssembly

open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableSoundParametric
open R2CoherenceV31ReachableFreshBranches1
open R2CoherenceV31ReachableFreshBranches2
open R2CoherenceV31ReachableFreshBranches3
open R2CoherenceV31FreshnessClear
open R2CoherenceV31ReachableSoundFresh

variable {n ψ κ τ : Nat}

theorem reachableSoundFresh_birthParametric_of_scrubL_gt_two
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (h3 : 2 < ψ) (r : DirectedRing n)
    (payload : R2CoherenceV31FootprintCover3.Cover3PayloadReachableV31
      (κ := κ) (τ := τ) hψ h2 r)
    (scrubForeign :
      R2CoherenceV31ReachableCover2.ScrubLContinuationForeignPrefixMainClearV31
        (κ := κ) (τ := τ) hψ h2 r)
    (current :
      R2CoherenceV31ReachableSweepFresh2.ReachableCurrentOpenRSweepFootprintFreshV31
        (κ := κ) (τ := τ) hψ h2 r)
    (onh :
      R2CoherenceV31OpenNoHazardClose.SanitizedR2NewEqualFreshChainOriginNoMainMutation
        (κ := κ) (τ := τ) hψ (by decide : 0 < 2) h2) :
    ∀ C : FC n ψ κ τ,
      ReachableFromV31
        (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r)
        hψ h2 r C →
      ReachablePhaseFactsFreshV31 r C := by
  let E : FC n ψ κ τ → Prop :=
    BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r

  have hc :=
    R2CoherenceV31FootprintCover4.pendingFootprintCoveredReachableFresh_of_scrubL_gt_two
      hψ h2 h3 r payload scrubForeign

  have scrReplay :=
    R2CoherenceV31ReplayProducers.scrubLFreshPrivateReplay_birthEntrance
      hψ h2 r payload scrubForeign
  have orReplay :=
    R2CoherenceV31ReplayProducers.openRFreshPrivateReplay_birthEntrance
      hψ h2 r payload hc

  have all :=
    R2CoherenceV31FootprintCover5.consumers_of_freshCover hψ h2 r hc
  rcases all with
    ⟨⟨seekS, seekR2, seekReplay, mixS, mixR2, haz⟩,
      ⟨scr8, scr9, scrS, scrR2, orS⟩⟩

  have swSafe :=
    R2CoherenceV31ReachableSweepFresh.sweepCurrentOpenRServedSafeFresh_of_footprintFresh
      hψ h2 r
      (R2CoherenceV31ReachableSweepFresh2.sweepCurrentOpenRServedFootprintFresh_of_reachableInvariant
        hψ h2 r current)
  have swTail :=
    R2CoherenceV31FootprintCover5.sweepStrongTailFresh_of_freshCover
      hψ h2 r hc

  have rel7 :=
    R2CoherenceV31FootprintCover5.releaseP7Fresh_of_freshCover_gt_two
      hψ h2 h3 r hc
  have rel8 :=
    R2CoherenceV31FootprintCover5.releaseP8Fresh_of_freshCover
      hψ h2 r hc
  have rel9 :=
    R2CoherenceV31FootprintCover5.releaseP9Fresh_of_freshCover
      hψ h2 r hc
  have relS :=
    R2CoherenceV31FootprintCover5.releaseSFresh_of_freshCover
      hψ h2 r hc
  have relR2 :=
    R2CoherenceV31FootprintCover5.releaseR2Fresh_of_freshCover
      hψ h2 r hc

  have mixR1 :=
    R2CoherenceV31ReachableSeekMixedFresh.mixedR1Fresh_frame
      (κ := κ) (τ := τ) hψ h2 r
  have orR1 :=
    R2CoherenceV31FreshResidualLedger.openRR1Fresh_of_installed
      E hψ h2 r
  have orR2 :=
    R2CoherenceV31FreshResidualLedger.openRR2Fresh_of_installed
      E hψ h2 r

  have hSeek :=
    R2CoherenceV31ReachableSoundFreshInstances.stepPreservesFresh_seek_of_residuals
      E hψ h2 r seekS seekR2 seekReplay
  have hSweep :=
    R2CoherenceV31FreshBranchesBirth.sweepStep_birthFresh
      hψ h2 r swSafe swTail
  have hCommit :=
    R2CoherenceV31FreshBranchesBirth.commitStep_birthFresh
      (κ := κ) (τ := τ) hψ h2 r
  have hRelease :=
    R2CoherenceV31FreshBranchesBirth.releaseStep_birthFresh
      hψ h2 r rel7 rel8 rel9 relS relR2
  have hScrubL :=
    R2CoherenceV31ReachableSoundFreshInstances.stepPreservesFresh_scrubL_of_residuals
      E hψ h2 r scr8 scr9 scrS scrR2 scrReplay
  have hOpenR :=
    R2CoherenceV31ReachableSoundFreshInstances.stepPreservesFresh_openR_of_residuals
      E hψ h2 r orS orR1 orR2 orReplay
  have hSealed :=
    R2CoherenceV31FreshBranchesBirth.sealedStep_birthFresh
      (κ := κ) (τ := τ) hψ h2 r
  have hOpenHazard :=
    R2CoherenceV31FreshBranchesBirth.openHazardStep_birthFresh
      hψ h2 r haz
  have hOpenNoHazard :=
    R2CoherenceV31FreshBranchesBirth.openNoHazardStep_birthFresh
      hψ h2 r onh
  have hMixed :=
    R2CoherenceV31FreshBranchesBirth.mixedStep_birthFresh
      hψ h2 r mixS mixR1 mixR2

  exact
    R2CoherenceV31ReachableSoundFreshInstances.reachableSoundFresh_of_branchSteps
      (κ := κ) (τ := τ) E hψ h2 r
      hSeek hSweep hCommit hRelease hScrubL hOpenR hSealed
      hOpenHazard hOpenNoHazard hMixed
      (R2CoherenceV31ReachableSoundFresh.birthEntrancePayloadFreshV31
        (κ := κ) (τ := τ) hψ h2 r)
      (fun _ hBirth => hBirth.2)

end R2CoherenceV31FreshBranchesBirthAssembly
