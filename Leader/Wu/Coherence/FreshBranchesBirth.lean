import Leader.Wu.Coherence.ReachableFreshCommitSealedSweep
import Leader.Wu.Coherence.ReachableFreshReleaseMixedHazard
import Leader.Wu.Coherence.ReachableFreshSeekScrubLOpenR
import Leader.Wu.Coherence.ReachableSoundFresh

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

/-!
Entrance-parametric branch wrappers, specialised to the birth entrance.

The seven branch preservation theorems are stated against
the quarantine trace, and no bridge exists from `ReachableFromV31 E` to
`ReachableFromQuarantineV31` for an arbitrary entrance `E`.  That is true, but
the campaign only ever instantiates the parametric interface at the birth
entrance, where `reachableFromV31_birth_iff` IS exactly that bridge.  This file
tests whether the seven wrappers are therefore immediate at `BirthEntranceV1`,
with no refactor of the accepted branch modules.
-/

namespace R2CoherenceV31FreshBranchesBirth

open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts
open R2CoherenceV31ReachableSoundParametric
open R2CoherenceV31ReachableFreshBranches1
open R2CoherenceV31ReachableFreshBranches2
open R2CoherenceV31ReachableFreshBranches3
open R2CoherenceV31FreshnessClear
open R2CoherenceV31ReachableSoundFresh

variable {n ψ κ τ : Nat}

private theorem birthTrace
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : ReachableFromV31 (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 ring)
      hψ h2 ring C) : ReachableFromQuarantineV31 hψ h2 ring C :=
  (reachableFromV31_birth_iff hψ h2 ring C).1 h

theorem commitStep_birthFresh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    StepPreservesBranchFreshV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 ring) hψ h2 ring .commit := by
  intro C e hg ht hf hb
  exact R2CoherenceV31ReachableFreshBranches1.commitStep_reachable_fresh
    hψ h2 ring C e hg (birthTrace hψ h2 ring C ht) hf hb

theorem sealedStep_birthFresh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    StepPreservesBranchFreshV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 ring) hψ h2 ring .sealed := by
  intro C e hg ht hf hb
  exact R2CoherenceV31ReachableFreshBranches1.sealedStep_reachable_fresh
    hψ h2 ring C e hg (birthTrace hψ h2 ring C ht) hf hb

theorem sweepStep_birthFresh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hSafe : SweepCurrentOpenRServedSafeFreshV31 (κ:=κ) (τ:=τ) hψ h2 ring)
    (hTail : SweepStrongTailPreservationFreshV31 (κ:=κ) (τ:=τ) hψ h2 ring) :
    StepPreservesBranchFreshV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 ring) hψ h2 ring .sweep := by
  intro C e hg ht hf hb
  exact R2CoherenceV31ReachableFreshBranches1.sweepStep_reachable_fresh_of_residuals
    hψ h2 ring hSafe hTail C e hg (birthTrace hψ h2 ring C ht) hf hb

theorem releaseStep_birthFresh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (p7 : ReleaseP7FreshV31 (κ:=κ) (τ:=τ) hψ h2 ring)
    (p8 : ReleaseP8FreshV31 (κ:=κ) (τ:=τ) hψ h2 ring)
    (p9 : ReleaseP9FreshV31 (κ:=κ) (τ:=τ) hψ h2 ring)
    (s : ReleaseSFreshV31 (κ:=κ) (τ:=τ) hψ h2 ring)
    (r2 : ReleaseR2FreshV31 (κ:=κ) (τ:=τ) hψ h2 ring) :
    StepPreservesBranchFreshV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 ring) hψ h2 ring .release := by
  intro C e hg ht hf hb
  exact R2CoherenceV31ReachableFreshBranches2.releaseStep_reachable_fresh_of_residuals
    hψ h2 ring p7 p8 p9 s r2 C e hg (birthTrace hψ h2 ring C ht) hf hb

theorem mixedStep_birthFresh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (s : MixedSFreshV31 (κ:=κ) (τ:=τ) hψ h2 ring)
    (r1 : MixedR1FreshV31 (κ:=κ) (τ:=τ) hψ h2 ring)
    (r2 : MixedR2FreshV31 (κ:=κ) (τ:=τ) hψ h2 ring) :
    StepPreservesBranchFreshV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 ring) hψ h2 ring .mixed := by
  intro C e hg ht hf hb
  exact R2CoherenceV31ReachableFreshBranches2.mixedStep_reachable_fresh_of_residuals
    hψ h2 ring s r1 r2 C e hg (birthTrace hψ h2 ring C ht) hf hb

theorem openHazardStep_birthFresh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hn : OpenHazardFreshSeekPrepaidFreshV31 (κ:=κ) (τ:=τ) hψ h2 ring) :
    StepPreservesBranchFreshV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 ring) hψ h2 ring .openHazard := by
  intro C e hg ht hf hb
  exact R2CoherenceV31ReachableFreshBranches2.openHazardStep_reachable_fresh_of_residuals
    hψ h2 ring hn C e hg (birthTrace hψ h2 ring C ht) hf hb

theorem openNoHazardStep_birthFresh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hChain : R2CoherenceV31OpenNoHazardClose.SanitizedR2NewEqualFreshChainOriginNoMainMutation
      (κ := κ) (τ := τ) hψ (by decide : 0 < 2) h2) :
    StepPreservesBranchFreshV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 ring) hψ h2 ring .openNoHazard := by
  intro C e hg ht hf hb
  exact openNoHazardStep_reachable_fresh
    hψ h2 ring hChain C e hg (birthTrace hψ h2 ring C ht) hf hb

end R2CoherenceV31FreshBranchesBirth
