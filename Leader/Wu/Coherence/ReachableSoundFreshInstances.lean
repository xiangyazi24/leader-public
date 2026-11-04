import Leader.Wu.Coherence.ReachableSoundFresh
import Leader.Wu.Coherence.ReachableFreshCommitSealedSweep
import Leader.Wu.Coherence.ReachableFreshReleaseMixedHazard
import Leader.Wu.Coherence.ReachableFreshSeekScrubLOpenR

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableSoundFreshInstances

open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus4
open R2CoherenceV31MainClearTruth R2CoherenceV31MainClearTruth.WeakFreshnessLayer
open R2CoherenceV31FreshnessClear
open R2CoherenceV31ReachableSoundFresh R2CoherenceV31ReachableSoundParametric
open R2CoherenceV31ReachableFreshBranches1
open R2CoherenceV31ReachableFreshBranches2
open R2CoherenceV31ReachableFreshBranches3
open R2CoherenceV31OpenNoHazardClose
open R2CoherenceV31FinalSimulation R2CoherenceV31FinalSimulation4
open R2CoherenceV31FinalSimulation5

variable {n ψ κ τ : Nat}

abbrev FreshStep (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) (b : BranchV3) : Prop :=
  StepPreservesBranchFreshV31P E hψ h2 r b
abbrev FreshSeekStep (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop := FreshStep E hψ h2 r .seek
abbrev FreshSweepStep (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop := FreshStep E hψ h2 r .sweep
abbrev FreshCommitStep (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop := FreshStep E hψ h2 r .commit
abbrev FreshReleaseStep (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop := FreshStep E hψ h2 r .release
abbrev FreshScrubLStep (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop := FreshStep E hψ h2 r .scrubL
abbrev FreshOpenRStep (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop := FreshStep E hψ h2 r .openR
abbrev FreshSealedStep (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop := FreshStep E hψ h2 r .sealed
abbrev FreshOpenHazardStep (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop := FreshStep E hψ h2 r .openHazard
abbrev FreshOpenNoHazardStep (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop := FreshStep E hψ h2 r .openNoHazard
abbrev FreshMixedStep (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop := FreshStep E hψ h2 r .mixed

private theorem reachableStepFresh
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (r : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (h : ReachableFromV31 E hψ h2 r C) :
    ReachableFromV31 E hψ h2 r (stepV3 hψ h2 r C e) := by
  rcases h with ⟨C0,w,hE,hC⟩
  refine ⟨C0,w ++ [e],hE,?_⟩
  rw [List.foldl_append, ← hC]
  rfl

/-- Entrance-parametric Fresh induction.  Parts 1/2 are intentionally not
claimed parametric by their installed wrappers below; callers may supply any
ten `FreshStep`s, including later parametric restatements of those branches. -/
theorem reachableSoundFresh_of_branchSteps
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (r : DirectedRing n)
    (hSeek : FreshSeekStep E hψ h2 r)
    (hSweep : FreshSweepStep E hψ h2 r)
    (hCommit : FreshCommitStep E hψ h2 r)
    (hRelease : FreshReleaseStep E hψ h2 r)
    (hScrubL : FreshScrubLStep E hψ h2 r)
    (hOpenR : FreshOpenRStep E hψ h2 r)
    (hSealed : FreshSealedStep E hψ h2 r)
    (hOpenHazard : FreshOpenHazardStep E hψ h2 r)
    (hOpenNoHazard : FreshOpenNoHazardStep E hψ h2 r)
    (hMixed : FreshMixedStep E hψ h2 r)
    (hBase : ∀ C0, E C0 → ReachablePhaseFactsFreshV31 r C0)
    (hGeomBase : ∀ C0, E C0 → ElectionGeometryV31 r C0) :
    ∀ C, ReachableFromV31 E hψ h2 r C → ReachablePhaseFactsFreshV31 r C := by
  intro C hReach
  rcases hReach with ⟨C0,w,hE,hC⟩
  have carry : ∀ (v : List (Fin n)) (D : FC n ψ κ τ),
      ReachableFromV31 E hψ h2 r D → ElectionGeometryV31 r D →
      ReachablePhaseFactsFreshV31 r D →
      ReachablePhaseFactsFreshV31 r (v.foldl (stepV3 hψ h2 r) D) := by
    intro v
    induction v with
    | nil => intro D _ _ hF; simpa using hF
    | cons e v ih =>
      intro D hT hG hF
      simp only [List.foldl_cons]
      have hN : ReachablePhaseFactsFreshV31 r (stepV3 hψ h2 r D e) := by
        cases hb : branchAtV3 hψ h2 (D e) (D (r.rightNeighbor e)) with
        | seek => exact hSeek D e hG hT hF hb
        | sweep => exact hSweep D e hG hT hF hb
        | commit => exact hCommit D e hG hT hF hb
        | release => exact hRelease D e hG hT hF hb
        | scrubL => exact hScrubL D e hG hT hF hb
        | openR => exact hOpenR D e hG hT hF hb
        | sealed => exact hSealed D e hG hT hF hb
        | openHazard => exact hOpenHazard D e hG hT hF hb
        | openNoHazard => exact hOpenNoHazard D e hG hT hF hb
        | mixed => exact hMixed D e hG hT hF hb
      exact ih _ (reachableStepFresh E hψ h2 r D e hT)
        ((electionGeometryStepV31 (κ:=κ) (τ:=τ) hψ h2 r) D e hG) hN
  rw [hC]
  exact carry w C0 ⟨C0,[],hE,rfl⟩ (hGeomBase C0 hE) (hBase C0 hE)

-- Part 3: genuinely entrance-parametric wrappers.
theorem stepPreservesFresh_seek_of_residuals
    (E : FC n ψ κ τ → Prop) (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n)
    (s : SeekSFreshPreservationV31P E hψ h2 r)
    (r2 : SeekStrongR2FreshPreservationV31P E hψ h2 r)
    (rp : SeekFreshPrivateReplayV31P E hψ h2 r) : FreshSeekStep E hψ h2 r :=
  seekStep_reachable_fresh_of_residuals E hψ h2 r s r2 rp

theorem stepPreservesFresh_scrubL_of_residuals
    (E : FC n ψ κ τ → Prop) (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n)
    (p8 : ScrubLP8FreshPreservationV31P E hψ h2 r)
    (p9 : ScrubLP9FreshPreservationV31P E hψ h2 r)
    (s : ScrubLSFreshPreservationV31P E hψ h2 r)
    (r2 : ScrubLStrongR2FreshPreservationV31P E hψ h2 r)
    (rp : ScrubLFreshPrivateReplayV31P E hψ h2 r) : FreshScrubLStep E hψ h2 r :=
  scrubLStep_reachable_fresh_of_residuals E hψ h2 r p8 p9 s r2 rp

theorem stepPreservesFresh_openR_of_residuals
    (E : FC n ψ κ τ → Prop) (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n)
    (s : OpenRSFreshSourceV31P E hψ h2 r)
    (r1 : OpenRR1FreshPreservationV31P E hψ h2 r)
    (r2 : OpenRStrongR2FreshPreservationV31P E hψ h2 r)
    (rp : OpenRFreshPrivateReplayV31P E hψ h2 r) : FreshOpenRStep E hψ h2 r :=
  openRStep_reachable_fresh_of_residuals E hψ h2 r s r1 r2 rp

private theorem birthTrace
    (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n) (C : FC n ψ κ τ)
    (h : ReachableFromV31 (BirthEntranceV1 hψ h2 r) hψ h2 r C) :
    ReachableFromQuarantineV31 hψ h2 r C :=
  (reachableFromV31_birth_iff (κ:=κ) (τ:=τ) hψ h2 r C).1 h

-- Parts 1/2 and OPEN-NO-HAZARD: BirthEntrance compatibility wrappers.
theorem stepPreservesFresh_commit_of_residuals
    (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n) :
    FreshCommitStep (κ:=κ) (τ:=τ)
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r := by
  intro C e hg ht hf hb
  exact commitStep_reachable_fresh (κ:=κ) (τ:=τ) hψ h2 r C e hg
    (birthTrace (κ:=κ) (τ:=τ) hψ h2 r C ht) hf hb

theorem stepPreservesFresh_sealed_of_residuals
    (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n) :
    FreshSealedStep (κ:=κ) (τ:=τ)
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r := by
  intro C e hg ht hf hb
  exact sealedStep_reachable_fresh (κ:=κ) (τ:=τ) hψ h2 r C e hg
    (birthTrace (κ:=κ) (τ:=τ) hψ h2 r C ht) hf hb

theorem stepPreservesFresh_sweep_of_residuals
    (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n)
    (hs : SweepCurrentOpenRServedSafeFreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (htl : SweepStrongTailPreservationFreshV31 (κ:=κ) (τ:=τ) hψ h2 r) :
    FreshSweepStep (κ:=κ) (τ:=τ)
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r := by
  intro C e hg ht hf hb
  exact sweepStep_reachable_fresh_of_residuals (κ:=κ) (τ:=τ) hψ h2 r hs htl
    C e hg (birthTrace (κ:=κ) (τ:=τ) hψ h2 r C ht) hf hb

theorem stepPreservesFresh_release_of_residuals
    (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n)
    (p7 : ReleaseP7FreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (p8 : ReleaseP8FreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (p9 : ReleaseP9FreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (s : ReleaseSFreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (r2 : ReleaseR2FreshV31 (κ:=κ) (τ:=τ) hψ h2 r) :
    FreshReleaseStep (κ:=κ) (τ:=τ)
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r := by
  intro C e hg ht hf hb
  exact releaseStep_reachable_fresh_of_residuals (κ:=κ) (τ:=τ)
    hψ h2 r p7 p8 p9 s r2 C e hg
    (birthTrace (κ:=κ) (τ:=τ) hψ h2 r C ht) hf hb

theorem stepPreservesFresh_openHazard_of_residuals
    (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n)
    (hn : OpenHazardFreshSeekPrepaidFreshV31 (κ:=κ) (τ:=τ) hψ h2 r) :
    FreshOpenHazardStep (κ:=κ) (τ:=τ)
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r := by
  intro C e hg ht hf hb
  exact openHazardStep_reachable_fresh_of_residuals (κ:=κ) (τ:=τ) hψ h2 r hn
    C e hg (birthTrace (κ:=κ) (τ:=τ) hψ h2 r C ht) hf hb

theorem stepPreservesFresh_mixed_of_residuals
    (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n)
    (s : MixedSFreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (r1 : MixedR1FreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (r2 : MixedR2FreshV31 (κ:=κ) (τ:=τ) hψ h2 r) :
    FreshMixedStep (κ:=κ) (τ:=τ)
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r := by
  intro C e hg ht hf hb
  exact mixedStep_reachable_fresh_of_residuals (κ:=κ) (τ:=τ) hψ h2 r s r1 r2
    C e hg (birthTrace (κ:=κ) (τ:=τ) hψ h2 r C ht) hf hb

theorem stepPreservesFresh_openNoHazard_of_residuals
    (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n)
    (hc : SanitizedR2NewEqualFreshChainOriginNoMainMutation
      (κ:=κ) (τ:=τ) hψ (by decide : 0<2) h2) :
    FreshOpenNoHazardStep (κ:=κ) (τ:=τ)
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r := by
  intro C e hg ht hf hb
  exact openNoHazardStep_reachable_fresh (κ:=κ) (τ:=τ) hψ h2 r hc C e hg
    (birthTrace (κ:=κ) (τ:=τ) hψ h2 r C ht) hf hb

theorem reachableSoundFresh_of_installed
    (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n)
    (seekS : SeekSFreshPreservationV31P (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (seekR2 : SeekStrongR2FreshPreservationV31P (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (seekReplay : SeekFreshPrivateReplayV31P (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (swSafe : SweepCurrentOpenRServedSafeFreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (swTail : SweepStrongTailPreservationFreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (rel7 : ReleaseP7FreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (rel8 : ReleaseP8FreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (rel9 : ReleaseP9FreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (relS : ReleaseSFreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (relR2 : ReleaseR2FreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (scr8 : ScrubLP8FreshPreservationV31P (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (scr9 : ScrubLP9FreshPreservationV31P (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (scrS : ScrubLSFreshPreservationV31P (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (scrR2 : ScrubLStrongR2FreshPreservationV31P (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (scrReplay : ScrubLFreshPrivateReplayV31P (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (orS : OpenRSFreshSourceV31P (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (orR1 : OpenRR1FreshPreservationV31P (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (orR2 : OpenRStrongR2FreshPreservationV31P (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (orReplay : OpenRFreshPrivateReplayV31P (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (haz : OpenHazardFreshSeekPrepaidFreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (onh : SanitizedR2NewEqualFreshChainOriginNoMainMutation
      (κ:=κ) (τ:=τ) hψ (by decide : 0<2) h2)
    (mixS : MixedSFreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (mixR1 : MixedR1FreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (mixR2 : MixedR2FreshV31 (κ:=κ) (τ:=τ) hψ h2 r) :
    ∀ C : FC n ψ κ τ,
      ReachableFromQuarantineV31 hψ h2 r C → ReachablePhaseFactsFreshV31 r C := by
  let E : FC n ψ κ τ → Prop := BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r
  have hs := stepPreservesFresh_seek_of_residuals E hψ h2 r seekS seekR2 seekReplay
  have hw := stepPreservesFresh_sweep_of_residuals (κ:=κ) (τ:=τ) hψ h2 r swSafe swTail
  have hc := stepPreservesFresh_commit_of_residuals (κ:=κ) (τ:=τ) hψ h2 r
  have hr := stepPreservesFresh_release_of_residuals (κ:=κ) (τ:=τ) hψ h2 r rel7 rel8 rel9 relS relR2
  have hsl := stepPreservesFresh_scrubL_of_residuals E hψ h2 r scr8 scr9 scrS scrR2 scrReplay
  have hor := stepPreservesFresh_openR_of_residuals E hψ h2 r orS orR1 orR2 orReplay
  have hse := stepPreservesFresh_sealed_of_residuals (κ:=κ) (τ:=τ) hψ h2 r
  have hoh := stepPreservesFresh_openHazard_of_residuals (κ:=κ) (τ:=τ) hψ h2 r haz
  have honh := stepPreservesFresh_openNoHazard_of_residuals (κ:=κ) (τ:=τ) hψ h2 r onh
  have hm := stepPreservesFresh_mixed_of_residuals (κ:=κ) (τ:=τ) hψ h2 r mixS mixR1 mixR2
  have hSound := reachableSoundFresh_of_branchSteps (κ:=κ) (τ:=τ) E hψ h2 r
    hs hw hc hr hsl hor hse hoh honh hm
    (birthEntrancePayloadFreshV31 (κ:=κ) (τ:=τ) hψ h2 r) (fun _ hBirth => hBirth.2)
  intro C ht
  exact hSound C ((reachableFromV31_birth_iff (κ:=κ) (τ:=τ) hψ h2 r C).2 ht)

abbrev C1FreshEntranceV31
    (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n) : FC n ψ κ τ → Prop :=
  C1FinalV31AdmittedEntrance (kappa:=κ) (tau:=τ) hψ h2 r

def C1FinalV31AdmittedReachableFreshResidual
    (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n) : Prop :=
  ∀ Q, ReachableFromV31 (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r)
      hψ h2 r Q → ReachablePhaseFactsFreshV31 r Q

theorem admittedEntrancePayloadFreshV31
   (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n)
   (Q : FC n ψ κ τ)
   (hQ : C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r Q) :
   ReachablePhaseFactsFreshV31 r Q := by
 rcases hQ with ⟨C,_,_,_,rfl⟩
 have hf := reachablePhaseFacts_liftFinalV31 r C
 have hn : ∀ i : Fin n, (liftFinalV31 C i).ctl.tok = .none := by
   intro i; rfl
 refine ⟨hf,?_,?_,?_,?_,?_,?_⟩
 · intro o hs; rw [hn (r.rightNeighbor o)] at hs; cases hs
 · intro s o hs; rw [hn s] at hs; cases hs
 · intro s o hs; rw [hn s] at hs; cases hs
 · intro e o hs; rw [hn (r.rightNeighbor e)] at hs; cases hs
 · intro e hs; rw [hn e] at hs; cases hs
 · intro s o p hs; rw [hn s] at hs; cases hs

theorem c1FinalV31AdmittedReachableFreshResidual_of_branchSteps
    (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n)
    (hGeom : C1FinalV31AdmittedElectionGeometryResidual
      (kappa:=κ) (tau:=τ) hψ h2 r)
    (hs : FreshSeekStep (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (hw : FreshSweepStep (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (hc : FreshCommitStep (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (hr : FreshReleaseStep (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (hsl : FreshScrubLStep (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (hor : FreshOpenRStep (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (hse : FreshSealedStep (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (hoh : FreshOpenHazardStep (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (honh : FreshOpenNoHazardStep (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (hm : FreshMixedStep (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r) :
    C1FinalV31AdmittedReachableFreshResidual (κ:=κ) (τ:=τ) hψ h2 r := by
  let E : FC n ψ κ τ → Prop := C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r
  apply reachableSoundFresh_of_branchSteps (κ:=κ) (τ:=τ) E hψ h2 r
    hs hw hc hr hsl hor hse hoh honh hm
  · exact admittedEntrancePayloadFreshV31 (κ:=κ) (τ:=τ) hψ h2 r
  · intro Q hQ
    rcases hQ with ⟨C,hA,hL,hO,rfl⟩
    exact hGeom C hA hL hO

theorem c1FinalV31AdmittedReachableFreshResidual_of_installedParametric
    (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n)
    (hGeom : C1FinalV31AdmittedElectionGeometryResidual
      (kappa:=κ) (tau:=τ) hψ h2 r)
    (seekS : SeekSFreshPreservationV31P
      (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (seekR2 : SeekStrongR2FreshPreservationV31P
      (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (seekReplay : SeekFreshPrivateReplayV31P
      (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (hSweep : FreshSweepStep
      (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (hCommit : FreshCommitStep
      (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (hRelease : FreshReleaseStep
      (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (scr8 : ScrubLP8FreshPreservationV31P
      (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (scr9 : ScrubLP9FreshPreservationV31P
      (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (scrS : ScrubLSFreshPreservationV31P
      (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (scrR2 : ScrubLStrongR2FreshPreservationV31P
      (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (scrReplay : ScrubLFreshPrivateReplayV31P
      (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (orS : OpenRSFreshSourceV31P
      (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (orR1 : OpenRR1FreshPreservationV31P
      (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (orR2 : OpenRStrongR2FreshPreservationV31P
      (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (orReplay : OpenRFreshPrivateReplayV31P
      (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (hSealed : FreshSealedStep
      (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (hOpenHazard : FreshOpenHazardStep
      (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (hOpenNoHazard : FreshOpenNoHazardStep
      (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r)
    (hMixed : FreshMixedStep
      (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r) :
    C1FinalV31AdmittedReachableFreshResidual (κ:=κ) (τ:=τ) hψ h2 r := by
  let E : FC n ψ κ τ → Prop :=
    C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r
  have hs := stepPreservesFresh_seek_of_residuals
    (κ:=κ) (τ:=τ) E hψ h2 r seekS seekR2 seekReplay
  have hsl := stepPreservesFresh_scrubL_of_residuals
    (κ:=κ) (τ:=τ) E hψ h2 r scr8 scr9 scrS scrR2 scrReplay
  have hor := stepPreservesFresh_openR_of_residuals
    (κ:=κ) (τ:=τ) E hψ h2 r orS orR1 orR2 orReplay
  exact c1FinalV31AdmittedReachableFreshResidual_of_branchSteps
    (κ:=κ) (τ:=τ) hψ h2 r hGeom
    hs hSweep hCommit hRelease hsl hor hSealed hOpenHazard hOpenNoHazard hMixed

theorem c1FinalV31AdmittedReachablePhaseResidual_of_fresh
    (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n)
    (hFresh : C1FinalV31AdmittedReachableFreshResidual
      (κ:=κ) (τ:=τ) hψ h2 r) :
    C1FinalV31AdmittedReachablePhaseResidual
      (kappa:=κ) (tau:=τ) hψ h2 r := by
  intro C hA hL hO w
  have hR : ReachableFromV31 (C1FreshEntranceV31 (κ:=κ) (τ:=τ) hψ h2 r)
      hψ h2 r (w.foldl (stepV3 hψ h2 r) (liftFinalV31 C)) :=
    ⟨liftFinalV31 C,w,⟨C,hA,hL,hO,rfl⟩,rfl⟩
  exact (hFresh _ hR).1



end R2CoherenceV31ReachableSoundFreshInstances
