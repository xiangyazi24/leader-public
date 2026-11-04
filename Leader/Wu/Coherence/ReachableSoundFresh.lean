import Leader.Wu.Coherence.FreshPayload
import Leader.Wu.Coherence.ReachableSoundInstances

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableSoundFresh

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31OpenNoHazard R2CoherenceV31OpenNoHazardClose
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard
open R2CoherenceV31ReachableOpenNoHazard3
open R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31MainClearTruth
open R2CoherenceV31MainClearTruth.WeakFreshnessLayer
open R2CoherenceV31FreshnessClear

variable {n ψ κ τ : Nat}

def StepPreservesBranchFreshV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (b : BranchV3) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsFreshV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = b →
      ReachablePhaseFactsFreshV31 ring (stepV3 hψ h2 ring C e)

abbrev StepPreservesV31_seek_fresh (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :=
  StepPreservesBranchFreshV31 (κ := κ) (τ := τ) hψ h2 ring .seek
abbrev StepPreservesV31_sweep_fresh (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :=
  StepPreservesBranchFreshV31 (κ := κ) (τ := τ) hψ h2 ring .sweep
abbrev StepPreservesV31_commit_fresh (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :=
  StepPreservesBranchFreshV31 (κ := κ) (τ := τ) hψ h2 ring .commit
abbrev StepPreservesV31_release_fresh (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :=
  StepPreservesBranchFreshV31 (κ := κ) (τ := τ) hψ h2 ring .release
abbrev StepPreservesV31_scrubL_fresh (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :=
  StepPreservesBranchFreshV31 (κ := κ) (τ := τ) hψ h2 ring .scrubL
abbrev StepPreservesV31_openR_fresh (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :=
  StepPreservesBranchFreshV31 (κ := κ) (τ := τ) hψ h2 ring .openR
abbrev StepPreservesV31_sealed_fresh (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :=
  StepPreservesBranchFreshV31 (κ := κ) (τ := τ) hψ h2 ring .sealed
abbrev StepPreservesV31_openHazard_fresh (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :=
  StepPreservesBranchFreshV31 (κ := κ) (τ := τ) hψ h2 ring .openHazard
abbrev StepPreservesV31_openNoHazard_fresh (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :=
  StepPreservesBranchFreshV31 (κ := κ) (τ := τ) hψ h2 ring .openNoHazard
abbrev StepPreservesV31_mixed_fresh (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :=
  StepPreservesBranchFreshV31 (κ := κ) (τ := τ) hψ h2 ring .mixed

theorem birthEntrancePayloadFreshV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (hBirth : BirthEntranceV1 hψ h2 ring C) :
    ReachablePhaseFactsFreshV31 ring C := by
  exact reachablePhaseFactsFresh_of_oldStrong ring C
    (R2CoherenceV31ReachableOpenNoHazard4.reachablePhaseFactsPlus4StrongR2_entrance hψ h2 ring C hBirth)

private theorem gpF (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [h i]

private theorem ppF (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val - k) =
    R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [h i]

private theorem footprintBackF
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (owner p : Fin n) (h : InOpenRFreshFootprintV31 ring D owner p) :
    InOpenRFreshFootprintV31 ring C owner p := by
  rcases h with ⟨j, ko, q, ho, kD, hp⟩
  rw [gpF ring hLab j ko.val] at ho
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hf : R2Coherence.groupPos ring (eraseCfgV3 D) j q.val = front := by
    simpa [front] using gpF ring hLab j q.val
  have hv :
      (raw (D (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val))).label.val =
        (raw (C front)).label.val := by
    rw [hf]
    exact congrArg Fin.val (hLab front)
  have hk : kD.val < (raw (C front)).label.val + 1 := by
    simpa only [hv] using kD.isLt
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hk⟩
  refine ⟨j, ko, q, ho, kC, ?_⟩
  have h0 : R2Coherence.prefixPos ring (eraseCfgV3 D) front kD.val = p := by
    simpa only [hf] using hp
  simpa [front, kC] using (ppF ring hLab front kD.val).symm.trans h0

private theorem pendingBackF
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D) (owner : Fin n)
    (h : PendingOpenROwnerV31 ring D owner) :
    PendingOpenROwnerV31 ring C owner := by
  rcases h with ⟨hs, hu, hr⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [(hF (ring.rightNeighbor owner)).2.2.2] at hs
    exact hs
  · have hl := congrArg Fin.val (hF owner).1
    have hh := congrArg Fin.val (hF (ring.rightNeighbor owner)).1
    unfold successorB at hu ⊢
    simpa only [hl, hh] using hu
  · have hl := congrArg Fin.val (hF owner).1
    unfold atRootB at hr ⊢
    simpa only [hl] using hr

private theorem safeF
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D) (owner p : Fin n)
    (h : SweepOpenRSafeFreshV31 ring C owner p) :
    SweepOpenRSafeFreshV31 ring D owner p := by
  rcases h with hc | hout
  · left
    unfold FreshnessClearV31 at hc ⊢
    exact (hF p).2.2.1.trans hc
  · right
    intro hf
    exact hout (footprintBackF ring (fun x => (hF x).1) owner p hf)

theorem sweepOpenROverlapFresh_openNoHazard_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hP8 : SweepOpenROverlapFreshV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    SweepOpenROverlapFreshV31 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hF : OpenNoHazardFrameV31 C D := by
    simpa [D] using openNoHazard_step_frame hψ h2 ring C e hb
  intro s owner hsD hpD
  have hsC := hsD
  rw [(hF s).2.2.2] at hsC
  have hpC := pendingBackF ring hF owner hpD
  rcases hP8 s owner hsC hpC with ⟨ha, hb'⟩
  exact ⟨safeF ring hF owner s ha,
    safeF ring hF owner (ring.rightNeighbor s) hb'⟩

theorem sweepOpenROverlapFreshWide_openNoHazard_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hP9 : SweepOpenROverlapFreshWideV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    SweepOpenROverlapFreshWideV31 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hF : OpenNoHazardFrameV31 C D := by
    simpa [D] using openNoHazard_step_frame hψ h2 ring C e hb
  intro s owner hsD hpD
  have hsC := hsD
  rw [(hF s).2.2.2] at hsC
  have hpC := pendingBackF ring hF owner hpD
  rcases hP9 s owner hsC hpC with ⟨ha, ht⟩
  constructor
  · exact safeF ring hF owner (ring.rightNeighbor s) ha
  · intro dD
    have hv := congrArg Fin.val (hF s).1
    have hd : dD.val < ψ - (raw (C s)).label.val := by
      rw [← hv]
      exact dD.isLt
    let dC : Fin (ψ - (raw (C s)).label.val) := ⟨dD.val, hd⟩
    exact safeF ring hF owner _ (by simpa [dC] using ht dC)

theorem scrubLIncomingOpenRFresh_openNoHazard_fresh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hChain : SanitizedR2NewEqualFreshChainOriginNoMainMutation
      (κ := κ) (τ := τ) hψ (by decide : 0 < 2) h2)
    (C : FC n ψ κ τ) (e : Fin n)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hP7 : ScrubLIncomingOpenRFreshV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    ScrubLIncomingOpenRFreshV31 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hF : OpenNoHazardFrameV31 C D := by
    simpa [D] using openNoHazard_step_frame hψ h2 ring C e hb
  intro owner hs hu hr
  have hp := pendingBackF ring hF owner ⟨hs, hu, hr⟩
  have hOld := hP7 owner hp.1 hp.2.1 hp.2.2
  exact (R2CoherenceV31ReachableOpenNoHazard3.openNoHazardOwnerFreshTransport
    (κ := κ) (τ := τ) hψ h2 ring) hChain C e owner hTrace hOld hb

/-- Fresh lineage: Plus4-strongR2 is superseded only for the freshness-facing
P8/P9/S/R1 clauses.  The `q14010_bad_right_produce` fixture therefore no longer
blocks OPEN-NO-HAZARD: the installed `.produce` leaves `path = .bot`.

The remaining Fresh branch re-derivations are exactly SEEK, SWEEP, COMMIT,
RELEASE, SCRUBL, OPEN-R, SEALED, OPEN-HAZARD, and MIXED.  Each old branch proof
either reads an old MainClear-valued P8/P9/S/R1 premise or is already exposed
as a whole-branch residual. -/
def FreshBranchRederivationResidualsV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesV31_seek_fresh (κ := κ) (τ := τ) hψ h2 ring ∧
  StepPreservesV31_sweep_fresh (κ := κ) (τ := τ) hψ h2 ring ∧
  StepPreservesV31_commit_fresh (κ := κ) (τ := τ) hψ h2 ring ∧
  StepPreservesV31_release_fresh (κ := κ) (τ := τ) hψ h2 ring ∧
  StepPreservesV31_scrubL_fresh (κ := κ) (τ := τ) hψ h2 ring ∧
  StepPreservesV31_openR_fresh (κ := κ) (τ := τ) hψ h2 ring ∧
  StepPreservesV31_sealed_fresh (κ := κ) (τ := τ) hψ h2 ring ∧
  StepPreservesV31_openHazard_fresh (κ := κ) (τ := τ) hψ h2 ring ∧
  StepPreservesV31_mixed_fresh (κ := κ) (τ := τ) hψ h2 ring

theorem openNoHazardStep_reachable_fresh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hChain : SanitizedR2NewEqualFreshChainOriginNoMainMutation
      (κ := κ) (τ := τ) hψ (by decide : 0 < 2) h2)
    (C : FC n ψ κ τ) (e : Fin n)
    (_hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hFresh : ReachablePhaseFactsFreshV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    ReachablePhaseFactsFreshV31 ring (stepV3 hψ h2 ring C e) := by
  rcases hFresh with ⟨hFacts, hP7, hP8, hP9, hS, hR1, hR2⟩
  have hFactsD :=
    R2CoherenceV31ReachableOpenNoHazard.openNoHazardStep_reachable
      hψ h2 ring hChain C e hTrace hFacts hb
  have hP7D := scrubLIncomingOpenRFresh_openNoHazard_fresh
    hψ h2 ring hChain C e hTrace hP7 hb
  have hP8D := sweepOpenROverlapFresh_openNoHazard_step
    hψ h2 ring C e hP8 hb
  have hP9D := sweepOpenROverlapFreshWide_openNoHazard_step
    hψ h2 ring C e hP9 hb
  have hSD :=
    R2CoherenceV31FreshnessClear.seekIncomingSweepOpenROverlapFreshWide_openNoHazard_step
        hψ h2 ring C e hS hb
  have hR1D :=
    R2CoherenceV31FreshnessClear.openRForwardFreshnessClear_openNoHazard_step
      hψ h2 ring C e hR1 hb
  have hR2D :=
    R2CoherenceV31FreshnessClear.sweepPendingOpenRFootprintOwnedV31F_openNoHazard_step
      hψ h2 ring C e hR2 hb
  exact ⟨hFactsD, hP7D, hP8D, hP9D, hSD, hR1D, hR2D⟩

theorem stepPreservesV31_openNoHazard_fresh_of_seam
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hChain : SanitizedR2NewEqualFreshChainOriginNoMainMutation
      (κ := κ) (τ := τ) hψ (by decide : 0 < 2) h2) :
    StepPreservesV31_openNoHazard_fresh
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hGeom hTrace hFresh hb
  exact openNoHazardStep_reachable_fresh
    hψ h2 ring hChain C e hGeom hTrace hFresh hb

end R2CoherenceV31ReachableSoundFresh
