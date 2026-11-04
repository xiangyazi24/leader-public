import Leader.Wu.Coherence.ReachableStrongOwnership
import Leader.Wu.Coherence.ReachableSoundInstances

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableOpenNoHazard5

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31OpenNoHazard R2CoherenceV31OpenNoHazardClose
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard
open R2CoherenceV31ReachableOpenNoHazard3
open R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31ReachableSound

variable {n ψ κ τ : Nat}

def OpenNoHazardServedMainClearPreservationV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e p : Fin n),
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard →
    (p = e ∨ p = ring.rightNeighbor e) →
    MainClearV3 (C p) →
      MainClearV3 (stepV3 hψ h2 ring C e p)

private theorem gp5 (ring : DirectedRing n) {C D : FC n ψ κ τ}
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

private theorem pp5 (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val - k) =
    R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [h i]

private theorem footprintBack5
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (owner p : Fin n)
    (hF : InOpenRFreshFootprintV31 ring D owner p) :
    InOpenRFreshFootprintV31 ring C owner p := by
  rcases hF with ⟨j, ko, q, hOwner, kD, hPrefix⟩
  rw [gp5 ring hLab j ko.val] at hOwner
  have hq := gp5 ring hLab j q.val
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hFront : R2Coherence.groupPos ring (eraseCfgV3 D) j q.val = front := by
    simpa [front] using hq
  have hv :
      (raw (D (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val))).label.val =
        (raw (C front)).label.val := by
    rw [hFront]
    exact congrArg Fin.val (hLab front)
  have hk : kD.val < (raw (C front)).label.val + 1 := by
    simpa only [hv] using kD.isLt
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hk⟩
  refine ⟨j, ko, q, hOwner, kC, ?_⟩
  have h0 : R2Coherence.prefixPos ring (eraseCfgV3 D) front kD.val = p := by
    simpa only [hFront] using hPrefix
  have hp := pp5 ring hLab front kD.val
  have hc := hp.symm.trans h0
  simpa [front, kC] using hc


private theorem pendingBack5
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D) (owner : Fin n)
    (h : PendingOpenROwnerV31 ring D owner) :
    PendingOpenROwnerV31 ring C owner := by
  rcases h with ⟨hs, hsucc, hr⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [(hF (ring.rightNeighbor owner)).2.2.2] at hs
    exact hs
  · have hl := congrArg Fin.val (hF owner).1
    have hh := congrArg Fin.val (hF (ring.rightNeighbor owner)).1
    unfold successorB at hsucc ⊢
    simpa only [hl, hh] using hsucc
  · have hl := congrArg Fin.val (hF owner).1
    unfold atRootB at hr ⊢
    simpa only [hl] using hr

private theorem rootEq5 {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label) (p : Fin n) :
    atRootB (D p) = atRootB (C p) := by
  unfold atRootB
  rw [hLab p]

private theorem mainClearStep5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hMain : OpenNoHazardServedMainClearPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard)
    (hm : MainClearV3 (C p)) :
    MainClearV3 (stepV3 hψ h2 ring C e p) := by
  by_cases hpe : p = e
  · exact hMain C e p hGeom hTrace hPlus hb (Or.inl hpe) hm
  · by_cases hpr : p = ring.rightNeighbor e
    · exact hMain C e p hGeom hTrace hPlus hb (Or.inr hpr) hm
    · rw [stepV3_other hψ h2 ring C e p hpe hpr]
      exact hm

private theorem safeAt5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hMain : OpenNoHazardServedMainClearPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e owner p : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard)
    (h : SweepOpenRSafeAtV31 ring C owner p) :
    SweepOpenRSafeAtV31 ring (stepV3 hψ h2 ring C e) owner p := by
  have hF := openNoHazard_step_frame hψ h2 ring C e hb
  have hLab : ∀ x, (raw (stepV3 hψ h2 ring C e x)).label =
      (raw (C x)).label := fun x => (hF x).1
  unfold SweepOpenRSafeAtV31 at h ⊢
  rcases h with hm | hout
  · exact Or.inl (mainClearStep5 hψ h2 ring hMain C e p
      hGeom hTrace hPlus hb hm)
  · exact Or.inr (fun hf => hout (footprintBack5 ring hLab owner p hf))

private theorem tailSafe5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hMain : OpenNoHazardServedMainClearPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e owner base : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard)
    (h : ∀ d : Fin (ψ - (raw (C base)).label.val),
      SweepOpenRSafeAtV31 ring C owner (R2Coherence.fwd ring base d.val)) :
    ∀ d : Fin (ψ - (raw (stepV3 hψ h2 ring C e base)).label.val),
      SweepOpenRSafeAtV31 ring (stepV3 hψ h2 ring C e) owner
        (R2Coherence.fwd ring base d.val) := by
  intro dD
  have hF := openNoHazard_step_frame hψ h2 ring C e hb
  have hv := congrArg Fin.val (hF base).1
  have hd : dD.val < ψ - (raw (C base)).label.val := by
    simpa only [hv] using dD.isLt
  let dC : Fin (ψ - (raw (C base)).label.val) := ⟨dD.val, hd⟩
  exact safeAt5 hψ h2 ring hMain C e owner _ hGeom hTrace hPlus hb
    (by simpa [dC] using h dC)


theorem seekIncomingSweepOpenROverlapClearWide_openNoHazard_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hMain : OpenNoHazardServedMainClearPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    SeekIncomingSweepOpenROverlapClearWideV31 ring
      (stepV3 hψ h2 ring C e) := by
  have hF := openNoHazard_step_frame hψ h2 ring C e hb
  have hLab : ∀ x, (raw (stepV3 hψ h2 ring C e x)).label =
      (raw (C x)).label := fun x => (hF x).1
  intro pred owner hSeekD hPendingD
  have hSeekC := hSeekD
  rw [(hF (ring.rightNeighbor pred)).2.2.2] at hSeekC
  have hPendingC := pendingBack5 ring hF owner hPendingD
  have hOld := hPlus.2.1 pred owner hSeekC hPendingC
  constructor
  · intro hRootD
    have hRootC : atRootB (C (ring.rightNeighbor pred)) = true := by
      rw [← rootEq5 hLab _]
      exact hRootD
    rcases hOld.1 hRootC with ⟨ha, ht⟩
    exact ⟨safeAt5 hψ h2 ring hMain C e owner _ hGeom hTrace hPlus hb ha,
      tailSafe5 hψ h2 ring hMain C e owner (ring.rightNeighbor pred)
        hGeom hTrace hPlus hb ht⟩
  · intro hnD hrD
    have hnC : atRootB (C (ring.rightNeighbor pred)) = false := by
      rw [← rootEq5 hLab _]
      exact hnD
    have hrC : atRootB (C pred) = true := by
      rw [← rootEq5 hLab _]
      exact hrD
    rcases hOld.2 hnC hrC with ⟨ha, ht⟩
    exact ⟨safeAt5 hψ h2 ring hMain C e owner _ hGeom hTrace hPlus hb ha,
      tailSafe5 hψ h2 ring hMain C e owner pred
        hGeom hTrace hPlus hb ht⟩

theorem openRForwardMainClear_openNoHazard_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hMain : OpenNoHazardServedMainClearPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    OpenRForwardMainClearV31 ring (stepV3 hψ h2 ring C e) := by
  have hF := openNoHazard_step_frame hψ h2 ring C e hb
  intro owner hOpenD dD
  have hOpenC := hOpenD
  rw [(hF owner).2.2.2] at hOpenC
  have hv := congrArg Fin.val (hF owner).1
  have hd : dD.val < ψ - (raw (C owner)).label.val := by
    simpa only [hv] using dD.isLt
  let dC : Fin (ψ - (raw (C owner)).label.val) := ⟨dD.val, hd⟩
  have hmC := hPlus.2.2.1 owner hOpenC dC
  have hmC' : MainClearV3
      (C (R2Coherence.fwd ring owner dD.val)) := by
    simpa [dC] using hmC
  exact mainClearStep5 hψ h2 ring hMain C e _
    hGeom hTrace hPlus hb hmC'


theorem openNoHazardStep_reachable_full
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hChain : SanitizedR2NewEqualFreshChainOriginNoMainMutation
      (κ := κ) (τ := τ) hψ (by decide : 0 < 2) h2)
    (hMain : OpenNoHazardServedMainClearPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    ReachablePhaseFactsPlus4StrongR2V31 ring
      (stepV3 hψ h2 ring C e) := by
  have hOldPlus4 : ReachablePhaseFactsPlus4V31 ring C :=
    ⟨hPlus.1, hPlus.2.1, hPlus.2.2.1, hPlus.2.2.2.1⟩
  have hFactsD :=
    R2CoherenceV31ReachableOpenNoHazard.openNoHazardStep_reachable
      hψ h2 ring hChain C e hTrace hPlus.1.1.1.1 hb
  have hP7D :=
    R2CoherenceV31ReachableOpenNoHazard3.openNoHazard_preserves_scrubLIncoming_plus4
      hψ h2 ring hChain C e hTrace hOldPlus4 hb
  have hP8D :=
    R2CoherenceV31ReachableOpenNoHazard4.sweepOpenROverlapClear_openNoHazard_of_strongR2
      hψ h2 ring C e hPlus.1.2 hPlus.2.2.2 hb
  have hP9D :=
    R2CoherenceV31ReachableOpenNoHazard4.sweepOpenROverlapClearWide_openNoHazard_of_strongR2
      hψ h2 ring C e hPlus.1.2 hPlus.2.2.2 hb
  have hSD := seekIncomingSweepOpenROverlapClearWide_openNoHazard_step
    hψ h2 ring hMain C e hGeom hTrace hPlus hb
  have hR1D := openRForwardMainClear_openNoHazard_step
    hψ h2 ring hMain C e hGeom hTrace hPlus hb
  have hR2D :=
    R2CoherenceV31ReachableOpenNoHazard4.openRPhaseOwnershipDisjointStrong_openNoHazard_step
      hψ h2 ring C e hPlus.2.2.2 hb
  exact ⟨⟨⟨⟨hFactsD, hP7D⟩, hP8D⟩, hP9D⟩, hSD, hR1D, hR2D⟩

theorem stepPreservesV31_openNoHazard_of_residuals
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hChain : SanitizedR2NewEqualFreshChainOriginNoMainMutation
      (κ := κ) (τ := τ) hψ (by decide : 0 < 2) h2)
    (hMain : OpenNoHazardServedMainClearPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    StepPreservesV31_openNoHazard (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hGeom hTrace hPlus hb
  exact openNoHazardStep_reachable_full
    hψ h2 ring hChain hMain C e hGeom hTrace hPlus hb

end R2CoherenceV31ReachableOpenNoHazard5
