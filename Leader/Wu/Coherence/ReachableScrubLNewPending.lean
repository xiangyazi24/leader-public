import Leader.Wu.Coherence.ReachableScrubLResiduals
import Leader.Wu.Coherence.ReachableReleaseOwnerAdjacentRoot
import Leader.Wu.Coherence.ReachableFootprintCovered

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableScrubL3

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard3
open R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31ReachableScrubL R2CoherenceV31ReachableScrubL2
open R2CoherenceV31ReachableReleaseOwner2
open R2CoherenceV31ReachableAdjacentRoot

variable {n ψ κ τ : Nat}

private theorem row3 (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .scrubL) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = scrubLStageV3 l r := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all [rowV3]
  all_goals grind

private theorem shape3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL) :
    successorB (C e) (C (ring.rightNeighbor e)) = true ∧
      atRootB (C (ring.rightNeighbor e)) = false := by
  have hp := scrubL_guard_prepays_current_owner
    hψ h2 ring C e hPlus.1.1.1.1 hb
  have hr : atRootB (C (ring.rightNeighbor e)) = false := by
    cases h : atRootB (C (ring.rightNeighbor e)) with
    | false => rfl
    | true =>
      have hz : (raw (C (ring.rightNeighbor e))).label.val = 0 := by
        simpa [atRootB] using h
      exact (hp.2.1 hz).elim
  have hs : successorB (C e) (C (ring.rightNeighbor e)) = true := by
    simpa [ElectionGeometryV31, passiveEdgeOKV3, hr] using hGeom e
  exact ⟨hs, hr⟩

private theorem edgeNe3 (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    e ≠ ring.rightNeighbor e := by
  intro h
  have hv : (raw (C (ring.rightNeighbor e))).label.val =
      (raw (C e)).label.val + 1 := by simpa [successorB] using hs
  have he := congrArg (fun p : Fin n => (raw (C p)).label.val) h
  omega

private theorem left3 (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hr : atRootB (C (ring.rightNeighbor e)) = false) :
    stepV3 hψ h2 ring C e e =
      if atRootB (C e) then setControl (clearMain (C e)) .releasing .openR
      else setControl (clearMain (C e)) .releasing .scrubL := by
  have hrow := row3 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, scrubLStageV3, hs, hr]

private theorem right3 (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hr : atRootB (C (ring.rightNeighbor e)) = false) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      setControl (clearMain (C (ring.rightNeighbor e))) .releasing .none := by
  have hrow := row3 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  have hne := Ne.symm (edgeNe3 ring C e hs)
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, scrubLStageV3, hs, hr, hne]

private theorem scrubSource3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hr : atRootB (C (ring.rightNeighbor e)) = false)
    (ht : (stepV3 hψ h2 ring C e p).ctl.tok = .scrubL) :
    p = e ∨ stepV3 hψ h2 ring C e p = C p := by
  by_cases hp : p = e
  · exact Or.inl hp
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      rw [right3 hψ h2 ring C e hb hs hr] at ht
      simp [setControl] at ht
    · exact Or.inr (stepV3_other hψ h2 ring C e p hp hpr)

private theorem rootEq3 (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n) :
    atRootB (stepV3 hψ h2 ring C e p) = atRootB (C p) := by
  unfold atRootB
  rw [stepV3_labels_eq_or_held hψ h2 ring C e p]

private theorem succEq3 (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n) :
    successorB (stepV3 hψ h2 ring C e p)
        (stepV3 hψ h2 ring C e (ring.rightNeighbor p)) =
      successorB (C p) (C (ring.rightNeighbor p)) := by
  unfold successorB
  rw [stepV3_labels_eq_or_held hψ h2 ring C e p,
    stepV3_labels_eq_or_held hψ h2 ring C e (ring.rightNeighbor p)]


def ScrubLContinuationNewPendingV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n) : Prop :=
  PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) owner ∧
    ¬ PendingOpenROwnerV31 ring C owner

theorem scrubLContinuationNewPending_iff
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL) :
    ScrubLContinuationNewPendingV31 hψ h2 ring C e owner ↔
      ring.rightNeighbor owner = e ∧
      atRootB (C owner) = true ∧
      successorB (C owner) (C e) = true ∧
      atRootB (C e) = false ∧
      (C e).ctl.tok ≠ .scrubL := by
  rcases shape3 hψ h2 ring C e hGeom hPlus hb with ⟨hs, hr⟩
  unfold ScrubLContinuationNewPendingV31
  constructor
  · rintro ⟨hD, hNot⟩
    have hsC : successorB (C owner) (C (ring.rightNeighbor owner)) = true := by
      rw [← succEq3 hψ h2 ring C e owner]
      exact hD.2.1
    have hrootC : atRootB (C owner) = true := by
      rw [← rootEq3 hψ h2 ring C e owner]
      exact hD.2.2
    rcases scrubSource3 hψ h2 ring C e (ring.rightNeighbor owner)
      hb hs hr hD.1 with hnew | heq
    · have hrootE : atRootB (C e) = false := by
        cases h0 : atRootB (C e) with
        | false => rfl
        | true =>
          have hx := hD.1
          rw [hnew] at hx
          rw [left3 hψ h2 ring C e hb hs hr] at hx
          simp [h0, setControl] at hx
      have hold : (C e).ctl.tok ≠ .scrubL := by
        intro ht
        apply hNot
        refine ⟨?_, hsC, hrootC⟩
        simpa [hnew] using ht
      exact ⟨hnew, hrootC, by simpa [hnew] using hsC, hrootE, hold⟩
    · exfalso
      apply hNot
      refine ⟨?_, hsC, hrootC⟩
      rw [← heq]
      exact hD.1
  · rintro ⟨hnew, hroot, hsOwner, hnonroot, hold⟩
    constructor
    · refine ⟨?_, ?_, ?_⟩
      · rw [hnew, left3 hψ h2 ring C e hb hs hr]
        simp [hnonroot, setControl]
      · rw [succEq3 hψ h2 ring C e owner]
        simpa [hnew] using hsOwner
      · rw [rootEq3 hψ h2 ring C e owner]
        exact hroot
    · intro hOld
      apply hold
      simpa [hnew] using hOld.1

theorem scrubLContinuationNewPending_labels
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hNew : ScrubLContinuationNewPendingV31 hψ h2 ring C e owner) :
    (raw (C owner)).label.val = 0 ∧
    (raw (C e)).label.val = 1 ∧
    (raw (C (ring.rightNeighbor e))).label.val = 2 ∧ 3 ≤ ψ := by
  have hc := (scrubLContinuationNewPending_iff
    hψ h2 ring C e owner hGeom hPlus hb).1 hNew
  have h0 : (raw (C owner)).label.val = 0 := by
    simpa [atRootB] using hc.2.1
  have h1a : (raw (C e)).label.val = (raw (C owner)).label.val + 1 := by
    simpa [successorB] using hc.2.2.1
  have hs := (shape3 hψ h2 ring C e hGeom hPlus hb).1
  have h2a : (raw (C (ring.rightNeighbor e))).label.val =
      (raw (C e)).label.val + 1 := by simpa [successorB] using hs
  have hlt := (raw (C (ring.rightNeighbor e))).label.isLt
  omega

private theorem traceStep3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (h : ReachableFromQuarantineV31 hψ h2 ring C) :
    ReachableFromQuarantineV31 hψ h2 ring (stepV3 hψ h2 ring C e) := by
  rcases h with ⟨C0, w, hBirth, hC⟩
  refine ⟨C0, w ++ [e], hBirth, ?_⟩
  rw [List.foldl_append, ← hC]
  rfl

theorem overlapSeek_of_cover
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hFacts : ReachablePhaseFactsV31 ring C)
    (hCover : PendingOpenRFootprintCoveredV31 ring C) :
    SweepOpenROverlapClearV31 ring C ∧
    SweepOpenROverlapClearWideV31 ring C ∧
    SeekIncomingSweepOpenROverlapClearWideV31 ring C := by
  have safe : ∀ owner p, PendingOpenROwnerV31 ring C owner →
      SweepOpenRSafeAtV31 ring C owner p := by
    intro owner p hp
    exact pendingOwner_safe_everywhere_of_covered
      ring C hFacts hCover owner p hp
  refine ⟨?_, ?_, ?_⟩
  · intro sweep owner _ hp
    exact ⟨by simpa [SweepOpenRSafeAtV31] using safe owner sweep hp,
      by simpa [SweepOpenRSafeAtV31] using
        safe owner (ring.rightNeighbor sweep) hp⟩
  · intro sweep owner _ hp
    exact ⟨safe owner (ring.rightNeighbor sweep) hp,
      fun d => safe owner (R2Coherence.fwd ring sweep d.val) hp⟩
  · intro pred owner _ hp
    constructor
    · intro _
      exact ⟨safe owner (ring.rightNeighbor (ring.rightNeighbor pred)) hp,
        fun d => safe owner
          (R2Coherence.fwd ring (ring.rightNeighbor pred) d.val) hp⟩
    · intro _ _
      exact ⟨safe owner (ring.rightNeighbor pred) hp,
        fun d => safe owner (R2Coherence.fwd ring pred d.val) hp⟩

private theorem postCover3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C) :
    PendingOpenRFootprintCoveredV31 ring (stepV3 hψ h2 ring C e) := by
  exact hCov _ (traceStep3 hψ h2 ring C e hTrace)
    ((R2CoherenceV31Closure2.electionGeometryStepV31
      (κ := κ) (τ := τ) hψ h2 ring) C e hGeom)


theorem scrubLP8Preservation_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 ring) :
    ScrubLP8PreservationV31 (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hGeom hTrace hPlus hb _
  have hf := reachablePhaseFacts_scrubL_step
    hψ h2 ring C e hGeom hTrace hPlus hb
  exact (overlapSeek_of_cover ring _ hf
    (postCover3 hψ h2 ring hCov C e hGeom hTrace)).1

theorem scrubLP9Preservation_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 ring) :
    ScrubLP9PreservationV31 (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hGeom hTrace hPlus hb _ _
  have hf := reachablePhaseFacts_scrubL_step
    hψ h2 ring C e hGeom hTrace hPlus hb
  exact (overlapSeek_of_cover ring _ hf
    (postCover3 hψ h2 ring hCov C e hGeom hTrace)).2.1

theorem scrubLSPreservation_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 ring) :
    ScrubLSPreservationV31 (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hGeom hTrace _ _ hP3
  exact (overlapSeek_of_cover ring _ hP3.1.1.1
    (postCover3 hψ h2 ring hCov C e hGeom hTrace)).2.2

/-- The exact part of strong-R2 which cover does not supply for a genuinely
new SCRUBL pending owner: on the cover's direct-main-clear arm we still need
phase ownership. -/
def ScrubLNewPendingMainClearOwnedV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e owner sweep p : Fin n),
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL →
    ScrubLContinuationNewPendingV31 hψ h2 ring C e owner →
    (stepV3 hψ h2 ring C e sweep).ctl.tok = .sweep →
    InSweepWideReadV31 ring (stepV3 hψ h2 ring C e) sweep p →
    InOpenRFreshFootprintV31 ring (stepV3 hψ h2 ring C e) owner p →
    MainClearV3 (stepV3 hψ h2 ring C e p) →
      PhaseOwnedV31 (stepV3 hψ h2 ring C e p)

theorem scrubLNewPendingStrongTail_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 ring)
    (hDirect : ScrubLNewPendingMainClearOwnedV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hNew : ScrubLContinuationNewPendingV31 hψ h2 ring C e owner) :
    ∀ (sweep p : Fin n),
      (stepV3 hψ h2 ring C e sweep).ctl.tok = .sweep →
      InSweepWideReadV31 ring (stepV3 hψ h2 ring C e) sweep p →
      InOpenRFreshFootprintV31 ring (stepV3 hψ h2 ring C e) owner p →
        PhaseOwnedV31 (stepV3 hψ h2 ring C e p) := by
  intro sweep p hSweep hRead hFoot
  have hf := reachablePhaseFacts_scrubL_step
    hψ h2 ring C e hGeom hTrace hPlus hb
  have hc := postCover3 hψ h2 ring hCov C e hGeom hTrace
  have hn := hNew
  unfold ScrubLContinuationNewPendingV31 at hn
  rcases hc owner p hn.1 hFoot with hm | hg
  · exact hDirect C e owner sweep p hGeom hTrace hPlus hb
      hNew hSweep hRead hFoot hm
  · rcases hg with ⟨k, hk⟩
    have hs := hf.2.2.2.2.1 (ring.rightNeighbor owner) hn.1.1
    have ho := (hs.2.2 k).2
    rw [hk] at ho
    exact ho

/-- Formal reason the cover cannot by itself imply the strong-R2 tail. -/
theorem mainClear_open_none_not_phaseOwned3 (u : Cell ψ κ τ) :
    MainClearV3 (setControl (clearMain u) .open .none) ∧
      ¬ PhaseOwnedV31 (setControl (clearMain u) .open .none) := by
  constructor
  · unfold MainClearV3 R2CoherenceBranches.MainClear
    simp [eraseCellV3, setControl, clearMain, R2Coherence.clearMainPhys,
      PPLLExpiringComparisonRepair.clearComparisonCarrier, R2Coherence.raw]
  · simp [PhaseOwnedV31, setControl]

end R2CoherenceV31ReachableScrubL3
