import Leader.Wu.Coherence.ReachableFreshCommitSealedSweep
import Leader.Wu.Coherence.ReachableCoverForeignPrefix
import Leader.Wu.Coherence.FreshStrongOwnership

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableSweepFresh

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus4 R2CoherenceV31ReachableSweep
open R2CoherenceV31ReachableAdjacentRoot
open R2CoherenceV31ReachableCover R2CoherenceV31ReachableCover2
open R2CoherenceV31ReachableFreshBranches1
open R2CoherenceV31MainClearTruth
open R2CoherenceV31MainClearTruth.WeakFreshnessLayer
open R2CoherenceV31FreshnessClear
open R2CoherenceV31ReachableSoundFresh

variable {n ψ κ τ : Nat}

/-- Served-safe residual, copied at its consumed type. -/
def SweepCurrentOpenRServedSafeFreshQ14129
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e o : Fin n), ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsFreshV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep →
    (C o).ctl.tok = .openR →
      SweepOpenRSafeFreshV31 ring C o e ∧
      SweepOpenRSafeFreshV31 ring C o (ring.rightNeighbor e)

/-- Tail residual, copied at its now-plumbed F-clause type. -/
def SweepStrongTailPreservationFreshQ14129
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n), ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsFreshV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep →
      SeekIncomingSweepOpenROverlapFreshWideV31 ring
        (stepV3 hψ h2 ring C e) ∧
      OpenRForwardFreshnessClearV31 ring (stepV3 hψ h2 ring C e) ∧
      R2CoherenceV31FreshnessClear.SweepPendingOpenRFootprintOwnedV31F
        ring (stepV3 hψ h2 ring C e)

/-- Exact extra information still missing for a *current* openR owner.Only served cells which really lie in that current owner's footprint need a
freshness fact; the complementary cases are the right disjunct of P8 safety. -/
def SweepCurrentOpenRServedFootprintFreshV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e o : Fin n), ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsFreshV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep →
    (C o).ctl.tok = .openR →
      (InOpenRFreshFootprintV31 ring C o e → FreshnessClearV31 (C e)) ∧
      (InOpenRFreshFootprintV31 ring C o (ring.rightNeighbor e) →
        FreshnessClearV31 (C (ring.rightNeighbor e)))

theorem sweepCurrentOpenRServedSafeFresh_of_footprintFresh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCur : SweepCurrentOpenRServedFootprintFreshV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    SweepCurrentOpenRServedSafeFreshV31
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e o hg ht hF hb ho
  have h := hCur C e o hg ht hF hb ho
  constructor
  · by_cases hf : InOpenRFreshFootprintV31 ring C o e
    · exact Or.inl (h.1 hf)
    · exact Or.inr hf
  · by_cases hf : InOpenRFreshFootprintV31 ring C o (ring.rightNeighbor e)
    · exact Or.inl (h.2 hf)
    · exact Or.inr hf

private theorem pendingSafeFresh_of_cover_phase
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hPhase : PhaseMainClearV31 ring C)
    (hCover : PendingOpenRFootprintCoveredV31 ring C)
    (owner p : Fin n) (hp : PendingOpenROwnerV31 ring C owner) :
    SweepOpenRSafeFreshV31 ring C owner p := by
  by_cases hf : InOpenRFreshFootprintV31 ring C owner p
  · rcases hCover owner p hp hf with hm | hg
    · exact Or.inl (freshnessClear_of_mainClear _ hm)
    · left
      rcases hg with ⟨k, hk⟩
      have hGroup := hPhase.2.2.2.2 (ring.rightNeighbor owner) hp.1
      unfold GroupOwnedClearV31 at hGroup
      rw [← hk]
      exact freshnessClear_of_mainClear _ (hGroup k).1
  · exact Or.inr hf

/-- Cover + P5 is already strong enough to produce the F sentence. -/
theorem sweepPendingOpenRFootprintOwnedFresh_of_cover_phase
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hPhase : PhaseMainClearV31 ring C)
    (hCover : PendingOpenRFootprintCoveredV31 ring C) :
    R2CoherenceV31FreshnessClear.SweepPendingOpenRFootprintOwnedV31F ring C := by
  intro sweep owner p _hs hp _hr hf
  rcases pendingSafeFresh_of_cover_phase ring C hPhase hCover owner p hp with hc | hout
  · exact Or.inr hc
  · exact (hout hf).elim

private theorem boolFalse_sf (b : Bool) (h : b ≠ true) : b = false := by
  cases b <;> simp_all

private theorem sweepCond_sf
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .sweep) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok = .sweep := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowSweep_sf
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .sweep) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = sweepStageV3 l r := by
  rcases sweepCond_sf hψ h2 l r hb with ⟨hs, hw⟩
  simp [rowV3, hs, hw]

private theorem succLabels_sf (l r : Cell ψ κ τ)
    (h : successorB l r = true) :
    (raw r).label.val = (raw l).label.val + 1 := by
  simpa [successorB] using h

private theorem edgeNe_sf
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    e ≠ ring.rightNeighbor e := by
  intro he
  have hv := congrArg (fun p : Fin n => (raw (C p)).label.val) he
  have hs' := succLabels_sf (C e) (C (ring.rightNeighbor e)) hs
  omega

private theorem leftGood_sf
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e e =
      setControl (clearMain (C e)) .closing .none := by
  have hr := rowSweep_sf hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hr, sweepStageV3, hs]

private theorem rightGood_sf
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      setControl (clearMain (C (ring.rightNeighbor e))) .closing
        (if atTerminalB (C (ring.rightNeighbor e)) then .commit else .sweep) := by
  have hr := rowSweep_sf hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  have hn := edgeNe_sf ring C e hs
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hr, sweepStageV3, hs, Ne.symm hn]

private theorem leftBad_sf
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false) :
    stepV3 hψ h2 ring C e e = startClosing (C e) := by
  have hr := rowSweep_sf hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hr, sweepStageV3, hs]

private theorem badOther_sf
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false)
    (hpe : p ≠ e) : stepV3 hψ h2 ring C e p = C p := by
  by_cases hpr : p = ring.rightNeighbor e
  · subst p
    have hr := rowSweep_sf hψ h2 (C e) (C (ring.rightNeighbor e)) hb
    simpa [stepV3, protocolV3, PopulationProtocol.step,
      hr, sweepStageV3, hs, hpe]
  · exact stepV3_other hψ h2 ring C e p hpe hpr

private theorem postOpenROld_sf
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (ho : (stepV3 hψ h2 ring C e p).ctl.tok = .openR) :
    stepV3 hψ h2 ring C e p = C p := by
  by_cases hs : successorB (C e) (C (ring.rightNeighbor e)) = true
  · by_cases hpe : p = e
    · subst p
      rw [leftGood_sf hψ h2 ring C e hb hs] at ho
      simp [setControl] at ho
    · by_cases hpr : p = ring.rightNeighbor e
      · subst p
        rw [rightGood_sf hψ h2 ring C e hb hs] at ho
        cases ht : atTerminalB (C (ring.rightNeighbor e)) <;>
          simp [setControl, ht] at ho
      · exact stepV3_other hψ h2 ring C e p hpe hpr
  · have hsF := boolFalse_sf _ hs
    by_cases hpe : p = e
    · subst p
      rw [leftBad_sf hψ h2 ring C e hb hsF] at ho
      simp [startClosing, setControl] at ho
    · exact badOther_sf hψ h2 ring C e p hb hsF hpe

private theorem clearFresh_sf
    (u : Cell ψ κ τ) (m : R2Coherence.Mark) (t : TokenV3) :
    FreshnessClearV31 (setControl (clearMain u) m t) := by
  apply freshnessClear_of_mainClear
  unfold MainClearV3 R2CoherenceBranches.MainClear
  simp [eraseCellV3, setControl, clearMain, R2Coherence.clearMainPhys,
    PPLLExpiringComparisonRepair.clearComparisonCarrier, R2Coherence.raw]

private theorem sweepFreshnessClear_mono_sf
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hc : FreshnessClearV31 (C p)) :
    FreshnessClearV31 (stepV3 hψ h2 ring C e p) := by
  by_cases hs : successorB (C e) (C (ring.rightNeighbor e)) = true
  · by_cases hpe : p = e
    · subst p
      rw [leftGood_sf hψ h2 ring C e hb hs]
      exact clearFresh_sf _ .closing .none
    · by_cases hpr : p = ring.rightNeighbor e
      · subst p
        rw [rightGood_sf hψ h2 ring C e hb hs]
        exact clearFresh_sf _ .closing _
      · rw [stepV3_other hψ h2 ring C e p hpe hpr]
        exact hc
  · have hsF := boolFalse_sf _ hs
    by_cases hpe : p = e
    · subst p
      rw [leftBad_sf hψ h2 ring C e hb hsF]
      simpa [FreshnessClearV31, startClosing, setControl, raw] using hc
    · rw [badOther_sf hψ h2 ring C e p hb hsF hpe]
      exact hc

private theorem traceStep_sf
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (h : ReachableFromQuarantineV31 hψ h2 ring C) :
    ReachableFromQuarantineV31 hψ h2 ring (stepV3 hψ h2 ring C e) := by
  rcases h with ⟨C0, w, hb, hC⟩
  refine ⟨C0, w ++ [e], hb, ?_⟩
  rw [List.foldl_append, ← hC]
  rfl

theorem openRForwardFreshnessClear_sweep_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hR1 : OpenRForwardFreshnessClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep) :
    OpenRForwardFreshnessClearV31 ring (stepV3 hψ h2 ring C e) := by
  intro o hoD dD
  have heq := postOpenROld_sf hψ h2 ring C e o hb hoD
  have hoC : (C o).ctl.tok = .openR := by
    rw [heq] at hoD
    exact hoD
  have hv := congrArg Fin.val (stepV3_labels_eq_or_held hψ h2 ring C e o)
  have hd : dD.val < ψ - (raw (C o)).label.val := by
    simpa only [hv] using dD.isLt
  let dC : Fin (ψ - (raw (C o)).label.val) := ⟨dD.val, hd⟩
  exact sweepFreshnessClear_mono_sf hψ h2 ring C e _ hb
    (by simpa [dC] using hR1 o hoC dC)

/-- The entire Fresh SWEEP tail closes from the reachable cover. -/
theorem sweepStrongTailPreservationFresh_of_cover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 ring) :
    SweepStrongTailPreservationFreshV31
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hGeom hTrace hFresh hb
  rcases hFresh with ⟨hFacts, _h7, _h8, _h9, _hS, hR1, _hF⟩
  let D := stepV3 hψ h2 ring C e
  have hTraceD : ReachableFromQuarantineV31 hψ h2 ring D := by
    simpa [D] using traceStep_sf hψ h2 ring C e hTrace
  have hGeomD : ElectionGeometryV31 ring D := by
    simpa [D] using
      ((electionGeometryStepV31 (κ := κ) (τ := τ) hψ h2 ring) C e hGeom)
  have hCoverD : PendingOpenRFootprintCoveredV31 ring D :=
    hCov D hTraceD hGeomD
  have hPhaseD : PhaseMainClearV31 ring D := by
    simpa [D] using
      R2CoherenceV31ReachableSweep.sweepStep_reachable_phase
        hψ h2 ring C e hTrace hFacts hb
  have safe : ∀ owner p, PendingOpenROwnerV31 ring D owner →
      SweepOpenRSafeFreshV31 ring D owner p := by
    intro owner p hp
    exact pendingSafeFresh_of_cover_phase ring D hPhaseD hCoverD owner p hp
  have hSD : SeekIncomingSweepOpenROverlapFreshWideV31 ring D := by
    intro pred owner _hSeek hp
    constructor
    · intro _hRoot
      exact ⟨safe owner (ring.rightNeighbor (ring.rightNeighbor pred)) hp,
        fun d => safe owner (R2Coherence.fwd ring (ring.rightNeighbor pred) d.val) hp⟩
    · intro _hNotRoot _hRoot
      exact ⟨safe owner (ring.rightNeighbor pred) hp,
        fun d => safe owner (R2Coherence.fwd ring pred d.val) hp⟩
  have hR1D : OpenRForwardFreshnessClearV31 ring D := by
    simpa [D] using openRForwardFreshnessClear_sweep_step
      hψ h2 ring C e hR1 hb
  have hFD :
      R2CoherenceV31FreshnessClear.SweepPendingOpenRFootprintOwnedV31F ring D :=
    sweepPendingOpenRFootprintOwnedFresh_of_cover_phase
      ring D hPhaseD hCoverD
  exact ⟨hSD, hR1D, hFD⟩

/-- Reduced SWEEP wrapper.  The tail residual is gone.  The only remaining
SWEEP-specific premise is the exact current-openR served-footprint clause,
which is not a pending-owner/F-clause statement. -/
theorem stepPreservesFresh_sweep_closed
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCur : SweepCurrentOpenRServedFootprintFreshV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hCov : PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 ring) :
    StepPreservesV31_sweep_fresh (κ := κ) (τ := τ) hψ h2 ring := by
  exact sweepStep_reachable_fresh_of_residuals hψ h2 ring
    (sweepCurrentOpenRServedSafeFresh_of_footprintFresh
      hψ h2 ring hCur)
    (sweepStrongTailPreservationFresh_of_cover
      hψ h2 ring hCov)

end R2CoherenceV31ReachableSweepFresh
