import Leader.Wu.Coherence.FootprintCoverForeignProvenance
import Leader.Wu.Coherence.FreshnessClear
import Leader.Wu.Coherence.ReachableOpenNoHazardServed

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31FootprintCover3

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure2
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachablePlus2 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableAdjacentRoot R2CoherenceV31ReachableCover
open R2CoherenceV31ReachableCover2 R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31ReachableOpenNoHazard5
open R2CoherenceV31ReachableReleaseOwner2
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31OpenNoHazard
open R2CoherenceV31FootprintCover2R
open R2CoherenceV31MainClearTruth
open R2CoherenceV31MainClearTruth.WeakFreshnessLayer
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31ReachableSoundFresh

variable {n ψ κ τ : Nat}

/-- Exact strong RELEASE creation seam after deleting the false anchoring claim. -/
def ReleaseNewPendingForeignFootprintMainClearV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e owner p : Fin n),
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release →
    let D := stepV3 hψ h2 ring C e
    PendingOpenROwnerV31 ring D owner →
    ¬ PendingOpenROwnerV31 ring C owner →
    InOpenRFreshFootprintV31 ring D owner p →
    ¬ InGroupOwnedFootprintV31 ring D (ring.rightNeighbor owner) p →
      MainClearV3 (D p)

/-- Q6's replacement route at the exact strength required by the old cover. -/
theorem releaseNewPendingForeign_of_psi2_primitives
    (ring : DirectedRing n) (D : FC n 2 κ τ)
    (hAdj : AdjacentRootPredecessorMainClearPsi2V31 ring D)
    (hDich : Psi2PendingFootprintDichotomyV31 ring D)
    (owner p : Fin n) (hp : PendingOpenROwnerV31 ring D owner)
    (hf : InOpenRFreshFootprintV31 ring D owner p)
    (hout : ¬ InGroupOwnedFootprintV31 ring D (ring.rightNeighbor owner) p) :
    MainClearV3 (D p) := by
  rcases hDich owner p hp hf with hg | ⟨pred, hpo, hr, hEq⟩
  · exact (hout hg).elim
  · rw [hEq]
    exact hAdj pred hr (by rw [hpo]; exact hp.2.2)

/-- The compiled weak adjacent-root invariant proves only the Fresh version. -/
theorem releaseNewPendingForeignFresh_of_psi2_primitives
    (ring : DirectedRing n) (D : FC n 2 κ τ)
    (hAdj : AdjacentRootPredecessorFreshnessClearPsi2V31 ring D)
    (hDich : Psi2PendingFootprintDichotomyV31 ring D)
    (owner p : Fin n) (hp : PendingOpenROwnerV31 ring D owner)
    (hf : InOpenRFreshFootprintV31 ring D owner p)
    (hout : ¬ InGroupOwnedFootprintV31 ring D (ring.rightNeighbor owner) p) :
    FreshnessClearV31 (D p) := by
  rcases hDich owner p hp hf with hg | ⟨pred, hpo, hr, hEq⟩
  · exact (hout hg).elim
  · rw [hEq]
    exact hAdj pred hr (by rw [hpo]; exact hp.2.2)

private theorem rowReleaseMainClear3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .release) :
    (MainClearV3 l → MainClearV3 (rowV3 hψ (by decide : 0 < 2) h2 l r).1) ∧
    (MainClearV3 r → MainClearV3 (rowV3 hψ (by decide : 0 < 2) h2 l r).2) :=
  rowMainClear2 hψ h2 l r hb (by decide)

private theorem releaseMainClear3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release) :
    CoverMainClearStepV31 C (stepV3 hψ h2 ring C e) := by
  have h := rowReleaseMainClear3 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  intro p hm
  by_cases he : p = e
  · subst p
    simpa [stepV3, protocolV3, PopulationProtocol.step] using h.1 hm
  · by_cases hr : p = ring.rightNeighbor e
    · subst p
      simpa [stepV3, protocolV3, PopulationProtocol.step, he] using h.2 hm
    · rw [stepV3_other hψ h2 ring C e p he hr]
      exact hm

theorem foreignProvenance_release_step_of_newPendingForeign
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hRel : ReleaseNewPendingForeignFootprintMainClearV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hg : ElectionGeometryV31 ring C)
    (ht : ReachableFromQuarantineV31 hψ h2 ring C)
    (hp : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hP : PendingOwnerForeignFootprintMainClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release) :
    PendingOwnerForeignFootprintMainClearV31 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hNew : CoverNewPendingStepV31 ring C D := by
    intro owner p hD hC hF
    by_cases hG : InGroupOwnedFootprintV31 ring D (ring.rightNeighbor owner) p
    · exact Or.inr hG
    · exact Or.inl (by
        simpa [D] using hRel C e owner p hg ht hp hb hD hC hF hG)
  have hCov := pendingCover_step_of_old_new ring
    (stepV3_labels_eq_or_held hψ h2 ring C e)
    (releaseMainClear3 hψ h2 ring C e hb) hNew
    (pendingFootprintCovered_of_foreignProvenance ring C hP)
  exact foreignProvenance_of_pendingFootprintCovered ring D hCov

private theorem pendingBackONH3
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

/-- OPEN-NO-HAZARD arm from the repository's exact served-MainClear leaf. -/
theorem foreignProvenance_openNoHazard_step_of_servedMainClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hMain : OpenNoHazardServedMainClearPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hg : ElectionGeometryV31 ring C)
    (ht : ReachableFromQuarantineV31 hψ h2 ring C)
    (hp : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hP : PendingOwnerForeignFootprintMainClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    PendingOwnerForeignFootprintMainClearV31 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hF : OpenNoHazardFrameV31 C D := by
    simpa [D] using openNoHazard_step_frame hψ h2 ring C e hb
  have hMC : CoverMainClearStepV31 C D := by
    intro p hm
    by_cases he : p = e
    · exact (by simpa [D] using hMain C e p hg ht hp hb (Or.inl he) hm)
    · by_cases hr : p = ring.rightNeighbor e
      · exact (by simpa [D] using hMain C e p hg ht hp hb (Or.inr hr) hm)
      · rw [show D p = C p by
          simpa [D] using stepV3_other hψ h2 ring C e p he hr]
        exact hm
  have hNew : CoverNewPendingStepV31 ring C D := by
    intro owner _ hD hC _
    exact (hC (pendingBackONH3 ring hF owner hD)).elim
  have hCov := pendingCover_step_of_old_new ring
    (fun p => (hF p).1) hMC hNew
    (pendingFootprintCovered_of_foreignProvenance ring C hP)
  exact foreignProvenance_of_pendingFootprintCovered ring D hCov

/-- Exactly the three cover-specific residuals after this file. -/
def FootprintCover3ResidualsV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ScrubLContinuationForeignPrefixMainClearV31
      (κ := κ) (τ := τ) hψ h2 ring ∧
  ReleaseNewPendingForeignFootprintMainClearV31
      (κ := κ) (τ := τ) hψ h2 ring ∧
  OpenNoHazardServedMainClearPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring

theorem foreignProvenance_step_of_cover3Residuals
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hR : FootprintCover3ResidualsV31 (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hg : ElectionGeometryV31 ring C)
    (ht : ReachableFromQuarantineV31 hψ h2 ring C)
    (hp : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hP : PendingOwnerForeignFootprintMainClearV31 ring C) :
    PendingOwnerForeignFootprintMainClearV31 ring (stepV3 hψ h2 ring C e) := by
  cases hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) with
  | seek =>
      exact foreignProvenance_seek_step
        hψ h2 ring C e hP hb
  | sweep =>
      exact foreignProvenance_sweep_step
        hψ h2 ring C e hP hb
  | commit =>
      exact foreignProvenance_commit_step
        hψ h2 ring C e hP hb
  | release =>
      exact foreignProvenance_release_step_of_newPendingForeign
        hψ h2 ring hR.2.1 C e hg ht hp hP hb
  | scrubL =>
      exact foreignProvenance_scrubL_step_of_foreignPrefix
        hψ h2 ring hR.1 C e hg ht hp hP hb
  | openR =>
      exact foreignProvenance_openR_step
        hψ h2 ring C e hP hb
  | sealed =>
      exact foreignProvenance_sealed_step
        hψ h2 ring C e hP hb
  | openHazard =>
      exact foreignProvenance_openHazard_step
        hψ h2 ring C e hP hb
  | openNoHazard =>
      exact foreignProvenance_openNoHazard_step_of_servedMainClear
        hψ h2 ring hR.2.2 C e hg ht hp hP hb
  | mixed =>
      exact foreignProvenance_mixed_step
        hψ h2 ring C e hP hb

/-- Upstream payload availability, separated from the three cover debts. -/
def Cover3PayloadReachableV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : FC n ψ κ τ, ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C

private theorem traceStep3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (h : ReachableFromQuarantineV31 hψ h2 ring C) :
    ReachableFromQuarantineV31 hψ h2 ring (stepV3 hψ h2 ring C e) := by
  rcases h with ⟨C0, w, hb, hC⟩
  refine ⟨C0, w ++ [e], hb, ?_⟩
  rw [List.foldl_append, ← hC]
  rfl

theorem pendingFootprintCoveredReachable_of_cover3Residuals
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hPayload : Cover3PayloadReachableV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hR : FootprintCover3ResidualsV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 ring := by
  intro C hTrace _
  apply pendingFootprintCovered_of_foreignProvenance ring C
  rcases hTrace with ⟨C0, w, hBirth, hC⟩
  have h0 := pendingOwnerForeignFootprintMainClear_entrance
    hψ h2 ring C0 hBirth
  have carry : ∀ (v : List (Fin n)) (D : FC n ψ κ τ),
      ReachableFromQuarantineV31 hψ h2 ring D →
      ElectionGeometryV31 ring D →
      PendingOwnerForeignFootprintMainClearV31 ring D →
      PendingOwnerForeignFootprintMainClearV31 ring
        (v.foldl (stepV3 hψ h2 ring) D) := by
    intro v
    induction v with
    | nil => intro D _ _ hP; simpa using hP
    | cons e v ih =>
      intro D ht hg hP
      simp only [List.foldl_cons]
      have h1 := foreignProvenance_step_of_cover3Residuals
        hψ h2 ring hR D e hg ht (hPayload D ht) hP
      exact ih _ (traceStep3 hψ h2 ring D e ht)
        ((electionGeometryStepV31 (κ := κ) (τ := τ) hψ h2 ring) D e hg) h1
  rw [hC]
  exact carry w C0 ⟨C0, [], hBirth, rfl⟩ hBirth.2 h0


end R2CoherenceV31FootprintCover3
