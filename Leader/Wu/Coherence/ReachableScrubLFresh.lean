import Leader.Wu.Coherence.ReachableFreshSeekScrubLOpenR
import Leader.Wu.Coherence.ReachableCoverForeignPrefix

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableScrubLFresh

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableFreshBranches3
open R2CoherenceV31ReachableCover R2CoherenceV31ReachableCover2
open R2CoherenceV31MainClearTruth
open R2CoherenceV31MainClearTruth.WeakFreshnessLayer
open R2CoherenceV31FreshnessClear
open R2CoherenceV31ReachableSoundParametric
open R2CoherenceV31ReachableSoundFresh
open R2CoherenceV31ReachableAdjacentRoot

variable {n ψ κ τ : Nat}

private theorem scrubCond_sf (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ) (hb : branchAtV3 hψ h2 l r = .scrubL) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧ r.ctl.tok ≠ .commit ∧
      l.ctl.tok ≠ .release ∧ r.ctl.tok = .scrubL := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowScrub_sf (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ) (hb : branchAtV3 hψ h2 l r = .scrubL) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = scrubLStageV3 l r := by
  rcases scrubCond_sf hψ h2 l r hb with ⟨hs,hw,hc,hr,hl⟩
  simp [rowV3, hs, hw, hc, hr, hl]

private theorem scrubGood_sf (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hg : ElectionGeometryV31 ring C) (hf : ReachablePhaseFactsV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL) :
    successorB (C e) (C (ring.rightNeighbor e)) = true ∧
    atRootB (C (ring.rightNeighbor e)) = false ∧
    GroupOwnedClearV31 ring C (ring.rightNeighbor e) := by
  have ht := (scrubCond_sf hψ h2 (C e) (C (ring.rightNeighbor e)) hb).2.2.2.2
  have hh := hf.2.2.2.2.1 (ring.rightNeighbor e) ht
  have hr : atRootB (C (ring.rightNeighbor e)) = false := by
    cases h : atRootB (C (ring.rightNeighbor e)) with
    | false => rfl
    | true =>
      have hz : (raw (C (ring.rightNeighbor e))).label.val = 0 := by
        simpa [atRootB] using h
      exact (hh.2.1 hz).elim
  have hs : successorB (C e) (C (ring.rightNeighbor e)) = true := by
    simpa [ElectionGeometryV31, passiveEdgeOKV3, hr] using hg e
  exact ⟨hs, hr, hh.2.2⟩

private theorem edgeNe_sf (C : FC n ψ κ τ) (ring : DirectedRing n) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    e ≠ ring.rightNeighbor e := by
  intro h
  have he := congrArg (fun p : Fin n => (raw (C p)).label.val) h
  have hv : (raw (C (ring.rightNeighbor e))).label.val =
      (raw (C e)).label.val + 1 := by simpa [successorB] using hs
  omega

private theorem left_sf (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hr : atRootB (C (ring.rightNeighbor e)) = false) :
    stepV3 hψ h2 ring C e e =
      if atRootB (C e) then setControl (clearMain (C e)) .releasing .openR
      else setControl (clearMain (C e)) .releasing .scrubL := by
  have hrow := rowScrub_sf hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hrow, scrubLStageV3, hs, hr]

private theorem right_sf (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hr : atRootB (C (ring.rightNeighbor e)) = false) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      setControl (clearMain (C (ring.rightNeighbor e))) .releasing .none := by
  have hrow := rowScrub_sf hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  have hne := Ne.symm (edgeNe_sf C ring e hs)
  simp [stepV3, protocolV3, PopulationProtocol.step, hrow, scrubLStageV3, hs, hr, hne]

private theorem clearOwned_sf (u : Cell ψ κ τ) (t : TokenV3) :
    MainClearV3 (setControl (clearMain u) .releasing t) ∧
    PhaseOwnedV31 (setControl (clearMain u) .releasing t) := by
  constructor
  · unfold MainClearV3 R2CoherenceBranches.MainClear
    simp [eraseCellV3, setControl, clearMain, R2Coherence.clearMainPhys,
      PPLLExpiringComparisonRepair.clearComparisonCarrier, R2Coherence.raw]
  · simp [PhaseOwnedV31, setControl]


private theorem gp_sf (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label) (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change R2Coherence.fwd ring (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [h i]

private theorem groupStartSucc_sf (ring : DirectedRing n) (C : FC n ψ κ τ)
    (e : Fin n) (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    R2Coherence.groupStart ring (eraseCfgV3 C) e =
      R2Coherence.groupStart ring (eraseCfgV3 C) (ring.rightNeighbor e) := by
  unfold R2Coherence.groupStart
  change R2Coherence.back ring e (raw (C e)).label.val =
    R2Coherence.back ring (ring.rightNeighbor e)
      (raw (C (ring.rightNeighbor e))).label.val
  have hv : (raw (C (ring.rightNeighbor e))).label.val =
      (raw (C e)).label.val + 1 := by simpa [successorB] using hs
  rw [hv]
  exact (R2CoherenceV31ReachableOpenNoHazard.back_rightNeighbor_succ_reach
    ring e (raw (C e)).label.val).symm

private theorem reindexGroup_sf (ring : DirectedRing n) (C : FC n ψ κ τ)
    (a b : Fin n)
    (hs : R2Coherence.groupStart ring (eraseCfgV3 C) a =
      R2Coherence.groupStart ring (eraseCfgV3 C) b)
    (h : GroupOwnedClearV31 ring C b) : GroupOwnedClearV31 ring C a := by
  intro k
  have hk := h k
  unfold R2Coherence.groupPos at hk ⊢
  rw [hs]
  exact hk

private theorem mono_sf (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hr : atRootB (C (ring.rightNeighbor e)) = false)
    (h : MainClearV3 (C p) ∧ PhaseOwnedV31 (C p)) :
    MainClearV3 (stepV3 hψ h2 ring C e p) ∧
      PhaseOwnedV31 (stepV3 hψ h2 ring C e p) := by
  by_cases hp : p = e
  · subst p
    rw [left_sf hψ h2 ring C e hb hs hr]
    cases hroot : atRootB (C e) <;> simp [hroot]
    · exact clearOwned_sf (C e) .scrubL
    · exact clearOwned_sf (C e) .openR
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      rw [right_sf hψ h2 ring C e hb hs hr]
      exact clearOwned_sf _ .none
    · rw [stepV3_other hψ h2 ring C e p hp hpr]
      exact h

private theorem groupTransport_sf (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (hMono : ∀ p, MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) →
      MainClearV3 (D p) ∧ PhaseOwnedV31 (D p))
    (i : Fin n) (h : GroupOwnedClearV31 ring C i) :
    GroupOwnedClearV31 ring D i := by
  intro k
  have hk := h k
  change MainClearV3 (D (R2Coherence.groupPos ring (eraseCfgV3 D) i k.val)) ∧
    PhaseOwnedV31 (D (R2Coherence.groupPos ring (eraseCfgV3 D) i k.val))
  rw [gp_sf ring hLab i k.val]
  exact hMono _ hk

private theorem scrubSource_sf (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hr : atRootB (C (ring.rightNeighbor e)) = false)
    (ht : (stepV3 hψ h2 ring C e p).ctl.tok = .scrubL) :
    p = e ∨ stepV3 hψ h2 ring C e p = C p := by
  by_cases hp : p = e
  · exact Or.inl hp
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      rw [right_sf hψ h2 ring C e hb hs hr] at ht
      simp [setControl] at ht
    · exact Or.inr (stepV3_other hψ h2 ring C e p hp hpr)

private theorem traceStep_sf (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (h : ReachableFromQuarantineV31 hψ h2 ring C) :
    ReachableFromQuarantineV31 hψ h2 ring (stepV3 hψ h2 ring C e) := by
  rcases h with ⟨C0,w,hb,hC⟩
  refine ⟨C0, w ++ [e], hb, ?_⟩
  rw [List.foldl_append, ← hC]
  rfl

private theorem birthReach_sf (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : ReachableFromV31 (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 ring)
      hψ h2 ring C) : ReachableFromQuarantineV31 hψ h2 ring C :=
  (reachableFromV31_birth_iff hψ h2 ring C).1 h


private theorem postCover_sf (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31 (kappa:=κ) (tau:=τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n) (hg : ElectionGeometryV31 ring C)
    (ht : ReachableFromQuarantineV31 hψ h2 ring C) :
    PendingOpenRFootprintCoveredV31 ring (stepV3 hψ h2 ring C e) := by
  have htD := traceStep_sf hψ h2 ring C e ht
  have hgD := (R2CoherenceV31Closure2.electionGeometryStepV31
    (κ:=κ) (τ:=τ) hψ h2 ring) C e hg
  exact hCov _ htD hgD

theorem postPendingSuccessorGroupOwnedClear_scrubL_fresh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) (hg : ElectionGeometryV31 ring C)
    (hf : ReachablePhaseFactsFreshV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL) :
    ∀ owner, PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) owner →
      GroupOwnedClearV31 ring (stepV3 hψ h2 ring C e) (ring.rightNeighbor owner) := by
  let D := stepV3 hψ h2 ring C e
  rcases scrubGood_sf hψ h2 ring C e hg hf.1 hb with ⟨hs,hr,hGR⟩
  have hGE := reindexGroup_sf ring C e (ring.rightNeighbor e)
    (groupStartSucc_sf ring C e hs) hGR
  have hLab : ∀ p, (raw (D p)).label = (raw (C p)).label := by
    intro p; simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  have hMono : ∀ p, MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) →
      MainClearV3 (D p) ∧ PhaseOwnedV31 (D p) := by
    intro p hp
    simpa [D] using mono_sf hψ h2 ring C e p hb hs hr hp
  have hTrans : ∀ i, GroupOwnedClearV31 ring C i → GroupOwnedClearV31 ring D i :=
    fun i hi => groupTransport_sf ring hLab hMono i hi
  intro owner hp
  rcases scrubSource_sf hψ h2 ring C e (ring.rightNeighbor owner)
    hb hs hr hp.1 with hnew | heq
  · simpa [D, hnew] using hTrans e hGE
  · have htC : (C (ring.rightNeighbor owner)).ctl.tok = .scrubL := by
      simpa [D, heq] using hp.1
    exact hTrans _ ((hf.1.2.2.2.2.1 _ htC).2.2)

private theorem safeCovered_sf (ring : DirectedRing n) (D : FC n ψ κ τ)
    (hCov : PendingOpenRFootprintCoveredV31 ring D) (owner p : Fin n)
    (hp : PendingOpenROwnerV31 ring D owner)
    (hG : GroupOwnedClearV31 ring D (ring.rightNeighbor owner)) :
    SweepOpenRSafeFreshV31 ring D owner p := by
  by_cases hf : InOpenRFreshFootprintV31 ring D owner p
  · left
    rcases hCov owner p hp hf with hm | hg
    · exact freshnessClear_of_mainClear _ hm
    · rcases hg with ⟨k,hk⟩
      have hm := (hG k).1
      rw [hk] at hm
      exact freshnessClear_of_mainClear _ hm
  · exact Or.inr hf

theorem scrubLP8Fresh_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31 (kappa:=κ) (tau:=τ) hψ h2 ring) :
    ScrubLP8FreshPreservationV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 ring) hψ h2 ring := by
  intro C e hg ht hf hb _
  have hq := birthReach_sf hψ h2 ring C ht
  have hc := postCover_sf hψ h2 ring hCov C e hg hq
  have hG := postPendingSuccessorGroupOwnedClear_scrubL_fresh hψ h2 ring C e hg hf hb
  intro s o _ hp
  exact ⟨safeCovered_sf ring _ hc o s hp (hG o hp),
    safeCovered_sf ring _ hc o (ring.rightNeighbor s) hp (hG o hp)⟩

theorem scrubLP9Fresh_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31 (kappa:=κ) (tau:=τ) hψ h2 ring) :
    ScrubLP9FreshPreservationV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 ring) hψ h2 ring := by
  intro C e hg ht hf hb _ _
  have hq := birthReach_sf hψ h2 ring C ht
  have hc := postCover_sf hψ h2 ring hCov C e hg hq
  have hG := postPendingSuccessorGroupOwnedClear_scrubL_fresh hψ h2 ring C e hg hf hb
  intro s o _ hp
  exact ⟨safeCovered_sf ring _ hc o (ring.rightNeighbor s) hp (hG o hp),
    fun d => safeCovered_sf ring _ hc o (R2Coherence.fwd ring s d.val) hp (hG o hp)⟩


theorem scrubLSFresh_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31 (kappa:=κ) (tau:=τ) hψ h2 ring) :
    ScrubLSFreshPreservationV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 ring) hψ h2 ring := by
  intro C e hg ht hf hb _
  have hq := birthReach_sf hψ h2 ring C ht
  have hc := postCover_sf hψ h2 ring hCov C e hg hq
  have hG := postPendingSuccessorGroupOwnedClear_scrubL_fresh hψ h2 ring C e hg hf hb
  intro pred o _ hp
  constructor
  · intro _
    exact ⟨safeCovered_sf ring _ hc o (ring.rightNeighbor (ring.rightNeighbor pred)) hp (hG o hp),
      fun d => safeCovered_sf ring _ hc o
        (R2Coherence.fwd ring (ring.rightNeighbor pred) d.val) hp (hG o hp)⟩
  · intro _ _
    exact ⟨safeCovered_sf ring _ hc o (ring.rightNeighbor pred) hp (hG o hp),
      fun d => safeCovered_sf ring _ hc o (R2Coherence.fwd ring pred d.val) hp (hG o hp)⟩

theorem scrubLR2Fresh_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31 (kappa:=κ) (tau:=τ) hψ h2 ring) :
    ScrubLStrongR2FreshPreservationV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 ring) hψ h2 ring := by
  intro C e hg ht hf hb _ _
  have hq := birthReach_sf hψ h2 ring C ht
  have hc := postCover_sf hψ h2 ring hCov C e hg hq
  have hG := postPendingSuccessorGroupOwnedClear_scrubL_fresh hψ h2 ring C e hg hf hb
  intro s o p _ hp _ hfoot
  rcases safeCovered_sf ring _ hc o p hp (hG o hp) with hz | hout
  · exact Or.inr hz
  · exact (hout hfoot).elim

end R2CoherenceV31ReachableScrubLFresh
