import Leader.Wu.Coherence.ReachableOwnershipPayload

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableFourBranches

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31BirthQuarantine
open R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts
open R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus
open R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3
open R2CoherenceV31ReachablePlus4

variable {n ψ κ τ : Nat}

private theorem branch_commit_conditions_four
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .commit) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧ r.ctl.tok = .commit := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowV3_commit_eq_four
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .commit) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = commitStageV3 l r := by
  rcases branch_commit_conditions_four hψ h2 l r hb with
    ⟨hSeek, hSweep, hCommit⟩
  simp [rowV3, hSeek, hSweep, hCommit]

private theorem commitStageV3_right_four
    (l r : Cell ψ κ τ) :
    (commitStageV3 l r).2 = setControl (clearMain r) .sealed .none := by
  simp [commitStageV3]



private theorem commit_step_left_four
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    stepV3 hψ h2 ring C e e =
      (commitStageV3 (C e) (C (ring.rightNeighbor e))).1 := by
  have hrow := rowV3_commit_eq_four hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hrow]

private theorem commit_step_right_four
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    (hne : ring.rightNeighbor e ≠ e) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      setControl (clearMain (C (ring.rightNeighbor e))) .sealed .none := by
  have hrow := rowV3_commit_eq_four hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, hne, commitStageV3_right_four]

private theorem clear_control_mainClear_four
    (u : Cell ψ κ τ) (m : R2Coherence.Mark) (t : TokenV3) :
    MainClearV3 (setControl (clearMain u) m t) := by
  unfold MainClearV3 R2CoherenceBranches.MainClear
  simp [eraseCellV3, setControl, clearMain,
    R2Coherence.clearMainPhys,
    PPLLExpiringComparisonRepair.clearComparisonCarrier,
    R2Coherence.raw]



private theorem clear_sealed_owned_four (u : Cell ψ κ τ) :
    MainClearV3 (setControl (clearMain u) .sealed .none) ∧
      PhaseOwnedV31 (setControl (clearMain u) .sealed .none) := by
  exact ⟨clear_control_mainClear_four u .sealed .none,
    by simp [PhaseOwnedV31, setControl]⟩

private theorem clear_commit_owned_four (u : Cell ψ κ τ) :
    MainClearV3 (setControl (clearMain u) .closing .commit) ∧
      PhaseOwnedV31 (setControl (clearMain u) .closing .commit) := by
  exact ⟨clear_control_mainClear_four u .closing .commit,
    by simp [PhaseOwnedV31, setControl]⟩

private theorem commit_ownedPair_mono_four
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    (hOld : MainClearV3 (C p) ∧ PhaseOwnedV31 (C p)) :
    MainClearV3 (stepV3 hψ h2 ring C e p) ∧
      PhaseOwnedV31 (stepV3 hψ h2 ring C e p) := by
  by_cases hpe : p = e
  · subst p
    rw [commit_step_left_four hψ h2 ring C e hb]
    unfold commitStageV3
    dsimp only
    split
    · exact hOld
    · split
      · exact clear_sealed_owned_four (C e)
      · exact clear_commit_owned_four (C e)
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      have hrne : ring.rightNeighbor e ≠ e := hpe
      rw [commit_step_right_four hψ h2 ring C e hb hrne]
      exact clear_sealed_owned_four (C (ring.rightNeighbor e))
    · rw [stepV3_other hψ h2 ring C e p hpe hpr]
      exact hOld

private theorem groupPos_eq_of_labels_four
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change
    R2Coherence.fwd ring
        (R2Coherence.back ring i (raw (D i)).label.val) k =
      R2Coherence.fwd ring
        (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [hLab i]

private theorem sweptPrefix_transport_four
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label)
    (hMono : ∀ p : Fin n,
      MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) →
        MainClearV3 (D p) ∧ PhaseOwnedV31 (D p))
    (i : Fin n) (hOld : SweptPrefixOwnedClearV31 ring C i) :
    SweptPrefixOwnedClearV31 ring D i := by
  unfold SweptPrefixOwnedClearV31 at hOld ⊢
  intro kD
  have hVal := congrArg (fun x : Fin ψ => x.val) (hLab i)
  have hkC : kD.val < (raw (C i)).label.val := by
    simpa only [hVal] using kD.isLt
  let kC : Fin (raw (C i)).label.val := ⟨kD.val, hkC⟩
  have hAt := hOld kC
  have hGP := groupPos_eq_of_labels_four ring hLab i kD.val
  change MainClearV3
      (D (R2Coherence.groupPos ring (eraseCfgV3 D) i kD.val)) ∧
    PhaseOwnedV31
      (D (R2Coherence.groupPos ring (eraseCfgV3 D) i kD.val))
  rw [hGP]
  apply hMono
  simpa [kC] using hAt


theorem commitStep_reachable_P1
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hPlus : ReachablePhaseFactsPlus4V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    ∀ i : Fin n,
      (stepV3 hψ h2 ring C e i).ctl.tok = .sweep →
        SweptPrefixOwnedClearV31 ring (stepV3 hψ h2 ring C e) i := by
  have hc := branch_commit_conditions_four hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hLab : ∀ p : Fin n,
      (raw (stepV3 hψ h2 ring C e p)).label = (raw (C p)).label :=
    stepV3_labels_eq_or_held hψ h2 ring C e
  have hMono : ∀ p : Fin n,
      MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) →
        MainClearV3 (stepV3 hψ h2 ring C e p) ∧
          PhaseOwnedV31 (stepV3 hψ h2 ring C e p) := by
    intro p hp
    exact commit_ownedPair_mono_four hψ h2 ring C e p hb hp
  have hP1 := hPlus.1.1.1.1.1
  intro i hSweepD
  have hie : i ≠ e := by
    intro hi
    subst i
    have hx := hSweepD
    rw [commit_step_left_four hψ h2 ring C e hb] at hx
    by_cases hr : atRootB (C (ring.rightNeighbor e)) = true
    · have hx' : (C e).ctl.tok = .sweep := by
        simpa [commitStageV3, hr] using hx
      exact hc.2.1 hx'
    · by_cases hl : atRootB (C e) = true
      · have hx' : (TokenV3.none : TokenV3) = .sweep := by
          simpa [commitStageV3, hr, hl, setControl] using hx
        simp at hx'
      · have hx' : (TokenV3.commit : TokenV3) = .sweep := by
          simpa [commitStageV3, hr, hl, setControl] using hx
        simp at hx'
  have hir : i ≠ ring.rightNeighbor e := by
    intro hi
    subst i
    by_cases hre : ring.rightNeighbor e = e
    · exact hie hre
    · have hx := hSweepD
      rw [commit_step_right_four hψ h2 ring C e hb hre] at hx
      simp [setControl] at hx
  have hSweepC : (C i).ctl.tok = .sweep := by
    have hx := hSweepD
    rw [stepV3_other hψ h2 ring C e i hie hir] at hx
    exact hx
  exact sweptPrefix_transport_four ring hLab hMono i (hP1 i hSweepC)


/-- First unresolved clause in the requested branch order: commit P2.

This is deliberately a proof obligation, not an added payload clause.  On the
interior `commitStageV3` arm the old `.commit` owner is the responder, while
the post `.commit` owner is the initiator.  The census says no extra
invariant is needed: ElectionGeometry gives the successor edge, hence equal
group starts; labels are globally framed and `commit_ownedPair_mono_four`
transports every owned-clear cell.  The remaining work is that owner-reindex
algebra, so the file stops here rather than skipping to sealed/openHazard/mixed. -/
def CommitP2OwnerReindexV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit →
      let D := stepV3 hψ h2 ring C e
      ∀ i : Fin n,
        (D i).ctl.tok = .commit →
          GroupOwnedClearV31 ring D i


private theorem groupStart_successor_four
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    R2Coherence.groupStart ring (eraseCfgV3 C) (ring.rightNeighbor e) =
      R2Coherence.groupStart ring (eraseCfgV3 C) e := by
  unfold R2Coherence.groupStart
  change
    R2Coherence.back ring (ring.rightNeighbor e)
        (raw (C (ring.rightNeighbor e))).label.val =
      R2Coherence.back ring e (raw (C e)).label.val
  have hv :
      (raw (C (ring.rightNeighbor e))).label.val =
        (raw (C e)).label.val + 1 := by
    simpa [successorB] using hs
  rw [hv]
  exact
    R2CoherenceV31ReachableOpenNoHazard.back_rightNeighbor_succ_reach
      ring e (raw (C e)).label.val



private theorem groupOwned_transport_four
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label)
    (hMono : ∀ p : Fin n,
      MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) →
        MainClearV3 (D p) ∧ PhaseOwnedV31 (D p))
    (i : Fin n) (hOld : GroupOwnedClearV31 ring C i) :
    GroupOwnedClearV31 ring D i := by
  unfold GroupOwnedClearV31 at hOld ⊢
  intro k
  have h := hOld k
  change MainClearV3
      (C (R2Coherence.groupPos ring (eraseCfgV3 C) i k.val)) ∧
    PhaseOwnedV31
      (C (R2Coherence.groupPos ring (eraseCfgV3 C) i k.val)) at h
  change MainClearV3
      (D (R2Coherence.groupPos ring (eraseCfgV3 D) i k.val)) ∧
    PhaseOwnedV31
      (D (R2Coherence.groupPos ring (eraseCfgV3 D) i k.val))
  rw [groupPos_eq_of_labels_four ring hLab i k.val]
  exact hMono _ h



private theorem groupOwned_reindex_four
    (ring : DirectedRing n) (C : FC n ψ κ τ) (a b : Fin n)
    (hStart :
      R2Coherence.groupStart ring (eraseCfgV3 C) a =
        R2Coherence.groupStart ring (eraseCfgV3 C) b)
    (hOld : GroupOwnedClearV31 ring C b) :
    GroupOwnedClearV31 ring C a := by
  unfold GroupOwnedClearV31 at hOld ⊢
  intro k
  have h := hOld k
  change MainClearV3
      (C (R2Coherence.groupPos ring (eraseCfgV3 C) b k.val)) ∧
    PhaseOwnedV31
      (C (R2Coherence.groupPos ring (eraseCfgV3 C) b k.val)) at h
  change MainClearV3
      (C (R2Coherence.groupPos ring (eraseCfgV3 C) a k.val)) ∧
    PhaseOwnedV31
      (C (R2Coherence.groupPos ring (eraseCfgV3 C) a k.val))
  have hp :
      R2Coherence.groupPos ring (eraseCfgV3 C) a k.val =
        R2Coherence.groupPos ring (eraseCfgV3 C) b k.val := by
    unfold R2Coherence.groupPos
    rw [hStart]
  rw [hp]
  exact h



theorem commitP2OwnerReindexV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    CommitP2OwnerReindexV31 (κ := κ) (τ := τ) hψ h2 ring := by
  unfold CommitP2OwnerReindexV31
  intro C e hTrace hPlus hb
  simp only
  have hFacts : ReachablePhaseFactsV31 ring C := hPlus.1.1.1.1
  have hP2 := hFacts.2.1
  have hGeom : ElectionGeometryV31 ring C :=
    R2CoherenceV31ReachableSweep.electionGeometry_of_quarantineTrace
      hψ h2 ring C hTrace
  have hc := branch_commit_conditions_four hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hLab : ∀ p : Fin n,
      (raw (stepV3 hψ h2 ring C e p)).label = (raw (C p)).label :=
    stepV3_labels_eq_or_held hψ h2 ring C e
  have hMono : ∀ p : Fin n,
      MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) →
        MainClearV3 (stepV3 hψ h2 ring C e p) ∧
          PhaseOwnedV31 (stepV3 hψ h2 ring C e p) := by
    intro p hp
    exact commit_ownedPair_mono_four hψ h2 ring C e p hb hp
  intro i hCommitD
  by_cases hie : i = e
  · subst i
    by_cases hr0 : atRootB (C (ring.rightNeighbor e)) = true
    · have hCommitC : (C e).ctl.tok = .commit := by
        have hx := hCommitD
        rw [commit_step_left_four hψ h2 ring C e hb] at hx
        simpa [commitStageV3, hr0] using hx
      exact groupOwned_transport_four ring hLab hMono e
        (hP2 e hCommitC)
    · by_cases hl0 : atRootB (C e) = true
      · have hx := hCommitD
        rw [commit_step_left_four hψ h2 ring C e hb] at hx
        simp [commitStageV3, hr0, hl0, setControl] at hx
      · have hEdge := hGeom e
        have hs :
            successorB (C e) (C (ring.rightNeighbor e)) = true := by
          unfold passiveEdgeOKV3 at hEdge
          simp [hr0] at hEdge
          exact hEdge
        have hOldR :
            (C (ring.rightNeighbor e)).ctl.tok = .commit := hc.2.2
        have hOldGroupR := hP2 (ring.rightNeighbor e) hOldR
        have hStart := groupStart_successor_four ring C e hs
        have hOldGroupE := groupOwned_reindex_four ring C e
          (ring.rightNeighbor e) hStart.symm hOldGroupR
        exact groupOwned_transport_four ring hLab hMono e hOldGroupE
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      have hrne : ring.rightNeighbor e ≠ e := hie
      have hx := hCommitD
      rw [commit_step_right_four hψ h2 ring C e hb hrne] at hx
      simp [setControl] at hx
    · have hCommitC : (C i).ctl.tok = .commit := by
        have hx := hCommitD
        rw [stepV3_other hψ h2 ring C e i hie hir] at hx
        exact hx
      exact groupOwned_transport_four ring hLab hMono i
        (hP2 i hCommitC)

end R2CoherenceV31ReachableFourBranches
