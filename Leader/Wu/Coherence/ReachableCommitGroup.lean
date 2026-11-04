import Leader.Wu.Coherence.ReachableCommitOwner
import Leader.Wu.Coherence.ReachableStrongOwnership


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31ReachableThreeBranches


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard4


variable {n ψ κ τ : Nat}


private theorem branch_commit_conditions_three
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .commit) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧ r.ctl.tok = .commit := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind


private theorem rowV3_commit_eq_three
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .commit) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = commitStageV3 l r := by
  rcases branch_commit_conditions_three hψ h2 l r hb with ⟨_, hs, hc⟩
  simp [rowV3, hs, hc]


private theorem commitStageV3_right_three (l r : Cell ψ κ τ) :
    (commitStageV3 l r).2 = setControl (clearMain r) .sealed .none := by
  simp [commitStageV3]


private theorem commit_step_left_three
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    stepV3 hψ h2 ring C e e =
      (commitStageV3 (C e) (C (ring.rightNeighbor e))).1 := by
  have hr := rowV3_commit_eq_three hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hr]


private theorem commit_step_right_three
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    (hne : ring.rightNeighbor e ≠ e) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      setControl (clearMain (C (ring.rightNeighbor e))) .sealed .none := by
  have hr := rowV3_commit_eq_three hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hr, hne, commitStageV3_right_three]


private theorem clear_control_mainClear_three
    (u : Cell ψ κ τ) (m : R2Coherence.Mark) (t : TokenV3) :
    MainClearV3 (setControl (clearMain u) m t) := by
  unfold MainClearV3 R2CoherenceBranches.MainClear
  simp [eraseCellV3, setControl, clearMain, R2Coherence.clearMainPhys,
    PPLLExpiringComparisonRepair.clearComparisonCarrier, R2Coherence.raw]


private theorem clear_sealed_owned_three (u : Cell ψ κ τ) :
    MainClearV3 (setControl (clearMain u) .sealed .none) ∧
      PhaseOwnedV31 (setControl (clearMain u) .sealed .none) := by
  exact ⟨clear_control_mainClear_three u .sealed .none,
    by simp [PhaseOwnedV31, setControl]⟩


private theorem clear_commit_owned_three (u : Cell ψ κ τ) :
    MainClearV3 (setControl (clearMain u) .closing .commit) ∧
      PhaseOwnedV31 (setControl (clearMain u) .closing .commit) := by
  exact ⟨clear_control_mainClear_three u .closing .commit,
    by simp [PhaseOwnedV31, setControl]⟩


private theorem commit_ownedPair_mono_three
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    (hOld : MainClearV3 (C p) ∧ PhaseOwnedV31 (C p)) :
    MainClearV3 (stepV3 hψ h2 ring C e p) ∧
      PhaseOwnedV31 (stepV3 hψ h2 ring C e p) := by
  by_cases hpe : p = e
  · subst p
    rw [commit_step_left_three hψ h2 ring C e hb]
    unfold commitStageV3
    dsimp only
    split
    · exact hOld
    · split
      · exact clear_sealed_owned_three (C e)
      · exact clear_commit_owned_three (C e)
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      rw [commit_step_right_three hψ h2 ring C e hb hpe]
      exact clear_sealed_owned_three (C (ring.rightNeighbor e))
    · rw [stepV3_other hψ h2 ring C e p hpe hpr]
      exact hOld


private theorem groupPos_eq_of_labels_three
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [hLab i]


private theorem groupOwned_transport_three
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
  rw [groupPos_eq_of_labels_three ring hLab i k.val]
  exact hMono _ h



private theorem groupStart_successor_three
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    R2Coherence.groupStart ring (eraseCfgV3 C) (ring.rightNeighbor e) =
      R2Coherence.groupStart ring (eraseCfgV3 C) e := by
  unfold R2Coherence.groupStart
  change R2Coherence.back ring (ring.rightNeighbor e)
      (raw (C (ring.rightNeighbor e))).label.val =
    R2Coherence.back ring e (raw (C e)).label.val
  have hv : (raw (C (ring.rightNeighbor e))).label.val =
      (raw (C e)).label.val + 1 := by
    simpa [successorB] using hs
  rw [hv]
  exact R2CoherenceV31ReachableOpenNoHazard.back_rightNeighbor_succ_reach
    ring e (raw (C e)).label.val


private theorem groupOwned_reindex_three
    (ring : DirectedRing n) (C : FC n ψ κ τ) (a b : Fin n)
    (hStart : R2Coherence.groupStart ring (eraseCfgV3 C) a =
      R2Coherence.groupStart ring (eraseCfgV3 C) b)
    (hOld : GroupOwnedClearV31 ring C b) :
    GroupOwnedClearV31 ring C a := by
  unfold GroupOwnedClearV31 at hOld ⊢
  intro k
  have h := hOld k
  have hp : R2Coherence.groupPos ring (eraseCfgV3 C) a k.val =
      R2Coherence.groupPos ring (eraseCfgV3 C) b k.val := by
    unfold R2Coherence.groupPos
    rw [hStart]
  rw [hp]
  exact h


private theorem commit_step_eq_of_post_token_three
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    {t : TokenV3} (hn : t ≠ .none) (hc : t ≠ .commit)
    (ht : (stepV3 hψ h2 ring C e i).ctl.tok = t) :
    stepV3 hψ h2 ring C e i = C i := by
  by_cases hie : i = e
  · subst i
    rw [commit_step_left_three hψ h2 ring C e hb] at ht ⊢
    by_cases hr0 : atRootB (C (ring.rightNeighbor e)) = true
    · simp [commitStageV3, hr0]
    · by_cases hl0 : atRootB (C e) = true
      · exfalso
        apply hn
        simpa [commitStageV3, hr0, hl0, setControl] using ht.symm
      · exfalso
        apply hc
        simpa [commitStageV3, hr0, hl0, setControl] using ht.symm
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      rw [commit_step_right_three hψ h2 ring C e hb hie] at ht
      exfalso
      apply hn
      simpa [setControl] using ht.symm
    · exact stepV3_other hψ h2 ring C e i hie hir


/-- `commitStageV3` (Leader/Wu/Coherence/Controller.lean:140-147) only clears the
served pair, seals the responder, and on the interior arm propagates commit
left.  P1 and P2 are imported from ReachableFourBranches; this theorem closes
the next three old reachable clauses. -/
theorem commitStep_reachable_P3_P5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    (∀ i : Fin n,
      (stepV3 hψ h2 ring C e i).ctl.mark = .sealed →
        GroupOwnedClearV31 ring (stepV3 hψ h2 ring C e) i) ∧
    (∀ i : Fin n,
      (stepV3 hψ h2 ring C e i).ctl.tok = .release →
        (stepV3 hψ h2 ring C e i).ctl.mark = .releasing ∧
          GroupOwnedClearV31 ring (stepV3 hψ h2 ring C e) i) ∧
    (∀ i : Fin n,
      (stepV3 hψ h2 ring C e i).ctl.tok = .scrubL →
        (stepV3 hψ h2 ring C e i).ctl.mark = .releasing ∧
          (raw (stepV3 hψ h2 ring C e i)).label.val ≠ 0 ∧
          GroupOwnedClearV31 ring (stepV3 hψ h2 ring C e) i) := by
  have hFacts : ReachablePhaseFactsV31 ring C := hPlus.1.1.1.1
  have hP2 := hFacts.2.1
  have hP3 := hFacts.2.2.1
  have hP4 := hFacts.2.2.2.1
  have hP5 := hFacts.2.2.2.2.1
  have hc := branch_commit_conditions_three hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hGeom : ElectionGeometryV31 ring C :=
    R2CoherenceV31ReachableSweep.electionGeometry_of_quarantineTrace
      hψ h2 ring C hTrace
  have hLab : ∀ p : Fin n,
      (raw (stepV3 hψ h2 ring C e p)).label = (raw (C p)).label :=
    stepV3_labels_eq_or_held hψ h2 ring C e
  have hMono : ∀ p : Fin n,
      MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) →
        MainClearV3 (stepV3 hψ h2 ring C e p) ∧
          PhaseOwnedV31 (stepV3 hψ h2 ring C e p) := by
    intro p hp
    exact commit_ownedPair_mono_three hψ h2 ring C e p hb hp
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    by_cases hie : i = e
    · subst i
      by_cases hr0 : atRootB (C (ring.rightNeighbor e)) = true
      · have hiC : (C e).ctl.mark = .sealed := by
          have hx := hi
          rw [commit_step_left_three hψ h2 ring C e hb] at hx
          simpa [commitStageV3, hr0] using hx
        exact groupOwned_transport_three ring hLab hMono e (hP3 e hiC)
      · by_cases hl0 : atRootB (C e) = true
        · have hEdge := hGeom e
          have hs : successorB (C e) (C (ring.rightNeighbor e)) = true := by
            unfold passiveEdgeOKV3 at hEdge
            simp [hr0] at hEdge
            exact hEdge
          have hStart := groupStart_successor_three ring C e hs
          have hOldE := groupOwned_reindex_three ring C e
            (ring.rightNeighbor e) hStart.symm
            (hP2 (ring.rightNeighbor e) hc.2.2)
          exact groupOwned_transport_three ring hLab hMono e hOldE
        · have hx := hi
          rw [commit_step_left_three hψ h2 ring C e hb] at hx
          simp [commitStageV3, hr0, hl0, setControl] at hx
    · by_cases hir : i = ring.rightNeighbor e
      · subst i
        exact groupOwned_transport_three ring hLab hMono
          (ring.rightNeighbor e) (hP2 (ring.rightNeighbor e) hc.2.2)
      · have hiC := hi
        rw [stepV3_other hψ h2 ring C e i hie hir] at hiC
        exact groupOwned_transport_three ring hLab hMono i (hP3 i hiC)
  · intro i hi
    have hEq := commit_step_eq_of_post_token_three hψ h2 ring C e i hb
      (t := .release) (by decide) (by decide) hi
    have hiC := hi
    rw [hEq] at hiC
    rcases hP4 i hiC with ⟨hm, hg⟩
    constructor
    · rw [hEq]
      exact hm
    · exact groupOwned_transport_three ring hLab hMono i hg
  · intro i hi
    have hEq := commit_step_eq_of_post_token_three hψ h2 ring C e i hb
      (t := .scrubL) (by decide) (by decide) hi
    have hiC := hi
    rw [hEq] at hiC
    rcases hP5 i hiC with ⟨hm, hz, hg⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hEq]
      exact hm
    · rw [hEq]
      exact hz
    · exact groupOwned_transport_three ring hLab hMono i hg


/-- STOP: P6 is the first clause not closed in this drop.


A post `.openR` owner itself is unchanged (use
`commit_step_eq_of_post_token_three`), but `OpenROwnerFreshV3` quantifies over
other cells in its intrinsic-fresh footprint.  `commitStageV3` may clear the
served responder and, off the root arm, the initiator.  Closing P6 therefore
needs the global argument that every such cleared phase-owned cell is outside
an active intrinsic-fresh demand (or makes its front vacuous).  That argument
is not a fieldwise frame lemma, so the requested `commitStep_reachable_full`
and the later sealed/openHazard/mixed branches are intentionally not stated
after this first unresolved clause. -/
def CommitP6OpenRFreshPreservationV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit →
      ∀ i : Fin n,
        (stepV3 hψ h2 ring C e i).ctl.tok = .openR →
          (stepV3 hψ h2 ring C e i).ctl.mark = .releasing ∧
            OpenROwnerFreshV3 ring (stepV3 hψ h2 ring C e) i


end R2CoherenceV31ReachableThreeBranches
