import Leader.Wu.Coherence.ReachableStrongOwnership

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableSeek

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
open R2CoherenceV31ReachableSweep
open R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus
open R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3
open R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard4

variable {n ψ κ τ : Nat}

private theorem branch_seek_token_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .seek) :
    r.ctl.tok = .seek := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowV3_seek_eq_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .seek) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = seekStageV3 l r := by
  have hSeek := branch_seek_token_seek69 hψ h2 l r hb
  simp [rowV3, hSeek]

private theorem seekStage_phys_seek69 (l r : Cell ψ κ τ) :
    (seekStageV3 l r).1.phys = l.phys ∧
      (seekStageV3 l r).2.phys = r.phys := by
  unfold seekStageV3
  repeat' split <;> simp [setControl]

private theorem seek_step_left_eq_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    stepV3 hψ h2 ring C e e =
      (seekStageV3 (C e) (C (ring.rightNeighbor e))).1 := by
  have hrow := rowV3_seek_eq_seek69 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hrow]

private theorem seek_step_right_eq_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek)
    (hne : ring.rightNeighbor e ≠ e) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      (seekStageV3 (C e) (C (ring.rightNeighbor e))).2 := by
  have hrow := rowV3_seek_eq_seek69 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hrow, hne]

private theorem seek_step_phys_eq_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    ∀ p : Fin n, (stepV3 hψ h2 ring C e p).phys = (C p).phys := by
  intro p
  have hs := seekStage_phys_seek69 (C e) (C (ring.rightNeighbor e))
  by_cases hpe : p = e
  · subst p
    rw [seek_step_left_eq_seek69 hψ h2 ring C e hb]
    exact hs.1
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      rw [seek_step_right_eq_seek69 hψ h2 ring C e hb hpe]
      exact hs.2
    · rw [stepV3_other hψ h2 ring C e p hpe hpr]

private theorem seek_step_raw_eq_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    raw (stepV3 hψ h2 ring C e p) = raw (C p) := by
  change
    (stepV3 hψ h2 ring C e p).phys.base.core.core =
      (C p).phys.base.core.core
  exact congrArg (fun x : R2.Cell ψ κ τ => x.base.core.core)
    (seek_step_phys_eq_seek69 hψ h2 ring C e hb p)

private theorem seek_step_ctl_shape_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    (stepV3 hψ h2 ring C e p).ctl = (C p).ctl ∨
      ((stepV3 hψ h2 ring C e p).ctl.mark = .closing ∧
        ((stepV3 hψ h2 ring C e p).ctl.tok = .none ∨
         (stepV3 hψ h2 ring C e p).ctl.tok = .seek ∨
         ((stepV3 hψ h2 ring C e p).ctl.tok = .sweep ∧
           atRootB (C p) = true))) := by
  by_cases hpe : p = e
  · subst p
    rw [seek_step_left_eq_seek69 hψ h2 ring C e hb]
    cases hr : atRootB (C (ring.rightNeighbor e)) <;>
      cases hl : atRootB (C e) <;>
      simp [seekStageV3, hr, hl, setControl]
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      rw [seek_step_right_eq_seek69 hψ h2 ring C e hb hpe]
      cases hr : atRootB (C (ring.rightNeighbor e)) <;>
        cases hl : atRootB (C e) <;>
        simp [seekStageV3, hr, hl, setControl]
    · left
      rw [stepV3_other hψ h2 ring C e p hpe hpr]
private theorem seek_step_ctl_eq_of_old_token_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek)
    {t : TokenV3}
    (ht : (stepV3 hψ h2 ring C e p).ctl.tok = t)
    (hn : t ≠ .none) (hk : t ≠ .seek) (hw : t ≠ .sweep) :
    (stepV3 hψ h2 ring C e p).ctl = (C p).ctl := by
  rcases seek_step_ctl_shape_seek69 hψ h2 ring C e p hb with h | h
  · exact h
  · rcases h.2 with h0 | hs | hsweep
    · exact (hn (ht.symm.trans h0)).elim
    · exact (hk (ht.symm.trans hs)).elim
    · exact (hw (ht.symm.trans hsweep.1)).elim

private theorem seek_step_ctl_eq_of_sealed_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek)
    (hm : (stepV3 hψ h2 ring C e p).ctl.mark = .sealed) :
    (stepV3 hψ h2 ring C e p).ctl = (C p).ctl := by
  rcases seek_step_ctl_shape_seek69 hψ h2 ring C e p hb with h | h
  · exact h
  · have hc : (R2Coherence.Mark.sealed : R2Coherence.Mark) = .closing :=
      hm.symm.trans h.1
    cases hc

private theorem seek_post_sweep_old_or_root_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek)
    (hs : (stepV3 hψ h2 ring C e p).ctl.tok = .sweep) :
    (C p).ctl.tok = .sweep ∨ atRootB (C p) = true := by
  rcases seek_step_ctl_shape_seek69 hψ h2 ring C e p hb with h | h
  · left
    rw [h] at hs
    exact hs
  · rcases h.2 with h0 | hk | hw
    · have hx : (TokenV3.sweep : TokenV3) = .none := hs.symm.trans h0
      cases hx
    · have hx : (TokenV3.sweep : TokenV3) = .seek := hs.symm.trans hk
      cases hx
    · exact Or.inr hw.2

private theorem mainClear_of_phys_eq_seek69
    {u v : Cell ψ κ τ} (hPhys : u.phys = v.phys)
    (hm : MainClearV3 v) : MainClearV3 u := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at hm ⊢
  simpa [eraseCellV3, R2Coherence.raw, hPhys] using hm

private theorem phaseOwned_seek_step_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek)
    (hOld : PhaseOwnedV31 (C p)) :
    PhaseOwnedV31 (stepV3 hψ h2 ring C e p) := by
  rcases seek_step_ctl_shape_seek69 hψ h2 ring C e p hb with h | h
  · unfold PhaseOwnedV31 at hOld ⊢
    rw [h]
    exact hOld
  · unfold PhaseOwnedV31
    left
    rw [h.1]
    decide

private theorem ownedClear_seek_step_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek)
    (hOld : MainClearV3 (C p) ∧ PhaseOwnedV31 (C p)) :
    MainClearV3 (stepV3 hψ h2 ring C e p) ∧
      PhaseOwnedV31 (stepV3 hψ h2 ring C e p) := by
  constructor
  · exact mainClear_of_phys_eq_seek69
      (seek_step_phys_eq_seek69 hψ h2 ring C e hb p) hOld.1
  · exact phaseOwned_seek_step_seek69 hψ h2 ring C e p hb hOld.2

private theorem groupPos_eq_of_labels_seek69
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

private theorem sweptPrefix_seek_step_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek)
    (hOld : SweptPrefixOwnedClearV31 ring C i) :
    SweptPrefixOwnedClearV31 ring (stepV3 hψ h2 ring C e) i := by
  have hLab := stepV3_labels_eq_or_held hψ h2 ring C e
  unfold SweptPrefixOwnedClearV31 at hOld ⊢
  intro k
  dsimp only
  have hVal := congrArg Fin.val (hLab i)
  have hkC : k.val < (raw (C i)).label.val := by
    rw [← hVal]
    exact k.isLt
  let kC : Fin (raw (C i)).label.val := ⟨k.val, hkC⟩
  have hPrev := hOld kC
  dsimp only at hPrev
  rw [groupPos_eq_of_labels_seek69 ring hLab i k.val]
  exact ownedClear_seek_step_seek69 hψ h2 ring C e _ hb hPrev

private theorem groupOwned_seek_step_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek)
    (hOld : GroupOwnedClearV31 ring C i) :
    GroupOwnedClearV31 ring (stepV3 hψ h2 ring C e) i := by
  have hLab := stepV3_labels_eq_or_held hψ h2 ring C e
  unfold GroupOwnedClearV31 at hOld ⊢
  intro k
  dsimp only
  have hPrev := hOld k
  dsimp only at hPrev
  rw [groupPos_eq_of_labels_seek69 ring hLab i k.val]
  exact ownedClear_seek_step_seek69 hψ h2 ring C e _ hb hPrev

private theorem sweptPrefix_root_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek)
    (hRoot : atRootB (C i) = true) :
    SweptPrefixOwnedClearV31 ring (stepV3 hψ h2 ring C e) i := by
  have hRaw := seek_step_raw_eq_seek69 hψ h2 ring C e i hb
  have hzC : (raw (C i)).label.val = 0 := by
    simpa [atRootB] using hRoot
  have hzD :
      (raw (stepV3 hψ h2 ring C e i)).label.val = 0 := by
    rw [hRaw]
    exact hzC
  unfold SweptPrefixOwnedClearV31
  intro k
  exact Fin.elim0 (Fin.cast hzD k)



private theorem prefixPos_eq_of_labels_seek69
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change
    R2Coherence.back ring i ((raw (D i)).label.val - k) =
      R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [hLab i]

private theorem openROwnerFresh_of_phys_eq_seek69
    (ring : DirectedRing n) {C D : FC n ψ κ τ} (owner : Fin n)
    (hPhys : ∀ p : Fin n, (D p).phys = (C p).phys)
    (hFresh : OpenROwnerFreshV3 ring C owner) :
    OpenROwnerFreshV3 ring D owner := by
  have hRaw : ∀ p : Fin n, raw (D p) = raw (C p) := by
    intro p
    exact congrArg
      (fun x : R2.Cell ψ κ τ => x.base.core.core) (hPhys p)
  have hLab : ∀ p : Fin n,
      (raw (D p)).label = (raw (C p)).label := by
    intro p
    exact congrArg
      (fun x : BoundedAgentState ψ κ => x.label) (hRaw p)
  unfold OpenROwnerFreshV3 at hFresh ⊢
  intro j ko hHitD
  have hGPko := groupPos_eq_of_labels_seek69 ring hLab j ko.val
  rw [hGPko] at hHitD
  have hOldGroup := hFresh j ko hHitD
  unfold GroupIntrinsicFreshV3 at hOldGroup ⊢
  intro q
  have hGPq := groupPos_eq_of_labels_seek69 ring hLab j q.val
  rw [hGPq]
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  change IntrinsicFreshAtV3 ring D front
  have hOldFront : IntrinsicFreshAtV3 ring C front := by
    simpa [front] using hOldGroup q
  unfold IntrinsicFreshAtV3 at hOldFront ⊢
  intro hEqD
  have hState :
      (raw (D front)).state = (raw (C front)).state := by
    exact congrArg
      (fun x : BoundedAgentState ψ κ => x.state) (hRaw front)
  have hEqC : (raw (C front)).state = .equal := by
    rw [← hState]
    exact hEqD
  have hOldAt := hOldFront hEqC
  intro kD
  have hLabelVal :
      (raw (D front)).label.val = (raw (C front)).label.val := by
    exact congrArg (fun x : Fin ψ => x.val) (hLab front)
  have hkC : kD.val < (raw (C front)).label.val + 1 := by
    let m : Nat := kD.val
    have hk : m < (raw (D front)).label.val + 1 := kD.isLt
    simpa only [hLabelVal] using hk
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hkC⟩
  have hOldK := hOldAt kC
  have hPP := prefixPos_eq_of_labels_seek69 ring hLab front kD.val
  rw [hPP]
  let p := R2Coherence.prefixPos ring (eraseCfgV3 C) front kD.val
  change R2Coherence.freshComponent (eraseCellV3 (D p)) kD.val
  have hOldK' :
      R2Coherence.freshComponent (eraseCellV3 (C p)) kD.val := by
    simpa [p, kC] using hOldK
  unfold R2Coherence.freshComponent at hOldK' ⊢
  change
    (raw (D p)).label.val = kD.val ∧
      (match (raw (D p)).path with
       | .bot => False
       | .some lab b =>
           lab.val = kD.val ∧
             b.val = (if (raw (D p)).bit then 1 else 0))
  change
    (raw (C p)).label.val = kD.val ∧
      (match (raw (C p)).path with
       | .bot => False
       | .some lab b =>
           lab.val = kD.val ∧
             b.val = (if (raw (C p)).bit then 1 else 0)) at hOldK'
  rw [hRaw p]
  exact hOldK'

private theorem pendingOpenR_before_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek)
    (hPost : PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) owner) :
    PendingOpenROwnerV31 ring C owner := by
  rcases hPost with ⟨hScrub, hSucc, hRoot⟩
  have hCtl := seek_step_ctl_eq_of_old_token_seek69
    hψ h2 ring C e (ring.rightNeighbor owner) hb hScrub
    (by decide) (by decide) (by decide)
  have hScrubC : (C (ring.rightNeighbor owner)).ctl.tok = .scrubL := by
    rw [hCtl] at hScrub
    exact hScrub
  have hLab := stepV3_labels_eq_or_held hψ h2 ring C e
  refine ⟨hScrubC, ?_, ?_⟩
  · unfold successorB at hSucc ⊢
    simpa [hLab owner, hLab (ring.rightNeighbor owner)] using hSucc
  · unfold atRootB at hRoot ⊢
    simpa [hLab owner] using hRoot

/-- SEEK is physically inert, so a pending-owner freshness certificate is
transported without the chain-origin seam used by open/no-hazard. -/
theorem scrubLIncoming_seek_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hIncoming : ScrubLIncomingOpenRFreshV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    ScrubLIncomingOpenRFreshV31 ring (stepV3 hψ h2 ring C e) := by
  intro owner hScrub hSucc hRoot
  have hPost : PendingOpenROwnerV31 ring
      (stepV3 hψ h2 ring C e) owner := ⟨hScrub, hSucc, hRoot⟩
  have hPre := pendingOpenR_before_seek69 hψ h2 ring C e owner hb hPost
  have hFresh := hIncoming owner hPre.1 hPre.2.1 hPre.2.2
  exact openROwnerFresh_of_phys_eq_seek69 ring owner
    (seek_step_phys_eq_seek69 hψ h2 ring C e hb) hFresh

/-- The six old reachable clauses are seek-closed.  Existing phase debt is
physical + ownership debt, hence frame transport; a newly created sweep is at
label zero and has an empty strict swept prefix. -/
theorem reachablePhaseFacts_seek_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hFacts : ReachablePhaseFactsV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    ReachablePhaseFactsV31 ring (stepV3 hψ h2 ring C e) := by
  rcases hFacts with
    ⟨hSweep, hCommit, hSealed, hRelease, hScrub, hOpenR⟩
  have hPhys := seek_step_phys_eq_seek69 hψ h2 ring C e hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases seek_post_sweep_old_or_root_seek69
        hψ h2 ring C e i hb hi with hiC | hRoot
    · exact sweptPrefix_seek_step_seek69
        hψ h2 ring C e i hb (hSweep i hiC)
    · exact sweptPrefix_root_seek69 hψ h2 ring C e i hb hRoot
  · intro i hi
    have hCtl := seek_step_ctl_eq_of_old_token_seek69
      hψ h2 ring C e i hb hi (by decide) (by decide) (by decide)
    have hiC : (C i).ctl.tok = .commit := by
      rw [hCtl] at hi
      exact hi
    exact groupOwned_seek_step_seek69
      hψ h2 ring C e i hb (hCommit i hiC)
  · intro i hi
    have hCtl := seek_step_ctl_eq_of_sealed_seek69
      hψ h2 ring C e i hb hi
    have hiC : (C i).ctl.mark = .sealed := by
      rw [hCtl] at hi
      exact hi
    exact groupOwned_seek_step_seek69
      hψ h2 ring C e i hb (hSealed i hiC)
  · intro i hi
    have hCtl := seek_step_ctl_eq_of_old_token_seek69
      hψ h2 ring C e i hb hi (by decide) (by decide) (by decide)
    have hiC : (C i).ctl.tok = .release := by
      rw [hCtl] at hi
      exact hi
    rcases hRelease i hiC with ⟨hm, hg⟩
    constructor
    · rw [hCtl]
      exact hm
    · exact groupOwned_seek_step_seek69 hψ h2 ring C e i hb hg
  · intro i hi
    have hCtl := seek_step_ctl_eq_of_old_token_seek69
      hψ h2 ring C e i hb hi (by decide) (by decide) (by decide)
    have hiC : (C i).ctl.tok = .scrubL := by
      rw [hCtl] at hi
      exact hi
    rcases hScrub i hiC with ⟨hm, hz, hg⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hCtl]
      exact hm
    · intro hzero
      apply hz
      have hRaw := seek_step_raw_eq_seek69 hψ h2 ring C e i hb
      have hv := congrArg
        (fun x : BoundedAgentState ψ κ => x.label.val) hRaw
      rw [← hv]
      exact hzero
    · exact groupOwned_seek_step_seek69 hψ h2 ring C e i hb hg
  · intro i hi
    have hCtl := seek_step_ctl_eq_of_old_token_seek69
      hψ h2 ring C e i hb hi (by decide) (by decide) (by decide)
    have hiC : (C i).ctl.tok = .openR := by
      rw [hCtl] at hi
      exact hi
    rcases hOpenR i hiC with ⟨hm, hf⟩
    constructor
    · rw [hCtl]
      exact hm
    · exact openROwnerFresh_of_phys_eq_seek69 ring i hPhys hf

private theorem footprint_after_seek_to_before_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek)
    (hFoot : InOpenRFreshFootprintV31 ring
      (stepV3 hψ h2 ring C e) owner p) :
    InOpenRFreshFootprintV31 ring C owner p := by
  have hLab : ∀ x : Fin n,
      (raw (stepV3 hψ h2 ring C e x)).label = (raw (C x)).label :=
    stepV3_labels_eq_or_held hψ h2 ring C e
  rcases hFoot with ⟨j, ko, q, hOwnerD, kD, hPrefixD⟩
  have hGPko := groupPos_eq_of_labels_seek69 ring hLab j ko.val
  rw [hGPko] at hOwnerD
  have hGPq := groupPos_eq_of_labels_seek69 ring hLab j q.val
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hFrontD :
      R2Coherence.groupPos ring
        (eraseCfgV3 (stepV3 hψ h2 ring C e)) j q.val = front := by
    simpa [front] using hGPq
  have hLabelVal :
      (raw (stepV3 hψ h2 ring C e
        (R2Coherence.groupPos ring
          (eraseCfgV3 (stepV3 hψ h2 ring C e)) j q.val))).label.val =
        (raw (C front)).label.val := by
    rw [hFrontD]
    exact congrArg (fun x : Fin ψ => x.val) (hLab front)
  have hkC : kD.val < (raw (C front)).label.val + 1 := by
    let m : Nat := kD.val
    have hmD : m <
        (raw (stepV3 hψ h2 ring C e
          (R2Coherence.groupPos ring
            (eraseCfgV3 (stepV3 hψ h2 ring C e)) j q.val))).label.val + 1 :=
      kD.isLt
    simpa only [hLabelVal] using hmD
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hkC⟩
  refine ⟨j, ko, q, hOwnerD, kC, ?_⟩
  let m : Nat := kD.val
  have hPrefixD0 :
      R2Coherence.prefixPos ring (eraseCfgV3 (stepV3 hψ h2 ring C e))
        (R2Coherence.groupPos ring
          (eraseCfgV3 (stepV3 hψ h2 ring C e)) j q.val) m = p := by
    simpa [m] using hPrefixD
  have hPrefixD1 :
      R2Coherence.prefixPos ring (eraseCfgV3 (stepV3 hψ h2 ring C e))
        front m = p := by
    simpa only [hFrontD] using hPrefixD0
  have hPP := prefixPos_eq_of_labels_seek69 ring hLab front m
  have hPrefixC :
      R2Coherence.prefixPos ring (eraseCfgV3 C) front m = p := by
    exact hPP.symm.trans hPrefixD1
  have hFrontC :
      R2Coherence.groupPos ring (eraseCfgV3 C) j q.val = front := by
    rfl
  have hkCm : kC.val = m := by rfl
  simpa only [hFrontC, hkCm] using hPrefixC

private theorem safeAt_seek_step_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek)
    (hSafe : SweepOpenRSafeAtV31 ring C owner p) :
    SweepOpenRSafeAtV31 ring (stepV3 hψ h2 ring C e) owner p := by
  unfold SweepOpenRSafeAtV31 at hSafe ⊢
  rcases hSafe with hm | hout
  · left
    exact mainClear_of_phys_eq_seek69
      (seek_step_phys_eq_seek69 hψ h2 ring C e hb p) hm
  · right
    intro hFoot
    exact hout (footprint_after_seek_to_before_seek69
      hψ h2 ring C e owner p hb hFoot)

private theorem seek_post_sweep_origin_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e s : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek)
    (hSweepD : (stepV3 hψ h2 ring C e s).ctl.tok = .sweep) :
    (C s).ctl.tok = .sweep ∨
      (s = ring.rightNeighbor e ∧
        atRootB (C (ring.rightNeighbor e)) = true) ∨
      (s = e ∧
        atRootB (C (ring.rightNeighbor e)) = false ∧
        atRootB (C e) = true) := by
  by_cases hse : s = e
  · subst s
    rw [seek_step_left_eq_seek69 hψ h2 ring C e hb] at hSweepD
    cases hr : atRootB (C (ring.rightNeighbor e)) with
    | true =>
        left
        simpa [seekStageV3, hr] using hSweepD
    | false =>
        cases hl : atRootB (C e) with
        | true => exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
        | false => simp [seekStageV3, hr, hl, setControl] at hSweepD
  · by_cases hsr : s = ring.rightNeighbor e
    · subst s
      rw [seek_step_right_eq_seek69 hψ h2 ring C e hb hse] at hSweepD
      cases hr : atRootB (C (ring.rightNeighbor e)) with
      | true => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | false =>
          cases hl : atRootB (C e) <;>
            simp [seekStageV3, hr, hl, setControl] at hSweepD
    · left
      rw [stepV3_other hψ h2 ring C e s hse hsr] at hSweepD
      exact hSweepD



private theorem wideWindow_seek_transport_seek69
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e front owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek)
    (hSource :
      SweepOpenRSafeAtV31 ring C owner (ring.rightNeighbor front) ∧
      ∀ d : Fin (ψ - (raw (C front)).label.val),
        SweepOpenRSafeAtV31 ring C owner
          (R2Coherence.fwd ring front d.val)) :
    SweepOpenRSafeAtV31 ring (stepV3 hψ h2 ring C e) owner
        (ring.rightNeighbor front) ∧
      ∀ d : Fin
          (ψ - (raw (stepV3 hψ h2 ring C e front)).label.val),
        SweepOpenRSafeAtV31 ring (stepV3 hψ h2 ring C e) owner
          (R2Coherence.fwd ring front d.val) := by
  constructor
  · exact safeAt_seek_step_seek69
      hψ h2 ring C e owner (ring.rightNeighbor front) hb hSource.1
  · intro dD
    have hLab := stepV3_labels_eq_or_held hψ h2 ring C e front
    have hVal :
        (raw (stepV3 hψ h2 ring C e front)).label.val =
          (raw (C front)).label.val :=
      congrArg (fun x : Fin ψ => x.val) hLab
    have hdC : dD.val < ψ - (raw (C front)).label.val := by
      let m : Nat := dD.val
      have hm : m < ψ -
          (raw (stepV3 hψ h2 ring C e front)).label.val := dD.isLt
      simpa only [hVal] using hm
    let dC : Fin (ψ - (raw (C front)).label.val) := ⟨dD.val, hdC⟩
    have hOld := hSource.2 dC
    change SweepOpenRSafeAtV31 ring C owner
      (R2Coherence.fwd ring front dD.val) at hOld
    exact safeAt_seek_step_seek69
      hψ h2 ring C e owner (R2Coherence.fwd ring front dD.val) hb hOld

/-- S is exactly the prepayment needed when SEEK creates a root sweep.
Remote, already-live sweeps use the pre-state wide clause. -/
theorem sweepOpenROverlapClearWide_seek_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hWide : SweepOpenROverlapClearWideV31 ring C)
    (hS : SeekIncomingSweepOpenROverlapClearWideV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    SweepOpenROverlapClearWideV31 ring (stepV3 hψ h2 ring C e) := by
  intro sweep owner hSweepD hPendingD
  have hPendingC := pendingOpenR_before_seek69
    hψ h2 ring C e owner hb hPendingD
  have hOrigin := seek_post_sweep_origin_seek69
    hψ h2 ring C e sweep hb hSweepD
  rcases hOrigin with hOld | hNewR | hNewL
  · exact wideWindow_seek_transport_seek69
      hψ h2 ring C e sweep owner hb
      (hWide sweep owner hOld hPendingC)
  · rcases hNewR with ⟨rfl, hRootR⟩
    have hSeekR := branch_seek_token_seek69 hψ h2
      (C e) (C (ring.rightNeighbor e)) hb
    have hSource := (hS e owner hSeekR hPendingC).1 hRootR
    exact wideWindow_seek_transport_seek69
      hψ h2 ring C e (ring.rightNeighbor e) owner hb hSource
  · rcases hNewL with ⟨hSweepE, hNotRootR, hRootL⟩
    subst sweep
    have hSeekR := branch_seek_token_seek69 hψ h2
      (C e) (C (ring.rightNeighbor e)) hb
    have hSource := (hS e owner hSeekR hPendingC).2 hNotRootR hRootL
    exact wideWindow_seek_transport_seek69
      hψ h2 ring C e e owner hb hSource


/-- Pointwise overlap is recovered from the post-state wide clause. -/
theorem sweepOpenROverlapClear_seek_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hWide : SweepOpenROverlapClearWideV31 ring C)
    (hS : SeekIncomingSweepOpenROverlapClearWideV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    SweepOpenROverlapClearV31 ring (stepV3 hψ h2 ring C e) := by
  exact sweepOpenROverlapClearWide_implies_pointwise ring _
    (sweepOpenROverlapClearWide_seek_step
      hψ h2 ring C e hWide hS hb)

/-- The requested old nine obligations close under SEEK.  `hGeom` and
`hTrace` are threaded through the interface; no extra causal
fact from them is needed before the Plus4 S field. -/
theorem reachablePhaseFactsPlus3_seek_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (_hGeom : ElectionGeometryV31 ring C)
    (_hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    ReachablePhaseFactsPlus3V31 ring (stepV3 hψ h2 ring C e) := by
  rcases hPlus with ⟨hP3, hS, _hR1, _hR2⟩
  rcases hP3 with ⟨hP2, hWide⟩
  rcases hP2 with ⟨hP, _hPoint⟩
  rcases hP with ⟨hFacts, hIncoming⟩
  have hFactsD := reachablePhaseFacts_seek_step
    hψ h2 ring C e hFacts hb
  have hIncomingD := scrubLIncoming_seek_step
    hψ h2 ring C e hIncoming hb
  have hWideD := sweepOpenROverlapClearWide_seek_step
    hψ h2 ring C e hWide hS hb
  have hPointD :=
    sweepOpenROverlapClearWide_implies_pointwise
      ring (stepV3 hψ h2 ring C e) hWideD
  exact ⟨⟨⟨hFactsD, hIncomingD⟩, hPointD⟩, hWideD⟩

/-- STOP: first Plus4 field not derivable from the current payload.

In the nonroot/nonroot arm of `seekStageV3`, a seek on `rightNeighbor e`
moves to `e`.  If `e` has label 1, let `x` be its root predecessor.  In the
post-state, S instantiated at `x` now sees a seek at `rightNeighbor x = e`;
its second implication is active and demands the whole root-sweep safety
window.  In the pre-state:

* S at the serviced edge `e` is vacuous because both `e` and its responder
  are nonroot;
* S at `x` is not guarded because `e` did not yet carry the moved seek;
* Plus3 has no obligation on a seek-only future window;
* R1 requires a current `.openR`, and strong R2 requires a live `.sweep`.

`R2CoherenceV31ReachableFacts.lean:23-45` deliberately has no seek clause,
and `R2CoherenceV31SeekFork.lean:95-113,127-135` confirms that multiple seeks
are not excluded by the old shape.  Thus this is a genuine missing
seek-provenance/prepayment transport, not a field-equation exercise. -/
def SeekIncomingSweepOpenROverlapClearWideSeekPreservationV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ReachableFromQuarantineV31 hψ h2 ring C →
    ElectionGeometryV31 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek →
      SeekIncomingSweepOpenROverlapClearWideV31 ring
        (stepV3 hψ h2 ring C e)

/-
The requested `seekStep_reachable_plus4` is intentionally not stated as a
theorem after this STOP.  S is the first field after the old nine, so the
instruction says to stop here; R1 and strong-R2 seek preservation are therefore
not attempted in this file.
-/

end R2CoherenceV31ReachableSeek
