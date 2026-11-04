import Leader.Wu.Coherence.ReachableStrongOwnership
import Leader.Wu.Coherence.ReachablePrepaid

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableRelease

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear R2CoherenceV31BirthQuarantine
open R2CoherenceV31QuarantineReach R2CoherenceV31ReachableFacts
open R2CoherenceV31ReachableSweep R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard4

variable {n ψ κ τ : Nat}

private theorem branch_release_conditions_rel
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .release) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok = .release := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowV3_release_eq_rel
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .release) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = releaseStageV3 l r := by
  rcases branch_release_conditions_rel hψ h2 l r hb with
    ⟨hSeek, hSweep, hCommit, hRelease⟩
  simp [rowV3, hSeek, hSweep, hCommit, hRelease]

/-- `releaseStageV3` is control-only (`R2CoherenceV31.lean:149-163`).
Together with `stepV3_other` (`:329-334`), every physical field is framed. -/
private theorem releaseStageV3_phys_rel (l r : Cell ψ κ τ) :
    (releaseStageV3 l r).1.phys = l.phys ∧
      (releaseStageV3 l r).2.phys = r.phys := by
  unfold releaseStageV3
  repeat' split <;> simp [setControl, startClosing]

private theorem release_step_left_rel
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release) :
    stepV3 hψ h2 ring C e e =
      (releaseStageV3 (C e) (C (ring.rightNeighbor e))).1 := by
  have hr := rowV3_release_eq_rel hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hr]

private theorem release_step_right_rel
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release)
    (hne : ring.rightNeighbor e ≠ e) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      (releaseStageV3 (C e) (C (ring.rightNeighbor e))).2 := by
  have hr := rowV3_release_eq_rel hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hr, hne]

private theorem release_step_phys_rel
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release) :
    ∀ p : Fin n, (stepV3 hψ h2 ring C e p).phys = (C p).phys := by
  intro p
  have hs := releaseStageV3_phys_rel (C e) (C (ring.rightNeighbor e))
  by_cases hpe : p = e
  · subst p
    rw [release_step_left_rel hψ h2 ring C e hb]
    exact hs.1
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      rw [release_step_right_rel hψ h2 ring C e hb hpe]
      exact hs.2
    · rw [stepV3_other hψ h2 ring C e p hpe hpr]

private theorem release_step_raw_rel
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release) :
    raw (stepV3 hψ h2 ring C e p) = raw (C p) := by
  exact congrArg (fun x : R2.Cell ψ κ τ => x.base.core.core)
    (release_step_phys_rel hψ h2 ring C e hb p)

private theorem mainClear_of_phys_eq_rel
    {u v : Cell ψ κ τ} (hp : u.phys = v.phys)
    (hm : MainClearV3 v) : MainClearV3 u := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at hm ⊢
  simpa [eraseCellV3, R2Coherence.raw, hp] using hm

private theorem release_ctl_origin_rel
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release) :
    (stepV3 hψ h2 ring C e p).ctl = (C p).ctl ∨
      (p = e ∧
        ((stepV3 hψ h2 ring C e p).ctl = ⟨.releasing, .none⟩ ∨
         (stepV3 hψ h2 ring C e p).ctl = ⟨.sealed, .none⟩ ∨
         (stepV3 hψ h2 ring C e p).ctl = ⟨.closing, .commit⟩ ∨
         (stepV3 hψ h2 ring C e p).ctl = ⟨.closing, .seek⟩)) ∨
      (p = ring.rightNeighbor e ∧
        successorB (C e) (C (ring.rightNeighbor e)) = true ∧
        ((stepV3 hψ h2 ring C e p).ctl = ⟨.releasing, .release⟩ ∨
         (stepV3 hψ h2 ring C e p).ctl = ⟨.releasing, .scrubL⟩)) := by
  by_cases hpe : p = e
  · subst p
    rw [release_step_left_rel hψ h2 ring C e hb]
    unfold releaseStageV3
    repeat' split <;> simp_all [setControl, startClosing]
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      rw [release_step_right_rel hψ h2 ring C e hb hpe]
      unfold releaseStageV3
      repeat' split <;> simp_all [setControl, startClosing]
    · left
      rw [stepV3_other hψ h2 ring C e p hpe hpr]


private theorem phaseOwned_mono_rel
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release)
    (hOld : PhaseOwnedV31 (C p)) :
    PhaseOwnedV31 (stepV3 hψ h2 ring C e p) := by
  rcases release_ctl_origin_rel hψ h2 ring C e p hb with h | h | h
  · unfold PhaseOwnedV31 at hOld ⊢
    rw [h]
    exact hOld
  · rcases h with ⟨_, hc⟩
    unfold PhaseOwnedV31
    rcases hc with hc | hc | hc | hc <;> rw [hc] <;> simp
  · rcases h with ⟨_, _, hc⟩
    unfold PhaseOwnedV31
    rcases hc with hc | hc <;> rw [hc] <;> simp


private theorem ownedClear_mono_rel
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release)
    (hOld : MainClearV3 (C p) ∧ PhaseOwnedV31 (C p)) :
    MainClearV3 (stepV3 hψ h2 ring C e p) ∧
      PhaseOwnedV31 (stepV3 hψ h2 ring C e p) := by
  exact ⟨mainClear_of_phys_eq_rel
      (release_step_phys_rel hψ h2 ring C e hb p) hOld.1,
    phaseOwned_mono_rel hψ h2 ring C e p hb hOld.2⟩

private theorem groupPos_eq_labels_rel
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [hLab i]

private theorem sweptPrefix_transport_rel
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (hMono : ∀ p, MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) →
      MainClearV3 (D p) ∧ PhaseOwnedV31 (D p))
    (i : Fin n) (hOld : SweptPrefixOwnedClearV31 ring C i) :
    SweptPrefixOwnedClearV31 ring D i := by
  unfold SweptPrefixOwnedClearV31 at hOld ⊢
  intro kD
  have hv := congrArg Fin.val (hLab i)
  have hkC : kD.val < (raw (C i)).label.val := by
    rw [← hv]
    exact kD.isLt
  let kC : Fin (raw (C i)).label.val := ⟨kD.val, hkC⟩
  have hAt := hOld kC
  rw [groupPos_eq_labels_rel ring hLab i kD.val]
  exact hMono _ (by simpa [kC] using hAt)

private theorem groupOwned_transport_rel
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (hMono : ∀ p, MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) →
      MainClearV3 (D p) ∧ PhaseOwnedV31 (D p))
    (i : Fin n) (hOld : GroupOwnedClearV31 ring C i) :
    GroupOwnedClearV31 ring D i := by
  unfold GroupOwnedClearV31 at hOld ⊢
  intro k
  rw [groupPos_eq_labels_rel ring hLab i k.val]
  exact hMono _ (hOld k)

private theorem groupStart_successor_rel
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

private theorem groupOwned_reindex_rel
    (ring : DirectedRing n) (C : FC n ψ κ τ) (a b : Fin n)
    (hStart : R2Coherence.groupStart ring (eraseCfgV3 C) a =
      R2Coherence.groupStart ring (eraseCfgV3 C) b)
    (hOld : GroupOwnedClearV31 ring C b) :
    GroupOwnedClearV31 ring C a := by
  unfold GroupOwnedClearV31 at hOld ⊢
  intro k
  have hp : R2Coherence.groupPos ring (eraseCfgV3 C) a k.val =
      R2Coherence.groupPos ring (eraseCfgV3 C) b k.val := by
    unfold R2Coherence.groupPos
    rw [hStart]
  rw [hp]
  exact hOld k

private theorem ownerFresh_phys_rel
    (ring : DirectedRing n) {C D : FC n ψ κ τ} (owner : Fin n)
    (hp : ∀ p, (D p).phys = (C p).phys)
    (hf : OpenROwnerFreshV3 ring C owner) : OpenROwnerFreshV3 ring D owner := by
  have hRaw : ∀ p : Fin n, raw (D p) = raw (C p) := by
    intro p
    exact congrArg
      (fun x : R2.Cell ψ κ τ => x.base.core.core) (hp p)
  have hLab : ∀ p : Fin n,
      (raw (D p)).label = (raw (C p)).label := by
    intro p
    exact congrArg
      (fun x : BoundedAgentState ψ κ => x.label) (hRaw p)
  have hPP : ∀ (i : Fin n) (k : Nat),
      R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
        R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
    intro i k
    unfold R2Coherence.prefixPos
    change
      R2Coherence.back ring i ((raw (D i)).label.val - k) =
        R2Coherence.back ring i ((raw (C i)).label.val - k)
    rw [hLab i]
  unfold OpenROwnerFreshV3 at hf ⊢
  intro j ko hHitD
  have hGPko := groupPos_eq_labels_rel ring hLab j ko.val
  rw [hGPko] at hHitD
  have hOldGroup := hf j ko hHitD
  unfold GroupIntrinsicFreshV3 at hOldGroup ⊢
  intro q
  have hGPq := groupPos_eq_labels_rel ring hLab j q.val
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
  rw [hPP front kD.val]
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


private theorem ctl_eq_of_frame_token_rel
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n) (t : TokenV3)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release)
    (ht : (stepV3 hψ h2 ring C e p).ctl.tok = t)
    (h0 : t ≠ .none) (hr : t ≠ .release) (hs : t ≠ .scrubL)
    (hc : t ≠ .commit) (hk : t ≠ .seek) :
    (stepV3 hψ h2 ring C e p).ctl = (C p).ctl := by
  rcases release_ctl_origin_rel hψ h2 ring C e p hb with h | h | h
  · exact h
  · rcases h with ⟨_, hx⟩
    rcases hx with hx | hx | hx | hx <;> rw [hx] at ht <;> simp_all
  · rcases h with ⟨_, _, hx⟩
    rcases hx with hx | hx <;> rw [hx] at ht <;> simp_all

/-- P1-P6 for RELEASE. New commit/sealed debt stays at `e`; new release/scrubL
debt is reindexed to the successor. No new sweep/openR is created. -/
theorem reachablePhaseFacts_release_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hFacts : ReachablePhaseFactsV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release) :
    ReachablePhaseFactsV31 ring (stepV3 hψ h2 ring C e) := by
  have hDebt := release_guard_prepays_owner hψ h2 ring C e hFacts hb
  rcases hFacts with ⟨hSweep, hCommit, hSealed, hRelease, hScrub, hOpenR⟩
  let D := stepV3 hψ h2 ring C e
  have hPhys : ∀ p, (D p).phys = (C p).phys := by
    intro p
    exact release_step_phys_rel hψ h2 ring C e hb p
  have hLab : ∀ p, (raw (D p)).label = (raw (C p)).label := by
    intro p
    exact congrArg (fun x : BoundedAgentState ψ κ => x.label)
      (release_step_raw_rel hψ h2 ring C e p hb)
  have hMono : ∀ p, MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) →
      MainClearV3 (D p) ∧ PhaseOwnedV31 (D p) := by
    intro p hp
    exact ownedClear_mono_rel hψ h2 ring C e p hb hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hCtl := ctl_eq_of_frame_token_rel hψ h2 ring C e i .sweep hb hi
      (by decide) (by decide) (by decide) (by decide) (by decide)
    have hiC : (C i).ctl.tok = .sweep := by rw [hCtl] at hi; exact hi
    exact sweptPrefix_transport_rel ring hLab hMono i (hSweep i hiC)
  · intro i hi
    rcases release_ctl_origin_rel hψ h2 ring C e i hb with hCtl | hL | hR
    · have hiC : (C i).ctl.tok = .commit := by rw [hCtl] at hi; exact hi
      exact groupOwned_transport_rel ring hLab hMono i (hCommit i hiC)
    · rcases hL with ⟨hie, _⟩
      subst i
      exact groupOwned_transport_rel ring hLab hMono e hDebt.2
    · rcases hR with ⟨_, _, hx⟩
      rcases hx with hx | hx <;> rw [hx] at hi <;> cases hi
  · intro i hi
    rcases release_ctl_origin_rel hψ h2 ring C e i hb with hCtl | hL | hR
    · have hiC : (C i).ctl.mark = .sealed := by rw [hCtl] at hi; exact hi
      exact groupOwned_transport_rel ring hLab hMono i (hSealed i hiC)
    · rcases hL with ⟨hie, _⟩
      subst i
      exact groupOwned_transport_rel ring hLab hMono e hDebt.2
    · rcases hR with ⟨_, _, hx⟩
      rcases hx with hx | hx <;> rw [hx] at hi <;> cases hi
  · intro i hi
    rcases release_ctl_origin_rel hψ h2 ring C e i hb with hCtl | hL | hR
    · have hiC : (C i).ctl.tok = .release := by rw [hCtl] at hi; exact hi
      rcases hRelease i hiC with ⟨hm, hg⟩
      exact ⟨by rw [hCtl]; exact hm,
        groupOwned_transport_rel ring hLab hMono i hg⟩
    · rcases hL with ⟨_, hx⟩
      rcases hx with hx | hx | hx | hx <;> rw [hx] at hi <;> cases hi
    · rcases hR with ⟨rfl, hs, hx⟩
      have hStart := groupStart_successor_rel ring C e hs
      have hg := groupOwned_reindex_rel ring C (ring.rightNeighbor e) e
        hStart hDebt.2
      constructor
      · rcases hx with hx | hx <;> rw [hx] <;> rfl
      · exact groupOwned_transport_rel ring hLab hMono (ring.rightNeighbor e) hg
  · intro i hi
    rcases release_ctl_origin_rel hψ h2 ring C e i hb with hCtl | hL | hR
    · have hiC : (C i).ctl.tok = .scrubL := by rw [hCtl] at hi; exact hi
      rcases hScrub i hiC with ⟨hm, hz, hg⟩
      refine ⟨by rw [hCtl]; exact hm, ?_,
        groupOwned_transport_rel ring hLab hMono i hg⟩
      intro hzD
      apply hz
      have hv := congrArg Fin.val (hLab i)
      exact hv.symm.trans hzD
    · rcases hL with ⟨_, hx⟩
      rcases hx with hx | hx | hx | hx <;> rw [hx] at hi <;> cases hi
    · rcases hR with ⟨rfl, hs, hx⟩
      have hStart := groupStart_successor_rel ring C e hs
      have hg := groupOwned_reindex_rel ring C (ring.rightNeighbor e) e
        hStart hDebt.2
      have hSucc : (raw (C (ring.rightNeighbor e))).label.val =
          (raw (C e)).label.val + 1 := by
        simpa [successorB] using hs
      have hzC : (raw (C (ring.rightNeighbor e))).label.val ≠ 0 := by omega
      refine ⟨?_, ?_, groupOwned_transport_rel ring hLab hMono
        (ring.rightNeighbor e) hg⟩
      · rcases hx with hx | hx <;> rw [hx] <;> rfl
      · intro hzD
        apply hzC
        have hv := congrArg Fin.val (hLab (ring.rightNeighbor e))
        exact hv.symm.trans hzD
  · intro i hi
    have hCtl := ctl_eq_of_frame_token_rel hψ h2 ring C e i .openR hb hi
      (by decide) (by decide) (by decide) (by decide) (by decide)
    have hiC : (C i).ctl.tok = .openR := by rw [hCtl] at hi; exact hi
    rcases hOpenR i hiC with ⟨hm, hf⟩
    exact ⟨by rw [hCtl]; exact hm, ownerFresh_phys_rel ring i hPhys hf⟩


/-- STOP: first clause after P1-P6 that is not supplied by the current
payload/API. On the successor+quiet+terminal arm (`R2CoherenceV31.lean:149-163`)
RELEASE can create a fresh `scrubL` at `rightNeighbor e`. If `e` is root,
this makes `e` a new `PendingOpenROwnerV31` although the pre-state incoming
clause may have been vacuous. `release_guard_prepays_owner` gives only
`GroupOwnedClearV31 ring C e`. That does not imply `OpenROwnerFreshV3 ring C e`:
the latter quantifies every arithmetic group window which hits `e`, including
boundary-overlap windows outside `e`'s own owned group. A trace-specific
provenance/prepayment bridge for this newly created pending owner is needed. -/
def ReleaseScrubLIncomingOpenRFreshPreservationV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release →
      ScrubLIncomingOpenRFreshV31 ring (stepV3 hψ h2 ring C e)

/- `releaseStep_reachable_full` is intentionally not asserted after this STOP.
P7 is the first unclosed conjunct, so pointwise/wide overlap, S, R1, and strong
R2 preservation are not attempted here. -/

end R2CoherenceV31ReachableRelease
