import Leader.Wu.Coherence.ReachableOpenR
import Leader.Wu.Coherence.ReachableStrongOwnership

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableOpenR2

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
open R2CoherenceV31ReachableOpenR
open R2CoherenceV31ReachableOpenNoHazard
open R2CoherenceV31ReachableOpenNoHazard4

variable {n ψ κ τ : Nat}

/-- P1-P5 plus the openR structural/freshness clause P6. -/
def ReachablePhaseFactsP1P6StrongR2V31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ReachablePhaseFactsP1P5V31 ring C ∧
    ∀ i : Fin n, (C i).ctl.tok = .openR →
      (C i).ctl.mark = .releasing ∧ OpenROwnerFreshV3 ring C i

private theorem plus4_of_strongR2_openR2
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : ReachablePhaseFactsPlus4StrongR2V31 ring C) :
    ReachablePhaseFactsPlus4V31 ring C := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

private theorem bool_false_of_not_true_openR2
    (b : Bool) (h : b ≠ true) : b = false := by
  cases b <;> simp_all

private theorem branch_openR_conditions_openR2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openR) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
      r.ctl.tok ≠ .scrubL ∧ l.ctl.tok = .openR := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowV3_openR_eq_openR2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openR) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = openRStageV3 l r := by
  rcases branch_openR_conditions_openR2 hψ h2 l r hb with
    ⟨hSeek, _hSweep, hCommit, _hRelease, hScrub, hOpenR⟩
  simp [rowV3, hSeek, hCommit, hScrub, hOpenR]

private theorem successor_labels_openR2
    (l r : Cell ψ κ τ) (h : successorB l r = true) :
    (raw r).label.val = (raw l).label.val + 1 := by
  simpa [successorB] using h

private theorem edge_distinct_of_successor_openR2
    (C : FC n ψ κ τ) (ring : DirectedRing n) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    e ≠ ring.rightNeighbor e := by
  intro h
  have hSame := congrArg (fun p : Fin n => (raw (C p)).label.val) h
  have hSucc := successor_labels_openR2
    (C e) (C (ring.rightNeighbor e)) hs
  omega

private theorem openR_step_left_good_openR2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e e =
      setControl (clearMain (C e)) .open .none := by
  have hrow := rowV3_openR_eq_openR2 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, openRStageV3, hs]

private theorem openR_step_right_good_openR2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      if atTerminalB (C (ring.rightNeighbor e)) then
        setControl (clearMain (C (ring.rightNeighbor e))) .open .none
      else
        setControl (clearMain (C (ring.rightNeighbor e))) .releasing .openR := by
  have hrow := rowV3_openR_eq_openR2 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hne := edge_distinct_of_successor_openR2 C ring e hs
  have hrne : ring.rightNeighbor e ≠ e := Ne.symm hne
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, openRStageV3, hs, hrne]


private theorem openR_step_left_bad_openR2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false) :
    stepV3 hψ h2 ring C e e = startClosing (C e) := by
  have hrow := rowV3_openR_eq_openR2 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, openRStageV3, hs]

private theorem openR_step_bad_other_openR2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false)
    (hi : i ≠ e) :
    stepV3 hψ h2 ring C e i = C i := by
  by_cases hir : i = ring.rightNeighbor e
  · subst i
    have hrow := rowV3_openR_eq_openR2 hψ h2
      (C e) (C (ring.rightNeighbor e)) hb
    simpa [stepV3, protocolV3, PopulationProtocol.step,
      hrow, openRStageV3, hs, hi]
  · exact stepV3_other hψ h2 ring C e i hi hir

private theorem groupPos_eq_of_labels_openR2
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

private theorem prefixPos_eq_of_labels_openR2
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

private theorem freshComponent_false_of_mainClear_openR2
    (u : Cell ψ κ τ) (k : Nat)
    (hm : MainClearV3 u)
    (hf : R2Coherence.freshComponent (eraseCellV3 u) k) : False := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at hm
  unfold R2Coherence.freshComponent at hf
  change
    (raw u).label.val = k ∧
      (match (raw u).path with
       | .bot => False
       | .some lab b =>
           lab.val = k ∧ b.val = (if (raw u).bit then 1 else 0)) at hf
  have hPath : (raw u).path = .bot := hm.2.1
  rw [hPath] at hf
  exact hf.2

private theorem fwd_zero_openR2
    (ring : DirectedRing n) (i : Fin n) :
    R2Coherence.fwd ring i 0 = i := by
  apply Fin.ext
  simp [R2Coherence.fwd, Nat.mod_eq_of_lt i.isLt]

private theorem fwd_one_openR2
    (ring : DirectedRing n) (i : Fin n) :
    R2Coherence.fwd ring i 1 = ring.rightNeighbor i := by
  apply Fin.ext
  rfl

private theorem served_mainClear_of_R1_openR2
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hR1 : OpenRForwardMainClearV31 ring C)
    (hOpen : (C e).ctl.tok = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    MainClearV3 (C e) ∧ MainClearV3 (C (ring.rightNeighbor e)) := by
  have hSuffix := hR1 e hOpen
  have hELt : (raw (C e)).label.val < ψ := (raw (C e)).label.isLt
  have h0 : 0 < ψ - (raw (C e)).label.val := by omega
  let d0 : Fin (ψ - (raw (C e)).label.val) := ⟨0, h0⟩
  have he := hSuffix d0
  have hf0 : R2Coherence.fwd ring e d0.val = e := by
    simpa [d0] using fwd_zero_openR2 ring e
  rw [hf0] at he
  have hSucc := successor_labels_openR2
    (C e) (C (ring.rightNeighbor e)) hs
  have hRLt : (raw (C (ring.rightNeighbor e))).label.val < ψ :=
    (raw (C (ring.rightNeighbor e))).label.isLt
  have h1 : 1 < ψ - (raw (C e)).label.val := by omega
  let d1 : Fin (ψ - (raw (C e)).label.val) := ⟨1, h1⟩
  have hr := hSuffix d1
  have hf1 :
      R2Coherence.fwd ring e d1.val = ring.rightNeighbor e := by
    simpa [d1] using fwd_one_openR2 ring e
  rw [hf1] at hr
  exact ⟨he, hr⟩

private theorem openR_good_states_openR2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    (raw (stepV3 hψ h2 ring C e e)).state = .none ∧
      (raw (stepV3 hψ h2 ring C e (ring.rightNeighbor e))).state = .none := by
  constructor
  · rw [openR_step_left_good_openR2 hψ h2 ring C e hb hs]
    simp [setControl, clearMain, raw]
  · rw [openR_step_right_good_openR2 hψ h2 ring C e hb hs]
    cases ht : atTerminalB (C (ring.rightNeighbor e)) <;>
      simp [ht, setControl, clearMain, raw]

private theorem openR_bad_phys_eq_openR2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false) :
    ∀ p : Fin n, (stepV3 hψ h2 ring C e p).phys = (C p).phys := by
  intro p
  by_cases hpe : p = e
  · subst p
    rw [openR_step_left_bad_openR2 hψ h2 ring C e hb hs]
    simp [startClosing, setControl]
  · rw [openR_step_bad_other_openR2 hψ h2 ring C e p hb hs hpe]


private theorem groupIntrinsicFresh_openR_good_openR2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e j : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hClearE : MainClearV3 (C e))
    (hClearR : MainClearV3 (C (ring.rightNeighbor e)))
    (hOld : GroupIntrinsicFreshV3 ring C j) :
    GroupIntrinsicFreshV3 ring (stepV3 hψ h2 ring C e) j := by
  let D := stepV3 hψ h2 ring C e
  have hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label := by
    intro p
    simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  have hStates := openR_good_states_openR2 hψ h2 ring C e hb hs
  unfold GroupIntrinsicFreshV3 at hOld ⊢
  intro q
  have hGPq := groupPos_eq_of_labels_openR2 ring hLab j q.val
  rw [hGPq]
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  change IntrinsicFreshAtV3 ring D front
  have hOldFront : IntrinsicFreshAtV3 ring C front := by
    simpa [front] using hOld q
  unfold IntrinsicFreshAtV3 at hOldFront ⊢
  intro hEqD
  by_cases hfe : front = e
  · have hx := hEqD
    rw [hfe, hStates.1] at hx
    cases hx
  · by_cases hfr : front = ring.rightNeighbor e
    · have hx := hEqD
      rw [hfr, hStates.2] at hx
      cases hx
    · have hFrontEq : D front = C front := by
        dsimp [D]
        exact stepV3_other hψ h2 ring C e front hfe hfr
      have hEqC : (raw (C front)).state = .equal := by
        simpa [hFrontEq] using hEqD
      have hOldAt := hOldFront hEqC
      intro kD
      have hLabelVal :
          (raw (D front)).label.val = (raw (C front)).label.val :=
        congrArg (fun x : Fin ψ => x.val) (hLab front)
      have hkC : kD.val < (raw (C front)).label.val + 1 := by
        let m : Nat := kD.val
        have hm : m < (raw (D front)).label.val + 1 := kD.isLt
        simpa only [hLabelVal] using hm
      let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hkC⟩
      have hOldK := hOldAt kC
      have hPP := prefixPos_eq_of_labels_openR2 ring hLab front kD.val
      rw [hPP]
      let p := R2Coherence.prefixPos ring
        (eraseCfgV3 C) front kD.val
      change R2Coherence.freshComponent (eraseCellV3 (D p)) kD.val
      have hOldK' :
          R2Coherence.freshComponent (eraseCellV3 (C p)) kD.val := by
        simpa [p, kC] using hOldK
      by_cases hpe : p = e
      · exact (freshComponent_false_of_mainClear_openR2
          (C p) kD.val (by simpa [hpe] using hClearE)
          hOldK').elim
      · by_cases hpr : p = ring.rightNeighbor e
        · exact (freshComponent_false_of_mainClear_openR2
            (C p) kD.val (by simpa [hpr] using hClearR)
            hOldK').elim
        · have hDp : D p = C p := by
            dsimp [D]
            exact stepV3_other hψ h2 ring C e p hpe hpr
          simpa [hDp, p] using hOldK'

private theorem old_ownerFresh_openR_good_openR2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hClearE : MainClearV3 (C e))
    (hClearR : MainClearV3 (C (ring.rightNeighbor e)))
    (hFresh : OpenROwnerFreshV3 ring C owner) :
    OpenROwnerFreshV3 ring (stepV3 hψ h2 ring C e) owner := by
  let D := stepV3 hψ h2 ring C e
  have hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label := by
    intro p
    simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  unfold OpenROwnerFreshV3 at hFresh ⊢
  intro j ko hHitD
  have hGP := groupPos_eq_of_labels_openR2 ring hLab j ko.val
  rw [hGP] at hHitD
  have hOldGroup := hFresh j ko hHitD
  exact groupIntrinsicFresh_openR_good_openR2
    hψ h2 ring C e j hb hs hClearE hClearR hOldGroup

private theorem new_right_ownerFresh_openR_good_openR2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hElection : ElectionGeometryV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hClearE : MainClearV3 (C e))
    (hClearR : MainClearV3 (C (ring.rightNeighbor e)))
    (hFreshE : OpenROwnerFreshV3 ring C e) :
    OpenROwnerFreshV3 ring
      (stepV3 hψ h2 ring C e) (ring.rightNeighbor e) := by
  let D := stepV3 hψ h2 ring C e
  have hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label := by
    intro p
    simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  unfold OpenROwnerFreshV3
  intro j k hHitD
  have hGP := groupPos_eq_of_labels_openR2 ring hLab j k.val
  rw [hGP] at hHitD
  have hSucc := successor_labels_openR2
    (C e) (C (ring.rightNeighbor e)) hs
  have hNonroot :
      (raw (C (ring.rightNeighbor e))).label.val ≠ 0 := by
    omega
  obtain ⟨kp, hPred⟩ := R2CoherenceV31ReachableOpenNoHazard.nonroot_window_contains_predecessor_reach
    ring C hElection j e k hNonroot hHitD
  have hOldGroup := hFreshE j kp hPred
  exact groupIntrinsicFresh_openR_good_openR2
    hψ h2 ring C e j hb hs hClearE hClearR hOldGroup


private theorem openROwnerFresh_of_phys_eq_openR2
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
  have hGPko := groupPos_eq_of_labels_openR2 ring hLab j ko.val
  rw [hGPko] at hHitD
  have hOldGroup := hFresh j ko hHitD
  unfold GroupIntrinsicFreshV3 at hOldGroup ⊢
  intro q
  have hGPq := groupPos_eq_of_labels_openR2 ring hLab j q.val
  rw [hGPq]
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  change IntrinsicFreshAtV3 ring D front
  have hOldFront : IntrinsicFreshAtV3 ring C front := by
    simpa [front] using hOldGroup q
  unfold IntrinsicFreshAtV3 at hOldFront ⊢
  intro hEqD
  have hState :
      (raw (D front)).state = (raw (C front)).state :=
    congrArg (fun x : BoundedAgentState ψ κ => x.state) (hRaw front)
  have hEqC : (raw (C front)).state = .equal := by
    rw [← hState]
    exact hEqD
  have hOldAt := hOldFront hEqC
  intro kD
  have hLabelVal :
      (raw (D front)).label.val = (raw (C front)).label.val :=
    congrArg (fun x : Fin ψ => x.val) (hLab front)
  have hkC : kD.val < (raw (C front)).label.val + 1 := by
    let m : Nat := kD.val
    have hm : m < (raw (D front)).label.val + 1 := kD.isLt
    simpa only [hLabelVal] using hm
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hkC⟩
  have hOldK := hOldAt kC
  have hPP := prefixPos_eq_of_labels_openR2 ring hLab front kD.val
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

/-- Strong-R2 version of the P6 residual.  The proof itself consumes R1;
strong R2 is retained in the payload so this theorem composes with P1-P5. -/
theorem openRForwardMainClearOwnerFreshStepV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hElection : ElectionGeometryV31 ring C)
    (_hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR) :
    let D := stepV3 hψ h2 ring C e
    ∀ owner : Fin n,
      (D owner).ctl.tok = .openR →
        (D owner).ctl.mark = .releasing ∧ OpenROwnerFreshV3 ring D owner := by
  dsimp only
  let D := stepV3 hψ h2 ring C e
  change ∀ owner : Fin n, (D owner).ctl.tok = .openR →
    (D owner).ctl.mark = .releasing ∧ OpenROwnerFreshV3 ring D owner
  have hFacts : ReachablePhaseFactsV31 ring C := hPlus.1.1.1.1
  rcases hFacts with ⟨_, _, _, _, _, hOpenOwners⟩
  have hR1 : OpenRForwardMainClearV31 ring C := hPlus.2.2.1
  have hc := branch_openR_conditions_openR2 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hOpenE : (C e).ctl.tok = .openR := hc.2.2.2.2.2
  intro owner hTokD
  by_cases hs : successorB (C e) (C (ring.rightNeighbor e)) = true
  · have hClear := served_mainClear_of_R1_openR2
      ring C e hR1 hOpenE hs
    by_cases hoe : owner = e
    · subst owner
      have hDe : D e = setControl (clearMain (C e)) .open .none := by
        dsimp [D]
        exact openR_step_left_good_openR2 hψ h2 ring C e hb hs
      rw [hDe] at hTokD
      simp [setControl] at hTokD
    · by_cases hor : owner = ring.rightNeighbor e
      · subst owner
        have hDr0 := openR_step_right_good_openR2 hψ h2 ring C e hb hs
        cases ht : atTerminalB (C (ring.rightNeighbor e)) with
        | true =>
            have hDr : D (ring.rightNeighbor e) =
                setControl (clearMain (C (ring.rightNeighbor e))) .open .none := by
              dsimp [D]
              simpa [ht] using hDr0
            rw [hDr] at hTokD
            simp [setControl] at hTokD
        | false =>
            have hDr : D (ring.rightNeighbor e) =
                setControl (clearMain (C (ring.rightNeighbor e)))
                  .releasing .openR := by
              dsimp [D]
              simpa [ht] using hDr0
            have hOldE := hOpenOwners e hOpenE
            constructor
            · rw [hDr]
              rfl
            · exact new_right_ownerFresh_openR_good_openR2
                hψ h2 ring C e hElection hb hs hClear.1 hClear.2 hOldE.2
      · have hEq : D owner = C owner := by
          dsimp [D]
          exact stepV3_other hψ h2 ring C e owner hoe hor
        have hTokC := hTokD
        rw [hEq] at hTokC
        have hOld := hOpenOwners owner hTokC
        constructor
        · rw [hEq]
          exact hOld.1
        · exact old_ownerFresh_openR_good_openR2
            hψ h2 ring C e owner hb hs hClear.1 hClear.2 hOld.2
  · have hsF := bool_false_of_not_true_openR2 _ hs
    by_cases hoe : owner = e
    · subst owner
      have hDe : D e = startClosing (C e) := by
        dsimp [D]
        exact openR_step_left_bad_openR2 hψ h2 ring C e hb hsF
      rw [hDe] at hTokD
      simp [startClosing, setControl] at hTokD
    · have hEq : D owner = C owner := by
        dsimp [D]
        exact openR_step_bad_other_openR2 hψ h2 ring C e owner hb hsF hoe
      have hTokC := hTokD
      rw [hEq] at hTokC
      have hOld := hOpenOwners owner hTokC
      constructor
      · rw [hEq]
        exact hOld.1
      · have hPhys : ∀ p : Fin n, (D p).phys = (C p).phys := by
          intro p
          simpa [D] using openR_bad_phys_eq_openR2 hψ h2 ring C e hb hsF p
        exact openROwnerFresh_of_phys_eq_openR2 ring owner hPhys hOld.2


/-- P1-P5 come from the earlier theorem after projecting strong R2 to ordinary Plus4;
P6 is the theorem above. -/
theorem openRStep_reachable_P1_P6
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hElection : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR) :
    ReachablePhaseFactsP1P6StrongR2V31 ring
      (stepV3 hψ h2 ring C e) := by
  constructor
  · exact R2CoherenceV31ReachableOpenR.openRStep_reachable_P1_P5
      hψ h2 ring C e hElection hTrace
      (plus4_of_strongR2_openR2 ring C hPlus) hb
  · exact openRForwardMainClearOwnerFreshStepV31
      hψ h2 ring C e hPlus hElection hTrace hb

end R2CoherenceV31ReachableOpenR2
