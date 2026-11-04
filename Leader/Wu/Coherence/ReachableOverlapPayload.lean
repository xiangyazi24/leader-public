import Leader.Wu.Coherence.ReachableHandoffPayload

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachablePlus2

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
open R2CoherenceV31ReachableOpenNoHazard
open R2CoherenceV31ReachablePlus

variable {n ψ κ τ : Nat}

/-- A root which would become the next `openR` owner if the `scrubL`
on its right is served. -/
def PendingOpenROwnerV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) (owner : Fin n) : Prop :=
  (C (ring.rightNeighbor owner)).ctl.tok = .scrubL ∧
    successorB (C owner) (C (ring.rightNeighbor owner)) = true ∧
    atRootB (C owner) = true

/-- Exact physical footprint which `OpenROwnerFreshV3 ring C owner`
can read. -/
def InOpenRFreshFootprintV31
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (owner p : Fin n) : Prop :=
  ∃ (j : Fin n) (ko q : Fin ψ),
    R2Coherence.groupPos ring (eraseCfgV3 C) j ko.val = owner ∧
      ∃ k : Fin
          ((raw (C
            (R2Coherence.groupPos ring (eraseCfgV3 C) j q.val))).label.val + 1),
        R2Coherence.prefixPos ring (eraseCfgV3 C)
            (R2Coherence.groupPos ring (eraseCfgV3 C) j q.val) k.val = p

/-- Every cell which this sweep may clear is either already main-clear or
outside every freshness read belonging to every pending owner it overlaps. -/
def SweepOpenROverlapClearV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (e owner : Fin n),
    (C e).ctl.tok = .sweep →
    PendingOpenROwnerV31 ring C owner →
      (MainClearV3 (C e) ∨
        ¬ InOpenRFreshFootprintV31 ring C owner e) ∧
      (MainClearV3 (C (ring.rightNeighbor e)) ∨
        ¬ InOpenRFreshFootprintV31
          ring C owner (ring.rightNeighbor e))

def ReachablePhaseFactsPlus2V31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ReachablePhaseFactsPlusV31 ring C ∧
    SweepOpenROverlapClearV31 ring C

/-- Entrance is vacuous: `quarantineInitV31` installs `.none` tokens at every
cell (`Leader/Wu/Coherence/BirthQuarantine.lean:21-25`). -/
theorem sweepOpenROverlapClear_quarantineInit
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    SweepOpenROverlapClearV31 ring (quarantineInitV31 C) := by
  intro e owner hSweep _
  simp [quarantineInitV31, setControl] at hSweep

theorem reachablePhaseFactsPlus2_entrance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ)
    (hBirth : BirthEntranceV1 hψ h2 ring C) :
    ReachablePhaseFactsPlus2V31 ring C := by
  constructor
  · exact reachablePhaseFactsPlus_entrance hψ h2 ring C hBirth
  · rcases hBirth.1 with ⟨_, D, _, hEq⟩
    rw [hEq]
    exact sweepOpenROverlapClear_quarantineInit ring D

private theorem bool_false_of_not_true_plus2
    (b : Bool) (h : b ≠ true) : b = false := by
  cases b <;> simp_all

private theorem branch_sweep_conditions_plus2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .sweep) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok = .sweep := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowV3_sweep_eq_plus2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .sweep) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = sweepStageV3 l r := by
  rcases branch_sweep_conditions_plus2 hψ h2 l r hb with
    ⟨hSeek, hSweep⟩
  simp [rowV3, hSeek, hSweep]

private theorem successor_labels_plus2
    (l r : Cell ψ κ τ) (h : successorB l r = true) :
    (raw r).label.val = (raw l).label.val + 1 := by
  simpa [successorB] using h

private theorem edge_distinct_of_successor_plus2
    (C : FC n ψ κ τ) (ring : DirectedRing n) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    e ≠ ring.rightNeighbor e := by
  intro h
  have hSame := congrArg (fun p : Fin n => (raw (C p)).label.val) h
  have hSucc := successor_labels_plus2
    (C e) (C (ring.rightNeighbor e)) hs
  omega

private theorem sweep_step_left_good_plus2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e e =
      setControl (clearMain (C e)) .closing .none := by
  have hrow := rowV3_sweep_eq_plus2 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, sweepStageV3, hs]

private theorem sweep_step_right_good_plus2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      setControl (clearMain (C (ring.rightNeighbor e))) .closing
        (if atTerminalB (C (ring.rightNeighbor e))
          then .commit else .sweep) := by
  have hrow := rowV3_sweep_eq_plus2 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hne := edge_distinct_of_successor_plus2 C ring e hs
  have hrne : ring.rightNeighbor e ≠ e := Ne.symm hne
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, sweepStageV3, hs, hrne]

private theorem sweep_step_left_bad_plus2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false) :
    stepV3 hψ h2 ring C e e = startClosing (C e) := by
  have hrow := rowV3_sweep_eq_plus2 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, sweepStageV3, hs]

private theorem sweep_step_bad_other_plus2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false)
    (hi : i ≠ e) :
    stepV3 hψ h2 ring C e i = C i := by
  by_cases hij : i = ring.rightNeighbor e
  · subst i
    have hrow := rowV3_sweep_eq_plus2 hψ h2
      (C e) (C (ring.rightNeighbor e)) hb
    simpa [stepV3, protocolV3, PopulationProtocol.step,
      hrow, sweepStageV3, hs, hi]
  · exact stepV3_other hψ h2 ring C e i hi hij


private theorem groupPos_eq_of_labels_plus2
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

private theorem prefixPos_eq_of_labels_plus2
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

private theorem freshComponent_false_of_mainClear_plus2
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
  have hPath : (raw u).path = .bot := by
    exact hm.2.1
  rw [hPath] at hf
  exact hf.2

private theorem sweep_bad_phys_eq_plus2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false) :
    ∀ p : Fin n,
      (stepV3 hψ h2 ring C e p).phys = (C p).phys := by
  intro p
  by_cases hpe : p = e
  · subst p
    rw [sweep_step_left_bad_plus2 hψ h2 ring C e hb hs]
    simp [startClosing, setControl]
  · rw [sweep_step_bad_other_plus2 hψ h2 ring C e p hb hs hpe]

private theorem openROwnerFresh_of_phys_eq_plus2
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
  have hGPko := groupPos_eq_of_labels_plus2 ring hLab j ko.val
  rw [hGPko] at hHitD
  have hOldGroup := hFresh j ko hHitD
  unfold GroupIntrinsicFreshV3 at hOldGroup ⊢
  intro q
  have hGPq := groupPos_eq_of_labels_plus2 ring hLab j q.val
  rw [hGPq]
  let front :=
    R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
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
    have hk : m < (raw (D front)).label.val + 1 := by
      exact kD.isLt
    have hk' : m < (raw (C front)).label.val + 1 := by
      simpa only [hLabelVal] using hk
    exact hk'
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hkC⟩
  have hOldK := hOldAt kC
  have hPP := prefixPos_eq_of_labels_plus2 ring hLab front kD.val
  rw [hPP]
  let p := R2Coherence.prefixPos ring
    (eraseCfgV3 C) front kD.val
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

/-- The pointwise clause is exactly sufficient to transport a pending owner's
freshness through one sweep.  Labels are globally preserved by
`stepV3_labels_eq_or_held`
(`Leader/Wu/Coherence/LabelPreservation.lean:326-344`). -/
theorem sweep_preserves_pending_owner_fresh_of_overlapClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hOverlap : SweepOpenROverlapClearV31 ring C)
    (hPending : PendingOpenROwnerV31 ring C owner)
    (hFresh : OpenROwnerFreshV3 ring C owner)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep) :
    OpenROwnerFreshV3 ring (stepV3 hψ h2 ring C e) owner := by
  let D := stepV3 hψ h2 ring C e
  have hc := branch_sweep_conditions_plus2 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hSweep : (C e).ctl.tok = .sweep := hc.2
  have hSafe := hOverlap e owner hSweep hPending
  by_cases hsT :
      successorB (C e) (C (ring.rightNeighbor e)) = true
  · have hLab : ∀ p : Fin n,
        (raw (D p)).label = (raw (C p)).label := by
      intro p
      simpa [D] using
        (stepV3_labels_eq_or_held hψ h2 ring C e p)
    have hStateE : (raw (D e)).state = .none := by
      rw [show D e = stepV3 hψ h2 ring C e e by rfl,
        sweep_step_left_good_plus2 hψ h2 ring C e hb hsT]
      simp [setControl, clearMain, raw]
    have hStateR :
        (raw (D (ring.rightNeighbor e))).state = .none := by
      rw [show D (ring.rightNeighbor e) =
          stepV3 hψ h2 ring C e (ring.rightNeighbor e) by rfl,
        sweep_step_right_good_plus2 hψ h2 ring C e hb hsT]
      simp [setControl, clearMain, raw]
    unfold OpenROwnerFreshV3 at hFresh ⊢
    intro j ko hHitD
    have hGPko := groupPos_eq_of_labels_plus2 ring hLab j ko.val
    rw [hGPko] at hHitD
    have hOldGroup := hFresh j ko hHitD
    unfold GroupIntrinsicFreshV3 at hOldGroup ⊢
    intro q
    have hGPq := groupPos_eq_of_labels_plus2 ring hLab j q.val
    rw [hGPq]
    let front :=
      R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
    change IntrinsicFreshAtV3 ring D front
    unfold IntrinsicFreshAtV3
    intro hEqD
    by_cases hfe : front = e
    · have hx := hEqD
      rw [hfe, hStateE] at hx
      cases hx
    · by_cases hfr : front = ring.rightNeighbor e
      · have hx := hEqD
        rw [hfr, hStateR] at hx
        cases hx
      · have hFrontEq : D front = C front := by
          dsimp [D]
          exact stepV3_other hψ h2 ring C e front hfe hfr
        have hEqC : (raw (C front)).state = .equal := by
          simpa [hFrontEq] using hEqD
        have hOldAt := (hOldGroup q) hEqC
        rw [hLab front]
        intro k
        have hOldK := hOldAt k
        have hPP := prefixPos_eq_of_labels_plus2
          ring hLab front k.val
        rw [hPP]
        let p := R2Coherence.prefixPos ring
          (eraseCfgV3 C) front k.val
        change R2Coherence.freshComponent (eraseCellV3 (D p)) k.val
        by_cases hpe : p = e
        · rcases hSafe.1 with hm | hout
          · exact (freshComponent_false_of_mainClear_plus2
              (C p) k.val (by simpa [hpe] using hm)
              (by simpa [p] using hOldK)).elim
          · exfalso
            apply hout
            refine ⟨j, ko, q, hHitD, ?_⟩
            refine ⟨k, ?_⟩
            simpa [p, front] using hpe
        · by_cases hpr : p = ring.rightNeighbor e
          · rcases hSafe.2 with hm | hout
            · exact (freshComponent_false_of_mainClear_plus2
                (C p) k.val (by simpa [hpr] using hm)
                (by simpa [p] using hOldK)).elim
            · exfalso
              apply hout
              refine ⟨j, ko, q, hHitD, ?_⟩
              refine ⟨k, ?_⟩
              simpa [p, front] using hpr
          · have hDp : D p = C p := by
              dsimp [D]
              exact stepV3_other hψ h2 ring C e p hpe hpr
            simpa [hDp, p] using hOldK
  · have hsF := bool_false_of_not_true_plus2 _ hsT
    apply openROwnerFresh_of_phys_eq_plus2
      ring owner ?_ hFresh
    intro p
    exact sweep_bad_phys_eq_plus2 hψ h2 ring C e hb hsF p


/-- A post-sweep `scrubL` token was already present before the sweep:
a good sweep writes only `none/sweep/commit`, while a bad sweep writes only
`seek` on the left and holds every other cell. -/
private theorem scrubL_after_sweep_was_before_plus2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hPost : (stepV3 hψ h2 ring C e p).ctl.tok = .scrubL) :
    (C p).ctl.tok = .scrubL := by
  by_cases hsT :
      successorB (C e) (C (ring.rightNeighbor e)) = true
  · by_cases hpe : p = e
    · subst p
      rw [sweep_step_left_good_plus2 hψ h2 ring C e hb hsT] at hPost
      simp [setControl] at hPost
    · by_cases hpr : p = ring.rightNeighbor e
      · subst p
        rw [sweep_step_right_good_plus2 hψ h2 ring C e hb hsT] at hPost
        cases ht : atTerminalB (C (ring.rightNeighbor e)) <;>
          simp [setControl, ht] at hPost
      · rw [stepV3_other hψ h2 ring C e p hpe hpr] at hPost
        exact hPost
  · have hsF := bool_false_of_not_true_plus2 _ hsT
    by_cases hpe : p = e
    · subst p
      rw [sweep_step_left_bad_plus2 hψ h2 ring C e hb hsF] at hPost
      simp [startClosing, setControl] at hPost
    · rw [sweep_step_bad_other_plus2
        hψ h2 ring C e p hb hsF hpe] at hPost
      exact hPost

private theorem pendingOpenR_before_sweep_plus2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hScrub :
      (stepV3 hψ h2 ring C e
        (ring.rightNeighbor owner)).ctl.tok = .scrubL)
    (hSucc :
      successorB
        (stepV3 hψ h2 ring C e owner)
        (stepV3 hψ h2 ring C e (ring.rightNeighbor owner)) = true)
    (hRoot : atRootB (stepV3 hψ h2 ring C e owner) = true) :
    PendingOpenROwnerV31 ring C owner := by
  have hLab := stepV3_labels_eq_or_held hψ h2 ring C e
  refine ⟨?_, ?_, ?_⟩
  · exact scrubL_after_sweep_was_before_plus2
      hψ h2 ring C e (ring.rightNeighbor owner) hb hScrub
  · unfold successorB at hSucc ⊢
    simpa [hLab owner, hLab (ring.rightNeighbor owner)] using hSucc
  · unfold atRootB at hRoot ⊢
    simpa [hLab owner] using hRoot

/-- Local induction form: the Plus2 conjunct closes the pending-owner
sweep gap. -/
theorem sweepStep_preserves_scrubLIncoming_plus2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hPlus : ReachablePhaseFactsPlus2V31 ring C)
    (_hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hb : branchAtV3 hψ h2
      (C e) (C (ring.rightNeighbor e)) = .sweep) :
    ScrubLIncomingOpenRFreshV31 ring
      (stepV3 hψ h2 ring C e) := by
  intro owner hScrub hSucc hRoot
  have hPending := pendingOpenR_before_sweep_plus2
    hψ h2 ring C e owner hb hScrub hSucc hRoot
  have hFresh := hPlus.1.2 owner
    hPending.1 hPending.2.1 hPending.2.2
  exact sweep_preserves_pending_owner_fresh_of_overlapClear
    hψ h2 ring C e owner hPlus.2 hPending hFresh hb

/-- Exact discharge of the named transport interface once the new
pointwise invariant is known on reachable prestates. -/
theorem sweepPendingOpenRFreshTransport_of_overlapClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hOverlap :
      ∀ C : FC n ψ κ τ,
        ReachableFromQuarantineV31 hψ h2 ring C →
          SweepOpenROverlapClearV31 ring C) :
    SweepPendingOpenRFreshTransportV31
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e owner hTrace _hFacts hIncoming hb hScrub hSucc hRoot
  have hPending := pendingOpenR_before_sweep_plus2
    hψ h2 ring C e owner hb hScrub hSucc hRoot
  have hFresh := hIncoming owner
    hPending.1 hPending.2.1 hPending.2.2
  exact sweep_preserves_pending_owner_fresh_of_overlapClear
    hψ h2 ring C e owner (hOverlap C hTrace) hPending hFresh hb

/-- Still-open preservation leaf for the *new pointwise conjunct itself*.
After a good sweep the sweep token advances to the responder, but its next
responder is a third cell which was not one of the two cells just cleared.
The pre-state clause for the old sweep edge therefore does not by itself say
that this third cell is clear/outside the pending owner's freshness footprint.
This is the next invariant-strengthening target; no `sorry` is introduced. -/
def SweepOverlapClearSweepPreservationV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ReachablePhaseFactsPlus2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep →
      SweepOpenROverlapClearV31 ring
        (stepV3 hψ h2 ring C e)

end R2CoherenceV31ReachablePlus2
