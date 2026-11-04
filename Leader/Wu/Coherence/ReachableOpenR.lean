import Leader.Wu.Coherence.ReachableOwnershipPayload
import Leader.Wu.Coherence.ReachableSweep

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableOpenR

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

variable {n ψ κ τ : Nat}

/-- Plus4 version of the existing sweep/open-no-hazard induction target. -/
def OpenRStepReachablePlus4V31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ReachablePhaseFactsPlus4V31 ring C →
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR →
      ReachablePhaseFactsPlus4V31 ring (stepV3 hψ h2 ring C e)

abbrev openRStep_reachable
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  OpenRStepReachablePlus4V31 (κ := κ) (τ := τ) hψ h2 ring

/-- First five clauses of `ReachablePhaseFactsV31`, kept as one local target
so the first successful block has a compact theorem statement. -/
def ReachablePhaseFactsP1P5V31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  (∀ i : Fin n, (C i).ctl.tok = .sweep →
      SweptPrefixOwnedClearV31 ring C i) ∧
  (∀ i : Fin n, (C i).ctl.tok = .commit →
      GroupOwnedClearV31 ring C i) ∧
  (∀ i : Fin n, (C i).ctl.mark = .sealed →
      GroupOwnedClearV31 ring C i) ∧
  (∀ i : Fin n, (C i).ctl.tok = .release →
      (C i).ctl.mark = .releasing ∧ GroupOwnedClearV31 ring C i) ∧
  (∀ i : Fin n, (C i).ctl.tok = .scrubL →
      (C i).ctl.mark = .releasing ∧
        (raw (C i)).label.val ≠ 0 ∧ GroupOwnedClearV31 ring C i)

private theorem bool_false_of_not_true_openR
    (b : Bool) (h : b ≠ true) : b = false := by
  cases b <;> simp_all

private theorem branch_openR_conditions_reach
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openR) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
      r.ctl.tok ≠ .scrubL ∧ l.ctl.tok = .openR := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowV3_openR_eq_reach
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openR) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = openRStageV3 l r := by
  rcases branch_openR_conditions_reach hψ h2 l r hb with
    ⟨hSeek, hSweep, hCommit, hRelease, hScrub, hOpenR⟩
  simp [rowV3, hSeek, hSweep, hCommit, hRelease, hScrub, hOpenR]

private theorem successor_labels_openR
    (l r : Cell ψ κ τ) (h : successorB l r = true) :
    (raw r).label.val = (raw l).label.val + 1 := by
  simpa [successorB] using h

private theorem edge_distinct_of_successor_openR
    (C : FC n ψ κ τ) (ring : DirectedRing n) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    e ≠ ring.rightNeighbor e := by
  intro h
  have hSame := congrArg (fun p : Fin n => (raw (C p)).label.val) h
  have hSucc := successor_labels_openR
    (C e) (C (ring.rightNeighbor e)) hs
  omega

private theorem openR_step_left_good
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e e =
      setControl (clearMain (C e)) .open .none := by
  have hrow := rowV3_openR_eq_reach hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, openRStageV3, hs]

private theorem openR_step_right_good
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      if atTerminalB (C (ring.rightNeighbor e)) then
        setControl (clearMain (C (ring.rightNeighbor e))) .open .none
      else
        setControl (clearMain (C (ring.rightNeighbor e))) .releasing .openR := by
  have hrow := rowV3_openR_eq_reach hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hne := edge_distinct_of_successor_openR C ring e hs
  have hrne : ring.rightNeighbor e ≠ e := Ne.symm hne
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, openRStageV3, hs, hrne]


private theorem openR_step_left_bad
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false) :
    stepV3 hψ h2 ring C e e = startClosing (C e) := by
  have hrow := rowV3_openR_eq_reach hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, openRStageV3, hs]

private theorem openR_step_bad_other
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false)
    (hi : i ≠ e) :
    stepV3 hψ h2 ring C e i = C i := by
  by_cases hir : i = ring.rightNeighbor e
  · subst i
    have hrow := rowV3_openR_eq_reach hψ h2
      (C e) (C (ring.rightNeighbor e)) hb
    simpa [stepV3, protocolV3, PopulationProtocol.step,
      hrow, openRStageV3, hs, hi]
  · exact stepV3_other hψ h2 ring C e i hi hir

private theorem groupPos_eq_of_labels_openR
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

private theorem mainClear_setControl_iff_openR
    (u : Cell ψ κ τ) (m : R2Coherence.Mark) (t : TokenV3) :
    MainClearV3 (setControl u m t) ↔ MainClearV3 u := by
  simp [MainClearV3, R2CoherenceBranches.MainClear,
    eraseCellV3, setControl, R2Coherence.raw]

private theorem clearMain_mainClear_openR (u : Cell ψ κ τ) :
    MainClearV3 (clearMain u) := by
  unfold MainClearV3 R2CoherenceBranches.MainClear
  simp [eraseCellV3, clearMain, R2Coherence.clearMainPhys,
    PPLLExpiringComparisonRepair.clearComparisonCarrier,
    R2Coherence.raw]

private theorem cleared_control_mainClear_openR
    (u : Cell ψ κ τ) (m : R2Coherence.Mark) (t : TokenV3) :
    MainClearV3 (setControl (clearMain u) m t) := by
  exact (mainClear_setControl_iff_openR (clearMain u) m t).2
    (clearMain_mainClear_openR u)

private theorem startClosing_owned_of_mainClear_openR
    (u : Cell ψ κ τ) (hm : MainClearV3 u) :
    MainClearV3 (startClosing u) ∧ PhaseOwnedV31 (startClosing u) := by
  constructor
  · simpa [startClosing] using
      (mainClear_setControl_iff_openR u .closing .seek).2 hm
  · simp [PhaseOwnedV31, startClosing, setControl]

private def SurvivingOwnedPhaseV31
    (C : FC n ψ κ τ) (owner : Fin n) : Prop :=
  (C owner).ctl.tok = .sweep ∨ CarriesGroupOwnedPhaseV31 C owner

private theorem surviving_owned_phase_good_openR
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hPost : SurvivingOwnedPhaseV31
      (stepV3 hψ h2 ring C e) owner) :
    owner ≠ e ∧ owner ≠ ring.rightNeighbor e ∧
      stepV3 hψ h2 ring C e owner = C owner := by
  have hLeft := openR_step_left_good hψ h2 ring C e hb hs
  have hRight := openR_step_right_good hψ h2 ring C e hb hs
  have hoe : owner ≠ e := by
    intro h
    subst owner
    unfold SurvivingOwnedPhaseV31 CarriesGroupOwnedPhaseV31 at hPost
    rw [hLeft] at hPost
    simp [setControl] at hPost
  have hor : owner ≠ ring.rightNeighbor e := by
    intro h
    subst owner
    unfold SurvivingOwnedPhaseV31 CarriesGroupOwnedPhaseV31 at hPost
    rw [hRight] at hPost
    cases ht : atTerminalB (C (ring.rightNeighbor e)) <;>
      simp [ht, setControl] at hPost
  exact ⟨hoe, hor, stepV3_other hψ h2 ring C e owner hoe hor⟩



private theorem surviving_owned_phase_bad_openR
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false)
    (hPost : SurvivingOwnedPhaseV31
      (stepV3 hψ h2 ring C e) owner) :
    owner ≠ e ∧ stepV3 hψ h2 ring C e owner = C owner := by
  have hLeft := openR_step_left_bad hψ h2 ring C e hb hs
  have hoe : owner ≠ e := by
    intro h
    subst owner
    unfold SurvivingOwnedPhaseV31 CarriesGroupOwnedPhaseV31 at hPost
    rw [hLeft] at hPost
    simp [startClosing, setControl] at hPost
  exact ⟨hoe, openR_step_bad_other hψ h2 ring C e owner hb hs hoe⟩



private theorem surviving_owned_phase_frame_openR
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hPost : SurvivingOwnedPhaseV31
      (stepV3 hψ h2 ring C e) owner) :
    stepV3 hψ h2 ring C e owner = C owner := by
  by_cases hs : successorB (C e) (C (ring.rightNeighbor e)) = true
  · exact (surviving_owned_phase_good_openR
      hψ h2 ring C e owner hb hs hPost).2.2
  · have hsF := bool_false_of_not_true_openR _ hs
    exact (surviving_owned_phase_bad_openR
      hψ h2 ring C e owner hb hsF hPost).2


private theorem sweptPrefix_frame_openR
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hR2 : OpenRPhaseOwnershipDisjointV31 ring C)
    (hOld : SweptPrefixOwnedClearV31 ring C owner)
    (hPost : (stepV3 hψ h2 ring C e owner).ctl.tok = .sweep) :
    SweptPrefixOwnedClearV31 ring (stepV3 hψ h2 ring C e) owner := by
  let D := stepV3 hψ h2 ring C e
  have hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label := by
    intro p
    simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  unfold SweptPrefixOwnedClearV31 at hOld ⊢
  intro kD
  dsimp only
  have hv := congrArg Fin.val (hLab owner)
  have hkC : kD.val < (raw (C owner)).label.val := by
    rw [← hv]
    exact kD.isLt
  let kC : Fin (raw (C owner)).label.val := ⟨kD.val, hkC⟩
  let p := R2Coherence.groupPos ring (eraseCfgV3 C) owner kD.val
  have hPrev : MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) := by
    simpa [p, kC] using hOld kC
  have hPos := groupPos_eq_of_labels_openR ring hLab owner kD.val
  rw [hPos]
  change MainClearV3 (D p) ∧ PhaseOwnedV31 (D p)
  by_cases hs : successorB (C e) (C (ring.rightNeighbor e)) = true
  · have hGood := surviving_owned_phase_good_openR hψ h2 ring C e owner hb hs
      (Or.inl hPost)
    have hPreSweep := hPost
    rw [hGood.2.2] at hPreSweep
    rcases branch_openR_conditions_reach hψ h2
      (C e) (C (ring.rightNeighbor e)) hb with
      ⟨_, _, _, _, _, hOpenR⟩
    have hDis := hR2 e owner hOpenR hs hGood.2.1
    by_cases hpe : p = e
    · have hFoot : InSweptOwnedFootprintV31 ring C owner e :=
        ⟨kC, by simpa [p, kC] using hpe⟩
      exact ((hDis.1 hPreSweep) hFoot).elim
    · by_cases hpr : p = ring.rightNeighbor e
      · cases ht : atTerminalB (C (ring.rightNeighbor e)) with
        | true =>
            have hFoot : InSweptOwnedFootprintV31 ring C owner
                (ring.rightNeighbor e) :=
              ⟨kC, by simpa [p, kC] using hpr⟩
            exact (((hDis.2.2 ht).1 hPreSweep) hFoot).elim
        | false =>
            have hRight := openR_step_right_good hψ h2 ring C e hb hs
            rw [hpr]
            change MainClearV3
                (stepV3 hψ h2 ring C e (ring.rightNeighbor e)) ∧
              PhaseOwnedV31
                (stepV3 hψ h2 ring C e (ring.rightNeighbor e))
            rw [hRight]
            simpa [ht] using And.intro
              (cleared_control_mainClear_openR
                (C (ring.rightNeighbor e)) .releasing .openR)
              (show PhaseOwnedV31
                  (setControl (clearMain (C (ring.rightNeighbor e)))
                    .releasing .openR) by
                simp [PhaseOwnedV31, setControl])
      · have hp := stepV3_other hψ h2 ring C e p hpe hpr
        simpa [D, hp] using hPrev
  · have hsF := bool_false_of_not_true_openR _ hs
    have hBad := surviving_owned_phase_bad_openR hψ h2 ring C e owner hb hsF
      (Or.inl hPost)
    by_cases hpe : p = e
    · have hLeft := openR_step_left_bad hψ h2 ring C e hb hsF
      have hm : MainClearV3 (C e) := by simpa [hpe] using hPrev.1
      rw [hpe, show D e = stepV3 hψ h2 ring C e e by rfl, hLeft]
      exact startClosing_owned_of_mainClear_openR (C e) hm
    · have hp := openR_step_bad_other hψ h2 ring C e p hb hsF hpe
      simpa [D, hp] using hPrev



private theorem groupOwned_frame_openR
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hR2 : OpenRPhaseOwnershipDisjointV31 ring C)
    (hOld : GroupOwnedClearV31 ring C owner)
    (hPost : CarriesGroupOwnedPhaseV31 (stepV3 hψ h2 ring C e) owner) :
    GroupOwnedClearV31 ring (stepV3 hψ h2 ring C e) owner := by
  let D := stepV3 hψ h2 ring C e
  have hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label := by
    intro p
    simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  have hFrame := surviving_owned_phase_frame_openR hψ h2 ring C e owner hb
    (Or.inr hPost)
  have hPreCarry := hPost
  unfold CarriesGroupOwnedPhaseV31 at hPreCarry
  rw [hFrame] at hPreCarry
  unfold GroupOwnedClearV31 at hOld ⊢
  intro k
  dsimp only
  let p := R2Coherence.groupPos ring (eraseCfgV3 C) owner k.val
  have hPrev : MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) := by
    simpa [p] using hOld k
  have hPos := groupPos_eq_of_labels_openR ring hLab owner k.val
  rw [hPos]
  change MainClearV3 (D p) ∧ PhaseOwnedV31 (D p)
  by_cases hs : successorB (C e) (C (ring.rightNeighbor e)) = true
  · have hGood := surviving_owned_phase_good_openR hψ h2 ring C e owner hb hs
      (Or.inr hPost)
    rcases branch_openR_conditions_reach hψ h2
      (C e) (C (ring.rightNeighbor e)) hb with
      ⟨_, _, _, _, _, hOpenR⟩
    have hDis := hR2 e owner hOpenR hs hGood.2.1
    by_cases hpe : p = e
    · have hFoot : InGroupOwnedFootprintV31 ring C owner e :=
        ⟨k, by simpa [p] using hpe⟩
      exact ((hDis.2.1 hPreCarry) hFoot).elim
    · by_cases hpr : p = ring.rightNeighbor e
      · cases ht : atTerminalB (C (ring.rightNeighbor e)) with
        | true =>
            have hFoot : InGroupOwnedFootprintV31 ring C owner
                (ring.rightNeighbor e) :=
              ⟨k, by simpa [p] using hpr⟩
            exact (((hDis.2.2 ht).2 hPreCarry) hFoot).elim
        | false =>
            have hRight := openR_step_right_good hψ h2 ring C e hb hs
            rw [hpr]
            change MainClearV3
                (stepV3 hψ h2 ring C e (ring.rightNeighbor e)) ∧
              PhaseOwnedV31
                (stepV3 hψ h2 ring C e (ring.rightNeighbor e))
            rw [hRight]
            simpa [ht] using And.intro
              (cleared_control_mainClear_openR
                (C (ring.rightNeighbor e)) .releasing .openR)
              (show PhaseOwnedV31
                  (setControl (clearMain (C (ring.rightNeighbor e)))
                    .releasing .openR) by
                simp [PhaseOwnedV31, setControl])
      · have hp := stepV3_other hψ h2 ring C e p hpe hpr
        simpa [D, hp] using hPrev
  · have hsF := bool_false_of_not_true_openR _ hs
    by_cases hpe : p = e
    · have hLeft := openR_step_left_bad hψ h2 ring C e hb hsF
      have hm : MainClearV3 (C e) := by simpa [hpe] using hPrev.1
      rw [hpe, show D e = stepV3 hψ h2 ring C e e by rfl, hLeft]
      exact startClosing_owned_of_mainClear_openR (C e) hm
    · have hp := openR_step_bad_other hψ h2 ring C e p hb hsF hpe
      simpa [D, hp] using hPrev


/-- P1-P5 close from Plus4.  R2 is consumed exactly at the served cells on the
good arm; the bad arm is physical-state inert and only makes the left control
more strongly owned. -/
theorem openRStep_reachable_P1_P5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (_hElection : ElectionGeometryV31 ring C)
    (_hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus4 : ReachablePhaseFactsPlus4V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR) :
    ReachablePhaseFactsP1P5V31 ring (stepV3 hψ h2 ring C e) := by
  rcases hPlus4 with ⟨hPlus3, _hS, _hR1, hR2⟩
  rcases hPlus3 with ⟨hPlus2, _hWide⟩
  rcases hPlus2 with ⟨hPlus, _hOverlap⟩
  rcases hPlus with ⟨hFacts, _hIncomingFresh⟩
  rcases hFacts with
    ⟨hSweep, hCommit, hSealed, hRelease, hScrub, _hOpenR⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hFrame := surviving_owned_phase_frame_openR
      hψ h2 ring C e i hb (Or.inl hi)
    have hiC := hi
    rw [hFrame] at hiC
    exact sweptPrefix_frame_openR
      hψ h2 ring C e i hb hR2 (hSweep i hiC) hi
  · intro i hi
    have hCarryD :
        CarriesGroupOwnedPhaseV31 (stepV3 hψ h2 ring C e) i := Or.inl hi
    have hFrame := surviving_owned_phase_frame_openR
      hψ h2 ring C e i hb (Or.inr hCarryD)
    have hiC := hi
    rw [hFrame] at hiC
    exact groupOwned_frame_openR
      hψ h2 ring C e i hb hR2 (hCommit i hiC) hCarryD
  · intro i hi
    have hCarryD :
        CarriesGroupOwnedPhaseV31 (stepV3 hψ h2 ring C e) i :=
      Or.inr (Or.inl hi)
    have hFrame := surviving_owned_phase_frame_openR
      hψ h2 ring C e i hb (Or.inr hCarryD)
    have hiC := hi
    rw [hFrame] at hiC
    exact groupOwned_frame_openR
      hψ h2 ring C e i hb hR2 (hSealed i hiC) hCarryD
  · intro i hi
    have hCarryD :
        CarriesGroupOwnedPhaseV31 (stepV3 hψ h2 ring C e) i :=
      Or.inr (Or.inr (Or.inl hi))
    have hFrame := surviving_owned_phase_frame_openR
      hψ h2 ring C e i hb (Or.inr hCarryD)
    have hiC := hi
    rw [hFrame] at hiC
    have hOld := hRelease i hiC
    constructor
    · rw [hFrame]
      exact hOld.1
    · exact groupOwned_frame_openR
        hψ h2 ring C e i hb hR2 hOld.2 hCarryD
  · intro i hi
    have hCarryD :
        CarriesGroupOwnedPhaseV31 (stepV3 hψ h2 ring C e) i :=
      Or.inr (Or.inr (Or.inr hi))
    have hFrame := surviving_owned_phase_frame_openR
      hψ h2 ring C e i hb (Or.inr hCarryD)
    have hiC := hi
    rw [hFrame] at hiC
    have hOld := hScrub i hiC
    refine ⟨?_, ?_, ?_⟩
    · rw [hFrame]
      exact hOld.1
    · rw [hFrame]
      exact hOld.2.1
    · exact groupOwned_frame_openR
        hψ h2 ring C e i hb hR2 hOld.2.2 hCarryD

/-- First unclosed clause (P6).

On a good OPEN-R service both served physical main carriers are cleared and,
on the nonterminal arm, the `.openR` owner advances from `e` to
`ring.rightNeighbor e`.  Plus4/R1 supplies that the forward suffix of the old
owner was already `MainClearV3`; that is exactly the semantic input needed to
show that clearing the served cells cannot invalidate any surviving
`OpenROwnerFreshV3` proof.  The new right-owner case additionally needs the
non-root-window/predecessor arithmetic that identifies every arithmetic window
containing the new owner with one that already contained the old owner.

Current main contains both proof patterns only as private helpers:
`freshComponent_false_of_mainClear_plus2` / the sweep owner-fresh transport in
`R2CoherenceV31ReachablePlus2.lean`, and
`nonroot_window_contains_predecessor_reach` in
`R2CoherenceV31ReachableOpenNoHazard.lean`.  This proposition names exactly the
missing P6 transport without pretending that those private declarations are
available to this importing module. -/
def OpenRForwardMainClearOwnerFreshStepV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ReachablePhaseFactsPlus4V31 ring C →
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR →
    let D := stepV3 hψ h2 ring C e
    ∀ owner : Fin n,
      (D owner).ctl.tok = .openR →
        (D owner).ctl.mark = .releasing ∧
          OpenROwnerFreshV3 ring D owner

/-
STOP at P6.

P1-P5 are discharged above, consuming R2 on the good OPEN-R arm exactly where
`clearMain` would otherwise erase a surviving phase-owned cell.  P6 is the
first clause for which the present public API does not expose the required
R1-based freshness transport/new-owner arithmetic.  Therefore, as requested,
P7-P9, S, R1 self-preservation, R2 self-preservation, and the final theorem
`openRStep_reachable` are not asserted in this round.
-/

end R2CoherenceV31ReachableOpenR
