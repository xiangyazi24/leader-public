import Leader.Wu.Coherence.ReachableOpenRIncomingSeek
import Leader.Wu.Coherence.FreshPayload

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableOpenRTail

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure2
open R2CoherenceV31ReachablePlus2 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard3
open R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31MainClearTruth R2CoherenceV31FreshnessClear
open R2CoherenceV31PhaseMainClear

variable {n ψ κ τ : Nat}

private theorem boolFalseT (b : Bool) (h : b ≠ true) : b = false := by
  cases b <;> simp_all

private theorem openRCondsT
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openR) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
    r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
    r.ctl.tok ≠ .scrubL ∧ l.ctl.tok = .openR := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowOpenRT
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openR) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = openRStageV3 l r := by
  rcases openRCondsT hψ h2 l r hb with ⟨hs, _, hc, _, hsl, ho⟩
  simp [rowV3, hs, hc, hsl, ho]

private theorem succLabelsT (l r : Cell ψ κ τ)
    (h : successorB l r = true) :
    (raw r).label.val = (raw l).label.val + 1 := by
  simpa [successorB] using h

private theorem edgeNeT (C : FC n ψ κ τ) (ring : DirectedRing n)
    (e : Fin n) (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    e ≠ ring.rightNeighbor e := by
  intro h
  have hv := congrArg (fun p : Fin n => (raw (C p)).label.val) h
  have hs' := succLabelsT (C e) (C (ring.rightNeighbor e)) hs
  omega

private theorem leftGoodT
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e e =
      setControl (clearMain (C e)) .open .none := by
  have hr := rowOpenRT hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hr, openRStageV3, hs]

private theorem rightGoodT
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      if atTerminalB (C (ring.rightNeighbor e)) then
        setControl (clearMain (C (ring.rightNeighbor e))) .open .none
      else
        setControl (clearMain (C (ring.rightNeighbor e))) .releasing .openR := by
  have hr := rowOpenRT hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  have hn := Ne.symm (edgeNeT C ring e hs)
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hr, openRStageV3, hs, hn]

private theorem leftBadT
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false) :
    stepV3 hψ h2 ring C e e = startClosing (C e) := by
  have hr := rowOpenRT hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hr, openRStageV3, hs]

private theorem badOtherT
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false)
    (hp : p ≠ e) : stepV3 hψ h2 ring C e p = C p := by
  by_cases hr : p = ring.rightNeighbor e
  · subst p
    have hw := rowOpenRT hψ h2 (C e) (C (ring.rightNeighbor e)) hb
    simpa [stepV3, protocolV3, PopulationProtocol.step,
      hw, openRStageV3, hs, hp]
  · exact stepV3_other hψ h2 ring C e p hp hr


private theorem clearFreshT
    (u : Cell ψ κ τ) (m : R2Coherence.Mark) (t : TokenV3) :
    FreshnessClearV31 (setControl (clearMain u) m t) := by
  apply freshnessClear_of_mainClear
  unfold MainClearV3 R2CoherenceBranches.MainClear
  simp [eraseCellV3, setControl, clearMain, R2Coherence.clearMainPhys,
    PPLLExpiringComparisonRepair.clearComparisonCarrier, R2Coherence.raw]

private theorem startFreshT
    (u : Cell ψ κ τ) (h : FreshnessClearV31 u) :
    FreshnessClearV31 (startClosing u) := by
  unfold FreshnessClearV31 at h ⊢
  simpa [startClosing, setControl, raw] using h

private theorem freshStepT
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (h : FreshnessClearV31 (C p)) :
    FreshnessClearV31 (stepV3 hψ h2 ring C e p) := by
  by_cases hs : successorB (C e) (C (ring.rightNeighbor e)) = true
  · by_cases hp : p = e
    · subst p
      rw [leftGoodT hψ h2 ring C e hb hs]
      exact clearFreshT _ .open .none
    · by_cases hr : p = ring.rightNeighbor e
      · subst p
        rw [rightGoodT hψ h2 ring C e hb hs]
        cases ht : atTerminalB (C (ring.rightNeighbor e)) with
        | true => simpa [ht] using clearFreshT (C (ring.rightNeighbor e)) .open .none
        | false => simpa [ht] using clearFreshT (C (ring.rightNeighbor e)) .releasing .openR
      · rw [stepV3_other hψ h2 ring C e p hp hr]
        exact h
  · have hsF := boolFalseT _ hs
    by_cases hp : p = e
    · subst p
      rw [leftBadT hψ h2 ring C e hb hsF]
      exact startFreshT _ h
    · rw [badOtherT hψ h2 ring C e p hb hsF hp]
      exact h

private theorem openRSourceT
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (ht : (stepV3 hψ h2 ring C e p).ctl.tok = .openR) :
    stepV3 hψ h2 ring C e p = C p ∨
      (successorB (C e) (C (ring.rightNeighbor e)) = true ∧
       p = ring.rightNeighbor e) := by
  by_cases hs : successorB (C e) (C (ring.rightNeighbor e)) = true
  · by_cases hp : p = e
    · subst p
      rw [leftGoodT hψ h2 ring C e hb hs] at ht
      simp [setControl] at ht
    · by_cases hr : p = ring.rightNeighbor e
      · exact Or.inr ⟨hs, hr⟩
      · exact Or.inl (stepV3_other hψ h2 ring C e p hp hr)
  · have hsF := boolFalseT _ hs
    by_cases hp : p = e
    · subst p
      rw [leftBadT hψ h2 ring C e hb hsF] at ht
      simp [startClosing, setControl] at ht
    · exact Or.inl (badOtherT hψ h2 ring C e p hb hsF hp)

private theorem modLT (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

private theorem fwdRnT (ring : DirectedRing n) (i : Fin n) (d : Nat) :
    R2Coherence.fwd ring (ring.rightNeighbor i) d =
      R2Coherence.fwd ring i (d + 1) := by
  apply Fin.ext
  unfold R2Coherence.fwd DirectedRing.rightNeighbor
  dsimp only
  rw [modLT]
  congr 1
  omega

/-- Fresh R1 tail for one OPEN-R service. -/
theorem openRForwardFreshnessClear_openR_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hR1 : OpenRForwardFreshnessClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR) :
    OpenRForwardFreshnessClearV31 ring (stepV3 hψ h2 ring C e) := by
  have hLab := stepV3_labels_eq_or_held hψ h2 ring C e
  have hOpenE := (openRCondsT hψ h2 (C e) (C (ring.rightNeighbor e)) hb).2.2.2.2.2
  intro o hOpenD dD
  rcases openRSourceT hψ h2 ring C e o hb hOpenD with hEq | ⟨hs, ho⟩
  · have hOpenC : (C o).ctl.tok = .openR := by rw [← hEq]; exact hOpenD
    have hv := congrArg Fin.val (hLab o)
    have hd : dD.val < ψ - (raw (C o)).label.val := by
      simpa only [hv] using dD.isLt
    let dC : Fin (ψ - (raw (C o)).label.val) := ⟨dD.val, hd⟩
    exact freshStepT hψ h2 ring C e _ hb (by simpa [dC] using hR1 o hOpenC dC)
  · subst o
    cases ht : atTerminalB (C (ring.rightNeighbor e)) with
    | true =>
        have hx := hOpenD
        rw [rightGoodT hψ h2 ring C e hb hs] at hx
        simp [ht, setControl] at hx
    | false =>
        have hv := congrArg Fin.val (hLab (ring.rightNeighbor e))
        have hdR : dD.val < ψ - (raw (C (ring.rightNeighbor e))).label.val := by
          simpa only [hv] using dD.isLt
        have hsL := succLabelsT (C e) (C (ring.rightNeighbor e)) hs
        have hdE : dD.val + 1 < ψ - (raw (C e)).label.val := by omega
        let dC : Fin (ψ - (raw (C e)).label.val) := ⟨dD.val + 1, hdE⟩
        have hf := hR1 e hOpenE dC
        have hp := fwdRnT ring e dD.val
        have hf' : FreshnessClearV31
            (C (R2Coherence.fwd ring (ring.rightNeighbor e) dD.val)) := by
          rw [hp]
          simpa [dC] using hf
        exact freshStepT hψ h2 ring C e _ hb hf'


/-- On a good OPEN-R service the left endpoint becomes ordinary open/none.
Therefore, if that post cell still lies in a live sweep/pending-owner overlap,
the strong ownership conjunct is false. -/
theorem openR_good_left_overlap_blocks_strongR2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e sweep owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hSweep : (stepV3 hψ h2 ring C e sweep).ctl.tok = .sweep)
    (hPending : PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) owner)
    (hRead : InSweepWideReadV31 ring (stepV3 hψ h2 ring C e) sweep e)
    (hFoot : InOpenRFreshFootprintV31 ring (stepV3 hψ h2 ring C e) owner e) :
    ¬ OpenRPhaseOwnershipDisjointStrongV31 ring
        (stepV3 hψ h2 ring C e) := by
  intro hStrong
  have ho := hStrong.2 sweep owner e hSweep hPending hRead hFoot
  have hl := leftGoodT hψ h2 ring C e hb hs
  unfold PhaseOwnedV31 at ho
  rw [hl] at ho
  simp [setControl] at ho

end R2CoherenceV31ReachableOpenRTail
