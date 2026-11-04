import Leader.Wu.Coherence.ReachableOpenROwnerFresh


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31ReachableOpenR3


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure2
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenR2
open R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31QuarantineReach


variable {n ψ κ τ : Nat}


private theorem boolFalse3 (b : Bool) (h : b ≠ true) : b = false := by
  cases b <;> simp_all


private theorem openRconds3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openR) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
    r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
    r.ctl.tok ≠ .scrubL ∧ l.ctl.tok = .openR := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind


private theorem rowOpenR3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openR) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = openRStageV3 l r := by
  rcases openRconds3 hψ h2 l r hb with
    ⟨hs, _, hc, _, hsl, ho⟩
  simp [rowV3, hs, hc, hsl, ho]


private theorem succLabels3 (l r : Cell ψ κ τ)
    (h : successorB l r = true) :
    (raw r).label.val = (raw l).label.val + 1 := by
  simpa [successorB] using h


private theorem edgeNe3 (C : FC n ψ κ τ) (ring : DirectedRing n)
    (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    e ≠ ring.rightNeighbor e := by
  intro h
  have hh := congrArg (fun p : Fin n => (raw (C p)).label.val) h
  have hs' := succLabels3 (C e) (C (ring.rightNeighbor e)) hs
  omega


private theorem leftGood3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e e =
      setControl (clearMain (C e)) .open .none := by
  have hr := rowOpenR3 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hr, openRStageV3, hs]


private theorem rightGood3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      if atTerminalB (C (ring.rightNeighbor e)) then
        setControl (clearMain (C (ring.rightNeighbor e))) .open .none
      else setControl (clearMain (C (ring.rightNeighbor e))) .releasing .openR := by
  have hr := rowOpenR3 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  have hn := Ne.symm (edgeNe3 C ring e hs)
  simp [stepV3, protocolV3, PopulationProtocol.step, hr,
    openRStageV3, hs, hn]


private theorem leftBad3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false) :
    stepV3 hψ h2 ring C e e = startClosing (C e) := by
  have hr := rowOpenR3 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hr, openRStageV3, hs]


private theorem badOther3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false)
    (hp : p ≠ e) : stepV3 hψ h2 ring C e p = C p := by
  by_cases hr : p = ring.rightNeighbor e
  · subst p
    have hw := rowOpenR3 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
    simpa [stepV3, protocolV3, PopulationProtocol.step,
      hw, openRStageV3, hs, hp]
  · exact stepV3_other hψ h2 ring C e p hp hr


private theorem tokenSource3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n) (t : TokenV3)
    (hn : t ≠ .none) (ho : t ≠ .openR) (hk : t ≠ .seek)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (ht : (stepV3 hψ h2 ring C e p).ctl.tok = t) :
    stepV3 hψ h2 ring C e p = C p := by
  by_cases hs : successorB (C e) (C (ring.rightNeighbor e)) = true
  · by_cases hp : p = e
    · subst p
      rw [leftGood3 hψ h2 ring C e hb hs] at ht
      have hh : (TokenV3.none : TokenV3) = t := by simpa [setControl] using ht
      exact (hn hh.symm).elim
    · by_cases hr : p = ring.rightNeighbor e
      · subst p
        rw [rightGood3 hψ h2 ring C e hb hs] at ht
        cases hterm : atTerminalB (C (ring.rightNeighbor e)) with
        | true =>
            have hh : (TokenV3.none : TokenV3) = t := by
              simpa [hterm, setControl] using ht
            exact (hn hh.symm).elim
        | false =>
            have hh : TokenV3.openR = t := by
              simpa [hterm, setControl] using ht
            exact (ho hh.symm).elim
      · exact stepV3_other hψ h2 ring C e p hp hr
  · have hsF := boolFalse3 _ hs
    by_cases hp : p = e
    · subst p
      rw [leftBad3 hψ h2 ring C e hb hsF] at ht
      have hh : TokenV3.seek = t := by simpa [startClosing, setControl] using ht
      exact (hk hh.symm).elim
    · exact badOther3 hψ h2 ring C e p hb hsF hp



private theorem gpLabels3
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [h i]


private theorem ppLabels3
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val - k) =
    R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [h i]


private theorem freshFalseMainClear3 (u : Cell ψ κ τ) (k : Nat)
    (hm : MainClearV3 u)
    (hf : R2Coherence.freshComponent (eraseCellV3 u) k) : False := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at hm
  unfold R2Coherence.freshComponent at hf
  change (raw u).label.val = k ∧
    (match (raw u).path with
     | .bot => False
     | .some lab b => lab.val = k ∧
       b.val = (if (raw u).bit then 1 else 0)) at hf
  have hPath : (raw u).path = .bot := by
    exact hm.2.1
  rw [hPath] at hf
  exact hf.2



private theorem clearedMainClear3
    (u : Cell ψ κ τ) (m : R2Coherence.Mark) (t : TokenV3) :
    MainClearV3 (setControl (clearMain u) m t) := by
  unfold MainClearV3 R2CoherenceBranches.MainClear
  simp [eraseCellV3, setControl, clearMain, R2Coherence.clearMainPhys,
    PPLLExpiringComparisonRepair.clearComparisonCarrier, R2Coherence.raw]


private theorem startClosingMainClear3 (u : Cell ψ κ τ)
    (h : MainClearV3 u) : MainClearV3 (startClosing u) := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at h ⊢
  simpa [startClosing, setControl, eraseCellV3, R2Coherence.raw] using h


private theorem fwd0_3 (ring : DirectedRing n) (i : Fin n) :
    R2Coherence.fwd ring i 0 = i := by
  apply Fin.ext
  simp [R2Coherence.fwd, Nat.mod_eq_of_lt i.isLt]


private theorem fwd1_3 (ring : DirectedRing n) (i : Fin n) :
    R2Coherence.fwd ring i 1 = ring.rightNeighbor i := by
  apply Fin.ext
  rfl


private theorem servedClear3
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hR1 : OpenRForwardMainClearV31 ring C)
    (ho : (C e).ctl.tok = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    MainClearV3 (C e) ∧ MainClearV3 (C (ring.rightNeighbor e)) := by
  have hS := hR1 e ho
  have h0 : 0 < ψ - (raw (C e)).label.val := by
    have := (raw (C e)).label.isLt
    omega
  let d0 : Fin (ψ - (raw (C e)).label.val) := ⟨0, h0⟩
  have he := hS d0
  rw [show R2Coherence.fwd ring e d0.val = e by simpa [d0] using fwd0_3 ring e] at he
  have hSucc := succLabels3 (C e) (C (ring.rightNeighbor e)) hs
  have h1 : 1 < ψ - (raw (C e)).label.val := by
    have := (raw (C (ring.rightNeighbor e))).label.isLt
    omega
  let d1 : Fin (ψ - (raw (C e)).label.val) := ⟨1, h1⟩
  have hr := hS d1
  rw [show R2Coherence.fwd ring e d1.val = ring.rightNeighbor e by
    simpa [d1] using fwd1_3 ring e] at hr
  exact ⟨he, hr⟩


private theorem goodStates3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    (raw (stepV3 hψ h2 ring C e e)).state = .none ∧
    (raw (stepV3 hψ h2 ring C e (ring.rightNeighbor e))).state = .none := by
  constructor
  · rw [leftGood3 hψ h2 ring C e hb hs]
    simp [setControl, clearMain, raw]
  · rw [rightGood3 hψ h2 ring C e hb hs]
    cases ht : atTerminalB (C (ring.rightNeighbor e)) <;>
      simp [ht, setControl, clearMain, raw]


private theorem ownerFreshGood3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hce : MainClearV3 (C e))
    (hcr : MainClearV3 (C (ring.rightNeighbor e)))
    (hf : OpenROwnerFreshV3 ring C owner) :
    OpenROwnerFreshV3 ring (stepV3 hψ h2 ring C e) owner := by
  let D := stepV3 hψ h2 ring C e
  have hLab : ∀ p, (raw (D p)).label = (raw (C p)).label := by
    intro p
    simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  have hsD := goodStates3 hψ h2 ring C e hb hs
  unfold OpenROwnerFreshV3 at hf ⊢
  intro j ko hHitD
  have hgp := gpLabels3 ring hLab j ko.val
  rw [hgp] at hHitD
  have hg := hf j ko hHitD
  unfold GroupIntrinsicFreshV3 at hg ⊢
  intro q
  have hgpq := gpLabels3 ring hLab j q.val
  rw [hgpq]
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  change IntrinsicFreshAtV3 ring D front
  have hOld : IntrinsicFreshAtV3 ring C front := by simpa [front] using hg q
  unfold IntrinsicFreshAtV3 at hOld ⊢
  intro hEqD
  by_cases hfe : front = e
  · rw [hfe, hsD.1] at hEqD
    cases hEqD
  · by_cases hfr : front = ring.rightNeighbor e
    · rw [hfr, hsD.2] at hEqD
      cases hEqD
    · have hFront : D front = C front := by
        dsimp [D]
        exact stepV3_other hψ h2 ring C e front hfe hfr
      have hEqC : (raw (C front)).state = .equal := by simpa [hFront] using hEqD
      have hOldAt := hOld hEqC
      intro kD
      have hv := congrArg Fin.val (hLab front)
      have hkC : kD.val < (raw (C front)).label.val + 1 := by
        simpa only [hv] using kD.isLt
      let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hkC⟩
      have hOldK := hOldAt kC
      have hpp := ppLabels3 ring hLab front kD.val
      rw [hpp]
      let p := R2Coherence.prefixPos ring (eraseCfgV3 C) front kD.val
      change R2Coherence.freshComponent (eraseCellV3 (D p)) kD.val
      have hOldK' : R2Coherence.freshComponent (eraseCellV3 (C p)) kD.val := by
        simpa [p, kC] using hOldK
      by_cases hpe : p = e
      · exact (freshFalseMainClear3 (C p) kD.val
          (by simpa [hpe] using hce) hOldK').elim
      · by_cases hpr : p = ring.rightNeighbor e
        · exact (freshFalseMainClear3 (C p) kD.val
            (by simpa [hpr] using hcr) hOldK').elim
        · have hp : D p = C p := by
            dsimp [D]
            exact stepV3_other hψ h2 ring C e p hpe hpr
          simpa [hp, p] using hOldK'



private theorem ownerFreshPhys3
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
  unfold OpenROwnerFreshV3 at hf ⊢
  intro j ko hHitD
  have hGPko := gpLabels3 ring hLab j ko.val
  rw [hGPko] at hHitD
  have hOldGroup := hf j ko hHitD
  unfold GroupIntrinsicFreshV3 at hOldGroup ⊢
  intro q
  have hGPq := gpLabels3 ring hLab j q.val
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
    have hk : m < (raw (D front)).label.val + 1 := by
      exact kD.isLt
    have hk' : m < (raw (C front)).label.val + 1 := by
      simpa only [hLabelVal] using hk
    exact hk'
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hkC⟩
  have hOldK := hOldAt kC
  have hPP := ppLabels3 ring hLab front kD.val
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


private theorem pendingBefore3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hD : PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) owner) :
    PendingOpenROwnerV31 ring C owner := by
  rcases hD with ⟨hScrub, hSucc, hRoot⟩
  have hEq := tokenSource3 hψ h2 ring C e (ring.rightNeighbor owner)
    .scrubL (by decide) (by decide) (by decide) hb hScrub
  refine ⟨?_, ?_, ?_⟩
  · rw [← hEq]
    exact hScrub
  · have hL := congrArg Fin.val (stepV3_labels_eq_or_held hψ h2 ring C e owner)
    have hR := congrArg Fin.val
      (stepV3_labels_eq_or_held hψ h2 ring C e (ring.rightNeighbor owner))
    unfold successorB at hSucc ⊢
    simpa only [hL, hR] using hSucc
  · have hL := congrArg Fin.val (stepV3_labels_eq_or_held hψ h2 ring C e owner)
    unfold atRootB at hRoot ⊢
    simpa only [hL] using hRoot


/-- P7. -/
theorem scrubLIncomingOpenRFresh_openR_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (_hElection : ElectionGeometryV31 ring C)
    (_hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR) :
    ScrubLIncomingOpenRFreshV31 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hP7 : ScrubLIncomingOpenRFreshV31 ring C := hPlus.1.1.1.2
  have hR1 : OpenRForwardMainClearV31 ring C := hPlus.2.2.1
  have ho : (C e).ctl.tok = .openR :=
    (openRconds3 hψ h2 (C e) (C (ring.rightNeighbor e)) hb).2.2.2.2.2
  intro owner hScrub hSucc hRoot
  have hPendD : PendingOpenROwnerV31 ring D owner := ⟨hScrub, hSucc, hRoot⟩
  have hPendC := pendingBefore3 hψ h2 ring C e owner hb hPendD
  have hFreshC := hP7 owner hPendC.1 hPendC.2.1 hPendC.2.2
  by_cases hs : successorB (C e) (C (ring.rightNeighbor e)) = true
  · have hc := servedClear3 ring C e hR1 ho hs
    exact ownerFreshGood3 hψ h2 ring C e owner hb hs hc.1 hc.2 hFreshC
  · have hsF := boolFalse3 _ hs
    have hp : ∀ p, (D p).phys = (C p).phys := by
      intro p
      by_cases hpe : p = e
      · subst p
        dsimp [D]
        rw [leftBad3 hψ h2 ring C e hb hsF]
        simp [startClosing, setControl]
      · dsimp [D]
        rw [badOther3 hψ h2 ring C e p hb hsF hpe]
    exact ownerFreshPhys3 ring owner hp hFreshC


private theorem footprintBack3
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ x, (raw (D x)).label = (raw (C x)).label)
    (owner p : Fin n)
    (hF : InOpenRFreshFootprintV31 ring D owner p) :
    InOpenRFreshFootprintV31 ring C owner p := by
  rcases hF with ⟨j, ko, q, hOwnerD, kD, hPrefixD⟩
  have hko := gpLabels3 ring hLab j ko.val
  rw [hko] at hOwnerD
  have hq := gpLabels3 ring hLab j q.val
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hFrontD : R2Coherence.groupPos ring (eraseCfgV3 D) j q.val = front := by
    simpa [front] using hq
  have hVal :
      (raw (D (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val))).label.val =
      (raw (C front)).label.val := by
    rw [hFrontD]
    exact congrArg Fin.val (hLab front)
  have hkC : kD.val < (raw (C front)).label.val + 1 := by
    simpa only [hVal] using kD.isLt
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hkC⟩
  refine ⟨j, ko, q, hOwnerD, kC, ?_⟩
  let m : Nat := kD.val
  have h0 : R2Coherence.prefixPos ring (eraseCfgV3 D)
      (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val) m = p := by
    simpa [m] using hPrefixD
  have h1 : R2Coherence.prefixPos ring (eraseCfgV3 D) front m = p := by
    simpa only [hFrontD] using h0
  have hpp := ppLabels3 ring hLab front m
  have hc : R2Coherence.prefixPos ring (eraseCfgV3 C) front m = p :=
    hpp.symm.trans h1
  simpa [front, kC, m] using hc


private theorem safeAtOpenR3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hSafe : SweepOpenRSafeAtV31 ring C owner p) :
    SweepOpenRSafeAtV31 ring (stepV3 hψ h2 ring C e) owner p := by
  let D := stepV3 hψ h2 ring C e
  have hLab : ∀ x, (raw (D x)).label = (raw (C x)).label := by
    intro x
    simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e x
  unfold SweepOpenRSafeAtV31 at hSafe ⊢
  rcases hSafe with hm | hout
  · left
    by_cases hs : successorB (C e) (C (ring.rightNeighbor e)) = true
    · by_cases hpe : p = e
      · subst p
        try dsimp [D]
        rw [leftGood3 hψ h2 ring C e hb hs]
        exact clearedMainClear3 _ _ _
      · by_cases hpr : p = ring.rightNeighbor e
        · subst p
          try dsimp [D]
          rw [rightGood3 hψ h2 ring C e hb hs]
          cases ht : atTerminalB (C (ring.rightNeighbor e)) with
          | true => simpa [ht] using
              (clearedMainClear3 (C (ring.rightNeighbor e)) .open .none)
          | false => simpa [ht] using
              (clearedMainClear3 (C (ring.rightNeighbor e)) .releasing .openR)
        · try dsimp [D]
          rw [stepV3_other hψ h2 ring C e p hpe hpr]
          exact hm
    · have hsF := boolFalse3 _ hs
      by_cases hpe : p = e
      · subst p
        try dsimp [D]
        rw [leftBad3 hψ h2 ring C e hb hsF]
        exact startClosingMainClear3 _ hm
      · try dsimp [D]
        rw [badOther3 hψ h2 ring C e p hb hsF hpe]
        exact hm
  · right
    intro hFD
    exact hout (footprintBack3 ring hLab owner p hFD)


/-- P8. -/
theorem sweepOpenROverlapClear_openR_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR) :
    SweepOpenROverlapClearV31 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  intro sweep owner hSweepD hPendingD
  have hEq := tokenSource3 hψ h2 ring C e sweep .sweep
    (by decide) (by decide) (by decide) hb hSweepD
  have hSweepC : (C sweep).ctl.tok = .sweep := by rw [← hEq]; exact hSweepD
  have hPendingC := pendingBefore3 hψ h2 ring C e owner hb hPendingD
  have hOld := hPlus.1.1.2 sweep owner hSweepC hPendingC
  exact ⟨safeAtOpenR3 hψ h2 ring C e owner sweep hb hOld.1,
    safeAtOpenR3 hψ h2 ring C e owner (ring.rightNeighbor sweep) hb hOld.2⟩


/-- P9. -/
theorem sweepOpenROverlapClearWide_openR_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR) :
    SweepOpenROverlapClearWideV31 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  intro sweep owner hSweepD hPendingD
  have hEq := tokenSource3 hψ h2 ring C e sweep .sweep
    (by decide) (by decide) (by decide) hb hSweepD
  have hSweepC : (C sweep).ctl.tok = .sweep := by rw [← hEq]; exact hSweepD
  have hPendingC := pendingBefore3 hψ h2 ring C e owner hb hPendingD
  have hOld := hPlus.1.2 sweep owner hSweepC hPendingC
  constructor
  · exact safeAtOpenR3 hψ h2 ring C e owner (ring.rightNeighbor sweep) hb hOld.1
  · intro dD
    have hv := congrArg Fin.val (stepV3_labels_eq_or_held hψ h2 ring C e sweep)
    have hdC : dD.val < ψ - (raw (C sweep)).label.val := by
      simpa only [hv] using dD.isLt
    let dC : Fin (ψ - (raw (C sweep)).label.val) := ⟨dD.val, hdC⟩
    exact safeAtOpenR3 hψ h2 ring C e owner
      (R2Coherence.fwd ring sweep dD.val) hb (by simpa [dC] using hOld.2 dC)


end R2CoherenceV31ReachableOpenR3
