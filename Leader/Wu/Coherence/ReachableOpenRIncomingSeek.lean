import Leader.Wu.Coherence.ReachableOpenRBadSeek

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableOpenR5

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31OpenNoHazard
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31ReachableOpenR2 R2CoherenceV31ReachableOpenR3
open R2CoherenceV31ReachableOpenR4

variable {n ψ κ τ : Nat}

def OpenRIncomingSeekClauseV31
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (e owner : Fin n) : Prop :=
  (atRootB (C e) = true →
      (¬ InOpenRFreshFootprintV31 ring C owner (ring.rightNeighbor e)) ∧
      ∀ d : Fin (ψ - (raw (C e)).label.val),
        ¬ InOpenRFreshFootprintV31 ring C owner
          (R2Coherence.fwd ring e d.val)) ∧
  (atRootB (C e) = false →
      ∀ pred : Fin n, ring.rightNeighbor pred = e →
        atRootB (C pred) = true →
          (¬ InOpenRFreshFootprintV31 ring C owner e) ∧
          ∀ d : Fin (ψ - (raw (C pred)).label.val),
            ¬ InOpenRFreshFootprintV31 ring C owner
              (R2Coherence.fwd ring pred d.val))

def OpenRIncomingSeekPrepaidV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (e owner : Fin n),
    (C e).ctl.tok = .openR →
    PendingOpenROwnerV31 ring C owner →
      OpenRIncomingSeekClauseV31 ring C e owner

def SeekIncomingSweepOpenROverlapClearWideStrongV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  SeekIncomingSweepOpenROverlapClearWideV31 ring C ∧
    OpenRIncomingSeekPrepaidV31 ring C

def ReachablePhaseFactsPlus4StrongR2StrongSV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ReachablePhaseFactsPlus3V31 ring C ∧
    SeekIncomingSweepOpenROverlapClearWideStrongV31 ring C ∧
    OpenRForwardMainClearV31 ring C ∧
    OpenRPhaseOwnershipDisjointStrongV31 ring C

theorem openRIncomingSeekPrepaid_quarantineInit
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    OpenRIncomingSeekPrepaidV31 ring (quarantineInitV31 C) := by
  intro e owner h
  simp [quarantineInitV31, setControl] at h

theorem reachablePhaseFactsPlus4StrongR2StrongS_entrance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (hBirth : BirthEntranceV1 hψ h2 ring C) :
    ReachablePhaseFactsPlus4StrongR2StrongSV31 ring C := by
  have h := reachablePhaseFactsPlus4StrongR2_entrance hψ h2 ring C hBirth
  refine ⟨h.1, ⟨h.2.1, ?_⟩, h.2.2.1, h.2.2.2⟩
  rcases hBirth.1 with ⟨_, D, _, hEq⟩
  rw [hEq]
  exact openRIncomingSeekPrepaid_quarantineInit ring D

private theorem gp5 (ring : DirectedRing n) {C D : FC n ψ κ τ}
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

private theorem pp5 (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val - k) =
    R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [h i]


private theorem footprintBack5
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (owner p : Fin n)
    (hF : InOpenRFreshFootprintV31 ring D owner p) :
    InOpenRFreshFootprintV31 ring C owner p := by
  rcases hF with ⟨j, ko, q, hOwner, kD, hPrefix⟩
  rw [gp5 ring hLab j ko.val] at hOwner
  have hq := gp5 ring hLab j q.val
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hFront : R2Coherence.groupPos ring (eraseCfgV3 D) j q.val = front := by
    simpa [front] using hq
  have hv :
      (raw (D (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val))).label.val =
        (raw (C front)).label.val := by
    rw [hFront]
    exact congrArg Fin.val (hLab front)
  have hk : kD.val < (raw (C front)).label.val + 1 := by
    simpa only [hv] using kD.isLt
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hk⟩
  refine ⟨j, ko, q, hOwner, kC, ?_⟩
  have h0 : R2Coherence.prefixPos ring (eraseCfgV3 D) front kD.val = p := by
    simpa only [hFront] using hPrefix
  have hp := pp5 ring hLab front kD.val
  have hc := hp.symm.trans h0
  simpa [front, kC] using hc

private theorem notFoot5
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (owner p : Fin n)
    (h : ¬ InOpenRFreshFootprintV31 ring C owner p) :
    ¬ InOpenRFreshFootprintV31 ring D owner p := by
  exact fun hf => h (footprintBack5 ring hLab owner p hf)

private theorem tailNotFoot5
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (owner base : Fin n)
    (h : ∀ d : Fin (ψ - (raw (C base)).label.val),
      ¬ InOpenRFreshFootprintV31 ring C owner
        (R2Coherence.fwd ring base d.val)) :
    ∀ d : Fin (ψ - (raw (D base)).label.val),
      ¬ InOpenRFreshFootprintV31 ring D owner
        (R2Coherence.fwd ring base d.val) := by
  intro dD
  have hv := congrArg Fin.val (hLab base)
  have hd : dD.val < ψ - (raw (C base)).label.val := by
    simpa only [hv] using dD.isLt
  let dC : Fin (ψ - (raw (C base)).label.val) := ⟨dD.val, hd⟩
  exact notFoot5 ring hLab owner _ (by simpa [dC] using h dC)

private theorem rootEq5 {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label) (p : Fin n) :
    atRootB (D p) = atRootB (C p) := by
  unfold atRootB
  rw [hLab p]

private theorem clauseLabels5
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (e owner : Fin n) (h : OpenRIncomingSeekClauseV31 ring C e owner) :
    OpenRIncomingSeekClauseV31 ring D e owner := by
  unfold OpenRIncomingSeekClauseV31 at h ⊢
  constructor
  · intro hrD
    have hrC : atRootB (C e) = true := by
      rw [← rootEq5 hLab e]; exact hrD
    rcases h.1 hrC with ⟨ha, ht⟩
    exact ⟨notFoot5 ring hLab owner _ ha,
      tailNotFoot5 ring hLab owner e ht⟩
  · intro hnD pred hp hrD
    have hnC : atRootB (C e) = false := by
      rw [← rootEq5 hLab e]; exact hnD
    have hrC : atRootB (C pred) = true := by
      rw [← rootEq5 hLab pred]; exact hrD
    rcases h.2 hnC pred hp hrC with ⟨ha, ht⟩
    exact ⟨notFoot5 ring hLab owner _ ha,
      tailNotFoot5 ring hLab owner pred ht⟩

private theorem pendingBackFrame5
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D) (owner : Fin n)
    (h : PendingOpenROwnerV31 ring D owner) :
    PendingOpenROwnerV31 ring C owner := by
  rcases h with ⟨hs, hsucc, hr⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [(hF (ring.rightNeighbor owner)).2.2.2] at hs; exact hs
  · have hl := congrArg Fin.val (hF owner).1
    have hh := congrArg Fin.val (hF (ring.rightNeighbor owner)).1
    unfold successorB at hsucc ⊢
    simpa only [hl, hh] using hsucc
  · have hl := congrArg Fin.val (hF owner).1
    unfold atRootB at hr ⊢
    simpa only [hl] using hr

theorem openRIncomingSeekPrepaid_openNoHazard_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hPre : OpenRIncomingSeekPrepaidV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    OpenRIncomingSeekPrepaidV31 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hF : OpenNoHazardFrameV31 C D := by
    simpa [D] using openNoHazard_step_frame hψ h2 ring C e hb
  have hLab : ∀ p, (raw (D p)).label = (raw (C p)).label := fun p => (hF p).1
  intro o owner hOpenD hPendD
  have hOpenC := hOpenD
  rw [(hF o).2.2.2] at hOpenC
  exact clauseLabels5 ring hLab o owner
    (hPre o owner hOpenC (pendingBackFrame5 ring hF owner hPendD))

private theorem boolFalse5 (b : Bool) (h : b ≠ true) : b = false := by
  cases b <;> simp_all

private theorem openRconds5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openR) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
    r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
    r.ctl.tok ≠ .scrubL ∧ l.ctl.tok = .openR := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowOpenR5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openR) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = openRStageV3 l r := by
  rcases openRconds5 hψ h2 l r hb with ⟨hs, _, hc, _, hsl, ho⟩
  simp [rowV3, hs, hc, hsl, ho]

private theorem succLabels5 (l r : Cell ψ κ τ)
    (h : successorB l r = true) :
    (raw r).label.val = (raw l).label.val + 1 := by
  simpa [successorB] using h


private theorem edgeNe5 (C : FC n ψ κ τ) (ring : DirectedRing n)
    (e : Fin n) (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    e ≠ ring.rightNeighbor e := by
  intro h
  have hh := congrArg (fun p : Fin n => (raw (C p)).label.val) h
  have hs' := succLabels5 (C e) (C (ring.rightNeighbor e)) hs
  omega

private theorem leftGood5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e e = setControl (clearMain (C e)) .open .none := by
  have hr := rowOpenR5 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hr, openRStageV3, hs]

private theorem rightGood5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      if atTerminalB (C (ring.rightNeighbor e)) then
        setControl (clearMain (C (ring.rightNeighbor e))) .open .none
      else setControl (clearMain (C (ring.rightNeighbor e))) .releasing .openR := by
  have hr := rowOpenR5 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  have hn := Ne.symm (edgeNe5 C ring e hs)
  simp [stepV3, protocolV3, PopulationProtocol.step, hr, openRStageV3, hs, hn]

private theorem leftBad5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false) :
    stepV3 hψ h2 ring C e e = startClosing (C e) := by
  have hr := rowOpenR5 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hr, openRStageV3, hs]

private theorem badOther5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false)
    (hp : p ≠ e) : stepV3 hψ h2 ring C e p = C p := by
  by_cases hr : p = ring.rightNeighbor e
  · subst p
    have hw := rowOpenR5 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
    simpa [stepV3, protocolV3, PopulationProtocol.step, hw, openRStageV3, hs, hp]
  · exact stepV3_other hψ h2 ring C e p hp hr

private theorem scrubSource5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (ht : (stepV3 hψ h2 ring C e p).ctl.tok = .scrubL) :
    stepV3 hψ h2 ring C e p = C p := by
  by_cases hs : successorB (C e) (C (ring.rightNeighbor e)) = true
  · by_cases hp : p = e
    · subst p; rw [leftGood5 hψ h2 ring C e hb hs] at ht; simp [setControl] at ht
    · by_cases hr : p = ring.rightNeighbor e
      · subst p; rw [rightGood5 hψ h2 ring C e hb hs] at ht
        cases hterm : atTerminalB (C (ring.rightNeighbor e)) <;> simp [hterm, setControl] at ht
      · exact stepV3_other hψ h2 ring C e p hp hr
  · have hsF := boolFalse5 _ hs
    by_cases hp : p = e
    · subst p; rw [leftBad5 hψ h2 ring C e hb hsF] at ht
      simp [startClosing, setControl] at ht
    · exact badOther5 hψ h2 ring C e p hb hsF hp

private theorem pendingBackOpenR5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (h : PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) owner) :
    PendingOpenROwnerV31 ring C owner := by
  rcases h with ⟨hs, hsucc, hr⟩
  have heq := scrubSource5 hψ h2 ring C e (ring.rightNeighbor owner) hb hs
  refine ⟨?_, ?_, ?_⟩
  · rw [← heq]; exact hs
  · have hl := congrArg Fin.val (stepV3_labels_eq_or_held hψ h2 ring C e owner)
    have hh := congrArg Fin.val
      (stepV3_labels_eq_or_held hψ h2 ring C e (ring.rightNeighbor owner))
    unfold successorB at hsucc ⊢
    simpa only [hl, hh] using hsucc
  · have hl := congrArg Fin.val (stepV3_labels_eq_or_held hψ h2 ring C e owner)
    unfold atRootB at hr ⊢
    simpa only [hl] using hr

private theorem openRSource5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (ht : (stepV3 hψ h2 ring C e p).ctl.tok = .openR) :
    stepV3 hψ h2 ring C e p = C p ∨
      (successorB (C e) (C (ring.rightNeighbor e)) = true ∧
       p = ring.rightNeighbor e) := by
  by_cases hs : successorB (C e) (C (ring.rightNeighbor e)) = true
  · by_cases hp : p = e
    · subst p; rw [leftGood5 hψ h2 ring C e hb hs] at ht; simp [setControl] at ht
    · by_cases hr : p = ring.rightNeighbor e
      · exact Or.inr ⟨hs, hr⟩
      · exact Or.inl (stepV3_other hψ h2 ring C e p hp hr)
  · have hsF := boolFalse5 _ hs
    by_cases hp : p = e
    · subst p; rw [leftBad5 hψ h2 ring C e hb hsF] at ht
      simp [startClosing, setControl] at ht
    · exact Or.inl (badOther5 hψ h2 ring C e p hb hsF hp)

private theorem rightNeighborInjective5 (ring : DirectedRing n) :
    Function.Injective ring.rightNeighbor := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases ha : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv; omega
    · have hbeq : b.val + 1 = n := by omega
      rw [hbeq, Nat.mod_self] at hv; omega
  · have haeq : a.val + 1 = n := by omega
    rw [haeq, Nat.mod_self] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv; omega
    · have hbeq : b.val + 1 = n := by omega
      omega


private theorem clearSafe5 (u : Cell ψ κ τ) (m : R2Coherence.Mark) (t : TokenV3) :
    MainClearV3 (setControl (clearMain u) m t) := by
  unfold MainClearV3 R2CoherenceBranches.MainClear
  simp [eraseCellV3, setControl, clearMain, R2Coherence.clearMainPhys,
    PPLLExpiringComparisonRepair.clearComparisonCarrier, R2Coherence.raw]

private theorem closingSafe5 (u : Cell ψ κ τ) (h : MainClearV3 u) :
    MainClearV3 (startClosing u) := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at h ⊢
  simpa [startClosing, setControl, eraseCellV3, R2Coherence.raw] using h

private theorem safeAtOpenR5
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
        rw [leftGood5 hψ h2 ring C e hb hs]
        exact clearSafe5 (C e) .open .none
      · by_cases hpr : p = ring.rightNeighbor e
        · subst p
          rw [rightGood5 hψ h2 ring C e hb hs]
          cases ht : atTerminalB (C (ring.rightNeighbor e)) with
          | true =>
              simpa [ht] using
                (clearSafe5 (C (ring.rightNeighbor e)) .open .none)
          | false =>
              simpa [ht] using
                (clearSafe5 (C (ring.rightNeighbor e)) .releasing .openR)
        · rw [stepV3_other hψ h2 ring C e p hpe hpr]
          exact hm
    · have hsF := boolFalse5 _ hs
      by_cases hpe : p = e
      · subst p
        rw [leftBad5 hψ h2 ring C e hb hsF]
        exact closingSafe5 _ hm
      · rw [badOther5 hψ h2 ring C e p hb hsF hpe]
        exact hm
  · right
    exact fun hf => hout (footprintBack5 ring hLab owner p hf)

private theorem tailSafeOpenR5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner base : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (h : ∀ d : Fin (ψ - (raw (C base)).label.val),
      SweepOpenRSafeAtV31 ring C owner (R2Coherence.fwd ring base d.val)) :
    ∀ d : Fin (ψ - (raw (stepV3 hψ h2 ring C e base)).label.val),
      SweepOpenRSafeAtV31 ring (stepV3 hψ h2 ring C e) owner
        (R2Coherence.fwd ring base d.val) := by
  intro dD
  have hv := congrArg Fin.val (stepV3_labels_eq_or_held hψ h2 ring C e base)
  have hd : dD.val < ψ - (raw (C base)).label.val := by
    simpa only [hv] using dD.isLt
  let dC : Fin (ψ - (raw (C base)).label.val) := ⟨dD.val, hd⟩
  exact safeAtOpenR5 hψ h2 ring C e owner _ hb
    (by simpa [dC] using h dC)

theorem openRIncomingSeekPrepaid_openR_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hPre : OpenRIncomingSeekPrepaidV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR) :
    OpenRIncomingSeekPrepaidV31 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hLab : ∀ p, (raw (D p)).label = (raw (C p)).label := by
    intro p; simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  intro o owner hOpenD hPendD
  have hPendC := pendingBackOpenR5 hψ h2 ring C e owner hb hPendD
  rcases openRSource5 hψ h2 ring C e o hb hOpenD with hEq | ⟨hs, ho⟩
  · have hOpenC : (C o).ctl.tok = .openR := by rw [← hEq]; exact hOpenD
    exact clauseLabels5 ring hLab o owner (hPre o owner hOpenC hPendC)
  · subst o
    have hOpenE := (openRconds5 hψ h2 (C e) (C (ring.rightNeighbor e)) hb).2.2.2.2.2
    have hOld := hPre e owner hOpenE hPendC
    unfold OpenRIncomingSeekClauseV31
    constructor
    · intro hrD
      have hrC : atRootB (C (ring.rightNeighbor e)) = true := by
        rw [← rootEq5 hLab (ring.rightNeighbor e)]; exact hrD
      have hz : (raw (C (ring.rightNeighbor e))).label.val = 0 := by
        simpa [atRootB] using hrC
      have hv := succLabels5 (C e) (C (ring.rightNeighbor e)) hs
      omega
    · intro _ pred hp hrD
      have hpred : pred = e := rightNeighborInjective5 ring hp
      subst pred
      have hrC : atRootB (C e) = true := by
        rw [← rootEq5 hLab e]; exact hrD
      rcases hOld.1 hrC with ⟨ha, ht⟩
      exact ⟨notFoot5 ring hLab owner _ ha,
        tailNotFoot5 ring hLab owner e ht⟩

theorem seekIncomingSweepOpenROverlapClearWide_openR_step_of_strongS
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hS : SeekIncomingSweepOpenROverlapClearWideStrongV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR) :
    SeekIncomingSweepOpenROverlapClearWideV31 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hLab : ∀ p, (raw (D p)).label = (raw (C p)).label := by
    intro p; simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  intro pred owner hSeekD hPendD
  have hPendC := pendingBackOpenR5 hψ h2 ring C e owner hb hPendD
  by_cases hs : successorB (C e) (C (ring.rightNeighbor e)) = true
  · have hsite : D (ring.rightNeighbor pred) = C (ring.rightNeighbor pred) := by
      by_cases h0 : ring.rightNeighbor pred = e
      · rw [h0] at hSeekD
        rw [leftGood5 hψ h2 ring C e hb hs] at hSeekD
        simp [setControl] at hSeekD
      · by_cases h1 : ring.rightNeighbor pred = ring.rightNeighbor e
        · rw [h1] at hSeekD
          rw [rightGood5 hψ h2 ring C e hb hs] at hSeekD
          cases ht : atTerminalB (C (ring.rightNeighbor e)) <;> simp [ht, setControl] at hSeekD
        · dsimp [D]; exact stepV3_other hψ h2 ring C e _ h0 h1
    have hSeekC : (C (ring.rightNeighbor pred)).ctl.tok = .seek := by
      rw [← hsite]; exact hSeekD
    have hOld := hS.1 pred owner hSeekC hPendC
    constructor
    · intro hrD
      have hrC : atRootB (C (ring.rightNeighbor pred)) = true := by
        rw [← rootEq5 hLab _]; exact hrD
      rcases hOld.1 hrC with ⟨ha, ht⟩
      exact ⟨safeAtOpenR5 hψ h2 ring C e owner _ hb ha,
        tailSafeOpenR5 hψ h2 ring C e owner (ring.rightNeighbor pred) hb ht⟩
    · intro hnD hrD
      have hnC : atRootB (C (ring.rightNeighbor pred)) = false := by
        rw [← rootEq5 hLab _]; exact hnD
      have hrC : atRootB (C pred) = true := by rw [← rootEq5 hLab _]; exact hrD
      rcases hOld.2 hnC hrC with ⟨ha, ht⟩
      exact ⟨safeAtOpenR5 hψ h2 ring C e owner _ hb ha,
        tailSafeOpenR5 hψ h2 ring C e owner pred hb ht⟩
  · have hsF := boolFalse5 _ hs
    by_cases hnew : ring.rightNeighbor pred = e
    · have hOpenE := (openRconds5 hψ h2 (C e) (C (ring.rightNeighbor e)) hb).2.2.2.2.2
      have hPre := hS.2 e owner hOpenE hPendC
      rw [hnew]
      constructor
      · intro hrD
        have hrC : atRootB (C e) = true := by rw [← rootEq5 hLab e]; exact hrD
        rcases hPre.1 hrC with ⟨ha, ht⟩
        exact ⟨Or.inr (notFoot5 ring hLab owner _ ha),
          fun d => Or.inr (tailNotFoot5 ring hLab owner e ht d)⟩
      · intro hnD hrD
        have hnC : atRootB (C e) = false := by rw [← rootEq5 hLab e]; exact hnD
        have hrC : atRootB (C pred) = true := by rw [← rootEq5 hLab pred]; exact hrD
        rcases hPre.2 hnC pred hnew hrC with ⟨ha, ht⟩
        exact ⟨Or.inr (notFoot5 ring hLab owner _ ha),
          fun d => Or.inr (tailNotFoot5 ring hLab owner pred ht d)⟩
    · have hsite := badOther5 hψ h2 ring C e (ring.rightNeighbor pred) hb hsF hnew
      have hSeekC : (C (ring.rightNeighbor pred)).ctl.tok = .seek := by
        rw [← hsite]; exact hSeekD
      have hOld := hS.1 pred owner hSeekC hPendC
      constructor
      · intro hrD
        have hrC : atRootB (C (ring.rightNeighbor pred)) = true := by rw [← rootEq5 hLab _]; exact hrD
        rcases hOld.1 hrC with ⟨ha, ht⟩
        exact ⟨safeAtOpenR5 hψ h2 ring C e owner _ hb ha,
          tailSafeOpenR5 hψ h2 ring C e owner (ring.rightNeighbor pred) hb ht⟩
      · intro hnD hrD
        have hnC : atRootB (C (ring.rightNeighbor pred)) = false := by rw [← rootEq5 hLab _]; exact hnD
        have hrC : atRootB (C pred) = true := by rw [← rootEq5 hLab _]; exact hrD
        rcases hOld.2 hnC hrC with ⟨ha, ht⟩
        exact ⟨safeAtOpenR5 hψ h2 ring C e owner _ hb ha,
          tailSafeOpenR5 hψ h2 ring C e owner pred hb ht⟩

theorem openRReplay_newSeek_is_bad
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e pred : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hnew : ring.rightNeighbor pred = e)
    (hSeekD : (stepV3 hψ h2 ring C e (ring.rightNeighbor pred)).ctl.tok = .seek) :
    successorB (C e) (C (ring.rightNeighbor e)) = false := by
  apply Bool.eq_false_iff.mpr
  intro hs
  have hx := hSeekD
  rw [hnew] at hx
  rw [leftGood5 hψ h2 ring C e hb hs] at hx
  simp [setControl] at hx

theorem openRReplay_oldSeekClearWide
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e pred owner : Fin n)
    (hS : SeekIncomingSweepOpenROverlapClearWideV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hOldSite : ring.rightNeighbor pred ≠ e)
    (hSeekD : (stepV3 hψ h2 ring C e (ring.rightNeighbor pred)).ctl.tok = .seek)
    (hPendD : PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) owner) :
    let D := stepV3 hψ h2 ring C e
    (atRootB (D (ring.rightNeighbor pred)) = true →
      SweepOpenRSafeAtV31 ring D owner (ring.rightNeighbor (ring.rightNeighbor pred)) ∧
      ∀ d : Fin (ψ - (raw (D (ring.rightNeighbor pred))).label.val),
        SweepOpenRSafeAtV31 ring D owner
          (R2Coherence.fwd ring (ring.rightNeighbor pred) d.val)) ∧
    (atRootB (D (ring.rightNeighbor pred)) = false →
      atRootB (D pred) = true →
      SweepOpenRSafeAtV31 ring D owner (ring.rightNeighbor pred) ∧
      ∀ d : Fin (ψ - (raw (D pred)).label.val),
        SweepOpenRSafeAtV31 ring D owner (R2Coherence.fwd ring pred d.val)) := by
  dsimp only
  let D := stepV3 hψ h2 ring C e
  have hLab : ∀ p, (raw (D p)).label = (raw (C p)).label := by
    intro p
    simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  have hPendC := pendingBackOpenR5 hψ h2 ring C e owner hb hPendD
  by_cases hs : successorB (C e) (C (ring.rightNeighbor e)) = true
  · have hsite : D (ring.rightNeighbor pred) = C (ring.rightNeighbor pred) := by
      by_cases h1 : ring.rightNeighbor pred = ring.rightNeighbor e
      · have hx := hSeekD
        rw [h1] at hx
        rw [rightGood5 hψ h2 ring C e hb hs] at hx
        cases ht : atTerminalB (C (ring.rightNeighbor e)) <;>
          simp [ht, setControl] at hx
      · dsimp [D]
        exact stepV3_other hψ h2 ring C e _ hOldSite h1
    have hSeekC : (C (ring.rightNeighbor pred)).ctl.tok = .seek := by
      rw [← hsite]
      exact hSeekD
    have hOld := hS pred owner hSeekC hPendC
    constructor
    · intro hrD
      have hrC : atRootB (C (ring.rightNeighbor pred)) = true := by
        rw [← rootEq5 hLab _]
        exact hrD
      rcases hOld.1 hrC with ⟨ha, ht⟩
      exact ⟨safeAtOpenR5 hψ h2 ring C e owner _ hb ha,
        tailSafeOpenR5 hψ h2 ring C e owner (ring.rightNeighbor pred) hb ht⟩
    · intro hnD hrD
      have hnC : atRootB (C (ring.rightNeighbor pred)) = false := by
        rw [← rootEq5 hLab _]
        exact hnD
      have hrC : atRootB (C pred) = true := by
        rw [← rootEq5 hLab _]
        exact hrD
      rcases hOld.2 hnC hrC with ⟨ha, ht⟩
      exact ⟨safeAtOpenR5 hψ h2 ring C e owner _ hb ha,
        tailSafeOpenR5 hψ h2 ring C e owner pred hb ht⟩
  · have hsF := boolFalse5 _ hs
    have hsite : D (ring.rightNeighbor pred) = C (ring.rightNeighbor pred) := by
      dsimp [D]
      exact badOther5 hψ h2 ring C e _ hb hsF hOldSite
    have hSeekC : (C (ring.rightNeighbor pred)).ctl.tok = .seek := by
      rw [← hsite]
      exact hSeekD
    have hOld := hS pred owner hSeekC hPendC
    constructor
    · intro hrD
      have hrC : atRootB (C (ring.rightNeighbor pred)) = true := by
        rw [← rootEq5 hLab _]
        exact hrD
      rcases hOld.1 hrC with ⟨ha, ht⟩
      exact ⟨safeAtOpenR5 hψ h2 ring C e owner _ hb ha,
        tailSafeOpenR5 hψ h2 ring C e owner (ring.rightNeighbor pred) hb ht⟩
    · intro hnD hrD
      have hnC : atRootB (C (ring.rightNeighbor pred)) = false := by
        rw [← rootEq5 hLab _]
        exact hnD
      have hrC : atRootB (C pred) = true := by
        rw [← rootEq5 hLab _]
        exact hrD
      rcases hOld.2 hnC hrC with ⟨ha, ht⟩
      exact ⟨safeAtOpenR5 hψ h2 ring C e owner _ hb ha,
        tailSafeOpenR5 hψ h2 ring C e owner pred hb ht⟩

end R2CoherenceV31ReachableOpenR5
