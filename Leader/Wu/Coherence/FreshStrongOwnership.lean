import Leader.Wu.Coherence.ReachableOpenRFreshTail
import Leader.Wu.Coherence.FreshPayload

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31StrongR2Route

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure2
open R2CoherenceV31ReachablePlus2 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard3
open R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31MainClearTruth
open R2CoherenceV31MainClearTruth.WeakFreshnessLayer
open R2CoherenceV31FreshnessClear
open R2CoherenceV31PhaseMainClear

variable {n ψ κ τ : Nat}

/-- Fresh replacement for the ownership-only extra sentence of strong R2. -/
def SweepPendingOpenRFootprintOwnedV31F
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (sweep owner p : Fin n),
    (C sweep).ctl.tok = .sweep →
    PendingOpenROwnerV31 ring C owner →
    InSweepWideReadV31 ring C sweep p →
    InOpenRFreshFootprintV31 ring C owner p →
      PhaseOwnedV31 (C p) ∨ FreshnessClearV31 (C p)

theorem sweepPendingOpenRFootprintOwnedV31F_of_old
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : SweepPendingOpenRFootprintOwnedV31 ring C) :
    SweepPendingOpenRFootprintOwnedV31F ring C := by
  intro sweep owner p hs hp hr hf
  exact Or.inl (h sweep owner p hs hp hr hf)

private theorem openNoHazardOpenNoneF
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openNoHazard) :
    l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
      l.ctl.mark = .open ∧ r.ctl.mark = .open := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem phaseOwnedNotOpenNoneF
    (u : Cell ψ κ τ) (ho : PhaseOwnedV31 u)
    (hm : u.ctl.mark = .open) (ht : u.ctl.tok = .none) : False := by
  unfold PhaseOwnedV31 at ho
  rcases ho with h | h
  · exact h hm
  · exact h ht

theorem openNoHazardSweepReadFreshnessTransport_of_R2F
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e sweep owner p : Fin n)
    (hF : SweepPendingOpenRFootprintOwnedV31F ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard)
    (hs : (C sweep).ctl.tok = .sweep)
    (hp : PendingOpenROwnerV31 ring C owner)
    (hr : InSweepWideReadV31 ring C sweep p)
    (hv : p = e ∨ p = ring.rightNeighbor e)
    (hf : InOpenRFreshFootprintV31 ring C owner p) :
    FreshnessClearV31 (stepV3 hψ h2 ring C e p) := by
  rcases hF sweep owner p hs hp hr hf with ho | hc
  · have h := openNoHazardOpenNoneF hψ h2 (C e) (C (ring.rightNeighbor e)) hb
    rcases hv with hpe | hpe
    · have ho' : PhaseOwnedV31 (C e) := by
        simpa only [hpe] using ho
      exact (phaseOwnedNotOpenNoneF (C e) ho' h.2.2.1 h.1).elim
    · have ho' : PhaseOwnedV31 (C (ring.rightNeighbor e)) := by
        simpa only [hpe] using ho
      exact (phaseOwnedNotOpenNoneF
        (C (ring.rightNeighbor e)) ho' h.2.2.2 h.2.1).elim
  · exact openNoHazard_preserves_freshnessClear hψ h2 ring C e p hb hc

theorem openNoHazardSweepReadSafeFresh_of_R2F
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e sweep owner p : Fin n)
    (hF : SweepPendingOpenRFootprintOwnedV31F ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard)
    (hs : (C sweep).ctl.tok = .sweep)
    (hp : PendingOpenROwnerV31 ring C owner)
    (hr : InSweepWideReadV31 ring C sweep p)
    (hv : p = e ∨ p = ring.rightNeighbor e)
    (hf : InOpenRFreshFootprintV31 ring C owner p) :
    SweepOpenRSafeFreshV31 ring (stepV3 hψ h2 ring C e) owner p := by
  exact Or.inl (openNoHazardSweepReadFreshnessTransport_of_R2F
    hψ h2 ring C e sweep owner p hF hb hs hp hr hv hf)

private theorem boolFalseF (b : Bool) (h : b ≠ true) : b = false := by
  cases b <;> simp_all

private theorem openRCondsF
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openR) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
    r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
    r.ctl.tok ≠ .scrubL ∧ l.ctl.tok = .openR := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

theorem openR_service_served_pair_not_scrubL
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR) :
    (C e).ctl.tok ≠ .scrubL ∧
      (C (ring.rightNeighbor e)).ctl.tok ≠ .scrubL := by
  have h := openRCondsF hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  constructor
  · intro hs
    have hx : (TokenV3.openR : TokenV3) = .scrubL := h.2.2.2.2.2.symm.trans hs
    cases hx
  · exact h.2.2.2.2.1

private theorem rowOpenRF
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openR) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = openRStageV3 l r := by
  rcases openRCondsF hψ h2 l r hb with ⟨hs, _, hc, _, hsl, ho⟩
  simp [rowV3, hs, hc, hsl, ho]


private theorem succLabelsF (l r : Cell ψ κ τ)
    (h : successorB l r = true) :
    (raw r).label.val = (raw l).label.val + 1 := by
  simpa [successorB] using h

private theorem edgeNeF (C : FC n ψ κ τ) (ring : DirectedRing n)
    (e : Fin n) (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    e ≠ ring.rightNeighbor e := by
  intro h
  have hv := congrArg (fun p : Fin n => (raw (C p)).label.val) h
  have hs' := succLabelsF (C e) (C (ring.rightNeighbor e)) hs
  omega

private theorem leftGoodF
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e e = setControl (clearMain (C e)) .open .none := by
  have hr := rowOpenRF hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hr, openRStageV3, hs]

private theorem rightGoodF
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      if atTerminalB (C (ring.rightNeighbor e)) then
        setControl (clearMain (C (ring.rightNeighbor e))) .open .none
      else setControl (clearMain (C (ring.rightNeighbor e))) .releasing .openR := by
  have hr := rowOpenRF hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  have hn := Ne.symm (edgeNeF C ring e hs)
  simp [stepV3, protocolV3, PopulationProtocol.step, hr, openRStageV3, hs, hn]

private theorem leftBadF
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false) :
    stepV3 hψ h2 ring C e e = startClosing (C e) := by
  have hr := rowOpenRF hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hr, openRStageV3, hs]

private theorem badOtherF
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false)
    (hp : p ≠ e) : stepV3 hψ h2 ring C e p = C p := by
  by_cases hr : p = ring.rightNeighbor e
  · subst p
    have hw := rowOpenRF hψ h2 (C e) (C (ring.rightNeighbor e)) hb
    simpa [stepV3, protocolV3, PopulationProtocol.step, hw, openRStageV3, hs, hp]
  · exact stepV3_other hψ h2 ring C e p hp hr

private theorem clearFreshF
    (u : Cell ψ κ τ) (m : R2Coherence.Mark) (t : TokenV3) :
    FreshnessClearV31 (setControl (clearMain u) m t) := by
  apply freshnessClear_of_mainClear
  unfold MainClearV3 R2CoherenceBranches.MainClear
  simp [eraseCellV3, setControl, clearMain, R2Coherence.clearMainPhys,
    PPLLExpiringComparisonRepair.clearComparisonCarrier, R2Coherence.raw]

private theorem ownedOrFreshStepF
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (h : PhaseOwnedV31 (C p) ∨ FreshnessClearV31 (C p)) :
    PhaseOwnedV31 (stepV3 hψ h2 ring C e p) ∨
      FreshnessClearV31 (stepV3 hψ h2 ring C e p) := by
  by_cases hs : successorB (C e) (C (ring.rightNeighbor e)) = true
  · by_cases hp : p = e
    · subst p; rw [leftGoodF hψ h2 ring C e hb hs]
      exact Or.inr (clearFreshF _ .open .none)
    · by_cases hr : p = ring.rightNeighbor e
      · subst p; rw [rightGoodF hψ h2 ring C e hb hs]
        cases ht : atTerminalB (C (ring.rightNeighbor e)) with
        | true => exact Or.inr (by simpa [ht] using clearFreshF (C (ring.rightNeighbor e)) .open .none)
        | false => exact Or.inr (by simpa [ht] using clearFreshF (C (ring.rightNeighbor e)) .releasing .openR)
      · rw [stepV3_other hψ h2 ring C e p hp hr]; exact h
  · have hsF := boolFalseF _ hs
    by_cases hp : p = e
    · subst p; rw [leftBadF hψ h2 ring C e hb hsF]
      left; simp [PhaseOwnedV31, startClosing, setControl]
    · rw [badOtherF hψ h2 ring C e p hb hsF hp]; exact h

private theorem tokenSourceF
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n) (t : TokenV3)
    (hn : t ≠ .none) (ho : t ≠ .openR) (hk : t ≠ .seek)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (ht : (stepV3 hψ h2 ring C e p).ctl.tok = t) :
    stepV3 hψ h2 ring C e p = C p := by
  by_cases hs : successorB (C e) (C (ring.rightNeighbor e)) = true
  · by_cases hp : p = e
    · subst p; rw [leftGoodF hψ h2 ring C e hb hs] at ht
      have x : (TokenV3.none : TokenV3) = t := by simpa [setControl] using ht
      exact (hn x.symm).elim
    · by_cases hr : p = ring.rightNeighbor e
      · subst p; rw [rightGoodF hψ h2 ring C e hb hs] at ht
        cases hz : atTerminalB (C (ring.rightNeighbor e)) with
        | true =>
            have x : (TokenV3.none : TokenV3) = t := by simpa [hz, setControl] using ht
            exact (hn x.symm).elim
        | false =>
            have x : TokenV3.openR = t := by simpa [hz, setControl] using ht
            exact (ho x.symm).elim
      · exact stepV3_other hψ h2 ring C e p hp hr
  · have hsF := boolFalseF _ hs
    by_cases hp : p = e
    · subst p; rw [leftBadF hψ h2 ring C e hb hsF] at ht
      have x : TokenV3.seek = t := by simpa [startClosing, setControl] using ht
      exact (hk x.symm).elim
    · exact badOtherF hψ h2 ring C e p hb hsF hp

private theorem gpF (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change R2Coherence.fwd ring (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [h i]

private theorem ppF (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val-k) =
    R2Coherence.back ring i ((raw (C i)).label.val-k)
  rw [h i]

private theorem pendingBackF
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (h : PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) owner) :
    PendingOpenROwnerV31 ring C owner := by
  rcases h with ⟨hs, hu, hr⟩
  have heq := tokenSourceF hψ h2 ring C e (ring.rightNeighbor owner) .scrubL
    (by decide) (by decide) (by decide) hb hs
  refine ⟨?_, ?_, ?_⟩
  · rw [← heq]; exact hs
  · have hl := congrArg Fin.val (stepV3_labels_eq_or_held hψ h2 ring C e owner)
    have hh := congrArg Fin.val (stepV3_labels_eq_or_held hψ h2 ring C e (ring.rightNeighbor owner))
    unfold successorB at hu ⊢; simpa only [hl, hh] using hu
  · have hl := congrArg Fin.val (stepV3_labels_eq_or_held hψ h2 ring C e owner)
    unfold atRootB at hr ⊢; simpa only [hl] using hr

private theorem sweepBackF
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e sweep : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (h : (stepV3 hψ h2 ring C e sweep).ctl.tok = .sweep) :
    (C sweep).ctl.tok = .sweep := by
  have heq := tokenSourceF hψ h2 ring C e sweep .sweep
    (by decide) (by decide) (by decide) hb h
  rw [← heq]; exact h

private theorem readBackF
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e sweep p : Fin n)
    (h : InSweepWideReadV31 ring (stepV3 hψ h2 ring C e) sweep p) :
    InSweepWideReadV31 ring C sweep p := by
  unfold InSweepWideReadV31 at h ⊢
  rcases h with h | ⟨d, hp⟩
  · exact Or.inl h
  · right
    have hv := congrArg Fin.val (stepV3_labels_eq_or_held hψ h2 ring C e sweep)
    have hd : d.val < ψ-(raw (C sweep)).label.val := by simpa only [hv] using d.isLt
    let dc : Fin (ψ-(raw (C sweep)).label.val) := ⟨d.val, hd⟩
    exact ⟨dc, by simpa [dc] using hp⟩

private theorem footBackF
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner p : Fin n)
    (h : InOpenRFreshFootprintV31 ring (stepV3 hψ h2 ring C e) owner p) :
    InOpenRFreshFootprintV31 ring C owner p := by
  let D : FC n ψ κ τ := stepV3 hψ h2 ring C e
  change InOpenRFreshFootprintV31 ring D owner p at h
  have hL : ∀ x, (raw (D x)).label = (raw (C x)).label := by
    intro x
    simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e x
  rcases h with ⟨j, ko, q, ho, kD, hp⟩
  rw [gpF ring hL j ko.val] at ho
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hFront : R2Coherence.groupPos ring (eraseCfgV3 D) j q.val = front := by
    simpa [front] using gpF ring hL j q.val
  have hv :
      (raw (D (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val))).label.val =
        (raw (C front)).label.val := by
    rw [hFront]
    exact congrArg Fin.val (hL front)
  have hk : kD.val < (raw (C front)).label.val + 1 := by
    simpa only [hv] using kD.isLt
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hk⟩
  refine ⟨j, ko, q, ho, kC, ?_⟩
  have h0 : R2Coherence.prefixPos ring (eraseCfgV3 D) front kD.val = p := by
    simpa only [hFront] using hp
  simpa [front, kC] using (ppF ring hL front kD.val).symm.trans h0

/-- The corrected Fresh sentence is preserved by OPEN-R. -/
theorem sweepPendingOpenRFootprintOwnedV31F_openR_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hF : SweepPendingOpenRFootprintOwnedV31F ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR) :
    SweepPendingOpenRFootprintOwnedV31F ring (stepV3 hψ h2 ring C e) := by
  intro sweep owner p hs hp hr hf
  have hsC := sweepBackF hψ h2 ring C e sweep hb hs
  have hpC := pendingBackF hψ h2 ring C e owner hb hp
  have hrC := readBackF hψ h2 ring C e sweep p hr
  have hfC := footBackF hψ h2 ring C e owner p hf
  exact ownedOrFreshStepF hψ h2 ring C e p hb (hF sweep owner p hsC hpC hrC hfC)

/-- The left-overlap witness now lands in the freshness arm. -/
theorem openR_good_left_overlap_satisfies_R2F_point
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    PhaseOwnedV31 (stepV3 hψ h2 ring C e e) ∨
      FreshnessClearV31 (stepV3 hψ h2 ring C e e) := by
  right
  rw [leftGoodF hψ h2 ring C e hb hs]
  exact clearFreshF _ .open .none

end R2CoherenceV31StrongR2Route
