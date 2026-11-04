import Leader.L3.Top.SuffixFinalMobile

/-!
Partial P.12--P.13 preparation and race results for the fixed
topClockFinalClasses at the pinned leaderless bad-pair entrance.

This module records physical continuation of an already pinned anchor,
the actual pure pending serial suffix, the nonborder tail's two genuine
distinct race edges and their actual OLD window inputs, and the
post-cut first-edge-selection clock on the real TopFixedTraceNext.

TopClockPreparationPhase and TopClockRacePhase themselves remain open.
The V(r) pending-work potential and the third-edge-hazard/race-outcome
classification are NOT supplied by the source theorems used here.
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The same permanent first-tail anchor survives one real edge.
Consumer: P.12 preparation and P.13 off-race-edge induction. -/
theorem topPreparationPinnedNext {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (h : topClockPinned ring C s Z) :
    topClockPinned ring C s (topFixedTraceNext ring C Z e) := by
  obtain ⟨Y0, hcut, hfrom, hold⟩ := h
  have hreach : topClockReached ring C Z :=
    markedFrom_reached ring C Y0 Z hfrom
  have hclock : Y0.1.2.clock ≤ Z.1.2.clock :=
    markedFrom_clock ring C Y0 Z hcut.1 hfrom
  exact ⟨Y0, hcut, markedFrom_next ring C Y0 Z e hfrom,
    noOld_next ring C s hg Y0.1.2.clock Z
      hreach hclock e hold⟩

/-- A pinned state supplies the original proof-only class's
consecutive pending source serial suffix, not just E/P slot shape.
Consumer: P.12 source-to-pending correspondence. -/
theorem topPreparationPinnedSuffix {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s)
    (Z : TopFixedTraceState n)
    (h : topClockPinned ring C s Z) :
    (topClockFinalClasses ring C s).consecutivePendingSuffix Z := by
  obtain ⟨Y0, hcut, hfrom, hold⟩ := h
  change MarkedDown ring C s Z ∧
    topClockConcreteConsecutivePendingSuffix s Z
  exact ⟨markedFrom_down ring C s Y0 Z hcut hfrom,
    suffix_of_pinned ring C s hg Y0 Z hcut hfrom hold⟩

/-- One actual physical edge preserves both the pinned anchor and
the serial-suffix class, even on an edge accepting a new packet.
Consumer: P.12/P.13 state provenance. -/
theorem topPreparationPinnedSuffixNext {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (h : topClockPinned ring C s Z) :
    topClockPinned ring C s (topFixedTraceNext ring C Z e) ∧
    (topClockFinalClasses ring C s).consecutivePendingSuffix
      (topFixedTraceNext ring C Z e) := by
  have hnext := topPreparationPinnedNext ring C s hg Z e h
  exact ⟨hnext,
    topPreparationPinnedSuffix ring C s hg
      (topFixedTraceNext ring C Z e) hnext⟩

/-- The P.12 outgoing and incoming sites around a nonborder tail
are distinct physical directed scheduler edges.
Consumer: the two-edge conditional race. -/
theorem topPreparationRaceEdgesDistinct {n : Nat}
    (hn : 5 ≤ n) (s : Fin n)
    (h : Fin (topClockSpan n)) (hleft : 1 ≤ h.val) :
    winSite s h.val ≠ winSite s (h.val - 1) := by
  intro heq
  have hindices : h.val = h.val - 1 :=
    winSite_inj hn s h.val (h.val - 1)
      (by omega : h.val ≤ topClockSpan n)
      (by omega : h.val - 1 ≤ topClockSpan n) heq
  omega

/-- The misplaced-tail cut contains a concrete nonborder tail
and two distinct edges.  Consumer: P.12 race preparation. -/
theorem topPreparationMisplacedEdges {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (hmis : (topClockFinalClasses ring C s).misplacedTail Z) :
    ∃ h : Fin (topClockSpan n),
      topClockConcreteMisplacedAt s Z h ∧
      winSite s h.val ≠ winSite s (h.val - 1) := by
  change MarkedDown ring C s Z ∧
    topClockConcreteMisplacedTail ring C s Z at hmis
  obtain ⟨_, _, _, h, hh⟩ := hmis.2
  exact ⟨h, hh, topPreparationRaceEdgesDistinct hn s h hh.1⟩

/-- The exact old QI input guards at the misplaced-tail edge:
the source contains S(true), its RIGHT neighbour contains S(false),
and ALL target carries are OFF.  In particular, the existing
topPortPhysicalQITailConverts lemma with right-input E is not
directly applicable.  Consumer: the missing physical f_h winning
row, not a replacement for it. -/
theorem topPreparationMisplacedOwnerWindow {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n)
    (h : Fin (topClockSpan n))
    (hh : topClockConcreteMisplacedAt s Z h) :
    ∃ (v w : Fin (compileAdvice (ceilLogTwo n)).topA),
      topClockConcreteInputAt s Z h = .S v true ∧
      (∃ j : Fin (topClockSpan n),
        j.val = h.val + 1 ∧
        topClockConcreteInputAt s Z j = .S w false) ∧
      (∀ j : Fin (topClockSpan n),
        topClockConcreteCarryAt s Z j = .OFF) := by
  obtain ⟨sample, _, _, _, _, htail, _⟩ := hh.2.2.1
  obtain ⟨nextSample, _, _, _, _, hsettled, _⟩ :=
    hh.2.2.2.1
      (⟨h.val + 1, hh.2.1⟩ : Fin (topClockSpan n))
      (show h.val < h.val + 1 by omega)
  exact ⟨sample.value, nextSample.value, htail,
    ⟨⟨h.val + 1, hh.2.1⟩, rfl, hsettled⟩,
    hh.2.2.2.2.2⟩

/-- The physical trace extends one specific fixed cut's word.
Consumer: a race event that cannot count pre-cut services. -/
def topPreparationTraceExtends {n : Nat}
    (Z Y : TopFixedTraceState n) : Prop :=
  ∃ word : List (Fin n), Y.2 = Z.2 ++ word

/-- A nominated edge has been selected AFTER cut Z and is the
last physical service in Y.  Consumer: edge-clock P.12 lemma. -/
def topPreparationRaceSelectedAfter {n : Nat}
    (s : Fin n) (h : Fin (topClockSpan n))
    (Z Y : TopFixedTraceState n) : Prop :=
  ∃ word : List (Fin n),
    Y.2 = Z.2 ++ word ++ [winSite s h.val] ∨
    Y.2 = Z.2 ++ word ++ [winSite s (h.val - 1)]

/-- A one-bit stopped first-edge-selection potential, not the
V(r)-bounded preparation-work potential of P.12. -/
noncomputable def topPreparationRaceEdgePotential {n : Nat}
    (s : Fin n) (h : Fin (topClockSpan n))
    (Z Y : TopFixedTraceState n) : Nat :=
  if topPreparationRaceSelectedAfter s h Z Y then 0 else 1

/-- On the actual uniformly scheduled TopFixedTraceNext chain,
the first nominated edge served AFTER the given cut has mean
at most n.  No hazard-free race outcome or 1/2 fair branch
has been inferred. Consumer: P.12 race timing substep. -/
theorem topPreparationRaceEdgeClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (h : Fin (topClockSpan n))
    (Z : TopFixedTraceState n) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (topFixedTraceNext ring C)
      (topPreparationRaceSelectedAfter s h Z)
      Z ((n : Nat) : Rat) := by
  classical
  have hclosed :
      ∀ Y : TopFixedTraceState n,
        topPreparationTraceExtends Z Y →
        ¬ topPreparationRaceSelectedAfter s h Z Y →
        ∀ e : Fin n,
          topPreparationTraceExtends Z
            (topFixedTraceNext ring C Y e) := by
    intro Y hY _ e
    obtain ⟨word, hw⟩ := hY
    refine ⟨word ++ [e], ?_⟩
    change Y.2 ++ [e] = Z.2 ++ (word ++ [e])
    rw [hw, List.append_assoc]
  have hpositive :
      ∀ Y : TopFixedTraceState n,
        topPreparationTraceExtends Z Y →
        ¬ topPreparationRaceSelectedAfter s h Z Y →
        0 < topPreparationRaceEdgePotential s h Z Y := by
    intro Y _ hnot
    unfold topPreparationRaceEdgePotential
    rw [if_neg hnot]
    omega
  have hnonincrease :
      ∀ Y : TopFixedTraceState n,
        topPreparationTraceExtends Z Y →
        ¬ topPreparationRaceSelectedAfter s h Z Y →
        ∀ e : Fin n,
          topPreparationRaceSelectedAfter s h Z
              (topFixedTraceNext ring C Y e) ∨
            topPreparationRaceEdgePotential s h Z
              (topFixedTraceNext ring C Y e) ≤
            topPreparationRaceEdgePotential s h Z Y := by
    intro Y _ hnot e
    right
    change (if topPreparationRaceSelectedAfter s h Z
        (topFixedTraceNext ring C Y e) then 0 else 1) ≤
      (if topPreparationRaceSelectedAfter s h Z Y then 0 else 1)
    rw [if_neg hnot]
    split <;> omega
  have hdrop :
      ∀ Y : TopFixedTraceState n,
        topPreparationTraceExtends Z Y →
        ¬ topPreparationRaceSelectedAfter s h Z Y →
        topPreparationRaceSelectedAfter s h Z
            (topFixedTraceNext ring C Y (winSite s h.val)) ∨
          topPreparationRaceEdgePotential s h Z
              (topFixedTraceNext ring C Y (winSite s h.val)) + 1 ≤
            topPreparationRaceEdgePotential s h Z Y := by
    intro Y hY _
    left
    obtain ⟨word, hw⟩ := hY
    refine ⟨word, Or.inl ?_⟩
    change Y.2 ++ [winSite s h.val] =
      Z.2 ++ word ++ [winSite s h.val]
    rw [hw, List.append_assoc]
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C)
    (topPreparationRaceSelectedAfter s h Z)
    (by omega : 0 < n) Z n).2
  intro T
  have hstart : topPreparationTraceExtends Z Z :=
    ⟨[], by simp⟩
  have hbound := topFinalCostOfRows
    (topFixedTraceNext ring C)
    (topPreparationTraceExtends Z)
    (topPreparationRaceSelectedAfter s h Z)
    (topPreparationRaceEdgePotential s h Z)
    (fun _ => winSite s h.val)
    hclosed hpositive hnonincrease hdrop Z hstart T
  have hvalue : topPreparationRaceEdgePotential s h Z Z ≤ 1 := by
    unfold topPreparationRaceEdgePotential
    split <;> omega
  have hscale :
      n * topPreparationRaceEdgePotential s h Z Z ≤ n := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left n hvalue
  exact Nat.le_trans hbound
    (Nat.mul_le_mul_left (n ^ T) hscale)

/-- Each final misplaced cut has the actual QI tail guard and
two distinct physical edges; one of those edges is encountered
within n expected interactions AFTER that cut.  No implication
to favourable/unfavourable cuts is claimed.
Consumer: P.12 physical race classification. -/
theorem topPreparationMisplacedRaceEdgeClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (hmis : (topClockFinalClasses ring C s).misplacedTail Z) :
    ∃ h : Fin (topClockSpan n),
      topClockConcreteMisplacedAt s Z h ∧
      winSite s h.val ≠ winSite s (h.val - 1) ∧
      UniformFirstHit.ExpectedHittingTimeAtMost
        (topFixedTraceNext ring C)
        (topPreparationRaceSelectedAfter s h Z)
        Z ((n : Nat) : Rat) := by
  obtain ⟨h, hh, hne⟩ :=
    topPreparationMisplacedEdges ring hn C s Z hmis
  exact ⟨h, hh, hne,
    topPreparationRaceEdgeClock ring hn C s h Z⟩

end MarkedCells
end L3

#print axioms L3.MarkedCells.topPreparationPinnedNext
#print axioms L3.MarkedCells.topPreparationPinnedSuffix
#print axioms L3.MarkedCells.topPreparationPinnedSuffixNext
#print axioms L3.MarkedCells.topPreparationRaceEdgesDistinct
#print axioms L3.MarkedCells.topPreparationMisplacedEdges
#print axioms L3.MarkedCells.topPreparationMisplacedOwnerWindow
#print axioms L3.MarkedCells.topPreparationRaceEdgeClock
#print axioms L3.MarkedCells.topPreparationMisplacedRaceEdgeClock
