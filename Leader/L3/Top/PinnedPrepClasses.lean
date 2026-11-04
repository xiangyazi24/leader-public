import Leader.L3.Top.PinnedRaceClasses
import Leader.L3.Top.PinnedPrepareAlign

/-!
# Q7 (P.12): the pinned classes whose misplaced and favourable cuts carry the settled bookkeeping

The alignment of the pending suffix after a favourable front (`k % r = 0`) is a statement about
the export indices of the settled registers, which no static clause of
`topClockPinnedFavClasses` records.  The class value `topClockPrepClasses` changes exactly the
clauses `misplacedTail` and `favourable` (and the specs of these two) of
`topClockPinnedFavClasses`:

* `misplacedTail` also asks `PuPin`: the cut extends a permanent first-tail cut `Y0`, has no old
  pending input, and satisfies the pending-or-settled labelled window invariant `PuLinv` and
  `PuAll` with respect to the clock of `Y0`;
* `favourable` also asks `PuPin` of the misplaced cut just before the front is formed.

The race lands in the new classes: an edge off the race edges keeps the cut misplaced, front-free
and carry-free, hence keeps `PuPin` (`pupin_next`); the outgoing edge forms the front from a cut
that satisfies `PuPin`.  The phases P.4--P.11 and the unfavourable phase read neither clause and
transfer by `exact`.

Consumer: `TopClockPhaseBundle.cuts` (TopClockAssembly).
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- **Pinned with the settled bookkeeping**: the state extends a permanent first-tail cut `Y0`,
has no pending input old with respect to the clock of `Y0`, and satisfies the pending-or-settled
labelled window invariant and `PuAll` with respect to that clock.

Consumer: `topClockPrepClasses`. -/
def PuPin {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Prop :=
  ∃ Y0 : TopFixedTraceState n, topFreshTailPermanentCut ring C s Y0 ∧
    MarkedFrom ring C Y0 Z ∧ topClockNoOldPending s Z Y0.1.2.clock ∧
    PuLinv s Z Y0.1.2.clock ∧ PuAllAt s Z Y0.1.2.clock

/-- A state with the settled bookkeeping is pinned.

Consumer: `topClockPrepClasses`. -/
theorem pupin_pinned {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (h : PuPin ring C s Z) :
    topClockPinned ring C s Z := by
  obtain ⟨Y0, hcut, hfrom, hold, _⟩ := h
  exact ⟨Y0, hcut, hfrom, hold⟩

/-- The exports after the clock of a permanent cut have operands, at every state extending it.

Consumer: `pupin_next`. -/
theorem pinned_hnone {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Y0 Y : TopFixedTraceState n) (hcut : topFreshTailPermanentCut ring C s Y0)
    (hY : MarkedFrom ring C Y0 Y) :
    ∀ ex ∈ topClockConcreteExportsAfter s Y Y0.1.2.clock, ex.operand ≠ none := by
  obtain ⟨hreach0, _, anchor, hanchor, htime, hfuture⟩ := hcut
  obtain ⟨w, hw⟩ := hY
  have hpure : topClockConcretePureStream s Y anchor := by
    rw [hw]
    exact hfuture w
  intro ex hex
  rw [← htime] at hex
  obtain ⟨i, hi, hexi⟩ := List.getElem_of_mem hex
  obtain ⟨sample, _, _, _, _, hop, _, _⟩ := hpure ⟨i, hi⟩
  intro hnn
  have h1 : (topClockConcreteExportAt s Y anchor.time ⟨i, hi⟩).operand = none := by
    show (topClockConcreteExportsAfter s Y anchor.time)[i].operand = none
    rw [hexi]
    exact hnn
  rw [hop] at h1
  exact absurd h1 (by simp)

/-- **The settled bookkeeping survives a letter** whose successor window is front-free and
carry-free.

Consumer: `topPrepRacePhase`. -/
theorem pupin_next {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y : TopFixedTraceState n) (e : Fin n)
    (hP : PuPin ring C s Y)
    (hfree : puFree (topClockSpan n) (cellOf s (topFixedTraceNext ring C Y e))) :
    PuPin ring C s (topFixedTraceNext ring C Y e) := by
  obtain ⟨Y0, hcut, hfrom, hold, hl, ha⟩ := hP
  have hreach : topClockReached ring C Y := markedFrom_reached ring C Y0 Y hfrom
  have hclock : Y0.1.2.clock ≤ Y.1.2.clock := markedFrom_clock ring C Y0 Y hcut.1 hfrom
  have hfrom' := markedFrom_next ring C Y0 Y e hfrom
  have hnone := pinned_hnone ring C s Y0 _ hcut hfrom'
  exact ⟨Y0, hcut, hfrom', noOld_next ring C s hg Y0.1.2.clock Y hreach hclock e hold,
    pulinv_step ring C s hg _ Y hreach hclock e hnone hfree hl,
    pulinv_all_step ring C s hg _ Y hreach hclock e hnone hfree hl ha⟩

/-- A misplaced-tail cut is front-free and carry-free.

Consumer: `topPrepRacePhase`. -/
theorem misAt_free {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (h : Fin (topClockSpan n))
    (hm : topClockConcreteMisplacedAt s Z h) : puFree (topClockSpan n) (cellOf s Z) := by
  obtain ⟨hL, hR, _⟩ := misAt_cells s Z h hm
  intro j hj
  by_cases hjh : j < h.val
  · obtain ⟨hep, hc⟩ := hL j hjh
    refine ⟨hc, ?_⟩
    intro hx
    rcases hep with he | hp
    · rw [hx] at he; exact absurd he (by decide)
    · rw [hx] at hp; exact absurd hp (by simp [Inp.isP])
  · obtain ⟨hs, hc⟩ := hR j (by omega) hj
    refine ⟨hc, ?_⟩
    intro hx
    rw [hx] at hs
    exact absurd hs (by simp [Inp.isS])

/-- **The pinned classes with the settled bookkeeping.**

Consumer: `TopClockPhaseBundle.cuts` (TopClockAssembly). -/
noncomputable def topClockPrepClasses {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) : TopClockCutClasses ring C s :=
  { topClockPinnedFavClasses ring C s with
    misplacedTail := fun Z =>
      PuPin ring C s Z ∧ (topClockStrongClasses ring C s).misplacedTail Z
    favourable := fun Z =>
      topClockPinned ring C s Z ∧ MarkedDown ring C s Z ∧
        topClockConcreteFavourable ring C s Z ∧
        ∃ (pre : List (Fin n)) (e : Fin n), Z.2 = pre ++ [e] ∧
          PuPin ring C s (topFixedTraceRun ring C pre)
    misplacedSpec := by
      intro Z h
      exact (topClockStrongClasses ring C s).misplacedSpec Z h.2
    favourableSpec := by
      intro Z h
      exact h.2.2.1.1 }

/-- P.4--P.5 for the classes with the settled bookkeeping.

Consumer: `TopClockPhaseBundle.marked` (TopClockAssembly). -/
theorem topPrepMarkedPhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockMarkedDebtPhase ring C s (topClockPrepClasses ring C s) :=
  topClockPinnedMarkedPhase ring hn C s hl hbad

/-- P.6--P.10 for the classes with the settled bookkeeping.

Consumer: `TopClockPhaseBundle.settled` (TopClockAssembly). -/
theorem topPrepSettledPhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockSettledWorkPhase ring C s (topClockPrepClasses ring C s) :=
  topClockPinnedSettledWorkPhase ring hn C s hl hbad

/-- P.11 for the classes with the settled bookkeeping.

Consumer: `TopClockPhaseBundle.mobile` (TopClockAssembly). -/
theorem topPrepMobilePhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockFinalMobilePhase ring C s (topClockPrepClasses ring C s) :=
  topClockPinnedMobilePhase ring hn C s hl hbad

/-- P.13 unfavourable branch for the classes with the settled bookkeeping.

Consumer: `TopClockPhaseBundle.unfavourable` (TopClockAssembly). -/
theorem topPrepUnfavourablePhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockUnfavourablePhase ring C s (topClockPrepClasses ring C s) :=
  topPinnedUnfavourablePhase ring hn C s hl hbad

/-- **P.12 race for the classes with the settled bookkeeping.**

Consumer: `TopClockPhaseBundle.race` (TopClockAssembly). -/
theorem topPrepRacePhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockRacePhase ring C s (topClockPrepClasses ring C s) := by
  classical
  have hg : WinGeo ring C s := ⟨hn, hl, hbad⟩
  intro Z hZ
  have hn0 : 0 < n := by omega
  let Pt : TopFixedTraceState n → Prop := fun Y =>
    topFixedStrictStop ring C s Y ∨ (topClockPrepClasses ring C s).favourable Y ∨
      (topClockPrepClasses ring C s).unfavourable Y
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C) Pt hn0 Z n).2
  intro T
  by_cases hstop : topFixedStrictStop ring C s Z
  · rw [costNumerator_terminal _ _ Z (Or.inl hstop) T]
    exact Nat.zero_le _
  · have hmis : (topClockPrepClasses ring C s).misplacedTail Z := by
      rcases hZ with h | h
      · exact absurd h hstop
      · exact h
    obtain ⟨hpu, hdown, hreach, hpure, hsuf, h, hh⟩ := hmis
    let R : TopFixedTraceState n → Prop := fun Y =>
      PuPin ring C s Y ∧ topClockConcreteMisplacedAt s Y h
    let I : TopFixedTraceState n → Prop := fun Y => R Y ∨ Pt Y
    have hreachR : ∀ Y, R Y → topClockReached ring C Y := by
      intro Y hY
      obtain ⟨Y0, _, hfrom, _⟩ := hY.1
      exact markedFrom_reached ring C Y0 Y hfrom
    have hfav : ∀ Y, R Y →
        (topClockPrepClasses ring C s).favourable
          (topFixedTraceNext ring C Y (winSite s h.val)) := by
      intro Y hR
      have hpin := pupin_pinned ring C s Y hR.1
      have hfv := race_favourable ring C s hg Y h hpin hR.2
      have hreachY := hreachR Y hR
      refine ⟨topPreparationPinnedNext ring C s hg Y _ hpin, hfv.1, ⟨hfv.2.1, hfv.2.2⟩, Y.2,
        winSite s h.val, rfl, ?_⟩
      rw [← hreachY]
      exact hR.1
    have hcost := topFinalCostOfRows (topFixedTraceNext ring C) I Pt (fun _ => 1)
      (fun _ => winSite s h.val)
      (by
        intro Y hI hnot e
        rcases hI with hR | hP
        · by_cases he1 : e = winSite s h.val
          · subst he1
            exact Or.inr (Or.inr (Or.inl (hfav Y hR)))
          · by_cases he2 : e = winSite s (h.val - 1)
            · subst he2
              exact Or.inr (Or.inr (Or.inr (by
                have := race_unfavourable ring C s hg Y h (pupin_pinned ring C s Y hR.1) hR.2
                exact this)))
            · have hmo := misAt_off ring C s hg Y (hreachR Y hR) h hR.2 e he1 he2
              exact Or.inl ⟨pupin_next ring C s hg Y e hR.1 (misAt_free s _ h hmo), hmo⟩
        · exact absurd hP hnot)
      (fun _ _ _ => by omega)
      (fun Y _ _ e => Or.inr (Nat.le_refl _))
      (by
        intro Y hI hnot
        rcases hI with hR | hP
        · exact Or.inl (Or.inr (Or.inl (hfav Y hR)))
        · exact absurd hP hnot)
      Z (Or.inl ⟨hpu, hh⟩) T
    exact Nat.le_trans hcost (by simp)

/-- A favourable cut of the classes with the settled bookkeeping is a favourable cut of the
pinned-favourable classes.

Consumer: `topPrepFavClear`, and every helper stated for `topClockPinnedFavClasses`. -/
theorem prepFavourable_forget {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n)
    (h : (topClockPrepClasses ring C s).favourable Z) :
    (topClockPinnedFavClasses ring C s).favourable Z :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- A misplaced cut of the classes with the settled bookkeeping is a misplaced cut of the
pinned-favourable classes.

Consumer: `Leader/L3/TopPinnedPrepareFav.lean`. -/
theorem prepMisplaced_forget {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n)
    (h : (topClockPrepClasses ring C s).misplacedTail Z) :
    (topClockPinnedFavClasses ring C s).misplacedTail Z :=
  ⟨pupin_pinned ring C s Z h.1, h.2⟩

/-- **P.12 favourable, clearing stage for the classes with the settled bookkeeping**: from a
favourable cut the pinned pending-only class is reached within mean `n * r`.

Consumer: `Leader/L3/TopPinnedPrepareFav.lean`. -/
theorem topPrepFavClear {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) (Z : TopFixedTraceState n)
    (hZ : (topClockPrepClasses ring C s).favourable Z) :
    UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C)
      (topClockPrepClasses ring C s).pendingOnly Z ((n * topClockSpan n : Nat) : Rat) :=
  topPinnedFavourableClear ring hn C s hl hbad Z hZ.1 hZ.2.2.1

end MarkedCells
end L3

#print axioms L3.MarkedCells.pupin_next
#print axioms L3.MarkedCells.topPrepRacePhase
#print axioms L3.MarkedCells.topPrepUnfavourablePhase
#print axioms L3.MarkedCells.topPrepFavClear
