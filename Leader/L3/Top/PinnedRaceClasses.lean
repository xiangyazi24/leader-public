import Leader.L3.Top.PinnedRaceClear

/-!
# Q7 (P.12): the pinned classes with a pinned favourable class

`topClockPinnedClasses` inherits the favourable class of `topClockStrongClasses`: `MarkedDown`
and the concrete favourable shape.  `MarkedDown` does not carry the pin (no old pending input after
the clock of the permanent cut), so a favourable cut of that class cannot start the clearing and
completion stages.  The class value `topClockPinnedFavClasses` changes exactly one clause: the
favourable class also asks `topClockPinned`.  The race lands in it (the successor of a pinned cut
is pinned), and the phases P.4--P.11 and the unfavourable phase do not read the favourable class,
so they transfer unchanged.

Consumer: `TopClockPhaseBundle.cuts` (TopClockAssembly).
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- **The pinned classes with a pinned favourable class.**

Consumer: `TopClockPhaseBundle.cuts` (TopClockAssembly). -/
noncomputable def topClockPinnedFavClasses {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) : TopClockCutClasses ring C s :=
  { topClockPinnedClasses ring C s with
    favourable := fun Z => topClockPinned ring C s Z ∧ MarkedDown ring C s Z ∧
      topClockConcreteFavourable ring C s Z
    favourableSpec := by
      intro Z h
      exact h.2.2.1 }

/-- P.4--P.5 for the pinned-favourable classes.

Consumer: `TopClockPhaseBundle.marked` (TopClockAssembly). -/
theorem topPinnedFavMarkedPhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockMarkedDebtPhase ring C s (topClockPinnedFavClasses ring C s) :=
  topClockPinnedMarkedPhase ring hn C s hl hbad

/-- P.6--P.10 for the pinned-favourable classes.

Consumer: `TopClockPhaseBundle.settled` (TopClockAssembly). -/
theorem topPinnedFavSettledPhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockSettledWorkPhase ring C s (topClockPinnedFavClasses ring C s) :=
  topClockPinnedSettledWorkPhase ring hn C s hl hbad

/-- P.11 for the pinned-favourable classes.

Consumer: `TopClockPhaseBundle.mobile` (TopClockAssembly). -/
theorem topPinnedFavMobilePhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockFinalMobilePhase ring C s (topClockPinnedFavClasses ring C s) :=
  topClockPinnedMobilePhase ring hn C s hl hbad

/-- P.13 unfavourable branch for the pinned-favourable classes.

Consumer: `TopClockPhaseBundle.unfavourable` (TopClockAssembly). -/
theorem topPinnedFavUnfavourablePhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockUnfavourablePhase ring C s (topClockPinnedFavClasses ring C s) :=
  topPinnedUnfavourablePhase ring hn C s hl hbad

/-- **P.12 race for the pinned-favourable classes.**

Consumer: `TopClockPhaseBundle.race` (TopClockAssembly). -/
theorem topPinnedFavRacePhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockRacePhase ring C s (topClockPinnedFavClasses ring C s) := by
  classical
  have hg : WinGeo ring C s := ⟨hn, hl, hbad⟩
  intro Z hZ
  have hn0 : 0 < n := by omega
  let Pt : TopFixedTraceState n → Prop := fun Y =>
    topFixedStrictStop ring C s Y ∨ (topClockPinnedFavClasses ring C s).favourable Y ∨
      (topClockPinnedFavClasses ring C s).unfavourable Y
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C) Pt hn0 Z n).2
  intro T
  by_cases hstop : topFixedStrictStop ring C s Z
  · rw [costNumerator_terminal _ _ Z (Or.inl hstop) T]
    exact Nat.zero_le _
  · have hmis : (topClockPinnedClasses ring C s).misplacedTail Z := by
      rcases hZ with h | h
      · exact absurd h hstop
      · exact h
    obtain ⟨hpin, hdown, hreach, hpure, hsuf, h, hh⟩ := hmis
    let R : TopFixedTraceState n → Prop := fun Y =>
      topClockPinned ring C s Y ∧ topClockConcreteMisplacedAt s Y h
    let I : TopFixedTraceState n → Prop := fun Y => R Y ∨ Pt Y
    have hreachR : ∀ Y, R Y → topClockReached ring C Y := by
      intro Y hY
      obtain ⟨Y0, _, hfrom, _⟩ := hY.1
      exact markedFrom_reached ring C Y0 Y hfrom
    have hfav : ∀ Y, R Y →
        (topClockPinnedFavClasses ring C s).favourable
          (topFixedTraceNext ring C Y (winSite s h.val)) := by
      intro Y hR
      exact ⟨topPreparationPinnedNext ring C s hg Y _ hR.1,
        race_favourable ring C s hg Y h hR.1 hR.2⟩
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
              exact Or.inr (Or.inr (Or.inr (race_unfavourable ring C s hg Y h hR.1 hR.2)))
            · exact Or.inl ⟨topPreparationPinnedNext ring C s hg Y e hR.1,
                misAt_off ring C s hg Y (hreachR Y hR) h hR.2 e he1 he2⟩
        · exact absurd hP hnot)
      (fun _ _ _ => by omega)
      (fun Y _ _ e => Or.inr (Nat.le_refl _))
      (by
        intro Y hI hnot
        rcases hI with hR | hP
        · exact Or.inl (Or.inr (Or.inl (hfav Y hR)))
        · exact absurd hP hnot)
      Z (Or.inl ⟨hpin, hh⟩) T
    exact Nat.le_trans hcost (by simp)

/-- **P.12 favourable, clearing stage for the pinned-favourable classes**: from a favourable cut
the pinned pending-only class is reached within mean `n * r`.

Consumer: `TopClockPhaseBundle.favourable` (TopClockAssembly), first stage. -/
theorem topPinnedFavClear {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) (Z : TopFixedTraceState n)
    (hZ : (topClockPinnedFavClasses ring C s).favourable Z) :
    UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C)
      (topClockPinnedFavClasses ring C s).pendingOnly Z ((n * topClockSpan n : Nat) : Rat) :=
  topPinnedFavourableClear ring hn C s hl hbad Z hZ.1 hZ.2.2

end MarkedCells
end L3

#print axioms L3.MarkedCells.topPinnedFavMarkedPhase
#print axioms L3.MarkedCells.topPinnedFavSettledPhase
#print axioms L3.MarkedCells.topPinnedFavMobilePhase
#print axioms L3.MarkedCells.topPinnedFavUnfavourablePhase
#print axioms L3.MarkedCells.topPinnedFavRacePhase
#print axioms L3.MarkedCells.topPinnedFavClear
