import Leader.L3.Top.PinnedPhaseStop

/-!
# Q7 (P.12): the classes without an earlier strict stop

`topFixedStrictStop` asks for the minimal strict terminal of the whole audit (see
`TopPinnedPhaseStop`), so a state with a strict terminal already in its audit never stops
strictly later.  The class value `topClockStopClasses` is `topClockPrepClasses` with
`NoPrefixStop` conjoined to the clauses `firstTail`, `coloured`, `settledEmpty`, `pendingOnly`,
`misplacedTail`, `favourable` and `unfavourable` (and the specs of these clauses).

The three clauses `pendingOnly`, `misplacedTail`, `favourable` are the ones the preparation and
favourable phases read; the other four carry the same conjunct because each of their phases starts
from a state of that clause: a source state with an earlier strict stop could not reach a target
that asks for `NoPrefixStop`.

Every proved phase transfers: the invariant `NoPrefixStop ∨ strictStop` is closed along every
path that has not hit the target (`noPrefixStop_next`), so strengthening the target by
`NoPrefixStop` costs nothing (`phase_nps_hit`, through `topFinalCostTargetOnClosed`).

Consumer: `TopClockPhaseBundle.cuts` (TopClockAssembly).
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- **The classes without an earlier strict stop.**

Consumer: `TopClockPhaseBundle.cuts` (TopClockAssembly). -/
noncomputable def topClockStopClasses {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) : TopClockCutClasses ring C s :=
  { topClockPrepClasses ring C s with
    firstTail := fun Z => (topClockPrepClasses ring C s).firstTail Z ∧ NoPrefixStop ring C s Z
    coloured := fun Z => (topClockPrepClasses ring C s).coloured Z ∧ NoPrefixStop ring C s Z
    settledEmpty := fun Z =>
      (topClockPrepClasses ring C s).settledEmpty Z ∧ NoPrefixStop ring C s Z
    pendingOnly := fun Z =>
      (topClockPrepClasses ring C s).pendingOnly Z ∧ NoPrefixStop ring C s Z
    misplacedTail := fun Z =>
      (topClockPrepClasses ring C s).misplacedTail Z ∧ NoPrefixStop ring C s Z
    favourable := fun Z =>
      (topClockPrepClasses ring C s).favourable Z ∧ NoPrefixStop ring C s Z
    unfavourable := fun Z =>
      (topClockPrepClasses ring C s).unfavourable Z ∧ NoPrefixStop ring C s Z
    firstTailSpec := fun Z h => (topClockPrepClasses ring C s).firstTailSpec Z h.1
    colouredSpec := fun Z h => (topClockPrepClasses ring C s).colouredSpec Z h.1
    settledSpec := fun Z h => (topClockPrepClasses ring C s).settledSpec Z h.1
    pendingSpec := fun Z h => (topClockPrepClasses ring C s).pendingSpec Z h.1
    misplacedSpec := fun Z h => (topClockPrepClasses ring C s).misplacedSpec Z h.1
    favourableSpec := fun Z h => (topClockPrepClasses ring C s).favourableSpec Z h.1
    unfavourableSpec := fun Z h =>
      ⟨(topClockPrepClasses ring C s).unfavourableSpec Z h.1, h.2⟩ }

/-- **Strengthening the target by `NoPrefixStop` costs nothing** from a state that has no earlier
strict stop (or stops now): any target `Q` that contains the strict stops and the `NoPrefixStop`
states of the target `T` is hit as fast as `T`.

Consumer: `topStopMarkedPhase`, `topStopSettledPhase`, `topStopMobilePhase`,
`topStopUnfavourablePhase`, `topStopRacePhase`, `topStopFavClear`. -/
theorem phase_nps_hit {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hn : 0 < n) (T Q : TopFixedTraceState n → Prop)
    (hQs : ∀ Y, topFixedStrictStop ring C s Y → Q Y)
    (hTQ : ∀ Y, NoPrefixStop ring C s Y → T Y → Q Y)
    (Z : TopFixedTraceState n)
    (hZ : NoPrefixStop ring C s Z ∨ topFixedStrictStop ring C s Z) (K : Nat)
    (h : UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C) T Z (K : Rat)) :
    UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C) Q Z (K : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C) Q hn Z K).2
  intro Tm
  have h1 := (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C) T hn Z K).1 h Tm
  have h2 := topFinalCostTargetOnClosed (topFixedTraceNext ring C)
    (fun Y => NoPrefixStop ring C s Y ∨ topFixedStrictStop ring C s Y) Q T
    (by
      intro x hx hnQ e
      rcases hx with hx | hx
      · by_cases hst : topFixedStrictStop ring C s (topFixedTraceNext ring C x e)
        · exact Or.inr hst
        · exact Or.inl (noPrefixStop_next ring C s x e hx hst)
      · exact absurd (hQs x hx) hnQ)
    (by
      intro x hx hTx
      rcases hx with hx | hx
      · exact hTQ x hx hTx
      · exact hQs x hx)
    Tm Z hZ
  exact Nat.le_trans h2 h1

/-- A member of the source class of a `NoPrefixStop`-strengthened clause is a strict stop or has
no earlier strict stop.

Consumer: every `topStop*Phase`. -/
theorem stopOr_nps_source {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (A : TopFixedTraceState n → Prop) (Z : TopFixedTraceState n)
    (h : topClockStopOr ring C s (fun Y => A Y ∧ NoPrefixStop ring C s Y) Z) :
    NoPrefixStop ring C s Z ∨ topFixedStrictStop ring C s Z := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h.2

/-- Generic transfer of a phase `A → B` to the strengthened clauses.

Consumer: `topStopMarkedPhase`, `topStopSettledPhase`, `topStopMobilePhase`,
`topStopUnfavourablePhase`. -/
theorem phase_nps_transfer {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hn : 0 < n) (A B : TopFixedTraceState n → Prop) (K : Nat)
    (h : ∀ Z, topClockStopOr ring C s A Z →
      UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C)
        (topClockStopOr ring C s B) Z (K : Rat)) :
    ∀ Z, topClockStopOr ring C s (fun Y => A Y ∧ NoPrefixStop ring C s Y) Z →
      UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C)
        (topClockStopOr ring C s (fun Y => B Y ∧ NoPrefixStop ring C s Y)) Z (K : Rat) := by
  intro Z hZ
  refine phase_nps_hit ring C s hn _ _ (fun Y hY => Or.inl hY) ?_ Z
    (stopOr_nps_source ring C s A Z hZ) K
    (h Z (by rcases hZ with hZ | hZ; exact Or.inl hZ; exact Or.inr hZ.1))
  intro Y hY hT
  rcases hT with hT | hT
  · exact Or.inl hT
  · exact Or.inr ⟨hT, hY⟩

/-- P.4--P.5 for the classes without an earlier strict stop.

Consumer: `TopClockPhaseBundle.marked` (TopClockAssembly). -/
theorem topStopMarkedPhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockMarkedDebtPhase ring C s (topClockStopClasses ring C s) :=
  phase_nps_transfer ring C s (by omega) _ _ _ (topPrepMarkedPhase ring hn C s hl hbad)

/-- P.6--P.10 for the classes without an earlier strict stop.

Consumer: `TopClockPhaseBundle.settled` (TopClockAssembly). -/
theorem topStopSettledPhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockSettledWorkPhase ring C s (topClockStopClasses ring C s) :=
  phase_nps_transfer ring C s (by omega) _ _ _ (topPrepSettledPhase ring hn C s hl hbad)

/-- P.11 for the classes without an earlier strict stop.

Consumer: `TopClockPhaseBundle.mobile` (TopClockAssembly). -/
theorem topStopMobilePhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockFinalMobilePhase ring C s (topClockStopClasses ring C s) :=
  phase_nps_transfer ring C s (by omega) _ _ _ (topPrepMobilePhase ring hn C s hl hbad)

/-- P.13 unfavourable branch for the classes without an earlier strict stop.

Consumer: `TopClockPhaseBundle.unfavourable` (TopClockAssembly). -/
theorem topStopUnfavourablePhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockUnfavourablePhase ring C s (topClockStopClasses ring C s) :=
  phase_nps_transfer ring C s (by omega) _ _ _ (topPrepUnfavourablePhase ring hn C s hl hbad)

/-- P.12 race for the classes without an earlier strict stop.

Consumer: `TopClockPhaseBundle.race` (TopClockAssembly). -/
theorem topStopRacePhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockRacePhase ring C s (topClockStopClasses ring C s) := by
  intro Z hZ
  refine phase_nps_hit ring C s (by omega) _ _ (fun Y hY => Or.inl hY) ?_ Z
    (stopOr_nps_source ring C s _ Z hZ) n
    (topPrepRacePhase ring hn C s hl hbad Z
      (by rcases hZ with hZ | hZ; exact Or.inl hZ; exact Or.inr hZ.1))
  intro Y hY hT
  rcases hT with hT | hT | hT
  · exact Or.inl hT
  · exact Or.inr (Or.inl ⟨hT, hY⟩)
  · exact Or.inr (Or.inr ⟨hT, hY⟩)

/-- A favourable cut of the classes without an earlier strict stop is a favourable cut of the
classes with the settled bookkeeping.

Consumer: `topStopFavClear`. -/
theorem stopFavourable_forget {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n)
    (h : (topClockStopClasses ring C s).favourable Z) :
    (topClockPrepClasses ring C s).favourable Z := h.1

/-- A misplaced cut of the classes without an earlier strict stop is a misplaced cut of the
classes with the settled bookkeeping.

Consumer: `Leader/L3/Top/PinnedPhaseSweep.lean`. -/
theorem stopMisplaced_forget {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n)
    (h : (topClockStopClasses ring C s).misplacedTail Z) :
    (topClockPrepClasses ring C s).misplacedTail Z := h.1

/-- **P.12 favourable, clearing stage for the classes without an earlier strict stop**: from a
favourable cut a strict stop or the pending-only class is reached within mean `n * r`.

Consumer: `topStopFavourablePhase` (first stage). -/
theorem topStopFavClear {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) (Z : TopFixedTraceState n)
    (hZ : (topClockStopClasses ring C s).favourable Z) :
    UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C)
      (topClockStopOr ring C s (topClockStopClasses ring C s).pendingOnly) Z
      ((n * topClockSpan n : Nat) : Rat) := by
  refine phase_nps_hit ring C s (by omega) _ _ (fun Y hY => Or.inl hY) ?_ Z
    (Or.inl hZ.2) _ (topPrepFavClear ring hn C s hl hbad Z hZ.1)
  intro Y hY hT
  exact Or.inr ⟨hT, hY⟩

/-- The fresh-tail phase transfers to the classes without an earlier strict stop: the initial
state has no earlier stop.

Consumer: `TopClockPhaseBundle.fresh` (TopClockAssembly). -/
theorem topStopFreshPhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (h : TopClockFreshTailPhase ring C s (topClockPrepClasses ring C s)) :
    TopClockFreshTailPhase ring C s (topClockStopClasses ring C s) := by
  refine phase_nps_hit ring C s (by omega) _ _ (fun Y hY => Or.inl hY) ?_ _
    (Or.inl (noPrefixStop_initial ring C s)) _ h
  intro Y hY hT
  rcases hT with hT | hT
  · exact Or.inl hT
  · exact Or.inr ⟨hT, hY⟩

end MarkedCells
end L3

#print axioms L3.MarkedCells.phase_nps_hit
#print axioms L3.MarkedCells.topStopMarkedPhase
#print axioms L3.MarkedCells.topStopSettledPhase
#print axioms L3.MarkedCells.topStopMobilePhase
#print axioms L3.MarkedCells.topStopUnfavourablePhase
#print axioms L3.MarkedCells.topStopRacePhase
#print axioms L3.MarkedCells.topStopFavClear
#print axioms L3.MarkedCells.topStopFreshPhase
