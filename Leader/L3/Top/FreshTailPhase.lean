import Leader.L3.Top.FreshTailCohortWave
import Leader.L3.Top.FreshTailJointAnchor
import Leader.L3.Top.PinnedPhaseClasses

/-!
Q7c P.3: conditional selected-cohort final mile.

The source-state preservation and the entrance at the first genuine
acceptance are hypotheses, not proved by this module. In particular,
this module does not assert an unconditional one-edge census or a
first-genuine-to-issued-barrier extraction.

The cost comparison is conditioned on the actual first-hit history.
There is no unrestricted implication from an arbitrary genuine-tail
state to the stronger permanent first-tail cut.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- A selected post-anchor cohort survives every finite continuation
when the total real-edge preservation hypothesis is supplied.
The replay equality is the actual fixed-public audit word equation.
Consumer: topFreshTailPostAnchorCohortPureFuture. -/
theorem topFreshTailPostAnchorCohortWaveRun
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hstep :
      ∀ (Y : TopFixedTraceState n)
        (a : DigitExport (compileAdvice (ceilLogTwo n)) n),
        TopFreshTailPostAnchorCohortWave ring C s hn Y a →
        ∀ e : Fin n,
          Nonempty (TopFreshTailPostAnchorCohortWave ring C s hn
            (topFixedTraceNext ring C Y e) a))
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (word : List (Fin n)) :
    Nonempty (TopFreshTailPostAnchorCohortWave ring C s hn
      (topFixedTraceRun ring C (Z.2 ++ word)) anchor) := by
  have hfold :
      ∀ (v : List (Fin n)) (Y : TopFixedTraceState n),
        TopFreshTailPostAnchorCohortWave ring C s hn Y anchor →
        Nonempty (TopFreshTailPostAnchorCohortWave ring C s hn
          (v.foldl (topFixedTraceNext ring C) Y) anchor) := by
    intro v
    induction v with
    | nil =>
        intro Y hY
        exact ⟨hY⟩
    | cons e rest ih =>
        intro Y hY
        obtain ⟨Wnext⟩ := hstep Y anchor hY e
        exact ih (topFixedTraceNext ring C Y e) Wnext
  rw [topFixedTraceRunAppendWord ring C Z.2 word]
  rw [← W.reached]
  exact hfold word Z W

/-- Every future chronological comparison export is an authentic
sampled serial of the fixed anchored stream. The selected-cohort
exportRecords field additionally proves the public digit value;
only the seven clauses of concrete purity are projected here.
Consumer: topFreshTailBackwardsPurityOfCohortWave. -/
theorem topFreshTailPostAnchorCohortPureFuture
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hstep :
      ∀ (Y : TopFixedTraceState n)
        (a : DigitExport (compileAdvice (ceilLogTwo n)) n),
        TopFreshTailPostAnchorCohortWave ring C s hn Y a →
        ∀ e : Fin n,
          Nonempty (TopFreshTailPostAnchorCohortWave ring C s hn
            (topFixedTraceNext ring C Y e) a))
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor) :
    ∀ word : List (Fin n),
      topClockConcretePureStream s
        (topFixedTraceRun ring C (Z.2 ++ word)) anchor := by
  intro word
  obtain ⟨Wend⟩ :=
    topFreshTailPostAnchorCohortWaveRun ring C s hn hbad hl
      hstep Z anchor W word
  unfold topClockConcretePureStream
  intro i
  obtain ⟨sample, hrecord, hlane, hsite, _, htail,
    hoperand, hvalue, hexportTail⟩ := Wend.exportRecords i
  exact ⟨sample, hrecord, hlane, hsite, htail,
    hoperand, hvalue, hexportTail⟩

/-- A first genuine receipt has an anchor whose entire future
comparison-export stream is pure, provided the real selected-wave
entrance and real one-edge preservation producers are supplied.
The pre-anchor predicate already includes reachedness and absence
of genuine tails at every strict prefix.
Consumer: topFreshTailPermanentCutOfBackwardsPurity and
topStopFreshPhaseOfCohortWave. -/
theorem topFreshTailBackwardsPurityOfCohortWave
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hstep :
      ∀ (Y : TopFixedTraceState n)
        (a : DigitExport (compileAdvice (ceilLogTwo n)) n),
        TopFreshTailPostAnchorCohortWave ring C s hn Y a →
        ∀ e : Fin n,
          Nonempty (TopFreshTailPostAnchorCohortWave ring C s hn
            (topFixedTraceNext ring C Y e) a))
    (hbase :
      ∀ (Z : TopFixedTraceState n),
        TopFreshTailJointPreAnchor ring C s Z →
        topClockGenuineTailAccepted C s Z →
        ∃ anchor : DigitExport (compileAdvice (ceilLogTwo n)) n,
          topClockConcreteTailAnchor s Z anchor ∧
          anchor.time = Z.1.2.clock ∧
          Nonempty (TopFreshTailPostAnchorCohortWave ring C s hn
            Z anchor)) :
    TopFreshTailBackwardsPurity ring C s := by
  intro Z hreached hfirst haccepted
  obtain ⟨anchor, hanchor, htime, ⟨W⟩⟩ :=
    hbase Z ⟨hreached, hfirst⟩ haccepted
  refine ⟨anchor, hanchor, htime, ?_⟩
  exact topFreshTailPostAnchorCohortPureFuture ring C s hn hbad hl
    hstep Z anchor W

/-- On the actual histories preceding the first anchor hit, the
stop-or-permanent-firstTail first-hit cost is no greater than the
stop-or-genuine-anchor first-hit cost, with zero additional time.
The closed class combines the joint no-earlier-genuine-tail prefix
condition with no earlier strict stop (or strict stop now).
Consumer: topStopFreshPhaseOfCohortWave. -/
theorem topFreshTailCohortFirstHitCostDomination
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hpurity : TopFreshTailBackwardsPurity ring C s) :
    ∀ T : Nat,
      costNumerator (topFixedTraceNext ring C)
        (topClockStopOr ring C s
          (MarkedCells.topClockStopClasses ring C s).firstTail)
        ((C, digitAuditInitial (piD C)), []) T ≤
      costNumerator (topFixedTraceNext ring C)
        (topFreshTailJointAnchorHit ring C s)
        ((C, digitAuditInitial (piD C)), []) T := by
  have hentry :
      ∀ Y : TopFixedTraceState n,
        (TopFreshTailJointPreAnchor ring C s Y ∧
          (MarkedCells.NoPrefixStop ring C s Y ∨
           topFixedStrictStop ring C s Y)) →
        topFreshTailJointAnchorHit ring C s Y →
        topClockStopOr ring C s
          (MarkedCells.topClockStopClasses ring C s).firstTail Y := by
    intro Y hY hhit
    rcases hhit with hstrict | htail
    · exact Or.inl hstrict
    · rcases hY.2 with hnostop | hstrict
      · refine Or.inr ?_
        change topFreshTailPermanentCut ring C s Y ∧
          MarkedCells.NoPrefixStop ring C s Y
        exact ⟨topFreshTailPermanentCutOfBackwardsPurity
          ring C s hpurity Y hY.1.1 hY.1.2 htail, hnostop⟩
      · exact Or.inl hstrict
  have hclosed :
      ∀ Y : TopFixedTraceState n,
        (TopFreshTailJointPreAnchor ring C s Y ∧
          (MarkedCells.NoPrefixStop ring C s Y ∨
           topFixedStrictStop ring C s Y)) →
        ¬ topClockStopOr ring C s
          (MarkedCells.topClockStopClasses ring C s).firstTail Y →
        ∀ e : Fin n,
          TopFreshTailJointPreAnchor ring C s
            (topFixedTraceNext ring C Y e) ∧
          (MarkedCells.NoPrefixStop ring C s
            (topFixedTraceNext ring C Y e) ∨
           topFixedStrictStop ring C s
            (topFixedTraceNext ring C Y e)) := by
    intro Y hY hnotTarget e
    have hnotAnchor : ¬ topFreshTailJointAnchorHit ring C s Y := by
      intro ha
      exact hnotTarget (hentry Y hY ha)
    refine ⟨topFreshTailJointPreAnchorNext ring C s Y
      hY.1 hnotAnchor e, ?_⟩
    rcases hY.2 with hnostop | hstrict
    · by_cases hstrictNext :
        topFixedStrictStop ring C s (topFixedTraceNext ring C Y e)
      · exact Or.inr hstrictNext
      · exact Or.inl (MarkedCells.noPrefixStop_next
          ring C s Y e hnostop hstrictNext)
    · exact False.elim (hnotAnchor (Or.inl hstrict))
  have hinitial :
      TopFreshTailJointPreAnchor ring C s
        ((C, digitAuditInitial (piD C)), []) ∧
      (MarkedCells.NoPrefixStop ring C s
          ((C, digitAuditInitial (piD C)), []) ∨
       topFixedStrictStop ring C s
          ((C, digitAuditInitial (piD C)), [])) := by
    constructor
    · refine ⟨by unfold topClockReached; rfl, ?_⟩
      intro pre suffix hword hne
      exact absurd (List.append_eq_nil_iff.mp hword).2 hne
    · exact Or.inl (MarkedCells.noPrefixStop_initial ring C s)
  intro T
  exact topFinalCostTargetOnClosed (topFixedTraceNext ring C)
    (fun Y =>
      TopFreshTailJointPreAnchor ring C s Y ∧
      (MarkedCells.NoPrefixStop ring C s Y ∨
       topFixedStrictStop ring C s Y))
    (topClockStopOr ring C s
      (MarkedCells.topClockStopClasses ring C s).firstTail)
    (topFreshTailJointAnchorHit ring C s)
    hclosed hentry T ((C, digitAuditInitial (piD C)), []) hinitial

/-- The exact P.3 budget at the NoPrefixStop cut classes follows
without a second waiting stage: first-genuine cost is charged by
the joint anchor clock, while selected-cohort permanence merely
strengthens the first-hit target on its closed history class.
Consumer: TopClockPhaseBundle.fresh and topFixedClock_of_phases. -/
theorem topStopFreshPhaseOfCohortWave
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hstep :
      ∀ (Y : TopFixedTraceState n)
        (a : DigitExport (compileAdvice (ceilLogTwo n)) n),
        TopFreshTailPostAnchorCohortWave ring C s hn Y a →
        ∀ e : Fin n,
          Nonempty (TopFreshTailPostAnchorCohortWave ring C s hn
            (topFixedTraceNext ring C Y e) a))
    (hbase :
      ∀ (Z : TopFixedTraceState n),
        TopFreshTailJointPreAnchor ring C s Z →
        topClockGenuineTailAccepted C s Z →
        ∃ anchor : DigitExport (compileAdvice (ceilLogTwo n)) n,
          topClockConcreteTailAnchor s Z anchor ∧
          anchor.time = Z.1.2.clock ∧
          Nonempty (TopFreshTailPostAnchorCohortWave ring C s hn
            Z anchor)) :
    TopClockFreshTailPhase ring C s
      (MarkedCells.topClockStopClasses ring C s) := by
  have hpurity : TopFreshTailBackwardsPurity ring C s :=
    topFreshTailBackwardsPurityOfCohortWave
      ring C s hn hbad hl hstep hbase
  have hdomination :
      ∀ T : Nat,
        costNumerator (topFixedTraceNext ring C)
          (topClockStopOr ring C s
            (MarkedCells.topClockStopClasses ring C s).firstTail)
          ((C, digitAuditInitial (piD C)), []) T ≤
        costNumerator (topFixedTraceNext ring C)
          (topFreshTailJointAnchorHit ring C s)
          ((C, digitAuditInitial (piD C)), []) T :=
    topFreshTailCohortFirstHitCostDomination
      ring C s hn hbad hl hpurity
  have hanchor :=
    topFreshTailJointAnchorClock ring C s hn hbad hl
  have hnpos : 0 < n := by omega
  unfold TopClockFreshTailPhase
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C)
    (topClockStopOr ring C s
      (MarkedCells.topClockStopClasses ring C s).firstTail)
    hnpos ((C, digitAuditInitial (piD C)), [])
    (n * topClockF (topClockSpan n))).2
  intro T
  have hanchorCost :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (topFixedTraceNext ring C)
      (topFreshTailJointAnchorHit ring C s)
      hnpos ((C, digitAuditInitial (piD C)), [])
      (n * topClockF (topClockSpan n))).1 hanchor T
  exact Nat.le_trans (hdomination T) hanchorCost

/-- P.3 at the stop classes with the one-edge preservation discharged by
`topFreshTailCohortWaveStepOfRows`; only the first-genuine entrance
`hbase` remains. Consumer: the Q7 phase bundle (`TopClockPhaseBundle.fresh`)
once the entrance is proved. -/
theorem topStopFreshPhaseOfEntrance
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hbase :
      ∀ (Z : TopFixedTraceState n),
        TopFreshTailJointPreAnchor ring C s Z →
        topClockGenuineTailAccepted C s Z →
        ∃ anchor : DigitExport (compileAdvice (ceilLogTwo n)) n,
          topClockConcreteTailAnchor s Z anchor ∧
          anchor.time = Z.1.2.clock ∧
          Nonempty (TopFreshTailPostAnchorCohortWave ring C s hn
            Z anchor)) :
    TopClockFreshTailPhase ring C s
      (MarkedCells.topClockStopClasses ring C s) :=
  topStopFreshPhaseOfCohortWave ring C s hn hbad hl
    (fun Y a W e => topFreshTailCohortWaveStepOfRows ring C s hn hbad hl Y a W e)
    hbase

end L3

#print axioms L3.topFreshTailPostAnchorCohortWaveRun
#print axioms L3.topFreshTailPostAnchorCohortPureFuture
#print axioms L3.topFreshTailBackwardsPurityOfCohortWave
#print axioms L3.topFreshTailCohortFirstHitCostDomination
#print axioms L3.topStopFreshPhaseOfCohortWave
#print axioms L3.topStopFreshPhaseOfEntrance
