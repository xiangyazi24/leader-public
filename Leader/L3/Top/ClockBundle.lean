import Leader.L3.Top.FreshTailPhase
import Leader.L3.Top.PinnedRenewal
import Leader.L3.Top.PortPhase
import Leader.L3.RequestStage

/-!
# Q7 phase bundle at the stop classes, and the Q9 request clock

Every field of `TopClockPhaseBundle` (TopClockAssembly) at the class value
`MarkedCells.topClockStopClasses` is proved except the fresh-tail phase P.3,
which `topStopFreshPhaseOfEntrance` (TopFreshTailPhase) reduces to the
first-genuine entrance of the cohort wave.  This module names that entrance
once, as `TopFreshTailFirstGenuineEntrance`, and carries it through
`topFixedClock_of_phases` and `stageRequestMissingClock_of_fixedTop` to the
headline premise `StageRequestMissingClock` (old Q9).
-/

namespace L3

open Classical

/-- The first-genuine entrance of the post-anchor cohort wave (paper proof
through the inversions S and T): at every reached state whose
strict prefixes carry no genuine tail and which has just accepted a genuine
tail, the time-now concrete anchor exists and the cohort wave holds there.
Consumer: `topClockPhaseBundleOfEntrance`. -/
def TopFreshTailFirstGenuineEntrance {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) : Prop :=
  ∀ (C : HeadlineConfiguration n) (s : Fin n),
    (∀ i : Fin n, (C i).l = false) →
    HeadlineDigit.BadCompletePair C s →
    ∀ (Z : TopFixedTraceState n),
      TopFreshTailJointPreAnchor ring C s Z →
      topClockGenuineTailAccepted C s Z →
      ∃ anchor : DigitExport (compileAdvice (ceilLogTwo n)) n,
        topClockConcreteTailAnchor s Z anchor ∧
        anchor.time = Z.1.2.clock ∧
        Nonempty (TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)

/-- The full Q7 phase bundle at `topClockStopClasses`: port
(`topClockConcretePortPhase`), fresh tail (`topStopFreshPhaseOfEntrance`), the
seven phases of `topStopPhases`, and the renewal (`topStopRenewalPhase`).
Consumer: `topClockAllPhasePropsOfEntrance`. -/
theorem topClockPhaseBundleOfEntrance {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) (hentry : TopFreshTailFirstGenuineEntrance ring hn)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    Nonempty (TopClockPhaseBundle ring C s) := by
  obtain ⟨hmarked, hsettled, hmobile, hprep, hrace, hfav, hunf⟩ :=
    MarkedCells.topStopPhases ring hn C s hl hbad
  exact ⟨{
    cuts := MarkedCells.topClockStopClasses ring C s
    port := topClockConcretePortPhase ring C s hbad
    fresh := topStopFreshPhaseOfEntrance ring C s hn hbad hl
      (hentry C s hl hbad)
    marked := hmarked
    settled := hsettled
    mobile := hmobile
    prepare := hprep
    race := hrace
    favourable := hfav
    unfavourable := hunf
    renew := MarkedCells.topStopRenewalPhase ring hn C s hl hbad }⟩

/-- All Q7 phase contracts, from the entrance.
Consumer: `stageRequestMissingClockOfEntrance`. -/
theorem topClockAllPhasePropsOfEntrance {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) (hentry : TopFreshTailFirstGenuineEntrance ring hn) :
    TopClockAllPhaseProps ring :=
  ⟨hn, fun C s _ hl _ hbad =>
    topClockPhaseBundleOfEntrance ring hn hentry C s hl hbad⟩

/-- The headline premise `hrequest` (old Q9) from the cohort-wave entrance:
`topFixedClock_of_phases`, then `stageRequestMissingClock_of_fixedTop`.
Consumer: `l3HeadlineOfCleanBranches` (HeadlineCleanAssembly). -/
theorem stageRequestMissingClockOfEntrance {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) (hentry : TopFreshTailFirstGenuineEntrance ring hn) :
    StageRequestMissingClock ring :=
  stageRequestMissingClock_of_fixedTop ring
    (topFixedClock_of_phases ring
      (topClockAllPhasePropsOfEntrance ring hn hentry))

end L3

#print axioms L3.topClockPhaseBundleOfEntrance
#print axioms L3.topClockAllPhasePropsOfEntrance
#print axioms L3.stageRequestMissingClockOfEntrance
