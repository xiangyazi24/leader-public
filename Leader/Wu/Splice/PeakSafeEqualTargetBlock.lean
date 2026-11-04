import Leader.Wu.ShortGap.SegmentPeakMerge
import Leader.Wu.Safety.Counterexamples
import Leader.Wu.Comparison.StableRulerGarbageSurvives

set_option autoImplicit false

namespace Q11588PeakSafeCensus

open PPLL

/-- This is the exact combinatorial content of the spec's survival sentence:
if all groups crossed by a carrier have ID at most the source ID, a PeakSafe
word cannot contain a later equal target. -/
theorem repeatPeakSafe_blocks_equal_after_bounded_crossing
    {word : List Nat}
    (hpeak : SegmentPeakWord.RepeatPeakSafe word)
    {i j : Nat}
    (hi : i < word.length) (hj : j < word.length)
    (hij : i < j)
    (heq : word.get ⟨i, hi⟩ = word.get ⟨j, hj⟩)
    (hsurvive : forall k (hk : k < word.length),
      i < k -> k < j ->
        word.get ⟨k, hk⟩ <= word.get ⟨i, hi⟩) : False := by
  obtain ⟨k, hk, hik, hkj, hhigh⟩ :=
    hpeak i j hi hj hij heq
  exact (Nat.not_lt_of_ge (hsurvive k hk hik hkj)) hhigh

/-- A one-group leader-delimited word is PeakSafe vacuously. -/
theorem singleton_repeatPeakSafe (x : Nat) :
    SegmentPeakWord.RepeatPeakSafe [x] := by
  intro i j hi hj hij _
  simp only [List.length_cons, List.length_nil] at hi hj
  omega

/-- Bare physical PeakSafe/stable-ruler geometry does not authenticate a
comparison carrier.  The old exact Algorithm-11 counterexample has a stable
ruler and a singleton positive segment, yet CHECK creates the responder. -/
theorem stable_peakSafe_shape_can_still_CHECK_birth :
    isStableIDSequence (by omega : 2 > 0)
        PPLLCounterexample.ring4 PPLLCounterexample.counterConfig ∧
      SegmentPeakWord.RepeatPeakSafe
        [groupID PPLLCounterexample.ring4.hn
          PPLLCounterexample.counterConfig (2 : Fin 4)] ∧
      (PPLLCounterexample.badAfterCheckSig).2.leader = true := by
  refine ⟨
    PPLLCounterexample.counterConfig_paper_safe.stable_id_sequence,
    singleton_repeatPeakSafe _, ?_⟩
  have h := congrArg
    (fun q : AgentState 2 × AgentState 2 => q.2.leader)
    PPLLCounterexample.bad_trace_check_creates_responder
  simpa using h

/-- The literal current terminal consumer does not globally erase a malformed
comparison component merely because an unrelated row executes. -/
theorem current_consumer_does_not_globally_sanitize_source_incoherence :
    Q11475Counterexample.afterOne (2 : Fin 8) =
      Q11475Counterexample.badInitial (2 : Fin 8) :=
  Q11475Counterexample.forged_component_survives_current_step

#print axioms Q11588PeakSafeCensus.repeatPeakSafe_blocks_equal_after_bounded_crossing
#print axioms Q11588PeakSafeCensus.singleton_repeatPeakSafe
#print axioms Q11588PeakSafeCensus.stable_peakSafe_shape_can_still_CHECK_birth
#print axioms Q11588PeakSafeCensus.current_consumer_does_not_globally_sanitize_source_incoherence

end Q11588PeakSafeCensus
