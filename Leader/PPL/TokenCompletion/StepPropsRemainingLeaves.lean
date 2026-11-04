import Leader.PPL.TokenCompletion.StepPropsSixLeaves
import Leader.PPL.TokenCompletion.RightmostResponderSelectedPair
import Leader.PPL.TokenCompletion.SweepEmptyBirth

namespace PPL

set_option autoImplicit false

/-!
Lemma 4 leaves closed so far: the rightmost-responder literal cases
(via the selected-pair cases) and the sweep empty-birth literal cases.
The one-step wiring then needs only the initiator branch, the sweep
initiator and responder literal cases, and touched-coverage soundness.
-/

theorem lemma4RightmostResponderLiteralCases_closed :
    Lemma4RightmostResponderLiteralCases :=
  lemma4RightmostResponderLiteralCases_of_selectedPairCases
    lemma4RightmostResponderSelectedPairCases_proved

theorem lemma4RightmostResponderBranch_closed :
    Lemma4RightmostResponderBranch :=
  lemma4RightmostResponderBranch_of_literalCases
    lemma4CoverageGhostRunSound_proved
    lemma4RightmostResponderLiteralCases_closed

theorem lemma4StepProps_of_remainingLeaves
    (hInitiator : Lemma4RightmostInitiatorBranch)
    (h3 : Lemma4SweepInitiatorLiteralCases)
    (h4 : Lemma4SweepResponderLiteralCases)
    (h6 : Lemma4CoverageTouchedCoverageSound) :
    Lemma4CoverageStep ∧
      Lemma4RightmostProgressStep ∧
      Lemma4SweepMissingRows :=
  lemma4StepProps_of_literalLeaves
    hInitiator
    lemma4RightmostResponderLiteralCases_closed
    h3 h4
    lemma4SweepEmptyBirthLiteralCases_proved
    h6

end PPL

#print axioms PPL.lemma4RightmostResponderLiteralCases_closed
#print axioms PPL.lemma4RightmostResponderBranch_closed
#print axioms PPL.lemma4StepProps_of_remainingLeaves
