import Leader.PPL.TokenCompletion.StepPropsThreeLeaves
import Leader.PPL.TokenCompletion.SweepResponderSameId

namespace PPL

set_option autoImplicit false

/-!
# Lemma 4 step properties from two leaves

Touched-coverage soundness and the sweep responder literal cases are proved
unconditionally (`lemma4CoverageTouchedCoverageSound_proved`,
`lemma4SweepResponderLiteralCases_closed`).  The Lemma 4 one-step wiring
now rests on the rightmost-initiator branch and the sweep initiator literal
cases.
-/

/-- The Lemma 4 one-step properties (coverage step, rightmost progress,
missing sweep rows) from the rightmost-initiator branch and the sweep
initiator literal cases. -/
theorem lemma4StepProps_of_twoLeaves
    (hInitiator : Lemma4RightmostInitiatorBranch)
    (h3 : Lemma4SweepInitiatorLiteralCases) :
    Lemma4CoverageStep ∧
      Lemma4RightmostProgressStep ∧
      Lemma4SweepMissingRows :=
  lemma4StepProps_of_threeLeaves
    hInitiator h3
    lemma4SweepResponderLiteralCases_closed

end PPL

#print axioms PPL.lemma4StepProps_of_twoLeaves
