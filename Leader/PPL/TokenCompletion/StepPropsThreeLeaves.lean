import Leader.PPL.TokenCompletion.StepPropsRemainingLeaves
import Leader.PPL.TokenCompletion.CoverageTouched

namespace PPL

set_option autoImplicit false

/-!
# Lemma 4 step properties after touched coverage

Touched-coverage soundness is now proved unconditionally
(`lemma4CoverageTouchedCoverageSound_proved`).  The one-step wiring of
Lemma 4 therefore rests on three open leaves: the rightmost-initiator
branch and the sweep initiator and responder literal cases.
-/

/-- The Lemma 4 one-step properties (coverage step, rightmost progress,
missing sweep rows) from the three remaining literal leaves; the
touched-coverage leaf is discharged by its proof. -/
theorem lemma4StepProps_of_threeLeaves
    (hInitiator : Lemma4RightmostInitiatorBranch)
    (h3 : Lemma4SweepInitiatorLiteralCases)
    (h4 : Lemma4SweepResponderLiteralCases) :
    Lemma4CoverageStep ∧
      Lemma4RightmostProgressStep ∧
      Lemma4SweepMissingRows :=
  lemma4StepProps_of_remainingLeaves
    hInitiator h3 h4
    lemma4CoverageTouchedCoverageSound_proved

end PPL

#print axioms PPL.lemma4StepProps_of_threeLeaves
