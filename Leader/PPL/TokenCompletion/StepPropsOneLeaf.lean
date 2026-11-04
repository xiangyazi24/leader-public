import Leader.PPL.TokenCompletion.StepPropsTwoLeaves
import Leader.PPL.TokenCompletion.SweepInitiatorRows
import Leader.PPL.TokenCompletion.SweepInitiatorArrival
import Leader.PPL.TokenCompletion.SweepInitiator

namespace PPL

set_option autoImplicit false

/-!
# Lemma 4 step properties from the rightmost-initiator branch

The sweep initiator literal cases follow from the same-id branch, which is
assembled from the proved arrival, right-move and turn-core rows.  With
touched coverage and the sweep responder cases already closed, the Lemma 4
one-step wiring rests on the rightmost-initiator branch alone.
-/

/-- The sweep initiator literal cases, unconditionally. -/
theorem lemma4SweepInitiatorLiteralCases_closed :
    Lemma4SweepInitiatorLiteralCases :=
  lemma4SweepInitiatorLiteralCases_of_sameIdBranch
    (lemma4SweepInitiatorSameIdBranch_of_arrivalRow
      lemma4SweepInitiatorArrivalRow_proved)

/-- The Lemma 4 one-step properties (coverage step, rightmost progress,
missing sweep rows) from the rightmost-initiator branch alone. -/
theorem lemma4StepProps_of_initiatorBranch
    (hInitiator : Lemma4RightmostInitiatorBranch) :
    Lemma4CoverageStep ∧
      Lemma4RightmostProgressStep ∧
      Lemma4SweepMissingRows :=
  lemma4StepProps_of_twoLeaves
    hInitiator
    lemma4SweepInitiatorLiteralCases_closed

end PPL

#print axioms PPL.lemma4SweepInitiatorLiteralCases_closed
#print axioms PPL.lemma4StepProps_of_initiatorBranch
