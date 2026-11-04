import Leader.PPL.TokenCompletion.CoverageLeaves
import Leader.PPL.TokenCompletion.CoverageOrigin
import Leader.PPL.TokenCompletion.OffPairLiteral
import Leader.PPL.TokenCompletion.RightmostInitiator
import Leader.PPL.TokenCompletion.RightmostResponder
import Leader.PPL.TokenCompletion.SweepRows

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
Exact one-step wiring from the six requested literal leaves.

Current main supplies all adapters needed to reach the three step interfaces:

* h6 plus the two proved origin rows -> Lemma4CoverageStep;
* the initiator branch (h1 was refuted, ERRATA S3.9; the aged route
  TokenCorrectnessLemma4RightmostInitiatorAged.lean produces the branch),
  h2 plus GhostSound and the proved off-pair literal row
  -> Lemma4RightmostProgressStep;
* h3/h4/h5 plus GhostSound -> Lemma4SweepMissingRows.

This theorem deliberately stops there.  TokenCorrectnessLemma4Sweep.lean
contains lemma4HalfPowerDynamicsCovered_of_steps only inside a comment:
the pure multi-interaction sweep geometry has not been proved on main.
-/
theorem lemma4StepProps_of_literalLeaves
    (hInitiator : Lemma4RightmostInitiatorBranch)
    (h2 : Lemma4RightmostResponderLiteralCases)
    (h3 : Lemma4SweepInitiatorLiteralCases)
    (h4 : Lemma4SweepResponderLiteralCases)
    (h5 : Lemma4SweepEmptyBirthLiteralCases)
    (h6 : Lemma4CoverageTouchedCoverageSound) :
    Lemma4CoverageStep ∧
      Lemma4RightmostProgressStep ∧
      Lemma4SweepMissingRows := by
  have hsound : Lemma4CoverageGhostRunSound :=
    lemma4CoverageGhostRunSound_proved

  have hcov : Lemma4CoverageStep :=
    lemma4CoverageStep_of_remaining
      h6
      lemma4CoverageOriginInitiatorRow_proved
      lemma4CoverageOriginResponderRow_proved

  have hResponder : Lemma4RightmostResponderBranch :=
    lemma4RightmostResponderBranch_of_literalCases
      hsound h2

  have hEndpoint :
      Lemma4RightmostOffPairEndpointNoOvertake :=
    lemma4RightmostOffPairEndpointNoOvertake_of_literalCases
      hsound
      lemma4RightmostOffPairLiteralCases_proved

  have hright : Lemma4RightmostProgressStep :=
    lemma4RightmostProgressStep_closed
      hInitiator hResponder hEndpoint

  have hrows : Lemma4SweepMissingRows :=
    lemma4SweepMissingRows_of_literal
      hsound h3 h4 h5

  exact ⟨hcov, hright, hrows⟩

end PPL

#print axioms PPL.lemma4StepProps_of_literalLeaves
