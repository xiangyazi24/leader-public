import Leader.PPL.TokenCompletion.StepPropsOneLeaf
import Leader.PPL.TokenCompletion.RightmostInitiatorStateLocal
import Leader.PPL.TokenCompletion.FreshTerminalRun
import Leader.PPL.TokenCompletion.RightmostInitiatorSurvivalRows
import Leader.PPL.TokenCompletion.RightmostInitiatorTerminalRows

/-!
Lemma 4 one-interaction step properties, unconditionally.

The rightmost-initiator branch reduces to the aged no-prior-completion row,
which reduces to the terminal and survival state-local residuals; both are
now proved.  Together with the closed sweep-initiator literal cases this
yields the coverage step, the rightmost progress step and the missing sweep
rows with no remaining hypothesis.  The multi-interaction half-power sweep
that turns these into `lemma4_deterministic_core` is not part of this file.
-/

namespace PPL

/-- The rightmost-initiator branch, unconditionally. -/
theorem lemma4RightmostInitiatorBranch_proved :
    Lemma4RightmostInitiatorBranch :=
  lemma4RightmostInitiatorBranch_of_noPriorRow
    (lemma4RightmostInitiatorAgedNoPriorCompletionRow_of_stateLocalResiduals
      lemma4RightmostInitiatorTerminalStateLocalResidual_proved
      lemma4RightmostInitiatorSurvivalStateLocalResidual_proved)

/-- Lemma 4 one-interaction step properties, unconditionally. -/
theorem lemma4StepProps_proved :
    Lemma4CoverageStep ∧
      Lemma4RightmostProgressStep ∧
      Lemma4SweepMissingRows :=
  lemma4StepProps_of_initiatorBranch
    lemma4RightmostInitiatorBranch_proved

end PPL

#print axioms PPL.lemma4RightmostInitiatorBranch_proved
#print axioms PPL.lemma4StepProps_proved
