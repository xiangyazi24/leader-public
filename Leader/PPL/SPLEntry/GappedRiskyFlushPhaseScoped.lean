import Leader.PPL.SPLEntry.GappedRiskyScopedRoute
import Leader.PPL.SPLEntry.GappedRiskyInsertedResponderCases
import Leader.PPL.SPLEntry.GappedRiskyInsertedResponderBlackFacts
import Leader.PPL.SPLEntry.GappedRiskyInsertedResponderWhiteFacts

/-!
# The gapped risky flush phase, closed

The four responder colour cases (wrap/non-wrap, black/white) are proved in
`L18GappedRiskyInsertedResponderBlackFacts` and
`L18GappedRiskyInsertedResponderWhiteFacts`. They give the inserted-step row
(`l18GappedRiskyInsertedStepRow_of_responderCases`), and the inserted-step row
together with the proved letter-2 sweep row gives the scoped flush phase
(`l18GappedRiskyFlushPhaseScoped_of_insertedStepRow`).
-/

namespace PPL.Convergence.L18

set_option autoImplicit false

/-- Every step inserted into the risky flush word preserves the flush invariant. -/
theorem l18GappedRiskyInsertedStepRow_proved :
    L18GappedRiskyInsertedStepRow :=
  l18GappedRiskyInsertedStepRow_of_responderCases
    l18GappedRiskyInsertedResponderWrapBlackCase_proved
    l18GappedRiskyInsertedResponderWrapWhiteCase_proved
    l18GappedRiskyInsertedResponderNonwrapBlackCase_proved
    l18GappedRiskyInsertedResponderNonwrapWhiteCase_proved

/-- Gapped risky flush phase: a schedule containing the risky flush word as a
subsequence either hits SPL or ends in a CDL configuration with no risky token. -/
theorem l18GappedRiskyFlushPhaseScoped_proved :
    L18GappedRiskyFlushPhaseScoped :=
  l18GappedRiskyFlushPhaseScoped_of_insertedStepRow
    l18GappedRiskyInsertedStepRow_proved

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.l18GappedRiskyInsertedStepRow_proved
#print axioms PPL.Convergence.L18.l18GappedRiskyFlushPhaseScoped_proved
