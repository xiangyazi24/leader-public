import Leader.PPL.Elim.AttemptLongIncident
import Leader.PPL.Elim.AttemptLongRaceRefine
import Leader.PPL.Elim.AttemptLongRetainedRoot
import Leader.PPL.Elim.AttemptLongFirstCut

/-!
L17 long-attempt retry mass, closed.

Conjunct 4 uses the retained-control bridge (`longFullFactor_closed`)
instead of the refuted quarter-Bellman leaf
(`longFirstIncidentQuarterBellmanV2_false`).
-/

namespace PPL.Convergence.LDLocal

set_option autoImplicit false

theorem longAttemptFirstCutStageFactorSpec_closed :
    LongAttemptFirstCutStageFactorSpec := by
  unfold LongAttemptFirstCutStageFactorSpec
  intro hSealed n ring C0 F hb hab
  refine
    And.intro
      (longAttemptFirstCutStageFactorSpec_entry_closed
        ring F hb hab)
      ?_
  refine
    And.intro
      (longRaceFactor_proved
        longFirstProgressRaceCounterRefinement_proved
        hSealed ring F hb hab)
      ?_
  refine
    And.intro
      (longIncidentFactor_proved
        hSealed ring F hb hab)
      (longFullFactor_closed
        hSealed ring F hb hab)

theorem longAttemptRetryMassSpec_closed :
    LongAttemptRetryMassSpec :=
  longAttemptRetryMassSpec_of_firstCutCounts
    longAttemptFirstCutStageFactorSpec_closed

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.longAttemptFirstCutStageFactorSpec_closed
#print axioms PPL.Convergence.LDLocal.longAttemptRetryMassSpec_closed
