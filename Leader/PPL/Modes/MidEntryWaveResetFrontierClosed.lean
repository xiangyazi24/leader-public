import Leader.PPL.Modes.MidEntryWaveResetFrontierHit

namespace PPL.Modes.Lemma5

set_option autoImplicit false

/--
The reset-frontier one-step debt of the L5(i) Wave route, closed from the
three position-of-e rows: the appended letter is away from the frontier,
hits it with more selected edges to come, or hits the last selected edge.
-/
theorem lemma5iLeaderWaveResetFrontierOneStep_proved :
    Lemma5iLeaderWaveResetFrontierOneStep :=
  lemma5iLeaderWaveResetFrontierOneStep_of_routeRows
    lemma5iWaveResetFrontierAwayRow_proved
    lemma5iWaveResetFrontierHitContinueRow_proved
    lemma5iWaveResetFrontierHitFinishRow_proved

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iLeaderWaveResetFrontierOneStep_proved
