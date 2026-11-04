import Leader.PPL.Elim.OneLeaderBound
import Leader.PPL.Elim.AttemptSimulation
import Leader.PPL.Elim.AttemptCostModerateMin
import Leader.PPL.Elim.AttemptCostModerateSealed
import Leader.PPL.Elim.AttemptLongProducer
import Leader.PPL.Elim.AttemptLongSealedRowsAdvance
import Leader.PPL.Elim.AttemptLongSealedRowsRace
import Leader.PPL.Elim.AttemptRetryModerateSplice

namespace PPL.Convergence.L17

set_option autoImplicit false
set_option Elab.async false

/-- Lemma 17 (C17 = 862592) from the four open long sealed post-carrier
residuals; every other producer input is closed on main. -/
theorem lemma17_wordBound_of_leaves
    (hLiveWait :
      PPL.Convergence.LDLocal.LongLiveWaitPostCarrierResidual)
    (hIncident :
      PPL.Convergence.LDLocal.LongIncidentPostCarrierResidual)
    (hRetained :
      PPL.Convergence.LDLocal.LongRetainedPostCarrierResidual)
    (hRecovery :
      PPL.Convergence.LDLocal.LongRecoveryPostCarrierResidual)
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : PPL.LiteralElimConfig n)
    (hPB : PPL.Elim.PB ring C) :
    Lemma17WordBound 862592 ring C := by
  have hAttempt :
      PPL.Convergence.LDLocal.ModerateAttemptProducerSpec :=
    PPL.Convergence.LDLocal.moderateAttemptProducer_of_attempt_specs
      PPL.Convergence.LDLocal.moderateSimulationSpec_proved
      (PPL.Convergence.LDLocal.moderateAttemptCostSpec_min
        PPL.Convergence.LDLocal.moderateSealedControlStageRows)
      PPL.Convergence.LDLocal.moderateAttemptRetryMassSpec_closed

  have hLong :
      PPL.Convergence.LDLocal.LongAttemptProducerSpec :=
    PPL.Convergence.LDLocal.longAttemptProducerSpec_of_stage_residuals
      hLiveWait
      PPL.Convergence.LDLocal.longAdvancePostCarrierResidual_proved
      PPL.Convergence.LDLocal.longRacePostCarrierResidual_proved
      hIncident
      hRetained
      hRecovery

  have hPhysical :
      PPL.Convergence.LDLocal.LongBoundaryPhysicalSpec :=
    PPL.Convergence.LDLocal.longBoundaryPhysical_of_longAttempt
      hLong

  exact
    lemma17_wordBound_of_producers
      hAttempt hPhysical
      hn3 hpsi ring C hPB

end PPL.Convergence.L17

#print axioms PPL.Convergence.L17.lemma17_wordBound_of_leaves
