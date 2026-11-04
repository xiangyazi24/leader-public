import Leader.PPL.Elim.AttemptLongRetryClosed
import Leader.PPL.Elim.AttemptLongCleanReadyStrict
import Leader.PPL.Elim.AttemptLongSealedCorrected
import Leader.PPL.Elim.AttemptLongSealedRows
import Leader.PPL.Elim.AttemptSimulation

/-!
L17 long attempt producer: every input is closed except the six
path-qualified sealed post-carrier stage residuals.
-/

namespace PPL.Convergence.LDLocal

set_option autoImplicit false

theorem longAttemptProducerSpec_of_sealedCorrected
    (hPost : LongSealedControlStageRowsSpecCorrected) :
    LongAttemptProducerSpec :=
  longAttemptProducer_of_attempt_specs
    longSimulationSpec_proved
    (longAttemptCostSpec_closed_corrected
      longCRStageRowsSpec_proved hPost)
    longAttemptRetryMassSpec_closed

theorem longAttemptProducerSpec_of_stage_residuals
    (hLiveWait : LongLiveWaitPostCarrierResidual)
    (hAdvance : LongAdvancePostCarrierResidual)
    (hRace : LongRacePostCarrierResidual)
    (hIncident : LongIncidentPostCarrierResidual)
    (hRetained : LongRetainedPostCarrierResidual)
    (hRecovery : LongRecoveryPostCarrierResidual) :
    LongAttemptProducerSpec :=
  longAttemptProducerSpec_of_sealedCorrected
    (longSealedControlStageRowsSpecCorrected_of_stage_residuals
      hLiveWait hAdvance hRace hIncident hRetained hRecovery)

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.longAttemptProducerSpec_of_sealedCorrected
#print axioms PPL.Convergence.LDLocal.longAttemptProducerSpec_of_stage_residuals
