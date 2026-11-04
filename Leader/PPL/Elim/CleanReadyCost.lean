import Leader.PPL.Elim.CleanReadyDrain
import Leader.PPL.Elim.CleanReadySweep

/-!
# LD(736) File 2 endpoint

All four corrected clean-ready stage obligations are proved, so the File-2 raw cost
bound holds with no further physical assumptions.
-/

namespace PPL.Convergence.LDLocal

theorem crRankStep_proved : CRRankStepSpecCorrected :=
  crRankStep_corrected crDrainStep crRepairStep crSweepStep crReturnStep

theorem cleanReady_cost_proved : CleanReadyCostObligation :=
  cleanReady_cost crDrainStep crRepairStep crSweepStep crReturnStep

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.crRankStep_proved
#print axioms PPL.Convergence.LDLocal.cleanReady_cost_proved
