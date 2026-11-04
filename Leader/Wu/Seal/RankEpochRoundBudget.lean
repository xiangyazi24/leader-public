import Leader.Wu.Seal.RankEpochReadyOutcome
import Leader.Wu.Seal.RankEpochStoppedOutcome
import Leader.Wu.Scheduler.TraceConvergence
import Leader.Wu.Seal.HomeFrontQuotient
import Leader.Wu.Seal.RankEpochMonotone
import Leader.Wu.Seal.ABGate

set_option autoImplicit false
set_option Elab.async false

namespace PPLLCompleteMultiLeaderCleanup
namespace SealRankEpochSecondSubtarget

open PPLL
open PPLLCompleteMultiLeaderCleanup.SealRankEpochFirstSubtarget

variable {n psi kappa tau : Nat}

/-- Explicit stopped-round target.  The first subtarget gives H = 2*n^3
interactions and the second subtarget records the logarithmic round budget
separately; no asymptotic notation is hidden in the statement. -/
theorem stoppedOutcome_round_budget_Hp
    (ring : DirectedRing n) (hn : 1 < n)
    (base X : Fin n -> PPLLCompleteMultiLeaderCleanup.PPartialSealSweepHomeFrontQuotientSol.SealSweepHomeFrontSite)
    (hX : PPLLCompleteMultiLeaderCleanup.PPartialSealSweepRankEpochAuditSol.ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base X)
    (hgate : PPLLCompleteMultiLeaderCleanup.PPartialSealSweepABGateBreakthroughSol.HomeFrontReadyOrAB ring X)
    (roundBudget : Nat)
    (hRound : 2 * n ^ 3 <= roundBudget)
    (hProbabilityLift :
      4 * PPLLTraceConvergence.localHitCount ring PPLLCompleteMultiLeaderCleanup.PPartialSealSweepHomeFrontQuotientSol.sealSweepHomeFrontPair
        (PPLLCompleteMultiLeaderCleanup.SealRankEpochStoppedOutcome.rankEpochDropOrPostSealTest base (rankEpochReadyTest ring))
        X (2 * n ^ 3) <=
      16 * PPLLTraceConvergence.localHitCount ring PPLLCompleteMultiLeaderCleanup.PPartialSealSweepHomeFrontQuotientSol.sealSweepHomeFrontPair
        (PPLLCompleteMultiLeaderCleanup.SealRankEpochStoppedOutcome.rankEpochDropOrPostSealTest base (rankEpochReadyTest ring))
        X roundBudget) :
    n ^ (2 * n ^ 3) <=
      16 * PPLLTraceConvergence.localHitCount ring PPLLCompleteMultiLeaderCleanup.PPartialSealSweepHomeFrontQuotientSol.sealSweepHomeFrontPair
        (PPLLCompleteMultiLeaderCleanup.SealRankEpochStoppedOutcome.rankEpochDropOrPostSealTest base (rankEpochReadyTest ring))
        X roundBudget := by
  have hcount := readyOrAB_twoOutcome_scaled_count
    (psi := psi) (kappa := kappa) (tau := tau)
    ring hn base X hX hgate
  exact Nat.le_trans hcount hProbabilityLift

end SealRankEpochSecondSubtarget
end PPLLCompleteMultiLeaderCleanup

#print axioms PPLLCompleteMultiLeaderCleanup.SealRankEpochSecondSubtarget.stoppedOutcome_round_budget_Hp
