import Leader.Wu.Elimination.CleanBoundaryDecision

open FiniteUniformStoppingTree
open LDSinkGapCleanup LDTwoGapFrame
open LDSinkTwoGapNoResetKernel LDSinkTwoGapDeletionWired
open LDSinkTwoGapRestartClosure CleanBoundaryDecision
open LDSinkTwoGapReachInvariant

set_option autoImplicit false

namespace LDSinkTwoGapRankUnconditional

noncomputable section

variable {n psi : Nat}

/-- The clean-boundary field is now a theorem, so gap-pair closure along the
real physical retry step carries no residual. -/
theorem physicalReach_gapPair_unconditional
    (hpsi : psi > 0) (F : TwoGapFrame n) (x : AState n psi)
    (hx : ActiveReach (physicalBlockStep hpsi F) (GapPair hpsi F) x) :
    GapPair hpsi F x :=
  physicalReach_gapPair hpsi F
    (restartCleanBoundarySignalResidual_K2 hpsi F) x hx

/-- UNCONDITIONAL uniform rank bound: every state reachable through the real
physical block step from a gap-pair seed obeys the same fixed frame bound.
The frame is a parameter of the step, so the bound and the horizon it feeds
are the identical numerical expression at every restart. -/
theorem uniform_rank_bound_unconditional
    (hpsi : psi > 0) (F : TwoGapFrame n) (x : AState n psi)
    (hx : ActiveReach (physicalBlockStep hpsi F) (GapPair hpsi F) x) :
    R F x <= 16 * (F.recovery.d + F.attack.d) :=
  uniform_rank_bound hpsi F
    (restartCleanBoundarySignalResidual_K2 hpsi F) x hx

end

end LDSinkTwoGapRankUnconditional

#print axioms LDSinkTwoGapRankUnconditional.physicalReach_gapPair_unconditional
#print axioms LDSinkTwoGapRankUnconditional.uniform_rank_bound_unconditional
