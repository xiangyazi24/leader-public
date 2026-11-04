import Leader.Wu.Elimination.BirthDispatcherMetadataFrames
import Leader.Wu.Elimination.MultiLeaderCleanupCheckInert

namespace K2BirthDispatcher

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLWallSweepRepair

set_option autoImplicit false
set_option pp.structureInstances false

variable {ψ κ : Nat}

theorem disappear_signal (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    authSignalPair (authorizedDisappear hψ l r) = authSignalPair (l, r) :=
  authSignalPair_of_peace
    (PPLLCompleteMultiLeaderCleanup.PhysicalBridge.CheckInert.checkInert_authorizedDisappear_peaceViewPair
      hψ l r)

theorem compare_signal (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    authSignalPair (PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hψ l r) =
      authSignalPair (l, r) :=
  authSignalPair_of_peace
    (PPLLCompleteMultiLeaderCleanup.PhysicalBridge.CheckInert.compareActionOne_peaceViewPair hψ l r)

theorem suppress_signal (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    authSignalPair (authorizedReconcile (suppressSigResetKill hψ) l r) =
      authSignalPair (l, r) := ExpiringK2Projection.suppression_observation hψ l.core r.core

/-- The actual post-CHECK metadata suffix, stopping at the writer's input.
In particular it contains no legacy Algorithm 15. -/
def beforeWrite (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q0 := authorizedDisappear hψ l r
  let q1 := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hψ q0.1 q0.2
  authorizedReconcile (suppressSigResetKill hψ) q1.1 q1.2

theorem beforeWrite_signal (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    authSignalPair (beforeWrite hψ l r) = authSignalPair (l, r) := by
  unfold beforeWrite
  dsimp only
  rw [suppress_signal, compare_signal, disappear_signal]

theorem beforeWrite_domain (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (beforeWrite hψ l r).1.core.inProtocolDomain κ ∧
      (beforeWrite hψ l r).2.core.inProtocolDomain κ := by
  let q0 := authorizedDisappear hψ l r
  have h0 := authorizedReconcile_inProtocolDomain (disappear hψ) l r
    (disappear_inProtocolDomain hψ l.core r.core hl hr)
  let q1 := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hψ q0.1 q0.2
  have h1 := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne_inProtocolDomain
    hψ q0.1 q0.2 h0.1 h0.2
  exact authorizedReconcile_inProtocolDomain (suppressSigResetKill hψ) q1.1 q1.2
    (suppressSigResetKill_inProtocolDomain hψ q1.1.core q1.2.core h1.1 h1.2)

#print axioms beforeWrite_signal
#print axioms beforeWrite_domain

end K2BirthDispatcher
