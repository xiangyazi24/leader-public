import Leader.Wu.Birth.ShortDoneTerminalConsumer

set_option autoImplicit false

/-! # The terminal host row never removes a right leader

`row_right_leader`: if the responder of the physical terminal host row is a leader, it is still a leader
after the row.  The whole prefix through CHECK, the stationary persistent writer, normalization and expiry
is covered by `BirthShortDoneTerminalConsumer.metadata_existing_leaders`; the missing piece was the final
collision/K2 stage: both-leader collisions clear only the left leader, and the K2 sink kernel frames the
right leader flag (`LDSinkTwoGapEpochSuccessor.kernelC_right_leader_eq`).

Consumer: the with-leader physical rows of V10h (a surviving right leader makes the served and outgoing
edges non-dangerous). The left analogue is false (collisions and MOVE clear left leaders). -/

namespace BirthShortDoneTerminalRowRightLeader

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation PPLLExpiringComparisonRepair
open K2BirthDispatcher ExpiringK2Projection LDSinkTwoGapEpochSuccessor LDSinkKernelC

variable {ψ κ τ width : Nat}

theorem collisionRow_right_leader (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    (collisionRow hψ l r).2.core.core.leader = r.core.core.leader := by
  by_cases hb : l.core.core.leader = true ∧ r.core.core.leader = true
  · exact (collisionRow_of_both hψ l r hb.1 hb.2).2.1.trans hb.2.symm
  · rw [collisionRow_of_not_both hψ l r hb]
    have ho := ExpiringK2Projection.observe_row hψ l r
    have he := congrArg (fun q : AgentState 1 × AgentState 1 => q.2.leader) ho
    change (ExpiringK2Projection.row hψ l r).2.core.core.leader =
      (sinkKernelC (by decide) (observeCell l) (observeCell r)).2.leader at he
    exact he.trans (kernelC_right_leader_eq (by decide) (observeCell l) (observeCell r))

theorem finalPhysical_right_leader (hψ : 0 < ψ) (oldL oldR metaL metaR : ExpiringAgentState ψ κ τ) :
    (finalPhysical hψ oldL oldR metaL metaR).2.core.core.leader = metaR.core.core.leader := by
  unfold finalPhysical
  exact (collisionRow_right_leader hψ _ _).trans (initializeNewborn_leader oldR metaR)

theorem row_right_leader_eq (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    (BirthShortDoneTerminalHost.row hψ hwidth hle l r).2.core.core.leader =
      (BirthShortDoneTerminalHost.metadata hψ hwidth hle l r).2.core.core.leader := by
  unfold BirthShortDoneTerminalHost.row
  dsimp only
  exact finalPhysical_right_leader hψ l r _ _

theorem row_right_leader (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ) (hr : r.core.core.leader = true) :
    (BirthShortDoneTerminalHost.row hψ hwidth hle l r).2.core.core.leader = true :=
  (row_right_leader_eq hψ hwidth hle l r).trans
    ((BirthShortDoneTerminalConsumer.metadata_existing_leaders hψ hwidth hle l r).2 hr)

end BirthShortDoneTerminalRowRightLeader
