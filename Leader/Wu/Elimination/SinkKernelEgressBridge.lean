import Leader.Wu.Elimination.SinkGapCleanup
import Leader.Wu.Elimination.MultiLeaderCleanup

/-! Bridge: the verbatim copy `LDSinkGapCleanup.sinkKernel` is definitionally the
repository's `eliminateLeadersNoCollisionEgressSink`. -/

theorem LDSinkGapCleanup.sinkKernel_eq_egressSink {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    LDSinkGapCleanup.sinkKernel hψ l r = PPLLCompleteMultiLeaderCleanup.eliminateLeadersNoCollisionEgressSink hψ l r := rfl

#print axioms LDSinkGapCleanup.sinkKernel_eq_egressSink
