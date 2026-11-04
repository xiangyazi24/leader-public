import Leader.PPL.Elim.TransferOneLeader
import Leader.PPL.Elim.SealedStepConsumers
import Leader.PPL.Elim.PBClosure

/-!
# YSM21 repair: LD(736) ⇒ one leader, with proved PB closure

Composes the accepted Wave-5 pieces.  The only remaining hypotheses are the two
LD(736) attempt producers (`ModerateAttemptProducerSpec` and
`LongBoundaryPhysicalSpec`).
-/

namespace PPL.Convergence.LDTransfer

set_option autoImplicit false

open PPL.Convergence.LDLocal
open K2ArbitraryElimination.FiniteAccounting

theorem ld736Statement_of_producers
    (hAttempt : ModerateAttemptProducerSpec)
    (hPhysical : LongBoundaryPhysicalSpec) :
    LD736Statement := by
  intro n hn ring C hPB h2 F T
  exact
    ld736_costNumerator_of_producers
      hAttempt hPhysical hn ring C hPB h2 F T

/-- Paper-level YSM21 repair endpoint: from any PB configuration, the
expected time to a unique leader is at most 862592 n² (finite-word form). -/
theorem one_leader_costNumerator_of_producers
    (hAttempt : ModerateAttemptProducerSpec)
    (hPhysical : LongBoundaryPhysicalSpec)
    {n : Nat} (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Config n) (hPB : PPL.Elim.PB ring C) :
    ∀ T : Nat,
      costNumerator (stepE ring)
        (fun D => PPL.Elim.leaderCount D = 1) C T ≤
      n ^ T * (862592 * n * n) :=
  ld736_transfer_costNumerator
    PPL.Convergence.LDLocal.pbStepClosure PPL.Convergence.LDLocal.lastLeaderSurvival
    (ld736Statement_of_producers hAttempt hPhysical)
    hn ring C hPB

end PPL.Convergence.LDTransfer

#print axioms PPL.Convergence.LDTransfer.ld736Statement_of_producers
#print axioms PPL.Convergence.LDTransfer.one_leader_costNumerator_of_producers
