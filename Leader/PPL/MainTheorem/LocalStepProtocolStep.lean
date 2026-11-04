import Leader.PPL.MainTheorem.MissAmplification
import Leader.Wu.Scheduler.ClosedDomainAmplification

/-!
P_PL Theorem 1 cleanup, phase 2: the declarations of this file that served only the old
psi <= log2 n + 1 route to `theorem1Statement_proved` moved to
`Leader/PPL/LogWindow/CostTiny.lean`, namespace `PPL.Superseded.LogWindow`: `Theorem1TinyProducer`, `Theorem1TinyUniformProducer`, `theorem1TinyProducer_mono`, `theorem1Tiny_uniformPsiBound`, `theorem1TinyUniformProducer_of_producer`, `theorem1TinyBlock`, `theorem1TinyBlock_pos`, `theorem1TinyBlock_le_64`, `theorem1TinySPLTest`, `theorem1TinySPLTest_spec`, `theorem1TinyReaches_eq_hits`, `theorem1TinyFailure_eq_localMiss`, `theorem1TinyEndpointMiss_eq_localMiss`, `theorem1TinyHalfFailure_of_producer`, `theorem1TinyNCost_of_producer`.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail
open PPLLResearchFormulation
open PPLLTraceConvergence
open PPLLSchedulerBlocks
open PPLLClosedDomainSchedulerAmplificationSol

/--
The generic local scheduler step is exactly the PopulationProtocol step for
the literal P_PL protocol wrapper.
-/
theorem theorem1SmallN_localStep_eq_protocolStep
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n) :
    localStep ring
        (PPL.protocol psi kappa).transition C e =
      PopulationProtocol.step
        (PPL.protocol psi kappa) ring C e := by
  exact
    PPLLResearchFormulation.localStep_eq_protocol_step
      (PPL.protocol psi kappa) ring C e

end PPL

#print axioms PPL.theorem1SmallN_localStep_eq_protocolStep
