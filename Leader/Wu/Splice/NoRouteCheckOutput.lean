import Leader.Wu.Splice.CheckStructuralCensus
import Leader.Wu.Splice.NoRouteDoneStages
import Leader.Wu.Splice.NoRouteStageCheck

set_option autoImplicit false
set_option Elab.async false

namespace B9NoRouteCheckOutput

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open B9CheckStructuralCensus
open B9NoRouteStagesB

variable {n psi kappa tau : Nat}

/-- The consumer-facing CHECK output theorem.  The supplied hypotheses are exactly
    the facts needed at the CHECK seam: no generation transport is unfolded. -/
theorem currentCheckOutputNoEqual_of_input
    (hpsi : 0 < psi)
    (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (e : Fin n)
    (hinput : NoEqualOnPair
      (currentCheckInputAt hpsi h2 ring C e).1.core
      (currentCheckInputAt hpsi h2 ring C e).2.core)
    (hleft : LeftZeroDepart
      (currentCheckInputAt hpsi h2 ring C e).1.core) :
    NoEqualOnPair
      (currentCheckOutputAt hpsi h2 ring C e).1.core
      (currentCheckOutputAt hpsi h2 ring C e).2.core := by
  unfold currentCheckOutputAt
  exact B9NoRouteStageCheck.check_preserves_noEqual hpsi
    (currentCheckInputAt hpsi h2 ring C e).1
    (currentCheckInputAt hpsi h2 ring C e).2
    hinput hleft

end B9NoRouteCheckOutput

#print axioms B9NoRouteCheckOutput.currentCheckOutputNoEqual_of_input
