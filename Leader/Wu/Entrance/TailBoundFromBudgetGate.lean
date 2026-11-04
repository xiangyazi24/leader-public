import Leader.Wu.Entrance.TailComposition
import Leader.Wu.Entrance.FinalLeafDomainBound

set_option autoImplicit false
set_option Elab.async false

namespace CFinalRefereeForm

open CFinalAssembly2

variable {n psi : Nat}

-- Direct corollary of CFinalAssembly2.sharedBirthWordMassV2_of_frozenC4
-- and CFinalTailComposition.b7_bound_of_sharedBirthWordMass.
theorem current_referee_form
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (h3 : 2 < psi) (hpsin : psi <= n)
    (ring : DirectedRing n)
    (hC4 :
      B6EntranceK2Budget.B6EntranceK2Budget.B6EntranceK2Budget.FrozenC4GateBundle
        hpsi h2 ring)
    (hSim : B6EntranceK2Mass3.C4C5FinalR1MassSimulation hpsi h2 ring) :
    CFinalAssembly2.FinalB7OneOverN
      hpsi h2 ring (CFinalAssembly2.FinalLeafHV2 n psi) := by
  have hLeaf := CFinalAssembly2.sharedBirthWordMassV2_of_frozenC4
    hpsi h2 h3 hpsin ring hC4 hSim
  have hn2 : 2 <= n := by omega
  exact CFinalTailComposition.b7_bound_of_sharedBirthWordMass
    hpsi h2 hn2 ring hLeaf

end CFinalRefereeForm
