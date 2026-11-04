import Leader.Wu.Entrance.LocalRulerWord

set_option autoImplicit false
set_option Elab.async false

namespace B6PreparedRelativeContract

open PPLL PPLLResearchFormulation
open BirthCheckPermitRepairLeaf BirthCheckChainR1Ring
open B6LocalReverseFill

variable {n psi kappa tau : Nat}
variable {ring : DirectedRing n}

/-- Relative ruler normal form: full successor arc, with no absolute phase.
Declared here, upstream of the entrance modules, so that a consumer of the
prepared state can require it without importing its own consumer. -/
def RulerNFRel (hpsi : 0 < psi) (ring : DirectedRing n)
    (I : Interval ring)
    (C : BirthCheckPermitRepairLeaf.FC n psi kappa tau) : Prop :=
  ∀ k : Nat, k + 1 < I.size ->
    (C (cell ring I.first (k + 1))).core.core.label =
      B6LocalRuler.nextLabel hpsi
        (C (cell ring I.first k)).core.core.label

/-- The one new semantic residual: the missing first core ruler edge `0 -> 1`. -/
def ZeroOneRulerLeaf (hpsi : 0 < psi) (ring : DirectedRing n)
    (I : Interval ring)
    (C : BirthCheckPermitRepairLeaf.FC n psi kappa tau) : Prop :=
  (C (cell ring I.first 1)).core.core.label =
    B6LocalRuler.nextLabel hpsi
      (C (cell ring I.first 0)).core.core.label

end B6PreparedRelativeContract
