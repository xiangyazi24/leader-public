import Leader.Wu.Splice.ZeroRefreshBlockMass

set_option autoImplicit false

namespace B9OneServiceWeakBridge

open FiniteUniformStoppingTree
open BirthB1DrainCoupling
open B9SpliceControllerR1TableV6

variable {n psi kappa tau : Nat}

/-- Counting-only replacement for the refuted V10c semantic bridge.
It deliberately says nothing about V10c productivity. -/
def OneServiceWeakBridgeV10c
    (A : PortBlockAdapter (R1ConfigV6 n psi kappa tau) n) : Prop :=
  forall C : R1ConfigV6 n psi kappa tau,
    n ^ (2 * n) <=
      4 * successCount (hitStep A.next A.hit) (.active C) 1

end B9OneServiceWeakBridge
