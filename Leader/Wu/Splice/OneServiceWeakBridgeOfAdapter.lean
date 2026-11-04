import Leader.Wu.Splice.ZeroRefreshBlockMass

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9OneServiceWeakBridge

open FiniteUniformStoppingTree
open BirthB1DrainCoupling
open B9SpliceControllerR1TableV6

variable {n psi kappa tau : Nat}

/-- Counting-only replacement for the refuted V10c semantic bridge.
It deliberately contains no V10c productivity claim. -/
def OneServiceWeakBridgeV10c
    (A : PortBlockAdapter (R1ConfigV6 n psi kappa tau) n) : Prop :=
  forall C : R1ConfigV6 n psi kappa tau,
    n ^ (2 * n) <=
      4 * successCount (hitStep A.next A.hit) (.active C) 1

/-- Existing generic three-port coupling supplies the weak bridge for every
explicit adapter on the consumer domain `3 <= n`. -/
theorem oneServiceWeakBridgeV10c_of_adapter
    (A : PortBlockAdapter (R1ConfigV6 n psi kappa tau) n)
    (hn : 3 <= n) :
    OneServiceWeakBridgeV10c A := by
  intro C
  exact portBlock_quarter A hn C

#print axioms B9OneServiceWeakBridge.oneServiceWeakBridgeV10c_of_adapter

end B9OneServiceWeakBridge
