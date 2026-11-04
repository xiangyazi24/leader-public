import Leader.Wu.Splice.CheckXSupplier

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9CheckFreezeLifetime

open B9CheckXSupplierDesign

/-!
# B9 CHECK freeze-lifetime audit

Current main has no raw-scheduler producer for any of the three inequalities
below.  They are the exact semantic inputs required by the already-proved
`freezeBudget_le_existingTimeline` leaf.

Nearby results are weaker in the relevant metric:

* route traversal constructs finite service schedules but does not bound raw
  scheduler delay before those edges are chosen;
* splice/rewrite has finite productive-service / debt bounds, while scheduler
  stutters may be inserted arbitrarily;
* comparison cleanup has local participation bounds, and the active lineage
  writer still requires the guarded safety repair before a lease-lifetime
  theorem can be stated for the executable mechanism.
-/

/-- Missing route-lifecycle conclusion, once `routeLife` is defined as the
raw-interaction lifetime from route-gate ARM through route retirement and the
reverse RELEASE sweep. -/
def RouteLifetimeBound (routeLife T : Nat) : Prop :=
  routeLife <= T

/-- Missing staged-splice/rewrite conclusion, with `spliceLife` measured in
raw scheduler interactions rather than controller-changing services. -/
def SpliceLifetimeBound (spliceLife T : Nat) : Prop :=
  spliceLife <= T

/-- Missing active lineage-reservation conclusion, after the guarded active
writer is available: commit or safe scrub/abandon must discharge the lease
within the existing timeline. -/
def LeaseLifetimeBound (leaseLife T : Nat) : Prop :=
  leaseLife <= T

/-- Exact semantic premises needed by the existing max-budget arithmetic. -/
def FreezeLifetimeBounds
    (routeLife spliceLife leaseLife T : Nat) : Prop :=
  RouteLifetimeBound routeLife T /\
    SpliceLifetimeBound spliceLife T /\
    LeaseLifetimeBound leaseLife T

/-- No fourth timing epoch is needed once the three missing lifecycle bridges
have supplied their bounds. -/
theorem freezeBudget_le_of_lifetime_bounds
    {routeLife spliceLife leaseLife T : Nat}
    (h : FreezeLifetimeBounds routeLife spliceLife leaseLife T) :
    freezeBudget routeLife spliceLife leaseLife <= T := by
  exact freezeBudget_le_existingTimeline h.1 h.2.1 h.2.2

/-- Same seam with the three obligations exposed separately. -/
theorem freezeBudget_arithmetic_seam
    {routeLife spliceLife leaseLife T : Nat}
    (hr : RouteLifetimeBound routeLife T)
    (hs : SpliceLifetimeBound spliceLife T)
    (hl : LeaseLifetimeBound leaseLife T) :
    freezeBudget routeLife spliceLife leaseLife <= T := by
  exact freezeBudget_le_existingTimeline hr hs hl

end B9CheckFreezeLifetime

#print axioms B9CheckXSupplierDesign.freezeBudget_le_existingTimeline
#print axioms B9CheckFreezeLifetime.freezeBudget_le_of_lifetime_bounds
#print axioms B9CheckFreezeLifetime.freezeBudget_arithmetic_seam
