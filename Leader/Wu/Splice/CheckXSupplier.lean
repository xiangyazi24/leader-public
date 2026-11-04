import Leader.Wu.Splice.CheckGlobalWitnessCensus
import Leader.Wu.Splice.StaleHoldTable


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9CheckXSupplierDesign


open PPLL PPLLRepair PPLLResearchFormulation
open BirthPhaseCohortDesign
open B9CheckStructuralCensus
open B9CheckGlobalWitnessCensus
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table
open B9SpliceControllerR1TableV4
open B9SpliceControllerR1TableV6
open B9SpliceControllerR1TableV7
open B9SpliceControllerR1TableV8
open BirthDoneLineageQuarantineDesign


variable {n psi kappa tau : Nat}


/-- Combined physical controller.  The route gate is encoded inside `splice`,
so the only independent product beyond V8 is the four-valued lineage lease. -/
structure XSupplierAgent (psi kappa tau : Nat) where
  splice : R1AgentStateV6 psi kappa tau
  lineage : LineageRole
  deriving DecidableEq, Repr


abbrev XSupplierConfig (n psi kappa tau : Nat) :=
  Fin n -> XSupplierAgent psi kappa tau


/-- Reuse V8's formerly-malformed `(none,true,false)` code point as the
route-owned stationary-writer gate. -/
def RouteWriterGateShape
    (u : R1AgentStateV6 psi kappa tau) : Prop :=
  role u.carrier = .none /\
    u.carrier.repairPending = true /\
    u.acquireTicket = false


private instance instDecidableRouteWriterGateShape
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (RouteWriterGateShape u) := by
  unfold RouteWriterGateShape
  infer_instance


/-- Controller-only ARM.  No physical field or ticket is created. -/
def armRouteWriterGate
    (u : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau :=
  { u with
      carrier := { u.carrier with repairPending := true }
      acquireTicket := false }


/-- Controller-only RELEASE. -/
def clearRouteWriterGate
    (u : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau :=
  { u with
      carrier := { u.carrier with repairPending := false }
      acquireTicket := false }


/-- Literal controller rows to be placed above V8 malformed-pending cleanup. -/
def routeArmWrite
    (l r : R1AgentStateV6 psi kappa tau) :=
  (armRouteWriterGate l, r)


def routeReleaseWrite
    (l r : R1AgentStateV6 psi kappa tau) :=
  (clearRouteWriterGate l, r)


/-- Only the stationary writer is frozen while either touched endpoint owns a
live route gate.  This predicate is consumed at the writer cut, not around the
whole host row. -/
def RouteWriterFrozenPair
    (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  RouteWriterGateShape l \/ RouteWriterGateShape r


/-- Exact state multiplier over the old physical carrier. -/
def lineageRoleFactor : Nat := 4


def xSupplierStateFactor : Nat :=
  controllerStateFactorV8 * lineageRoleFactor


theorem xSupplierStateFactor_eq : xSupplierStateFactor = 64 := by
  unfold xSupplierStateFactor lineageRoleFactor
  rw [controllerStateFactorV8_eq]


/-! The three exact global theorems the executable mechanism must supply. -/


def MechanismSuppliesPeakSafeRewriteAndBoundaryX
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  PeakSafeRewriteAndBoundaryX
    (kappa := kappa) (tau := tau) hpsi h2 ring


def MechanismSuppliesComparisonRouteRefreshX
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  ComparisonRouteRefreshX
    (kappa := kappa) (tau := tau) hpsi h2 ring


def MechanismSuppliesCrossedIDRewriteX
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  CrossedIDRewriteX
    (kappa := kappa) (tau := tau) hpsi h2 ring


/-- The only timing arithmetic needed at this interface: each freeze inherits
one already-budgeted transaction lifetime rather than starting a new epoch. -/
def freezeBudget
    (routeLife spliceLife leaseLife : Nat) : Nat :=
  Nat.max routeLife (Nat.max spliceLife leaseLife)


theorem freezeBudget_le_existingTimeline
    {routeLife spliceLife leaseLife T : Nat}
    (hr : routeLife <= T) (hs : spliceLife <= T)
    (hl : leaseLife <= T) :
    freezeBudget routeLife spliceLife leaseLife <= T := by
  unfold freezeBudget
  exact Nat.max_le.mpr
    ⟨hr, Nat.max_le.mpr ⟨hs, hl⟩⟩


/-! Closed controller fixtures.  `clearControlV6` gives a literal neutral V8
site while retaining the real physical carrier. -/


private def routeNeutralFixture : R1AgentStateV6 2 1 1 :=
  clearControlV6 (q11703StartV7 (0 : Fin 3))


private def routeArmedFixture : R1AgentStateV6 2 1 1 :=
  (routeArmWrite routeNeutralFixture routeNeutralFixture).1


theorem route_arm_fixture :
    RouteWriterGateShape routeArmedFixture := by
  unfold RouteWriterGateShape routeArmedFixture routeArmWrite
    armRouteWriterGate routeNeutralFixture
  decide


/-- The new gate is not V7's `(none,false,true)` host fence. -/
theorem route_gate_disjoint_fixture :
    ¬ HostFenceShapeV7 routeArmedFixture := by
  unfold HostFenceShapeV7 routeArmedFixture routeArmWrite
    armRouteWriterGate routeNeutralFixture
  decide


private def routeReleasedFixture : R1AgentStateV6 2 1 1 :=
  (routeReleaseWrite routeArmedFixture routeNeutralFixture).1


theorem route_release_fixture :
    ¬ RouteWriterGateShape routeReleasedFixture := by
  unfold RouteWriterGateShape routeReleasedFixture routeReleaseWrite
    clearRouteWriterGate routeArmedFixture routeArmWrite
    armRouteWriterGate routeNeutralFixture
  decide


#print axioms B9CheckXSupplierDesign.xSupplierStateFactor_eq
#print axioms B9CheckXSupplierDesign.freezeBudget_le_existingTimeline
#print axioms B9CheckXSupplierDesign.route_arm_fixture
#print axioms B9CheckXSupplierDesign.route_gate_disjoint_fixture
#print axioms B9CheckXSupplierDesign.route_release_fixture


end B9CheckXSupplierDesign
