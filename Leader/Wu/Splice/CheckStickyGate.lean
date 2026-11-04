import Leader.Wu.Splice.CheckRouteOwner


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9CheckStickyGate


open PPLL PPLLRepair PPLLResearchFormulation
open BirthPhaseCohortDesign
open B9SpliceControllerR1TableV6
open B9CheckXSupplierDesign


variable {n psi width kappa tau : Nat}


private instance instDecidableRouteWriterGateShapeV10
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (RouteWriterGateShape u) := by
  unfold RouteWriterGateShape
  infer_instance


/-! ## 1. Sticky ARM and writer rows -/


/-- V10 has exactly V9's ARM condition. -/
def RouteArmGuardV10
    (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  B9CheckRouteLifecycle.RouteArmGuardV9 l r


/-- ARM only installs the Boolean gate.  In particular, an owner that happens
    to retire in this same physical row does not launch RELEASE. -/
def routeArmWriteV10
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  let q := B9CheckRouteLifecycle.writerSkippingHostV9
    hpsi hwidth hle l.carrier.splice.base r.carrier.splice.base
  let l' := B9CheckRouteLifecycle.setPhysicalKeepV9 l q.1
  let r' := B9CheckRouteLifecycle.setPhysicalKeepV9 r q.2
  (B9CheckRouteLifecycle.setRouteWriterGateV9 l',
    B9CheckRouteLifecycle.setRouteWriterGateV9 r')


theorem routeArmWriteV10_gates
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    RouteWriterGateShape (routeArmWriteV10 hpsi hwidth hle l r).1 ∧
      RouteWriterGateShape (routeArmWriteV10 hpsi hwidth hle l r).2 := by
  simp [routeArmWriteV10]


theorem routeArmWriteV10_no_release
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    ¬ B9CheckRouteLifecycle.RouteReleaseTokenShapeV9
        (routeArmWriteV10 hpsi hwidth hle l r).1 ∧
      ¬ B9CheckRouteLifecycle.RouteReleaseTokenShapeV9
        (routeArmWriteV10 hpsi hwidth hle l r).2 := by
  have hg := routeArmWriteV10_gates
    (kappa := kappa) (tau := tau) hpsi hwidth hle l r
  constructor
  · intro hr
    exact (B9CheckRouteLifecycle.release_token_disjoint_route_gate
      (routeArmWriteV10 hpsi hwidth hle l r).1) ⟨hr, hg.1⟩
  · intro hr
    exact (B9CheckRouteLifecycle.release_token_disjoint_route_gate
      (routeArmWriteV10 hpsi hwidth hle l r).2) ⟨hr, hg.2⟩


/-- The ordinary frozen physical row is also sticky.  Existing gates are
    reinstalled after the writer-skipping host, and no owner retirement is
    inspected. -/
def routeStickyWriteV10
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  let q := B9CheckRouteLifecycle.writerSkippingHostV9
    hpsi hwidth hle l.carrier.splice.base r.carrier.splice.base
  let l' := B9CheckRouteLifecycle.setPhysicalKeepV9 l q.1
  let r' := B9CheckRouteLifecycle.setPhysicalKeepV9 r q.2
  let l'' := if RouteWriterGateShape l then
    B9CheckRouteLifecycle.setRouteWriterGateV9 l' else l'
  let r'' := if RouteWriterGateShape r then
    B9CheckRouteLifecycle.setRouteWriterGateV9 r' else r'
  (l'', r'')


theorem routeStickyWriteV10_left_sticky
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hg : RouteWriterGateShape l) :
    RouteWriterGateShape
      (routeStickyWriteV10 hpsi hwidth hle l r).1 := by
  simp [routeStickyWriteV10, hg]


theorem routeStickyWriteV10_right_sticky
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hg : RouteWriterGateShape r) :
    RouteWriterGateShape
      (routeStickyWriteV10 hpsi hwidth hle l r).2 := by
  simp [routeStickyWriteV10, hg]


/-! ## 2. Cleanup-owned quiescent release -/


/-- Keep the physical projection unambiguous: this is the V9 lifecycle
    projection, not the older route-gate alias. -/
abbrev xPhysicalV10
    (S : XSupplierConfig n psi kappa tau) :
    BirthPhaseCohortDesign.FC n psi kappa tau :=
  B9CheckRouteLifecycle.xPhysical S


/-- Proof-side certificate supplied by comparison cleanup before it is allowed
    to issue the release token.  `no_live_route` is the safety condition;
    `no_arm_owner` makes the release window stable against a fresh ARM from an
    old executable `path0Crossed` owner. -/
structure SegmentRouteQuiescentV10
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (S : XSupplierConfig n psi kappa tau)
    (segment : Fin n -> Prop) : Prop where
  no_live_route : forall i, segment i ->
    B9CheckRouteLifecycle.ReleasedSiteSafeV9
      (kappa := kappa) (tau := tau) hpsi h2 ring S i
  no_arm_owner : forall i, segment i ->
    ¬ B9CheckRouteLifecycle.CrossedRouteOwnerV9 (S i).splice


/-- RELEASE may be launched only by cleanup, at a still-gated site in the
    certified quiescent segment. -/
def QuiescentReleaseGuardV10
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (S : XSupplierConfig n psi kappa tau)
    (segment : Fin n -> Prop) (i : Fin n) : Prop :=
  SegmentRouteQuiescentV10 hpsi h2 ring S segment ∧
    segment i ∧ RouteWriterGateShape (S i).splice


/-- The cleanup handoff reuses the old `(none,true,true)` code point. -/
def startQuiescentReleaseV10
    (u : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau :=
  B9CheckRouteLifecycle.setRouteReleaseTokenV9 u


theorem startQuiescentReleaseV10_token
    (u : R1AgentStateV6 psi kappa tau) :
    B9CheckRouteLifecycle.RouteReleaseTokenShapeV9
      (startQuiescentReleaseV10 u) := by
  simp [startQuiescentReleaseV10]


/-- Once started, the reverse token uses V9's release guard and write verbatim. -/
def RouteReleaseSweepGuardV10
    (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  B9CheckRouteLifecycle.RouteReleaseGuardV9 l r


def routeReleaseWriteV10
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  B9CheckRouteLifecycle.routeReleaseWriteV9 l r


/-- Exact V10 release-safety obligation: every site whose gate cleanup may
    start from the certified segment is crossed by no live route. -/
def RouteReleaseSoundV10
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (h2 : 2 <= psi) (ring : DirectedRing n) : Prop :=
  forall (S : XSupplierConfig n psi kappa tau)
      (segment : Fin n -> Prop) (i : Fin n),
    QuiescentReleaseGuardV10 hpsi h2 ring S segment i ->
      B9CheckRouteLifecycle.ReleasedSiteSafeV9
        (kappa := kappa) (tau := tau) hpsi h2 ring S i


theorem routeReleaseSoundV10
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (h2 : 2 <= psi) (ring : DirectedRing n) :
    RouteReleaseSoundV10
      (width := width) (kappa := kappa) (tau := tau)
      hpsi hwidth hle h2 ring := by
  intro S segment i h
  exact h.1.no_live_route i h.2.1


/-- The same certificate also forbids a stale local ARM owner while the reverse
    release sweep is being launched. -/
theorem quiescentReleaseGuardV10_no_arm
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (S : XSupplierConfig n psi kappa tau)
    (segment : Fin n -> Prop) (i : Fin n)
    (h : QuiescentReleaseGuardV10 hpsi h2 ring S segment i) :
    ¬ B9CheckRouteLifecycle.CrossedRouteOwnerV9 (S i).splice := by
  exact h.1.no_arm_owner i h.2.1


/-- V10 adds no product state: the gate bit and reverse token are the V9 code
    points already counted in the factor 64. -/
theorem routeLifecycleStateFactorV10_eq :
    xSupplierStateFactor = 64 := by
  exact B9CheckRouteLifecycle.routeLifecycleStateFactorV9_eq


/-! ## 3. Lifetime charge -/


/-- Sticky-gate tail charge, in the same style as `LeaseLifetimeBound` and
    `RouteLifetimeBound`: measure only from the last live route's retirement
    until the reverse release sweep has removed the final gate.  This tail is
    charged to comparison cleanup, not to any one route. -/
def ComparisonCleanupGateTailBoundV10
    (lastRetirementToSweepEnd T : Nat) : Prop :=
  lastRetirementToSweepEnd <= T


end B9CheckStickyGate


#print axioms B9CheckStickyGate.routeArmWriteV10_gates
#print axioms B9CheckStickyGate.routeArmWriteV10_no_release
#print axioms B9CheckStickyGate.routeStickyWriteV10_left_sticky
#print axioms B9CheckStickyGate.routeStickyWriteV10_right_sticky
#print axioms B9CheckStickyGate.startQuiescentReleaseV10_token
#print axioms B9CheckStickyGate.routeReleaseSoundV10
#print axioms B9CheckStickyGate.quiescentReleaseGuardV10_no_arm
#print axioms B9CheckStickyGate.routeLifecycleStateFactorV10_eq
#print axioms B9CheckRouteOwner.overlapping_live_route_fixture
