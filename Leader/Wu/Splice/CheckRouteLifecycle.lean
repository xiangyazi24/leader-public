import Leader.Wu.Splice.CheckRouteGate


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9CheckRouteLifecycle


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair PPLLComparisonHistory
open BirthSigMoveDisposalRepair BirthGenerationDone BirthStationaryWrite
open BirthShortDoneCuts BirthShortDoneTerminalEntryCut
open BirthShortDoneTerminalHost
open K2BirthDispatcher K2BirthLeaderNormalize
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV6
open B9SpliceControllerR1TableV7 B9SpliceControllerR1TableV8
open B9CheckXSupplierDesign B9CheckRouteGate B9CheckStructuralCensus
open BirthDoneLineageQuarantineDesign


variable {n psi width kappa tau : Nat}


/-! ## 1. Two route-lifecycle code points -/


/-- Controller-neutral V8 code point. -/
def RouteNeutralV9 (u : R1AgentStateV6 psi kappa tau) : Prop :=
  role u.carrier = .none /\
    u.carrier.repairPending = false /\
    u.acquireTicket = false


/-- The one additional *meaning*, not one additional state: `(none,true,true)`.
It is the backward retirement token. -/
def RouteReleaseTokenShapeV9
    (u : R1AgentStateV6 psi kappa tau) : Prop :=
  role u.carrier = .none /\
    u.carrier.repairPending = true /\
    u.acquireTicket = true


private instance instDecidableRouteNeutralV9
    (u : R1AgentStateV6 psi kappa tau) : Decidable (RouteNeutralV9 u) := by
  unfold RouteNeutralV9
  infer_instance


private instance instDecidableRouteWriterGateShapeV9
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (RouteWriterGateShape u) := by
  unfold RouteWriterGateShape
  infer_instance


private instance instDecidableRouteReleaseTokenShapeV9
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (RouteReleaseTokenShapeV9 u) := by
  unfold RouteReleaseTokenShapeV9
  infer_instance


private instance instDecidableRouteWriterFrozenPairV9
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (RouteWriterFrozenPair l r) := by
  unfold RouteWriterFrozenPair
  infer_instance


/-- A site may participate in the route-only table iff it is neutral or already
one of our gates.  Active splice roles are deliberately excluded. -/
def RouteGateCompatibleV9
    (u : R1AgentStateV6 psi kappa tau) : Prop :=
  RouteNeutralV9 u \/ RouteWriterGateShape u


private instance instDecidableRouteGateCompatibleV9
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (RouteGateCompatibleV9 u) := by
  unfold RouteGateCompatibleV9
  infer_instance


/-- Force exactly the adopted gate code point, preserving all physical state. -/
def setRouteWriterGateV9
    (u : R1AgentStateV6 psi kappa tau) : R1AgentStateV6 psi kappa tau :=
  setControlV6 u .none true


/-- Force `(none,true,true)`: first install the gate code point, then set the
already-existing V6 ticket bit. -/
def setRouteReleaseTokenV9
    (u : R1AgentStateV6 psi kappa tau) : R1AgentStateV6 psi kappa tau :=
  setTicketV6 (setControlV6 u .none true) true


/-- Return either route-only code point to ordinary controller-neutral state. -/
def clearRouteLifecycleV9
    (u : R1AgentStateV6 psi kappa tau) : R1AgentStateV6 psi kappa tau :=
  clearControlV6 u


@[simp] theorem setRouteWriterGateV9_shape
    (u : R1AgentStateV6 psi kappa tau) :
    RouteWriterGateShape (setRouteWriterGateV9 u) := by
  unfold setRouteWriterGateV9 RouteWriterGateShape
  exact ⟨rfl, rfl, rfl⟩


@[simp] theorem setRouteReleaseTokenV9_shape
    (u : R1AgentStateV6 psi kappa tau) :
    RouteReleaseTokenShapeV9 (setRouteReleaseTokenV9 u) := by
  unfold setRouteReleaseTokenV9 RouteReleaseTokenShapeV9
  exact ⟨rfl, rfl, rfl⟩


/-- The gate and release token are two distinct old V8 code points. -/
theorem release_token_disjoint_route_gate
    (u : R1AgentStateV6 psi kappa tau) :
    ¬ (RouteReleaseTokenShapeV9 u /\ RouteWriterGateShape u) := by
  intro h
  rcases h with ⟨hr, hg⟩
  unfold RouteReleaseTokenShapeV9 at hr
  unfold RouteWriterGateShape at hg
  have hbad : (true : Bool) = false := hr.2.2.symm.trans hg.2.2
  cases hbad


/-- No product is added to the carrier. -/
theorem routeLifecycleStateFactorV9_eq : xSupplierStateFactor = 64 := by
  exact xSupplierStateFactor_eq


/-! ## 2. Executable ARM and RELEASE guards -/


/-- Existing executable route owner.  A forged true value only over-gates;
canonical authorization is a separate already-existing invariant. -/
def CrossedRouteOwnerV9
    (u : R1AgentStateV6 psi kappa tau) : Prop :=
  u.carrier.splice.base.core.path0Crossed = true


private instance instDecidableCrossedRouteOwnerV9
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (CrossedRouteOwnerV9 u) := by
  unfold CrossedRouteOwnerV9
  infer_instance


/-- ARM is a finite local test.  It is allowed when both controller code points
belong to the route-only subtable and the left endpoint carries the existing
crossed-route owner bit.  The physical row used by this service skips WRITE. -/
def RouteArmGuardV9
    (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  RouteGateCompatibleV9 l /\
    RouteGateCompatibleV9 r /\
    CrossedRouteOwnerV9 l


private instance instDecidableRouteArmGuardV9
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (RouteArmGuardV9 l r) := by
  unfold RouteArmGuardV9
  infer_instance


/-- RELEASE is local once the retirement token exists.  The token is on the
right because the directed route moved clockwise and the cleanup sweep moves
backward across the trail. -/
def RouteReleaseGuardV9
    (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  RouteReleaseTokenShapeV9 r


private instance instDecidableRouteReleaseGuardV9
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (RouteReleaseGuardV9 l r) := by
  unfold RouteReleaseGuardV9
  infer_instance


/-- One reverse release service.  Across a gate the token moves one site left;
at the first nongate it disappears.  Physical state is untouched. -/
def routeReleaseWriteV9
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  if RouteWriterGateShape l then
    (setRouteReleaseTokenV9 l, clearRouteLifecycleV9 r)
  else
    (l, clearRouteLifecycleV9 r)


/-! ## 3. The literal writer-skipping physical host -/


/-- Ordinary metadata with exactly one edit: use the existing `beforeWriteWidth`
cut directly instead of `stationaryPersistentAuthorizedRow`.  Birth marking is
still computed from the actual resulting pair. -/
def doneOrdinaryMetadataFrozenV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (kappa : Nat) (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let c := doneThroughCheckEntryWidth hpsi hwidth hle kappa l r
  let b := beforeWriteWidth hpsi hwidth hle c.1 c.2
  markLeaderBirth (authBirth l r b) b


theorem doneOrdinaryMetadataFrozenV9_domain
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    (doneOrdinaryMetadataFrozenV9 hpsi hwidth hle kappa l r).1.core.inProtocolDomain kappa /\
      (doneOrdinaryMetadataFrozenV9 hpsi hwidth hle kappa l r).2.core.inProtocolDomain kappa := by
  have hc := doneThroughCheckEntryWidth_domain (κ := kappa)
    hpsi hwidth hle l r hl hr
  have hb := beforeWriteWidth_domain (κ := kappa)
    hpsi hwidth hle _ _ hc.1 hc.2
  exact markLeaderBirth_inProtocolDomain _ _ hb


/-- Same responder-delete / initiator-wait priority as TerminalHost. -/
def doneMetadataAuthorizedFrozenV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (kappa : Nat) (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  if deletionActive r0 then authorizedEliminateSig hpsi l0 r0
  else if deletionActive l0 then (l0, r0)
  else doneOrdinaryMetadataFrozenV9 hpsi hwidth hle kappa l0 r0


theorem doneMetadataAuthorizedFrozenV9_domain
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    (doneMetadataAuthorizedFrozenV9 hpsi hwidth hle kappa l r).1.core.inProtocolDomain kappa /\
      (doneMetadataAuthorizedFrozenV9 hpsi hwidth hle kappa l r).2.core.inProtocolDomain kappa := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  unfold doneMetadataAuthorizedFrozenV9
  dsimp only
  split
  · exact authorizedReconcile_inProtocolDomain (eliminateSig hpsi) l0 r0
      (eliminateSig_inProtocolDomain hpsi l0.core r0.core hl0 hr0)
  · split
    · exact ⟨hl0, hr0⟩
    · exact doneOrdinaryMetadataFrozenV9_domain
        hpsi hwidth hle l0 r0 hl0 hr0


/-- Unchanged finite reification. -/
def doneMetadataBoundedFrozenV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa × AuthorizedBoundedAgentState psi kappa :=
  let q := doneMetadataAuthorizedFrozenV9 hpsi hwidth hle kappa l.erase r.erase
  let hq := doneMetadataAuthorizedFrozenV9_domain
    hpsi hwidth hle l.erase r.erase
      l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)


/-- Unchanged disposal preparation and expiry. -/
def doneMetadataFrozenV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau :=
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let q := doneMetadataBoundedFrozenV9 hpsi hwidth hle l0.core r0.core
  (deletionPriorityExpireOne tau l0 ⟨q.1, l0.stall⟩,
    deletionPriorityExpireOne tau r0 ⟨q.2, r0.stall⟩)


/-- Unchanged current-leader normalization. -/
def metadataFrozenV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau :=
  let q := doneMetadataFrozenV9 hpsi hwidth hle l r
  (normalizeLeader hpsi q.1, normalizeLeader hpsi q.2)


/-- Unchanged final physical tail, with the original endpoints in the same two
arguments as TerminalHost.row. -/
def writerSkippingHostV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau :=
  let q := metadataFrozenV9 hpsi hwidth hle l r
  finalPhysical hpsi l r q.1 q.2


/-! ## 4. V9 controller row and XSupplier step -/


/-- Change only the physical carrier and retain the controller code point. -/
def setPhysicalKeepV9
    (u : R1AgentStateV6 psi kappa tau)
    (b : ExpiringAgentState psi kappa tau) : R1AgentStateV6 psi kappa tau :=
  { u with carrier := setPhysical u.carrier b }


private def pairCrossedOwnerV9
    (l r : R1AgentStateV6 psi kappa tau) : Bool :=
  l.carrier.splice.base.core.path0Crossed ||
    r.carrier.splice.base.core.path0Crossed


private def pairCrossedPhysicalV9
    (l r : ExpiringAgentState psi kappa tau) : Bool :=
  l.core.path0Crossed || r.core.path0Crossed


/-- ARM preempts WRITE in the same service.  If the physical tail retires the
owner immediately, create the release token instead of stranding the new gates. -/
def routeArmWriteV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  let q := writerSkippingHostV9 hpsi hwidth hle
    l.carrier.splice.base r.carrier.splice.base
  let l' := setPhysicalKeepV9 l q.1
  let r' := setPhysicalKeepV9 r q.2
  if pairCrossedPhysicalV9 q.1 q.2 = true then
    (setRouteWriterGateV9 l', setRouteWriterGateV9 r')
  else
    (setRouteWriterGateV9 l', setRouteReleaseTokenV9 r')


/-- Existing gates also execute the physical row with WRITE omitted.  A
true-to-false owner transition starts the reverse release sweep. -/
def routeFrozenWriteV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  let q := writerSkippingHostV9 hpsi hwidth hle
    l.carrier.splice.base r.carrier.splice.base
  let l' := setPhysicalKeepV9 l q.1
  let r' := setPhysicalKeepV9 r q.2
  let l'' := if RouteWriterGateShape l then setRouteWriterGateV9 l' else l'
  let r'' := if RouteWriterGateShape r then setRouteWriterGateV9 r' else r'
  if pairCrossedOwnerV9 l r = true /\
      pairCrossedPhysicalV9 q.1 q.2 = false then
    (l'', setRouteReleaseTokenV9 r')
  else
    (l'', r'')


/-- Route rows sit above V8's malformed-code cleanup.  A gate adjacent to an
active splice role fails closed here; the lifecycle invariant below must prove
that reachable executions use the explicit splice-ownership transfer instead
of remaining in this conflict shape. -/
def routeRowV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  if RouteReleaseGuardV9 l r then
    routeReleaseWriteV9 l r
  else if RouteReleaseTokenShapeV9 l then
    (l, r)
  else if RouteArmGuardV9 l r then
    routeArmWriteV9 hpsi hwidth hle l r
  else if RouteWriterFrozenPair l r then
    if RouteGateCompatibleV9 l /\ RouteGateCompatibleV9 r then
      routeFrozenWriteV9 hpsi hwidth hle l r
    else
      (l, r)
  else
    rowV8 hpsi hwidth hle l r


/-- Lineage is orthogonal in this round; V9 changes only the splice/route
coordinate. -/
def xRowV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : XSupplierAgent psi kappa tau) :
    XSupplierAgent psi kappa tau × XSupplierAgent psi kappa tau :=
  let q := routeRowV9 hpsi hwidth hle l.splice r.splice
  (⟨q.1, l.lineage⟩, ⟨q.2, r.lineage⟩)


def stepV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (S : XSupplierConfig n psi kappa tau)
    (e : Fin n) : XSupplierConfig n psi kappa tau :=
  let j := ring.rightNeighbor e
  if j = e then S
  else
    let q := xRowV9 hpsi hwidth hle (S e) (S j)
    fun i => if i = e then q.1 else if i = j then q.2 else S i


/-- Physical projection, now named at the V9 layer. -/
abbrev xPhysical
    (S : XSupplierConfig n psi kappa tau) :
    BirthPhaseCohortDesign.FC n psi kappa tau :=
  B9CheckRouteGate.xPhysical S


/-! ## 5. Exact proof-side lifecycle statements -/


/-- Every site in every *strictly crossed* current group is frozen.  This is
stronger than merely gating one boundary edge and is exactly what the
stationary writer needs. -/
def RouteGateCoverageV9
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (S : XSupplierConfig n psi kappa tau) : Prop :=
  forall e pos referenceC leader sourceSite history carrier,
    CurrentRouteWitnessAt hpsi h2 ring (xPhysical S) e pos
      referenceC leader sourceSite history carrier ->
    forall k,
      carrier.route.source < k -> k < carrier.route.target ->
      forall d, d < psi ->
        RouteWriterGateShape
          (S (groupOffset ring
            (stableGroupStart ring leader psi k) d)).splice


/-- Exact theorem statement for ARM closure.  It is kept as a Prop because
current main has not yet connected `CurrentRouteWitnessAt` to the executable
`path0Crossed` owner. -/
def RouteGateCoverageClosedV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (h2 : 2 <= psi) (ring : DirectedRing n) : Prop :=
  forall (S : XSupplierConfig n psi kappa tau) (e : Fin n),
    RouteGateCoverageV9 (kappa := kappa) (tau := tau) hpsi h2 ring S ->
      RouteGateCoverageV9 (kappa := kappa) (tau := tau) hpsi h2 ring
        (stepV9 (kappa := kappa) (tau := tau)
          hpsi hwidth hle ring S e)


/-- A released physical site is crossed by no surviving route. -/
def ReleasedSiteSafeV9
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (S : XSupplierConfig n psi kappa tau) (i : Fin n) : Prop :=
  forall e pos referenceC leader sourceSite history carrier,
    CurrentRouteWitnessAt hpsi h2 ring (xPhysical S) e pos
      referenceC leader sourceSite history carrier ->
    forall k,
      carrier.route.source < k -> k < carrier.route.target ->
      forall d, d < psi ->
        i != groupOffset ring (stableGroupStart ring leader psi k) d


/-- Exact theorem statement for RELEASE.  This is where overlap/reference-count
soundness lives: whenever a gate disappears, no successor route may still own
that site. -/
def RouteReleaseSoundV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (h2 : 2 <= psi) (ring : DirectedRing n) : Prop :=
  forall (S : XSupplierConfig n psi kappa tau) (e i : Fin n),
    RouteWriterGateShape (S i).splice ->
    (¬ RouteWriterGateShape
      ((stepV9 (kappa := kappa) (tau := tau)
        hpsi hwidth hle ring S e) i).splice) ->
    ReleasedSiteSafeV9 (kappa := kappa) (tau := tau) hpsi h2 ring
      (stepV9 (kappa := kappa) (tau := tau)
        hpsi hwidth hle ring S e) i


/-- Successor-route dichotomy needed by the crossed-ID proof.


Fresh routes already satisfy the successor bound.  A transported route supplies
an old witness with the same source/target/payload and an exact physical frame
on every group strictly inside that route.  The route gate is intended to prove
that last equality. -/
def RouteTransportOrFreshV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (h2 : 2 <= psi) (ring : DirectedRing n) : Prop :=
  forall (S : XSupplierConfig n psi kappa tau) (edge : Fin n),
    let T := stepV9 hpsi hwidth hle ring S edge
    forall e pos referenceC leader sourceSite history
      (carrier : EqualPrefixCarrier ring
        (currentCheckOutputRawConfig hpsi h2 ring (xPhysical T) e)
        referenceC leader),
      CurrentRouteWitnessAt hpsi h2 ring (xPhysical T) e pos
        referenceC leader sourceSite history carrier ->
      ((forall k,
          carrier.route.source < k -> k < carrier.route.target ->
          groupID ring.hn
              (fun i => BirthPhaseCohortDesign.rawAt (xPhysical T) i)
              (stableGroupStart ring leader psi k) <=
            carrier.route.payload) \/
       (exists (e0 pos0 : Fin n)
          (reference0 : Fin n -> AgentState psi)
          (source0 : Fin n) (history0 : LocalComparisonHistory n)
          (carrier0 : EqualPrefixCarrier ring
            (currentCheckOutputRawConfig hpsi h2 ring (xPhysical S) e0)
            reference0 leader),
          CurrentRouteWitnessAt hpsi h2 ring (xPhysical S) e0 pos0
              reference0 leader source0 history0 carrier0 /\
          carrier0.route.source = carrier.route.source /\
          carrier0.route.target = carrier.route.target /\
          carrier0.route.payload = carrier.route.payload /\
          forall k,
            carrier.route.source < k -> k < carrier.route.target ->
            groupID ring.hn
                (fun i => BirthPhaseCohortDesign.rawAt (xPhysical T) i)
                (stableGroupStart ring leader psi k) =
              groupID ring.hn
                (fun i => BirthPhaseCohortDesign.rawAt (xPhysical S) i)
                (stableGroupStart ring leader psi k)))


/-- The crossed-ID target, now over the executable V9 step. -/
def CrossedIDRewriteV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (h2 : 2 <= psi) (ring : DirectedRing n) : Prop :=
  CrossedIDRewriteForXSupplierStep
    (kappa := kappa) (tau := tau) hpsi h2 ring
    (stepV9 (kappa := kappa) (tau := tau) hpsi hwidth hle ring)


/-- Once the route dichotomy is proved, the old crossed-ID bound transports
mechanically.  No PeakSafe argument is repeated here. -/
theorem crossedIDRewriteV9_of_routeTransportOrFresh
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (h2 : 2 <= psi) (ring : DirectedRing n)
    (hroute : RouteTransportOrFreshV9
      (kappa := kappa) (tau := tau) hpsi hwidth hle h2 ring) :
    CrossedIDRewriteV9
      (kappa := kappa) (tau := tau) hpsi hwidth hle h2 ring := by
  unfold CrossedIDRewriteV9 CrossedIDRewriteForXSupplierStep
  intro S edge hold
  unfold crossed_id_survival_bound at hold |-
  intro e pos referenceC leader sourceSite history carrier hw
  intro k hsk hkt
  have hr := hroute S edge e pos referenceC leader sourceSite history carrier hw
  rcases hr with hfresh | htransport
  · exact hfresh k hsk hkt
  · rcases htransport with
      ⟨e0, pos0, reference0, source0, history0, carrier0,
        hw0, hs, ht, hp, hframe⟩
    have hsk0 : carrier0.route.source < k := by
      rw [hs]
      exact hsk
    have hkt0 : k < carrier0.route.target := by
      rw [ht]
      exact hkt
    calc
      groupID ring.hn
          (fun i => BirthPhaseCohortDesign.rawAt
            (xPhysical (stepV9 hpsi hwidth hle ring S edge)) i)
          (stableGroupStart ring leader psi k) =
        groupID ring.hn
          (fun i => BirthPhaseCohortDesign.rawAt (xPhysical S) i)
          (stableGroupStart ring leader psi k) :=
        hframe k hsk hkt
      _ <= carrier0.route.payload :=
        hold e0 pos0 reference0 leader source0 history0 carrier0
          hw0 k hsk0 hkt0
      _ = carrier.route.payload := hp


/-- Off every route-only guard the V9 row is the V8 row: the four route
branches of `routeRowV9` are skipped in order. -/
private theorem routeRowV9_eq_rowV8_of_off
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hrel : ¬ RouteReleaseTokenShapeV9 r)
    (htok : ¬ RouteReleaseTokenShapeV9 l)
    (harm : ¬ RouteArmGuardV9 l r)
    (hfrozen : ¬ RouteWriterFrozenPair l r) :
    routeRowV9 hpsi hwidth hle l r = rowV8 hpsi hwidth hle l r := by
  unfold routeRowV9
  rw [if_neg (show ¬ RouteReleaseGuardV9 l r from hrel), if_neg htok,
    if_neg harm, if_neg hfrozen]


/-! ## 6. Closed finite fixtures -/


private theorem hTwo : 0 < 2 := by decide
private theorem hTwoLe : 2 <= 2 := by decide


/-- Reuse a literal V7/V8 neutral cell and explicitly clear its old controller. -/
private def neutralFixtureV9 : R1AgentStateV6 2 1 1 :=
  clearControlV6 (q11703StartV7 (0 : Fin 3))


/-- Fixture-only setter for the already-existing authorization owner bit. -/
private def setOwnerBitFixtureV9
    (u : R1AgentStateV6 2 1 1) (b : Bool) : R1AgentStateV6 2 1 1 :=
  { u with
    carrier :=
      { u.carrier with
        splice :=
          { u.carrier.splice with
            base :=
              { u.carrier.splice.base with
                core := { u.carrier.splice.base.core with path0Crossed := b } } } } }


private def ownerFixtureV9 : R1AgentStateV6 2 1 1 :=
  setOwnerBitFixtureV9 neutralFixtureV9 true


private def offFixtureV9 : R1AgentStateV6 2 1 1 :=
  setOwnerBitFixtureV9 neutralFixtureV9 false


private def gateFixtureV9 : R1AgentStateV6 2 1 1 :=
  setRouteWriterGateV9 offFixtureV9


private def releaseFixtureV9 : R1AgentStateV6 2 1 1 :=
  setRouteReleaseTokenV9 offFixtureV9


/-- ARM decoding is genuinely closed and finite. -/
theorem route_arm_guard_fixture_v9 :
    RouteArmGuardV9 ownerFixtureV9 offFixtureV9 := by
  decide


/-- RELEASE moves the token left across exactly one gate and clears its old
site. -/
theorem route_release_fixture_v9 :
    let q := routeReleaseWriteV9 gateFixtureV9 releaseFixtureV9
    RouteReleaseTokenShapeV9 q.1 /\ RouteNeutralV9 q.2 := by
  decide


/-- With no gate, no release token and no crossed owner, the new table is
byte-for-byte V8. -/
theorem off_gate_v8_fixture_v9 :
    routeRowV9 hTwo hTwo hTwoLe offFixtureV9 offFixtureV9 =
      rowV8 hTwo hTwo hTwoLe offFixtureV9 offFixtureV9 := by
  have hpend : offFixtureV9.carrier.repairPending = false := rfl
  have hown : offFixtureV9.carrier.splice.base.core.path0Crossed = false := rfl
  have hgate : ¬ RouteWriterGateShape offFixtureV9 := fun h =>
    Bool.false_ne_true (hpend.symm.trans h.2.1)
  exact routeRowV9_eq_rowV8_of_off hTwo hTwo hTwoLe offFixtureV9 offFixtureV9
    (fun h => Bool.false_ne_true (hpend.symm.trans h.2.1))
    (fun h => Bool.false_ne_true (hpend.symm.trans h.2.1))
    (fun h => Bool.false_ne_true (hown.symm.trans h.2.2))
    (fun h => h.elim hgate hgate)


end B9CheckRouteLifecycle


#print axioms B9CheckRouteLifecycle.setRouteWriterGateV9_shape
#print axioms B9CheckRouteLifecycle.setRouteReleaseTokenV9_shape
#print axioms B9CheckRouteLifecycle.release_token_disjoint_route_gate
#print axioms B9CheckRouteLifecycle.routeLifecycleStateFactorV9_eq
#print axioms B9CheckRouteLifecycle.doneOrdinaryMetadataFrozenV9_domain
#print axioms B9CheckRouteLifecycle.doneMetadataAuthorizedFrozenV9_domain
#print axioms B9CheckRouteLifecycle.crossedIDRewriteV9_of_routeTransportOrFresh
#print axioms B9CheckRouteLifecycle.route_arm_guard_fixture_v9
#print axioms B9CheckRouteLifecycle.route_release_fixture_v9
#print axioms B9CheckRouteLifecycle.off_gate_v8_fixture_v9
