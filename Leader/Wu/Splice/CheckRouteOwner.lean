import Leader.Wu.Splice.CheckRouteLifecycle

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9CheckRouteOwner

open PPLL PPLLRepair PPLLResearchFormulation
open BirthPhaseCohortDesign
open PPLLComparisonHistory
open B9CheckStructuralCensus
open B9CheckXSupplierDesign B9CheckRouteGate B9CheckRouteLifecycle

variable {n psi width kappa tau : Nat}

/-! ## 1. Literal overlap: route ownership is not unique -/

private theorem hTwo : 0 < 2 := by decide
private theorem hEleven : 0 < 11 := by decide
private def ring11 : DirectedRing 11 := ⟨hEleven⟩

/-- Two leaders at 0 and 10, alternating labels, zero group bits.  The starts
of target groups 3 and 4 (sites 6 and 8) carry live equal-prefix components. -/
private def overlapReference (i : Fin 11) : AgentState 2 :=
  let u : AgentState 2 :=
    { BirthShortDoneTerminalPositiveWitness.raw false with
      leader := if i = (0 : Fin 11) ∨ i = (10 : Fin 11) then true else false
      label := ⟨i.val % 2, Nat.mod_lt _ hTwo⟩ }
  if i = (6 : Fin 11) ∨ i = (8 : Fin 11) then
    { u with state := .equal, path := .some 0 0 }
  else u

/-- Literal leader/label geometry matching the non-wrapping B9 segment shape. -/
theorem overlap_reference_geometry :
    (overlapReference (0 : Fin 11)).leader = true ∧
    (overlapReference (10 : Fin 11)).leader = true ∧
    (∀ i : Fin 11, 0 < i.val → i.val < 10 →
      (overlapReference i).leader = false) ∧
    (∀ i : Fin 11, i.val < 10 →
      (overlapReference i).label.val = i.val % 2) := by
  decide

private def route13 :
    StableSignalRoute ring11 overlapReference (0 : Fin 11) where
  source := 1
  target := 3
  payload := 0
  source_pos := by decide
  travels_forward := by decide
  target_in_range := by decide
  payload_from_source := by decide
  survived_crossing := by
    intro k hsk hkt
    have hk : k = 2 := by omega
    subst k
    decide

private def route14 :
    StableSignalRoute ring11 overlapReference (0 : Fin 11) where
  source := 1
  target := 4
  payload := 0
  source_pos := by decide
  travels_forward := by decide
  target_in_range := by decide
  payload_from_source := by decide
  survived_crossing := by
    intro k hsk hkt
    have hk : k = 2 ∨ k = 3 := by omega
    rcases hk with hk | hk
    · subst k; decide
    · subst k; decide

private def carrier13 :
    EqualPrefixCarrier ring11 overlapReference overlapReference
      (0 : Fin 11) :=
  EqualPrefixCarrier.zero hTwo route13
    (by
      refine ⟨0, 0, ?_, rfl, ?_⟩
      · decide
      · decide)
    (by
      refine ⟨0, 0, ?_, rfl, ?_⟩
      · decide
      · decide)
    (by decide)

private def carrier14 :
    EqualPrefixCarrier ring11 overlapReference overlapReference
      (0 : Fin 11) :=
  EqualPrefixCarrier.zero hTwo route14
    (by
      refine ⟨0, 0, ?_, rfl, ?_⟩
      · decide
      · decide)
    (by
      refine ⟨0, 0, ?_, rfl, ?_⟩
      · decide
      · decide)
    (by decide)

/-- Two distinct live equal-prefix routes cross the same physical group 2. -/
theorem overlapping_live_route_fixture :
    carrier13.route.target ≠ carrier14.route.target ∧
    carrier13.route.source < 2 ∧ 2 < carrier13.route.target ∧
    carrier14.route.source < 2 ∧ 2 < carrier14.route.target ∧
    carrier13.upto = 0 ∧ carrier14.upto = 0 := by
  decide

/-! ## 2. The fresh/adjacent branch is vacuous -/

/-- A route that has advanced by at most one group has no strictly crossed
interior group.  Hence it satisfies exactly the first disjunct used by
`RouteTransportOrFreshV9`, independently of the physical row. -/
theorem adjacent_route_crossed_bound
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (e : Fin n) (referenceC : Fin n -> AgentState psi)
    (leader : Fin n)
    (carrier : EqualPrefixCarrier ring
      (currentCheckOutputRawConfig hpsi h2 ring C e)
      referenceC leader)
    (hadj : carrier.route.target <= carrier.route.source + 1) :
    forall k,
      carrier.route.source < k -> k < carrier.route.target ->
      groupID ring.hn
          (fun i => BirthPhaseCohortDesign.rawAt C i)
          (stableGroupStart ring leader psi k) <=
        carrier.route.payload := by
  intro k hsk hkt
  omega

/-! ## 3. Exact remaining transport theorem -/

/-- Every non-fresh successor route must be an old route with the same key,
and `stepV9` must frame every group strictly inside that route.  This is the
remaining semantic bridge from the executable `path0Crossed` owner to the
proof-side `CurrentRouteWitnessAt`; no reference-count assumption is hidden. -/
def SurvivingRouteTransportV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (h2 : 2 <= psi) (ring : DirectedRing n) : Prop :=
  forall (S : XSupplierConfig n psi kappa tau) (edge : Fin n),
    let T := stepV9 hpsi hwidth hle ring S edge
    forall e pos referenceC leader sourceSite history
      (carrier : EqualPrefixCarrier ring
        (currentCheckOutputRawConfig hpsi h2 ring (B9CheckRouteLifecycle.xPhysical T) e)
        referenceC leader),
      CurrentRouteWitnessAt hpsi h2 ring (B9CheckRouteLifecycle.xPhysical T) e pos
        referenceC leader sourceSite history carrier ->
      carrier.route.source + 1 < carrier.route.target ->
      exists (e0 pos0 : Fin n)
        (reference0 : Fin n -> AgentState psi)
        (source0 : Fin n) (history0 : LocalComparisonHistory n)
        (carrier0 : EqualPrefixCarrier ring
          (currentCheckOutputRawConfig hpsi h2 ring (B9CheckRouteLifecycle.xPhysical S) e0)
          reference0 leader),
        CurrentRouteWitnessAt hpsi h2 ring (B9CheckRouteLifecycle.xPhysical S) e0 pos0
            reference0 leader source0 history0 carrier0 /\
        carrier0.route.source = carrier.route.source /\
        carrier0.route.target = carrier.route.target /\
        carrier0.route.payload = carrier.route.payload /\
        forall k,
          carrier.route.source < k -> k < carrier.route.target ->
          groupID ring.hn
              (fun i => BirthPhaseCohortDesign.rawAt (B9CheckRouteLifecycle.xPhysical T) i)
              (stableGroupStart ring leader psi k) =
            groupID ring.hn
              (fun i => BirthPhaseCohortDesign.rawAt (B9CheckRouteLifecycle.xPhysical S) i)
              (stableGroupStart ring leader psi k)

/-- Thus `RouteTransportOrFreshV9` is reduced to exactly the surviving-route
transport theorem above; the genuinely fresh adjacent case is already closed. -/
theorem routeTransportOrFreshV9_of_survivingRouteTransport
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (h2 : 2 <= psi) (ring : DirectedRing n)
    (htransport : SurvivingRouteTransportV9
      (kappa := kappa) (tau := tau) hpsi hwidth hle h2 ring) :
    RouteTransportOrFreshV9
      (kappa := kappa) (tau := tau) hpsi hwidth hle h2 ring := by
  unfold RouteTransportOrFreshV9
  unfold SurvivingRouteTransportV9 at htransport
  intro S edge
  dsimp only
  intro e pos referenceC leader sourceSite history carrier hw
  by_cases hadj : carrier.route.target <= carrier.route.source + 1
  · exact Or.inl
      (adjacent_route_crossed_bound
        (kappa := kappa) (tau := tau)
        hpsi h2 ring
        (B9CheckRouteLifecycle.xPhysical
          (stepV9 (kappa := kappa) (tau := tau)
            hpsi hwidth hle ring S edge))
        e referenceC leader carrier hadj)
  · have hlong : carrier.route.source + 1 < carrier.route.target := by
      omega
    exact Or.inr
      (htransport S edge e pos referenceC leader sourceSite
        history carrier hw hlong)

end B9CheckRouteOwner

#print axioms B9CheckRouteOwner.overlap_reference_geometry
#print axioms B9CheckRouteOwner.overlapping_live_route_fixture
#print axioms B9CheckRouteOwner.adjacent_route_crossed_bound
#print axioms B9CheckRouteOwner.routeTransportOrFreshV9_of_survivingRouteTransport
