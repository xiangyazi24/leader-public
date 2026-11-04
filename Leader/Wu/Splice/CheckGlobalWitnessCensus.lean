import Leader.Wu.Splice.CheckWholeStep


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9CheckGlobalWitnessCensus


open PPLL PPLLRepair PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLComparisonHistory
open BirthPhaseCohortDesign
open B9CheckStructuralCensus


variable {n psi kappa tau : Nat}


/-- The literal current width-two physical step used by the B9 certificate. -/
def wholePhysicalStep
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (e : Fin n) : BirthPhaseCohortDesign.FC n psi kappa tau :=
  BirthShortDoneTerminalConsumer.step
    hpsi (by decide : 0 < 2) h2 ring C e


/-- NEEDS X for `leader_delimited_peak_safe`.
The stationary writer can rewrite group bits and `finalPhysical` can merge
leader-delimited segments.  The staged splice/deletion transaction must certify
the rewritten/split/merged successor before commit. -/
def PeakSafeRewriteAndBoundaryX
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  forall (C : BirthPhaseCohortDesign.FC n psi kappa tau) (e : Fin n),
    leader_delimited_peak_safe hpsi ring C ->
    leader_delimited_peak_safe hpsi ring
      (wholePhysicalStep hpsi h2 ring C e)


/-- The successor DONE cuts required by the first half of
`comparison_route_certified`.  This is the part naturally supplied by the
constant-state guarded lineage lease. -/
def SuccessorDoneCutsCertified
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) : Prop :=
  forall e : Fin n,
    let d := currentDoneIntermediateAt hpsi h2 ring C e
    exists hL hR : LocalComparisonHistory n,
      FullLocalHistoryTrusted d.1.core hL /\
      FullLocalHistoryTrusted d.2.core hR /\
      CurrentDoneMoveCompatible hpsi
        ({ concrete := d.1.core, history := hL } : MarkedAgentState n psi)
        ({ concrete := d.2.core, history := hR } : MarkedAgentState n psi)


/-- The successor equal-prefix route witnesses required by the second half of
`comparison_route_certified`.  They must be reattached to the current physical
segment after writer/boundary changes, or dropped when the carrier is cleared. -/
def SuccessorEqualRoutesCertified
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) : Prop :=
  forall e : Fin n,
    let q := currentCheckOutputAt hpsi h2 ring C e
    (q.1.core.state = .equal ->
      CurrentEqualPrefixLineageAt hpsi h2 ring C e e) /\
    (q.2.core.state = .equal ->
      CurrentEqualPrefixLineageAt hpsi h2 ring C e
        (ring.rightNeighbor e))


/-- NEEDS X for `comparison_route_certified`.
The lease supplies the DONE-cut half; the route/quarantine transaction must
supply the current equal-prefix witnesses after physical rewrites. -/
def ComparisonRouteRefreshX
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  forall (C : BirthPhaseCohortDesign.FC n psi kappa tau) (e : Fin n),
    comparison_route_certified hpsi h2 ring C ->
    let D := wholePhysicalStep hpsi h2 ring C e
    SuccessorDoneCutsCertified hpsi h2 ring D /\
      SuccessorEqualRoutesCertified hpsi h2 ring D


/-- The split above is definitionally the existing route certificate. -/
theorem comparison_route_certified_iff_components
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) :
    comparison_route_certified hpsi h2 ring C <->
      SuccessorDoneCutsCertified hpsi h2 ring C /\
        SuccessorEqualRoutesCertified hpsi h2 ring C := by
  rfl


/-- NEEDS X for `crossed_id_survival_bound`.
The stationary writer must freeze a live crossed group or certify that its
rewritten physical ID remains below the route payload. -/
def CrossedIDRewriteX
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  forall (C : BirthPhaseCohortDesign.FC n psi kappa tau) (e : Fin n),
    crossed_id_survival_bound hpsi h2 ring C ->
    crossed_id_survival_bound hpsi h2 ring
      (wholePhysicalStep hpsi h2 ring C e)


/-- YES for `leader_boundary_clearing`.
The only physical hazard is a leader-set change in `finalPhysical`; the next
current CHECK input reruns the leader/reset walls, so no extra state is needed. -/
def LeaderBoundaryClearingPreservationStatement
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  forall (C : BirthPhaseCohortDesign.FC n psi kappa tau) (e : Fin n),
    leader_boundary_clearing hpsi h2 ring C ->
    leader_boundary_clearing hpsi h2 ring
      (wholePhysicalStep hpsi h2 ring C e)


end B9CheckGlobalWitnessCensus


#print axioms B9CheckGlobalWitnessCensus.comparison_route_certified_iff_components
#print axioms B9CheckGlobalWitnessCensus.PeakSafeRewriteAndBoundaryX
#print axioms B9CheckGlobalWitnessCensus.ComparisonRouteRefreshX
#print axioms B9CheckGlobalWitnessCensus.CrossedIDRewriteX
#print axioms B9CheckGlobalWitnessCensus.LeaderBoundaryClearingPreservationStatement
