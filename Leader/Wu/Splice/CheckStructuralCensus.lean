import Leader.Wu.Birth.FirstBirthCohort
import Leader.Wu.ShortGap.SegmentPeakMerge
import Leader.Wu.Safety.SignalCoherence
import Leader.Wu.Comparison.HistoryDoneMove
import Leader.Wu.Comparison.HistoryEntryResetSanitize
import Leader.Wu.Comparison.HistoryLateLifts

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9CheckStructuralCensus

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
  BirthShortDoneTerminalEntryCut
open BirthPhaseCohortDesign
open PPLLComparisonHistory

variable {n psi kappa tau : Nat}

/-! ## Exact current cuts used by CheckBlockedAt -/

/-- The prepared/normalized pair occurring literally at the front of
`BirthPhaseCohortDesign.CheckBlockedAt`. -/
def preparedPairAt
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) (e : Fin n) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let pl := prepareExpiringDisposal hpsi (C e)
  let pr := prepareExpiringDisposal hpsi (C (ring.rightNeighbor e))
  (normalizeDeletion pl.core.erase, normalizeDeletion pr.core.erase)

/-- The exact input to the current DONE movement stage on one edge. -/
def currentDoneIntermediateAt
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) (e : Fin n) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let p := preparedPairAt hpsi ring C e
  generationBeforeMoveEntryWidth
    hpsi (by decide : 0 < 2) h2 kappa p.1 p.2

/-- The literal current pre-CHECK pair used by `CheckBlockedAt`. -/
def currentCheckInputAt
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) (e : Fin n) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let p := preparedPairAt hpsi ring C e
  doneBeforeCheckEntryWidth
    hpsi (by decide : 0 < 2) h2 kappa p.1 p.2

/-- The raw Algorithm-11 output from the exact current pre-CHECK pair.
The guarded wrapper can only make this stage an identity; a positive
`ActualCheckBirth` is necessarily on this raw branch. -/
def currentCheckOutputAt
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) (e : Fin n) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let b := currentCheckInputAt hpsi h2 ring C e
  authorizedCheckSig hpsi b.1 b.2

/-- Whole raw configuration at that proof-side CHECK output cut.  The first
endpoint has the same priority as `PopulationProtocol.step` on an alias edge. -/
def currentCheckOutputRawConfig
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) (e : Fin n) :
    Fin n → AgentState psi :=
  let q := currentCheckOutputAt hpsi h2 ring C e
  fun i =>
    if i = e then q.1.core
    else if i = ring.rightNeighbor e then q.2.core
    else BirthPhaseCohortDesign.rawAt C i

/-! ## 1. Leader-delimited PeakSafe physical geometry -/

/-- IDs of the complete positive groups strictly after `leader` and before the
next certified leader boundary.  Entry `j` is group `j+1`. -/
def leaderSegmentWord
    (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (leader : Fin n) (groups : Nat) : List Nat :=
  (List.range groups).map (fun j =>
    groupID ring.hn
      (fun i => BirthPhaseCohortDesign.rawAt C i)
      (groupOffset ring leader ((j + 1) * psi)))

/-- Physical meaning of a non-wrapping leader-delimited complete-group
segment.  There is no intervening leader, and the segment is actually rooted
at modulo-`psi` group boundaries. -/
def LeaderDelimitedSegmentAt
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (leader : Fin n) (groups : Nat) : Prop :=
  let endpoint := groupOffset ring leader ((groups + 1) * psi)
  (BirthPhaseCohortDesign.rawAt C leader).leader = true ∧
    (BirthPhaseCohortDesign.rawAt C leader).label = ⟨0, hpsi⟩ ∧
    (groups + 1) * psi < n ∧
    (BirthPhaseCohortDesign.rawAt C endpoint).leader = true ∧
    (BirthPhaseCohortDesign.rawAt C endpoint).label = ⟨0, hpsi⟩ ∧
    (∀ d, 0 < d → d < (groups + 1) * psi →
      (BirthPhaseCohortDesign.rawAt C
        (groupOffset ring leader d)).leader = false) ∧
    (∀ d, d < (groups + 1) * psi →
      (BirthPhaseCohortDesign.rawAt C
        (groupOffset ring leader d)).label =
        ⟨d % psi, Nat.mod_lt d hpsi⟩)

/-- Every current leader has a physical next-leader segment, and every such
segment carries the constructive certificate used by `SegmentPeakWord.merge`.
`SegmentPeakWord.repeat_peak_safe` yields the spec's pairwise PeakSafe law. -/
def leader_delimited_peak_safe
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) : Prop :=
  (∀ leader,
      (BirthPhaseCohortDesign.rawAt C leader).leader = true →
        ∃ groups, LeaderDelimitedSegmentAt hpsi ring C leader groups) ∧
    ∀ leader groups,
      LeaderDelimitedSegmentAt hpsi ring C leader groups →
        SegmentPeakWord (leaderSegmentWord ring C leader groups)

theorem leader_segment_repeat_peak_safe
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (h : leader_delimited_peak_safe hpsi ring C)
    (leader : Fin n) (groups : Nat)
    (hseg : LeaderDelimitedSegmentAt hpsi ring C leader groups) :
    SegmentPeakWord.RepeatPeakSafe
      (leaderSegmentWord ring C leader groups) :=
  SegmentPeakWord.repeat_peak_safe (h.2 leader groups hseg)

/-! ## 2. Authenticated current CHECK lineage -/

/-- The frozen/reference route agrees with the actual current physical segment
at the two IDs whose equality would matter to terminal CHECK.  Interior groups
are deliberately left to `crossed_id_survival_bound`. -/
def RouteEndpointsAgree
    (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (referenceC : Fin n → AgentState psi) (leader : Fin n)
    (route : StableSignalRoute ring referenceC leader) : Prop :=
  groupID ring.hn referenceC
      (stableGroupStart ring leader psi route.source) =
    groupID ring.hn
      (fun i => BirthPhaseCohortDesign.rawAt C i)
      (stableGroupStart ring leader psi route.source) ∧
  groupID ring.hn referenceC
      (stableGroupStart ring leader psi route.target) =
    groupID ring.hn
      (fun i => BirthPhaseCohortDesign.rawAt C i)
      (stableGroupStart ring leader psi route.target)

/-- One equal CHECK endpoint has a trusted current source mark and a concrete
`EqualPrefixCarrier` rooted at the corresponding source group. -/
def CurrentRouteWitnessAt
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (e pos : Fin n)
    (referenceC : Fin n → AgentState psi) (leader sourceSite : Fin n)
    (history : LocalComparisonHistory n)
    (carrier : EqualPrefixCarrier ring
      (currentCheckOutputRawConfig hpsi h2 ring C e)
      referenceC leader) : Prop :=
  FullLocalHistoryTrusted
      (currentCheckOutputRawConfig hpsi h2 ring C e pos) history ∧
    history.state = .trusted sourceSite ∧
    carrier.route.source = containingGroupIndex leader sourceSite psi ∧
    carrier.route.source < carrier.route.target ∧
    carrier.upto =
      (currentCheckOutputRawConfig hpsi h2 ring C e pos).label.val ∧
    pos = groupOffset ring
      (stableGroupStart ring leader psi carrier.route.target) carrier.upto ∧
    ∃ groups,
      LeaderDelimitedSegmentAt hpsi ring C leader groups ∧
      carrier.route.target ≤ groups ∧
      RouteEndpointsAgree ring C referenceC leader carrier.route

/-- Existential packaging used by the global route predicate. -/
def CurrentEqualPrefixLineageAt
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (e pos : Fin n) : Prop :=
  ∃ (referenceC : Fin n → AgentState psi) (leader sourceSite : Fin n)
      (history : LocalComparisonHistory n)
      (carrier : EqualPrefixCarrier ring
        (currentCheckOutputRawConfig hpsi h2 ring C e)
        referenceC leader),
    CurrentRouteWitnessAt hpsi h2 ring C e pos
      referenceC leader sourceSite history carrier

/-- Current-host comparison certification.  Its first conjunct is exactly the
anti-splice requirement at every actual DONE input; its second conjunct
requires every touched equal CHECK output to possess authenticated equal-prefix
ancestry on the current leader segment. -/
def comparison_route_certified
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) : Prop :=
  (∀ e : Fin n,
      let d := currentDoneIntermediateAt hpsi h2 ring C e
      ∃ hL hR : LocalComparisonHistory n,
        FullLocalHistoryTrusted d.1.core hL ∧
        FullLocalHistoryTrusted d.2.core hR ∧
        CurrentDoneMoveCompatible hpsi
          ({ concrete := d.1.core, history := hL } : MarkedAgentState n psi)
          ({ concrete := d.2.core, history := hR } : MarkedAgentState n psi)) ∧
    ∀ e : Fin n,
      let q := currentCheckOutputAt hpsi h2 ring C e
      (q.1.core.state = .equal →
        CurrentEqualPrefixLineageAt hpsi h2 ring C e e) ∧
      (q.2.core.state = .equal →
        CurrentEqualPrefixLineageAt hpsi h2 ring C e
          (ring.rightNeighbor e))

/-- The requested DONE consequence is literally a projection of
`comparison_route_certified`. -/
theorem comparison_route_certified_done_compatible
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (h : comparison_route_certified hpsi h2 ring C)
    (e : Fin n) :
    let d := currentDoneIntermediateAt hpsi h2 ring C e
    ∃ hL hR : LocalComparisonHistory n,
      FullLocalHistoryTrusted d.1.core hL ∧
      FullLocalHistoryTrusted d.2.core hR ∧
      CurrentDoneMoveCompatible hpsi
        ({ concrete := d.1.core, history := hL } : MarkedAgentState n psi)
        ({ concrete := d.2.core, history := hR } : MarkedAgentState n psi) := by
  exact h.1 e

/-! ## 3. Physical crossed-ID survival -/

/-- Every genuinely crossed *current physical* group has ID at most the source
payload.  `StableSignalRoute.survived_crossing` supplies the analogous fact on
`referenceC`; this predicate is the missing bridge back to the live `FC`. -/
def crossed_id_survival_bound
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) : Prop :=
  ∀ (e pos : Fin n) (referenceC : Fin n → AgentState psi)
      (leader sourceSite : Fin n) (history : LocalComparisonHistory n)
      (carrier : EqualPrefixCarrier ring
        (currentCheckOutputRawConfig hpsi h2 ring C e)
        referenceC leader),
    CurrentRouteWitnessAt hpsi h2 ring C e pos
        referenceC leader sourceSite history carrier →
      ∀ k,
        carrier.route.source < k →
        k < carrier.route.target →
        groupID ring.hn
            (fun i => BirthPhaseCohortDesign.rawAt C i)
            (stableGroupStart ring leader psi k) ≤
          carrier.route.payload

/-! ## Separate local boundary-clearing hypothesis for the structural theorem -/

/-- An edge incident to a prepared leader reaches CHECK with no live comparison
carrier on either endpoint. -/
def leader_boundary_clearing
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) : Prop :=
  ∀ e : Fin n,
    let p := preparedPairAt hpsi ring C e
    let b := currentCheckInputAt hpsi h2 ring C e
    (p.1.core.leader = true ∨ p.2.core.leader = true) →
      ComparisonNeutral b.1.core ∧ ComparisonNeutral b.2.core

#print axioms B9CheckStructuralCensus.leader_segment_repeat_peak_safe
#print axioms B9CheckStructuralCensus.comparison_route_certified_done_compatible

end B9CheckStructuralCensus
