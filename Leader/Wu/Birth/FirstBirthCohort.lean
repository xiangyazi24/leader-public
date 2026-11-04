import Leader.Wu.Birth.ShortDoneTerminalCheckInputSources
import Leader.Wu.Birth.ShortDoneTerminalFirstHit
import Leader.Wu.Birth.ShortDoneTerminalFixedSite
import Leader.Wu.Birth.DisposalRouteInvariant
import Leader.Wu.Birth.ReleaseTerminalInvariant
import Leader.Wu.Comparison.HistoryCompare
import Leader.Wu.Birth.ShortDoneTerminalCheckInputNonvacuity
import Leader.Wu.Birth.ShortDoneTerminalCheckInputProducerWitness


namespace BirthPhaseCohortDesign


open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLPathStallComparisonRepair
  PPLLComparisonHistory LDSinkBoundedKernel
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalEntryCut
  BirthShortDoneTerminalBirthSources
  BirthShortDoneTerminalCheckInputSources
  BirthDisposalRouteInvariant BirthReleaseTerminalInvariant


set_option autoImplicit false


variable {n psi kappa tau : Nat}


abbrev FC (n psi kappa tau : Nat) :=
  Fin n -> ExpiringAgentState psi kappa tau



def rawAt (C : FC n psi kappa tau) (i : Fin n) : AgentState psi :=
  (C i).core.core.erase


/-- The exact first-birth predicate used by the current first-hit theorem.
`FirstBirthAt` is not a declaration on main. -/
def FirstBirthAt
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (pre : List (Fin n)) (e : Fin n) : Prop :=
  BirthShortDoneTerminalObserver.NoBirthAlong
      hpsi (by decide : 0 < 2) h2 ring C pre /\
    (let D := run
        (BirthShortDoneTerminalConsumer.step
          hpsi (by decide : 0 < 2) h2 ring) C pre
     BirthShortDoneTerminalObserver.birthEvent
        hpsi (by decide : 0 < 2) h2
        (D e) (D (ring.rightNeighbor e)) = true)


/-- Exact prepared P-prime source exclusion used by
`birthEvent_false_of_no_input_sources`. -/
def PPrimeBlockedAt
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e : Fin n) : Prop :=
  let l := C e
  let r := C (ring.rightNeighbor e)
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let l0 := normalizeDeletion pl.core.erase
  let r0 := normalizeDeletion pr.core.erase
  ¬ PPrimeBarrierBirthGuard hpsi l0 r0


/-- Exact current CHECK-source exclusion used by
`birthEvent_false_of_no_input_sources`. -/
def CheckBlockedAt
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e : Fin n) : Prop :=
  let l := C e
  let r := C (ring.rightNeighbor e)
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let l0 := normalizeDeletion pl.core.erase
  let r0 := normalizeDeletion pr.core.erase
  let b := doneBeforeCheckEntryWidth
    hpsi (by decide : 0 < 2) h2 kappa l0 r0
  ¬ ActualCheckBirthInput hpsi b


/-- A site is causally classified when its complete comparison history is
trusted, or its currently prepared physical carrier is already disposal-due.
This permits arbitrary/tainted history only on the explicit disposal side. -/
def CohortClassifiedAt
    (hpsi : 0 < psi) (u : ExpiringAgentState psi kappa tau)
    (H : LocalComparisonHistory n) : Prop :=
  FullLocalHistoryTrusted u.core.core.erase H \/
    DisposalDue hpsi
      (normalizeDeletion (prepareExpiringDisposal hpsi u).core.erase)


/-- Physical comparison material that zero-budget `pathExpireOne` can erase.
Probe is deliberately not included: P-prime is handled by `PPrimeBlockedAt`. -/
def ComparisonLive (u : AgentState psi) : Prop :=
  u.state ≠ .none \/ u.path ≠ .bot \/ u.path2 ≠ none \/
    u.p_carry = true


/-- B9-ready theorem-side certificate.

The two `*_blocked` fields are intentionally the exact current source
predicates from `birthEvent_false_of_no_input_sources`.  They are temporary
frontier clauses: once provenance-to-source-exclusion lemmas exist for the
current TerminalHost, they should become derived theorems rather than stored
fields. -/
structure BirthCohort
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) : Prop where
  leader_exists : exists i, (C i).core.core.leader = true
  comparison_classified :
    exists H : Fin n -> LocalComparisonHistory n,
      forall i, CohortClassifiedAt hpsi (C i) (H i)
  pprime_blocked : forall e, PPrimeBlockedAt hpsi ring C e
  check_blocked : forall e, CheckBlockedAt hpsi h2 ring C e
  no_terminal_five :
    forall i, NoTerminalFive (C i).core.erase.core


/-- Exact current-row condition preventing zero-budget expiry from deleting a
live comparison member.  This is branch-sensitive: an active deletion output
or real path/permission progress is safe even when the old timer is zero;
otherwise a live endpoint must have positive credit.

The parameters `hpsi` and `h2` are necessary if this predicate is to be exact,
because the pre-expiry physical output is the actual width-two TerminalHost
metadata result. -/
def EndpointSafeForCohort
    (hpsi : 0 < psi) (h2 : 2 <= psi) (tau : Nat)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (e : Fin n) : Prop :=
  let l0 := prepareExpiringDisposal hpsi (C e)
  let r0 := prepareExpiringDisposal hpsi (C (ring.rightNeighbor e))
  let q := BirthShortDoneTerminalHost.doneMetadataBoundedEntryWidth
    hpsi (by decide : 0 < 2) h2 l0.core r0.core
  (ComparisonLive l0.core.erase.core ->
      deletionActive q.1.erase = true \/
      PathProgressView.ofState q.1 ≠ PathProgressView.ofState l0.core \/
      0 < l0.stall.val) /\
    (ComparisonLive r0.core.erase.core ->
      deletionActive q.2.erase = true \/
      PathProgressView.ofState q.2 ≠ PathProgressView.ofState r0.core \/
      0 < r0.stall.val)


/-- Prefix-decomposable load condition on the literal original word. -/
def LoadSafeAlong
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) : List (Fin n) -> Prop
  | [] => True
  | e :: es =>
      EndpointSafeForCohort hpsi h2 tau ring C e /\
      LoadSafeAlong hpsi h2 ring
        (BirthShortDoneTerminalConsumer.step
          hpsi (by decide : 0 < 2) h2 ring C e) es


/-- Immediate B9 half: the two stored exact source exclusions are sufficient
for the current terminal observer to report no birth on every edge. -/
theorem birthEvent_false_of_cohort
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau)
    (hcohort : BirthCohort hpsi h2 ring C) (e : Fin n) :
    BirthShortDoneTerminalObserver.birthEvent
      hpsi (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e)) = false := by
  apply
    BirthShortDoneTerminalCheckInputSources.birthEvent_false_of_no_input_sources
      hpsi (by decide : 0 < 2) h2
  · simpa only [PPrimeBlockedAt] using hcohort.pprime_blocked e
  · simpa only [CheckBlockedAt] using hcohort.check_blocked e


/-- Exact B8 source-quarantine premise on the actual successor of the first
birth row.  A first birth changes only its two scheduled endpoints, so it says
nothing about birth-capable material on a disjoint edge, while the two adjacent
edges can also change because they share one of those endpoints.  Therefore the
sound post-birth boundary is global: on every edge of the actual successor,
both prepared source predicates consumed by
`birthEvent_false_of_no_input_sources` must be absent.  A later provenance and
disposal theorem may derive this proposition from `PPLLComparisonHistory` plus
local sanitation, but history trust or disposal-due status alone is not, at the
current frontier, a proved replacement for either exact source exclusion. -/
def PostBirthSourceQuarantine
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (birthEdge : Fin n) : Prop :=
  let D := BirthShortDoneTerminalConsumer.step
    hpsi (by decide : 0 < 2) h2 ring C birthEdge
  forall e,
    PPrimeBlockedAt hpsi ring D e /\ CheckBlockedAt hpsi h2 ring D e


/-- B8 quarantine feeds B9 directly on the real post-birth configuration. -/
theorem postBirthSourceQuarantine_no_birth
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (birthEdge e : Fin n)
    (hq : PostBirthSourceQuarantine hpsi h2 ring C birthEdge) :
    let D := BirthShortDoneTerminalConsumer.step
      hpsi (by decide : 0 < 2) h2 ring C birthEdge
    BirthShortDoneTerminalObserver.birthEvent
      hpsi (by decide : 0 < 2) h2
      (D e) (D (ring.rightNeighbor e)) = false := by
  unfold PostBirthSourceQuarantine at hq
  dsimp only at hq ⊢
  apply
    BirthShortDoneTerminalCheckInputSources.birthEvent_false_of_no_input_sources
      hpsi (by decide : 0 < 2) h2
  · simpa only [PPrimeBlockedAt] using (hq e).1
  · simpa only [CheckBlockedAt] using (hq e).2

end BirthPhaseCohortDesign

#print axioms BirthPhaseCohortDesign.birthEvent_false_of_cohort
#print axioms BirthPhaseCohortDesign.postBirthSourceQuarantine_no_birth
