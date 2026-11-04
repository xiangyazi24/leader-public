import Std.Tactic
import Leader.Wu.Birth.ShortDoneTerminalLoadBound
import Leader.Wu.Birth.ShortDoneTerminalHandoffExpiry
import Leader.Wu.Birth.HScaleHorizonFails

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace StateBoundEpochCoverage

open PPLL PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
open BirthShortDoneParticipationBudget
open BirthShortDoneParticipationLoadMass
open BirthShortDoneTerminalHost
open ExpiringK2Projection K2BirthDispatcher K2BirthLeaderNormalize
open FixedSpanRenewalPayload FiniteUniformStoppingTree
open Q11497FeasibilityAudit

variable {n psi width kappa tau T : Nat}

abbrev Carrier (psi kappa tau : Nat) :=
  ExpiringAgentState psi kappa tau

/-! ## 1. One carrier: certified refresh or well-founded clear -/

/-- Exactly the two events that may refresh the comparison timer inside the
current priority expiry call.  Entry preparation is intentionally absent. -/
def ExpiryRefreshEvent
    (old out : Carrier psi kappa tau) : Prop :=
  deletionActive out.core.erase = true \/
    PathProgressView.ofState out.core !=
      PathProgressView.ofState old.core

private instance instDecidableExpiryRefreshEvent
    (old out : Carrier psi kappa tau) :
    Decidable (ExpiryRefreshEvent old out) := by
  unfold ExpiryRefreshEvent
  infer_instance

theorem deletionPriorityExpireOne_fresh_of_event
    (tau : Nat) (old out : Carrier psi kappa tau)
    (h : ExpiryRefreshEvent old out) :
    deletionPriorityExpireOne tau old out =
      { core := out.core, stall := freshStall tau } := by
  rcases h with hactive | hprogress
  · exact deletionPriorityExpireOne_of_active tau old out hactive
  · exact
      BirthShortDoneParticipationBudget.deletionPriorityExpireOne_of_progress
        tau old out (bne_iff_ne.mp hprogress)

/-- If neither refresh event occurs and the old credit is zero, the existing
path stall policy physically clears the path. -/
theorem deletionPriorityExpireOne_static_zero_clears
    (tau : Nat) (old out : Carrier psi kappa tau)
    (hinactive : deletionActive out.core.erase = false)
    (hstatic : PathProgressView.ofState out.core =
      PathProgressView.ofState old.core)
    (hzero : old.stall.val = 0) :
    (deletionPriorityExpireOne tau old out).core.core.path = .bot := by
  rw [deletionPriorityExpireOne, if_neg (by simp [hinactive])]
  exact (pathExpireOne_zero_clears tau old out hstatic hzero).1

/-- If neither refresh event occurs and positive credit remains, exactly the
same existing path policy strictly spends timer credit. -/
theorem deletionPriorityExpireOne_static_decreases
    (tau : Nat) (old out : Carrier psi kappa tau)
    (hinactive : deletionActive out.core.erase = false)
    (hstatic : PathProgressView.ofState out.core =
      PathProgressView.ofState old.core)
    (hpos : 0 < old.stall.val) :
    (deletionPriorityExpireOne tau old out).stall.val < old.stall.val := by
  rw [deletionPriorityExpireOne, if_neg (by simp [hinactive])]
  exact pathExpireOne_decreases_of_static tau old out hstatic hpos

/-- The old fixed-base theorem remains the base case of the coverage argument.
The sequence-valued monitor below is needed because successive physical local
opportunities can have different partners/roles. -/
theorem pathStaticRun_feeder
    (tau : Nat) (base : Carrier psi kappa tau -> Carrier psi kappa tau)
    (hbase : forall s,
      PathProgressView.ofState (base s).core =
        PathProgressView.ofState s.core)
    (s : Carrier psi kappa tau) :
    (pathStaticRun tau base (s.stall.val + 1) s).core.core.path = .bot :=
  pathStaticRun_clears tau base hbase s

/-- Proof-only stopping monitor.  It adds no protocol state.  `refreshed q`
means the literal expiry action took one of the two certified refresh branches;
`cleared q` means the literal expiry result has `path = bot`. -/
inductive CoverageNode (psi kappa tau : Nat) where
  | active (s : Carrier psi kappa tau)
  | refreshed (s : Carrier psi kappa tau)
  | cleared (s : Carrier psi kappa tau)

/-- The terminal monitor states carry their promised physical fact. -/
def CoverageGood (tau : Nat) : CoverageNode psi kappa tau -> Prop
  | .active _ => False
  | .refreshed s => s.stall = freshStall tau
  | .cleared s => s.core.core.path = .bot

/-- One monitored local opportunity.  `base` is the physical state presented
as `out` to the one literal `deletionPriorityExpireOne` call at this
opportunity. -/
def coverageStep (tau : Nat)
    (base : Carrier psi kappa tau -> Carrier psi kappa tau) :
    CoverageNode psi kappa tau -> CoverageNode psi kappa tau
  | .active s =>
      let out := base s
      let q := deletionPriorityExpireOne tau s out
      if ExpiryRefreshEvent s out then .refreshed q
      else if q.core.core.path = .bot then .cleared q
      else .active q
  | .refreshed s => .refreshed s
  | .cleared s => .cleared s

/-- A varying sequence of local opportunities.  `start` is proof-side indexing
only; it is not an epoch counter stored by the protocol. -/
def coverageRun (tau : Nat)
    (base : Nat -> Carrier psi kappa tau -> Carrier psi kappa tau) :
    Nat -> Nat -> CoverageNode psi kappa tau -> CoverageNode psi kappa tau
  | _, 0, x => x
  | start, k + 1, x =>
      coverageRun tau base (start + 1) k
        (coverageStep tau (base start) x)

@[simp] theorem coverageRun_refreshed
    (tau : Nat)
    (base : Nat -> Carrier psi kappa tau -> Carrier psi kappa tau)
    (start k : Nat) (s : Carrier psi kappa tau) :
    coverageRun tau base start k (.refreshed s) = .refreshed s := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih => simp [coverageRun, coverageStep, ih]

@[simp] theorem coverageRun_cleared
    (tau : Nat)
    (base : Nat -> Carrier psi kappa tau -> Carrier psi kappa tau)
    (start k : Nat) (s : Carrier psi kappa tau) :
    coverageRun tau base start k (.cleared s) = .cleared s := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih => simp [coverageRun, coverageStep, ih]

theorem per_carrier_refresh_or_clear
    (tau : Nat)
    (base : Nat -> Carrier psi kappa tau -> Carrier psi kappa tau)
    (start : Nat) (s : Carrier psi kappa tau) :
    CoverageGood tau
      (coverageRun tau base start (s.stall.val + 1) (.active s)) := by
  generalize hk : s.stall.val = k
  induction k generalizing start s base with
  | zero =>
      let out := base start s
      let q := deletionPriorityExpireOne tau s out
      by_cases hrefresh : ExpiryRefreshEvent s out
      · have hq : q = { core := out.core, stall := freshStall tau } := by
          dsimp [q]
          exact deletionPriorityExpireOne_fresh_of_event tau s out hrefresh
        have hstep :
            coverageStep tau (base start) (.active s) = .refreshed q := by
          simp [coverageStep, out, q, hrefresh]
        change CoverageGood tau
          (coverageStep tau (base start) (.active s))
        rw [hstep]
        change q.stall = freshStall tau
        rw [hq]
      · have hinactive : deletionActive out.core.erase = false := by
          cases ha : deletionActive out.core.erase with
          | false => rfl
          | true => exact False.elim (hrefresh (Or.inl ha))
        have hstatic :
            PathProgressView.ofState out.core =
              PathProgressView.ofState s.core := by
          by_cases hs :
              PathProgressView.ofState out.core =
                PathProgressView.ofState s.core
          · exact hs
          · exact False.elim
              (hrefresh (Or.inr (bne_iff_ne.mpr hs)))
        have hqpath : q.core.core.path = .bot := by
          dsimp [q]
          exact deletionPriorityExpireOne_static_zero_clears
            tau s out hinactive hstatic hk
        have hstep :
            coverageStep tau (base start) (.active s) = .cleared q := by
          simp [coverageStep, out, q, hrefresh, hqpath]
        change CoverageGood tau
          (coverageStep tau (base start) (.active s))
        rw [hstep]
        exact hqpath
  | succ k ih =>
      let out := base start s
      let q := deletionPriorityExpireOne tau s out
      by_cases hrefresh : ExpiryRefreshEvent s out
      · have hq : q = { core := out.core, stall := freshStall tau } := by
          dsimp [q]
          exact deletionPriorityExpireOne_fresh_of_event tau s out hrefresh
        have hstep :
            coverageStep tau (base start) (.active s) = .refreshed q := by
          simp [coverageStep, out, q, hrefresh]
        change CoverageGood tau
          (coverageRun tau base (start + 1) (k + 1)
            (coverageStep tau (base start) (.active s)))
        rw [hstep, coverageRun_refreshed]
        change q.stall = freshStall tau
        rw [hq]
      · have hinactive : deletionActive out.core.erase = false := by
          cases ha : deletionActive out.core.erase with
          | false => rfl
          | true => exact False.elim (hrefresh (Or.inl ha))
        have hstatic :
            PathProgressView.ofState out.core =
              PathProgressView.ofState s.core := by
          by_cases hs :
              PathProgressView.ofState out.core =
                PathProgressView.ofState s.core
          · exact hs
          · exact False.elim
              (hrefresh (Or.inr (bne_iff_ne.mpr hs)))
        by_cases hqpath : q.core.core.path = .bot
        · have hstep :
              coverageStep tau (base start) (.active s) = .cleared q := by
            simp [coverageStep, out, q, hrefresh, hqpath]
          change CoverageGood tau
            (coverageRun tau base (start + 1) (k + 1)
              (coverageStep tau (base start) (.active s)))
          rw [hstep, coverageRun_cleared]
          exact hqpath
        · have hpos : 0 < s.stall.val := by omega
          have hqeq :
              q = { core := out.core, stall := decStall s.stall hpos } := by
            dsimp [q]
            rw [deletionPriorityExpireOne,
              if_neg (by simp [hinactive])]
            exact pathExpireOne_succ_of_static
              tau s out hstatic hpos
          have hqstall : q.stall.val = k := by
            rw [hqeq]
            simp [decStall]
            omega
          have hstep :
              coverageStep tau (base start) (.active s) = .active q := by
            simp [coverageStep, out, q, hrefresh, hqpath]
          change CoverageGood tau
            (coverageRun tau base (start + 1) (k + 1)
              (coverageStep tau (base start) (.active s)))
          rw [hstep]
          have hrec :=
            ih (start := start + 1) (s := q) (base := base) hqstall
          exact hrec

/-- Every executable stall belongs to `Fin (tau+1)`, hence the stopping prefix
above always uses at most `tau+1` of this carrier's own local opportunities. -/
theorem per_carrier_coverage_within_tau_plus_one
    (tau : Nat)
    (base : Nat -> Carrier psi kappa tau -> Carrier psi kappa tau)
    (start : Nat) (s : Carrier psi kappa tau) :
    exists k,
      k <= tau + 1 /\
      CoverageGood tau
        (coverageRun tau base start k (.active s)) := by
  refine ⟨s.stall.val + 1, ?_,
    per_carrier_refresh_or_clear tau base start s⟩
  have hs := s.stall.isLt
  omega

/-! ## 2. Attachment to the literal terminal host -/

/-- Disposal preparation is not a hidden timer refresh and preserves the
physical path. -/
theorem prepareExpiringDisposal_monitor_frame
    (hpsi : 0 < psi) (u : Carrier psi kappa tau) :
    (prepareExpiringDisposal hpsi u).core.erase.core.path =
        u.core.erase.core.path /\
      (prepareExpiringDisposal hpsi u).stall = u.stall := by
  constructor
  · change
      (prepareBoundedDisposal hpsi u.core).erase.core.path =
        u.core.erase.core.path
    exact
      (congrArg (fun a : AuthorizedAgentState psi => a.core.path)
        (erase_prepareBoundedDisposal hpsi u.core)).trans
        (prepareDisposal_path hpsi u.core.erase)
  · rfl

private theorem normalizeLeader_path_frame
    (hpsi : 0 < psi) (u : Carrier psi kappa tau) :
    (K2BirthLeaderNormalize.normalizeLeader hpsi u).core.erase.core.path =
      u.core.erase.core.path := by
  unfold K2BirthLeaderNormalize.normalizeLeader
  split <;> rfl

private theorem nonK2_path_eq
    {a b : Carrier psi kappa tau}
    (h : ExpiringK2Projection.nonK2 a =
      ExpiringK2Projection.nonK2 b) :
    a.core.erase.core.path = b.core.erase.core.path := by
  have hp := congrArg
    (fun u : Carrier psi kappa tau => u.core.erase.core.path) h
  change a.core.erase.core.path = b.core.erase.core.path at hp
  exact hp

theorem terminal_row_expiry_frames
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : Carrier psi kappa tau) :
    let l0 := prepareExpiringDisposal hpsi l
    let r0 := prepareExpiringDisposal hpsi r
    let q := doneMetadataBoundedEntryWidth hpsi hwidth hle l0.core r0.core
    let eL := deletionPriorityExpireOne tau l0
      ({ core := q.1, stall := l0.stall } : Carrier psi kappa tau)
    let eR := deletionPriorityExpireOne tau r0
      ({ core := q.2, stall := r0.stall } : Carrier psi kappa tau)
    (row hpsi hwidth hle l r).1.stall = eL.stall /\
      (row hpsi hwidth hle l r).2.stall = eR.stall /\
      (row hpsi hwidth hle l r).1.core.erase.core.path =
        eL.core.erase.core.path /\
      (row hpsi hwidth hle l r).2.core.erase.core.path =
        eR.core.erase.core.path := by
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let q := doneMetadataBoundedEntryWidth hpsi hwidth hle l0.core r0.core
  let eL := deletionPriorityExpireOne tau l0
    ({ core := q.1, stall := l0.stall } : Carrier psi kappa tau)
  let eR := deletionPriorityExpireOne tau r0
    ({ core := q.2, stall := r0.stall } : Carrier psi kappa tau)
  have ht :
      (row hpsi hwidth hle l r).1.stall = eL.stall /\
        (row hpsi hwidth hle l r).2.stall = eR.stall := by
    simpa [l0, r0, q, eL, eR] using
      (BirthShortDoneTerminalConsumer.row_timers_once
        (κ := kappa) (τ := tau) hpsi hwidth hle l r)
  have hw :
      row hpsi hwidth hle l r =
        K2BirthDispatcher.finalPhysical hpsi l r
          (K2BirthLeaderNormalize.normalizeLeader hpsi eL)
          (K2BirthLeaderNormalize.normalizeLeader hpsi eR) := by
    simpa [l0, r0, q, eL, eR] using
      (BirthShortDoneTerminalHost.row_real_host_witness
        hpsi hwidth hle l r)
  have hf := K2BirthDispatcher.finalPhysical_nonK2 hpsi l r
    (K2BirthLeaderNormalize.normalizeLeader hpsi eL)
    (K2BirthLeaderNormalize.normalizeLeader hpsi eR)
  have hLp := nonK2_path_eq hf.1
  have hRp := nonK2_path_eq hf.2
  have hnL := normalizeLeader_path_frame hpsi eL
  have hnR := normalizeLeader_path_frame hpsi eR
  have hpL :
      (row hpsi hwidth hle l r).1.core.erase.core.path =
        eL.core.erase.core.path := by
    rw [hw]
    exact hLp.trans hnL
  have hpR :
      (row hpsi hwidth hle l r).2.core.erase.core.path =
        eR.core.erase.core.path := by
    rw [hw]
    exact hRp.trans hnR
  exact ⟨ht.1, ht.2, hpL, hpR⟩

/-- The exact pre-expiry state for the left role of one terminal-host row. -/
def terminalLeftExpiryBase
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : Carrier psi kappa tau) : Carrier psi kappa tau :=
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let q := doneMetadataBoundedEntryWidth hpsi hwidth hle l0.core r0.core
  { core := q.1, stall := l0.stall }

/-- The exact pre-expiry state for the right role of one terminal-host row. -/
def terminalRightExpiryBase
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : Carrier psi kappa tau) : Carrier psi kappa tau :=
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let q := doneMetadataBoundedEntryWidth hpsi hwidth hle l0.core r0.core
  { core := q.2, stall := r0.stall }

/-- Certified left-role refresh event of the literal host. -/
def TerminalLeftRefreshEvent
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : Carrier psi kappa tau) : Prop :=
  ExpiryRefreshEvent
    (prepareExpiringDisposal hpsi l)
    (terminalLeftExpiryBase hpsi hwidth hle l r)

/-- Certified right-role refresh event of the literal host. -/
def TerminalRightRefreshEvent
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : Carrier psi kappa tau) : Prop :=
  ExpiryRefreshEvent
    (prepareExpiringDisposal hpsi r)
    (terminalRightExpiryBase hpsi hwidth hle l r)

theorem terminal_left_refresh_is_fresh
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : Carrier psi kappa tau)
    (h : TerminalLeftRefreshEvent hpsi hwidth hle l r) :
    (row hpsi hwidth hle l r).1.stall = freshStall tau := by
  have he := deletionPriorityExpireOne_fresh_of_event tau
    (prepareExpiringDisposal hpsi l)
    (terminalLeftExpiryBase hpsi hwidth hle l r) h
  have hs :
      (deletionPriorityExpireOne tau
        (prepareExpiringDisposal hpsi l)
        (terminalLeftExpiryBase hpsi hwidth hle l r)).stall =
        freshStall tau := by
    simpa using congrArg ExpiringAgentState.stall he
  have ht := BirthShortDoneTerminalConsumer.row_timers_once
    (κ := kappa) (τ := tau) hpsi hwidth hle l r
  have hframe :
      (row hpsi hwidth hle l r).1.stall =
        (deletionPriorityExpireOne tau
          (prepareExpiringDisposal hpsi l)
          (terminalLeftExpiryBase hpsi hwidth hle l r)).stall := by
    simpa [terminalLeftExpiryBase] using ht.1
  exact hframe.trans hs

theorem terminal_right_refresh_is_fresh
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : Carrier psi kappa tau)
    (h : TerminalRightRefreshEvent hpsi hwidth hle l r) :
    (row hpsi hwidth hle l r).2.stall = freshStall tau := by
  have he := deletionPriorityExpireOne_fresh_of_event tau
    (prepareExpiringDisposal hpsi r)
    (terminalRightExpiryBase hpsi hwidth hle l r) h
  have hs :
      (deletionPriorityExpireOne tau
        (prepareExpiringDisposal hpsi r)
        (terminalRightExpiryBase hpsi hwidth hle l r)).stall =
        freshStall tau := by
    simpa using congrArg ExpiringAgentState.stall he
  have ht := BirthShortDoneTerminalConsumer.row_timers_once
    (κ := kappa) (τ := tau) hpsi hwidth hle l r
  have hframe :
      (row hpsi hwidth hle l r).2.stall =
        (deletionPriorityExpireOne tau
          (prepareExpiringDisposal hpsi r)
          (terminalRightExpiryBase hpsi hwidth hle l r)).stall := by
    simpa [terminalRightExpiryBase] using ht.2
  exact hframe.trans hs

/-- Literal freshness premise required by the existing terminal load theorem at
one epoch start.  Only sites actually charged in that epoch need occur in the
list. -/
def EpochStartFresh
    (sites : List (Fin n))
    (C : Fin n -> Carrier psi kappa tau) : Prop :=
  forall i, i ∈ sites -> (C i).stall.val = tau

/-- One fresh timer is not stable until a later deterministic raw boundary:
one static local opportunity immediately spends one unit.  This is the first
obstruction to deriving `EpochStartFresh` merely from "a refresh occurred
somewhere in the previous epoch". -/
theorem fresh_credit_spent_by_one_static_opportunity
    (tau : Nat) (htau : 0 < tau)
    (s : Carrier psi kappa tau)
    (hfresh : s.stall = freshStall tau) :
    (pathIdleTick tau s).stall.val = tau - 1 /\
      (pathIdleTick tau s).stall.val != tau := by
  have hpos : 0 < s.stall.val := by
    rw [hfresh]
    simp [freshStall, htau]
  have hstep := pathExpireOne_succ_of_static tau s s rfl hpos
  change
    (pathExpireOne tau s s).stall.val = tau - 1 /\
      (pathExpireOne tau s s).stall.val != tau
  rw [hstep]
  constructor
  · simp [decStall, hfresh, freshStall]
  · simp [decStall, hfresh, freshStall]
    omega

/-- Bad raw-word indicator for the *lower* tail needed by coverage: the selected
site receives fewer than `m` of its own local opportunities. -/
def underOpportunityBit
    (ring : DirectedRing n) (i : Fin n) (m : Nat)
    (word : DetSchedule n) : Nat :=
  if endpointParticipations ring i word < m then 1 else 0

/-- Exact raw-word numerator of the lower-tail event. -/
def underOpportunityNumerator
    (ring : DirectedRing n) (i : Fin n) (E m : Nat) : Nat :=
  wordSum n E (underOpportunityBit ring i m)

/-- Multiplicity union numerator for exactly the sites charged in an epoch. -/
def listedUnderOpportunityMass
    (ring : DirectedRing n) (sites : List (Fin n))
    (E m : Nat) : Nat :=
  (sites.map (fun i => underOpportunityNumerator ring i E m)).sum

theorem underOpportunityBit_eq_one_iff
    (ring : DirectedRing n) (i : Fin n) (m : Nat)
    (word : DetSchedule n) :
    underOpportunityBit ring i m word = 1 <->
      endpointParticipations ring i word < m := by
  unfold underOpportunityBit
  by_cases h : endpointParticipations ring i word < m <;> simp [h]

/-- Total endpoint-opportunity load over all raw words of one fixed length. -/
def opportunityNumerator
    (ring : DirectedRing n) (i : Fin n) (E : Nat) : Nat :=
  wordSum n E (fun word => endpointParticipations ring i word)

private theorem chooseCount_one (k : Nat) : chooseCount k 1 = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [chooseCount, ih, Nat.succ_eq_add_one, Nat.add_comm]

private theorem opportunityNumerator_eq_chooseMomentOne
    (ring : DirectedRing n) (i : Fin n) (E : Nat) :
    opportunityNumerator ring i E =
      chooseMomentNumerator ring i E 1 := by
  unfold opportunityNumerator chooseMomentNumerator
  rw [<- rawWord_sum n E
        (fun w => endpointParticipations ring i w),
      <- rawWord_sum n E
        (fun w => chooseCount (endpointParticipations ring i w) 1)]
  apply ofFn_sum_eq
  intro a
  exact
    (chooseCount_one
      (endpointParticipations ring i (rawWord n E a))).symm

/-- For `n >= 2`, one uniform raw edge gives exactly two favorable scheduler
letters for a fixed site.  Thus one own opportunity has exact one-step mass
`2/n`, not merely an asymptotic approximation. -/
theorem one_step_opportunity_mass
    (hn2 : 2 <= n) (ring : DirectedRing n) (i : Fin n) :
    opportunityNumerator ring i 1 = 2 := by
  rw [opportunityNumerator_eq_chooseMomentOne,
    chooseMoment_eq_cap hn2 ring i 1 1]
  simp [factorialMomentCap]

/-- Number of fixed raw epochs used to cover a cap.  The `E=0` branch is kept
total; every useful coverage application separately assumes `0 < E`. -/
def epochCount (Tcap E : Nat) : Nat :=
  if E = 0 then 0 else (Tcap + E - 1) / E

/-- Exact cross-multiplied lower-tail premise sufficient to union-charge `K`
epochs and the caller-listed sites to total scheduler failure at most `1/n`.
This is the mass theorem still needed from the raw scheduler. -/
def EpochOpportunityCoverageScale
    (ring : DirectedRing n) (sites : List (Fin n))
    (E tau K : Nat) : Prop :=
  n * K * listedUnderOpportunityMass ring sites E (tau + 1) <= n ^ E

/-- Generic finite union arithmetic with a common denominator.  If every one
of `K` epoch events has numerator `bad j` and each was budgeted at scale
`denom*K`, then their normalized union costs at most `1/denom`. -/
theorem finite_epoch_union_crossmul
    {K denom mass : Nat} (hK : 0 < K)
    (bad : Fin K -> Nat)
    (hbad : forall j, denom * K * bad j <= mass) :
    denom * (List.ofFn bad).sum <= mass := by
  have hs := ofFn_sum_le
    (fun j : Fin K => (denom * K) * bad j)
    (fun _ : Fin K => mass)
    (fun j => hbad j)
  rw [ofFn_sum_mul_left, ofFn_sum_const] at hs
  have hreassoc :
      (denom * K) * (List.ofFn bad).sum =
        K * (denom * (List.ofFn bad).sum) := by
    ac_rfl
  rw [hreassoc] at hs
  exact Nat.le_of_mul_le_mul_left hs hK

/-! ## 4. The proposed fixed-epoch hscale is false -/

/-- The raw epoch length proposed in the question, specialized to the checked
`tauChoice`. -/
def requestedEpochLength (n c : Nat) : Nat :=
  n * (tauChoice n + 1) * c

theorem requestedEpochLength_four
    (c : Nat) : requestedEpochLength 4 c = 196 * c := by
  unfold requestedEpochLength
  rw [Q11578HScaleAudit.tauChoice_four_order]

/-- This directly refutes task 3 as stated.  For every positive `c`, even the
`Q=1` fixed-site terminal hscale is false.  Any additional site/epoch union
factor only strengthens the impossible left-hand side. -/
theorem requested_epoch_hscale_four_fails
    (c : Nat) (hc : 0 < c) :
    not
      (chooseCount (requestedEpochLength 4 c) (tauChoice 4 + 1) *
          2 ^ (tauChoice 4 + 1) <=
        4 ^ (tauChoice 4 + 1)) := by
  have hE : 99 <= requestedEpochLength 4 c := by
    rw [requestedEpochLength_four]
    omega
  have hf :=
    Q11578HScaleAudit.fixed_site_hscale_four_fails_of_99_le
      (requestedEpochLength 4 c) hE
  rw [Q11578HScaleAudit.tauChoice_four_order]
  exact hf

/-! The corrected route is therefore:

1. use `per_carrier_coverage_within_tau_plus_one` as a proof-only stopping
   monitor over the literal local expiry opportunities;
2. prove `EpochOpportunityCoverageScale` (a binomial lower-tail bound with
   exact one-step parameter `2/n`) on the original raw scheduler;
3. replace the old fixed-horizon load application by a reset-aware theorem
   stopped at `.refreshed` or `.cleared`.

A predetermined raw boundary cannot use the old `EpochStartFresh` premise, and
`requestedEpochLength` cannot satisfy its old hscale at `tauChoice`. -/

#check @BirthShortDoneTerminalConsumer.row_timers_once
#check @PPLLLeaderCreationCleanupRepair.deletionPriorityExpireOne_of_active
#check @BirthShortDoneParticipationBudget.deletionPriorityExpireOne_of_progress
#check @PPLLPathStallComparisonRepair.pathStaticRun_clears
#check @BirthShortDoneTerminalHandoffExpiry.row_right_handoff_or_end
#check @BirthShortDoneTerminalLoadBound.terminal_fixed_site_exposure_crossmul
#check @Q11578HScaleAudit.fixed_site_hscale_four_fails_of_99_le

end StateBoundEpochCoverage

#print axioms StateBoundEpochCoverage.deletionPriorityExpireOne_fresh_of_event
#print axioms StateBoundEpochCoverage.deletionPriorityExpireOne_static_zero_clears
#print axioms StateBoundEpochCoverage.deletionPriorityExpireOne_static_decreases
#print axioms StateBoundEpochCoverage.pathStaticRun_feeder
#print axioms StateBoundEpochCoverage.per_carrier_refresh_or_clear
#print axioms StateBoundEpochCoverage.per_carrier_coverage_within_tau_plus_one
#print axioms StateBoundEpochCoverage.prepareExpiringDisposal_monitor_frame
#print axioms StateBoundEpochCoverage.terminal_row_expiry_frames
#print axioms StateBoundEpochCoverage.terminal_left_refresh_is_fresh
#print axioms StateBoundEpochCoverage.terminal_right_refresh_is_fresh
#print axioms StateBoundEpochCoverage.fresh_credit_spent_by_one_static_opportunity
#print axioms StateBoundEpochCoverage.underOpportunityBit_eq_one_iff
#print axioms StateBoundEpochCoverage.one_step_opportunity_mass
#print axioms StateBoundEpochCoverage.finite_epoch_union_crossmul
#print axioms StateBoundEpochCoverage.requestedEpochLength_four
#print axioms StateBoundEpochCoverage.requested_epoch_hscale_four_fails
