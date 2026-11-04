import Leader.Wu.Birth.DoneLineageLeaseTransitions

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthDoneLineageLeaseHostStep

open PPLL PPLLRepair PPLLWallSweepRepair
open PPLLComparisonHistory
open BirthDoneLineageQuarantineDesign
open BirthDoneLineageLeaseTransitions

variable {n psi : Nat}

/-! ## Module-local decidability -/

private instance instDecidableDoneHandoffGuardLocal
    (hpsi : 0 < psi) (l r : AgentState psi) :
    Decidable (DoneHandoffGuard hpsi l r) := by
  unfold DoneHandoffGuard
  infer_instance

private instance instDecidableComparisonNeutralLocal
    (u : AgentState psi) : Decidable (ComparisonNeutral u) := by
  unfold ComparisonNeutral
  infer_instance

private instance instDecidableSourceArmReadyLocal
    (l r : LineageCell psi) : Decidable (SourceArmReady l r) := by
  unfold SourceArmReady
  infer_instance

private instance instDecidableGrantPredecessorPermitReadyLocal
    (l r : LineageCell psi) :
    Decidable (GrantPredecessorPermitReady l r) := by
  unfold GrantPredecessorPermitReady
  infer_instance

private instance instDecidableLeaseCutInvariantLocal
    (hpsi : 0 < psi)
    (l r : MarkedAgentState n psi)
    (lrole rrole : LineageRole) :
    Decidable (LeaseCutInvariant hpsi l r lrole rrole) := by
  unfold LeaseCutInvariant DoneRoleReady RoleLineageSound
  infer_instance

/-! ## One scheduled lease-carrying row -/

private def asCell (m : MarkedAgentState n psi)
    (role : LineageRole) : LineageCell psi :=
  { concrete := m.concrete
    role := role }

/-- Exact producer premise for the grant branch.  The pair is evaluated at the
literal current post-control DONE cut.  A writer that makes the grant branch
ready must also establish one common trusted source there. -/
def GrantProducerPremise (hpsi : 0 < psi)
    (l r : MarkedAgentState n psi)
    (lrole rrole : LineageRole) : Prop :=
  let q := currentDoneCut hpsi l r
  GrantPredecessorPermitReady
      (asCell q.1 lrole) (asCell q.2 rrole) ->
    SameTrustedSource q.1.history.state q.2.history.state

/-- The edge-local controller at the literal current DONE cut.

Priority is the adopted one:

1. scrub a forged/stale lease cut;
2. commit a live certified DONE handoff;
3. grant a predecessor permit when ready;
4. arm a fresh neutral source when ready;
5. otherwise frame.

On the non-scrub branches the physical input is exactly `currentDoneCut`; the
commit branch is the adopted `commitFrontier`, i.e. the replacement for the
final backward-depart write. -/
def leasePairStep (hpsi : 0 < psi)
    (l r : MarkedAgentState n psi)
    (lrole rrole : LineageRole) :
    LineageCell psi × LineageCell psi :=
  let q := currentDoneCut hpsi l r
  let lc := asCell q.1 lrole
  let rc := asCell q.2 rrole
  if _hscrub : ¬ LeaseCutInvariant hpsi q.1 q.2 lrole rrole then
    localScrub lc rc
  else if _hcommit : DoneHandoffGuard hpsi lc.concrete rc.concrete then
    commitFrontier hpsi lc rc
  else if _hgrant : GrantPredecessorPermitReady lc rc then
    grantPredecessorPermit lc rc
  else if _harm : SourceArmReady lc rc then
    armSource lc rc
  else
    (lc, rc)

/-- Reattach the exact histories produced by `currentDoneCut` to the physical
states selected by the lease controller.  Source IDs remain proof-side. -/
def leaseMarkedPair (hpsi : 0 < psi)
    (l r : MarkedAgentState n psi)
    (lrole rrole : LineageRole) :
    MarkedAgentState n psi × MarkedAgentState n psi :=
  let q := currentDoneCut hpsi l r
  let c := leasePairStep hpsi l r lrole rrole
  (attachHistory q.1 c.1, attachHistory q.2 c.2)

/-- Role projection of the same edge-local action. -/
def leaseRolePair (hpsi : 0 < psi)
    (l r : MarkedAgentState n psi)
    (lrole rrole : LineageRole) :
    LineageRole × LineageRole :=
  let c := leasePairStep hpsi l r lrole rrole
  (c.1.role, c.2.role)

structure LeaseHostConfig (n psi : Nat) where
  marked : Fin n -> MarkedAgentState n psi
  role : Fin n -> LineageRole

/-- Replace exactly the scheduled initiator/responder pair, in the same shape as
one directed-ring physical interaction. -/
private def replaceScheduledPair {alpha : Type}
    (ring : DirectedRing n) (C : Fin n -> alpha)
    (e : Fin n) (q : alpha × alpha) : Fin n -> alpha :=
  fun i =>
    if i = e then q.1
    else if i = ring.rightNeighbor e then q.2
    else C i

/-- Whole-host one-edge step carrying the adopted lease.  The same scheduled
edge chooses both the physical pair action and the two lease roles. -/
def leaseHostStep (hpsi : 0 < psi)
    (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    LeaseHostConfig n psi :=
  let j := ring.rightNeighbor e
  let mp := leaseMarkedPair hpsi
    (S.marked e) (S.marked j) (S.role e) (S.role j)
  let rp := leaseRolePair hpsi
    (S.marked e) (S.marked j) (S.role e) (S.role j)
  { marked := replaceScheduledPair ring S.marked e mp
    role := replaceScheduledPair ring S.role e rp }

/-! ## The three incident cuts -/

/-- `LeaseSafe` specialized to one oriented cut. -/
def LeaseCutAt (hpsi : 0 < psi)
    (ring : DirectedRing n) (S : LeaseHostConfig n psi)
    (i : Fin n) : Prop :=
  let j := ring.rightNeighbor i
  let q := currentDoneCut hpsi (S.marked i) (S.marked j)
  LeaseCutInvariant hpsi q.1 q.2 (S.role i) (S.role j)

/-- Exact missing commit-side guard: after the predicted host step, the incoming
cut `(left e,e)` must still satisfy the lease invariant. -/
def CommitIncomingLeaseGuard (hpsi : 0 < psi)
    (ring : DirectedRing n) (S : LeaseHostConfig n psi)
    (e : Fin n) : Prop :=
  LeaseCutAt hpsi ring (leaseHostStep hpsi ring S e)
    (ring.leftNeighbor e)

/-- Scheduled cut `(e,right e)` after the step. -/
def ScheduledLeaseGuard (hpsi : 0 < psi)
    (ring : DirectedRing n) (S : LeaseHostConfig n psi)
    (e : Fin n) : Prop :=
  LeaseCutAt hpsi ring (leaseHostStep hpsi ring S e) e

/-- Outgoing cut `(right e,right(right e))` after the step. -/
def RightIncidentLeaseGuard (hpsi : 0 < psi)
    (ring : DirectedRing n) (S : LeaseHostConfig n psi)
    (e : Fin n) : Prop :=
  LeaseCutAt hpsi ring (leaseHostStep hpsi ring S e)
    (ring.rightNeighbor e)

/-! ## Smallest literal counterexample: n = 3, psi = 2 -/

private instance instDecidableLeaseSafeHostLocal (hpsi : 0 < psi)
    (ring : DirectedRing n) (M : Fin n -> MarkedAgentState n psi)
    (role : Fin n -> LineageRole) :
    Decidable (LeaseSafe hpsi ring M role) := by
  unfold LeaseSafe
  (try dsimp only)
  infer_instance

private instance instDecidableLeaseCutAtLocal (hpsi : 0 < psi)
    (ring : DirectedRing n) (S : LeaseHostConfig n psi) (i : Fin n) :
    Decidable (LeaseCutAt hpsi ring S i) := by
  unfold LeaseCutAt
  (try dsimp only)
  infer_instance

private instance instDecidableCommitIncomingLeaseGuardLocal (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : LeaseHostConfig n psi) (e : Fin n) :
    Decidable (CommitIncomingLeaseGuard hpsi ring C e) := by
  unfold CommitIncomingLeaseGuard
  (try dsimp only)
  infer_instance

private instance instDecidableScheduledLeaseGuardLocal (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : LeaseHostConfig n psi) (e : Fin n) :
    Decidable (ScheduledLeaseGuard hpsi ring C e) := by
  unfold ScheduledLeaseGuard
  (try dsimp only)
  infer_instance

private instance instDecidableRightIncidentLeaseGuardLocal (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : LeaseHostConfig n psi) (e : Fin n) :
    Decidable (RightIncidentLeaseGuard hpsi ring C e) := by
  unfold RightIncidentLeaseGuard
  (try dsimp only)
  infer_instance

private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide

private def ring3 : DirectedRing 3 := ⟨hThree⟩

private def p0 : Fin 3 := 0
private def p1 : Fin 3 := 1
private def p2 : Fin 3 := 2

/-- Minimal concrete state constructor, copied field-for-field from the standard
`PPLLCounterexample.state2` shape so this file needs only the requested import. -/
private def base2 (label : Fin 2) (state : MainState) : AgentState 2 :=
  { leader := false
    probe := false
    phase := false
    bit := false
    wait := true
    state := state
    path := .bot
    reset := false
    carry := false
    count := 0
    label := label
    h_field := false
    path2 := none
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := false
    echo := false
    signal_B := 0
    bullet := 0
    shield := true
    write_state := .none
    write := .none
    last := false
    last_set := false
    last_unset := false
    b_carry := false
    gen_ws := false
    ws_echo := false
    signal_ws := false }

private def trustedStateHistory (source : Fin 3) :
    LocalComparisonHistory 3 :=
  { state := .trusted source
    path := .absent
    path2 := .absent
    pCarry := .absent }

/-- Before the scheduled edge `1 -> 2`:

* site 0: CHECK-ready, no lease;
* site 1: CHECK-ready, predecessor permit;
* site 2: depart, frontier;
* sites 1 and 2 name the same trusted source.

Thus only edge `1 -> 2` has a live DONE guard, and that edge is certified. -/
private def beforeMarked (i : Fin 3) : MarkedAgentState 3 2 :=
  if i = p0 then
    ⟨base2 0 .CHECK_ready, trustedStateHistory p0⟩
  else if i = p1 then
    ⟨base2 0 .CHECK_ready, trustedStateHistory p1⟩
  else
    ⟨base2 1 .depart, trustedStateHistory p1⟩

private def beforeRole (i : Fin 3) : LineageRole :=
  if i = p1 then .predecessorPermit
  else if i = p2 then .frontier
  else .none

private def before : LeaseHostConfig 3 2 :=
  { marked := beforeMarked
    role := beforeRole }

private def after : LeaseHostConfig 3 2 :=
  leaseHostStep hTwo ring3 before p1

/-- The three requested oriented cuts are exactly `0 -> 1`, `1 -> 2`, and
`2 -> 0`. -/
theorem counterexample_incident_geometry :
    ring3.leftNeighbor p1 = p0 /\
    ring3.rightNeighbor p1 = p2 /\
    ring3.rightNeighbor (ring3.rightNeighbor p1) = p0 := by
  decide

/-- The starting configuration satisfies the all-edge lease invariant. -/
theorem counterexample_before_leaseSafe :
    LeaseSafe hTwo ring3 before.marked before.role := by
  decide

/-- On the scheduled edge the host takes the certified commit, and its concrete
output is exactly the repository's literal current marked DONE row. -/
theorem counterexample_scheduled_pair_uses_literal_physical_row :
    let hp := leaseMarkedPair hTwo
      (before.marked p1) (before.marked p2)
      (before.role p1) (before.role p2)
    let old := markedDoneCaptureSigMove hTwo
      (before.marked p1) (before.marked p2)
    (hp.1.concrete, hp.2.concrete) =
      (old.1.concrete, old.2.concrete) := by
  decide

/-- The commit moves the frontier to site 1 and consumes site 2's frontier.
Site 0 is untouched. -/
theorem counterexample_after_fields :
    (after.marked p0).concrete.state = .CHECK_ready /\
    after.role p0 = .none /\
    (after.marked p1).concrete.state = .depart /\
    after.role p1 = .frontier /\
    (after.marked p2).concrete.state = .depart /\
    after.role p2 = .none := by
  decide

/-- Re-check all three incident cuts.  Exactly the incoming cut fails; the
scheduled and outgoing cuts remain safe. -/
theorem counterexample_incident_recheck :
    ¬ CommitIncomingLeaseGuard hTwo ring3 before p1 /\
    ScheduledLeaseGuard hTwo ring3 before p1 /\
    RightIncidentLeaseGuard hTwo ring3 before p1 := by
  decide

/-- The incoming cut is newly live, but its predecessor has no permit. -/
theorem counterexample_incoming_cut_witness :
    let q := currentDoneCut hTwo
      (after.marked p0) (after.marked p1)
    DoneHandoffGuard hTwo q.1.concrete q.2.concrete /\
      after.role p0 = .none /\
      after.role p1 = .frontier := by
  decide

/-- Therefore the unconditional whole-host preservation statement requested
here is false for the adopted invariant. -/
theorem counterexample_after_not_leaseSafe :
    ¬ LeaseSafe hTwo ring3 after.marked after.role := by
  decide

end BirthDoneLineageLeaseHostStep

#print axioms BirthDoneLineageLeaseHostStep.counterexample_incident_geometry
#print axioms BirthDoneLineageLeaseHostStep.counterexample_before_leaseSafe
#print axioms BirthDoneLineageLeaseHostStep.counterexample_scheduled_pair_uses_literal_physical_row
#print axioms BirthDoneLineageLeaseHostStep.counterexample_after_fields
#print axioms BirthDoneLineageLeaseHostStep.counterexample_incident_recheck
#print axioms BirthDoneLineageLeaseHostStep.counterexample_incoming_cut_witness
#print axioms BirthDoneLineageLeaseHostStep.counterexample_after_not_leaseSafe
