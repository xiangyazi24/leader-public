import Leader.Wu.Birth.DoneLineageLeaseHostStep

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthDoneLineageLeaseActiveReservation

open PPLL PPLLRepair PPLLWallSweepRepair
open PPLLComparisonHistory PPLLWallSweepHistory
open BirthDoneLineageQuarantineDesign
open BirthDoneLineageLeaseTransitions
open BirthDoneLineageLeaseHostStep

variable {n psi : Nat}

/-! ## Active predecessor-edge writer -/

/-- Active repair on the predecessor edge `(p,e)` of a pending commit.

If `e` carries `predecessorPermit` and `p` is unowned, erase the physical and
marked comparison lineage at `p`.  This makes the future incoming DONE cut
vacuous without inventing a source-ID tag.  If `p` is already lease-owned,
leave it alone and erase `e` instead, safely abandoning the pending commit.
Otherwise frame.  No new lease value is introduced. -/
def activePredecessorLeaseStep
    (l r : LineageCell psi) : LineageCell psi × LineageCell psi :=
  if r.role = .predecessorPermit then
    if l.role = .none then
      (scrubCell l, r)
    else
      (l, scrubCell r)
  else
    (l, r)

/-- Marked refinement of the same writer.  The repository eraser clears both
the concrete carrier and its proof-side comparison history. -/
def activePredecessorMarkedPair
    (l r : MarkedAgentState n psi)
    (lrole rrole : LineageRole) :
    MarkedAgentState n psi × MarkedAgentState n psi :=
  if rrole = .predecessorPermit then
    if lrole = .none then
      (PPLLWallSweepHistory.markedClearComparisonSignal l, r)
    else
      (l, PPLLWallSweepHistory.markedClearComparisonSignal r)
  else
    (l, r)

/-- Lease-role projection of `activePredecessorLeaseStep`. -/
def activePredecessorRolePair
    (lrole rrole : LineageRole) : LineageRole × LineageRole :=
  if rrole = .predecessorPermit then
    if lrole = .none then (.none, rrole) else (lrole, .none)
  else
    (lrole, rrole)

private def replaceEdgePair {alpha : Type}
    (ring : DirectedRing n) (C : Fin n -> alpha)
    (e : Fin n) (q : alpha × alpha) : Fin n -> alpha :=
  fun i =>
    if i = e then q.1
    else if i = ring.rightNeighbor e then q.2
    else C i

/-- Whole-ring lift of the active predecessor-edge writer. -/
def activePredecessorHostStep
    (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    LeaseHostConfig n psi :=
  let j := ring.rightNeighbor e
  let mp := activePredecessorMarkedPair
    (S.marked e) (S.marked j) (S.role e) (S.role j)
  let rp := activePredecessorRolePair (S.role e) (S.role j)
  { marked := replaceEdgePair ring S.marked e mp
    role := replaceEdgePair ring S.role e rp }

/-! ## The guarded commit used for the regressions -/

private instance instDecidableLeaseCutInvariantActive
    (hpsi : 0 < psi)
    (l r : MarkedAgentState n psi)
    (lrole rrole : LineageRole) :
    Decidable (LeaseCutInvariant hpsi l r lrole rrole) := by
  unfold LeaseCutInvariant DoneRoleReady RoleLineageSound
  infer_instance

private instance instDecidableLeaseSafeActive
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (M : Fin n -> MarkedAgentState n psi)
    (role : Fin n -> LineageRole) :
    Decidable (LeaseSafe hpsi ring M role) := by
  unfold LeaseSafe
  dsimp only
  infer_instance

private instance instDecidableLeaseCutAtActive
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    Decidable (LeaseCutAt hpsi ring S e) := by
  unfold LeaseCutAt
  dsimp only
  infer_instance

private instance instDecidableCommitIncomingActive
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    Decidable (CommitIncomingLeaseGuard hpsi ring S e) := by
  unfold CommitIncomingLeaseGuard
  infer_instance

private instance instDecidableScheduledActive
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    Decidable (ScheduledLeaseGuard hpsi ring S e) := by
  unfold ScheduledLeaseGuard
  infer_instance

private instance instDecidableRightIncidentActive
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    Decidable (RightIncidentLeaseGuard hpsi ring S e) := by
  unfold RightIncidentLeaseGuard
  infer_instance

/-- A live scheduled DONE cut whose current lease certificate is valid. -/
def CertifiedCommitAt
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) : Prop :=
  let j := ring.rightNeighbor e
  let q := currentDoneCut hpsi (S.marked e) (S.marked j)
  DoneHandoffGuard hpsi q.1.concrete q.2.concrete /\
    LeaseCutInvariant hpsi q.1 q.2 (S.role e) (S.role j)

private instance instDecidableCertifiedCommitAtActive
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    Decidable (CertifiedCommitAt hpsi ring S e) := by
  unfold CertifiedCommitAt
  dsimp only
  infer_instance

/-- Exact three-cut postcheck from the passive guarded host. -/
def CommitClosureGuard
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) : Prop :=
  CommitIncomingLeaseGuard hpsi ring S e /\
    ScheduledLeaseGuard hpsi ring S e /\
    RightIncidentLeaseGuard hpsi ring S e

private instance instDecidableCommitClosureGuardActive
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    Decidable (CommitClosureGuard hpsi ring S e) := by
  unfold CommitClosureGuard
  infer_instance

/-- Unsafe candidate commits are still refused. -/
def guardedLeaseHostStep
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    LeaseHostConfig n psi :=
  if CommitClosureGuard hpsi ring S e then
    leaseHostStep hpsi ring S e
  else
    S

/-! ## Fixture -/

private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide
private def ring3 : DirectedRing 3 := ⟨hThree⟩
private def p0 : Fin 3 := 0
private def p1 : Fin 3 := 1
private def p2 : Fin 3 := 2

private def base2 (label : Fin 2) (state : MainState) : AgentState 2 :=
  { leader := false, probe := false, phase := false, bit := false, wait := true,
    state := state, path := .bot, reset := false, carry := false, count := 0,
    label := label, h_field := false, path2 := none, path3 := none,
    path4 := none, path5 := none, p := false, p_carry := false,
    reset_cmd := false, echo := false, signal_B := 0, bullet := 0,
    shield := true, write_state := .none, write := .none, last := false,
    last_set := false, last_unset := false, b_carry := false, gen_ws := false,
    ws_echo := false, signal_ws := false }

private def trustedStateHistory (source : Fin 3) :
    LocalComparisonHistory 3 :=
  { state := .trusted source, path := .absent,
    path2 := .absent, pCarry := .absent }

private def blockedMarked (i : Fin 3) : MarkedAgentState 3 2 :=
  if i = p0 then
    ⟨base2 0 .CHECK_ready, trustedStateHistory p0⟩
  else if i = p1 then
    ⟨base2 0 .CHECK_ready, trustedStateHistory p1⟩
  else
    ⟨base2 1 .depart, trustedStateHistory p1⟩

private def blockedRole (i : Fin 3) : LineageRole :=
  if i = p1 then .predecessorPermit
  else if i = p2 then .frontier
  else .none

private def blockedBefore : LeaseHostConfig 3 2 :=
  { marked := blockedMarked, role := blockedRole }

private def repairedBefore : LeaseHostConfig 3 2 :=
  activePredecessorHostStep ring3 blockedBefore p0

private def committedAfter : LeaseHostConfig 3 2 :=
  guardedLeaseHostStep hTwo ring3 repairedBefore p1

/-- The starting fixture is still the safe pre-state. -/
theorem q11670_blocked_before_safe :
    LeaseSafe hTwo ring3 blockedBefore.marked blockedBefore.role := by
  decide

/-- The raw candidate is still exactly the unsafe transition. -/
theorem q11670_raw_candidate_still_unsafe :
    ¬ LeaseSafe hTwo ring3
      (leaseHostStep hTwo ring3 blockedBefore p1).marked
      (leaseHostStep hTwo ring3 blockedBefore p1).role := by
  decide

/-- Hence the guarded host still blocks that unsafe step before repair. -/
theorem q11670_unsafe_step_still_blocked :
    forall i : Fin 3,
      (guardedLeaseHostStep hTwo ring3 blockedBefore p1).marked i =
          blockedBefore.marked i /\
        (guardedLeaseHostStep hTwo ring3 blockedBefore p1).role i =
          blockedBefore.role i := by
  decide

/-- Scheduling the predecessor edge `0 -> 1` really clears the conflicting
source-0 lineage and frames the pending commit endpoint at site 1. -/
theorem q11670_active_writer_repairs_predecessor :
    (repairedBefore.marked p0).concrete.state = .none /\
      (repairedBefore.marked p0).history.state = .absent /\
      repairedBefore.role p0 = .none /\
      repairedBefore.marked p1 = blockedBefore.marked p1 /\
      repairedBefore.role p1 = .predecessorPermit := by
  decide

/-- The certified `1 -> 2` commit survives, and its three-cut postcheck is now
true because the newly exposed predecessor cut has been neutralized. -/
theorem q11670_active_writer_enables_certified_commit :
    CertifiedCommitAt hTwo ring3 repairedBefore p1 /\
      CommitClosureGuard hTwo ring3 repairedBefore p1 := by
  decide

/-- One active predecessor write followed by the guarded scheduled edge escapes
the old closed deadlock through a certified, LeaseSafe commit. -/
theorem q11670_active_writer_then_commits_safely :
    (committedAfter.marked p1).concrete.state = .depart /\
      committedAfter.role p1 = .frontier /\
      committedAfter.role p2 = .none /\
      LeaseSafe hTwo ring3 committedAfter.marked committedAfter.role := by
  decide

/-- Alternate local branch: if the predecessor is already lease-owned, do not
steal it.  Scrub the waiting permit endpoint instead; this kills the pending
commit and leaves a LeaseSafe configuration. -/
private def occupiedRole (i : Fin 3) : LineageRole :=
  if i = p0 then .sourceArmed else blockedRole i

private def occupiedBefore : LeaseHostConfig 3 2 :=
  { marked := blockedMarked, role := occupiedRole }

private def abandonedAfter : LeaseHostConfig 3 2 :=
  activePredecessorHostStep ring3 occupiedBefore p0

theorem occupied_predecessor_safe_abandon :
    LeaseSafe hTwo ring3 occupiedBefore.marked occupiedBefore.role /\
      ¬ CertifiedCommitAt hTwo ring3 abandonedAfter p1 /\
      (abandonedAfter.marked p1).history.state = .absent /\
      abandonedAfter.role p1 = .none /\
      LeaseSafe hTwo ring3 abandonedAfter.marked abandonedAfter.role := by
  decide

/-! ## Exact next-round obligation -/

/-- No grant/source premise is needed: the active writer only frames or erases
comparison state and lease ownership.  The next round should prove exactly this
global three-incident-cut preservation statement. -/
def ActiveReservationLeaseSafePreservationStatement : Prop :=
  forall {n psi : Nat} (hpsi : 0 < psi)
      (ring : DirectedRing n) (S : LeaseHostConfig n psi) (e : Fin n),
    LeaseSafe hpsi ring S.marked S.role ->
      LeaseSafe hpsi ring
        (activePredecessorHostStep ring S e).marked
        (activePredecessorHostStep ring S e).role

end BirthDoneLineageLeaseActiveReservation

#print axioms BirthDoneLineageLeaseActiveReservation.q11670_raw_candidate_still_unsafe
#print axioms BirthDoneLineageLeaseActiveReservation.q11670_unsafe_step_still_blocked
#print axioms BirthDoneLineageLeaseActiveReservation.q11670_active_writer_enables_certified_commit
#print axioms BirthDoneLineageLeaseActiveReservation.q11670_active_writer_then_commits_safely
#print axioms BirthDoneLineageLeaseActiveReservation.occupied_predecessor_safe_abandon
#print axioms BirthDoneLineageLeaseActiveReservation.ActiveReservationLeaseSafePreservationStatement
