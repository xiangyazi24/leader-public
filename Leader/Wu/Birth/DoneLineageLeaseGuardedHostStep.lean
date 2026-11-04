import Leader.Wu.Birth.DoneLineageLeaseHostStep


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace BirthDoneLineageLeaseGuardedHostStep


open PPLL PPLLRepair PPLLWallSweepRepair
open PPLLComparisonHistory
open BirthDoneLineageQuarantineDesign
open BirthDoneLineageLeaseTransitions
open BirthDoneLineageLeaseHostStep


variable {n psi : Nat}


/-! ## Local decidability -/


private instance instDecidableDoneHandoffGuardGuarded
    (hpsi : 0 < psi) (l r : AgentState psi) :
    Decidable (DoneHandoffGuard hpsi l r) := by
  unfold DoneHandoffGuard
  infer_instance


private instance instDecidableComparisonNeutralGuarded
    (u : AgentState psi) : Decidable (ComparisonNeutral u) := by
  unfold ComparisonNeutral
  infer_instance


private instance instDecidableGrantPredecessorPermitReadyGuarded
    (l r : LineageCell psi) :
    Decidable (GrantPredecessorPermitReady l r) := by
  unfold GrantPredecessorPermitReady
  infer_instance


private instance instDecidableLeaseCutInvariantGuarded
    (hpsi : 0 < psi)
    (l r : MarkedAgentState n psi)
    (lrole rrole : LineageRole) :
    Decidable (LeaseCutInvariant hpsi l r lrole rrole) := by
  unfold LeaseCutInvariant DoneRoleReady RoleLineageSound
  infer_instance


private instance instDecidableLeaseCutAtGuarded
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (i : Fin n) :
    Decidable (LeaseCutAt hpsi ring S i) := by
  unfold LeaseCutAt
  dsimp only
  infer_instance


private instance instDecidableCommitIncomingGuarded
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    Decidable (CommitIncomingLeaseGuard hpsi ring S e) := by
  unfold CommitIncomingLeaseGuard
  infer_instance


private instance instDecidableScheduledGuarded
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    Decidable (ScheduledLeaseGuard hpsi ring S e) := by
  unfold ScheduledLeaseGuard
  infer_instance


private instance instDecidableRightIncidentGuarded
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    Decidable (RightIncidentLeaseGuard hpsi ring S e) := by
  unfold RightIncidentLeaseGuard
  infer_instance


private instance instDecidableGrantProducerGuarded
    (hpsi : 0 < psi)
    (l r : MarkedAgentState n psi)
    (lrole rrole : LineageRole) :
    Decidable (GrantProducerPremise hpsi l r lrole rrole) := by
  unfold GrantProducerPremise
  dsimp only
  unfold SameTrustedSource
  infer_instance


private instance instDecidableLeaseSafeGuarded
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (M : Fin n -> MarkedAgentState n psi)
    (role : Fin n -> LineageRole) :
    Decidable (LeaseSafe hpsi ring M role) := by
  unfold LeaseSafe
  dsimp only
  infer_instance


private instance instDecidableNoComparisonSourceGuarded
    (C : Fin n -> LineageCell psi) :
    Decidable (NoComparisonSource C) := by
  unfold NoComparisonSource
  infer_instance


/-! ## Exact local commit guard -/


/-- The constant-state predecessor reservation guard.  It predicts the adopted
host candidate on the scheduled pair and checks only the newly exposed incoming
cut `(left e,e)`.  No fifth lease value is introduced.


Unfolding this predicate gives exactly `DoneRoleReady ∧ RoleLineageSound` on
that predicted cut: the left-neighbour role must be a predecessor permit if the
DONE guard is live, and a permit/frontier pair must carry one trusted source. -/
def CommitLeftReservationGuard
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) : Prop :=
  let T := leaseHostStep hpsi ring S e
  LeaseCutAt hpsi ring T (ring.leftNeighbor e)


/-- This is exactly the missing incoming certificate. -/
theorem commitLeftReservationGuard_implies_commitIncomingLeaseGuard
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n)
    (h : CommitLeftReservationGuard hpsi ring S e) :
    CommitIncomingLeaseGuard hpsi ring S e := by
  exact h


/-- Local normal form of the guard.  The only extra lease datum read outside
`(e,right e)` is the role on the predecessor cut; source identity remains
proof-side in the already-existing marked history. -/
theorem commitLeftReservationGuard_local_form
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    CommitLeftReservationGuard hpsi ring S e <->
      let T := leaseHostStep hpsi ring S e
      let p := ring.leftNeighbor e
      let q := currentDoneCut hpsi
        (T.marked p) (T.marked (ring.rightNeighbor p))
      DoneRoleReady hpsi q.1 q.2
          (T.role p) (T.role (ring.rightNeighbor p)) /\
        RoleLineageSound q.1 q.2
          (T.role p) (T.role (ring.rightNeighbor p)) := by
  rfl


/-- A certified commit candidate is a live scheduled DONE cut whose old lease
certificate already holds.  Under `LeaseSafe` this is precisely the branch in
which `leasePairStep` reaches `commitFrontier`. -/
def CertifiedCommitAt
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) : Prop :=
  let j := ring.rightNeighbor e
  let q := currentDoneCut hpsi (S.marked e) (S.marked j)
  DoneHandoffGuard hpsi q.1.concrete q.2.concrete /\
    LeaseCutInvariant hpsi q.1 q.2 (S.role e) (S.role j)


private instance instDecidableCertifiedCommitAtGuarded
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    Decidable (CertifiedCommitAt hpsi ring S e) := by
  unfold CertifiedCommitAt
  dsimp only
  infer_instance


/-- Re-check the three and only three oriented cuts that can touch the two
changed endpoints.  The first conjunct is the new commit guard. -/
def IncidentClosureGuard
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) : Prop :=
  CommitLeftReservationGuard hpsi ring S e /\
    ScheduledLeaseGuard hpsi ring S e /\
    RightIncidentLeaseGuard hpsi ring S e


private instance instDecidableIncidentClosureGuarded
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    Decidable (IncidentClosureGuard hpsi ring S e) := by
  unfold IncidentClosureGuard CommitLeftReservationGuard
  infer_instance


/-- Guarded host step.  A candidate physical/lease row is committed only when
all three incident cuts certify in its predicted successor.  In particular a
certified DONE commit cannot execute without `CommitLeftReservationGuard`.
Failure of the guard frames the whole configuration. -/
def guardedLeaseHostStep
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    LeaseHostConfig n psi :=
  if IncidentClosureGuard hpsi ring S e then
    leaseHostStep hpsi ring S e
  else
    S


/-- A waiting certified commit is literally blocked by the new guard. -/
theorem certified_commit_blocked_of_left_guard_failure
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n)
    (_hcommit : CertifiedCommitAt hpsi ring S e)
    (hleft : ¬ CommitLeftReservationGuard hpsi ring S e) :
    guardedLeaseHostStep hpsi ring S e = S := by
  simp [guardedLeaseHostStep, IncidentClosureGuard, hleft]


/-! ## Ring locality -/


private theorem leftNeighbor_rightNeighbor_local
    (ring : DirectedRing n) (i : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi]
    have heq : i.val + 1 + n - 1 = n + i.val := by omega
    rw [heq, add_self_mod, Nat.mod_eq_of_lt i.isLt]
  · have hie : i.val + 1 = n := by omega
    rw [hie, Nat.mod_self]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    omega


private theorem rightNeighbor_injective_local
    (ring : DirectedRing n) : Function.Injective ring.rightNeighbor := by
  intro a b hab
  have h := congrArg ring.leftNeighbor hab
  simpa only [leftNeighbor_rightNeighbor_local] using h


private theorem leaseHostStep_marked_other
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    (leaseHostStep hpsi ring S e).marked i = S.marked i := by
  change
    (if i = e then
      (leaseMarkedPair hpsi
        (S.marked e) (S.marked (ring.rightNeighbor e))
        (S.role e) (S.role (ring.rightNeighbor e))).1
    else if i = ring.rightNeighbor e then
      (leaseMarkedPair hpsi
        (S.marked e) (S.marked (ring.rightNeighbor e))
        (S.role e) (S.role (ring.rightNeighbor e))).2
    else
      S.marked i) = S.marked i
  simp only [hi, hj, if_false]


private theorem leaseHostStep_role_other
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    (leaseHostStep hpsi ring S e).role i = S.role i := by
  change
    (if i = e then
      (leaseRolePair hpsi
        (S.marked e) (S.marked (ring.rightNeighbor e))
        (S.role e) (S.role (ring.rightNeighbor e))).1
    else if i = ring.rightNeighbor e then
      (leaseRolePair hpsi
        (S.marked e) (S.marked (ring.rightNeighbor e))
        (S.role e) (S.role (ring.rightNeighbor e))).2
    else
      S.role i) = S.role i
  simp only [hi, hj, if_false]


/-- The guarded host step preserves the all-edge lease invariant on every
nonempty directed ring.  The grant-producer premise is retained in the public
contract requested by R4.  The present proof is stronger than that premise:
`IncidentClosureGuard` directly certifies the exact post-step cuts, so no
producer fact is consumed in the proof. -/
theorem guardedLeaseHostStep_preserves_leaseSafe
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n)
    (hsafe : LeaseSafe hpsi ring S.marked S.role)
    (_hgrant : forall i : Fin n,
      GrantProducerPremise hpsi
        (S.marked i) (S.marked (ring.rightNeighbor i))
        (S.role i) (S.role (ring.rightNeighbor i))) :
    LeaseSafe hpsi ring
      (guardedLeaseHostStep hpsi ring S e).marked
      (guardedLeaseHostStep hpsi ring S e).role := by
  unfold guardedLeaseHostStep
  split
  next hclosure =>
    have hcuts := hclosure
    unfold IncidentClosureGuard at hcuts
    unfold LeaseSafe
    intro i
    change LeaseCutAt hpsi ring (leaseHostStep hpsi ring S e) i
    by_cases hleft : i = ring.leftNeighbor e
    · subst i
      exact hcuts.1
    · by_cases he : i = e
      · subst i
        exact hcuts.2.1
      · by_cases hright : i = ring.rightNeighbor e
        · subst i
          exact hcuts.2.2
        · have hri_e : ring.rightNeighbor i ≠ e := by
            intro h
            apply hleft
            calc
              i = ring.leftNeighbor (ring.rightNeighbor i) :=
                (leftNeighbor_rightNeighbor_local ring i).symm
              _ = ring.leftNeighbor e := congrArg ring.leftNeighbor h
          have hri_right :
              ring.rightNeighbor i ≠ ring.rightNeighbor e := by
            intro h
            exact he (rightNeighbor_injective_local ring h)
          have hmi := leaseHostStep_marked_other
            hpsi ring S e i he hright
          have hmr := leaseHostStep_marked_other
            hpsi ring S e (ring.rightNeighbor i) hri_e hri_right
          have hri := leaseHostStep_role_other
            hpsi ring S e i he hright
          have hrr := leaseHostStep_role_other
            hpsi ring S e (ring.rightNeighbor i) hri_e hri_right
          have hold : LeaseCutAt hpsi ring S i := by
            exact hsafe i
          unfold LeaseCutAt at hold ⊢
          dsimp only at hold ⊢
          rw [hmi, hmr, hri, hrr]
          exact hold
  next _ =>
    exact hsafe


/-! ## The fixture, now blocked -/


private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide


private def ring3 : DirectedRing 3 := ⟨hThree⟩


private def p0 : Fin 3 := 0
private def p1 : Fin 3 := 1
private def p2 : Fin 3 := 2


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
  { marked := blockedMarked
    role := blockedRole }


/-- The original assumptions still hold, including all grant-producer
premises (which are vacuous on this fixture). -/
theorem q11670_blocked_before_safe :
    LeaseSafe hTwo ring3 blockedBefore.marked blockedBefore.role := by
  decide


theorem q11670_blocked_grant_producers :
    forall e : Fin 3,
      GrantProducerPremise hTwo
        (blockedBefore.marked e)
        (blockedBefore.marked (ring3.rightNeighbor e))
        (blockedBefore.role e)
        (blockedBefore.role (ring3.rightNeighbor e)) := by
  decide


private instance instDecidableCommitLeftReservationGuarded
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    Decidable (CommitLeftReservationGuard hpsi ring S e) := by
  unfold CommitLeftReservationGuard
  dsimp only
  infer_instance

theorem q11670_certified_commit_waits :
    CertifiedCommitAt hTwo ring3 blockedBefore p1 /\
      ¬ CommitLeftReservationGuard hTwo ring3 blockedBefore p1 := by
  decide


/-- Required R4 regression: the old bad commit is blocked by the guarded host. -/
theorem q11670_counterexample_now_blocked :
    forall i : Fin 3,
      (guardedLeaseHostStep hTwo ring3 blockedBefore p1).marked i =
          blockedBefore.marked i /\
        (guardedLeaseHostStep hTwo ring3 blockedBefore p1).role i =
          blockedBefore.role i := by
  decide


/-- A role-only reservation is insufficient.  Giving site 0 the physical
`predecessorPermit` does not repair the distinct trusted sources 0 and 1. -/
private def roleOnlyReserved : LeaseHostConfig 3 2 :=
  { marked := blockedBefore.marked
    role := fun i =>
      if i = p0 then .predecessorPermit else blockedBefore.role i }


theorem q11670_role_only_reservation_still_fails :
    roleOnlyReserved.role p0 = .predecessorPermit /\
      CertifiedCommitAt hTwo ring3 roleOnlyReserved p1 /\
      ¬ CommitLeftReservationGuard hTwo ring3 roleOnlyReserved p1 := by
  decide


/-- In fact every possible scheduled edge stutters on the literal fixture. -/
theorem q11670_every_guarded_edge_stutters :
    forall e i : Fin 3,
      (guardedLeaseHostStep hTwo ring3 blockedBefore e).marked i =
          blockedBefore.marked i /\
        (guardedLeaseHostStep hTwo ring3 blockedBefore e).role i =
          blockedBefore.role i := by
  decide


private theorem leaseHostConfig_ext
    (A B : LeaseHostConfig n psi)
    (hm : forall i, A.marked i = B.marked i)
    (hr : forall i, A.role i = B.role i) : A = B := by
  cases A with
  | mk Am Ar =>
      cases B with
      | mk Bm Br =>
          dsimp only at hm hr
          have hm' : Am = Bm := by
            funext i
            exact hm i
          have hr' : Ar = Br := by
            funext i
            exact hr i
          cases hm'
          cases hr'
          rfl


theorem q11670_every_guarded_edge_eq (e : Fin 3) :
    guardedLeaseHostStep hTwo ring3 blockedBefore e = blockedBefore := by
  apply leaseHostConfig_ext
  · intro i
    exact (q11670_every_guarded_edge_stutters e i).1
  · intro i
    exact (q11670_every_guarded_edge_stutters e i).2


/-- Execute a finite deterministic schedule under the guarded lease host. -/
def runGuardedLeaseSchedule
    (hpsi : 0 < psi) (ring : DirectedRing n) :
    LeaseHostConfig n psi -> List (Fin n) -> LeaseHostConfig n psi
  | S, [] => S
  | S, e :: rest =>
      runGuardedLeaseSchedule hpsi ring
        (guardedLeaseHostStep hpsi ring S e) rest


theorem q11670_every_finite_schedule_stuck
    (schedule : List (Fin 3)) :
    runGuardedLeaseSchedule hTwo ring3 blockedBefore schedule =
      blockedBefore := by
  have h0 :
      guardedLeaseHostStep hTwo ring3 blockedBefore p0 = blockedBefore :=
    q11670_every_guarded_edge_eq p0
  have h1 :
      guardedLeaseHostStep hTwo ring3 blockedBefore p1 = blockedBefore :=
    q11670_every_guarded_edge_eq p1
  have h2 :
      guardedLeaseHostStep hTwo ring3 blockedBefore p2 = blockedBefore :=
    q11670_every_guarded_edge_eq p2
  induction schedule with
  | nil => rfl
  | cons e rest ih =>
      have hstep :
          guardedLeaseHostStep hTwo ring3 blockedBefore e = blockedBefore := by
        cases e using Fin.cases with
        | zero =>
            change guardedLeaseHostStep hTwo ring3 blockedBefore p0 = blockedBefore
            exact h0
        | succ e =>
            cases e using Fin.cases with
            | zero =>
                change guardedLeaseHostStep hTwo ring3 blockedBefore p1 = blockedBefore
                exact h1
            | succ e =>
                cases e using Fin.cases with
                | zero =>
                    change guardedLeaseHostStep hTwo ring3 blockedBefore p2 = blockedBefore
                    exact h2
                | succ e =>
                    exact Fin.elim0 e
      calc
        runGuardedLeaseSchedule hTwo ring3 blockedBefore (e :: rest) =
            runGuardedLeaseSchedule hTwo ring3
              (guardedLeaseHostStep hTwo ring3 blockedBefore e) rest := rfl
        _ = runGuardedLeaseSchedule hTwo ring3 blockedBefore rest := by
          rw [hstep]
        _ = blockedBefore := ih


private def blockedCells (i : Fin 3) : LineageCell 2 :=
  { concrete := (blockedBefore.marked i).concrete
    role := blockedBefore.role i }


/-- The sourceless escape is unavailable: this deadlock still contains
active comparison state. -/
theorem q11670_deadlock_not_sourceless :
    ¬ NoComparisonSource blockedCells := by
  decide


/-- Formal R4 liveness verdict: a certified commit waits forever under the
passive four-state guard, every finite schedule is trapped, and the state is not
sourceless. -/
theorem four_state_passive_guard_liveness_fails :
    CertifiedCommitAt hTwo ring3 blockedBefore p1 /\
      ¬ CommitLeftReservationGuard hTwo ring3 blockedBefore p1 /\
      (forall schedule : List (Fin 3),
        runGuardedLeaseSchedule hTwo ring3 blockedBefore schedule =
          blockedBefore) /\
      ¬ NoComparisonSource blockedCells := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact q11670_certified_commit_waits.1
  · exact q11670_certified_commit_waits.2
  · exact q11670_every_finite_schedule_stuck
  · exact q11670_deadlock_not_sourceless


end BirthDoneLineageLeaseGuardedHostStep


#print axioms BirthDoneLineageLeaseGuardedHostStep.commitLeftReservationGuard_local_form
#print axioms BirthDoneLineageLeaseGuardedHostStep.guardedLeaseHostStep_preserves_leaseSafe
#print axioms BirthDoneLineageLeaseGuardedHostStep.q11670_counterexample_now_blocked
#print axioms BirthDoneLineageLeaseGuardedHostStep.q11670_role_only_reservation_still_fails
#print axioms BirthDoneLineageLeaseGuardedHostStep.q11670_every_finite_schedule_stuck
#print axioms BirthDoneLineageLeaseGuardedHostStep.four_state_passive_guard_liveness_fails
