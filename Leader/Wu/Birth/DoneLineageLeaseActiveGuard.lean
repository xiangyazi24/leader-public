import Leader.Wu.Birth.DoneLineageLeaseActiveSafety

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthDoneLineageLeaseActiveGuard

open PPLL PPLLRepair PPLLWallSweepRepair
open PPLLComparisonHistory PPLLWallSweepHistory
open BirthDoneLineageQuarantineDesign
open BirthDoneLineageLeaseTransitions
open BirthDoneLineageLeaseHostStep
open BirthDoneLineageLeaseActiveReservation

variable {n psi : Nat}

private instance instDecidableLeaseCutInvariantGuard
    (hpsi : 0 < psi) (l r : MarkedAgentState n psi)
    (lrole rrole : LineageRole) :
    Decidable (LeaseCutInvariant hpsi l r lrole rrole) := by
  unfold LeaseCutInvariant DoneRoleReady RoleLineageSound
  infer_instance

private instance instDecidableLeaseCutAtGuard
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (i : Fin n) :
    Decidable (LeaseCutAt hpsi ring S i) := by
  unfold LeaseCutAt
  dsimp only
  infer_instance

private instance instDecidableLeaseSafeGuard
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (M : Fin n -> MarkedAgentState n psi)
    (role : Fin n -> LineageRole) :
    Decidable (LeaseSafe hpsi ring M role) := by
  unfold LeaseSafe
  dsimp only
  infer_instance

/-- Small anti-unmask guard: check only the incoming cut after the predicted
active predecessor write. -/
def ActiveReverseCutGuard
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) : Prop :=
  let T := activePredecessorHostStep ring S e
  LeaseCutAt hpsi ring T (ring.leftNeighbor e)

private instance instDecidableActiveReverseCutGuard
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    Decidable (ActiveReverseCutGuard hpsi ring S e) := by
  unfold ActiveReverseCutGuard
  infer_instance

/-- Whole-step closure: the reverse guard plus the other two incident cuts. -/
def ActiveIncidentClosureGuard
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) : Prop :=
  ActiveReverseCutGuard hpsi ring S e /\
    (let T := activePredecessorHostStep ring S e
     LeaseCutAt hpsi ring T e /\
       LeaseCutAt hpsi ring T (ring.rightNeighbor e))

private instance instDecidableActiveIncidentClosureGuard
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    Decidable (ActiveIncidentClosureGuard hpsi ring S e) := by
  unfold ActiveIncidentClosureGuard
  infer_instance

/-- Refuse an active scrub unless all changed incident cuts remain certified. -/
def guardedActivePredecessorHostStep
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    LeaseHostConfig n psi :=
  if ActiveIncidentClosureGuard hpsi ring S e then
    activePredecessorHostStep ring S e
  else S

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

private theorem activeHostStep_marked_other
    (ring : DirectedRing n) (S : LeaseHostConfig n psi)
    (e i : Fin n) (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    (activePredecessorHostStep ring S e).marked i = S.marked i := by
  change
    (if i = e then
      (activePredecessorMarkedPair
        (S.marked e) (S.marked (ring.rightNeighbor e))
        (S.role e) (S.role (ring.rightNeighbor e))).1
    else if i = ring.rightNeighbor e then
      (activePredecessorMarkedPair
        (S.marked e) (S.marked (ring.rightNeighbor e))
        (S.role e) (S.role (ring.rightNeighbor e))).2
    else S.marked i) = S.marked i
  simp only [hi, hj, if_false]

private theorem activeHostStep_role_other
    (ring : DirectedRing n) (S : LeaseHostConfig n psi)
    (e i : Fin n) (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    (activePredecessorHostStep ring S e).role i = S.role i := by
  change
    (if i = e then
      (activePredecessorRolePair
        (S.role e) (S.role (ring.rightNeighbor e))).1
    else if i = ring.rightNeighbor e then
      (activePredecessorRolePair
        (S.role e) (S.role (ring.rightNeighbor e))).2
    else S.role i) = S.role i
  simp only [hi, hj, if_false]

/-- The guarded active writer preserves the all-edge lease invariant. -/
theorem guardedActivePredecessorHostStep_preserves_leaseSafe
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n)
    (hsafe : LeaseSafe hpsi ring S.marked S.role) :
    LeaseSafe hpsi ring
      (guardedActivePredecessorHostStep hpsi ring S e).marked
      (guardedActivePredecessorHostStep hpsi ring S e).role := by
  unfold guardedActivePredecessorHostStep
  split
  next hclosure =>
    have hcuts := hclosure
    unfold ActiveIncidentClosureGuard ActiveReverseCutGuard at hcuts
    dsimp only at hcuts
    unfold LeaseSafe
    intro i
    change LeaseCutAt hpsi ring (activePredecessorHostStep ring S e) i
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
          have hmi := activeHostStep_marked_other ring S e i he hright
          have hmr := activeHostStep_marked_other
            ring S e (ring.rightNeighbor i) hri_e hri_right
          have hri := activeHostStep_role_other ring S e i he hright
          have hrr := activeHostStep_role_other
            ring S e (ring.rightNeighbor i) hri_e hri_right
          have hold : LeaseCutAt hpsi ring S i := by exact hsafe i
          unfold LeaseCutAt at hold ⊢
          dsimp only at hold ⊢
          rw [hmi, hmr, hri, hrr]
          exact hold
  next _ =>
    exact hsafe

private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide
private def ring2 : DirectedRing 2 := ⟨hTwo⟩
private def ring3 : DirectedRing 3 := ⟨hThree⟩
private def a0 : Fin 2 := 0
private def a1 : Fin 2 := 1
private def b0 : Fin 3 := 0
private def b1 : Fin 3 := 1
private def b2 : Fin 3 := 2

private def base2 (label : Fin 2) (state : MainState) : AgentState 2 :=
  { leader := false, probe := false, phase := false, bit := false, wait := true,
    state := state, path := .bot, reset := false, carry := false, count := 0,
    label := label, h_field := false, path2 := none, path3 := none,
    path4 := none, path5 := none, p := false, p_carry := false,
    reset_cmd := false, echo := false, signal_B := 0, bullet := 0,
    shield := true, write_state := .none, write := .none, last := false,
    last_set := false, last_unset := false, b_carry := false, gen_ws := false,
    ws_echo := false, signal_ws := false }

private def emptyHistory2 : LocalComparisonHistory 2 :=
  { state := .absent, path := .absent, path2 := .absent, pCarry := .absent }

private def badMarked (i : Fin 2) : MarkedAgentState 2 2 :=
  if i = a0 then
    ⟨{ base2 1 .none with path2 := some ⟨0, 0, 0, 3⟩ }, emptyHistory2⟩
  else
    ⟨{ base2 0 .CHECK_ready with path2 := some ⟨0, 0, 0, 5⟩ }, emptyHistory2⟩
private def badRole (i : Fin 2) : LineageRole :=
  if i = a1 then .predecessorPermit else .none
private def badBefore : LeaseHostConfig 2 2 :=
  { marked := badMarked, role := badRole }
private def badGuarded : LeaseHostConfig 2 2 :=
  guardedActivePredecessorHostStep hTwo ring2 badBefore a0

/-- The counterexample is refused at the reverse guard, so the guarded result frames and is safe. -/
theorem q11791_counterexample_blocked_and_safe :
    ¬ ActiveReverseCutGuard hTwo ring2 badBefore a0 /\
      ¬ ActiveIncidentClosureGuard hTwo ring2 badBefore a0 /\
      badGuarded.marked a0 = badBefore.marked a0 /\
      badGuarded.marked a1 = badBefore.marked a1 /\
      LeaseSafe hTwo ring2 badGuarded.marked badGuarded.role := by
  decide

private def trustedHistory3 (source : Fin 3) : LocalComparisonHistory 3 :=
  { state := .trusted source, path := .absent,
    path2 := .absent, pCarry := .absent }
private def blockedMarked3 (i : Fin 3) : MarkedAgentState 3 2 :=
  if i = b0 then ⟨base2 0 .CHECK_ready, trustedHistory3 b0⟩
  else if i = b1 then ⟨base2 0 .CHECK_ready, trustedHistory3 b1⟩
  else ⟨base2 1 .depart, trustedHistory3 b1⟩
private def blockedRole3 (i : Fin 3) : LineageRole :=
  if i = b1 then .predecessorPermit
  else if i = b2 then .frontier else .none
private def blockedBefore3 : LeaseHostConfig 3 2 :=
  { marked := blockedMarked3, role := blockedRole3 }
private def repaired3 : LeaseHostConfig 3 2 :=
  guardedActivePredecessorHostStep hTwo ring3 blockedBefore3 b0
private def committed3 : LeaseHostConfig 3 2 :=
  BirthDoneLineageLeaseActiveReservation.guardedLeaseHostStep
    hTwo ring3 repaired3 b1

/-- The deadlock still repairs in one active write and commits on the second step. -/
theorem q11670_deadlock_still_resolves :
    ActiveIncidentClosureGuard hTwo ring3 blockedBefore3 b0 /\
      (repaired3.marked b0).concrete.state = .none /\
      repaired3.role b0 = .none /\
      LeaseSafe hTwo ring3 repaired3.marked repaired3.role /\
      (committed3.marked b1).concrete.state = .depart /\
      committed3.role b1 = .frontier /\
      committed3.role b2 = .none /\
      LeaseSafe hTwo ring3 committed3.marked committed3.role := by
  decide

private def occupiedRole3 (i : Fin 3) : LineageRole :=
  if i = b0 then .sourceArmed else blockedRole3 i
private def occupiedBefore3 : LeaseHostConfig 3 2 :=
  { marked := blockedMarked3, role := occupiedRole3 }
private def abandoned3 : LeaseHostConfig 3 2 :=
  guardedActivePredecessorHostStep hTwo ring3 occupiedBefore3 b0

/-- Lease-owned predecessor: the permit endpoint is still scrubbed and abandoned safely. -/
theorem occupied_predecessor_abandon_still_holds :
    ActiveIncidentClosureGuard hTwo ring3 occupiedBefore3 b0 /\
      (abandoned3.marked b1).history.state = .absent /\
      abandoned3.role b1 = .none /\
      LeaseSafe hTwo ring3 abandoned3.marked abandoned3.role := by
  decide

end BirthDoneLineageLeaseActiveGuard

#print axioms BirthDoneLineageLeaseActiveGuard.guardedActivePredecessorHostStep_preserves_leaseSafe
#print axioms BirthDoneLineageLeaseActiveGuard.q11791_counterexample_blocked_and_safe
#print axioms BirthDoneLineageLeaseActiveGuard.q11670_deadlock_still_resolves
#print axioms BirthDoneLineageLeaseActiveGuard.occupied_predecessor_abandon_still_holds
