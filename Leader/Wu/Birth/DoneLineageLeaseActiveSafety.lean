import Leader.Wu.Birth.DoneLineageLeaseActiveReservation


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace BirthDoneLineageLeaseActiveSafety


open PPLL PPLLRepair PPLLWallSweepRepair
open PPLLComparisonHistory PPLLWallSweepHistory
open BirthDoneLineageQuarantineDesign
open BirthDoneLineageLeaseTransitions
open BirthDoneLineageLeaseHostStep
open BirthDoneLineageLeaseActiveReservation


variable {n psi : Nat}


private instance instDecidableDoneHandoffGuardSafety
    (hpsi : 0 < psi) (l r : AgentState psi) :
    Decidable (DoneHandoffGuard hpsi l r) := by
  unfold DoneHandoffGuard
  infer_instance


private instance instDecidableDoneRoleReadySafety
    (hpsi : 0 < psi)
    (l r : MarkedAgentState n psi)
    (lrole rrole : LineageRole) :
    Decidable (DoneRoleReady hpsi l r lrole rrole) := by
  unfold DoneRoleReady
  infer_instance


private instance instDecidableRoleLineageSoundSafety
    (l r : MarkedAgentState n psi)
    (lrole rrole : LineageRole) :
    Decidable (RoleLineageSound l r lrole rrole) := by
  unfold RoleLineageSound
  infer_instance


private instance instDecidableLeaseCutInvariantSafety
    (hpsi : 0 < psi)
    (l r : MarkedAgentState n psi)
    (lrole rrole : LineageRole) :
    Decidable (LeaseCutInvariant hpsi l r lrole rrole) := by
  unfold LeaseCutInvariant DoneRoleReady RoleLineageSound
  infer_instance


private instance instDecidableLeaseSafeSafety
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (M : Fin n -> MarkedAgentState n psi)
    (role : Fin n -> LineageRole) :
    Decidable (LeaseSafe hpsi ring M role) := by
  unfold LeaseSafe
  dsimp only
  infer_instance


private theorem hTwo : 0 < 2 := by decide
private def ring2 : DirectedRing 2 := ⟨hTwo⟩
private def p0 : Fin 2 := 0
private def p1 : Fin 2 := 1


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


private def emptyHistory : LocalComparisonHistory 2 :=
  { state := .absent
    path := .absent
    path2 := .absent
    pCarry := .absent }


/-- Site 1 carries action 5.  Site 0 carries action 3, which Step 4 moves left
before Step 5 can move action 5 right on the reverse cut. -/
private def beforeMarked (i : Fin 2) : MarkedAgentState 2 2 :=
  if i = p0 then
    ⟨{ base2 1 .none with path2 := some ⟨0, 0, 0, 3⟩ }, emptyHistory⟩
  else
    ⟨{ base2 0 .CHECK_ready with path2 := some ⟨0, 0, 0, 5⟩ },
      emptyHistory⟩


private def beforeRole (i : Fin 2) : LineageRole :=
  if i = p1 then .predecessorPermit else .none


private def before : LeaseHostConfig 2 2 :=
  { marked := beforeMarked
    role := beforeRole }


private def after : LeaseHostConfig 2 2 :=
  activePredecessorHostStep ring2 before p0


/-- Both oriented cuts are safe before the active writer. -/
theorem counterexample_before_safe :
    LeaseSafe hTwo ring2 before.marked before.role := by
  decide


/-- The active writer takes its intended first branch and scrubs site 0. -/
theorem counterexample_active_writer_scrubs_p0 :
    (after.marked p0).concrete.state = .none /\
      (after.marked p0).concrete.path2 = none /\
      after.role p0 = .none /\
      after.marked p1 = before.marked p1 /\
      after.role p1 = .predecessorPermit := by
  decide


/-- Before the scrub, the reverse cut is not a live DONE handoff. -/
theorem counterexample_old_reverse_cut_not_live :
    let q := currentDoneCut hTwo
      (before.marked p1) (before.marked p0)
    ¬ DoneHandoffGuard hTwo q.1.concrete q.2.concrete := by
  decide


/-- Removing site 0's action-3 blocker exposes site 1's action 5. -/
theorem counterexample_new_reverse_cut_states :
    let q := currentDoneCut hTwo
      (after.marked p1) (after.marked p0)
    q.1.concrete.state = .CHECK_ready /\
      q.2.concrete.state = .depart := by
  decide


/-- Exactly the readiness half fails; lineage soundness is still vacuous
because the right role is `.none`. -/
theorem counterexample_failed_clause :
    let q := currentDoneCut hTwo
      (after.marked p1) (after.marked p0)
    ¬ DoneRoleReady hTwo q.1 q.2
        (after.role p1) (after.role p0) /\
      RoleLineageSound q.1 q.2
        (after.role p1) (after.role p0) := by
  decide


/-- Hence the active reservation step does not preserve `LeaseSafe`. -/
theorem counterexample_after_not_safe :
    ¬ LeaseSafe hTwo ring2 after.marked after.role := by
  decide


/-- The requested universal preservation statement is false. -/
theorem activeReservationLeaseSafePreservationStatement_false :
    ¬ ActiveReservationLeaseSafePreservationStatement := by
  intro hpres
  unfold ActiveReservationLeaseSafePreservationStatement at hpres
  have hs := hpres (n := 2) (psi := 2)
    hTwo ring2 before p0 counterexample_before_safe
  exact counterexample_after_not_safe hs


end BirthDoneLineageLeaseActiveSafety


#print axioms BirthDoneLineageLeaseActiveSafety.counterexample_before_safe
#print axioms BirthDoneLineageLeaseActiveSafety.counterexample_failed_clause
#print axioms BirthDoneLineageLeaseActiveSafety.counterexample_after_not_safe
#print axioms BirthDoneLineageLeaseActiveSafety.activeReservationLeaseSafePreservationStatement_false
