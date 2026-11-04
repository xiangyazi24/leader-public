import Leader.Wu.Elimination.LDSinkTwoGapPhysPortSpec

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkProtectedAbsorption LDTwoGapFrame
open LDSinkTwoGapNoResetKernel LDSinkTwoGapEntrance LDSinkTwoGapDeletionWired
open LDSinkTwoGapReachInvariant LDSinkTwoGapPhysPortSpecInstance

namespace LDSinkTwoGapRaceSupportResolution

/-!
The current `SecondSupport` seed is every `GapPair`, before any physical
race entrance has been established.  Its deterministic second-success
requirement is already impossible at depth one: a bullet-free seed can
take any first edge, and no next edge deletes a tagged leader.  This file
uses the exact `sinkKernelC` transition reached by `attemptStepConf`.
-/

/-- A five-cell ring with leaders at 0, 2, and 4 gives two legal length-two
gaps.  The remaining edge is outside both gap interiors. -/
def coldFrame : TwoGapFrame 5 where
  recovery :=
    { ring := ⟨by decide⟩, low := 0, d := 2,
      hd := by decide, hdn := by decide }
  attack :=
    { ring := ⟨by decide⟩, low := 2, d := 2,
      hd := by decide, hdn := by decide }
  shared := by decide
  length_lt := by decide

theorem coldHPsi : (1 : Nat) > 0 := by decide

/-- Unused protocol fields are fixed to their declared zero/empty values;
the three race fields start with no signal, no bullet, and no shield. -/
def coldFollower : AgentState 1 where
  leader := false
  probe := false
  phase := false
  bit := false
  wait := false
  state := .none
  path := .bot
  reset := false
  carry := false
  count := 0
  label := 0
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
  shield := false
  write_state := .none
  write := .none
  last := false
  last_set := false
  last_unset := false
  b_carry := false
  gen_ws := false
  ws_echo := false
  signal_ws := false

/-- The exact cold configuration, with the intended three leaders. -/
def coldConf (i : Fin 5) : AgentState 1 :=
  { coldFollower with leader := i.val == 0 || i.val == 2 || i.val == 4 }

def coldState : AState 5 1 := ⟨coldConf, .transit⟩

private theorem cold_recovery_invariant :
    GapInvariant coldHPsi coldFrame.recovery coldConf := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor <;> decide
  · intro k hk hkd
    have hk1 : k = 1 := by change k < 2 at hkd; omega
    subst k
    decide
  · intro k hk
    have hk01 : k = 0 ∨ k = 1 := by change k < 2 at hk; omega
    rcases hk01 with hk0 | hk1 <;> subst k <;> decide
  · intro k j hk hkd hbullet hkj hjd
    exact (hbullet rfl).elim

private theorem cold_attack_invariant :
    GapInvariant coldHPsi coldFrame.attack coldConf := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor <;> decide
  · intro k hk hkd
    have hk1 : k = 1 := by change k < 2 at hkd; omega
    subst k
    decide
  · intro k hk
    have hk01 : k = 0 ∨ k = 1 := by change k < 2 at hk; omega
    rcases hk01 with hk0 | hk1 <;> subst k <;> decide
  · intro k j hk hkd hbullet hkj hjd
    exact (hbullet rfl).elim

/-- The counterexample seed satisfies both actual gap invariants, including
label alignment and the bullet/signal order predicate. -/
theorem cold_gapPair : GapPair coldHPsi coldFrame coldState :=
  ⟨cold_recovery_invariant, cold_attack_invariant⟩

/-- Exact finite kernel check: every first scheduler edge preserves all
leader bits in the cold configuration. -/
theorem cold_one_step_leaders : ∀ e v : Fin 5,
    (sinkStepC coldHPsi coldFrame.attack coldConf e v).leader =
      (coldConf v).leader := by
  decide

/-- Exact finite kernel check: every two-edge word preserves all leader
bits.  FIRE may produce a bullet on the second edge, but MOVE cannot yet
bring that new bullet into a victim. -/
theorem cold_two_step_leaders : ∀ e f v : Fin 5,
    (sinkStepC coldHPsi coldFrame.attack
      (sinkStepC coldHPsi coldFrame.attack coldConf e) f v).leader =
      (coldConf v).leader := by
  decide

private theorem cold_not_success : ¬ NoResetSuccess coldFrame coldConf := by
  unfold NoResetSuccess EndpointDeleted
  decide

/-- No first edge succeeds, so every proposed `firstGood` really enters
the inductively defined second support at this seed. -/
theorem cold_first_not_success (e : Fin 5) :
    ¬ NoResetSuccess coldFrame (attemptStepConf coldHPsi coldFrame coldState e) := by
  rw [attemptStepConf_eq_sinkStepC]
  change ¬ NoResetSuccess coldFrame (sinkStepC coldHPsi coldFrame.attack coldConf e)
  simpa only [NoResetSuccess, EndpointDeleted, cold_one_step_leaders] using
    cold_not_success

/-- The second support contains a state with no successful physical edge,
for every possible first selector.  This is a reachable-support witness,
not merely a raw malformed state. -/
theorem cold_supported_no_success
    (firstGood : AState 5 1 → Fin 5) :
    let b := postState coldHPsi coldFrame coldState (firstGood coldState)
    SecondSupport coldHPsi coldFrame firstGood b ∧
      ∀ e : Fin 5, ¬ NoResetSuccess coldFrame
        (attemptStepConf coldHPsi coldFrame b e) := by
  dsimp only
  constructor
  · exact .enter coldState cold_gapPair
      (cold_first_not_success (firstGood coldState))
  · intro e
    rw [attemptStepConf_eq_sinkStepC]
    change ¬ NoResetSuccess coldFrame
      (sinkStepC coldHPsi coldFrame.attack
        (attemptStepConf coldHPsi coldFrame coldState (firstGood coldState)) e)
    rw [attemptStepConf_eq_sinkStepC]
    change ¬ NoResetSuccess coldFrame
      (sinkStepC coldHPsi coldFrame.attack
        (sinkStepC coldHPsi coldFrame.attack coldConf (firstGood coldState)) e)
    simpa only [NoResetSuccess, EndpointDeleted, cold_two_step_leaders] using
      cold_not_success

/-- The existing deterministic race port interface has no instance for a
legal frame.  Consequently a universally instantiated theorem using this
interface cannot establish the physical deletion theorem. -/
theorem no_racePortResidual :
    ¬ Nonempty (RacePortResidual coldHPsi coldFrame) := by
  rintro ⟨H⟩
  let b := postState coldHPsi coldFrame coldState (H.firstGood coldState)
  have hb := cold_supported_no_success H.firstGood
  exact hb.2 (H.secondGood b) (H.success b hb.1)

/-! ## Nonempty physical entrance for the corrected protected race -/

/-- A parked live bullet at cell 3 faces the shared leader at cell 2, whose
recovery signal has arrived.  This is a real `GapPair ∧ RaceReady` state. -/
def readyConf (i : Fin 5) : AgentState 1 :=
  if i.val = 2 then { coldConf i with signal_B := 1, shield := true }
  else if i.val = 3 then { coldConf i with bullet := 2 }
  else coldConf i

def readyState : AState 5 1 := ⟨readyConf, .parked⟩

private theorem ready_recovery_invariant :
    GapInvariant coldHPsi coldFrame.recovery readyConf := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor <;> decide
  · intro k hk hkd
    have hk1 : k = 1 := by change k < 2 at hkd; omega
    subst k
    decide
  · intro k hk
    have hk01 : k = 0 ∨ k = 1 := by change k < 2 at hk; omega
    rcases hk01 with hk0 | hk1 <;> subst k <;> decide
  · intro k j hk hkd hbullet hkj hjd
    have hk12 : k = 1 ∨ k = 2 := by change k ≤ 2 at hkd; omega
    rcases hk12 with hk1 | hk2 <;> subst k <;>
      exact (hbullet (by decide)).elim

private theorem ready_attack_invariant :
    GapInvariant coldHPsi coldFrame.attack readyConf := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor <;> decide
  · intro k hk hkd
    have hk1 : k = 1 := by change k < 2 at hkd; omega
    subst k
    decide
  · intro k hk
    have hk01 : k = 0 ∨ k = 1 := by change k < 2 at hk; omega
    rcases hk01 with hk0 | hk1 <;> subst k <;> decide
  · intro k j hk hkd hbullet hkj hjd
    have hj12 : j = 1 ∨ j = 2 := by change j ≤ 2 at hjd; omega
    rcases hj12 with hj1 | hj2 <;> subst j <;> decide

/-- The corrected physical race domain is inhabited, with all gap and
entrance predicates checked against one complete concrete configuration. -/
theorem ready_gapPair_raceReady :
    GapPair coldHPsi coldFrame readyState ∧ RaceReady coldFrame readyState.conf := by
  refine ⟨⟨ready_recovery_invariant, ready_attack_invariant⟩, ?_, ?_, ?_⟩
  · decide
  · decide
  · intro k hk hkd
    have hk12 : k = 1 ∨ k = 2 := by change k ≤ 2 at hkd; omega
    rcases hk12 with hk1 | hk2 <;> subst k <;> decide

/-- Concrete confirmation of the corrected event order: edge 1 prepares
the shared victim as responder, and edge 2 deletes it on the next step. -/
theorem ready_prepare_delete :
    (sinkStepC coldHPsi coldFrame.attack
      (sinkStepC coldHPsi coldFrame.attack readyConf 1) 2 2).leader = false := by
  decide

/-- Reversing the first event lets FIRE re-shield the victim; C then absorbs
the parked live bullet.  This refutes treating the attack edge as the
favorable first arrival at this entrance. -/
theorem ready_attack_first_absorbs :
    let C := sinkStepC coldHPsi coldFrame.attack readyConf 2
    (C 2).leader = true ∧ (C 2).shield = true ∧ (C 3).bullet = (0 : Fin 3) := by
  decide

/-! ## The inherited entrance potential also fails on the closed gap domain -/

/-- The attack gap is clean and ready to create its next shot, but the old
ghost phase is still parked.  No one-edge successor has yet parked a live
attack bullet. -/
def renewalConf (i : Fin 5) : AgentState 1 :=
  { coldConf i with signal_B := if i.val = 4 then 1 else 0 }

def renewalState : AState 5 1 := ⟨renewalConf, .parked⟩

/-- This renewal state is legal even under both gap invariants. -/
theorem renewal_gapPair : GapPair coldHPsi coldFrame renewalState := by
  constructor
  · exact ⟨cold_recovery_invariant.1, cold_recovery_invariant.2.1,
      cold_recovery_invariant.2.2.1,
      fun _ _ _ _ hb _ _ => (hb rfl).elim⟩
  · exact ⟨cold_attack_invariant.1, cold_attack_invariant.2.1,
      cold_attack_invariant.2.2.1,
      fun _ _ _ _ hb _ _ => (hb rfl).elim⟩

private theorem renewal_attack_clean : CleanReady coldFrame.attack renewalConf := by
  constructor
  · decide
  · intro k _ _
    rfl

/-- The inherited rank has already spent all phase debt and is exactly one
at a state that still needs a fresh physical shot. -/
theorem renewal_rank_one : R coldFrame renewalState = 1 := by
  have hd : LDSinkGapDoneInvariant.GapDoneC coldFrame.attack renewalConf :=
    .inl renewal_attack_clean
  simp [R, phaseDebtA, W, renewalState, LDSinkGapServiceRank.gapWC, hd]

private theorem renewal_one_step_fields : ∀ e : Fin 5,
    (sinkStepC coldHPsi coldFrame.attack renewalConf e 3).bullet ≠ (2 : Fin 3) ∧
      ∀ v : Fin 5,
        (sinkStepC coldHPsi coldFrame.attack renewalConf e v).leader =
          (coldConf v).leader := by
  decide

/-- All five exact physical interactions stay in the entrance process:
none deletes a tagged leader or produces the parked live shot. -/
theorem renewal_entrance_active (e : Fin 5) :
    entranceStep coldHPsi coldFrame renewalState e =
      .active (postState coldHPsi coldFrame renewalState e) := by
  classical
  have hn : ¬ EntranceSuccess coldFrame
      (attemptStepConf coldHPsi coldFrame renewalState e) := by
    rw [attemptStepConf_eq_sinkStepC]
    change ¬ EntranceSuccess coldFrame
      (sinkStepC coldHPsi coldFrame.attack renewalConf e)
    intro hs
    rcases hs with hr | hd
    · exact (renewal_one_step_fields e).1 hr.1
    · apply cold_not_success
      simpa only [NoResetSuccess, EndpointDeleted, (renewal_one_step_fields e).2] using hd
  rw [entrance_normal_form, if_neg hn]

/-- Restricting the inherited Bellman row to `GapPair` does not repair it.
At this concrete seed the old potential is 5, every active child costs at
least 5, and the additional one-step charge forces 30 ≤ 25. -/
theorem no_gapPair_entrance_bellman_row :
    ¬ (∀ b : AState 5 1, GapPair coldHPsi coldFrame b →
      1 * 5 + (List.ofFn (fun e : Fin 5 =>
        entrancePotential coldFrame (entranceStep coldHPsi coldFrame b e))).sum ≤
          5 * entrancePotential coldFrame (.active b)) := by
  intro H
  have hstep := H renewalState renewal_gapPair
  have hpositive : ∀ e : Fin 5, 5 ≤
      entrancePotential coldFrame (entranceStep coldHPsi coldFrame renewalState e) := by
    intro e
    rw [renewal_entrance_active]
    change 5 ≤ 5 * R coldFrame (postState coldHPsi coldFrame renewalState e)
    have hpos := R_pos coldFrame (postState coldHPsi coldFrame renewalState e)
    omega
  have hsum := ofFn_sum_le (fun _ : Fin 5 => 5)
    (fun e : Fin 5 => entrancePotential coldFrame
      (entranceStep coldHPsi coldFrame renewalState e)) hpositive
  rw [FiniteUniformStoppingTree.ofFn_sum_const] at hsum
  change 1 * 5 + _ ≤ 5 * (5 * R coldFrame renewalState) at hstep
  rw [renewal_rank_one] at hstep
  omega

/-- The old unrestricted certificate is in particular impossible; its
failure is not caused solely by malformed states outside the gap domain. -/
theorem no_entranceBellman : ¬ EntranceBellman coldHPsi coldFrame := by
  intro H
  apply no_gapPair_entrance_bellman_row
  intro b _
  exact H.2.2 b

end LDSinkTwoGapRaceSupportResolution

#print axioms LDSinkTwoGapRaceSupportResolution.cold_gapPair
#print axioms LDSinkTwoGapRaceSupportResolution.cold_supported_no_success
#print axioms LDSinkTwoGapRaceSupportResolution.no_racePortResidual
#print axioms LDSinkTwoGapRaceSupportResolution.ready_gapPair_raceReady
#print axioms LDSinkTwoGapRaceSupportResolution.ready_prepare_delete
#print axioms LDSinkTwoGapRaceSupportResolution.ready_attack_first_absorbs
#print axioms LDSinkTwoGapRaceSupportResolution.renewal_gapPair
#print axioms LDSinkTwoGapRaceSupportResolution.no_gapPair_entrance_bellman_row
#print axioms LDSinkTwoGapRaceSupportResolution.no_entranceBellman
