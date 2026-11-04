import Leader.Wu.RaceEntrance.ArrivalRaceMass
import Leader.Wu.RaceEntrance.LocalService

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption LDTwoGapFrame
open LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptResidual LDSinkTwoGapAttemptCells
open LDSinkTwoGapDeletion LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant
open LDSinkTwoGapArrivalRaceMass LDSinkTwoGapRaceEntranceLocalService

namespace LDSinkTwoGapRaceEntranceControlledTail

variable {n psi : Nat}

/-!
The comparison scheduler sends the outgoing shared-leader FIRE symbol to
its incoming FIRE edge while that leader is ready.  Every effective edge
still executes the actual K2 kernel.  A unique parked live shot facing an
unshielded target reaches physical deletion under this scheduler with
potential at most `3*n`.  A ready target needs a real preparation event
before its final deleting edge; that delay is included in the budget.

This file makes no uniform-scheduler change-of-measure claim.
-/

def SharedReady (F : TwoGapFrame n) (C : Fin n → AgentState psi) : Prop :=
  (C (deletePort F)).signal_B = (1 : Fin 2)

noncomputable def controlledPort (F : TwoGapFrame n)
    (C : Fin n → AgentState psi) (e : Fin n) : Fin n := by
  classical
  exact if SharedReady F C ∧ e = deletePort F then preparePort F else e

theorem controlledPort_prepare (F : TwoGapFrame n)
    (C : Fin n → AgentState psi) :
    controlledPort F C (preparePort F) = preparePort F := by
  classical
  simp [controlledPort, preparePort_ne_deletePort]

theorem controlledPort_delete_ready (F : TwoGapFrame n)
    (C : Fin n → AgentState psi) (hr : SharedReady F C) :
    controlledPort F C (deletePort F) = preparePort F := by
  classical
  simp [controlledPort, hr]

theorem controlledPort_of_not_ready (F : TwoGapFrame n)
    (C : Fin n → AgentState psi) (hr : ¬ SharedReady F C) (e : Fin n) :
    controlledPort F C e = e := by
  classical
  simp [controlledPort, hr]

theorem controlledPort_of_ne_delete (F : TwoGapFrame n)
    (C : Fin n → AgentState psi) (e : Fin n) (he : e ≠ deletePort F) :
    controlledPort F C e = e := by
  classical
  simp [controlledPort, he]

private theorem signal_zero_of_not_ready (F : TwoGapFrame n)
    (C : Fin n → AgentState psi) (hr : ¬ SharedReady F C) :
    (C (deletePort F)).signal_B = (0 : Fin 2) := by
  apply Fin.ext
  have hb := (C (deletePort F)).signal_B.isLt
  have hn : (C (deletePort F)).signal_B.val ≠ 1 := by
    intro he
    exact hr (Fin.ext he)
  omega

private theorem fire_right_shield_false (hpsi : psi > 0) (l r : AgentState psi)
    (hs : r.shield = false) :
    (eliminateLeadersNoCollisionFire hpsi l r).2.shield = false := by
  unfold eliminateLeadersNoCollisionFire
  repeat first | rfl | exact hs | split

private theorem move_right_shield (hpsi : psi > 0) (nl : Fin psi)
    (l r : AgentState psi) :
    (absorbProtectedMove hpsi nl l r).2.shield = r.shield := by
  unfold absorbProtectedMove
  split
  · rfl
  · unfold eliminateLeadersNoCollisionZeroLeaderEgressMove
    repeat first | rfl | split

private theorem signal_right_shield (nl : Fin psi) (l r : AgentState psi) :
    (eliminateLeadersNoCollisionSignalLeaderSink nl l r).2.shield = r.shield := by
  unfold eliminateLeadersNoCollisionSignalLeaderSink
  repeat first | rfl | split

private theorem dummy_right_shield (q : AgentState psi × AgentState psi) :
    (dummyBulletSink q).2.shield = q.2.shield := by
  unfold dummyBulletSink
  repeat first | rfl | split

/-- The responder never raises a false shield: FIRE writes false there,
and every later production stage preserves that shield field. -/
theorem kernelC_right_shield_false (hpsi : psi > 0) (l r : AgentState psi)
    (hs : r.shield = false) : (sinkKernelC hpsi l r).2.shield = false := by
  unfold sinkKernelC
  rw [dummy_right_shield, signal_right_shield, move_right_shield]
  exact fire_right_shield_false hpsi l r hs

private theorem right_injective (G : GapFrame n) (e f : Fin n)
    (h : G.ring.rightNeighbor e = G.ring.rightNeighbor f) : e = f := by
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = (f.val + 1) % n at hv
  have he := e.isLt
  have hf := f.isLt
  apply Fin.ext
  by_cases he1 : e.val + 1 < n <;> by_cases hf1 : f.val + 1 < n
  · rw [Nat.mod_eq_of_lt he1, Nat.mod_eq_of_lt hf1] at hv
    omega
  · have hfn : f.val + 1 = n := by omega
    rw [hfn, Nat.mod_self, Nat.mod_eq_of_lt he1] at hv
    omega
  · have hen : e.val + 1 = n := by omega
    rw [hen, Nat.mod_self, Nat.mod_eq_of_lt hf1] at hv
    omega
  · omega

theorem shared_frame (hpsi : psi > 0) (F : TwoGapFrame n)
    (C : Fin n → AgentState psi) (e : Fin n)
    (ha : e ≠ preparePort F) (hb : e ≠ deletePort F) :
    sinkStepC hpsi F.attack C e (deletePort F) = C (deletePort F) := by
  apply sinkStepC_other hpsi F.attack C e (deletePort F) hb.symm
  intro he
  exact ha (right_injective F.attack e (preparePort F)
    (he.symm.trans (preparePort_right F).symm))

structure TailState (hpsi : psi > 0) (F : TwoGapFrame n) where
  raw : AActive hpsi F
  shield : (raw.val.conf (deletePort F)).shield = false
  live : (raw.val.conf (overwritePort F)).bullet = (2 : Fin 3)

private theorem tail_delete_not_ready (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TailState hpsi F) (hr : ¬ SharedReady F z.raw.val.conf) :
    NoResetSuccess F (attemptStepConf hpsi F z.raw.val (deletePort F)) := by
  apply secondReady_delete hpsi F z.raw.val
  exact ⟨z.raw.property.attack.1.1, z.shield,
    signal_zero_of_not_ready F z.raw.val.conf hr,
    z.raw.property.attack.2.1 1 (by decide) (by have h := F.attack.hd; omega), z.live⟩

private theorem controlled_nondelete_ne_delete (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TailState hpsi F) (e : Fin n)
    (hn : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw.val
      (controlledPort F z.raw.val.conf e))) :
    controlledPort F z.raw.val.conf e ≠ deletePort F := by
  classical
  intro he
  by_cases hr : SharedReady F z.raw.val.conf
  · unfold controlledPort at he
    split at he
    · exact preparePort_ne_deletePort F he
    · rename_i hnot
      have hdel : e = deletePort F := he
      exact hnot ⟨hr, hdel⟩
  · rw [he] at hn
    exact hn (tail_delete_not_ready hpsi F z hr)

private theorem tail_post_shield (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TailState hpsi F) (e : Fin n) (hb : e ≠ deletePort F) :
    (attemptStepConf hpsi F z.raw.val e (deletePort F)).shield = false := by
  by_cases ha : e = preparePort F
  · subst e
    rw [attemptStepConf_eq_sinkStepC, sinkStepC, preparePort_right,
      updatePair_responder _ _ _ _ (preparePort_ne_deletePort F).symm]
    exact kernelC_right_shield_false hpsi _ _ z.shield
  · rw [attemptStepConf_eq_sinkStepC, shared_frame hpsi F z.raw.val.conf e ha hb]
    exact z.shield

private theorem tail_post_live (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TailState hpsi F) (e : Fin n)
    (hs : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw.val e))
    (ha : ¬ NoResetAbsorbedAt F z.raw.val e (attemptStepConf hpsi F z.raw.val e)) :
    (attemptStepConf hpsi F z.raw.val e (overwritePort F)).bullet = (2 : Fin 3) := by
  change (postConf hpsi F z.raw.val e (F.attack.pos 1)).bullet = (2 : Fin 3)
  by_cases ht : Touched F.attack e (overwritePort F)
  · obtain ⟨u, hu, hu1, hb⟩ := liveTouched_K2 hpsi F z.raw e 1
      (by decide) (by have h := F.attack.hd; omega) z.live ht hs ha
    have he : u = 1 := by omega
    simpa only [he] using hb
  · rw [postConf_cell_eq_attack hpsi F z.raw.val e (F.attack.pos 1) ht]
    exact z.live

noncomputable def tailNext (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TailState hpsi F) (e : Fin n)
    (hn : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw.val
      (controlledPort F z.raw.val.conf e))) : TailState hpsi F := by
  classical
  let f := controlledPort F z.raw.val.conf e
  have hf : f ≠ deletePort F := controlled_nondelete_ne_delete hpsi F z e hn
  have ha : ¬ NoResetAbsorbedAt F z.raw.val f (attemptStepConf hpsi F z.raw.val f) := by
    intro h
    exact hf h.2.1
  have hn' : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw.val f) := hn
  have hraw : attemptStepRaw hpsi F z.raw.val f =
      .active (postState hpsi F z.raw.val f) := by
    simp only [attemptStepRaw, if_neg hn', if_neg ha]
    rfl
  exact ⟨⟨postState hpsi F z.raw.val f,
    (attemptLaws_K2 hpsi F).continuation z.raw f _ hraw⟩,
    tail_post_shield hpsi F z f hf, tail_post_live hpsi F z f hn ha⟩

noncomputable def tailStep (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TailState hpsi F) (e : Fin n) : StopNode (TailState hpsi F) := by
  classical
  exact if h : NoResetSuccess F (attemptStepConf hpsi F z.raw.val
      (controlledPort F z.raw.val.conf e)) then .success
    else .active (tailNext hpsi F z e h)

noncomputable def tailWork (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (TailState hpsi F) → Nat := by
  classical
  exact fun x => match x with
    | .active z => if SharedReady F z.raw.val.conf then 3 else 2
    | .success => 0
    | .failure => 0

noncomputable def tailPotential (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (TailState hpsi F)) : Nat := n * tailWork hpsi F x

private theorem prepare_not_ready (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TailState hpsi F) (hr : SharedReady F z.raw.val.conf) :
    ¬ SharedReady F (attemptStepConf hpsi F z.raw.val (preparePort F)) := by
  have hg : GapPair hpsi F z.raw.val := ⟨z.raw.property.recovery, z.raw.property.attack⟩
  have hrace := (raceReady_iff_two_cells hpsi F z.raw.val hg).mpr ⟨z.live, hr⟩
  have hfirst := firstReady_of_gapPair_raceReady hpsi F z.raw.val hg hrace
  have hsecond := firstReady_prepare hpsi F z.raw.val hfirst
  intro hh
  have hz := hsecond.victim_signal
  change (attemptStepConf hpsi F z.raw.val (preparePort F)
    (deletePort F)).signal_B = (0 : Fin 2) at hz
  change (attemptStepConf hpsi F z.raw.val (preparePort F)
    (deletePort F)).signal_B = (1 : Fin 2) at hh
  rw [hz] at hh
  cases hh

private theorem child_work_le_three (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TailState hpsi F) (e : Fin n) :
    tailWork hpsi F (tailStep hpsi F z e) ≤ 3 := by
  classical
  unfold tailStep
  split
  · exact Nat.zero_le _
  · change (if SharedReady F (tailNext hpsi F z e _).raw.val.conf then 3 else 2) ≤ 3
    split <;> decide

private theorem child_work_le_two_of_post_not_ready
    (hpsi : psi > 0) (F : TwoGapFrame n) (z : TailState hpsi F) (e : Fin n)
    (hr : ¬ SharedReady F (attemptStepConf hpsi F z.raw.val
      (controlledPort F z.raw.val.conf e))) :
    tailWork hpsi F (tailStep hpsi F z e) ≤ 2 := by
  classical
  unfold tailStep
  split
  · exact Nat.zero_le _
  · change (if SharedReady F (attemptStepConf hpsi F z.raw.val
      (controlledPort F z.raw.val.conf e)) then 3 else 2) ≤ 2
    rw [if_neg hr]
    exact Nat.le_refl _

private theorem ready_work_row (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TailState hpsi F) (hr : SharedReady F z.raw.val.conf) :
    1 + (List.ofFn (fun e => tailWork hpsi F (tailStep hpsi F z e))).sum ≤
      n * tailWork hpsi F (.active z) := by
  classical
  have hg := child_work_le_two_of_post_not_ready hpsi F z (preparePort F)
    (by rw [controlledPort_prepare]; exact prepare_not_ready hpsi F z hr)
  have hs := LDSinkGapCleanup.ofFn_sum_lt n
    (fun e => tailWork hpsi F (tailStep hpsi F z e)) 3 (preparePort F)
    (child_work_le_three hpsi F z) (by omega)
  simpa only [tailWork, if_pos hr, Nat.add_comm] using hs

private theorem sum_spike (n : Nat) : ∀ (a : Fin n) (v : Nat),
    (List.ofFn (fun e : Fin n => if e = a then v else 0)).sum = v := by
  induction n with
  | zero => intro a; exact a.elim0
  | succ n ih =>
      intro a v
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have ht : (List.ofFn (fun i : Fin n =>
            if i.succ = (0 : Fin (n + 1)) then v else 0)).sum = 0 := by
          have hh := ofFn_sum_eq
            (fun i : Fin n => if i.succ = (0 : Fin (n + 1)) then v else 0)
            (fun _ : Fin n => 0) (by
              intro i
              have hn : i.succ ≠ (0 : Fin (n + 1)) := by
                intro he
                have hv := congrArg Fin.val he
                change i.val + 1 = 0 at hv
                omega
              rw [if_neg hn])
          simpa only [FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_zero] using hh
        simp [ht]
      · intro a
        rw [List.ofFn_succ, List.sum_cons]
        have hn : (0 : Fin (n + 1)) ≠ a.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = a.val + 1 at hv
          omega
        rw [if_neg hn, Nat.zero_add]
        have hh := ofFn_sum_eq
          (fun i : Fin n => if i.succ = a.succ then v else 0)
          (fun i : Fin n => if i = a then v else 0)
          (by intro i; simp only [Fin.succ_inj])
        rw [hh]
        exact ih a v

private theorem not_ready_work_row (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TailState hpsi F) (hr : ¬ SharedReady F z.raw.val.conf) :
    1 + (List.ofFn (fun e => tailWork hpsi F (tailStep hpsi F z e))).sum ≤
      n * tailWork hpsi F (.active z) := by
  classical
  let f := fun e => tailWork hpsi F (tailStep hpsi F z e)
  have hrow : ∀ e : Fin n,
      f e + (if e = deletePort F then 2 else 0) ≤
        2 + (if e = preparePort F then 1 else 0) := by
    intro e
    by_cases hb : e = deletePort F
    · subst e
      have hs := tail_delete_not_ready hpsi F z hr
      simp [f, tailStep, controlledPort_of_not_ready F z.raw.val.conf hr,
        hs, tailWork, (preparePort_ne_deletePort F).symm]
    · by_cases ha : e = preparePort F
      · simpa [f, ha, preparePort_ne_deletePort] using child_work_le_three hpsi F z e
      · have hh : ¬ SharedReady F (attemptStepConf hpsi F z.raw.val
            (controlledPort F z.raw.val.conf e)) := by
          rw [controlledPort_of_not_ready F z.raw.val.conf hr]
          unfold SharedReady
          rw [attemptStepConf_eq_sinkStepC, shared_frame hpsi F z.raw.val.conf e ha hb]
          exact hr
        simpa [f, hb, ha] using child_work_le_two_of_post_not_ready hpsi F z e hh
  have hs := ofFn_sum_le _ _ hrow
  rw [ofFn_sum_add, ofFn_sum_add, sum_spike, sum_spike,
    FiniteUniformStoppingTree.ofFn_sum_const] at hs
  change 1 + _ ≤ n * (if SharedReady F z.raw.val.conf then 3 else 2)
  rw [if_neg hr]
  dsimp only [f] at hs
  omega

/-- The final controlled hit pays for actual ready-to-dummy preparation.
There is no assumption that a redirected victim edge already deletes. -/
theorem tail_bellman (hpsi : psi > 0) (F : TwoGapFrame n) :
    NatBellmanSuperSolution (tailStep hpsi F) 1 (tailPotential hpsi F) := by
  classical
  refine ⟨rfl, rfl, ?_⟩
  intro z
  have hr : 1 + (List.ofFn (fun e => tailWork hpsi F (tailStep hpsi F z e))).sum ≤
      n * tailWork hpsi F (.active z) := by
    by_cases h : SharedReady F z.raw.val.conf
    · exact ready_work_row hpsi F z h
    · exact not_ready_work_row hpsi F z h
  change 1 * n + (List.ofFn (fun e : Fin n =>
    n * tailWork hpsi F (tailStep hpsi F z e))).sum ≤
      n * (n * tailWork hpsi F (.active z))
  rw [Nat.one_mul, ofFn_sum_mul_left]
  have hs := Nat.mul_le_mul_left n hr
  simpa only [Nat.mul_add, Nat.mul_one] using hs

theorem tail_truncated_cost (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TailState hpsi F) (T : Nat) :
    truncatedActiveCostNumerator (tailStep hpsi F) (.active z) T ≤
      n ^ T * (3 * n) := by
  classical
  have hc := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (tailStep hpsi F) 1 (tailPotential hpsi F) (tail_bellman hpsi F) (.active z) T
  have hp : tailPotential hpsi F (.active z) ≤ 3 * n := by
    change n * (if SharedReady F z.raw.val.conf then 3 else 2) ≤ 3 * n
    split <;> omega
  exact Nat.le_trans (by simpa only [Nat.one_mul] using hc)
    (Nat.mul_le_mul_left (n ^ T) hp)

private theorem tail_no_failure (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TailState hpsi F) (e : Fin n) : tailStep hpsi F z e ≠ .failure := by
  classical
  unfold tailStep
  split <;> intro he <;> cases he

theorem tail_half (hpsi : psi > 0) (F : TwoGapFrame n) (z : TailState hpsi F) :
    n ^ (6 * n) ≤ 2 * successCount (tailStep hpsi F) (.active z) (6 * n) := by
  have hp : 0 < 6 * n := Nat.mul_pos (by decide) F.attack.ring.hn
  have hc := tail_truncated_cost hpsi F z (6 * n)
  have hactive := two_mul_activeCount_le_pow_of_scaled_cost
    (tailStep hpsi F) (.active z) hp (by decide : 0 < 1)
    (num := 3 * n) (by simpa only [Nat.one_mul, Nat.mul_comm] using hc)
    (by omega)
  have hf := BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure
    (tailStep hpsi F) (tail_no_failure hpsi F) z (6 * n)
  have hparts := node_count_partition (tailStep hpsi F) (.active z) (6 * n)
  omega

noncomputable def controlledPhysicalStep (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (e : Fin n) : StopNode (AState n psi) :=
  physicalBlockStep hpsi F b (controlledPort F b.conf e)

def eraseTail (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (TailState hpsi F) → StopNode (AState n psi)
  | .active z => .active z.raw.val
  | .success => .success
  | .failure => .failure

/-- Exact edge-by-edge erasure to the same physical K2 configurations under
the explicitly displayed comparison scheduler. -/
theorem tailStep_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (TailState hpsi F)) (e : Fin n) :
    eraseTail hpsi F (stepNode (tailStep hpsi F) x e) =
      stepNode (controlledPhysicalStep hpsi F) (eraseTail hpsi F x) e := by
  classical
  cases x with
  | success => rfl
  | failure => rfl
  | active z =>
      change eraseTail hpsi F (tailStep hpsi F z e) =
        physicalBlockStep hpsi F z.raw.val (controlledPort F z.raw.val.conf e)
      rw [physicalBlockStep_normal_form]
      by_cases hs : NoResetSuccess F (attemptStepConf hpsi F z.raw.val
          (controlledPort F z.raw.val.conf e)) <;>
        simp [tailStep, hs, eraseTail, tailNext]

private theorem treeWeight_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (w : StopNode (AState n psi) → Nat)
    (x : StopNode (TailState hpsi F)) (T : Nat) :
    treeWeight (tailStep hpsi F) (fun y => w (eraseTail hpsi F y)) x T =
      treeWeight (controlledPhysicalStep hpsi F) w (eraseTail hpsi F x) T := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      simp only [treeWeight]
      apply ofFn_sum_eq
      intro e
      rw [ih, tailStep_erases]

theorem controlled_parked_half (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : AActive hpsi F) (hs : (x.val.conf (deletePort F)).shield = false)
    (hb : (x.val.conf (overwritePort F)).bullet = (2 : Fin 3)) :
    n ^ (6 * n) ≤
      2 * successCount (controlledPhysicalStep hpsi F) (.active x.val) (6 * n) := by
  let z : TailState hpsi F := ⟨x, hs, hb⟩
  have hm := tail_half hpsi F z
  have hw : (fun y => successWeight (eraseTail hpsi F y)) = successWeight := by
    funext y
    cases y <;> rfl
  have he := treeWeight_erases hpsi F successWeight (.active z) (6 * n)
  rw [hw] at he
  change successCount (tailStep hpsi F) (.active z) (6 * n) =
    successCount (controlledPhysicalStep hpsi F) (.active x.val) (6 * n) at he
  rw [he] at hm
  exact hm

end LDSinkTwoGapRaceEntranceControlledTail

#print axioms LDSinkTwoGapRaceEntranceControlledTail.kernelC_right_shield_false
#print axioms LDSinkTwoGapRaceEntranceControlledTail.tailNext
#print axioms LDSinkTwoGapRaceEntranceControlledTail.tail_bellman
#print axioms LDSinkTwoGapRaceEntranceControlledTail.tail_truncated_cost
#print axioms LDSinkTwoGapRaceEntranceControlledTail.tailStep_erases
#print axioms LDSinkTwoGapRaceEntranceControlledTail.controlled_parked_half
