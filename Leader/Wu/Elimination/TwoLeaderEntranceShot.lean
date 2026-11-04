import Leader.Wu.Elimination.TwoLeaderEntranceShotRows

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkProtectedAbsorption LDSinkGapCleanupBound
open K2TwoLeaderGeometry K2TwoLeaderEntranceCore K2TwoLeaderEntranceShotRows
open LDSinkTwoGapRaceEntranceLocalService

namespace K2TwoLeaderEntranceShot

variable {n ψ : Nat}

private theorem parked_delete (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (x : ShotState hψ F) (hp : x.position = 1) (hr : ¬ SharedReady F x.conf) :
    Deleted F (rawConf hψ F x.conf (deletePort F)) := by
  apply secondReady_delete hψ F.attack.ring F x.conf
  exact ⟨x.invariant.2.1.1, x.shield, signal_zero_of_not_ready F x.conf hr,
    x.invariant.2.2.1 1 (by omega) (by have := F.attack.hd; omega),
    by simpa only [hp, overwritePort] using x.shot.2.2.1⟩

private theorem allowed_edge (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (x : ShotState hψ F) (e : Fin n)
    (hn : ¬ Deleted F (rawConf hψ F x.conf (controlledPort F x.conf e))) :
    1 < x.position ∨ controlledPort F x.conf e ≠ deletePort F := by
  by_cases hp : 1 < x.position
  · exact .inl hp
  · apply Or.inr
    intro he
    by_cases hr : SharedReady F x.conf
    · exact controlled_ready_ne_delete F x.conf hr e he
    · rw [he] at hn
      exact hn (parked_delete hψ F x (by have := x.shot.1; omega) hr)

noncomputable def shotNext (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (x : ShotState hψ F) (e : Fin n)
    (hn : ¬ Deleted F (rawConf hψ F x.conf (controlledPort F x.conf e))) :
    ShotState hψ F :=
  ⟨rawConf hψ F x.conf (controlledPort F x.conf e),
    rawConf_invariant hψ F x.conf x.invariant _ hn,
    nextShotPosition F x.position (controlledPort F x.conf e),
    shot_row hψ F x _ (allowed_edge hψ F x e hn),
    controlled_shield_closed hψ F x.conf x.shield e⟩

/-- This stopped service can succeed only at actual physical deletion. -/
noncomputable def shotStep (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (x : ShotState hψ F) (e : Fin n) : StopNode (ShotState hψ F) := by
  classical
  exact if h : Deleted F (rawConf hψ F x.conf (controlledPort F x.conf e)) then .success
    else .active (shotNext hψ F x e h)

noncomputable def shotWork (hψ : 0 < ψ) (F : TwoLeaderFrame n) :
    StopNode (ShotState hψ F) → Nat := by
  classical
  exact fun x => match x with
  | .active x => 2 * x.position + if SharedReady F x.conf then 1 else 0
  | .success => 0
  | .failure => 0

noncomputable def shotPotential (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (x : StopNode (ShotState hψ F)) : Nat := n * shotWork hψ F x

private theorem next_position_le (F : TwoLeaderFrame n) (p : Nat) (e : Fin n) :
    nextShotPosition F p e ≤ p := by
  unfold nextShotPosition
  split <;> omega

private theorem child_le (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (x : ShotState hψ F) (e : Fin n) :
    shotWork hψ F (shotStep hψ F x e) ≤ 2 * x.position + 1 := by
  classical
  have hp := next_position_le F x.position (controlledPort F x.conf e)
  unfold shotStep
  split
  · exact Nat.zero_le _
  · change 2 * nextShotPosition F x.position (controlledPort F x.conf e) +
      (if SharedReady F (rawConf hψ F x.conf (controlledPort F x.conf e)) then 1 else 0) ≤ _
    split <;> omega

private theorem child_not_ready_le (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (x : ShotState hψ F) (e : Fin n)
    (hr : ¬ SharedReady F (rawConf hψ F x.conf (controlledPort F x.conf e))) :
    shotWork hψ F (shotStep hψ F x e) ≤
      2 * nextShotPosition F x.position (controlledPort F x.conf e) := by
  classical
  unfold shotStep
  split
  · exact Nat.zero_le _
  · change 2 * nextShotPosition F x.position (controlledPort F x.conf e) +
      (if SharedReady F (rawConf hψ F x.conf (controlledPort F x.conf e)) then 1 else 0) ≤ _
    rw [if_neg hr, Nat.add_zero]
    exact Nat.le_refl _

private theorem prepare_not_ready (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (x : ShotState hψ F) (hr : SharedReady F x.conf) :
    ¬ SharedReady F (rawConf hψ F x.conf (preparePort F)) := by
  have hz := (prepare_row hψ F x.conf x.invariant hr).2.2.1
  intro hh
  change (rawConf hψ F x.conf (preparePort F) (deletePort F)).signal_B = 1 at hh
  rw [hz] at hh
  cases hh

/-- A quiet B initiator preserves its zero signal.  Only the incoming A
row can add readiness credit when the shared leader is initially quiet. -/
private theorem not_ready_other (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (x : ShotState hψ F) (hr : ¬ SharedReady F x.conf) (e : Fin n)
    (ha : e ≠ preparePort F) : ¬ SharedReady F (rawConf hψ F x.conf e) := by
  have hz := signal_zero_of_not_ready F x.conf hr
  have hpost : (rawConf hψ F x.conf e (deletePort F)).signal_B = 0 := by
    by_cases hb : e = deletePort F
    · subst e
      rw [rawConf, K2OutputSafety.rawStep, updatePair_initiator]
      exact (LDSinkTwoGapRaceEntranceControlledRank.kernelC_left_quiet_fields hψ _ _ hz).2
    · rw [shared_frame hψ F x.conf e ha hb]
      exact hz
  intro h
  change (rawConf hψ F x.conf e (deletePort F)).signal_B = 1 at h
  rw [hpost] at h
  cases h

private theorem ready_row (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (x : ShotState hψ F) (hr : SharedReady F x.conf) :
    1 + (List.ofFn (fun e => shotWork hψ F (shotStep hψ F x e))).sum ≤
      n * shotWork hψ F (.active x) := by
  classical
  have hd := child_not_ready_le hψ F x (preparePort F)
    (by rw [controlledPort_prepare]; exact prepare_not_ready hψ F x hr)
  have hp := next_position_le F x.position (controlledPort F x.conf (preparePort F))
  have hs := LDSinkGapCleanup.ofFn_sum_lt n
    (fun e => shotWork hψ F (shotStep hψ F x e)) (2 * x.position + 1)
    (preparePort F) (child_le hψ F x) (by omega)
  simpa only [shotWork, if_pos hr, Nat.add_comm] using hs

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

private theorem predecessor_ne_prepare (F : TwoLeaderFrame n)
    (p : Nat) (hp : 0 < p) (hpd : p ≤ F.attack.d) :
    F.attack.pos (p - 1) ≠ preparePort F := by
  by_cases h1 : p = 1
  · simpa only [h1, Nat.sub_self, deletePort] using (prepare_ne_delete F).symm
  · exact (prepare_ne_attack_positive F (p - 1) (by omega) (by omega)).symm

private theorem not_ready_row (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (x : ShotState hψ F) (hr : ¬ SharedReady F x.conf) :
    1 + (List.ofFn (fun e => shotWork hψ F (shotStep hψ F x e))).sum ≤
      n * shotWork hψ F (.active x) := by
  classical
  let p := F.attack.pos (x.position - 1)
  let f := fun e => shotWork hψ F (shotStep hψ F x e)
  have hpa : p ≠ preparePort F := predecessor_ne_prepare F x.position x.shot.1 x.shot.2.1
  have hid := controlledPort_of_not_ready F x.conf hr
  have hrow : ∀ e : Fin n,
      f e + (if e = p then 2 else 0) ≤
        2 * x.position + (if e = preparePort F then 1 else 0) := by
    intro e
    by_cases he : e = p
    · subst e
      rw [if_pos rfl, if_neg hpa]
      by_cases h1 : x.position = 1
      · have hpB : p = deletePort F := by simp only [p, h1, Nat.sub_self, deletePort]
        have hd := parked_delete hψ F x h1 hr
        have hz : f p = 0 := by
          simp only [f, shotStep, hid, hpB, dif_pos hd, shotWork]
        rw [hz, h1]
        omega
      · have hn : ¬ SharedReady F (rawConf hψ F x.conf (controlledPort F x.conf p)) := by
          rw [hid]
          exact not_ready_other hψ F x hr p hpa
        have hd := child_not_ready_le hψ F x p hn
        rw [hid] at hd
        have hpnext : nextShotPosition F x.position p = x.position - 1 := by
          simp [nextShotPosition, p]
        rw [hpnext] at hd
        change f p ≤ 2 * (x.position - 1) at hd
        have hp := x.shot.1
        omega
    · rw [if_neg he, Nat.add_zero]
      by_cases ha : e = preparePort F
      · rw [if_pos ha]
        exact child_le hψ F x e
      · rw [if_neg ha, Nat.add_zero]
        have hn : ¬ SharedReady F (rawConf hψ F x.conf (controlledPort F x.conf e)) := by
          rw [hid]
          exact not_ready_other hψ F x hr e ha
        have hd := child_not_ready_le hψ F x e hn
        have hp := next_position_le F x.position (controlledPort F x.conf e)
        change f e ≤ _ at hd
        omega
  have hs := ofFn_sum_le _ _ hrow
  rw [ofFn_sum_add, ofFn_sum_add, sum_spike, sum_spike,
    FiniteUniformStoppingTree.ofFn_sum_const] at hs
  change 1 + _ ≤ n * (2 * x.position + if SharedReady F x.conf then 1 else 0)
  rw [if_neg hr, Nat.add_zero]
  dsimp only [f] at hs
  omega

/-- The real shot position and one readiness credit pay every physical row. -/
theorem shot_bellman (hψ : 0 < ψ) (F : TwoLeaderFrame n) :
    NatBellmanSuperSolution (shotStep hψ F) 1 (shotPotential hψ F) := by
  classical
  refine ⟨rfl, rfl, ?_⟩
  intro x
  have hr : 1 + (List.ofFn (fun e => shotWork hψ F (shotStep hψ F x e))).sum ≤
      n * shotWork hψ F (.active x) := by
    by_cases h : SharedReady F x.conf
    · exact ready_row hψ F x h
    · exact not_ready_row hψ F x h
  change 1 * n + (List.ofFn (fun e => n * shotWork hψ F (shotStep hψ F x e))).sum ≤
    n * (n * shotWork hψ F (.active x))
  rw [Nat.one_mul, ofFn_sum_mul_left]
  simpa only [Nat.mul_add, Nat.mul_one] using Nat.mul_le_mul_left n hr

theorem shot_truncated_cost (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (x : ShotState hψ F) (T : Nat) :
    truncatedActiveCostNumerator (shotStep hψ F) (.active x) T ≤
      n ^ T * (n * (2 * F.attack.d + 1)) := by
  classical
  have hc := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (shotStep hψ F) 1 (shotPotential hψ F) (shot_bellman hψ F) (.active x) T
  have hp : shotPotential hψ F (.active x) ≤ n * (2 * F.attack.d + 1) := by
    apply Nat.mul_le_mul_left
    change 2 * x.position + (if SharedReady F x.conf then 1 else 0) ≤ _
    have hd := x.shot.2.1
    split <;> omega
  exact Nat.le_trans (by simpa only [Nat.one_mul] using hc)
    (Nat.mul_le_mul_left (n ^ T) hp)

private theorem shot_no_failure (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (x : ShotState hψ F) (e : Fin n) : shotStep hψ F x e ≠ .failure := by
  classical
  unfold shotStep
  split <;> intro h <;> cases h

theorem shot_half (hψ : 0 < ψ) (F : TwoLeaderFrame n) (x : ShotState hψ F) :
    n ^ (2 * n * (2 * F.attack.d + 1)) ≤
      2 * successCount (shotStep hψ F) (.active x) (2 * n * (2 * F.attack.d + 1)) := by
  let T := 2 * n * (2 * F.attack.d + 1)
  have hp : 0 < T := Nat.mul_pos (Nat.mul_pos (by decide) F.attack.ring.hn) (by omega)
  have hc := shot_truncated_cost hψ F x T
  have ha := two_mul_activeCount_le_pow_of_scaled_cost (shotStep hψ F) (.active x)
    hp (by decide : 0 < 1) (num := n * (2 * F.attack.d + 1))
    (by simpa only [Nat.one_mul, Nat.mul_comm] using hc)
    (by dsimp only [T]; simp only [Nat.mul_one, Nat.mul_assoc, Nat.le_refl])
  have hf := BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure
    (shotStep hψ F) (shot_no_failure hψ F) x T
  have hparts := node_count_partition (shotStep hψ F) (.active x) T
  change n ^ T ≤ 2 * successCount (shotStep hψ F) (.active x) T
  omega

def eraseShot (hψ : 0 < ψ) (F : TwoLeaderFrame n) :
    StopNode (ShotState hψ F) → StopNode (Fin n → AgentState ψ)
  | .active x => .active x.conf
  | .success => .success
  | .failure => .failure

/-- Exact same-edge physical erasure, including the actual deletion endpoint. -/
theorem shotStep_erases (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (x : StopNode (ShotState hψ F)) (e : Fin n) :
    eraseShot hψ F (stepNode (shotStep hψ F) x e) =
      stepNode (controlledPhysicalStep hψ F) (eraseShot hψ F x) e := by
  classical
  cases x with
  | success => rfl
  | failure => rfl
  | active x =>
      change eraseShot hψ F (shotStep hψ F x e) = controlledPhysicalStep hψ F x.conf e
      rw [controlledPhysicalStep_normal_form]
      by_cases h : Deleted F (rawConf hψ F x.conf (controlledPort F x.conf e)) <;>
        simp [shotStep, h, eraseShot, shotNext]

private theorem shot_tree_erases (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (w : StopNode (Fin n → AgentState ψ) → Nat) (x : StopNode (ShotState hψ F)) (T : Nat) :
    treeWeight (shotStep hψ F) (fun y => w (eraseShot hψ F y)) x T =
      treeWeight (controlledPhysicalStep hψ F) w (eraseShot hψ F x) T := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      simp only [treeWeight]
      apply ofFn_sum_eq
      intro e
      rw [ih, shotStep_erases]

/-- Any actual fresh shot with a false victim shield has half controlled
physical deletion mass; no phase, artificial seed, or terminal-ready premise. -/
theorem fresh_controlled_half (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (hf : FreshShot hψ F C)
    (hs : (C (deletePort F)).shield = false) :
    n ^ (2 * n * (2 * F.attack.d + 1)) ≤
      2 * successCount (controlledPhysicalStep hψ F) (.active C)
        (2 * n * (2 * F.attack.d + 1)) := by
  let x : ShotState hψ F := ⟨C, hf.1, F.attack.d, hf.2, hs⟩
  have hm := shot_half hψ F x
  have hw : (fun y => successWeight (eraseShot hψ F y)) = successWeight := by
    funext y
    cases y <;> rfl
  have he := shot_tree_erases hψ F successWeight (.active x) (2 * n * (2 * F.attack.d + 1))
  rw [hw] at he
  change successCount (shotStep hψ F) (.active x) _ =
    successCount (controlledPhysicalStep hψ F) (.active C) _ at he
  rwa [he] at hm

end K2TwoLeaderEntranceShot

#print axioms K2TwoLeaderEntranceShot.shot_bellman
#print axioms K2TwoLeaderEntranceShot.shot_half
#print axioms K2TwoLeaderEntranceShot.shotStep_erases
#print axioms K2TwoLeaderEntranceShot.fresh_controlled_half
