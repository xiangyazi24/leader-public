import Leader.Wu.Elimination.TwoLeaderEntranceSelection

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkProtectedAbsorption
open K2TwoLeaderGeometry K2TwoLeaderEntranceCore
open LDSinkTwoGapRaceEntranceDummyService LDSinkTwoGapRaceEntranceColourCoupling

namespace K2TwoLeaderEntranceBudget

variable {n psi : Nat}

/-! Physical dummy regeneration and its exact finite-word audit.  A pending
recovery dummy is an actual bullet in the same configuration as the attack.
No independent recovery process or scheduler event-count premise is assumed. -/

/-- A pending recovery dummy prevents the shared FIRE gate from reopening. -/
theorem dummy_not_sharedReady (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (b : (Fin n → AgentState psi)) (hg : WrapInvariant hpsi F b) (p : Nat)
    (hp : 0 < p) (hpd : p < F.recovery.d) (hf : DummyFront F.recovery b p) :
    ¬ SharedReady F b := by
  have hz := hg.1.2.2.2 p F.recovery.d (by omega) (by omega)
    (by rw [hf.1]; decide) (by omega) (Nat.le_refl _)
  rw [F.shared_endpoint] at hz
  intro hs
  change (b (F.attack.pos 0)).signal_B = (1 : Fin 2) at hs
  rw [hz] at hs
  cases hs

/-- Every collapsed ready event physically starts a new highest dummy at
distance `a-1`.  Its shooter cell is cleared in this same FIRE/MOVE row. -/
theorem prepare_dummy_front (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (b : (Fin n → AgentState psi)) (hg : WrapInvariant hpsi F b) (hr : SharedReady F b) :
    DummyFront F.recovery (rawConf hpsi F b (preparePort F)) (F.recovery.d - 1) := by
  have hd := F.recovery.hd
  have hp : F.recovery.d - 1 + 1 = F.recovery.d := by omega
  have ha : (b (deletePort F)).label = nextLabel hpsi (b (preparePort F)) := by
    have h := hg.1.2.2.1 (F.recovery.d - 1) (by omega)
    simpa only [hp, F.shared_endpoint, preparePort, deletePort] using h
  have hrow := incoming_fire_pair hpsi (b (preparePort F)) (b (deletePort F))
    (hg.1.2.1 (F.recovery.d - 1) (by omega) (by omega)) hg.2.1.1 hr ha
  constructor
  · change (rawConf hpsi F b (preparePort F) (preparePort F)).bullet = (1 : Fin 3)
    rw [rawConf, K2OutputSafety.rawStep, updatePair_initiator, prepare_right, hrow]
  · intro k hk hkd
    have he : k = F.recovery.d := by omega
    subst k
    rw [F.shared_endpoint]
    change (rawConf hpsi F b (preparePort F) (deletePort F)).bullet = (0 : Fin 3)
    rw [rawConf, K2OutputSafety.rawStep, prepare_right,
      updatePair_responder _ _ _ _ (prepare_ne_delete F).symm, hrow]

def Collapses (F : TwoLeaderFrame n) (b : (Fin n → AgentState psi)) (e : Fin n) : Prop :=
  SharedReady F b ∧ (e = preparePort F ∨ e = deletePort F)

theorem physical_collapses_iff (F : TwoLeaderFrame n) (C : Fin n → AgentState psi) (e : Fin n) :
    (redirection F).Collapses C e ↔ Collapses F C e := collapses_iff F C e

private theorem effective_of_collapses (F : TwoLeaderFrame n) (b : (Fin n → AgentState psi))
    (e : Fin n) (hc : Collapses F b e) :
    controlledPort F b e = preparePort F := by
  rcases hc.2 with rfl | rfl
  · exact controlledPort_prepare F b
  · exact controlledPort_delete_ready F b hc.1

private theorem effective_of_not_collapses (F : TwoLeaderFrame n) (b : (Fin n → AgentState psi))
    (e : Fin n) (hc : ¬ Collapses F b e) : controlledPort F b e = e := by
  classical
  unfold controlledPort
  split
  · rename_i h
    exact (hc ⟨h.1, .inr h.2⟩).elim
  · rfl

def serviceLength (F : TwoLeaderFrame n) : Nat := F.recovery.d - 1

structure PendingState (hpsi : psi > 0) (F : TwoLeaderFrame n) where
  raw : (Fin n → AgentState psi)
  gap : WrapInvariant hpsi F raw
  position : Nat
  bound : position ≤ serviceLength F
  front : 0 < position → DummyFront F.recovery raw position

def initialPending (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (b : (Fin n → AgentState psi)) (hg : WrapInvariant hpsi F b) : PendingState hpsi F :=
  ⟨b, hg, 0, Nat.zero_le _, fun h => (by omega : False).elim⟩

private theorem pending_position_zero_of_collapse (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : PendingState hpsi F) (e : Fin n) (hc : Collapses F z.raw e) : z.position = 0 := by
  by_cases hp : z.position = 0
  · exact hp
  · have hpos : 0 < z.position := by omega
    have hbd := z.bound
    have hd := F.recovery.hd
    have hlt : z.position < F.recovery.d := by unfold serviceLength at hbd; omega
    exact (dummy_not_sharedReady hpsi F z.raw z.gap z.position hpos hlt
      (z.front hpos) hc.1).elim

private theorem nextDummyPosition_le (G : GapFrame n) (p : Nat) (e : Fin n) :
    nextDummyPosition G p e ≤ p := by
  unfold nextDummyPosition
  split
  · exact Nat.zero_le _
  · split <;> omega

private theorem next_gap (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : PendingState hpsi F) (e : Fin n)
    (hn : ¬ Deleted F (rawConf hpsi F z.raw (controlledPort F z.raw e))) :
    WrapInvariant hpsi F (rawConf hpsi F z.raw (controlledPort F z.raw e)) :=
  rawConf_invariant hpsi F z.raw z.gap _ hn

noncomputable def pendingNext (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : PendingState hpsi F) (e : Fin n)
    (hn : ¬ Deleted F (rawConf hpsi F z.raw (controlledPort F z.raw e))) :
    PendingState hpsi F := by
  classical
  let y := rawConf hpsi F z.raw (controlledPort F z.raw e)
  have hg : WrapInvariant hpsi F y := next_gap hpsi F z e hn
  by_cases hc : Collapses F z.raw e
  · refine ⟨y, hg, serviceLength F, Nat.le_refl _, ?_⟩
    intro _
    have hf := prepare_dummy_front hpsi F z.raw z.gap hc.1
    change DummyFront F.recovery
      (rawConf hpsi F z.raw (controlledPort F z.raw e)) (F.recovery.d - 1)
    rwa [effective_of_collapses F z.raw e hc]
  · have he := effective_of_not_collapses F z.raw e hc
    have hconf : rawConf hpsi F z.raw e = sinkStepC hpsi F.recovery z.raw e :=
      rawConf_eq_gap hpsi F F.recovery z.raw e
    refine ⟨y, hg, nextDummyPosition F.recovery z.position e,
      Nat.le_trans (nextDummyPosition_le F.recovery z.position e) z.bound, ?_⟩
    intro hp
    have hpre : 0 < z.position := by
      have hle := nextDummyPosition_le F.recovery z.position e
      omega
    have hd := F.recovery.hd
    have hb := z.bound
    have hlt : z.position < F.recovery.d := by unfold serviceLength at hb; omega
    have hpost : GapInvariant hpsi F.recovery (sinkStepC hpsi F.recovery z.raw e) := by
      have hh := hg.1
      change GapInvariant hpsi F.recovery
        (rawConf hpsi F z.raw (controlledPort F z.raw e)) at hh
      rw [he, hconf] at hh
      exact hh
    have hf := dummy_front_row hpsi F.recovery z.raw z.gap.1
      z.position hpre hlt (z.front hpre) e hpost hp
    change DummyFront F.recovery
      (rawConf hpsi F z.raw (controlledPort F z.raw e)) _
    rw [he, hconf]
    exact hf

noncomputable def pendingStep (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : PendingState hpsi F) (e : Fin n) : StopNode (PendingState hpsi F) := by
  classical
  exact if h : Deleted F (rawConf hpsi F z.raw (controlledPort F z.raw e))
    then .success else .active (pendingNext hpsi F z e h)

private theorem pendingNext_position_collapse (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : PendingState hpsi F) (e : Fin n)
    (hn : ¬ Deleted F (rawConf hpsi F z.raw (controlledPort F z.raw e)))
    (hc : Collapses F z.raw e) : (pendingNext hpsi F z e hn).position = serviceLength F := by
  classical
  simp only [pendingNext, hc, dite_true]

private theorem pendingNext_position_other (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : PendingState hpsi F) (e : Fin n)
    (hn : ¬ Deleted F (rawConf hpsi F z.raw (controlledPort F z.raw e)))
    (hc : ¬ Collapses F z.raw e) :
    (pendingNext hpsi F z e hn).position = nextDummyPosition F.recovery z.position e := by
  classical
  simp only [pendingNext, hc, dite_false]

structure BudgetState (hpsi : psi > 0) (F : TwoLeaderFrame n) (M : Nat) where
  pending : PendingState hpsi F
  remaining : Nat
  bound : remaining ≤ M

def withRemaining (hpsi : psi > 0) (F : TwoLeaderFrame n) (M m : Nat) (hm : m ≤ M) :
    StopNode (PendingState hpsi F) → StopNode (BudgetState hpsi F M)
  | .active z => .active ⟨z, m, hm⟩
  | .success => .success
  | .failure => .failure

noncomputable def budgetStep (hpsi : psi > 0) (F : TwoLeaderFrame n) (M : Nat)
    (z : BudgetState hpsi F M) (e : Fin n) : StopNode (BudgetState hpsi F M) := by
  classical
  exact if Collapses F z.pending.raw e then
    if hz : z.remaining = 0 then .failure
    else withRemaining hpsi F M (z.remaining - 1) (by have h := z.bound; omega)
      (pendingStep hpsi F z.pending e)
  else withRemaining hpsi F M z.remaining z.bound (pendingStep hpsi F z.pending e)

def budgetPotential (hpsi : psi > 0) (F : TwoLeaderFrame n) (M : Nat) :
    StopNode (BudgetState hpsi F M) → Nat
  | .active z => serviceLength F * (M - z.remaining) +
      (serviceLength F - z.pending.position)
  | .success => 0
  | .failure => serviceLength F * (M + 1)

private theorem collapsed_potential_eq (hpsi : psi > 0) (F : TwoLeaderFrame n) (M : Nat)
    (z : BudgetState hpsi F M) (e : Fin n) (hc : Collapses F z.pending.raw e) :
    budgetPotential hpsi F M (budgetStep hpsi F M z e) = budgetPotential hpsi F M (.active z) := by
  classical
  have hp := pending_position_zero_of_collapse hpsi F z.pending e hc
  have he := effective_of_collapses F z.pending.raw e hc
  have hn : ¬ Deleted F (rawConf hpsi F z.pending.raw
      (controlledPort F z.pending.raw e)) := by
    rw [he]
    exact prepare_not_success hpsi F z.pending.raw z.pending.gap
  unfold budgetStep
  rw [if_pos hc]
  by_cases hz : z.remaining = 0
  · rw [dif_pos hz]
    simp only [budgetPotential, hz, hp, Nat.sub_zero, Nat.mul_add, Nat.mul_one]
  · rw [dif_neg hz]
    simp only [pendingStep, dif_neg hn, withRemaining, budgetPotential,
      pendingNext_position_collapse hpsi F z.pending e hn hc, hp, Nat.sub_self,
      Nat.add_zero, Nat.sub_zero]
    have hm : M - (z.remaining - 1) = M - z.remaining + 1 := by have h := z.bound; omega
    rw [hm, Nat.mul_add, Nat.mul_one]

private theorem other_potential_le (hpsi : psi > 0) (F : TwoLeaderFrame n) (M : Nat)
    (z : BudgetState hpsi F M) (e : Fin n) (hc : ¬ Collapses F z.pending.raw e) :
    budgetPotential hpsi F M (budgetStep hpsi F M z e) ≤
      budgetPotential hpsi F M (.active z) +
        (if e = F.recovery.pos (z.pending.position - 1) then 1 else 0) := by
  classical
  unfold budgetStep
  rw [if_neg hc]
  unfold pendingStep
  split
  · exact Nat.zero_le _
  · rename_i hn
    simp only [withRemaining, budgetPotential,
      pendingNext_position_other hpsi F z.pending e hn hc]
    have hbound := z.pending.bound
    unfold nextDummyPosition
    by_cases hp : z.pending.position = 0
    · rw [if_pos hp]
      omega
    · rw [if_neg hp]
      split <;> omega

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

/-- This row pays for repeated, physically regenerated dummy FIRING events.
Only one raw service symbol can raise the audit potential by one. -/
theorem budget_potential_row (hpsi : psi > 0) (F : TwoLeaderFrame n) (M : Nat)
    (z : BudgetState hpsi F M) :
    (List.ofFn (fun e => budgetPotential hpsi F M (budgetStep hpsi F M z e))).sum ≤
      n * budgetPotential hpsi F M (.active z) + 1 := by
  classical
  have hrow : ∀ e : Fin n,
      budgetPotential hpsi F M (budgetStep hpsi F M z e) ≤
        budgetPotential hpsi F M (.active z) +
          (if e = F.recovery.pos (z.pending.position - 1) then 1 else 0) := by
    intro e
    by_cases hc : Collapses F z.pending.raw e
    · rw [collapsed_potential_eq hpsi F M z e hc]
      exact Nat.le_add_right _ _
    · exact other_potential_le hpsi F M z e hc
  have hs := ofFn_sum_le _ _ hrow
  rwa [ofFn_sum_add, sum_spike, FiniteUniformStoppingTree.ofFn_sum_const] at hs

private theorem budget_node_row (hpsi : psi > 0) (F : TwoLeaderFrame n) (M : Nat)
    (x : StopNode (BudgetState hpsi F M)) :
    (List.ofFn (fun e => budgetPotential hpsi F M
      (stepNode (budgetStep hpsi F M) x e))).sum ≤ n * budgetPotential hpsi F M x + 1 := by
  cases x with
  | active z => exact budget_potential_row hpsi F M z
  | success => simp only [stepNode, FiniteUniformStoppingTree.ofFn_sum_const]; omega
  | failure => simp only [stepNode, FiniteUniformStoppingTree.ofFn_sum_const]; omega

/-- Exact finite-tree telescope; the unit row allowance is one scheduler
symbol per interaction, not one additional FIRING event per interaction. -/
theorem budget_weight_bound (hpsi : psi > 0) (F : TwoLeaderFrame n) (M : Nat)
    (x : StopNode (BudgetState hpsi F M)) (T : Nat) :
    n * treeWeight (budgetStep hpsi F M) (budgetPotential hpsi F M) x T ≤
      n ^ T * (n * budgetPotential hpsi F M x + T) := by
  induction T generalizing x with
  | zero => simp only [treeWeight, Nat.pow_zero, Nat.one_mul, Nat.add_zero, Nat.le_refl]
  | succ T ih =>
      rw [treeWeight, ← ofFn_sum_mul_left]
      calc
        (List.ofFn (fun e => n * treeWeight (budgetStep hpsi F M) (budgetPotential hpsi F M)
            (stepNode (budgetStep hpsi F M) x e) T)).sum ≤
            (List.ofFn (fun e => n ^ T *
              (n * budgetPotential hpsi F M (stepNode (budgetStep hpsi F M) x e) + T))).sum :=
          ofFn_sum_le _ _ (fun e => ih _)
        _ = n ^ T * (n * (List.ofFn (fun e => budgetPotential hpsi F M
              (stepNode (budgetStep hpsi F M) x e))).sum + n * T) := by
          rw [ofFn_sum_mul_left, ofFn_sum_add, ofFn_sum_mul_left,
            FiniteUniformStoppingTree.ofFn_sum_const]
        _ ≤ n ^ T * (n * (n * budgetPotential hpsi F M x + 1) + n * T) := by
          apply Nat.mul_le_mul_left
          apply Nat.add_le_add_right
          exact Nat.mul_le_mul_left n (budget_node_row hpsi F M x)
        _ = n ^ (T + 1) * (n * budgetPotential hpsi F M x + (T + 1)) := by
          simp only [Nat.pow_succ, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
          ac_rfl

def initialBudget (hpsi : psi > 0) (F : TwoLeaderFrame n) (M : Nat)
    (b : (Fin n → AgentState psi)) (hg : WrapInvariant hpsi F b) : BudgetState hpsi F M :=
  ⟨initialPending hpsi F b hg, M, Nat.le_refl _⟩

/-- Budget exhaustion is the only audit failure.  The numerator is an
actual stopped-tree failure count at the same deterministic horizon. -/
theorem budget_failure_bound (hpsi : psi > 0) (F : TwoLeaderFrame n) (M : Nat)
    (b : (Fin n → AgentState psi)) (hg : WrapInvariant hpsi F b) (T : Nat) :
    n * (serviceLength F * (M + 1)) *
      failureCount (budgetStep hpsi F M) (.active (initialBudget hpsi F M b hg)) T ≤
        n ^ T * (n * serviceLength F + T) := by
  let x := StopNode.active (initialBudget hpsi F M b hg)
  have hw : ∀ y : StopNode (BudgetState hpsi F M),
      (serviceLength F * (M + 1)) * failureWeight y ≤ budgetPotential hpsi F M y := by
    intro y
    cases y with
    | success => exact Nat.zero_le _
    | failure => simp only [failureWeight, budgetPotential, Nat.mul_one, Nat.le_refl]
    | active z => exact Nat.zero_le _
  have hm := treeWeight_mono (budgetStep hpsi F M)
    (fun y => (serviceLength F * (M + 1)) * failureWeight y)
    (budgetPotential hpsi F M) hw x T
  rw [treeWeight_mul_left] at hm
  have ht := budget_weight_bound hpsi F M x T
  have hi : budgetPotential hpsi F M x = serviceLength F := by
    simp only [x, initialBudget, initialPending, budgetPotential, Nat.sub_self,
      Nat.mul_zero, Nat.sub_zero, Nat.zero_add]
  rw [hi] at ht
  have hle := Nat.le_trans (Nat.mul_le_mul_left n hm) ht
  simpa only [failureCount, Nat.mul_assoc] using hle

def erasePending (hpsi : psi > 0) (F : TwoLeaderFrame n) :
    StopNode (PendingState hpsi F) → StopNode ((Fin n → AgentState psi))
  | .active z => .active z.raw
  | .success => .success
  | .failure => .failure

private theorem pendingNext_raw (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : PendingState hpsi F) (e : Fin n)
    (hn : ¬ Deleted F (rawConf hpsi F z.raw (controlledPort F z.raw e))) :
    (pendingNext hpsi F z e hn).raw = rawConf hpsi F z.raw (controlledPort F z.raw e) := by
  classical
  by_cases hc : Collapses F z.raw e <;> simp only [pendingNext, hc, dite_true, dite_false]

private theorem pendingStep_erases (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : PendingState hpsi F) (e : Fin n) :
    erasePending hpsi F (pendingStep hpsi F z e) =
      ControlledSchedulerMass.controlledStep (originalPhysicalStep hpsi F) (redirection F) z.raw e := by
  classical
  simp only [ControlledSchedulerMass.controlledStep, effective_eq]
  rw [originalPhysicalStep_normal_form]
  by_cases hs : Deleted F (rawConf hpsi F z.raw (controlledPort F z.raw e))
  · simp only [pendingStep, dif_pos hs, if_pos hs, erasePending]
  · simp only [pendingStep, dif_neg hs, if_neg hs, erasePending, pendingNext_raw]

def eraseBudget (hpsi : psi > 0) (F : TwoLeaderFrame n) (M : Nat) :
    StopNode (BudgetState hpsi F M) → StopNode ((Fin n → AgentState psi) × Nat)
  | .active z => .active (z.pending.raw, z.remaining)
  | .success => .success
  | .failure => .failure

private theorem withRemaining_erases (hpsi : psi > 0) (F : TwoLeaderFrame n) (M m : Nat)
    (hm : m ≤ M) (x : StopNode (PendingState hpsi F)) :
    eraseBudget hpsi F M (withRemaining hpsi F M m hm x) =
      ControlledSchedulerMass.withBudget m (erasePending hpsi F x) := by
  cases x <;> rfl

/-- The pending-dummy proof fields and their physical closure erase exactly
to the external adaptive-redirection audit, including the budget failure. -/
theorem budgetStep_erases (hpsi : psi > 0) (F : TwoLeaderFrame n) (M : Nat)
    (x : StopNode (BudgetState hpsi F M)) (e : Fin n) :
    eraseBudget hpsi F M (stepNode (budgetStep hpsi F M) x e) =
      stepNode (ControlledSchedulerMass.auditStep (originalPhysicalStep hpsi F)
        (redirection F)) (eraseBudget hpsi F M x) e := by
  classical
  cases x with
  | success => rfl
  | failure => rfl
  | active z =>
      change eraseBudget hpsi F M (budgetStep hpsi F M z e) =
        ControlledSchedulerMass.auditStep (originalPhysicalStep hpsi F) (redirection F)
          (z.pending.raw, z.remaining) e
      unfold budgetStep ControlledSchedulerMass.auditStep
      simp only [physical_collapses_iff]
      by_cases hc : Collapses F z.pending.raw e
      · rw [if_pos hc, if_pos hc]
        by_cases hz : z.remaining = 0
        · rw [dif_pos hz, hz]
          rfl
        · rw [dif_neg hz, withRemaining_erases, pendingStep_erases]
          have hm : z.remaining = (z.remaining - 1) + 1 := by omega
          rw [hm, Nat.add_sub_cancel]
      · rw [if_neg hc, if_neg hc, withRemaining_erases, pendingStep_erases]

private theorem audit_treeWeight_erases (hpsi : psi > 0) (F : TwoLeaderFrame n) (M : Nat)
    (w : StopNode ((Fin n → AgentState psi) × Nat) → Nat)
    (x : StopNode (BudgetState hpsi F M)) (T : Nat) :
    treeWeight (budgetStep hpsi F M) (fun y => w (eraseBudget hpsi F M y)) x T =
      treeWeight (ControlledSchedulerMass.auditStep (originalPhysicalStep hpsi F)
        (redirection F)) w (eraseBudget hpsi F M x) T := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      simp only [treeWeight]
      apply ofFn_sum_eq
      intro e
      rw [ih, budgetStep_erases]

/-- The usable count bound is on the literal original physical tree's
bounded redirection audit, rather than on an unconnected counter process. -/
theorem physical_audit_failure_bound (hpsi : psi > 0) (F : TwoLeaderFrame n) (M : Nat)
    (b : (Fin n → AgentState psi)) (hg : WrapInvariant hpsi F b) (T : Nat) :
    n * (serviceLength F * (M + 1)) *
      failureCount (ControlledSchedulerMass.auditStep (originalPhysicalStep hpsi F)
        (redirection F)) (.active (b, M)) T ≤
          n ^ T * (n * serviceLength F + T) := by
  have hw : (fun y => failureWeight (eraseBudget hpsi F M y)) = failureWeight := by
    funext y
    cases y <;> rfl
  have he := audit_treeWeight_erases hpsi F M failureWeight
    (.active (initialBudget hpsi F M b hg)) T
  rw [hw] at he
  change failureCount (budgetStep hpsi F M) (.active (initialBudget hpsi F M b hg)) T =
    failureCount (ControlledSchedulerMass.auditStep (originalPhysicalStep hpsi F)
      (redirection F)) (.active (b, M)) T at he
  have hb := budget_failure_bound hpsi F M b hg T
  rwa [he] at hb

end K2TwoLeaderEntranceBudget

#print axioms K2TwoLeaderEntranceBudget.dummy_not_sharedReady
#print axioms K2TwoLeaderEntranceBudget.prepare_dummy_front
#print axioms K2TwoLeaderEntranceBudget.budget_potential_row
#print axioms K2TwoLeaderEntranceBudget.budgetStep_erases
#print axioms K2TwoLeaderEntranceBudget.physical_audit_failure_bound
