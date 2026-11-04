import Leader.Wu.RaceEntrance.DummyService
import Leader.Core.ControlledSchedulerMass

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkProtectedAbsorption LDTwoGapFrame
open LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptResidual LDSinkTwoGapDeletionWired
open LDSinkTwoGapReachInvariant LDSinkTwoGapArrivalRaceMass
open LDSinkTwoGapRaceEntranceControlledTail LDSinkTwoGapRaceEntranceControlledRank
open LDSinkTwoGapRaceEntranceDummyService

namespace LDSinkTwoGapRaceEntranceCollapseBudget

variable {n psi : Nat}

/-!
The audit counts BOTH preimages of each controlled incoming FIRE.  The
physical pending-dummy projection pays for its next repetition: while the
dummy has positive distance, the shared leader cannot fire again, and only
one raw predecessor port reduces that distance in each row.
-/

noncomputable def physicalRedirection (F : TwoGapFrame n) :
    ControlledSchedulerMass.Redirection (AState n psi) n := by
  classical
  exact {
    two_le := by have h := F.attack.hd; have h' := F.attack.hdn; omega
    gate := fun b => decide (SharedReady F b.conf)
    portA := fun _ => preparePort F
    portB := fun _ => deletePort F
    distinct := fun _ _ => preparePort_ne_deletePort F }

theorem physical_effective_eq (F : TwoGapFrame n) (b : AState n psi) (e : Fin n) :
    (physicalRedirection F).effective b e = controlledPort F b.conf e := by
  classical
  simp only [physicalRedirection, ControlledSchedulerMass.Redirection.effective,
    decide_eq_true_eq, controlledPort]

def Collapses (F : TwoGapFrame n) (b : AState n psi) (e : Fin n) : Prop :=
  SharedReady F b.conf ∧ (e = preparePort F ∨ e = deletePort F)

theorem physical_collapses_iff (F : TwoGapFrame n) (b : AState n psi) (e : Fin n) :
    (physicalRedirection F).Collapses b e ↔ Collapses F b e := by
  classical
  simp only [ControlledSchedulerMass.Redirection.Collapses, physicalRedirection,
    decide_eq_true_eq, Collapses]

private theorem effective_of_collapses (F : TwoGapFrame n) (b : AState n psi)
    (e : Fin n) (hc : Collapses F b e) :
    controlledPort F b.conf e = preparePort F := by
  rcases hc.2 with rfl | rfl
  · exact controlledPort_prepare F b.conf
  · exact controlledPort_delete_ready F b.conf hc.1

private theorem effective_of_not_collapses (F : TwoGapFrame n) (b : AState n psi)
    (e : Fin n) (hc : ¬ Collapses F b e) : controlledPort F b.conf e = e := by
  classical
  unfold controlledPort
  split
  · rename_i h
    exact (hc ⟨h.1, .inr h.2⟩).elim
  · rfl

def serviceLength (F : TwoGapFrame n) : Nat := F.recovery.d - 1

structure PendingState (hpsi : psi > 0) (F : TwoGapFrame n) where
  raw : AState n psi
  gap : GapPair hpsi F raw
  position : Nat
  bound : position ≤ serviceLength F
  front : 0 < position → DummyFront F.recovery raw.conf position

def initialPending (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b) : PendingState hpsi F :=
  ⟨b, hg, 0, Nat.zero_le _, fun h => (by omega : False).elim⟩

private theorem pending_position_zero_of_collapse (hpsi : psi > 0) (F : TwoGapFrame n)
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

private theorem next_gap (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : PendingState hpsi F) (e : Fin n)
    (hn : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw (controlledPort F z.raw.conf e))) :
    GapPair hpsi F (postState hpsi F z.raw (controlledPort F z.raw.conf e)) := by
  classical
  apply LDSinkTwoGapRestartClosure.gapPair_physical_step hpsi F
    (CleanBoundaryDecision.restartCleanBoundarySignalResidual_K2 hpsi F)
    z.raw (controlledPort F z.raw.conf e) _ z.gap
  rw [physicalBlockStep_normal_form, if_neg hn]

noncomputable def pendingNext (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : PendingState hpsi F) (e : Fin n)
    (hn : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw (controlledPort F z.raw.conf e))) :
    PendingState hpsi F := by
  classical
  let y := postState hpsi F z.raw (controlledPort F z.raw.conf e)
  have hg : GapPair hpsi F y := next_gap hpsi F z e hn
  by_cases hc : Collapses F z.raw e
  · refine ⟨y, hg, serviceLength F, Nat.le_refl _, ?_⟩
    intro _
    have hf := prepare_dummy_front hpsi F z.raw z.gap hc.1
    change DummyFront F.recovery
      (attemptStepConf hpsi F z.raw (controlledPort F z.raw.conf e)) (F.recovery.d - 1)
    rwa [effective_of_collapses F z.raw e hc]
  · have he := effective_of_not_collapses F z.raw e hc
    have hconf : attemptStepConf hpsi F z.raw e = sinkStepC hpsi F.recovery z.raw.conf e :=
      postConf_eq_recovery hpsi F z.raw e
    refine ⟨y, hg, nextDummyPosition F.recovery z.position e,
      Nat.le_trans (nextDummyPosition_le F.recovery z.position e) z.bound, ?_⟩
    intro hp
    have hpre : 0 < z.position := by
      have hle := nextDummyPosition_le F.recovery z.position e
      omega
    have hd := F.recovery.hd
    have hb := z.bound
    have hlt : z.position < F.recovery.d := by unfold serviceLength at hb; omega
    have hpost : GapInvariant hpsi F.recovery (sinkStepC hpsi F.recovery z.raw.conf e) := by
      have hh := hg.recovery
      change GapInvariant hpsi F.recovery
        (attemptStepConf hpsi F z.raw (controlledPort F z.raw.conf e)) at hh
      rw [he, hconf] at hh
      exact hh
    have hf := dummy_front_row hpsi F.recovery z.raw.conf z.gap.recovery
      z.position hpre hlt (z.front hpre) e hpost hp
    change DummyFront F.recovery
      (attemptStepConf hpsi F z.raw (controlledPort F z.raw.conf e)) _
    rw [he, hconf]
    exact hf

noncomputable def pendingStep (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : PendingState hpsi F) (e : Fin n) : StopNode (PendingState hpsi F) := by
  classical
  exact if h : NoResetSuccess F (attemptStepConf hpsi F z.raw (controlledPort F z.raw.conf e))
    then .success else .active (pendingNext hpsi F z e h)

private theorem pendingNext_position_collapse (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : PendingState hpsi F) (e : Fin n)
    (hn : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw (controlledPort F z.raw.conf e)))
    (hc : Collapses F z.raw e) : (pendingNext hpsi F z e hn).position = serviceLength F := by
  classical
  simp only [pendingNext, hc, dite_true]

private theorem pendingNext_position_other (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : PendingState hpsi F) (e : Fin n)
    (hn : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw (controlledPort F z.raw.conf e)))
    (hc : ¬ Collapses F z.raw e) :
    (pendingNext hpsi F z e hn).position = nextDummyPosition F.recovery z.position e := by
  classical
  simp only [pendingNext, hc, dite_false]

structure BudgetState (hpsi : psi > 0) (F : TwoGapFrame n) (M : Nat) where
  pending : PendingState hpsi F
  remaining : Nat
  bound : remaining ≤ M

def withRemaining (hpsi : psi > 0) (F : TwoGapFrame n) (M m : Nat) (hm : m ≤ M) :
    StopNode (PendingState hpsi F) → StopNode (BudgetState hpsi F M)
  | .active z => .active ⟨z, m, hm⟩
  | .success => .success
  | .failure => .failure

noncomputable def budgetStep (hpsi : psi > 0) (F : TwoGapFrame n) (M : Nat)
    (z : BudgetState hpsi F M) (e : Fin n) : StopNode (BudgetState hpsi F M) := by
  classical
  exact if Collapses F z.pending.raw e then
    if hz : z.remaining = 0 then .failure
    else withRemaining hpsi F M (z.remaining - 1) (by have h := z.bound; omega)
      (pendingStep hpsi F z.pending e)
  else withRemaining hpsi F M z.remaining z.bound (pendingStep hpsi F z.pending e)

def budgetPotential (hpsi : psi > 0) (F : TwoGapFrame n) (M : Nat) :
    StopNode (BudgetState hpsi F M) → Nat
  | .active z => serviceLength F * (M - z.remaining) +
      (serviceLength F - z.pending.position)
  | .success => 0
  | .failure => serviceLength F * (M + 1)

private theorem collapsed_potential_eq (hpsi : psi > 0) (F : TwoGapFrame n) (M : Nat)
    (z : BudgetState hpsi F M) (e : Fin n) (hc : Collapses F z.pending.raw e) :
    budgetPotential hpsi F M (budgetStep hpsi F M z e) = budgetPotential hpsi F M (.active z) := by
  classical
  have hp := pending_position_zero_of_collapse hpsi F z.pending e hc
  have he := effective_of_collapses F z.pending.raw e hc
  have hn : ¬ NoResetSuccess F (attemptStepConf hpsi F z.pending.raw
      (controlledPort F z.pending.raw.conf e)) := by
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

private theorem other_potential_le (hpsi : psi > 0) (F : TwoGapFrame n) (M : Nat)
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
theorem budget_potential_row (hpsi : psi > 0) (F : TwoGapFrame n) (M : Nat)
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

private theorem budget_node_row (hpsi : psi > 0) (F : TwoGapFrame n) (M : Nat)
    (x : StopNode (BudgetState hpsi F M)) :
    (List.ofFn (fun e => budgetPotential hpsi F M
      (stepNode (budgetStep hpsi F M) x e))).sum ≤ n * budgetPotential hpsi F M x + 1 := by
  cases x with
  | active z => exact budget_potential_row hpsi F M z
  | success => simp only [stepNode, FiniteUniformStoppingTree.ofFn_sum_const]; omega
  | failure => simp only [stepNode, FiniteUniformStoppingTree.ofFn_sum_const]; omega

/-- Exact finite-tree telescope; the unit row allowance is one scheduler
symbol per interaction, not one additional FIRING event per interaction. -/
theorem budget_weight_bound (hpsi : psi > 0) (F : TwoGapFrame n) (M : Nat)
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

def initialBudget (hpsi : psi > 0) (F : TwoGapFrame n) (M : Nat)
    (b : AState n psi) (hg : GapPair hpsi F b) : BudgetState hpsi F M :=
  ⟨initialPending hpsi F b hg, M, Nat.le_refl _⟩

/-- Budget exhaustion is the only audit failure.  The numerator is an
actual stopped-tree failure count at the same deterministic horizon. -/
theorem budget_failure_bound (hpsi : psi > 0) (F : TwoGapFrame n) (M : Nat)
    (b : AState n psi) (hg : GapPair hpsi F b) (T : Nat) :
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

def erasePending (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (PendingState hpsi F) → StopNode (AState n psi)
  | .active z => .active z.raw
  | .success => .success
  | .failure => .failure

private theorem pendingNext_raw (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : PendingState hpsi F) (e : Fin n)
    (hn : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw (controlledPort F z.raw.conf e))) :
    (pendingNext hpsi F z e hn).raw = postState hpsi F z.raw (controlledPort F z.raw.conf e) := by
  classical
  by_cases hc : Collapses F z.raw e <;> simp only [pendingNext, hc, dite_true, dite_false]

private theorem pendingStep_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : PendingState hpsi F) (e : Fin n) :
    erasePending hpsi F (pendingStep hpsi F z e) =
      ControlledSchedulerMass.controlledStep (physicalBlockStep hpsi F) (physicalRedirection F) z.raw e := by
  classical
  simp only [ControlledSchedulerMass.controlledStep, physical_effective_eq]
  rw [physicalBlockStep_normal_form]
  by_cases hs : NoResetSuccess F (attemptStepConf hpsi F z.raw (controlledPort F z.raw.conf e))
  · simp only [pendingStep, dif_pos hs, if_pos hs, erasePending]
  · simp only [pendingStep, dif_neg hs, if_neg hs, erasePending, pendingNext_raw]

def eraseBudget (hpsi : psi > 0) (F : TwoGapFrame n) (M : Nat) :
    StopNode (BudgetState hpsi F M) → StopNode (AState n psi × Nat)
  | .active z => .active (z.pending.raw, z.remaining)
  | .success => .success
  | .failure => .failure

private theorem withRemaining_erases (hpsi : psi > 0) (F : TwoGapFrame n) (M m : Nat)
    (hm : m ≤ M) (x : StopNode (PendingState hpsi F)) :
    eraseBudget hpsi F M (withRemaining hpsi F M m hm x) =
      ControlledSchedulerMass.withBudget m (erasePending hpsi F x) := by
  cases x <;> rfl

/-- The pending-dummy proof fields and their physical closure erase exactly
to the external adaptive-redirection audit, including the budget failure. -/
theorem budgetStep_erases (hpsi : psi > 0) (F : TwoGapFrame n) (M : Nat)
    (x : StopNode (BudgetState hpsi F M)) (e : Fin n) :
    eraseBudget hpsi F M (stepNode (budgetStep hpsi F M) x e) =
      stepNode (ControlledSchedulerMass.auditStep (physicalBlockStep hpsi F)
        (physicalRedirection F)) (eraseBudget hpsi F M x) e := by
  classical
  cases x with
  | success => rfl
  | failure => rfl
  | active z =>
      change eraseBudget hpsi F M (budgetStep hpsi F M z e) =
        ControlledSchedulerMass.auditStep (physicalBlockStep hpsi F) (physicalRedirection F)
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

private theorem audit_treeWeight_erases (hpsi : psi > 0) (F : TwoGapFrame n) (M : Nat)
    (w : StopNode (AState n psi × Nat) → Nat)
    (x : StopNode (BudgetState hpsi F M)) (T : Nat) :
    treeWeight (budgetStep hpsi F M) (fun y => w (eraseBudget hpsi F M y)) x T =
      treeWeight (ControlledSchedulerMass.auditStep (physicalBlockStep hpsi F)
        (physicalRedirection F)) w (eraseBudget hpsi F M x) T := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      simp only [treeWeight]
      apply ofFn_sum_eq
      intro e
      rw [ih, budgetStep_erases]

/-- The usable count bound is on the literal original physical tree's
bounded redirection audit, rather than on an unconnected counter process. -/
theorem physical_audit_failure_bound (hpsi : psi > 0) (F : TwoGapFrame n) (M : Nat)
    (b : AState n psi) (hg : GapPair hpsi F b) (T : Nat) :
    n * (serviceLength F * (M + 1)) *
      failureCount (ControlledSchedulerMass.auditStep (physicalBlockStep hpsi F)
        (physicalRedirection F)) (.active (b, M)) T ≤
          n ^ T * (n * serviceLength F + T) := by
  have hw : (fun y => failureWeight (eraseBudget hpsi F M y)) = failureWeight := by
    funext y
    cases y <;> rfl
  have he := audit_treeWeight_erases hpsi F M failureWeight
    (.active (initialBudget hpsi F M b hg)) T
  rw [hw] at he
  change failureCount (budgetStep hpsi F M) (.active (initialBudget hpsi F M b hg)) T =
    failureCount (ControlledSchedulerMass.auditStep (physicalBlockStep hpsi F)
      (physicalRedirection F)) (.active (b, M)) T at he
  have hb := budget_failure_bound hpsi F M b hg T
  rwa [he] at hb

/-- When the recovery gap is at least the attack gap, a fixed budget retains
all but one eighth of the controlled tree at the birth-and-shot horizon.
This estimate has no initial shield or phase premise. -/
theorem physical_audit_failure_eighth (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b)
    (hab : F.attack.d ≤ F.recovery.d) :
    8 * failureCount (ControlledSchedulerMass.auditStep (physicalBlockStep hpsi F)
      (physicalRedirection F)) (.active (b, 535)) (2 * n * (13 * F.attack.d + 7)) ≤
        n ^ (2 * n * (13 * F.attack.d + 7)) := by
  let T := 2 * n * (13 * F.attack.d + 7)
  let R := serviceLength F
  let f := failureCount (ControlledSchedulerMass.auditStep (physicalBlockStep hpsi F)
    (physicalRedirection F)) (.active (b, 535)) T
  have hR : 0 < R := by
    have hd := F.recovery.hd
    dsimp only [R, serviceLength]
    omega
  have hn : 0 < n := by have hd := F.recovery.hdn; omega
  have htime : 2 * (13 * F.attack.d + 7) ≤ 66 * R := by
    have hd := F.recovery.hd
    dsimp only [R, serviceLength]
    omega
  have htime' : T ≤ 66 * (n * R) := by
    have h := Nat.mul_le_mul_left n htime
    simpa only [T, Nat.mul_assoc, Nat.mul_left_comm] using h
  have hupper : n * R + T ≤ (n * R) * 67 := by
    rw [Nat.mul_comm (n * R) 67]
    omega
  have hb := physical_audit_failure_bound hpsi F 535 b hg T
  change n * (R * 536) * f ≤ n ^ T * (n * R + T) at hb
  have hscaled : ((n * R) * 67) * (8 * f) ≤ ((n * R) * 67) * n ^ T := by
    calc
      ((n * R) * 67) * (8 * f) = n * (R * 536) * f := by
        simp only [Nat.mul_assoc]
        rw [← Nat.mul_assoc 67 8 f]
      _ ≤ n ^ T * (n * R + T) := hb
      _ ≤ n ^ T * ((n * R) * 67) := Nat.mul_le_mul_left _ hupper
      _ = ((n * R) * 67) * n ^ T := Nat.mul_comm _ _
  have hpos : 0 < (n * R) * 67 := Nat.mul_pos (Nat.mul_pos hn hR) (by decide)
  exact Nat.le_of_mul_le_mul_left hscaled hpos

end LDSinkTwoGapRaceEntranceCollapseBudget

#print axioms LDSinkTwoGapRaceEntranceCollapseBudget.physical_effective_eq
#print axioms LDSinkTwoGapRaceEntranceCollapseBudget.physical_collapses_iff
#print axioms LDSinkTwoGapRaceEntranceCollapseBudget.pendingNext
#print axioms LDSinkTwoGapRaceEntranceCollapseBudget.budget_potential_row
#print axioms LDSinkTwoGapRaceEntranceCollapseBudget.budget_failure_bound
#print axioms LDSinkTwoGapRaceEntranceCollapseBudget.budgetStep_erases
#print axioms LDSinkTwoGapRaceEntranceCollapseBudget.physical_audit_failure_bound
#print axioms LDSinkTwoGapRaceEntranceCollapseBudget.physical_audit_failure_eighth
