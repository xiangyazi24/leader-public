import Leader.Wu.Elimination.TwoLeaderEntranceSelection

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkProtectedAbsorption LDSinkGapDoneInvariant LDSinkGapServiceRank LDSinkGapCleanupBound
open K2TwoLeaderGeometry K2TwoLeaderEntranceCore
open LDSinkTwoGapRaceEntranceLocalService

namespace K2TwoLeaderEntranceUnshield

variable {n psi : Nat}

/-!
The first controlled incoming FIRE removes the shared leader's old shield.
Until it is ready, control is the identity and the actual recovery cleanup
rank supplies service.  At readiness the incoming row really fires and
moves a dummy, while neutral rows preserve readiness.  This initial service
cost depends on the recovery length and cannot be charged to a short attack
gap without an additional global argument.
-/

def UnshieldedOrDeleted (F : TwoLeaderFrame n) (C : Fin n → AgentState psi) : Prop :=
  (C (deletePort F)).shield = false ∨ Deleted F C

abbrev UnshieldState (hpsi : psi > 0) (F : TwoLeaderFrame n) :=
  { b : (Fin n → AgentState psi) // WrapInvariant hpsi F b }

/-- The actual responder FIRE clears the victim shield. -/
theorem prepare_unshields (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState psi) (hg : WrapInvariant hpsi F C) (hr : SharedReady F C) :
    (rawConf hpsi F C (preparePort F) (deletePort F)).shield = false :=
  (prepare_row hpsi F C hg hr).2.1

private theorem unshield_next_gap (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : UnshieldState hpsi F) (e : Fin n)
    (hn : ¬ UnshieldedOrDeleted F
      (rawConf hpsi F z.val (controlledPort F z.val e))) :
    WrapInvariant hpsi F (rawConf hpsi F z.val (controlledPort F z.val e)) :=
  rawConf_invariant hpsi F z.val z.property _ (fun h => hn (.inr h))

noncomputable def unshieldStep (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : UnshieldState hpsi F) (e : Fin n) : StopNode (UnshieldState hpsi F) := by
  classical
  exact if h : UnshieldedOrDeleted F
      (rawConf hpsi F z.val (controlledPort F z.val e)) then .success
    else .active ⟨rawConf hpsi F z.val (controlledPort F z.val e),
      unshield_next_gap hpsi F z e h⟩

noncomputable def unshieldRawStep (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (b : (Fin n → AgentState psi)) (e : Fin n) : StopNode ((Fin n → AgentState psi)) := by
  classical
  exact if UnshieldedOrDeleted F
      (rawConf hpsi F b (controlledPort F b e)) then .success
    else .active (rawConf hpsi F b (controlledPort F b e))

def eraseUnshield (hpsi : psi > 0) (F : TwoLeaderFrame n) :
    StopNode (UnshieldState hpsi F) → StopNode ((Fin n → AgentState psi))
  | .active z => .active z.val
  | .success => .success
  | .failure => .failure

theorem unshieldStep_erases (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (x : StopNode (UnshieldState hpsi F)) (e : Fin n) :
    eraseUnshield hpsi F (stepNode (unshieldStep hpsi F) x e) =
      stepNode (unshieldRawStep hpsi F) (eraseUnshield hpsi F x) e := by
  classical
  cases x with
  | success => rfl
  | failure => rfl
  | active z =>
      by_cases hs : UnshieldedOrDeleted F
        (rawConf hpsi F z.val (controlledPort F z.val e)) <;>
        simp [stepNode, unshieldStep, unshieldRawStep, hs, eraseUnshield]

private theorem unshield_tree_erases (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (w : StopNode ((Fin n → AgentState psi)) → Nat)
    (x : StopNode (UnshieldState hpsi F)) (T : Nat) :
    treeWeight (unshieldStep hpsi F) (fun y => w (eraseUnshield hpsi F y)) x T =
      treeWeight (unshieldRawStep hpsi F) w (eraseUnshield hpsi F x) T := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      simp only [treeWeight]
      apply ofFn_sum_eq
      intro e
      rw [ih, unshieldStep_erases]

noncomputable def unshieldWork (hpsi : psi > 0) (F : TwoLeaderFrame n) :
    StopNode (UnshieldState hpsi F) → Nat
  | .active z => 1 + gapWC F.recovery z.val
  | .success => 0
  | .failure => 0

noncomputable def unshieldPotential (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (x : StopNode (UnshieldState hpsi F)) : Nat := n * unshieldWork hpsi F x

private theorem child_work_le (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : UnshieldState hpsi F) (e : Fin n) :
    unshieldWork hpsi F (unshieldStep hpsi F z e) ≤
      1 + gapWC F.recovery
        (rawConf hpsi F z.val (controlledPort F z.val e)) := by
  classical
  unfold unshieldStep
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

private theorem ready_child_le_one (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : UnshieldState hpsi F) (hr : SharedReady F z.val) (e : Fin n) :
    unshieldWork hpsi F (unshieldStep hpsi F z e) ≤ 1 := by
  classical
  by_cases ha : e = preparePort F
  · subst e
    have he : UnshieldedOrDeleted F
        (rawConf hpsi F z.val (controlledPort F z.val (preparePort F))) := by
      rw [controlledPort_prepare]
      exact .inl (prepare_unshields hpsi F z.val z.property hr)
    simp only [unshieldStep, dif_pos he, unshieldWork, Nat.zero_le]
  · by_cases hb : e = deletePort F
    · subst e
      have he : UnshieldedOrDeleted F
          (rawConf hpsi F z.val (controlledPort F z.val (deletePort F))) := by
        rw [controlledPort_delete_ready F z.val hr]
        exact .inl (prepare_unshields hpsi F z.val z.property hr)
      simp only [unshieldStep, dif_pos he, unshieldWork, Nat.zero_le]
    · unfold unshieldStep
      split
      · exact Nat.zero_le _
      · rename_i hn
        have hg := unshield_next_gap hpsi F z e hn
        have hsig : SharedReady F
            (rawConf hpsi F z.val (controlledPort F z.val e)) := by
          rw [controlledPort_of_ne_delete F z.val e hb]
          unfold SharedReady
          rw [shared_frame hpsi F z.val e ha hb]
          exact hr
        have hclean : CleanReady F.recovery
            (rawConf hpsi F z.val (controlledPort F z.val e)) := by
          apply (cleanReady_iff_shooter_signal hpsi F.recovery _ hg.1).mpr
          change (rawConf hpsi F z.val (controlledPort F z.val e)
            (F.recovery.pos F.recovery.d)).signal_B = (1 : Fin 2)
          rw [F.shared_endpoint]
          exact hsig
        have hd : GapDoneC F.recovery
            (rawConf hpsi F z.val (controlledPort F z.val e)) := .inl hclean
        change 1 + gapWC F.recovery
          (rawConf hpsi F z.val (controlledPort F z.val e)) ≤ 1
        simp only [gapWC, if_pos hd, Nat.add_zero, Nat.le_refl]

private theorem ready_work_row (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : UnshieldState hpsi F) (hr : SharedReady F z.val) :
    1 + (List.ofFn (fun e => unshieldWork hpsi F (unshieldStep hpsi F z e))).sum ≤
      n * unshieldWork hpsi F (.active z) := by
  classical
  have hc : CleanReady F.recovery z.val := by
    apply (cleanReady_iff_shooter_signal hpsi F.recovery _ z.property.1).mpr
    simpa only [F.shared_endpoint, deletePort, SharedReady] using hr
  have hd : GapDoneC F.recovery z.val := .inl hc
  have hw : unshieldWork hpsi F (.active z) = 1 := by
    simp only [unshieldWork, gapWC, if_pos hd, Nat.add_zero]
  have he : UnshieldedOrDeleted F
      (rawConf hpsi F z.val (controlledPort F z.val (preparePort F))) := by
    rw [controlledPort_prepare]
    exact .inl (prepare_unshields hpsi F z.val z.property hr)
  have hdrop : unshieldWork hpsi F (unshieldStep hpsi F z (preparePort F)) + 1 ≤ 1 := by
    simp only [unshieldStep, dif_pos he, unshieldWork, Nat.zero_add, Nat.le_refl]
  have hs := LDSinkGapCleanup.ofFn_sum_lt n
    (fun e => unshieldWork hpsi F (unshieldStep hpsi F z e)) 1 (preparePort F)
    (ready_child_le_one hpsi F z hr) hdrop
  rw [hw]
  omega

private theorem nonready_work_row (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : UnshieldState hpsi F) (hr : ¬ SharedReady F z.val) :
    1 + (List.ofFn (fun e => unshieldWork hpsi F (unshieldStep hpsi F z e))).sum ≤
      n * unshieldWork hpsi F (.active z) := by
  have hn : ¬ GapDoneC F.recovery z.val := by
    rintro (hc | hl | hh)
    · apply hr
      have hsig := hc.1
      rw [F.shared_endpoint] at hsig
      exact hsig
    · have he := z.property.1.1.1
      rw [he] at hl
      cases hl
    · have he := z.property.1.1.2
      rw [he] at hh
      cases hh
  have hmono : ∀ e : Fin n,
      unshieldWork hpsi F (unshieldStep hpsi F z e) ≤ unshieldWork hpsi F (.active z) := by
    intro e
    have hb := child_work_le hpsi F z e
    have hconf : rawConf hpsi F z.val e = sinkStepC hpsi F.recovery z.val e :=
      rawConf_eq_gap hpsi F F.recovery z.val e
    rw [controlledPort_of_not_ready F z.val hr e, hconf] at hb
    exact Nat.le_trans hb (Nat.add_le_add_left
      (gapWC_step_le' hpsi F.recovery z.val z.property.1 hn e) 1)
  obtain ⟨e, he⟩ := exists_gapWC_step_lt' hpsi F.recovery z.val z.property.1 hn
  have hdrop : unshieldWork hpsi F (unshieldStep hpsi F z e) + 1 ≤
      unshieldWork hpsi F (.active z) := by
    have hb := child_work_le hpsi F z e
    have hconf : rawConf hpsi F z.val e = sinkStepC hpsi F.recovery z.val e :=
      rawConf_eq_gap hpsi F F.recovery z.val e
    rw [controlledPort_of_not_ready F z.val hr e, hconf] at hb
    change _ ≤ 1 + gapWC F.recovery z.val
    omega
  have hs := LDSinkGapCleanup.ofFn_sum_lt n
    (fun e => unshieldWork hpsi F (unshieldStep hpsi F z e))
    (unshieldWork hpsi F (.active z)) e hmono hdrop
  omega

theorem unshield_bellman (hpsi : psi > 0) (F : TwoLeaderFrame n) :
    NatBellmanSuperSolution (unshieldStep hpsi F) 1 (unshieldPotential hpsi F) := by
  classical
  refine ⟨rfl, rfl, ?_⟩
  intro z
  have hrow : 1 + (List.ofFn (fun e =>
      unshieldWork hpsi F (unshieldStep hpsi F z e))).sum ≤
      n * unshieldWork hpsi F (.active z) := by
    by_cases hr : SharedReady F z.val
    · exact ready_work_row hpsi F z hr
    · exact nonready_work_row hpsi F z hr
  change 1 * n + (List.ofFn (fun e =>
    n * unshieldWork hpsi F (unshieldStep hpsi F z e))).sum ≤
      n * (n * unshieldWork hpsi F (.active z))
  rw [Nat.one_mul, ofFn_sum_mul_left]
  have hs := Nat.mul_le_mul_left n hrow
  simpa only [Nat.mul_add, Nat.mul_one] using hs

theorem unshield_truncated_cost (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : UnshieldState hpsi F) (T : Nat) :
    truncatedActiveCostNumerator (unshieldStep hpsi F) (.active z) T ≤
      n ^ T * (n * (2 * F.recovery.d + 1)) := by
  have hc := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (unshieldStep hpsi F) 1 (unshieldPotential hpsi F) (unshield_bellman hpsi F) (.active z) T
  have hr := gapWC_le_two_d hpsi F.recovery z.val z.property.1
  have hp : unshieldPotential hpsi F (.active z) ≤ n * (2 * F.recovery.d + 1) := by
    apply Nat.mul_le_mul_left
    change 1 + gapWC F.recovery z.val ≤ _
    omega
  exact Nat.le_trans (by simpa only [Nat.one_mul] using hc)
    (Nat.mul_le_mul_left (n ^ T) hp)

private theorem unshield_no_failure (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : UnshieldState hpsi F) (e : Fin n) : unshieldStep hpsi F z e ≠ .failure := by
  classical
  unfold unshieldStep
  split <;> intro he <;> cases he

theorem unshield_half (hpsi : psi > 0) (F : TwoLeaderFrame n) (z : UnshieldState hpsi F) :
    n ^ (2 * n * (2 * F.recovery.d + 1)) ≤
      2 * successCount (unshieldStep hpsi F) (.active z)
        (2 * n * (2 * F.recovery.d + 1)) := by
  let T := 2 * n * (2 * F.recovery.d + 1)
  have hp : 0 < T := by
    have hn := F.recovery.ring.hn
    dsimp only [T]
    exact Nat.mul_pos (Nat.mul_pos (by decide) hn) (by omega)
  have hc := unshield_truncated_cost hpsi F z T
  have hactive := two_mul_activeCount_le_pow_of_scaled_cost
    (unshieldStep hpsi F) (.active z) hp (by decide : 0 < 1)
    (num := n * (2 * F.recovery.d + 1))
    (by simpa only [Nat.one_mul, Nat.mul_comm] using hc)
    (by dsimp only [T]; simp only [Nat.mul_one, Nat.mul_assoc, Nat.le_refl])
  have hf := BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure
    (unshieldStep hpsi F) (unshield_no_failure hpsi F) z T
  have hparts := node_count_partition (unshieldStep hpsi F) (.active z) T
  change n ^ T ≤ 2 * successCount (unshieldStep hpsi F) (.active z) T
  omega

/-- The first-unshield service is derived for every initial physical gap
pair, with its recovery-length cost and its actual post-state stopping target. -/
theorem gapPair_unshield_half (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (b : (Fin n → AgentState psi)) (hg : WrapInvariant hpsi F b) :
    n ^ (2 * n * (2 * F.recovery.d + 1)) ≤
      2 * successCount (unshieldRawStep hpsi F) (.active b)
        (2 * n * (2 * F.recovery.d + 1)) := by
  let z : UnshieldState hpsi F := ⟨b, hg⟩
  have hs := unshield_half hpsi F z
  have hw : (fun y => successWeight (eraseUnshield hpsi F y)) = successWeight := by
    funext y
    cases y <;> rfl
  have he := unshield_tree_erases hpsi F successWeight (.active z)
    (2 * n * (2 * F.recovery.d + 1))
  rw [hw] at he
  change successCount (unshieldStep hpsi F) (.active z) _ =
    successCount (unshieldRawStep hpsi F) (.active b) _ at he
  rwa [he] at hs

/-!
The first collapsed ready event already completes this service.  The exact
bounded-event theorem therefore transfers its half mass with budget one,
without any multi-dummy service hypothesis.
-/

/-- Stop only after an actual unredirected K2 row unshields the victim or
deletes a real endpoint.  The continuing configuration is the raw successor. -/
noncomputable def originalUnshieldStep (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState psi) (e : Fin n) : StopNode (Fin n → AgentState psi) := by
  classical
  exact if UnshieldedOrDeleted F (rawConf hpsi F C e) then .success
    else .active (rawConf hpsi F C e)

theorem original_controlled_eq (hpsi : psi > 0) (F : TwoLeaderFrame n) :
    ControlledSchedulerMass.controlledStep (originalUnshieldStep hpsi F) (redirection F) =
      unshieldRawStep hpsi F := by
  funext C e
  unfold ControlledSchedulerMass.controlledStep
  rw [effective_eq]
  rfl

/-- Every collapsed event, including an original A choice, ends unshield
service on that very interaction. -/
theorem collapse_completes_unshield (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState psi) (hg : WrapInvariant hpsi F C) (e : Fin n)
    (hc : (redirection F).Collapses C e) : unshieldRawStep hpsi F C e = .success := by
  classical
  obtain ⟨hr, he⟩ := (collapses_iff F C e).mp hc
  have hp : controlledPort F C e = preparePort F := by
    rcases he with rfl | rfl
    · exact controlledPort_prepare F C
    · exact controlledPort_delete_ready F C hr
  have hs : UnshieldedOrDeleted F (rawConf hpsi F C (preparePort F)) :=
    .inl (prepare_unshields hpsi F C hg hr)
  simp only [unshieldRawStep, hp, if_pos hs]

/-- A budget of one never rejects a live unshield-service path. -/
theorem unshield_audit_row (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : UnshieldState hpsi F) (e : Fin n) :
    ControlledSchedulerMass.auditStep (originalUnshieldStep hpsi F) (redirection F)
      (z.val, 1) e = ControlledSchedulerMass.withBudget 1 (unshieldRawStep hpsi F z.val e) := by
  classical
  unfold ControlledSchedulerMass.auditStep
  by_cases hc : (redirection F).Collapses z.val e
  · rw [if_pos hc, original_controlled_eq,
      collapse_completes_unshield hpsi F z.val z.property e hc]
    rfl
  · rw [if_neg hc, original_controlled_eq]

def eraseAudited (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (x : StopNode (UnshieldState hpsi F)) : StopNode ((Fin n → AgentState psi) × Nat) :=
  ControlledSchedulerMass.withBudget 1 (eraseUnshield hpsi F x)

theorem unshield_audit_erases (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (x : StopNode (UnshieldState hpsi F)) (e : Fin n) :
    eraseAudited hpsi F (stepNode (unshieldStep hpsi F) x e) =
      stepNode (ControlledSchedulerMass.auditStep (originalUnshieldStep hpsi F)
        (redirection F)) (eraseAudited hpsi F x) e := by
  cases x with
  | success => rfl
  | failure => rfl
  | active z =>
    change ControlledSchedulerMass.withBudget 1
      (eraseUnshield hpsi F (stepNode (unshieldStep hpsi F) (.active z) e)) = _
    rw [unshieldStep_erases]
    exact (unshield_audit_row hpsi F z e).symm

theorem unshield_audit_simulation (hpsi : psi > 0) (F : TwoLeaderFrame n) :
    LDSinkTwoGapDeletion.SuccessSimulation (unshieldStep hpsi F)
      (ControlledSchedulerMass.auditStep (originalUnshieldStep hpsi F) (redirection F))
      (fun x y => eraseAudited hpsi F x = y) where
  terminal := by
    intro x y h
    rw [← h]
    cases x <;> exact Nat.le_refl _
  next := by
    intro x y h e
    rw [← h]
    exact unshield_audit_erases hpsi F x e

/-- Uniform original-scheduler first-unshield/deletion service.  Its factor
four is the proved controlled half mass times the exact one-event transfer. -/
theorem original_unshield_quarter (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState psi) (hg : WrapInvariant hpsi F C) :
    n ^ (2 * n * (2 * F.recovery.d + 1)) ≤
      4 * successCount (originalUnshieldStep hpsi F) (.active C)
        (2 * n * (2 * F.recovery.d + 1)) := by
  let z : UnshieldState hpsi F := ⟨C, hg⟩
  let T := 2 * n * (2 * F.recovery.d + 1)
  have hm := unshield_half hpsi F z
  have hs := LDSinkTwoGapDeletion.successCount_le_of_simulation (unshieldStep hpsi F)
    (ControlledSchedulerMass.auditStep (originalUnshieldStep hpsi F) (redirection F))
    (fun x y => eraseAudited hpsi F x = y) (unshield_audit_simulation hpsi F)
    (.active z) (.active (C, 1)) rfl T
  have hb : n ^ T ≤ 2 * ControlledSchedulerMass.boundedSuccessCount
      (originalUnshieldStep hpsi F) (redirection F) (.active C) T 1 :=
    Nat.le_trans hm (Nat.mul_le_mul_left 2 hs)
  exact ControlledSchedulerMass.raw_success_mass_lower (originalUnshieldStep hpsi F)
    (redirection F) (.active C) T 1 2 hb

/-- The success edge carries the same physical configuration into the next
service: either real endpoint deletion or both gap invariants and false shield. -/
theorem original_unshield_handoff (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState psi) (hg : WrapInvariant hpsi F C) (e : Fin n)
    (he : originalUnshieldStep hpsi F C e = .success) :
    Deleted F (rawConf hpsi F C e) ∨
      (WrapInvariant hpsi F (rawConf hpsi F C e) ∧
        (rawConf hpsi F C e (deletePort F)).shield = false) := by
  classical
  have hs : UnshieldedOrDeleted F (rawConf hpsi F C e) := by
    unfold originalUnshieldStep at he
    split at he
    · assumption
    · cases he
  by_cases hd : Deleted F (rawConf hpsi F C e)
  · exact .inl hd
  · exact .inr ⟨rawConf_invariant hpsi F C hg e hd, hs.resolve_right hd⟩

end K2TwoLeaderEntranceUnshield

#print axioms K2TwoLeaderEntranceUnshield.prepare_unshields
#print axioms K2TwoLeaderEntranceUnshield.unshieldStep_erases
#print axioms K2TwoLeaderEntranceUnshield.unshield_bellman
#print axioms K2TwoLeaderEntranceUnshield.unshield_truncated_cost
#print axioms K2TwoLeaderEntranceUnshield.gapPair_unshield_half
#print axioms K2TwoLeaderEntranceUnshield.collapse_completes_unshield
#print axioms K2TwoLeaderEntranceUnshield.unshield_audit_erases
#print axioms K2TwoLeaderEntranceUnshield.original_unshield_quarter
#print axioms K2TwoLeaderEntranceUnshield.original_unshield_handoff
