import Leader.Wu.RaceEntrance.DummyService

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkProtectedAbsorption LDSinkGapDoneInvariant LDSinkGapServiceRank LDSinkGapCleanupBound
open LDTwoGapFrame LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptResidual
open LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant
open LDSinkTwoGapArrivalRaceMass LDSinkTwoGapRaceEntranceLocalService
open LDSinkTwoGapRaceEntranceControlledTail LDSinkTwoGapRaceEntranceColourCoupling

namespace LDSinkTwoGapRaceEntranceUnshieldService

variable {n psi : Nat}

/-!
The first controlled incoming FIRE removes the shared leader's old shield.
Until it is ready, control is the identity and the actual recovery cleanup
rank supplies service.  At readiness the incoming row really fires and
moves a dummy, while neutral rows preserve readiness.  This initial service
cost depends on the recovery length and cannot be charged to a short attack
gap without an additional global argument.
-/

def UnshieldedOrDeleted (F : TwoGapFrame n) (C : Fin n → AgentState psi) : Prop :=
  (C (deletePort F)).shield = false ∨ NoResetSuccess F C

abbrev UnshieldState (hpsi : psi > 0) (F : TwoGapFrame n) :=
  { b : AState n psi // GapPair hpsi F b }

theorem prepare_unshields (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b) (hr : SharedReady F b.conf) :
    (attemptStepConf hpsi F b (preparePort F) (deletePort F)).shield = false := by
  have hd := F.recovery.hd
  have hp : F.recovery.d - 1 + 1 = F.recovery.d := by omega
  have ha : (b.conf (deletePort F)).label = nextLabel hpsi (b.conf (preparePort F)) := by
    have h := hg.recovery.2.2.1 (F.recovery.d - 1) (by omega)
    simpa only [hp, F.shared, preparePort, deletePort] using h
  have hrow := incoming_fire_pair hpsi (b.conf (preparePort F)) (b.conf (deletePort F))
    (hg.recovery.2.1 (F.recovery.d - 1) (by omega) (by omega)) hg.attack.1.1 hr ha
  rw [attemptStepConf_eq_sinkStepC, sinkStepC, preparePort_right,
    updatePair_responder _ _ _ _ (preparePort_ne_deletePort F).symm, hrow]

private theorem unshield_next_gap (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : UnshieldState hpsi F) (e : Fin n)
    (hn : ¬ UnshieldedOrDeleted F
      (attemptStepConf hpsi F z.val (controlledPort F z.val.conf e))) :
    GapPair hpsi F (postState hpsi F z.val (controlledPort F z.val.conf e)) := by
  classical
  apply LDSinkTwoGapRestartClosure.gapPair_physical_step hpsi F
    (CleanBoundaryDecision.restartCleanBoundarySignalResidual_K2 hpsi F)
    z.val (controlledPort F z.val.conf e) _ z.property
  rw [physicalBlockStep_normal_form, if_neg (fun h => hn (.inr h))]

noncomputable def unshieldStep (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : UnshieldState hpsi F) (e : Fin n) : StopNode (UnshieldState hpsi F) := by
  classical
  exact if h : UnshieldedOrDeleted F
      (attemptStepConf hpsi F z.val (controlledPort F z.val.conf e)) then .success
    else .active ⟨postState hpsi F z.val (controlledPort F z.val.conf e),
      unshield_next_gap hpsi F z e h⟩

noncomputable def unshieldRawStep (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (e : Fin n) : StopNode (AState n psi) := by
  classical
  exact if UnshieldedOrDeleted F
      (attemptStepConf hpsi F b (controlledPort F b.conf e)) then .success
    else .active (postState hpsi F b (controlledPort F b.conf e))

def eraseUnshield (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (UnshieldState hpsi F) → StopNode (AState n psi)
  | .active z => .active z.val
  | .success => .success
  | .failure => .failure

theorem unshieldStep_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (UnshieldState hpsi F)) (e : Fin n) :
    eraseUnshield hpsi F (stepNode (unshieldStep hpsi F) x e) =
      stepNode (unshieldRawStep hpsi F) (eraseUnshield hpsi F x) e := by
  classical
  cases x with
  | success => rfl
  | failure => rfl
  | active z =>
      by_cases hs : UnshieldedOrDeleted F
        (attemptStepConf hpsi F z.val (controlledPort F z.val.conf e)) <;>
        simp [stepNode, unshieldStep, unshieldRawStep, hs, eraseUnshield]

private theorem unshield_tree_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (w : StopNode (AState n psi) → Nat)
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

noncomputable def unshieldWork (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (UnshieldState hpsi F) → Nat
  | .active z => 1 + gapWC F.recovery z.val.conf
  | .success => 0
  | .failure => 0

noncomputable def unshieldPotential (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (UnshieldState hpsi F)) : Nat := n * unshieldWork hpsi F x

private theorem child_work_le (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : UnshieldState hpsi F) (e : Fin n) :
    unshieldWork hpsi F (unshieldStep hpsi F z e) ≤
      1 + gapWC F.recovery
        (attemptStepConf hpsi F z.val (controlledPort F z.val.conf e)) := by
  classical
  unfold unshieldStep
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

private theorem ready_child_le_one (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : UnshieldState hpsi F) (hr : SharedReady F z.val.conf) (e : Fin n) :
    unshieldWork hpsi F (unshieldStep hpsi F z e) ≤ 1 := by
  classical
  by_cases ha : e = preparePort F
  · subst e
    have he : UnshieldedOrDeleted F
        (attemptStepConf hpsi F z.val (controlledPort F z.val.conf (preparePort F))) := by
      rw [controlledPort_prepare]
      exact .inl (prepare_unshields hpsi F z.val z.property hr)
    simp only [unshieldStep, dif_pos he, unshieldWork, Nat.zero_le]
  · by_cases hb : e = deletePort F
    · subst e
      have he : UnshieldedOrDeleted F
          (attemptStepConf hpsi F z.val (controlledPort F z.val.conf (deletePort F))) := by
        rw [controlledPort_delete_ready F z.val.conf hr]
        exact .inl (prepare_unshields hpsi F z.val z.property hr)
      simp only [unshieldStep, dif_pos he, unshieldWork, Nat.zero_le]
    · unfold unshieldStep
      split
      · exact Nat.zero_le _
      · rename_i hn
        have hg := unshield_next_gap hpsi F z e hn
        have hsig : SharedReady F
            (attemptStepConf hpsi F z.val (controlledPort F z.val.conf e)) := by
          rw [controlledPort_of_ne_delete F z.val.conf e hb]
          unfold SharedReady
          rw [attemptStepConf_eq_sinkStepC, shared_frame hpsi F z.val.conf e ha hb]
          exact hr
        have hclean : CleanReady F.recovery
            (attemptStepConf hpsi F z.val (controlledPort F z.val.conf e)) := by
          apply (cleanReady_iff_shooter_signal hpsi F.recovery _ hg.recovery).mpr
          change (attemptStepConf hpsi F z.val (controlledPort F z.val.conf e)
            (F.recovery.pos F.recovery.d)).signal_B = (1 : Fin 2)
          rw [F.shared]
          exact hsig
        have hd : GapDoneC F.recovery
            (attemptStepConf hpsi F z.val (controlledPort F z.val.conf e)) := .inl hclean
        change 1 + gapWC F.recovery
          (attemptStepConf hpsi F z.val (controlledPort F z.val.conf e)) ≤ 1
        simp only [gapWC, if_pos hd, Nat.add_zero, Nat.le_refl]

private theorem ready_work_row (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : UnshieldState hpsi F) (hr : SharedReady F z.val.conf) :
    1 + (List.ofFn (fun e => unshieldWork hpsi F (unshieldStep hpsi F z e))).sum ≤
      n * unshieldWork hpsi F (.active z) := by
  classical
  have hc : CleanReady F.recovery z.val.conf := by
    apply (cleanReady_iff_shooter_signal hpsi F.recovery _ z.property.recovery).mpr
    simpa only [F.shared, deletePort, SharedReady] using hr
  have hd : GapDoneC F.recovery z.val.conf := .inl hc
  have hw : unshieldWork hpsi F (.active z) = 1 := by
    simp only [unshieldWork, gapWC, if_pos hd, Nat.add_zero]
  have he : UnshieldedOrDeleted F
      (attemptStepConf hpsi F z.val (controlledPort F z.val.conf (preparePort F))) := by
    rw [controlledPort_prepare]
    exact .inl (prepare_unshields hpsi F z.val z.property hr)
  have hdrop : unshieldWork hpsi F (unshieldStep hpsi F z (preparePort F)) + 1 ≤ 1 := by
    simp only [unshieldStep, dif_pos he, unshieldWork, Nat.zero_add, Nat.le_refl]
  have hs := LDSinkGapCleanup.ofFn_sum_lt n
    (fun e => unshieldWork hpsi F (unshieldStep hpsi F z e)) 1 (preparePort F)
    (ready_child_le_one hpsi F z hr) hdrop
  rw [hw]
  omega

private theorem nonready_work_row (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : UnshieldState hpsi F) (hr : ¬ SharedReady F z.val.conf) :
    1 + (List.ofFn (fun e => unshieldWork hpsi F (unshieldStep hpsi F z e))).sum ≤
      n * unshieldWork hpsi F (.active z) := by
  have hn : ¬ GapDoneC F.recovery z.val.conf := by
    rintro (hc | hl | hh)
    · apply hr
      have hsig := hc.1
      rw [F.shared] at hsig
      exact hsig
    · have he := z.property.recovery.1.1
      rw [he] at hl
      cases hl
    · have he := z.property.recovery.1.2
      rw [he] at hh
      cases hh
  have hmono : ∀ e : Fin n,
      unshieldWork hpsi F (unshieldStep hpsi F z e) ≤ unshieldWork hpsi F (.active z) := by
    intro e
    have hb := child_work_le hpsi F z e
    have hconf : attemptStepConf hpsi F z.val e = sinkStepC hpsi F.recovery z.val.conf e :=
      postConf_eq_recovery hpsi F z.val e
    rw [controlledPort_of_not_ready F z.val.conf hr e, hconf] at hb
    exact Nat.le_trans hb (Nat.add_le_add_left
      (gapWC_step_le' hpsi F.recovery z.val.conf z.property.recovery hn e) 1)
  obtain ⟨e, he⟩ := exists_gapWC_step_lt' hpsi F.recovery z.val.conf z.property.recovery hn
  have hdrop : unshieldWork hpsi F (unshieldStep hpsi F z e) + 1 ≤
      unshieldWork hpsi F (.active z) := by
    have hb := child_work_le hpsi F z e
    have hconf : attemptStepConf hpsi F z.val e = sinkStepC hpsi F.recovery z.val.conf e :=
      postConf_eq_recovery hpsi F z.val e
    rw [controlledPort_of_not_ready F z.val.conf hr e, hconf] at hb
    change _ ≤ 1 + gapWC F.recovery z.val.conf
    omega
  have hs := LDSinkGapCleanup.ofFn_sum_lt n
    (fun e => unshieldWork hpsi F (unshieldStep hpsi F z e))
    (unshieldWork hpsi F (.active z)) e hmono hdrop
  omega

theorem unshield_bellman (hpsi : psi > 0) (F : TwoGapFrame n) :
    NatBellmanSuperSolution (unshieldStep hpsi F) 1 (unshieldPotential hpsi F) := by
  classical
  refine ⟨rfl, rfl, ?_⟩
  intro z
  have hrow : 1 + (List.ofFn (fun e =>
      unshieldWork hpsi F (unshieldStep hpsi F z e))).sum ≤
      n * unshieldWork hpsi F (.active z) := by
    by_cases hr : SharedReady F z.val.conf
    · exact ready_work_row hpsi F z hr
    · exact nonready_work_row hpsi F z hr
  change 1 * n + (List.ofFn (fun e =>
    n * unshieldWork hpsi F (unshieldStep hpsi F z e))).sum ≤
      n * (n * unshieldWork hpsi F (.active z))
  rw [Nat.one_mul, ofFn_sum_mul_left]
  have hs := Nat.mul_le_mul_left n hrow
  simpa only [Nat.mul_add, Nat.mul_one] using hs

theorem unshield_truncated_cost (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : UnshieldState hpsi F) (T : Nat) :
    truncatedActiveCostNumerator (unshieldStep hpsi F) (.active z) T ≤
      n ^ T * (n * (2 * F.recovery.d + 1)) := by
  have hc := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (unshieldStep hpsi F) 1 (unshieldPotential hpsi F) (unshield_bellman hpsi F) (.active z) T
  have hr := gapWC_le_two_d hpsi F.recovery z.val.conf z.property.recovery
  have hp : unshieldPotential hpsi F (.active z) ≤ n * (2 * F.recovery.d + 1) := by
    apply Nat.mul_le_mul_left
    change 1 + gapWC F.recovery z.val.conf ≤ _
    omega
  exact Nat.le_trans (by simpa only [Nat.one_mul] using hc)
    (Nat.mul_le_mul_left (n ^ T) hp)

private theorem unshield_no_failure (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : UnshieldState hpsi F) (e : Fin n) : unshieldStep hpsi F z e ≠ .failure := by
  classical
  unfold unshieldStep
  split <;> intro he <;> cases he

theorem unshield_half (hpsi : psi > 0) (F : TwoGapFrame n) (z : UnshieldState hpsi F) :
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
theorem gapPair_unshield_half (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b) :
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

end LDSinkTwoGapRaceEntranceUnshieldService

#print axioms LDSinkTwoGapRaceEntranceUnshieldService.prepare_unshields
#print axioms LDSinkTwoGapRaceEntranceUnshieldService.unshieldStep_erases
#print axioms LDSinkTwoGapRaceEntranceUnshieldService.unshield_bellman
#print axioms LDSinkTwoGapRaceEntranceUnshieldService.unshield_truncated_cost
#print axioms LDSinkTwoGapRaceEntranceUnshieldService.gapPair_unshield_half
