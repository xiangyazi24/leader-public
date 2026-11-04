import Leader.Wu.RaceEntrance.ControlledRank
import Leader.Wu.RaceEntrance.ControlledTail
import Leader.Wu.RaceEntrance.FreshService

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkProtectedAbsorption LDSinkGapDoneInvariant LDSinkGapServiceRank LDSinkGapCleanupBound
open LDTwoGapFrame LDSinkTwoGapNoResetKernel LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant
open LDSinkTwoGapRaceEntranceLocalService LDSinkTwoGapRaceEntranceFreshService
open LDSinkTwoGapArrivalRaceMass LDSinkTwoGapRaceEntranceControlledTail
open LDSinkTwoGapRaceEntranceControlledRank

namespace LDSinkTwoGapRaceEntranceControlledBirth

variable {n psi : Nat}

/-!
The stopping event here requires an actual outgoing FIRE from a clean attack
sector, or physical deletion.  Merely clearing an unrelated old bullet and
thereby obtaining a fresh-shot predicate does not stop this carrier.
The comparison scheduler always executes the same physical K2 successor.
-/

def BirthEvent (hpsi : psi > 0) (F : TwoGapFrame n) (b : AState n psi) (e : Fin n) : Prop :=
  NoResetSuccess F (attemptStepConf hpsi F b e) ∨
    (CleanReady F.attack b.conf ∧ e = outgoingPort F)

abbrev BirthState (hpsi : psi > 0) (F : TwoGapFrame n) :=
  { b : AState n psi // GapPair hpsi F b }

private theorem gapPair_after_not_event (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (e : Fin n)
    (hn : ¬ BirthEvent hpsi F z.val e) :
    GapPair hpsi F (postState hpsi F z.val e) := by
  classical
  apply LDSinkTwoGapRestartClosure.gapPair_physical_step hpsi F
    (CleanBoundaryDecision.restartCleanBoundarySignalResidual_K2 hpsi F)
    z.val e (postState hpsi F z.val e) z.property
  rw [physicalBlockStep_normal_form, if_neg (fun h => hn (.inl h))]

noncomputable def birthStep (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (e : Fin n) : StopNode (BirthState hpsi F) := by
  classical
  exact if h : BirthEvent hpsi F z.val e then .success
    else .active ⟨postState hpsi F z.val e, gapPair_after_not_event hpsi F z e h⟩

def birthBase (F : TwoGapFrame n) : Nat := 2 * F.attack.d + 1

noncomputable def birthWork (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (BirthState hpsi F) → Nat
  | .active z => birthBase F + gapWC F.attack z.val.conf
  | .success => 0
  | .failure => 0

noncomputable def birthPotential (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (BirthState hpsi F)) : Nat := n * birthWork hpsi F x

private theorem child_work_le (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (e : Fin n) :
    birthWork hpsi F (birthStep hpsi F z e) ≤
      birthBase F + gapWC F.attack (attemptStepConf hpsi F z.val e) := by
  classical
  unfold birthStep
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

private theorem child_work_le_bound (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (e : Fin n) :
    birthWork hpsi F (birthStep hpsi F z e) ≤ birthBase F + 2 * F.attack.d := by
  classical
  unfold birthStep
  split
  · exact Nat.zero_le _
  · rename_i hn
    have hg := gapPair_after_not_event hpsi F z e hn
    exact Nat.add_le_add_left (gapWC_le_two_d hpsi F.attack _ hg.attack) _

private theorem outgoing_work_zero (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (hc : CleanReady F.attack z.val.conf) :
    birthWork hpsi F (birthStep hpsi F z (outgoingPort F)) = 0 := by
  classical
  have hs : BirthEvent hpsi F z.val (outgoingPort F) := .inr ⟨hc, rfl⟩
  simp [birthStep, hs, birthWork]

private theorem neutral_work_le (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (hc : CleanReady F.attack z.val.conf) (e : Fin n)
    (ho : e ≠ outgoingPort F) (hi : e ≠ incomingPort F) :
    birthWork hpsi F (birthStep hpsi F z e) ≤ birthBase F := by
  classical
  unfold birthStep
  split
  · exact Nat.zero_le _
  · rename_i hn
    have hclean := (clean_neutral hpsi F z.val z.property hc e ho hi
      (fun h => hn (.inl h))).2
    have hd : GapDoneC F.attack (attemptStepConf hpsi F z.val e) := .inl hclean
    change birthBase F + gapWC F.attack (attemptStepConf hpsi F z.val e) ≤ _
    simp [gapWC, hd]

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

/-- The extra `2*d+1` pays the exact clean-to-dummy reset in average. -/
private theorem clean_work_row (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (hc : CleanReady F.attack z.val.conf) :
    1 + (List.ofFn (fun e : Fin n => birthWork hpsi F (birthStep hpsi F z e))).sum ≤
      n * birthWork hpsi F (.active z) := by
  classical
  let f := fun e : Fin n => birthWork hpsi F (birthStep hpsi F z e)
  have hports : outgoingPort F ≠ incomingPort F := (firingPorts F).ab
  have hrow : ∀ e : Fin n,
      f e + (if e = outgoingPort F then birthBase F else 0) ≤
        birthBase F + (if e = incomingPort F then 2 * F.attack.d else 0) := by
    intro e
    by_cases ho : e = outgoingPort F
    · subst e
      simp [f, outgoing_work_zero hpsi F z hc, hports]
    · by_cases hi : e = incomingPort F
      · simpa [f, ho, hi, hports.symm] using child_work_le_bound hpsi F z (incomingPort F)
      · simpa [ho, hi, f] using neutral_work_le hpsi F z hc e ho hi
  have hsum := ofFn_sum_le _ _ hrow
  rw [ofFn_sum_add, ofFn_sum_add, sum_spike, sum_spike,
    FiniteUniformStoppingTree.ofFn_sum_const] at hsum
  have hzero : gapWC F.attack z.val.conf = 0 := by
    have hd : GapDoneC F.attack z.val.conf := .inl hc
    simp [gapWC, hd]
  change 1 + _ ≤ n * (birthBase F + gapWC F.attack z.val.conf)
  rw [hzero, Nat.add_zero]
  dsimp only [f, birthBase] at hsum ⊢
  omega

private theorem nonclean_work_row (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (hc : ¬ CleanReady F.attack z.val.conf) :
    1 + (List.ofFn (fun e : Fin n => birthWork hpsi F (birthStep hpsi F z e))).sum ≤
      n * birthWork hpsi F (.active z) := by
  have hn : ¬ GapDoneC F.attack z.val.conf := by
    rintro (hd | hl | hr)
    · exact hc hd
    · have he := z.property.attack.1.1
      rw [he] at hl
      cases hl
    · have he := z.property.attack.1.2
      rw [he] at hr
      cases hr
  have hmono : ∀ e : Fin n,
      birthWork hpsi F (birthStep hpsi F z e) ≤ birthWork hpsi F (.active z) := by
    intro e
    have h1 := child_work_le hpsi F z e
    have h2 := gapWC_step_le' hpsi F.attack z.val.conf z.property.attack hn e
    change _ ≤ birthBase F + gapWC F.attack z.val.conf
    exact Nat.le_trans h1 (Nat.add_le_add_left h2 _)
  obtain ⟨e, he⟩ := exists_gapWC_step_lt' hpsi F.attack z.val.conf z.property.attack hn
  have hdrop : birthWork hpsi F (birthStep hpsi F z e) + 1 ≤
      birthWork hpsi F (.active z) := by
    have hb := child_work_le hpsi F z e
    change _ ≤ birthBase F + gapWC F.attack z.val.conf
    change gapWC F.attack (attemptStepConf hpsi F z.val e) < _ at he
    omega
  have hs := LDSinkGapCleanup.ofFn_sum_lt n
    (fun e => birthWork hpsi F (birthStep hpsi F z e))
    (birthWork hpsi F (.active z)) e hmono hdrop
  omega

private theorem birth_bellman (hpsi : psi > 0) (F : TwoGapFrame n) :
    NatBellmanSuperSolution (birthStep hpsi F) 1 (birthPotential hpsi F) := by
  classical
  refine ⟨rfl, rfl, ?_⟩
  intro z
  have hrow : 1 + (List.ofFn (fun e : Fin n =>
      birthWork hpsi F (birthStep hpsi F z e))).sum ≤
      n * birthWork hpsi F (.active z) := by
    by_cases hc : CleanReady F.attack z.val.conf
    · exact clean_work_row hpsi F z hc
    · exact nonclean_work_row hpsi F z hc
  change 1 * n + (List.ofFn (fun e : Fin n =>
    n * birthWork hpsi F (birthStep hpsi F z e))).sum ≤
      n * (n * birthWork hpsi F (.active z))
  rw [Nat.one_mul, ofFn_sum_mul_left]
  have hs := Nat.mul_le_mul_left n hrow
  simpa only [Nat.mul_add, Nat.mul_one] using hs

noncomputable def controlledBirthStep (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (e : Fin n) : StopNode (BirthState hpsi F) :=
  birthStep hpsi F z (controlledPort F z.val.conf e)

noncomputable def readyWork (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (BirthState hpsi F) → Nat := by
  classical
  exact fun x => match x with
    | .active z => if SharedReady F z.val.conf then 1 else 0
    | .success => 0
    | .failure => 0

noncomputable def correctedWork (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (BirthState hpsi F)) : Nat :=
  3 * birthWork hpsi F x + 2 * readyWork hpsi F x

noncomputable def correctedPotential (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (BirthState hpsi F)) : Nat := n * correctedWork hpsi F x

private theorem prepare_ne_outgoing (F : TwoGapFrame n) :
    preparePort F ≠ outgoingPort F :=
  F.recovery_before_shared_ne_attack (F.recovery.d - 1) F.attack.d
    (by have h := F.recovery.hd; omega) (Nat.le_refl _)

private theorem delete_ne_outgoing (F : TwoGapFrame n) :
    deletePort F ≠ outgoingPort F := (firingPorts F).ac.symm

private theorem prepare_not_event (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) : ¬ BirthEvent hpsi F z.val (preparePort F) := by
  rintro (hs | ⟨_, he⟩)
  · exact prepare_not_success hpsi F z.val z.property hs
  · exact prepare_ne_outgoing F he

private theorem ready_delete_not_event (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (hr : SharedReady F z.val.conf) :
    ¬ BirthEvent hpsi F z.val (deletePort F) := by
  rintro (hs | ⟨_, he⟩)
  · exact ready_delete_not_success hpsi F z.val z.property hr hs
  · exact delete_ne_outgoing F he

private theorem prepare_work_eq (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) :
    birthWork hpsi F (birthStep hpsi F z (preparePort F)) =
      birthWork hpsi F (.active z) := by
  classical
  unfold birthStep
  rw [dif_neg (prepare_not_event hpsi F z)]
  change birthBase F + gapWC F.attack
    (sinkStepC hpsi F.attack z.val.conf (preparePort F)) =
      birthBase F + gapWC F.attack z.val.conf
  rw [prepare_attack_rank_eq]

private theorem ready_redirection_loss (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (hr : SharedReady F z.val.conf) :
    birthWork hpsi F (birthStep hpsi F z (preparePort F)) ≤
      birthWork hpsi F (birthStep hpsi F z (deletePort F)) + 2 := by
  classical
  rw [prepare_work_eq]
  unfold birthStep
  rw [dif_neg (ready_delete_not_event hpsi F z hr)]
  change birthBase F + gapWC F.attack z.val.conf ≤
    birthBase F + gapWC F.attack (sinkStepC hpsi F.attack z.val.conf (F.attack.pos 0)) + 2
  by_cases hc : CleanReady F.attack z.val.conf
  · have hd : GapDoneC F.attack z.val.conf := .inl hc
    rw [gapWC, if_pos hd]
    omega
  · have hn : ¬ GapDoneC F.attack z.val.conf := by
      rintro (hh | hl | hr')
      · exact hc hh
      · have he := z.property.attack.1.1
        rw [he] at hl
        cases hl
      · have he := z.property.attack.1.2
        rw [he] at hr'
        cases hr'
    have h := ready_victim_rank_loss_le_two hpsi F.attack z.val.conf
      z.property.attack hn hr
    omega

private theorem controlled_base_ready_sum (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (hr : SharedReady F z.val.conf) :
    (List.ofFn (fun e => birthWork hpsi F (controlledBirthStep hpsi F z e))).sum ≤
      n * birthWork hpsi F (.active z) + 1 := by
  classical
  have hs : ∀ e : Fin n,
      birthWork hpsi F (controlledBirthStep hpsi F z e) ≤
        birthWork hpsi F (birthStep hpsi F z e) + (if e = deletePort F then 2 else 0) := by
    intro e
    by_cases he : e = deletePort F
    · subst e
      simpa only [controlledBirthStep, controlledPort_delete_ready F z.val.conf hr,
        if_pos rfl, ite_true] using ready_redirection_loss hpsi F z hr
    · simp only [controlledBirthStep, controlledPort_of_ne_delete F z.val.conf e he,
        if_neg he, Nat.add_zero, Nat.le_refl]
  have hsum := ofFn_sum_le _ _ hs
  rw [ofFn_sum_add, sum_spike] at hsum
  have hbase : 1 + (List.ofFn (fun e => birthWork hpsi F (birthStep hpsi F z e))).sum ≤
      n * birthWork hpsi F (.active z) := by
    by_cases hc : CleanReady F.attack z.val.conf
    · exact clean_work_row hpsi F z hc
    · exact nonclean_work_row hpsi F z hc
  omega

private theorem controlled_base_not_ready_sum (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (hr : ¬ SharedReady F z.val.conf) :
    1 + (List.ofFn (fun e => birthWork hpsi F (controlledBirthStep hpsi F z e))).sum ≤
      n * birthWork hpsi F (.active z) := by
  simp only [controlledBirthStep, controlledPort_of_not_ready F z.val.conf hr]
  by_cases hc : CleanReady F.attack z.val.conf
  · exact clean_work_row hpsi F z hc
  · exact nonclean_work_row hpsi F z hc

private theorem prepare_ready_signal_zero (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (hr : SharedReady F z.val.conf) :
    (attemptStepConf hpsi F z.val (preparePort F) (deletePort F)).signal_B = (0 : Fin 2) := by
  have hd := F.recovery.hd
  have hp : F.recovery.d - 1 + 1 = F.recovery.d := by omega
  have ha : (z.val.conf (deletePort F)).label =
      nextLabel hpsi (z.val.conf (preparePort F)) := by
    have h := z.property.recovery.2.2.1 (F.recovery.d - 1) (by omega)
    simpa only [hp, F.shared, deletePort, preparePort] using h
  have hrow := kernelC_prepare_responder hpsi
    (z.val.conf (preparePort F)) (z.val.conf (deletePort F))
    (z.property.recovery.2.1 (F.recovery.d - 1) (by omega) (by omega))
    z.property.attack.1.1 hr ha
  rw [attemptStepConf_eq_sinkStepC, sinkStepC, preparePort_right,
    updatePair_responder _ _ _ _ (preparePort_ne_deletePort F).symm]
  exact hrow.2.2.1

private theorem readyWork_le_one (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (BirthState hpsi F)) : readyWork hpsi F x ≤ 1 := by
  classical
  cases x with
  | success => exact Nat.zero_le _
  | failure => exact Nat.zero_le _
  | active z =>
      change (if SharedReady F z.val.conf then 1 else 0) ≤ 1
      split <;> decide

private theorem child_readyWork_zero (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (e : Fin n)
    (hs : (attemptStepConf hpsi F z.val (controlledPort F z.val.conf e)
      (deletePort F)).signal_B = (0 : Fin 2)) :
    readyWork hpsi F (controlledBirthStep hpsi F z e) = 0 := by
  classical
  unfold controlledBirthStep birthStep
  split
  · rfl
  · change (if SharedReady F (attemptStepConf hpsi F z.val
      (controlledPort F z.val.conf e)) then 1 else 0) = 0
    have hn : ¬ SharedReady F (attemptStepConf hpsi F z.val
        (controlledPort F z.val.conf e)) := by
      intro h
      change (attemptStepConf hpsi F z.val (controlledPort F z.val.conf e)
        (deletePort F)).signal_B = (1 : Fin 2) at h
      rw [hs] at h
      cases h
    rw [if_neg hn]

private theorem ready_child_sum (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (hr : SharedReady F z.val.conf) :
    (List.ofFn (fun e => readyWork hpsi F (controlledBirthStep hpsi F z e))).sum + 2 ≤ n := by
  classical
  let f := fun e => readyWork hpsi F (controlledBirthStep hpsi F z e)
  have ha : f (preparePort F) = 0 := by
    apply child_readyWork_zero hpsi F z
    rw [controlledPort_prepare]
    exact prepare_ready_signal_zero hpsi F z hr
  have hb : f (deletePort F) = 0 := by
    apply child_readyWork_zero hpsi F z
    rw [controlledPort_delete_ready F z.val.conf hr]
    exact prepare_ready_signal_zero hpsi F z hr
  have hrow : ∀ e : Fin n,
      f e + (if e = preparePort F then 1 else 0) +
        (if e = deletePort F then 1 else 0) ≤ 1 := by
    intro e
    by_cases he : e = preparePort F
    · subst e
      simp [ha, preparePort_ne_deletePort]
    · by_cases hd : e = deletePort F
      · subst e
        simp [hb, (preparePort_ne_deletePort F).symm]
      · simpa [f, he, hd] using readyWork_le_one hpsi F (controlledBirthStep hpsi F z e)
  have hsum := ofFn_sum_le _ _ hrow
  rw [ofFn_sum_add, ofFn_sum_add, sum_spike, sum_spike,
    FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_one] at hsum
  simpa only [Nat.add_assoc] using hsum

private theorem signal_zero_of_not_ready (F : TwoGapFrame n)
    (C : Fin n → AgentState psi) (hr : ¬ SharedReady F C) :
    (C (deletePort F)).signal_B = (0 : Fin 2) := by
  apply Fin.ext
  have hb := (C (deletePort F)).signal_B.isLt
  have hn : (C (deletePort F)).signal_B.val ≠ 1 := by
    intro he
    exact hr (Fin.ext he)
  omega

private theorem not_ready_child_sum (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (hr : ¬ SharedReady F z.val.conf) :
    (List.ofFn (fun e => readyWork hpsi F (controlledBirthStep hpsi F z e))).sum ≤ 1 := by
  classical
  have hrow : ∀ e : Fin n,
      readyWork hpsi F (controlledBirthStep hpsi F z e) ≤
        if e = preparePort F then 1 else 0 := by
    intro e
    by_cases ha : e = preparePort F
    · rw [if_pos ha]
      exact readyWork_le_one hpsi F _
    · rw [if_neg ha]
      have hz : (attemptStepConf hpsi F z.val (controlledPort F z.val.conf e)
          (deletePort F)).signal_B = (0 : Fin 2) := by
        rw [controlledPort_of_not_ready F z.val.conf hr]
        by_cases hb : e = deletePort F
        · subst e
          rw [attemptStepConf_eq_sinkStepC, sinkStepC, updatePair_initiator]
          exact (kernelC_left_quiet_fields hpsi _ _
            (signal_zero_of_not_ready F z.val.conf hr)).2
        · rw [attemptStepConf_eq_sinkStepC, shared_frame hpsi F z.val.conf e ha hb]
          exact signal_zero_of_not_ready F z.val.conf hr
      rw [child_readyWork_zero hpsi F z e hz]
      exact Nat.le_refl _
  have hsum := ofFn_sum_le _ _ hrow
  rwa [sum_spike] at hsum

/-- The physically derived correction has coefficients three and two.
When ready, both raw symbols A and B spend the ready credit; when not ready,
only A can replenish it.  Suppressing B costs at most two attack services. -/
theorem controlled_birth_bellman (hpsi : psi > 0) (F : TwoGapFrame n) :
    NatBellmanSuperSolution (controlledBirthStep hpsi F) 1 (correctedPotential hpsi F) := by
  classical
  refine ⟨rfl, rfl, ?_⟩
  intro z
  have hwork : 1 + (List.ofFn (fun e => correctedWork hpsi F
      (controlledBirthStep hpsi F z e))).sum ≤ n * correctedWork hpsi F (.active z) := by
    simp only [correctedWork, ofFn_sum_add, ofFn_sum_mul_left]
    by_cases hr : SharedReady F z.val.conf
    · have hb := controlled_base_ready_sum hpsi F z hr
      have hs := ready_child_sum hpsi F z hr
      change 1 + _ ≤ n * (3 * birthWork hpsi F (.active z) + 2 *
        (if SharedReady F z.val.conf then 1 else 0))
      rw [if_pos hr, Nat.mul_one, Nat.mul_add]
      rw [Nat.mul_left_comm n 3]
      omega
    · have hb := controlled_base_not_ready_sum hpsi F z hr
      have hs := not_ready_child_sum hpsi F z hr
      change 1 + _ ≤ n * (3 * birthWork hpsi F (.active z) + 2 *
        (if SharedReady F z.val.conf then 1 else 0))
      rw [if_neg hr, Nat.mul_zero, Nat.add_zero]
      rw [Nat.mul_left_comm n 3]
      omega
  change 1 * n + (List.ofFn (fun e : Fin n =>
    n * correctedWork hpsi F (controlledBirthStep hpsi F z e))).sum ≤
      n * (n * correctedWork hpsi F (.active z))
  rw [Nat.one_mul, ofFn_sum_mul_left]
  have hs := Nat.mul_le_mul_left n hwork
  simpa only [Nat.mul_add, Nat.mul_one] using hs

theorem controlled_birth_truncated_cost (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (T : Nat) :
    truncatedActiveCostNumerator (controlledBirthStep hpsi F) (.active z) T ≤
      n ^ T * (n * (12 * F.attack.d + 5)) := by
  have hc := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (controlledBirthStep hpsi F) 1 (correctedPotential hpsi F)
    (controlled_birth_bellman hpsi F) (.active z) T
  have hg := gapWC_le_two_d hpsi F.attack z.val.conf z.property.attack
  have hs := readyWork_le_one hpsi F (.active z)
  have hp : correctedPotential hpsi F (.active z) ≤ n * (12 * F.attack.d + 5) := by
    apply Nat.mul_le_mul_left
    change 3 * (2 * F.attack.d + 1 + gapWC F.attack z.val.conf) +
      2 * readyWork hpsi F (.active z) ≤ _
    omega
  exact Nat.le_trans (by simpa only [Nat.one_mul] using hc)
    (Nat.mul_le_mul_left (n ^ T) hp)

private theorem controlled_birth_no_failure (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (e : Fin n) : controlledBirthStep hpsi F z e ≠ .failure := by
  classical
  unfold controlledBirthStep birthStep
  split <;> intro he <;> cases he

theorem controlled_birth_half (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) :
    n ^ (2 * n * (12 * F.attack.d + 5)) ≤
      2 * successCount (controlledBirthStep hpsi F) (.active z)
        (2 * n * (12 * F.attack.d + 5)) := by
  let T := 2 * n * (12 * F.attack.d + 5)
  have hp : 0 < T :=
    Nat.mul_pos (Nat.mul_pos (by decide) F.attack.ring.hn) (by omega)
  have hc := controlled_birth_truncated_cost hpsi F z T
  have hactive := two_mul_activeCount_le_pow_of_scaled_cost
    (controlledBirthStep hpsi F) (.active z) hp (by decide : 0 < 1)
    (num := n * (12 * F.attack.d + 5))
    (by simpa only [Nat.one_mul, Nat.mul_comm] using hc)
    (by dsimp only [T]; simp only [Nat.mul_one, Nat.mul_assoc, Nat.le_refl])
  have hf := BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure
    (controlledBirthStep hpsi F) (controlled_birth_no_failure hpsi F) z T
  have hparts := node_count_partition (controlledBirthStep hpsi F) (.active z) T
  change n ^ T ≤ 2 * successCount (controlledBirthStep hpsi F) (.active z) T
  omega

/-- Every certified birth event supplies the actual fresh-shot certificate;
the proof-only phase can be retagged without altering any physical field. -/
theorem birthEvent_produces_fresh (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (e : Fin n) (he : BirthEvent hpsi F z.val e) :
    FreshOrDeleted hpsi F (attemptStepConf hpsi F z.val e) := by
  rcases he with hs | ⟨hc, rfl⟩
  · exact .inr hs
  · exact .inl (clean_outgoing_attemptEntrance hpsi F z.val z.property hc)

noncomputable def rawBirthStep (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (e : Fin n) : StopNode (AState n psi) := by
  classical
  exact if BirthEvent hpsi F b e then .success else .active (postState hpsi F b e)

noncomputable def controlledRawBirthStep (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (e : Fin n) : StopNode (AState n psi) :=
  rawBirthStep hpsi F b (controlledPort F b.conf e)

def eraseBirth (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (BirthState hpsi F) → StopNode (AState n psi)
  | .active z => .active z.val
  | .success => .success
  | .failure => .failure

/-- The closed gap proof changes neither the physical state nor the
comparison scheduler's effective edge or its stopping event. -/
theorem controlledBirthStep_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (BirthState hpsi F)) (e : Fin n) :
    eraseBirth hpsi F (stepNode (controlledBirthStep hpsi F) x e) =
      stepNode (controlledRawBirthStep hpsi F) (eraseBirth hpsi F x) e := by
  classical
  cases x with
  | success => rfl
  | failure => rfl
  | active z =>
      by_cases hs : BirthEvent hpsi F z.val (controlledPort F z.val.conf e) <;>
        simp [stepNode, controlledBirthStep, birthStep, controlledRawBirthStep,
          rawBirthStep, hs, eraseBirth]

private theorem treeWeight_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (w : StopNode (AState n psi) → Nat)
    (x : StopNode (BirthState hpsi F)) (T : Nat) :
    treeWeight (controlledBirthStep hpsi F) (fun y => w (eraseBirth hpsi F y)) x T =
      treeWeight (controlledRawBirthStep hpsi F) w (eraseBirth hpsi F x) T := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      simp only [treeWeight]
      apply ofFn_sum_eq
      intro e
      rw [ih, controlledBirthStep_erases]

/-- The quantitative statement on the raw physical configurations.  The
only initial premise is the already established gap pair invariant. -/
theorem controlled_raw_birth_half (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b) :
    n ^ (2 * n * (12 * F.attack.d + 5)) ≤
      2 * successCount (controlledRawBirthStep hpsi F) (.active b)
        (2 * n * (12 * F.attack.d + 5)) := by
  let z : BirthState hpsi F := ⟨b, hg⟩
  have hm := controlled_birth_half hpsi F z
  have hw : (fun y => successWeight (eraseBirth hpsi F y)) = successWeight := by
    funext y
    cases y <;> rfl
  have he := treeWeight_erases hpsi F successWeight (.active z)
    (2 * n * (12 * F.attack.d + 5))
  rw [hw] at he
  change successCount (controlledBirthStep hpsi F) (.active z) _ =
    successCount (controlledRawBirthStep hpsi F) (.active b) _ at he
  rw [he] at hm
  exact hm

theorem controlledBirth_success_produces_fresh (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (e : Fin n)
    (hs : controlledBirthStep hpsi F z e = .success) :
    FreshOrDeleted hpsi F (attemptStepConf hpsi F z.val (controlledPort F z.val.conf e)) := by
  classical
  apply birthEvent_produces_fresh hpsi F z
  by_cases he : BirthEvent hpsi F z.val (controlledPort F z.val.conf e)
  · exact he
  · simp only [controlledBirthStep, birthStep, dif_neg he] at hs
    cases hs

end LDSinkTwoGapRaceEntranceControlledBirth

#print axioms LDSinkTwoGapRaceEntranceControlledBirth.controlled_birth_bellman
#print axioms LDSinkTwoGapRaceEntranceControlledBirth.controlled_birth_truncated_cost
#print axioms LDSinkTwoGapRaceEntranceControlledBirth.controlled_birth_half
#print axioms LDSinkTwoGapRaceEntranceControlledBirth.birthEvent_produces_fresh
#print axioms LDSinkTwoGapRaceEntranceControlledBirth.controlledBirthStep_erases
#print axioms LDSinkTwoGapRaceEntranceControlledBirth.controlled_raw_birth_half
#print axioms LDSinkTwoGapRaceEntranceControlledBirth.controlledBirth_success_produces_fresh
