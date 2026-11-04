import Leader.Wu.RaceEntrance.ControlledShot
import Leader.Wu.RaceEntrance.UnshieldService
import Leader.Wu.RaceEntrance.CollapseBudget
import Leader.Core.ControlledSuccessCoverage

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair LDSinkGapCleanup LDSinkProtectedAbsorption LDTwoGapFrame
open LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptResidual LDSinkTwoGapAttemptCells
open LDSinkTwoGapDeletion LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant
open LDSinkTwoGapArrivalRaceMass LDSinkTwoGapRaceEntranceTransit
open LDSinkTwoGapRaceEntranceControlledTail LDSinkTwoGapRaceEntranceControlledRank
open LDSinkTwoGapRaceEntranceControlledShot LDSinkTwoGapRaceEntranceUnshieldService
open LDSinkTwoGapRaceEntranceCollapseBudget LDSinkTwoGapRaceEntranceAuditCoverage

namespace LDSinkTwoGapRaceEntranceLocalizedFinish

variable {n psi : Nat}

/-! A localized live shot may initially face a shielded but Ready target.
The first controlled incoming FIRE physically removes that shield and enters
the existing shot service.  Before that FIRE, the target remains Ready and
the live shot cannot be absorbed.  Work is `position+3` in this first mode
and the already proved shot work afterwards. -/

structure ReadyShot (hpsi : psi > 0) (F : TwoGapFrame n) where
  raw : AActive hpsi F
  position : Nat
  lower : 0 < position
  upper : position ≤ F.attack.d
  live : (raw.val.conf (F.attack.pos position)).bullet = (2 : Fin 3)
  ready : SharedReady F raw.val.conf

def retainedPosition (F : TwoGapFrame n) (t : Nat) (e : Fin n) : Nat :=
  if t = 1 then 1 else nextShotPosition F t e

private theorem retained_bounds (F : TwoGapFrame n) (t : Nat) (ht : 0 < t) (e : Fin n) :
    0 < retainedPosition F t e ∧ retainedPosition F t e ≤ t := by
  unfold retainedPosition nextShotPosition
  split
  · omega
  · split <;> omega

theorem retained_live_row (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : AActive hpsi F) (t : Nat) (ht : 0 < t) (hb : t ≤ F.attack.d)
    (hl : (x.val.conf (F.attack.pos t)).bullet = (2 : Fin 3)) (e : Fin n)
    (hs : ¬ NoResetSuccess F (attemptStepConf hpsi F x.val e))
    (ha : ¬ NoResetAbsorbedAt F x.val e (attemptStepConf hpsi F x.val e)) :
    (attemptStepConf hpsi F x.val e (F.attack.pos (retainedPosition F t e))).bullet = (2 : Fin 3) := by
  by_cases ht1 : t = 1
  · subst t
    simp only [retainedPosition]
    change (postConf hpsi F x.val e (F.attack.pos 1)).bullet = (2 : Fin 3)
    by_cases hh : Touched F.attack e (F.attack.pos 1)
    · obtain ⟨u, hu, hu1, hlive⟩ := liveTouched_K2 hpsi F x e 1 ht hb hl hh hs ha
      have he : u = 1 := by omega
      simpa only [he] using hlive
    · rw [postConf_cell_eq_attack hpsi F x.val e (F.attack.pos 1) hh]
      exact hl
  · rw [retainedPosition, if_neg ht1]
    exact transit_position_row hpsi F x t (by omega) hb hl e

private theorem ready_effective_ne_delete (F : TwoGapFrame n) (C : Fin n → AgentState psi)
    (hr : SharedReady F C) (e : Fin n) : controlledPort F C e ≠ deletePort F := by
  classical
  unfold controlledPort
  split
  · exact preparePort_ne_deletePort F
  · rename_i h
    intro he
    exact h ⟨hr, he⟩

private theorem ready_post_invariant (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : ReadyShot hpsi F) (e : Fin n)
    (hs : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw.val (controlledPort F z.raw.val.conf e))) :
    AInvariant hpsi F (postState hpsi F z.raw.val (controlledPort F z.raw.val.conf e)) := by
  have ha : ¬ NoResetAbsorbedAt F z.raw.val (controlledPort F z.raw.val.conf e)
      (attemptStepConf hpsi F z.raw.val (controlledPort F z.raw.val.conf e)) := by
    intro h
    exact ready_effective_ne_delete F z.raw.val.conf z.ready e h.2.1
  apply (attemptLaws_K2 hpsi F).continuation z.raw (controlledPort F z.raw.val.conf e) _
  simp only [attemptStepRaw, if_neg hs, if_neg ha]
  rfl

noncomputable def asShot (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : AActive hpsi F) (t : Nat) (ht : 0 < t) (hb : t ≤ F.attack.d)
    (hl : (x.val.conf (F.attack.pos t)).bullet = (2 : Fin 3))
    (hs : (x.val.conf (deletePort F)).shield = false) : ShotState hpsi F := by
  classical
  exact if h : t = 1 then .inr ⟨x, hs, by subst t; exact hl⟩
    else .inl ⟨x, t, by omega, hb, hl, hs⟩

private theorem asShot_work_le (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : AActive hpsi F) (t : Nat) (ht : 0 < t) (hb : t ≤ F.attack.d)
    (hl : (x.val.conf (F.attack.pos t)).bullet = (2 : Fin 3))
    (hs : (x.val.conf (deletePort F)).shield = false) :
    shotWork hpsi F (.active (asShot hpsi F x t ht hb hl hs)) ≤ t + 2 := by
  classical
  unfold asShot
  split
  · rename_i h
    simp only [shotWork, tailWork, h]
    split <;> decide
  · exact Nat.le_refl _

abbrev FinishState (hpsi : psi > 0) (F : TwoGapFrame n) :=
  Sum (ReadyShot hpsi F) (ShotState hpsi F)

noncomputable def readyNext (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : ReadyShot hpsi F) (e : Fin n)
    (hn : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw.val (controlledPort F z.raw.val.conf e))) :
    FinishState hpsi F := by
  classical
  let f := controlledPort F z.raw.val.conf e
  let y : AActive hpsi F := ⟨postState hpsi F z.raw.val f, ready_post_invariant hpsi F z e hn⟩
  let u := retainedPosition F z.position f
  have hu := retained_bounds F z.position z.lower f
  have hub := Nat.le_trans hu.2 z.upper
  have ha : ¬ NoResetAbsorbedAt F z.raw.val f (attemptStepConf hpsi F z.raw.val f) := by
    intro h
    exact ready_effective_ne_delete F z.raw.val.conf z.ready e h.2.1
  have hl : (y.val.conf (F.attack.pos u)).bullet = (2 : Fin 3) :=
    retained_live_row hpsi F z.raw z.position z.lower z.upper z.live f hn ha
  by_cases hc : e = preparePort F ∨ e = deletePort F
  · have he : f = preparePort F := by
      rcases hc with rfl | rfl
      · exact controlledPort_prepare F z.raw.val.conf
      · exact controlledPort_delete_ready F z.raw.val.conf z.ready
    have hs : (y.val.conf (deletePort F)).shield = false := by
      change (attemptStepConf hpsi F z.raw.val f (deletePort F)).shield = false
      rw [he]
      exact prepare_unshields hpsi F z.raw.val ⟨z.raw.property.recovery, z.raw.property.attack⟩ z.ready
    exact .inr (asShot hpsi F y u hu.1 hub hl hs)
  · have hpa : e ≠ preparePort F := fun h => hc (.inl h)
    have hpb : e ≠ deletePort F := fun h => hc (.inr h)
    have hr : SharedReady F y.val.conf := by
      change SharedReady F (attemptStepConf hpsi F z.raw.val f)
      dsimp only [f]
      rw [controlledPort_of_ne_delete F z.raw.val.conf e hpb]
      unfold SharedReady
      rw [attemptStepConf_eq_sinkStepC, shared_frame hpsi F z.raw.val.conf e hpa hpb]
      exact z.ready
    exact .inl ⟨y, u, hu.1, hub, hl, hr⟩

noncomputable def finishStep (hpsi : psi > 0) (F : TwoGapFrame n) :
    FinishState hpsi F → Fin n → StopNode (FinishState hpsi F) := by
  classical
  exact fun x e => match x with
    | .inl z => if h : NoResetSuccess F (attemptStepConf hpsi F z.raw.val
        (controlledPort F z.raw.val.conf e)) then .success else .active (readyNext hpsi F z e h)
    | .inr z => inRace (shotStep hpsi F z e)

noncomputable def finishWork (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (FinishState hpsi F) → Nat
  | .active (.inl z) => z.position + 3
  | .active (.inr z) => shotWork hpsi F (.active z)
  | .success => 0
  | .failure => 0

noncomputable def finishPotential (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (FinishState hpsi F)) : Nat := n * finishWork hpsi F x

private theorem finishWork_inRace (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (ShotState hpsi F)) :
    finishWork hpsi F (inRace x) = shotWork hpsi F x := by cases x <;> rfl

private theorem readyNext_work_le (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : ReadyShot hpsi F) (e : Fin n)
    (hn : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw.val (controlledPort F z.raw.val.conf e))) :
    finishWork hpsi F (.active (readyNext hpsi F z e hn)) ≤
      z.position + (if e = preparePort F ∨ e = deletePort F then 2 else 3) := by
  classical
  have hp := retained_bounds F z.position z.lower (controlledPort F z.raw.val.conf e)
  by_cases hc : e = preparePort F ∨ e = deletePort F
  · simp only [readyNext, hc, dite_true, finishWork]
    exact Nat.le_trans (asShot_work_le hpsi F _ _ _ _ _ _)
      (Nat.add_le_add_right hp.2 2)
  · simp only [readyNext, hc, dite_false, finishWork]
    exact Nat.add_le_add_right hp.2 3

private theorem ready_child_work_le (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : ReadyShot hpsi F) (e : Fin n) :
    finishWork hpsi F (finishStep hpsi F (.inl z) e) ≤ z.position + 3 := by
  classical
  simp only [finishStep]
  split
  · exact Nat.zero_le _
  · rename_i hn
    have h := readyNext_work_le hpsi F z e hn
    split at h <;> omega

private theorem ready_prepare_work_drop (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : ReadyShot hpsi F) :
    finishWork hpsi F (finishStep hpsi F (.inl z) (preparePort F)) + 1 ≤ z.position + 3 := by
  classical
  simp only [finishStep]
  split
  · change 0 + 1 ≤ _
    omega
  · rename_i hn
    have h := readyNext_work_le hpsi F z (preparePort F) hn
    rw [if_pos (.inl rfl)] at h
    omega

theorem finish_bellman (hpsi : psi > 0) (F : TwoGapFrame n) :
    NatBellmanSuperSolution (finishStep hpsi F) 1 (finishPotential hpsi F) := by
  refine ⟨rfl, rfl, ?_⟩
  intro x
  cases x with
  | inl z =>
      have hr := LDSinkGapCleanup.ofFn_sum_lt n
        (fun e => finishWork hpsi F (finishStep hpsi F (.inl z) e))
        (z.position + 3) (preparePort F)
        (ready_child_work_le hpsi F z) (ready_prepare_work_drop hpsi F z)
      change 1 * n + (List.ofFn (fun e => n * finishWork hpsi F (finishStep hpsi F (.inl z) e))).sum ≤
        n * (n * (z.position + 3))
      rw [Nat.one_mul, ofFn_sum_mul_left]
      have h := Nat.mul_le_mul_left n hr
      rw [Nat.mul_add, Nat.mul_one] at h
      omega
  | inr z =>
      have h := (shot_bellman hpsi F).2.2 z
      change 1 * n + (List.ofFn (fun e => n * finishWork hpsi F (inRace (shotStep hpsi F z e)))).sum ≤
        n * (n * shotWork hpsi F (.active z))
      simpa only [finishWork_inRace, shotPotential] using h

def eraseFinish (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (FinishState hpsi F) → StopNode (AState n psi)
  | .active (.inl z) => .active z.raw.val
  | .active (.inr z) => eraseShot hpsi F (.active z)
  | .success => .success
  | .failure => .failure

private theorem eraseFinish_inRace (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (ShotState hpsi F)) :
    eraseFinish hpsi F (inRace x) = eraseShot hpsi F x := by cases x <;> rfl

private theorem asShot_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : AActive hpsi F) (t : Nat) (ht : 0 < t) (hb : t ≤ F.attack.d)
    (hl : (x.val.conf (F.attack.pos t)).bullet = (2 : Fin 3))
    (hs : (x.val.conf (deletePort F)).shield = false) :
    eraseShot hpsi F (.active (asShot hpsi F x t ht hb hl hs)) = .active x.val := by
  classical
  unfold asShot
  split <;> rfl

private theorem readyNext_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : ReadyShot hpsi F) (e : Fin n)
    (hn : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw.val (controlledPort F z.raw.val.conf e))) :
    eraseFinish hpsi F (.active (readyNext hpsi F z e hn)) =
      .active (postState hpsi F z.raw.val (controlledPort F z.raw.val.conf e)) := by
  classical
  by_cases hc : e = preparePort F ∨ e = deletePort F
  · simp only [readyNext, hc, dite_true, eraseFinish]
    exact asShot_erases hpsi F _ _ _ _ _ _
  · simp only [readyNext, hc, dite_false, eraseFinish]

theorem finishStep_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (FinishState hpsi F)) (e : Fin n) :
    eraseFinish hpsi F (stepNode (finishStep hpsi F) x e) =
      stepNode (controlledPhysicalStep hpsi F) (eraseFinish hpsi F x) e := by
  classical
  cases x with
  | success => rfl
  | failure => rfl
  | active x =>
      cases x with
      | inl z =>
          change eraseFinish hpsi F (finishStep hpsi F (.inl z) e) =
            physicalBlockStep hpsi F z.raw.val (controlledPort F z.raw.val.conf e)
          rw [physicalBlockStep_normal_form]
          by_cases hs : NoResetSuccess F (attemptStepConf hpsi F z.raw.val (controlledPort F z.raw.val.conf e))
          · simp only [finishStep, dif_pos hs, if_pos hs, eraseFinish]
          · simp only [finishStep, dif_neg hs, if_neg hs]
            exact readyNext_erases hpsi F z e hs
      | inr z =>
          change eraseFinish hpsi F (inRace (shotStep hpsi F z e)) = _
          rw [eraseFinish_inRace]
          exact shotStep_erases hpsi F (.active z) e

private theorem finish_no_failure (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : FinishState hpsi F) (e : Fin n) : finishStep hpsi F z e ≠ .failure := by
  intro he
  have h := finishStep_erases hpsi F (.active z) e
  change eraseFinish hpsi F (finishStep hpsi F z e) = _ at h
  rw [he] at h
  cases z with
  | inl z =>
      change .failure = controlledPhysicalStep hpsi F z.raw.val e at h
      unfold controlledPhysicalStep at h
      rw [physicalBlockStep_normal_form] at h
      split at h <;> cases h
  | inr z =>
      cases z with
      | inl z =>
          change .failure = controlledPhysicalStep hpsi F z.raw.val e at h
          unfold controlledPhysicalStep at h
          rw [physicalBlockStep_normal_form] at h
          split at h <;> cases h
      | inr z =>
          change .failure = controlledPhysicalStep hpsi F z.raw.val e at h
          unfold controlledPhysicalStep at h
          rw [physicalBlockStep_normal_form] at h
          split at h <;> cases h

theorem finish_half (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : ReadyShot hpsi F) (L : Nat) (hL : z.position ≤ L) :
    n ^ (2 * n * (L + 3)) ≤
      2 * successCount (finishStep hpsi F) (.active (.inl z)) (2 * n * (L + 3)) := by
  let T := 2 * n * (L + 3)
  have hT : 0 < T := Nat.mul_pos (Nat.mul_pos (by decide) F.attack.ring.hn) (by omega)
  have hc := truncatedActiveCostNumerator_mul_le_of_natSuperSolution (finishStep hpsi F)
    1 (finishPotential hpsi F) (finish_bellman hpsi F) (.active (.inl z)) T
  have hp : finishPotential hpsi F (.active (.inl z)) ≤ n * (L + 3) :=
    Nat.mul_le_mul_left n (Nat.add_le_add_right hL 3)
  have hcost := Nat.le_trans (by simpa only [Nat.one_mul] using hc) (Nat.mul_le_mul_left (n ^ T) hp)
  have ha := two_mul_activeCount_le_pow_of_scaled_cost (finishStep hpsi F) (.active (.inl z))
    hT (by decide : 0 < 1) (num := n * (L + 3))
    (by simpa only [Nat.mul_one, Nat.one_mul, Nat.mul_comm] using hcost)
    (by dsimp only [T]; simp only [Nat.mul_one, Nat.mul_assoc, Nat.le_refl])
  have hf := BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure (finishStep hpsi F)
    (finish_no_failure hpsi F) (.inl z) T
  have hparts := node_count_partition (finishStep hpsi F) (.active (.inl z)) T
  change n ^ T ≤ 2 * successCount (finishStep hpsi F) (.active (.inl z)) T
  omega

private theorem finish_tree_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (w : StopNode (AState n psi) → Nat) (x : StopNode (FinishState hpsi F)) (T : Nat) :
    treeWeight (finishStep hpsi F) (fun y => w (eraseFinish hpsi F y)) x T =
      treeWeight (controlledPhysicalStep hpsi F) w (eraseFinish hpsi F x) T := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      simp only [treeWeight]
      apply ofFn_sum_eq
      intro e
      rw [ih, finishStep_erases]

theorem ready_controlled_half (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : ReadyShot hpsi F) (L : Nat) (hL : z.position ≤ L) :
    n ^ (2 * n * (L + 3)) ≤
      2 * successCount (controlledPhysicalStep hpsi F) (.active z.raw.val) (2 * n * (L + 3)) := by
  have hm := finish_half hpsi F z L hL
  have hw : (fun y => successWeight (eraseFinish hpsi F y)) = successWeight := by
    funext y
    cases y with
    | success => rfl
    | failure => rfl
    | active y => cases y with
      | inl y => rfl
      | inr y => cases y <;> rfl
  have he := finish_tree_erases hpsi F successWeight (.active (.inl z)) (2 * n * (L + 3))
  rw [hw] at he
  change successCount (finishStep hpsi F) (.active (.inl z)) _ =
    successCount (controlledPhysicalStep hpsi F) (.active z.raw.val) _ at he
  rwa [he] at hm

private theorem finish_audit_failure_quarter (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : ReadyShot hpsi F) :
    4 * failureCount (ControlledSchedulerMass.auditStep (physicalBlockStep hpsi F)
      (physicalRedirection F)) (.active (z.raw.val, 291)) (2 * n * (16 * F.recovery.d + 4)) ≤
      n ^ (2 * n * (16 * F.recovery.d + 4)) := by
  let T := 2 * n * (16 * F.recovery.d + 4)
  let R := serviceLength F
  let f := failureCount (ControlledSchedulerMass.auditStep (physicalBlockStep hpsi F)
    (physicalRedirection F)) (.active (z.raw.val, 291)) T
  have hR : 0 < R := by have h := F.recovery.hd; dsimp only [R, serviceLength]; omega
  have hn : 0 < n := F.recovery.ring.hn
  have ht : 2 * (16 * F.recovery.d + 4) ≤ 72 * R := by
    have h := F.recovery.hd
    dsimp only [R, serviceLength]
    omega
  have ht' : T ≤ 72 * (n * R) := by
    have h := Nat.mul_le_mul_left n ht
    simpa only [T, Nat.mul_assoc, Nat.mul_left_comm] using h
  have hu : n * R + T ≤ (n * R) * 73 := by rw [Nat.mul_comm (n * R) 73]; omega
  have hb := physical_audit_failure_bound hpsi F 291 z.raw.val
    ⟨z.raw.property.recovery, z.raw.property.attack⟩ T
  change n * (R * 292) * f ≤ n ^ T * (n * R + T) at hb
  have hscaled : ((n * R) * 73) * (4 * f) ≤ ((n * R) * 73) * n ^ T := by
    calc
      ((n * R) * 73) * (4 * f) = n * (R * 292) * f := by
        simp only [Nat.mul_assoc]
        rw [← Nat.mul_assoc 73 4 f]
      _ ≤ n ^ T * (n * R + T) := hb
      _ ≤ n ^ T * ((n * R) * 73) := Nat.mul_le_mul_left _ hu
      _ = ((n * R) * 73) * n ^ T := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_left hscaled (Nat.mul_pos (Nat.mul_pos hn hR) (by decide))

theorem localized_bounded_quarter (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : ReadyShot hpsi F) (hz : z.position ≤ 16 * F.recovery.d + 1) :
    n ^ (2 * n * (16 * F.recovery.d + 4)) ≤
      4 * ControlledSchedulerMass.boundedSuccessCount (physicalBlockStep hpsi F)
        (physicalRedirection F) (.active z.raw.val) (2 * n * (16 * F.recovery.d + 4)) 291 := by
  have hc := ready_controlled_half hpsi F z (16 * F.recovery.d + 1) hz
  have hf := finish_audit_failure_quarter hpsi F z
  have heq : ControlledSchedulerMass.controlledStep (physicalBlockStep hpsi F) (physicalRedirection F) =
      controlledPhysicalStep hpsi F := by
    funext b e
    simp only [ControlledSchedulerMass.controlledStep, physical_effective_eq, controlledPhysicalStep]
  have hcover := controlled_success_covered (physicalBlockStep hpsi F) (physicalRedirection F)
    (.active z.raw.val) (2 * n * (16 * F.recovery.d + 4)) 291
  rw [heq] at hcover
  change n ^ (2 * n * (16 * F.recovery.d + 4)) ≤
    2 * successCount (controlledPhysicalStep hpsi F) (.active z.raw.val)
      (2 * n * (16 * F.recovery.d + 4)) at hc
  change _ ≤ 4 * successCount (ControlledSchedulerMass.auditStep (physicalBlockStep hpsi F)
    (physicalRedirection F)) (.active (z.raw.val, 291)) _
  simp only [ControlledSchedulerMass.withBudget] at hcover
  omega

def finishCollapseBudget : Nat := 291

/-- Localized controlled service transferred to the original uniform K2
tree, charging both preimages of every collapsed incoming FIRE. -/
theorem localized_ready_uniform_mass (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : ReadyShot hpsi F) (hz : z.position ≤ 16 * F.recovery.d + 1) :
    n ^ (2 * n * (16 * F.recovery.d + 4)) ≤
      (4 * 2 ^ finishCollapseBudget) * successCount (physicalBlockStep hpsi F) (.active z.raw.val)
        (2 * n * (16 * F.recovery.d + 4)) := by
  exact ControlledSchedulerMass.raw_success_mass_lower (physicalBlockStep hpsi F)
    (physicalRedirection F) (.active z.raw.val) (2 * n * (16 * F.recovery.d + 4)) finishCollapseBudget 4
    (localized_bounded_quarter hpsi F z hz)

/-- The directly usable physical handoff interface from recovery readiness;
the shared shield may have either value and the live shot may already be parked. -/
theorem localized_cleanReady_uniform_mass (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : AActive hpsi F) (t : Nat) (ht : 0 < t) (hb : t ≤ F.attack.d)
    (hl : (x.val.conf (F.attack.pos t)).bullet = (2 : Fin 3))
    (hr : CleanReady F.recovery x.val.conf) (hcap : t ≤ 16 * F.recovery.d + 1) :
    n ^ (2 * n * (16 * F.recovery.d + 4)) ≤
      (4 * 2 ^ finishCollapseBudget) * successCount (physicalBlockStep hpsi F) (.active x.val)
        (2 * n * (16 * F.recovery.d + 4)) := by
  have hs : SharedReady F x.val.conf := by
    have h := hr.1
    rw [F.shared] at h
    exact h
  exact localized_ready_uniform_mass hpsi F ⟨x, t, ht, hb, hl, hs⟩ hcap

end LDSinkTwoGapRaceEntranceLocalizedFinish

#print axioms LDSinkTwoGapRaceEntranceLocalizedFinish.retained_live_row
#print axioms LDSinkTwoGapRaceEntranceLocalizedFinish.finish_bellman
#print axioms LDSinkTwoGapRaceEntranceLocalizedFinish.finishStep_erases
#print axioms LDSinkTwoGapRaceEntranceLocalizedFinish.ready_controlled_half
#print axioms LDSinkTwoGapRaceEntranceLocalizedFinish.localized_bounded_quarter
#print axioms LDSinkTwoGapRaceEntranceLocalizedFinish.localized_cleanReady_uniform_mass
