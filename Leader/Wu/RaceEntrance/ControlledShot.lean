import Leader.Wu.RaceEntrance.ControlledTail
import Leader.Wu.RaceEntrance.ControlledRank
import Leader.Wu.RaceEntrance.Transit

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkProtectedAbsorption LDTwoGapFrame
open LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptCells LDSinkTwoGapDeletion
open LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant
open LDSinkTwoGapArrivalRaceMass LDSinkTwoGapRaceEntranceTransit
open LDSinkTwoGapRaceEntranceControlledTail LDSinkTwoGapRaceEntranceControlledRank

namespace LDSinkTwoGapRaceEntranceControlledShot

variable {n psi : Nat}

/-!
A fresh unique shot moves on the actual K2 path under ready-edge
redirection, then pays the real final-hit tail.  Its total comparison
potential is at most `n*(d+2)`.  The target shield stays false under every
comparison edge; no physical reset or independent recovery copy is used.
-/

private theorem signal_zero_of_not_ready (F : TwoGapFrame n)
    (C : Fin n → AgentState psi) (hr : ¬ SharedReady F C) :
    (C (deletePort F)).signal_B = (0 : Fin 2) := by
  apply Fin.ext
  have hb := (C (deletePort F)).signal_B.isLt
  have hn : (C (deletePort F)).signal_B.val ≠ 1 := by
    intro he
    exact hr (Fin.ext he)
  omega

/-- The comparison scheduler preserves a false shared shield on all raw
configurations.  This includes both preimages of the incoming FIRE row. -/
theorem controlled_shield_closed (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hs : (b.conf (deletePort F)).shield = false) (e : Fin n) :
    (attemptStepConf hpsi F b (controlledPort F b.conf e) (deletePort F)).shield = false := by
  classical
  let f := controlledPort F b.conf e
  by_cases ha : f = preparePort F
  · change (attemptStepConf hpsi F b f (deletePort F)).shield = false
    rw [ha, attemptStepConf_eq_sinkStepC, sinkStepC, preparePort_right,
      updatePair_responder _ _ _ _ (preparePort_ne_deletePort F).symm]
    exact kernelC_right_shield_false hpsi _ _ hs
  · by_cases hb : f = deletePort F
    · have hr : ¬ SharedReady F b.conf := by
        intro hr
        have hne : controlledPort F b.conf e ≠ deletePort F := by
          unfold controlledPort
          split
          · exact preparePort_ne_deletePort F
          · rename_i hh
            intro he
            exact hh ⟨hr, he⟩
        exact hne hb
      change (attemptStepConf hpsi F b f (deletePort F)).shield = false
      rw [hb, attemptStepConf_eq_sinkStepC, sinkStepC, updatePair_initiator]
      exact (kernelC_left_quiet_fields hpsi _ _ (signal_zero_of_not_ready F b.conf hr)).1.trans hs
    · change (attemptStepConf hpsi F b f (deletePort F)).shield = false
      rw [attemptStepConf_eq_sinkStepC, shared_frame hpsi F b.conf f ha hb]
      exact hs

private theorem controlled_not_absorbed (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hs : (b.conf (deletePort F)).shield = false) (e : Fin n) :
    ¬ NoResetAbsorbedAt F b (controlledPort F b.conf e)
      (attemptStepConf hpsi F b (controlledPort F b.conf e)) := by
  intro ha
  have hz := controlled_shield_closed hpsi F b hs e
  have ht := ha.2.2.2.2.2.1
  change (attemptStepConf hpsi F b (controlledPort F b.conf e) (deletePort F)).shield = true at ht
  rw [hz] at ht
  cases ht

structure TransitState (hpsi : psi > 0) (F : TwoGapFrame n) where
  raw : AActive hpsi F
  position : Nat
  lower : 1 < position
  upper : position ≤ F.attack.d
  live : (raw.val.conf (F.attack.pos position)).bullet = (2 : Fin 3)
  shield : (raw.val.conf (deletePort F)).shield = false

abbrev ShotState (hpsi : psi > 0) (F : TwoGapFrame n) :=
  Sum (TransitState hpsi F) (TailState hpsi F)

noncomputable def shotNext (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TransitState hpsi F) (e : Fin n)
    (hn : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw.val
      (controlledPort F z.raw.val.conf e))) : ShotState hpsi F := by
  classical
  let f := controlledPort F z.raw.val.conf e
  let y := postState hpsi F z.raw.val f
  have ha := controlled_not_absorbed hpsi F z.raw.val z.shield e
  have hn' : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw.val f) := hn
  have ha' : ¬ NoResetAbsorbedAt F z.raw.val f (attemptStepConf hpsi F z.raw.val f) := ha
  have hraw : attemptStepRaw hpsi F z.raw.val f = .active y := by
    simp only [attemptStepRaw, if_neg hn', if_neg ha']
    rfl
  have hy : AInvariant hpsi F y := (attemptLaws_K2 hpsi F).continuation z.raw f y hraw
  have hr := transit_unique_row hpsi F z.raw z.position z.lower z.upper z.live f
  have hshield := controlled_shield_closed hpsi F z.raw.val z.shield e
  by_cases hp : nextShotPosition F z.position f = 1
  · have hlive := hr.2.2.1
    rw [hp] at hlive
    exact .inr ⟨⟨y, hy⟩, hshield, hlive⟩
  · have hlo : 1 < nextShotPosition F z.position f := by have ht := hr.1; omega
    exact .inl ⟨⟨y, hy⟩, nextShotPosition F z.position f, hlo, hr.2.1, hr.2.2.1, hshield⟩

noncomputable def shotStep (hpsi : psi > 0) (F : TwoGapFrame n) :
    ShotState hpsi F → Fin n → StopNode (ShotState hpsi F) := by
  classical
  exact fun x e => match x with
    | .inl z => if h : NoResetSuccess F (attemptStepConf hpsi F z.raw.val
        (controlledPort F z.raw.val.conf e)) then .success else .active (shotNext hpsi F z e h)
    | .inr z => inRace (tailStep hpsi F z e)

noncomputable def shotWork (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (ShotState hpsi F) → Nat
  | .active (.inl z) => z.position + 2
  | .active (.inr z) => tailWork hpsi F (.active z)
  | .success => 0
  | .failure => 0

noncomputable def shotPotential (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (ShotState hpsi F)) : Nat := n * shotWork hpsi F x

private theorem shotWork_inRace (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (TailState hpsi F)) :
    shotWork hpsi F (inRace x) = tailWork hpsi F x := by
  cases x <;> rfl

private theorem shotNext_work_le (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TransitState hpsi F) (e : Fin n)
    (hn : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw.val
      (controlledPort F z.raw.val.conf e))) :
    shotWork hpsi F (.active (shotNext hpsi F z e hn)) ≤
      nextShotPosition F z.position (controlledPort F z.raw.val.conf e) + 2 := by
  classical
  by_cases hp : nextShotPosition F z.position (controlledPort F z.raw.val.conf e) = 1
  · simp only [shotNext, hp, dite_true, shotWork]
    change (if SharedReady F (attemptStepConf hpsi F z.raw.val
      (controlledPort F z.raw.val.conf e)) then 3 else 2) ≤ 3
    split <;> decide
  · simp only [shotNext, hp, dite_false, shotWork, Nat.le_refl]

private theorem transit_child_work_le (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TransitState hpsi F) (e : Fin n) :
    shotWork hpsi F (shotStep hpsi F (.inl z) e) ≤ z.position + 2 := by
  classical
  simp only [shotStep]
  split
  · exact Nat.zero_le _
  · rename_i hn
    have hs := shotNext_work_le hpsi F z e hn
    have hpos : nextShotPosition F z.position (controlledPort F z.raw.val.conf e) ≤ z.position := by
      unfold nextShotPosition
      split <;> omega
    omega

private theorem transit_good_work_drop (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TransitState hpsi F) :
    shotWork hpsi F (shotStep hpsi F (.inl z) (F.attack.pos (z.position - 1))) + 1 ≤
      z.position + 2 := by
  classical
  have ht := z.lower
  have hu := z.upper
  have hd := F.attack.hdn
  have he : F.attack.pos (z.position - 1) ≠ deletePort F := by
    exact F.attack.pos_ne (by omega) (by omega) (by omega)
  have hport := controlledPort_of_ne_delete F z.raw.val.conf
    (F.attack.pos (z.position - 1)) he
  simp only [shotStep]
  split
  · change 0 + 1 ≤ _
    omega
  · rename_i hn
    have hs := shotNext_work_le hpsi F z (F.attack.pos (z.position - 1)) hn
    rw [hport, nextShotPosition, if_pos rfl] at hs
    omega

/-- The same physical shot pays transit and final preparation/deletion in
one stopped process; no time is erased at the parked handoff. -/
theorem shot_bellman (hpsi : psi > 0) (F : TwoGapFrame n) :
    NatBellmanSuperSolution (shotStep hpsi F) 1 (shotPotential hpsi F) := by
  refine ⟨rfl, rfl, ?_⟩
  intro x
  cases x with
  | inl z =>
      have hs := LDSinkGapCleanup.ofFn_sum_lt n
        (fun e => shotWork hpsi F (shotStep hpsi F (.inl z) e))
        (z.position + 2) (F.attack.pos (z.position - 1))
        (transit_child_work_le hpsi F z) (transit_good_work_drop hpsi F z)
      change 1 * n + (List.ofFn (fun e : Fin n =>
        n * shotWork hpsi F (shotStep hpsi F (.inl z) e))).sum ≤ n * (n * (z.position + 2))
      rw [Nat.one_mul, ofFn_sum_mul_left]
      have hh := Nat.mul_le_mul_left n hs
      rw [Nat.mul_add, Nat.mul_one] at hh
      omega
  | inr z =>
      have ht := (tail_bellman hpsi F).2.2 z
      change 1 * n + (List.ofFn (fun e : Fin n =>
        n * shotWork hpsi F (inRace (tailStep hpsi F z e)))).sum ≤
          n * (n * tailWork hpsi F (.active z))
      simpa only [shotWork_inRace, tailPotential] using ht

theorem shot_truncated_cost (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : ShotState hpsi F) (T : Nat) :
    truncatedActiveCostNumerator (shotStep hpsi F) (.active x) T ≤
      n ^ T * (n * (F.attack.d + 2)) := by
  classical
  have hc := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (shotStep hpsi F) 1 (shotPotential hpsi F) (shot_bellman hpsi F) (.active x) T
  have hp : shotPotential hpsi F (.active x) ≤ n * (F.attack.d + 2) := by
    apply Nat.mul_le_mul_left
    cases x with
    | inl z => exact Nat.add_le_add_right z.upper 2
    | inr z =>
        change (if SharedReady F z.raw.val.conf then 3 else 2) ≤ F.attack.d + 2
        have hd := F.attack.hd
        split <;> omega
  exact Nat.le_trans (by simpa only [Nat.one_mul] using hc)
    (Nat.mul_le_mul_left (n ^ T) hp)

private theorem shot_no_failure (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : ShotState hpsi F) (e : Fin n) : shotStep hpsi F x e ≠ .failure := by
  classical
  cases x with
  | inl z => simp only [shotStep]; split <;> intro he <;> cases he
  | inr z =>
      simp only [shotStep, tailStep]
      split <;> intro he <;> cases he

theorem shot_half (hpsi : psi > 0) (F : TwoGapFrame n) (x : ShotState hpsi F) :
    n ^ (2 * n * (F.attack.d + 2)) ≤
      2 * successCount (shotStep hpsi F) (.active x) (2 * n * (F.attack.d + 2)) := by
  let T := 2 * n * (F.attack.d + 2)
  have hp : 0 < T := Nat.mul_pos (Nat.mul_pos (by decide) F.attack.ring.hn) (by omega)
  have hc := shot_truncated_cost hpsi F x T
  have hactive := two_mul_activeCount_le_pow_of_scaled_cost
    (shotStep hpsi F) (.active x) hp (by decide : 0 < 1)
    (num := n * (F.attack.d + 2)) (by simpa only [Nat.one_mul, Nat.mul_comm] using hc)
    (by dsimp only [T]; simp only [Nat.mul_one, Nat.mul_assoc, Nat.le_refl])
  have hf := BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure
    (shotStep hpsi F) (shot_no_failure hpsi F) x T
  have hparts := node_count_partition (shotStep hpsi F) (.active x) T
  change n ^ T ≤ 2 * successCount (shotStep hpsi F) (.active x) T
  omega

def eraseShot (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (ShotState hpsi F) → StopNode (AState n psi)
  | .active (.inl z) => .active z.raw.val
  | .active (.inr z) => .active z.raw.val
  | .success => .success
  | .failure => .failure

private theorem shotNext_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TransitState hpsi F) (e : Fin n)
    (hn : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw.val
      (controlledPort F z.raw.val.conf e))) :
    eraseShot hpsi F (.active (shotNext hpsi F z e hn)) =
      .active (postState hpsi F z.raw.val (controlledPort F z.raw.val.conf e)) := by
  classical
  by_cases hp : nextShotPosition F z.position (controlledPort F z.raw.val.conf e) = 1 <;>
    simp only [shotNext, hp, dite_true, dite_false, eraseShot]

private theorem eraseShot_inRace (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (TailState hpsi F)) :
    eraseShot hpsi F (inRace x) = eraseTail hpsi F x := by
  cases x <;> rfl

theorem shotStep_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (ShotState hpsi F)) (e : Fin n) :
    eraseShot hpsi F (stepNode (shotStep hpsi F) x e) =
      stepNode (controlledPhysicalStep hpsi F) (eraseShot hpsi F x) e := by
  classical
  cases x with
  | success => rfl
  | failure => rfl
  | active x =>
      cases x with
      | inl z =>
          change eraseShot hpsi F (shotStep hpsi F (.inl z) e) =
            physicalBlockStep hpsi F z.raw.val (controlledPort F z.raw.val.conf e)
          rw [physicalBlockStep_normal_form]
          by_cases hs : NoResetSuccess F (attemptStepConf hpsi F z.raw.val
              (controlledPort F z.raw.val.conf e))
          · simp [shotStep, hs, eraseShot]
          · simp only [shotStep, dif_neg hs, if_neg hs]
            exact shotNext_erases hpsi F z e hs
      | inr z =>
          change eraseShot hpsi F (inRace (tailStep hpsi F z e)) = _
          rw [eraseShot_inRace]
          exact tailStep_erases hpsi F (.active z) e

private theorem treeWeight_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (w : StopNode (AState n psi) → Nat)
    (x : StopNode (ShotState hpsi F)) (T : Nat) :
    treeWeight (shotStep hpsi F) (fun y => w (eraseShot hpsi F y)) x T =
      treeWeight (controlledPhysicalStep hpsi F) w (eraseShot hpsi F x) T := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      simp only [treeWeight]
      apply ofFn_sum_eq
      intro e
      rw [ih, shotStep_erases]

/-- A fresh shot facing an unshielded shared leader reaches actual deletion
with half of comparison words by `2*n*(d+2)`. -/
theorem fresh_controlled_half (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hf : AttemptEntrance hpsi F b)
    (hs : (b.conf (deletePort F)).shield = false) :
    n ^ (2 * n * (F.attack.d + 2)) ≤
      2 * successCount (controlledPhysicalStep hpsi F) (.active b) (2 * n * (F.attack.d + 2)) := by
  let z : TransitState hpsi F :=
    ⟨⟨b, hf.1⟩, F.attack.d, (by have h := F.attack.hd; omega), Nat.le_refl _, hf.2.2, hs⟩
  have hm := shot_half hpsi F (.inl z)
  have hw : (fun y => successWeight (eraseShot hpsi F y)) = successWeight := by
    funext y
    cases y with
    | success => rfl
    | failure => rfl
    | active y => cases y <;> rfl
  have he := treeWeight_erases hpsi F successWeight (.active (.inl z))
    (2 * n * (F.attack.d + 2))
  rw [hw] at he
  change successCount (shotStep hpsi F) (.active (.inl z)) _ =
    successCount (controlledPhysicalStep hpsi F) (.active b) _ at he
  rw [he] at hm
  exact hm

end LDSinkTwoGapRaceEntranceControlledShot

#print axioms LDSinkTwoGapRaceEntranceControlledShot.controlled_shield_closed
#print axioms LDSinkTwoGapRaceEntranceControlledShot.shot_bellman
#print axioms LDSinkTwoGapRaceEntranceControlledShot.shot_truncated_cost
#print axioms LDSinkTwoGapRaceEntranceControlledShot.shotStep_erases
#print axioms LDSinkTwoGapRaceEntranceControlledShot.fresh_controlled_half
