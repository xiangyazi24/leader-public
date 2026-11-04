import Leader.Wu.RaceEntrance.Transit
import Leader.Wu.RaceEntrance.UnshieldService

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkProtectedAbsorption LDSinkGapDoneInvariant LDSinkGapServiceRank LDSinkGapCleanupBound
open LDTwoGapFrame LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptResidual LDSinkTwoGapAttemptCells
open LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant LDSinkTwoGapEntrance
open LDSinkTwoGapRaceEntranceTransit

namespace LDSinkTwoGapRaceEntranceLocalizedRecovery

variable {n psi : Nat}

/-!
Race recovery cleanup against the remaining travel of an actual unique live
shot.  Readiness or physical deletion wins; arrival at attack position one
without readiness loses.  Readiness has priority on a simultaneous row.
Initial readiness is an immediate success, carrying the unchanged input.

The finite charge certificate is recovery rank plus distance already moved.
Its failure value is the full required distance.  C5's unit row slack pays
the one raw attack predecessor that can increase this distance.  This is
uniform finite-tree accounting, with no independence or stopping-time law.
-/

def RecoveryReadyOrDeleted (F : TwoGapFrame n) (C : Fin n → AgentState psi) : Prop :=
  CleanReady F.recovery C ∨ NoResetSuccess F C

structure RaceState (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat) where
  raw : AActive hpsi F
  position : Nat
  lower : 1 < position
  upper : position ≤ F.attack.d
  localized : position ≤ q + 1
  live : (raw.val.conf (F.attack.pos position)).bullet = (2 : Fin 3)
  not_ready : ¬ CleanReady F.recovery raw.val.conf

private theorem race_not_done (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (z : RaceState hpsi F q) : ¬ GapDoneC F.recovery z.raw.val.conf := by
  rintro (hc | hl | hr)
  · exact z.not_ready hc
  · have h := z.raw.property.recovery.1.1
    rw [h] at hl
    cases hl
  · have h := z.raw.property.recovery.1.2
    rw [h] at hr
    cases hr

private theorem race_not_absorbed (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (z : RaceState hpsi F q) (e : Fin n) :
    ¬ NoResetAbsorbedAt F z.raw.val e (attemptStepConf hpsi F z.raw.val e) := by
  intro ha
  have hb := z.raw.property.tag.parked_iff.mp ha.1
  have hp := old_bullet_unique hpsi F z.raw 1 z.position
    (by decide) (by have h := F.attack.hd; omega)
    (by have h := z.lower; omega) z.upper (by rw [hb]; decide)
    (by rw [z.live]; decide)
  have hl := z.lower
  omega

theorem race_post_invariant (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (z : RaceState hpsi F q) (e : Fin n)
    (hn : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw.val e)) :
    AInvariant hpsi F (postState hpsi F z.raw.val e) := by
  have ha := race_not_absorbed hpsi F q z e
  apply (attemptLaws_K2 hpsi F).continuation z.raw e _
  simp only [attemptStepRaw, if_neg hn, if_neg ha]
  rfl

private theorem next_position_le (F : TwoGapFrame n) (t : Nat) (e : Fin n) :
    nextShotPosition F t e ≤ t := by
  unfold nextShotPosition
  split <;> omega

noncomputable def raceNext (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (z : RaceState hpsi F q) (e : Fin n)
    (hn : ¬ RecoveryReadyOrDeleted F (attemptStepConf hpsi F z.raw.val e))
    (hu : nextShotPosition F z.position e ≠ 1) : RaceState hpsi F q := by
  have hi := race_post_invariant hpsi F q z e (fun h => hn (.inr h))
  have hp := transit_unique_row hpsi F z.raw z.position z.lower z.upper z.live e
  exact ⟨⟨postState hpsi F z.raw.val e, hi⟩, nextShotPosition F z.position e,
    by omega, hp.2.1, Nat.le_trans (next_position_le F z.position e) z.localized,
    hp.2.2.1, fun hc => hn (.inl hc)⟩

noncomputable def raceStep (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (z : RaceState hpsi F q) (e : Fin n) : StopNode (RaceState hpsi F q) := by
  classical
  exact if h : RecoveryReadyOrDeleted F (attemptStepConf hpsi F z.raw.val e) then .success
    else if hu : nextShotPosition F z.position e = 1 then .failure
    else .active (raceNext hpsi F q z e h hu)

/-- Raw post-configuration tree retaining only the certified shot position.
This tree uses the original scheduler symbol, without redirection. -/
noncomputable def rawRaceStep (hpsi : psi > 0) (F : TwoGapFrame n)
    (bp : AState n psi × Nat) (e : Fin n) : StopNode (AState n psi × Nat) := by
  classical
  exact if RecoveryReadyOrDeleted F (attemptStepConf hpsi F bp.1 e) then .success
    else if nextShotPosition F bp.2 e = 1 then .failure
    else .active (postState hpsi F bp.1 e, nextShotPosition F bp.2 e)

def eraseRace (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat) :
    StopNode (RaceState hpsi F q) → StopNode (AState n psi × Nat)
  | .active z => .active (z.raw.val, z.position)
  | .success => .success
  | .failure => .failure

theorem raceStep_erases (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (x : StopNode (RaceState hpsi F q)) (e : Fin n) :
    eraseRace hpsi F q (stepNode (raceStep hpsi F q) x e) =
      stepNode (rawRaceStep hpsi F) (eraseRace hpsi F q x) e := by
  classical
  cases x with
  | success => rfl
  | failure => rfl
  | active z =>
      by_cases hs : RecoveryReadyOrDeleted F (attemptStepConf hpsi F z.raw.val e)
      · simp only [stepNode, raceStep, rawRaceStep, dif_pos hs, if_pos hs, eraseRace]
      · by_cases hu : nextShotPosition F z.position e = 1 <;>
          simp only [stepNode, raceStep, rawRaceStep, hs, hu, dite_true, dite_false,
            ite_true, ite_false, eraseRace, raceNext]

noncomputable def initialRace (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (x : AActive hpsi F) (hq : 0 < q) (hb : q + 1 ≤ F.attack.d)
    (hl : (x.val.conf (F.attack.pos (q + 1))).bullet = (2 : Fin 3)) :
    StopNode (RaceState hpsi F q) := by
  classical
  exact if hc : CleanReady F.recovery x.val.conf then .success
    else .active ⟨x, q + 1, by omega, hb, Nat.le_refl _, hl, hc⟩

noncomputable def initialRaw (F : TwoGapFrame n) (b : AState n psi) (q : Nat) :
    StopNode (AState n psi × Nat) := by
  classical
  exact if CleanReady F.recovery b.conf then .success else .active (b, q + 1)

theorem initialRace_erases (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (x : AActive hpsi F) (hq : 0 < q) (hb : q + 1 ≤ F.attack.d)
    (hl : (x.val.conf (F.attack.pos (q + 1))).bullet = (2 : Fin 3)) :
    eraseRace hpsi F q (initialRace hpsi F q x hq hb hl) = initialRaw F x.val q := by
  classical
  by_cases hc : CleanReady F.recovery x.val.conf <;>
    simp only [initialRace, initialRaw, hc, dite_true, dite_false, ite_true, ite_false, eraseRace]

theorem initial_ready_zero (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (x : AActive hpsi F) (hq : 0 < q) (hb : q + 1 ≤ F.attack.d)
    (hl : (x.val.conf (F.attack.pos (q + 1))).bullet = (2 : Fin 3))
    (hc : CleanReady F.recovery x.val.conf) :
    initialRace hpsi F q x hq hb hl = .success := by
  classical
  simp only [initialRace, dif_pos hc]

/-- Readiness wins even when the very same row also reaches position one. -/
theorem ready_arrival_tie_success (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (z : RaceState hpsi F q) (e : Fin n)
    (hc : CleanReady F.recovery (attemptStepConf hpsi F z.raw.val e)) :
    raceStep hpsi F q z e = .success := by
  classical
  exact dif_pos (.inl hc)

/-- A nondeletion success hands off the actual certified post-state.  Its
retained live shot is still in the localized sector, possibly already parked. -/
theorem success_payload (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (z : RaceState hpsi F q) (e : Fin n) (he : raceStep hpsi F q z e = .success) :
    NoResetSuccess F (attemptStepConf hpsi F z.raw.val e) ∨
      (AInvariant hpsi F (postState hpsi F z.raw.val e) ∧
        CleanReady F.recovery (attemptStepConf hpsi F z.raw.val e) ∧
        1 ≤ nextShotPosition F z.position e ∧ nextShotPosition F z.position e ≤ q + 1 ∧
        (attemptStepConf hpsi F z.raw.val e
          (F.attack.pos (nextShotPosition F z.position e))).bullet = (2 : Fin 3)) := by
  classical
  have hh : RecoveryReadyOrDeleted F (attemptStepConf hpsi F z.raw.val e) := by
    unfold raceStep at he
    split at he
    · assumption
    · split at he <;> cases he
  by_cases hd : NoResetSuccess F (attemptStepConf hpsi F z.raw.val e)
  · exact .inl hd
  · have hp := transit_unique_row hpsi F z.raw z.position z.lower z.upper z.live e
    exact .inr ⟨race_post_invariant hpsi F q z e hd, hh.resolve_right hd, hp.1,
      Nat.le_trans (next_position_le F z.position e) z.localized, hp.2.2.1⟩

noncomputable def recoveryWork (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat) :
    StopNode (RaceState hpsi F q) → Nat
  | .active z => gapWC F.recovery z.raw.val.conf
  | .success => 0
  | .failure => 0

noncomputable def recoveryPotential (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (x : StopNode (RaceState hpsi F q)) : Nat := n * recoveryWork hpsi F q x

noncomputable def chargePotential (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat) :
    StopNode (RaceState hpsi F q) → Nat
  | .active z => gapWC F.recovery z.raw.val.conf + (q + 1 - z.position)
  | .success => 0
  | .failure => q

private theorem physical_recovery_row (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (z : RaceState hpsi F q) :
    1 + (List.ofFn (fun e => gapWC F.recovery (attemptStepConf hpsi F z.raw.val e))).sum ≤
      n * gapWC F.recovery z.raw.val.conf := by
  have hn := race_not_done hpsi F q z
  have hconf : ∀ e, attemptStepConf hpsi F z.raw.val e = sinkStepC hpsi F.recovery z.raw.val.conf e :=
    fun e => postConf_eq_recovery hpsi F z.raw.val e
  have hm : ∀ e, gapWC F.recovery (attemptStepConf hpsi F z.raw.val e) ≤
      gapWC F.recovery z.raw.val.conf := by
    intro e
    rw [hconf]
    exact gapWC_step_le' hpsi F.recovery z.raw.val.conf z.raw.property.recovery hn e
  obtain ⟨e, he⟩ := exists_gapWC_step_lt' hpsi F.recovery z.raw.val.conf z.raw.property.recovery hn
  have hd : gapWC F.recovery (attemptStepConf hpsi F z.raw.val e) + 1 ≤
      gapWC F.recovery z.raw.val.conf := by rw [hconf]; omega
  have hs := LDSinkGapCleanup.ofFn_sum_lt n
    (fun e => gapWC F.recovery (attemptStepConf hpsi F z.raw.val e))
    (gapWC F.recovery z.raw.val.conf) e hm hd
  omega

private theorem recovery_child_le (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (z : RaceState hpsi F q) (e : Fin n) :
    recoveryWork hpsi F q (raceStep hpsi F q z e) ≤
      gapWC F.recovery (attemptStepConf hpsi F z.raw.val e) := by
  classical
  unfold raceStep
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · exact Nat.le_refl _

theorem recovery_bellman (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat) :
    NatBellmanSuperSolution (raceStep hpsi F q) 1 (recoveryPotential hpsi F q) := by
  refine ⟨rfl, rfl, ?_⟩
  intro z
  have hs := ofFn_sum_le _ _ (recovery_child_le hpsi F q z)
  have hr := physical_recovery_row hpsi F q z
  have hrow : 1 + (List.ofFn (fun e => recoveryWork hpsi F q (raceStep hpsi F q z e))).sum ≤
      n * recoveryWork hpsi F q (.active z) := by change _ ≤ n * gapWC F.recovery _; omega
  change 1 * n + (List.ofFn (fun e => n * recoveryWork hpsi F q (raceStep hpsi F q z e))).sum ≤
    n * (n * recoveryWork hpsi F q (.active z))
  rw [Nat.one_mul, ofFn_sum_mul_left]
  have h := Nat.mul_le_mul_left n hrow
  simpa only [Nat.mul_add, Nat.mul_one] using h

private theorem sum_spike (n : Nat) : ∀ a : Fin n,
    (List.ofFn (fun e : Fin n => if e = a then 1 else 0)).sum = 1 := by
  induction n with
  | zero => intro a; exact a.elim0
  | succ n ih =>
      intro a
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have ht : (List.ofFn (fun i : Fin n =>
            if i.succ = (0 : Fin (n + 1)) then 1 else 0)).sum = 0 := by
          have hh := ofFn_sum_eq
            (fun i : Fin n => if i.succ = (0 : Fin (n + 1)) then 1 else 0)
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
          (fun i : Fin n => if i.succ = a.succ then 1 else 0)
          (fun i : Fin n => if i = a then 1 else 0)
          (by intro i; simp only [Fin.succ_inj])
        rw [hh]
        exact ih a

private theorem charge_child_le (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (z : RaceState hpsi F q) (e : Fin n) :
    chargePotential hpsi F q (raceStep hpsi F q z e) ≤
      gapWC F.recovery (attemptStepConf hpsi F z.raw.val e) + (q + 1 - z.position) +
        (if e = F.attack.pos (z.position - 1) then 1 else 0) := by
  classical
  have hp := z.lower
  have hq := z.localized
  unfold raceStep
  split
  · exact Nat.zero_le _
  · split
    · rename_i hn hu
      change q ≤ _
      by_cases he : e = F.attack.pos (z.position - 1)
      · simp only [nextShotPosition, if_pos he] at hu
        rw [if_pos he]
        omega
      · simp only [nextShotPosition, if_neg he] at hu
        omega
    · change gapWC F.recovery (attemptStepConf hpsi F z.raw.val e) +
          (q + 1 - nextShotPosition F z.position e) ≤ _
      by_cases he : e = F.attack.pos (z.position - 1) <;>
        simp only [nextShotPosition, he, ite_true, ite_false] <;> omega

/-- The true K2 recovery rank pays the actual attack-motion charge, including
the final arrival edge that becomes failure. -/
theorem charge_potential_row (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (z : RaceState hpsi F q) :
    (List.ofFn (fun e => chargePotential hpsi F q (raceStep hpsi F q z e))).sum ≤
      n * chargePotential hpsi F q (.active z) := by
  have hs := ofFn_sum_le _ _ (charge_child_le hpsi F q z)
  rw [ofFn_sum_add, ofFn_sum_add, sum_spike, FiniteUniformStoppingTree.ofFn_sum_const] at hs
  have hr := physical_recovery_row hpsi F q z
  change _ ≤ n * (gapWC F.recovery z.raw.val.conf + (q + 1 - z.position))
  rw [Nat.mul_add]
  omega

/-- Finite failure charge bound from an arbitrary certified starting
distance.  The initial state may already be recovery-ready. -/
theorem failure_charge_bound (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (x : AActive hpsi F) (hq : 0 < q) (hb : q + 1 ≤ F.attack.d)
    (hl : (x.val.conf (F.attack.pos (q + 1))).bullet = (2 : Fin 3)) (T : Nat) :
    q * failureCount (raceStep hpsi F q) (initialRace hpsi F q x hq hb hl) T ≤
      n ^ T * gapWC F.recovery x.val.conf := by
  classical
  let z := initialRace hpsi F q x hq hb hl
  have hw : ∀ y : StopNode (RaceState hpsi F q),
      q * failureWeight y ≤ chargePotential hpsi F q y := by
    intro y
    cases y with
    | active y => exact Nat.zero_le _
    | success => exact Nat.le_refl _
    | failure => simp only [failureWeight, chargePotential, Nat.mul_one, Nat.le_refl]
  have hm := treeWeight_mono (raceStep hpsi F q)
    (fun y => q * failureWeight y) (chargePotential hpsi F q) hw z T
  rw [treeWeight_mul_left] at hm
  have ht := treeWeight_le_pow_mul_of_child_sum_le (raceStep hpsi F q)
    (chargePotential hpsi F q) (charge_potential_row hpsi F q) z T
  have hi : chargePotential hpsi F q z ≤ gapWC F.recovery x.val.conf := by
    dsimp only [z, initialRace]
    split
    · exact Nat.zero_le _
    · simp only [chargePotential, Nat.sub_self, Nat.add_zero, Nat.le_refl]
  exact Nat.le_trans hm (Nat.le_trans ht (Nat.mul_le_mul_left _ hi))

/-- The recovery stopping race pays all elapsed active interactions.  Losing
early to arrival can only reduce the genuine C5 cleanup cost. -/
theorem race_truncated_cost (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (x : AActive hpsi F) (hq : 0 < q) (hb : q + 1 ≤ F.attack.d)
    (hl : (x.val.conf (F.attack.pos (q + 1))).bullet = (2 : Fin 3)) (T : Nat) :
    truncatedActiveCostNumerator (raceStep hpsi F q) (initialRace hpsi F q x hq hb hl) T ≤
      n ^ T * (n * (2 * F.recovery.d)) := by
  classical
  let z := initialRace hpsi F q x hq hb hl
  have hc := truncatedActiveCostNumerator_mul_le_of_natSuperSolution (raceStep hpsi F q)
    1 (recoveryPotential hpsi F q) (recovery_bellman hpsi F q) z T
  have hp : recoveryPotential hpsi F q z ≤ n * (2 * F.recovery.d) := by
    dsimp only [z, initialRace]
    split
    · exact Nat.zero_le _
    · exact Nat.mul_le_mul_left n (gapWC_le_two_d hpsi F.recovery x.val.conf x.property.recovery)
  exact Nat.le_trans (by simpa only [Nat.one_mul] using hc) (Nat.mul_le_mul_left _ hp)

/-- At `8*n*a`, at most a quarter of the same race words remain active. -/
theorem race_active_quarter (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (x : AActive hpsi F) (hq : 0 < q) (hb : q + 1 ≤ F.attack.d)
    (hl : (x.val.conf (F.attack.pos (q + 1))).bullet = (2 : Fin 3)) :
    4 * activeCount (raceStep hpsi F q) (initialRace hpsi F q x hq hb hl)
      (8 * n * F.recovery.d) ≤ n ^ (8 * n * F.recovery.d) := by
  let T := 8 * n * F.recovery.d
  let z := initialRace hpsi F q x hq hb hl
  have hc := race_truncated_cost hpsi F q x hq hb hl T
  have hlive := horizon_mul_activeCount_le_truncatedActiveCostNumerator (raceStep hpsi F q) z T
  have hscaled : (n * (2 * F.recovery.d)) * (4 * activeCount (raceStep hpsi F q) z T) ≤
      (n * (2 * F.recovery.d)) * n ^ T := by
    calc
      (n * (2 * F.recovery.d)) * (4 * activeCount (raceStep hpsi F q) z T) =
          T * activeCount (raceStep hpsi F q) z T := by
        change (n * (2 * F.recovery.d)) * (4 * activeCount (raceStep hpsi F q) z T) =
          ((2 * 4) * n * F.recovery.d) * activeCount (raceStep hpsi F q) z T
        ac_rfl
      _ ≤ truncatedActiveCostNumerator (raceStep hpsi F q) z T := hlive
      _ ≤ n ^ T * (n * (2 * F.recovery.d)) := hc
      _ = (n * (2 * F.recovery.d)) * n ^ T := Nat.mul_comm _ _
  have hn : 0 < n := F.recovery.ring.hn
  have ha : 0 < 2 * F.recovery.d := by have h := F.recovery.hd; omega
  exact Nat.le_of_mul_le_mul_left hscaled (Nat.mul_pos hn ha)

/-- A shot localized at `16*a+1` needs `16*a` actual moving symbols to lose
this race.  Its arrival-first failure mass is at most one eighth, at every
finite horizon. -/
theorem localized_failure_eighth (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : AActive hpsi F) (hb : 16 * F.recovery.d + 1 ≤ F.attack.d)
    (hl : (x.val.conf (F.attack.pos (16 * F.recovery.d + 1))).bullet = (2 : Fin 3))
    (T : Nat) :
    8 * failureCount (raceStep hpsi F (16 * F.recovery.d))
      (initialRace hpsi F (16 * F.recovery.d) x (by have h := F.recovery.hd; omega) hb hl) T ≤
      n ^ T := by
  let q := 16 * F.recovery.d
  have hq : 0 < q := by have h := F.recovery.hd; dsimp only [q]; omega
  let z := initialRace hpsi F q x hq hb hl
  have hc := failure_charge_bound hpsi F q x hq hb hl T
  have hg := gapWC_le_two_d hpsi F.recovery x.val.conf x.property.recovery
  have hscaled : (2 * F.recovery.d) * (8 * failureCount (raceStep hpsi F q) z T) ≤
      (2 * F.recovery.d) * n ^ T := by
    calc
      (2 * F.recovery.d) * (8 * failureCount (raceStep hpsi F q) z T) =
          q * failureCount (raceStep hpsi F q) z T := by
        change (2 * F.recovery.d) * (8 * failureCount (raceStep hpsi F q) z T) =
          ((2 * 8) * F.recovery.d) * failureCount (raceStep hpsi F q) z T
        ac_rfl
      _ ≤ n ^ T * gapWC F.recovery x.val.conf := hc
      _ ≤ n ^ T * (2 * F.recovery.d) := Nat.mul_le_mul_left _ hg
      _ = (2 * F.recovery.d) * n ^ T := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_left hscaled (by have h := F.recovery.hd; omega)

theorem localized_success_five_eighths (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : AActive hpsi F) (hb : 16 * F.recovery.d + 1 ≤ F.attack.d)
    (hl : (x.val.conf (F.attack.pos (16 * F.recovery.d + 1))).bullet = (2 : Fin 3)) :
    5 * n ^ (8 * n * F.recovery.d) ≤
      8 * successCount (raceStep hpsi F (16 * F.recovery.d))
        (initialRace hpsi F (16 * F.recovery.d) x (by have h := F.recovery.hd; omega) hb hl)
        (8 * n * F.recovery.d) := by
  have hq : 0 < 16 * F.recovery.d := by have h := F.recovery.hd; omega
  have ha := race_active_quarter hpsi F (16 * F.recovery.d) x hq hb hl
  have hf := localized_failure_eighth hpsi F x hb hl (8 * n * F.recovery.d)
  have hp := node_count_partition (raceStep hpsi F (16 * F.recovery.d))
    (initialRace hpsi F (16 * F.recovery.d) x hq hb hl) (8 * n * F.recovery.d)
  omega

theorem race_treeWeight_erases (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (w : StopNode (AState n psi × Nat) → Nat)
    (x : StopNode (RaceState hpsi F q)) (T : Nat) :
    treeWeight (raceStep hpsi F q) (fun y => w (eraseRace hpsi F q y)) x T =
      treeWeight (rawRaceStep hpsi F) w (eraseRace hpsi F q x) T := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      simp only [treeWeight]
      apply ofFn_sum_eq
      intro e
      rw [ih, raceStep_erases]

theorem race_counts_erases (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (x : StopNode (RaceState hpsi F q)) (T : Nat) :
    activeCount (raceStep hpsi F q) x T =
        activeCount (rawRaceStep hpsi F) (eraseRace hpsi F q x) T ∧
      successCount (raceStep hpsi F q) x T =
        successCount (rawRaceStep hpsi F) (eraseRace hpsi F q x) T ∧
      failureCount (raceStep hpsi F q) x T =
        failureCount (rawRaceStep hpsi F) (eraseRace hpsi F q x) T := by
  have ha : (fun y => activeWeight (eraseRace hpsi F q y)) = activeWeight := by
    funext y
    cases y <;> rfl
  have hs : (fun y => successWeight (eraseRace hpsi F q y)) = successWeight := by
    funext y
    cases y <;> rfl
  have hf : (fun y => failureWeight (eraseRace hpsi F q y)) = failureWeight := by
    funext y
    cases y <;> rfl
  exact ⟨by simpa only [activeCount, ha] using race_treeWeight_erases hpsi F q activeWeight x T,
    by simpa only [successCount, hs] using race_treeWeight_erases hpsi F q successWeight x T,
    by simpa only [failureCount, hf] using race_treeWeight_erases hpsi F q failureWeight x T⟩

/-- All three counts are on the literal uniform physical update tree,
including immediate initial readiness and same-edge readiness/arrival ties. -/
theorem localized_raw_mass_bounds (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : AActive hpsi F) (hb : 16 * F.recovery.d + 1 ≤ F.attack.d)
    (hl : (x.val.conf (F.attack.pos (16 * F.recovery.d + 1))).bullet = (2 : Fin 3)) :
    8 * failureCount (rawRaceStep hpsi F) (initialRaw F x.val (16 * F.recovery.d))
        (8 * n * F.recovery.d) ≤ n ^ (8 * n * F.recovery.d) ∧
      4 * activeCount (rawRaceStep hpsi F) (initialRaw F x.val (16 * F.recovery.d))
        (8 * n * F.recovery.d) ≤ n ^ (8 * n * F.recovery.d) ∧
      5 * n ^ (8 * n * F.recovery.d) ≤
        8 * successCount (rawRaceStep hpsi F) (initialRaw F x.val (16 * F.recovery.d))
          (8 * n * F.recovery.d) := by
  have hq : 0 < 16 * F.recovery.d := by have h := F.recovery.hd; omega
  have he := race_counts_erases hpsi F (16 * F.recovery.d)
    (initialRace hpsi F (16 * F.recovery.d) x hq hb hl) (8 * n * F.recovery.d)
  rw [initialRace_erases] at he
  refine ⟨?_, ?_, ?_⟩
  · have h := localized_failure_eighth hpsi F x hb hl (8 * n * F.recovery.d)
    rwa [he.2.2] at h
  · have h := race_active_quarter hpsi F (16 * F.recovery.d) x hq hb hl
    rwa [he.1] at h
  · have h := localized_success_five_eighths hpsi F x hb hl
    rwa [he.2.1] at h

theorem localized_raw_half (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : AActive hpsi F) (hb : 16 * F.recovery.d + 1 ≤ F.attack.d)
    (hl : (x.val.conf (F.attack.pos (16 * F.recovery.d + 1))).bullet = (2 : Fin 3)) :
    n ^ (8 * n * F.recovery.d) ≤
      2 * successCount (rawRaceStep hpsi F) (initialRaw F x.val (16 * F.recovery.d))
        (8 * n * F.recovery.d) := by
  have h := (localized_raw_mass_bounds hpsi F x hb hl).2.2
  omega

end LDSinkTwoGapRaceEntranceLocalizedRecovery

#print axioms LDSinkTwoGapRaceEntranceLocalizedRecovery.race_post_invariant
#print axioms LDSinkTwoGapRaceEntranceLocalizedRecovery.raceStep_erases
#print axioms LDSinkTwoGapRaceEntranceLocalizedRecovery.success_payload
#print axioms LDSinkTwoGapRaceEntranceLocalizedRecovery.recovery_bellman
#print axioms LDSinkTwoGapRaceEntranceLocalizedRecovery.charge_potential_row
#print axioms LDSinkTwoGapRaceEntranceLocalizedRecovery.failure_charge_bound
#print axioms LDSinkTwoGapRaceEntranceLocalizedRecovery.race_active_quarter
#print axioms LDSinkTwoGapRaceEntranceLocalizedRecovery.localized_failure_eighth
#print axioms LDSinkTwoGapRaceEntranceLocalizedRecovery.localized_raw_mass_bounds
#print axioms LDSinkTwoGapRaceEntranceLocalizedRecovery.localized_raw_half
