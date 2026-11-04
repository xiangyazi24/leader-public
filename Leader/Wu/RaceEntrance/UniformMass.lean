import Leader.Wu.Birth.ControlledBirthShotComposition
import Leader.Wu.RaceEntrance.UnshieldService
import Leader.Wu.RaceEntrance.CollapseBudget
import Leader.Core.ControlledSuccessCoverage

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDTwoGapFrame LDSinkTwoGapNoResetKernel
open LDSinkTwoGapDeletion LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant
open LDSinkTwoGapArrivalRaceMass LDSinkTwoGapRaceEntranceControlledTail
open LDSinkTwoGapControlledBirthShotComposition
open LDSinkTwoGapRaceEntranceUnshieldService
open LDSinkTwoGapRaceEntranceCollapseBudget LDSinkTwoGapRaceEntranceAuditCoverage

namespace LDSinkTwoGapRaceEntranceUniformMass

variable {n psi : Nat}

/-!
All three services are actual K2 steps: remove the old shared shield, create
an outgoing fresh live shot, and deliver it to physical deletion.  A bounded
adaptive scheduler audit then transfers the resulting count to the original
uniform scheduler.  The recovery gap is at least the attack gap.  The first
unshield cost remains in the horizon and is not silently charged to the
shorter attack gap.
-/

private theorem unshield_active_data (hpsi : psi > 0) (F : TwoGapFrame n)
    (z y : UnshieldState hpsi F) (e : Fin n)
    (he : unshieldStep hpsi F z e = .active y) :
    y.val = postState hpsi F z.val (controlledPort F z.val.conf e) ∧
      ¬ UnshieldedOrDeleted F
        (attemptStepConf hpsi F z.val (controlledPort F z.val.conf e)) := by
  classical
  unfold unshieldStep at he
  split at he
  · cases he
  · rename_i hn
    exact ⟨congrArg Subtype.val (StopNode.active.inj he).symm, hn⟩

/-- The handoff is the same physical interaction that ended unshield service. -/
noncomputable def unshieldHandoff (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : UnshieldState hpsi F) (e : Fin n) : StopNode (AState n psi) :=
  controlledPhysicalStep hpsi F z.val e

theorem unshieldHandoff_quarter (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : UnshieldState hpsi F) (e : Fin n)
    (he : unshieldStep hpsi F z e = .success) :
    n ^ (2 * n * (13 * F.attack.d + 7)) ≤
      4 * successCount (controlledPhysicalStep hpsi F) (unshieldHandoff hpsi F z e)
        (2 * n * (13 * F.attack.d + 7)) := by
  classical
  have hu : UnshieldedOrDeleted F
      (attemptStepConf hpsi F z.val (controlledPort F z.val.conf e)) := by
    unfold unshieldStep at he
    split at he
    · assumption
    · cases he
  unfold unshieldHandoff controlledPhysicalStep
  rw [physicalBlockStep_normal_form]
  by_cases hd : NoResetSuccess F
      (attemptStepConf hpsi F z.val (controlledPort F z.val.conf e))
  · rw [if_pos hd]
    simp only [successCount, treeWeight_success, successWeight, Nat.mul_one]
    omega
  · rw [if_neg hd]
    have hs : (attemptStepConf hpsi F z.val (controlledPort F z.val.conf e)
        (deletePort F)).shield = false := hu.resolve_right hd
    have hg : GapPair hpsi F (postState hpsi F z.val (controlledPort F z.val.conf e)) := by
      apply LDSinkTwoGapRestartClosure.gapPair_physical_step hpsi F
        (CleanBoundaryDecision.restartCleanBoundarySignalResidual_K2 hpsi F)
        z.val (controlledPort F z.val.conf e) _ z.property
      rw [physicalBlockStep_normal_form, if_neg hd]
    exact gapPair_unshielded_deletion_quarter hpsi F _ hg hs

noncomputable def unshieldDeletionStep (hpsi : psi > 0) (F : TwoGapFrame n) :=
  sequentialStep (unshieldStep hpsi F) (controlledPhysicalStep hpsi F) (unshieldHandoff hpsi F)

def eraseService (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (Sum (UnshieldState hpsi F) (AState n psi)) → StopNode (AState n psi)
  | .active (.inl z) => .active z.val
  | .active (.inr b) => .active b
  | .success => .success
  | .failure => .failure

private theorem eraseService_inRace (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (AState n psi)) : eraseService hpsi F (inRace x) = x := by
  cases x <;> rfl

/-- The first-unshield handoff consumes no extra interaction and preserves
the full physical state, including the existing phase classifier. -/
theorem unshieldDeletionStep_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (Sum (UnshieldState hpsi F) (AState n psi))) (e : Fin n) :
    eraseService hpsi F (stepNode (unshieldDeletionStep hpsi F) x e) =
      stepNode (controlledPhysicalStep hpsi F) (eraseService hpsi F x) e := by
  classical
  cases x with
  | success => rfl
  | failure => rfl
  | active x =>
      cases x with
      | inr b => exact eraseService_inRace hpsi F _
      | inl z =>
          change eraseService hpsi F
            (sequentialStep (unshieldStep hpsi F) (controlledPhysicalStep hpsi F)
              (unshieldHandoff hpsi F) (.inl z) e) = controlledPhysicalStep hpsi F z.val e
          cases he : unshieldStep hpsi F z e with
          | success =>
              simp only [sequentialStep, he, eraseService_inRace, unshieldHandoff]
          | failure =>
              unfold unshieldStep at he
              split at he <;> cases he
          | active y =>
              have hd := unshield_active_data hpsi F z y e he
              have hn : ¬ NoResetSuccess F
                  (attemptStepConf hpsi F z.val (controlledPort F z.val.conf e)) :=
                fun h => hd.2 (.inr h)
              simp only [sequentialStep, he, eraseService, controlledPhysicalStep]
              rw [physicalBlockStep_normal_form, if_neg hn, hd.1]

theorem unshield_deletion_simulation (hpsi : psi > 0) (F : TwoGapFrame n) :
    SuccessSimulation (unshieldDeletionStep hpsi F) (controlledPhysicalStep hpsi F)
      (fun x y => eraseService hpsi F x = y) where
  terminal := by
    intro x y h
    rw [← h]
    cases x with
    | success => exact Nat.le_refl _
    | failure => exact Nat.le_refl _
    | active x => cases x <;> exact Nat.le_refl _
  next := by
    intro x y h e
    rw [← h]
    exact unshieldDeletionStep_erases hpsi F x e

/-- Actual controlled deletion mass from every gap pair.  No initial shield,
phase, rank, or entrance-service hypothesis is carried by this theorem. -/
theorem gapPair_controlled_deletion_eighth (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b) :
    n ^ (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) ≤
      8 * successCount (controlledPhysicalStep hpsi F) (.active b)
        (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) := by
  let z : UnshieldState hpsi F := ⟨b, hg⟩
  let H := 2 * n * (2 * F.recovery.d + 1)
  let L := 2 * n * (13 * F.attack.d + 7)
  have hseq := sequential_mass (unshieldStep hpsi F) (controlledPhysicalStep hpsi F)
    (unshieldHandoff hpsi F) z H L 2 4 (unshield_half hpsi F z)
    (unshieldHandoff_quarter hpsi F)
  have hsim := successCount_le_of_simulation (unshieldDeletionStep hpsi F)
    (controlledPhysicalStep hpsi F) (fun x y => eraseService hpsi F x = y)
    (unshield_deletion_simulation hpsi F) (.active (.inl z)) (.active b) rfl (H + L)
  have htime : H + L = 2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8) := by
    dsimp only [H, L]
    rw [← Nat.mul_add]
    congr 1
    omega
  change n ^ (H + L) ≤ 8 * successCount (unshieldDeletionStep hpsi F)
    (.active (.inl z)) (H + L) at hseq
  rw [htime] at hseq hsim
  exact Nat.le_trans hseq (Nat.mul_le_mul_left 8 hsim)

theorem physical_controlled_step_eq (hpsi : psi > 0) (F : TwoGapFrame n) :
    ControlledSchedulerMass.controlledStep (physicalBlockStep hpsi F) (physicalRedirection F) =
      controlledPhysicalStep hpsi F := by
  funext b e
  simp only [ControlledSchedulerMass.controlledStep, physical_effective_eq, controlledPhysicalStep]

/-- The coarse dummy-service budget covers the complete three-service
horizon when the recovery gap is at least the attack gap. -/
theorem physical_audit_failure_sixteenth (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b) (hab : F.attack.d ≤ F.recovery.d) :
    16 * failureCount (ControlledSchedulerMass.auditStep (physicalBlockStep hpsi F)
      (physicalRedirection F)) (.active (b, 1231))
        (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) ≤
      n ^ (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) := by
  let T := 2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)
  let R := serviceLength F
  let f := failureCount (ControlledSchedulerMass.auditStep (physicalBlockStep hpsi F)
    (physicalRedirection F)) (.active (b, 1231)) T
  have hR : 0 < R := by
    have hd := F.recovery.hd
    dsimp only [R, serviceLength]
    omega
  have hn : 0 < n := by have hd := F.recovery.hdn; omega
  have htime : 2 * (2 * F.recovery.d + 13 * F.attack.d + 8) ≤ 76 * R := by
    have hd := F.recovery.hd
    dsimp only [R, serviceLength]
    omega
  have htime' : T ≤ 76 * (n * R) := by
    have h := Nat.mul_le_mul_left n htime
    simpa only [T, Nat.mul_assoc, Nat.mul_left_comm] using h
  have hupper : n * R + T ≤ (n * R) * 77 := by
    rw [Nat.mul_comm (n * R) 77]
    omega
  have hb := physical_audit_failure_bound hpsi F 1231 b hg T
  change n * (R * 1232) * f ≤ n ^ T * (n * R + T) at hb
  have hscaled : ((n * R) * 77) * (16 * f) ≤ ((n * R) * 77) * n ^ T := by
    calc
      ((n * R) * 77) * (16 * f) = n * (R * 1232) * f := by
        simp only [Nat.mul_assoc]
        rw [← Nat.mul_assoc 77 16 f]
      _ ≤ n ^ T * (n * R + T) := hb
      _ ≤ n ^ T * ((n * R) * 77) := Nat.mul_le_mul_left _ hupper
      _ = ((n * R) * 77) * n ^ T := Nat.mul_comm _ _
  have hpos : 0 < (n * R) * 77 := Nat.mul_pos (Nat.mul_pos hn hR) (by decide)
  exact Nat.le_of_mul_le_mul_left hscaled hpos

/-- At least one sixteenth of the controlled words both delete and respect
the fixed collapse budget, on the literal physical audit tree. -/
theorem gapPair_bounded_deletion_sixteenth (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b) (hab : F.attack.d ≤ F.recovery.d) :
    n ^ (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) ≤
      16 * ControlledSchedulerMass.boundedSuccessCount (physicalBlockStep hpsi F)
        (physicalRedirection F) (.active b)
        (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) 1231 := by
  have hc := gapPair_controlled_deletion_eighth hpsi F b hg
  have hf := physical_audit_failure_sixteenth hpsi F b hg hab
  have hcover := controlled_success_covered (physicalBlockStep hpsi F)
    (physicalRedirection F) (.active b)
    (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) 1231
  rw [physical_controlled_step_eq] at hcover
  change _ ≤ 16 * successCount (ControlledSchedulerMass.auditStep (physicalBlockStep hpsi F)
    (physicalRedirection F)) (.active (b, 1231)) _
  simp only [ControlledSchedulerMass.withBudget] at hcover
  omega

/-- Absolute collapse budget for the complete service horizon. -/
def uniformCollapseBudget : Nat := 1231

/-- Original uniform K2 scheduler, fixed deterministic horizon, and actual
endpoint deletion.  The denominator is an absolute constant, independent of
both gap lengths and ring size.  The ordering premise remains explicit. -/
theorem gapPair_uniform_deletion_mass (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b) (hab : F.attack.d ≤ F.recovery.d) :
    n ^ (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) ≤
      (16 * 2 ^ uniformCollapseBudget) * successCount (physicalBlockStep hpsi F) (.active b)
        (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) := by
  exact ControlledSchedulerMass.raw_success_mass_lower (physicalBlockStep hpsi F)
    (physicalRedirection F) (.active b)
    (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) uniformCollapseBudget 16
    (gapPair_bounded_deletion_sixteenth hpsi F b hg hab)

end LDSinkTwoGapRaceEntranceUniformMass

#print axioms LDSinkTwoGapRaceEntranceUniformMass.unshieldHandoff_quarter
#print axioms LDSinkTwoGapRaceEntranceUniformMass.unshieldDeletionStep_erases
#print axioms LDSinkTwoGapRaceEntranceUniformMass.unshield_deletion_simulation
#print axioms LDSinkTwoGapRaceEntranceUniformMass.gapPair_controlled_deletion_eighth
#print axioms LDSinkTwoGapRaceEntranceUniformMass.physical_audit_failure_sixteenth
#print axioms LDSinkTwoGapRaceEntranceUniformMass.gapPair_bounded_deletion_sixteenth
#print axioms LDSinkTwoGapRaceEntranceUniformMass.gapPair_uniform_deletion_mass
