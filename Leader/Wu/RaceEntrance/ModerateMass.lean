import Leader.Wu.RaceEntrance.UniformMass

set_option autoImplicit false

open FiniteUniformStoppingTree LDTwoGapFrame LDSinkTwoGapNoResetKernel
open LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant
open LDSinkTwoGapRaceEntranceControlledTail LDSinkTwoGapRaceEntranceCollapseBudget
open LDSinkTwoGapRaceEntranceAuditCoverage LDSinkTwoGapRaceEntranceUniformMass

namespace LDSinkTwoGapRaceEntranceModerateMass

variable {n psi : Nat}

/-!
The already proved three-service controlled deletion count holds for all
gap lengths.  Only its finite collapse-budget cutoff needs a ratio bound.
For `b <= 16*a+1`, the same actual pending-dummy producer bounds the audit
failure mass with a larger absolute budget.  No additional physical row,
exact dummy-cycle theorem, or entrance hypothesis is introduced here.
-/

theorem moderate_audit_failure_sixteenth (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b)
    (hab : F.attack.d ≤ 16 * F.recovery.d + 1) :
    16 * failureCount (ControlledSchedulerMass.auditStep (physicalBlockStep hpsi F)
      (physicalRedirection F)) (.active (b, 14127))
        (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) ≤
      n ^ (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) := by
  let T := 2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)
  let R := serviceLength F
  let f := failureCount (ControlledSchedulerMass.auditStep (physicalBlockStep hpsi F)
    (physicalRedirection F)) (.active (b, 14127)) T
  have hR : 0 < R := by
    have hd := F.recovery.hd
    dsimp only [R, serviceLength]
    omega
  have hn : 0 < n := F.recovery.ring.hn
  have htime : 2 * (2 * F.recovery.d + 13 * F.attack.d + 8) ≤ 882 * R := by
    have hd := F.recovery.hd
    dsimp only [R, serviceLength]
    omega
  have htime' : T ≤ 882 * (n * R) := by
    have h := Nat.mul_le_mul_left n htime
    simpa only [T, Nat.mul_assoc, Nat.mul_left_comm] using h
  have hupper : n * R + T ≤ (n * R) * 883 := by
    rw [Nat.mul_comm (n * R) 883]
    omega
  have hb := physical_audit_failure_bound hpsi F 14127 b hg T
  change n * (R * 14128) * f ≤ n ^ T * (n * R + T) at hb
  have hscaled : ((n * R) * 883) * (16 * f) ≤ ((n * R) * 883) * n ^ T := by
    calc
      ((n * R) * 883) * (16 * f) = n * (R * 14128) * f := by
        simp only [Nat.mul_assoc]
        rw [← Nat.mul_assoc 883 16 f]
      _ ≤ n ^ T * (n * R + T) := hb
      _ ≤ n ^ T * ((n * R) * 883) := Nat.mul_le_mul_left _ hupper
      _ = ((n * R) * 883) * n ^ T := Nat.mul_comm _ _
  have hpos : 0 < (n * R) * 883 := Nat.mul_pos (Nat.mul_pos hn hR) (by decide)
  exact Nat.le_of_mul_le_mul_left hscaled hpos

theorem moderate_bounded_deletion_sixteenth (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b)
    (hab : F.attack.d ≤ 16 * F.recovery.d + 1) :
    n ^ (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) ≤
      16 * ControlledSchedulerMass.boundedSuccessCount (physicalBlockStep hpsi F)
        (physicalRedirection F) (.active b)
        (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) 14127 := by
  have hc := gapPair_controlled_deletion_eighth hpsi F b hg
  have hf := moderate_audit_failure_sixteenth hpsi F b hg hab
  have hcover := controlled_success_covered (physicalBlockStep hpsi F)
    (physicalRedirection F) (.active b)
    (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) 14127
  rw [physical_controlled_step_eq] at hcover
  change _ ≤ 16 * successCount (ControlledSchedulerMass.auditStep (physicalBlockStep hpsi F)
    (physicalRedirection F)) (.active (b, 14127)) _
  simp only [ControlledSchedulerMass.withBudget] at hcover
  omega

def moderateCollapseBudget : Nat := 14127

/-- Actual original-scheduler deletion mass from every gap pair in the
moderate-ratio regime.  Initial shield and phase remain unrestricted. -/
theorem gapPair_moderate_uniform_deletion_mass (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b)
    (hab : F.attack.d ≤ 16 * F.recovery.d + 1) :
    n ^ (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) ≤
      (16 * 2 ^ moderateCollapseBudget) * successCount (physicalBlockStep hpsi F) (.active b)
        (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) := by
  exact ControlledSchedulerMass.raw_success_mass_lower (physicalBlockStep hpsi F)
    (physicalRedirection F) (.active b)
    (2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)) moderateCollapseBudget 16
    (moderate_bounded_deletion_sixteenth hpsi F b hg hab)

theorem horizon_le_thirty_n_span (F : TwoGapFrame n) :
    2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8) ≤
      30 * n * (F.recovery.d + F.attack.d) := by
  have ha := F.recovery.hd
  have hb := F.attack.hd
  have hs : 2 * (2 * F.recovery.d + 13 * F.attack.d + 8) ≤
      30 * (F.recovery.d + F.attack.d) := by omega
  have hm := Nat.mul_le_mul_left n hs
  simpa only [Nat.mul_assoc, Nat.mul_left_comm] using hm

/-- Constant physical deletion mass at a common linear pair-span horizon. -/
theorem gapPair_moderate_uniform_at_span (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b)
    (hab : F.attack.d ≤ 16 * F.recovery.d + 1) :
    n ^ (30 * n * (F.recovery.d + F.attack.d)) ≤
      (16 * 2 ^ moderateCollapseBudget) * successCount (physicalBlockStep hpsi F) (.active b)
        (30 * n * (F.recovery.d + F.attack.d)) := by
  let T := 2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)
  let H := 30 * n * (F.recovery.d + F.attack.d)
  let K := 16 * 2 ^ moderateCollapseBudget
  have ht : T ≤ H := horizon_le_thirty_n_span F
  have hsum : T + (H - T) = H := by omega
  have hm := gapPair_moderate_uniform_deletion_mass hpsi F b hg hab
  have hp := ThreePortSerialCount.success_padding (physicalBlockStep hpsi F)
    (.active b) T (H - T)
  rw [hsum] at hp
  change n ^ T ≤ K * successCount (physicalBlockStep hpsi F) (.active b) T at hm
  calc
    n ^ H = n ^ (H - T) * n ^ T := by
      rw [← Nat.pow_add]
      congr 1
      omega
    _ ≤ n ^ (H - T) * (K * successCount (physicalBlockStep hpsi F) (.active b) T) :=
      Nat.mul_le_mul_left _ hm
    _ = K * (n ^ (H - T) * successCount (physicalBlockStep hpsi F) (.active b) T) :=
      Nat.mul_left_comm _ _ _
    _ ≤ K * successCount (physicalBlockStep hpsi F) (.active b) H := Nat.mul_le_mul_left K hp

end LDSinkTwoGapRaceEntranceModerateMass

#print axioms LDSinkTwoGapRaceEntranceModerateMass.moderate_audit_failure_sixteenth
#print axioms LDSinkTwoGapRaceEntranceModerateMass.moderate_bounded_deletion_sixteenth
#print axioms LDSinkTwoGapRaceEntranceModerateMass.gapPair_moderate_uniform_deletion_mass
#print axioms LDSinkTwoGapRaceEntranceModerateMass.horizon_le_thirty_n_span
#print axioms LDSinkTwoGapRaceEntranceModerateMass.gapPair_moderate_uniform_at_span
