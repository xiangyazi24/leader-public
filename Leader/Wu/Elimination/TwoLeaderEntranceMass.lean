import Leader.Wu.Elimination.TwoLeaderEntranceComposition
import Leader.Wu.Elimination.TwoLeaderEntranceBudget
import Leader.Core.ControlledSuccessCoverage

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open K2TwoLeaderGeometry K2TwoLeaderEntranceCore
open K2TwoLeaderEntranceComposition K2TwoLeaderEntranceBudget
open LDSinkTwoGapRaceEntranceAuditCoverage

namespace K2TwoLeaderEntranceMass

variable {n psi : Nat}

/-! Constant original-scheduler deletion mass on the actual complementary
pair.  The ordered choice bounds a physically proved dummy-service audit;
there is no external assumption on the number of collapsed events. -/

/-- The coarse dummy-service budget covers the complete three-service
horizon when the recovery gap is at least the attack gap. -/
theorem physical_audit_failure_sixteenth (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (b : (Fin n → AgentState psi)) (hg : WrapInvariant hpsi F b) (hab : F.attack.d ≤ F.recovery.d) :
    16 * failureCount (ControlledSchedulerMass.auditStep (originalPhysicalStep hpsi F)
      (redirection F)) (.active (b, 1263))
        (2 * n * (2 * F.recovery.d + 14 * F.attack.d + 7)) ≤
      n ^ (2 * n * (2 * F.recovery.d + 14 * F.attack.d + 7)) := by
  let T := 2 * n * (2 * F.recovery.d + 14 * F.attack.d + 7)
  let R := serviceLength F
  let f := failureCount (ControlledSchedulerMass.auditStep (originalPhysicalStep hpsi F)
    (redirection F)) (.active (b, 1263)) T
  have hR : 0 < R := by
    have hd := F.recovery.hd
    dsimp only [R, serviceLength]
    omega
  have hn : 0 < n := by have hd := F.recovery.hdn; omega
  have htime : 2 * (2 * F.recovery.d + 14 * F.attack.d + 7) ≤ 78 * R := by
    have hd := F.recovery.hd
    dsimp only [R, serviceLength]
    omega
  have htime' : T ≤ 78 * (n * R) := by
    have h := Nat.mul_le_mul_left n htime
    simpa only [T, Nat.mul_assoc, Nat.mul_left_comm] using h
  have hupper : n * R + T ≤ (n * R) * 79 := by
    rw [Nat.mul_comm (n * R) 79]
    omega
  have hb := physical_audit_failure_bound hpsi F 1263 b hg T
  change n * (R * 1264) * f ≤ n ^ T * (n * R + T) at hb
  have hscaled : ((n * R) * 79) * (16 * f) ≤ ((n * R) * 79) * n ^ T := by
    calc
      ((n * R) * 79) * (16 * f) = n * (R * 1264) * f := by
        simp only [Nat.mul_assoc]
        rw [← Nat.mul_assoc 79 16 f]
      _ ≤ n ^ T * (n * R + T) := hb
      _ ≤ n ^ T * ((n * R) * 79) := Nat.mul_le_mul_left _ hupper
      _ = ((n * R) * 79) * n ^ T := Nat.mul_comm _ _
  have hpos : 0 < (n * R) * 79 := Nat.mul_pos (Nat.mul_pos hn hR) (by decide)
  exact Nat.le_of_mul_le_mul_left hscaled hpos

/-- At least one sixteenth of the controlled words both delete and respect
the fixed collapse budget, on the literal physical audit tree. -/
theorem bounded_deletion_sixteenth (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (b : (Fin n → AgentState psi)) (hg : WrapInvariant hpsi F b) (hab : F.attack.d ≤ F.recovery.d) :
    n ^ (2 * n * (2 * F.recovery.d + 14 * F.attack.d + 7)) ≤
      16 * ControlledSchedulerMass.boundedSuccessCount (originalPhysicalStep hpsi F)
        (redirection F) (.active b)
        (2 * n * (2 * F.recovery.d + 14 * F.attack.d + 7)) 1263 := by
  have hc := controlled_deletion_eighth hpsi F b hg
  have hf := physical_audit_failure_sixteenth hpsi F b hg hab
  have hcover := controlled_success_covered (originalPhysicalStep hpsi F)
    (redirection F) (.active b)
    (2 * n * (2 * F.recovery.d + 14 * F.attack.d + 7)) 1263
  rw [physical_controlled_eq] at hcover
  change _ ≤ 16 * successCount (ControlledSchedulerMass.auditStep (originalPhysicalStep hpsi F)
    (redirection F)) (.active (b, 1263)) _
  simp only [ControlledSchedulerMass.withBudget] at hcover
  omega

/-- Absolute collapse budget for the complete service horizon. -/
def uniformCollapseBudget : Nat := 1263

/-- Original uniform K2 scheduler, fixed deterministic horizon, and actual
endpoint deletion.  The denominator is an absolute constant, independent of
both gap lengths and ring size.  The ordering premise remains explicit. -/
theorem uniform_deletion_mass (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (b : (Fin n → AgentState psi)) (hg : WrapInvariant hpsi F b) (hab : F.attack.d ≤ F.recovery.d) :
    n ^ (2 * n * (2 * F.recovery.d + 14 * F.attack.d + 7)) ≤
      (16 * 2 ^ uniformCollapseBudget) * successCount (originalPhysicalStep hpsi F) (.active b)
        (2 * n * (2 * F.recovery.d + 14 * F.attack.d + 7)) := by
  exact ControlledSchedulerMass.raw_success_mass_lower (originalPhysicalStep hpsi F)
    (redirection F) (.active b)
    (2 * n * (2 * F.recovery.d + 14 * F.attack.d + 7)) uniformCollapseBudget 16
    (bounded_deletion_sixteenth hpsi F b hg hab)

/-- The complete first-unshield, birth, and shot horizon is linear in the
physical pair span.  Both gap lengths remain visible in this bound. -/
theorem ordered_horizon_le_square (F : TwoLeaderFrame n)
    (hab : F.attack.d ≤ F.recovery.d) :
    2 * n * (2 * F.recovery.d + 14 * F.attack.d + 7) ≤
      20 * n * n := by
  have hb := F.attack.hd
  have hs : 2 * (2 * F.recovery.d + 14 * F.attack.d + 7) ≤
      20 * (F.recovery.d + F.attack.d) := by omega
  rw [F.lengths_sum] at hs
  have hm := Nat.mul_le_mul_left n hs
  simpa only [Nat.mul_assoc, Nat.mul_left_comm] using hm

/-- Absorbing success pads the proved physical count to a simple quadratic
horizon, without restarting the protocol or discarding scheduler symbols. -/
theorem uniform_deletion_at_square (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (b : (Fin n → AgentState psi)) (hg : WrapInvariant hpsi F b) (hab : F.attack.d ≤ F.recovery.d) :
    n ^ (20 * n * n) ≤
      (16 * 2 ^ uniformCollapseBudget) * successCount (originalPhysicalStep hpsi F) (.active b)
        (20 * n * n) := by
  let T := 2 * n * (2 * F.recovery.d + 14 * F.attack.d + 7)
  let H := 20 * n * n
  let K := 16 * 2 ^ uniformCollapseBudget
  have ht : T ≤ H := ordered_horizon_le_square F hab
  have hsum : T + (H - T) = H := by omega
  have hm := uniform_deletion_mass hpsi F b hg hab
  have hp := ThreePortSerialCount.success_padding (originalPhysicalStep hpsi F)
    (.active b) T (H - T)
  rw [hsum] at hp
  change n ^ T ≤ K * successCount (originalPhysicalStep hpsi F) (.active b) T at hm
  calc
    n ^ H = n ^ (H - T) * n ^ T := by
      rw [← Nat.pow_add]
      congr 1
      omega
    _ ≤ n ^ (H - T) * (K * successCount (originalPhysicalStep hpsi F) (.active b) T) :=
      Nat.mul_le_mul_left _ hm
    _ = K * (n ^ (H - T) * successCount (originalPhysicalStep hpsi F) (.active b) T) :=
      Nat.mul_left_comm _ _ _
    _ ≤ K * successCount (originalPhysicalStep hpsi F) (.active b) H := Nat.mul_le_mul_left K hp

end K2TwoLeaderEntranceMass

#print axioms K2TwoLeaderEntranceMass.physical_audit_failure_sixteenth
#print axioms K2TwoLeaderEntranceMass.bounded_deletion_sixteenth
#print axioms K2TwoLeaderEntranceMass.uniform_deletion_mass
#print axioms K2TwoLeaderEntranceMass.ordered_horizon_le_square
#print axioms K2TwoLeaderEntranceMass.uniform_deletion_at_square
