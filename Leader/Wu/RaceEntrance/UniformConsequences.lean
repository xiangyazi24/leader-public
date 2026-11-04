import Leader.Wu.RaceEntrance.UniformMass
import Leader.Wu.RaceEntrance.SupportResolution

set_option autoImplicit false

open FiniteUniformStoppingTree LDTwoGapFrame LDSinkTwoGapNoResetKernel
open LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant LDSinkTwoGapArrivalRaceMass
open LDSinkTwoGapRaceEntranceUniformMass LDSinkTwoGapRaceSupportResolution

namespace LDSinkTwoGapRaceEntranceUniformConsequences

variable {n psi : Nat}

/-- The complete first-unshield, birth, and shot horizon is linear in the
physical pair span.  Both gap lengths remain visible in this bound. -/
theorem ordered_horizon_le_n_span (F : TwoGapFrame n)
    (hab : F.attack.d ≤ F.recovery.d) :
    2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8) ≤
      19 * n * (F.recovery.d + F.attack.d) := by
  have hb := F.attack.hd
  have hs : 2 * (2 * F.recovery.d + 13 * F.attack.d + 8) ≤
      19 * (F.recovery.d + F.attack.d) := by omega
  have hm := Nat.mul_le_mul_left n hs
  simpa only [Nat.mul_assoc, Nat.mul_left_comm] using hm

/-- Absorbing success pads the proved physical count to a simple pair-span
horizon, without restarting the protocol or discarding scheduler symbols. -/
theorem gapPair_uniform_deletion_at_span (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b) (hab : F.attack.d ≤ F.recovery.d) :
    n ^ (19 * n * (F.recovery.d + F.attack.d)) ≤
      (16 * 2 ^ uniformCollapseBudget) * successCount (physicalBlockStep hpsi F) (.active b)
        (19 * n * (F.recovery.d + F.attack.d)) := by
  let T := 2 * n * (2 * F.recovery.d + 13 * F.attack.d + 8)
  let H := 19 * n * (F.recovery.d + F.attack.d)
  let K := 16 * 2 ^ uniformCollapseBudget
  have ht : T ≤ H := ordered_horizon_le_n_span F hab
  have hsum : T + (H - T) = H := by omega
  have hm := gapPair_uniform_deletion_mass hpsi F b hg hab
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

/-- The theorem domain includes an actual shielded shared leader, so the
first-unshield service is not removed by an empty initial-state predicate. -/
theorem shielded_ordered_domain_nonempty :
    ∃ b : AState 5 1, GapPair coldHPsi coldFrame b ∧
      coldFrame.attack.d ≤ coldFrame.recovery.d ∧
        (b.conf (deletePort coldFrame)).shield = true := by
  exact ⟨readyState, ready_gapPair_raceReady.1, by decide, by decide⟩

end LDSinkTwoGapRaceEntranceUniformConsequences

#print axioms LDSinkTwoGapRaceEntranceUniformConsequences.ordered_horizon_le_n_span
#print axioms LDSinkTwoGapRaceEntranceUniformConsequences.gapPair_uniform_deletion_at_span
#print axioms LDSinkTwoGapRaceEntranceUniformConsequences.shielded_ordered_domain_nonempty
