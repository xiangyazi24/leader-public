import Leader.Wu.Elimination.MultiLeaderCleanupSegmentDescent
import Leader.Wu.Elimination.MultiLeaderCleanupRepairTail

/-!
# Strict count descent for the corrected full cleanup word

The raw/full bridge proves strict descent after the leader-kill word.  The
repair-tail theorem separately proves that the corrected merged-follower sweep
frames every leader bit.  This module composes those results so downstream
round producers can use the literal `fullWord` directly.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PhysicalBridge

open PPLL PPLLResearchFormulation
  PPLLExpiringComparisonRepair
  PPLLWallSweepFiniteCleanup
  PPLLWallSweepClockwiseScheduler
  PPLLNoCheckBirthConditionTwoGeometry

variable {psi n kappa tau : Nat}

/-- Pointwise equality of erased leader bits gives equality of raw physical
leader counts on finite expiring configurations. -/
theorem rawPhysicalLeaderCount_erase_eq_of_leader_frame
    (C D : EConfig n psi kappa tau)
    (hleader : ∀ i,
      (D i).core.erase.core.leader =
        (C i).core.erase.core.leader) :
    rawPhysicalLeaderCount (eraseExpiringCleanupConfig D) =
      rawPhysicalLeaderCount (eraseExpiringCleanupConfig C) := by
  have hmass :
      (fun i : Fin n =>
        rawLeaderMass ((eraseExpiringCleanupConfig D) i)) =
      (fun i : Fin n =>
        rawLeaderMass ((eraseExpiringCleanupConfig C) i)) := by
    funext i
    unfold rawLeaderMass eraseExpiringCleanupConfig
    rw [hleader i]
  unfold rawPhysicalLeaderCount
  rw [hmass]

/-- Under the exact prefix-readiness and post-kill sweep facts, the literal
corrected `fullWord` strictly lowers the physical leader count of the complete
expiring transition.  The repair tail contributes no additional deletion: its
global leader frame transports the kill-word inequality unchanged. -/
theorem SegmentCleanupReady.physicalFullOutput_count_lt_of_readyAlong
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (plan : SegmentCleanupPlan ring)
    (C : EConfig n psi kappa tau)
    (hready : SegmentCleanupReady
      hpsi ring plan (eraseExpiringCleanupConfig C))
    (halong : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C plan.word)
    (hnoActive : NoActiveDeletion
      (plan.physicalWordOutput hpsi kappa tau C))
    (hsourceFollower :
      ((plan.physicalWordOutput hpsi kappa tau C)
        plan.predIncoming).core.erase.core.leader = false)
    (hsourceReset :
      ((plan.physicalWordOutput hpsi kappa tau C)
        plan.predIncoming).core.erase.core.reset_cmd = true)
    (hsourceEcho :
      ((plan.physicalWordOutput hpsi kappa tau C)
        plan.predIncoming).core.erase.core.echo = false)
    (hfollowers : ∀ k, 0 < k → k ≤ plan.dVS →
      ((plan.physicalWordOutput hpsi kappa tau C)
        (cwPos ring plan.predIncoming k)).core.erase.core.leader = false)
    (hecho : ∀ k, 0 < k → k ≤ plan.dVS →
      ((plan.physicalWordOutput hpsi kappa tau C)
        (cwPos ring plan.predIncoming k)).core.erase.core.echo = false) :
    rawPhysicalLeaderCount
        (eraseExpiringCleanupConfig
          (plan.physicalFullOutput hpsi kappa tau C)) <
      rawPhysicalLeaderCount (eraseExpiringCleanupConfig C) := by
  let B := plan.physicalWordOutput hpsi kappa tau C
  let D := plan.physicalFullOutput hpsi kappa tau C
  have hword :=
    PPLLCompleteMultiLeaderCleanup.PhysicalBridge.SegmentCleanupReady.expiringPhysicalLeaderCount_lt_of_readyAlong
      hpsi kappa tau ring plan C hready halong
  change rawPhysicalLeaderCount (eraseExpiringCleanupConfig B) <
      rawPhysicalLeaderCount (eraseExpiringCleanupConfig C) at hword
  have hsweep := plan.physicalFullOutput_repairTail_of_post_word
    hpsi kappa tau ring hn C hnoActive hsourceFollower
      hsourceReset hsourceEcho hfollowers hecho
  change NoActiveDeletion D ∧
      (∀ i, (D i).core.erase.core.leader =
        (B i).core.erase.core.leader) ∧ _ at hsweep
  have hcountFrame :=
    rawPhysicalLeaderCount_erase_eq_of_leader_frame B D hsweep.2.1
  change rawPhysicalLeaderCount (eraseExpiringCleanupConfig D) <
    rawPhysicalLeaderCount (eraseExpiringCleanupConfig C)
  rw [hcountFrame]
  exact hword

end PhysicalBridge
end PPLLCompleteMultiLeaderCleanup
