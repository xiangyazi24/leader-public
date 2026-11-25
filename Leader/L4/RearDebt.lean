import Leader.L4.RearMovement
import Leader.L4.RearGhostBudget
import Leader.L4.RearFilledLink
import Leader.L4.RearEntrance

/-!
# Literal rear-root debt and L4 entrance
This module closes the concrete debt premise with the occupied-landing,
ghost-phase inventory and refill matching on the same observer and tape.
-/

namespace L4.RearTrace
open TaggedTrace

theorem concreteRearDebt_literal : ConcreteRearDebt := by
  intro p c n x i w h
  obtain ⟨hp,hcal,hn,hnd,hm,hcov,ha⟩ := h
  have htrace : LiveCoveredTrace x i w := ⟨hp,hcal,hn,hnd,hm,hcov,ha⟩
  have hMove := literal_ghostMovement_bound x i w htrace
  have hFill := globalFilled_bound_of_live htrace
  have hRefill := concrete_refill_bound_global hn i (rearInit x i) w hm
  change 2*ghostAdvances i (rearInit x i) w ≤ (rearTrack x i w).rearHits +
    globalFilled i (rearInit x i) w + 1 at hRefill
  rw [rearTrack_tag] at hMove
  rw [hits_eq_moves_on_survival _ _ rfl ha]
  omega

end L4.RearTrace

namespace L4
open TaggedTrace

theorem rear_allTags_mean_literal {p c n : Nat} (x : Config p c n)
    (hp : 2 ≤ p) (hcal : 12 ≤ c) (hn : 4 ≤ n) (hnd : (∃ j : Fin n, (x j).mark = true))
    (hm : MCOV x) (hc : COV x) :
    IIDExpectedHittingTimeAtMost allAdvance allEnded (allInit x) (48*n^2) :=
  concreteAllTags_mean_of_rearDebt RearTrace.concreteRearDebt_literal x hp hcal hn hnd hm hc

/-- Ordered cover, extinction on the common clock, and concrete
fresh peacefulness, without a debt or post-cover bridge premise. -/
theorem rooted_rear_entrance_literal {p c n : Nat} (x : Config p c n)
    (hp : 2 ≤ p) (hcal : 12 ≤ c) (hn : 4 ≤ n) (hnd : RootedEntrance.RootNonempty x) :
    IIDExpectedHittingTimeAtMost step QuietEntrance x (49*n^2) :=
  entrance_mean_of_rearDebt RearTrace.concreteRearDebt_literal x hp hcal hn hnd

theorem rear_entrance_literal {p c n : Nat} (x : Config p c n)
    (hp : 2≤p) (hcal : 12≤c) (hn : 4≤n) (hnd : ¬p∣n) :
    IIDExpectedHittingTimeAtMost step QuietEntrance x (49*n^2) :=
  rooted_rear_entrance_literal x hp hcal hn (RootedEntrance.rooted_of_not_dvd (by omega) x hnd)

theorem rooted_rear_entrance_printed {p c n : Nat} (x : Config p c n)
    (hp : 2≤p) (hcal : 12≤c) (hn : 4≤n) (hr : RootedEntrance.RootNonempty x) :
    IIDExpectedHittingTimeAtMost step QuietEntrance x (2049*n^2) := by
  intro t
  exact Nat.le_trans (rooted_rear_entrance_literal x hp hcal hn hr t)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 49≤2049)))

theorem rear_entrance_printed {p c n : Nat} (x : Config p c n)
    (hp : 2 ≤ p) (hcal : 12 ≤ c) (hn : 4 ≤ n) (hnd : ¬ p ∣ n) :
    IIDExpectedHittingTimeAtMost step QuietEntrance x (2049*n^2) := by
  intro t
  exact Nat.le_trans (rear_entrance_literal x hp hcal hn hnd t)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 49 ≤ 2049)))

end L4

#print axioms L4.RearTrace.concreteRearDebt_literal
#print axioms L4.rear_allTags_mean_literal
#print axioms L4.rear_entrance_literal
#print axioms L4.rear_entrance_printed
