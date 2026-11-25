import Leader.L4.WidthPaidOwnerClock
import Leader.L4.WidthBeginMean

namespace L4.WidthProductionEntrance

open AllSizeProtocol PhysicalCustody ShortResetChart WidthSectorGeometry
open WidthFreshForward WidthCycleEpoch

variable {s n d : Nat}

/-- Both predicates name the same generated BEGIN receipt on the same suffix.
    Reordering witnesses does not change the sampled marks or the budget. -/
theorem beginReceipt_iff (P : WidthLower s n) (S : Sector P.h d)
    (z y : Tape s n) : BeginReceipt P S z y ↔ WidthBeginMean.FirstBeginAt P S z y := by
  constructor
  · rintro ⟨a,w,op,k,p,O,T,M,Y⟩
    exact ⟨a,w,op,k,p,M,Y,O,T⟩
  · rintro ⟨a,w,op,k,p,M,Y,O,T⟩
    exact ⟨a,w,op,k,p,O,T,M,Y⟩

theorem actual_predecessor (P : WidthLower s n) (S : Sector P.h d) :
    Predecessor P S := by
  constructor
  intro z X t
  have H := WidthBeginMean.first_begin_expected P S z X t
  exact Nat.le_trans (RankRenewal.cost_mono_target (next:=tapeStep)
    (WidthBeginMean.FirstBeginAt P S z) (BeginReceipt P S z)
    (fun y => (beginReceipt_iff P S z y).mpr) t z) H

theorem owner_cycle_mean (P : WidthLower s n) (S : Sector P.h d) (hs : 6≤s)
    (z : Tape s n) (X : P.Post z.raw) :
    L4.IIDExpectedHittingTimeAtMost tapeStep (CycleReceipt P S z)
      z (20*n*(d+2)^2) :=
  WidthCycleEpoch.owner_cycle_mean P S (actual_predecessor P S) hs z X

theorem paid_max_mean (P : WidthLower s n) (F : OwnerFamily P)
    (hs : 6≤s) (advice : s=ell (ell n)) (N : 1<n)
    (x : Raw s n) (X : P.Post x) :
    L4.IIDExpectedHittingTimeAtMost tapeStep (PaidDone P F x)
      (tapeStart x) (5120*n^2) :=
  WidthCycleEpoch.paid_max_mean P F (fun q=>actual_predecessor P (F.sector q))
    hs advice N x X

/-- All five WIDTH producers, on the generated raw process. The only input
    is the permanent lower cut with certified H6 spacing. The WIDTH cache,
    BEGIN, genuine cycle, absorbing display, and all-owner paid clock are
    proved, not fields of the lower-cut structure. -/
theorem packed_from_certified_h6 (P : WidthLower s n) (hs : 6≤s)
    (advice : s=ell (ell n)) (N : 1<n) (x : Raw s n) (X : P.Q x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s)
      (fun z=>Nonempty (PackedFiber z)) x ((s+5132)*n^2) :=
  width_packed_of_predecessors P (fun _ S=>actual_predecessor P S)
    hs advice N x X

#print axioms beginReceipt_iff
#print axioms actual_predecessor
#print axioms owner_cycle_mean
#print axioms paid_max_mean
#print axioms packed_from_certified_h6

end L4.WidthProductionEntrance
