import Leader.L4.WidthProductionEntrance
import Leader.L4.PhysicalCacheSweep
namespace L4.WidthPackTiming
open PhysicalCustody WidthPackJoint WidthCacheAllSites WidthPackedBridge
open BStarH6WordChart MonitorRawBridge

variable {s n : Nat}

theorem width_packed_stage_quadratic (hs : 6 ≤ s) (N : 1 < n)
    (P6 : Raw s n → Prop) (h : Fin n → Bool) (hh : ∃ i, h i = true)
    (lower_closed : ∀ y e, P6 y → P6 (rawNext s y e))
    (mask : ∀ y, P6 y → ∀ i, oldH6 (rows s) y i = h i)
    (spacing : ∀ y, P6 y → CertifiedSpacing y)
    (OwnerGood : Header h → Raw s n → Prop)
    (owner_closed : ∀ q y e, OwnerGood q y → OwnerGood q (rawNext s y e))
    (owner_flags : ∀ q y, OwnerGood q y → OwnerWordFlagsCorrect h hh q y)
    (postcache : ∀ y, WidthCorrect h hh P6 y → Nonempty (PaidOwnerMonitor h OwnerGood y))
    (x : Raw s n) (X : P6 x) :
    IIDExpectedHittingTimeAtMost (rawNext s) (fun z => Nonempty (PackedFiber z))
      x (5122*n^2) := by
  obtain ⟨cache_closed, cache_mean⟩ := PhysicalCacheSweep.width_raw_quadratic N h hh P6 lower_closed mask x X
  have start := cache_mean
  rw [show 5122*n^2 = 2*n^2 + 5120*n^2 by
    rw [← Nat.add_mul]]
  refine AllSizeComposition.additive_stage _ _ _ _ _ x start ?_
  intro y Y
  obtain ⟨m⟩ := postcache y Y
  have A : P6 y := Y.1
  have T := expected_of_monitor_words (rawNext s) m.step m.project m.done
    (fun z => Nonempty (PackedFiber z)) m.step_project m.start
    (fun w D => by
      rw [m.base]
      exact packed_of_width_joint hs N P6 h hh lower_closed mask spacing OwnerGood
        owner_closed owner_flags _
        (qwidth_of_prefix_receipts P6 h hh lower_closed cache_closed OwnerGood
          owner_closed y A Y m.Receipt m.credit w (m.terminal w D))) _ m.price
  simpa only [m.base] using T

end L4.WidthPackTiming
namespace L4.WidthProductionEntrance
open AllSizeProtocol PhysicalCustody ShortResetChart WidthSectorGeometry
open WidthFreshForward WidthCycleEpoch
variable {s n : Nat}
theorem packed_from_certified_h6_quadratic (P : WidthLower s n) (hs : 6≤s)
    (advice : s=ell (ell n)) (N : 1<n) (x : Raw s n) (X : P.Q x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s)
      (fun z=>Nonempty (PackedFiber z)) x (5122*n^2) := by
  let F := family_of_lower P hs advice x X
  exact WidthPackTiming.width_packed_stage_quadratic hs N
    P.Q P.h P.hh P.closed P.frozen P.spacing (OwnerGood P F)
    (owner_good_closed P F) (owner_good_flags P F hs)
    (fun y Y=>⟨paidOwnerMonitor P F (fun q=>actual_predecessor P (F.sector q))
      hs advice N y Y⟩) x X

end L4.WidthProductionEntrance
