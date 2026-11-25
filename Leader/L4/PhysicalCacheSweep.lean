import Leader.L4.ReportCacheSweep
import Leader.L4.WidthCacheAllSites
import Leader.L4.MonitorRawBridge

namespace L4.PhysicalCacheSweep
open AllSizeProtocol PhysicalCustody BStarH6Ordinal BStarH6WordChart
open WidthCacheAllSites ReportCacheAllSites ReportCacheSweep ReportCacheWindow

variable {s n : Nat}

/-- Applies to arbitrary Width bytes at the frozen H6 cut; no advice bound
is used to pay for the cache. -/
theorem width_raw_quadratic (N : 1<n) (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (Q : Raw s n → Prop) (closed : ∀ x e,Q x→Q (rawNext s x e))
    (mask : ∀ x,Q x→∀ i,oldH6 (rows s) x i=h i)
    (x : Raw s n) (A : Q x) :
    (∀ y e, WidthCorrect h hh Q y → WidthCorrect h hh Q (rawNext s y e)) ∧
    IIDExpectedHittingTimeAtMost (rawNext s) (WidthCorrect h hh Q) x (2*n^2) := by
  have F := width_frame (rows s) h Q (ShortResetCycle.edge_sep N) closed mask
  exact ⟨all_closed hh F,(MonitorRawBridge.height_iff_row _ _ _ _).mp
    (all_expected_quadratic hh F x A)⟩

/-- Applies to arbitrary Report2 bytes at a frozen H5 cut; the digits
and report span do not appear in the cache price. -/
theorem report2_raw_quadratic (N : 1<n) (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (Q : Raw s n → Prop) (closed : ∀ x e,Q x→Q (rawNext s x e))
    (mask : ∀ x,Q x→∀ i,(oldHeaders (rows s) (x i)).h5=h i)
    (x : Raw s n) (A : Q x) :
    (∀ y e, Report2Correct h hh Q y → Report2Correct h hh Q (rawNext s y e)) ∧
    IIDExpectedHittingTimeAtMost (rawNext s) (Report2Correct h hh Q) x (2*n^2) := by
  have F := report2_frame (rows s) h Q (ShortResetCycle.edge_sep N) closed mask
  exact ⟨all_closed hh F,(MonitorRawBridge.height_iff_row _ _ _ _).mp
    (all_expected_quadratic hh F x A)⟩

#print axioms width_raw_quadratic
#print axioms report2_raw_quadratic
end L4.PhysicalCacheSweep
