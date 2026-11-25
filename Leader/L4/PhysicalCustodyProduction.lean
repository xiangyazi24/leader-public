import Leader.L4.PhysicalCustodyAssembly
import Leader.L4.ReportStageEnvelope

namespace L4.PhysicalCustodyProduction
open AllSizeProtocol PhysicalCustody PhysicalCustodyAssembly
open AdviceBandRadiusBudget ReportStageQuadratic

noncomputable def K_custody : Nat :=
  PhysicalCustodyAssembly.K_custody ((trialCeiling (U2 6) n0)+(prepBudget+prepBudget))

/-- Absolute production custody from any raw start on the original tape. -/
theorem custody_reached {s n : Nat} (advice : s=ell (ell n)) (S : 6≤s) (x : Raw s n) :
    IIDExpectedHittingTimeAtMost (rawNext s) Custody x
      (PhysicalCustodyAssembly.K_custody ((trialCeiling (U2 6) n0)+(prepBudget+prepBudget))*n^2) :=
  @custody_reached_of_quadratic_reports s n advice S ((trialCeiling (U2 6) n0)+(prepBudget+prepBudget))
    (@ReportStageEnvelope.both_from_h4 n s advice S) x

end L4.PhysicalCustodyProduction
