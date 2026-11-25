import Leader.L4.ReportAbsoluteBudget
import Leader.L4.ReportStageQuadratic

namespace L4.ReportStageEnvelope
open AllSizeProtocol PhysicalCustody ShortMIS3Entrance ReportStageMeans ReportStageQuadratic
open ReportAbsoluteBudget AdviceBandRadiusBudget
variable {n s : Nat}

theorem both_from_h4 (advice : s=ell (ell n)) (S : 6≤s) (N : 189<n)
    (x : Raw s n) (A : PermanentH4 N x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (DeployedSecond advice S N) x
      (((trialCeiling (U2 6) n0)+(prepBudget+prepBudget))*n^2) :=
  @both_from_h4_given n s advice S N x A (trialCeiling (U2 6) n0)
    (@flat_report_service n s S advice)

#print axioms both_from_h4
end L4.ReportStageEnvelope
