import Leader.L4.ReportPrelaunchDoorLift
import Leader.L4.ReportOwnerPrelaunchAdapter

namespace L4.ReportPrelaunchDoorClock
open PhysicalCustody ReportResetRawHooks ReportResetBarrier ShortResetCycle ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchDoorLift

variable {s n : Nat} {h : Fin n → Bool}

/-- Three actual consecutive gaps determine the chart length; this
    charges the frozen owner geometry rather than the whole raw ring. -/
theorem chart_cap_of_gaps (C : Chart h) (G : GapInput h) :
    C.L≤3*G.B := by
  obtain ⟨a,_,A,F⟩ := G.gaps C.root C.rootHeader
  obtain ⟨b,_,B,K⟩ := G.gaps (ShortResetChart.nextAt C.root a) F.atEnd
  obtain ⟨c,_,D,J⟩ := G.gaps (ShortResetChart.nextAt (ShortResetChart.nextAt C.root a) b) K.atEnd
  have room : a+b+c<n := by have := G.room; omega
  let T := ShortLayerGeometry.chart_of_three C.rootHeader F K J room
  have L : C.L=a+b+c := (ShortReadCaptureGeometry.chart_unique C T rfl).1
  omega

/-- The actual fixed-chart clock now needs only the local source
    outcomes at K0, not a chart-wide or stopping-time hypothesis. -/
theorem receipt_mean_of_root_rows
    (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h)
    (Q : Raw s n→Prop) (F : Fibre (h:=h) d Q)
    (R : RootRows d C (Cached d hh Q))
    (B : Nat) (L : C.L≤B)
    (x : {x : Raw s n // Cached d hh Q x}) :
    Height.IIDExpectedHittingTimeAtMost
      (ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F))
      ReportOwnerReceiptClock.done (x,none)
      (n*ReportResetEventClock.resetCoefficient B (params d s).digits) := by
  have D := doorCases d C hh G F N R
  have S := ReportPrelaunchK1.rowCases d C hh G Q F N D
  exact ReportOwnerPrelaunchAdapter.owner_receipt_mean_of_row_cases
    d C (cached_fibre d N hh Q F) N x B L S

theorem receipt_mean_with_gap_cap
    (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h)
    (Q : Raw s n→Prop) (F : Fibre (h:=h) d Q)
    (R : RootRows d C (Cached d hh Q))
    (x : {x : Raw s n // Cached d hh Q x}) :
    Height.IIDExpectedHittingTimeAtMost
      (ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F))
      ReportOwnerReceiptClock.done (x,none)
      (n*ReportResetEventClock.resetCoefficient (3*G.B) (params d s).digits) :=
  receipt_mean_of_root_rows d C N hh G Q F R _ (chart_cap_of_gaps C G) x

end L4.ReportPrelaunchDoorClock
