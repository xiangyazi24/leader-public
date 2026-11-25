import Leader.L4.ReportPrelaunchDoorClock
import Leader.L4.ReportPrelaunchDoorProducer

namespace L4.ReportPrelaunchDoorReady
open PhysicalCustody ReportResetRawHooks ShortResetCycle ReportOwnerResetDrain
open ReportPrelaunchK1Geometry

variable {s n : Nat} {h : Fin n → Bool}

/-- Genuine physical per-owner first RESET0 receipt from arbitrary
report work bytes on the frozen, already-cached chart. In particular
this does not assume local source cases or an external first-launch law. -/
theorem receipt_mean
    (d : Sheet) (C : Chart h) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h)
    (Q : Raw s n→Prop) (F : Fibre (h:=h) d Q)
    (x : {x : Raw s n // Cached d hh Q x}) :
    Height.IIDExpectedHittingTimeAtMost
      (ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F))
      ReportOwnerReceiptClock.done (x,none)
      (n*ReportResetEventClock.resetCoefficient (3*G.B) (params d s).digits) := by
  have R := ReportPrelaunchDoorProducer.rootRows d C (Cached d hh Q) N
    (ReportPrelaunchDoorProducer.digits_positive d S)
    (cached_fibre d N hh Q F).mask
  exact ReportPrelaunchDoorClock.receipt_mean_with_gap_cap d C N hh G Q F R x

end L4.ReportPrelaunchDoorReady
