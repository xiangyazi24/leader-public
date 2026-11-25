import Leader.L4.ReportWriteSplit
import Leader.L4.ReportWriteBankClosure

namespace L4.ReportWriteRailSupplier
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchClock ReportOwnerProvenanceTransport
open ReportOwnerIssueControl ReportOwnerForwardControl ReportOwnerReverseControl
open ReportByteRows ReportRawProjection ReportOwnerCommandRail
open ReportGoodEightCut ReportWriteOrigin ReportWriteSplit ReportAcqExtract
open ReportGoodEightBank ReportWriteBankClosure ReportLeaseOwner
variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

theorem rail_supplier (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) : RailSupplier d hh Q G := by
  intro r x reset w X R k K Live
  let C := charter G r
  obtain ⟨pre,fly,t,W,_,I,_,Lo,Hi,Emit,Tag,_,Turn⟩ :=
    healthy_write_split_from_receipt d C N hh G F digit x X reset w R k K Live
  have L := Live.2.1
  change (tok d C (rawRun (rawRun x reset) w) k).fault=false at L
  rw [W] at L ⊢
  exact write_origin_from_issue_cut d hh G F N r x X reset R digit
    pre fly k t I I.2.1 Lo Hi Emit Tag Turn L

theorem bank_expected_from_cached (d : Sheet) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : {x : Raw s n // Cached d hh Q x}) :
    IIDExpectedHittingTimeAtMost (rawNext s) (GoodEightBank d hh Q G) x.val
      (2*ReportResetEventClock.resetCoefficient (3*G.B) (params d s).digits*n^2) :=
  bank_expected d N S hh G F
    (rail_supplier d N hh G F (ReportPrelaunchDoorProducer.digits_positive d S)) x

end L4.ReportWriteRailSupplier
