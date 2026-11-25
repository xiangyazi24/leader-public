import Leader.L4.ReportItemNineStaging
import Leader.L4.ReportStagedWriteInstall
import Leader.L4.ReportItemNineWriteCredits
import Leader.L4.ReportSnapshotLease

namespace L4.ReportItemNineAdapters
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerIssueControl ReportOwnerDoorProjection
open ReportIndexedSourcePrefix ReportLeaseOwner ReportGoodEightCut
open ReportOwnerAcquireReturn ReportOwnerCommandRail ReportIndexedFlightContract
open ReportItemNineStaging ReportItemNineTrace ReportItemNineWriteCredits

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

/-- The named ITEM9H1 frame is an exact instance of WRITEHIT1. -/
theorem item_nine_staged_frame (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q) :
    ItemNineStagedFrame d hh Q G := staged_prefix_frame d N hh G F

/-- Every concrete write entry consumed by the paper recurrence is
the physical installation attributed to that actual receipt. -/
theorem item_nine_write_credits (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (r : Owner h)
    (Room : (params d s).digits≤(charter G r).b)
    (b : Raw s n) (X : Cached d hh Q b) (I : LegalIssue d (charter G r) b)
    (PC : PostAcqPC (params d s) (readPC d (charter G r) b))
    (w : List (Fin n)) (NR : NoRestartTape d (charter G r) b w)
    (l : List Receipt) (T : AckTape d (charter G r) b w l) :
    WriteCredits d (charter G r) b w l (snapshotInputs d (charter G r) b).prior :=
  write_credits_from_tape d N hh G F digit r Room b X I PC w NR l T

end L4.ReportItemNineAdapters

namespace L4.ReportItemNineAdapters
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerIssueControl ReportOwnerDoorProjection
open ReportIndexedSourcePrefix ReportLeaseOwner ReportGoodEightCut ReportGoodEightBank
open ReportOwnerAcquireReturn ReportOwnerCommandRail ReportIndexedFlightContract
open ReportItemNineStaging ReportItemNineTrace ReportItemNineWriteCredits
open ReportSnapshotLease ReportLeaseGrants ReportPrelaunchAllOwners
open ReportOwnerAcquireProvenance (BeforeConsume)

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

theorem snapshots_for_charter (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (Rail : RailSupplier d hh Q G)
    (r : Owner h) (issue : Raw s n) (X : Cached d hh Q issue)
    (w v : List (Fin n)) (l : List Receipt) :
    let C := charter G r
    let p := params d s
    let acq := rawNext s issue (door C)
    let old := rawRun acq w
    let b := rawNext s old (door C)
    p.digits≤C.a → p.digits≤C.L-(C.a+C.b) →
    LegalIssue d C issue → readPC d C issue=(1,acqOp p) →
    (∀ i,h i=true→Compatible (rawGrant d issue i)) →
    BeforeConsume d C acq w → (tok d C old 0).tag=3 → (tok d C old 0).outcome≠1 →
    FirstCut d hh Q G b → LegalIssue d C b → NoRestartTape d C b v →
    AckTape d C b v l → SnapshotReceipts d C b l := by
  let a := Classical.choose (G.gaps r.val r.property)
  have A := Classical.choose_spec (G.gaps r.val r.property)
  let b := Classical.choose (G.gaps (nextAt r.val a) A.2.2.atEnd)
  have B := Classical.choose_spec (G.gaps (nextAt r.val a) A.2.2.atEnd)
  let c := Classical.choose (G.gaps (nextAt (nextAt r.val a) b) B.2.2.atEnd)
  have C := Classical.choose_spec (G.gaps (nextAt (nextAt r.val a) b) B.2.2.atEnd)
  have Room : a+b+c<n := by
    have P : a≤G.B := A.2.1
    have Q : b≤G.B := B.2.1
    have S : c≤G.B := C.2.1
    have := G.room
    omega
  let ch := chart_of_three r.property A.2.2 B.2.2 C.2.2 Room
  have Ct : charter G r=ch := rfl
  dsimp only
  rw [Ct]
  intro HA HC
  have Ca : ch.a=a := rfl
  have Cb : ch.b=b := rfl
  have CL : ch.L=a+b+c := rfl
  have H : (params d s).digits≤c := by rw [Ca,Cb,CL] at HC; omega
  exact snapshot_receipts_of_acq d N hh G F digit Rail r.property A.2.2
    B.2.2 C.2.2 Room HA H issue X w v l

end L4.ReportItemNineAdapters
