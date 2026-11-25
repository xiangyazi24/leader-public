import Leader.L4.ReportIndexedActualACK
import Leader.L4.ReportIndexedReadLedger

namespace L4.ReportReaderACK
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerIssueControl ReportOwnerReverseControl
open ReportOwnerForwardControl ReportOwnerDoorProjection ReportOwnerForwardLocations
open ReportIndexedReadLedger ReportIndexedActualACK ReportIndexedLaunchData
open ReportIssuedSegment ReportIndexedSourcePrefix ReportOwnerIndexedFlight
open ReportOwnerSerial

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

/-- Both halves attributed to the actual source's captured left/right
bank selectors, on the very tape that contributed this ordered credit. -/
theorem receipt_read_samples (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    {r0 : Fin n} {a b c : Nat} (Root : h r0=true)
    (GA : Gap h r0 a) (GB : Gap h (nextAt r0 a) b)
    (GC : Gap h (nextAt (nextAt r0 a) b) c) (Room : a+b+c<n)
    (HA : (params d s).digits≤a) (HC : (params d s).digits≤c)
    (x : Raw s n) (X : Cached d hh Q x)
    (I : LegalIssue d (chart_of_three Root GA GB GC Room) x)
    (w : List (Fin n)) (l : List Receipt)
    (T : AckTape d (chart_of_three Root GA GB GC Room) x w l)
    (r : Receipt) (M : r∈l) (Range : IndexedOp (params d s) r.1)
    (O : r.1<writeOp (params d s)) (j : Nat)
    (D : indexedReadOffset (params d s) r.1=j) (K : j<(params d s).digits) :
    let C := chart_of_three Root GA GB GC Room
    let p := params d s
    ∃ pre fly post : List (Fin n), ∃ hi lo : Nat,
      w=(pre++door C::fly)++door C::post ∧
      let issue := rawRun x pre
      let y := rawNext s issue (door C)
      let cap := acqCaptureIndex p (selectBytes d (issue C.root))
      Sample d C r.1 y fly j 0 (cap/4) hi ∧
      Sample d C r.1 y fly (a+b+j) 2 (cap%2) lo ∧
      CreditAt d C (rawRun y fly) (door C) ∧ r.2.payload=hi*2^ReportByteRows.d p+lo := by
  dsimp only
  let C := chart_of_three Root GA GB GC Room
  let p := params d s
  obtain ⟨pre,fly,post,sent,recv,W,_,_,Data,_,_,Walk,Ack,Receipt,_⟩ :=
    receipt_actual_walk d C N hh G F digit x X I w l T r M Range
  let z := rawRun x pre
  let y := rawNext s z (door C)
  have X0 := (serial_run d C N hh G F digit x X (.inl I) pre).1
  have Y := (cached_fibre d N hh Q F).closed z (door C) X0
  obtain ⟨L,R,Hits⟩ := reader_geometry d hh F N y Y Root GA GB GC Room r.1 j D K HA HC
  obtain ⟨_,Left,Right⟩ := reader_walk_result d C r.1 y sent recv j (a+b+j) fly O Hits L R Walk
  let cap := acqCaptureIndex p (selectBytes d (z C.root))
  have A : cap<8 := ((selectBytes d (z C.root)).extractLsb' (sourceBase p+(16+2*ReportByteRows.d p)) 3).isLt
  have S : sent.banks=2*(cap/4)+cap%2 := by
    rw [Data]
    rw [concreteSeed,if_pos O]
    rfl
  have B0 : sent.banks/2=cap/4 := by omega
  have B1 : sent.banks%2=cap%2 := by omega
  have End : DState d C r.1 (rawRun y fly) 0 (some recv) := walk_at d C r.1 y _ fly _ Walk
  refine ⟨pre,fly,post,recv.hi,recv.lo,W,B0 ▸ Left,B1 ▸ Right,Ack,?_⟩
  rw [Receipt]
  exact reply_payload d C r.1 _ recv End O

end L4.ReportReaderACK
