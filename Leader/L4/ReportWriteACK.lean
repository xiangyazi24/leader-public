import Leader.L4.ReportIndexedActualACK
import Leader.L4.ReportStagedWriteInstall
import Leader.L4.ReportAcqExtract

namespace L4.ReportWriteACK
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerIssueControl ReportOwnerReverseControl
open ReportOwnerForwardControl ReportOwnerDoorProjection ReportOwnerForwardLocations
open ReportIndexedActualACK ReportIndexedLaunchData ReportIndexedFlightContract
open ReportIssuedSegment ReportIndexedSourcePrefix ReportOwnerIndexedFlight
open ReportOwnerSerial ReportLeaseOwner ReportWriteHitLedger

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

/-- A real ACK in the indexed source log has its own WRITE installation
witness. No caller supplies a successful flight, an authentic source byte,
a hit ledger or a root-grant premise. The closed cached chart supplies
the actual old offset of that digit. -/
theorem receipt_write_install (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (r : Owner h) (j : Fin (params d s).digits) (J : j.val<(charter G r).b)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d (charter G r) x)
    (w : List (Fin n)) (l : List Receipt)
    (T : AckTape d (charter G r) x w l)
    (q : Receipt) (M : q∈l) (Op : q.1=writeOp (params d s)+j.val) :
    let C := charter G r
    let p := params d s
    ∃ pre fly post : List (Fin n), ∃ f : Tok,
      w=(pre++door C::fly)++door C::post ∧
      let issue := rawRun x pre
      let y := rawNext s issue (door C)
      let old := rawRun y fly
      IssuedSegment d C issue fly (writeOp p+j.val) f ∧
      WriteFlightResult d C issue fly j
        (acqCaptureIndex p (selectBytes d (issue C.root))/2%2) f ∧
      q.2=tok d C old 0 := by
  dsimp only
  let C := charter G r
  let p := params d s
  have Range : IndexedOp p q.1 := by
    rw [Op]
    have K : j.val<p.digits := j.isLt
    change IndexedOp p (writeOp p+j.val)
    unfold IndexedOp cmpOp writeOp sealOp
    omega
  obtain ⟨pre,fly,post,sent,recv,W,Legal,P,Data,A,No,Walk,Ack,D,_⟩ :=
    receipt_actual_walk d C N hh G F digit x X I w l T q M Range
  let issue := rawRun x pre
  let y := rawNext s issue (door C)
  let old := rawRun y fly
  let f := indexedF p q.1 (some sent)
  have Y := (serial_run d C N hh G F digit x X (.inl I) pre).1
  obtain ⟨t,Src,Tag⟩ := ReportWriteSplit.structural_issue_emits_F
    d C N hh F issue Y Legal A.shape
  let v := selectBytes d (issue C.root)
  obtain ⟨a,Seed,_,Token⟩ :=
    indexed_source_canonical p v _ t (params_beta_pos d s)
      (congrArg Prod.fst P) q.1 (congrArg Prod.snd P) Range Src Tag
  have Eq : t=f := by
    rw [Token,Seed,←Data]
  have Pack : IssuedSegment d C issue fly q.1 f := by
    refine ⟨Legal,P,?_,rfl,rfl,rfl,A.packet,No,?_,Ack⟩
    · rw [←Eq]
      exact Src
    · exact (walk_at d C q.1 y _ fly (.backward 0 (some recv)) Walk :
        DState d C q.1 old 0 (some recv)).pc
  rw [Op] at Pack
  exact ⟨pre,fly,post,f,W,Pack,write_flight_result d N hh G F digit
    r issue fly j f Y J Pack,D⟩

#print axioms receipt_write_install
end L4.ReportWriteACK

namespace L4.ReportWriteACK
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerIssueControl ReportOwnerReverseControl
open ReportOwnerForwardControl ReportOwnerDoorProjection ReportOwnerForwardLocations
open ReportIndexedFlightContract ReportIndexedSourcePrefix ReportLeaseOwner ReportGenerationAncestry
open ReportOwnerAcquireReturn ReportOwnerCommandRail ReportAcqExtract

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

theorem no_restart_drop (d : Sheet) (C : Chart h) (x : Raw s n)
    (u v : List (Fin n)) (H : NoRestartTape d C x (u++v)) :
    NoRestartTape d C (rawRun x u) v := by
  induction u generalizing x with
  | nil => exact H
  | cons e u IH => exact IH _ H.2

/-- The old file which issued each real WRITE supplies the installed
digit even at the later end of the same generation. No later step is
allowed to reset the source or substitute a different physical bank. -/
theorem receipt_write_at_current_cut (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (r : Owner h) (j : Fin (params d s).digits) (J : j.val<(charter G r).b)
    (x : Raw s n) (X : Cached d hh Q x)
    (I : LegalIssue d (charter G r) x) (A : StrongSerial d (charter G r) x)
    (PC : PostAcqPC (params d s) (readPC d (charter G r) x))
    (w : List (Fin n)) (NR : NoRestartTape d (charter G r) x w)
    (l : List Receipt) (T : AckTape d (charter G r) x w l)
    (q : Receipt) (M : q∈l) (Op : q.1=writeOp (params d s)+j.val) :
    let C := charter G r
    let p := params d s
    ∃ pre fly post : List (Fin n), ∃ f : Tok,
      w=(pre++door C::fly)++door C::post ∧
      let issue := rawRun x pre
      let prior := acqCaptureIndex p (selectBytes d (issue C.root))/2%2
      IssuedSegment d C issue fly (writeOp p+j.val) f ∧
      WriteFlightResult d C issue fly j prior f ∧
      reportDigitPair p (selectBytes d (rawRun x w (nextAt (centre C) j.val))) (1-prior)=
        BitVec.ofNat (2*ReportByteRows.d p)
          (ancestrySendDigits p (selectBytes d (issue C.root))) := by
  dsimp only
  let C := charter G r
  let p := params d s
  obtain ⟨pre,fly,post,f,W,Seg,Write,_⟩ :=
    receipt_write_install d N hh G F digit r j J x X I w l T q M Op
  let u := pre++door C::fly
  let issue := rawRun x pre
  let old := rawRun (rawNext s issue (door C)) fly
  let after := rawNext s old (door C)
  have UU : rawRun x u=old := by
    unfold u
    rw [ShortOwnerEpochJS.raw_append]
    rfl
  have W' : w=(u++[door C])++post := by
    rw [List.append_assoc]
    exact W
  have U : rawRun x (u++[door C])=after := by
    rw [ShortOwnerEpochJS.raw_snoc,UU]
  have H : NoRestartTape d C x ((u++[door C])++post) := W' ▸ NR
  have Tail := no_restart_drop d C x (u++[door C]) post H
  have Front := no_restart_prefix d C x (u++[door C]) post H
  rw [U] at Tail
  have S := strong_run d C N hh G F digit x X A (u++[door C])
  have Ctl := raw_postacq_run d C hh F N digit x (u++[door C]) X PC Front
  rw [U] at S Ctl
  have OldPC : readPC d C old=(2,writeOp p+j.val) := Seg.2.2.2.2.2.2.2.2.1
  let prior := acqCaptureIndex p (selectBytes d (issue C.root))/2%2
  have Last := staged_credit_to_prefix d N hh G F digit r issue fly post j prior f J
    Write OldPC S.1 S.2.1 Ctl.2.1 Tail
  have V : f.payload%2^(2*ReportByteRows.d p)=
      ancestrySendDigits p (selectBytes d (issue C.root)) := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,V,_,_,_⟩ := Write
    exact V
  refine ⟨pre,fly,post,f,W,Seg,Write,?_⟩
  rw [W',ShortOwnerEpochJS.raw_append,U]
  exact Last.trans (congrArg (BitVec.ofNat (2*ReportByteRows.d p)) V)

#print axioms no_restart_drop
#print axioms receipt_write_at_current_cut
end L4.ReportWriteACK
