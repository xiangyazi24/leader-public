import Leader.L4.ReportWriteACK

namespace L4.ReportItemNineWriteCredits
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerIssueControl ReportOwnerDoorProjection
open ReportIndexedFlightContract ReportIndexedSourcePrefix ReportLeaseOwner ReportGenerationAncestry
open ReportOwnerAcquireReturn ReportOwnerCommandRail ReportAcqExtract ReportWriteACK

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

/-- Exact item-9 per-credit projection, from the live WRITE flight and
the source capture on the actual post-ACQ tape. -/
theorem write_credits_from_tape (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (r : Owner h)
    (Room : (params d s).digits≤(charter G r).b)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d (charter G r) x)
    (PC : PostAcqPC (params d s) (readPC d (charter G r) x))
    (w : List (Fin n)) (NR : NoRestartTape d (charter G r) x w)
    (l : List Receipt) (T : AckTape d (charter G r) x w l) :
    let C := charter G r
    let p := params d s
    let prior := ownerCaptureIndex d C x/2%2
    ∀ q∈l,∀ j : Fin p.digits,q.1=writeOp p+j.val →
      ∃ pre flight tail : List (Fin n),∃ f : Tok,
        w=pre++(door C::(flight++(door C::tail))) ∧
        let issue := rawRun x pre
        let old := rawRun (rawNext s issue (door C)) flight
        let after := rawNext s old (door C)
        readPC d C issue=(1,writeOp p+j.val) ∧
        readPC d C old=(2,writeOp p+j.val) ∧
        q.2=tok d C old 0 ∧ CreditAt d C old (door C) ∧
        ancestryWriteTarget p f=1-prior ∧
        f.payload%2^(2*ReportByteRows.d p)=ancestrySendDigits p (selectBytes d (issue C.root)) ∧
        reportDigitPair p (selectBytes d (after (nextAt (centre C) j.val))) (1-prior)=
          BitVec.ofNat (2*ReportByteRows.d p) (f.payload%2^(2*ReportByteRows.d p)) := by
  dsimp only
  let C := charter G r
  let p := params d s
  intro q M j Op
  obtain ⟨pre,fly,post,f,W,Seg,Hit,Q⟩ :=
    receipt_write_install d N hh G F digit r j (Nat.lt_of_lt_of_le j.isLt Room)
      x X I w l T q M Op
  have Split : w=pre++(door C::(fly++(door C::post))) := by
    rw [W,List.append_assoc]
    rfl
  have Pre := no_restart_prefix d C x pre (door C::(fly++(door C::post))) (Split ▸ NR)
  have Capture : ownerCaptureIndex d C (rawRun x pre)=ownerCaptureIndex d C x :=
    (raw_postacq_run d C hh F N digit x pre X PC Pre).2.2
  change acqCaptureIndex p (selectBytes d (rawRun x pre C.root))=
    ownerCaptureIndex d C x at Capture
  rw [Capture] at Hit
  obtain ⟨_,_,k,_,_,Site,_,_,_,_,_,_,Target,Send,_,AtAck,Cred⟩ := Hit
  rw [Site] at AtAck
  exact ⟨pre,fly,post,f,Split,Seg.2.1,Seg.2.2.2.2.2.2.2.2.1,Q,Cred,Target,Send,AtAck⟩

end L4.ReportItemNineWriteCredits
