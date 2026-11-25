import Leader.L4.ReportWriteACK
import Leader.L4.ReportSealDescriptor

namespace L4.ReportSealStagedBank
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportOwnerIssueControl ReportOwnerDoorProjection ReportPrelaunchClock
open ReportOwnerAcquireReturn ReportOwnerCommandRail ReportPrelaunchRank ReportAcqExtract
open ReportIndexedFlightContract ReportIndexedSourcePrefix ReportLeaseOwner
open ReportGenerationAncestry ReportWriteACK ReportSealDescriptor

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

theorem logical_injective (m a b : Nat) (E : logical m a=logical m b) : a=b := by
  unfold logical at E
  repeat' first | omega | split at E

theorem write_ordinal (p : Params) (j : Fin p.digits) :
    logical p.digits (writeOp p+j.val)=cmpOp p+(p.digits+1+2*j.val) := by
  have J := j.isLt
  unfold logical writeOp cmpOp
  rw [if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  omega

/-- No missing offset at SEAL: the exact ordered receipt log contains
the actual WRITE opcode for every digit, not just the right length. -/
theorem seal_has_write_receipt (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (l : List Receipt) (T : AckTape d C x w l)
    (Start : (readPC d C x).2=cmpOp (params d s))
    (End : (readPC d C (rawRun x w)).2=sealOp (params d s))
    (j : Fin (params d s).digits) :
    ∃ q∈l, q.1=writeOp (params d s)+j.val := by
  let p := params d s
  obtain ⟨Count,Ord,_⟩ := at_seal_descriptor d C x w l Start End T
  change l.length=3*p.digits at Count
  have B : p.digits+1+2*j.val<l.length := by rw [Count]; have J : j.val<p.digits := j.isLt; omega
  obtain ⟨q,M,Eq⟩ := ordered_complete p (cmpOp p) l Ord (p.digits+1+2*j.val) B
  exact ⟨q,M,logical_injective p.digits _ _ (Eq.trans (write_ordinal p j).symm)⟩

/-- At any actual SEAL cut all entries of the descriptor's bank
are the entries from the same nonrestart ordered WRITE receipts.
No equality with a future report value is claimed. -/
theorem seal_staged_entries (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (r : Owner h)
    (Width : (params d s).digits≤(charter G r).b)
    (x : Raw s n) (X : Cached d hh Q x)
    (I : LegalIssue d (charter G r) x) (A : StrongSerial d (charter G r) x)
    (Start : (readPC d (charter G r) x).2=cmpOp (params d s))
    (w : List (Fin n)) (NR : NoRestartTape d (charter G r) x w)
    (l : List Receipt) (T : AckTape d (charter G r) x w l)
    (End : (readPC d (charter G r) (rawRun x w)).2=sealOp (params d s)) :
    let C := charter G r
    let p := params d s
    let y := rawRun x w
    let desc := descriptor p (selectBytes d (y C.root))
    ∀ j : Fin p.digits, ∃ q∈l, q.1=writeOp p+j.val ∧
      ∃ pre fly post : List (Fin n), ∃ f : Tok,
        w=(pre++door C::fly)++door C::post ∧
        let issue := rawRun x pre
        let prior := acqCaptureIndex p (selectBytes d (issue C.root))/2%2
        IssuedSegment d C issue fly (writeOp p+j.val) f ∧
        WriteFlightResult d C issue fly j prior f ∧
        reportDigitPair p (selectBytes d (y (nextAt (centre C) j.val))) ((desc/4)%2)=
          BitVec.ofNat (2*ReportByteRows.d p)
            (ancestrySendDigits p (selectBytes d (issue C.root))) := by
  dsimp only
  let C := charter G r
  let p := params d s
  let y := rawRun x w
  intro j
  have PC : PostAcqPC p (readPC d C x) := by
    exact ⟨.inl I.2.1,Start ▸ Nat.le_refl _,I.1⟩
  obtain ⟨q,M,Op⟩ := seal_has_write_receipt d C x w l T Start End j
  obtain ⟨pre,fly,post,f,W,Seg,Hit,Value⟩ :=
    receipt_write_at_current_cut d N hh G F digit r j (Nat.lt_of_lt_of_le j.isLt Width)
      x X I A PC w NR l T q M Op
  have W1 : w=pre++((door C::fly)++door C::post) := by rw [W,List.append_assoc]
  have R := no_restart_prefix d C x pre ((door C::fly)++door C::post) (W1 ▸ NR)
  have E := (raw_postacq_run d C hh F N digit x pre X PC R).2.2.trans
    (raw_postacq_run d C hh F N digit x w X PC NR).2.2.symm
  have Cap : acqCaptureIndex p (selectBytes d (rawRun x pre C.root))=
      acqCaptureIndex p (selectBytes d (y C.root)) := E
  have Sel := (descriptor_fields p (selectBytes d (y C.root))).2.2
  rw [captured_selector_index,←Cap] at Sel
  exact ⟨q,M,Op,pre,fly,post,f,W,Seg,Hit,Sel.symm ▸ Value⟩

end L4.ReportSealStagedBank
