import Leader.L4.ReportFreshSealLineage
import Leader.L4.ReportIssuedSegment
import Leader.L4.ReportAcqExtract

namespace L4.ReportItemNineTapeCut
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerIssueControl ReportOwnerDoorProjection
open ReportOwnerAcquireReturn ReportOwnerCommandRail ReportPrelaunchRank ReportAcqExtract
open ReportIndexedSourcePrefix ReportLeaseOwner ReportGenerationAncestry
open ReportSealDescriptor ReportIssuedSegment ReportFreshSealLineage
open ReportOwnerReverseControl ReportOwnerForwardControl

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

/-- Split the original ordered ACK tape, preserving the raw cut and the
exact concatenation of receipt lists. -/
theorem split_ack_tape (d : Sheet) (C : Chart h) (x : Raw s n)
    (u v : List (Fin n)) (l : List Receipt) (T : AckTape d C x (u++v) l) :
    ∃ ls ms, l=ls++ms ∧ AckTape d C x u ls ∧ AckTape d C (rawRun x u) v ms := by
  induction u generalizing x l with
  | nil => exact ⟨[],l,rfl,.nil x,T⟩
  | cons e u IH =>
    change AckTape d C x (e::(u++v)) l at T
    cases T with
    | hold H T =>
      obtain ⟨ls,ms,E,L,R⟩ := IH _ _ T
      exact ⟨ls,ms,E,.hold H L,R⟩
    | credit H T =>
      obtain ⟨ls,ms,E,L,R⟩ := IH _ _ T
      exact ⟨_,ms,congrArg (List.cons _) E,.credit H L,R⟩

theorem same_opcode_file (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (l : List Receipt) (T : AckTape d C x w l)
    (P : (readPC d C (rawRun x w)).2=(readPC d C x).2) :
    file d C (rawRun x w)=file d C x := by
  have L := tape_count d C x w l T
  unfold logicalPC at L
  rw [P] at L
  have Z : l=[] := List.length_eq_zero_iff.mp (by omega)
  rw [Z] at T
  exact tape_replay d C x w [] T

theorem logical_commit (p : Params) :
    logical p.digits (commitOp p)=commitOp p := by
  unfold commitOp logical
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]

/-- The one SEAL credit precedes the physical COMMIT witness on the
original successful generation. A count alone does not supply a row;
tape_receipt_origin returns the actual old root D and consume mark. -/
theorem commit_log_seal_receipt (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (l : List Receipt) (T : AckTape d C x w l)
    (S : (readPC d C x).2=cmpOp (params d s))
    (E : (readPC d C (rawRun x w)).2=commitOp (params d s)) :
    ∃ pre post : List (Fin n), w=pre++door C::post ∧
      let old := rawRun x pre
      (readPC d C old).2=sealOp (params d s) ∧ CreditAt d C old (door C) := by
  let p := params d s
  have L := tape_count d C x w l T
  have O := tape_order d C x w l T
  unfold logicalPC at L O
  rw [S,E,logical_cmp,logical_commit] at L
  rw [S,logical_cmp] at O
  have Len : l.length=3*p.digits+1 := by
    change commitOp p=cmpOp p+l.length at L
    unfold commitOp cmpOp at L
    omega
  obtain ⟨r,M,R⟩ := ordered_complete p (cmpOp p) l O (3*p.digits) (by rw [Len]; omega)
  have S0 : logical p.digits (sealOp p)=cmpOp p+3*p.digits := by
    rw [logical_seal]
    unfold sealOp cmpOp
    omega
  have UB := (ordered_range p (cmpOp p) l O r M).2
  have Bound : r.1<4*p.digits+5 := by
    by_cases B : r.1<4*p.digits+5
    · exact B
    · have A : logical p.digits r.1=r.1 := by unfold logical; rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
      rw [Len,A] at UB
      unfold cmpOp at UB
      omega
  have Op := logical_injective p.digits r.1 (sealOp p) Bound (by unfold sealOp; omega) (R.trans S0.symm)
  obtain ⟨u,v,W,Exact,Credit⟩ := tape_receipt_origin d C x w l T r M
  exact ⟨u,v,W,(congrArg Prod.fst Exact).symm.trans Op,Credit⟩

end L4.ReportItemNineTapeCut

namespace L4.ReportItemNineTapeCut
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerIssueControl ReportOwnerDoorProjection
open ReportOwnerAcquireReturn ReportOwnerCommandRail ReportPrelaunchRank ReportAcqExtract
open ReportIndexedSourcePrefix ReportLeaseOwner ReportGenerationAncestry ReportGoodEightCut
open ReportSealDescriptor ReportIssuedSegment ReportFreshSealLineage
open ReportOwnerReverseControl ReportOwnerForwardControl ReportIngressOwnership
open ReportOwnerProvenanceTransport ReportOwnerForwardLocations

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

theorem ack_tail (d : Sheet) (C : Chart h) (x : Raw s n)
    (e : Fin n) (w : List (Fin n)) (l : List Receipt) (T : AckTape d C x (e::w) l) :
    ∃ ms,AckTape d C (rawNext s x e) w ms := by
  cases T with
  | hold _ T => exact ⟨_,T⟩
  | credit _ T => exact ⟨_,T⟩

/-- Relift the accepted COMMIT to the literal source SEAL issue inside
the same post-ACQ positive log. The two suffixes are not resampled.
The descriptor is unchanged from SEAL issue through COMMIT issue;
both old guards are verified via the literal source and return rows. -/
theorem cut_at_actual_seal (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (r : Owner h)
    (b : Raw s n) (B : Cached d hh Q b)
    (I : LegalIssue d (charter G r) b) (S : StrongSerial d (charter G r) b)
    (Start : (readPC d (charter G r) b).2=cmpOp (params d s))
    (w : List (Fin n)) (l : List Receipt) (T : AckTape d (charter G r) b w l)
    (e : Fin n) (atCentre : rightNeighbor e=centre (charter G r))
    (Accepted : let x := rawRun b w
      ancestryCommitOpportunity (params d s) (h e) true
        (selectBytes d (x e)) (selectBytes d (x (centre (charter G r))))) :
    let C := charter G r
    let p := params d s
    ∃ pre late : List (Fin n), ∃ pl ll : List Receipt,
      w=pre++late ∧ l=pl++ll ∧
      let oldSealIssue := rawRun b pre
      AckTape d C b pre pl ∧ AckTape d C oldSealIssue late ll ∧
      readPC d C oldSealIssue=(1,sealOp p) ∧
      tok d C (rawRun b w) (C.a-1)=({tag:=2,opcode:=commitOp p,payload:=descriptor p (selectBytes d (oldSealIssue C.root))}:Tok) := by
  dsimp only
  let C := charter G r
  let p := params d s
  let x := rawRun b w
  obtain ⟨J,H⟩ := ingress_cell G r e atCentre
  have Ce : out C (C.a-1)=e := congrArg Prod.fst H
  have Lane : C.route.port (C.a-1)=0 := congrArg Prod.snd H
  have E : tok d C x (C.a-1)=publicationToken p (h e) (selectBytes d (x e)) 0 := by
    rw [predecessor_projection,Ce,Lane]
    rfl
  have Tag := (congrArg MISByteCodec.Token.tag E).trans
    (((rankReady_iff p (h e) (selectBytes d (x e)) 0).mp Accepted.2.1).1)
  have Live := (congrArg MISByteCodec.Token.fault E).trans Accepted.2.2.1
  have Opc := (congrArg MISByteCodec.Token.opcode E).trans Accepted.2.2.2.1
  have ST := (strong_run d C N hh G F digit b B S w).2.1
  have PC := (ST.2 (C.a-1) J (.inl Tag) Live).symm.trans Opc
  have FW := forward_wait_of_tag d C x ST.1 _ J Tag
  obtain ⟨com,cf,W,_,CommitPC,Packet,_⟩ :=
    healthy_issued_prefix d C N hh G F digit b B I w (C.a-1) (commitOp p)
      FW PC (.inr rfl) (fun _=>Nat.le_refl _) Live
  let bCommit := rawRun b com
  have Split : AckTape d C b (com++door C::cf) l := W ▸ T
  obtain ⟨lc,_,_,Tcom,_⟩ := split_ack_tape d C b com (door C::cf) l Split
  obtain ⟨ap,aq,WA,SEA,Ack⟩ := commit_log_seal_receipt d C b com lc Tcom Start
    (congrArg Prod.snd CommitPC)
  let oldAck := rawRun b ap
  let ackNew := rawNext s oldAck (door C)
  have ACK := Ack
  obtain ⟨_,Rev,_,Match,Live,Ok,_,_,_⟩ := ACK
  have SealPhase : (readPC d C oldAck).1=2 := Rev.1.1
  obtain ⟨pre,sf,WS,_,OldLegal,_,Same,_⟩ :=
    waiting_issued_segment d C N hh G F digit b B I ap SealPhase
  let bSeal := rawRun b pre
  have PCSeal : readPC d C bSeal=(1,sealOp p) := Prod.ext OldLegal.2.1 (Same.trans SEA)
  have C1 : AckTape d C b (ap++door C::aq) lc := WA ▸ Tcom
  obtain ⟨lc1,lc2,_,Tack,Tlate⟩ := split_ack_tape d C b ap (door C::aq) lc C1
  obtain ⟨lt,Post⟩ := ack_tail d C oldAck (door C) aq lc2 Tlate
  have One : AckTape d C b (pre++door C::sf) lc1 := WS ▸ Tack
  obtain ⟨_,ls,_,_,FS⟩ := split_ack_tape d C b pre (door C::sf) lc1 One
  have E0 : oldAck=rawRun bSeal (door C::sf) := by unfold oldAck bSeal; rw [WS,ShortOwnerEpochJS.raw_append]
  have Read0 : (readPC d C (rawRun bSeal (door C::sf))).2=(readPC d C bSeal).2 := by
    rw [←E0,SEA,PCSeal]
  have File0 := same_opcode_file d C bSeal (door C::sf) ls FS Read0
  rw [←E0] at File0
  have CachedAck := (strong_run d C N hh G F digit b B S ap).1
  obtain ⟨_,_,PCNew,Desc1⟩ := raw_seal_ack_keeps_descriptor d C hh G F N oldAck CachedAck
    Rev SEA (Match.trans SEA) Live Ok digit
  have E1 : bCommit=rawRun ackNew aq := by unfold bCommit; rw [WA,ShortOwnerEpochJS.raw_append]; rfl
  have Read1 : (readPC d C (rawRun ackNew aq)).2=(readPC d C ackNew).2 := by
    rw [←E1,CommitPC,PCNew]
  have File1 := same_opcode_file d C ackNew aq lt Post Read1
  rw [←E1] at File1
  have Desc2 := (descriptor_of_file_eq p (selectBytes d (bCommit C.root)) _ File1).trans
    (Desc1.trans (descriptor_of_file_eq p _ _ File0))
  let late := (door C::sf)++door C::(aq++door C::cf)
  have Total : w=pre++late := by
    rw [W,WA,WS]
    simp [late,List.append_assoc]
  obtain ⟨lp,ll,L,Before,Late⟩ :=
    split_ack_tape d C b pre late l (Total ▸ T)
  rw [Desc2] at Packet
  exact ⟨pre,late,lp,ll,Total,L,Before,Late,PCSeal,Packet⟩

end L4.ReportItemNineTapeCut
