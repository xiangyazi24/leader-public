import Leader.L4.ReportLateSourceCut
import Leader.L4.ReportLateIngressSplit
import Leader.L4.ReportSealAckTape
import Leader.L4.ReportSealNoRestart

namespace L4.ReportFreshSealLineage
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerCommandRail
open ReportOwnerIssueControl ReportOwnerReverseControl ReportOwnerForwardControl
open ReportOwnerDoorProjection ReportOwnerForwardLocations ReportWriteSplit ReportOwnerReverseShape
open ReportOwnerAcquireReturn ReportSealDescriptor ReportSealCommitLaunch
open ReportLateSourceCut ReportLateIngressSplit ReportSealAckTape ReportSealNoRestart
open ReportCentreSealOwner ReportSealCommitOrigin ReportIndexedSourcePrefix
open ReportOwnerSerial ReportGenerationAncestry ReportLeaseOwner ReportIngressOwnership
open ReportOwnerProvenanceTransport ReportRawProjection

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

theorem forward_wait_of_tag (d : Sheet) (C : Chart h) (x : Raw s n)
    (A : Serial d C x) (k : Nat) (K : k<C.L) (Tag : (tok d C x k).tag=2) :
    ForwardWait d C x k := by
  rcases A with I|⟨j,I⟩|⟨j,I⟩
  · have B := I.2.2 k K
    omega
  · have B := I.2.2 k K
    rw [Tag] at B
    unfold frontTag at B
    split at B
    · contradiction
    · split at B
      · obtain rfl : j=k := by omega
        exact I
      · contradiction
  · have B := I.2.2 k K
    rw [Tag] at B
    unfold backTag at B
    split at B
    · contradiction
    · split at B <;> contradiction

/-- The complete physical prefix of a healthy late command, stopping
at its current cursor (for COMMIT, before the applying ingress). -/
theorem healthy_issued_prefix (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (I : LegalIssue d C x) (w : List (Fin n)) (k op : Nat)
    (Let : ForwardWait d C (rawRun x w) k) (P : (readPC d C (rawRun x w)).2=op)
    (Op : op=sealOp (params d s) ∨ op=commitOp (params d s))
    (K : op=commitOp (params d s) → k≤C.a-1)
    (H : (tok d C (rawRun x w) k).fault=false) :
    ∃ pre fly : List (Fin n), w=pre++door C::fly ∧
      let y := rawRun x pre
      LegalIssue d C y ∧ readPC d C y=(1,op) ∧
      tok d C (rawRun x w) k=({tag:=2,opcode:=op,payload:=descriptor (params d s) (selectBytes d (y C.root))}:Tok) ∧
      BeforeTurn d C (rawNext s y (door C)) fly k := by
  obtain ⟨pre,fly,W,J,PC,Y,TokenEq,_,B⟩ :=
    late_issue_split d C N hh G F digit x X I w k op Let P Op
  let y := rawRun x pre
  let z := rawNext s y (door C)
  let t : Tok := {tag:=2,opcode:=op,payload:=descriptor (params d s) (selectBytes d (y C.root))}
  have Shape := before_turn_start d C z fly k B
  have A : Flight d C z 0 t := ⟨Shape,descriptor_forward _ _ op Op,.inl TokenEq⟩
  have V := before_turn_as_late d C N hh G F z Y t A fly k B K
  have L := late_origin_run d C hh G F N z Y t A fly k V
  have E : rawRun x w=rawRun z fly := by
    rw [W,ShortOwnerEpochJS.raw_append]
    rfl
  have Healthy : (tok d C (rawRun z fly) k).fault=false := by rwa [←E]
  refine ⟨pre,fly,W,J,PC,?_,B⟩
  rw [E]
  rcases L.2.1.packet with R|R
  · exact R
  · rw [R] at Healthy
    contradiction

end L4.ReportFreshSealLineage

namespace L4.ReportFreshSealLineage
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerCommandRail ReportOwnerIssueControl
open ReportOwnerReverseControl ReportOwnerForwardControl ReportOwnerDoorProjection
open ReportOwnerForwardLocations ReportOwnerReverseShape ReportWriteSplit
open ReportOwnerAcquireReturn ReportSealDescriptor ReportSealCommitLaunch
open ReportLateSourceCut ReportLateIngressSplit ReportSealAckTape ReportSealNoRestart
open ReportCentreSealOwner ReportSealCommitOrigin ReportIndexedSourcePrefix
open ReportOwnerSerial ReportGenerationAncestry ReportLeaseOwner ReportIngressOwnership
open ReportOwnerProvenanceTransport ReportRawProjection
variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

/-- From a genuine own RESET on the sampled tape, a guarded COMMIT ingress
has the actual healthy SEAL's issue and guarded installation, the real
successful old-root consume, and the matching COMMIT issue and flight.
Both source issues carry the same exact descriptor. No tape is replayed
out of order and the terminal COMMIT need not carry the descriptor. -/
theorem seal_commit_after_receipt (d : Sheet) (G : GapInput h) (r : Owner h)
    (N : 1<n) (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (a : Raw s n) (A : Cached d hh Q a) (flight : List (Fin n))
    (R : Generated d (charter G r) a flight .done) (digit : 0<(params d s).digits)
    (w : List (Fin n)) (e : Fin n)
    (atCentre : rightNeighbor e=centre (charter G r))
    (Accept : let x := rawRun (rawRun a flight) w
      ancestryCommitOpportunity (params d s) (h e) true (selectBytes d (x e))
        (selectBytes d (x (centre (charter G r))))) :
    let C := charter G r
    let p := params d s
    let x0 := rawRun a flight
    let x := rawRun x0 w
    ∃ pre sf beforeAck beforeCommit cf : List (Fin n),
      let sealPrefix := pre++door C::sf
      let afterSeal := beforeAck++door C::(beforeCommit++door C::cf)
      let issueSeal := rawRun x0 pre
      let old := rawRun x0 sealPrefix
      let sealed := rawNext s old (centre C)
      let ackOld := rawRun sealed beforeAck
      let ackNew := rawNext s ackOld (door C)
      let issueCommit := rawRun ackNew beforeCommit
      let delta := descriptor p (selectBytes d (issueSeal C.root))
      w=sealPrefix++centre C::afterSeal ∧
      readPC d C issueSeal=(1,sealOp p) ∧
      reportHeaderSetSeal p (selectBytes d (old (centre C))) ∧
      tok d C old C.a=({tag:=2,opcode:=sealOp p,payload:=delta}:Tok) ∧
      centreSeal d C sealed=some delta ∧
      CreditAt d C ackOld (door C) ∧ (readPC d C ackOld).2=sealOp p ∧
      readPC d C issueCommit=(1,commitOp p) ∧
      descriptor p (selectBytes d (issueCommit C.root))=delta ∧
      tok d C x (C.a-1)=({tag:=2,opcode:=commitOp p,payload:=delta}:Tok) ∧
      NoSealTape d C sealed afterSeal ∧ NoRestartTape d C sealed afterSeal := by
  dsimp only
  let C := charter G r
  let p := params d s
  let x0 := rawRun a flight
  let x := rawRun x0 w
  obtain ⟨pre,post,W,PS,Guard,Same,B,No,NR⟩ :=
    accepted_commit_no_restart_since_seal d G r N hh F a A flight R digit w e atCentre Accept
  let old := rawRun x0 pre
  let sealed := rawNext s old (centre C)
  have X := (cached_genuine_full_parked d C N hh F a A flight R).1
  have S := seed_receipt d C N hh F a A flight R
  have SO := strong_run d C N hh G F digit x0 X S pre
  have SX := strong_run d C N hh G F digit x0 X S w
  let CF := cached_fibre d N hh Q F
  obtain ⟨_,K,Ch,Lane,_⟩ := canonical_centre G r
  have TSeal : tok d C old C.a=publicationToken p true (selectBytes d (old (centre C))) 1 := by
    rw [predecessor_projection,Ch,Lane]
    rfl
  have SealTag := ((rankReady_iff p true (selectBytes d (old (centre C))) 1).mp Guard.1).1
  have SealFault : (tok d C old C.a).fault=false := by rw [TSeal]; exact Guard.2.1
  have SF := forward_wait_of_tag d C old SO.2.1.1 C.a K ((congrArg MISByteCodec.Token.tag TSeal).trans SealTag)
  have I0 : LegalIssue d C x0 := by
    have A0 := (cached_genuine_full_parked d C N hh F a A flight R).2
    have P0 : readPC d C x0=(1,1) := pc_fields d C x0 .issue1 (by decide) A0.1.1
    rcases S.1 with H|⟨_,H⟩|⟨_,H⟩
    · exact H
    · have B : (readPC d C x0).1=2 := H.1.1
      rw [P0] at B
      contradiction
    · have B : (readPC d C x0).1=2 := H.1.1
      rw [P0] at B
      contradiction
  obtain ⟨u,sf,Split,_,IssueS,PacketS,_⟩ :=
    healthy_issued_prefix d C N hh G F digit x0 X I0 pre C.a (sealOp p) SF PS
      (.inl rfl) (fun U=>by simp only [sealOp,commitOp] at U; omega) SealFault
  obtain ⟨J,Cell⟩ := ingress_cell G r e atCentre
  have Ce : out C (C.a-1)=e := congrArg Prod.fst Cell
  have La : C.route.port (C.a-1)=0 := congrArg Prod.snd Cell
  have TC : tok d C x (C.a-1)=publicationToken p (h e) (selectBytes d (x e)) 0 := by
    rw [predecessor_projection,Ce,La]
    rfl
  have CommitTag := ((rankReady_iff p (h e) (selectBytes d (x e)) 0).mp Accept.2.1).1
  have CTag := (congrArg MISByteCodec.Token.tag TC).trans CommitTag
  have CLive := (congrArg MISByteCodec.Token.fault TC).trans Accept.2.2.1
  have COp := (congrArg MISByteCodec.Token.opcode TC).trans Accept.2.2.2.1
  have Pc := (SX.2.1.2 (C.a-1) J (.inl CTag) CLive).symm.trans COp
  have CV := forward_wait_of_tag d C x SX.2.1.1 _ J CTag
  have PosSealed : (readPC d C sealed).2=sealOp p := by
    rw [raw_nondoor_control d C old (centre C) N (CF.mask old SO.1)
      (Ne.symm (ReportChartPartition.door_not_outgoing C C.a K))]
    exact PS
  have Replay : x=rawRun sealed post := by
    unfold x
    rw [W,ShortOwnerEpochJS.raw_append]
    rfl
  have PEnd : (readPC d C (rawRun sealed post)).2=commitOp p := Replay ▸ Pc
  have Y := CF.closed old (centre C) SO.1
  have Serial := strong_step d C N hh G F old SO.1 SO.2.1 digit (centre C)
  obtain ⟨v,rest,ACK,OldOP,Credit,Issue,_,_,_⟩ :=
    ack_on_original_tape d C N hh G F digit sealed Y Serial post NR PosSealed PEnd
  let ackOld := rawRun sealed v
  let ackNew := rawNext s ackOld (door C)
  have AY := CF.closed ackOld (door C) (strong_run d C N hh G F digit sealed Y Serial v).1
  have End : x=rawRun ackNew rest := by
    rw [Replay,ACK,ShortOwnerEpochJS.raw_append]
    rfl
  obtain ⟨q,cf,Cut,_,IssueC,PacketC,_⟩ :=
    healthy_issued_prefix d C N hh G F digit ackNew AY Issue rest (C.a-1) (commitOp p)
      (End ▸ CV) (End ▸ Pc) (.inr rfl) (fun _=>Nat.le_refl _) (End ▸ CLive)
  rw [←End] at PacketC
  have D : descriptor p (selectBytes d (rawRun ackNew q C.root))=
      descriptor p (selectBytes d (rawRun x0 u C.root)) := by
    rw [PacketS,PacketC] at Same
    exact Same.symm
  have Filled : centreSeal d C sealed=some (descriptor p (selectBytes d (rawRun x0 u C.root))) := by
    rw [PacketC,D] at B
    exact B
  have Tape : post=v++door C::(q++door C::cf) := ACK.trans (by rw [Cut])
  rw [D] at PacketC
  refine ⟨u,sf,v,q,cf,?_,IssueS,?_,?_,?_,?_,?_,?_,?_,PacketC,?_,?_⟩
  · rw [←Split,←Tape]; exact W
  · rw [←Split]; exact Guard
  · rw [←Split]; exact PacketS
  · rw [←Split]; exact Filled
  · rw [←Split]; exact Credit
  · rw [←Split]; exact OldOP
  · rw [←Split]; exact IssueC
  · rw [←Split]; exact D
  · rw [←Split,←Tape]; exact No
  · rw [←Split,←Tape]; exact NR

end L4.ReportFreshSealLineage
