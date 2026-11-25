import Leader.L4.ReportItemNineAdapters
import Leader.L4.ReportItemNinePublication
import Leader.L4.ReportItemNineCmpSeed
import Leader.L4.ReportItemNineTapeCut
import Leader.L4.ReportWriteRailSupplier
import Leader.L4.ReportCurrentCustodyCut

namespace L4.ReportItemNineActualPublication
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerIssueControl ReportOwnerDoorProjection
open ReportIndexedSourcePrefix ReportLeaseOwner ReportGoodEightCut ReportGenerationAncestry
open ReportOwnerAcquireReturn ReportOwnerCommandRail ReportAcqExtract
open ReportItemNineStaging ReportItemNineTrace ReportItemNineCmpSeed
open ReportItemNineTapeCut ReportItemNineAdapters ReportItemNinePublication
open ReportOwnerAcquireProvenance (BeforeConsume from_genuine_issue)
open ReportDigitArithmetic ReportStaticSpacing

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

/-- Semantic publication on its actual guarded mark. The input is a
genuine ACQ issue, its sampled flight and the original no-restart positive
suffix, not claimed reader values, staged bytes, an authenticated COMMIT
packet, or independently chosen tape fragments. -/
theorem publication_of_actual_acq (d : Sheet) (N : 1<n) (Spos : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (r : Owner h) (issue : Raw s n) (A : FirstCut d hh Q G issue)
    (I : LegalIssue d (charter G r) issue)
    (PC : readPC d (charter G r) issue=(1,acqOp (params d s)))
    (flight w : List (Fin n))
    (T : BeforeConsume d (charter G r) (rawNext s issue (door (charter G r))) flight)
    (Tag : (tok d (charter G r) (rawRun (rawNext s issue (door (charter G r))) flight) 0).tag=3)
    (ND : (tok d (charter G r) (rawRun (rawNext s issue (door (charter G r))) flight) 0).outcome≠1)
    (Left : (params d s).digits≤(charter G r).a)
    (Mid : (params d s).digits≤(charter G r).b)
    (Right : (params d s).digits≤(charter G r).L-((charter G r).a+(charter G r).b))
    (NR : let C := charter G r
      let b := rawNext s (rawRun (rawNext s issue (door C)) flight) (door C)
      NoRestartTape d C b w)
    (e : Fin n) (atCentre : rightNeighbor e=centre (charter G r))
    (Accept : let C := charter G r
      let b := rawNext s (rawRun (rawNext s issue (door C)) flight) (door C)
      let x := rawRun b w
      ancestryCommitOpportunity (params d s) (h e) true
        (selectBytes d (x e)) (selectBytes d (x (centre C)))) :
    let C := charter G r
    let p := params d s
    let b := rawNext s (rawRun (rawNext s issue (door C)) flight) (door C)
    let inputs := snapshotInputs d C b
    let x := rawRun b w
    let post := fun i=>selectBytes d (rawNext s x e i)
    let c := centre C
    let a := updateDist p.radius inputs.leftRoot inputs.left
    let z := updateDist p.radius inputs.rightRoot inputs.right
    publicationSelector p (selectBytes d (x c))=inputs.prior ∧
      publicationSelector p (post c)=1-inputs.prior ∧
      publicationSelector p (post c)≠publicationSelector p (selectBytes d (x c)) ∧
      reportValue p post c true=a ∧ reportValue p post c false=z ∧
      publicationPair p (post c) (publicationSelector p (post c))=
        2*(decide (reportValue p post c true<p.radius)).toNat+
          (decide (reportValue p post c false<p.radius)).toNat ∧
      publicationA p (post c) (publicationSelector p (post c))=Z p (selectBytes d (x c)) := by
  dsimp only
  let C := charter G r
  let p := params d s
  let launched := rawNext s issue (door C)
  let old := rawRun launched flight
  let b := rawNext s old (door C)
  let digit := ReportPrelaunchDoorProducer.digits_positive d Spos
  obtain ⟨X,R,O,Match,Live,_⟩ := from_genuine_issue d C hh G F N issue A.1.1.1 I PC digit
    flight T Tag ND
  have ACK := raw_acq_consume_six d C hh G F N old X R O Match Live ND digit
  have B1 := first_cut_closed d N hh G F digit issue (door C) A
  have B2 := first_cut_run d N hh G F digit launched B1 flight
  have B := first_cut_closed d N hh G F digit old (door C) B2
  have Serial := seed_after_acq d C b ACK.2.1 ACK.2.2.1
  have Bi : LegalIssue d C b := by
    refine ⟨?_,ACK.2.1⟩
    rw [ACK.2.2.1]
    change cmpOp p≤commitOp p
    unfold cmpOp commitOp
    omega
  have C0 : PostAcqPC p (readPC d C b) := by
    have B0 := Bi.1
    rw [ACK.2.2.1] at B0 ⊢
    exact ⟨.inl rfl,Nat.le_refl _,B0⟩
  obtain ⟨l,Log⟩ := ack_tape_run d C N hh G F digit b B.1.1.1 Serial C0 w NR
  obtain ⟨pre,late,lp,ll,W,_,Prefix,Late,SealPC,Packet⟩ :=
    cut_at_actual_seal d N hh G F digit r b B.1.1.1 Bi Serial
      (congrArg Prod.snd ACK.2.2.1) w l Log e atCentre Accept
  have NRpre := no_restart_prefix d C b pre late (W ▸ NR)
  have Snap := snapshots_for_charter d N hh G F digit
    (ReportWriteRailSupplier.rail_supplier d N hh G F digit)
    r issue A.1.1.1 flight pre lp Left Right I PC A.1.2 T Tag ND B Bi NRpre Prefix
  have Writes := item_nine_write_credits d N hh G F digit r Mid b B.1.1.1 Bi C0 pre NRpre lp Prefix
  have Zero := raw_acq_consume_zero_cmp d C N hh F old X R O Tag Match Live ND
  have Replay : rawRun b w=rawRun (rawRun b pre) late := by rw [W,ShortOwnerEpochJS.raw_append]
  have Result := item9_handoff d N Spos hh G F (item_nine_staged_frame d N hh G F)
    r b pre late lp ll e B Serial ACK.2.2.1 Zero Prefix Late SealPC Snap Writes Mid
    atCentre (Replay ▸ Accept) (Replay ▸ Packet)
  rw [←Replay] at Result
  exact Result.2.2.2

end L4.ReportItemNineActualPublication

namespace L4.ReportItemNineActualPublication
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerIssueControl ReportOwnerDoorProjection
open ReportIndexedSourcePrefix ReportLeaseOwner ReportGoodEightCut ReportGenerationAncestry
open ReportOwnerAcquireReturn ReportOwnerCommandRail ReportAcqExtract
open ReportItemNineTrace ReportDigitArithmetic ReportStaticSpacing
open ReportCurrentCustodyCut ReportFreshIndexedSource ReportFreshAcqFile
open ReportIngressOwnership ReportOwnerProvenanceTransport ReportOwnerForwardLocations
open ReportOwnerAcquireProvenance (BeforeConsume)

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

/-- Current-cut form. On every actual accepted COMMIT in the closed
custody region, the old input snapshot and every mark needed to justify
the publication are recovered, rather than supplied. -/
theorem publication_at_current_cut (d : Sheet) (N : 1<n) (Spos : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (r : Owner h) (x : Raw s n) (A : CurrentCustodyCut d hh Q G x)
    (Left : (params d s).digits≤(charter G r).a)
    (Mid : (params d s).digits≤(charter G r).b)
    (Right : (params d s).digits≤(charter G r).L-((charter G r).a+(charter G r).b))
    (e : Fin n) (atCentre : rightNeighbor e=centre (charter G r))
    (Accept : ancestryCommitOpportunity (params d s) (h e) true
      (selectBytes d (x e)) (selectBytes d (x (centre (charter G r))))) :
    let C := charter G r
    let p := params d s
    ∃ issue : Raw s n, ∃ flight post : List (Fin n),
      let start := rawNext s issue (door C)
      let old := rawRun start flight
      let b := rawNext s old (door C)
      let inputs := snapshotInputs d C b
      let y := fun i=>selectBytes d (rawNext s x e i)
      let c := centre C
      let a := updateDist p.radius inputs.leftRoot inputs.left
      let z := updateDist p.radius inputs.rightRoot inputs.right
      FirstCut d hh Q G issue ∧ LegalIssue d C issue ∧
      readPC d C issue=(1,acqOp p) ∧ BeforeConsume d C start flight ∧
      (tok d C old 0).tag=3 ∧ (tok d C old 0).outcome≠1 ∧
      x=rawRun b post ∧ NoRestartTape d C b post ∧
      publicationSelector p (selectBytes d (x c))=inputs.prior ∧
      publicationSelector p (y c)=1-inputs.prior ∧
      publicationSelector p (y c)≠publicationSelector p (selectBytes d (x c)) ∧
      reportValue p y c true=a ∧ reportValue p y c false=z ∧
      publicationPair p (y c) (publicationSelector p (y c))=
        2*(decide (reportValue p y c true<p.radius)).toNat+
          (decide (reportValue p y c false<p.radius)).toNat ∧
      publicationA p (y c) (publicationSelector p (y c))=Z p (selectBytes d (x c)) := by
  dsimp only
  let C := charter G r
  let p := params d s
  let digit := ReportPrelaunchDoorProducer.digits_positive d Spos
  have Epoch : FreshAcqEpoch d hh Q G C x := (A.1.2 C (charter_mem G r)).1
  have Strong : StrongSerial d C x := by
    obtain ⟨a,reset,w,B,R,E,_⟩ := Epoch
    have X := B.1.1.1
    have Br := first_cut_run d N hh G F digit a B reset
    rw [E]
    exact (strong_run d C N hh G F digit (rawRun a reset) Br.1.1.1
      (seed_receipt d C N hh F a X reset R) w).2.1
  obtain ⟨J,H⟩ := ingress_cell G r e atCentre
  have Ce : out C (C.a-1)=e := congrArg Prod.fst H
  have Lane : C.route.port (C.a-1)=0 := congrArg Prod.snd H
  have E : tok d C x (C.a-1)=publicationToken p (h e) (selectBytes d (x e)) 0 := by
    rw [predecessor_projection,Ce,Lane]
    rfl
  have Tag := (congrArg MISByteCodec.Token.tag E).trans
    (((rankReady_iff p (h e) (selectBytes d (x e)) 0).mp Accept.2.1).1)
  have Live := (congrArg MISByteCodec.Token.fault E).trans Accept.2.2.1
  have Opc := (congrArg MISByteCodec.Token.opcode E).trans Accept.2.2.2.1
  have PC := (Strong.2 (C.a-1) J (.inl Tag) Live).symm.trans Opc
  have After : cmpOp p≤(readPC d C x).2 := by
    rw [PC]
    change cmpOp p≤commitOp p
    unfold cmpOp commitOp
    omega
  obtain ⟨a,reset,lead,flight,post,B,R,W,I,Issue,Before,Tg,ND,NR,_,_⟩ :=
    fresh_current_captures d N hh G F digit C x Epoch After
  let issue := rawRun (rawRun a reset) lead
  have X0 := first_cut_run d N hh G F digit a B reset
  have X := first_cut_run d N hh G F digit (rawRun a reset) X0 lead
  let b := rawNext s (rawRun (rawNext s issue (door C)) flight) (door C)
  have E : x=rawRun b post := W
  have H : ancestryCommitOpportunity p (h e) true (selectBytes d (rawRun b post e))
      (selectBytes d (rawRun b post (centre C))) := by
    rw [←E]
    exact Accept
  have Result := publication_of_actual_acq d N Spos hh G F r issue X I Issue
    flight post Before Tg ND Left Mid Right NR e atCentre H
  dsimp only at Result
  change x=rawRun (rawNext s (rawRun (rawNext s issue (door C)) flight) (door C)) post at W
  rw [←W] at Result
  exact ⟨issue,flight,post,X,I,Issue,Before,Tg,ND,W,NR,Result⟩

end L4.ReportItemNineActualPublication
