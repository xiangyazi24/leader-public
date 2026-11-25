import Leader.L4.ReportIndexedSourcePrefix
import Leader.L4.ReportSealCommitLaunch
import Leader.L4.ReportSealReverse

namespace L4.ReportSealDescriptorTransport
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchClock ReportOwnerProvenanceTransport ReportOwnerDoorProjection
open ReportPrelaunchDoorLift ReportOwnerForwardLocations ReportOwnerForwardControl
open ReportOwnerIssueControl ReportOwnerReverseShape ReportOwnerReverseControl
open ReportOwnerSerial ReportByteRows ReportRawProjection ReportOwnerCommandRail
open ReportOwnerAcquireReturn ReportIndexedSourcePrefix ReportSealDescriptor
open ReportOwnerAcquireProvenance (BeforeConsume NoConsume)
open ReportSealReverse (Reply SealD)
variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

theorem comparison_of_file_eq (p : Params) (x y : BitVec p.w)
    (H : drainFile p x=drainFile p y) : comparisonFile p x=comparisonFile p y := by
  change (x.extractLsb' (sourceBase p) (19+2*d p)).toNat=
    (y.extractLsb' (sourceBase p) (19+2*d p)).toNat at H
  have E := BitVec.eq_of_toNat_eq H
  unfold comparisonFile
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  have J : 5+(2*d p+i)<19+2*d p := by omega
  have B := congrArg (fun z : BitVec (19+2*d p) => z.getLsbD (5+2*d p+i)) E
  simpa only [BitVec.getLsbD_extractLsb',I,J,decide_true,
    Bool.true_and,Nat.add_assoc] using B

theorem file_eq_if_same_pc (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (A : StrongSerial d C x) (PC : PostAcqPC (params d s) (readPC d C x))
    (w : List (Fin n)) (NR : NoRestartTape d C x w)
    (End : (readPC d C (rawRun x w)).2=(readPC d C x).2) :
    file d C (rawRun x w)=file d C x := by
  obtain ⟨l,T⟩ := ack_tape_run d C N hh G F digit x X A PC w NR
  have L := tape_count d C x w l T
  unfold logicalPC at L
  rw [End] at L
  have B : l.length=0 := by omega
  have E : l=[] := List.length_eq_zero_iff.mp B
  exact (tape_replay d C x w l T).trans (by rw [E]; rfl)

private theorem root_pub (d : Sheet) (C : Chart h) (x : Raw s n) :
    tok d C x 0=publicationToken (params d s) true (selectBytes d (x C.root)) 0 := by
  rw [root_tok]; rfl

theorem healthy_issue_keeps_file (d : Sheet) (C : Chart h) (N : 1<n)
    (x : Raw s n) (M : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (I : LegalIssue d C x) (Pos : 0<(readPC d C x).2)
    (NZ : (readPC d C (rawNext s x (door C))).2≠0) :
    file d C (rawNext s x (door C))=file d C x := by
  rw [door_file d C x N M,root_pub]
  have W := (raw_door_final d C x N M).1
  let p := params d s
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  have V : readPC d C (rawNext s x (door C))=acqSourcePC p v t := W
  exact (indexed_issue_file p v t I.2.1 I.1 Pos (by rwa [←V])).2

private theorem file_low_congr (p : Params) (a b : BitVec p.w)
    (H : ∀ i,i<grantBase p→a.getLsbD i=b.getLsbD i) :
    drainFile p a=drainFile p b := by
  change (a.extractLsb' (sourceBase p) (19+2*d p)).toNat=
    (b.extractLsb' (sourceBase p) (19+2*d p)).toNat
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  apply H
  unfold grantBase sealBase sourceW
  omega

theorem seal_ack_keeps_entire_file (d : Sheet) (C : Chart h) (N : 1<n)
    (x : Raw s n) (M : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (R : SealD d C x 0) :
    file d C (rawNext s x (door C))=file d C x := by
  let p := params d s
  let e := door C
  let u := selectBytes d (x e)
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  have Tok : t=Reply p := (root_pub d C x).symm.trans R.packet
  change publicationToken p true v 0=Reply p at Tok
  have O : sourceOpcode p v=sealOp p := congrArg Prod.snd R.pc
  have L : writeOp p≤sourceOpcode p v := by rw [O]; unfold writeOp sealOp; omega
  have Ack := write_seal_ack_row_file p (h e) u v (congrArg Prod.fst R.pc) L (Nat.le_of_eq O)
    (by rw [Tok]; rfl) (by rw [Tok,O]; rfl) (by rw [Tok]; rfl)
    (by rw [Tok]; change (0:Nat)≠1; decide)
  apply Eq.trans _ Ack
  apply file_low_congr p
  intro i I
  have M' := (ReportLeaseStep.raw_low_pair d x e N M i I).2
  rw [show rightNeighbor e=C.root from RearTrace.right_predecessor C.root,C.rootHeader] at M'
  exact M'

private theorem wait_root_tag_of_no_consume (d : Sheet) (C : Chart h)
    (x : Raw s n) (S : Serial d C x) (P : (readPC d C x).1=2)
    (NC : NoConsume d C x (door C)) :
    (tok d C x 0).tag=1 ∨ (tok d C x 0).tag=2 := by
  rcases S with I|⟨k,I⟩|⟨k,I⟩
  · have V := I.2.1
    omega
  · rw [I.2.2 0 C.positive]
    by_cases K : k=0
    · subst k; exact .inr rfl
    · exact .inl (by simp [frontTag,show 0<k by omega])
  · by_cases K : k=0
    · subst k
      have E := I.2.2 0 C.positive
      have B : (tok d C x 0).tag=3 := E
      exact (NC.elim (fun H=>H rfl) (fun H=>H B)).elim
    · exact .inl (by rw [I.2.2 0 C.positive]; simp [backTag,show 0<k by omega])

/-- Real WAIT frames both decoded source control and source file until
the first root D consume. Arbitrary marks, including unrelated owner
operations and the current command's terminal turn, are retained. -/
theorem wait_file_before_first_consume (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (x : Raw s n) (X : Cached d hh Q x) (A : Serial d C x)
    (P : LegalWait d C x) (w : List (Fin n)) (T : BeforeConsume d C x w) :
    Cached d hh Q (rawRun x w) ∧ Serial d C (rawRun x w) ∧
      readPC d C (rawRun x w)=readPC d C x ∧ file d C (rawRun x w)=file d C x := by
  let CF := cached_fibre d N hh Q F
  induction T with
  | nil => exact ⟨X,A,rfl,rfl⟩
  | @snoc w e B NC IH =>
    obtain ⟨Y,Ser,PC,E⟩ := IH
    rw [ShortOwnerEpochJS.raw_snoc]
    let z := rawRun x w
    refine ⟨CF.closed z e Y,ReportOwnerSerial.all_mark d C N hh G F z Y Ser digit e,?_⟩
    by_cases D : e=door C
    · subst e
      let p := params d s
      let v := selectBytes d (z C.root)
      let t := publicationToken p true v 0
      have L : LegalWait d C z := by unfold LegalWait; rw [PC]; exact P
      have Tag := wait_root_tag_of_no_consume d C z Ser L.1 NC
      rw [root_pub] at Tag
      have H := indexed_wait_file p v t L.1 L.2 Tag
      have Raw := (raw_door_final d C z N (CF.mask z Y)).1
      have File := door_file d C z N (CF.mask z Y)
      rw [root_pub] at File
      exact ⟨(Raw.trans H.1).trans PC,(File.trans H.2).trans E⟩
    · exact ⟨(raw_nondoor_control d C z e N (CF.mask z Y) D).trans PC,
        (nondoor_file d C z e N (CF.mask z Y) D).trans E⟩

theorem no_door_file_control (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (w : List (Fin n))
    (E : ∀ e∈w,e≠door C) :
    Cached d hh Q (rawRun x w) ∧ readPC d C (rawRun x w)=readPC d C x ∧
      file d C (rawRun x w)=file d C x := by
  let CF := cached_fibre d N hh Q F
  induction w generalizing x with
  | nil => exact ⟨X,rfl,rfl⟩
  | cons a w IH =>
    have D := E a (List.mem_cons_self)
    have ⟨Y,P,B⟩ := IH _ (CF.closed x a X) (fun e M=>E e (List.mem_cons_of_mem _ M))
    exact ⟨Y,P.trans (raw_nondoor_control d C x a N (CF.mask x X) D),
      B.trans (nondoor_file d C x a N (CF.mask x X) D)⟩

private theorem no_door_legal (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (A : LegalIssue d C x)
    (w : List (Fin n)) (E : ∀ e∈w,e≠door C) :
    LegalIssue d C (rawRun x w) := by
  let CF := cached_fibre d N hh Q F
  induction w generalizing x with
  | nil => exact A
  | cons a w IH =>
    exact IH _ (CF.closed x a X)
      (nondoor_preserves d C hh G F N x X A a (E a List.mem_cons_self)).1
      (fun e M=>E e (List.mem_cons_of_mem _ M))

/-- Both exact source commands on the original tape use the same whole
file. A genuine SEAL launch is followed by its first successful consume,
then by the first owner-door mark, which necessarily launches COMMIT.
No grant or bank hypothesis is needed for this *source* transport. -/
theorem seal_to_commit_source (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (I : LegalIssue d C x) (PC : readPC d C x=(1,sealOp (params d s)))
    (Good : comparisonFile (params d s) (selectBytes d (x C.root))/4≠3 ∧
      comparisonFile (params d s) (selectBytes d (x C.root))%4≠3)
    (before : List (Fin n)) (B : BeforeConsume d C (rawNext s x (door C)) before)
    (Ack : SealD d C (rawRun (rawNext s x (door C)) before) 0)
    (between : List (Fin n)) (NoDoor : ∀ e∈between,e≠door C) :
    let p := params d s
    let old := rawRun (rawNext s x (door C)) before
    let issue := rawRun (rawNext s old (door C)) between
    let launched := rawNext s issue (door C)
    let desc := descriptor p (selectBytes d (x C.root))
    Cached d hh Q issue ∧ LegalIssue d C issue ∧
      readPC d C issue=(1,commitOp p) ∧ file d C issue=file d C x ∧
      tok d C launched 0=({tag:=2,opcode:=commitOp p,payload:=desc}:Tok) ∧
      ForwardWait d C launched 0 ∧ readPC d C launched=(2,commitOp p) := by
  dsimp only
  let p := params d s
  let x0 := rawNext s x (door C)
  let old := rawRun x0 before
  let after := rawNext s old (door C)
  let issue := rawRun after between
  let CF := cached_fibre d N hh Q F
  obtain ⟨Y,V,PC0,_,_⟩ :=
    ReportSealCommitLaunch.launch d C hh G F N x X I (sealOp p) (.inl rfl) PC Good
  have Pos : 0<(readPC d C x).2 := by
    rw [PC]
    change 0<sealOp p
    unfold sealOp
    omega
  have NZ : (readPC d C x0).2≠0 := by
    rw [PC0]
    change sealOp p≠0
    unfold sealOp
    omega
  have Iss := healthy_issue_keeps_file d C N x (CF.mask x X) I Pos NZ
  obtain ⟨Z,_,_,WaitFile⟩ :=
    wait_file_before_first_consume d C N hh G F digit x0 Y (.inr (.inl ⟨0,V⟩)) V.1 before B
  have ConsumeFile := seal_ack_keeps_entire_file d C N old (CF.mask old Z) Ack
  obtain ⟨W,E,NewPC⟩ := ReportSealReverse.seal_root_consume d C hh G F N old Z Ack digit
  have L : LegalIssue d C after := by
    refine ⟨?_,E⟩
    rw [NewPC]
    exact Nat.le_refl _
  obtain ⟨H0,H1,H2⟩ := no_door_file_control d C N hh F after W between NoDoor
  have Legal := no_door_legal d C N hh G F after W L between NoDoor
  have GoalPC := H1.trans NewPC
  have Same : file d C issue=file d C x := H2.trans (ConsumeFile.trans (WaitFile.trans Iss))
  have Comp := comparison_of_file_eq p (selectBytes d (issue C.root)) (selectBytes d (x C.root)) Same
  have Desc := descriptor_of_file_eq p (selectBytes d (issue C.root)) (selectBytes d (x C.root)) Same
  have Good' : comparisonFile p (selectBytes d (issue C.root))/4≠3 ∧
      comparisonFile p (selectBytes d (issue C.root))%4≠3 := by rwa [Comp]
  obtain ⟨_,J,New,Packet,_⟩ :=
    ReportSealCommitLaunch.launch d C hh G F N issue H0 Legal (commitOp p) (.inr rfl) GoalPC Good'
  change tok d C (rawNext s issue (door C)) 0=
    ({tag:=2,opcode:=commitOp p,payload:=descriptor p (selectBytes d (issue C.root))}:Tok) at Packet
  rw [Desc] at Packet
  exact ⟨H0,Legal,GoalPC,Same,Packet,J,New⟩

end L4.ReportSealDescriptorTransport
