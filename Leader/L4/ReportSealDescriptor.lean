import Leader.L4.ReportLeaseStep
import Leader.L4.ReportOwnerAcquireReturn

namespace L4.ReportSealDescriptor
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportByteRows ReportRawProjection
open ReportOwnerDoorProjection ReportOwnerAcquireReturn ReportWriterPayload

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

/-- Both literal positive commands use the capture selector and the
two strict comparison bits of the same old source file. -/
def comparisonFile (p : Params) (x : BitVec p.w) : Nat :=
  (x.extractLsb' (sourceBase p+(5+2*d p)) 4).toNat

def descriptor (p : Params) (x : BitVec p.w) : Nat :=
  let sel := capturedSelector p x
  let cmp := comparisonFile p x
  4*(2*sel+(1-sel))+2*(cmp/4==1).toNat+(cmp%4==1).toNat

theorem descriptor_fields (p : Params) (x : BitVec p.w) :
    descriptor p x<16 ∧ descriptor p x/8=capturedSelector p x ∧
      (descriptor p x/4)%2=1-capturedSelector p x := by
  unfold descriptor
  dsimp only
  have S : capturedSelector p x≤1 := by unfold capturedSelector; omega
  have C1 : ((comparisonFile p x / 4)==1).toNat≤1 := by
    cases ((comparisonFile p x / 4)==1) <;> decide
  have C0 : ((comparisonFile p x % 4)==1).toNat≤1 := by
    cases ((comparisonFile p x % 4)==1) <;> decide
  omega

theorem source_seal_commit_payload (p : Params) (x : BitVec p.w) (old t : Tok)
    (I : sourcePhase p x=1) (L : sealOp p≤sourceOpcode p x)
    (U : sourceOpcode p x≤commitOp p)
    (Issue : (source p x old).2=some t)
    (F : t.tag=2) :
    t={tag:=2,opcode:=sourceOpcode p x,payload:=descriptor p x} := by
  have A : ¬commitOp p<sourceOpcode p x := Nat.not_lt_of_ge U
  have B : sourceOpcode p x≠acqOp p := by unfold sealOp acqOp at *; omega
  have J : ¬sourceOpcode p x<writeOp p := by unfold sealOp writeOp at *; omega
  have K : ¬sourceOpcode p x<sealOp p := Nat.not_lt_of_ge L
  unfold sourcePhase at I
  unfold sourceOpcode at A B J K L U
  simp only [source,I,A,decide_false,show ((1:Nat)==0)=false by decide,
    show ((1:Nat)==3)=false by decide,Bool.false_or,Bool.false_eq_true,
    if_false,beq_self_eq_true,if_true,J,K,L,decide_true,Bool.and_false,Bool.true_and] at Issue
  split at Issue
  · simp only [Option.some.injEq] at Issue
    subst t
    simp [MISByteCodec.E] at F
  · have E := Option.some.inj Issue
    subst t
    simp only [beq_iff_eq,B,if_false]
    rfl

/-- Exact source guard for issuing either late command. A reserved
comparison trit causes restart; no rival-byte test is used here. -/
theorem source_seal_commit_launch_iff (p : Params) (x : BitVec p.w) (old : Tok)
    (I : sourcePhase p x=1) (L : sealOp p≤sourceOpcode p x)
    (U : sourceOpcode p x≤commitOp p) :
    ((source p x old).2=some ({tag:=2,opcode:=sourceOpcode p x,payload:=descriptor p x}:Tok)) ↔
      comparisonFile p x/4≠3 ∧ comparisonFile p x%4≠3 := by
  have A : ¬commitOp p<sourceOpcode p x := Nat.not_lt_of_ge U
  have B : sourceOpcode p x≠acqOp p := by unfold sealOp acqOp at *; omega
  have J : ¬sourceOpcode p x<writeOp p := by unfold sealOp writeOp at *; omega
  have K : ¬sourceOpcode p x<sealOp p := Nat.not_lt_of_ge L
  unfold sourcePhase at I
  unfold sourceOpcode at A B J K L U ⊢
  simp only [source,I,A,decide_false,show ((1:Nat)==0)=false by decide,
    show ((1:Nat)==3)=false by decide,Bool.false_or,Bool.false_eq_true,
    if_false,beq_self_eq_true,if_true,J,K,L,decide_true,Bool.and_false,Bool.true_and]
  split
  · rename_i Bad
    change ((comparisonFile p x/4==3)||(comparisonFile p x%4==3))=true at Bad
    simp [Bool.or_eq_true,beq_iff_eq] at Bad
    have Ne (H : MISByteCodec.E=
        ({tag:=2,opcode:=sourceOpcode p x,payload:=descriptor p x}:Tok)) : False := by
      have J := congrArg MISByteCodec.Token.tag H
      change (0 : Nat)=2 at J
      omega
    constructor
    · intro Conversely
      exact (Ne (Option.some.inj Conversely)).elim
    · intro H
      exact (Bad.elim H.1 H.2).elim
  · rename_i Good
    change ¬((comparisonFile p x/4==3)||(comparisonFile p x%4==3))=true at Good
    have Good' : comparisonFile p x/4≠3 ∧ comparisonFile p x%4≠3 := by
      simpa [Bool.or_eq_true,beq_iff_eq] using Good
    constructor
    · intro _
      exact Good'
    · intro _
      simp only [beq_iff_eq,B,if_false]
      rfl

/-- This is emitted at the actual root receiving endpoint; the
intermediate work patch is not an installation at the other endpoint. -/
theorem raw_seal_commit_payload (sheet : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) sheet Q) (N : 1<n)
    (x : Raw s n) (X : Cached sheet hh Q x) (t : Tok)
    (I : sourcePhase (params sheet s) (selectBytes sheet (x C.root))=1)
    (L : sealOp (params sheet s)≤sourceOpcode (params sheet s) (selectBytes sheet (x C.root)))
    (U : sourceOpcode (params sheet s) (selectBytes sheet (x C.root))≤commitOp (params sheet s))
    (Issue : (source (params sheet s) (selectBytes sheet (x C.root))
      (publicationToken (params sheet s) true (selectBytes sheet (x C.root)) 0)).2=some t)
    (Ft : t.tag=2) :
    let p := params sheet s
    let v := selectBytes sheet (x C.root)
    resetTokenRead p (selectBytes sheet (rawNext s x (door C) C.root)) 0=
      resetTokenWire p ({tag:=2,opcode:=sourceOpcode p v,payload:=descriptor p v}:Tok) := by
  dsimp only
  let p := params sheet s
  let v := selectBytes sheet (x C.root)
  let u := selectBytes sheet (rawNext s x (door C) C.root)
  have W := (raw_door_final sheet C x N ((cached_fibre sheet N hh Q F).mask x X)).2
  change resetTokenRead p u 0 =
    (match (source p v (publicationToken p true v 0)).2 with
      | none=>prelaunchDoorNormWire p v
      | some a=>resetTokenWire p a) at W
  rw [Issue] at W
  have T := source_seal_commit_payload p v _ t I L U Issue Ft
  rw [T] at W
  exact W

theorem descriptor_of_file_eq (p : Params) (x y : BitVec p.w)
    (H : drainFile p x=drainFile p y) : descriptor p x=descriptor p y := by
  change (x.extractLsb' (sourceBase p) (19+2*d p)).toNat=
    (y.extractLsb' (sourceBase p) (19+2*d p)).toNat at H
  have E := BitVec.eq_of_toNat_eq H
  have Out : comparisonFile p x=comparisonFile p y := by
    unfold comparisonFile
    apply congrArg BitVec.toNat
    apply BitVec.eq_of_getLsbD_eq
    intro i I
    have J : 5+(2*d p+i)<19+2*d p := by omega
    have B := congrArg (fun z : BitVec (19+2*d p) => z.getLsbD (5+2*d p+i)) E
    simpa only [BitVec.getLsbD_extractLsb',I,J,decide_true,
      Bool.true_and,Nat.add_assoc] using B
  have Cap : capturedSelector p x=capturedSelector p y := by
    rw [captured_selector_index,captured_selector_index,acq_index_of_file p x y H]
  unfold descriptor
  rw [Out,Cap]

private theorem drain_file_low_congr (p : Params) (a b : BitVec p.w)
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

open ReportPrelaunchClock ReportPrelaunchDoorLift ReportPrelaunchK1Geometry
open ReportOwnerReverseControl

/-- The real successful SEAL consume leaves the whole data file
alone and moves to empty ISSUE(COMMIT), so it cannot recompute a
different descriptor between these two specific commands. -/
theorem raw_seal_ack_keeps_descriptor (sheet : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) sheet Q) (N : 1<n)
    (x : Raw s n) (X : Cached sheet hh Q x) (R : ReverseWait sheet C x 0)
    (Op : (readPC sheet C x).2=sealOp (params sheet s))
    (Match : (tok sheet C x 0).opcode=sealOp (params sheet s))
    (Live : (tok sheet C x 0).fault=false) (Ok : (tok sheet C x 0).outcome≠1)
    (digit : 0<(params sheet s).digits) :
    let p := params sheet s
    let y := rawNext s x (door C)
    Cached sheet hh Q y ∧ EmptyIssueShape sheet C y ∧ readPC sheet C y=(1,commitOp p) ∧
      descriptor p (selectBytes sheet (y C.root))=descriptor p (selectBytes sheet (x C.root)) := by
  dsimp only
  let p := params sheet s
  let e := door C
  let u := selectBytes sheet (x e)
  let v := selectBytes sheet (x C.root)
  let t := publicationToken p true v 0
  let y := rawNext s x e
  let CF := cached_fibre sheet N hh Q F
  have rt : tok sheet C x 0=t := by
    rw [root_tok]
    exact (prelaunch_root_decode p v).symm
  have Tag : t.tag=3 := (congrArg MISByteCodec.Token.tag rt).symm.trans
    (R.2.2 0 C.positive)
  have PC : sourceOpcode p v=sealOp p := Op
  have O : t.opcode=sourceOpcode p v :=
    (congrArg MISByteCodec.Token.opcode rt).symm.trans (Match.trans PC.symm)
  have L : writeOp p≤sourceOpcode p v := by
    rw [PC]
    unfold writeOp sealOp
    omega
  have U : sourceOpcode p v≤sealOp p := Nat.le_of_eq PC
  have A : t.fault=false := (congrArg MISByteCodec.Token.fault rt).symm.trans Live
  have B : t.outcome≠1 := by rwa [rt] at Ok
  have Next := write_seal_ack_control p v t R.1.1 L U Tag O A B
  rw [PC] at Next
  have E : readPC sheet C y=(1,commitOp p) := by
    have W := (raw_door_final sheet C x N (CF.mask x X)).1
    have S : acqSourcePC p v t=(1,commitOp p) := by simpa [writeSealNext] using Next
    exact W.trans S
  have D := write_seal_ack_row_file p (h e) u v R.1.1 L U Tag O A B
  have Pair : drainFile p (selectBytes sheet (y C.root))=
    drainFile p ((row p (h e,true) (u,v)).2.apply v) := by
    apply drain_file_low_congr
    intro i I
    have H := (ReportLeaseStep.raw_low_pair sheet x e N (CF.mask x X) i I).2
    rw [show rightNeighbor e=C.root from RearTrace.right_predecessor C.root,C.rootHeader] at H
    exact H
  exact ⟨CF.closed x e X,door_consumes_root sheet C hh G F N x X R digit,E,
    descriptor_of_file_eq p _ _ (Pair.trans D)⟩

end L4.ReportSealDescriptor
