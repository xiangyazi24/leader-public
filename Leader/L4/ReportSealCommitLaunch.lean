import Leader.L4.ReportByteRows
import Leader.L4.ReportSealDescriptor
import Leader.L4.ReportOwnerIssueControl

namespace L4.ReportSealCommitLaunch
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportByteRows ReportRawProjection
open ReportOwnerDoorProjection ReportOwnerForwardControl ReportOwnerReverseControl
open ReportOwnerForwardLocations ReportPrelaunchClock ReportPrelaunchK1Geometry
open ReportSealDescriptor ReportWriterPayload ReportOwnerIssueControl ReportPrelaunchDoorLift

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem descriptor_forward (p : Params) (x : BitVec p.w) (op : Nat)
    (O : op=sealOp p ∨ op=commitOp p) :
    SealCommitForward p ({tag:=2,opcode:=op,payload:=descriptor p x}:Tok) := by
  obtain ⟨B,H,L⟩ := descriptor_fields p x
  refine ⟨rfl,O,B,?_,rfl,rfl,rfl,fun _=>rfl⟩
  change (((descriptor p x >>> 3)%2==1) != ((descriptor p x >>> 2)%2==1))=true
  simp only [Nat.shiftRight_eq_div_pow,show (2:Nat)^3=8 by decide,show (2:Nat)^2=4 by decide,H,L]
  have A : capturedSelector p x≤1 := by unfold capturedSelector; omega
  rcases (show capturedSelector p x=0 ∨ capturedSelector p x=1 by omega) with E|E <;> simp [E]

/-- A nonreserved late comparison file on the literal root door emits
the actual healthy forward packet, not just its provisional source intent. -/
theorem launch (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (op : Nat) (Op : op=sealOp (params d s) ∨ op=commitOp (params d s))
    (P : readPC d C x=(1,op))
    (Good : comparisonFile (params d s) (selectBytes d (x C.root))/4≠3 ∧
      comparisonFile (params d s) (selectBytes d (x C.root))%4≠3) :
    let p := params d s
    let v := selectBytes d (x C.root)
    let y := rawNext s x (door C)
    Cached d hh Q y ∧ ForwardWait d C y 0 ∧ readPC d C y=(2,op) ∧
      tok d C y 0=({tag:=2,opcode:=op,payload:=descriptor p v}:Tok) ∧
      SealCommitForward p (tok d C y 0) := by
  dsimp only
  let p := params d s
  let v := selectBytes d (x C.root)
  let y := rawNext s x (door C)
  let t : Tok := {tag:=2,opcode:=op,payload:=descriptor p v}
  let CF := cached_fibre d N hh Q F
  have Y := CF.closed x (door C) X
  have P0 : sourcePhase p v=1 := congrArg Prod.fst P
  have P1 : sourceOpcode p v=op := congrArg Prod.snd P
  have ord : sealOp p≤commitOp p := by unfold sealOp commitOp; omega
  change op=sealOp p ∨ op=commitOp p at Op
  have L : sealOp p≤sourceOpcode p v := by
    rw [P1]
    rcases Op with O|O <;> rw [O] <;> omega
  have U : sourceOpcode p v≤commitOp p := by
    rw [P1]
    rcases Op with O|O <;> rw [O] <;> omega
  have S := (source_seal_commit_launch_iff p v (publicationToken p true v 0) P0 L U).mpr Good
  have Issue : (source p v (publicationToken p true v 0)).2=some t := by
    rw [S,P1]
  have Eq : t=({tag:=2,opcode:=sourceOpcode p v,payload:=descriptor p v}:Tok) :=
    source_seal_commit_payload p v _ t P0 L U Issue rfl
  have Fit : RankFits p t := by
    rcases source_issue_fits p v (publicationToken p true v 0) P0 U with H|⟨a,E,_,A⟩
    · rw [Issue] at H
      have J := congrArg MISByteCodec.Token.tag (Option.some.inj H)
      contradiction
    · rw [Issue] at E
      exact (Option.some.inj E).symm ▸ A
  have W := raw_seal_commit_payload d C hh F N x X t P0 L U Issue rfl
  have Act : tok d C y 0=t := by
    rw [root_tok,W,←Eq]
    exact seal_commit_wire_roundtrip p t (descriptor_forward p v op Op) Fit false
  rcases ReportOwnerIssueControl.door_step d C hh G F N x X I with H|⟨V,J⟩
  · have E := H.2.2 0 C.positive
    change (tok d C y 0).tag=0 at E
    rw [Act] at E
    contradiction
  · exact ⟨Y,V,Prod.ext V.1.1 (J.trans P1),Act,Act.symm ▸ descriptor_forward p v op Op⟩

end L4.ReportSealCommitLaunch
