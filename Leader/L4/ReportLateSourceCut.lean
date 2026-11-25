import Leader.L4.ReportSealCommitLaunch
import Leader.L4.ReportWriteSplit

namespace L4.ReportLateSourceCut
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerCommandRail
open ReportOwnerIssueControl ReportOwnerReverseControl ReportOwnerForwardControl
open ReportOwnerDoorProjection ReportOwnerForwardLocations ReportWriteSplit
open ReportOwnerAcquireReturn ReportSealDescriptor ReportSealCommitLaunch

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

theorem actual_late_launch (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x) (op : Nat)
    (P : (readPC d C x).2=op) (O : op=sealOp (params d s) ∨ op=commitOp (params d s))
    (W : ForwardWait d C (rawNext s x (door C)) 0) :
    let p := params d s
    let v := selectBytes d (x C.root)
    let y := rawNext s x (door C)
    Cached d hh Q y ∧ ForwardWait d C y 0 ∧ readPC d C y=(2,op) ∧
      tok d C y 0=({tag:=2,opcode:=op,payload:=descriptor p v}:Tok) ∧
      SealCommitForward p (tok d C y 0) := by
  let p := params d s
  let v := selectBytes d (x C.root)
  let old := publicationToken p true v 0
  obtain ⟨t,Src,Tag⟩ := structural_issue_emits_F d C N hh F x X I W
  have Phase : sourcePhase p v=1 := I.2.1
  have OP : sourceOpcode p v=op := P
  have L : sealOp p≤sourceOpcode p v := by
    rw [OP]
    rcases O with H|H <;> rw [H] <;> simp only [sealOp,commitOp] <;> dsimp only [p] <;> omega
  have U : sourceOpcode p v≤commitOp p := I.1
  have T := source_seal_commit_payload p v old t Phase L U Src Tag
  have B := (source_seal_commit_launch_iff p v old Phase L U).mp (T ▸ Src)
  exact ReportSealCommitLaunch.launch d C hh G F N x X I op O (Prod.ext Phase P) B

/-- Find the literal launch of the present late-command cursor, with
the exact original source descriptor. The comparison guard is derived
from the fact of launch, not an extra cleanliness premise. -/
theorem late_issue_split (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (I : LegalIssue d C x) (w : List (Fin n)) (k op : Nat)
    (A : ForwardWait d C (rawRun x w) k) (P : (readPC d C (rawRun x w)).2=op)
    (O : op=sealOp (params d s) ∨ op=commitOp (params d s)) :
    ∃ pre fly : List (Fin n), w=pre++door C::fly ∧
      let y := rawRun x pre
      let z := rawNext s y (door C)
      LegalIssue d C y ∧ readPC d C y=(1,op) ∧ Cached d hh Q z ∧
      tok d C z 0=({tag:=2,opcode:=op,payload:=descriptor (params d s) (selectBytes d (y C.root))}:Tok) ∧
      SealCommitForward (params d s) (tok d C z 0) ∧ BeforeTurn d C z fly k := by
  obtain ⟨pre,fly,W,Y,J,E,B⟩ := forward_issue_split d C N hh G F digit x X I w k A
  have R := actual_late_launch d C N hh G F _ Y J op (E.trans P) O
    (before_turn_start d C _ fly k B)
  exact ⟨pre,fly,W,J,Prod.ext J.2.1 (E.trans P),R.1,R.2.2.2.1,R.2.2.2.2,B⟩

#print axioms actual_late_launch
#print axioms late_issue_split
end L4.ReportLateSourceCut
