import Leader.L4.ReportIndexedLaunchData

namespace L4.ReportArithmeticLaunch
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerIssueControl
open ReportIndexedLaunchData ReportOwnerIndexedFlight ReportDigitArithmetic

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

theorem reader_source (p : Params) (v : BitVec p.w) (t : Tok)
    (op : Nat) (O : IndexedOp p op) (R : op<writeOp p)
    (P : sourcePhase p v=1) (PC : sourceOpcode p v=op) :
    (source p v t).2=some (indexedF p op (some (concreteSeed p v op))) := by
  have Q : ¬commitOp p<op := Nat.not_lt_of_ge (indexed_op_le p op O)
  have A : op≠acqOp p := by have := O.1; unfold cmpOp acqOp at *; omega
  have S : ¬sealOp p≤op := Nat.not_le_of_gt O.2
  have W : ¬writeOp p≤op := Nat.not_le_of_gt R
  unfold sourcePhase at P
  unfold sourceOpcode at PC
  rw [show concreteSeed p v op=readSeed p v from if_pos R]
  simp only [source,P,PC,Q,decide_false,show ((1:Nat)==0)=false by decide,
    show ((1:Nat)==3)=false by decide,Bool.false_or,Bool.false_eq_true,
    if_false,beq_self_eq_true,if_true,O.1,R,W,S,decide_true,
    Bool.false_and,Bool.and_true,beq_false_of_ne A,indexedF,readSeed_payload]
  rfl

theorem write_source (p : Params) (v : BitVec p.w) (t : Tok)
    (I : ItemNineInputs) (j : Nat) (J : j<p.digits) (B : 2≤p.beta)
    (P : sourcePhase p v=1) (PC : sourceOpcode p v=writeOp p+j)
    (H : ItemNineAt p I (writeOp p+j) (item9Read p v)) :
    (source p v t).2=some (indexedF p (writeOp p+j)
      (some (concreteSeed p v (writeOp p+j)))) := by
  let a := digit p.beta j (updateDist p.radius I.leftRoot I.left)
  let b := digit p.beta j (updateDist p.radius I.rightRoot I.right)
  have AB : a<p.beta := Nat.mod_lt _ (by omega)
  have BB : b<p.beta := Nat.mod_lt _ (by omega)
  have AA : a<2^d p := Nat.lt_of_lt_of_le AB (indexed_beta_bound p)
  have BA : b<2^d p := Nat.lt_of_lt_of_le BB (indexed_beta_bound p)
  have Send := (item9_at_write p I v j J H).trans (item9_send_digits p I j B)
  change ancestrySendDigits p v=2^d p*a+b at Send
  have Halves := item9_pack_halves p a b BA
  have W : writeOp p≤writeOp p+j := Nat.le_add_right _ _
  have U : writeOp p+j<sealOp p := by unfold writeOp sealOp; omega
  have E := ancestry_source_write_intent p v t P (PC.symm ▸ W) (PC.symm ▸ U) (by
    change (decide (ancestrySendDigits p v%2^d p<p.beta) &&
      decide (ancestrySendDigits p v/2^d p%2^d p<p.beta))=true
    rw [Send,Halves.1,Halves.2,Nat.mod_eq_of_lt AA]
    simp [AB,BB])
  rw [E,PC]
  simp only [indexedF,concreteSeed,if_neg (Nat.not_lt_of_ge W),writeSeed_payload]

#print axioms reader_source
#print axioms write_source

/-- The actual source door launches the indexed healthy flight. The WRITE
guard is derived from arithmetic digit bounds, not assumed. -/
theorem actual_seed (d : Sheet) (C : Chart h) (op : Nat)
    (Range : IndexedOp (params d s) op) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (PC : readPC d C x=(1,op)) (Y : ItemNineInputs)
    (B : 2≤(params d s).beta)
    (A : ItemNineAt (params d s) Y op (item9Read (params d s) (selectBytes d (x C.root)))) :
    let p := params d s
    let u := selectBytes d (x C.root)
    let y := rawNext s x (door C)
    Cached d hh Q y ∧ FState d C op y 0 (some (concreteSeed p u op)) := by
  dsimp only
  let p := params d s
  let u := selectBytes d (x C.root)
  let t := publicationToken p true u 0
  have H : (source p u t).2=some (indexedF p op (some (concreteSeed p u op))) := by
    have C1 : sourcePhase p u=1 := congrArg Prod.fst PC
    have C2 : sourceOpcode p u=op := congrArg Prod.snd PC
    by_cases R : op<writeOp p
    · exact reader_source p u t op Range R C1 C2
    · have J : op-writeOp p<p.digits := by
        have K : op<sealOp p := Range.2
        unfold writeOp sealOp at *
        omega
      have E : op=writeOp p+(op-writeOp p) := by omega
      have D : sourceOpcode p u=writeOp p+(op-writeOp p) := C2.trans E
      exact E.symm ▸ write_source p u t Y _ J B C1 D (E ▸ A)
  obtain ⟨Z,q,E,_,Seed⟩ := indexed_door_seed d C op Range hh G F N x X I PC _ H rfl
  exact ⟨Z,E ▸ Seed⟩

#print axioms actual_seed
end L4.ReportArithmeticLaunch
