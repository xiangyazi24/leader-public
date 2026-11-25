import Leader.L4.ReportOwnerIndexedFlight
import Leader.L4.ReportWriteSplit

namespace L4.ReportIndexedLaunchData
open AllSizeProtocol ReportByteRows
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- The literal CMP/READ issue seeds the two old reader-bank selectors
and starts the two indexed payload digits at zero. -/
def readSeed (p : Params) (x : BitVec p.w) : IndexedData :=
  ⟨2*(acqCaptureIndex p x/4)+acqCaptureIndex p x%2,0,0⟩

/-- A WRITE issue uses the old source file, with the prior centre
selector and its complement, split into its two literal digits. -/
def writeSeed (p : Params) (x : BitVec p.w) : IndexedData :=
  let j := ancestrySourceCentre p x
  let z := ancestrySendDigits p x
  ⟨2*j+(1-j),z/2^d p,z%2^d p⟩

theorem readSeed_ok (p : Params) (x : BitVec p.w) (op : Nat)
    (B : 0<p.beta) (O : op<writeOp p) : (readSeed p x).OK p op := by
  have Bound : acqCaptureIndex p x<8 :=
    (x.extractLsb' (sourceBase p+(16+2*d p)) 3).isLt
  exact ⟨by unfold readSeed; dsimp only; omega,B,B,(fun E=>False.elim ((Nat.not_le_of_gt O) E))⟩

theorem writeSeed_ok (p : Params) (x : BitVec p.w) (op : Nat)
    (L : ancestrySendDigits p x%2^d p<p.beta)
    (H : ancestrySendDigits p x/2^d p<p.beta) : (writeSeed p x).OK p op := by
  have B := ancestry_source_centre_lt p x
  refine ⟨?_,H,L,?_⟩
  · unfold writeSeed
    dsimp only
    omega
  · intro _
    unfold writeSeed
    dsimp only
    omega

theorem readSeed_payload (p : Params) (x : BitVec p.w) :
    indexedPayload p (readSeed p x)=(2*(acqCaptureIndex p x/4)+acqCaptureIndex p x%2)*2^(2*d p) := by
  change 0+2^d p*(0+2^d p*(2*(acqCaptureIndex p x/4)+acqCaptureIndex p x%2))=_
  rw [Nat.zero_add,Nat.zero_add,←Nat.mul_assoc,←Nat.pow_add,show d p+d p=2*d p by omega,Nat.mul_comm]

private theorem raw_write_hi_lt (p : Params) (x : BitVec p.w) :
    ancestrySendDigits p x/2^d p<2^d p := by
  have B := ancestry_send_digits_lt p x
  rw [show 2*d p=d p+d p by omega,Nat.pow_add] at B
  exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr B

theorem writeSeed_payload (p : Params) (x : BitVec p.w) :
    indexedPayload p (writeSeed p x)=
      ancestryWritePayload p (ancestrySourceCentre p x) (ancestrySendDigits p x) := by
  let b := 2*ancestrySourceCentre p x+(1-ancestrySourceCentre p x)
  let z := ancestrySendDigits p x
  change z%2^d p+2^d p*(z/2^d p+2^d p*b)=b*2^(2*d p)+z
  rw [Nat.mul_add,←Nat.mul_assoc,←Nat.pow_add,show d p+d p=2*d p by omega]
  have K := Nat.mod_add_div z (2^d p)
  rw [←Nat.add_assoc, K, Nat.mul_comm (2^(2*d p)), Nat.add_comm]

def concreteSeed (p : Params) (x : BitVec p.w) (op : Nat) : IndexedData :=
  if op<writeOp p then readSeed p x else writeSeed p x

theorem indexed_source_canonical (p : Params) (x : BitVec p.w) (old t : Tok)
    (B : 0<p.beta) (P : sourcePhase p x=1) (op : Nat) (PC : sourceOpcode p x=op)
    (O : IndexedOp p op) (Issued : (source p x old).2=some t) (T : t.tag=2) :
    ∃ q : IndexedData, q=concreteSeed p x op ∧ q.OK p op ∧ t=indexedF p op (some q) := by
  have L := O.1
  have U := O.2
  have Q : ¬commitOp p<op := Nat.not_lt_of_ge (indexed_op_le p op O)
  have A : op≠acqOp p := by unfold cmpOp acqOp at *; omega
  have S : ¬sealOp p≤op := by omega
  unfold sourcePhase at P
  unfold sourceOpcode at PC
  by_cases R : op<writeOp p
  · have W : ¬writeOp p≤op := by omega
    simp only [source,P,PC,Q,decide_false,show ((1:Nat)==0)=false by decide,
      show ((1:Nat)==3)=false by decide,Bool.false_or,Bool.false_eq_true,
      if_false,beq_self_eq_true,if_true,L,U,R,W,S,decide_true,Bool.and_false,
      Bool.false_and,Bool.and_true,Bool.true_and,beq_false_of_ne A] at Issued
    refine ⟨readSeed p x,by simp [concreteSeed,R],readSeed_ok p x op B R,?_⟩
    rw [←Option.some.inj Issued]
    change ({tag:=2,opcode:=op,payload:=(2*(acqCaptureIndex p x/4)+acqCaptureIndex p x%2)*2^(2*d p)}:Tok)=_
    simp only [indexedF,readSeed_payload]
  · have W : writeOp p≤op := by omega
    have D0 := raw_write_hi_lt p x
    by_cases D : ancestrySendDigits p x%2^d p<p.beta ∧ ancestrySendDigits p x/2^d p<p.beta
    · have E : (source p x old).2=some
        ({tag:=2,opcode:=sourceOpcode p x,payload:=(ancestryWritePayload p (ancestrySourceCentre p x) (ancestrySendDigits p x))}:Tok) := by
        apply ancestry_source_write_intent p x old P
          (by unfold sourceOpcode; rw [PC]; exact W)
          (by unfold sourceOpcode; rw [PC]; exact U)
        change ((decide (ancestrySendDigits p x%2^d p<p.beta)) &&
          (decide ((ancestrySendDigits p x/2^d p)%2^d p<p.beta)))=true
        rw [Nat.mod_eq_of_lt D0]
        simp [D.1,D.2]
      rw [Issued] at E
      refine ⟨writeSeed p x,by simp [concreteSeed,R],writeSeed_ok p x op D.1 D.2,?_⟩
      rw [Option.some.inj E]
      simp only [indexedF,writeSeed_payload]
      change ({tag:=2,opcode:=sourceOpcode p x,payload:=_}:Tok)={tag:=2,opcode:=op,payload:=_}
      rw [show sourceOpcode p x=op from PC]
    · simp only [source,P,PC,Q,decide_false,show ((1:Nat)==0)=false by decide,
        show ((1:Nat)==3)=false by decide,Bool.false_or,Bool.false_eq_true,
        if_false,beq_self_eq_true,if_true,L,U,R,W,S,decide_true,Bool.and_false,
        Bool.false_and,Bool.and_true,Bool.true_and,beq_false_of_ne A] at Issued
      split at Issued
      · rw [←Option.some.inj Issued] at T
        contradiction
      · rename_i G
        change ¬((!(decide (ancestrySendDigits p x%2^d p<p.beta) &&
            decide ((ancestrySendDigits p x/2^d p)%2^d p<p.beta)) || false)=true) at G
        rw [Nat.mod_eq_of_lt D0] at G
        have C : ancestrySendDigits p x%2^d p<p.beta ∧ ancestrySendDigits p x/2^d p<p.beta := by
          simpa using G
        exact False.elim (D C)

open PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry ReportRawProjection
open ReportOwnerIssueControl ReportOwnerDoorProjection ReportPrelaunchDoorLift
open ReportPrelaunchClock ReportOwnerReverseControl ReportOwnerForwardControl
open ReportOwnerIndexedFlight

theorem params_beta_pos (d : Sheet) (s : Nat) : 0<(params d s).beta := by
  cases d <;> simp [params,firstParams,secondParams]

/-- The actual joined owner-door mark reifies the byte-level source seed.
The old source row is the supplier, not an assumed canonical token. -/
theorem indexed_door_seed {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}
    (d : Sheet) (C : Chart h) (op : Nat)
    (Range : IndexedOp (params d s) op) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (PC : readPC d C x=(1,op)) (t : Tok)
    (Issue : (source (params d s) (selectBytes d (x C.root))
        (publicationToken (params d s) true (selectBytes d (x C.root)) 0)).2=some t)
    (Tag : t.tag=2) :
    let y := rawNext s x (door C)
    Cached d hh Q y ∧ ∃ q, q=concreteSeed (params d s) (selectBytes d (x C.root)) op ∧
      t=indexedF (params d s) op (some q) ∧
      FState d C op y 0 (some q) := by
  let p := params d s
  let v := selectBytes d (x C.root)
  let y := rawNext s x (door C)
  have C1 : sourcePhase p v=1 := congrArg Prod.fst PC
  have C2 : sourceOpcode p v=op := congrArg Prod.snd PC
  obtain ⟨q,Seed,Good,E⟩ := indexed_source_canonical p v _ t
    (params_beta_pos d s) C1 op C2 Range Issue Tag
  let CF := cached_fibre d N hh Q F
  have Wire := (raw_door_final d C x N (CF.mask x X)).2
  change resetTokenRead p (selectBytes d (y C.root)) 0=
    (match (source p v (publicationToken p true v 0)).2 with
    | none => prelaunchDoorNormWire p v
    | some z => resetTokenWire p z) at Wire
  rw [Issue,E] at Wire
  have Actual : tok d C y 0=indexedF p op (some q) := by
    rw [root_tok,Wire]
    exact indexed_F_roundtrip p op Range false (some q) Good
  exact ⟨CF.closed x (door C) X,q,Seed,E,launch_from_token d C op Range hh G F N x X I PC q Good Actual⟩

theorem indexed_door_seed_of_forward {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}
    (d : Sheet) (C : Chart h) (op : Nat)
    (Range : IndexedOp (params d s) op) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (PC : readPC d C x=(1,op)) (A : ForwardWait d C (rawNext s x (door C)) 0) :
    Cached d hh Q (rawNext s x (door C)) ∧
      FState d C op (rawNext s x (door C)) 0
        (some (concreteSeed (params d s) (selectBytes d (x C.root)) op)) := by
  obtain ⟨t,T,Tag⟩ := ReportWriteSplit.structural_issue_emits_F d C N hh F x X I A
  obtain ⟨Y,q,Seed,_,S⟩ := indexed_door_seed d C op Range hh G F N x X I PC t T Tag
  exact ⟨Y,Seed ▸ S⟩

#print axioms indexed_door_seed_of_forward
#print axioms params_beta_pos
#print axioms indexed_door_seed
#print axioms indexed_source_canonical
end L4.ReportIndexedLaunchData
