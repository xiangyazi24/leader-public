import Leader.L4.BStarPhysicalCmpSem

namespace L4.BStarCmpReceipt
open AllSizeProtocol BStarTrace BStarLongToken BStarLongArithmetic
open BStarLongCommand BStarPhysicalDigitSem BStarPhysicalWordSem
open BStarLongSignatures L4.Compiler.Digits L4.Compiler.Native

/-- Physical receipt: equal in the high bit. Accepted compiler
scalar: equal in the low bit. The unused code 3 is not a CMP outcome. -/
def accepted (q : Nat) : Nat := q/2+2*(q%2)

theorem physical_accept (a b : Nat) :
    accepted (cmpPack (decide (a=b)) (decide (a<b)))=cmpCode a b := by
  by_cases E : a=b
  · subst b
    simp [accepted,cmpPack,cmpCode]
  · by_cases L : a<b <;> simp [accepted,cmpPack,cmpCode,E,L]

theorem projections (a b : Nat) :
    let q := cmpPack (decide (a=b)) (decide (a<b))
    q/2=(decide (cmpCode a b=1)).toNat ∧ q%2=(decide (cmpCode a b=2)).toNat := by
  by_cases E : a=b
  · subst b
    simp [cmpPack,cmpCode]
  · by_cases L : a<b <;> simp [cmpPack,cmpCode,E,L]

/-- Result of each real CMP alias when the current comparison's result
is present in the pending receipt before any physical packed write. -/
theorem pending_projections (x : BitVec LW) (i : Nat) (xs : Pending) (a b : Nat)
    (H : newest x xs i=cmpPack (decide (a=b)) (decide (a<b))) :
    aliasValue x xs (.cmpEq i)=some (decide (cmpCode a b=1)).toNat ∧
    aliasValue x xs (.cmpLt i)=some (decide (cmpCode a b=2)).toNat := by
  exact ⟨congrArg some (by change newest x xs i/2=_; rw [H]; exact (projections a b).1),
    congrArg some (by change newest x xs i%2=_; rw [H]; exact (projections a b).2)⟩

theorem pending_head (x : BitVec LW) (i q : Nat) (tail : Pending) :
    newest x ((i,q)::tail) i=q := by simp [newest]

private theorem cmp_op_min {op : Nat} (E : arithKind op=some .cmp) : 13≤op := by
  unfold arithKind at E
  split at E
  · contradiction
  · omega

/-- A CMP physical instruction starts the sweep with equal=true and
less=false; this does not depend on packed source bytes. -/
theorem issue_cmp (x : BitVec LW) {op : Nat} (hi : op<408) (K : arithKind op=some .cmp) :
    BStarLongDoor.initial op x=some (cmpPack true false) := by
  have L := cmp_op_min K
  have A : op≠acquire := by unfold acquire; omega
  have C : op≠copyLoad := by unfold copyLoad; omega
  have S : op≠stageOp := by unfold stageOp; omega
  have E : op≠sealOp := by unfold sealOp; omega
  have T : op≠commitOp := by unfold commitOp; omega
  simp [BStarLongDoor.initial,A,C,S,E,T,K,cmpPack]

/-- The numerical terminal turn and reply binder preserve the two raw
physical flag bits. No conversion is inserted in the physical row. -/
theorem terminal_cmp (g : LongGeometry) (j : Fin 11) (p : Payload)
    (ok : p.fault=0) (hi : p.opcode.toNat<408) (K : arithKind p.opcode.toNat=some .cmp)
    (small : p.argument.toNat<4) :
    finish p=.reply {p with race:=0,outcome:=0} ∧
    BStarLongCommand.bind g j (finish p)=.reply {p with race:=0,outcome:=0} := by
  let op := p.opcode.toNat
  have L := cmp_op_min K
  have a : op≠acquire := by unfold op acquire; omega
  have b : op≠admit := by unfold op admit; omega
  have c : op≠bitOp := by unfold op bitOp; omega
  have d : op≠sealOp := by unfold op sealOp; omega
  have arg : BitVec.ofNat 34 (low p.argument.toNat 2)=p.argument := by
    rw [show low p.argument.toNat 2=p.argument.toNat from Nat.mod_eq_of_lt small]
    exact BitVec.ofNat_toNat 34 p.argument
  have w : replyWidth op 0 p.argument.toNat=some 2 := by
    simp [replyWidth,a,b,c,d,show arithKind op=some .cmp from K]
  have f : finish p=.reply {p with race:=0,outcome:=0} := by
    unfold finish
    change (if p.fault != 0 then _ else if op==acquire then _ else
      match replyWidth op 0 p.argument.toNat with
      | none => fault true
      | some w => .reply (cropped {p with race:=0,outcome:=0} w))=_
    simp [ok,a,w,cropped,arg]
  refine ⟨f,?_⟩
  rw [f]
  have bound : ¬ op≥413 := by unfold op; omega
  simp [BStarLongCommand.bind,ok,show ¬p.opcode.toNat≥413 from bound,
    show replyWidth p.opcode.toNat 0 p.argument.toNat=some 2 from w,cropped,arg]

/-- At the last chronological significant CMP visit, the accepted
compiler's comparison is exactly the adapted physical scalar. -/
theorem sweep_receipt {r : Nat} {geom : Fin r → LongGeometry} {old updated : Fin r → BitVec LW}
    {i a b : Nat} {tokens : Nat → Payload} (H : DigitSweep geom old updated i (.cmp a b) tokens)
    (ha : WordSlot a) (hb : WordSlot b) (init : BStarPhysicalWordSem.arg tokens 0=cmpPack true false) :
    let left := val (readWord old a ha)
    let right := val (readWord old b hb)
    accepted (BStarPhysicalWordSem.arg tokens r)=cmpCode left right ∧ updated=old := by
  obtain ⟨hw,h⟩ := BStarPhysicalCmpSem.physical_cmp_word H ha hb init
  dsimp only
  rw [hw,physical_accept]
  exact ⟨rfl,h⟩

#print axioms sweep_receipt
#print axioms terminal_cmp

/-- The leading alias of this receipt uses the new physical scalar,
never the old packed scalar at the same address. Rest of alias run is
left to the literal allocator, with the accepted Boolean value stored
on its own SSA index. -/
theorem receipt_eq (x : BitVec LW) (i a b : Nat) (tail : List Code) :
    aliases x (i+1) (.cmpEq i::tail) [(i,cmpPack (decide (a=b)) (decide (a<b)))] =
      aliases x (i+1+1) tail
        [(i+1,(decide (cmpCode a b=1)).toNat),(i,cmpPack (decide (a=b)) (decide (a<b)))] := by
  have P := (pending_projections x i _ a b (pending_head x i _ [])).1
  simp only [aliases,P]

theorem receipt_lt (x : BitVec LW) (i a b : Nat) (tail : List Code) :
    aliases x (i+1) (.cmpLt i::tail) [(i,cmpPack (decide (a=b)) (decide (a<b)))] =
      aliases x (i+1+1) tail
        [(i+1,(decide (cmpCode a b=2)).toNat),(i,cmpPack (decide (a=b)) (decide (a<b)))] := by
  have P := (pending_projections x i _ a b (pending_head x i _ [])).2
  simp only [aliases,P]

def physical : Code → Bool
  | .header _ _ | .bconst _ | .cmpEq _ | .cmpLt _ => false
  | _ => true

def isCmp : Code → Bool
  | .cmp _ _ => true
  | _ => false

def operands : Code → List Nat
  | .maskB a | .shl3 a | .cmpEq a | .cmpLt a | .not a | .scan5 a | .phaseEq a _ => [a]
  | .add a b | .sub a b | .cmp a b | .and a b | .or a b => [a,b]
  | .mux q a b | .bmux q a b => [q,a,b]
  | _ => []

private def kindAt (i : Nat) : Bool :=
  ((get i).map isCmp).getD false

/-- Every raw CMP operand reference is an immediate alias of the
same comparison; no later physical tour or unrelated alias reads it. -/
def receiptOK (j : Nat) : Bool :=
  match get j with
  | some (.cmpEq i) | some (.cmpLt i) => (j==i+1) && kindAt i
  | some c => (operands c).all (fun i => !(kindAt i))
  | none => false

private theorem receipt_check : (List.range 474).all receiptOK=true := by
  decide +kernel

theorem receipt_index {j : Nat} (hj : j<474) : receiptOK j=true :=
  List.all_eq_true.mp receipt_check j (List.mem_range.mpr hj)

theorem physical_table : tourNodes = (List.range 474).filter
    (fun i => ((get i).map physical).getD false) := by
  decide +kernel

def isCmpConsumer : Code → Bool
  | .cmpEq _ | .cmpLt _ => true
  | _ => false

theorem cmp_consumers_count :
    ((List.range 474).filter (fun i => ((get i).map isCmpConsumer).getD false)).length=50 := by
  decide +kernel

theorem exports_no_raw_cmp :
    ([BStarLongSignatures.needIx]++outDigits0++outDigits1++outHeaders0++outHeaders1).all
      (fun i => !(kindAt i))=true := by
  decide +kernel

#print axioms receipt_index
#print axioms physical_table
#print axioms cmp_consumers_count
#print axioms exports_no_raw_cmp

theorem cmp_alias_index {j i : Nat} (hj : j<474) (lt : Bool)
    (E : get j=some (if lt then .cmpLt i else .cmpEq i)) :
    j=i+1 ∧ ∃ a b, get i=some (.cmp a b) := by
  have H := receipt_index hj
  have A : (j==i+1) && kindAt i=true := by
    cases lt <;> simpa [receiptOK,E] using H
  obtain ⟨J,K⟩ := Bool.and_eq_true_iff.mp A
  refine ⟨beq_iff_eq.mp J,?_⟩
  unfold kindAt at K
  cases G : get i with
  | none => simp [G] at K
  | some c =>
    cases c <;> simp [G,isCmp] at K
    exact ⟨_,_,rfl⟩

/-- Literal file-accept patch on a comparison receipt, before the
next physical operation. The first same-receipt alias is assigned the
accepted compiler Boolean, using the pending result rather than any
old file value. The physical CMP slot retains its native encoding. -/
theorem actual_receipt (x : BitVec LW) (physical i ra rb a b : Nat) (p : Payload) (lt : Bool)
    (N : nodeOf physical=some i) (M : get i=some (.cmp ra rb))
    (Ali : get (i+1)=some (if lt then .cmpLt i else .cmpEq i))
    (next : physical<407)
    (H : p.argument.toNat=cmpPack (decide (a=b)) (decide (a<b))) :
    acceptFile x physical p=
      let q := cmpPack (decide (a=b)) (decide (a<b))
      let v := (decide (cmpCode a b=if lt then 2 else 1)).toNat
      let ys := aliases x (i+1+1) (literal.drop (i+1+1)) [(i+1,v),(i,q)]
      (BStarLongOutgoing.fuse (ys.reverse.map (fun (j,z) => writeScalar j z))).compose
        (BStarLongDoor.schedule (physical+1)) := by
  have bound : i+1<literal.length := by
    exact (List.getElem?_eq_some_iff.mp Ali).choose
  have drop : literal.drop (i+1) =
      (if lt then .cmpLt i else .cmpEq i)::literal.drop (i+1+1) := by
    rw [List.drop_eq_getElem_cons bound]
    have Q := Ali
    unfold BStarLongArithmetic.get at Q
    rw [List.getElem?_eq_getElem bound] at Q
    rw [Option.some.inj Q]
  simp only [acceptFile,N,M,nodeResult,Option.toList,List.map_cons,List.map_nil,if_pos next,H,drop]
  cases lt
  · rw [show (if false then .cmpLt i else .cmpEq i)=Code.cmpEq i from rfl,receipt_eq]; rfl
  · rw [show (if true then .cmpLt i else .cmpEq i)=Code.cmpLt i from rfl,receipt_lt]; rfl

#print axioms actual_receipt
end L4.BStarCmpReceipt
