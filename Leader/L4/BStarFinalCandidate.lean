import Leader.L4.BStarStageIssue

/-! The final source receipt binds its descriptor to the old captured
center selector. This records the exact source boundary before
STAGE; correctness of the whole incoming register file is separate. -/
namespace L4.BStarFinalCandidate
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongArithmetic BStarLongDoor BStarLongSignatures
open L4.Compiler.Native

def lastNode : Nat := 473
def lastOp : Nat := 407

theorem last_node : nodeOf lastOp=some lastNode := by decide +kernel
theorem last_code : get lastNode=some (.bmux 137 5 472) := by decide +kernel

def finalChoice (old : BitVec LW) : Bool := source old BStarLongSignatures.needIx==1

def finalDesc (old : BitVec LW) (h : ((capturedSelector 1).read old).toNat<3) :
    BStarLongPublication.Descriptor :=
  let s := ((capturedSelector 1).read old).toNat
  ⟨⟨s,h⟩,⟨(s+1)%3,by omega⟩,⟨(s+2)%3,by omega⟩,finalChoice old⟩

theorem final_desc_valid (old : BitVec LW) (h : ((capturedSelector 1).read old).toNat<3) :
    (finalDesc old h).valid=true := by simp [finalDesc,BStarLongPublication.Descriptor.valid]

def finalValues (old : BitVec LW) : Pending :=
  ((nodeResult old 0 (.bmux 137 5 472)).toList.map (fun v => (lastNode,v)))

def finalHeaders (old : BitVec LW) : BitVec 18 :=
  BitVec.ofNat 18 ((outHeaders0++outHeaders1).foldl
    (fun a j => a*2+newest old (finalValues old) j) 0)

theorem final_need (old : BitVec LW) :
    (newest old (finalValues old) BStarLongSignatures.needIx==1)=finalChoice old := by
  unfold finalValues nodeResult finalChoice newest lastNode BStarLongSignatures.needIx
  simp

def finalEffect (old : BitVec LW) (h : ((capturedSelector 1).read old).toNat<3) : Patch LW :=
  let ws := BStarLongOutgoing.fuse
    ((finalValues old).reverse.map fun (i,y) => writeScalar i y)
  let q := ((sourceDescriptor.assign (BStarLongPublication.encode (finalDesc old h))).compose
    (need.assign (BitVec.ofBool (finalChoice old)))).compose (candidateHeaders.assign (finalHeaders old))
  (ws.compose q).compose (schedule BStarLongCommand.stageOp)

theorem final_receipt_exact (old : BitVec LW) (p : Payload)
    (h : ((capturedSelector 1).read old).toNat<3) :
    acceptFile old lastOp p=finalEffect old h := by
  have drop : literal.drop (lastNode+1)=[] := by
    apply List.drop_eq_nil_of_le
    rw [literal_length]
    decide
  simp only [acceptFile,last_node,last_code,drop,aliases,show ¬lastOp<407 by decide,if_false,dif_pos h]
  change _ = finalEffect old h
  unfold finalEffect finalDesc finalHeaders
  have E : nodeResult old p.argument.toNat (.bmux 137 5 472)=
      nodeResult old 0 (.bmux 137 5 472) := rfl
  rw [E]
  have need := final_need old
  change (newest old ((nodeResult old 0 (.bmux 137 5 472)).toList.map
    (fun v => (lastNode,v))) BStarLongSignatures.needIx==1)=finalChoice old at need
  simp only [need,finalValues]

theorem final_receipt_refuses_spare (old : BitVec LW) (p : Payload)
    (h : ¬((capturedSelector 1).read old).toNat<3) :
    acceptFile old lastOp p=faultRestart := by
  simp only [acceptFile,last_node,last_code,show ¬lastOp<407 by decide,if_false,dif_neg h]

private theorem schedule_frames {n : Nat} (f : Field LW n)
    (lo : 1764≤f.offset) (hi : f.offset+n≤2195) (x : BitVec LW) :
    f.read ((schedule BStarLongCommand.stageOp).apply x)=f.read x := by
  unfold schedule setToken
  simp only [Patch.compose_apply]
  rw [Field.read_other_assign f (kField 0) _ _ (.inr lo),
    Field.read_other_assign f ctrlOp _ _ (.inl hi),
    Field.read_other_assign f ctrlPhase _ _ (.inl (Nat.le_trans hi (by decide)))]

/-- Exact words installed for the next STAGE, including the descriptor
bank identities from the old capture file (not a new bank read). -/
theorem final_fields (old : BitVec LW) (p : Payload)
    (h : ((capturedSelector 1).read old).toNat<3) :
    let fresh := (acceptFile old lastOp p).apply old
    sourceDescriptor.read fresh=BStarLongPublication.encode (finalDesc old h) ∧
      need.read fresh=BitVec.ofBool (finalChoice old) ∧ candidateHeaders.read fresh=finalHeaders old := by
  dsimp only
  rw [final_receipt_exact old p h]
  simp only [finalEffect,Patch.compose_apply]
  constructor
  · rw [schedule_frames sourceDescriptor (by decide) (by decide),
      Field.read_other_assign sourceDescriptor candidateHeaders _ _ (by decide),
      Field.read_other_assign sourceDescriptor need _ _ (by decide),Field.read_assign]
  constructor
  · rw [schedule_frames need (by decide) (by decide),
      Field.read_other_assign need candidateHeaders _ _ (by decide),Field.read_assign]
  · rw [schedule_frames candidateHeaders (by decide) (by decide),Field.read_assign]

private def makeDesc (s : Fin 3) (b : Bool) : BStarLongPublication.Descriptor :=
  ⟨s,⟨(s.val+1)%3,by omega⟩,⟨(s.val+2)%3,by omega⟩,b⟩

private theorem decode_make :
    ∀ (s : Fin 3) (b : Bool),
      BStarLongPublication.decode (BStarLongPublication.encode (makeDesc s b))=some (makeDesc s b) := by
  decide +kernel

theorem decode_final (old : BitVec LW) (h : ((capturedSelector 1).read old).toNat<3) :
    BStarLongPublication.decode (BStarLongPublication.encode (finalDesc old h))=some (finalDesc old h) := by
  exact decode_make ⟨((capturedSelector 1).read old).toNat,h⟩ (finalChoice old)

end L4.BStarFinalCandidate
