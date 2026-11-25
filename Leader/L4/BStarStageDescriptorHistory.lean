import Leader.L4.BStarFinalCandidate

namespace L4.BStarStageDescriptorHistory
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongDoor BStarLongToken BStarLongCommand
open BStarFinalCandidate BStarLongArithmetic

def descOfStage (p : Payload) : Option BStarLongPublication.Descriptor :=
  BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2^18))

/-- Actual ISSUE reads the old seven descriptor bits exactly, and the
eighteen header bits occupy a disjoint low field in the tour payload. -/
theorem stage_packet (x : BitVec LW) (arg : Nat) {p : Payload}
    (A : initial stageOp x=some arg) (P : forward stageOp arg=.forward p) :
    descOfStage p=BStarLongPublication.decode (sourceDescriptor.read x) := by
  classical
  have D : BitVec.ofNat 7 (sourceDescriptor.read x).toNat=sourceDescriptor.read x := by simp
  have C : initial stageOp x =
      match BStarLongPublication.decode (sourceDescriptor.read x) with
      | none => none
      | some _ => some ((sourceDescriptor.read x).toNat*2^18+(candidateHeaders.read x).toNat) := by
    simp [initial,stageOp,acquire,copyLoad,sealOp,commitOp,D] <;> rfl
  obtain ⟨_,_,E⟩ : ∃ d,BStarLongPublication.decode (sourceDescriptor.read x)=some d ∧
      arg=(sourceDescriptor.read x).toNat*2^18+(candidateHeaders.read x).toNat := by
    rw [C] at A
    cases Z : BStarLongPublication.decode (sourceDescriptor.read x) with
    | none => rw [Z] at A; contradiction
    | some d => rw [Z] at A; exact ⟨d,rfl,(Option.some.inj A).symm⟩
  have Q : arg<2^34 := by
    have H₁ := (sourceDescriptor.read x).isLt
    have H₂ := (candidateHeaders.read x).isLt
    change (sourceDescriptor.read x).toNat<128 at H₁
    change (candidateHeaders.read x).toNat<262144 at H₂
    omega
  have low : (candidateHeaders.read x).toNat<2^18 := (candidateHeaders.read x).isLt
  have div : arg/2^18 = (sourceDescriptor.read x).toNat := by
    omega
  have Pay : p.argument=BitVec.ofNat 34 arg := congrArg Payload.argument (Token.forward.inj P).symm
  unfold descOfStage
  rw [Pay,BitVec.toNat_ofNat,Nat.mod_eq_of_lt Q,div,D]

/-- Directly after the checked final arithmetic receipt, the literal
next STAGE payload protects the captured *center* selector, not a new
selector sample. Extending the equality across the gap and downstream
tour is a separate chronological framing theorem. -/
theorem final_stage_descriptor (old : BitVec LW) (r : Payload)
    (h : ((capturedSelector 1).read old).toNat<3) (arg : Nat) (p : Payload)
    (A : initial stageOp ((acceptFile old lastOp r).apply old)=some arg)
    (P : forward stageOp arg=.forward p) :
    descOfStage p=some (finalDesc old h) ∧
      (finalDesc old h).old.val=((capturedSelector 1).read old).toNat := by
  refine ⟨?_,rfl⟩
  rw [stage_packet ((acceptFile old lastOp r).apply old) arg A P,
    (final_fields old r h).1,decode_final old h]

#print axioms final_stage_descriptor
end L4.BStarStageDescriptorHistory
