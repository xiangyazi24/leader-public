import Leader.L4.BStarFreshNumericConsume

/-! Numeric ISSUE cannot take the malformed-argument reset on a legal
captured center selector. In particular mux operands are ordinary
bit-vector reads; only their static file address needs checking. -/
namespace L4.BStarNumericIssueDefined
open AllSizeProtocol BStarTrace BStarLongWork BStarLongCommand BStarLongDoor BStarLongLayout BStarLongSignatures

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem mux_coverage :
    ((List.range 408).all fun op =>
      if arithKind op==some .mux then (muxInputs.find? fun e=>e.1==op).isSome else true) = true := by
  decide

theorem initial_defined (old : BitVec LW) (op : Nat) (lo : 13≤op) (hi : op<408)
    (center : ((capturedSelector 1).read old).toNat<3) :
    (initial op old).isSome=true := by
  have ac : op≠acquire := by unfold acquire; omega
  have ld : op≠copyLoad := by unfold copyLoad; omega
  have st : op≠stageOp := by unfold stageOp; omega
  have sl : op≠sealOp := by unfold sealOp; omega
  have co : op≠commitOp := by unfold commitOp; omega
  unfold initial
  simp only [beq_iff_eq,ac,ld,st,sl,co,Bool.or_eq_true,false_or,if_false]
  cases O : arithKind op with
  | none => rfl
  | some k =>
    cases k <;> try rfl
    case centerLoad =>
      have C : ((capturedSelector 1).read old).toNat≠3 := by omega
      simp [C]
    case mux =>
      have look := (List.all_eq_true.mp mux_coverage) op (List.mem_range.mpr hi)
      simpa [scalarMux,O] using look

#print axioms initial_defined
end L4.BStarNumericIssueDefined
