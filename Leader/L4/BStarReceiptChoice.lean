import Leader.L4.BStarNativeSelectorOutput
import Leader.L4.BStarBankCapture

namespace L4.BStarReceiptChoice
open BStarLongPublication BStarLongToken BStarCommitReceiptAuth BStarNativeSelectorOutput

/-- The two candidate banks are different, so any two certified receipts
selecting the same real COMMIT bank give the same native Boolean. -/
theorem receipt_bit_fixed {d : Descriptor} {bank : Fin 3} {f g : Payload}
    {o p : Nat} (V : d.valid=true)
    (F : ReceiptBank o d f bank) (G : ReceiptBank p d g bank) :
    receiptChoice d f=receiptChoice d g := by
  have U : d.b0≠d.b1 := by
    intro J
    have Y := congrArg Fin.val J
    have h := Bool.and_eq_true_iff.mp V
    have s := beq_iff_eq.mp h.1
    have t := beq_iff_eq.mp h.2
    omega
  have E := (receipt_bank F).symm.trans (receipt_bank G)
  cases L : receiptChoice d f <;> cases R : receiptChoice d g
  all_goals simp only [L,R] at E
  · rfl
  · exact (U E).elim
  · exact (U E.symm).elim
  · rfl

#print axioms receipt_bit_fixed
end L4.BStarReceiptChoice
