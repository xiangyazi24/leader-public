import Leader.Wu.Safety.ReversedPathWriterView
import Leader.Wu.Safety.ReversedPathWriterPrepare
import Leader.Wu.Safety.ReversedPathWriterAfterPrepare

set_option autoImplicit false
set_option Elab.async false

namespace ZZSafeN4WriterComposeCoreGPT

open PPLL ZZSafeN4WriterViewGPT

/-- The complete WRITE_SEQ pipeline frames every field recorded by
`WriterProtectedView`. -/
theorem writeSeq_view (l r : AgentState 2) :
    pairView (writeSeq hpsi2 l r) = pairView (l, r) := by
  rw [writeSeq_eq_afterPrepare]
  exact
    (ZZSafeN4WriterAfterGPT.writeSeqAfterPrepare_view
      (writeSeqThroughPrepare hpsi2 l r).1
      (writeSeqThroughPrepare hpsi2 l r).2).trans
      (ZZSafeN4WriterPrepareGPT.writeSeqThroughPrepare_view l r)

end ZZSafeN4WriterComposeCoreGPT

#print axioms ZZSafeN4WriterComposeCoreGPT.writeSeq_view
