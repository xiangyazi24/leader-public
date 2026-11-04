import Leader.PPL.Safety.SPLFieldFrame
import Leader.PPL.TokenCorrectness.PersistenceLeftMirror
import Leader.PPL.TokenCorrectness.PersistenceLeftRow
import Leader.PPL.TokenCorrectness.PersistenceRightMirror

namespace PPL.Safety.SPL

set_option autoImplicit false

/-!
Both Remark-2 directional selected rows are now unconditional, and the
Algorithm-2/3 field frame is proved.  The S_PL Algorithm-2/3 step property
therefore needs only the token residual.
-/

theorem remark2LeftSelectedRow_closed :
    PPL.Remark2LeftSelectedRow :=
  PPL.remark2LeftSelectedRow_of_shape
    PPL.remark2LeftSelectedShape_proved

theorem remark2_one_step_unique_closedRows :
    PPL.remark2_one_step_unique :=
  PPL.remark2_one_step_unique_closed
    PPL.remark2RightSelectedRow_closed
    remark2LeftSelectedRow_closed

theorem splAlgorithm23_of_tokenResidual
    (htoken : SPLAlgorithm23TokenResidual) :
    SPLAlgorithm23StepProp :=
  splAlgorithm23_of_residuals
    splAlgorithm23FieldFrameResidual_proved
    htoken
    PPL.remark2RightSelectedRow_closed
    remark2LeftSelectedRow_closed

end PPL.Safety.SPL

#print axioms PPL.Safety.SPL.remark2LeftSelectedRow_closed
#print axioms PPL.Safety.SPL.remark2_one_step_unique_closedRows
#print axioms PPL.Safety.SPL.splAlgorithm23_of_tokenResidual
