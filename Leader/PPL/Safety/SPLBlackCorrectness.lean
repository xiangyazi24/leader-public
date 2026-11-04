import Leader.PPL.Safety.SPLBlackOldImageInitiatorMovedRightSemantic
import Leader.PPL.Safety.SPLBlackOldImageResponderSemantic
import Leader.PPL.Safety.SPLBlackFreshBirth

/-!
# Algorithm 2/3 black correctness row, closed

The old-image row follows from its two semantic seams (initiator moved-right,
responder), both proved; the fresh-birth row is proved in
`SPLBlackFreshBirth`. Together they give the black correctness row.
-/

namespace PPL.Safety.SPL

set_option autoImplicit false

/-- Old-image black tokens stay correct across a step (Remark 2 transport). -/
theorem splAlgorithm23BlackOldImageRow_proved :
    SPLAlgorithm23BlackOldImageRow :=
  splAlgorithm23BlackOldImageRow_of_semanticSeams
    splBlackOldImageInitiatorMovedRightSemanticRow_proved
    splBlackOldImageResponderSemanticRow_proved

/-- Black token correctness row of the SPL safety argument. -/
theorem splAlgorithm23BlackCorrectnessRow_proved :
    SPLAlgorithm23BlackCorrectnessRow :=
  splAlgorithm23BlackCorrectnessRow_of_caseRows
    splAlgorithm23BlackOldImageRow_proved
    splAlgorithm23BlackFreshBirthRow_proved

end PPL.Safety.SPL

#print axioms PPL.Safety.SPL.splAlgorithm23BlackOldImageRow_proved
#print axioms PPL.Safety.SPL.splAlgorithm23BlackCorrectnessRow_proved
