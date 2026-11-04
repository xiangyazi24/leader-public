import Leader.PPL.Safety.SPLWhiteOldImageInitiatorMovedRightSemantic
import Leader.PPL.Safety.SPLWhiteOldImageResponderSemantic
import Leader.PPL.Safety.SPLBlackCorrectness
import Leader.PPL.Safety.SPLNoNewRiskyClosed
import Leader.PPL.Safety.SPLPersistenceClosed
import Leader.PPL.MainTheorem.Skeleton

/-!
# Algorithm 2/3 white correctness row and the SPL token residual, closed

The white old-image row follows from its two semantic seams; the white
fresh-birth row is proved in `SPLWhiteCorrectnessRoute`. With the black row and
the no-new-risky row, this closes `SPLAlgorithm23TokenResidual`.
-/

namespace PPL.Safety.SPL

set_option autoImplicit false

/-- White token correctness row of the SPL safety argument. -/
theorem splAlgorithm23WhiteCorrectnessRow_proved :
    SPLAlgorithm23WhiteCorrectnessRow :=
  splAlgorithm23WhiteCorrectnessRow_of_semanticSeams
    splWhiteOldImageInitiatorMovedRightSemanticRow_proved
    splWhiteOldImageResponderSemanticRow_proved

/-- The only open SPL Algorithm-2/3 token residual, now proved. -/
theorem splAlgorithm23TokenResidual_proved :
    SPLAlgorithm23TokenResidual :=
  splAlgorithm23TokenResidual_proved_of_rows
    splAlgorithm23NoNewRiskyRow_proved
    splAlgorithm23BlackCorrectnessRow_proved
    splAlgorithm23WhiteCorrectnessRow_proved

/-- The local one-step SPL closure property, unconditionally. -/
theorem splLocalStepProp_proved :
    SPLLocalStepProp :=
  splLocalStep_of_alg23
    (splAlgorithm23_of_tokenResidual
      splAlgorithm23TokenResidual_proved)

end PPL.Safety.SPL

namespace PPL

set_option autoImplicit false

/-- Theorem 1 (a), safety: every SPL configuration is safe for the output map. -/
theorem theorem1SPL_isSafe_proved
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hSPL : SPL ring C) :
    PopulationProtocol.IsSafe
      (protocol psi kappa)
      ring C PPL.Safety.SPL.output :=
  theorem1SPL_isSafe_of_local
    PPL.Safety.SPL.splLocalStepProp_proved
    hn3 hpsi ring C hSPL

end PPL

#print axioms PPL.Safety.SPL.splAlgorithm23WhiteCorrectnessRow_proved
#print axioms PPL.Safety.SPL.splAlgorithm23TokenResidual_proved
#print axioms PPL.Safety.SPL.splLocalStepProp_proved
#print axioms PPL.theorem1SPL_isSafe_proved
