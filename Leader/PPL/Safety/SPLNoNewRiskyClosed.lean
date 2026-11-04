import Leader.PPL.Safety.SPLNoNewRiskyInitiator
import Leader.PPL.Safety.SPLNoNewRiskyResponder
import Leader.PPL.Safety.SPLTokenResidualRoute

namespace PPL.Safety.SPL

set_option autoImplicit false

/--
No new risky token after one interaction from an SPL configuration: the
initiator and responder site rows close the selected-pair remainder, and every
other site is a literal frame (`splNoNewRisky_of_selectedPair`).
-/
theorem splNoNewRiskySelectedPair_proved : SPLNoNewRiskySelectedPair :=
  splNoNewRiskySelectedPair_of_siteRows
    splNoNewRiskySelectedInitiatorRow_proved
    splNoNewRiskySelectedResponderRow_proved

/-- The no-new-risky row of the SPL Algorithm 2/3 token residual. -/
theorem splAlgorithm23NoNewRiskyRow_proved : SPLAlgorithm23NoNewRiskyRow :=
  splNoNewRiskySelectedPair_proved

end PPL.Safety.SPL

#print axioms PPL.Safety.SPL.splNoNewRiskySelectedPair_proved
#print axioms PPL.Safety.SPL.splAlgorithm23NoNewRiskyRow_proved
