import Leader.PPL.Elim.OneLeaderBoundLeaves
import Leader.PPL.Elim.AttemptLongSealedRowsLiveWait
import Leader.PPL.Elim.AttemptLongSealedRowsIncident
import Leader.PPL.Elim.AttemptLongSealedRowsRetained
import Leader.PPL.Elim.AttemptLongSealedRowsRecovery

namespace PPL.Convergence.L17

set_option autoImplicit false
set_option Elab.async false

/-- Lemma 17 (C17 = 862592), unconditional: all four long sealed
post-carrier residuals are proved. -/
theorem lemma17_wordBound_closed
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : PPL.LiteralElimConfig n)
    (hPB : PPL.Elim.PB ring C) :
    Lemma17WordBound 862592 ring C :=
  lemma17_wordBound_of_leaves
    PPL.Convergence.LDLocal.longLiveWaitPostCarrierResidual_proved
    PPL.Convergence.LDLocal.longIncidentPostCarrierResidual_proved
    PPL.Convergence.LDLocal.longRetainedPostCarrierResidual_proved
    PPL.Convergence.LDLocal.longRecoveryPostCarrierResidual_proved
    hn3 hpsi ring C hPB

end PPL.Convergence.L17

#print axioms PPL.Convergence.L17.lemma17_wordBound_closed
