import Leader.PPL.MainTheorem.ReachCPBPadded
import Leader.PPL.ReachCPB.MismatchHistNoNewFresh
import Leader.PPL.ReachCPB.MismatchCompletionHistPhase

/-!
# Theorem 1, L16: reduction to the new-fresh-completion exclusion

The lineage-history producer is proved on main
(`lemma16MismatchLineageHistoryProducer_proved`), so the mismatch witness
spec needs only `Lemma16MismatchHistNewFreshForcesCPB` (a genuinely new
selected fresh completion on a non-CPB canonical step forces CPB).  The
canonical live row (`Lemma16PostEpochFreshLiveStepGeomLastCanon`) is not
consumed by this chain.
-/

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false

theorem lemma16MismatchWitnessCappedSpec_of_newFreshForcesCPB
    (hNoNew : Lemma16MismatchHistNewFreshForcesCPB) :
    Lemma16MismatchWitnessCappedSpec :=
  lemma16MismatchCompletionHistToWitness_proved
    lemma16MismatchLineageHistoryProducer_proved
    (lemma16MismatchCompletionStepSpecHist_closed_of_newFreshForcesCPB
      hNoNew)

end PPL.Convergence.ReachCPB

namespace PPL

theorem theorem1L16PaddedBound_of_newFreshForcesCPB_core
    (hNoNew :
      PPL.Convergence.ReachCPB.Lemma16MismatchHistNewFreshForcesCPB)
    (hcore : PPL.lemma4_deterministic_core) :
    Theorem1L16PaddedBound :=
  theorem1L16PaddedBound_of_mismatchWitness_core
    (PPL.Convergence.ReachCPB.lemma16MismatchWitnessCappedSpec_of_newFreshForcesCPB
      hNoNew)
    hcore

end PPL

#print axioms PPL.Convergence.ReachCPB.lemma16MismatchWitnessCappedSpec_of_newFreshForcesCPB
#print axioms PPL.theorem1L16PaddedBound_of_newFreshForcesCPB_core
