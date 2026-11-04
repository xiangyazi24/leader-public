import Leader.PPL.ReachCPB.BulletSweepClosed
import Leader.PPL.ReachCPB.ModeScrubStep
import Leader.PPL.MainTheorem.Statement
import Leader.PPL.MainTheorem.Whp
import Leader.PPL.ReachCPB.CdGeometryPairStep
import Leader.PPL.ReachCPB.LastPairRow
import Leader.PPL.ReachCPB.StepDetectPersistence
import Leader.PPL.ReachCPB.StepDist
import Leader.PPL.MainTheorem.GeneralFixedCut

/-!
# Theorem 1, L16 padded bound from the mismatch witness and the Lemma 4 core

P_PL Theorem 1 cleanup, phase 2: the former `Theorem1L16PaddedReduced` is folded in.  Its imports
are now taken directly (only those this file's declarations use); its one
declaration, `theorem1L16PaddedBound_of_mismatch_core`, served only the old
psi <= log2 n + 1 route and moved to `Leader/Superseded/Theorem1LogWindow/`.
Step 6a: the bound below is the log-window special case of
`PPL.Theorem1General.theorem1L16PaddedBound_of_mismatchWitness_core`
(`Leader/PPL/MainTheorem/GeneralFixedCut.lean`); the private fixed-cut counting
helpers that used to be copied here live there.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-- Theorem 1, L16 padded bound (log window) from the capped mismatch witness
and the Lemma 4 deterministic core. -/
theorem theorem1L16PaddedBound_of_mismatchWitness_core
    (hMismatchCanon :
      PPL.Convergence.ReachCPB.Lemma16MismatchWitnessCappedSpec)
    (hcore : PPL.lemma4_deterministic_core) :
    Theorem1L16PaddedBound := by
  intro n psi hn3 hpsi hnpow _ ring C0
  exact
    PPL.Theorem1General.theorem1L16PaddedBound_of_mismatchWitness_core
      hMismatchCanon hcore hn3 hpsi hnpow ring C0

end PPL

#print axioms PPL.theorem1L16PaddedBound_of_mismatchWitness_core
