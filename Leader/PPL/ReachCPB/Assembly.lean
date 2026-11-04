import Leader.PPL.ReachCPB.ForcingCapped
import Leader.PPL.ReachCPB.ModeCapped
import Leader.PPL.ReachCPB.MismatchCapped

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false

/-!
The eight remaining premises and their source definitions are:

* `Lemma16DetectPersistenceCappedStepSpec` —
  `Leader/PPL/ReachCPB/ForcingCapped.lean:29`.
* `Lemma16DistForcingCappedStepSpec` —
  `Leader/PPL/ReachCPB/ForcingCapped.lean:48`.
* `Lemma16LastForcingCappedStepSpec` —
  `Leader/PPL/ReachCPB/ForcingCapped.lean:85`.
* `ModeScrubOneStepSpec` —
  `Leader/PPL/ReachCPB/ModeCapped.lean:147`.
* `Lemma16MismatchCompletionStepSpec` —
  `Leader/PPL/ReachCPB/MismatchCapped.lean:433`.
* `Lemma16CdGeometryPairStepSpec` —
  `Leader/PPL/ReachCPB/MismatchCapped.lean:739`.
* `Lemma16BulletSweepNatBound` —
  `Leader/PPL/ReachCPB/WordBound.lean:262`.
* `PPL.lemma4_deterministic_core` —
  `Leader/PPL/TokenCorrectness/Ghost.lean:560`.
-/

/-- Assemble the capped Lemma-16 word bound from six one-interaction
specifications, the bullet-sweep bound, and the deterministic Lemma-4 core. -/
theorem lemma16_wordBound_of_steps
    (hDetect : Lemma16DetectPersistenceCappedStepSpec)
    (hDist : Lemma16DistForcingCappedStepSpec)
    (hLast : Lemma16LastForcingCappedStepSpec)
    (hMode : ModeScrubOneStepSpec)
    (hMismatch : Lemma16MismatchCompletionStepSpec)
    (hGeometry : Lemma16CdGeometryPairStepSpec)
    (h15 : Lemma16BulletSweepNatBound)
    (hcore : PPL.lemma4_deterministic_core)
    {n psi kappa modeC : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hc : 6 <= modeC)
    (hkappa : kappa = 8 * modeC * psi)
    (hnpow : n <= 2 ^ psi)
    (hpsiK : psi <= lemma16K n)
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    Lemma16WordBound ring C := by
  exact lemma16_wordBound_capped
    h15
    (lemma16DetectPersistenceCapped hDetect)
    (lemma16ModeCappedReachCount hMode)
    (lemma16DistForcingCapped hDist)
    (lemma16LastForcingCapped hLast)
    (lemma16MismatchWitnessCapped hMismatch)
    (lemma16CdTraceUntilSuccess_proved hGeometry)
    hcore hn3 hpsi hc hkappa hnpow hpsiK ring C

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16_wordBound_of_steps
