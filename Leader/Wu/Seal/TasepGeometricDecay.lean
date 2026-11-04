import Leader.Wu.Seal.TasepOneStepContraction

namespace PPLLCompleteMultiLeaderCleanup
namespace SealTasepGeometricDecay

open PPLL PPLLResearchFormulation PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepTasepFiniteTimeSol
open SealJohnsonEnergyIdentity SealTasepL2Contraction

set_option autoImplicit false
set_option Elab.async false

private theorem iterCentered {n : Nat} (ring : DirectedRing n) (hn : 1 < n)
    (k : Nat) (f : SealObs n) (hzero : sealSliceIntSum k f = 0) :
    ∀ t : Nat, sealSliceIntSum k (sealPStarNumeratorIter ring k f t) = 0 := by
  intro t
  induction t with
  | zero => simpa [sealPStarNumeratorIter] using hzero
  | succ t ih =>
      simp only [sealPStarNumeratorIter]
      rw [sealPStarNumerator_sum ring hn k (sealPStarNumeratorIter ring k f t), ih]
      simp

/-- Exact denominator-cleared geometric L2 decay for the seal TASEP adjoint. -/
theorem sealTasepGeometricL2Decay {n : Nat} (ring : DirectedRing n) (k : Nat) :
    SealTasepGeometricL2DecayAt ring k := by
  intro hn hP f hzero t
  have hz := iterCentered ring hn k f hzero
  induction t with
  | zero => simp [sealPStarNumeratorIter]
  | succ t ih =>
      have hs := sealTasepGeometricL2OneStep ring hn k hP
        (sealPStarNumeratorIter ring k f t) (hz t)
      have hs' :
          (4 * n ^ 3) *
              sealAllPairsSquaredEnergy k (sealPStarNumeratorIter ring k f (t + 1)) <=
            (n ^ 2 * (4 * n ^ 3 - 1)) *
              sealAllPairsSquaredEnergy k (sealPStarNumeratorIter ring k f t) := by
        simpa only [sealPStarNumeratorIter] using hs
      have hstep :
          (4 * n ^ 3) ^ t *
              ((4 * n ^ 3) *
                sealAllPairsSquaredEnergy k (sealPStarNumeratorIter ring k f (t + 1))) <=
            (4 * n ^ 3) ^ t *
              ((n ^ 2 * (4 * n ^ 3 - 1)) *
                sealAllPairsSquaredEnergy k (sealPStarNumeratorIter ring k f t)) :=
        Nat.mul_le_mul_left ((4 * n ^ 3) ^ t) hs'
      have hiter :
          (n ^ 2 * (4 * n ^ 3 - 1)) *
              ((4 * n ^ 3) ^ t *
                sealAllPairsSquaredEnergy k (sealPStarNumeratorIter ring k f t)) <=
            (n ^ 2 * (4 * n ^ 3 - 1)) *
              ((n ^ 2 * (4 * n ^ 3 - 1)) ^ t *
                sealAllPairsSquaredEnergy k f) :=
        Nat.mul_le_mul_left (n ^ 2 * (4 * n ^ 3 - 1)) ih
      calc
        (4 * n ^ 3) ^ (t + 1) *
            sealAllPairsSquaredEnergy k (sealPStarNumeratorIter ring k f (t + 1)) =
          (4 * n ^ 3) ^ t *
            ((4 * n ^ 3) *
              sealAllPairsSquaredEnergy k (sealPStarNumeratorIter ring k f (t + 1))) := by
          rw [Nat.pow_succ]
          ac_rfl
        _ <= (4 * n ^ 3) ^ t *
            ((n ^ 2 * (4 * n ^ 3 - 1)) *
              sealAllPairsSquaredEnergy k (sealPStarNumeratorIter ring k f t)) := hstep
        _ = (n ^ 2 * (4 * n ^ 3 - 1)) *
            ((4 * n ^ 3) ^ t *
              sealAllPairsSquaredEnergy k (sealPStarNumeratorIter ring k f t)) := by ac_rfl
        _ <= (n ^ 2 * (4 * n ^ 3 - 1)) *
            ((n ^ 2 * (4 * n ^ 3 - 1)) ^ t *
              sealAllPairsSquaredEnergy k f) := hiter
        _ = (n ^ 2 * (4 * n ^ 3 - 1)) ^ (t + 1) *
            sealAllPairsSquaredEnergy k f := by
          rw [Nat.pow_succ (n ^ 2 * (4 * n ^ 3 - 1)) t]
          ac_rfl

end SealTasepGeometricDecay
end PPLLCompleteMultiLeaderCleanup

#print axioms PPLLCompleteMultiLeaderCleanup.SealTasepGeometricDecay.sealTasepGeometricL2Decay
