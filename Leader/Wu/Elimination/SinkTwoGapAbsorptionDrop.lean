import Leader.Wu.Elimination.SinkTwoGapEntranceBellman

set_option autoImplicit false

open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption LDSinkGapDoneInvariant
  LDSinkGapBlockedPreStep LDSinkGapServiceRank LDTwoGapFrame
open Classical
open LDSinkTwoGapNoResetKernel
open FiniteUniformStoppingTree

namespace LDSinkTwoGapEntrance

variable {n ψ : Nat}

/-- Correct raw absorption-drop statement.  `GapBlocked` supplies exactly the
missing "the absorbed position-1 shot is the top/only remaining attack bullet"
fact required by `gapWC_blocked_victim_lt`. -/
theorem entranceAbsorptionResidual_of_blocked
    (hψ : ψ > 0) (F : TwoGapFrame n) :
    ∀ (x : AState n ψ) (e : Fin n),
      GapBlocked F.attack x.conf →
      GapInvariant hψ F.attack x.conf →
      attemptStepRaw hψ F x e = .failure →
        R F
            (advanceAState F x (attemptStepConf hψ F x e)) <
          R F x := by
  classical
  intro x e hb hi hf
  have hfail := (attemptStepRaw_failure_iff hψ F x e).1 hf
  rcases hfail.2 with ⟨hparked, he, _habs⟩
  subst e
  have hw :
      W F (attemptStepConf hψ F x (F.attack.pos 0)) < W F x.conf := by
    rw [attemptStepConf_eq_sinkStepC]
    simpa only [W] using
      (LDSinkGapServiceRank.gapWC_blocked_victim_lt
        hψ F.attack x.conf hb hi)
  simpa [R, advanceAState, advanceAPhase, hparked] using
    (Nat.add_lt_add_left hw (1 + phaseDebtA F .parked))

#print axioms LDSinkTwoGapEntrance.entranceAbsorptionResidual_of_blocked

end LDSinkTwoGapEntrance
