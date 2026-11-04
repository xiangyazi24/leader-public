import Leader.PPL.Elim.SealedStep
import Leader.PPL.Elim.ControlRows
import Leader.PPL.Elim.CleanLiveCost
import Leader.PPL.Elim.ModerateRegime

/-!
# Wave 5: consumers of `SealedStepSpec`, discharged

`sealedStepSpec` (LDLocalSealedStep) proves the File-3 sealed step.  This file
feeds it to the File-4 product closure, the File-5 control rows, the boundary
regime, and the corrected moderate/LD(736) assembly, so none of them carries
`SealedStepSpec` as a hypothesis any more.
-/

namespace PPL.Convergence.LDLocal

set_option autoImplicit false

open K2ArbitraryElimination.FiniteAccounting

theorem twoLeaderSealed_step_proved
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (h : TwoLeaderSealed F C) (e : Fin n) :
    TaggedDeleted F (stepE ring C e) ∨
      ∃ h' : TwoLeaderSealed F (stepE ring C e), True :=
  twoLeaderSealed_step sealedStepSpec ring F C h e

theorem controlRowSpec_closed
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b) :
    ControlRowSpec sealedStepSpec F hb :=
  controlRowSpec_proved sealedStepSpec F hb

theorem boundary_ld_closed
    {n : Nat} (ring : DirectedRing n)
    (C : Config n)
    (hPB : PPL.Elim.PB ring C)
    (h2 : 2 ≤ PPL.Elim.leaderCount C)
    (F : TripleFrame ring C)
    (hb : F.b = 1) :
    ∀ T,
      costNumerator
          (stepE ring) (TaggedDeleted F) C T ≤
        n ^ T * (6 * n * (F.a + 1)) :=
  boundary_ld_sealed sealedStepSpec ring C hPB h2 F hb

/-- LD(736) now needs only the moderate attempt producer and the long/boundary
physical interface. -/
theorem ld736_costNumerator_of_producers
    (hAttempt : ModerateAttemptProducerSpec)
    (hPhysical : LongBoundaryPhysicalSpec)
    {n : Nat} (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (C : Config n)
    (hPB : PPL.Elim.PB ring C)
    (h2 : 2 ≤ PPL.Elim.leaderCount C)
    (F : TripleFrame ring C) :
    ∀ T : Nat,
      costNumerator
          (stepE ring) (TaggedDeleted F) C T ≤
        n ^ T * (736 * n * (F.a + F.b)) :=
  ld736_costNumerator_of_moderate_corrected
    (moderate_ld_corrected hAttempt) hPhysical sealedStepSpec
    hn ring C hPB h2 F

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.twoLeaderSealed_step_proved
#print axioms PPL.Convergence.LDLocal.controlRowSpec_closed
#print axioms PPL.Convergence.LDLocal.boundary_ld_closed
#print axioms PPL.Convergence.LDLocal.ld736_costNumerator_of_producers
