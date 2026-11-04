import Leader.L3.Grant.DrainWarmStageCost
import Leader.L3.Grant.DrainWarm
import Leader.L3.Small.RenewalNative
import Leader.L3.Bank.Counter
import Leader.L3.RenewalPreparationStage

/-!
# Transfer of the shared grant-drain bound to the SMALL and BANK stages

`grantDrainSharedBoundProved` bounds the expected time from any
protected source state of the canonical grant-drain model to a
grant-free state by `37 n^2`. Both reference processes refine that
model exactly on their drain domains (`sharedSmallCanonicalRefinementHolds`,
`grantDrainBankCanonicalRefinementFromProjection`). A step-exact
refinement on a forward-closed domain carries the cost bound edge
by edge (`Counter.resetClockCostLeOfStoppedSimulation`), so the single
source theorem gives both stage clocks, with no second stochastic
argument (renewal.tex:1074-1085).
-/

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.SmallRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false

/-- Generic transfer: a forward-closed domain `Inv` of a reference
process whose lifted states are protected, which the grant-drain
model refines step for step, inherits the shared `37 n^2` bound
toward any class `G` that a grant-free lift certifies. -/
theorem grantDrainStageTransfer
    {n : Nat} {ring : DirectedRing n} {X : Type}
    (M : GrantDrainModel n ring) (hM : GrantDrainSharedBound M)
    (next : X → Fin n → X)
    (lift : X → List (Fin n) → M.State)
    (Inv G : X → Prop)
    (hclosed : ∀ x e, Inv x → Inv (next x e))
    (hstep : ∀ x past e, Inv x →
      M.step (lift x past) e = lift (next x e) (e :: past))
    (hplus : ∀ x past, Inv x →
      PPlus ring (M.view (lift x past)).native)
    (hfree : ∀ x past, Inv x → M.grantFree (lift x past) → G x) :
    ∀ x, Inv x →
      UniformFirstHit.ExpectedHittingTimeAtMost next G x
        ((37 * n ^ 2 : Nat) : Rat) := by
  intro x hx
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    next G ring.hn x (37 * n ^ 2)).2
  intro T
  have hsource :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      M.step M.grantFree ring.hn (lift x []) (37 * n ^ 2)).1
      (hM (lift x []) (hplus x [] hx)) T
  have hcompare :=
    L3.Counter.resetClockCostLeOfStoppedSimulation
      next M.step G M.grantFree
      (fun y a => Inv y ∧ ∃ past, a = lift y past)
      (fun y a hr hfreeA => by
        obtain ⟨hy, past, rfl⟩ := hr
        exact hfree y past hy hfreeA)
      (fun y a e hr _ _ => by
        obtain ⟨hy, past, rfl⟩ := hr
        exact ⟨hclosed y e hy, e :: past, hstep y past e hy⟩)
      x (lift x []) ⟨hx, [], rfl⟩ T
  exact Nat.le_trans hcompare hsource

/-- SMALL sigma_B to sigma_G: the stage clock consumed by
`smallReferenceClockOfDrainAndFinish`, now proved. -/
theorem smallReferenceGrantDrainStage
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    StageReferenceGrantDrain (renewalSmallNext ring)
      (fun r => headlineRooted ring r.1 ∧
        smallReferenceSeenComplete r)
      (smallReferenceGrantFreeRootedSeen ring) := by
  have hR := sharedSmallCanonicalRefinementHolds ring hn hsmall
  exact grantDrainStageTransfer
    (grantDrainCanonicalModel ring hn
      (sharedSmallSourceFresh ring)
      (sharedSmallSourceScratchNext ring))
    (grantDrainSharedBoundProved ring hn _ _)
    (renewalSmallNext ring) sharedSmallSourceView
    (fun r => headlineRooted ring r.1 ∧ smallReferenceSeenComplete r)
    (smallReferenceGrantFreeRootedSeen ring)
    (fun r e hr =>
      ⟨smallReferenceRootedClosed ring hn r hr.1 e,
        smallReferenceSeenCompleteStep ring r e hr.2⟩)
    (fun r past e hr => hR.2 r past e hr.2)
    (fun r past hr => by
      rw [(hR.1 r past hr.2).1]
      exact hr.1.1)
    (fun r past hr hfreeA => by
      refine ⟨hr.1, hr.2, ?_⟩
      intro i
      rw [← (hR.1 r past hr.2).2.2 i]
      exact hfreeA i)

/-- BANK sigma_B to sigma_G on the rooted, inherited-authority-extinct
class: the stage clock for `renewalBankReferenceClockOfStages`. -/
theorem bankReferenceGrantDrainStage
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    StageReferenceGrantDrain
      (bankValidRootedReferenceData ring hbank).referenceNext
      (fun z => headlineRooted ring z.val.1 ∧
        InheritedAuthorityExtinct ring hbank z)
      (BankPostInheritedGrantDrain ring hbank) := by
  have hR := grantDrainBankCanonicalRefinementFromProjection ring hn hbank
  exact grantDrainStageTransfer
    (grantDrainCanonicalModel ring hn
      (bankStageDrainFresh ring hbank)
      (bankStageDrainScratchNext ring hbank))
    (grantDrainSharedBoundProved ring hn _ _)
    (bankValidRootedReferenceData ring hbank).referenceNext
    (bankStageDrainProjection ring hbank)
    (fun z => headlineRooted ring z.val.1 ∧
      InheritedAuthorityExtinct ring hbank z)
    (BankPostInheritedGrantDrain ring hbank)
    (fun z e hz =>
      ⟨bankReferenceRootedStep ring hn hbank z e hz.1,
        inheritedAuthorityExtinctStep ring hbank z hz.2 e⟩)
    (fun z past e hz => hR.2 z past e hz.2)
    (fun z past hz => by
      rw [(hR.1 z past hz.2).1]
      exact hz.1.1)
    (fun z past hz hfreeA => by
      refine ⟨⟨hz.1, ?_⟩, hz.2⟩
      intro i
      rw [← (hR.1 z past hz.2).2.2 i]
      exact hfreeA i)

/-- The BANK reference clock with R8 and R9 discharged: what remains
is the rooted start, the sigma_B producer into rooted and
InheritedAuthorityExtinct (R7), and the prepared-to-generated finish
(R10). -/
theorem renewalBankReferenceClockOfOldAndFinish {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (rooted : (bankValidRootedReferenceData ring hbank).Reference → Prop)
    (hstart : ∀ seed : RootedSeed ring,
      ¬ headlineGeneratedTarget ring seed.val →
        rooted ((bankValidRootedReferenceData ring hbank).referenceStart seed))
    (hOld : StageInheritedAuthorityExtinction
      (bankValidRootedReferenceData ring hbank).referenceNext
      rooted
      (fun z => headlineRooted ring z.val.1 ∧
        InheritedAuthorityExtinct ring hbank z)
      (ceilLogTwo n))
    (hFinish : StageReferenceGeneratedFinish
      (bankValidRootedReferenceData ring hbank).referenceNext
      (BankPreparedAtSomeRoot ring hbank)
      (bankValidRootedReferenceData ring hbank).referenceStop
      (headlineReferenceFinishRate (ceilLogTwo n))) :
    ReferenceClock ring (bankValidRootedReferenceData ring hbank)
      (renewalBankReferenceCeiling n) := by
  exact renewalBankReferenceClockOfStages ring hn hbank
    rooted
    (fun z => headlineRooted ring z.val.1 ∧
      InheritedAuthorityExtinct ring hbank z)
    (BankPostInheritedGrantDrain ring hbank)
    (BankAnyPostInheritedSingleton ring hbank)
    (BankPreparedAtSomeRoot ring hbank)
    hstart hOld
    (bankReferenceGrantDrainStage ring hn hbank)
    (bankSingletonStageWithInheritedInvariant ring hn hbank)
    (bankPreparationStageWithInheritedInvariant ring hn hbank)
    hFinish

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainStageTransfer
#print axioms L3.GrantDrainEntrance.smallReferenceGrantDrainStage
#print axioms L3.GrantDrainEntrance.bankReferenceGrantDrainStage
#print axioms L3.GrantDrainEntrance.renewalBankReferenceClockOfOldAndFinish
