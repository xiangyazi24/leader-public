import Leader.Wu.Seal.RankEpochStoppedOutcome


namespace PPLLCompleteMultiLeaderCleanup
namespace SealRankEpochFirstSubtarget


open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLSchedulerBlocks PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepHomeFrontQuotientSol
open PPartialSealSweepHomeTrapCurrentSol
open PPartialSealSweepABReadyCompositionSol
open PPartialSealSweepABGateBreakthroughSol
open PPartialSealSweepRankEpochAuditSol
open SealRankEpochStoppedOutcome


set_option autoImplicit false
set_option Elab.async false


variable {n psi kappa tau : Nat}


/-- The second stopped outcome for the first sub-target is literal Ready. -/
noncomputable def rankEpochReadyTest
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) : Bool := by
  classical
  exact decide (HomeFrontHitReady ring X)


theorem rankEpochReadyTest_spec
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) :
    rankEpochReadyTest ring X = true <-> HomeFrontHitReady ring X := by
  classical
  simp [rankEpochReadyTest]


/-- Empty local history tests exactly the current configuration. -/
private theorem hitsWithinLocal_nil
    {Q : Type} (ring : DirectedRing n) (T : Q -> Q -> Q × Q)
    (post : (Fin n -> Q) -> Bool) (X : Fin n -> Q) :
    hitsWithinLocal ring T post X [] = post X := by
  rfl


private theorem hitsWithinLocal_of_final
    {Q : Type} (ring : DirectedRing n) (T : Q -> Q -> Q × Q)
    (post : (Fin n -> Q) -> Bool) (X : Fin n -> Q)
    (word : DetSchedule n)
    (hfinal : post (runLocalSchedule ring T X word) = true) :
    hitsWithinLocal ring T post X word = true := by
  induction word generalizing X with
  | nil =>
      rw [hitsWithinLocal_nil ring T post X]
      simpa only [runLocalSchedule] using hfinal
  | cons e rest ih =>
      simp only [runLocalSchedule] at hfinal
      simp only [hitsWithinLocal, Bool.or_eq_true]
      exact Or.inr (ih (localStep ring T X e) hfinal)


private theorem countP_le_countP_of_true_imp
    {alpha : Type} (p q : alpha -> Bool) (xs : List alpha)
    (himp : forall x, x ∈ xs -> p x = true -> q x = true) :
    xs.countP p <= xs.countP q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have htail : forall y, y ∈ xs -> p y = true -> q y = true := by
        intro y hy
        exact himp y (by simp [hy])
      have hi := ih htail
      rw [List.countP_cons, List.countP_cons]
      cases hp : p x with
      | false =>
          cases q x <;> simp_all <;> omega
      | true =>
          have hq : q x = true := himp x (by simp) hp
          simpa [hp, hq] using hi


/-- Every endpoint counted by the verified completion reserve has necessarily
hit the stopped two-outcome test by that same horizon. -/
private theorem endpointCount_le_readyOutcomeHitCount
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite) (t : Nat) :
    homeFrontDropOrReadyEndpointCountFrom ring base X t <=
      localHitCount ring sealSweepHomeFrontPair
        (rankEpochDropOrPostSealTest base (rankEpochReadyTest ring)) X t := by
  unfold homeFrontDropOrReadyEndpointCountFrom localHitCount
  apply countP_le_countP_of_true_imp
  intro word _hword hgood
  apply hitsWithinLocal_of_final
  have hspec :=
    (homeFrontDropOrReadyEndpointTest_spec ring base
      (runLocalSchedule ring sealSweepHomeFrontPair X word)).1 hgood
  apply (rankEpochDropOrPostSealTest_spec base
    (runLocalSchedule ring sealSweepHomeFrontPair X word)
    (rankEpochReadyTest ring)).2
  rcases hspec with hdrop | hready
  · exact Or.inl hdrop
  · exact Or.inr ((rankEpochReadyTest_spec ring _).2 hready)


/-- Candidate (b), with exact pair `H = 2*n^3`, `p = 4`.
Starting after the historical Ready-or-AB gate, the verified stopped-AB drift
and Ready suffix estimates give a quarter of endpoint mass; every such endpoint
is a historical hit of the stopped two-outcome test. -/
theorem readyOrAB_twoOutcome_scaled_count
    (ring : DirectedRing n) (hn : 1 < n)
    (base X : Fin n -> SealSweepHomeFrontSite)
    (hX : ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base X)
    (hgate : HomeFrontReadyOrAB ring X) :
    n ^ (2 * n ^ 3) <=
      4 * localHitCount ring sealSweepHomeFrontPair
        (rankEpochDropOrPostSealTest base (rankEpochReadyTest ring))
        X (2 * n ^ 3) := by
  have hcountLe : homeFrontHomeCount X <= homeFrontHomeCount base := by
    exact Nat.le_of_eq (sameHomeSupport_homeCount_eq base X hX.2)
  have hcompletion :=
    positiveHomeFrontReadyOrAB_completion_quarter
      ring hn base X hX.1 hcountLe hgate
        (2 * n ^ 3) (Nat.le_refl _)
  have hsubset :=
    endpointCount_le_readyOutcomeHitCount
      ring base X (2 * n ^ 3)
  exact Nat.le_trans hcompletion (Nat.mul_le_mul_left 4 hsubset)


end SealRankEpochFirstSubtarget
end PPLLCompleteMultiLeaderCleanup


#print axioms PPLLCompleteMultiLeaderCleanup.SealRankEpochFirstSubtarget.rankEpochReadyTest_spec
#print axioms PPLLCompleteMultiLeaderCleanup.SealRankEpochFirstSubtarget.readyOrAB_twoOutcome_scaled_count
