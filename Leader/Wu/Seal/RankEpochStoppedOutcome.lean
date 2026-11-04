import Leader.Wu.Seal.RankEpochAmplification

namespace PPLLCompleteMultiLeaderCleanup
namespace SealRankEpochStoppedOutcome

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLSchedulerBlocks PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepHomeFrontQuotientSol
open PPartialSealSweepRankEpochAuditSol
open PPartialSealSweepRankEpochAmplificationSol

set_option autoImplicit false
set_option Elab.async false

variable {n psi kappa tau : Nat}

/-- Historical stopped target: strict drop from the frozen base, or the
quotient-visible post-seal completion flag. -/
def rankEpochDropOrPostSealTest
    (base : Fin n -> SealSweepHomeFrontSite)
    (postSealTest : (Fin n -> SealSweepHomeFrontSite) -> Bool)
    (X : Fin n -> SealSweepHomeFrontSite) : Bool :=
  homeFrontHomeDropTest base X || postSealTest X

theorem rankEpochDropOrPostSealTest_spec
    (base X : Fin n -> SealSweepHomeFrontSite)
    (postSealTest : (Fin n -> SealSweepHomeFrontSite) -> Bool) :
    rankEpochDropOrPostSealTest base postSealTest X = true <->
      homeFrontHomeCount X < homeFrontHomeCount base \/
        postSealTest X = true := by
  rw [rankEpochDropOrPostSealTest, Bool.or_eq_true]
  simp [homeFrontHomeDropTest]

/-- `p` is the reciprocal success-mass scale: `n^H <= p * hits` means
success fraction at least `1/p`. Runtime-admissible targets are
`H*p = O(n loglog n)` uniformly over ranks, or
`sum_r H_r*p_r = O(n^2 loglog n)`. -/
def UniformReachableHomeRankEpochStoppedOutcomeCount
    (ring : DirectedRing n)
    (base : Fin n -> SealSweepHomeFrontSite)
    (postSealTest : (Fin n -> SealSweepHomeFrontSite) -> Bool)
    (H p : Nat) : Prop :=
  forall X : Fin n -> SealSweepHomeFrontSite,
    ReachableHomeRankEpoch
        (psi := psi) (kappa := kappa) (tau := tau) ring base X ->
      n ^ H <= p * localHitCount ring sealSweepHomeFrontPair
        (rankEpochDropOrPostSealTest base postSealTest) X H

/-- Semantic obligation for the eventual concrete post-seal entry test. -/
def PostSealTestSoundness
    (postSealTest : (Fin n -> SealSweepHomeFrontSite) -> Bool)
    (postSealSuccess : (Fin n -> SealSweepHomeFrontSite) -> Prop) : Prop :=
  forall X, postSealTest X = true -> postSealSuccess X

/-- An H-letter quotient word is literally the same H physical interactions. -/
theorem quotientWord_exact_physical_H
    (ring : DirectedRing n)
    (C : PPartialSealSweepOverlaySol.SealSweepConfig n psi kappa tau)
    (word : DetSchedule n) (H : Nat) (hlen : word.length = H) :
    sealSweepHomeFrontConfig
        (runLocalSchedule ring
          PPartialSealSweepOverlaySol.P_partialSealSweep C word) =
      runLocalSchedule ring sealSweepHomeFrontPair
        (sealSweepHomeFrontConfig C) word /\ word.length = H := by
  exact ⟨sealSweepHomeFrontConfig_runLocalSchedule_exact ring C word, hlen⟩

private theorem hitsWithinLocal_or {Q : Type}
    (ring : DirectedRing n) (T : Q -> Q -> Q × Q)
    (p q : (Fin n -> Q) -> Bool) (X : Fin n -> Q) (word : DetSchedule n) :
    hitsWithinLocal ring T (fun Y => p Y || q Y) X word =
      (hitsWithinLocal ring T p X word || hitsWithinLocal ring T q X word) := by
  induction word generalizing X with
  | nil => rfl
  | cons e rest ih =>
      simp only [hitsWithinLocal]
      rw [ih (localStep ring T X e)]
      cases hp : p X <;> cases hq : q X <;>
        cases hp' : hitsWithinLocal ring T p (localStep ring T X e) rest <;>
        cases hq' : hitsWithinLocal ring T q (localStep ring T X e) rest <;> rfl

private theorem hitsWithinLocal_prefix_witness {Q : Type}
    (ring : DirectedRing n) (T : Q -> Q -> Q × Q)
    (post : (Fin n -> Q) -> Bool) (X : Fin n -> Q) (word : DetSchedule n)
    (hhit : hitsWithinLocal ring T post X word = true) :
    exists pre suffix : DetSchedule n,
      word = pre ++ suffix /\
        post (runLocalSchedule ring T X pre) = true := by
  induction word generalizing X with
  | nil => exact ⟨[], [], rfl, hhit⟩
  | cons e rest ih =>
      simp only [hitsWithinLocal, Bool.or_eq_true] at hhit
      rcases hhit with hnow | htail
      · exact ⟨[], e :: rest, rfl, hnow⟩
      · obtain ⟨pre, suffix, hrest, hpre⟩ :=
          ih (localStep ring T X e) htail
        refine ⟨e :: pre, suffix, ?_, ?_⟩
        · simp [hrest]
        · simpa only [runLocalSchedule] using hpre

/-- Missing both stopped outcomes keeps the failure block in the frozen epoch. -/
theorem stoppedOutcome_miss_stays_epoch
    (ring : DirectedRing n) (base X : Fin n -> SealSweepHomeFrontSite)
    (postSealTest : (Fin n -> SealSweepHomeFrontSite) -> Bool)
    (hX : ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base X)
    (word : DetSchedule n)
    (hmiss : hitsWithinLocal ring sealSweepHomeFrontPair
      (rankEpochDropOrPostSealTest base postSealTest) X word = false) :
    ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base
      (runLocalSchedule ring sealSweepHomeFrontPair X word) := by
  change hitsWithinLocal ring sealSweepHomeFrontPair
      (fun Y => homeFrontHomeDropTest base Y || postSealTest Y)
      X word = false at hmiss
  rw [hitsWithinLocal_or ring sealSweepHomeFrontPair
    (homeFrontHomeDropTest base) postSealTest X word] at hmiss
  have hdropMiss : hitsWithinLocal ring sealSweepHomeFrontPair
      (homeFrontHomeDropTest base) X word = false :=
    (Bool.or_eq_false_iff.mp hmiss).1
  have hnotlt : ¬ homeFrontHomeCount
      (runLocalSchedule ring sealSweepHomeFrontPair X word) <
      homeFrontHomeCount base := by
    intro hlt
    have htrue := (homeRankDrop_hitsWithinLocal_iff_endpoint
      ring base X word).2 hlt
    rw [hdropMiss] at htrue
    contradiction
  have hle :=
    PPartialSealSweepReadySuffixHalfMassSol.homeFrontHomeCount_run_le
      ring X word
  have hXrank := sameHomeSupport_homeCount_eq base X hX.2
  have hbaseLe : homeFrontHomeCount base <=
      homeFrontHomeCount
        (runLocalSchedule ring sealSweepHomeFrontPair X word) :=
    Nat.le_of_not_gt hnotlt
  have hXle : homeFrontHomeCount X <=
      homeFrontHomeCount
        (runLocalSchedule ring sealSweepHomeFrontPair X word) := by
    rw [hXrank]
    exact hbaseLe
  have hrank : homeFrontHomeCount
      (runLocalSchedule ring sealSweepHomeFrontPair X word) =
      homeFrontHomeCount X := Nat.le_antisymm hle hXle
  exact reachableHomeRankEpoch_run_of_sameRank
    ring base X hX word hrank

/-- A combined hit is either strict positive rank descent or a certified
post-seal prefix satisfying the semantic handoff. -/
theorem rankEpochDropOrPostSeal_hit_split
    (ring : DirectedRing n) (base X : Fin n -> SealSweepHomeFrontSite)
    (postSealTest : (Fin n -> SealSweepHomeFrontSite) -> Bool)
    (postSealSuccess : (Fin n -> SealSweepHomeFrontSite) -> Prop)
    (hsound : PostSealTestSoundness postSealTest postSealSuccess)
    (hbase : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring base)
    (hX : HomeRankNoDropReach ring base X) (word : DetSchedule n)
    (hhit : hitsWithinLocal ring sealSweepHomeFrontPair
      (rankEpochDropOrPostSealTest base postSealTest) X word = true) :
    (SealSweepPositiveHomeFrontState
        (psi := psi) (kappa := kappa) (tau := tau) ring
        (runLocalSchedule ring sealSweepHomeFrontPair X word) /\
      homeFrontHomeCount
          (runLocalSchedule ring sealSweepHomeFrontPair X word) <
        homeFrontHomeCount base) \/
    (exists pre suffix : DetSchedule n,
      word = pre ++ suffix /\
      postSealTest (runLocalSchedule ring sealSweepHomeFrontPair X pre) = true /\
      postSealSuccess (runLocalSchedule ring sealSweepHomeFrontPair X pre)) := by
  change hitsWithinLocal ring sealSweepHomeFrontPair
      (fun Y => homeFrontHomeDropTest base Y || postSealTest Y)
      X word = true at hhit
  rw [hitsWithinLocal_or ring sealSweepHomeFrontPair
    (homeFrontHomeDropTest base) postSealTest X word,
    Bool.or_eq_true] at hhit
  rcases hhit with hdrop | hpost
  · exact Or.inl (homeRankNoDropReach_hit_endpoint_strictPositive
      ring base X hbase hX word hdrop)
  · obtain ⟨pre, suffix, hword, hpre⟩ :=
      hitsWithinLocal_prefix_witness ring sealSweepHomeFrontPair
        postSealTest X word hpost
    exact Or.inr ⟨pre, suffix, hword, hpre, hsound _ hpre⟩

#print axioms rankEpochDropOrPostSealTest_spec
#print axioms quotientWord_exact_physical_H
#print axioms stoppedOutcome_miss_stays_epoch
#print axioms rankEpochDropOrPostSeal_hit_split
#print axioms UniformReachableHomeRankEpochStoppedOutcomeCount

end SealRankEpochStoppedOutcome
end PPLLCompleteMultiLeaderCleanup
