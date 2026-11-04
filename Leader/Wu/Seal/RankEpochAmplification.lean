import Leader.Wu.Seal.RankEpochMonotone

/-!
# Exact target-conditioned amplification for home-rank epochs

The home-rank epoch is not closed under every quotient step: a successful
step leaves the epoch by strictly deleting a home.  It has exactly the weaker
closure needed by the scheduler product.  Every prefix which has not hit the
fixed-base rank-drop target remains in the same no-drop provenance hull.

This file implements that conditional closure against the current
`SchedulerBlocks` API.  A uniform one-block hit-count inequality is retained
as an explicit premise.  Exact `allSchedules` decomposition then gives the
geometric miss numerator

`(n^L - favorable)^blocks`

without division, independence axioms, or a TASEP/mixing assertion.

The final interface says what an outer induction may consume: every counted
hit ends at an exact positive-image state whose home rank is strictly below
the fixed base rank.  Producing the one-block premise remains the separate
stochastic problem.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepRankEpochAmplificationSol

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLSchedulerBlocks PPLLNoCheckBirthConditionTwoGeometry
open PPLLClosedDomainSchedulerAmplificationSol
open PPartialSealSweepHomeFrontQuotientSol
open PPartialSealSweepHomeTrapCurrentSol
open PPartialSealSweepReadySuffixHalfMassSol
open PPartialSealSweepABGateBreakthroughSol
open PPartialSealSweepRankEpochAuditSol

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Exact no-drop provenance hull -/

/-- An endpoint reached from `base` by a concrete scheduler word with exactly
the base home rank.  Rank monotonicity makes this the exact no-drop provenance
hull: no earlier prefix of the witness can have dropped and then recovered. -/
def HomeRankNoDropReach
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite) : Prop :=
  exists word : DetSchedule n,
    runLocalSchedule ring sealSweepHomeFrontPair base word = X /\
      homeFrontHomeCount X = homeFrontHomeCount base

theorem homeRankNoDropReach_self
    (ring : DirectedRing n)
    (base : Fin n -> SealSweepHomeFrontSite) :
    HomeRankNoDropReach ring base base := by
  exact ⟨[], rfl, rfl⟩

theorem homeRankNoDropReach_homeCount_eq
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite)
    (hX : HomeRankNoDropReach ring base X) :
    homeFrontHomeCount X = homeFrontHomeCount base := by
  obtain ⟨_word, _hword, hrank⟩ := hX
  exact hrank

/-- A same-base-rank continuation appends its word to the provenance
witness. -/
theorem homeRankNoDropReach_run_of_sameBaseRank
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite)
    (hX : HomeRankNoDropReach ring base X)
    (word : DetSchedule n)
    (hrank : homeFrontHomeCount
        (runLocalSchedule ring sealSweepHomeFrontPair X word) =
      homeFrontHomeCount base) :
    HomeRankNoDropReach ring base
      (runLocalSchedule ring sealSweepHomeFrontPair X word) := by
  obtain ⟨pre, hpre, _hXrank⟩ := hX
  refine ⟨pre ++ word, ?_, hrank⟩
  rw [runLocalSchedule_append, hpre]

/-- The exact provenance hull implies the extensional same-support fact. -/
theorem homeRankNoDropReach_sameHomeSupport
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite)
    (hX : HomeRankNoDropReach ring base X) :
    SameHomeSupport base X := by
  obtain ⟨word, hword, hrank⟩ := hX
  have hsupport := quotientHomeSupport_run_eq_of_sameRank
    ring base word (by simpa [hword] using hrank)
  unfold SameHomeSupport
  simpa [hword] using hsupport

/-- From a positive exact-image base, the provenance hull lands in the
previous file's source-faithful extensional epoch. -/
theorem homeRankNoDropReach_to_reachableHomeRankEpoch
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite)
    (hbase : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring base)
    (hX : HomeRankNoDropReach ring base X) :
    ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base X := by
  have hsupport := homeRankNoDropReach_sameHomeSupport
    ring base X hX
  obtain ⟨word, hword, _hrank⟩ := hX
  constructor
  · rw [← hword]
    exact positiveHomeFrontState_run ring base hbase word
  · exact hsupport

/-! ## A missed prefix stays in the provenance hull -/

/-- Boolean specification of the fixed-base strict-rank target. -/
theorem homeFrontHomeDropTest_spec
    (base X : Fin n -> SealSweepHomeFrontSite) :
    homeFrontHomeDropTest base X = true <->
      homeFrontHomeCount X < homeFrontHomeCount base := by
  simp [homeFrontHomeDropTest]

private theorem endpointTest_false_of_hitsWithinLocal_false
    {Q : Type} (ring : DirectedRing n)
    (T : Q -> Q -> Q × Q)
    (postTest : (Fin n -> Q) -> Bool)
    (X : Fin n -> Q) (word : DetSchedule n)
    (hmiss : hitsWithinLocal ring T postTest X word = false) :
    postTest (runLocalSchedule ring T X word) = false := by
  cases hpost : postTest (runLocalSchedule ring T X word) with
  | false => rfl
  | true =>
      have hhit := hitsWithinLocal_of_endpoint
        ring T postTest X word hpost
      rw [hmiss] at hhit
      contradiction

/-- Target-conditioned closure: a schedule prefix which misses strict rank
drop has an endpoint in the same exact provenance hull. -/
theorem homeRankNoDropReach_run_of_miss
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite)
    (hX : HomeRankNoDropReach ring base X)
    (word : DetSchedule n)
    (hmiss : hitsWithinLocal ring sealSweepHomeFrontPair
      (homeFrontHomeDropTest base) X word = false) :
    HomeRankNoDropReach ring base
      (runLocalSchedule ring sealSweepHomeFrontPair X word) := by
  let Y := runLocalSchedule ring sealSweepHomeFrontPair X word
  have hendFalse : homeFrontHomeDropTest base Y = false :=
    endpointTest_false_of_hitsWithinLocal_false
      ring sealSweepHomeFrontPair (homeFrontHomeDropTest base)
      X word hmiss
  have hnotlt : ¬ (homeFrontHomeCount Y <
      homeFrontHomeCount base) := by
    intro hlt
    have htrue : homeFrontHomeDropTest base Y = true :=
      (homeFrontHomeDropTest_spec base Y).2 hlt
    rw [hendFalse] at htrue
    contradiction
  have hleX : homeFrontHomeCount Y <= homeFrontHomeCount X :=
    homeFrontHomeCount_run_le ring X word
  have hXrank := homeRankNoDropReach_homeCount_eq ring base X hX
  have hYrank : homeFrontHomeCount Y = homeFrontHomeCount base := by
    omega
  exact homeRankNoDropReach_run_of_sameBaseRank
    ring base X hX word hYrank

/-- With a positive base, every missed prefix endpoint enters both the exact
provenance hull and the source-faithful extensional epoch. -/
theorem homeRankNoDropReach_run_of_miss_enters_epoch
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite)
    (hbase : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring base)
    (hX : HomeRankNoDropReach ring base X)
    (word : DetSchedule n)
    (hmiss : hitsWithinLocal ring sealSweepHomeFrontPair
      (homeFrontHomeDropTest base) X word = false) :
    HomeRankNoDropReach ring base
        (runLocalSchedule ring sealSweepHomeFrontPair X word) /\
      ReachableHomeRankEpoch
        (psi := psi) (kappa := kappa) (tau := tau) ring base
        (runLocalSchedule ring sealSweepHomeFrontPair X word) := by
  have hhull := homeRankNoDropReach_run_of_miss
    ring base X hX word hmiss
  exact ⟨hhull,
    homeRankNoDropReach_to_reachableHomeRankEpoch
      ring base _ hbase hhull⟩

/-! ## Target-conditioned exact scheduler multiplication -/

private theorem rankEpoch_sum_if_false_le_countP_not_mul
    {alpha : Type} (p : alpha -> Bool) (f : alpha -> Nat)
    (xs : List alpha) (B : Nat)
    (hf : forall x, x ∈ xs -> p x = false -> f x <= B) :
    (xs.map (fun x => if p x then 0 else f x)).sum <=
      xs.countP (fun x => !p x) * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have htail : forall y, y ∈ xs ->
          p y = false -> f y <= B := by
        intro y hy
        exact hf y (by simp [hy])
      have hi := ih htail
      rw [List.map_cons, List.sum_cons, List.countP_cons]
      cases hp : p x
      · have hx : f x <= B := hf x (by simp) hp
        simpa [hp, Nat.add_mul, Nat.add_comm] using
          Nat.add_le_add hx hi
      · simpa [hp] using hi

/-- Exact two-block multiplication on the no-drop hull.  Unlike the generic
closed-domain theorem, closure is requested only for prefixes counted as
misses; successful prefixes contribute zero in `localMissCount_add_eq_sum`. -/
theorem homeRankNoDrop_localMissCount_add_le_mul
    (ring : DirectedRing n)
    (base : Fin n -> SealSweepHomeFrontSite)
    (a b A B : Nat)
    (hA : forall X : Fin n -> SealSweepHomeFrontSite,
      HomeRankNoDropReach ring base X ->
        localMissCount ring sealSweepHomeFrontPair
          (homeFrontHomeDropTest base) X a <= A)
    (hB : forall X : Fin n -> SealSweepHomeFrontSite,
      HomeRankNoDropReach ring base X ->
        localMissCount ring sealSweepHomeFrontPair
          (homeFrontHomeDropTest base) X b <= B) :
    forall X : Fin n -> SealSweepHomeFrontSite,
      HomeRankNoDropReach ring base X ->
        localMissCount ring sealSweepHomeFrontPair
          (homeFrontHomeDropTest base) X (a + b) <= A * B := by
  intro X hX
  rw [localMissCount_add_eq_sum]
  let p := hitsWithinLocal ring sealSweepHomeFrontPair
    (homeFrontHomeDropTest base) X
  let f := fun pre => localMissCount ring sealSweepHomeFrontPair
    (homeFrontHomeDropTest base)
    (runLocalSchedule ring sealSweepHomeFrontPair X pre) b
  have hsum :
      ((allSchedules n a).map
        (fun pre => if p pre then 0 else f pre)).sum <=
        (allSchedules n a).countP (fun pre => !p pre) * B := by
    apply rankEpoch_sum_if_false_le_countP_not_mul
    intro pre _hpre hmiss
    exact hB _ (homeRankNoDropReach_run_of_miss
      ring base X hX pre hmiss)
  have hprefix :
      (allSchedules n a).countP (fun pre => !p pre) <= A := by
    exact hA X hX
  exact Nat.le_trans hsum (Nat.mul_le_mul_right B hprefix)

/-! ## Explicit one-block premise and its exact amplification -/

/-- The sole state-uniform stochastic premise.  It is deliberately a
definition, not a theorem claiming that the TASEP estimate has been proved. -/
def UniformNoDropRankOneBlockHitCount
    (ring : DirectedRing n)
    (base : Fin n -> SealSweepHomeFrontSite)
    (L favorable : Nat) : Prop :=
  forall X : Fin n -> SealSweepHomeFrontSite,
    HomeRankNoDropReach ring base X ->
      favorable <= localHitCount ring sealSweepHomeFrontPair
        (homeFrontHomeDropTest base) X L

/-- Source-facing form of the same missing one-block theorem.  This premise
is uniform over the frozen extensional epoch and is not proved here. -/
def UniformReachableHomeRankEpochOneBlockHitCount
    (ring : DirectedRing n)
    (base : Fin n -> SealSweepHomeFrontSite)
    (L favorable : Nat) : Prop :=
  forall X : Fin n -> SealSweepHomeFrontSite,
    ReachableHomeRankEpoch
        (psi := psi) (kappa := kappa) (tau := tau) ring base X ->
      favorable <= localHitCount ring sealSweepHomeFrontPair
        (homeFrontHomeDropTest base) X L

/-- Exact provenance is a subdomain of the frozen extensional epoch, so a
uniform epoch premise supplies the no-drop-hull premise needed below. -/
theorem uniformReachableHomeRankEpochOneBlockHitCount_to_noDrop
    (ring : DirectedRing n)
    (base : Fin n -> SealSweepHomeFrontSite)
    (hbase : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring base)
    (L favorable : Nat)
    (hone : UniformReachableHomeRankEpochOneBlockHitCount
      (psi := psi) (kappa := kappa) (tau := tau)
      ring base L favorable) :
    UniformNoDropRankOneBlockHitCount ring base L favorable := by
  intro X hX
  exact hone X (homeRankNoDropReach_to_reachableHomeRankEpoch
    ring base X hbase hX)

/-- The explicit hit numerator gives the exact complementary one-block miss
budget `n^L - favorable`. -/
theorem uniformNoDropRankOneBlockHitCount_oneBlock_miss_le
    (ring : DirectedRing n)
    (base : Fin n -> SealSweepHomeFrontSite)
    (L favorable : Nat)
    (hone : UniformNoDropRankOneBlockHitCount
      ring base L favorable)
    (X : Fin n -> SealSweepHomeFrontSite)
    (hX : HomeRankNoDropReach ring base X) :
    localMissCount ring sealSweepHomeFrontPair
        (homeFrontHomeDropTest base) X L <=
      n ^ L - favorable := by
  have hhit := hone X hX
  have hpartition := localMissCount_add_localHitCount
    ring sealSweepHomeFrontPair (homeFrontHomeDropTest base) X L
  rw [allSchedules_length] at hpartition
  omega

/-- Exact aligned-block multiplication using only target-conditioned hull
closure and the scheduler list product. -/
theorem uniformNoDropRankOneBlockHitCount_repeated_miss_le
    (ring : DirectedRing n)
    (base : Fin n -> SealSweepHomeFrontSite)
    (L favorable : Nat)
    (hone : UniformNoDropRankOneBlockHitCount
      ring base L favorable) :
    forall blocks X,
      HomeRankNoDropReach ring base X ->
        localMissCount ring sealSweepHomeFrontPair
            (homeFrontHomeDropTest base) X (blocks * L) <=
          (n ^ L - favorable) ^ blocks := by
  intro blocks
  induction blocks with
  | zero =>
      intro X hX
      have hlen : localMissCount ring sealSweepHomeFrontPair
          (homeFrontHomeDropTest base) X 0 <=
          (allSchedules n 0).length := by
        unfold localMissCount
        exact List.countP_le_length
      simpa [allSchedules] using hlen
  | succ blocks ih =>
      intro X hX
      have hmul := homeRankNoDrop_localMissCount_add_le_mul
        ring base (blocks * L) L
        ((n ^ L - favorable) ^ blocks)
        (n ^ L - favorable)
        ih
        (uniformNoDropRankOneBlockHitCount_oneBlock_miss_le
          ring base L favorable hone)
        X hX
      simpa [Nat.succ_mul, Nat.pow_succ] using hmul

/-- Division-free amplified success inequality.  The exact total scheduler
mass is bounded by geometric misses plus successful schedules. -/
theorem uniformNoDropRankOneBlockHitCount_repeated_total_le_miss_add_hit
    (ring : DirectedRing n)
    (base : Fin n -> SealSweepHomeFrontSite)
    (L favorable blocks : Nat)
    (hone : UniformNoDropRankOneBlockHitCount
      ring base L favorable)
    (X : Fin n -> SealSweepHomeFrontSite)
    (hX : HomeRankNoDropReach ring base X) :
    n ^ (blocks * L) <=
      (n ^ L - favorable) ^ blocks +
        localHitCount ring sealSweepHomeFrontPair
          (homeFrontHomeDropTest base) X (blocks * L) := by
  have hmiss := uniformNoDropRankOneBlockHitCount_repeated_miss_le
    ring base L favorable hone blocks X hX
  have hpartition := localMissCount_add_localHitCount
    ring sealSweepHomeFrontPair (homeFrontHomeDropTest base)
    X (blocks * L)
  rw [allSchedules_length] at hpartition
  omega

/-- Equivalent explicit lower numerator, still entirely in `Nat`. -/
theorem uniformNoDropRankOneBlockHitCount_repeated_hit_lower
    (ring : DirectedRing n)
    (base : Fin n -> SealSweepHomeFrontSite)
    (L favorable blocks : Nat)
    (hone : UniformNoDropRankOneBlockHitCount
      ring base L favorable)
    (X : Fin n -> SealSweepHomeFrontSite)
    (hX : HomeRankNoDropReach ring base X) :
    n ^ (blocks * L) - (n ^ L - favorable) ^ blocks <=
      localHitCount ring sealSweepHomeFrontPair
        (homeFrontHomeDropTest base) X (blocks * L) := by
  have htotal :=
    uniformNoDropRankOneBlockHitCount_repeated_total_le_miss_add_hit
      ring base L favorable blocks hone X hX
  omega

/-! ## Minimal outer strict-rank descent interface -/

/-- Once rank has dropped below the fixed base, quotient monotonicity keeps it
below that base under every later local step. -/
theorem homeRankDrop_localStepClosed
    (ring : DirectedRing n)
    (base : Fin n -> SealSweepHomeFrontSite) :
    LocalStepClosed ring sealSweepHomeFrontPair
      (fun X => homeFrontHomeCount X < homeFrontHomeCount base) := by
  intro X hX edge
  have hle := homeFrontHomeCount_localStep_le ring X edge
  omega

/-- Hence the prefix-hit target is exactly strict rank descent at the endpoint;
there is no persistence assumption beyond rank monotonicity. -/
theorem homeRankDrop_hitsWithinLocal_iff_endpoint
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite)
    (word : DetSchedule n) :
    hitsWithinLocal ring sealSweepHomeFrontPair
        (homeFrontHomeDropTest base) X word = true <->
      homeFrontHomeCount
          (runLocalSchedule ring sealSweepHomeFrontPair X word) <
        homeFrontHomeCount base := by
  exact hitsWithinLocal_iff_closed_endpoint
    ring sealSweepHomeFrontPair
    (fun Y => homeFrontHomeCount Y < homeFrontHomeCount base)
    (homeFrontHomeDropTest base)
    (fun Y => homeFrontHomeDropTest_spec base Y)
    (homeRankDrop_localStepClosed ring base) X word

/-- Every hit counted by the fixed-rank block is an exact positive-image
endpoint with strictly smaller rank.  This is the minimal semantic handoff to
an outer induction on the finite home rank. -/
theorem homeRankNoDropReach_hit_endpoint_strictPositive
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite)
    (hbase : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring base)
    (hX : HomeRankNoDropReach ring base X)
    (word : DetSchedule n)
    (hhit : hitsWithinLocal ring sealSweepHomeFrontPair
      (homeFrontHomeDropTest base) X word = true) :
    SealSweepPositiveHomeFrontState
        (psi := psi) (kappa := kappa) (tau := tau) ring
        (runLocalSchedule ring sealSweepHomeFrontPair X word) /\
      homeFrontHomeCount
          (runLocalSchedule ring sealSweepHomeFrontPair X word) <
        homeFrontHomeCount base := by
  have hEpoch := homeRankNoDropReach_to_reachableHomeRankEpoch
    ring base X hbase hX
  constructor
  · exact positiveHomeFrontState_run ring X hEpoch.1 word
  · exact (homeRankDrop_hitsWithinLocal_iff_endpoint
      ring base X word).1 hhit

/-- Count and semantics packaged for the outer strict-rank induction.  The
only unproved input is still the explicit uniform one-block hit count. -/
theorem uniformNoDropRankOneBlockHitCount_outerStrictRankDescent
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite)
    (hbase : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring base)
    (hX : HomeRankNoDropReach ring base X)
    (L favorable blocks : Nat)
    (hone : UniformNoDropRankOneBlockHitCount
      ring base L favorable) :
    (n ^ (blocks * L) - (n ^ L - favorable) ^ blocks <=
      localHitCount ring sealSweepHomeFrontPair
        (homeFrontHomeDropTest base) X (blocks * L)) /\
      forall word : DetSchedule n,
        hitsWithinLocal ring sealSweepHomeFrontPair
            (homeFrontHomeDropTest base) X word = true ->
          SealSweepPositiveHomeFrontState
              (psi := psi) (kappa := kappa) (tau := tau) ring
              (runLocalSchedule ring sealSweepHomeFrontPair X word) /\
            homeFrontHomeCount
                (runLocalSchedule ring sealSweepHomeFrontPair X word) <
              homeFrontHomeCount base := by
  constructor
  · exact uniformNoDropRankOneBlockHitCount_repeated_hit_lower
      ring base L favorable blocks hone X hX
  · intro word hhit
    exact homeRankNoDropReach_hit_endpoint_strictPositive
      ring base X hbase hX word hhit

/-- Frozen-epoch-facing form of the outer interface.  Its only substantive
premise is the explicitly named uniform one-block count. -/
theorem uniformReachableHomeRankEpochOneBlockHitCount_outerStrictRankDescent
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite)
    (hbase : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring base)
    (hX : HomeRankNoDropReach ring base X)
    (L favorable blocks : Nat)
    (hone : UniformReachableHomeRankEpochOneBlockHitCount
      (psi := psi) (kappa := kappa) (tau := tau)
      ring base L favorable) :
    (n ^ (blocks * L) - (n ^ L - favorable) ^ blocks <=
      localHitCount ring sealSweepHomeFrontPair
        (homeFrontHomeDropTest base) X (blocks * L)) /\
      forall word : DetSchedule n,
        hitsWithinLocal ring sealSweepHomeFrontPair
            (homeFrontHomeDropTest base) X word = true ->
          SealSweepPositiveHomeFrontState
              (psi := psi) (kappa := kappa) (tau := tau) ring
              (runLocalSchedule ring sealSweepHomeFrontPair X word) /\
            homeFrontHomeCount
                (runLocalSchedule ring sealSweepHomeFrontPair X word) <
              homeFrontHomeCount base := by
  exact uniformNoDropRankOneBlockHitCount_outerStrictRankDescent
    ring base X hbase hX L favorable blocks
    (uniformReachableHomeRankEpochOneBlockHitCount_to_noDrop
      ring base hbase L favorable hone)

#print axioms homeRankNoDropReach_run_of_miss_enters_epoch
#print axioms homeRankNoDrop_localMissCount_add_le_mul
#print axioms uniformNoDropRankOneBlockHitCount_repeated_miss_le
#print axioms uniformNoDropRankOneBlockHitCount_repeated_hit_lower
#print axioms homeRankDrop_hitsWithinLocal_iff_endpoint
#print axioms uniformNoDropRankOneBlockHitCount_outerStrictRankDescent
#print axioms uniformReachableHomeRankEpochOneBlockHitCount_outerStrictRankDescent

end PPartialSealSweepRankEpochAmplificationSol
end PPLLCompleteMultiLeaderCleanup
