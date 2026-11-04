import Leader.Wu.Seal.RankEpochAmplification


namespace PPLLCompleteMultiLeaderCleanup
namespace SealRankEpochScaledAmplifier


open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLSchedulerBlocks
open PPartialSealSweepHomeFrontQuotientSol
open PPartialSealSweepRankEpochAuditSol


set_option autoImplicit false


variable {n psi kappa tau : Nat}


/-- Division-free one-block input: the exact scheduler mass is at most `p`
times the number of schedules which hit the chosen Boolean success test. -/
def UniformReachableHomeRankEpochScaledOneBlockHitCount
    (ring : DirectedRing n)
    (base : Fin n -> SealSweepHomeFrontSite)
    (successTest : (Fin n -> SealSweepHomeFrontSite) -> Bool)
    (H p : Nat) : Prop :=
  forall X : Fin n -> SealSweepHomeFrontSite,
    ReachableHomeRankEpoch
        (psi := psi) (kappa := kappa) (tau := tau) ring base X ->
      n ^ H <= p * localHitCount ring sealSweepHomeFrontPair
        successTest X H


/-- Exact failure-branch premise needed by the existing same-rank epoch
closure theorem.  Only blocks which miss `successTest` need preserve rank. -/
def ReachableHomeRankEpochFailureSameRank
    (ring : DirectedRing n)
    (base : Fin n -> SealSweepHomeFrontSite)
    (successTest : (Fin n -> SealSweepHomeFrontSite) -> Bool) : Prop :=
  forall (X : Fin n -> SealSweepHomeFrontSite) (word : DetSchedule n),
    ReachableHomeRankEpoch
        (psi := psi) (kappa := kappa) (tau := tau) ring base X ->
      hitsWithinLocal ring sealSweepHomeFrontPair successTest X word = false ->
        homeFrontHomeCount
            (runLocalSchedule ring sealSweepHomeFrontPair X word) =
          homeFrontHomeCount X


/-- A failed block with unchanged rank remains in the frozen rank epoch. -/
theorem reachableHomeRankEpoch_run_of_failure
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite)
    (successTest : (Fin n -> SealSweepHomeFrontSite) -> Bool)
    (hfailure : ReachableHomeRankEpochFailureSameRank
      (psi := psi) (kappa := kappa) (tau := tau)
      ring base successTest)
    (hX : ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base X)
    (word : DetSchedule n)
    (hmiss : hitsWithinLocal ring sealSweepHomeFrontPair
      successTest X word = false) :
    ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base
      (runLocalSchedule ring sealSweepHomeFrontPair X word) :=
  reachableHomeRankEpoch_run_of_sameRank ring base X hX word
    (hfailure X word hX hmiss)


/-- Scaled complement of the one-block hit premise.  No division or rounding
is used. -/
theorem uniformReachableHomeRankEpochScaledOneBlockHitCount_oneBlock_miss_le
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite)
    (successTest : (Fin n -> SealSweepHomeFrontSite) -> Bool)
    (H p : Nat)
    (hone : UniformReachableHomeRankEpochScaledOneBlockHitCount
      (psi := psi) (kappa := kappa) (tau := tau)
      ring base successTest H p)
    (hX : ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base X) :
    p * localMissCount ring sealSweepHomeFrontPair successTest X H <=
      (p - 1) * n ^ H := by
  have hhit := hone X hX
  have hpart := localMissCount_add_localHitCount
    ring sealSweepHomeFrontPair successTest X H
  rw [allSchedules_length] at hpart
  have hpos : 0 < n ^ H := Nat.pow_pos ring.hn
  have hp0 : p ≠ 0 := by
    intro hp
    rw [hp] at hhit
    simp only [Nat.zero_mul] at hhit
    omega
  have hp : 0 < p := Nat.pos_of_ne_zero hp0
  have hsum := Nat.add_le_add_left hhit
    (p * localMissCount ring sealSweepHomeFrontPair successTest X H)
  have hscaled :
      p * localMissCount ring sealSweepHomeFrontPair successTest X H + n ^ H <=
        (p - 1) * n ^ H + n ^ H := by
    calc
      _ <= p * localMissCount ring sealSweepHomeFrontPair successTest X H +
          p * localHitCount ring sealSweepHomeFrontPair successTest X H := hsum
      _ = p * (localMissCount ring sealSweepHomeFrontPair successTest X H +
          localHitCount ring sealSweepHomeFrontPair successTest X H) := by
            rw [Nat.mul_add]
      _ = p * n ^ H := by rw [hpart]
      _ = ((p - 1) + 1) * n ^ H := by
            apply congrArg (fun q : Nat => q * n ^ H)
            omega
      _ = (p - 1) * n ^ H + n ^ H := by simp [Nat.add_mul]
  omega


private theorem scaled_sum_if_false_le_countP_not_mul
    {alpha : Type} (test : alpha -> Bool) (f : alpha -> Nat)
    (xs : List alpha) (scale B : Nat)
    (hf : forall x, x ∈ xs -> test x = false -> scale * f x <= B) :
    scale * (xs.map (fun x => if test x then 0 else f x)).sum <=
      xs.countP (fun x => !test x) * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have htail : forall y, y ∈ xs -> test y = false -> scale * f y <= B := by
        intro y hy
        exact hf y (by simp [hy])
      have hi := ih htail
      rw [List.map_cons, List.sum_cons, List.countP_cons]
      cases hx : test x
      · have hhead := hf x (by simp) hx
        simpa [hx, Nat.mul_add, Nat.add_mul, Nat.add_comm] using
          Nat.add_le_add hhead hi
      · simpa [hx] using hi


/-- Target-conditioned scaled scheduler multiplication.  This reuses the exact
`SchedulerBlocks.localMissCount_add_eq_sum` product decomposition; only failed
prefixes need the rank-epoch closure premise. -/
theorem scaledRankEpoch_localMissCount_add_le_mul
    (ring : DirectedRing n)
    (base : Fin n -> SealSweepHomeFrontSite)
    (successTest : (Fin n -> SealSweepHomeFrontSite) -> Bool)
    (hfailure : ReachableHomeRankEpochFailureSameRank
      (psi := psi) (kappa := kappa) (tau := tau)
      ring base successTest)
    (a b scaleA scaleB A B : Nat)
    (hA : forall X, ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base X ->
      scaleA * localMissCount ring sealSweepHomeFrontPair successTest X a <= A)
    (hB : forall X, ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base X ->
      scaleB * localMissCount ring sealSweepHomeFrontPair successTest X b <= B) :
    forall X, ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base X ->
      (scaleA * scaleB) * localMissCount ring sealSweepHomeFrontPair
        successTest X (a + b) <= A * B := by
  intro X hX
  rw [localMissCount_add_eq_sum]
  let q := hitsWithinLocal ring sealSweepHomeFrontPair successTest X
  let f := fun pre => localMissCount ring sealSweepHomeFrontPair successTest
    (runLocalSchedule ring sealSweepHomeFrontPair X pre) b
  have hsum :
      scaleB * ((allSchedules n a).map
        (fun pre => if q pre then 0 else f pre)).sum <=
        (allSchedules n a).countP (fun pre => !q pre) * B := by
    apply scaled_sum_if_false_le_countP_not_mul
    intro pre _hpre hmiss
    exact hB _ (reachableHomeRankEpoch_run_of_failure
      ring base X successTest hfailure hX pre hmiss)
  have hprefix :
      scaleA * (allSchedules n a).countP (fun pre => !q pre) <= A := by
    simpa [q, localMissCount] using hA X hX
  change (scaleA * scaleB) * ((allSchedules n a).map
    (fun pre => if q pre then 0 else f pre)).sum <= A * B
  calc
    _ = scaleA * (scaleB * ((allSchedules n a).map
        (fun pre => if q pre then 0 else f pre)).sum) := by ac_rfl
    _ <= scaleA * ((allSchedules n a).countP (fun pre => !q pre) * B) :=
      Nat.mul_le_mul_left scaleA hsum
    _ = (scaleA * (allSchedules n a).countP (fun pre => !q pre)) * B := by
      ac_rfl
    _ <= A * B := Nat.mul_le_mul_right B hprefix


/-- Aligned-block denominator-scaled amplification. -/
theorem uniformReachableHomeRankEpochScaledOneBlockHitCount_repeated_miss_le
    (ring : DirectedRing n)
    (base : Fin n -> SealSweepHomeFrontSite)
    (successTest : (Fin n -> SealSweepHomeFrontSite) -> Bool)
    (H p : Nat)
    (hfailure : ReachableHomeRankEpochFailureSameRank
      (psi := psi) (kappa := kappa) (tau := tau)
      ring base successTest)
    (hone : UniformReachableHomeRankEpochScaledOneBlockHitCount
      (psi := psi) (kappa := kappa) (tau := tau)
      ring base successTest H p) :
    forall blocks X, ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base X ->
      p ^ blocks * localMissCount ring sealSweepHomeFrontPair
        successTest X (blocks * H) <=
      (p - 1) ^ blocks * n ^ (blocks * H) := by
  let F := (p - 1) * n ^ H
  have hraw : forall blocks X, ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base X ->
      p ^ blocks * localMissCount ring sealSweepHomeFrontPair
        successTest X (blocks * H) <= F ^ blocks := by
    intro blocks
    induction blocks with
    | zero =>
        intro X hX
        have hlen : localMissCount ring sealSweepHomeFrontPair
            successTest X 0 <= (allSchedules n 0).length := by
          unfold localMissCount
          exact List.countP_le_length
        simpa [allSchedules] using hlen
    | succ blocks ih =>
        intro X hX
        have hmul := scaledRankEpoch_localMissCount_add_le_mul
          ring base successTest hfailure
          (blocks * H) H (p ^ blocks) p (F ^ blocks) F ih
          (fun Y hY => by
            change p * localMissCount ring sealSweepHomeFrontPair
              successTest Y H <= (p - 1) * n ^ H
            exact uniformReachableHomeRankEpochScaledOneBlockHitCount_oneBlock_miss_le
              ring base Y successTest H p hone hY)
          X hX
        simpa [Nat.succ_mul, Nat.pow_succ] using hmul
  intro blocks X hX
  have h := hraw blocks X hX
  change p ^ blocks * localMissCount ring sealSweepHomeFrontPair
      successTest X (blocks * H) <= ((p - 1) * n ^ H) ^ blocks at h
  simpa only [Nat.mul_pow, <- Nat.pow_mul, Nat.mul_comm H blocks] using h


end SealRankEpochScaledAmplifier
end PPLLCompleteMultiLeaderCleanup


#print axioms PPLLCompleteMultiLeaderCleanup.SealRankEpochScaledAmplifier.reachableHomeRankEpoch_run_of_failure
#print axioms PPLLCompleteMultiLeaderCleanup.SealRankEpochScaledAmplifier.uniformReachableHomeRankEpochScaledOneBlockHitCount_oneBlock_miss_le
#print axioms PPLLCompleteMultiLeaderCleanup.SealRankEpochScaledAmplifier.uniformReachableHomeRankEpochScaledOneBlockHitCount_repeated_miss_le
