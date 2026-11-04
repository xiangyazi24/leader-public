import Leader.Wu.Seal.MixedNormalizer

/-!
# Quantitative iid amplification for the mixed seal sweep

R91 obtains restartability from a deterministic normalization word followed by
the positive all-closed landing word.  This file keeps the same protocol and
extracts scheduler multiplicity that the singleton-word bound discards.

The generic counting lemma is simple but important: once one length-`a`
prefix has hit the target, all `n^b` length-`b` suffixes are favorable at
horizon `a+b`.  The protocol-specific part then shortens the R91 prefix using
the conserved equality between open leader and follower tokens.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepIidComplexitySol

open PPLL PPLLResearchFormulation
open PPLLTraceConvergence PPLLSchedulerBlocks
open PPLLClosedDomainSchedulerAmplificationSol
open PPartialDynamicSweepLockSol
open PPartialSealSweepOverlaySol
open PPartialSealSweepPositiveLandingSol
open PPartialSealSweepUniformSchedulerSol
open PPartialSealSweepMixedNormalizerSol

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Generic suffix multiplicity -/

private theorem nat_le_sum_of_mem {x : Nat} {xs : List Nat}
    (hx : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp
      · have := ih hx
        simp only [List.sum_cons]
        omega

/-- If one exact length-`a` prefix hits the target, every length-`b` suffix
extends it to a distinct favorable scheduler outcome. -/
theorem localHitCount_add_lower_of_hit
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (postTest : (Fin n → Q) → Bool)
    (C : Fin n → Q) (a b : Nat) (pre : DetSchedule n)
    (hpreLength : pre.length = a)
    (hpreHit : hitsWithinLocal ring T postTest C pre = true) :
    n ^ b ≤ localHitCount ring T postTest C (a + b) := by
  unfold localHitCount
  rw [allSchedules_add, List.countP_flatMap]
  let chunkCount : DetSchedule n → Nat := fun word =>
    ((allSchedules n b).map (fun suffix => word ++ suffix)).countP
      (hitsWithinLocal ring T postTest C)
  have hchunk : chunkCount pre = (allSchedules n b).length := by
    unfold chunkCount
    rw [List.countP_map]
    apply List.countP_eq_length.mpr
    intro suffix hsuffix
    simp only [Function.comp_apply]
    rw [hitsWithinLocal_append, hpreHit]
    rfl
  have hpreMem : pre ∈ allSchedules n a :=
    mem_allSchedules_of_length n a pre hpreLength
  have hchunkMem : chunkCount pre ∈
      (allSchedules n a).map chunkCount :=
    List.mem_map.mpr ⟨pre, hpreMem, rfl⟩
  change n ^ b ≤ ((allSchedules n a).map chunkCount).sum
  rw [← allSchedules_length n b, ← hchunk]
  exact nat_le_sum_of_mem hchunkMem

/-- A producer with horizon `M` gives `n^S` favorable schedules at the longer
horizon `M+S`, not merely one: choose its padded hit prefix and leave the last
`S` scheduler choices arbitrary. -/
theorem localHitCount_suffix_lower_of_boundedSafeProducer
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Domain Safe : (Fin n → Q) → Prop)
    (safeTest : (Fin n → Q) → Bool)
    (hdec : ∀ C, safeTest C = true ↔ Safe C)
    (M S : Nat)
    (hproducer : BoundedSafeScheduleProducer ring T Domain Safe M)
    (C : Fin n → Q) (hC : Domain C) :
    n ^ S ≤ localHitCount ring T safeTest C (M + S) := by
  obtain ⟨pre, hpreLength, hpreHit⟩ :=
    boundedSafeProducer_exact_hit_schedule
      ring T Domain Safe safeTest hdec M hproducer C hC
  exact localHitCount_add_lower_of_hit
    ring T safeTest C M S pre hpreLength hpreHit

/-- Exact one-block miss budget retaining all arbitrary suffixes after a
bounded hit prefix. -/
theorem boundedSafeProducer_suffixRich_oneBlockPhase
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Domain Safe : (Fin n → Q) → Prop)
    (safeTest : (Fin n → Q) → Bool)
    (hdec : ∀ C, safeTest C = true ↔ Safe C)
    (M S : Nat)
    (hproducer : BoundedSafeScheduleProducer ring T Domain Safe M) :
    UniformFinitePhase ring T Domain Safe safeTest
      (M + S) (n ^ (M + S) - n ^ S) := by
  constructor
  · exact hdec
  · intro C hC
    rw [allSchedules_length]
    have hhit := localHitCount_suffix_lower_of_boundedSafeProducer
      ring T Domain Safe safeTest hdec M S hproducer C hC
    have htotal : n ^ S ≤ n ^ (M + S) := by
      rw [Nat.pow_add]
      exact Nat.le_mul_of_pos_left _ (Nat.pow_pos ring.hn)
    omega

/-! ## Balanced-token packing -/

/-- Open leader and open follower tokens are disjoint, so their total count
cannot exceed the number of sites. -/
theorem sealSweepOpenCounts_add_le
    (C : SealSweepConfig n psi kappa tau) :
    sealSweepOpenLeaderCount C + sealSweepOpenFollowerCount C ≤ n := by
  induction n with
  | zero =>
      change
        (List.ofFn (fun i : Fin 0 =>
          if sweepLockLeader (C i) && !(C i).2 then 1 else 0)).sum +
        (List.ofFn (fun i : Fin 0 =>
          if !sweepLockLeader (C i) && !(C i).2 then 1 else 0)).sum ≤ 0
      simp
  | succ n ih =>
      change
        (List.ofFn (fun i : Fin (n + 1) =>
          if sweepLockLeader (C i) && !(C i).2 then 1 else 0)).sum +
        (List.ofFn (fun i : Fin (n + 1) =>
          if !sweepLockLeader (C i) && !(C i).2 then 1 else 0)).sum ≤ n + 1
      rw [List.ofFn_succ, List.ofFn_succ, List.sum_cons, List.sum_cons]
      have htail := ih (C := fun i : Fin n => C i.succ)
      change
        (List.ofFn (fun i : Fin n =>
          if sweepLockLeader (C i.succ) && !(C i.succ).2 then 1 else 0)).sum +
        (List.ofFn (fun i : Fin n =>
          if !sweepLockLeader (C i.succ) && !(C i.succ).2 then 1 else 0)).sum ≤ n
        at htail
      cases hl : sweepLockLeader (C 0) <;>
        cases hc : (C 0).2 <;>
        simp [hl, hc] at * <;>
        omega

/-- Balance turns disjointness into the factor-two packing inequality. -/
theorem balanced_two_openLeaderCount_le
    (C : SealSweepConfig n psi kappa tau)
    (hbalanced : SealSweepOpenBalanced C) :
    2 * sealSweepOpenLeaderCount C ≤ n := by
  have hsum := sealSweepOpenCounts_add_le C
  change sealSweepOpenLeaderCount C =
    sealSweepOpenFollowerCount C at hbalanced
  omega

/-- The conserved balance cuts the coefficient of the quadratic rank from
one to one half.  The division is natural-number floor division. -/
theorem sealSweepMixedRank_le_half
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hbalanced : SealSweepOpenBalanced C) :
    sealSweepMixedRank ring C ≤ (n / 2) * n + n := by
  have hdouble := balanced_two_openLeaderCount_le C hbalanced
  have hhalf : sealSweepOpenLeaderCount C ≤ n / 2 := by
    omega
  have hcount := Nat.mul_le_mul_right n hhalf
  have hgap := sealSweepOpenGap_le ring C
  unfold sealSweepMixedRank
  exact Nat.add_le_add hcount hgap

/-- In a genuinely mixed state the gap is strictly below `n`, saving the last
unit in the rank bound. -/
theorem sealSweepMixedRank_le_half_of_not_allClosed
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hbalanced : SealSweepOpenBalanced C)
    (hnotClosed : ¬ SealSweepAllClosed C) :
    sealSweepMixedRank ring C ≤ (n / 2) * n + n - 1 := by
  have hdouble := balanced_two_openLeaderCount_le C hbalanced
  have hhalf : sealSweepOpenLeaderCount C ≤ n / 2 := by
    omega
  have hcount := Nat.mul_le_mul_right n hhalf
  have hgap :=
    (sealSweepOpenGap_pos_lt ring C hbalanced hnotClosed).2
  unfold sealSweepMixedRank
  omega

/-! ## A shorter R91 prefix and the resulting count -/

/-- Normalization followed by the existing all-closed landing theorem reaches
semantic safety within `(floor (n/2))*n + 3n` interactions. -/
theorem sealSweep_balancedPositive_reaches_isSafe_half
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hbalanced : SealSweepOpenBalanced C)
    (hleader : SealSweepHasLeader C) :
    ∃ word : DetSchedule n,
      word.length ≤ (n / 2) * n + 3 * n ∧
      PopulationProtocol.IsSafe
        (P_partialSealSweepProtocol psi kappa tau) ring
        (runLocalSchedule ring P_partialSealSweep C word)
        isLeaderOutput := by
  obtain ⟨pre, hpreLength, hDclosed, hDleader⟩ :=
    sealSweep_balancedPositive_normalizes_rankBound
      ring C hbalanced hleader
  have hpreBound : pre.length ≤ (n / 2) * n + n :=
    Nat.le_trans hpreLength
      (sealSweepMixedRank_le_half ring C hbalanced)
  let D := runLocalSchedule ring P_partialSealSweep C pre
  change SealSweepAllClosed D at hDclosed
  change SealSweepHasLeader D at hDleader
  have hDpositive : 0 < sealSweepLeaderCount D :=
    (sealSweep_hasLeader_iff_leaderCount_pos D).1 hDleader
  obtain ⟨tail, htailLength, htailReach, htailSafe⟩ :=
    sealSweep_allClosedPositive_reaches_isSafe_two_mul_sub_two
      ring D hDclosed hDpositive
  refine ⟨pre ++ tail, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · have hrun :
        runLocalSchedule ring P_partialSealSweep C (pre ++ tail) =
          runLocalSchedule ring P_partialSealSweep D tail := by
      rw [runLocalSchedule_append]
    have hsafeEq := congrArg
      (fun X : SealSweepConfig n psi kappa tau =>
        PopulationProtocol.IsSafe
          (P_partialSealSweepProtocol psi kappa tau) ring X
          isLeaderOutput)
      hrun
    exact Eq.mpr hsafeEq htailSafe

/-- Tight version using the strict mixed-state gap and the exact `2n-2`
landing length. -/
theorem sealSweep_balancedPositive_reaches_isSafe_half_tight
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hbalanced : SealSweepOpenBalanced C)
    (hleader : SealSweepHasLeader C) :
    ∃ word : DetSchedule n,
      word.length ≤ (n / 2) * n + 3 * n - 3 ∧
      PopulationProtocol.IsSafe
        (P_partialSealSweepProtocol psi kappa tau) ring
        (runLocalSchedule ring P_partialSealSweep C word)
        isLeaderOutput := by
  by_cases hclosed : SealSweepAllClosed C
  · have hpositive : 0 < sealSweepLeaderCount C :=
      (sealSweep_hasLeader_iff_leaderCount_pos C).1 hleader
    obtain ⟨word, hlength, hreach, hsafe⟩ :=
      sealSweep_allClosedPositive_reaches_isSafe_two_mul_sub_two
        ring C hclosed hpositive
    exact ⟨word, by omega, hsafe⟩
  · obtain ⟨pre, hpreLength, hDclosed, hDleader⟩ :=
      sealSweep_balancedPositive_normalizes_rankBound
        ring C hbalanced hleader
    have hpreBound : pre.length ≤ (n / 2) * n + n - 1 :=
      Nat.le_trans hpreLength
        (sealSweepMixedRank_le_half_of_not_allClosed
          ring C hbalanced hclosed)
    let D := runLocalSchedule ring P_partialSealSweep C pre
    change SealSweepAllClosed D at hDclosed
    change SealSweepHasLeader D at hDleader
    have hDpositive : 0 < sealSweepLeaderCount D :=
      (sealSweep_hasLeader_iff_leaderCount_pos D).1 hDleader
    obtain ⟨tail, htailLength, htailReach, htailSafe⟩ :=
      sealSweep_allClosedPositive_reaches_isSafe_two_mul_sub_two
        ring D hDclosed hDpositive
    refine ⟨pre ++ tail, ?_, ?_⟩
    · simp only [List.length_append]
      have hn := ring.hn
      omega
    · have hrun :
          runLocalSchedule ring P_partialSealSweep C (pre ++ tail) =
            runLocalSchedule ring P_partialSealSweep D tail := by
        rw [runLocalSchedule_append]
      have hsafeEq := congrArg
        (fun X : SealSweepConfig n psi kappa tau =>
          PopulationProtocol.IsSafe
            (P_partialSealSweepProtocol psi kappa tau) ring X
            isLeaderOutput)
        hrun
      exact Eq.mpr hsafeEq htailSafe

/-- Shorter restart producer on the exact R91 descendant domain. -/
theorem positiveDescendant_boundedLanding_half
    (ring : DirectedRing n) :
    PositiveDescendantBoundedLanding
      (psi := psi) (kappa := kappa) (tau := tau)
      ring ((n / 2) * n + 3 * n - 3) := by
  intro C hdesc _hnotSafe
  obtain ⟨hbalanced, hleader⟩ :=
    positiveDescendant_balanced_hasLeader ring C hdesc
  exact sealSweep_balancedPositive_reaches_isSafe_half_tight
    ring C hbalanced hleader

/-- At R91's original length `n²+3n`, at least
`n^(n²-floor(n/2)*n+3)` scheduler outcomes stabilize.  The exponent is the
uniform suffix left after the shorter balanced-token prefix. -/
theorem positiveDescendant_originalBlock_stabilizingScheduleCount_lower
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hC : SealSweepPositiveDescendant ring C) :
    n ^ (n * n - (n / 2) * n + 3) ≤
      stabilizingScheduleCount
        (P_partialSealSweepProtocol psi kappa tau) ring
        isLeaderOutput C (n * n + 3 * n) := by
  let M := (n / 2) * n + 3 * n - 3
  let S := n * n - (n / 2) * n + 3
  have hhalf : (n / 2) * n ≤ n * n :=
    Nat.mul_le_mul_right n (Nat.div_le_self n 2)
  have hMS : M + S = n * n + 3 * n := by
    dsimp [M, S]
    have hn := ring.hn
    omega
  have hlocal : n ^ S ≤ localHitCount
      ring P_partialSealSweep (sealSweepIsSafeTest ring) C (M + S) :=
    localHitCount_suffix_lower_of_boundedSafeProducer
      ring P_partialSealSweep
      (SealSweepPositiveDescendant ring)
      (fun X => PopulationProtocol.IsSafe
        (P_partialSealSweepProtocol psi kappa tau) ring X
        isLeaderOutput)
      (sealSweepIsSafeTest ring)
      (sealSweepIsSafeTest_spec ring)
      M S (positiveDescendant_boundedLanding_half ring) C hC
  have hsemantic := localHitCount_le_stabilizingScheduleCount
    (P_partialSealSweepProtocol psi kappa tau) ring isLeaderOutput
    (sealSweepIsSafeTest ring) (sealSweepIsSafeTest_spec ring)
    C (M + S)
  rw [hMS] at hlocal hsemantic
  have hresult := Nat.le_trans hlocal hsemantic
  simpa only [S] using hresult

/-- Exact one-block miss numerator corresponding to the multiplicity theorem.
This strictly strengthens R91's `n^L-1` budget for every `n>1`. -/
theorem positiveDescendant_originalBlock_suffixRichSSLEOn
    (ring : DirectedRing n) :
    UniformFiniteHorizonSSLEOn
      (P_partialSealSweepProtocol psi kappa tau) ring isLeaderOutput
      (SealSweepPositiveDescendant ring)
      (n * n + 3 * n)
      (n ^ (n * n + 3 * n) -
        n ^ (n * n - (n / 2) * n + 3)) := by
  intro C hC
  rw [allSchedules_length]
  have hcount :=
    positiveDescendant_originalBlock_stabilizingScheduleCount_lower
      ring C hC
  have hpow : n ^ (n * n - (n / 2) * n + 3) ≤
      n ^ (n * n + 3 * n) := by
    have hhalf : (n / 2) * n ≤ n * n :=
      Nat.mul_le_mul_right n (Nat.div_le_self n 2)
    have hn := ring.hn
    have hexp : n * n - (n / 2) * n + 3 ≤ n * n + 3 * n := by
      omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hexp
    calc
      n ^ (n * n - (n / 2) * n + 3) ≤
          n ^ (n * n - (n / 2) * n + 3) * n ^ d :=
        Nat.le_mul_of_pos_right _ (Nat.pow_pos ring.hn)
      _ = n ^ ((n * n - (n / 2) * n + 3) + d) :=
        (Nat.pow_add n (n * n - (n / 2) * n + 3) d).symm
      _ = n ^ (n * n + 3 * n) :=
        congrArg (fun e => n ^ e) hd.symm
  omega

/-- Closed-domain exact multiplication preserves the improved one-block miss
budget across aligned blocks. -/
theorem positiveDescendant_repeatedBlock_suffixRichSSLEOn
    (ring : DirectedRing n) :
    ∀ blocks,
      UniformFiniteHorizonSSLEOn
        (P_partialSealSweepProtocol psi kappa tau) ring isLeaderOutput
        (SealSweepPositiveDescendant ring)
        (blocks * (n * n + 3 * n))
        ((n ^ (n * n + 3 * n) -
          n ^ (n * n - (n / 2) * n + 3)) ^ blocks) := by
  let M := (n / 2) * n + 3 * n - 3
  let S := n * n - (n / 2) * n + 3
  let L := n * n + 3 * n
  have hhalf : (n / 2) * n ≤ n * n :=
    Nat.mul_le_mul_right n (Nat.div_le_self n 2)
  have hMS : M + S = L := by
    dsimp [M, S, L]
    have hn := ring.hn
    omega
  have hone := boundedSafeProducer_suffixRich_oneBlockPhase
    ring P_partialSealSweep
    (SealSweepPositiveDescendant ring)
    (fun X => PopulationProtocol.IsSafe
      (P_partialSealSweepProtocol psi kappa tau) ring X
      isLeaderOutput)
    (sealSweepIsSafeTest ring)
    (sealSweepIsSafeTest_spec ring)
    M S (positiveDescendant_boundedLanding_half ring)
  rw [hMS] at hone
  have hblocks := uniformFinitePhase_repeatedBlock_on_closedDomain
    ring P_partialSealSweep
    (SealSweepPositiveDescendant ring)
    (fun X => PopulationProtocol.IsSafe
      (P_partialSealSweepProtocol psi kappa tau) ring X
      isLeaderOutput)
    (sealSweepIsSafeTest ring)
    (positiveDescendant_localStepClosed ring)
    L (n ^ L - n ^ S) hone
  intro blocks
  exact uniformFinitePhase_isSafe_to_SSLEOn
    (P_partialSealSweepProtocol psi kappa tau) ring isLeaderOutput
    (SealSweepPositiveDescendant ring)
    (sealSweepIsSafeTest ring)
    (blocks * L) ((n ^ L - n ^ S) ^ blocks)
    (hblocks blocks)

/-! ## Explicit failure-at-most-`1/n` horizons -/

/-- The exact horizon already implicit in R91's singleton-word analysis.
Here `L=n²+3n` and `k=(n-1)(n^L-1)+1`. -/
theorem positiveDescendant_explicitOneOverN_original
    (ring : DirectedRing n) (hn2 : 1 < n) :
    let L := n * n + 3 * n
    let k := (n - 1) * (n ^ L - 1) + 1
    UniformOneOverNFailureAtHorizonOn
      (P_partialSealSweepProtocol psi kappa tau) ring isLeaderOutput
      (SealSweepPositiveDescendant ring) 1 (k * L) := by
  dsimp only
  have hL : 0 < n * n + 3 * n := by
    have hthree : 0 < 3 * n := Nat.mul_pos (by omega) ring.hn
    omega
  exact boundedIsSafeProducer_explicitOneOverNSSLEOn
    (P_partialSealSweepProtocol psi kappa tau) ring isLeaderOutput
    (SealSweepPositiveDescendant ring)
    (sealSweepIsSafeTest ring)
    (sealSweepIsSafeTest_spec ring)
    (positiveDescendant_localStepClosed ring)
    hn2 (n * n + 3 * n) hL
    (positiveDescendant_boundedLanding_poly ring)

/-- The balanced-token packing improvement uses the shorter block
`M=floor(n/2)*n+3n-3`, with the same exact finite-geometric arithmetic. -/
theorem positiveDescendant_explicitOneOverN_half
    (ring : DirectedRing n) (hn2 : 1 < n) :
    let M := (n / 2) * n + 3 * n - 3
    let k := (n - 1) * (n ^ M - 1) + 1
    UniformOneOverNFailureAtHorizonOn
      (P_partialSealSweepProtocol psi kappa tau) ring isLeaderOutput
      (SealSweepPositiveDescendant ring) 1 (k * M) := by
  dsimp only
  have hM : 0 < (n / 2) * n + 3 * n - 3 := by
    have hthree : 0 < 3 * n := Nat.mul_pos (by omega) ring.hn
    omega
  exact boundedIsSafeProducer_explicitOneOverNSSLEOn
    (P_partialSealSweepProtocol psi kappa tau) ring isLeaderOutput
    (SealSweepPositiveDescendant ring)
    (sealSweepIsSafeTest ring)
    (sealSweepIsSafeTest_spec ring)
    (positiveDescendant_localStepClosed ring)
    hn2 ((n / 2) * n + 3 * n - 3) hM
    (positiveDescendant_boundedLanding_half ring)

end PPartialSealSweepIidComplexitySol
end PPLLCompleteMultiLeaderCleanup
