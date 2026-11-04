import Leader.AAFJ.MultiBarrier.GlobalCountDrop
import Leader.AAFJ.MultiBarrier.ConsecutiveBarrierSupport
import Leader.AAFJ.MultiBarrier.AdjacentBarrierDrop

set_option autoImplicit false

namespace AAFJPK.GlobalBarrierCountDropAssembly

open BarrierAlgebra
open GlobalBarrierCountDrop
open OriginalArbitraryRemote
open OriginalNonbarrierWord
open PPLLNoCheckBirthConditionTwoGeometry

private theorem rawRun_append
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (u v : List (Fin n)) :
    rawRun hk ring C (u ++ v) =
      rawRun hk ring (rawRun hk ring C u) v := by
  induction u generalizing C with
  | nil => rfl
  | cons e es ih =>
      simp only [List.cons_append, rawRun]
      exact ih ((protocol k hk).step ring C e)

private theorem barrierCount_le_ringSize
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) :
    barrierCount hk ring (labelsOf C) ≤ n := by
  unfold barrierCount barrierSupport
  exact Nat.le_trans (List.length_filter_le _ _)
    (by simp [ExhaustiveList.fin])

private theorem cwDist_pos_of_ne
    {n : Nat} (ring : DirectedRing n) {a b : Fin n} (hne : a ≠ b) :
    0 < cwDist ring a b := by
  apply Nat.pos_of_ne_zero
  intro hd
  have hp := cwPos_cwDist ring a b
  rw [hd, cwPos_zero] at hp
  exact hne hp

private theorem select_consecutive
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k)
    (hcount : 1 < barrierCount hk ring (labelsOf C)) :
    ∃ q r : Fin n, ConsecutiveCharged hk ring C q r := by
  obtain ⟨q, r, hne, hq, hr, hpos, hbetween⟩ :=
    ArbitrarySupportGeometry.exists_cw_consecutive_barriers_of_count_gt_one
      hk ring (labelsOf C) hcount
  have hpos' : 0 < cwDist ring q r := by
    simpa [AAFJPK.SingleBarrierSanitation.cwDist,
      PPLLNoCheckBirthConditionTwoGeometry.cwDist] using hpos
  have hbetween' : ∀ e, BarrierAt hk ring (labelsOf C) e →
      ¬ (0 < cwDist ring q e ∧ cwDist ring q e < cwDist ring q r) := by
    intro e he h
    exact hbetween e he (by
      simpa [AAFJPK.SingleBarrierSanitation.cwDist,
        PPLLNoCheckBirthConditionTwoGeometry.cwDist] using h)
  exact ⟨q, r, ⟨hq, hr, hne, by
    intro e he hqe her
    exact hbetween' e he ⟨hqe, her⟩⟩⟩

/- The main assembly is stated with `2 < n`: the accepted adjacent terminal
   lemma has this genuine small-ring precondition.  The barrier-count premise
   is only `1 < count`; no exact-two or support-size assumption is carried. -/
theorem barrierCount_gt_one_strict_drop_word
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k)
    (hcount : 1 < barrierCount hk ring (labelsOf C)) :
    ∃ word : List (Fin n),
      word.length ≤ 4 * (n - 2) + 6 ∧
      barrierCount hk ring
          (labelsOf (rawRun hk ring C word)) <
        barrierCount hk ring (labelsOf C) := by
  have hn2 : 1 < n := by omega
  obtain ⟨q, r, hc⟩ := select_consecutive hk ring C hcount
  obtain ⟨pre, a, hpre, har, hca, hperm, hcountEq⟩ :=
    consecutive_reach_adjacent hk ring hn2 C q r hc
  let D := rawRun hk ring C pre
  have hfront : BarrierAt hk ring (labelsOf D) (ring.rightNeighbor a) := by
    rw [har]
    simpa [D] using hca.r_charged
  obtain ⟨u, hu, hdrop⟩ :=
    adjacent_barriers_bounded_drop hk ring hn3 D a
      hca.q_charged hfront
  have hdpos : 0 < cwDist ring q r := cwDist_pos_of_ne ring hc.ne
  have hdlt : cwDist ring q r < n := cwDist_lt ring q r
  have hpre' : pre.length ≤ 4 * (n - 2) := by
    omega
  refine ⟨pre ++ u, ?_, ?_⟩
  · rw [List.length_append]
    omega
  · rw [rawRun_append]
    have hdropD :
        barrierCount hk ring (labelsOf (rawRun hk ring D u)) <
          barrierCount hk ring (labelsOf D) := hdrop
    rw [hcountEq] at hdropD
    simpa [D] using hdropD

theorem barrierCount_gt_two_strict_drop_word
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k)
    (hcount : 2 < barrierCount hk ring (labelsOf C)) :
    ∃ word : List (Fin n),
      word.length ≤ 4 * (n - 2) + 6 ∧
      barrierCount hk ring
          (labelsOf (rawRun hk ring C word)) <
        barrierCount hk ring (labelsOf C) := by
  have hn3 : 2 < n := by
    have hle := barrierCount_le_ringSize hk ring C
    omega
  exact barrierCount_gt_one_strict_drop_word hk ring hn3 C (by omega)

#print axioms barrierCount_gt_one_strict_drop_word
#print axioms barrierCount_gt_two_strict_drop_word

end AAFJPK.GlobalBarrierCountDropAssembly
