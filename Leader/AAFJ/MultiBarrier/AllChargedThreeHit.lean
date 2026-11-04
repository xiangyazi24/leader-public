import Init.Omega
import Leader.AAFJ.MultiBarrier.PushOne
import Leader.AAFJ.MultiBarrier.AdjacentContact
import Leader.AAFJ.MultiBarrier.DropWordMass
import Leader.Core.LeaderCountPreservation

set_option autoImplicit false

namespace AAFJPK
namespace OriginalThreeCharged

open BarrierAlgebra
open OriginalNonbarrierWord
open FiniteUniformStoppingTree
open FixedSpanRenewalPayload

/-- On a ring of size greater than two, two clockwise successor steps do not
return to the starting vertex. -/
private theorem rightNeighbor_twice_ne_self
    {n : Nat} (ring : DirectedRing n) (hn3 : 2 < n) (e : Fin n) :
    ring.rightNeighbor (ring.rightNeighbor e) ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases h1 : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt h1] at hv
    by_cases h2 : e.val + 1 + 1 < n
    · rw [Nat.mod_eq_of_lt h2] at hv
      omega
    · have hw : e.val + 1 + 1 = n := by omega
      rw [hw, Nat.mod_self] at hv
      omega
  · have hw : e.val + 1 = n := by omega
    rw [hw, Nat.mod_self] at hv
    rw [Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
    omega

/-- Three cyclically consecutive charged edges force a strict barrier-count
drop under the literal original-protocol word `[q,q+,q]`.

No Boolean payload hypothesis is needed: bullet, leader, probe, and phase fields
are arbitrary in the input configuration. -/
theorem three_consecutive_charged_drop3
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (q : Fin n)
    (hq : BarrierAt hk ring (labelsOf C) q)
    (hq1 :
      BarrierAt hk ring (labelsOf C) (ring.rightNeighbor q))
    (hq2 :
      BarrierAt hk ring (labelsOf C)
        (ring.rightNeighbor (ring.rightNeighbor q))) :
    barrierCount hk ring
        (labelsOf
          (rawRun hk ring C [q, ring.rightNeighbor q, q])) <
      barrierCount hk ring (labelsOf C) := by
  have hn2 : 1 < n := by omega
  let q1 := ring.rightNeighbor q
  let q2 := ring.rightNeighbor q1
  let C1 := (protocol k hk).step ring C q
  let C2 := (protocol k hk).step ring C1 q1
  let C3 := (protocol k hk).step ring C2 q

  have hq1C : BarrierAt hk ring (labelsOf C) q1 := by
    simpa [q1] using hq1
  have hq2C : BarrierAt hk ring (labelsOf C) q2 := by
    simpa [q1, q2] using hq2

  have hle1 :
      barrierCount hk ring (labelsOf C1) ≤
        barrierCount hk ring (labelsOf C) := by
    simpa [C1] using
      protocol_step_barrierCount_le hk ring hn2 C q

  by_cases hd1 :
      barrierCount hk ring (labelsOf C1) <
        barrierCount hk ring (labelsOf C)
  · have hle2 :
        barrierCount hk ring (labelsOf C2) ≤
          barrierCount hk ring (labelsOf C1) := by
      simpa [C2] using
        protocol_step_barrierCount_le hk ring hn2 C1 q1
    have hle3 :
        barrierCount hk ring (labelsOf C3) ≤
          barrierCount hk ring (labelsOf C2) := by
      simpa [C3] using
        protocol_step_barrierCount_le hk ring hn2 C2 q
    have hf :
        barrierCount hk ring (labelsOf C3) <
          barrierCount hk ring (labelsOf C) := by
      omega
    simpa [rawRun, C1, C2, C3, q1] using hf

  · have hnot1 : ¬ AdvanceReady hk ring C q := by
      intro hr
      apply hd1
      have hd :=
        adjacent_ready_barrierCount_lt hk ring hn2
          C q q1 rfl hq hq1C hr.2.1
          (by simpa [q1] using hr.2.2)
      simpa [C1] using hd

    have hlabels1 : labelsOf C1 = labelsOf C := by
      simpa [C1] using
        labelsOf_step_eq_self_of_not_ready hk ring C q hnot1
    have hqC1 : BarrierAt hk ring (labelsOf C1) q := by
      rw [hlabels1]
      exact hq
    have hq1C1 : BarrierAt hk ring (labelsOf C1) q1 := by
      rw [hlabels1]
      exact hq1C
    have hq2C1 : BarrierAt hk ring (labelsOf C1) q2 := by
      rw [hlabels1]
      exact hq2C
    have hphase1 : (C1 q).phase = true := by
      simpa [C1] using
        (AAFJPK.OriginalPushOne.barrier_hit_source_controls_public
          hk ring C q hq).2

    have hle2 :
        barrierCount hk ring (labelsOf C2) ≤
          barrierCount hk ring (labelsOf C1) := by
      simpa [C2] using
        protocol_step_barrierCount_le hk ring hn2 C1 q1

    by_cases hd2 :
        barrierCount hk ring (labelsOf C2) <
          barrierCount hk ring (labelsOf C1)
    · have hle3 :
          barrierCount hk ring (labelsOf C3) ≤
            barrierCount hk ring (labelsOf C2) := by
        simpa [C3] using
          protocol_step_barrierCount_le hk ring hn2 C2 q
      have hf :
          barrierCount hk ring (labelsOf C3) <
            barrierCount hk ring (labelsOf C) := by
        omega
      simpa [rawRun, C1, C2, C3, q1] using hf

    · have hnot2 : ¬ AdvanceReady hk ring C1 q1 := by
        intro hr
        apply hd2
        have hd :=
          adjacent_ready_barrierCount_lt hk ring hn2
            C1 q1 q2 rfl hq1C1 hq2C1 hr.2.1
            (by simpa [q2] using hr.2.2)
        simpa [C2] using hd

      have hlabels2 : labelsOf C2 = labelsOf C1 := by
        simpa [C2] using
          labelsOf_step_eq_self_of_not_ready hk ring C1 q1 hnot2
      have hqC2 : BarrierAt hk ring (labelsOf C2) q := by
        rw [hlabels2]
        exact hqC1
      have hq1C2 : BarrierAt hk ring (labelsOf C2) q1 := by
        rw [hlabels2]
        exact hq1C1

      have hprobe2 : (C2 q1).probe = false := by
        simpa [C2] using
          (AAFJPK.OriginalPushOne.barrier_hit_source_controls_public
            hk ring C1 q1 hq1C1).1

      have hq_ne_q1 : q ≠ q1 := by
        dsimp [q1]
        exact (rightNeighbor_ne_self ring hn2 q).symm
      have hq_ne_q2 : q ≠ q2 := by
        dsimp [q1, q2]
        exact (rightNeighbor_twice_ne_self ring hn3 q).symm
      have hsame : C2 q = C1 q := by
        dsimp [C2]
        exact step_preserves_others
          (protocol k hk) ring C1 q1 q
          hq_ne_q1 (by simpa [q2] using hq_ne_q2)
      have hphase2 : (C2 q).phase = true := by
        rw [hsame]
        exact hphase1

      have hd3 :=
        adjacent_ready_barrierCount_lt hk ring hn2
          C2 q q1 rfl hqC2 hq1C2 hphase2 hprobe2
      have hd3' :
          barrierCount hk ring (labelsOf C3) <
            barrierCount hk ring (labelsOf C2) := by
        simpa [C3] using hd3
      have hf :
          barrierCount hk ring (labelsOf C3) <
            barrierCount hk ring (labelsOf C) := by
        omega
      simpa [rawRun, C1, C2, C3, q1] using hf

/-- A selected unit-valued list entry contributes at least one to the sum. -/
private theorem one_le_sum_map_of_mem_eq_one
    {A : Type} (xs : List A) (value : A → Nat) (chosen : A)
    (hmem : chosen ∈ xs) (hone : value chosen = 1) :
    1 ≤ (xs.map value).sum := by
  induction xs with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.map_cons, List.sum_cons]
      rcases hmem with hchosen | htail
      · subst head
        omega
      · have hrec := ih htail
        omega

/-- One explicit successful word contributes at least one scheduler leaf. -/
private theorem one_le_successCount_of_success_word
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (x : StopNode S)
    (w : List (Fin n))
    (hs : runStopped step x w = .success) :
    1 ≤ successCount step x w.length := by
  rw [← B9SpliceMatcherMass.wordSum_success_eq_successCount
    (n := n) step w.length x]
  unfold wordSum
  apply one_le_sum_map_of_mem_eq_one _ _ w.reverse
  · exact mem_allSchedules_of_length n w.length w.reverse (by simp)
  · simp only [List.reverse_reverse, hs]
    rfl

/-- If every physical edge is charged, then the `n` rotated three-letter
words `[q,q+,q]` contribute at least `n` successful leaves at depth three.
The separation is by their distinct first scheduler edge. -/
theorem all_charged_successCount_three
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k)
    (hall : ∀ e : Fin n, BarrierAt hk ring (labelsOf C) e) :
    n ≤
      successCount
        (OriginalDropWordMass.dropStep hk ring C) (.active C) 3 := by
  let step := OriginalDropWordMass.dropStep hk ring C
  have hchild : ∀ q : Fin n,
      1 ≤ successCount step (stepNode step (.active C) q) 2 := by
    intro q
    have hdrop :=
      three_consecutive_charged_drop3 hk ring hn3 C q
        (hall q)
        (hall (ring.rightNeighbor q))
        (hall (ring.rightNeighbor (ring.rightNeighbor q)))
    have hrun :
        runStopped step (.active C)
          [q, ring.rightNeighbor q, q] = .success := by
      simpa [step] using
        (OriginalDropWordMass.raw_drop_word_runs_success
          hk ring C [q, ring.rightNeighbor q, q] hdrop)
    have htail :
        runStopped step (stepNode step (.active C) q)
          [ring.rightNeighbor q, q] = .success := by
      simpa only [runStopped] using hrun
    have hs :=
      one_le_successCount_of_success_word
        step (stepNode step (.active C) q)
          [ring.rightNeighbor q, q] htail
    simpa using hs

  change n ≤
    (List.ofFn (fun q : Fin n =>
      successCount step (stepNode step (.active C) q) 2)).sum
  calc
    n = (List.ofFn (fun _ : Fin n => 1)).sum := by
      rw [ofFn_sum_const]
      simp
    _ ≤
        (List.ofFn (fun q : Fin n =>
          successCount step (stepNode step (.active C) q) 2)).sum := by
      apply ofFn_sum_le
      intro q
      exact hchild q

end OriginalThreeCharged
end AAFJPK

#print axioms AAFJPK.OriginalThreeCharged.three_consecutive_charged_drop3
#print axioms AAFJPK.OriginalThreeCharged.all_charged_successCount_three
