import Leader.AAFJ.MultiBarrier.AdjacentBarrierDrop
import Leader.Core.FiniteUniformStoppingTree

set_option autoImplicit false

namespace AAFJPK.AdjacentContactCylinder

open BarrierAlgebra
open FiniteUniformStoppingTree
open OriginalNonbarrierWord
open OriginalArbitraryRemote

/-- Strict drop relative to the root of this adjacent-contact cylinder. -/
def dropDone {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C0 D : Fin n → State k) : Prop :=
  barrierCount hk ring (labelsOf D) < barrierCount hk ring (labelsOf C0)

/-- Literal original step, absorbed at the first strict barrier-count drop. -/
noncomputable def dropStep {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C0 : Fin n → State k) :
    (Fin n → State k) → Fin n → StopNode (Fin n → State k) := by
  classical
  intro D e
  let E := (protocol k hk).step ring D e
  exact if dropDone hk ring C0 E then .success else .active E

private theorem le_sum_of_mem {a : Nat} {xs : List Nat} (ha : a ∈ xs) :
    a ≤ xs.sum := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      simp only [List.mem_cons] at ha
      simp only [List.sum_cons]
      rcases ha with rfl | ha
      · omega
      · exact Nat.le_trans (ih ha) (Nat.le_add_left _ _)

private theorem raw_drop_word_successCount_one_from
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn0 : 0 < n)
    (C0 D : Fin n → State k) (w : List (Fin n))
    (hD : ¬ dropDone hk ring C0 D)
    (hdrop : dropDone hk ring C0 (rawRun hk ring D w)) :
    1 ≤ successCount (dropStep hk ring C0) (.active D) w.length := by
  classical
  induction w generalizing D with
  | nil =>
      have : dropDone hk ring C0 D := by simpa [rawRun] using hdrop
      exact (hD this).elim
  | cons e es ih =>
      let E := (protocol k hk).step ring D e
      by_cases hE : dropDone hk ring C0 E
      · simp only [List.length_cons, successCount, treeWeight, stepNode]
        have hpow : 1 ≤ n ^ es.length := Nat.one_le_pow es.length n hn0
        apply Nat.le_trans hpow
        apply le_sum_of_mem
        rw [List.mem_ofFn]
        refine ⟨e, ?_⟩
        simp only [dropStep, E, hE, if_pos, treeWeight_success,
          successWeight, Nat.mul_one]
      · have htail : dropDone hk ring C0 (rawRun hk ring E es) := by
          simpa [rawRun, E] using hdrop
        have hchild := ih E hE htail
        simp only [List.length_cons, successCount, treeWeight, stepNode]
        apply Nat.le_trans hchild
        apply le_sum_of_mem
        rw [List.mem_ofFn]
        refine ⟨e, ?_⟩
        simp only [dropStep, E, hE, if_neg]
        rfl

private theorem raw_drop_word_successCount_one
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn0 : 0 < n)
    (C : Fin n → State k) (w : List (Fin n))
    (hdrop :
      barrierCount hk ring (labelsOf (rawRun hk ring C w)) <
        barrierCount hk ring (labelsOf C)) :
    1 ≤ successCount (dropStep hk ring C) (.active C) w.length := by
  apply raw_drop_word_successCount_one_from hk ring hn0 C C w
  · simp [dropDone]
  · exact hdrop

/-- Absorption pads every successful prefix by all raw suffixes. -/
private theorem successCount_padding
    {n : Nat} {S : Type}
    (step : S → Fin n → StopNode S) (z : StopNode S) (U K : Nat) :
    n ^ K * successCount step z U ≤ successCount step z (U + K) := by
  have one_step : ∀ (x : StopNode S) (T : Nat),
      n * successCount step x T ≤ successCount step x (T + 1) := by
    intro x T
    induction T generalizing x with
    | zero =>
        cases x with
        | active s => simp [successCount, treeWeight, successWeight]
        | failure => simp [successCount, treeWeight, successWeight]
        | success =>
            simp only [successCount, treeWeight, successWeight, stepNode,
              Nat.mul_one, Nat.zero_add]
            rw [ofFn_sum_const]
            simp
    | succ T ih =>
        change n * (List.ofFn (fun e : Fin n =>
          successCount step (stepNode step x e) T)).sum ≤
          (List.ofFn (fun e : Fin n =>
            successCount step (stepNode step x e) (T + 1))).sum
        rw [← ofFn_sum_mul_left]
        exact ofFn_sum_le _ _ (fun e => ih (stepNode step x e))
  induction K with
  | zero => simp
  | succ K ih =>
      calc
        n ^ (K + 1) * successCount step z U =
            n * (n ^ K * successCount step z U) := by
          rw [Nat.pow_succ]
          ac_rfl
        _ ≤ n * successCount step z (U + K) := Nat.mul_le_mul_left n ih
        _ ≤ successCount step z ((U + K) + 1) := one_step z (U + K)
        _ = successCount step z (U + (K + 1)) := by rw [Nat.add_assoc]

private theorem rawRun_append
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (u v : List (Fin n)) :
    rawRun hk ring C (u ++ v) = rawRun hk ring (rawRun hk ring C u) v := by
  induction u generalizing C with
  | nil => rfl
  | cons e es ih =>
      simp only [List.cons_append, rawRun]
      exact ih ((protocol k hk).step ring C e)

/-- Barrier count cannot increase along an arbitrary literal scheduler word. -/
theorem barrierCount_rawRun_le
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (w : List (Fin n)) :
    barrierCount hk ring (labelsOf (rawRun hk ring C w)) ≤
      barrierCount hk ring (labelsOf C) := by
  induction w generalizing C with
  | nil => simp [rawRun]
  | cons e es ih =>
      have hstep := protocol_step_barrierCount_le hk ring hn2 C e
      have htail := ih ((protocol k hk).step ring C e)
      exact Nat.le_trans (by simpa [rawRun] using htail) hstep

/-- Once a literal prefix has strictly lowered barrier count, every physical
suffix stays strictly below the count at the cylinder root. -/
theorem strict_drop_prefix_all_suffixes
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (w : List (Fin n))
    (hdrop :
      barrierCount hk ring (labelsOf (rawRun hk ring C w)) <
        barrierCount hk ring (labelsOf C)) :
    ∀ v : List (Fin n),
      barrierCount hk ring (labelsOf (rawRun hk ring C (w ++ v))) <
        barrierCount hk ring (labelsOf C) := by
  intro v
  rw [rawRun_append]
  have hsuffix := barrierCount_rawRun_le hk ring hn2 (rawRun hk ring C w) v
  omega

/-- Adjacent charged edges select a real guard-dependent prefix of length at
most six, and every arbitrary physical suffix remains a strict drop. -/
theorem adjacent_drop_cylinder
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (q : Fin n)
    (hq : BarrierAt hk ring (labelsOf C) q)
    (hqnext : BarrierAt hk ring (labelsOf C) (ring.rightNeighbor q)) :
    ∃ w : List (Fin n), w.length ≤ 6 ∧
      ∀ v : List (Fin n),
        barrierCount hk ring (labelsOf (rawRun hk ring C (w ++ v))) <
          barrierCount hk ring (labelsOf C) := by
  obtain ⟨w, hw, hdrop⟩ :=
    adjacent_barriers_bounded_drop hk ring hn3 C q hq hqnext
  exact ⟨w, hw, strict_drop_prefix_all_suffixes hk ring (by omega) C w hdrop⟩

/-- Exact stopped-tree cylinder mass at every common horizon `T ≥ 6`.
The selected source prefix may have length 1, 2, 3, or 6; its unrestricted
suffix contributes at least `n^(T-6)` scheduler words. -/
theorem adjacent_drop_successCount_pow
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (q : Fin n)
    (hq : BarrierAt hk ring (labelsOf C) q)
    (hqnext : BarrierAt hk ring (labelsOf C) (ring.rightNeighbor q))
    (T : Nat) (hT : 6 ≤ T) :
    n ^ (T - 6) ≤
      successCount (dropStep hk ring C) (.active C) T := by
  obtain ⟨w, hwlen, hdrop⟩ :=
    adjacent_barriers_bounded_drop hk ring hn3 C q hq hqnext
  have hwT : w.length ≤ T := by omega
  have hone :
      1 ≤ successCount (dropStep hk ring C) (.active C) w.length :=
    raw_drop_word_successCount_one hk ring (by omega) C w hdrop
  have hpad := successCount_padding
    (dropStep hk ring C) (.active C) w.length (T - w.length)
  have hmul :
      n ^ (T - w.length) ≤
        n ^ (T - w.length) *
          successCount (dropStep hk ring C) (.active C) w.length := by
    simpa using Nat.mul_le_mul_left (n ^ (T - w.length)) hone
  have hsT :
      n ^ (T - w.length) ≤
        successCount (dropStep hk ring C) (.active C) T := by
    calc
      n ^ (T - w.length) ≤
          n ^ (T - w.length) *
            successCount (dropStep hk ring C) (.active C) w.length := hmul
      _ ≤ successCount (dropStep hk ring C) (.active C)
          (w.length + (T - w.length)) := hpad
      _ = successCount (dropStep hk ring C) (.active C) T := by
        rw [Nat.add_sub_of_le hwT]
  exact Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) hsT

/-- Denominator-cleared form: at every horizon `T ≥ 6`, the exact uniform
scheduler success probability is at least `n⁻⁶`. -/
theorem adjacent_drop_mass_one_over_pow_six
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (q : Fin n)
    (hq : BarrierAt hk ring (labelsOf C) q)
    (hqnext : BarrierAt hk ring (labelsOf C) (ring.rightNeighbor q))
    (T : Nat) (hT : 6 ≤ T) :
    n ^ T ≤ n ^ 6 *
      successCount (dropStep hk ring C) (.active C) T := by
  have hs := adjacent_drop_successCount_pow hk ring hn3 C q hq hqnext T hT
  calc
    n ^ T = n ^ 6 * n ^ (T - 6) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hT]
    _ ≤ n ^ 6 * successCount (dropStep hk ring C) (.active C) T :=
      Nat.mul_le_mul_left (n ^ 6) hs

#print axioms barrierCount_rawRun_le
#print axioms strict_drop_prefix_all_suffixes
#print axioms adjacent_drop_cylinder
#print axioms adjacent_drop_successCount_pow
#print axioms adjacent_drop_mass_one_over_pow_six

end AAFJPK.AdjacentContactCylinder
