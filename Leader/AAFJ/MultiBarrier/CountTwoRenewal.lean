import Leader.AAFJ.MultiBarrier.PushIterate
import Leader.AAFJ.MultiBarrier.DropWordMass
import Leader.Core.UniformBlockRenewalCost

set_option autoImplicit false

namespace AAFJPK.OriginalCountTwoRenewal

open BarrierAlgebra
open OriginalNonbarrierWord
open FiniteUniformStoppingTree
open FixedSpanRenewalPayload

def blockLen (n : Nat) : Nat := 4 * (n - 2) + 6

abbrev CountTwoState {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) :=
  {D : Fin n → State k //
    barrierCount hk ring (labelsOf D) = 2}

private theorem child_count_eq_two
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 2 < n) (hndvd : ¬ k ∣ n)
    (s : CountTwoState hk ring) (e : Fin n)
    (hnot :
      ¬ barrierCount hk ring
          (labelsOf ((protocol k hk).step ring s.1 e)) < 2) :
    barrierCount hk ring
        (labelsOf ((protocol k hk).step ring s.1 e)) = 2 := by
  have hle :=
    protocol_step_barrierCount_le hk ring (by omega) s.1 e
  rw [s.2] at hle
  have hpos :=
    barrierCount_pos_of_not_dvd hk ring
      ((protocol k hk).step ring s.1 e) hndvd
  omega

/-- Real original-AAFJ child; stop exactly when its count falls below two.
Every non-success child carries its proof that the count is still exactly two. -/
noncomputable def countTwoStep
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 2 < n) (hndvd : ¬ k ∣ n)
    (s : CountTwoState hk ring) (e : Fin n) :
    StopNode (CountTwoState hk ring) :=
  let E := (protocol k hk).step ring s.1 e
  if hdrop : barrierCount hk ring (labelsOf E) < 2 then
    .success
  else
    .active ⟨E, by
      exact child_count_eq_two hk ring hn3 hndvd s e
        (by simpa [E] using hdrop)⟩

theorem countTwoStep_ne_failure
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 2 < n) (hndvd : ¬ k ∣ n)
    (s : CountTwoState hk ring) (e : Fin n) :
    countTwoStep hk ring hn3 hndvd s e ≠ .failure := by
  unfold countTwoStep
  dsimp
  split <;> simp

/-- Count two is equivalent to an oriented exact-two support witness. -/
private theorem exists_exactTwo_support
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (s : CountTwoState hk ring) :
    ∃ q r, ExactTwoBarrierSupport hk ring s.1 q r := by
  classical
  generalize hS :
    barrierSupport hk ring (labelsOf s.1) = S
  have hlen : S.length = 2 := by
    have h := s.2
    change
      (barrierSupport hk ring (labelsOf s.1)).length = 2 at h
    rw [hS] at h
    exact h
  have hnodup : S.Nodup := by
    have h := barrierSupport_nodup hk ring (labelsOf s.1)
    rw [hS] at h
    exact h
  cases S with
  | nil =>
      simp at hlen
  | cons q t =>
      cases t with
      | nil =>
          simp at hlen
      | cons r u =>
          have huLen : u.length = 0 := by
            simpa using hlen
          have hu : u = [] := List.eq_nil_of_length_eq_zero huLen
          subst u
          have hqr : q ≠ r := by
            simpa using hnodup
          refine ⟨q, r, hqr, ?_⟩
          intro e
          rw [← mem_barrierSupport_iff hk ring (labelsOf s.1) e, hS]
          simp

@[simp] private theorem runStopped_success
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (w : List (Fin n)) :
    runStopped step (.success : StopNode S) w = .success := by
  induction w with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem runStopped_append
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (x : StopNode S) (u v : List (Fin n)) :
    runStopped step x (u ++ v) =
      runStopped step (runStopped step x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e es ih =>
      simp only [List.cons_append, runStopped]
      exact ih (stepNode step x e)

/-- Endpoint raw count < 2 implies success in the proof-carrying stopped tree.
If success happened earlier, absorption consumes the remaining suffix. -/
private theorem runStopped_success_of_raw_drop
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 2 < n) (hndvd : ¬ k ∣ n)
    (s : CountTwoState hk ring) (w : List (Fin n))
    (hdrop :
      barrierCount hk ring
        (labelsOf (rawRun hk ring s.1 w)) < 2) :
    runStopped (countTwoStep hk ring hn3 hndvd)
      (.active s) w = .success := by
  induction w generalizing s with
  | nil =>
      simp [rawRun] at hdrop
      rw [s.2] at hdrop
      omega
  | cons e es ih =>
      let E := (protocol k hk).step ring s.1 e
      by_cases hE :
          barrierCount hk ring (labelsOf E) < 2
      · have hstep :
            countTwoStep hk ring hn3 hndvd s e = .success := by
          simp [countTwoStep, E, hE]
        simp only [runStopped, stepNode]
        rw [hstep]
        exact runStopped_success _ es
      · have hnot :
            ¬ barrierCount hk ring
                (labelsOf ((protocol k hk).step ring s.1 e)) < 2 := by
          simpa [E] using hE
        let sE : CountTwoState hk ring :=
          ⟨E, child_count_eq_two hk ring hn3 hndvd s e hnot⟩
        have htail :
            barrierCount hk ring
              (labelsOf (rawRun hk ring sE.1 es)) < 2 := by
          simpa [rawRun, E, sE] using hdrop
        have hrec := ih sE htail
        have hstep :
            countTwoStep hk ring hn3 hndvd s e = .active sE := by
          simp [countTwoStep, E, hE, sE]
        simp only [runStopped, stepNode]
        rw [hstep]
        exact hrec

/-- The accepted deterministic exact-two producer succeeds in this stopped tree. -/
private theorem countTwo_short_success_word
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 2 < n) (hndvd : ¬ k ∣ n)
    (s : CountTwoState hk ring) :
    ∃ w : List (Fin n),
      w.length ≤ blockLen n ∧
      runStopped (countTwoStep hk ring hn3 hndvd)
        (.active s) w = .success := by
  obtain ⟨q, r, hs⟩ := exists_exactTwo_support hk ring s
  obtain ⟨w, hw, hdrop⟩ :=
    AAFJPK.OriginalPushIter.exactTwo_strict_drop_word
      hk ring hn3 s.1 q r hs
  have hdrop2 :
      barrierCount hk ring (labelsOf (rawRun hk ring s.1 w)) < 2 := by
    rw [s.2] at hdrop
    exact hdrop
  exact ⟨w, by simpa [blockLen] using hw,
    runStopped_success_of_raw_drop hk ring hn3 hndvd s w hdrop2⟩

/-- Pad a successful word to the fixed renewal horizon. -/
private theorem countTwo_padded_success_word
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 2 < n) (hndvd : ¬ k ∣ n)
    (s : CountTwoState hk ring) :
    ∃ w : List (Fin n),
      w.length = blockLen n ∧
      runStopped (countTwoStep hk ring hn3 hndvd)
        (.active s) w = .success := by
  obtain ⟨u, huLen, hu⟩ :=
    countTwo_short_success_word hk ring hn3 hndvd s
  let z : Fin n := ⟨0, by omega⟩
  let w := u ++ List.replicate (blockLen n - u.length) z
  refine ⟨w, ?_, ?_⟩
  · dsimp [w]
    simp only [List.length_append, List.length_replicate]
    omega
  · dsimp [w]
    rw [runStopped_append, hu]
    exact runStopped_success _ _

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

/-- One explicit successful word contributes one scheduler leaf. -/
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

/-- Uniform one-block success numerator on every proof-carrying count-two state. -/
theorem countTwo_successCount_one
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 2 < n) (hndvd : ¬ k ∣ n)
    (s : CountTwoState hk ring) :
    1 ≤ successCount (countTwoStep hk ring hn3 hndvd)
      (.active s) (blockLen n) := by
  obtain ⟨w, hw, hs⟩ :=
    countTwo_padded_success_word hk ring hn3 hndvd s
  have h :=
    one_le_successCount_of_success_word
      (countTwoStep hk ring hn3 hndvd) (.active s) w hs
  simpa [hw] using h

/-- H2 for UniformBlockRenewal with q=1, K=L, q'=n^L. -/
theorem countTwo_block_mass
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 2 < n) (hndvd : ¬ k ∣ n)
    (s : CountTwoState hk ring) :
    n ^ blockLen n ≤
      n ^ blockLen n *
        successCount (countTwoStep hk ring hn3 hndvd)
          (.active s) (blockLen n) := by
  have hs := countTwo_successCount_one hk ring hn3 hndvd s
  simpa using Nat.mul_le_mul_left (n ^ blockLen n) hs

/-- Existing uniform-block renewal gives the geometric active tail. -/
theorem countTwo_block_tail
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 2 < n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k)
    (hC2 : barrierCount hk ring (labelsOf C) = 2)
    (m : Nat) :
    (n ^ blockLen n) ^ m *
        activeCount (countTwoStep hk ring hn3 hndvd)
          (.active (⟨C, hC2⟩ : CountTwoState hk ring))
          (m * blockLen n) ≤
      (n ^ blockLen n - 1) ^ m *
        n ^ (m * blockLen n) := by
  have hq' : 0 < n ^ blockLen n := Nat.pow_pos (by omega)
  have hmass :
      ∀ s : CountTwoState hk ring,
        n ^ (1 * blockLen n) ≤
          n ^ blockLen n *
            successCount (countTwoStep hk ring hn3 hndvd)
              (.active s) (1 * blockLen n) := by
    intro s
    simpa using countTwo_block_mass hk ring hn3 hndvd s
  have h :=
    UniformBlockRenewal.block_tail
      (step := countTwoStep hk ring hn3 hndvd)
      (n := n) (K := blockLen n) (q := 1)
      (q' := n ^ blockLen n)
      hq'
      (countTwoStep_ne_failure hk ring hn3 hndvd)
      hmass
      (⟨C, hC2⟩ : CountTwoState hk ring) m
  simpa [UniformBlockRenewal.retry] using h

/-- Existing cost theorem: normalized truncated cost is at most n^L * L. -/
theorem countTwo_truncated_cost
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 2 < n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k)
    (hC2 : barrierCount hk ring (labelsOf C) = 2)
    (T : Nat) :
    truncatedActiveCostNumerator
        (countTwoStep hk ring hn3 hndvd)
        (.active (⟨C, hC2⟩ : CountTwoState hk ring)) T ≤
      n ^ T * (n ^ blockLen n * blockLen n) := by
  have hq' : 0 < n ^ blockLen n := Nat.pow_pos (by omega)
  have hmass :
      ∀ s : CountTwoState hk ring,
        n ^ (1 * blockLen n) ≤
          n ^ blockLen n *
            successCount (countTwoStep hk ring hn3 hndvd)
              (.active s) (1 * blockLen n) := by
    intro s
    simpa using countTwo_block_mass hk ring hn3 hndvd s
  have h :=
    UniformBlockRenewalCost.truncatedActiveCostNumerator_block_geometric_le
      (step := countTwoStep hk ring hn3 hndvd)
      (n := n) (K := blockLen n) (q := 1)
      (q' := n ^ blockLen n)
      hq'
      (countTwoStep_ne_failure hk ring hn3 hndvd)
      hmass
      (⟨C, hC2⟩ : CountTwoState hk ring) T
  simpa using h

end AAFJPK.OriginalCountTwoRenewal

#print axioms AAFJPK.OriginalCountTwoRenewal.countTwoStep_ne_failure
#print axioms AAFJPK.OriginalCountTwoRenewal.countTwo_successCount_one
#print axioms AAFJPK.OriginalCountTwoRenewal.countTwo_block_mass
#print axioms AAFJPK.OriginalCountTwoRenewal.countTwo_block_tail
#print axioms AAFJPK.OriginalCountTwoRenewal.countTwo_truncated_cost
