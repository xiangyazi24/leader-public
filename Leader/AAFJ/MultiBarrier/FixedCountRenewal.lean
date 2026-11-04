import Leader.AAFJ.MultiBarrier.GlobalCountDropAssembly
import Leader.Core.UniformBlockRenewalCost
import Leader.Wu.Splice.MatcherMass

set_option autoImplicit false

namespace AAFJPK.OriginalMultiBarrierRenewal

open BarrierAlgebra
open OriginalNonbarrierWord
open GlobalBarrierCountDropAssembly
open FiniteUniformStoppingTree
open FixedSpanRenewalPayload

/-- Common horizon of the accepted strict-drop word from any count above one. -/
def blockLen (n : Nat) : Nat := 4 * (n - 2) + 6

/-- Proof-carrying carrier for one fixed barrier-count level. -/
abbrev FixedCountState {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (b : Nat) :=
  {D : Fin n → State k // barrierCount hk ring (labelsOf D) = b}

private theorem child_count_eq
    {n k b : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (s : FixedCountState hk ring b) (e : Fin n)
    (hnot : ¬ barrierCount hk ring
      (labelsOf ((protocol k hk).step ring s.1 e)) < b) :
    barrierCount hk ring
      (labelsOf ((protocol k hk).step ring s.1 e)) = b := by
  have hle := protocol_step_barrierCount_le hk ring hn2 s.1 e
  rw [s.2] at hle
  omega

/-- Actual original transition, stopped precisely on leaving the fixed count
level downward.  Monotonicity proves every other child remains in the carrier. -/
noncomputable def fixedCountStep
    {n k b : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (s : FixedCountState hk ring b) (e : Fin n) :
    StopNode (FixedCountState hk ring b) :=
  let E := (protocol k hk).step ring s.1 e
  if hdrop : barrierCount hk ring (labelsOf E) < b then
    .success
  else
    .active ⟨E, child_count_eq hk ring hn2 s e (by simpa [E] using hdrop)⟩

theorem fixedCountStep_ne_failure
    {n k b : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (s : FixedCountState hk ring b) (e : Fin n) :
    fixedCountStep hk ring hn2 s e ≠ .failure := by
  unfold fixedCountStep
  dsimp
  split <;> simp

@[simp] private theorem runStopped_success
    {S : Type} {n : Nat} (step : S → Fin n → StopNode S)
    (w : List (Fin n)) :
    runStopped step (.success : StopNode S) w = .success := by
  induction w with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem runStopped_append
    {S : Type} {n : Nat} (step : S → Fin n → StopNode S)
    (x : StopNode S) (u v : List (Fin n)) :
    runStopped step x (u ++ v) =
      runStopped step (runStopped step x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e es ih =>
      simp only [List.cons_append, runStopped]
      exact ih (stepNode step x e)

private theorem runStopped_success_of_raw_drop
    {n k b : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (s : FixedCountState hk ring b) (w : List (Fin n))
    (hdrop : barrierCount hk ring (labelsOf (rawRun hk ring s.1 w)) < b) :
    runStopped (fixedCountStep hk ring hn2) (.active s) w = .success := by
  induction w generalizing s with
  | nil =>
      simp [rawRun] at hdrop
      rw [s.2] at hdrop
      omega
  | cons e es ih =>
      let E := (protocol k hk).step ring s.1 e
      by_cases hE : barrierCount hk ring (labelsOf E) < b
      · have hstep : fixedCountStep hk ring hn2 s e = .success := by
          simp [fixedCountStep, E, hE]
        simp only [runStopped, stepNode]
        rw [hstep]
        exact runStopped_success _ es
      · let sE : FixedCountState hk ring b :=
          ⟨E, child_count_eq hk ring hn2 s e (by simpa [E] using hE)⟩
        have htail :
            barrierCount hk ring (labelsOf (rawRun hk ring sE.1 es)) < b := by
          simpa [rawRun, E, sE] using hdrop
        have hrec := ih sE htail
        have hstep : fixedCountStep hk ring hn2 s e = .active sE := by
          simp [fixedCountStep, E, hE, sE]
        simp only [runStopped, stepNode]
        rw [hstep]
        exact hrec

private theorem fixedCount_short_success_word
    {n k b : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (hb : 1 < b) (s : FixedCountState hk ring b) :
    ∃ w : List (Fin n), w.length ≤ blockLen n ∧
      runStopped (fixedCountStep hk ring (by omega)) (.active s) w = .success := by
  obtain ⟨w, hw, hdrop⟩ :=
    barrierCount_gt_one_strict_drop_word hk ring hn3 s.1 (by simpa [s.2])
  have hdropb :
      barrierCount hk ring (labelsOf (rawRun hk ring s.1 w)) < b := by
    simpa [s.2] using hdrop
  exact ⟨w, by simpa [blockLen] using hw,
    runStopped_success_of_raw_drop hk ring (by omega) s w hdropb⟩

private theorem fixedCount_padded_success_word
    {n k b : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (hb : 1 < b) (s : FixedCountState hk ring b) :
    ∃ w : List (Fin n), w.length = blockLen n ∧
      runStopped (fixedCountStep hk ring (by omega)) (.active s) w = .success := by
  obtain ⟨u, huLen, hu⟩ :=
    fixedCount_short_success_word hk ring hn3 hb s
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

private theorem one_le_successCount_of_success_word
    {S : Type} {n : Nat} (step : S → Fin n → StopNode S)
    (x : StopNode S) (w : List (Fin n))
    (hs : runStopped step x w = .success) :
    1 ≤ successCount step x w.length := by
  rw [← B9SpliceMatcherMass.wordSum_success_eq_successCount
    (n := n) step w.length x]
  unfold wordSum
  apply one_le_sum_map_of_mem_eq_one _ _ w.reverse
  · exact mem_allSchedules_of_length n w.length w.reverse (by simp)
  · simp only [List.reverse_reverse, hs]
    rfl

/-- Every proof-carrying level `b>1` has at least one successful raw scheduler
word at the common horizon `4(n-2)+6`. -/
theorem fixedCount_successCount_one
    {n k b : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (hb : 1 < b) (s : FixedCountState hk ring b) :
    1 ≤ successCount (fixedCountStep hk ring (by omega))
      (.active s) (blockLen n) := by
  obtain ⟨w, hw, hs⟩ := fixedCount_padded_success_word hk ring hn3 hb s
  have h := one_le_successCount_of_success_word
    (fixedCountStep hk ring (by omega)) (.active s) w hs
  simpa [hw] using h

/-- One-block success mass in the exact division-free form required by uniform
renewal. -/
theorem fixedCount_block_mass
    {n k b : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (hb : 1 < b) (s : FixedCountState hk ring b) :
    n ^ blockLen n ≤ n ^ blockLen n *
      successCount (fixedCountStep hk ring (by omega))
        (.active s) (blockLen n) := by
  have hs := fixedCount_successCount_one hk ring hn3 hb s
  simpa using Nat.mul_le_mul_left (n ^ blockLen n) hs

/-- Geometric active tail on any fixed multi-barrier level. -/
theorem fixedCount_block_tail
    {n k b : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (hb : 1 < b) (C : Fin n → State k)
    (hCb : barrierCount hk ring (labelsOf C) = b) (m : Nat) :
    (n ^ blockLen n) ^ m *
        activeCount (fixedCountStep hk ring (by omega))
          (.active (⟨C, hCb⟩ : FixedCountState hk ring b))
          (m * blockLen n) ≤
      (n ^ blockLen n - 1) ^ m * n ^ (m * blockLen n) := by
  have hq' : 0 < n ^ blockLen n := Nat.pow_pos (by omega)
  have hmass : ∀ s : FixedCountState hk ring b,
      n ^ (1 * blockLen n) ≤ n ^ blockLen n *
        successCount (fixedCountStep hk ring (by omega))
          (.active s) (1 * blockLen n) := by
    intro s
    simpa using fixedCount_block_mass hk ring hn3 hb s
  have h := UniformBlockRenewal.block_tail
    (step := fixedCountStep hk ring (by omega))
    (n := n) (K := blockLen n) (q := 1) (q' := n ^ blockLen n)
    hq' (fixedCountStep_ne_failure hk ring (by omega)) hmass
    (⟨C, hCb⟩ : FixedCountState hk ring b) m
  simpa [UniformBlockRenewal.retry] using h

/-- The normalized truncated active cost is at most `L*n^L`, uniformly over
all initial states on a fixed barrier-count level above one. -/
theorem fixedCount_truncated_cost
    {n k b : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (hb : 1 < b) (C : Fin n → State k)
    (hCb : barrierCount hk ring (labelsOf C) = b) (T : Nat) :
    truncatedActiveCostNumerator
        (fixedCountStep hk ring (by omega))
        (.active (⟨C, hCb⟩ : FixedCountState hk ring b)) T ≤
      n ^ T * (n ^ blockLen n * blockLen n) := by
  have hq' : 0 < n ^ blockLen n := Nat.pow_pos (by omega)
  have hmass : ∀ s : FixedCountState hk ring b,
      n ^ (1 * blockLen n) ≤ n ^ blockLen n *
        successCount (fixedCountStep hk ring (by omega))
          (.active s) (1 * blockLen n) := by
    intro s
    simpa using fixedCount_block_mass hk ring hn3 hb s
  have h := UniformBlockRenewalCost.truncatedActiveCostNumerator_block_geometric_le
    (step := fixedCountStep hk ring (by omega))
    (n := n) (K := blockLen n) (q := 1) (q' := n ^ blockLen n)
    hq' (fixedCountStep_ne_failure hk ring (by omega)) hmass
    (⟨C, hCb⟩ : FixedCountState hk ring b) T
  simpa using h

/-- On every ring above the two small exceptions, the exact nonuniform family
is definitionally the original journal protocol used by this carrier. -/
theorem exactFamily_large_eq_original
    {n : Nat} (hn3 : 2 < n) :
    AAFJExactFamily.protocolFor n (by omega) =
      protocol (AAFJExactN.leastNonDivisor n)
        (by
          have hk := AAFJExactN.leastNonDivisor_ge_two (by omega : 0 < n)
          omega) := by
  simpa using AAFJExactFamily.protocolFor_large (n := n) (by omega)
    (by omega) (by omega)

/-- Exact-family specialization of the fixed-level geometric tail.  The first
conjunct records the large-ring branch identification, so this interface cannot
silently be applied to either dedicated small-ring protocol. -/
theorem exactFamily_fixedCount_block_tail
    {n b : Nat} (hn3 : 2 < n) (ring : DirectedRing n)
    (C : Fin n → State (AAFJExactN.leastNonDivisor n))
    (hb : 1 < b)
    (hCb : barrierCount
      (by
        have hk := AAFJExactN.leastNonDivisor_ge_two (by omega : 0 < n)
        omega)
      ring (labelsOf C) = b)
    (m : Nat) :
    AAFJExactFamily.protocolFor n (by omega) =
        protocol (AAFJExactN.leastNonDivisor n)
          (by
            have hk := AAFJExactN.leastNonDivisor_ge_two (by omega : 0 < n)
            omega) ∧
      (n ^ blockLen n) ^ m *
          activeCount
            (fixedCountStep
              (by
                have hk := AAFJExactN.leastNonDivisor_ge_two
                  (by omega : 0 < n)
                omega)
              ring (by omega))
            (.active (⟨C, hCb⟩ : FixedCountState
              (by
                have hk := AAFJExactN.leastNonDivisor_ge_two
                  (by omega : 0 < n)
                omega)
              ring b))
            (m * blockLen n) ≤
        (n ^ blockLen n - 1) ^ m * n ^ (m * blockLen n) := by
  constructor
  · exact exactFamily_large_eq_original hn3
  · exact fixedCount_block_tail
      (by
        have hk := AAFJExactN.leastNonDivisor_ge_two (by omega : 0 < n)
        omega)
      ring hn3 hb C hCb m

/-- Exact-family specialization of the normalized truncated-cost bound. -/
theorem exactFamily_fixedCount_truncated_cost
    {n b : Nat} (hn3 : 2 < n) (ring : DirectedRing n)
    (C : Fin n → State (AAFJExactN.leastNonDivisor n))
    (hb : 1 < b)
    (hCb : barrierCount
      (by
        have hk := AAFJExactN.leastNonDivisor_ge_two (by omega : 0 < n)
        omega)
      ring (labelsOf C) = b)
    (T : Nat) :
    truncatedActiveCostNumerator
        (fixedCountStep
          (by
            have hk := AAFJExactN.leastNonDivisor_ge_two (by omega : 0 < n)
            omega)
          ring (by omega))
        (.active (⟨C, hCb⟩ : FixedCountState
          (by
            have hk := AAFJExactN.leastNonDivisor_ge_two (by omega : 0 < n)
            omega)
          ring b)) T ≤
      n ^ T * (n ^ blockLen n * blockLen n) := by
  exact fixedCount_truncated_cost
    (by
      have hk := AAFJExactN.leastNonDivisor_ge_two (by omega : 0 < n)
      omega)
    ring hn3 hb C hCb T

#print axioms fixedCountStep_ne_failure
#print axioms fixedCount_successCount_one
#print axioms fixedCount_block_tail
#print axioms fixedCount_truncated_cost
#print axioms exactFamily_large_eq_original
#print axioms exactFamily_fixedCount_block_tail
#print axioms exactFamily_fixedCount_truncated_cost

end AAFJPK.OriginalMultiBarrierRenewal
