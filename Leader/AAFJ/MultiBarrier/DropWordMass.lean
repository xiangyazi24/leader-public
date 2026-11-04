import Leader.AAFJ.Centered.TerminalPhysical
import Leader.AAFJ.NonbarrierWord
import Leader.Wu.Splice.MatcherMass


set_option autoImplicit false


namespace AAFJPK.OriginalDropWordMass


open BarrierAlgebra
open OriginalNonbarrierWord
open FiniteUniformStoppingTree
open FixedSpanRenewalPayload
open CenteredRenewal.TerminalPhysical


/-- Strict drop relative to the configuration at the start of this attempt. -/
def dropDone {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C0 D : Fin n → State k) : Prop :=
  barrierCount hk ring (labelsOf D) <
    barrierCount hk ring (labelsOf C0)


/-- Literal original AAFJ step, stopped on the first strict drop.
Every non-drop child stays physically active. -/
noncomputable def dropStep {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C0 : Fin n → State k) :
    (Fin n → State k) → Fin n → StopNode (Fin n → State k) := by
  classical
  exact predicateStopStep ((AAFJPK.protocol k hk).step ring)
    (dropDone hk ring C0)


@[simp] private theorem runStopped_success
    {S : Type} {n : Nat} (step : S → Fin n → StopNode S)
    (w : List (Fin n)) :
    runStopped step (.success : StopNode S) w = .success := by
  induction w with
  | nil => rfl
  | cons _ _ ih => exact ih


/-- If the unstopped literal execution ends below the fixed initial count,
then the stop-on-drop execution of the same word is successful.  If a strict
drop occurs earlier, absorption handles the remaining suffix automatically. -/
private theorem runStopped_drop_of_rawRun_drop_from
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C0 D : Fin n → State k) (w : List (Fin n))
    (hD : ¬ dropDone hk ring C0 D)
    (hdrop : dropDone hk ring C0 (rawRun hk ring D w)) :
    runStopped (dropStep hk ring C0) (.active D) w = .success := by
  classical
  induction w generalizing D with
  | nil =>
      have hbad : dropDone hk ring C0 D := by
        simpa [rawRun] using hdrop
      exact (hD hbad).elim
  | cons e es ih =>
      let E := (AAFJPK.protocol k hk).step ring D e
      by_cases hE : dropDone hk ring C0 E
      · simp [runStopped, stepNode, dropStep, predicateStopStep, E, hE]
      · have htail :
            dropDone hk ring C0 (rawRun hk ring E es) := by
          simpa [rawRun, E] using hdrop
        have hs := ih E hE htail
        simpa [runStopped, stepNode, dropStep, predicateStopStep, E, hE] using hs


theorem raw_drop_word_runs_success
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (w : List (Fin n))
    (hdrop :
      barrierCount hk ring (labelsOf (rawRun hk ring C w)) <
        barrierCount hk ring (labelsOf C)) :
    runStopped (dropStep hk ring C) (.active C) w = .success := by
  apply runStopped_drop_of_rawRun_drop_from hk ring C C w
  · simp [dropDone]
  · exact hdrop


/-- A selected unit-valued list entry contributes at least one to the sum. -/
private theorem one_le_sum_map_of_mem_eq_one {A : Type} (xs : List A)
    (value : A → Nat) (chosen : A) (hmem : chosen ∈ xs)
    (hone : value chosen = 1) :
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

/-- One successful explicit depth-T word contributes at least one unit to
the exact stopped-tree success numerator. -/
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


/-- Exact singleton finite-horizon mass from a deterministic dropping word. -/
theorem raw_drop_word_successCount_one
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (w : List (Fin n))
    (hdrop :
      barrierCount hk ring (labelsOf (rawRun hk ring C w)) <
        barrierCount hk ring (labelsOf C)) :
    1 ≤ successCount (dropStep hk ring C) (.active C) w.length := by
  apply one_le_successCount_of_success_word
  exact raw_drop_word_runs_success hk ring C w hdrop


/-- Same result in the repository's denominator-cleared mass syntax.
Here Q = n^|w|, i.e. success probability at least 1/n^|w|. -/
theorem raw_drop_word_singleton_mass
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (w : List (Fin n))
    (hdrop :
      barrierCount hk ring (labelsOf (rawRun hk ring C w)) <
        barrierCount hk ring (labelsOf C)) :
    n ^ w.length ≤
      n ^ w.length *
        successCount (dropStep hk ring C) (.active C) w.length := by
  have h := raw_drop_word_successCount_one hk ring C w hdrop
  simpa using Nat.mul_le_mul_left (n ^ w.length) h


#check raw_drop_word_runs_success
#check raw_drop_word_successCount_one
#check raw_drop_word_singleton_mass


#print axioms raw_drop_word_runs_success
#print axioms raw_drop_word_successCount_one
#print axioms raw_drop_word_singleton_mass


end AAFJPK.OriginalDropWordMass
