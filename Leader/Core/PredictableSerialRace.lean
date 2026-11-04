import Leader.Core.PredictableTwoTargetFiniteTree
import Leader.Core.UniformBlockRenewalCost


namespace PredictableRenewalOverlap


set_option autoImplicit false


open FiniteUniformStoppingTree
open PredictableTwoTargetFiniteTree


/-! ## A serial composition of two predictable two-target races -/


inductive SerialRaceState (A B : Type) where
  | first : A → SerialRaceState A B
  | second : B → SerialRaceState A B


/-- In the first race, `firstGood` advances to the second race and
`firstBad` fails.  In the second race, `secondGood` succeeds and `secondBad`
fails.  All other scheduler edges update only the current payload. -/
def serialRaceStep {A B : Type} {n : Nat}
    (firstGood firstBad : A → Fin n)
    (nextA : A → Fin n → A)
    (advance : A → B)
    (secondGood secondBad : B → Fin n)
    (nextB : B → Fin n → B) :
    SerialRaceState A B → Fin n → StopNode (SerialRaceState A B)
  | .first a, e =>
      if e = firstGood a then
        .active (.second (advance a))
      else if e = firstBad a then
        .failure
      else
        .active (.first (nextA a e))
  | .second b, e =>
      if e = secondGood b then
        .success
      else if e = secondBad b then
        .failure
      else
        .active (.second (nextB b e))


/-! ## Generic success-mass extension -/


/-- Every successful depth-`T` word has all `n` one-edge extensions still
successful. -/
private theorem n_mul_successCount_le_succ
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) :
    ∀ x T,
      n * successCount step x T ≤ successCount step x (T + 1) := by
  intro x T
  induction T generalizing x with
  | zero =>
      cases x with
      | active s =>
          change 0 ≤ successCount step (.active s) 1
          exact Nat.zero_le _
      | failure =>
          change 0 ≤ successCount step (.failure : StopNode S) 1
          exact Nat.zero_le _
      | success =>
          simp only [successCount, treeWeight, successWeight, stepNode,
            Nat.mul_one]
          rw [ofFn_sum_const]
          simp
  | succ T ih =>
      change
        n *
            (List.ofFn (fun e : Fin n =>
              treeWeight step successWeight (stepNode step x e) T)).sum ≤
          (List.ofFn (fun e : Fin n =>
            treeWeight step successWeight (stepNode step x e) (T + 1))).sum
      rw [← ofFn_sum_mul_left]
      apply ofFn_sum_le
      intro e
      simpa only [successCount] using ih (stepNode step x e)


/-- Success mass at horizon `U` gives `n^T` successful extensions at horizon
`U+T`. -/
private theorem pow_mul_successCount_le_add
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) :
    ∀ x U T,
      n ^ T * successCount step x U ≤
        successCount step x (U + T) := by
  intro x U T
  induction T with
  | zero => simp
  | succ T ih =>
      calc
        n ^ (T + 1) * successCount step x U =
            n * (n ^ T * successCount step x U) := by
              rw [Nat.pow_succ]
              ac_rfl
        _ ≤ n * successCount step x (U + T) :=
          Nat.mul_le_mul_left n ih
        _ ≤ successCount step x ((U + T) + 1) :=
          n_mul_successCount_le_succ step x (U + T)
        _ = successCount step x (U + (T + 1)) := by
          rw [Nat.add_assoc]


/-! ## The second serial phase is literally the ordinary second race -/


/-- Once the serial state has entered phase two, its success count is exactly
the success count of the underlying second two-target race. -/
theorem serialRace_second_successCount_eq
    {A B : Type} {n : Nat}
    (firstGood firstBad : A → Fin n)
    (nextA : A → Fin n → A)
    (advance : A → B)
    (secondGood secondBad : B → Fin n)
    (nextB : B → Fin n → B) :
    ∀ b T,
      successCount
          (serialRaceStep firstGood firstBad nextA advance
            secondGood secondBad nextB)
          (.active (.second b)) T =
        successCount
          (twoTargetStep secondGood secondBad nextB)
          (.active b) T := by
  intro b T
  induction T generalizing b with
  | zero => rfl
  | succ T ih =>
      simp only [successCount, treeWeight, stepNode]
      apply ofFn_sum_eq
      intro e
      by_cases hg : e = secondGood b
      · simp [serialRaceStep, twoTargetStep, hg,
          treeWeight_success, successWeight]
      · by_cases hb : e = secondBad b
        · simp only [serialRaceStep, twoTargetStep, hb]
          split <;>
            simp [treeWeight_success, treeWeight_failure, successWeight]
        · simpa [serialRaceStep, twoTargetStep, hg, hb, successCount] using
            ih (nextB b e)


/-- Quarter strength transfers verbatim to phase two of the serial race. -/
theorem serialRace_second_success_quarter_by_two_mul
    {A B : Type} {n : Nat}
    (firstGood firstBad : A → Fin n)
    (nextA : A → Fin n → A)
    (advance : A → B)
    (secondGood secondBad : B → Fin n)
    (nextB : B → Fin n → B)
    (hsecond : ∀ b, secondGood b ≠ secondBad b)
    (b : B) :
    n ^ (2 * n) ≤
      4 * successCount
        (serialRaceStep firstGood firstBad nextA advance
          secondGood secondBad nextB)
        (.active (.second b)) (2 * n) := by
  calc
    n ^ (2 * n) ≤
        4 * successCount
          (twoTargetStep secondGood secondBad nextB)
          (.active b) (2 * n) :=
      twoTarget_first_success_quarter_by_two_mul
        secondGood secondBad nextB hsecond b
    _ =
        4 * successCount
          (serialRaceStep firstGood firstBad nextA advance
            secondGood secondBad nextB)
          (.active (.second b)) (2 * n) := by
      rw [serialRace_second_successCount_eq]


/-! ## Sequential composition -/


/-- If every phase-two entry has denominator-cleared success mass
`n^U ≤ d * successCount U`, then every successful phase-one word of length `T`
can be continued to serial success with the same denominator `d`. -/
theorem serialRace_compose_successCount
    {A B : Type} {n d U : Nat}
    (firstGood firstBad : A → Fin n)
    (nextA : A → Fin n → A)
    (advance : A → B)
    (secondGood secondBad : B → Fin n)
    (nextB : B → Fin n → B)
    (hsecond : ∀ a,
      n ^ U ≤
        d * successCount
          (serialRaceStep firstGood firstBad nextA advance
            secondGood secondBad nextB)
          (.active (.second (advance a))) U) :
    ∀ a T,
      n ^ U *
          successCount
            (twoTargetStep firstGood firstBad nextA)
            (.active a) T ≤
        d * successCount
          (serialRaceStep firstGood firstBad nextA advance
            secondGood secondBad nextB)
          (.active (.first a)) (T + U) := by
  have hlong : ∀ a T,
      n ^ U * n ^ T ≤
        d * successCount
          (serialRaceStep firstGood firstBad nextA advance
            secondGood secondBad nextB)
          (.active (.second (advance a))) (T + U) := by
    intro a T
    have hext := pow_mul_successCount_le_add
      (serialRaceStep firstGood firstBad nextA advance
        secondGood secondBad nextB)
      (.active (.second (advance a))) U T
    calc
      n ^ U * n ^ T = n ^ T * n ^ U := Nat.mul_comm _ _
      _ ≤ n ^ T *
          (d * successCount
            (serialRaceStep firstGood firstBad nextA advance
              secondGood secondBad nextB)
            (.active (.second (advance a))) U) :=
        Nat.mul_le_mul_left (n ^ T) (hsecond a)
      _ = d *
          (n ^ T * successCount
            (serialRaceStep firstGood firstBad nextA advance
              secondGood secondBad nextB)
            (.active (.second (advance a))) U) := by
        ac_rfl
      _ ≤ d * successCount
          (serialRaceStep firstGood firstBad nextA advance
            secondGood secondBad nextB)
          (.active (.second (advance a))) (U + T) :=
        Nat.mul_le_mul_left d hext
      _ = d * successCount
          (serialRaceStep firstGood firstBad nextA advance
            secondGood secondBad nextB)
          (.active (.second (advance a))) (T + U) := by
        rw [Nat.add_comm U T]
  intro a T
  induction T generalizing a with
  | zero =>
      simp [successCount, treeWeight, successWeight]
  | succ T ih =>
      rw [show T + 1 + U = (T + U) + 1 by omega]
      change
        n ^ U *
            (List.ofFn (fun e : Fin n =>
              treeWeight
                (twoTargetStep firstGood firstBad nextA)
                successWeight
                (twoTargetStep firstGood firstBad nextA a e) T)).sum ≤
          d *
            (List.ofFn (fun e : Fin n =>
              treeWeight
                (serialRaceStep firstGood firstBad nextA advance
                  secondGood secondBad nextB)
                successWeight
                (serialRaceStep firstGood firstBad nextA advance
                  secondGood secondBad nextB (.first a) e)
                (T + U))).sum
      rw [← ofFn_sum_mul_left, ← ofFn_sum_mul_left]
      apply ofFn_sum_le
      intro e
      by_cases hg : e = firstGood a
      · simpa [twoTargetStep, serialRaceStep, hg,
          treeWeight_success, successWeight, successCount] using hlong a T
      · by_cases hb : e = firstBad a
        · simp only [twoTargetStep, serialRaceStep, hb]
          split
          · simpa [treeWeight_success, successWeight, successCount] using hlong a T
          · simp [treeWeight_failure, successWeight]
        · simpa [twoTargetStep, serialRaceStep, hg, hb, successCount] using
            ih (nextA a e)


/-! ## Two quarter-strength races give one sixteenth-strength serial race -/


/-- The abstract overlap capstone: two serial predictable `1/4` races yield
success mass at least `1/16` by horizon `4*n`, without any independence
assumption. -/
theorem serialRace_two_quarters_sixteenth_by_four_mul
    {A B : Type} {n : Nat}
    (firstGood firstBad : A → Fin n)
    (nextA : A → Fin n → A)
    (advance : A → B)
    (secondGood secondBad : B → Fin n)
    (nextB : B → Fin n → B)
    (hfirst : ∀ a, firstGood a ≠ firstBad a)
    (hsecond : ∀ b, secondGood b ≠ secondBad b)
    (a : A) :
    n ^ (4 * n) ≤
      16 * successCount
        (serialRaceStep firstGood firstBad nextA advance
          secondGood secondBad nextB)
        (.active (.first a)) (4 * n) := by
  have hfirstQuarter :=
    twoTarget_first_success_quarter_by_two_mul
      firstGood firstBad nextA hfirst a
  have hsecondQuarter : ∀ a,
      n ^ (2 * n) ≤
        4 * successCount
          (serialRaceStep firstGood firstBad nextA advance
            secondGood secondBad nextB)
          (.active (.second (advance a))) (2 * n) := by
    intro a
    exact serialRace_second_success_quarter_by_two_mul
      firstGood firstBad nextA advance secondGood secondBad nextB
      hsecond (advance a)
  have hcompose := serialRace_compose_successCount
    (d := 4) (U := 2 * n)
    firstGood firstBad nextA advance secondGood secondBad nextB
    hsecondQuarter a (2 * n)
  calc
    n ^ (4 * n) = n ^ (2 * n) * n ^ (2 * n) := by
      rw [show 4 * n = 2 * n + 2 * n by omega, Nat.pow_add]
    _ ≤ n ^ (2 * n) *
        (4 * successCount
          (twoTargetStep firstGood firstBad nextA)
          (.active a) (2 * n)) :=
      Nat.mul_le_mul_left (n ^ (2 * n)) hfirstQuarter
    _ = 4 *
        (n ^ (2 * n) * successCount
          (twoTargetStep firstGood firstBad nextA)
          (.active a) (2 * n)) := by
      ac_rfl
    _ ≤ 4 *
        (4 * successCount
          (serialRaceStep firstGood firstBad nextA advance
            secondGood secondBad nextB)
          (.active (.first a)) (2 * n + 2 * n)) :=
      Nat.mul_le_mul_left 4 hcompose
    _ = 16 * successCount
        (serialRaceStep firstGood firstBad nextA advance
          secondGood secondBad nextB)
        (.active (.first a)) (4 * n) := by
      rw [show 2 * n + 2 * n = 4 * n by omega]
      rw [← Nat.mul_assoc]


#print axioms serialRace_second_successCount_eq
#print axioms serialRace_compose_successCount
#print axioms serialRace_second_success_quarter_by_two_mul
#print axioms serialRace_two_quarters_sixteenth_by_four_mul


end PredictableRenewalOverlap
