import Leader.Core.PredictableTwoTargetFiniteTree

/-!
# Finite scheduler trees for an adaptive two-counter race

Two distinct scheduler targets are chosen from the current payload before each
raw scheduler draw.  Either target may therefore move after every prior draw.
Selecting the first target increments the first counter, selecting the second
increments the second counter, and every other edge may update the payload and
both future targets arbitrarily.  The race stops when either counter reaches
the common threshold `d`.

The proof never assumes independence.  Exact finite-tree recurrences show that
the scheduler counts depend only on the two counters, not on the payload.  The
recurrences are exchanged by swapping the counters, hence a race started from
equal counters has exactly equal success and failure counts at every horizon.

A remaining-relevant-hits Bellman potential bounds the truncated raw duration
by `n*d` from counters `(0,0)`.  For `2*d <= n`, finite Markov at horizon
`4*n^2` leaves at most one eighth of the scheduler tree unresolved.  Combining
this with exact fairness gives the denominator-cleared quarter bound required
by the centered rank block (in fact the proof yields a stronger constant).
-/

namespace PredictableCounterRaceFiniteTree

set_option autoImplicit false

open FiniteUniformStoppingTree
open PredictableTwoTargetFiniteTree

/-! ## Active race states and transitions -/

/-- An active two-counter race state.  The strict bounds ensure that reaching
`d` is represented only by an absorbing tree node, never by an active state. -/
structure ActiveRaceState (S : Type) (d : Nat) where
  payload : S
  firstHits : Nat
  secondHits : Nat
  first_lt : firstHits < d
  second_lt : secondHits < d

/-- Number of relevant target selections still available before both counters
would have reached the threshold.  An actual race stops strictly earlier. -/
def remaining {S : Type} {d : Nat} (st : ActiveRaceState S d) : Nat :=
  (d - st.firstHits) + (d - st.secondHits)

/-- Execute one raw scheduler draw.  Payload evolution is unrestricted and is
performed on target hits as well as irrelevant draws. -/
def counterRaceStep {S : Type} {n d : Nat}
    (first second : S → Fin n) (next : S → Fin n → S)
    (st : ActiveRaceState S d) (e : Fin n) :
    StopNode (ActiveRaceState S d) :=
  if hfirst : e = first st.payload then
    if hdone : st.firstHits + 1 = d then .success
    else .active
      { payload := next st.payload e
        firstHits := st.firstHits + 1
        secondHits := st.secondHits
        first_lt := by have := st.first_lt; omega
        second_lt := st.second_lt }
  else if hsecond : e = second st.payload then
    if hdone : st.secondHits + 1 = d then .failure
    else .active
      { payload := next st.payload e
        firstHits := st.firstHits
        secondHits := st.secondHits + 1
        first_lt := st.first_lt
        second_lt := by have := st.second_lt; omega }
  else .active
    { payload := next st.payload e
      firstHits := st.firstHits
      secondHits := st.secondHits
      first_lt := st.first_lt
      second_lt := st.second_lt }

/-- Canonical race start with both counters zero. -/
def initialState {S : Type} (payload : S) (d : Nat) (hd : 0 < d) :
    ActiveRaceState S d where
  payload := payload
  firstHits := 0
  secondHits := 0
  first_lt := hd
  second_lt := hd

/-! ## Payload-free exact count recurrences -/

/-- Exact success-count recurrence determined only by the counters. -/
def successNumerator (n d firstHits secondHits : Nat) : Nat → Nat
  | 0 => 0
  | T + 1 =>
      (if firstHits + 1 = d then n ^ T
        else successNumerator n d (firstHits + 1) secondHits T) +
      (if secondHits + 1 = d then 0
        else successNumerator n d firstHits (secondHits + 1) T) +
      (n - 2) * successNumerator n d firstHits secondHits T

/-- Exact failure-count recurrence determined only by the counters. -/
def failureNumerator (n d firstHits secondHits : Nat) : Nat → Nat
  | 0 => 0
  | T + 1 =>
      (if firstHits + 1 = d then 0
        else failureNumerator n d (firstHits + 1) secondHits T) +
      (if secondHits + 1 = d then n ^ T
        else failureNumerator n d firstHits (secondHits + 1) T) +
      (n - 2) * failureNumerator n d firstHits secondHits T

/-- Swapping the counters exchanges the two absorbing outcomes in the exact
finite recurrence. -/
theorem successNumerator_eq_failureNumerator_swap (n d : Nat) :
    ∀ firstHits secondHits T,
      successNumerator n d firstHits secondHits T =
        failureNumerator n d secondHits firstHits T := by
  intro firstHits secondHits T
  induction T generalizing firstHits secondHits with
  | zero => rfl
  | succ T ih =>
      simp only [successNumerator, failureNumerator]
      by_cases hfirst : firstHits + 1 = d <;>
        by_cases hsecond : secondHits + 1 = d <;>
        simp [hfirst, hsecond, ih, Nat.add_comm, Nat.add_left_comm,
          ]

private theorem nodup_ofFn_of_injective {n : Nat} {A : Type}
    (f : Fin n → A) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_ofFn] at hmem
        obtain ⟨i, hi⟩ := hmem
        have h := hf hi
        cases h
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

private theorem nodup_ofFn_fin (n : Nat) :
    (List.ofFn (fun i : Fin n => i)).Nodup :=
  nodup_ofFn_of_injective (fun i : Fin n => i) (fun _ _ h => h)

private theorem actual_success_eq_numerator
    {S : Type} {n d : Nat} (first second : S → Fin n)
    (next : S → Fin n → S)
    (hdistinct : ∀ s, first s ≠ second s) :
    ∀ (st : ActiveRaceState S d) T,
      successCount (counterRaceStep first second next) (.active st) T =
        successNumerator n d st.firstHits st.secondHits T := by
  intro st T
  induction T generalizing st with
  | zero => rfl
  | succ T ih =>
      simp only [successCount] at ih
      simp only [successCount, treeWeight]
      have hsum := sum_two_exceptions
        (List.ofFn (fun i : Fin n => i))
        (first st.payload) (second st.payload)
        (fun e => treeWeight (counterRaceStep first second next)
          successWeight
          (stepNode (counterRaceStep first second next) (.active st) e) T)
        (successNumerator n d st.firstHits st.secondHits T)
        (by
          exact nodup_ofFn_fin n)
        (by rw [List.mem_ofFn]; exact ⟨first st.payload, rfl⟩)
        (by rw [List.mem_ofFn]; exact ⟨second st.payload, rfl⟩)
        (hdistinct st.payload) (by
          intro e _ hef hes
          simp only [stepNode]
          rw [show counterRaceStep first second next st e = .active
              { payload := next st.payload e
                firstHits := st.firstHits
                secondHits := st.secondHits
                first_lt := st.first_lt
                second_lt := st.second_lt } by
            simp [counterRaceStep, hef, hes]]
          exact ih _)
      have hsum' :
          (List.ofFn (fun e => treeWeight
            (counterRaceStep first second next) successWeight
            (stepNode (counterRaceStep first second next) (.active st) e) T)).sum =
          treeWeight (counterRaceStep first second next) successWeight
              (stepNode (counterRaceStep first second next) (.active st)
                (first st.payload)) T +
            treeWeight (counterRaceStep first second next) successWeight
              (stepNode (counterRaceStep first second next) (.active st)
                (second st.payload)) T +
            (n - 2) * successNumerator n d st.firstHits st.secondHits T := by
        simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn] using hsum
      rw [hsum']
      simp only [successNumerator]
      by_cases hp : st.firstHits + 1 = d <;>
        by_cases hq : st.secondHits + 1 = d <;>
        simp [stepNode, counterRaceStep, hp, hq,
          (hdistinct st.payload).symm, treeWeight_success, treeWeight_failure,
          successWeight, ih]

private theorem actual_failure_eq_numerator
    {S : Type} {n d : Nat} (first second : S → Fin n)
    (next : S → Fin n → S)
    (hdistinct : ∀ s, first s ≠ second s) :
    ∀ (st : ActiveRaceState S d) T,
      failureCount (counterRaceStep first second next) (.active st) T =
        failureNumerator n d st.firstHits st.secondHits T := by
  intro st T
  induction T generalizing st with
  | zero => rfl
  | succ T ih =>
      simp only [failureCount] at ih
      simp only [failureCount, treeWeight]
      have hsum := sum_two_exceptions
        (List.ofFn (fun i : Fin n => i))
        (first st.payload) (second st.payload)
        (fun e => treeWeight (counterRaceStep first second next)
          failureWeight
          (stepNode (counterRaceStep first second next) (.active st) e) T)
        (failureNumerator n d st.firstHits st.secondHits T)
        (by
          exact nodup_ofFn_fin n)
        (by rw [List.mem_ofFn]; exact ⟨first st.payload, rfl⟩)
        (by rw [List.mem_ofFn]; exact ⟨second st.payload, rfl⟩)
        (hdistinct st.payload) (by
          intro e _ hef hes
          simp only [stepNode]
          rw [show counterRaceStep first second next st e = .active
              { payload := next st.payload e
                firstHits := st.firstHits
                secondHits := st.secondHits
                first_lt := st.first_lt
                second_lt := st.second_lt } by
            simp [counterRaceStep, hef, hes]]
          exact ih _)
      have hsum' :
          (List.ofFn (fun e => treeWeight
            (counterRaceStep first second next) failureWeight
            (stepNode (counterRaceStep first second next) (.active st) e) T)).sum =
          treeWeight (counterRaceStep first second next) failureWeight
              (stepNode (counterRaceStep first second next) (.active st)
                (first st.payload)) T +
            treeWeight (counterRaceStep first second next) failureWeight
              (stepNode (counterRaceStep first second next) (.active st)
                (second st.payload)) T +
            (n - 2) * failureNumerator n d st.firstHits st.secondHits T := by
        simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn] using hsum
      rw [hsum']
      simp only [failureNumerator]
      by_cases hp : st.firstHits + 1 = d <;>
        by_cases hq : st.secondHits + 1 = d <;>
        simp [stepNode, counterRaceStep, hp, hq,
          (hdistinct st.payload).symm, treeWeight_failure, treeWeight_success,
          failureWeight, ih]

/-- A symmetric counter race started from equal counters has exactly equal
success and failure scheduler counts at every finite raw horizon. -/
theorem successCount_eq_failureCount_of_counters_eq
    {S : Type} {n d : Nat} (first second : S → Fin n)
    (next : S → Fin n → S)
    (hdistinct : ∀ s, first s ≠ second s)
    (st : ActiveRaceState S d) (hcounters : st.firstHits = st.secondHits)
    (T : Nat) :
    successCount (counterRaceStep first second next) (.active st) T =
      failureCount (counterRaceStep first second next) (.active st) T := by
  rw [actual_success_eq_numerator first second next hdistinct,
    actual_failure_eq_numerator first second next hdistinct, hcounters]
  exact successNumerator_eq_failureNumerator_swap n d
    st.secondHits st.secondHits T

/-! ## Truncated raw-duration bound -/

private theorem pred_mul (m c : Nat) (hm : 0 < m) :
    m * c = c + (m - 1) * c := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simp [Nat.succ_mul, Nat.add_comm]

/-- Natural Bellman potential: `n` times the sum of the two remaining counter
distances. -/
def racePotential {S : Type} {d : Nat} (n : Nat) :
    StopNode (ActiveRaceState S d) → Nat
  | .active st => n * remaining st
  | .success => 0
  | .failure => 0

private theorem potential_first_le
    {S : Type} {n d : Nat} (first second : S → Fin n)
    (next : S → Fin n → S) (st : ActiveRaceState S d) :
    racePotential n (counterRaceStep first second next st (first st.payload)) ≤
      n * (remaining st - 1) := by
  by_cases hdone : st.firstHits + 1 = d
  · simp [counterRaceStep, hdone, racePotential]
  · have hrem : remaining
        ({ payload := next st.payload (first st.payload)
           firstHits := st.firstHits + 1
           secondHits := st.secondHits
           first_lt := by have := st.first_lt; omega
           second_lt := st.second_lt } : ActiveRaceState S d) =
        remaining st - 1 := by
      simp only [remaining]
      have := st.first_lt
      omega
    simp [counterRaceStep, hdone, racePotential, hrem]

private theorem potential_second_le
    {S : Type} {n d : Nat} (first second : S → Fin n)
    (next : S → Fin n → S)
    (hdistinct : ∀ s, first s ≠ second s)
    (st : ActiveRaceState S d) :
    racePotential n (counterRaceStep first second next st (second st.payload)) ≤
      n * (remaining st - 1) := by
  by_cases hdone : st.secondHits + 1 = d
  · simp [counterRaceStep, hdone, racePotential,
      (hdistinct st.payload).symm]
  · have hrem : remaining
        ({ payload := next st.payload (second st.payload)
           firstHits := st.firstHits
           secondHits := st.secondHits + 1
           first_lt := st.first_lt
           second_lt := by have := st.second_lt; omega } : ActiveRaceState S d) =
        remaining st - 1 := by
      simp only [remaining]
      have := st.second_lt
      omega
    simp [counterRaceStep, hdone, racePotential, hrem,
      (hdistinct st.payload).symm]

/-- The remaining-distance potential is a scale-two Bellman supersolution.
Equivalently, two relevant targets among `n` raw choices pay the raw clock. -/
theorem counterRace_natBellmanSuperSolution
    {S : Type} {n d : Nat} (first second : S → Fin n)
    (next : S → Fin n → S)
    (hdistinct : ∀ s, first s ≠ second s) :
    NatBellmanSuperSolution (counterRaceStep (d := d) first second next) 2
      (racePotential (S := S) (d := d) n) := by
  refine ⟨rfl, rfl, ?_⟩
  intro st
  let R := remaining st
  let c := n * R
  have hsum := sum_two_exceptions
    (List.ofFn (fun i : Fin n => i))
    (first st.payload) (second st.payload)
    (fun e => racePotential n (counterRaceStep first second next st e)) c
    (nodup_ofFn_fin n)
    (by rw [List.mem_ofFn]; exact ⟨first st.payload, rfl⟩)
    (by rw [List.mem_ofFn]; exact ⟨second st.payload, rfl⟩)
    (hdistinct st.payload) (by
      intro e _ hef hes
      simp [counterRaceStep, racePotential, remaining, c, R, hef, hes])
  have hp := potential_first_le (d := d) first second next st
  have hq := potential_second_le (d := d) first second next hdistinct st
  have hn : 0 < n := by
    have := (first st.payload).isLt
    omega
  have hn1 : n ≠ 1 := by
    intro heq
    apply hdistinct st.payload
    apply Fin.ext
    have hf := (first st.payload).isLt
    have hs := (second st.payload).isLt
    omega
  have hn2 : 2 ≤ n := by omega
  have hR : 0 < R := by
    dsimp [R, remaining]
    have hpLt := st.first_lt
    have hqLt := st.second_lt
    omega
  have hc : c = n + n * (R - 1) := by
    dsimp [c]
    have hpred := pred_mul R n hR
    calc
      n * R = R * n := Nat.mul_comm _ _
      _ = n + (R - 1) * n := hpred
      _ = n + n * (R - 1) := by rw [Nat.mul_comm (R - 1) n]
  have hnSplit1 := pred_mul n c hn
  have hnSplit2 := pred_mul (n - 1) c (by omega)
  have hsub : n - 1 - 1 = n - 2 := by omega
  rw [hsub] at hnSplit2
  have hsum' :
      (List.ofFn (fun e : Fin n =>
        racePotential n (counterRaceStep first second next st e))).sum =
      racePotential n (counterRaceStep first second next st (first st.payload)) +
        racePotential n (counterRaceStep first second next st (second st.payload)) +
        (n - 2) * c := by
    simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn] using hsum
  change 2 * n +
      (List.ofFn (fun e : Fin n =>
        racePotential n (counterRaceStep first second next st e))).sum ≤
      n * racePotential n (.active st)
  rw [hsum']
  rw [show racePotential n (.active st) = c by rfl]
  have hpq := Nat.add_le_add hp hq
  calc
    2 * n +
        (racePotential n
            (counterRaceStep first second next st (first st.payload)) +
          racePotential n
            (counterRaceStep first second next st (second st.payload)) +
          (n - 2) * c) ≤
        2 * n +
          (n * (R - 1) + n * (R - 1) + (n - 2) * c) :=
      Nat.add_le_add_left (Nat.add_le_add_right hpq _) _
    _ = c + c + (n - 2) * c := by rw [hc]; omega
    _ = n * c := by omega

/-- From counters `(0,0)`, the truncated raw-duration numerator is at most
`n*d` times scheduler-space size. -/
theorem initial_truncatedCost_le
    {S : Type} {n d : Nat} (first second : S → Fin n)
    (next : S → Fin n → S)
    (hdistinct : ∀ s, first s ≠ second s)
    (payload : S) (hd : 0 < d) (T : Nat) :
    truncatedActiveCostNumerator (counterRaceStep (d := d) first second next)
        (.active (initialState payload d hd)) T ≤ n ^ T * (n * d) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (counterRaceStep (d := d) first second next) 2
    (racePotential (S := S) (d := d) n)
    (counterRace_natBellmanSuperSolution first second next hdistinct)
    (.active (initialState payload d hd)) T
  have hpot : racePotential (S := S) (d := d) n
      (.active (initialState payload d hd)) = 2 * (n * d) := by
    simp only [racePotential, remaining, initialState, Nat.sub_zero]
    rw [Nat.mul_add, Nat.two_mul]
  rw [hpot] at h
  have h' : 2 * truncatedActiveCostNumerator
      (counterRaceStep (d := d) first second next)
      (.active (initialState payload d hd)) T ≤
      2 * (n ^ T * (n * d)) := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  exact Nat.le_of_mul_le_mul_left h' (by omega)

/-! ## The `4*n^2` quarter-success bound -/

/-- Under `2*d <= n`, at horizon `4*n^2` at most one eighth of all raw
scheduler words remain active. -/
theorem initial_eight_mul_activeCount_le_four_mul_sq
    {S : Type} {n d : Nat} (first second : S → Fin n)
    (next : S → Fin n → S)
    (hdistinct : ∀ s, first s ≠ second s)
    (payload : S) (hd : 0 < d) (hdn : 2 * d ≤ n) :
    8 * activeCount (counterRaceStep (d := d) first second next)
        (.active (initialState payload d hd)) (4 * n ^ 2) ≤
      n ^ (4 * n ^ 2) := by
  let step := counterRaceStep (d := d) first second next
  let start := initialState payload d hd
  let A := activeCount step (.active start) (4 * n ^ 2)
  let N := n ^ (4 * n ^ 2)
  have hlive := horizon_mul_activeCount_le_truncatedActiveCost
    step (.active start) (4 * n ^ 2)
  have hcost := initial_truncatedCost_le
    first second next hdistinct payload hd (4 * n ^ 2)
  have hcost2 := Nat.mul_le_mul_left 2 hcost
  have hdnScaled := Nat.mul_le_mul_left (N * n) hdn
  have hchain : (n ^ 2) * (8 * A) ≤ (n ^ 2) * N := by
    calc
      (n ^ 2) * (8 * A) = 2 * ((4 * n ^ 2) * A) := by
        dsimp [A]
        rw [show 8 = 2 * 4 by decide]
        ac_rfl
      _ ≤ 2 * truncatedActiveCostNumerator step (.active start)
          (4 * n ^ 2) := Nat.mul_le_mul_left 2 hlive
      _ ≤ 2 * (N * (n * d)) := by
        dsimp [step, start, N] at hcost2 ⊢
        exact hcost2
      _ = (N * n) * (2 * d) := by ac_rfl
      _ ≤ (N * n) * n := hdnScaled
      _ = (n ^ 2) * N := by
        simp [Nat.pow_two]
        ac_rfl
  have hn : 0 < n := by omega
  have hsq : 0 < n ^ 2 := Nat.pow_pos hn
  exact Nat.le_of_mul_le_mul_left hchain hsq

/-- The first counter reaches `d` before the second, and does so within
`4*n^2`, on at least one quarter of all scheduler words. -/
theorem initial_success_quarter_by_four_mul_sq
    {S : Type} {n d : Nat} (first second : S → Fin n)
    (next : S → Fin n → S)
    (hdistinct : ∀ s, first s ≠ second s)
    (payload : S) (hd : 0 < d) (hdn : 2 * d ≤ n) :
    n ^ (4 * n ^ 2) ≤
      4 * successCount (counterRaceStep (d := d) first second next)
        (.active (initialState payload d hd)) (4 * n ^ 2) := by
  let step := counterRaceStep (d := d) first second next
  let start := initialState payload d hd
  have hactive := initial_eight_mul_activeCount_le_four_mul_sq
    first second next hdistinct payload hd hdn
  have heq := successCount_eq_failureCount_of_counters_eq
    first second next hdistinct start (by rfl) (4 * n ^ 2)
  have hpartition := node_count_partition step (.active start) (4 * n ^ 2)
  dsimp [step, start] at hactive heq hpartition ⊢
  omega

#print axioms successCount_eq_failureCount_of_counters_eq
#print axioms counterRace_natBellmanSuperSolution
#print axioms initial_truncatedCost_le
#print axioms initial_success_quarter_by_four_mul_sq

end PredictableCounterRaceFiniteTree
