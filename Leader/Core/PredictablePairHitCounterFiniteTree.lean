import Leader.Core.PredictableTwoTargetFiniteTree

/-!
# Finite scheduler trees for cumulative predictable pair hits

At every active state two distinct scheduler edges are selected from the
current payload before the next raw draw.  A draw of either selected edge
increments one common hit counter.  Every draw may otherwise update the
payload, so both selectors may depend on the complete preceding history.

The tree stops successfully when the common counter reaches `d`.
All statements are exact finite scheduler-count inequalities over `Nat`.
-/

namespace PredictablePairHitCounterFiniteTree

set_option autoImplicit false

open FiniteUniformStoppingTree
open PredictableTwoTargetFiniteTree

private theorem pred_mul (m c : Nat) (hm : 0 < m) :
    m * c = c + (m - 1) * c := by
  obtain ⟨q, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simp [Nat.succ_mul, Nat.add_comm]

/-- An active state with fewer than `d` accumulated pair hits. -/
structure ActivePairHitState (S : Type) (d : Nat) where
  payload : S
  hits : Nat
  hits_lt : hits < d

/-- One raw scheduler draw.

Either current selected edge contributes one hit.  The payload update is
performed on target hits and irrelevant draws alike. -/
def pairHitCounterStep {S : Type} {n d : Nat}
    (first second : S → Fin n) (next : S → Fin n → S)
    (st : ActivePairHitState S d) (e : Fin n) :
    StopNode (ActivePairHitState S d) :=
  if hfirst : e = first st.payload then
    if hdone : st.hits + 1 = d then
      .success
    else
      .active
        { payload := next st.payload e
          hits := st.hits + 1
          hits_lt := by
            have := st.hits_lt
            omega }
  else if hsecond : e = second st.payload then
    if hdone : st.hits + 1 = d then
      .success
    else
      .active
        { payload := next st.payload e
          hits := st.hits + 1
          hits_lt := by
            have := st.hits_lt
            omega }
  else
    .active
      { payload := next st.payload e
        hits := st.hits
        hits_lt := st.hits_lt }

/-- Canonical zero-hit start.  Positivity of `d` is exactly what makes the
zero counter an active state. -/
def initialState {S : Type} (payload : S) (d : Nat) (hd : 0 < d) :
    ActivePairHitState S d where
  payload := payload
  hits := 0
  hits_lt := hd

/-- Natural remaining-service potential. -/
private def pairHitPotential {S : Type} {d : Nat} (n : Nat) :
    StopNode (ActivePairHitState S d) → Nat
  | .active st => n * (d - st.hits)
  | .success => 0
  | .failure => 0

/-- Two distinct predictable hit edges make the remaining-hit potential a
scale-two Bellman supersolution. -/
theorem pairHitCounter_natBellmanSuperSolution
    {S : Type} {n d : Nat}
    (first second : S → Fin n) (next : S → Fin n → S)
    (hdistinct : ∀ s, first s ≠ second s) :
    NatBellmanSuperSolution
      (pairHitCounterStep (d := d) first second next) 2
      (pairHitPotential (S := S) (d := d) n) := by
  refine ⟨rfl, rfl, ?_⟩
  intro st
  let c := n * (d - st.hits)
  let a :=
    pairHitPotential (S := S) (d := d) n
      (pairHitCounterStep (d := d) first second next st
        (first st.payload))
  let b :=
    pairHitPotential (S := S) (d := d) n
      (pairHitCounterStep (d := d) first second next st
        (second st.payload))

  have hsum :
      (List.ofFn (fun e : Fin n =>
        pairHitPotential (S := S) (d := d) n
          (pairHitCounterStep first second next st e))).sum =
        a + b + (n - 2) * c := by
    have h :=
      ofFn_sum_two_values_else_const
        (first st.payload) (second st.payload)
        (fun e : Fin n =>
          pairHitPotential (S := S) (d := d) n
            (pairHitCounterStep first second next st e))
        c (hdistinct st.payload) (by
          intro e hef hes
          simp [pairHitCounterStep, hef, hes, pairHitPotential, c])
    simpa only [a, b] using h

  have hlt := st.hits_lt
  have hremain :
      d - st.hits = (d - (st.hits + 1)) + 1 := by
    omega

  have ha : a + n = c := by
    dsimp [a, c]
    by_cases hdone : st.hits + 1 = d
    · have hsub : d - st.hits = 1 := by omega
      simp [pairHitCounterStep, hdone, pairHitPotential, hsub]
    · simp [pairHitCounterStep, hdone, pairHitPotential,
        hremain, Nat.mul_add]

  have hb : b + n = c := by
    dsimp [b, c]
    by_cases hdone : st.hits + 1 = d
    · have hsub : d - st.hits = 1 := by omega
      simp [pairHitCounterStep, (hdistinct st.payload).symm,
        hdone, pairHitPotential, hsub]
    · simp [pairHitCounterStep, (hdistinct st.payload).symm,
        hdone, pairHitPotential, hremain, Nat.mul_add]

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
  have hpred1 := pred_mul n c hn
  have hpred2 := pred_mul (n - 1) c (by omega)
  have hsub : n - 1 - 1 = n - 2 := by omega
  rw [hsub] at hpred2

  simp only [pairHitPotential]
  change 2 * n +
      (List.ofFn (fun e : Fin n =>
        pairHitPotential (S := S) (d := d) n
          (pairHitCounterStep first second next st e))).sum ≤
        n * c
  rw [hsum]
  calc
    2 * n + (a + b + (n - 2) * c) =
        (a + n) + (b + n) + (n - 2) * c := by
      omega
    _ = c + c + (n - 2) * c := by
      rw [ha, hb]
    _ = c + (n - 1) * c := by
      rw [hpred2]
      omega
    _ ≤ n * c := Nat.le_of_eq hpred1.symm

/-- From zero hits, twice the truncated raw-duration numerator is at most
`n*d` times the depth-`T` scheduler-space size. -/
theorem initial_two_mul_truncatedCost_le
    {S : Type} {n d : Nat}
    (first second : S → Fin n) (next : S → Fin n → S)
    (hdistinct : ∀ s, first s ≠ second s)
    (payload : S) (hd : 0 < d) (T : Nat) :
    2 * truncatedActiveCostNumerator
        (pairHitCounterStep (d := d) first second next)
        (.active (initialState payload d hd)) T ≤
      n ^ T * (n * d) := by
  simpa [pairHitPotential, initialState] using
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      (pairHitCounterStep (d := d) first second next) 2
      (pairHitPotential (S := S) (d := d) n)
      (pairHitCounter_natBellmanSuperSolution
        first second next hdistinct)
      (.active (initialState payload d hd)) T

/-- Six predictable pair hits: by raw horizon `384*n`, at most
`1/128` of the complete scheduler tree can remain active, in the exact
division-free count form. -/
theorem six_hits_timeout_128
    {S : Type} {n : Nat}
    (first second : S → Fin n) (next : S → Fin n → S)
    (hdistinct : ∀ s, first s ≠ second s)
    (payload : S) :
    128 *
        activeCount
          (pairHitCounterStep (d := 6) first second next)
          (.active (initialState payload 6 (by omega)))
          (384 * n) ≤
      n ^ (384 * n) := by
  let step := pairHitCounterStep (d := 6) first second next
  let start := initialState payload 6 (by omega)
  let H := 384 * n
  let N := n ^ H
  let A := activeCount step (.active start) H

  have hlive :=
    horizon_mul_activeCount_le_truncatedActiveCost
      step (.active start) H
  have hcost :=
    initial_two_mul_truncatedCost_le
      (d := 6) first second next hdistinct payload (by omega) H

  have hchain :
      (n * 6) * (128 * A) ≤ (n * 6) * N := by
    calc
      (n * 6) * (128 * A) = 2 * (H * A) := by
        dsimp [H]
        rw [show 128 = 2 * 64 by decide,
          show 384 = 6 * 64 by decide]
        ac_rfl
      _ ≤ 2 * truncatedActiveCostNumerator
          step (.active start) H :=
        Nat.mul_le_mul_left 2 hlive
      _ ≤ N * (n * 6) := by
        simpa [step, start, N] using hcost
      _ = (n * 6) * N := by
        ac_rfl

  have hn : 0 < n := by
    have := (first payload).isLt
    omega
  have hn6 : 0 < n * 6 := Nat.mul_pos hn (by omega)
  have hcancel :
      128 * A ≤ N :=
    Nat.le_of_mul_le_mul_left hchain hn6
  simpa [A, N, H, step, start] using hcancel

#print axioms pairHitCounter_natBellmanSuperSolution
#print axioms initial_two_mul_truncatedCost_le
#print axioms six_hits_timeout_128

end PredictablePairHitCounterFiniteTree
