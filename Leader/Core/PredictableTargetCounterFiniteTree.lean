import Leader.Core.PredictableTwoTargetFiniteTree

/-!
# Finite scheduler trees for cumulative predictable-target service

The distinguished scheduler edge may depend on the complete current payload.
Selecting it increments a counter; every draw, including a target draw, may
otherwise update the payload arbitrarily.  A natural Bellman potential proves
that `d` hits cost at most `n*d` in truncated expectation.  Consequently at
least half of all depth-`2*n*d` scheduler words have completed the service.
-/

namespace PredictableTargetCounterFiniteTree

set_option autoImplicit false

open FiniteUniformStoppingTree
open PredictableTwoTargetFiniteTree

private theorem sum_map_const {A : Type} (xs : List A) (c : Nat) :
    (xs.map (fun _ => c)).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons _ xs ih =>
      rw [List.map_cons, List.sum_cons, ih, List.length_cons]
      simp only [Nat.succ_mul]
      omega

private theorem pred_mul (m c : Nat) (hm : 0 < m) :
    m * c = c + (m - 1) * c := by
  obtain ⟨x, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simp [Nat.succ_mul, Nat.add_comm]

private theorem nodup_ofFn_of_injective {n : Nat} {A : Type}
    (f : Fin n -> A) (hf : Function.Injective f) :
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

private theorem sum_one_exception
    {A : Type} [BEq A] [LawfulBEq A]
    (xs : List A) (a : A) (f : A -> Nat) (c : Nat)
    (hnodup : xs.Nodup) (ha : a ∈ xs)
    (hother : forall z, z ∈ xs -> z ≠ a -> f z = c) :
    (xs.map f).sum = f a + (xs.length - 1) * c := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      rw [List.nodup_cons] at hnodup
      by_cases hxa : x = a
      · subst x
        have hall : xs.map f = xs.map (fun _ => c) := by
          apply List.map_congr_left
          intro z hz
          exact hother z (by simp [hz]) (by
            intro hza
            subst z
            exact hnodup.1 hz)
        rw [List.map_cons, List.sum_cons, hall, sum_map_const]
        simp
      · have hat : a ∈ xs := by
          rcases List.mem_cons.mp ha with h | h
          · exact False.elim (hxa h.symm)
          · exact h
        have hi := ih hnodup.2 hat (by
          intro z hz
          exact hother z (by simp [hz]))
        have hx : f x = c := hother x (by simp) hxa
        rw [List.map_cons, List.sum_cons, hx, hi, List.length_cons]
        have hpos : 0 < xs.length := List.length_pos_iff.mpr
          (List.ne_nil_of_mem hat)
        have hc := pred_mul xs.length c hpos
        rw [show xs.length + 1 - 1 = xs.length by omega]
        omega

/-- An active service state with fewer than `d` accumulated target hits. -/
structure ActiveHitState (S : Type) (d : Nat) where
  payload : S
  hits : Nat
  hits_lt : hits < d

/-- One raw scheduler draw.  The target is chosen predictably from the old
payload, while the payload update is unrestricted on every edge. -/
def targetCounterStep {S : Type} {n d : Nat}
    (target : S -> Fin n) (next : S -> Fin n -> S)
    (st : ActiveHitState S d) (e : Fin n) :
    StopNode (ActiveHitState S d) :=
  if htarget : e = target st.payload then
    if hdone : st.hits + 1 = d then .success
    else .active
      { payload := next st.payload e
        hits := st.hits + 1
        hits_lt := by have := st.hits_lt; omega }
  else .active
    { payload := next st.payload e
      hits := st.hits
      hits_lt := st.hits_lt }

/-- Canonical zero-hit start. -/
def initialState {S : Type} (payload : S) (d : Nat) (hd : 0 < d) :
    ActiveHitState S d where
  payload := payload
  hits := 0
  hits_lt := hd

private def servicePotential {S : Type} {d : Nat} (n : Nat) :
    StopNode (ActiveHitState S d) -> Nat
  | .active st => n * (d - st.hits)
  | .success => 0
  | .failure => 0

/-- The remaining-hit potential pays one unit of raw time per active step. -/
theorem targetCounter_natBellmanSuperSolution
    {S : Type} {n d : Nat} (target : S -> Fin n)
    (next : S -> Fin n -> S) :
    NatBellmanSuperSolution (targetCounterStep (d := d) target next) 1
      (servicePotential (S := S) (d := d) n) := by
  refine ⟨rfl, rfl, ?_⟩
  intro st
  let c := n * (d - st.hits)
  let a := servicePotential (S := S) (d := d) n
    (targetCounterStep (d := d) target next st (target st.payload))
  have hsum :
      (List.ofFn (fun e : Fin n =>
        servicePotential (S := S) (d := d) n
          (targetCounterStep target next st e))).sum =
        a + (n - 1) * c := by
    have h := sum_one_exception
      (List.ofFn (fun i : Fin n => i)) (target st.payload)
      (fun e => servicePotential (S := S) (d := d) n
        (targetCounterStep target next st e)) c
      (nodup_ofFn_fin n)
      (by rw [List.mem_ofFn]; exact ⟨target st.payload, rfl⟩)
      (by
        intro e _ he
        simp [targetCounterStep, he, servicePotential, c])
    simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn] using h
  have hn : 0 < n := by have := (target st.payload).isLt; omega
  have hlt := st.hits_lt
  have hremain : d - st.hits = (d - (st.hits + 1)) + 1 := by omega
  have hac : a + n = c := by
    dsimp [a, c]
    by_cases hdone : st.hits + 1 = d
    · have hsub : d - st.hits = 1 := by omega
      simp [targetCounterStep, hdone, servicePotential, hsub]
    · simp [targetCounterStep, hdone, servicePotential, hremain,
          Nat.mul_add]
  simp only [servicePotential]
  change 1 * n +
      (List.ofFn (fun e : Fin n =>
        servicePotential (S := S) (d := d) n
          (targetCounterStep target next st e))).sum <= n * c
  rw [hsum]
  have hpred : n * c = c + (n - 1) * c := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [Nat.succ_mul, Nat.add_comm]
  calc
    1 * n + (a + (n - 1) * c) = (a + n) + (n - 1) * c := by omega
    _ = c + (n - 1) * c := by rw [hac]
    _ = n * c := hpred.symm
    _ <= n * c := Nat.le_refl _

/-- From zero hits, the truncated raw-duration numerator is at most `n*d`
times the scheduler-space size. -/
theorem initial_truncatedCost_le
    {S : Type} {n d : Nat} (target : S -> Fin n)
    (next : S -> Fin n -> S) (payload : S) (hd : 0 < d) (T : Nat) :
    truncatedActiveCostNumerator
        (targetCounterStep (d := d) target next)
        (.active (initialState payload d hd)) T <= n ^ T * (n * d) := by
  simpa [servicePotential, initialState] using
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      (targetCounterStep (d := d) target next) 1
      (servicePotential (S := S) (d := d) n)
      (targetCounter_natBellmanSuperSolution target next)
      (.active (initialState payload d hd)) T

/-- This service tree never has failure leaves. -/
theorem failureCount_eq_zero
    {S : Type} {n d : Nat} (target : S -> Fin n)
    (next : S -> Fin n -> S) : forall st T,
    failureCount (targetCounterStep (d := d) target next) (.active st) T = 0 := by
  intro st T
  induction T generalizing st with
  | zero => rfl
  | succ T ih =>
      simp only [failureCount, treeWeight, stepNode]
      calc
        (List.ofFn (fun e : Fin n => treeWeight
            (targetCounterStep target next) failureWeight
            (targetCounterStep target next st e) T)).sum =
            (List.ofFn (fun _ : Fin n => 0)).sum := by
              apply ofFn_sum_eq
              intro e
              by_cases ht : e = target st.payload
              · by_cases hd : st.hits + 1 = d
                · simp [targetCounterStep, ht, hd, treeWeight_success,
                    failureWeight]
                · simpa [targetCounterStep, ht, hd, failureCount] using
                    ih { payload := next st.payload e
                         hits := st.hits + 1
                         hits_lt := by have := st.hits_lt; omega }
              · simpa [targetCounterStep, ht, failureCount] using
                  ih { payload := next st.payload e
                       hits := st.hits
                       hits_lt := st.hits_lt }
        _ = 0 := by rw [ofFn_sum_const]; simp

/-- Markov at `2*n*d`: at least half of all scheduler words have accumulated
`d` hits of the history-adaptive target. -/
theorem initial_success_half_by_two_mul
    {S : Type} {n d : Nat} (target : S -> Fin n)
    (next : S -> Fin n -> S) (payload : S) (hd : 0 < d) :
    n ^ (2 * n * d) <=
      2 * successCount (targetCounterStep (d := d) target next)
        (.active (initialState payload d hd)) (2 * n * d) := by
  let step := targetCounterStep (d := d) target next
  let start := initialState payload d hd
  let T := 2 * n * d
  let N := n ^ T
  let A := activeCount step (.active start) T
  have hcost := initial_truncatedCost_le target next payload hd T
  have hlive := horizon_mul_activeCount_le_truncatedActiveCost
    step (.active start) T
  have hscaled : (n * d) * (2 * A) <= (n * d) * N := by
    calc
      (n * d) * (2 * A) = T * A := by dsimp [T]; ac_rfl
      _ <= truncatedActiveCostNumerator step (.active start) T := hlive
      _ <= N * (n * d) := by simpa [step, start, N] using hcost
      _ = (n * d) * N := by ac_rfl
  have hn : 0 < n := by have := (target payload).isLt; omega
  have hnd : 0 < n * d := Nat.mul_pos hn hd
  have hhalf : 2 * A <= N := Nat.le_of_mul_le_mul_left hscaled hnd
  have hpartition := node_count_partition step (.active start) T
  have hfailure := failureCount_eq_zero target next start T
  dsimp [A, N, T, step, start] at hhalf hpartition hfailure ⊢
  rw [hfailure] at hpartition
  omega

/-- The renewal-search specialization: `4*n` adaptive barrier-edge hits are
served with probability at least one half by horizon `8*n^2`. -/
theorem four_mul_success_half_by_eight_mul_sq
    {S : Type} {n : Nat} (target : S -> Fin n)
    (next : S -> Fin n -> S) (payload : S) (hn : 0 < n) :
    n ^ (8 * n ^ 2) <=
      2 * successCount (targetCounterStep (d := 4 * n) target next)
        (.active (initialState payload (4 * n) (by omega))) (8 * n ^ 2) := by
  have h := initial_success_half_by_two_mul target next payload (d := 4 * n)
    (by omega)
  have hT : 2 * n * (4 * n) = 8 * n ^ 2 := by
    rw [show 8 = 2 * 4 by decide, Nat.pow_two]
    ac_rfl
  rw [hT] at h
  exact h

#print axioms targetCounter_natBellmanSuperSolution
#print axioms initial_truncatedCost_le
#print axioms initial_success_half_by_two_mul
#print axioms four_mul_success_half_by_eight_mul_sq

end PredictableTargetCounterFiniteTree
