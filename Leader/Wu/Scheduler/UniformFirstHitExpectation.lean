import Leader.Wu.Elimination.ArbitraryInputExpectedCost
import Leader.Wu.Scheduler.RepeatedBlocks

/-!
# The expected first-hitting time under the uniform scheduler, literally

A deterministic transition `next : S → Fin n → S` is driven by the uniform
random scheduler: at every step one of the `n` edges is chosen uniformly and
independently.  The first hitting time of a target `P` from `x` is
`τ = min {t : P (x_t)}` (`τ = ∞` if the run never enters `P`).

No measure theory is needed.  The law of the scheduler is the uniform product
measure on `(Fin n)^ℕ`; the probability of every event depending only on the
first `t` symbols (a cylinder event) is its number of length-`t` words divided
by `n^t`.  All events below are of that kind:

* `{τ > t}`: the states `x_0, …, x_t` all lie outside `P`.  Its word count is
  `survivalNumerator x t`, so `P(τ > t) = survivalProb x t`.
* `{τ = k}`: `x_0, …, x_{k-1} ∉ P` and `x_k ∈ P`.  Its word count is
  `firstHitNumerator x k`, so `P(τ = k) = firstHitProb x k`.
* `min(τ, T)`: its expectation is `costNumerator x T / n^T`
  (`truncatedExpectation`), the repository's existing truncated cost.

## Definition of the expectation

`τ` takes values in `ℕ ∪ {∞}`.  Its expectation is
`E[τ] = Σ_{k ≥ 0} k · P(τ = k) + ∞ · P(τ = ∞)`.  So `E[τ] ≤ B` for a finite
`B` means exactly two things: `P(τ = ∞) = 0` and every partial sum
`Σ_{k ≤ K} k · P(τ = k)` is at most `B` (a series of nonnegative terms is at
most `B` iff all its partial sums are).  `ExpectedHittingTimeAtMost x B` is
this conjunction, with `P(τ = ∞) = 0` written as `AlmostSurelyHits x`:
`P(τ > K) ≤ 1/m` for some `K`, for every `m`.  Since `{τ = ∞}` is the
decreasing intersection of the events `{τ > K}` (monotone:
`survivalNumerator_succ_le`), this says `P(τ = ∞) = inf_K P(τ > K) = 0`.

## The three standard forms coincide

* `truncatedExpectation_eq_tailProbSum`: `E[min(τ, T)] = Σ_{t<T} P(τ > t)`;
  in numerators `costNumerator_eq_tailSum`: `cost(T) = Σ_{t<T} F(t)·n^{T−t}`.
* `truncatedExpectation_mono`: `E[min(τ, T)]` is nondecreasing in `T`
  (numerators: `n · cost(T) ≤ cost(T+1)`), so its supremum is its limit,
  which by monotone convergence is `E[τ]`.
* `expectedHittingTimeAtMost_iff`: `E[τ] ≤ B` (the definition above)
  if and only if `E[min(τ, T)] ≤ B` for every `T`.  This is the
  combinatorial content of monotone convergence and of the tail-sum formula
  `E[τ] = Σ_t P(τ > t)`; it is proved here from word counts, including the
  step that the truncated bounds force `P(τ = ∞) = 0`
  (`survival_mul_le_cost`: `T · P(τ ≥ T+1) ≤ E[min(τ, T)]`).

Consequently an upstream bound `∀ T, costNumerator x T ≤ n^T * B` is,
exactly, `E[τ] ≤ B` for the uniform scheduler.

The bridge `survivalNumerator_eq_countP` identifies `survivalNumerator` with
any existing failure numerator of the form "count the length-`T` scheduler
words whose prefix test never met the target".
-/

namespace UniformFirstHit

open FiniteUniformStoppingTree K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

variable {S : Type} {n : Nat}

/-! ## Word counts of the events `{τ > t}` and `{τ = k}` -/

section Counts

variable (next : S → Fin n → S) (P : S → Prop)

open Classical in
/-- Indicator of `{τ > |w|}` on the word `w`: every state visited along `w`,
including the start and the endpoint, lies outside the target. -/
noncomputable def survivalWord : S → List (Fin n) → Nat
  | x, [] => if P x then 0 else 1
  | x, e :: es => if P x then 0 else survivalWord (next x e) es

open Classical in
/-- Indicator of `{τ = |w|}` on the word `w`: the target is entered for the
first time at the endpoint of `w`. -/
noncomputable def firstHitWord : S → List (Fin n) → Nat
  | x, [] => if P x then 1 else 0
  | x, e :: es => if P x then 0 else firstHitWord (next x e) es

/-- `F(t)`: number of length-`t` scheduler words with `τ > t`, so
`P(τ > t) = F(t) / n^t`. -/
noncomputable def survivalNumerator (x : S) (t : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n t (survivalWord next P x)

/-- Number of length-`k` scheduler words with `τ = k`, so
`P(τ = k) = firstHitNumerator x k / n^k`. -/
noncomputable def firstHitNumerator (x : S) (k : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n k (firstHitWord next P x)

/-- `Σ_{k ≤ K} k · #{τ = k} · n^{K−k}`, by its recursion; the closed form is
`momentNumerator_eq_sum`.  Divided by `n^K` it is `Σ_{k ≤ K} k · P(τ = k)`. -/
noncomputable def momentNumerator (x : S) : Nat → Nat
  | 0 => 0
  | K + 1 => n * momentNumerator x K + (K + 1) * firstHitNumerator next P x (K + 1)

end Counts

/-! ## Elementary recursions -/

section Recursions

variable (next : S → Fin n → S) (P : S → Prop)

private theorem wordSum_eq_zero (T : Nat) (f : List (Fin n) → Nat)
    (hf : ∀ u, f u = 0) : FixedSpanRenewalPayload.wordSum n T f = 0 := by
  unfold FixedSpanRenewalPayload.wordSum
  generalize allSchedules n T = xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [hf, ih]

theorem survivalNumerator_of_target (x : S) (hx : P x) (T : Nat) :
    survivalNumerator next P x T = 0 := by
  unfold survivalNumerator
  apply wordSum_eq_zero
  intro u
  cases u <;> simp [survivalWord, hx]

theorem firstHitNumerator_succ_of_target (x : S) (hx : P x) (T : Nat) :
    firstHitNumerator next P x (T + 1) = 0 := by
  unfold firstHitNumerator
  rw [FixedSpanRenewalPayload.wordSum_succ]
  rw [ofFn_sum_eq _ (fun _ => 0) (fun e => wordSum_eq_zero T _
    (fun u => by simp [firstHitWord, hx])), ofFn_sum_const]
  exact Nat.mul_zero _

theorem survivalNumerator_zero_of_not (x : S) (hx : ¬ P x) :
    survivalNumerator next P x 0 = 1 := by
  simp [survivalNumerator, FixedSpanRenewalPayload.wordSum, allSchedules,
    survivalWord, hx]

theorem firstHit_add_survival_zero (x : S) :
    firstHitNumerator next P x 0 + survivalNumerator next P x 0 = 1 := by
  by_cases hx : P x <;>
    simp [survivalNumerator, firstHitNumerator, FixedSpanRenewalPayload.wordSum,
      allSchedules, survivalWord, firstHitWord, hx]

/-- First-symbol recursion for `F`. -/
theorem survivalNumerator_succ_of_not (x : S) (hx : ¬ P x) (T : Nat) :
    survivalNumerator next P x (T + 1) =
      (List.ofFn (fun e => survivalNumerator next P (next x e) T)).sum := by
  unfold survivalNumerator
  rw [FixedSpanRenewalPayload.wordSum_succ]
  apply ofFn_sum_eq
  intro e
  congr 1
  funext u
  simp only [survivalWord, if_neg hx]

/-- First-symbol recursion for the first-hit counts. -/
theorem firstHitNumerator_succ_of_not (x : S) (hx : ¬ P x) (T : Nat) :
    firstHitNumerator next P x (T + 1) =
      (List.ofFn (fun e => firstHitNumerator next P (next x e) T)).sum := by
  unfold firstHitNumerator
  rw [FixedSpanRenewalPayload.wordSum_succ]
  apply ofFn_sum_eq
  intro e
  congr 1
  funext u
  simp only [firstHitWord, if_neg hx]

/-- **Survival splits into first hit and further survival.**  Among the
`n · F(T)` words of length `T+1` whose first `T` steps survive, those whose
last state enters the target are `{τ = T+1}`, the rest are `{τ > T+1}`:
`#{τ = T+1} + F(T+1) = n · F(T)`. -/
theorem firstHit_add_survival_succ (x : S) (T : Nat) :
    firstHitNumerator next P x (T + 1) + survivalNumerator next P x (T + 1) =
      n * survivalNumerator next P x T := by
  induction T generalizing x with
  | zero =>
    by_cases hx : P x
    · rw [firstHitNumerator_succ_of_target next P x hx,
        survivalNumerator_of_target next P x hx,
        survivalNumerator_of_target next P x hx]
      simp
    · rw [firstHitNumerator_succ_of_not next P x hx,
        survivalNumerator_succ_of_not next P x hx, ← ofFn_sum_add,
        ofFn_sum_eq _ (fun _ => 1) (fun e => firstHit_add_survival_zero next P (next x e)),
        ofFn_sum_const, survivalNumerator_zero_of_not next P x hx]
  | succ T ih =>
    by_cases hx : P x
    · rw [firstHitNumerator_succ_of_target next P x hx,
        survivalNumerator_of_target next P x hx,
        survivalNumerator_of_target next P x hx]
      simp
    · rw [firstHitNumerator_succ_of_not next P x hx,
        survivalNumerator_succ_of_not next P x hx, ← ofFn_sum_add,
        ofFn_sum_eq _ _ (fun e => ih (next x e)), ofFn_sum_mul_left,
        survivalNumerator_succ_of_not next P x hx T]

/-- `P(τ > T+1) ≤ P(τ > T)`, in numerators. -/
theorem survivalNumerator_succ_le (x : S) (T : Nat) :
    survivalNumerator next P x (T + 1) ≤ n * survivalNumerator next P x T := by
  have h := firstHit_add_survival_succ next P x T
  omega

/-- **Key cost recursion.**  `cost(T+1) = n · (cost(T) + F(T))`, i.e.
`E[min(τ, T+1)] = E[min(τ, T)] + P(τ > T)`. -/
theorem costNumerator_succ_eq (x : S) (T : Nat) :
    costNumerator next P x (T + 1) =
      n * (costNumerator next P x T + survivalNumerator next P x T) := by
  induction T generalizing x with
  | zero =>
    by_cases hx : P x
    · rw [costNumerator_terminal next P x hx, costNumerator_terminal next P x hx,
        survivalNumerator_of_target next P x hx]
      simp
    · rw [costNumerator_succ next P x hx 0,
        ofFn_sum_eq _ (fun _ => 0) (fun e => costNumerator_zero next P (next x e)),
        ofFn_sum_const, costNumerator_zero, survivalNumerator_zero_of_not next P x hx]
      simp
  | succ T ih =>
    by_cases hx : P x
    · rw [costNumerator_terminal next P x hx, costNumerator_terminal next P x hx,
        survivalNumerator_of_target next P x hx]
      simp
    · rw [costNumerator_succ next P x hx (T + 1),
        ofFn_sum_eq _ _ (fun e => ih (next x e)), ofFn_sum_mul_left, ofFn_sum_add,
        costNumerator_succ next P x hx T, survivalNumerator_succ_of_not next P x hx T,
        Nat.pow_succ n (T + 1)]
      generalize n ^ (T + 1) = p
      generalize (List.ofFn fun e => costNumerator next P (next x e) T).sum = a
      generalize (List.ofFn fun e => survivalNumerator next P (next x e) T).sum = b
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_comm p n]
      omega

/-- Monotonicity of the truncated expectation, cross-multiplied:
`E[min(τ, T)] ≤ E[min(τ, T+1)]`. -/
theorem costNumerator_mono (x : S) (T : Nat) :
    n * costNumerator next P x T ≤ costNumerator next P x (T + 1) := by
  rw [costNumerator_succ_eq, Nat.mul_add]
  exact Nat.le_add_right _ _

private theorem sum_map_mul_left (l : List Nat) (a : Nat) (f : Nat → Nat) :
    (l.map (fun t => a * f t)).sum = a * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons t l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

/-- Raising the exponent horizon `e` by one multiplies every term
`g t · n^{e−t}` (`t < m ≤ e + 1`) by `n`. -/
private theorem range_shift (g : Nat → Nat) (m e : Nat) (hm : m ≤ e + 1) :
    ((List.range m).map (fun t => g t * n ^ (e + 1 - t))).sum =
      n * ((List.range m).map (fun t => g t * n ^ (e - t))).sum := by
  rw [← sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t ht
  have ht' : t < m := List.mem_range.1 ht
  rw [show e + 1 - t = (e - t) + 1 by omega, Nat.pow_succ]
  rw [Nat.mul_comm (n ^ (e - t)) n, Nat.mul_left_comm]

/-- **Tail-sum formula, numerators.**
`cost(T) = Σ_{t<T} F(t) · n^{T−t}`, i.e. `E[min(τ, T)] = Σ_{t<T} P(τ > t)`. -/
theorem costNumerator_eq_tailSum (x : S) (T : Nat) :
    costNumerator next P x T =
      ((List.range T).map
        (fun t => survivalNumerator next P x t * n ^ (T - t))).sum := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [costNumerator_succ_eq, ih, List.range_succ, List.map_append,
      List.sum_append, range_shift _ T T (Nat.le_succ T)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      show T + 1 - T = 1 by omega, Nat.pow_one, Nat.add_zero, Nat.mul_add]
    rw [Nat.mul_comm (survivalNumerator next P x T) n]

/-- Closed form of `momentNumerator`: `Σ_{k ≤ K} k · #{τ = k} · n^{K−k}`. -/
theorem momentNumerator_eq_sum (x : S) (K : Nat) :
    momentNumerator next P x K =
      ((List.range (K + 1)).map
        (fun k => k * firstHitNumerator next P x k * n ^ (K - k))).sum := by
  induction K with
  | zero => simp [momentNumerator]
  | succ K ih =>
    rw [momentNumerator, ih, List.range_succ (n := K + 1), List.map_append,
      List.sum_append, range_shift _ (K + 1) K (Nat.le_refl _)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.sub_self, Nat.pow_zero, Nat.mul_one, Nat.add_zero]

/-- **Abel summation.**  `E[τ; τ ≤ K] + K · P(τ > K) = E[min(τ, K)]`. -/
theorem moment_add_survival (x : S) (K : Nat) :
    momentNumerator next P x K + K * survivalNumerator next P x K =
      costNumerator next P x K := by
  induction K with
  | zero => simp [momentNumerator]
  | succ K ih =>
    have h1 := firstHit_add_survival_succ next P x K
    rw [momentNumerator, costNumerator_succ_eq, ← ih, Nat.add_assoc, ← Nat.mul_add, h1]
    rw [Nat.succ_mul, Nat.mul_left_comm K n, Nat.mul_add, Nat.mul_add]
    omega

theorem moment_le_cost (x : S) (K : Nat) :
    momentNumerator next P x K ≤ costNumerator next P x K := by
  rw [← moment_add_survival next P x K]
  exact Nat.le_add_right _ _

/-- **Almost-sure hitting from a cost bound.**  `T · F(T) ≤ cost(T)`, i.e.
`T · P(τ > T) ≤ E[min(τ, T)]` (Markov's inequality at level `T`). -/
theorem survival_mul_le_cost (x : S) (T : Nat) :
    T * survivalNumerator next P x T ≤ costNumerator next P x T := by
  rw [← moment_add_survival next P x T]
  exact Nat.le_add_left _ _

/-- For `K ≥ T`: `E[min(τ, T)] ≤ E[τ; τ ≤ K] + T · P(τ > K)`, in numerators
at horizon `K = T + j`. -/
theorem cost_le_moment_add (x : S) (T j : Nat) :
    n ^ j * costNumerator next P x T ≤
      momentNumerator next P x (T + j) + T * survivalNumerator next P x (T + j) := by
  induction j with
  | zero =>
    rw [Nat.pow_zero, Nat.one_mul, Nat.add_zero, moment_add_survival]
    exact Nat.le_refl _
  | succ j ih =>
    have h1 := firstHit_add_survival_succ next P x (T + j)
    have hmul := Nat.mul_le_mul_left n ih
    rw [Nat.pow_succ, Nat.mul_comm (n ^ j) n, Nat.mul_assoc]
    refine Nat.le_trans hmul ?_
    rw [show T + (j + 1) = T + j + 1 by omega, momentNumerator, Nat.mul_add,
      Nat.mul_left_comm n T, ← h1, Nat.mul_add, Nat.add_assoc]
    have hle : T * firstHitNumerator next P x (T + (j + 1)) ≤
        (T + (j + 1)) * firstHitNumerator next P x (T + (j + 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- A survival bound at horizon `K` persists at every later horizon. -/
theorem survival_bound_persist (x : S) (m K i : Nat)
    (h : m * survivalNumerator next P x K ≤ n ^ K) :
    m * survivalNumerator next P x (K + i) ≤ n ^ (K + i) := by
  induction i with
  | zero => exact h
  | succ i ih =>
    calc m * survivalNumerator next P x (K + (i + 1))
        ≤ m * (n * survivalNumerator next P x (K + i)) :=
          Nat.mul_le_mul_left m (survivalNumerator_succ_le next P x (K + i))
      _ = n * (m * survivalNumerator next P x (K + i)) := Nat.mul_left_comm _ _ _
      _ ≤ n * n ^ (K + i) := Nat.mul_le_mul_left n ih
      _ = n ^ (K + (i + 1)) := by rw [← Nat.add_assoc, Nat.pow_succ, Nat.mul_comm]

private theorem pow_pos_nat (hn : 0 < n) (k : Nat) : 0 < n ^ k := by
  induction k with
  | zero => exact Nat.one_pos
  | succ k ih => rw [Nat.pow_succ]; exact Nat.mul_pos ih hn

/-- **Monotone convergence, combinatorial form.**  For `n > 0` and every
`B`: all truncated expectations are at most `B` iff `P(τ = ∞) = 0` and all
partial sums of `Σ_k k · P(τ = k)` are at most `B`. -/
theorem truncatedBound_iff (hn : 0 < n) (x : S) (B : Nat) :
    (∀ T, costNumerator next P x T ≤ n ^ T * B) ↔
      ((∀ m, ∃ K, m * survivalNumerator next P x K ≤ n ^ K) ∧
        ∀ K, momentNumerator next P x K ≤ n ^ K * B) := by
  constructor
  · intro hB
    refine ⟨?_, fun K => Nat.le_trans (moment_le_cost next P x K) (hB K)⟩
    intro m
    refine ⟨m * B + 1, ?_⟩
    have h := Nat.le_trans (survival_mul_le_cost next P x (m * B + 1)) (hB (m * B + 1))
    rcases Nat.eq_zero_or_pos B with hB0 | hBpos
    · subst hB0
      simp only [Nat.mul_zero, Nat.zero_add, Nat.one_mul] at h
      rw [Nat.mul_zero, Nat.zero_add, Nat.le_zero.1 h, Nat.mul_zero]
      exact Nat.zero_le _
    · apply Nat.le_of_mul_le_mul_right _ hBpos
      refine Nat.le_trans ?_ h
      rw [Nat.mul_right_comm]
      exact Nat.mul_le_mul_right _ (Nat.le_succ _)
  · rintro ⟨has, hmom⟩ T
    obtain ⟨K, hK⟩ := has (T * n ^ T + 1)
    have hK' := survival_bound_persist next P x (T * n ^ T + 1) K T hK
    rw [Nat.add_comm K T] at hK'
    have hc := cost_le_moment_add next P x T K
    have hm := hmom (T + K)
    generalize hs : survivalNumerator next P x (T + K) = s at hK' hc
    generalize hN : n ^ (T + K) = N at hK' hm
    have hNeq : N = n ^ T * n ^ K := by rw [← hN, Nat.pow_add]
    have hpT : 0 < n ^ T := pow_pos_nat hn T
    have hpK : 0 < n ^ K := pow_pos_nat hn K
    have hNpos : 0 < N := by rw [hNeq]; exact Nat.mul_pos hpT hpK
    -- (1) n^K · cost ≤ N·B + T·s; (2) (T·n^T + 1)·s ≤ N.
    have h1 : n ^ K * costNumerator next P x T ≤ N * B + T * s :=
      Nat.le_trans hc (Nat.add_le_add_right hm _)
    have h1' : N * costNumerator next P x T ≤ N * (n ^ T * B) + n ^ T * (T * s) := by
      have := Nat.mul_le_mul_left (n ^ T) h1
      rw [Nat.mul_add, ← Nat.mul_assoc, ← hNeq, Nat.mul_left_comm (n ^ T) N B] at this
      exact this
    rcases Nat.eq_zero_or_pos s with hs0 | hspos
    · subst hs0
      rw [Nat.mul_zero, Nat.mul_zero, Nat.add_zero] at h1'
      exact Nat.le_of_mul_le_mul_left h1' hNpos
    · have h2 : n ^ T * (T * s) < N := by
        have : n ^ T * (T * s) + s ≤ N := by
          rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm T (n ^ T), Nat.mul_assoc] at hK'
          exact hK'
        omega
      have h3 : N * costNumerator next P x T < N * (n ^ T * B + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left h3)

end Recursions

/-! ## Probabilities and expectations as rationals -/

section Rational

variable (next : S → Fin n → S) (P : S → Prop)

/-- `P(τ > t)` under the uniform scheduler. -/
noncomputable def survivalProb (x : S) (t : Nat) : Rat :=
  (survivalNumerator next P x t : Rat) / (n : Rat) ^ t

/-- `P(τ = k)` under the uniform scheduler. -/
noncomputable def firstHitProb (x : S) (k : Nat) : Rat :=
  (firstHitNumerator next P x k : Rat) / (n : Rat) ^ k

/-- `E[min(τ, T)]` under the uniform scheduler: the existing truncated cost
numerator over its denominator `n^T`. -/
noncomputable def truncatedExpectation (x : S) (T : Nat) : Rat :=
  (costNumerator next P x T : Rat) / (n : Rat) ^ T

/-- `Σ_{k ≤ K} k · P(τ = k)`, the partial sums of the series defining
`E[τ]` on `{τ < ∞}`. -/
noncomputable def partialExpectation (x : S) : Nat → Rat
  | 0 => 0
  | K + 1 => partialExpectation x K + ((K + 1 : Nat) : Rat) * firstHitProb next P x (K + 1)

/-- `Σ_{t < T} P(τ > t)`. -/
noncomputable def tailProbSum (x : S) : Nat → Rat
  | 0 => 0
  | T + 1 => tailProbSum x T + survivalProb next P x T

/-- `P(τ = ∞) = 0`: for every `m`, some horizon `K` has `P(τ > K) ≤ 1/m`. -/
def AlmostSurelyHits (x : S) : Prop :=
  ∀ m : Nat, ∃ K : Nat, (m : Rat) * survivalProb next P x K ≤ 1

/-- **`E[τ] ≤ B` for the uniform scheduler.**  `τ` is `ℕ ∪ {∞}`-valued and
`E[τ] = Σ_k k · P(τ = k) + ∞ · P(τ = ∞)`; this is at most a finite `B` iff
`P(τ = ∞) = 0` and every partial sum of the series is at most `B`. -/
def ExpectedHittingTimeAtMost (x : S) (B : Rat) : Prop :=
  AlmostSurelyHits next P x ∧ ∀ K : Nat, partialExpectation next P x K ≤ B

private theorem rat_div_le_iff {a b q : Rat} (hq : 0 < q) :
    a / q ≤ b ↔ a ≤ b * q := by
  constructor
  · intro h
    have h' := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hq)
    rwa [Rat.div_mul_cancel (Rat.ne_of_gt hq)] at h'
  · intro h
    apply Rat.le_of_mul_le_mul_right _ hq
    rwa [Rat.div_mul_cancel (Rat.ne_of_gt hq)]

private theorem rat_mul_div_cancel_right (a q m : Rat) (hm : m ≠ 0) :
    m * a / (q * m) = a / q := by
  rw [Rat.div_def, Rat.div_def, Rat.inv_mul_rev, Rat.mul_comm m a, Rat.mul_assoc,
    ← Rat.mul_assoc m, Rat.mul_inv_cancel m hm, Rat.one_mul]

private theorem rat_add_div (a b q : Rat) : (a + b) / q = a / q + b / q := by
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.add_mul]

private theorem rat_mul_div_assoc (a b q : Rat) : a * b / q = a * (b / q) := by
  rw [Rat.div_def, Rat.div_def, Rat.mul_assoc]

private theorem pow_pos_rat (hn : 0 < n) (T : Nat) : (0 : Rat) < (n : Rat) ^ T :=
  Rat.pow_pos (Rat.natCast_pos.2 hn)

/-- A numerator bound over `n^T` is the rational bound. -/
theorem natRatio_le_iff (hn : 0 < n) (a T B : Nat) :
    (a : Rat) / (n : Rat) ^ T ≤ (B : Rat) ↔ a ≤ n ^ T * B := by
  rw [rat_div_le_iff (pow_pos_rat hn T), ← Rat.natCast_pow, ← Rat.natCast_mul,
    Rat.natCast_le_natCast, Nat.mul_comm B]

theorem survivalProb_bound_iff (hn : 0 < n) (x : S) (m K : Nat) :
    (m : Rat) * survivalProb next P x K ≤ 1 ↔
      m * survivalNumerator next P x K ≤ n ^ K := by
  unfold survivalProb
  rw [← rat_mul_div_assoc, ← Rat.natCast_mul]
  have h := natRatio_le_iff hn (m * survivalNumerator next P x K) K 1
  rw [Nat.mul_one] at h
  exact h

/-- **Tail-sum formula.**  `E[min(τ, T)] = Σ_{t < T} P(τ > t)`. -/
theorem truncatedExpectation_eq_tailProbSum (hn : 0 < n) (x : S) (T : Nat) :
    truncatedExpectation next P x T = tailProbSum next P x T := by
  induction T with
  | zero =>
    simp [truncatedExpectation, tailProbSum, costNumerator_zero]
    rw [Rat.div_def, Rat.zero_mul]
  | succ T ih =>
    rw [tailProbSum, ← ih]
    unfold truncatedExpectation survivalProb
    rw [costNumerator_succ_eq, Rat.natCast_mul, Rat.natCast_add, Rat.pow_succ,
      rat_mul_div_cancel_right _ _ _ (Rat.ne_of_gt (Rat.natCast_pos.2 hn)), rat_add_div]

theorem survivalProb_nonneg (hn : 0 < n) (x : S) (t : Nat) :
    0 ≤ survivalProb next P x t := by
  unfold survivalProb
  rw [Rat.div_def]
  exact Rat.mul_nonneg Rat.natCast_nonneg
    (Rat.le_of_lt (Rat.inv_pos.2 (pow_pos_rat hn t)))

/-- `E[min(τ, T)]` is nondecreasing in `T`. -/
theorem truncatedExpectation_mono (hn : 0 < n) (x : S) (T : Nat) :
    truncatedExpectation next P x T ≤ truncatedExpectation next P x (T + 1) := by
  rw [truncatedExpectation_eq_tailProbSum next P hn, truncatedExpectation_eq_tailProbSum next P hn,
    tailProbSum]
  have h := (Rat.add_le_add_left (c := tailProbSum next P x T)).2
    (survivalProb_nonneg next P hn x T)
  rwa [Rat.add_zero] at h

theorem truncatedExpectation_le_of_le (hn : 0 < n) (x : S) {T T' : Nat} (h : T ≤ T') :
    truncatedExpectation next P x T ≤ truncatedExpectation next P x T' := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  induction j with
  | zero => exact Rat.le_refl
  | succ j ih =>
    exact Rat.le_trans (ih (Nat.le_add_right _ _))
      (truncatedExpectation_mono next P hn x (T + j))

/-- Since `E[min(τ, T)]` is nondecreasing, being bounded by `B` at every `T`
is the same as being bounded by `B` along any cofinal set of horizons: the
supremum and the limit agree. -/
theorem truncatedBound_iff_cofinal (hn : 0 < n) (x : S) (B : Rat) :
    (∀ T, truncatedExpectation next P x T ≤ B) ↔
      ∀ T, ∃ T', T ≤ T' ∧ truncatedExpectation next P x T' ≤ B := by
  constructor
  · intro h T
    exact ⟨T, Nat.le_refl T, h T⟩
  · intro h T
    obtain ⟨T', hT, hB⟩ := h T
    exact Rat.le_trans (truncatedExpectation_le_of_le next P hn x hT) hB

/-- `Σ_{k ≤ K} k · P(τ = k)` is the moment numerator over `n^K`. -/
theorem partialExpectation_eq (hn : 0 < n) (x : S) (K : Nat) :
    partialExpectation next P x K = (momentNumerator next P x K : Rat) / (n : Rat) ^ K := by
  induction K with
  | zero =>
    simp [partialExpectation, momentNumerator]
    rw [Rat.div_def, Rat.zero_mul]
  | succ K ih =>
    rw [partialExpectation, ih, momentNumerator, firstHitProb,
      Rat.natCast_add (n * momentNumerator next P x K),
      Rat.natCast_mul n, Rat.natCast_mul (K + 1), Rat.pow_succ,
      rat_add_div, rat_mul_div_cancel_right _ _ _ (Rat.ne_of_gt (Rat.natCast_pos.2 hn)),
      rat_mul_div_assoc]

/-- `T · P(τ > T) ≤ E[min(τ, T)]`; hence `P(τ > T) ≤ B / T` under an
expectation bound `B`. -/
theorem mul_survivalProb_le_truncated (hn : 0 < n) (x : S) (T : Nat) :
    (T : Rat) * survivalProb next P x T ≤ truncatedExpectation next P x T := by
  unfold survivalProb truncatedExpectation
  rw [← rat_mul_div_assoc, ← Rat.natCast_mul, rat_div_le_iff (pow_pos_rat hn T),
    Rat.div_mul_cancel (Rat.ne_of_gt (pow_pos_rat hn T)), Rat.natCast_le_natCast]
  exact survival_mul_le_cost next P x T

/-- **`E[τ] ≤ B` iff every truncated expectation is at most `B`.**  The
right side is the repository's existing cost clause; the left side is the
definition of the expectation of the `ℕ ∪ {∞}`-valued hitting time. -/
theorem expectedHittingTimeAtMost_iff (hn : 0 < n) (x : S) (B : Nat) :
    ExpectedHittingTimeAtMost next P x (B : Rat) ↔
      ∀ T, truncatedExpectation next P x T ≤ (B : Rat) := by
  have hT : (∀ T, truncatedExpectation next P x T ≤ (B : Rat)) ↔
      ∀ T, costNumerator next P x T ≤ n ^ T * B :=
    forall_congr' fun T => natRatio_le_iff hn _ T B
  have hM : (∀ K, partialExpectation next P x K ≤ (B : Rat)) ↔
      ∀ K, momentNumerator next P x K ≤ n ^ K * B :=
    forall_congr' fun K => by
      rw [partialExpectation_eq next P hn]
      exact natRatio_le_iff hn _ K B
  have hA : AlmostSurelyHits next P x ↔
      ∀ m, ∃ K, m * survivalNumerator next P x K ≤ n ^ K :=
    forall_congr' fun m => exists_congr fun K => survivalProb_bound_iff next P hn x m K
  unfold ExpectedHittingTimeAtMost
  rw [hT, hM, hA]
  exact (truncatedBound_iff next P hn x B).symm

/-- The cross-multiplied cost clause used by the upstream statements is
exactly `E[τ] ≤ B`. -/
theorem expectedHittingTimeAtMost_iff_cost (hn : 0 < n) (x : S) (B : Nat) :
    ExpectedHittingTimeAtMost next P x (B : Rat) ↔
      ∀ T, costNumerator next P x T ≤ n ^ T * B := by
  rw [expectedHittingTimeAtMost_iff next P hn]
  exact forall_congr' fun T => natRatio_le_iff hn _ T B

end Rational

/-! ## Bridge to prefix-test failure numerators -/

section Bridge

variable (next : S → Fin n → S) (P : S → Prop)

private theorem countP_eq_sum {A : Type} (xs : List A) (p : A → Bool) :
    xs.countP p = (xs.map (fun w => if p w = true then 1 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.countP_cons, List.map_cons, List.sum_cons, ih, Nat.add_comm]

private theorem sum_map_flatMap {A B : Type} (xs : List A) (f : A → List B)
    (g : B → Nat) :
    ((xs.flatMap f).map g).sum = (xs.map (fun a => ((f a).map g).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, ih]

/-- The forward enumeration `allSchedules` and the reversed-word sum
`wordSum` agree: both are the sum over all `n^T` words. -/
theorem allSchedules_sum_eq_wordSum (T : Nat) (g : List (Fin n) → Nat) :
    ((allSchedules n T).map g).sum = FixedSpanRenewalPayload.wordSum n T g := by
  induction T generalizing g with
  | zero => simp [FixedSpanRenewalPayload.wordSum, allSchedules]
  | succ T ih =>
    rw [FixedSpanRenewalPayload.wordSum_succ, show T + 1 = 1 + T by omega,
      PPLLSchedulerBlocks.allSchedules_add]
    have h1 : allSchedules n 1 = List.ofFn (fun e : Fin n => [e]) := by
      simp [allSchedules]
    rw [h1, sum_map_flatMap, List.map_ofFn]
    apply ofFn_sum_eq
    intro e
    show (((allSchedules n T).map (fun suf => [e] ++ suf)).map g).sum = _
    rw [List.map_map]
    exact ih (fun u => g (e :: u))

/-- Wordwise: the failure indicator of a prefix test equals `survivalWord`. -/
theorem survivalWord_eq_indicator (reach : S → List (Fin n) → Bool)
    (hnil : ∀ C, reach C [] = true ↔ P C)
    (hcons : ∀ C e es, reach C (e :: es) = true ↔ (P C ∨ reach (next C e) es = true))
    (x : S) (w : List (Fin n)) :
    (if (!(reach x w)) = true then 1 else 0) = survivalWord next P x w := by
  induction w generalizing x with
  | nil =>
    by_cases h : P x
    · have hr : reach x [] = true := (hnil x).2 h
      simp [survivalWord, h, hr]
    · have hr : reach x [] = false := by
        cases hr : reach x []
        · rfl
        · exact absurd ((hnil x).1 hr) h
      simp [survivalWord, h, hr]
  | cons e es ih =>
    by_cases h : P x
    · have hr : reach x (e :: es) = true := (hcons x e es).2 (Or.inl h)
      simp [survivalWord, h, hr]
    · have hr : reach x (e :: es) = reach (next x e) es := by
        apply Bool.eq_iff_iff.2
        rw [hcons x e es]
        exact ⟨fun h' => h'.resolve_left h, Or.inr⟩
      rw [hr, ih (next x e)]
      simp only [survivalWord, if_neg h]

/-- A failure numerator "count the length-`T` words whose prefix test never
met the target" is `F(T) = survivalNumerator x T`. -/
theorem survivalNumerator_eq_countP (reach : S → List (Fin n) → Bool)
    (hnil : ∀ C, reach C [] = true ↔ P C)
    (hcons : ∀ C e es, reach C (e :: es) = true ↔ (P C ∨ reach (next C e) es = true))
    (x : S) (T : Nat) :
    (allSchedules n T).countP (fun w => !(reach x w)) = survivalNumerator next P x T := by
  rw [countP_eq_sum, allSchedules_sum_eq_wordSum, survivalNumerator]
  congr 1
  funext w
  exact survivalWord_eq_indicator next P reach hnil hcons x w

end Bridge

end UniformFirstHit

#print axioms UniformFirstHit.firstHit_add_survival_succ
#print axioms UniformFirstHit.costNumerator_succ_eq
#print axioms UniformFirstHit.costNumerator_mono
#print axioms UniformFirstHit.costNumerator_eq_tailSum
#print axioms UniformFirstHit.momentNumerator_eq_sum
#print axioms UniformFirstHit.moment_add_survival
#print axioms UniformFirstHit.survival_mul_le_cost
#print axioms UniformFirstHit.truncatedBound_iff
#print axioms UniformFirstHit.truncatedExpectation_eq_tailProbSum
#print axioms UniformFirstHit.truncatedExpectation_mono
#print axioms UniformFirstHit.truncatedBound_iff_cofinal
#print axioms UniformFirstHit.partialExpectation_eq
#print axioms UniformFirstHit.mul_survivalProb_le_truncated
#print axioms UniformFirstHit.expectedHittingTimeAtMost_iff
#print axioms UniformFirstHit.expectedHittingTimeAtMost_iff_cost
#print axioms UniformFirstHit.survivalNumerator_eq_countP
