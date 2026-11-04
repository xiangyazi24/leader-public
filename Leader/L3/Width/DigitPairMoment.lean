import Leader.Wu.Elimination.ArbitraryInputExpectedCost

/-!
# Lemma e-max from per-pair exponential moments

Lemma e-max of repair.tex (`lem:e-max`, lines 1421-1465) composes the per-pair strict
completions of one lane: with `N = n (2 C_r + 1)` and `z = N / (N - 1)`, every comparison has
`E[z^{T_pair}] < 40` from an arbitrary legal state, so the maximum `T_max` of `m` of them has
`E[z^{T_max}] ≤ Σ E[z^{T_i}] < 40 m`, and Jensen with `ln z > 1 / N` gives
`E[T_max] < N ln (40 m)`.

This module states the per-goal input as an exponential moment and proves the composition on
the uniform scheduler, by word counts only (no measure theory, no real logarithm):

* `momentWord`, `momentNumerator`, `MomentBound`: on a scheduler word of length `L`, with
  `k = min(τ, L)` the truncated first-hit time, the weight `N^k (N-1)^{L-k}`; summed over the
  `n^T` words and divided by `n^T (N-1)^T` it is `E[z^{min(τ,T)}]`.  `MomentBound … N A x` says
  `E[z^{min(τ,T)}] ≤ A` for every `T`, i.e. `E[z^τ] ≤ A` (monotone convergence).
* `momentOfAllGoals` (union bound): persistent goals, each with moment at most `A` from `x` when
  not yet met, give the all-goal time moment at most `K A`.  Per word, the all-goal time is the
  first-hit time of one goal not met at `x` (`costWordAllLe`), and the weight is monotone in
  `k` (`weightMono`).  No independence is used.
* `costOfMoment` (Jensen, discrete): `E[z^τ] ≤ A` and `A (N-1)^t ≤ N^t` give `E[τ] ≤ t`.  The
  exponential sequence `z^k` lies above its secant at `t` (`tangentAbove`, `tangentBelow`,
  two Bernoulli inequalities), so `k + N ≤ t + N z^{k-t}` for every integer `k ≥ 0`; average.
  With `t` least such that `z^t ≥ A` this is `E[τ] ≤ ⌈log_z A⌉ ≤ N ln A + 1`.
* `simultaneousOfMoments`: the two together.
* `momentBlockFactor`: `5 (N-1)^N ≤ 2 N^N` for `N ≥ 2` (second-order Bernoulli), so a block of
  `N` letters multiplies `z^t` by at least `5/2`; `simultaneousOfMomentBlocks` takes
  `t = N j` with `K A 2^j ≤ 5^j`.  This pays `log_{5/2}` in place of `ln` (factor `1.09`).

What is NOT here: the per-pair moment `E[z^{T_pair}] < 40` itself.  It is the content of the
proof of Lemma e-max (geometric nominated-edge waits, preparation moment `w^{A_r} < 8`, failure
factorization `E[z^D 1_fail] ≤ y / 2` from the fair race, recursion `M_j < 5`).  The first-moment
clock `WidthStrictPairClock` (`E[T_pair] ≤ n h(r)`) does not imply it.
-/

namespace L3.PairMoment

open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false

/-! ### Finite sums over `Fin m` -/

/-- Pointwise comparison of finite sums. Consumer: `costOfMoment`, `momentOfAllGoals`. -/
theorem sumLe {m : Nat} (f g : Fin m → Nat) (h : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
    exact Nat.add_le_add (h 0) (ih _ _ (fun i => h i.succ))

/-- Additivity of finite sums. Consumer: `costOfMoment`, `sumSwap`. -/
theorem sumAdd {m : Nat} (f g : Fin m → Nat) :
    (List.ofFn fun i => f i + g i).sum = (List.ofFn f).sum + (List.ofFn g).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons, List.ofFn_succ,
      List.sum_cons, ih (fun i => f i.succ) (fun i => g i.succ)]
    omega

/-- A constant factor leaves a finite sum. Consumer: `costOfMoment`. -/
theorem sumMulLeft {m : Nat} (c : Nat) (f : Fin m → Nat) :
    (List.ofFn fun i => c * f i).sum = c * (List.ofFn f).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons,
      ih (fun i => f i.succ), Nat.mul_add]

/-- The sum of a constant. Consumer: `costOfMoment`, `momentOfAllGoals`. -/
theorem sumConst (m c : Nat) : (List.ofFn fun _ : Fin m => c).sum = m * c := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
    omega

/-- One term is at most the sum. Consumer: `momentWordAllLe`. -/
theorem termLeSum {m : Nat} (f : Fin m → Nat) (j : Fin m) : f j ≤ (List.ofFn f).sum := by
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
    rw [List.ofFn_succ, List.sum_cons]
    cases j using Fin.cases with
    | zero => exact Nat.le_add_right _ _
    | succ j => exact Nat.le_trans (ih (fun i => f i.succ) j) (Nat.le_add_left _ _)

/-- Exchange of a double finite sum. Consumer: `momentOfAllGoals`. -/
theorem sumSwap {m : Nat} : ∀ {K : Nat} (g : Fin K → Fin m → Nat),
    (List.ofFn fun w => (List.ofFn fun i => g i w).sum).sum =
      (List.ofFn fun i => (List.ofFn fun w => g i w).sum).sum := by
  intro K
  induction K with
  | zero =>
    intro g
    have h0 : (fun w : Fin m => (List.ofFn fun i : Fin 0 => g i w).sum) = fun _ => 0 :=
      funext fun w => by simp
    rw [h0, sumConst]
    simp
  | succ K ih =>
    intro g
    have h1 : (fun w : Fin m => (List.ofFn fun i : Fin (K + 1) => g i w).sum) =
        fun w => g 0 w + (List.ofFn fun i : Fin K => g i.succ w).sum :=
      funext fun w => by rw [List.ofFn_succ, List.sum_cons]
    rw [h1, sumAdd, ih (fun i => g i.succ), List.ofFn_succ (n := K), List.sum_cons]

/-! ### The exponential moment of a first-hit time -/

section Moment

variable {S : Type} {n : Nat}

/-- The weight `N^k (N-1)^{L-k}` of a scheduler word of length `L`, `k = min(τ, L)` its
truncated first-hit time.  Consumer: `momentNumerator`. -/
noncomputable def momentWord (next : S → Fin n → S) (P : S → Prop) (N : Nat) (x : S)
    (es : List (Fin n)) : Nat :=
  N ^ costWord next P x es * (N - 1) ^ (es.length - costWord next P x es)

/-- `E[z^{min(τ,T)}] · n^T (N-1)^T` with `z = N / (N-1)`. Consumer: `MomentBound`. -/
noncomputable def momentNumerator (next : S → Fin n → S) (P : S → Prop) (N : Nat) (x : S)
    (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T (momentWord next P N x)

/-- `E[z^τ] ≤ A`, `z = N / (N - 1)`, for the first hit of `P` from `x` under the uniform
scheduler (every truncation, so by monotone convergence the full moment).  This is the
per-pair input of Lemma e-max (`E[z^{T_pair}] < 40`, `N = n (2 C_r + 1)`).  Consumer:
`simultaneousOfMoments`. -/
def MomentBound (next : S → Fin n → S) (P : S → Prop) (N A : Nat) (x : S) : Prop :=
  ∀ T, momentNumerator next P N x T ≤ A * (n ^ T * (N - 1) ^ T)

/-- One step of the first-hit cost off the target. Consumer: `costWordAllLe`. -/
theorem costWordCons (next : S → Fin n → S) (P : S → Prop) (x : S) (e : Fin n)
    (es : List (Fin n)) (hx : ¬ P x) :
    costWord next P x (e :: es) = 1 + costWord next P (next x e) es := by
  classical
  simp [costWord, K2FiniteSafeEliminationExpected.rawCost, hx]

/-- For persistent goals not all met at `x`, on every word the all-goal first-hit time is at
most the first-hit time of one goal not met at `x`. Consumer: `momentWordAllLe`. -/
theorem costWordAllLe (next : S → Fin n → S) {K : Nat} (Good : Fin K → S → Prop)
    (hg : ∀ i x e, Good i x → Good i (next x e)) :
    ∀ (es : List (Fin n)) (x : S), ¬ (∀ i, Good i x) →
      ∃ j, ¬ Good j x ∧
        costWord next (fun y => ∀ i, Good i y) x es ≤ costWord next (Good j) x es := by
  intro es
  induction es with
  | nil =>
    intro x hx
    obtain ⟨j, hj⟩ := Classical.not_forall.mp hx
    refine ⟨j, hj, ?_⟩
    have h0 : costWord next (fun y => ∀ i, Good i y) x [] = 0 :=
      Nat.le_zero.mp (costWord_le_length next _ x [])
    rw [h0]
    exact Nat.zero_le _
  | cons e es ih =>
    intro x hx
    rw [costWordCons next _ x e es hx]
    by_cases hall : ∀ i, Good i (next x e)
    · obtain ⟨j, hj⟩ := Classical.not_forall.mp hx
      refine ⟨j, hj, ?_⟩
      rw [costWord_terminal next _ _ hall, costWordCons next _ x e es hj]
      omega
    · obtain ⟨j, hj, hle⟩ := ih (next x e) hall
      have hjx : ¬ Good j x := fun h => hj (hg j x e h)
      refine ⟨j, hjx, ?_⟩
      rw [costWordCons next _ x e es hjx]
      omega

/-- The weight `N^k (N-1)^{L-k}` is monotone in `k ≤ L`. Consumer: `momentWordAllLe`. -/
theorem weightMono (N k k' L : Nat) (h1 : k ≤ k') (h2 : k' ≤ L) :
    N ^ k * (N - 1) ^ (L - k) ≤ N ^ k' * (N - 1) ^ (L - k') := by
  obtain ⟨d, rfl⟩ : ∃ d, k' = k + d := ⟨k' - k, by omega⟩
  have hL : L - k = (L - (k + d)) + d := by omega
  rw [hL, Nat.pow_add, Nat.pow_add]
  have hp : (N - 1) ^ d ≤ N ^ d := Nat.pow_le_pow_left (Nat.sub_le N 1) d
  calc N ^ k * ((N - 1) ^ (L - (k + d)) * (N - 1) ^ d)
      = (N ^ k * (N - 1) ^ (L - (k + d))) * (N - 1) ^ d := by rw [Nat.mul_assoc]
    _ ≤ (N ^ k * (N - 1) ^ (L - (k + d))) * N ^ d := Nat.mul_le_mul_left _ hp
    _ = N ^ k * N ^ d * (N - 1) ^ (L - (k + d)) := by
      rw [Nat.mul_assoc, Nat.mul_comm ((N - 1) ^ _) (N ^ d), ← Nat.mul_assoc]

open Classical in
/-- The union bound per word: `z^{max_i τ_i} ≤ Σ_{i not met at x} z^{τ_i}`. Consumer:
`momentOfAllGoals`. -/
theorem momentWordAllLe (next : S → Fin n → S) {K : Nat} (Good : Fin K → S → Prop) (N : Nat)
    (hg : ∀ i x e, Good i x → Good i (next x e)) (x : S) (hx : ¬ (∀ i, Good i x))
    (es : List (Fin n)) :
    momentWord next (fun y => ∀ i, Good i y) N x es ≤
      (List.ofFn fun i => if Good i x then 0 else momentWord next (Good i) N x es).sum := by
  obtain ⟨j, hj, hle⟩ := costWordAllLe next Good hg es x hx
  have hw := weightMono N _ _ es.length hle (costWord_le_length next (Good j) x es)
  have ht := termLeSum (fun i => if Good i x then 0 else momentWord next (Good i) N x es) j
  rw [if_neg hj] at ht
  exact Nat.le_trans hw ht

/-- **Union bound for exponential moments**: persistent goals, each with `E[z^{τ_i}] ≤ A`
from `x` when not met at `x`, have all-goal moment `E[z^{max τ_i}] ≤ K A`.  No independence.
Consumer: `simultaneousOfMoments`. -/
theorem momentOfAllGoals (next : S → Fin n → S) {K : Nat} (Good : Fin K → S → Prop)
    (N A : Nat) (hg : ∀ i x e, Good i x → Good i (next x e)) (x : S)
    (hx : ¬ (∀ i, Good i x))
    (hmom : ∀ i, ¬ Good i x → MomentBound next (Good i) N A x) :
    MomentBound next (fun y => ∀ i, Good i y) N (K * A) x := by
  classical
  intro T
  unfold momentNumerator
  rw [← FixedSpanRenewalPayload.rawWord_sum]
  have h1 := sumLe _ _ (fun w : Fin (n ^ T) =>
    momentWordAllLe next Good N hg x hx (FixedSpanRenewalPayload.rawWord n T w))
  refine Nat.le_trans h1 (Nat.le_trans (Nat.le_of_eq (sumSwap _)) ?_)
  have h2 : ∀ i : Fin K,
      (List.ofFn fun w : Fin (n ^ T) => if Good i x then 0 else
        momentWord next (Good i) N x (FixedSpanRenewalPayload.rawWord n T w)).sum ≤
        A * (n ^ T * (N - 1) ^ T) := by
    intro i
    by_cases hi : Good i x
    · rw [show (fun w : Fin (n ^ T) => if Good i x then 0 else
          momentWord next (Good i) N x (FixedSpanRenewalPayload.rawWord n T w)) =
          fun _ => 0 from funext fun w => if_pos hi, sumConst, Nat.mul_zero]
      exact Nat.zero_le _
    · rw [show (fun w : Fin (n ^ T) => if Good i x then 0 else
          momentWord next (Good i) N x (FixedSpanRenewalPayload.rawWord n T w)) =
          fun w => momentWord next (Good i) N x (FixedSpanRenewalPayload.rawWord n T w) from
          funext fun w => if_neg hi,
        FixedSpanRenewalPayload.rawWord_sum n T (momentWord next (Good i) N x)]
      exact hmom i hi T
  refine Nat.le_trans (sumLe _ _ h2) ?_
  rw [sumConst]
  exact Nat.le_of_eq (Nat.mul_assoc _ _ _).symm

/-! ### Discrete Jensen: the exponential lies above its secant -/

/-- Bernoulli above the secant point: `(N + d) (N-1)^d ≤ N · N^d`, written with `N = M + 1`.
Consumer: `wordTangent`, `momentBlockFactor`. -/
theorem tangentAbove (M d : Nat) : (M + 1 + d) * M ^ d ≤ (M + 1) * (M + 1) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have e1 : (M + 1 + (d + 1)) * M ^ (d + 1) = ((M + 2 + d) * M) * M ^ d := by
      rw [Nat.pow_succ]; grind
    have e2 : (M + 1) * (M + 1 + d) = (M + 2 + d) * M + (d + 1) := by grind
    have e3 : (M + 1) * (M + 1) ^ (d + 1) = (M + 1) * ((M + 1) * (M + 1) ^ d) := by
      rw [Nat.pow_succ]; grind
    rw [e1, e3]
    calc (M + 2 + d) * M * M ^ d ≤ ((M + 1) * (M + 1 + d)) * M ^ d :=
          Nat.mul_le_mul_right _ (by rw [e2]; exact Nat.le_add_right _ _)
      _ = (M + 1) * ((M + 1 + d) * M ^ d) := Nat.mul_assoc _ _ _
      _ ≤ (M + 1) * ((M + 1) * (M + 1) ^ d) := Nat.mul_le_mul_left _ ih

/-- Bernoulli below the secant point: `N · N^m ≤ m N^m + N (N-1)^m`, with `N = M + 1`.
Consumer: `wordTangent`. -/
theorem tangentBelow (M m : Nat) :
    (M + 1) * (M + 1) ^ m ≤ m * (M + 1) ^ m + (M + 1) * M ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hp : M ^ m ≤ (M + 1) ^ m := Nat.pow_le_pow_left (Nat.le_succ M) m
    have e1 : (M + 1) * (M + 1) ^ (m + 1) = (M + 1) * ((M + 1) * (M + 1) ^ m) := by
      rw [Nat.pow_succ]; grind
    have e2 : (M + 1) * (m * (M + 1) ^ m + (M + 1) * M ^ m) =
        m * (M + 1) ^ (m + 1) + (M + 1) * M ^ (m + 1) + (M + 1) * M ^ m := by
      rw [Nat.pow_succ, Nat.pow_succ]; grind
    have e3 : (m + 1) * (M + 1) ^ (m + 1) =
        m * (M + 1) ^ (m + 1) + (M + 1) * (M + 1) ^ m := by
      rw [Nat.pow_succ]; grind
    have hq := Nat.mul_le_mul_left (M + 1) hp
    rw [e1, e3]
    calc (M + 1) * ((M + 1) * (M + 1) ^ m)
        ≤ (M + 1) * (m * (M + 1) ^ m + (M + 1) * M ^ m) := Nat.mul_le_mul_left _ ih
      _ = m * (M + 1) ^ (m + 1) + (M + 1) * M ^ (m + 1) + (M + 1) * M ^ m := e2
      _ ≤ m * (M + 1) ^ (m + 1) + (M + 1) * (M + 1) ^ m + (M + 1) * M ^ (m + 1) := by
        omega

/-- The per-word secant inequality `k + N ≤ t + N z^{k-t}`, cleared of denominators
(`N = M + 1`, `z = N / M`, `k ≤ L`). Consumer: `costOfMoment`. -/
theorem wordTangent (M k L t : Nat) (hk : k ≤ L) :
    (k + (M + 1)) * ((M + 1) ^ t * M ^ L) ≤
      t * ((M + 1) ^ t * M ^ L) + (M + 1) * (M ^ t * ((M + 1) ^ k * M ^ (L - k))) := by
  rcases Nat.le_total t k with htk | hkt
  · obtain ⟨d, rfl⟩ : ∃ d, k = t + d := ⟨k - t, by omega⟩
    have hL : M ^ L = M ^ (L - (t + d)) * M ^ t * M ^ d := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    have h := tangentAbove M d
    rw [hL, Nat.pow_add (M + 1) t d]
    generalize (M + 1) ^ t = A at *
    generalize M ^ t = B at *
    generalize M ^ (L - (t + d)) = Q at *
    generalize M ^ d = u at *
    generalize (M + 1) ^ d = v at *
    have e1 : (t + d + (M + 1)) * (A * (Q * B * u)) =
        t * (A * (Q * B * u)) + ((M + 1 + d) * u) * (A * Q * B) := by grind
    have e2 : t * (A * (Q * B * u)) + (M + 1) * (B * (A * v * Q)) =
        t * (A * (Q * B * u)) + ((M + 1) * v) * (A * Q * B) := by grind
    rw [e1, e2]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _
  · obtain ⟨m, rfl⟩ : ∃ m, t = k + m := ⟨t - k, by omega⟩
    have hL : M ^ L = M ^ k * M ^ (L - k) := by
      rw [← Nat.pow_add]; congr 1; omega
    have h := tangentBelow M m
    rw [hL, Nat.pow_add (M + 1) k m, Nat.pow_add M k m]
    generalize (M + 1) ^ k = a at *
    generalize (M + 1) ^ m = b at *
    generalize M ^ m = c at *
    generalize M ^ k = p at *
    generalize M ^ (L - k) = Q at *
    have e1 : (k + (M + 1)) * (a * b * (p * Q)) =
        k * (a * b * (p * Q)) + ((M + 1) * b) * (a * p * Q) := by grind
    have e2 : (k + m) * (a * b * (p * Q)) + (M + 1) * (p * c * (a * Q)) =
        k * (a * b * (p * Q)) + (m * b + (M + 1) * c) * (a * p * Q) := by grind
    rw [e1, e2]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

/-- **Discrete Jensen**: `E[z^τ] ≤ A` and `A (N-1)^t ≤ N^t` give `E[τ] ≤ t`, i.e. every
truncated first-hit cost is at most `n^T t`.  Consumer: `simultaneousOfMoments`. -/
theorem costOfMoment (next : S → Fin n → S) (P : S → Prop) (N A t : Nat) (hN : 2 ≤ N) (x : S)
    (hm : MomentBound next P N A x) (ht : A * (N - 1) ^ t ≤ N ^ t) :
    ∀ T, costNumerator next P x T ≤ n ^ T * t := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hM : 0 < M := by omega
  simp only [Nat.add_sub_cancel] at ht
  intro T
  have hmT := hm T
  simp only [Nat.add_sub_cancel] at hmT
  have hC : costNumerator next P x T =
      (List.ofFn fun i => costWord next P x (FixedSpanRenewalPayload.rawWord n T i)).sum := by
    unfold costNumerator
    rw [← FixedSpanRenewalPayload.rawWord_sum]
  have hMo : momentNumerator next P (M + 1) x T =
      (List.ofFn fun i =>
        momentWord next P (M + 1) x (FixedSpanRenewalPayload.rawWord n T i)).sum := by
    unfold momentNumerator
    rw [← FixedSpanRenewalPayload.rawWord_sum]
  have hword : ∀ i : Fin (n ^ T),
      (costWord next P x (FixedSpanRenewalPayload.rawWord n T i) + (M + 1)) *
          ((M + 1) ^ t * M ^ T) ≤
        t * ((M + 1) ^ t * M ^ T) + (M + 1) * (M ^ t *
          momentWord next P (M + 1) x (FixedSpanRenewalPayload.rawWord n T i)) := by
    intro i
    have hlen := FixedSpanRenewalPayload.rawWord_length n T i
    have hk := costWord_le_length next P x (FixedSpanRenewalPayload.rawWord n T i)
    rw [hlen] at hk
    unfold momentWord
    rw [hlen, Nat.add_sub_cancel]
    exact wordTangent M _ T t hk
  have hs := sumLe _ _ hword
  generalize hX : (M + 1) ^ t * M ^ T = X at hs
  have eL : (List.ofFn fun i : Fin (n ^ T) =>
      (costWord next P x (FixedSpanRenewalPayload.rawWord n T i) + (M + 1)) * X).sum =
      X * costNumerator next P x T + n ^ T * ((M + 1) * X) := by
    have hf : (fun i : Fin (n ^ T) =>
        (costWord next P x (FixedSpanRenewalPayload.rawWord n T i) + (M + 1)) * X) =
        fun i => X * costWord next P x (FixedSpanRenewalPayload.rawWord n T i) + (M + 1) * X :=
      funext fun i => by rw [Nat.add_mul, Nat.mul_comm _ X]
    rw [hf, sumAdd, sumMulLeft, sumConst, hC]
  have eR : (List.ofFn fun i : Fin (n ^ T) => t * X + (M + 1) * (M ^ t *
      momentWord next P (M + 1) x (FixedSpanRenewalPayload.rawWord n T i))).sum =
      n ^ T * (t * X) + (M + 1) * (M ^ t * momentNumerator next P (M + 1) x T) := by
    rw [sumAdd, sumConst, sumMulLeft, sumMulLeft, hMo]
  rw [eL, eR] at hs
  have hmom : (M + 1) * (M ^ t * momentNumerator next P (M + 1) x T) ≤
      (M + 1) * (n ^ T * X) := by
    apply Nat.mul_le_mul_left
    calc M ^ t * momentNumerator next P (M + 1) x T
        ≤ M ^ t * (A * (n ^ T * M ^ T)) := Nat.mul_le_mul_left _ hmT
      _ = (A * M ^ t) * (n ^ T * M ^ T) := by grind
      _ ≤ (M + 1) ^ t * (n ^ T * M ^ T) := Nat.mul_le_mul_right _ ht
      _ = n ^ T * X := by rw [← hX]; grind
  have e3 : (M + 1) * (n ^ T * X) = n ^ T * ((M + 1) * X) := by grind
  have hcancel : X * costNumerator next P x T ≤ X * (n ^ T * t) := by
    have e4 : n ^ T * (t * X) = X * (n ^ T * t) := by grind
    omega
  have hXpos : 0 < X := by
    rw [← hX]
    exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos hM)
  exact Nat.le_of_mul_le_mul_left hcancel hXpos

/-- **Lemma e-max from per-goal exponential moments**: persistent goals, each with
`E[z^{τ_i}] ≤ A` (`z = N / (N-1)`) from `x` when not met at `x`, are all met at expected cost
at most `t` once `K A (N-1)^t ≤ N^t`.  Planned consumer: the writer-lane and comparison-lane
e-max stages (BANK `widthStructuralClockOfPairs` in place of `simultaneousOfUniform`; the SMALL
pair table), through `simultaneousOfMomentBlocks`. -/
theorem simultaneousOfMoments (next : S → Fin n → S) {K : Nat} (Good : Fin K → S → Prop)
    (N A t : Nat) (hN : 2 ≤ N) (hg : ∀ i x e, Good i x → Good i (next x e)) (x : S)
    (hmom : ∀ i, ¬ Good i x → MomentBound next (Good i) N A x)
    (ht : K * A * (N - 1) ^ t ≤ N ^ t) :
    ∀ T, costNumerator next (fun y => ∀ i, Good i y) x T ≤ n ^ T * t := by
  intro T
  by_cases hx : ∀ i, Good i x
  · rw [costNumerator_terminal next _ x hx]
    exact Nat.zero_le _
  · exact costOfMoment next _ N (K * A) t hN x (momentOfAllGoals next Good N A hg x hx hmom) ht T

end Moment

/-! ### Blocks of `N` letters -/

/-- Second-order Bernoulli: `M^k (2 M^2 + 2 k M + k^2) ≤ 2 M^2 (M+1)^k + k M^k`.
Consumer: `momentBlockFactor`. -/
theorem secondOrder (M k : Nat) :
    M ^ k * (2 * M * M + 2 * k * M + k * k) ≤ 2 * M * M * (M + 1) ^ k + k * M ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkk : k * M ^ k ≤ k * k * M ^ k := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0; simp
      · rw [Nat.mul_assoc]
        exact Nat.le_mul_of_pos_left _ hpos
    have hi := Nat.mul_le_mul_left (M + 1) ih
    have e1 : M ^ (k + 1) * (2 * M * M + 2 * (k + 1) * M + (k + 1) * (k + 1)) +
        (M + 1) * (k * M ^ k) + k * k * M ^ k =
        (M + 1) * (M ^ k * (2 * M * M + 2 * k * M + k * k)) + (k + 1) * M ^ (k + 1) +
          k * M ^ k := by
      rw [Nat.pow_succ]; grind
    have e2 : (M + 1) * (2 * M * M * (M + 1) ^ k + k * M ^ k) =
        2 * M * M * (M + 1) ^ (k + 1) + (M + 1) * (k * M ^ k) := by
      rw [Nat.pow_succ]; grind
    rw [e2] at hi
    omega

/-- A block of `N ≥ 2` letters multiplies `z^t` by at least `5/2`: `5 (N-1)^N ≤ 2 N^N`.
Consumer: `momentBlocks`. -/
theorem momentBlockFactor (N : Nat) (hN : 2 ≤ N) : 5 * (N - 1) ^ N ≤ 2 * N ^ N := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hM : 0 < M := by omega
  simp only [Nat.add_sub_cancel]
  have h := secondOrder M (M + 1)
  have e1 : M ^ (M + 1) * (2 * M * M + 2 * (M + 1) * M + (M + 1) * (M + 1)) =
      M * M * (5 * M ^ (M + 1)) + (M + 1) * M ^ (M + 1) + 3 * M * M ^ (M + 1) := by grind
  have e2 : 2 * M * M * (M + 1) ^ (M + 1) = M * M * (2 * (M + 1) ^ (M + 1)) := by grind
  rw [e1, e2] at h
  have h2 : M * M * (5 * M ^ (M + 1)) ≤ M * M * (2 * (M + 1) ^ (M + 1)) := by omega
  exact Nat.le_of_mul_le_mul_left h2 (Nat.mul_pos hM hM)

/-- `j` blocks: `5^j (N-1)^{N j} ≤ 2^j N^{N j}`. Consumer: `simultaneousOfMomentBlocks`. -/
theorem momentBlocks (N : Nat) (hN : 2 ≤ N) (j : Nat) :
    5 ^ j * (N - 1) ^ (N * j) ≤ 2 ^ j * N ^ (N * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hb := momentBlockFactor N hN
    rw [Nat.mul_succ, Nat.pow_add (N - 1) (N * j) N, Nat.pow_add N (N * j) N, Nat.pow_succ,
      Nat.pow_succ]
    calc 5 ^ j * 5 * ((N - 1) ^ (N * j) * (N - 1) ^ N)
        = (5 ^ j * (N - 1) ^ (N * j)) * (5 * (N - 1) ^ N) := by grind
      _ ≤ (2 ^ j * N ^ (N * j)) * (2 * N ^ N) := Nat.mul_le_mul ih hb
      _ = 2 ^ j * 2 * (N ^ (N * j) * N ^ N) := by grind

/-- **Lemma e-max at a block horizon**: per-goal exponential moments `≤ A` at
`z = N / (N-1)` give all `K` goals at expected cost `N j` once `K A 2^j ≤ 5^j`
(`j ≈ log_{5/2} (K A)`, the paper's `N ln (40 m)` up to the factor `1 / ln (5/2) < 1.1`).
Planned consumer: the writer-lane and comparison-lane e-max stages (BANK and SMALL). -/
theorem simultaneousOfMomentBlocks {S : Type} {n : Nat} (next : S → Fin n → S) {K : Nat}
    (Good : Fin K → S → Prop) (N A j : Nat) (hN : 2 ≤ N)
    (hg : ∀ i x e, Good i x → Good i (next x e)) (x : S)
    (hmom : ∀ i, ¬ Good i x → MomentBound next (Good i) N A x)
    (hj : K * A * 2 ^ j ≤ 5 ^ j) :
    ∀ T, costNumerator next (fun y => ∀ i, Good i y) x T ≤ n ^ T * (N * j) := by
  apply simultaneousOfMoments next Good N A (N * j) hN hg x hmom
  have hb := momentBlocks N hN j
  have h1 : K * A * (N - 1) ^ (N * j) * 2 ^ j ≤ 5 ^ j * (N - 1) ^ (N * j) := by
    rw [Nat.mul_right_comm]
    exact Nat.mul_le_mul_right _ hj
  have h2 : 2 ^ j * (K * A * (N - 1) ^ (N * j)) ≤ 2 ^ j * N ^ (N * j) := by
    rw [Nat.mul_comm (2 ^ j)]
    exact Nat.le_trans h1 hb
  exact Nat.le_of_mul_le_mul_left h2 (Nat.pow_pos (by omega))

end L3.PairMoment

#print axioms L3.PairMoment.simultaneousOfMoments
#print axioms L3.PairMoment.simultaneousOfMomentBlocks
