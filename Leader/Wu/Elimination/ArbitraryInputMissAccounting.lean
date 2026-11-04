import Leader.Wu.Elimination.SafeEliminationWordCost

/-!
# Exact finite-word accounting for successive physical entry bounds

These algebraic lemmas keep one transition and every raw scheduler suffix.
The actual component supplies all predicate closures and mass estimates in
the consumer; no runtime phase or independence premise is introduced.
-/

namespace K2ArbitraryElimination.FiniteAccounting

open LDSinkBoundedKernel FiniteUniformStoppingTree LeaderCountDyadicTail

set_option autoImplicit false
set_option Elab.async false

variable {S : Type} {n : Nat}

/-- Literal indicator that the given current-state predicate has not been met. -/
noncomputable def miss (P : S → Prop) (x : S) : Nat := by
  classical
  exact if P x then 0 else 1

theorem miss_le_one (P : S → Prop) (x : S) : miss P x ≤ 1 := by
  unfold miss
  split <;> decide

theorem miss_mono (P Q : S → Prop) (h : ∀ x, P x → Q x) (x : S) :
    miss Q x ≤ miss P x := by
  classical
  by_cases hp : P x
  · simp [miss, hp, h x hp]
  · simp only [miss, if_neg hp]
    split <;> decide

/-- Pointwise inequalities sum over the identical original scheduler tree. -/
theorem wordSum_mono (next : S → Fin n → S) (w v : S → Nat)
    (h : ∀ x, w x ≤ v x) (x : S) (T : Nat) :
    wordSum next w x T ≤ wordSum next v x T :=
  wordSum_mono_on next (fun _ => True) (fun _ _ _ => True.intro)
    w v (fun x _ => h x) T x True.intro

theorem miss_mass_le (next : S → Fin n → S) (P : S → Prop) (x : S) (T : Nat) :
    wordSum next (miss P) x T ≤ n ^ T := by
  have h := wordSum_mono next (miss P) (fun _ => 1) (miss_le_one P) x T
  simpa only [wordSum_const, Nat.mul_one] using h

/-- Once a closed physical target is reached, its full suffix has zero miss weight. -/
theorem miss_zero (next : S → Fin n → S) (P : S → Prop)
    (hc : ∀ x e, P x → P (next x e)) (x : S) (hx : P x) (T : Nat) :
    wordSum next (miss P) x T = 0 := by
  induction T generalizing x with
  | zero => simp [miss, hx]
  | succ T ih =>
    rw [wordSum_succ, ofFn_sum_eq _ (fun _ => 0) (fun e => ih _ (hc x e hx)), ofFn_sum_const]
    exact Nat.mul_zero _

/-- Compose two finite-time estimates by conditioning on the actual prefix
endpoint. The bound counts every suffix and needs no independent times. -/
theorem compose_miss (next : S → Fin n → S) (P Q : S → Prop)
    (A B q a b : Nat) (x : S)
    (hA : q * wordSum next (miss P) x A ≤ a * n ^ A)
    (hB : ∀ y, P y → q * wordSum next (miss Q) y B ≤ b * n ^ B) :
    q * wordSum next (miss Q) x (A + B) ≤ (a + b) * n ^ (A + B) := by
  classical
  have hp : ∀ y, q * wordSum next (miss Q) y B ≤
      (q * n ^ B) * miss P y + b * n ^ B := by
    intro y
    by_cases hy : P y
    · simpa [miss, hy] using hB y hy
    · have h := Nat.mul_le_mul_left q (miss_mass_le next Q y B)
      simp only [miss, if_neg hy, Nat.mul_one]
      exact Nat.le_trans h (Nat.le_add_right _ _)
  rw [wordSum_horizon_add, ← wordSum_mul]
  calc
    wordSum next (fun y => q * wordSum next (miss Q) y B) x A ≤
        wordSum next (fun y => (q * n ^ B) * miss P y + b * n ^ B) x A :=
      wordSum_mono next _ _ hp x A
    _ = n ^ B * (q * wordSum next (miss P) x A) + n ^ A * (b * n ^ B) := by
      rw [wordSum_add, wordSum_mul, wordSum_const]
      ac_rfl
    _ ≤ n ^ B * (a * n ^ A) + n ^ A * (b * n ^ B) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ hA) _
    _ = _ := by rw [Nat.add_mul, Nat.pow_add]; ac_rfl

/-- Uniform actual endpoint contraction can restart on the same raw process. -/
theorem repeat_miss (next : S → Fin n → S) (P D : S → Prop)
    (hc : ∀ x e, D x → D (next x e))
    (hp : ∀ x e, P x → P (next x e)) (H q : Nat)
    (hb : ∀ x, D x → q * wordSum next (miss P) x H ≤ n ^ H)
    (x : S) (hx : D x) (j : Nat) :
    q ^ j * wordSum next (miss P) x (j * H) ≤ n ^ (j * H) := by
  classical
  have hblock : ∀ y, D y → q * wordSum next (miss P) y H ≤ 1 * n ^ H * miss P y := by
    intro y hy
    by_cases h : P y
    · rw [miss_zero next P hp y h H]
      simp
    · simpa only [miss, if_neg h, Nat.one_mul, Nat.mul_one] using hb y hy
  have h := iterate_contraction next D hc (miss P) H q 1 hblock j x hx
  have hm := Nat.mul_le_mul_left ((1 * n ^ H) ^ j) (miss_le_one P x)
  have he : (1 * n ^ H) ^ j * 1 = n ^ (j * H) := by
    rw [Nat.one_mul, Nat.mul_one, ← Nat.pow_mul, Nat.mul_comm H j]
  rw [he] at hm
  exact Nat.le_trans h hm

end K2ArbitraryElimination.FiniteAccounting
