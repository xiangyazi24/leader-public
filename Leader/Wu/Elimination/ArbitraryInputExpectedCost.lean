import Leader.Wu.Elimination.ArbitraryInputMissAccounting

/-!
# All finite-prefix costs from a uniform physical half-success block

Costs count every raw interaction until the first target prefix, including
unfinished prefixes. The proof splits deterministic scheduler words and
retains their actual endpoints; it does not assume independent phase times.
-/

namespace K2ArbitraryElimination.FiniteAccounting

open LDSinkBoundedKernel FiniteUniformStoppingTree LeaderCountDyadicTail

set_option autoImplicit false
set_option Elab.async false

variable {S : Type} {n : Nat}

/-- The repository's literal first-hit cost recursion for the chosen actual row. -/
noncomputable def costWord (next : S → Fin n → S) (P : S → Prop) (x : S)
    (es : List (Fin n)) : Nat := by
  classical
  exact K2FiniteSafeEliminationExpected.rawCost next P x es

/-- Exact sum over all n^T original finite scheduler words. -/
noncomputable def costNumerator (next : S → Fin n → S) (P : S → Prop) (x : S)
    (T : Nat) : Nat := FixedSpanRenewalPayload.wordSum n T (costWord next P x)

theorem costWord_le_length (next : S → Fin n → S) (P : S → Prop) (x : S)
    (es : List (Fin n)) : costWord next P x es ≤ es.length := by
  classical
  induction es generalizing x with
  | nil => exact Nat.le_refl _
  | cons e es ih =>
    simp only [costWord, K2FiniteSafeEliminationExpected.rawCost, List.length_cons]
    split
    · exact Nat.zero_le _
    · simpa only [costWord, Nat.add_comm] using Nat.add_le_add_left (ih (next x e)) 1

theorem costWord_terminal (next : S → Fin n → S) (P : S → Prop) (x : S)
    (hx : P x) (es : List (Fin n)) : costWord next P x es = 0 := by
  classical
  cases es <;> simp [costWord, K2FiniteSafeEliminationExpected.rawCost, hx]

@[simp] theorem costNumerator_zero (next : S → Fin n → S) (P : S → Prop) (x : S) :
    costNumerator next P x 0 = 0 := rfl

theorem costNumerator_terminal (next : S → Fin n → S) (P : S → Prop) (x : S)
    (hx : P x) (T : Nat) : costNumerator next P x T = 0 := by
  unfold costNumerator
  rw [← FixedSpanRenewalPayload.rawWord_sum]
  rw [ofFn_sum_eq _ (fun _ => 0) (fun _ => costWord_terminal next P x hx _), ofFn_sum_const]
  exact Nat.mul_zero _

theorem costNumerator_le_horizon (next : S → Fin n → S) (P : S → Prop) (x : S)
    (T : Nat) : costNumerator next P x T ≤ n ^ T * T := by
  unfold costNumerator
  rw [← FixedSpanRenewalPayload.rawWord_sum]
  have h := ofFn_sum_le
    (fun i : Fin (n ^ T) => costWord next P x (FixedSpanRenewalPayload.rawWord n T i))
    (fun _ => T) (fun i => by
      have h := costWord_le_length next P x (FixedSpanRenewalPayload.rawWord n T i)
      rwa [FixedSpanRenewalPayload.rawWord_length] at h)
  simpa only [ofFn_sum_const] using h

private theorem wordSum_one_add (T : Nat) (f : List (Fin n) → Nat) :
    FixedSpanRenewalPayload.wordSum n T (fun es => 1 + f es) =
      n ^ T + FixedSpanRenewalPayload.wordSum n T f := by
  rw [← FixedSpanRenewalPayload.rawWord_sum]
  change (List.ofFn (fun i : Fin (n ^ T) => 1 + f (FixedSpanRenewalPayload.rawWord n T i))).sum = _
  rw [ofFn_sum_add, ofFn_sum_const, Nat.mul_one, FixedSpanRenewalPayload.rawWord_sum]

/-- Exact first-symbol cost recurrence at an unfinished physical endpoint. -/
theorem costNumerator_succ (next : S → Fin n → S) (P : S → Prop) (x : S)
    (hx : ¬ P x) (T : Nat) :
    costNumerator next P x (T + 1) = n ^ (T + 1) +
      (List.ofFn (fun e => costNumerator next P (next x e) T)).sum := by
  classical
  unfold costNumerator
  rw [FixedSpanRenewalPayload.wordSum_succ]
  simp only [costWord, K2FiniteSafeEliminationExpected.rawCost, if_neg hx]
  rw [ofFn_sum_eq _ _ (fun e => wordSum_one_add T
    (fun es => K2FiniteSafeEliminationExpected.rawCost next P (next x e) es)),
    ofFn_sum_add, ofFn_sum_const, Nat.pow_succ]
  ac_rfl

private theorem cost_suffix_zero (next : S → Fin n → S) (P : S → Prop)
    (hc : ∀ x e, P x → P (next x e)) (x : S) (hx : P x) (A U : Nat) :
    wordSum next (fun y => costNumerator next P y U) x A = 0 := by
  induction A generalizing x with
  | zero => exact costNumerator_terminal next P x hx U
  | succ A ih =>
    rw [wordSum_succ, ofFn_sum_eq _ (fun _ => 0) (fun e => ih _ (hc x e hx)), ofFn_sum_const]
    exact Nat.mul_zero _

/-- The deterministic prefix/suffix split charges both completed and
unfinished words. All suffixes run from the exact physical prefix state. -/
theorem costNumerator_split (next : S → Fin n → S) (P : S → Prop)
    (hc : ∀ x e, P x → P (next x e)) (x : S) (A U : Nat) :
    costNumerator next P x (A + U) = n ^ U * costNumerator next P x A +
      wordSum next (fun y => costNumerator next P y U) x A := by
  classical
  induction A generalizing x with
  | zero => simp only [Nat.zero_add, costNumerator_zero, Nat.mul_zero, wordSum_zero]
  | succ A ih =>
    by_cases hx : P x
    · rw [costNumerator_terminal next P x hx, costNumerator_terminal next P x hx,
        cost_suffix_zero next P hc x hx]
      simp
    · rw [Nat.succ_add, costNumerator_succ next P x hx,
        costNumerator_succ next P x hx, wordSum_succ]
      rw [ofFn_sum_eq _ _ (fun e => ih (next x e)), ofFn_sum_add, ofFn_sum_mul_left]
      have he : n ^ (A + U + 1) = n ^ U * n ^ (A + 1) := by
        rw [show A + U + 1 = U + (A + 1) by omega, Nat.pow_add]
      rw [he, Nat.mul_add]
      ac_rfl

/-- Uniform half-success in B raw steps yields expected first-target cost
at most 2B at every finite horizon. Only actual closed-target row bounds
are premises; the physical consumer produces those bounds independently. -/
theorem cost_le_two_blocks (next : S → Fin n → S) (P : S → Prop)
    (hc : ∀ x e, P x → P (next x e)) (B : Nat) (hB : 0 < B)
    (hb : ∀ x, 2 * wordSum next (miss P) x B ≤ n ^ B) :
    ∀ T x, costNumerator next P x T ≤ n ^ T * (2 * B) := by
  classical
  intro T
  induction T using Nat.strongRecOn with
  | ind T ih =>
    intro x
    by_cases hsmall : T ≤ B
    · exact Nat.le_trans (costNumerator_le_horizon next P x T)
        (Nat.mul_le_mul_left _ (by omega))
    · let U := T - B
      have hU : U < T := by dsimp [U]; omega
      have hT : T = B + U := by dsimp [U]; omega
      have hpoint : ∀ y, costNumerator next P y U ≤ (n ^ U * (2 * B)) * miss P y := by
        intro y
        by_cases hy : P y
        · rw [costNumerator_terminal next P y hy]
          exact Nat.zero_le _
        · simpa only [miss, if_neg hy, Nat.mul_one] using ih U hU y
      rw [hT, costNumerator_split next P hc]
      have htail := wordSum_mono next _ _ hpoint x B
      rw [wordSum_mul] at htail
      have hhalf := Nat.mul_le_mul_left (n ^ U * B) (hb x)
      calc
        n ^ U * costNumerator next P x B +
            wordSum next (fun y => costNumerator next P y U) x B ≤
            n ^ U * (n ^ B * B) + (n ^ U * (2 * B)) * wordSum next (miss P) x B :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (costNumerator_le_horizon next P x B)) htail
        _ = n ^ U * (n ^ B * B) + (n ^ U * B) * (2 * wordSum next (miss P) x B) := by ac_rfl
        _ ≤ n ^ U * (n ^ B * B) + (n ^ U * B) * n ^ B := Nat.add_le_add_left hhalf _
        _ = _ := by simp only [Nat.pow_add, Nat.mul_add, Nat.two_mul]; ac_rfl

end K2ArbitraryElimination.FiniteAccounting

#print axioms K2ArbitraryElimination.FiniteAccounting.costNumerator_split
#print axioms K2ArbitraryElimination.FiniteAccounting.cost_le_two_blocks
