import Leader.L3.Top.PinnedRenewalSum

/-!
# Q7 (P.13-P.14): the geometric renewal of a trial, generically

A state class `A` (the start of a trial), a target `P`, and three further classes: `M` (the race
cut), `Fv` (favourable successor) and `Uf` (unfavourable successor).  The trial structure is:

* from `A` the class `P ∨ M` is reached within `a` (expected steps, scaled by `n`);
* every race state `M` outside `P` has two distinct letters `e1`, `e2`: the first leads to
  `Fv`, the second to `Uf`, and every other letter leads to `M ∨ P`;
* every favourable state reaches `P` within `f`;
* every unfavourable state reaches `P ∨ A` within `u`.

Then `P` is reached from `A` within `2 a + n + f + u`.  The factor two is the fair race: one
race step is decided by one of the two letters, so the unfavourable branch carries mass at most
one half.  The proof is a potential argument on the exact cost numerators: a bound `B` for the
start of a trial and a bound `B - a` for the race cut, whose one-step inequality is
`n + f + (u + B) ≤ 2 (B - a)`.

Consumer: `Leader/L3/Top/PinnedRenewal.lean`.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false

/-- **Cost of a first-hit composition with a constant payoff.**  A path charged until `P` is
bounded by the charge until `Q` plus the payoff `b` of the entry to `Q`, where the payoff bound
is only needed at the horizons up to the one considered.

Consumer: `renewal_generic`. -/
theorem cost_seq {S : Type} {n : Nat} (next : S → Fin n → S) (P Q : S → Prop) (b : Nat) :
    ∀ (T : Nat), (∀ T', T' ≤ T → ∀ y, Q y → costNumerator next P y T' ≤ n ^ T' * b) →
      ∀ x, costNumerator next P x T ≤ costNumerator next Q x T + n ^ T * b := by
  classical
  intro T
  induction T with
  | zero =>
    intro _ x
    simp only [costNumerator_zero, Nat.zero_add]
    exact Nat.zero_le _
  | succ T ih =>
    intro hafter x
    by_cases hp : P x
    · rw [costNumerator_terminal next P x hp]
      exact Nat.zero_le _
    · by_cases hq : Q x
      · rw [costNumerator_terminal next Q x hq, Nat.zero_add]
        exact hafter (T + 1) (Nat.le_refl _) x hq
      · rw [costNumerator_succ next P x hp, costNumerator_succ next Q x hq]
        have hsum := ofFn_sum_le
          (fun e : Fin n => costNumerator next P (next x e) T)
          (fun e : Fin n => costNumerator next Q (next x e) T + n ^ T * b)
          (fun e => ih (fun T' h => hafter T' (by omega)) (next x e))
        have hsumBound : (List.ofFn (fun e : Fin n => costNumerator next P (next x e) T)).sum ≤
            (List.ofFn (fun e : Fin n => costNumerator next Q (next x e) T)).sum +
              n * (n ^ T * b) := by
          simpa only [ofFn_sum_add, ofFn_sum_const] using hsum
        calc
          n ^ (T + 1) + (List.ofFn (fun e : Fin n => costNumerator next P (next x e) T)).sum ≤
              n ^ (T + 1) + ((List.ofFn (fun e : Fin n =>
                costNumerator next Q (next x e) T)).sum + n * (n ^ T * b)) :=
            Nat.add_le_add_left hsumBound _
          _ = (n ^ (T + 1) + (List.ofFn (fun e : Fin n =>
                costNumerator next Q (next x e) T)).sum) + n ^ (T + 1) * b := by
            rw [Nat.pow_succ]
            ac_rfl

/-- **The race step.**  From a race state with two distinct letters, the cost at horizon `T + 1`
is the step plus the costs of the successors; with the bounds `X1`, `X2` for the two decided
successors and `K` for every other one, `n K` bounds the cost as soon as `n + X1 + X2 ≤ 2 K`.

Consumer: `renewal_generic`. -/
theorem race_step {S : Type} {n : Nat} (next : S → Fin n → S) (P : S → Prop) (y : S)
    (hy : ¬ P y) (e1 e2 : Fin n) (h12 : e1 ≠ e2) (T X1 X2 K : Nat)
    (h1 : costNumerator next P (next y e1) T ≤ n ^ T * X1)
    (h2 : costNumerator next P (next y e2) T ≤ n ^ T * X2)
    (h3 : ∀ e, e ≠ e1 → e ≠ e2 → costNumerator next P (next y e) T ≤ n ^ T * K)
    (hK : n + X1 + X2 ≤ 2 * K) :
    costNumerator next P y (T + 1) ≤ n ^ (T + 1) * K := by
  rw [costNumerator_succ next P y hy T]
  have hs := ofFn_sum_two (fun e => costNumerator next P (next y e) T) e1 e2 h12
    (n ^ T * X1) (n ^ T * X2) (n ^ T * K) h1 h2 h3
  have hm : n ^ T * (n + X1 + X2) ≤ n ^ T * (2 * K) := Nat.mul_le_mul_left _ hK
  rw [Nat.pow_succ]
  have e1' : n ^ T * (n + X1 + X2) = n ^ T * n + n ^ T * X1 + n ^ T * X2 := by
    rw [Nat.mul_add, Nat.mul_add]
  have e2' : n ^ T * (2 * K) = 2 * (n ^ T * K) := by
    rw [Nat.mul_left_comm]
  have e3 : n ^ T * n * K = n * (n ^ T * K) := by
    rw [Nat.mul_comm (n ^ T) n, Nat.mul_assoc]
  rw [e3]
  omega

/-- **The geometric renewal, generically.**

Consumer: `topStopRenewalPhase`. -/
theorem renewal_generic {S : Type} {n : Nat} (next : S → Fin n → S)
    (P A M Fv Uf : S → Prop) (a f u : Nat)
    (hA : ∀ x, A x → ∀ T, costNumerator next (fun y => P y ∨ M y) x T ≤ n ^ T * a)
    (hrace : ∀ y, M y → ¬ P y → ∃ e1 e2 : Fin n, e1 ≠ e2 ∧ (P (next y e1) ∨ Fv (next y e1)) ∧
      (P (next y e2) ∨ Uf (next y e2)) ∧
      ∀ e, e ≠ e1 → e ≠ e2 → P (next y e) ∨ M (next y e))
    (hF : ∀ w, Fv w → ∀ T, costNumerator next P w T ≤ n ^ T * f)
    (hU : ∀ z, Uf z → ∀ T, costNumerator next (fun y => P y ∨ A y) z T ≤ n ^ T * u)
    (B : Nat) (hB : 2 * a + n + f + u ≤ B) :
    ∀ x, A x → ∀ T, costNumerator next P x T ≤ n ^ T * B := by
  have key : ∀ T, ∀ T', T' ≤ T →
      (∀ x, A x → costNumerator next P x T' ≤ n ^ T' * B) ∧
      (∀ y, M y → costNumerator next P y T' ≤ n ^ T' * (B - a)) := by
    intro T
    induction T with
    | zero =>
      intro T' hT'
      have : T' = 0 := by omega
      subst this
      exact ⟨fun x _ => by simp, fun y _ => by simp⟩
    | succ T ih =>
      -- the race cut at horizon `T + 1`
      have hM : ∀ y, M y → costNumerator next P y (T + 1) ≤ n ^ (T + 1) * (B - a) := by
        intro y hy
        by_cases hp : P y
        · rw [costNumerator_terminal next P y hp]; exact Nat.zero_le _
        · obtain ⟨e1, e2, h12, hc1, hc2, hc3⟩ := hrace y hy hp
          refine race_step next P y hp e1 e2 h12 T f (u + B) (B - a) ?_ ?_ ?_ (by omega)
          · rcases hc1 with h | h
            · rw [costNumerator_terminal next P _ h]; exact Nat.zero_le _
            · exact hF _ h T
          · rcases hc2 with h | h
            · rw [costNumerator_terminal next P _ h]; exact Nat.zero_le _
            · have hseq := cost_seq next P (fun y => P y ∨ A y) B T (by
                intro T' hT' w hw
                rcases hw with hw | hw
                · rw [costNumerator_terminal next P _ hw]; exact Nat.zero_le _
                · exact ((ih T' (by omega)).1 w hw))
                (next y e2)
              have hu := hU _ h T
              calc costNumerator next P (next y e2) T
                  ≤ costNumerator next (fun y => P y ∨ A y) (next y e2) T + n ^ T * B := hseq
                _ ≤ n ^ T * u + n ^ T * B := Nat.add_le_add_right hu _
                _ = n ^ T * (u + B) := (Nat.mul_add _ _ _).symm
          · intro e he1 he2
            rcases hc3 e he1 he2 with h | h
            · rw [costNumerator_terminal next P _ h]; exact Nat.zero_le _
            · exact (ih T (Nat.le_refl _)).2 _ h
      have hAx : ∀ x, A x → costNumerator next P x (T + 1) ≤ n ^ (T + 1) * B := by
        intro x hx
        have hseq := cost_seq next P (fun y => P y ∨ M y) (B - a) (T + 1) (by
          intro T' hT' w hw
          rcases hw with hw | hw
          · rw [costNumerator_terminal next P _ hw]; exact Nat.zero_le _
          · by_cases hle : T' ≤ T
            · exact (ih T' hle).2 w hw
            · have : T' = T + 1 := by omega
              subst this
              exact hM w hw) x
        calc costNumerator next P x (T + 1)
            ≤ costNumerator next (fun y => P y ∨ M y) x (T + 1) + n ^ (T + 1) * (B - a) := hseq
          _ ≤ n ^ (T + 1) * a + n ^ (T + 1) * (B - a) := Nat.add_le_add_right (hA x hx _) _
          _ = n ^ (T + 1) * (a + (B - a)) := (Nat.mul_add _ _ _).symm
          _ ≤ n ^ (T + 1) * B := Nat.mul_le_mul_left _ (by omega)
      intro T' hT'
      by_cases hle : T' ≤ T
      · exact ih T' hle
      · have : T' = T + 1 := by omega
        subst this
        exact ⟨hAx, hM⟩
  intro x hx T
  exact ((key T T (Nat.le_refl _)).1 x hx)

end L3

#print axioms L3.cost_seq
#print axioms L3.race_step
#print axioms L3.renewal_generic
