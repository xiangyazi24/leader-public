import Leader.L3.Top.MarkedDebt

/-!
# Q7 (P.11): the nominated-edge cost bound with closure off the target only

`topMarkedCostOfRows` needs the invariant class closed under every edge, even at target
states.  The clearing regime stops being invariant once the target is reached, so here the
closure is asked only at states off the target.

Consumer: `Leader/L3/TopFinalMobilePhase.lean`.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Strengthening the target on a closed class costs nothing.

Consumer: `topFinalCostOfRows`. -/
theorem topFinalCostTargetOnClosed {m : Nat} {S : Type}
    (next : S → Fin m → S) (I P Q : S → Prop)
    (hstep : ∀ x, I x → ¬ P x → ∀ e, I (next x e))
    (hstop : ∀ x, I x → Q x → P x) :
    ∀ T x, I x →
      costNumerator next P x T ≤ costNumerator next Q x T := by
  classical
  intro T
  induction T with
  | zero =>
      intro x hx
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      intro x hx
      by_cases hp : P x
      · rw [costNumerator_terminal next P x hp (T + 1)]
        exact Nat.zero_le _
      · have hq : ¬ Q x := by
          intro h
          exact hp (hstop x hx h)
        rw [costNumerator_succ next P x hp T,
          costNumerator_succ next Q x hq T]
        exact Nat.add_le_add_left
          (ofFn_sum_le
            (fun e : Fin m => costNumerator next P (next x e) T)
            (fun e : Fin m => costNumerator next Q (next x e) T)
            (fun e => ih (next x e) (hstep x hx hp e))) _

/-- **Nominated-edge potential on a closed class.**  On a class `I` closed
under every edge, a potential that never rises off the target `P` (a
successor is in `P` or has potential at most the present one), strictly
drops at one nominated edge (successor in `P` or potential smaller by one),
and is positive off `P`, bounds the first-hit cost by `n^T * (n * Φ x)`.

Consumer: `Leader/L3/TopFinalMobilePhase.lean`. -/
theorem topFinalCostOfRows {S : Type} {n : Nat}
    (next : S → Fin n → S) (I P : S → Prop) (Φ : S → Nat)
    (chosen : S → Fin n)
    (hclosed : ∀ x, I x → ¬ P x → ∀ e, I (next x e))
    (hpos : ∀ x, I x → ¬ P x → 0 < Φ x)
    (hnon : ∀ x, I x → ¬ P x → ∀ e, P (next x e) ∨ Φ (next x e) ≤ Φ x)
    (hdrop : ∀ x, I x → ¬ P x →
      P (next x (chosen x)) ∨ Φ (next x (chosen x)) + 1 ≤ Φ x) :
    ∀ x, I x → ∀ T, costNumerator next P x T ≤ n ^ T * (n * Φ x) := by
  classical
  let P' : S → Prop := fun x => P x ∨ ¬ I x
  let Φ' : S → Nat := fun x => if P' x then 0 else Φ x
  have hdrop' : ∀ x, ¬ P' x → Φ' (next x (chosen x)) + 1 ≤ Φ' x := by
    intro x hx
    have hxI : I x := by
      by_cases h : I x
      · exact h
      · exact absurd (Or.inr h) hx
    have hxP : ¬ P x := fun h => hx (Or.inl h)
    have hnI : I (next x (chosen x)) := hclosed x hxI hxP _
    have hΦx : Φ' x = Φ x := by simp [Φ', hx]
    rw [hΦx]
    rcases hdrop x hxI hxP with h | h
    · have : P' (next x (chosen x)) := Or.inl h
      simp only [Φ', this, if_true]
      exact hpos x hxI hxP
    · by_cases hP : P' (next x (chosen x))
      · simp only [Φ', hP, if_true]
        exact hpos x hxI hxP
      · simp only [Φ', hP, if_false]
        exact h
  have hnon' : ∀ x, ¬ P' x → ∀ e, Φ' (next x e) ≤ Φ' x := by
    intro x hx e
    have hxI : I x := by
      by_cases h : I x
      · exact h
      · exact absurd (Or.inr h) hx
    have hxP : ¬ P x := fun h => hx (Or.inl h)
    have hΦx : Φ' x = Φ x := by simp [Φ', hx]
    rw [hΦx]
    rcases hnon x hxI hxP e with h | h
    · have : P' (next x e) := Or.inl h
      simp only [Φ', this, if_true]
      exact Nat.zero_le _
    · by_cases hP : P' (next x e)
      · simp only [Φ', hP, if_true]
        exact Nat.zero_le _
      · simp only [Φ', hP, if_false]
        exact h
  have hmain := Prob.costNumerator_le_of_nominated_edge next P' Φ' chosen
    hdrop' hnon'
  intro x hx T
  have h1 := topFinalCostTargetOnClosed next I P P' hclosed
    (fun y hy hyP => by
      rcases hyP with h | h
      · exact h
      · exact absurd hy h) T x hx
  have h2 := hmain x T
  have hle : Φ' x ≤ Φ x := by
    by_cases h : P' x
    · simp only [Φ', h, if_true]
      exact Nat.zero_le _
    · simp only [Φ', h, if_false]
      exact Nat.le_refl _
  exact Nat.le_trans h1 (Nat.le_trans h2
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hle)))


end L3

#print axioms L3.topFinalCostOfRows
