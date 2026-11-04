import Leader.L3.Top.SettledWorkLift

/-!
# Q7 (P.6--P.10): first-hit costs of an absorbing chain and of a larger target

* Making the target absorbing does not change the first-hit cost.
* Under a closed invariant, a larger target has a smaller first-hit cost.

Consumer: `Leader/L3/TopSettledPotentialStage.lean`.
-/

namespace L3
namespace MarkedCells

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false

open Classical in
/-- The chain that stays at a target state.

Consumer: `costNumerator_absorb`. -/
noncomputable def absorb {S : Type} {n : Nat} (next : S → Fin n → S) (P : S → Prop) :
    S → Fin n → S :=
  fun x e => if P x then x else next x e

/-- The first-hit cost along a word does not see the absorbing step.

Consumer: `costNumerator_absorb`. -/
theorem costWord_absorb {S : Type} {n : Nat} (next : S → Fin n → S) (P : S → Prop) :
    ∀ (es : List (Fin n)) (x : S), costWord (absorb next P) P x es = costWord next P x es := by
  intro es
  induction es with
  | nil => intro x; rfl
  | cons e es ih =>
      intro x
      unfold costWord at *
      simp only [K2FiniteSafeEliminationExpected.rawCost]
      by_cases h : P x
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
        have := ih (next x e)
        have e1 : absorb next P x e = next x e := by unfold absorb; rw [if_neg h]
        rw [e1, this]

/-- **The absorbing chain has the same cost numerator.**

Consumer: `Leader/L3/TopSettledPotentialStage.lean`. -/
theorem costNumerator_absorb {S : Type} {n : Nat} (next : S → Fin n → S) (P : S → Prop)
    (x : S) (T : Nat) : costNumerator (absorb next P) P x T = costNumerator next P x T := by
  unfold costNumerator
  have : costWord (absorb next P) P x = costWord next P x := by
    funext es; exact costWord_absorb next P es x
  rw [this]

/-- A larger target stops no later, under a closed invariant.

Consumer: `costNumerator_mono_target`. -/
theorem costWord_mono_target {S : Type} {n : Nat} (next : S → Fin n → S) (P Q J : S → Prop)
    (hJ : ∀ x, J x → ∀ e, J (next x e)) (hPQ : ∀ x, J x → P x → Q x) :
    ∀ (es : List (Fin n)) (x : S), J x → costWord next Q x es ≤ costWord next P x es := by
  intro es
  induction es with
  | nil => intro x _; exact Nat.le_refl _
  | cons e es ih =>
      intro x hx
      unfold costWord at *
      simp only [K2FiniteSafeEliminationExpected.rawCost]
      by_cases hq : Q x
      · rw [if_pos hq]; exact Nat.zero_le _
      · have hp : ¬ P x := fun hp => hq (hPQ x hx hp)
        rw [if_neg hq, if_neg hp]
        exact Nat.add_le_add_left (ih (next x e) (hJ x hx e)) 1

/-- A sum over words is monotone.

Consumer: `costNumerator_mono_target`. -/
theorem wordSum_mono' (n T : Nat) (f g : List (Fin n) → Nat) (h : ∀ u, f u ≤ g u) :
    FixedSpanRenewalPayload.wordSum n T f ≤ FixedSpanRenewalPayload.wordSum n T g := by
  unfold FixedSpanRenewalPayload.wordSum
  generalize allSchedules n T = l
  induction l with
  | nil => exact Nat.le_refl _
  | cons u l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h _) ih

/-- **A larger target under a closed invariant has the smaller cost numerator.**

Consumer: `Leader/L3/TopSettledPotentialStage.lean`. -/
theorem costNumerator_mono_target {S : Type} {n : Nat} (next : S → Fin n → S)
    (P Q J : S → Prop) (hJ : ∀ x, J x → ∀ e, J (next x e)) (hPQ : ∀ x, J x → P x → Q x)
    (x : S) (hx : J x) (T : Nat) :
    costNumerator next Q x T ≤ costNumerator next P x T := by
  unfold costNumerator
  exact wordSum_mono' n T _ _ (fun u => costWord_mono_target next P Q J hJ hPQ u x hx)

end MarkedCells
end L3

#print axioms L3.MarkedCells.costNumerator_absorb
#print axioms L3.MarkedCells.costNumerator_mono_target
