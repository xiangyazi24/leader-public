import Leader.L3.Top.MarkedDebt

/-!
# Q7 (P.6--P.10): a history-dependent potential through a product chain

The doomed colouring of a settled run depends on the path from the cut, not on the
state alone.  The generic cost bound `topMarkedCostOfRows` is stated for a state type; we apply
it to the product of the state with the colouring, and transfer the first-hit cost back to the
state chain, because the first component of the product chain is the original chain.

Consumer: `Leader/L3/TopSettledWorkPhase.lean` (not yet written).
-/

namespace L3
namespace MarkedCells

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false

/-- The first-hit cost along a factor map of chains is the cost of the image.

Consumer: `costNumerator_lift`. -/
theorem costWord_lift {S S' : Type} {n : Nat} (next : S → Fin n → S) (P : S → Prop)
    (next' : S' → Fin n → S') (P' : S' → Prop) (π : S' → S)
    (hnext : ∀ x e, π (next' x e) = next (π x) e) (hP : ∀ x, P' x ↔ P (π x)) :
    ∀ (es : List (Fin n)) (x : S'), costWord next' P' x es = costWord next P (π x) es := by
  intro es
  induction es with
  | nil => intro x; rfl
  | cons e es ih =>
      intro x
      unfold costWord at *
      simp only [K2FiniteSafeEliminationExpected.rawCost]
      by_cases h : P' x
      · rw [if_pos h, if_pos ((hP x).1 h)]
      · rw [if_neg h, if_neg (fun h' => h ((hP x).2 h'))]
        have := ih (next' x e)
        rw [hnext] at this
        rw [this]

/-- **The cost numerator is the same on the product chain and on the base chain.**

Consumer: `Leader/L3/TopSettledWorkPhase.lean` (not yet written). -/
theorem costNumerator_lift {S S' : Type} {n : Nat} (next : S → Fin n → S) (P : S → Prop)
    (next' : S' → Fin n → S') (P' : S' → Prop) (π : S' → S)
    (hnext : ∀ x e, π (next' x e) = next (π x) e) (hP : ∀ x, P' x ↔ P (π x))
    (x : S') (T : Nat) :
    costNumerator next' P' x T = costNumerator next P (π x) T := by
  unfold costNumerator
  have : costWord next' P' x = costWord next P (π x) := by
    funext es; exact costWord_lift next P next' P' π hnext hP es x
  rw [this]

end MarkedCells
end L3

#print axioms L3.MarkedCells.costNumerator_lift
