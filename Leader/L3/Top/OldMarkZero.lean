import Leader.L3.Top.OldMarkSelect
import Leader.L3.Top.MarkedInv

/-!
# Q7: marked rank zero is the repaired coloured window

Consumer: `Leader/L3/Top/OldMarkStep.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- At marked rank zero no register is marked, and the barrier and the carry gap hold.

Consumer: `rank_old_zero_coloured`. -/
theorem rank_zero_old (r : Nat) (cells : Nat → Cell) (o : Nat → Bool) (hinv : Inv r cells)
    (h0 : rank r (markCells cells o) = 0) :
    (∀ j, j < r → o j = false) ∧ Barrier r cells ∧ Gap r cells := by
  have hmk : ∀ j, j < r → o j = false := by
    intro j hj
    have hz := scan_zero_wt r (markCells cells o) r 0 false false h0 j hj
    simp only [Nat.zero_add] at hz
    have hf := (wt_zero_facts r j hj _ _ _ hz).2
    cases hoj : o j
    · rfl
    · exfalso
      apply hf
      simp [markCells, mk, hoj]
  have hr : rank r cells = 0 := by
    have : rank r cells = rank r (markCells cells o) := by
      unfold rank
      exact (scan_congr r (markCells cells o) cells r 0 false false
        (fun i _ hi => by simp [markCells, mk, hmk i (by omega)])).1
    omega
  exact ⟨hmk, rank_zero_barrier r cells hr, rank_zero_gap r cells hinv hr⟩

end MarkedCells
end L3

#print axioms L3.MarkedCells.rank_zero_old
