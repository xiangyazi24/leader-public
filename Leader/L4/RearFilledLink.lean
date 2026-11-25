import Leader.L4.RearGhostBudget

/-! # The filled-advance folds in the rear clock and stock ledgers -/

namespace L4.RearTrace

/-- The chronological clock list and the physical ghost-block stock
projection count exactly the same filled departures. -/
theorem clockEvents_filled_eq_globalFilled {p c n : Nat}
    (i : Fin n) (s : Observer p c n) (w : List (Fin n)) :
    ((clockEvents i s w).map eventFilled).sum = globalFilled i s w := by
  induction w generalizing s with
  | nil => rfl
  | cons e w ih =>
    change eventFilled (clockEvent i s e) +
      ((clockEvents i (rearAdvance i s e) w).map eventFilled).sum =
        eventFilled (clockEvent i s e) + globalFilled i (rearAdvance i s e) w
    rw [ih]

/-- Concrete refill budget stated with the stock ledger's filled count. -/
theorem concrete_refill_bound_global {p c n : Nat} (hn : 4 ≤ n)
    (i : Fin n) (s : Observer p c n) (w : List (Fin n))
    (hm : MCOV s.tag.config) :
    2*ghostAdvances i s w ≤ (rearFold i s w).rearHits + globalFilled i s w + 1 := by
  simpa only [clockEvents_filled_eq_globalFilled] using concrete_refill_bound hn i s w hm

end L4.RearTrace

#print axioms L4.RearTrace.clockEvents_filled_eq_globalFilled
#print axioms L4.RearTrace.concrete_refill_bound_global
