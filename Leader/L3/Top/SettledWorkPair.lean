import Leader.L3.Top.SettledCoverStep

/-!
# Q7 (P.6): the settled pattern of one window edge

With empty carry hosts, one edge of the abstract window changes the settled/unsettled status
of its two registers in one of a few ways only.  This module is pure (no machine).

Consumer: `Leader/L3/Top/SettledWorkStep.lean` (the charge does not rise along an edge).
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The settled pattern of one edge (carry hosts empty): nothing changes; or the right
register is consumed by a carry or a front; or the left tail turns into a front; or the border
operand launches a carry; or a pending packet settles.

Consumer: `edge_charge`. -/
theorem pair_pat (b t : Bool) (x y : Cell) (hx : x.c ≠ .off → x.i = .e)
    (hy : y.c ≠ .off → y.i = .e) (hbt : b = true → t = false) :
    ((pair b t x y).1.i.isS = x.i.isS ∧ (pair b t x y).2.i.isS = y.i.isS ∧
      ¬ (x.i = .st ∧ x.c = .off ∧ b = false) ∧
      ¬ (x.i = .x ∧ x.c = .off ∧ y.i.isS = true ∧ y.c = .off ∧ t = false)) ∨
    (t = false ∧ x.i.isS = false ∧ (pair b t x y).1.i.isS = false ∧ y.i.isS = true ∧
      (pair b t x y).2.i.isS = false ∧ y.c = .off ∧ x.c ≠ .off) ∨
    (t = false ∧ x.i.isS = false ∧ (pair b t x y).1.i.isS = false ∧ y.i.isS = true ∧
      (pair b t x y).2.i.isS = false ∧ y.c = .off ∧ x.c = .off ∧ x.i = .x) ∨
    (x.i = .st ∧ x.c = .off ∧ b = false ∧ (pair b t x y).1.i.isS = false ∧
      (pair b t x y).2.i.isS = y.i.isS) ∨
    (b = true ∧ t = false ∧ x.c = .off ∧ x.i.isS = true ∧ (pair b t x y).1.i.isS = false ∧
      (pair b t x y).2.i.isS = y.i.isS) ∨
    (x.i.isP = true ∧ (pair b t x y).1.i.isS = true ∧ (pair b t x y).2.i.isS = y.i.isS ∧
      (t = true ∨ (y.i.isS = true ∧ y.c = .off))) := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  cases xi <;> cases xc <;> cases yi <;> cases yc <;> cases b <;> cases t <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS] at hx hy hbt ⊢

end MarkedCells
end L3

#print axioms L3.MarkedCells.pair_pat
