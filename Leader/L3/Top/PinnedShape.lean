import Leader.L3.Top.SettledWorkFrontClear

/-!
# Q7 (P.8--P.10): the shapes of one window edge when no front stands

With no erasure front before or after the edge, one edge of the abstract window either does
nothing, moves a pending packet into an empty site, settles a pending packet before a settled
site, retires a live carry whose right neighbour is not settled, advances a live carry through
a settled site, or launches a carry from a settled border site.

Consumer: `Leader/L3/Top/PinnedStep.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- **The six shapes of a front-free window edge.**

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem pair_shape (b : Bool) (x y : Cell)
    (hx : x.c = .off ∨ (x.i = .e ∧ x.c = .fresh))
    (hy : y.c = .off ∨ (y.i = .e ∧ y.c = .fresh))
    (hxi : x.i ≠ .x) (hyi : y.i ≠ .x)
    (hf1 : (pair b false x y).1.i ≠ .x) (hf2 : (pair b false x y).2.i ≠ .x) :
    ((pair b false x y).1 = x ∧ (pair b false x y).2 = y) ∨
    (x.i.isP = true ∧ x.c = .off ∧ y = { i := .e, c := .off } ∧
      (pair b false x y).1 = { i := .e, c := .off } ∧
      (pair b false x y).2 = { i := x.i, c := .off }) ∨
    (x.i.isP = true ∧ x.c = .off ∧ y.i.isS = true ∧ y.c = .off ∧
      (pair b false x y).1.i.isS = true ∧ (pair b false x y).1.c = .off ∧
      (pair b false x y).2 = y) ∨
    (x = { i := .e, c := .fresh } ∧ y.i.isS = false ∧
      (pair b false x y).1 = { i := .e, c := .off } ∧ (pair b false x y).2 = y) ∨
    (x = { i := .e, c := .fresh } ∧ y.i.isS = true ∧ y.c = .off ∧
      (pair b false x y).1 = { i := .e, c := .off } ∧
      (pair b false x y).2 = { i := .e, c := .fresh }) ∨
    (b = true ∧ x.i.isS = true ∧ x.c = .off ∧
      (pair b false x y).1 = { i := .e, c := .fresh } ∧ (pair b false x y).2 = y) := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  cases xi <;> cases xc <;> cases yi <;> cases yc <;> cases b <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS] at hx hy hxi hyi hf1 hf2 ⊢

end MarkedCells
end L3

#print axioms L3.MarkedCells.pair_shape
