import Leader.L3.Top.SettledPotentialEdge

/-!
# Q7 (P.8--P.10): the values of one window edge in the five nominated shapes

Consumer: `Leader/L3/Top/SettledPotentialNominate.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- A live carry advances through a settled carry-free site.

Consumer: `Leader/L3/Top/SettledPotentialNominate.lean`. -/
theorem pair_adv_eq (b : Bool) (y : Cell) (hy : y.i.isS = true) (hyc : y.c = .off) :
    pair b false { i := .e, c := .fresh } y = ({ i := .e, c := .off }, { i := .e, c := .fresh }) := by
  rcases y with ⟨yi, yc⟩
  cases yi <;> cases yc <;> cases b <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS] at hy hyc ⊢

/-- A live carry retires against a site that is not settled.

Consumer: `Leader/L3/Top/SettledPotentialNominate.lean`. -/
theorem pair_death_eq (b : Bool) (y : Cell) (hy : y.i.isS = false) (hyc : y.c = .off)
    (hyx : y.i ≠ .x) :
    pair b false { i := .e, c := .fresh } y = ({ i := .e, c := .off }, y) := by
  rcases y with ⟨yi, yc⟩
  cases yi <;> cases yc <;> cases b <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS] at hy hyc hyx ⊢

/-- A carry is launched from a settled carry-free border site.

Consumer: `Leader/L3/Top/SettledPotentialNominate.lean`. -/
theorem pair_launch_eq (x y : Cell) (hx : x.i.isS = true) (hxc : x.c = .off) (hyc : y.c = .off)
    (hyx : y.i ≠ .x) : pair true false x y = ({ i := .e, c := .fresh }, y) := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  cases xi <;> cases xc <;> cases yi <;> cases yc <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS] at hx hxc hyc hyx ⊢

/-- A pending packet moves into an empty carry-free site.

Consumer: `Leader/L3/Top/SettledPotentialNominate.lean`. -/
theorem pair_move_eq (b : Bool) (x : Cell) (hx : x.i.isP = true) (hxc : x.c = .off) :
    pair b false x { i := .e, c := .off } = ({ i := .e, c := .off }, { i := x.i, c := .off }) := by
  rcases x with ⟨xi, xc⟩
  cases xi <;> cases xc <;> cases b <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS] at hx hxc ⊢

/-- A pending packet settles before a settled carry-free site.

Consumer: `Leader/L3/Top/SettledPotentialNominate.lean`. -/
theorem pair_settle_eq (b : Bool) (x y : Cell) (hx : x.i.isP = true) (hxc : x.c = .off)
    (hy : y.i.isS = true) (hyc : y.c = .off) :
    (pair b false x y).2 = y ∧ (pair b false x y).1.i.isS = true ∧ (pair b false x y).1.c = .off := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  cases xi <;> cases xc <;> cases yi <;> cases yc <;> cases b <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS] at hx hxc hy hyc ⊢

/-- The rightmost witness.

Consumer: `Leader/L3/Top/SettledPotentialNominate.lean`. -/
theorem exists_last (P : Nat → Prop) :
    ∀ r, (∃ k, k < r ∧ P k) → ∃ q, q < r ∧ P q ∧ ∀ k, q < k → k < r → ¬ P k
  | 0, ⟨k, hk, _⟩ => absurd hk (by omega)
  | r + 1, h => by
      by_cases hr : P r
      · exact ⟨r, by omega, hr, fun k h1 h2 => by omega⟩
      · obtain ⟨k, hk, hPk⟩ := h
        have : ∃ k, k < r ∧ P k := ⟨k, by
          by_cases h' : k = r
          · subst h'; exact absurd hPk hr
          · omega, hPk⟩
        obtain ⟨q, hq, hPq, hlast⟩ := exists_last P r this
        refine ⟨q, by omega, hPq, fun k' h1 h2 => ?_⟩
        by_cases h' : k' = r
        · subst h'; exact hr
        · exact hlast k' h1 (by omega)

end MarkedCells
end L3

#print axioms L3.MarkedCells.pair_adv_eq
#print axioms L3.MarkedCells.pair_death_eq
#print axioms L3.MarkedCells.pair_launch_eq
#print axioms L3.MarkedCells.pair_move_eq
#print axioms L3.MarkedCells.pair_settle_eq
#print axioms L3.MarkedCells.exists_last
