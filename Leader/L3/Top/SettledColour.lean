import Leader.L3.Top.MarkedProgress
import Leader.L3.Top.MarkedInv

/-!
# Q7 (P.6): the history colouring of settled inputs and the front cover

After a coloured cut every settled input starts *active*.  A non-border settled tail
that turns into an erasure front dooms the right part of its active run; a front that
enters an active run dooms the rest of it; a consumed or erased input loses its colour.
The cover invariant (paper (iii)): every doomed input has an erasure front immediately
to its left, or a doomed input whose left neighbour is covered in turn.

This module is pure (abstract window): `colourGen` is one colour step,
`cover_step_machine` shows that the cover invariant is inductive, given the fresh-carry
invariants and the absence of inherited carries.

Consumer: `Leader/L3/Top/SettledCover.lean` (the colouring of a fixed-trace word).
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- `k` is reached from `h` through active settled registers.

Consumer: `cover_edge`. -/
def ActiveFrom (cells : Nat → Cell) (d : Nat → Prop) (h k : Nat) : Prop :=
  h ≤ k ∧ ∀ m, h ≤ m → m ≤ k → (cells m).i.isS = true ∧ ¬ d m

/-- Rule 3 fires: a non-border settled tail without a carry turns into a front.

Consumer: `colourGen`. -/
def EventA (cells : Nat → Cell) (p : Nat) : Prop :=
  (cells p).c = .off ∧ (cells p).i = .st ∧ p ≠ 0

/-- Rule 4 fires: a front enters an adjacent settled input without a carry.

Consumer: `colourGen`. -/
def EventB (r : Nat) (cells : Nat → Cell) (p : Nat) : Prop :=
  (cells p).c = .off ∧ (cells p).i = .x ∧ p + 1 < r ∧
    (cells (p + 1)).i.isS = true ∧ (cells (p + 1)).c = .off

/-- The registers newly doomed by the edge at `p`.

Consumer: `colourGen`. -/
def dooms (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) (po : Option Nat) (k : Nat) : Prop :=
  match po with
  | none => False
  | some p =>
      (EventA cells p ∧ ¬ d p ∧ p < k ∧ ActiveFrom cells d p k) ∨
      (EventB r cells p ∧ ¬ d (p + 1) ∧ p + 1 < k ∧ ActiveFrom cells d (p + 1) k)

/-- One colour step: a register stays doomed only while it stays settled, newly
settled registers are active, and the edge dooms as above.

Consumer: `cover_step_machine`. -/
def colourGen (r : Nat) (cells cells' : Nat → Cell) (d : Nat → Prop)
    (po : Option Nat) : Nat → Prop :=
  fun k => k < r ∧ (cells' k).i.isS = true ∧ (cells k).i.isS = true ∧
    (d k ∨ dooms r cells d po k)

/-- The cover invariant.

Consumer: `cover_step_machine`. -/
def Cover (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) : Prop :=
  ∀ u, d u → 0 < u ∧ (cells u).i.isS = true ∧ ((cells (u - 1)).i = .x ∨ d (u - 1))

/-- No inherited carry in the first `r` registers.

Consumer: `cover_step_machine`. -/
def NoInh (r : Nat) (cells : Nat → Cell) : Prop :=
  ∀ j, j < r → (cells j).c ≠ .inh

/-- A live carry sits on an empty host: a consequence of the fresh-carry invariant
without inherited carries.

Consumer: `cover_edge`. -/
theorem host_empty {r : Nat} {cells : Nat → Cell} (hinv : Inv r cells)
    (hni : NoInh r cells) {j : Nat} (hj : j < r) (hc : (cells j).c ≠ .off) :
    (cells j).i = .e := by
  have hf : (cells j).c = .fresh := by
    have := hni j hj
    cases h : (cells j).c <;> simp_all
  exact (hinv.1 j hj hf).1

/-! ### Local facts of one window edge -/

/-- The edge creates no inherited carry.

Consumer: `noInh_step`. -/
theorem pair_noinh (b t : Bool) (x y : Cell) (hx : x.c ≠ .inh) (hy : y.c ≠ .inh) :
    (pair b t x y).1.c ≠ .inh ∧ (pair b t x y).2.c ≠ .inh := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  cases xi <;> cases xk <;> cases yi <;> cases yk <;> cases b <;> cases t <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isS, Inp.isP] at hx hy ⊢

/-- Rule 3: the tail becomes a front.

Consumer: `cover_edge`. -/
theorem pair_event_a (b t : Bool) (x y : Cell) (hc : x.c = .off) (hi : x.i = .st)
    (hb : b = false) : (pair b t x y).1.i = .x := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  simp only at hc hi
  subst hc hi hb
  cases yi <;> cases yk <;> cases t <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isS, Inp.isP]

/-- Rule 3 leaves a carry-free responder alone.

Consumer: `cover_edge`. -/
theorem pair_event_a_y (b : Bool) (x y : Cell) (hc : x.c = .off) (hi : x.i = .st)
    (hb : b = false) (hy : y.c = .off) : (pair b false x y).2 = y := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  simp only at hc hi hy
  subst hc hi hb hy
  cases yi <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isS, Inp.isP]

/-- Rule 4: the front turns the settled responder into a front.

Consumer: `cover_edge`. -/
theorem pair_event_b (b : Bool) (x y : Cell) (hc : x.c = .off) (hi : x.i = .x)
    (hs : y.i.isS = true) (hy : y.c = .off) : (pair b false x y).2.i = .x := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  simp only at hc hi hy
  subst hc hi hy
  cases yi <;> cases b <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isS, Inp.isP] at hs ⊢

/-- The left neighbour of a doomed responder stays covered.

Consumer: `cover_edge`. -/
theorem pair_left_source (b : Bool) (x y : Cell) (dx : Bool)
    (hx : x.c ≠ .off → x.i = .e) (hy : y.c ≠ .off → y.i = .e)
    (hd : dx = true → x.i.isS = true) (hcov : x.i = .x ∨ dx = true)
    (hbd : b = true → dx = false)
    (hs : y.i.isS = true) (hs' : (pair b false x y).2.i.isS = true) :
    (pair b false x y).1.i = .x ∨
      ((pair b false x y).1.i.isS = true ∧ x.i.isS = true ∧ dx = true) := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  cases xi <;> cases xk <;> cases yi <;> cases yk <;> cases b <;> cases dx <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isS, Inp.isP]
      at hx hy hd hcov hbd hs hs' ⊢

/-- The responder of a covered doomed input stays covered.

Consumer: `cover_edge`. -/
theorem pair_left_responder (b : Bool) (x y : Cell) (dx dy : Bool)
    (hx : x.c ≠ .off → x.i = .e) (hy : y.c ≠ .off → y.i = .e)
    (hdx : dx = true → x.i.isS = true) (hdy : dy = true → y.i.isS = true)
    (hcov : y.i = .x ∨ dy = true)
    (hyl : dy = true → (x.i = .x ∨ dx = true)) :
    (pair b false x y).2.i = .x ∨
      ((pair b false x y).2.i.isS = true ∧ y.i.isS = true ∧ dy = true) := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  cases xi <;> cases xk <;> cases yi <;> cases yk <;> cases b <;> cases dx <;> cases dy <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isS, Inp.isP]
      at hx hy hdx hdy hcov hyl ⊢

end MarkedCells
end L3

#print axioms L3.MarkedCells.host_empty
#print axioms L3.MarkedCells.pair_noinh
#print axioms L3.MarkedCells.pair_event_a
#print axioms L3.MarkedCells.pair_event_a_y
#print axioms L3.MarkedCells.pair_event_b
#print axioms L3.MarkedCells.pair_left_source
#print axioms L3.MarkedCells.pair_left_responder
