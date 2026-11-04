import Leader.L3.Top.PinnedPrepareCells
import Leader.L3.Top.PinnedFill
import Leader.L3.Top.SettledWorkSourceModel

/-!
# Q7 (P.12 preparation, lemma 3, abstract layer): the fill regime of the window

While the window holds only empty registers, pending packets and settled non-tail packets, and no
front and no live carry, every edge of the window is one of three things:

* nothing (the pair does not change);
* a move: a pending packet goes right into an empty register;
* a settlement: a pending packet next to a settled non-tail packet settles in place.

`FillShape r c`: the window is a region of empty and pending registers followed by a block of
settled non-tail packets that fills the registers up to the terminal, and the border register is in
the region.  This module proves the three outcomes of an edge in the shape, and the shape of the
window after each of them.

Consumer: `Leader/L3/Top/PinnedPhaseFillStep.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- **The fill shape**: a carry-free region of empty and pending registers, then a block of `m`
settled non-tail packets up to the terminal; the border register is in the region.

Consumer: `FillInv`. -/
def FillShape (r : Nat) (c : Nat → Cell) : Prop :=
  ∃ m, m < r ∧
    (∀ j, j < r - m → (c j).c = .off ∧ ((c j).i = .e ∨ (c j).i = .pt ∨ (c j).i = .pn)) ∧
    (∀ j, r - m ≤ j → j < r → c j = { i := .sn, c := .off })

/-- A pending packet moves into an empty register.

Consumer: `fill_edge_cases`. -/
theorem fill_pair_move (b : Bool) (x : Cell) (hxc : x.c = .off) (hx : x.i.isP = true) :
    pair b false x { i := .e, c := .off } =
      ({ i := .e, c := .off }, { i := x.i, c := .off }) := by
  rcases x with ⟨xi, xk⟩
  simp only at hxc
  subst hxc
  cases xi <;> cases b <;> simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS] at hx ⊢

/-- A pending packet next to a settled non-tail packet settles in place.

Consumer: `fill_edge_cases`. -/
theorem fill_pair_settle (b : Bool) (x : Cell) (hxc : x.c = .off) (hx : x.i.isP = true) :
    pair b false x { i := .sn, c := .off } =
      ({ i := (if x.i = .pt then .st else .sn), c := .off }, { i := .sn, c := .off }) := by
  rcases x with ⟨xi, xk⟩
  simp only at hxc
  subst hxc
  cases xi <;> cases b <;> simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS] at hx ⊢

/-- Every other pair of the fill regime is unchanged.

Consumer: `fill_edge_cases`. -/
theorem fill_pair_none (b : Bool) (x y : Cell) (hxc : x.c = .off) (hyc : y.c = .off)
    (hx : x.i = .e ∨ x.i = .pt ∨ x.i = .pn ∨ x.i = .sn)
    (hy : y.i = .e ∨ y.i = .pt ∨ y.i = .pn ∨ y.i = .sn)
    (hb : b = true → x.i ≠ .sn)
    (hno : ¬ (x.i.isP = true ∧ (y.i = .e ∨ y.i = .sn))) :
    pair b false x y = (x, y) := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  simp only at hxc hyc hx hy hb hno
  subst hxc hyc
  rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> subst hx hy <;>
    cases b <;> simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS] at hb hno ⊢

/-- Every register of a fill window is carry-free and holds one of four input classes.

Consumer: `fill_edge_cases`. -/
theorem fill_kind {r : Nat} {c : Nat → Cell} (hs : FillShape r c) (j : Nat) (hj : j < r) :
    (c j).c = .off ∧ ((c j).i = .e ∨ (c j).i = .pt ∨ (c j).i = .pn ∨ (c j).i = .sn) := by
  obtain ⟨m, hm, hreg, hblk⟩ := hs
  by_cases h : j < r - m
  · obtain ⟨h1, h2⟩ := hreg j h
    exact ⟨h1, by rcases h2 with h2 | h2 | h2 <;> simp [h2]⟩
  · have := hblk j (by omega) hj
    rw [this]
    simp

/-- The border register of a fill window is in the region.

Consumer: `fill_edge_cases`. -/
theorem fill_border {r : Nat} {c : Nat → Cell} (hs : FillShape r c) (hr : 0 < r) :
    (c 0).i = .e ∨ (c 0).i = .pt ∨ (c 0).i = .pn := by
  obtain ⟨m, hm, hreg, _⟩ := hs
  exact (hreg 0 (by omega)).2

/-- **The three outcomes of a window edge in the fill regime.**

Consumer: `Leader/L3/Top/PinnedPhaseFillStep.lean`. -/
theorem fill_edge_cases (r p : Nat) (hp : p + 1 < r) (c : Nat → Cell) (hs : FillShape r c) :
    setTwo c p (pair (decide (p = 0)) false (c p) (c (p + 1))).1
        (pair (decide (p = 0)) false (c p) (c (p + 1))).2 = c ∨
    ((c p).i.isP = true ∧ c (p + 1) = { i := .e, c := .off } ∧
      setTwo c p (pair (decide (p = 0)) false (c p) (c (p + 1))).1
        (pair (decide (p = 0)) false (c p) (c (p + 1))).2 =
        setTwo c p { i := .e, c := .off } { i := (c p).i, c := .off }) ∨
    ((c p).i.isP = true ∧ c (p + 1) = { i := .sn, c := .off } ∧
      setTwo c p (pair (decide (p = 0)) false (c p) (c (p + 1))).1
        (pair (decide (p = 0)) false (c p) (c (p + 1))).2 =
        setOne c p { i := (if (c p).i = .pt then .st else .sn), c := .off }) := by
  have hkx := fill_kind hs p (by omega)
  have hky := fill_kind hs (p + 1) hp
  have hb : decide (p = 0) = true → (c p).i ≠ .sn := by
    intro h
    have h0 : p = 0 := by simpa using h
    subst h0
    rcases fill_border hs (by omega) with h | h | h <;> rw [h] <;> decide
  by_cases hP : (c p).i.isP = true
  · by_cases hye : (c (p + 1)).i = .e
    · right; left
      have hy : c (p + 1) = { i := .e, c := .off } := by
        rcases hc : c (p + 1) with ⟨yi, yk⟩
        rw [hc] at hye hky
        simp only at hye hky
        rw [hye, hky.1]
      refine ⟨hP, hy, ?_⟩
      rw [hy, fill_pair_move _ _ hkx.1 hP]
    · by_cases hys : (c (p + 1)).i = .sn
      · right; right
        have hy : c (p + 1) = { i := .sn, c := .off } := by
          rcases hc : c (p + 1) with ⟨yi, yk⟩
          rw [hc] at hys hky
          simp only at hys hky
          rw [hys, hky.1]
        refine ⟨hP, hy, ?_⟩
        rw [hy, fill_pair_settle _ _ hkx.1 hP]
        funext j
        simp only [setTwo, setOne]
        by_cases h1 : j = p
        · simp [h1]
        · by_cases h2 : j = p + 1
          · simp [h1, h2, hy]
          · simp [h1, h2]
      · left
        rw [fill_pair_none _ _ _ hkx.1 hky.1 hkx.2 hky.2 hb (by
          rintro ⟨_, h | h⟩
          · exact hye h
          · exact hys h)]
        funext j
        simp only [setTwo]
        by_cases h1 : j = p
        · simp [h1]
        · by_cases h2 : j = p + 1
          · simp [h1, h2]
          · simp [h1, h2]
  · left
    rw [fill_pair_none _ _ _ hkx.1 hky.1 hkx.2 hky.2 hb (by
      rintro ⟨h, _⟩
      exact hP h)]
    funext j
    simp only [setTwo]
    by_cases h1 : j = p
    · simp [h1]
    · by_cases h2 : j = p + 1
      · simp [h1, h2]
      · simp [h1, h2]

/-- A move keeps the fill shape.

Consumer: `fill_step_window`. -/
theorem fillShape_move {r p : Nat} {c : Nat → Cell} (hs : FillShape r c) (hp : p + 1 < r)
    (hP : (c p).i.isP = true) (hy : c (p + 1) = { i := .e, c := .off }) :
    FillShape r (setTwo c p { i := .e, c := .off } { i := (c p).i, c := .off }) := by
  obtain ⟨m, hm, hreg, hblk⟩ := hs
  have hpr : p < r - m := by
    apply Classical.byContradiction
    intro h
    have := hblk p (by omega) (by omega)
    rw [this] at hP
    simp [Inp.isP] at hP
  have hpr1 : p + 1 < r - m := by
    apply Classical.byContradiction
    intro h
    have := hblk (p + 1) (by omega) hp
    rw [this] at hy
    simp at hy
  refine ⟨m, hm, ?_, ?_⟩
  · intro j hj
    by_cases h1 : j = p
    · have hv : setTwo c p { i := .e, c := .off } { i := (c p).i, c := .off } j =
          { i := .e, c := .off } := by simp [setTwo, h1]
      rw [hv]
      simp
    · by_cases h2 : j = p + 1
      · have hv : setTwo c p { i := .e, c := .off } { i := (c p).i, c := .off } j =
            { i := (c p).i, c := .off } := by simp [setTwo, h1, h2]
        rw [hv]
        refine ⟨rfl, ?_⟩
        have := (hreg p hpr).2
        rcases this with h | h | h
        · rw [h] at hP; simp [Inp.isP] at hP
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · have hv : setTwo c p { i := .e, c := .off } { i := (c p).i, c := .off } j = c j := by
          simp [setTwo, h1, h2]
        rw [hv]
        exact hreg j hj
  · intro j hj1 hj2
    have h1 : j ≠ p := by omega
    have h2 : j ≠ p + 1 := by omega
    have hv : setTwo c p { i := .e, c := .off } { i := (c p).i, c := .off } j = c j := by
      simp [setTwo, h1, h2]
    rw [hv]
    exact hblk j hj1 hj2

/-- A settlement of a non-tail packet next to the block keeps the fill shape, provided it is not
at the border.

Consumer: `fill_step_window`. -/
theorem fillShape_settle {r p : Nat} {c : Nat → Cell} (hs : FillShape r c) (hp : p + 1 < r)
    (hpn : (c p).i = .pn) (h0 : 0 < p) (hy : c (p + 1) = { i := .sn, c := .off }) :
    FillShape r (setOne c p { i := .sn, c := .off }) := by
  obtain ⟨m, hm, hreg, hblk⟩ := hs
  have hpr : p < r - m := by
    apply Classical.byContradiction
    intro h
    have := hblk p (by omega) (by omega)
    rw [this] at hpn
    simp at hpn
  have hpr1 : r - m ≤ p + 1 := by
    apply Classical.byContradiction
    intro h
    have := (hreg (p + 1) (by omega)).2
    rw [hy] at this
    simp at this
  refine ⟨m + 1, by omega, ?_, ?_⟩
  · intro j hj
    have h1 : j ≠ p := by omega
    simp only [setOne, h1, if_false]
    exact hreg j (by omega)
  · intro j hj1 hj2
    simp only [setOne]
    by_cases h1 : j = p
    · simp [h1]
    · simp only [h1, if_false]
      exact hblk j (by omega) hj2

/-- Accepting a packet into the empty border register keeps the fill shape.

Consumer: `fill_step_window`. -/
theorem fillShape_accept {r : Nat} {c : Nat → Cell} (hs : FillShape r c) (hr : 0 < r) (t : Bool)
    (h0 : c 0 = { i := .e, c := .off }) :
    FillShape r (setOne c 0 { i := (if t then .pt else .pn), c := .off }) := by
  obtain ⟨m, hm, hreg, hblk⟩ := hs
  refine ⟨m, hm, ?_, ?_⟩
  · intro j hj
    simp only [setOne]
    by_cases h1 : j = 0
    · simp only [h1, if_true]
      refine ⟨?_, ?_⟩
      · simp
      · cases t <;> simp
    · simp only [h1, if_false]
      exact hreg j hj
  · intro j hj1 hj2
    simp only [setOne]
    have h1 : j ≠ 0 := by omega
    simp only [h1, if_false]
    exact hblk j hj1 hj2

/-- The terminal edge in the fill regime: nothing, a settlement of a pending non-tail packet, or the
deletion of a pending tail.

Consumer: `fill_step_window`. -/
theorem fill_term_cases (r : Nat) (hr : 0 < r) (c : Nat → Cell) (hs : FillShape r c) :
    (((c (r - 1)).i = .e ∨ (c (r - 1)).i = .sn) ∧
      setOne c (r - 1) (pair false true (c (r - 1)) { i := .e, c := .off }).1 = c) ∨
    ((c (r - 1)).i = .pn ∧
      setOne c (r - 1) (pair false true (c (r - 1)) { i := .e, c := .off }).1 =
        setOne c (r - 1) { i := .sn, c := .off }) ∨
    ((c (r - 1)).i = .pt ∧
      setOne c (r - 1) (pair false true (c (r - 1)) { i := .e, c := .off }).1 =
        setOne c (r - 1) { i := .e, c := .off }) := by
  have hk := fill_kind hs (r - 1) (by omega)
  rcases hx : c (r - 1) with ⟨xi, xk⟩
  rw [hx] at hk
  obtain ⟨hk1, hk2⟩ := hk
  simp only at hk1 hk2
  subst hk1
  rcases hk2 with h | h | h | h <;> subst h
  · left
    refine ⟨Or.inl rfl, ?_⟩
    simp (config := { decide := true }) [pair, inSlots, carries]
    funext j
    by_cases hj : j = r - 1
    · subst hj; simp [setOne, hx]
    · simp [setOne, hj]
  · right; right
    refine ⟨rfl, ?_⟩
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS]
  · right; left
    refine ⟨rfl, ?_⟩
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS]
  · left
    refine ⟨Or.inr rfl, ?_⟩
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS]
    funext j
    by_cases hj : j = r - 1
    · subst hj; simp [setOne, hx]
    · simp [setOne, hj]

/-- A terminal settlement keeps the fill shape.

Consumer: `fill_step_window`. -/
theorem fillShape_term_pn {r : Nat} {c : Nat → Cell} (hs : FillShape r c) (hr : 2 ≤ r)
    (hpn : (c (r - 1)).i = .pn) :
    FillShape r (setOne c (r - 1) { i := .sn, c := .off }) := by
  obtain ⟨m, hm, hreg, hblk⟩ := hs
  have hm0 : m = 0 := by
    apply Classical.byContradiction
    intro h
    have := hblk (r - 1) (by omega) (by omega)
    rw [this] at hpn
    simp at hpn
  subst hm0
  refine ⟨1, by omega, ?_, ?_⟩
  · intro j hj
    have h1 : j ≠ r - 1 := by omega
    simp only [setOne, h1, if_false]
    exact hreg j (by omega)
  · intro j hj1 hj2
    have : j = r - 1 := by omega
    subst this
    simp [setOne]

/-- A terminal deletion of a pending tail keeps the fill shape.

Consumer: `fill_step_window`. -/
theorem fillShape_term_pt {r : Nat} {c : Nat → Cell} (hs : FillShape r c) (hr : 2 ≤ r)
    (hpt : (c (r - 1)).i = .pt) :
    FillShape r (setOne c (r - 1) { i := .e, c := .off }) := by
  obtain ⟨m, hm, hreg, hblk⟩ := hs
  have hm0 : m = 0 := by
    apply Classical.byContradiction
    intro h
    have := hblk (r - 1) (by omega) (by omega)
    rw [this] at hpt
    simp at hpt
  subst hm0
  refine ⟨0, by omega, ?_, ?_⟩
  · intro j hj
    by_cases h1 : j = r - 1
    · subst h1; simp [setOne]
    · simp only [setOne, h1, if_false]
      exact hreg j hj
  · intro j hj1 hj2
    omega

/-- **The exit shape**: a settled tail at `h` (with a settled block after it), preceded by empty and
pending registers.  The tail is a misplaced cut when `1 ≤ h` and an aligned window when `h = 0`.

Consumer: `fill_step`. -/
def ExitShape (r : Nat) (c : Nat → Cell) (h : Nat) : Prop :=
  h + 1 < r ∧ (∀ j, j < h → (c j).c = .off ∧ ((c j).i = .e ∨ (c j).i = .pt ∨ (c j).i = .pn)) ∧
    c h = { i := .st, c := .off } ∧ (∀ j, h < j → j < r → c j = { i := .sn, c := .off })

/-- The settlement of the pending tail next to the block creates the exit shape.

Consumer: `fill_step`, `fill_win_edge`. -/
theorem exit_of_settle {r p : Nat} {c : Nat → Cell} (hs : FillShape r c) (hp : p + 1 < r)
    (hpt : (c p).i = .pt) (hy : c (p + 1) = { i := .sn, c := .off }) :
    ExitShape r (setOne c p { i := .st, c := .off }) p := by
  obtain ⟨m, hm, hreg, hblk⟩ := hs
  have hpr : p < r - m := by
    apply Classical.byContradiction
    intro h
    have := hblk p (by omega) (by omega)
    rw [this] at hpt
    simp at hpt
  have hpr1 : r - m ≤ p + 1 := by
    apply Classical.byContradiction
    intro h
    have := (hreg (p + 1) (by omega)).2
    rw [hy] at this
    simp at this
  refine ⟨hp, ?_, by simp [setOne], ?_⟩
  · intro j hj
    have h1 : j ≠ p := by omega
    simp only [setOne, h1, if_false]
    exact hreg j (by omega)
  · intro j hj1 hj2
    have h1 : j ≠ p := by omega
    simp only [setOne, h1, if_false]
    exact hblk j (by omega) hj2

end MarkedCells
end L3

#print axioms L3.MarkedCells.fill_edge_cases
#print axioms L3.MarkedCells.fill_term_cases
#print axioms L3.MarkedCells.exit_of_settle
