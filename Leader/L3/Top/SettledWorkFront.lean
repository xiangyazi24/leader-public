import Leader.L3.Top.SettledWorkPotTerm

/-!
# Q7 (P.7): a front always has an edge that lowers the potential

If an erasure front stands at register `p`, the edge at `p` strictly lowers the lexicographic
potential `(A, M)`: either the charge `A` of the active settled inputs falls, or the front debt
`M = 2 D + X` falls.  A front advancing into an active settled input dooms it (the charge
falls); into a doomed input consumes it; elsewhere the front retires.

Consumer: `Leader/L3/Top/SettledWorkFrontTrace.lean`.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The two cases of a front's edge: it advances into a settled input, or it retires.

Consumer: `front_edge_pot`. -/
theorem pair_front_x (b t : Bool) (x y : Cell) (hx : x.i = .x) (hxc : x.c = .off)
    (hy : y.c ≠ .off → y.i = .e) :
    (y.i.isS = true ∧ y.c = .off ∧ t = false →
      (pair b t x y).1.i.isS = false ∧ (pair b t x y).2.i.isS = false ∧
      fr (pair b t x y).1 + fr (pair b t x y).2 ≤ fr x + fr y) ∧
    (¬ (y.i.isS = true ∧ y.c = .off ∧ t = false) →
      fr (pair b t x y).1 + (if t = false then fr (pair b t x y).2 else 0) + 1 ≤
        fr x + fr y) := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  simp only at hx hxc
  subst hx; subst hxc
  cases yi <;> cases yc <;> cases b <;> cases t <;>
    simp (config := { decide := true }) [pair, inSlots, carries, fr, Inp.isP, Inp.isS] at hy ⊢

/-- No new doomed register, one fewer front: the debt falls.

Consumer: `front_edge_pot`. -/
theorem mn_lt_of (r : Nat) (cells cells' : Nat → Cell) (d : Nat → Prop) (po : Option Nat)
    (hnd : ∀ m, ¬ dooms r cells d po m) (hX : Xn r cells' + 1 ≤ Xn r cells) :
    Mn r cells' (colourGen r cells cells' d po) + 1 ≤ Mn r cells d := by
  have := Dn_le r d _ (colourGen_sub r cells cells' d po hnd)
  unfold Mn; omega

/-- No new doomed register, one doomed register loses its colour, fronts do not increase:
the debt falls.

Consumer: `front_edge_pot`. -/
theorem mn_lt_of_front (r : Nat) (cells cells' : Nat → Cell) (d : Nat → Prop)
    (po : Option Nat) (hnd : ∀ m, ¬ dooms r cells d po m) (q : Nat) (hq : q < r) (hdq : d q)
    (hdq' : ¬ colourGen r cells cells' d po q) (hX : Xn r cells' ≤ Xn r cells) :
    Mn r cells' (colourGen r cells cells' d po) + 1 ≤ Mn r cells d := by
  have := Dn_lt r d _ (colourGen_sub r cells cells' d po hnd) q hq hdq hdq'
  unfold Mn; omega

/-- **A front's window edge lowers the potential**: the charge falls, or the debt falls.

Consumer: `Leader/L3/Top/SettledWorkFrontTrace.lean`. -/
theorem front_edge_pot (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) (p : Nat)
    (hp : p + 1 < r) (hinv : Inv r cells) (hni : NoInh r cells)
    (hxx : (cells p).i = .x) :
    charge r (act r (setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2)
      (colourGen r cells (setTwo cells p
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2) d (some p))) <
    charge r (act r cells d) ∨
    Mn r (setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2)
      (colourGen r cells (setTwo cells p
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2) d (some p)) + 1 ≤
    Mn r cells d := by
  have hxc : (cells p).c = .off := by
    by_cases h : (cells p).c = .off
    · exact h
    · have := host_empty hinv hni (by omega) h
      rw [hxx] at this; cases this
  have hy : (cells (p + 1)).c ≠ .off → (cells (p + 1)).i = .e := fun h =>
    host_empty hinv hni hp h
  have hxS : (cells p).i.isS = false := by rw [hxx]; rfl
  have hF := pair_front_x (decide (p = 0)) false (cells p) (cells (p + 1)) hxx hxc hy
  have hX := Xn_two r cells p hp (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
    (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2
  have hfx : fr (cells p) = 1 := by simp [fr, hxx]
  have hnA : ¬ EventA cells p := by
    rintro ⟨_, h2, _⟩; rw [hxx] at h2; cases h2
  generalize hpr : pair (decide (p = 0)) false (cells p) (cells (p + 1)) = pr at hF hX ⊢
  have hS' : ∀ k, (setTwo cells p pr.1 pr.2 k).i.isS =
      if k = p then pr.1.i.isS else if k = p + 1 then pr.2.i.isS else (cells k).i.isS := by
    intro k
    unfold setTwo
    by_cases h1 : k = p
    · simp [h1]
    · by_cases h2 : k = p + 1
      · simp [h1, h2]
      · simp [h1, h2]
  have hSp : (setTwo cells p pr.1 pr.2 p).i.isS = pr.1.i.isS := by rw [hS']; simp
  have hSq : (setTwo cells p pr.1 pr.2 (p + 1)).i.isS = pr.2.i.isS := by rw [hS']; simp
  have hSo : ∀ k, k ≠ p → k ≠ p + 1 →
      (setTwo cells p pr.1 pr.2 k).i.isS = (cells k).i.isS := by
    intro k h1 h2; rw [hS']; simp [h1, h2]
  by_cases hadv : (cells (p + 1)).i.isS = true ∧ (cells (p + 1)).c = .off ∧ (false = false)
  · obtain ⟨hyS, hyc, _⟩ := hadv
    obtain ⟨hx'S, hy'S, hfr⟩ := hF.1 ⟨hyS, hyc, rfl⟩
    have hS2 : ∀ k, (setTwo cells p pr.1 pr.2 k).i.isS = true → (cells k).i.isS = true := by
      intro k hk
      by_cases h1 : k = p
      · subst h1; rw [hSp, hx'S] at hk; exact absurd hk (by simp)
      · by_cases h2 : k = p + 1
        · subst h2; rw [hSq, hy'S] at hk; exact absurd hk (by simp)
        · rw [hSo k h1 h2] at hk; exact hk
    by_cases ha : act r cells d (p + 1) = true
    · left
      obtain ⟨_, hyS', hyd⟩ := (act_iff r cells d (p + 1)).1 ha
      refine act_cut_case_lt r cells _ d (some p) (p + 1) ha ?_ hS2 ?_ ?_ ?_
      · intro k hk hact
        obtain ⟨_, hk2, _⟩ := (act_iff r cells d k).1 hact
        by_cases h1 : k = p
        · subst h1; rw [hxS] at hk2; exact absurd hk2 (by simp)
        · rw [hSo k h1 hk]; exact hk2
      · rw [hSq]; exact hy'S
      · intro m hm hA
        unfold dooms
        exact Or.inr ⟨⟨hxc, hxx, hp, hyS', hyc⟩, hyd, hm, hA⟩
      · intro m h
        unfold dooms at h
        rcases h with ⟨hA, _⟩ | ⟨_, _, h3, h4⟩
        · exact absurd hA hnA
        · exact ⟨h3, h4⟩
    · right
      have hd : d (p + 1) := by
        by_cases hd : d (p + 1)
        · exact hd
        · exact absurd ((act_iff r cells d (p + 1)).2 ⟨hp, hyS, hd⟩) ha
      have hnd : ∀ m, ¬ dooms r cells d (some p) m := by
        intro m h
        unfold dooms at h
        rcases h with ⟨hA, _⟩ | ⟨_, h2, _⟩
        · exact hnA hA
        · exact h2 hd
      refine mn_lt_of_front r cells _ d (some p) hnd (p + 1) hp hd ?_ (by omega)
      rintro ⟨_, h2, _⟩
      rw [hSq, hy'S] at h2; exact absurd h2 (by simp)
  · right
    have hn := hF.2 (by simpa using hadv)
    simp only [if_true] at hn
    have hnd : ∀ m, ¬ dooms r cells d (some p) m := by
      intro m h
      unfold dooms at h
      rcases h with ⟨hA, _⟩ | ⟨⟨_, _, _, h4, h5⟩, _⟩
      · exact hnA hA
      · exact hadv ⟨h4, h5, rfl⟩
    exact mn_lt_of r cells _ d (some p) hnd (by omega)

/-- **A front at the terminal register retires**: the debt falls.

Consumer: `Leader/L3/Top/SettledWorkFrontTrace.lean`. -/
theorem front_term_pot (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) (p : Nat)
    (hp : p + 1 = r) (hinv : Inv r cells) (hni : NoInh r cells)
    (hxx : (cells p).i = .x) :
    Mn r (setOne cells p (pair false true (cells p) { i := .e, c := .off }).1)
      (colourGen r cells (setOne cells p
        (pair false true (cells p) { i := .e, c := .off }).1) d (some p)) + 1 ≤
    Mn r cells d := by
  have hxc : (cells p).c = .off := by
    by_cases h : (cells p).c = .off
    · exact h
    · have := host_empty hinv hni (by omega) h
      rw [hxx] at this; cases this
  have hF := pair_front_x false true (cells p) { i := .e, c := .off } hxx hxc
    (by intro h; exact absurd rfl h)
  have hn := hF.2 (by simp)
  have hX := Xn_one r cells p (by omega)
    (pair false true (cells p) { i := .e, c := .off }).1
  have hfx : fr (cells p) = 1 := by simp [fr, hxx]
  have hfy : fr ({ i := .e, c := .off } : Cell) = 0 := by simp [fr]
  generalize hpr : pair false true (cells p) { i := .e, c := .off } = pr at hn hX
  simp [hfy] at hn
  have hnA : ¬ EventA cells p := by
    rintro ⟨_, h2, _⟩; rw [hxx] at h2; cases h2
  have hnB : ¬ EventB r cells p := by
    rintro ⟨_, _, h3, _⟩; omega
  exact mn_lt_of r cells _ d (some p) (dooms_none r cells d p hnA hnB) (by omega)

end MarkedCells
end L3
