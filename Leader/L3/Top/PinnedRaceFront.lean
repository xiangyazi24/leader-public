import Leader.L3.Top.PinnedRaceOff
import Leader.L3.Top.PinnedGv

/-!
# Q7 (P.12 favourable): the outward front sweeps the old suffix

After the outgoing edge wins, the window has the shape `FS r p`: `E/P` registers without carry
before `p`, an erasure front at `p`, and settled non-tails behind it.  One edge of the window
either keeps the shape with the same front, advances the front by one register (the edge of the
front itself), or, at the terminal, retires the front and leaves only `E/P` registers.  The
number of front and settled registers (`frontWork`) never rises and falls on the edge of the
front.

Consumer: `Leader/L3/Top/PinnedRaceClear.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The shape of a window with the outward front at `p`.

Consumer: `fs_edge`, `fs_term`, `fs_port`. -/
def FS (r p : Nat) (cells : Nat → Cell) : Prop :=
  p < r ∧ (∀ j, j < p → EP (cells j) ∧ (cells j).c = .off) ∧
    cells p = { i := .x, c := .off } ∧
    (∀ j, p < j → j < r → cells j = { i := .sn, c := .off })

/-- A window with only `E/P` registers without carry.

Consumer: `fs_term`, `fs_port`. -/
def Clr (r : Nat) (cells : Nat → Cell) : Prop :=
  ∀ j, j < r → EP (cells j) ∧ (cells j).c = .off

/-- One for a front or a settled non-tail register.

Consumer: `frontWork`. -/
def wX (cells : Nat → Cell) (k : Nat) : Nat :=
  if (cells k).i = .x ∨ (cells k).i = .sn then 1 else 0

/-- The number of front and settled non-tail registers.

Consumer: `fs_edge`. -/
def frontWork (r : Nat) (cells : Nat → Cell) : Nat := wsum (wX cells) r

/-- The row patterns of the front sweep.

Consumer: `fs_edge`. -/
theorem pair_front_pat (b : Bool) :
    (∀ x : Cell, EP x → x.c = .off →
      pair b false x { i := .x, c := .off } = (x, { i := .x, c := .off })) ∧
    pair b false { i := .x, c := .off } { i := .sn, c := .off } =
      ({ i := .e, c := .off }, { i := .x, c := .off }) ∧
    (b = false →
      pair b false { i := .sn, c := .off } { i := .sn, c := .off } =
        ({ i := .sn, c := .off }, { i := .sn, c := .off })) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx hxc
    rcases x with ⟨xi, xc⟩
    simp only at hxc
    subst hxc
    unfold EP at hx
    simp only at hx
    cases xi <;> cases b <;> simp_all (config := { decide := true })
      [pair, inSlots, carries, Inp.isP, Inp.isS]
  · cases b <;> simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS]
  · intro hb
    subst hb
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS]

/-- The terminal edge: a front retires, a settled non-tail stays.

Consumer: `fs_term`. -/
theorem pair_term_front :
    (pair false true { i := .x, c := .off } { i := .e, c := .off }).1 = { i := .e, c := .off } ∧
    (pair false true { i := .sn, c := .off } { i := .e, c := .off }).1 =
      { i := .sn, c := .off } := by
  refine ⟨?_, ?_⟩ <;>
  simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS]

/-- An `E/P` register has weight zero.

Consumer: `fs_edge`. -/
theorem wX_ep (cells : Nat → Cell) (k : Nat) (h : EP (cells k)) : wX cells k = 0 := by
  unfold wX EP at *
  rcases hc : cells k with ⟨ci, cc⟩
  rw [hc] at h
  simp only at h ⊢
  cases ci <;> simp_all [Inp.isP]

/-- The work is the same when the weights agree below `r`.

Consumer: `fs_edge`. -/
theorem frontWork_congr (r : Nat) (c1 c2 : Nat → Cell) (h : ∀ k, k < r → wX c1 k = wX c2 k) :
    frontWork r c1 = frontWork r c2 :=
  wsum_congr _ _ r h

/-- Editing a register with itself changes nothing.

Consumer: `fs_edge`. -/
theorem setTwo_self (cells : Nat → Cell) (q : Nat) : setTwo cells q (cells q) (cells (q + 1)) = cells := by
  funext k
  unfold setTwo
  by_cases h1 : k = q
  · subst h1; simp
  · by_cases h2 : k = q + 1
    · subst h2; simp [h1]
    · simp [h1, h2]

/-- **One window edge keeps the shape, or advances the front by one register.**  The front work
does not rise, and falls exactly when the front advances.

Consumer: `Leader/L3/Top/PinnedRaceClear.lean`. -/
theorem fs_edge (r p q : Nat) (cells : Nat → Cell) (hq : q + 1 < r) (h : FS r p cells) :
    (FS r p (edgeStep r cells q) ∧ frontWork r (edgeStep r cells q) ≤ frontWork r cells ∧
      q ≠ p) ∨
    (FS r (p + 1) (edgeStep r cells q) ∧ frontWork r (edgeStep r cells q) + 1 ≤ frontWork r cells ∧
      q = p) := by
  obtain ⟨hpr, hL, hX, hR⟩ := h
  unfold edgeStep
  rw [if_pos hq]
  have hpat := pair_front_pat (decide (q = 0))
  have hident : pair (decide (q = 0)) false (cells q) (cells (q + 1)) = (cells q, cells (q + 1)) →
      setTwo cells q (pair (decide (q = 0)) false (cells q) (cells (q + 1))).1
        (pair (decide (q = 0)) false (cells q) (cells (q + 1))).2 = cells := by
    intro hh; rw [hh]; exact setTwo_self cells q
  by_cases hqp : q = p
  · subst hqp
    right
    have hy := hR (q + 1) (by omega) hq
    have hpair : pair (decide (q = 0)) false (cells q) (cells (q + 1)) =
        ({ i := .e, c := .off }, { i := .x, c := .off }) := by
      rw [hX, hy]; exact hpat.2.1
    rw [hpair]
    simp only []
    have hw := wsum_edit (wX cells) (wX (setTwo cells q { i := .e, c := .off } { i := .x, c := .off }))
      q (fun k h1 h2 => by unfold wX; simp [setTwo, h1, h2]) r (by omega)
    have f1 : wX cells q = 1 := by unfold wX; rw [hX]; simp
    have f2 : wX cells (q + 1) = 1 := by unfold wX; rw [hy]; simp
    have g1 : wX (setTwo cells q { i := .e, c := .off } { i := .x, c := .off }) q = 0 := by
      unfold wX; simp [setTwo]
    have g2 : wX (setTwo cells q { i := .e, c := .off } { i := .x, c := .off }) (q + 1) = 1 := by
      unfold wX; simp [setTwo]
    refine ⟨⟨by omega, ?_, ?_, ?_⟩, ?_, by simp⟩
    · intro j hj
      by_cases hjq : j = q
      · subst hjq; simp only [setTwo, if_true]; exact ⟨Or.inl rfl, by simp⟩
      · have : j ≠ q + 1 := by omega
        simp only [setTwo, if_neg hjq, if_neg this]; exact hL j (by omega)
    · simp [setTwo]
    · intro j hj1 hj2
      have h1 : j ≠ q := by omega
      have h2 : j ≠ q + 1 := by omega
      simp only [setTwo, if_neg h1, if_neg h2]; exact hR j (by omega) hj2
    · unfold frontWork
      rw [f1, f2, g1, g2] at hw
      omega
  · left
    by_cases hA : q + 1 < p
    · have hq1 := hL q (by omega)
      have hq2 := hL (q + 1) hA
      have hpp := pair_ep_off (decide (q = 0)) (cells q) (cells (q + 1)) hq1.1 hq1.2 hq2.1 hq2.2
      refine ⟨⟨hpr, ?_, ?_, ?_⟩, ?_, hqp⟩
      · intro j hj
        by_cases hjq : j = q
        · subst hjq; simp only [setTwo, if_true]; exact ⟨hpp.1, hpp.2.1⟩
        · by_cases hjq1 : j = q + 1
          · subst hjq1; simp only [setTwo, if_neg hjq, if_true]; exact ⟨hpp.2.2.1, hpp.2.2.2⟩
          · simp only [setTwo, if_neg hjq, if_neg hjq1]; exact hL j hj
      · have h1 : p ≠ q := fun hh => hqp hh.symm
        have h2 : p ≠ q + 1 := by omega
        simp only [setTwo, if_neg h1, if_neg h2]; exact hX
      · intro j hj1 hj2
        have h1 : j ≠ q := by omega
        have h2 : j ≠ q + 1 := by omega
        simp only [setTwo, if_neg h1, if_neg h2]; exact hR j hj1 hj2
      · apply Nat.le_of_eq
        apply frontWork_congr
        intro k hk
        by_cases hjq : k = q
        · subst hjq
          rw [wX_ep _ _ (by simp only [setTwo, if_true]; exact hpp.1), wX_ep _ _ hq1.1]
        · by_cases hjq1 : k = q + 1
          · subst hjq1
            rw [wX_ep _ _ (by simp only [setTwo, if_neg hjq, if_true]; exact hpp.2.2.1),
              wX_ep _ _ hq2.1]
          · unfold wX; simp only [setTwo, if_neg hjq, if_neg hjq1]
    · by_cases hB : q + 1 = p
      · have hq1 := hL q (by omega)
        have hy : cells (q + 1) = { i := .x, c := .off } := by rw [hB]; exact hX
        have hpair : pair (decide (q = 0)) false (cells q) (cells (q + 1)) =
            (cells q, cells (q + 1)) := by
          rw [hy]; exact hpat.1 (cells q) hq1.1 hq1.2
        rw [hident hpair]
        exact ⟨⟨hpr, hL, hX, hR⟩, Nat.le_refl _, hqp⟩
      · have hC : p < q := by omega
        have hx := hR q hC (by omega)
        have hy := hR (q + 1) (by omega) hq
        have hq0 : decide (q = 0) = false := by simp; omega
        have hpair : pair (decide (q = 0)) false (cells q) (cells (q + 1)) =
            (cells q, cells (q + 1)) := by
          rw [hx, hy]
          exact hpat.2.2 hq0
        rw [hident hpair]
        exact ⟨⟨hpr, hL, hX, hR⟩, Nat.le_refl _, hqp⟩

/-- Editing a register with itself changes nothing.

Consumer: `fs_term`. -/
theorem setOne_self (cells : Nat → Cell) (q : Nat) : setOne cells q (cells q) = cells := by
  funext k
  unfold setOne
  by_cases h1 : k = q
  · subst h1; simp
  · simp [h1]

/-- **The terminal edge keeps the shape, or retires the front at the terminal.**

Consumer: `Leader/L3/Top/PinnedRaceClear.lean`. -/
theorem fs_term (r p : Nat) (cells : Nat → Cell) (hr : 1 ≤ r) (h : FS r p cells) :
    (FS r p (edgeStep r cells (r - 1)) ∧ frontWork r (edgeStep r cells (r - 1)) ≤ frontWork r cells ∧
      r - 1 ≠ p) ∨
    (Clr r (edgeStep r cells (r - 1)) ∧ r - 1 = p) := by
  obtain ⟨hpr, hL, hX, hR⟩ := h
  have hq : ¬ (r - 1 + 1 < r) := by omega
  unfold edgeStep
  rw [if_neg hq]
  by_cases hp : p = r - 1
  · right
    subst hp
    refine ⟨?_, rfl⟩
    have hpair := pair_term_front.1
    rw [hX, hpair]
    intro j hj
    by_cases hjp : j = r - 1
    · subst hjp; simp only [setOne, if_true]; exact ⟨Or.inl rfl, by simp⟩
    · simp only [setOne, if_neg hjp]; exact hL j (by omega)
  · left
    have hy := hR (r - 1) (by omega) (by omega)
    have hpair : (pair false true (cells (r - 1)) { i := .e, c := .off }).1 = cells (r - 1) := by
      rw [hy]; exact pair_term_front.2
    rw [hpair, setOne_self]
    exact ⟨⟨hpr, hL, hX, hR⟩, Nat.le_refl _, fun hh => hp hh.symm⟩

/-- **The port keeps the shape and the work.**

Consumer: `Leader/L3/Top/PinnedRaceClear.lean`. -/
theorem fs_port (r p : Nat) (cells : Nat → Cell) (hr : 1 ≤ r) (h : FS r p cells) (c' : Cell)
    (hc : c' = portClean (cells 0) ∨ ∃ t, c' = portAccept t (cells 0)) :
    FS r p (setOne cells 0 c') ∧ frontWork r (setOne cells 0 c') = frontWork r cells := by
  obtain ⟨hpr, hL, hX, hR⟩ := h
  by_cases hp0 : p = 0
  · subst hp0
    have hc0 : c' = cells 0 := by
      rcases hc with hc | ⟨t, hc⟩
      · rw [hc]; unfold portClean; rw [hX]; simp
      · rw [hc]; unfold portAccept; rw [hX]; simp
    rw [hc0, setOne_self]
    exact ⟨⟨hpr, hL, hX, hR⟩, rfl⟩
  · have h0 := hL 0 (by omega)
    have hcep : EP c' ∧ c'.c = .off := by
      rcases hc with hc | ⟨t, hc⟩
      · rw [hc]; unfold portClean; rw [if_pos h0.2]; exact h0
      · rw [hc]; unfold portAccept
        by_cases hx : cells 0 = { i := .e, c := .off }
        · rw [if_pos hx]
          refine ⟨?_, rfl⟩
          unfold EP
          cases t <;> simp [Inp.isP]
        · rw [if_neg hx]; exact h0
    refine ⟨⟨hpr, ?_, ?_, ?_⟩, ?_⟩
    · intro j hj
      by_cases hj0 : j = 0
      · subst hj0; simp only [setOne, if_true]; exact hcep
      · simp only [setOne, if_neg hj0]; exact hL j hj
    · simp only [setOne, if_neg hp0]; exact hX
    · intro j hj1 hj2
      have : j ≠ 0 := by omega
      simp only [setOne, if_neg this]; exact hR j hj1 hj2
    · apply frontWork_congr
      intro k hk
      by_cases hk0 : k = 0
      · subst hk0
        rw [wX_ep _ _ (by simp only [setOne, if_true]; exact hcep.1), wX_ep _ _ h0.1]
      · unfold wX; simp only [setOne, if_neg hk0]

end MarkedCells
end L3

#print axioms L3.MarkedCells.fs_edge
#print axioms L3.MarkedCells.fs_term
#print axioms L3.MarkedCells.fs_port
