import Leader.L3.Top.PinnedRaceStayRows

/-!
# Q7 (P.12 race): the left registers stay empty or pending and carry-free

At a misplaced-tail witness `h`, every edge other than `f_h` and `f_(h-1)` keeps the registers
left of `h` empty or pending and carry-free.

Consumer: `Leader/L3/TopPinnedRaceWin.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- An empty or pending, carry-free abstract register.

Consumer: `race_left_after`. -/
def LeftCell (c : Cell) : Prop := (c.i = .e ∨ c.i.isP = true) ∧ c.c = .off

/-- An interior pair of left registers stays left.

Consumer: `race_left_after`. -/
theorem pair_left (b : Bool) (x y : Cell) (hx : LeftCell x) (hy : LeftCell y) :
    LeftCell (pair b false x y).1 ∧ LeftCell (pair b false x y).2 := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  simp only at hx1 hx2 hy1 hy2
  subst hx2 hy2
  cases xi <;> cases yi <;> cases b <;>
    simp (config := { decide := true }) [LeftCell, pair, inSlots, carries, Inp.isP, Inp.isS]
      at hx1 hy1 ⊢

/-- The port cleanup keeps a left register.

Consumer: `race_left_after`. -/
theorem portClean_left (c : Cell) (h : LeftCell c) : LeftCell (portClean c) := by
  unfold portClean
  rw [if_pos h.2]
  exact h

/-- The port acceptance keeps a left register.

Consumer: `race_left_after`. -/
theorem portAccept_left (t : Bool) (c : Cell) (h : LeftCell c) : LeftCell (portAccept t c) := by
  unfold portAccept
  split
  · cases t <;> simp [LeftCell, Inp.isP]
  · exact h

/-- **The left registers survive every off-race edge.**

Consumer: `race_keep`. -/
theorem race_left_after {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (h : Nat) (hh : h < topClockSpan n) (hh1 : 1 ≤ h)
    (e : Fin n) (he1 : e ≠ winSite s h) (he2 : e ≠ winSite s (h - 1))
    (hleft : ∀ j, j < h → LeftCell (cellOf s Z j)) :
    ∀ j, j < h → LeftCell (cellOf s (topFixedTraceNext ring C Z e) j) := by
  intro j hj
  have hr3 := span_ge_three hg.hn
  by_cases hw : ∃ p, p < topClockSpan n ∧ e = winSite s p
  · obtain ⟨p, hp, rfl⟩ := hw
    rw [link_window ring C s Z hg hreach p hp j (by omega)]
    have hph : p ≠ h := fun h3 => he1 (by rw [h3])
    have hph1 : p ≠ h - 1 := fun h3 => he2 (by rw [h3])
    by_cases hp1 : p + 1 < topClockSpan n
    · have hj' : j ≠ p ∨ j = p := by omega
      unfold edgeStep
      rw [if_pos hp1]
      by_cases hjp : j = p
      · subst hjp
        have hpp := pair_left (decide (j = 0)) (cellOf s Z j) (cellOf s Z (j + 1))
          (hleft j hj) (hleft (j + 1) (by omega))
        simp only [setTwo, if_true]
        exact hpp.1
      · by_cases hjp1 : j = p + 1
        · subst hjp1
          have hpp := pair_left (decide (p = 0)) (cellOf s Z p) (cellOf s Z (p + 1))
            (hleft p (by omega)) (hleft (p + 1) hj)
          simp only [setTwo, if_neg hjp, if_true]
          exact hpp.2
        · simp only [setTwo, if_neg hjp, if_neg hjp1]
          exact hleft j hj
    · have hjp : j ≠ topClockSpan n - 1 := by omega
      unfold edgeStep
      rw [if_neg hp1]
      simp only [setOne, if_neg hjp]
      exact hleft j hj
  · rcases link_shape ring C s Z hg hreach e hw with hag | hag | ⟨t, hag⟩
    · rw [hag j (by omega)]; exact hleft j hj
    · rw [hag j (by omega)]
      by_cases hj0 : j = 0
      · subst hj0
        simp only [setOne, if_true]
        exact portClean_left _ (hleft 0 hj)
      · simp only [setOne, if_neg hj0]
        exact hleft j hj
    · rw [hag j (by omega)]
      by_cases hj0 : j = 0
      · subst hj0
        simp only [setOne, if_true]
        exact portAccept_left t _ (hleft 0 hj)
      · simp only [setOne, if_neg hj0]
        exact hleft j hj

end MarkedCells
end L3

#print axioms L3.MarkedCells.race_left_after
