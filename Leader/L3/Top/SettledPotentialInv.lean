import Leader.L3.Top.SettledPotentialStrict
import Leader.L3.Top.PinnedClasses

/-!
# Q7 (P.6--P.10): the invariant of the product chain and a tight bound on the measure

Consumer: `Leader/L3/Top/SettledPotentialFront.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The state-level part of the invariant: reached, pinned, and the barrier.

Consumer: `PInv`. -/
def StateInv {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Prop :=
  topClockReached ring C Z ∧ topClockPinned ring C s Z ∧ Barrier (topClockSpan n) (cellOf s Z)

/-- The chain on states paired with a colouring.

Consumer: `PInv`. -/
noncomputable def prodNext {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (x : TopFixedTraceState n × (Nat → Prop)) (e : Fin n) :
    TopFixedTraceState n × (Nat → Prop) :=
  (topFixedTraceNext ring C x.1 e, colourNext ring C s x.1 e x.2)

/-- The invariant of the product chain: the state-level part and a sound colouring.

Consumer: `Leader/L3/Top/SettledPotentialFront.lean`. -/
def PInv {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (x : TopFixedTraceState n × (Nat → Prop)) : Prop :=
  StateInv ring C s x.1 ∧ ColourInv s x.1 x.2

/-- Pinning is kept by every step.

Consumer: `pinv_next`. -/
theorem pinned_next {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Z : TopFixedTraceState n) (hreach : topClockReached ring C Z)
    (e : Fin n) (h : topClockPinned ring C s Z) : topClockPinned ring C s (topFixedTraceNext ring C Z e) := by
  obtain ⟨Y0, hcut, hmf, hold⟩ := h
  exact ⟨Y0, hcut, markedFrom_next ring C Y0 Z e hmf,
    noOld_next ring C s hg _ Z hreach (markedFrom_clock ring C Y0 Z hcut.1 hmf) e hold⟩

/-- **The invariant is closed.**

Consumer: `Leader/L3/Top/SettledPotentialFront.lean`. -/
theorem pinv_next {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (x : TopFixedTraceState n × (Nat → Prop)) (e : Fin n)
    (h : PInv ring C s x) : PInv ring C s (prodNext ring C s x e) := by
  obtain ⟨⟨hr, hp, hb⟩, hc⟩ := h
  exact ⟨⟨topClockReachedNext ring C x.1 e hr, pinned_next ring C s hg x.1 hr e hp,
    barrier_next ring C s hg x.1 hr e hc.2.1 hb⟩, cover_step_machine ring C s hg x.1 hr x.2 e hc⟩

/-- The fill work of a window is below `2 r^2`.

Consumer: `Gv_tight`. -/
theorem FT_tight (r : Nat) (cells : Nat → Cell) : FT r cells ≤ 2 * (r * r) := by
  unfold FT
  split
  · rename_i hfs
    have hw := wsum_le_below (fillW r cells) (2 * r + 1) (fsOf r cells) (fun k hk => by
      unfold fillW
      split <;> omega)
    obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
    have h2 : fsOf (q + 1) cells * (2 * (q + 1) + 1) ≤ q * (2 * (q + 1) + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 : q * (2 * (q + 1) + 1) + (q + 1 + 1) ≤ 2 * ((q + 1) * (q + 1)) := by
      have e1 : q * (2 * (q + 1) + 1) = 2 * (q * q) + 3 * q := by
        have : 2 * (q + 1) + 1 = 2 * q + 3 := by omega
        rw [this, Nat.mul_add, Nat.mul_left_comm]
        omega
      have e2 : (q + 1) * (q + 1) = q * q + 2 * q + 1 := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
        omega
      omega
    exact Nat.le_trans (Nat.add_le_add_right (Nat.le_trans hw h2) _) h3
  · omega

/-- The measure of a window is below `2 r^2 + 1`.

Consumer: `Th_tight`. -/
theorem Gv_tight (r : Nat) (cells : Nat → Cell) (hr : 1 ≤ r) : Gv r cells ≤ 2 * (r * r) + 1 := by
  have h1 := FT_tight r cells
  have h2 : r ≤ r * r := by
    calc r = r * 1 := (Nat.mul_one r).symm
      _ ≤ r * r := Nat.mul_le_mul_left r hr
  unfold Gv
  split
  · split <;> omega
  · omega

/-- **The supply potential is below `2 r^2 + r + 2`.**

Consumer: `Leader/L3/Top/SettledPotentialWork.lean`. -/
theorem Th_tight {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Z : TopFixedTraceState n) :
    Th s Z ≤ 2 * (topClockSpan n * topClockSpan n) + topClockSpan n + 2 := by
  have h1 := Gv_tight (topClockSpan n) (cellOf s Z) (by have := span_ge_three hg.hn; omega)
  have h2 := dist_le (topClockSpan n) (srcOf s Z)
  unfold Th
  split <;> omega

end MarkedCells
end L3

#print axioms L3.MarkedCells.pinv_next
#print axioms L3.MarkedCells.Th_tight
