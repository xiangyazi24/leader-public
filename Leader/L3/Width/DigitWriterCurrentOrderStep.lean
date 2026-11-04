import Leader.L3.Width.DigitWriterCurrentOrder
import Leader.L3.Width.DigitWriterCurrentBank
import Leader.L3.Width.DigitComparisonValuesFold

/-!
# Writer currentness: one audited edge changes the window carries by a `WinShape`

On the fixed marker layout (a delimiter at `src + R` and `src + 2R`, none in between), one audited
edge `e = digitSite (src + k)` changes the writer carries of the target window `[R, 2R)` as
`WinShape R k` says (`windowShape`).  The physical carries match the ghost ones (`CarryAll`), so a
carry moves only onto an empty cell; the delimiter at `src + R` makes the entry edge a terminal
row; a launch needs a delimiter on the source side, which is the cell `R` only.

Consumer: `WidthDigitWriterCurrentOrderRun` (the audit fold).
-/

namespace L3

open L3.WidthDigit
open L3.RenewalReferenceClock

set_option autoImplicit false

section Step

variable {c : Compiled} {n : Nat}

/-- The writer carries of the window cells `src + q`.  Consumer: `windowShape`. -/
def winCarry (ring : DirectedRing n) (root : Fin n) (src : Nat) (G : Fin n → DigitGhost c n) :
    Nat → Option (DigitCarryGhost c n) :=
  fun q => (G (digitSite ring root (src + q))).writer.carry

/-- **The three shapes of the writer carries at the two sites of one audited edge.**

Consumer: `windowShape`. -/
theorem edgeCarry (ring : DirectedRing n) (hn : 2 ≤ n) (S : Fin n → ProjD c)
    (G : Fin n → DigitGhost c n) (time : Nat) (e : Fin n) (hcar : CarryAll S G) :
    (((digitGhostStep ring S G time e e).writer.carry = none ∨
        (digitGhostStep ring S G time e e).writer.carry = (G e).writer.carry) ∧
      ((digitGhostStep ring S G time e (ring.rightNeighbor e)).writer.carry = none ∨
        (digitGhostStep ring S G time e (ring.rightNeighbor e)).writer.carry =
          (G (ring.rightNeighbor e)).writer.carry)) ∨
    ((workerW (S e).word (S (ring.rightNeighbor e)).word).betaY = false ∧
      (digitGhostStep ring S G time e e).writer.carry = none ∧
      (G (ring.rightNeighbor e)).writer.carry = none ∧
      ∃ (L : DigitCarryGhost c n) (u : DigitUse c n), (G e).writer.carry = some L ∧
        (digitGhostStep ring S G time e (ring.rightNeighbor e)).writer.carry =
          some { inherited := L.inherited, uses := L.uses ++ [u] }) ∨
    ((workerW (S e).word (S (ring.rightNeighbor e)).word).betaX = true ∧
      (G e).writer.carry = none ∧
      (∃ u : DigitUse c n, (digitGhostStep ring S G time e e).writer.carry =
        some { inherited := none, uses := [u] }) ∧
      (digitGhostStep ring S G time e (ring.rightNeighbor e)).writer.carry =
        (G (ring.rightNeighbor e)).writer.carry) := by
  have hne := rightNeighbor_ne ring hn e
  have hx := hcar e
  have hy := hcar (ring.rightNeighbor e)
  have hxN : (digitLaneView .writer (S e)
      (workerW (S e).word (S (ring.rightNeighbor e)).word).betaX).carryLive = false →
      (G e).writer.carry = none := by
    intro h
    have h' : (S e).top.wCarry.isW = false := h
    cases hh : (S e).top.wCarry with
    | OFF => rw [hh] at hx; exact hx
    | W cc => rw [hh] at h'; simp [WCarry.isW] at h'
  have hxS : (digitLaneView .writer (S e)
      (workerW (S e).word (S (ring.rightNeighbor e)).word).betaX).carryLive = true →
      ∃ L, (G e).writer.carry = some L := by
    intro h
    have h' : (S e).top.wCarry.isW = true := h
    cases hh : (S e).top.wCarry with
    | OFF => rw [hh] at h'; simp [WCarry.isW] at h'
    | W cc =>
      rw [hh] at hx
      obtain ⟨L, hL, -⟩ := hx
      exact ⟨L, hL⟩
  have hyN : (digitLaneView .writer (S (ring.rightNeighbor e))
      (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY).carryLive = false →
      (G (ring.rightNeighbor e)).writer.carry = none := by
    intro h
    have h' : (S (ring.rightNeighbor e)).top.wCarry.isW = false := h
    cases hh : (S (ring.rightNeighbor e)).top.wCarry with
    | OFF => rw [hh] at hy; exact hy
    | W cc => rw [hh] at h'; simp [WCarry.isW] at h'
  have key := carryShape DigitLane.writer time e (ring.rightNeighbor e)
    (digitLaneView .writer (S e) (workerW (S e).word (S (ring.rightNeighbor e)).word).betaX)
    (digitLaneView .writer (S (ring.rightNeighbor e))
      (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY)
    (G e).writer (G (ring.rightNeighbor e)).writer hxN hxS hyN
  have hx' : (digitGhostStep ring S G time e e).writer.carry =
      (digitLaneReplay DigitLane.writer time e (ring.rightNeighbor e)
        (digitLaneView .writer (S e) (workerW (S e).word (S (ring.rightNeighbor e)).word).betaX)
        (digitLaneView .writer (S (ring.rightNeighbor e))
          (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY)
        (G e).writer (G (ring.rightNeighbor e)).writer).x.carry := by
    simp [digitGhostStep, digitService]
  have hy' : (digitGhostStep ring S G time e (ring.rightNeighbor e)).writer.carry =
      (digitLaneReplay DigitLane.writer time e (ring.rightNeighbor e)
        (digitLaneView .writer (S e) (workerW (S e).word (S (ring.rightNeighbor e)).word).betaX)
        (digitLaneView .writer (S (ring.rightNeighbor e))
          (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY)
        (G e).writer (G (ring.rightNeighbor e)).writer).y.carry := by
    simp [digitGhostStep, digitService, hne]
  rw [hx', hy']
  exact key

/-- **One audited edge changes the writer carries of the target window by a `WinShape`.**

Consumer: `orderRun` (WidthDigitWriterCurrentOrderRun). -/
theorem windowShape (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n) (S : Fin n → ProjD c)
    (G : Fin n → DigitGhost c n) (time R src : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
    (hend : src + 2 * R < n)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hb2R : (S (digitSite ring root (src + 2 * R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (hcar : CarryAll S G) (j : Nat) (hj : j < n)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (ring.rightNeighbor (digitSite ring root j))).word).1.beta =
        (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (ring.rightNeighbor (digitSite ring root j))).word).2.beta =
        (S (ring.rightNeighbor (digitSite ring root j))).word.beta) :
    WinShape R (if src ≤ j then j - src else 0) (winCarry ring root src G)
      (winCarry ring root src (digitGhostStep ring S G time (digitSite ring root j))) := by
  have hne := rightNeighbor_ne ring hn (digitSite ring root j)
  have unch : ∀ q, R ≤ q → q < 2 * R → src + q ≠ j → src + q ≠ j + 1 →
      winCarry ring root src (digitGhostStep ring S G time (digitSite ring root j)) q =
        winCarry ring root src G q := by
    intro q h1 h2 n1 n2
    unfold winCarry
    have hq : digitSite ring root (src + q) ≠ digitSite ring root j := fun he =>
      n1 (bankRepairDigitSiteInj ring root (by omega) hj he)
    have hq2 : digitSite ring root (src + q) ≠ ring.rightNeighbor (digitSite ring root j) := by
      intro he
      rw [← bankRepairDigitSiteSucc] at he
      by_cases hjn : j + 1 < n
      · exact n2 (bankRepairDigitSiteInj ring root (by omega) hjn he)
      · have hjn' : j + 1 = n := by omega
        rw [hjn', bankRepairDigitSiteN] at he
        have h0 : digitSite ring root (src + q) = digitSite ring root 0 := he
        have := bankRepairDigitSiteInj ring root (by omega : src + q < n) (by omega : 0 < n) h0
        omega
    have hG : digitGhostStep ring S G time (digitSite ring root j) (digitSite ring root (src + q)) =
        G (digitSite ring root (src + q)) := by
      simp [digitGhostStep, hq, hq2]
    rw [hG]
  rcases Nat.lt_or_ge j src with hjs | hjs
  · rw [if_neg (by omega)]
    exact ⟨fun q h1 h2 _ _ => unch q h1 h2 (by omega) (by omega), fun h => by omega,
      fun h1 h2 => by omega, fun h => by omega⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hjs
    rw [if_pos hjs, Nat.add_sub_cancel_left]
    by_cases hf : k + 1 < R ∨ 2 * R ≤ k
    · exact ⟨fun q h1 h2 _ _ => unch q h1 h2 (by omega) (by omega), fun h => by omega,
        fun h1 h2 => by omega, fun h => by omega⟩
    · have hx := edgeCarry ring hn S G time (digitSite ring root (src + k)) hcar
      have hmx : (workerW (S (digitSite ring root (src + k))).word
          (S (ring.rightNeighbor (digitSite ring root (src + k)))).word).betaX =
          (S (digitSite ring root (src + k))).word.beta := hbX
      have hmy : (workerW (S (digitSite ring root (src + k))).word
          (S (ring.rightNeighbor (digitSite ring root (src + k)))).word).betaY =
          (S (ring.rightNeighbor (digitSite ring root (src + k)))).word.beta := hbY
      refine ⟨fun q h1 h2 n1 n2 => unch q h1 h2 (by omega) (by omega), ?_, ?_, ?_⟩
      · intro h
        have hbR' : (S (ring.rightNeighbor (digitSite ring root (src + k)))).word.beta = true := by
          rw [← h] at hbR
          exact hbR
        rw [← h]
        rcases hx with ⟨-, hy⟩ | ⟨hm, -⟩ | ⟨-, -, -, hy⟩
        · exact hy
        · rw [hmy, hbR'] at hm
          cases hm
        · exact Or.inr hy
      · intro hRk hk2
        rcases hx with hA | ⟨-, hx0, hy0, L, u, hL, hy1⟩ | ⟨hm, hg0, ⟨u, hu⟩, hyk⟩
        · exact Or.inl hA
        · exact Or.inr (Or.inl ⟨hx0, hy0, L, u, hL, hy1⟩)
        · have hkR : k = R := by
            by_cases hkR : k = R
            · exact hkR
            · have := hbF k (by omega) (by omega) hkR
              rw [hmx, this] at hm
              cases hm
          exact Or.inr (Or.inr ⟨hkR, hg0, ⟨u, hu⟩, hyk⟩)
      · intro h
        have hb2R' : (S (ring.rightNeighbor (digitSite ring root (src + k)))).word.beta = true := by
          have : k + 1 = 2 * R := h
          rw [← this] at hb2R
          exact hb2R
        rcases hx with ⟨hxa, -⟩ | ⟨hm, -⟩ | ⟨hm, -⟩
        · exact hxa
        · rw [hmy, hb2R'] at hm
          cases hm
        · have := hbF k (by omega) (by omega) (by omega)
          rw [hmx, this] at hm
          cases hm

end Step

end L3

#print axioms L3.windowShape
