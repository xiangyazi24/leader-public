import Leader.L3.Width.DigitWriterCurrentLive
import Leader.L3.Width.DigitComparisonValuesFold

/-!
# Writer currentness: a non-inherited live writer carry has an empty input, along the audit

`LiveInv S G`: at every site whose physical writer carry is live and whose ghost carry is a
non-inherited ledger, the writer input is empty.  One audit letter preserves it, with no
hypothesis: the two touched sites satisfy it by `liveTop_live_in` whatever their ghosts are, the
other sites are unchanged.  It holds at the start because every ghost carry of the initial ghost is
inherited.  This is the physical side of the `LiveE` clause of the aged window: `LiveE` follows
from `LiveInv` and the clause "every live carry of the target window is non-inherited".

Consumer: `liveE_of_ledgers` (WidthDigitWriterCurrentAge).
-/

namespace L3

open L3.WidthDigit

set_option autoImplicit false

section Inv

variable {c : Compiled} {n : Nat}

/-- Consumer: `liveInv_step`, `liveInv_fold`, `liveE_of_ledgers`. -/
def LiveInv (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n) : Prop :=
  ∀ i (L : DigitCarryGhost c n), (S i).top.wCarry.isW = true → (G i).writer.carry = some L →
    L.inherited = none → (S i).top.wIn = .E

/-- **One audited edge preserves `LiveInv`.**  Consumer: `liveInv_fold`. -/
theorem liveInv_step (ring : DirectedRing n) (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n)
    (time : Nat) (e : Fin n) (h : LiveInv S G) :
    LiveInv (phiD ring S e) (digitGhostStep ring S G time e) := by
  intro i L hlive hL hinh
  have key := liveTop_live_in c (S e).lift (S (ring.rightNeighbor e)).lift
    (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
    (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta
  by_cases hie : i = e
  · subst hie
    have hl : (liveTopPair c (S i).lift (S (ring.rightNeighbor i)).lift
        (pairW (S i).word (S (ring.rightNeighbor i)).word).1.beta
        (pairW (S i).word (S (ring.rightNeighbor i)).word).2.beta).x.wCarry.isW = true := by
      simpa [phiD, projectedEdge, pairD, topD] using hlive
    have := key.1 hl
    simpa [phiD, projectedEdge, pairD, topD] using this
  · by_cases hij : i = ring.rightNeighbor e
    · subst hij
      have hl : (liveTopPair c (S e).lift (S (ring.rightNeighbor e)).lift
          (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
          (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta).y.wCarry.isW = true := by
        simpa [phiD, projectedEdge, pairD, topD, hie] using hlive
      have := key.2 hl
      simpa [phiD, projectedEdge, pairD, topD, hie] using this
    · have hS : phiD ring S e i = S i := by simp [phiD, projectedEdge, hie, hij]
      have hG : digitGhostStep ring S G time e i = G i := by simp [digitGhostStep, hie, hij]
      rw [hS] at hlive ⊢
      rw [hG] at hL
      exact h i L hlive hL hinh

/-- Consumer: `liveInv_fold`. -/
theorem liveInv_initial (S : Fin n → ProjD c) : LiveInv S (digitGhostInitial S) := by
  intro i L hlive hL hinh
  by_cases hw : (S i).top.wCarry.isW = true
  · simp [digitGhostInitial, DigitGhost.initial, DigitLaneGhost.initial, digitLaneView, hw] at hL
    rw [← hL] at hinh
    simp at hinh
  · simp [digitGhostInitial, DigitGhost.initial, DigitLaneGhost.initial, digitLaneView, hw] at hL

/-- **`LiveInv` along the audit fold of a drained start.**  Consumer: `liveE_of_ledgers`. -/
theorem liveInv_fold {ring : DirectedRing n} (ref : WidthDigitReference ring) (w : List (Fin n)) :
    ∀ p : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      ref.drained p.1 → LiveInv (piD (ref.phys p.1)) p.2.current →
      LiveInv (piD (ref.phys (w.foldl (widthDigitAuditNext ref) p).1))
        (w.foldl (widthDigitAuditNext ref) p).2.current := by
  induction w with
  | nil => intro p _ hi; exact hi
  | cons e w ih =>
    intro p hd hi
    simp only [List.foldl_cons]
    apply ih
    · exact ref.drainedClosed p.1 hd e
    · show LiveInv (piD (ref.phys (ref.next p.1 e)))
        (digitGhostStep ring (piD (ref.phys p.1)) p.2.current (p.2.clock + 1) e)
      rw [ref.digitStep p.1 hd e]
      exact liveInv_step ring _ _ _ e hi

end Inv

end L3

#print axioms L3.liveInv_step
#print axioms L3.liveInv_fold
