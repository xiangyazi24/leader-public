import Leader.L3.Width.DigitWriterCurrentWrites

/-!
# Writer currentness: a non-inherited ghost ledger is non-empty

`LedgerNE G`: every writer ghost carry that is not inherited has a non-empty list of uses.  This is
the `uses ≠ []` part of the ledger clause of the aged window.  It is preserved by one audited edge
(`ledgerNE_step`): the only rows that create a ledger give it one use (launch) or extend an old
ledger (success), and the others keep or drop carries.  It holds initially because every initial
ghost carry is inherited.

Consumer: `WidthDigitWriterCurrentAge` (the ledger clause).
-/

namespace L3

open L3.WidthDigit

set_option autoImplicit false

section Abstract

variable {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat) (source dest : Fin n)
  (xv yv : DigitLaneView c) (gx gy : DigitLaneGhost c n) (Q : DigitCarryGhost c n → Prop)

/-- **A property of ledgers that holds on the old ledgers, on every extension by one use and on the
launched ledger holds on the ledgers after the lane replay.**

Consumer: `ledgerNE_step`. -/
theorem ledgerPair
    (hxP : ∀ L, gx.carry = some L → Q L)
    (hyP : ∀ L, gy.carry = some L → Q L)
    (hadv : ∀ (L0 : DigitCarryGhost c n) (u : DigitUse c n), Q { L0 with uses := L0.uses ++ [u] })
    (hlau : xv.leader = false → yv.leader = false → xv.carryLive = false → xv.marker = true →
      xv.input.isS = true →
      Q { inherited := none,
          uses := [{ time := time, target := source, operand := gx.input, value := inV c xv.input,
                     tail := inT xv.input, targetDigit := xv.digit, carryIn := true,
                     errorIn := false }] }) :
    (∀ L, (digitLaneReplay lane time source dest xv yv gx gy).x.carry = some L → Q L) ∧
      (∀ L, (digitLaneReplay lane time source dest xv yv gx gy).y.carry = some L → Q L) := by
  by_cases hroot : (xv.leader || yv.leader) = true
  · have g := replay_carry_root lane time source dest xv yv gx gy hroot
    rw [g.1, g.2]
    constructor
    · intro L hL
      by_cases hc : xv.carryLive = true
      · rw [if_pos hc] at hL; cases hL
      · rw [if_neg hc] at hL; exact hxP L hL
    · intro L hL
      by_cases hc : yv.carryLive = true
      · rw [if_pos hc] at hL; cases hL
      · rw [if_neg hc] at hL; exact hyP L hL
  · have hxl : xv.leader = false := by
      cases h : xv.leader
      · rfl
      · exact absurd (by simp [h]) hroot
    have hyl : yv.leader = false := by
      cases h : yv.leader
      · rfl
      · exact absurd (by simp [h]) hroot
    by_cases hxc : xv.carryLive = true
    · by_cases hm : yv.marker = true
      · have g := replay_carry_terminal lane time source dest xv yv gx gy hxl hyl hxc hm
        rw [g.1, g.2]
        exact ⟨(fun L hL => by cases hL), hyP⟩
      · have hm' : yv.marker = false := Bool.eq_false_iff.mpr hm
        by_cases hyc : yv.carryLive = true
        · have g := replay_carry_blockedCarry lane time source dest xv yv gx gy hxl hyl hxc hm' hyc
          rw [g.1, g.2]
          exact ⟨(fun L hL => by cases hL), hyP⟩
        · have hyc' : yv.carryLive = false := Bool.eq_false_iff.mpr hyc
          by_cases his : yv.input.isS = true
          · have g := replay_carry_success lane time source dest xv yv gx gy hxl hyl hxc hm' hyc'
              his
            rw [g.1, g.2]
            refine ⟨(fun L hL => by cases hL), ?_⟩
            intro L hL
            cases hL
            exact hadv _ _
          · have his' : yv.input.isS = false := Bool.eq_false_iff.mpr his
            have g := replay_carry_blockedInput lane time source dest xv yv gx gy hxl hyl hxc hm'
              his'
            rw [g.1, g.2]
            exact ⟨(fun L hL => by cases hL), hyP⟩
    · have hxc' : xv.carryLive = false := Bool.eq_false_iff.mpr hxc
      by_cases hxm : xv.marker = true
      · by_cases hxs : xv.input.isS = true
        · have g := replay_carry_launch lane time source dest xv yv gx gy hxl hyl hxc' hxm hxs
          rw [g.1, g.2]
          refine ⟨?_, hyP⟩
          intro L hL
          cases hL
          exact hlau hxl hyl hxc' hxm hxs
        · have hxs' : xv.input.isS = false := Bool.eq_false_iff.mpr hxs
          have g := replay_carry_idleInput lane time source dest xv yv gx gy hxl hyl hxc' hxs'
          rw [g.1, g.2]
          exact ⟨hxP, hyP⟩
      · have hxm' : xv.marker = false := Bool.eq_false_iff.mpr hxm
        have g := replay_carry_idleMarker lane time source dest xv yv gx gy hxl hyl hxc' hxm'
        rw [g.1, g.2]
        exact ⟨hxP, hyP⟩

end Abstract

section Inv

variable {c : Compiled} {n : Nat}

/-- Consumer: `ledgerNE_step`. -/
def LedgerNE (G : Fin n → DigitGhost c n) : Prop :=
  ∀ i (L : DigitCarryGhost c n), (G i).writer.carry = some L → L.inherited = none → L.uses ≠ []

/-- **One audited edge preserves `LedgerNE`.**  Consumer: `ledgerNE_fold`. -/
theorem ledgerNE_step (ring : DirectedRing n) (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n)
    (time : Nat) (e : Fin n) (h : LedgerNE G) :
    LedgerNE (digitGhostStep ring S G time e) := by
  have key := ledgerPair DigitLane.writer time e (ring.rightNeighbor e)
    (digitLaneView .writer (S e) (workerW (S e).word (S (ring.rightNeighbor e)).word).betaX)
    (digitLaneView .writer (S (ring.rightNeighbor e))
      (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY)
    (G e).writer (G (ring.rightNeighbor e)).writer
    (fun L : DigitCarryGhost c n => L.inherited = none → L.uses ≠ [])
    (fun L hL => h e L hL) (fun L hL => h _ L hL)
    (fun L0 u _ => by simp)
    (fun _ _ _ _ _ _ => by simp)
  intro i L hL hinh
  by_cases hie : i = e
  · subst hie
    have hL' : (digitLaneReplay DigitLane.writer time i (ring.rightNeighbor i)
        (digitLaneView .writer (S i) (workerW (S i).word (S (ring.rightNeighbor i)).word).betaX)
        (digitLaneView .writer (S (ring.rightNeighbor i))
          (workerW (S i).word (S (ring.rightNeighbor i)).word).betaY)
        (G i).writer (G (ring.rightNeighbor i)).writer).x.carry = some L := by
      simpa [digitGhostStep, digitService] using hL
    exact key.1 L hL' hinh
  · by_cases hij : i = ring.rightNeighbor e
    · subst hij
      have hL' : (digitLaneReplay DigitLane.writer time e (ring.rightNeighbor e)
          (digitLaneView .writer (S e) (workerW (S e).word (S (ring.rightNeighbor e)).word).betaX)
          (digitLaneView .writer (S (ring.rightNeighbor e))
            (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY)
          (G e).writer (G (ring.rightNeighbor e)).writer).y.carry = some L := by
        simpa [digitGhostStep, digitService, hie] using hL
      exact key.2 L hL' hinh
    · have hL' : (G i).writer.carry = some L := by
        simpa [digitGhostStep, hie, hij] using hL
      exact h i L hL' hinh

/-- Consumer: `ledgerNE_fold`. -/
theorem ledgerNE_initial (S : Fin n → ProjD c) : LedgerNE (digitGhostInitial S) := by
  intro i L hL hinh
  by_cases hw : (S i).top.wCarry.isW = true
  · simp [digitGhostInitial, DigitGhost.initial, DigitLaneGhost.initial, digitLaneView, hw] at hL
    rw [← hL] at hinh
    simp at hinh
  · simp [digitGhostInitial, DigitGhost.initial, DigitLaneGhost.initial, digitLaneView, hw] at hL

/-- **`LedgerNE` along the audit fold of a drained start.**  Consumer: `writerAgeCoreOfBody`. -/
theorem ledgerNE_fold {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (w : List (Fin n)) :
    ∀ p : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      LedgerNE p.2.current → LedgerNE (w.foldl (widthDigitAuditNext ref) p).2.current := by
  induction w with
  | nil => intro p hi; exact hi
  | cons e w ih =>
    intro p hi
    simp only [List.foldl_cons]
    exact ih _ (ledgerNE_step ring _ _ _ e hi)

end Inv

end L3

#print axioms L3.ledgerNE_fold
