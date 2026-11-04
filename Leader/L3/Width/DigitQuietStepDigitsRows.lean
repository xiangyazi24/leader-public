import Leader.L3.Width.DigitQuietStepGlue
import Leader.L3.Width.DigitQuietStepArith

/-!
# The digit rows of `liveTopPair`

The digit field of a side after one letter: the digit changes only by the three writes of the top
machine, each dropped when the side is dirty (`CertRows.lean` 605-758, `dX`, `dY`):

* BASE at the left side: left and right non-leaders, `wBase = ZERO`, writes `zeroDigit` (priority
  over the launch);
* LAUNCH at the left side: left a non-leader marker without writer carry holding a settled input
  `S v _`, right a non-leader, writes `digitMod (v + 1)`;
* ADVANCE at the right side: left with a live writer carry, left and right non-leaders, right not a
  marker, without carry and holding `S v _`, writes `digitMod (v + carry)`.

`digits_phi_left`, `digits_phi_right` state this for the projected letter `phiD` under `QWord` (the
resolved markers are the old ones).

Consumer: `WidthDigitQuietStepDigits` (`digits_kept`).
-/

namespace L3.DigitQuiet

open L3
open L3.AcceptedReceipts

set_option autoImplicit false

variable {c : Compiled}

/-- The digit rows (`dX`, `dY`) of `liveTopPair` with the base and writer-carry rows they read,
verbatim with their look flags, so that a digit lemma unfolds only these rows. -/
private def digitsBlock (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) :
    Fin c.topA × Fin c.topA :=
  let a := c.topA
  let wox : Agent c := { ox with beta := betaX }
  let woy : Agent c := { oy with beta := betaY }
  let rootX := ox.l
  let rootY := oy.l
  let wTerminal := topTerminal wox woy
  -- LOOK: writer carry and checker carry.
  let wc2Live := ox.wCarry.isW && !wTerminal
  let wc2Success := wc2Live && oy.wCarry.isOff && oy.wIn.isS
  let wc3 := topBorder wox && ox.wCarry.isOff && ox.wIn.isS && !rootY
  -- WB.  (wBaseX, wBaseY, baseWrite)
  let wb : WBase × WBase × Option (Fin c.topA) :=
    if rootY then (.NONE, oy.wBase, none)
    else if rootX && !rootY then
      (.NONE, (if oy.wBase == .NONE then .SEEK else oy.wBase), none)
    else if !rootX && ox.wBase == .ZERO then
      (.NONE, (if !rootY && !woy.beta && oy.wBase == .NONE then .ZERO else oy.wBase),
       some c.zeroDigit)
    else if !rootX && ox.wBase == .SEEK then
      (.NONE, (if !rootY && oy.wBase == .NONE then (if woy.beta then .ZERO else .SEEK) else oy.wBase),
       none)
    else (ox.wBase, oy.wBase, none)
  let wBaseX := wb.1
  let wBaseY := wb.2.1
  let baseWrite := wb.2.2
  -- WC look/commit.  (wCarryX, wCarryY, launch, advance)
  let wcr : WCarry × WCarry × Option (Fin c.topA) × Option (Fin c.topA) :=
    if rootX || rootY then
      ((if ox.wCarry.isW then .OFF else ox.wCarry), (if oy.wCarry.isW then .OFF else oy.wCarry),
       none, none)
    else if ox.wCarry.isW then
      if !wTerminal && wc2Success then
        let v := (inV c oy.wIn).val
        let cc := wcC ox.wCarry
        (.OFF, WC (cc && v + 1 == a), none, some (c.digitMod (v + (if cc then 1 else 0))))
      else (.OFF, oy.wCarry, none, none)
    else if wc3 then
      let v := (inV c ox.wIn).val
      (WC (v + 1 == a), oy.wCarry, some (c.digitMod (v + 1)), none)
    else (ox.wCarry, oy.wCarry, none, none)
  let wCarryX := wcr.1
  let wCarryY := wcr.2.1
  let launch := wcr.2.2.1
  let advance := wcr.2.2.2
  -- WD, with emission-first dirty gate.
  let propX : Option (Fin c.topA) :=
    match baseWrite with
    | some v => some v
    | none => launch
  let propY : Option (Fin c.topA) := advance
  let dX : Fin c.topA :=
    match propX with
    | some v => if !ox.topDirty then v else ox.d
    | none => ox.d
  let dY : Fin c.topA :=
    match propY with
    | some v => if !oy.topDirty then v else oy.d
    | none => oy.d
  (dX, dY)

private theorem liveTopPair_x_d (ox oy : Agent c) (betaX betaY : Bool) :
    (liveTopPair c ox oy betaX betaY).x.d = (digitsBlock c ox oy betaX betaY).1 := rfl

private theorem liveTopPair_y_d (ox oy : Agent c) (betaX betaY : Bool) :
    (liveTopPair c ox oy betaX betaY).y.d = (digitsBlock c ox oy betaX betaY).2 := rfl

/-- **The digit of the left side after the top machine** (old markers as resolved markers): kept,
or the dirty-gated BASE / LAUNCH write.  Consumer: `digits_phi_left`. -/
theorem digits_row_left (ox oy : Agent c) :
    (liveTopPair c ox oy ox.beta oy.beta).x.d =
      if ox.topDirty = true then ox.d
      else if ox.l = false ∧ oy.l = false ∧ ox.wBase = .ZERO then c.zeroDigit
      else if ox.l = false ∧ oy.l = false ∧ ox.beta = true ∧ ox.wCarry = .OFF ∧
          ox.wIn.isS = true then c.digitMod ((inV c ox.wIn).val + 1)
      else ox.d := by
  rcases ox with ⟨l,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,beta,d,_,_,_,_,_,_,_,wb,_,wi,wc,_,_,_,td⟩
  rcases oy with ⟨l2,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,beta2,d2,_,_,_,_,_,_,_,wb2,_,wi2,wc2,_,_,_,td2⟩
  rw [liveTopPair_x_d]
  cases l <;> cases l2 <;> cases beta <;> cases td <;> cases wb <;> cases wc <;> cases wi <;>
    simp [digitsBlock, topBorder, WCarry.isW, WCarry.isOff, InTok.isS]

/-- **The digit of the right side after the top machine**: kept, or the dirty-gated ADVANCE write.
Consumer: `digits_phi_right`. -/
theorem digits_row_right (ox oy : Agent c) :
    (liveTopPair c ox oy ox.beta oy.beta).y.d =
      if oy.topDirty = true then oy.d
      else if ox.l = false ∧ oy.l = false ∧ ox.wCarry.isW = true ∧ oy.beta = false ∧
          oy.wCarry = .OFF ∧ oy.wIn.isS = true then
        c.digitMod ((inV c oy.wIn).val + (if wcC ox.wCarry = true then 1 else 0))
      else oy.d := by
  rcases ox with ⟨l,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,beta,d,_,_,_,_,_,_,_,wb,_,wi,wc,_,_,_,td⟩
  rcases oy with ⟨l2,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,beta2,d2,_,_,_,_,_,_,_,wb2,_,wi2,wc2,_,_,_,td2⟩
  rw [liveTopPair_y_d]
  cases l <;> cases l2 <;> cases beta <;> cases beta2 <;> cases td2 <;> cases wc <;> cases wc2 <;>
    cases wi2 <;>
    simp [digitsBlock, topBorder, topTerminal, WCarry.isW, WCarry.isOff, InTok.isS, wcC]

/-- Under `QWord` the machine on the projected pair reads the old markers.  Consumer:
`digits_phi_left`, `digits_phi_right`. -/
theorem digits_topD_old (x y : ProjD c)
    (hbX : (pairW x.word y.word).1.beta = x.word.beta)
    (hbY : (pairW x.word y.word).2.beta = y.word.beta) :
    topD x y = liveTopPair c x.lift y.lift x.lift.beta y.lift.beta := by
  show liveTopPair c x.lift y.lift (pairW x.word y.word).1.beta (pairW x.word y.word).2.beta =
    liveTopPair c x.lift y.lift x.lift.beta y.lift.beta
  rw [hbX, hbY]
  rfl

/-- **The digit of the left endpoint after a letter.**  Consumer: `digits_kept`. -/
theorem digits_phi_left {n : Nat} (ring : DirectedRing n) (S : Fin n → ProjD c)
    (hW : QWord ring (wordProjection S)) (e : Fin n) (hne : ring.rightNeighbor e ≠ e) :
    ((phiD ring S e) e).top.d =
      if (S e).top.topDirty = true then (S e).top.d
      else if (S e).word.native.l = false ∧ (S (ring.rightNeighbor e)).word.native.l = false ∧
          (S e).top.wBase = .ZERO then c.zeroDigit
      else if (S e).word.native.l = false ∧ (S (ring.rightNeighbor e)).word.native.l = false ∧
          (S e).word.beta = true ∧ (S e).top.wCarry = .OFF ∧ (S e).top.wIn.isS = true then
        c.digitMod ((inV c (S e).top.wIn).val + 1)
      else (S e).top.d := by
  obtain ⟨hbX, hbY⟩ := resolved_betas ring S hW e hne
  rw [phiD_at_left]
  show (topD (S e) (S (ring.rightNeighbor e))).x.d = _
  rw [digits_topD_old _ _ hbX hbY]
  exact digits_row_left (S e).lift (S (ring.rightNeighbor e)).lift

/-- **The digit of the right endpoint after a letter.**  Consumer: `digits_kept`. -/
theorem digits_phi_right {n : Nat} (ring : DirectedRing n) (S : Fin n → ProjD c)
    (hW : QWord ring (wordProjection S)) (e : Fin n) (hne : ring.rightNeighbor e ≠ e) :
    ((phiD ring S e) (ring.rightNeighbor e)).top.d =
      if (S (ring.rightNeighbor e)).top.topDirty = true then (S (ring.rightNeighbor e)).top.d
      else if (S e).word.native.l = false ∧ (S (ring.rightNeighbor e)).word.native.l = false ∧
          (S e).top.wCarry.isW = true ∧ (S (ring.rightNeighbor e)).word.beta = false ∧
          (S (ring.rightNeighbor e)).top.wCarry = .OFF ∧
          (S (ring.rightNeighbor e)).top.wIn.isS = true then
        c.digitMod ((inV c (S (ring.rightNeighbor e)).top.wIn).val +
          (if wcC (S e).top.wCarry = true then 1 else 0))
      else (S (ring.rightNeighbor e)).top.d := by
  obtain ⟨hbX, hbY⟩ := resolved_betas ring S hW e hne
  rw [phiD_at_right ring S e hne]
  show (topD (S e) (S (ring.rightNeighbor e))).y.d = _
  rw [digits_topD_old _ _ hbX hbY]
  exact digits_row_right (S e).lift (S (ring.rightNeighbor e)).lift

end L3.DigitQuiet

#print axioms L3.DigitQuiet.digits_row_left
#print axioms L3.DigitQuiet.digits_row_right
#print axioms L3.DigitQuiet.digits_phi_left
#print axioms L3.DigitQuiet.digits_phi_right
