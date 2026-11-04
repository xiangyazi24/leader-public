import Leader.L3.Width.DigitComparisonValuesRow

/-!
# R10c digit values: the writer-carry rows of `liveTopPair`

The writer carry of `liveTopPair` (`CertRows.lean` 636-655, block WC) moves by one of five rows:

* leader row: a live carry next to the leader is dropped;
* terminal row: a live carry whose right neighbour is a delimiter is dropped;
* blocked row: a live carry whose right neighbour holds a carry, or no settled input, is dropped;
* advance row: see `liveTop_advance_carry` (`WidthDigitComparisonValuesRow`);
* launch row: a delimiter source without carry holding a settled input starts the carry
  `W (v + 1 = topA)`;
* idle: otherwise both carries stay.

Consumer: `Leader/L3/Width/DigitComparisonValuesLedger.lean` (the carry chain of a writer ledger).
-/

namespace L3

set_option autoImplicit false

section Carry

variable (c : Compiled) (ox oy : Agent c) (bX bY : Bool)

/-- Leader row.  Consumer: `writerCarryStep`. -/
theorem liveTop_carry_root (h : ox.l = true ∨ oy.l = true) :
    (liveTopPair c ox oy bX bY).x.wCarry = (if ox.wCarry.isW = true then .OFF else ox.wCarry) ∧
      (liveTopPair c ox oy bX bY).y.wCarry = (if oy.wCarry.isW = true then .OFF else oy.wCarry) := by
  rcases h with h | h <;>
    constructor <;>
    simp [liveTopPair, h]

/-- Terminal row.  Consumer: `writerCarryStep`. -/
theorem liveTop_carry_terminal (cc : Bool) (hxl : ox.l = false) (hyl : oy.l = false)
    (hbY : bY = true) (hw : ox.wCarry = .W cc) :
    (liveTopPair c ox oy bX bY).x.wCarry = .OFF ∧
      (liveTopPair c ox oy bX bY).y.wCarry = oy.wCarry := by
  constructor <;>
    simp [liveTopPair, hxl, hyl, hbY, hw, WCarry.isW, topTerminal]

/-- Blocked row, destination carry live.  Consumer: `writerCarryStep`. -/
theorem liveTop_carry_blockedCarry (cc c' : Bool) (hxl : ox.l = false) (hyl : oy.l = false)
    (hbY : bY = false) (hw : ox.wCarry = .W cc) (hy : oy.wCarry = .W c') :
    (liveTopPair c ox oy bX bY).x.wCarry = .OFF ∧
      (liveTopPair c ox oy bX bY).y.wCarry = oy.wCarry := by
  constructor <;>
    simp [liveTopPair, hxl, hyl, hbY, hw, hy, WCarry.isW, WCarry.isOff, topTerminal]

/-- Blocked row, destination without settled input.  Consumer: `writerCarryStep`. -/
theorem liveTop_carry_blockedInput (cc : Bool) (hxl : ox.l = false) (hyl : oy.l = false)
    (hbY : bY = false) (hw : ox.wCarry = .W cc) (hs : oy.wIn.isS = false) :
    (liveTopPair c ox oy bX bY).x.wCarry = .OFF ∧
      (liveTopPair c ox oy bX bY).y.wCarry = oy.wCarry := by
  constructor <;>
    simp [liveTopPair, hxl, hyl, hbY, hw, hs, WCarry.isW, WCarry.isOff, topTerminal]

/-- Launch row.  Consumer: `writerCarryStep`. -/
theorem liveTop_carry_launch (v : Fin c.topA) (T : Bool)
    (hxl : ox.l = false) (hyl : oy.l = false) (hbX : bX = true)
    (hw : ox.wCarry = .OFF) (hs : ox.wIn = .S v T) :
    (liveTopPair c ox oy bX bY).x.wCarry = .W (v.val + 1 == c.topA) ∧
      (liveTopPair c ox oy bX bY).y.wCarry = oy.wCarry := by
  constructor <;>
    simp [liveTopPair, hxl, hyl, hbX, hw, hs, WCarry.isW, WCarry.isOff, InTok.isS, topBorder,
      inV, WC]

/-- Idle row, source not a delimiter.  Consumer: `writerCarryStep`. -/
theorem liveTop_carry_idleBeta (hxl : ox.l = false) (hyl : oy.l = false) (hbX : bX = false)
    (hw : ox.wCarry = .OFF) :
    (liveTopPair c ox oy bX bY).x.wCarry = .OFF ∧
      (liveTopPair c ox oy bX bY).y.wCarry = oy.wCarry := by
  constructor <;>
    simp [liveTopPair, hxl, hyl, hbX, hw, WCarry.isW, WCarry.isOff, topBorder]

/-- Idle row, source without settled input.  Consumer: `writerCarryStep`. -/
theorem liveTop_carry_idleInput (hxl : ox.l = false) (hyl : oy.l = false)
    (hw : ox.wCarry = .OFF) (hs : ox.wIn.isS = false) :
    (liveTopPair c ox oy bX bY).x.wCarry = .OFF ∧
      (liveTopPair c ox oy bX bY).y.wCarry = oy.wCarry := by
  constructor <;>
    simp [liveTopPair, hxl, hyl, hw, hs, WCarry.isW, WCarry.isOff, topBorder]

end Carry

end L3

#print axioms L3.liveTop_carry_launch
#print axioms L3.liveTop_carry_blockedCarry
