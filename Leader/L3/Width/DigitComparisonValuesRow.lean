import Leader.L3.CertRows

/-!
# R10c digit values: the digit-write rows of `liveTopPair`

The top machine writes the digit `d` of a site only through three rows of `liveTopPair`
(`composed-full.mjs:503-698`, `CertRows.lean` 605-758), each gated by the OLD dirty bit of the
written cell (the emission-first dirty gate: a dirty cell keeps its digit and its report is
cleared):

* the writer advance at the destination: a live writer carry `W cc` at the source, the
  destination without carry holding a settled input `S v _`, both off the leader and the
  destination not a delimiter, stores `digitMod (v + cc)` and keeps the carry `W (cc && v + 1 = topA)`;
* the writer launch at the source: a delimiter source without carry holding a settled input
  `S v _` stores `digitMod (v + 1)` and starts the carry `W (v + 1 = topA)`;
* the base write at the source: a source with base label `ZERO` stores `0`.

Consumer: `Leader/L3/Width/DigitComparisonValues.lean` (value step of a writer completion).
-/

namespace L3

set_option autoImplicit false

section Rows

variable (c : Compiled) (ox oy : Agent c) (bX bY : Bool)

/-- **The writer advance row.**  The destination digit is the settled input plus the carry, unless
the destination is dirty.

Consumer: `writerAdvanceWrite`. -/
theorem liveTop_advance_d (cc : Bool) (v : Fin c.topA) (T : Bool)
    (hxl : ox.l = false) (hyl : oy.l = false) (hbY : bY = false)
    (hw : ox.wCarry = .W cc) (hoff : oy.wCarry = .OFF) (hs : oy.wIn = .S v T) :
    (liveTopPair c ox oy bX bY).y.d =
      (if oy.topDirty = true then oy.d else c.digitMod (v.val + (if cc then 1 else 0))) := by
  cases hd : oy.topDirty <;>
    simp [liveTopPair, hxl, hyl, hbY, hw, hoff, hs, hd, WCarry.isW, WCarry.isOff, InTok.isS,
      Compiled.digitMod, topTerminal, inV, wcC]

/-- The advance row keeps the carry going.

Consumer: `carryInv_pair` (WidthDigitComparisonValuesLedger). -/
theorem liveTop_advance_carry (cc : Bool) (v : Fin c.topA) (T : Bool)
    (hxl : ox.l = false) (hyl : oy.l = false) (hbY : bY = false)
    (hw : ox.wCarry = .W cc) (hoff : oy.wCarry = .OFF) (hs : oy.wIn = .S v T) :
    (liveTopPair c ox oy bX bY).y.wCarry = .W (cc && (v.val + 1 == c.topA)) ∧
      (liveTopPair c ox oy bX bY).x.wCarry = .OFF := by
  constructor <;>
    simp [liveTopPair, hxl, hyl, hbY, hw, hoff, hs, WCarry.isW, WCarry.isOff, InTok.isS,
      topTerminal, inV, wcC, WC]

/-- **The writer launch row.**  A delimiter source without carry holding a settled input stores the
input plus one, unless it is dirty.

Consumer: `writerLaunchWrite`. -/
theorem liveTop_launch_d (v : Fin c.topA) (T : Bool)
    (hxl : ox.l = false) (hyl : oy.l = false) (hbX : bX = true)
    (hbase : ox.wBase ≠ .ZERO) (hw : ox.wCarry = .OFF) (hs : ox.wIn = .S v T) :
    (liveTopPair c ox oy bX bY).x.d =
      (if ox.topDirty = true then ox.d else c.digitMod (v.val + 1)) := by
  cases hd : ox.topDirty <;> cases hb : ox.wBase
  all_goals first
    | exact absurd hb hbase
    | simp [liveTopPair, hxl, hyl, hbX, hw, hs, hd, hb, WCarry.isW, WCarry.isOff, InTok.isS,
        Compiled.digitMod, topTerminal, topBorder, inV]

/-- **The base write row.**  A source with base label `ZERO` stores the digit zero, unless it is
dirty.

Consumer: `writerBaseWrite`. -/
theorem liveTop_base_d (hxl : ox.l = false) (hyl : oy.l = false) (hb : ox.wBase = .ZERO) :
    (liveTopPair c ox oy bX bY).x.d = (if ox.topDirty = true then ox.d else c.zeroDigit) := by
  cases hd : ox.topDirty <;>
    simp [liveTopPair, hxl, hyl, hb, hd]

end Rows

end L3

#print axioms L3.liveTop_advance_d
#print axioms L3.liveTop_advance_carry
#print axioms L3.liveTop_launch_d
#print axioms L3.liveTop_base_d
