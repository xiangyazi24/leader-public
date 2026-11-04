import Leader.L3.Target

/-!
# R10c digit values: the carries of the lane replay

`digitLaneReplay` (`Target.lean`) updates the carry ghosts of the two endpoints of the edge by one of
six rows, mirroring the physical writer carry of `liveTopPair`: leader, terminal, blocked, success
(a new use is appended), launch (a ledger with one use) and idle.  This module computes the two
carry ghosts in each row.

Consumer: `Leader/L3/Width/DigitComparisonValuesLedger.lean`.
-/

namespace L3

set_option autoImplicit false

section Replay

variable {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat) (source dest : Fin n)
  (xv yv : DigitLaneView c) (gx gy : DigitLaneGhost c n)

/-- Leader row.  Consumer: `writerCarryStep`. -/
theorem replay_carry_root (hr : (xv.leader || yv.leader) = true) :
    (digitLaneReplay lane time source dest xv yv gx gy).x.carry =
        (if xv.carryLive = true then none else gx.carry) ∧
      (digitLaneReplay lane time source dest xv yv gx gy).y.carry =
        (if yv.carryLive = true then none else gy.carry) := by
  constructor <;> simp [digitLaneReplay, hr]

/-- Terminal row.  Consumer: `writerCarryStep`. -/
theorem replay_carry_terminal (hxl : xv.leader = false) (hyl : yv.leader = false)
    (hxc : xv.carryLive = true) (hm : yv.marker = true) :
    (digitLaneReplay lane time source dest xv yv gx gy).x.carry = none ∧
      (digitLaneReplay lane time source dest xv yv gx gy).y.carry = gy.carry := by
  constructor <;> simp [digitLaneReplay, hxl, hyl, hxc, hm]

/-- Blocked row, destination carry live.  Consumer: `writerCarryStep`. -/
theorem replay_carry_blockedCarry (hxl : xv.leader = false) (hyl : yv.leader = false)
    (hxc : xv.carryLive = true) (hm : yv.marker = false) (hyc : yv.carryLive = true) :
    (digitLaneReplay lane time source dest xv yv gx gy).x.carry = none ∧
      (digitLaneReplay lane time source dest xv yv gx gy).y.carry = gy.carry := by
  constructor <;> simp [digitLaneReplay, hxl, hyl, hxc, hm, hyc]

/-- Blocked row, destination without settled input.  Consumer: `writerCarryStep`. -/
theorem replay_carry_blockedInput (hxl : xv.leader = false) (hyl : yv.leader = false)
    (hxc : xv.carryLive = true) (hm : yv.marker = false) (his : yv.input.isS = false) :
    (digitLaneReplay lane time source dest xv yv gx gy).x.carry = none ∧
      (digitLaneReplay lane time source dest xv yv gx gy).y.carry = gy.carry := by
  constructor <;> simp [digitLaneReplay, hxl, hyl, hxc, hm, his]

/-- Success row: the ledger of the source gets one more use.  Consumer: `writerCarryStep`. -/
theorem replay_carry_success (hxl : xv.leader = false) (hyl : yv.leader = false)
    (hxc : xv.carryLive = true) (hm : yv.marker = false) (hyc : yv.carryLive = false)
    (his : yv.input.isS = true) :
    (digitLaneReplay lane time source dest xv yv gx gy).x.carry = none ∧
      (digitLaneReplay lane time source dest xv yv gx gy).y.carry =
        some { (gx.carry.getD { inherited := some (.missing { time := time, site := source, lane := lane } .carry), uses := [] }) with
          uses := (gx.carry.getD { inherited := some (.missing { time := time, site := source, lane := lane } .carry), uses := [] }).uses ++
            [{ time := time, target := dest, operand := gy.input, value := inV c yv.input,
               tail := inT yv.input, targetDigit := yv.digit, carryIn := xv.carryBit,
               errorIn := xv.carryError }] } := by
  constructor <;> simp [digitLaneReplay, hxl, hyl, hxc, hm, hyc, his]

/-- Launch row: a ledger with the first use, carry-in one.  Consumer: `writerCarryStep`. -/
theorem replay_carry_launch (hxl : xv.leader = false) (hyl : yv.leader = false)
    (hxc : xv.carryLive = false) (hxm : xv.marker = true) (hxs : xv.input.isS = true) :
    (digitLaneReplay lane time source dest xv yv gx gy).x.carry =
        some { inherited := none,
               uses := [{ time := time, target := source, operand := gx.input,
                          value := inV c xv.input, tail := inT xv.input,
                          targetDigit := xv.digit, carryIn := true, errorIn := false }] } ∧
      (digitLaneReplay lane time source dest xv yv gx gy).y.carry = gy.carry := by
  constructor <;> simp [digitLaneReplay, hxl, hyl, hxc, hxm, hxs]

/-- Idle row, source not a delimiter.  Consumer: `writerCarryStep`. -/
theorem replay_carry_idleMarker (hxl : xv.leader = false) (hyl : yv.leader = false)
    (hxc : xv.carryLive = false) (hxm : xv.marker = false) :
    (digitLaneReplay lane time source dest xv yv gx gy).x.carry = gx.carry ∧
      (digitLaneReplay lane time source dest xv yv gx gy).y.carry = gy.carry := by
  constructor <;> simp [digitLaneReplay, hxl, hyl, hxc, hxm]

/-- Idle row, source without settled input.  Consumer: `writerCarryStep`. -/
theorem replay_carry_idleInput (hxl : xv.leader = false) (hyl : yv.leader = false)
    (hxc : xv.carryLive = false) (hxs : xv.input.isS = false) :
    (digitLaneReplay lane time source dest xv yv gx gy).x.carry = gx.carry ∧
      (digitLaneReplay lane time source dest xv yv gx gy).y.carry = gy.carry := by
  constructor <;> simp [digitLaneReplay, hxl, hyl, hxc, hxs]

end Replay

end L3

#print axioms L3.replay_carry_success
#print axioms L3.replay_carry_launch
