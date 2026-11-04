import Leader.L3.Top.MarkedCells
import Leader.L3.Top.SettledWorkSourceModel
import Leader.L3.Bank.RepairDigitCohortDomination

/-!
# The Q7 window rows are the T22 lane rows

The Q7 settled-work phase (`L3.MarkedCells`, `topClockPinnedSettledWorkPhase`) runs on the
abstract window `Cell` (input class `Inp`, carry class `Car = off | fresh | inh`) and source
tokens `Tok`, with the rows `pair`, `portClean`/`portAccept`, `srcPair`. The e-packet lane
(`L3.CohortDomination.cohortEdge`) runs on input shapes, carry-live bits and output shapes with
the rows `bankRepairDigitFinStep`, `cohortTermStep`, `bankRepairDigitDelStep`,
`bankRepairDigitPipeStep`. Under the projection `inOf`, `liveOf = (· ≠ off)`, `outOf`:

* `finRowSame`: a window edge `pair bx false` is the Fin row;
* `termRowSame`: the terminal window edge is the terminal row;
* `portRowSame`: the port edge (accept when the token is data and the border is empty and
  carry-free, otherwise carry-host cleanup), together with the source port row
  `srcPair false true`, is the delivery row;
* `pipeRowSame`: the source edge `srcPair bx false false` is the Pipe row.

So the local rows coincide; the carry class `fresh/inh` is the only extra datum of the window
(read from the audit ghost ledger, `L3.MarkedCells.absCar`), and it does not influence the
shapes. Checked by exhaustive case analysis.
-/

namespace L3.PacketMomentRows

set_option autoImplicit false

open L3.MarkedCells
open L3.RenewalReferenceClock
open L3.CohortDomination

/-- Input class to input shape. Consumer: every row identity. -/
def inOf : Inp → BankRepairDigitInSh
  | .e => .E
  | .pt => .P true
  | .pn => .P false
  | .st => .S true
  | .sn => .S false
  | .x => .X

/-- Carry class to carry-live bit. Consumer: every row identity. -/
def liveOf (c : Car) : Bool := decide (c ≠ .off)

/-- Source token to output shape. Consumer: `portRowSame`, `pipeRowSame`. -/
def outOf : Tok → BankRepairDigitOutSh
  | .e => .E
  | .u => .U
  | .dn => .D false
  | .dt => .D true

/-- **Window edge = Fin row.** Consumer: the port of the Q7 settled-work potential to the
e-packet lane (phase U of Lemma e-packet). -/
theorem finRowSame (bx : Bool) (x y : Cell) :
    (inOf (pair bx false x y).1.i, liveOf (pair bx false x y).1.c,
      inOf (pair bx false x y).2.i, liveOf (pair bx false x y).2.c) =
    bankRepairDigitFinStep bx (inOf x.i) (liveOf x.c) (inOf y.i) (liveOf y.c) := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  cases bx <;> cases xi <;> cases xc <;> cases yi <;> cases yc <;> decide

/-- **Terminal window edge = terminal row.** Consumer: as `finRowSame`. -/
theorem termRowSame (x : Cell) :
    (inOf (pair false true x { i := .e, c := .off }).1.i,
      liveOf (pair false true x { i := .e, c := .off }).1.c) =
    cohortTermStep (inOf x.i) (liveOf x.c) := by
  rcases x with ⟨xi, xc⟩
  cases xi <;> cases xc <;> decide

/-- **Port edge = delivery row.** The source port row `srcPair false true acc` with
`acc` = empty carry-free border, and on the border cell acceptance of a data token
(`portAccept`) or else carry-host cleanup (`portClean`). Consumer: as `finRowSame`. -/
theorem portRowSame (x : Tok) (c : Cell) :
    (outOf (srcPair false true (decide (c = { i := .e, c := .off })) x .e).1,
      inOf (if x.isD && decide (c = { i := .e, c := .off }) then
        portAccept (decide (x = .dt)) c else portClean c).i,
      liveOf (if x.isD && decide (c = { i := .e, c := .off }) then
        portAccept (decide (x = .dt)) c else portClean c).c) =
    bankRepairDigitDelStep (outOf x) (inOf c.i) (liveOf c.c) := by
  rcases c with ⟨ci, cc⟩
  cases x <;> cases ci <;> cases cc <;> decide

/-- **Source edge = Pipe row.** Consumer: as `finRowSame`. -/
theorem pipeRowSame (bx : Bool) (x y : Tok) :
    (outOf (srcPair bx false false x y).1, outOf (srcPair bx false false x y).2) =
    bankRepairDigitPipeStep bx (outOf x) (outOf y) := by
  cases bx <;> cases x <;> cases y <;> decide

/-! ### The lift: lane cells as window cells

A lane carry-live bit lifts to a fresh carry (the U phase starts after the inherited carries
have retired, so every live carry of the phase is generated after the cut). -/

/-- Input shape to input class. Consumer: `liftC`. -/
def cellIn : BankRepairDigitInSh → Inp
  | .E => .e
  | .X => .x
  | .P true => .pt
  | .P false => .pn
  | .S true => .st
  | .S false => .sn

/-- A lane cell as a window cell. Consumer: `L3.PacketMomentWindow.winOf`. -/
def liftC (i : BankRepairDigitInSh) (k : Bool) : Cell :=
  { i := cellIn i, c := if k then .fresh else .off }

/-- Output shape to source token. Consumer: `L3.PacketMomentWindow.srcLane`. -/
def tokOf : BankRepairDigitOutSh → Tok
  | .E => .e
  | .U => .u
  | .D false => .dn
  | .D true => .dt

/-- **The Fin row, lifted.** Consumer: `L3.PacketMomentWindow.laneWin`. -/
theorem finLift (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) :
    pair bx false (liftC ix kx) (liftC iy ky) =
      (liftC (bankRepairDigitFinStep bx ix kx iy ky).1 (bankRepairDigitFinStep bx ix kx iy ky).2.1,
       liftC (bankRepairDigitFinStep bx ix kx iy ky).2.2.1
         (bankRepairDigitFinStep bx ix kx iy ky).2.2.2) := by
  cases bx <;> cases kx <;> cases ky <;>
    rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    decide

/-- **The terminal row, lifted.** Consumer: `L3.PacketMomentWindow.laneWin`. -/
theorem termLift (ix : BankRepairDigitInSh) (kx : Bool) :
    (pair false true (liftC ix kx) { i := .e, c := .off }).1 =
      liftC (cohortTermStep ix kx).1 (cohortTermStep ix kx).2 := by
  cases kx <;> rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> decide

/-- **The Pipe row, lifted.** Consumer: `L3.PacketMomentWindow.laneSrc`. -/
theorem pipeLift (bx : Bool) (ox oy : BankRepairDigitOutSh) :
    srcPair bx false false (tokOf ox) (tokOf oy) =
      (tokOf (bankRepairDigitPipeStep bx ox oy).1, tokOf (bankRepairDigitPipeStep bx ox oy).2) := by
  cases bx <;> rcases ox with _ | _ | ⟨_ | _⟩ <;> rcases oy with _ | _ | ⟨_ | _⟩ <;> decide

/-- **The delivery row, lifted**: the source port row with acceptance read off the border
cell, and on the border cell acceptance or carry-host cleanup.
Consumer: `L3.PacketMomentWindow.laneWin`, `L3.PacketMomentWindow.laneSrc`. -/
theorem portLift (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool) :
    (srcPair false true (decide (liftC iy ky = { i := .e, c := .off })) (tokOf ox) .e).1 =
        tokOf (bankRepairDigitDelStep ox iy ky).1 ∧
      (if (tokOf ox).isD && decide (liftC iy ky = { i := .e, c := .off }) then
          portAccept (decide (tokOf ox = .dt)) (liftC iy ky)
        else portClean (liftC iy ky)) =
        liftC (bankRepairDigitDelStep ox iy ky).2.1 (bankRepairDigitDelStep ox iy ky).2.2 := by
  cases ky <;> rcases ox with _ | _ | ⟨_ | _⟩ <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    decide

/-- Lifted cells carry no inherited carry. Consumer: `L3.PacketMomentWindow`. -/
theorem liftC_ne_inh (i : BankRepairDigitInSh) (k : Bool) : (liftC i k).c ≠ .inh := by
  cases k <;> simp [liftC]

end L3.PacketMomentRows

#print axioms L3.PacketMomentRows.finRowSame
#print axioms L3.PacketMomentRows.termRowSame
#print axioms L3.PacketMomentRows.portRowSame
#print axioms L3.PacketMomentRows.pipeRowSame
#print axioms L3.PacketMomentRows.finLift
#print axioms L3.PacketMomentRows.termLift
#print axioms L3.PacketMomentRows.pipeLift
#print axioms L3.PacketMomentRows.portLift
