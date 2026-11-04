import Leader.L3.Bank.RepairDigitCloseReceipt

/-!
# T32 item 1: value-carrying rows on `liveTopPair`

The T18 shape rows (`bankRepairDigitPipeStep`, `bankRepairDigitDelStep`, `bankRepairDigitFinStep`,
`cohortTermStep`) forget the digit carried by a packet. This module states the same rows on the
literal tokens, values included:

* `vPipe`: a data packet `D v T` moves into an empty right output with its value; a read slot `U`
  becomes `D d β` with the cell's digit `d` and border bit `β`.
* `vDel`: an accepted packet `D v T` becomes the delimiter's pending input `P v T`.
* `vFin`: pending inputs `P v T` move and settle (`S v T`) with their values.
* `vTerm`: the last target input settles `P v false ↦ S v false`.

Each row is proved for both lanes on `liveTopPair` (`writer…V`, `comparison…V`) and lane
generically on projected records (`pipeValD`, `delValD`, `finValD`, `termValD`).
-/

namespace L3.ValueRows

set_option autoImplicit false

open L3.RenewalReferenceClock

/-! ### The valued steps -/

section Steps

variable {A : Nat}

/-- Output motion across an edge whose right end is internal, with values. -/
def vPipe (bx : Bool) (d : Fin A) (ox oy : OutTok A) : OutTok A × OutTok A :=
  match ox with
  | .D v T => match oy with
    | .E => ((if T then .U else .E), .D v T)
    | _ => (.D v T, oy)
  | .U => (.D d bx, oy)
  | .E => ((if bx then .U else .E), oy)

/-- The delivery edge into a delimiter, with values: new `(output x, input y, live y)`. -/
def vDel (d : Fin A) (ox : OutTok A) (iy : InTok A) (ky : Bool) : OutTok A × InTok A × Bool :=
  match ox with
  | .D v T => if ky then (.D v T, .E, true)
            else match iy with
              | .E => ((if T then .U else .E), .P v T, false)
              | _ => (.D v T, iy, false)
  | .U => (.D d false, (if ky then .E else iy), ky)
  | .E => (.E, (if ky then .E else iy), ky)

/-- One lane across an edge whose right end is internal, with values: new
`(input x, live x, input y, live y)`. -/
def vFin (bx : Bool) (ix : InTok A) (kx : Bool) (iy : InTok A) (ky : Bool) :
    InTok A × Bool × InTok A × Bool :=
  if kx then
    (if ky then (.E, false, .E, true)
     else match iy with
       | .S _ _ => (.E, false, .E, true)
       | _ => (.E, false, iy, false))
  else if ky then
    match ix with
    | .E => (.E, false, .E, true)
    | .X => (.E, false, .E, true)
    | .P v T => (.P v T, false, .E, true)
    | .S v T => if bx then (.E, true, .E, true)
              else if T then (.X, false, .E, true) else (.S v T, false, .E, true)
  else
    match ix with
    | .E => (.E, false, iy, false)
    | .X => (.E, false, (match iy with | .S _ _ => .X | _ => iy), false)
    | .S v T => if bx then (.E, true, iy, false)
              else if T then (.X, false, iy, false) else (.S v T, false, iy, false)
    | .P v T => match iy with
      | .E => (.E, false, .P v T, false)
      | .S v' T' => (.S v T, false, .S v' T', false)
      | _ => (.P v T, false, iy, false)

/-- The terminal edge, with values: new `(input x, live x)`. -/
def vTerm (ix : InTok A) (kx : Bool) : InTok A × Bool :=
  if kx then (.E, false)
  else
    match ix with
    | .E => (.E, false)
    | .X => (.E, false)
    | .S v T => ((if T then .X else .S v T), false)
    | .P v T => ((if T then .E else .S v false), false)

end Steps

/-! ### The rows on `liveTopPair` -/

section Agents

theorem writerPipeV (c : Compiled) (ox oy : Agent c)
    (hl : ox.l = false) (hly : oy.l = false) (hby : oy.beta = false) :
    ((liveTopPair c ox oy).x.wOut, (liveTopPair c ox oy).y.wOut) =
      vPipe ox.beta ox.d ox.wOut oy.wOut := by
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut]
  cases hb : ox.beta <;> cases ho : ox.wOut <;> cases ho2 : oy.wOut <;>
    simp [liveTopWC, liveTopWI, liveTopWO,
      hl, hly, hby, hb, ho, ho2, OutTok.isD,
      OutTok.isU, OutTok.isE, outT, outV, vPipe] <;>
    (repeat' split) <;> simp_all

theorem comparisonPipeV (c : Compiled) (ox oy : Agent c)
    (hl : ox.l = false) (hly : oy.l = false) (hby : oy.beta = false) :
    ((liveTopPair c ox oy).x.qOut, (liveTopPair c ox oy).y.qOut) =
      vPipe ox.beta ox.d ox.qOut oy.qOut := by
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut]
  cases hb : ox.beta <;> cases ho : ox.qOut <;> cases ho2 : oy.qOut <;>
    simp [liveTopQC, liveTopQI, liveTopQO,
      hl, hly, hby, hb, ho, ho2, OutTok.isD,
      OutTok.isU, OutTok.isE, outT, outV, vPipe] <;>
    (repeat' split) <;> simp_all

theorem writerDelV (c : Compiled) (ox oy : Agent c)
    (hl : ox.l = false) (hly : oy.l = false) (hbx : ox.beta = false) (hby : oy.beta = true) :
    ((liveTopPair c ox oy).x.wOut, (liveTopPair c ox oy).y.wIn,
      (liveTopPair c ox oy).y.wCarry.isW) =
    vDel ox.d ox.wOut oy.wIn oy.wCarry.isW := by
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut]
  cases ho : ox.wOut <;>
    rcases hi : ox.wIn with _ | _ | ⟨v, _ | _⟩ | ⟨v, _ | _⟩ <;> cases hc : ox.wCarry <;>
    cases hi2 : oy.wIn <;> cases hc2 : oy.wCarry <;>
    simp [liveTopWC, liveTopWI, liveTopWO,
      hl, hly, hby, hbx, ho, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, WCarry.isOff, WCarry.isW, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, inV, outT, outV,
      vDel] <;>
    (repeat' split) <;> simp_all

theorem comparisonDelV (c : Compiled) (ox oy : Agent c)
    (hl : ox.l = false) (hly : oy.l = false) (hbx : ox.beta = false) (hby : oy.beta = true) :
    ((liveTopPair c ox oy).x.qOut, (liveTopPair c ox oy).y.qIn,
      (liveTopPair c ox oy).y.qCarry.isL) =
    vDel ox.d ox.qOut oy.qIn oy.qCarry.isL := by
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut]
  cases ho : ox.qOut <;>
    rcases hi : ox.qIn with _ | _ | ⟨v, _ | _⟩ | ⟨v, _ | _⟩ <;> cases hc : ox.qCarry <;>
    cases hi2 : oy.qIn <;> cases hc2 : oy.qCarry <;>
    simp [liveTopQC, liveTopQI, liveTopQO,
      hl, hly, hby, hbx, ho, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, QCarry.isOff, QCarry.isL, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, inV, outT, outV,
      vDel] <;>
    (repeat' split) <;> simp_all

theorem writerFinV (c : Compiled) (ox oy : Agent c)
    (hl : ox.l = false) (hly : oy.l = false) (hby : oy.beta = false) :
    ((liveTopPair c ox oy).x.wIn, (liveTopPair c ox oy).x.wCarry.isW,
      (liveTopPair c ox oy).y.wIn, (liveTopPair c ox oy).y.wCarry.isW) =
    vFin ox.beta ox.wIn ox.wCarry.isW oy.wIn oy.wCarry.isW := by
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut]
  cases hb : ox.beta <;> cases hi : ox.wIn <;> cases hc : ox.wCarry <;>
    cases hi2 : oy.wIn <;> cases hc2 : oy.wCarry <;>
    simp [liveTopWC, liveTopWI, liveTopWO,
      hl, hly, hby, hb, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, WCarry.isOff, WCarry.isW, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, inV,
      vFin, WC] <;>
    (repeat' split) <;> simp_all

theorem comparisonFinV (c : Compiled) (ox oy : Agent c)
    (hl : ox.l = false) (hly : oy.l = false) (hby : oy.beta = false) :
    ((liveTopPair c ox oy).x.qIn, (liveTopPair c ox oy).x.qCarry.isL,
      (liveTopPair c ox oy).y.qIn, (liveTopPair c ox oy).y.qCarry.isL) =
    vFin ox.beta ox.qIn ox.qCarry.isL oy.qIn oy.qCarry.isL := by
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut]
  cases hb : ox.beta <;> cases hi : ox.qIn <;> cases hc : ox.qCarry <;>
    cases hi2 : oy.qIn <;> cases hc2 : oy.qCarry <;>
    simp [liveTopQC, liveTopQI, liveTopQO,
      hl, hly, hby, hb, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, QCarry.isOff, QCarry.isL, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, inV,
      vFin, QC] <;>
    (repeat' split) <;> simp_all

theorem writerTermV (c : Compiled) (ox oy : Agent c)
    (hl : ox.l = false) (hly : oy.l = false) (hbx : ox.beta = false) (hby : oy.beta = true) :
    ((liveTopPair c ox oy).x.wIn, (liveTopPair c ox oy).x.wCarry.isW) =
      vTerm ox.wIn ox.wCarry.isW := by
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut]
  cases ho : ox.wOut <;>
    rcases hi : ox.wIn with _ | _ | ⟨v, _ | _⟩ | ⟨v, _ | _⟩ <;> cases hc : ox.wCarry <;>
    cases hi2 : oy.wIn <;> cases hc2 : oy.wCarry <;>
    simp [liveTopWC, liveTopWI, liveTopWO,
      hl, hly, hby, hbx, ho, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, WCarry.isOff, WCarry.isW, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, inV, outT,
      vTerm] <;>
    (repeat' split) <;> simp_all

theorem comparisonTermV (c : Compiled) (ox oy : Agent c)
    (hl : ox.l = false) (hly : oy.l = false) (hbx : ox.beta = false) (hby : oy.beta = true) :
    ((liveTopPair c ox oy).x.qIn, (liveTopPair c ox oy).x.qCarry.isL) =
      vTerm ox.qIn ox.qCarry.isL := by
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut]
  cases ho : ox.qOut <;>
    rcases hi : ox.qIn with _ | _ | ⟨v, _ | _⟩ | ⟨v, _ | _⟩ <;> cases hc : ox.qCarry <;>
    cases hi2 : oy.qIn <;> cases hc2 : oy.qCarry <;>
    simp [liveTopQC, liveTopQI, liveTopQO,
      hl, hly, hby, hbx, ho, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, QCarry.isOff, QCarry.isL, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, inV, outT,
      vTerm] <;>
    (repeat' split) <;> simp_all

end Agents

/-! ### Lane-generic rows on projected records -/

section Proj

variable (c : Compiled) (lane : DigitLane) (x y : ProjD c)

theorem pipeValD (hl : x.word.native.l = false) (hly : y.word.native.l = false)
    (hby : y.word.beta = false) :
    (bankRepairDigitLaneOut lane (bankRepairDigitTopPairOf c x y).x,
      bankRepairDigitLaneOut lane (bankRepairDigitTopPairOf c x y).y) =
    vPipe x.word.beta x.top.d (bankRepairDigitLaneOut lane x.top)
      (bankRepairDigitLaneOut lane y.top) := by
  cases lane
  · exact writerPipeV c x.lift y.lift hl hly hby
  · exact comparisonPipeV c x.lift y.lift hl hly hby

theorem delValD (hl : x.word.native.l = false) (hly : y.word.native.l = false)
    (hbx : x.word.beta = false) (hby : y.word.beta = true) :
    (bankRepairDigitLaneOut lane (bankRepairDigitTopPairOf c x y).x,
      bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).y,
      bankRepairDigitLaneLive lane (bankRepairDigitTopPairOf c x y).y) =
    vDel x.top.d (bankRepairDigitLaneOut lane x.top) (bankRepairDigitLaneIn lane y.top)
      (bankRepairDigitLaneLive lane y.top) := by
  cases lane
  · exact writerDelV c x.lift y.lift hl hly hbx hby
  · exact comparisonDelV c x.lift y.lift hl hly hbx hby

theorem finValD (hl : x.word.native.l = false) (hly : y.word.native.l = false)
    (hby : y.word.beta = false) :
    (bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).x,
      bankRepairDigitLaneLive lane (bankRepairDigitTopPairOf c x y).x,
      bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).y,
      bankRepairDigitLaneLive lane (bankRepairDigitTopPairOf c x y).y) =
    vFin x.word.beta (bankRepairDigitLaneIn lane x.top) (bankRepairDigitLaneLive lane x.top)
      (bankRepairDigitLaneIn lane y.top) (bankRepairDigitLaneLive lane y.top) := by
  cases lane
  · exact writerFinV c x.lift y.lift hl hly hby
  · exact comparisonFinV c x.lift y.lift hl hly hby

theorem termValD (hl : x.word.native.l = false) (hly : y.word.native.l = false)
    (hbx : x.word.beta = false) (hby : y.word.beta = true) :
    (bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).x,
      bankRepairDigitLaneLive lane (bankRepairDigitTopPairOf c x y).x) =
    vTerm (bankRepairDigitLaneIn lane x.top) (bankRepairDigitLaneLive lane x.top) := by
  cases lane
  · exact writerTermV c x.lift y.lift hl hly hbx hby
  · exact comparisonTermV c x.lift y.lift hl hly hbx hby

end Proj

end L3.ValueRows

#print axioms L3.ValueRows.pipeValD
#print axioms L3.ValueRows.delValD
#print axioms L3.ValueRows.finValD
#print axioms L3.ValueRows.termValD
