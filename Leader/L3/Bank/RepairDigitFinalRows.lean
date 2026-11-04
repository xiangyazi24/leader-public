import Leader.L3.Bank.RepairDigitLeadingFlush

/-!
# T18: lane-shape row equations for the final-region flush

The final-region rank only reads token shapes: the input kind with its tail bit, the
carry-live bit and the output kind with its tail bit. This module proves that the literal
`liveTopPair` row acts on those shapes by four small step functions:

* `bankRepairDigitFinStep`: an edge whose right end is internal (not leader, not delimiter);
* `bankRepairDigitDelStep`: the delivery edge into a delimiter;
* `bankRepairDigitPipeStep`: output motion across an edge whose right end is internal;
* the right end of an edge into a delimiter keeps its output.
-/

namespace L3.RenewalReferenceClock

set_option autoImplicit false

/-- Input shape: the kind with its tail bit. -/
inductive BankRepairDigitInSh | E | X | P (T : Bool) | S (T : Bool)
  deriving DecidableEq, Repr

/-- Output shape: the kind with its tail bit. -/
inductive BankRepairDigitOutSh | E | U | D (T : Bool)
  deriving DecidableEq, Repr

def bankRepairDigitInShOf {A : Nat} : InTok A → BankRepairDigitInSh
  | .E => .E
  | .X => .X
  | .P _ T => .P T
  | .S _ T => .S T

def bankRepairDigitOutShOf {A : Nat} : OutTok A → BankRepairDigitOutSh
  | .E => .E
  | .U => .U
  | .D _ T => .D T

/-- One lane across an edge whose right end `y` is internal: new
`(input x, live x, input y, live y)` from the old ones and the border bit of `x`. -/
def bankRepairDigitFinStep (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool)
    (iy : BankRepairDigitInSh) (ky : Bool) :
    BankRepairDigitInSh × Bool × BankRepairDigitInSh × Bool :=
  if kx then
    (if ky then (.E, false, .E, true)
     else match iy with
       | .S _ => (.E, false, .E, true)
       | _ => (.E, false, iy, false))
  else if ky then
    match ix with
    | .E => (.E, false, .E, true)
    | .X => (.E, false, .E, true)
    | .P T => (.P T, false, .E, true)
    | .S T => if bx then (.E, true, .E, true)
              else if T then (.X, false, .E, true) else (.S T, false, .E, true)
  else
    match ix with
    | .E => (.E, false, iy, false)
    | .X => (.E, false, (match iy with | .S _ => .X | _ => iy), false)
    | .S T => if bx then (.E, true, iy, false)
              else if T then (.X, false, iy, false) else (.S T, false, iy, false)
    | .P T => match iy with
      | .E => (.E, false, .P T, false)
      | .S T' => (.S T, false, .S T', false)
      | _ => (.P T, false, iy, false)

theorem bankRepairDigitWriterFinRow (c : Compiled) (ox oy : Agent c)
    (hl : ox.l = false) (hly : oy.l = false) (hby : oy.beta = false) :
    (bankRepairDigitInShOf (liveTopPair c ox oy).x.wIn, (liveTopPair c ox oy).x.wCarry.isW,
      bankRepairDigitInShOf (liveTopPair c ox oy).y.wIn, (liveTopPair c ox oy).y.wCarry.isW) =
    bankRepairDigitFinStep ox.beta (bankRepairDigitInShOf ox.wIn) ox.wCarry.isW
      (bankRepairDigitInShOf oy.wIn) oy.wCarry.isW := by
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut]
  cases hb : ox.beta <;> cases hi : ox.wIn <;> cases hc : ox.wCarry <;>
    cases hi2 : oy.wIn <;> cases hc2 : oy.wCarry <;>
    simp [liveTopWC, liveTopWI, liveTopWO,
      hl, hly, hby, hb, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, WCarry.isOff, WCarry.isW, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, inV,
      bankRepairDigitFinStep, bankRepairDigitInShOf, WC] <;>
    (repeat' split) <;> simp_all

theorem bankRepairDigitComparisonFinRow (c : Compiled) (ox oy : Agent c)
    (hl : ox.l = false) (hly : oy.l = false) (hby : oy.beta = false) :
    (bankRepairDigitInShOf (liveTopPair c ox oy).x.qIn, (liveTopPair c ox oy).x.qCarry.isL,
      bankRepairDigitInShOf (liveTopPair c ox oy).y.qIn, (liveTopPair c ox oy).y.qCarry.isL) =
    bankRepairDigitFinStep ox.beta (bankRepairDigitInShOf ox.qIn) ox.qCarry.isL
      (bankRepairDigitInShOf oy.qIn) oy.qCarry.isL := by
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut]
  cases hb : ox.beta <;> cases hi : ox.qIn <;> cases hc : ox.qCarry <;>
    cases hi2 : oy.qIn <;> cases hc2 : oy.qCarry <;>
    simp [liveTopQC, liveTopQI, liveTopQO,
      hl, hly, hby, hb, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, QCarry.isOff, QCarry.isL, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, inV,
      bankRepairDigitFinStep, bankRepairDigitInShOf, QC] <;>
    (repeat' split) <;> simp_all

/-- One lane across the delivery edge into a delimiter `y` from an internal `x`: new
`(output x, input y, live y)`. -/
def bankRepairDigitDelStep (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh)
    (ky : Bool) : BankRepairDigitOutSh × BankRepairDigitInSh × Bool :=
  match ox with
  | .D T => if ky then (.D T, .E, true)
            else match iy with
              | .E => ((if T then .U else .E), .P T, false)
              | _ => (.D T, iy, false)
  | .U => (.D false, (if ky then .E else iy), ky)
  | .E => (.E, (if ky then .E else iy), ky)

theorem bankRepairDigitWriterDelRow (c : Compiled) (ox oy : Agent c)
    (hl : ox.l = false) (hly : oy.l = false) (hbx : ox.beta = false) (hby : oy.beta = true) :
    (bankRepairDigitOutShOf (liveTopPair c ox oy).x.wOut,
      bankRepairDigitInShOf (liveTopPair c ox oy).y.wIn, (liveTopPair c ox oy).y.wCarry.isW) =
    bankRepairDigitDelStep (bankRepairDigitOutShOf ox.wOut) (bankRepairDigitInShOf oy.wIn)
      oy.wCarry.isW := by
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
      bankRepairDigitDelStep, bankRepairDigitInShOf, bankRepairDigitOutShOf, WC] <;>
    (repeat' split) <;> simp_all

theorem bankRepairDigitComparisonDelRow (c : Compiled) (ox oy : Agent c)
    (hl : ox.l = false) (hly : oy.l = false) (hbx : ox.beta = false) (hby : oy.beta = true) :
    (bankRepairDigitOutShOf (liveTopPair c ox oy).x.qOut,
      bankRepairDigitInShOf (liveTopPair c ox oy).y.qIn, (liveTopPair c ox oy).y.qCarry.isL) =
    bankRepairDigitDelStep (bankRepairDigitOutShOf ox.qOut) (bankRepairDigitInShOf oy.qIn)
      oy.qCarry.isL := by
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
      bankRepairDigitDelStep, bankRepairDigitInShOf, bankRepairDigitOutShOf, QC] <;>
    (repeat' split) <;> simp_all

/-- Output motion across an edge whose right end is internal: new `(output x, output y)`. -/
def bankRepairDigitPipeStep (bx : Bool) (ox oy : BankRepairDigitOutSh) :
    BankRepairDigitOutSh × BankRepairDigitOutSh :=
  match ox with
  | .D T => match oy with
    | .E => ((if T then .U else .E), .D T)
    | _ => (.D T, oy)
  | .U => (.D bx, oy)
  | .E => ((if bx then .U else .E), oy)

theorem bankRepairDigitWriterPipeRow (c : Compiled) (ox oy : Agent c)
    (hl : ox.l = false) (hly : oy.l = false) (hby : oy.beta = false) :
    (bankRepairDigitOutShOf (liveTopPair c ox oy).x.wOut,
      bankRepairDigitOutShOf (liveTopPair c ox oy).y.wOut) =
    bankRepairDigitPipeStep ox.beta (bankRepairDigitOutShOf ox.wOut)
      (bankRepairDigitOutShOf oy.wOut) := by
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut]
  cases hb : ox.beta <;> cases ho : ox.wOut <;> cases ho2 : oy.wOut <;>
    simp [liveTopWC, liveTopWI, liveTopWO,
      hl, hly, hby, hb, ho, ho2, OutTok.isD,
      OutTok.isU, OutTok.isE, outT, bankRepairDigitPipeStep, bankRepairDigitOutShOf] <;>
    (repeat' split) <;> simp_all

theorem bankRepairDigitComparisonPipeRow (c : Compiled) (ox oy : Agent c)
    (hl : ox.l = false) (hly : oy.l = false) (hby : oy.beta = false) :
    (bankRepairDigitOutShOf (liveTopPair c ox oy).x.qOut,
      bankRepairDigitOutShOf (liveTopPair c ox oy).y.qOut) =
    bankRepairDigitPipeStep ox.beta (bankRepairDigitOutShOf ox.qOut)
      (bankRepairDigitOutShOf oy.qOut) := by
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut]
  cases hb : ox.beta <;> cases ho : ox.qOut <;> cases ho2 : oy.qOut <;>
    simp [liveTopQC, liveTopQI, liveTopQO,
      hl, hly, hby, hb, ho, ho2, OutTok.isD,
      OutTok.isU, OutTok.isE, outT, bankRepairDigitPipeStep, bankRepairDigitOutShOf] <;>
    (repeat' split) <;> simp_all

/-- An edge into a delimiter keeps the delimiter's outputs. -/
theorem bankRepairDigitEntryRow (c : Compiled) (ox oy : Agent c)
    (hl : ox.l = false) (hly : oy.l = false) (hby : oy.beta = true) :
    (liveTopPair c ox oy).y.wOut = oy.wOut ∧ (liveTopPair c ox oy).y.qOut = oy.qOut := by
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut]
  cases ho : ox.wOut <;> cases ho2 : ox.qOut <;>
    simp [liveTopWI, liveTopWO, liveTopQI, liveTopQO,
      hl, hly, hby, ho, ho2, OutTok.isD,
      OutTok.isU, OutTok.isE] <;>
    (repeat' split) <;> simp_all

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankRepairDigitWriterFinRow
#print axioms L3.RenewalReferenceClock.bankRepairDigitComparisonFinRow
#print axioms L3.RenewalReferenceClock.bankRepairDigitWriterDelRow
#print axioms L3.RenewalReferenceClock.bankRepairDigitComparisonDelRow
#print axioms L3.RenewalReferenceClock.bankRepairDigitWriterPipeRow
#print axioms L3.RenewalReferenceClock.bankRepairDigitComparisonPipeRow
#print axioms L3.RenewalReferenceClock.bankRepairDigitEntryRow
