import Leader.L3.Width.DigitQuiet

/-!
# The quiet class: one letter on the lane views

`laneRow lane vx vy` is the new pair of lane views after one letter (`liveTopPair`) on the two
endpoints, written on the views of one lane (`DigitLaneView`): the in-slot block (WI / QI), the
out-slot block (WO / QO) and the carry block (WC / QC) transcribed from `CertRows.lean` 605-758,
with the old markers as the resolved betas.  `laneRow_correct` shows the physical record has exactly
these lane fields.  Everything the pair closure needs from the machine is stated on `laneRow`.

Consumer: `WidthDigitQuietStep*` (pair, region and digit closure of `QuietStepLaw`).
-/

namespace L3.DigitQuiet

open L3
open L3.AcceptedReceipts

set_option autoImplicit false

variable {c : Compiled}

/-- The success flag: a live carry on the left, not terminal, a free right with a settled input
(`wc2Success`, `qc2Success`).  Consumer: `laneRow`. -/
def rowSucc (vx vy : DigitLaneView c) : Bool :=
  (vx.carryLive && !(vy.leader || vy.marker)) && !vy.carryLive && vy.input.isS

/-- The launch flag: a non-leader delimiter on the left without carry holding a settled input, the
right not the leader (`wc3`, `qc3`).  Consumer: `laneRow`. -/
def rowLaunch (vx vy : DigitLaneView c) : Bool :=
  (!vx.leader && vx.marker) && !vx.carryLive && vx.input.isS && !vy.leader

/-- The in-slot block: new left input, new right input, and the acceptance of an out packet at the
delimiter on the right.  Consumer: `laneRow`. -/
def rowIn (vx vy : DigitLaneView c) : InSt c.topA × Bool :=
  if (vx.leader || vy.leader) = true then ({ iX := .E, iY := .E, fx := true, fy := true }, false) else
  let wTerminal := vy.leader || vy.marker
  let wo1 := vx.out.isD && vy.marker
  let s : InSt c.topA := { iX := vx.input, iY := vy.input, fx := false, fy := false }
  let s := if !s.fx && vx.carryLive then { s with iX := .E, fx := true } else s
  let s := if !s.fy && vy.carryLive then { s with iY := .E, fy := true } else s
  let s := if !s.fx && vx.input.isS && inT vx.input && !vx.marker then
             { s with iX := .X, fx := true } else s
  let s := if !s.fx && vx.input.isX then
             let s := { s with iX := .E, fx := true }
             if !s.fy && ((!vy.leader) && !vy.marker) && vy.input.isS then
               { s with iY := .X, fy := true } else s
           else s
  let s := if rowSucc vx vy && !s.fy then { s with iY := .E, fy := true } else s
  let s := if rowLaunch vx vy && !s.fx then { s with iX := .E, fx := true } else s
  let s := if !s.fx && vx.input.isP then
             if wTerminal then
               if !inT vx.input then { s with iX := .S (inV c vx.input) false, fx := true }
               else if !vx.marker then { s with iX := .E, fx := true }
               else s
             else if ((!vy.leader) && !vy.marker) && vy.input.isE && !vy.carryLive && !s.fy then
               { iX := .E, iY := .P (inV c vx.input) (inT vx.input), fx := true, fy := true }
             else if vy.input.isS && !vy.carryLive then
               { s with iX := .S (inV c vx.input) (inT vx.input), fx := true }
             else s
           else s
  let acc := !s.fy && wo1 && vy.input.isE && !vy.carryLive
  let s := if acc then { s with iY := .P (outV c vx.out) (outT vx.out), fy := true } else s
  (s, acc)

/-- The out-slot block: new left and right outputs.  Consumer: `laneRow`. -/
def rowOut (vx vy : DigitLaneView c) (acc : Bool) : OutTok c.topA × OutTok c.topA :=
  let wo1 := vx.out.isD && vy.marker
  if (vx.leader || vy.leader) = true then (.E, .E)
  else if wo1 = true then
    (if acc = true then ((if outT vx.out then .U else .E), vy.out) else (vx.out, vy.out))
  else if vx.out.isD && !vy.marker && vy.out.isE then
    ((if outT vx.out then .U else .E), .D (outV c vx.out) (outT vx.out))
  else if vx.out.isU then (.D vx.digit vx.marker, vy.out)
  else if vx.marker && vx.out.isE && !vx.leader then (.U, vy.out)
  else (vx.out, vy.out)

/-- A carry as `(live, bit, error)`.  Consumer: `rowCarry`. -/
abbrev CarryV := Bool × Bool × Bool

/-- The carry block: new left and right carries of one lane.  Consumer: `laneRow`. -/
def rowCarry (lane : DigitLane) (vx vy : DigitLaneView c) : CarryV × CarryV :=
  let off : CarryV := (false, false, false)
  let curX : CarryV := (vx.carryLive, vx.carryBit, vx.carryError)
  let curY : CarryV := (vy.carryLive, vy.carryBit, vy.carryError)
  if (vx.leader || vy.leader) = true then (off, off)
  else if vx.carryLive = true then
    if rowSucc vx vy = true then
      let v := (inV c vy.input).val
      let cc := vx.carryBit
      (off, (true, cc && (v + 1 == c.topA),
        match lane with
        | .writer => false
        | .comparison => vx.carryError || (vy.digit.val != (v + (if cc then 1 else 0)) % c.topA)))
    else (off, curY)
  else if rowLaunch vx vy = true then
    let v := (inV c vx.input).val
    ((true, v + 1 == c.topA,
      match lane with
      | .writer => false
      | .comparison => vx.digit.val != (v + 1) % c.topA), curY)
  else (curX, curY)

/-- **One letter on the lane views of the two endpoints**: the lane fields of the new left and right
records.  The leader, marker and digit fields are kept.  Consumer: `laneRow_correct`, the pair,
region and digit closure of `QuietStepLaw`. -/
def laneRow (lane : DigitLane) (vx vy : DigitLaneView c) : DigitLaneView c × DigitLaneView c :=
  let ib := rowIn vx vy
  let ob := rowOut vx vy ib.2
  let cb := rowCarry lane vx vy
  ({ vx with out := ob.1, input := ib.1.iX, carryLive := cb.1.1, carryBit := cb.1.2.1,
             carryError := cb.1.2.2 },
   { vy with out := ob.2, input := ib.1.iY, carryLive := cb.2.1, carryBit := cb.2.2.1,
             carryError := cb.2.2.2 })

/-- The writer-lane view of an agent record.  Consumer: `liveTop_row_writer`. -/
def aviewW (a : Agent c) : DigitLaneView c :=
  { leader := a.l, marker := a.beta, digit := a.d, out := a.wOut, input := a.wIn,
    carryLive := a.wCarry.isW, carryBit := wcC a.wCarry, carryError := false }

/-- The comparison-lane view of an agent record.  Consumer: `liveTop_row_comparison`. -/
def aviewQ (a : Agent c) : DigitLaneView c :=
  { leader := a.l, marker := a.beta, digit := a.d, out := a.qOut, input := a.qIn,
    carryLive := a.qCarry.isL, carryBit := qcC a.qCarry, carryError := qcE a.qCarry }

/-- The new left input of the writer lane.  Consumer: `laneRow_correct`. -/
theorem liveTop_in_x_writer (ox oy : Agent c) :
    (liveTopPair c ox oy ox.beta oy.beta).x.wIn =
      (rowIn (aviewW ox) (aviewW oy)).1.iX := by
  rcases ox with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc,_,_,qc,_⟩
  rcases oy with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc2,_,_,qc2,_⟩
  rcases wc with _ | _ <;> rcases wc2 with _ | _ <;> rfl

/-- The new right input of the writer lane.  Consumer: `laneRow_correct`. -/
theorem liveTop_in_y_writer (ox oy : Agent c) :
    (liveTopPair c ox oy ox.beta oy.beta).y.wIn =
      (rowIn (aviewW ox) (aviewW oy)).1.iY := by
  rcases ox with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc,_,_,qc,_⟩
  rcases oy with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc2,_,_,qc2,_⟩
  rcases wc with _ | _ <;> rcases wc2 with _ | _ <;> rfl

/-- The new left output of the writer lane.  Consumer: `laneRow_correct`. -/
theorem liveTop_out_x_writer (ox oy : Agent c) :
    (liveTopPair c ox oy ox.beta oy.beta).x.wOut =
      (rowOut (aviewW ox) (aviewW oy) (rowIn (aviewW ox) (aviewW oy)).2).1 := by
  rcases ox with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc,_,_,qc,_⟩
  rcases oy with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc2,_,_,qc2,_⟩
  rcases wc with _ | _ <;> rcases wc2 with _ | _ <;> rfl

/-- The new right output of the writer lane.  Consumer: `laneRow_correct`. -/
theorem liveTop_out_y_writer (ox oy : Agent c) :
    (liveTopPair c ox oy ox.beta oy.beta).y.wOut =
      (rowOut (aviewW ox) (aviewW oy) (rowIn (aviewW ox) (aviewW oy)).2).2 := by
  rcases ox with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc,_,_,qc,_⟩
  rcases oy with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc2,_,_,qc2,_⟩
  rcases wc with _ | _ <;> rcases wc2 with _ | _ <;> rfl

/-- The new left input of the comparison lane.  Consumer: `laneRow_correct`. -/
theorem liveTop_in_x_comparison (ox oy : Agent c) :
    (liveTopPair c ox oy ox.beta oy.beta).x.qIn =
      (rowIn (aviewQ ox) (aviewQ oy)).1.iX := by
  rcases ox with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc,_,_,qc,_⟩
  rcases oy with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc2,_,_,qc2,_⟩
  rcases qc with _ | _ <;> rcases qc2 with _ | _ <;> rfl

/-- The new right input of the comparison lane.  Consumer: `laneRow_correct`. -/
theorem liveTop_in_y_comparison (ox oy : Agent c) :
    (liveTopPair c ox oy ox.beta oy.beta).y.qIn =
      (rowIn (aviewQ ox) (aviewQ oy)).1.iY := by
  rcases ox with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc,_,_,qc,_⟩
  rcases oy with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc2,_,_,qc2,_⟩
  rcases qc with _ | _ <;> rcases qc2 with _ | _ <;> rfl

/-- The new left output of the comparison lane.  Consumer: `laneRow_correct`. -/
theorem liveTop_out_x_comparison (ox oy : Agent c) :
    (liveTopPair c ox oy ox.beta oy.beta).x.qOut =
      (rowOut (aviewQ ox) (aviewQ oy) (rowIn (aviewQ ox) (aviewQ oy)).2).1 := by
  rcases ox with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc,_,_,qc,_⟩
  rcases oy with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc2,_,_,qc2,_⟩
  rcases qc with _ | _ <;> rcases qc2 with _ | _ <;> rfl

/-- The new right output of the comparison lane.  Consumer: `laneRow_correct`. -/
theorem liveTop_out_y_comparison (ox oy : Agent c) :
    (liveTopPair c ox oy ox.beta oy.beta).y.qOut =
      (rowOut (aviewQ ox) (aviewQ oy) (rowIn (aviewQ ox) (aviewQ oy)).2).2 := by
  rcases ox with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc,_,_,qc,_⟩
  rcases oy with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc2,_,_,qc2,_⟩
  rcases qc with _ | _ <;> rcases qc2 with _ | _ <;> rfl


/-- The new left carry of the writer lane as `(live, bit, error)`.  Consumer: `laneRow_correct_writer`. -/
theorem liveTop_carry_x_writer (ox oy : Agent c) :
    ((liveTopPair c ox oy ox.beta oy.beta).x.wCarry.isW,
      wcC (liveTopPair c ox oy ox.beta oy.beta).x.wCarry, false) =
      (rowCarry .writer (aviewW ox) (aviewW oy)).1 := by
  unfold liveTopPair rowCarry rowSucc rowLaunch aviewW
  simp only [topTerminal, topBorder]
  rcases ox with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc,_,_,qc,_⟩
  rcases oy with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc2,_,_,qc2,_⟩
  rcases wc with _ | ⟨_ | _⟩ <;> rcases wc2 with _ | ⟨_ | _⟩ <;>
    simp [WCarry.isW, WCarry.isOff, wcC, WC] <;> (repeat' split) <;> simp_all

/-- The new right carry of the writer lane.  Consumer: `laneRow_correct_writer`. -/
theorem liveTop_carry_y_writer (ox oy : Agent c) :
    ((liveTopPair c ox oy ox.beta oy.beta).y.wCarry.isW,
      wcC (liveTopPair c ox oy ox.beta oy.beta).y.wCarry, false) =
      (rowCarry .writer (aviewW ox) (aviewW oy)).2 := by
  unfold liveTopPair rowCarry rowSucc rowLaunch aviewW
  simp only [topTerminal, topBorder]
  rcases ox with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc,_,_,qc,_⟩
  rcases oy with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc2,_,_,qc2,_⟩
  rcases wc with _ | ⟨_ | _⟩ <;> rcases wc2 with _ | ⟨_ | _⟩ <;>
    simp [WCarry.isW, WCarry.isOff, wcC, WC] <;> (repeat' split) <;> simp_all

/-- The new left carry of the comparison lane.  Consumer: `laneRow_correct_comparison`. -/
theorem liveTop_carry_x_comparison (ox oy : Agent c) :
    ((liveTopPair c ox oy ox.beta oy.beta).x.qCarry.isL,
      qcC (liveTopPair c ox oy ox.beta oy.beta).x.qCarry,
      qcE (liveTopPair c ox oy ox.beta oy.beta).x.qCarry) =
      (rowCarry .comparison (aviewQ ox) (aviewQ oy)).1 := by
  unfold liveTopPair rowCarry rowSucc rowLaunch aviewQ
  simp only [topTerminal, topBorder]
  rcases ox with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc,_,_,qc,_⟩
  rcases oy with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc2,_,_,qc2,_⟩
  rcases qc with _ | ⟨_ | _, _ | _⟩ <;> rcases qc2 with _ | ⟨_ | _, _ | _⟩ <;>
    simp [QCarry.isL, QCarry.isOff, qcC, qcE, QC, Compiled.digitMod, mod] <;>
    (repeat' split) <;> (try simp only [apply_ite Prod.fst, apply_ite Prod.snd] at *) <;>
    (try split at *) <;> simp_all

/-- The new right carry of the comparison lane.  Consumer: `laneRow_correct_comparison`. -/
theorem liveTop_carry_y_comparison (ox oy : Agent c) :
    ((liveTopPair c ox oy ox.beta oy.beta).y.qCarry.isL,
      qcC (liveTopPair c ox oy ox.beta oy.beta).y.qCarry,
      qcE (liveTopPair c ox oy ox.beta oy.beta).y.qCarry) =
      (rowCarry .comparison (aviewQ ox) (aviewQ oy)).2 := by
  unfold liveTopPair rowCarry rowSucc rowLaunch aviewQ
  simp only [topTerminal, topBorder]
  rcases ox with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc,_,_,qc,_⟩
  rcases oy with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wc2,_,_,qc2,_⟩
  rcases qc with _ | ⟨_ | _, _ | _⟩ <;> rcases qc2 with _ | ⟨_ | _, _ | _⟩ <;>
    simp [QCarry.isL, QCarry.isOff, qcC, qcE, QC, Compiled.digitMod, mod] <;>
    (repeat' split) <;> (try simp only [apply_ite Prod.fst, apply_ite Prod.snd] at *) <;>
    (try split at *) <;> simp_all

/-- The lane fields (all but leader, marker, digit) of two views agree.  Consumer:
`laneRow_correct`, the pair and region closure. -/
def LaneFieldsEq (v w : DigitLaneView c) : Prop :=
  v.out = w.out ∧ v.input = w.input ∧ v.carryLive = w.carryLive ∧ v.carryBit = w.carryBit ∧
    v.carryError = w.carryError

/-- **The lane fields of the new records are `laneRow` of the old views** (both lanes), when the
resolved betas are the old ones.  Consumer: the pair, region and digit closure of `QuietStepLaw`. -/
theorem laneRow_correct (lane : DigitLane) (x y : ProjD c)
    (hbX : (pairW x.word y.word).1.beta = x.word.beta)
    (hbY : (pairW x.word y.word).2.beta = y.word.beta) :
    LaneFieldsEq (digitLaneView lane (pairD x y).1 x.word.beta)
      (laneRow lane (digitLaneView lane x x.word.beta) (digitLaneView lane y y.word.beta)).1 ∧
    LaneFieldsEq (digitLaneView lane (pairD x y).2 y.word.beta)
      (laneRow lane (digitLaneView lane x x.word.beta) (digitLaneView lane y y.word.beta)).2 := by
  have e : topD x y = liveTopPair c x.lift y.lift x.lift.beta y.lift.beta := by
    show liveTopPair c x.lift y.lift (pairW x.word y.word).1.beta (pairW x.word y.word).2.beta =
      liveTopPair c x.lift y.lift x.lift.beta y.lift.beta
    rw [hbX, hbY]
    rfl
  cases lane
  · have hi := liveTop_in_x_writer x.lift y.lift
    have hi' := liveTop_in_y_writer x.lift y.lift
    have ho := liveTop_out_x_writer x.lift y.lift
    have ho' := liveTop_out_y_writer x.lift y.lift
    have hc := liveTop_carry_x_writer x.lift y.lift
    have hc' := liveTop_carry_y_writer x.lift y.lift
    have hrx : (digitLaneView DigitLane.writer x x.word.beta) = aviewW x.lift := rfl
    have hry : (digitLaneView DigitLane.writer y y.word.beta) = aviewW y.lift := rfl
    rw [hrx, hry]
    have hp1 : (pairD x y).1.top = (topD x y).x := rfl
    have hp2 : (pairD x y).2.top = (topD x y).y := rfl
    rw [e] at hp1 hp2
    simp only [laneRow, LaneFieldsEq, digitLaneView, hp1, hp2]
    refine ⟨⟨ho, hi, ?_, ?_, ?_⟩, ⟨ho', hi', ?_, ?_, ?_⟩⟩
    · exact congrArg Prod.fst hc
    · exact congrArg (fun p => p.2.1) hc
    · exact congrArg (fun p => p.2.2) hc
    · exact congrArg Prod.fst hc'
    · exact congrArg (fun p => p.2.1) hc'
    · exact congrArg (fun p => p.2.2) hc'
  · have hi := liveTop_in_x_comparison x.lift y.lift
    have hi' := liveTop_in_y_comparison x.lift y.lift
    have ho := liveTop_out_x_comparison x.lift y.lift
    have ho' := liveTop_out_y_comparison x.lift y.lift
    have hc := liveTop_carry_x_comparison x.lift y.lift
    have hc' := liveTop_carry_y_comparison x.lift y.lift
    have hrx : (digitLaneView DigitLane.comparison x x.word.beta) = aviewQ x.lift := rfl
    have hry : (digitLaneView DigitLane.comparison y y.word.beta) = aviewQ y.lift := rfl
    rw [hrx, hry]
    have hp1 : (pairD x y).1.top = (topD x y).x := rfl
    have hp2 : (pairD x y).2.top = (topD x y).y := rfl
    rw [e] at hp1 hp2
    simp only [laneRow, LaneFieldsEq, digitLaneView, hp1, hp2]
    refine ⟨⟨ho, hi, ?_, ?_, ?_⟩, ⟨ho', hi', ?_, ?_, ?_⟩⟩
    · exact congrArg Prod.fst hc
    · exact congrArg (fun p => p.2.1) hc
    · exact congrArg (fun p => p.2.2) hc
    · exact congrArg Prod.fst hc'
    · exact congrArg (fun p => p.2.1) hc'
    · exact congrArg (fun p => p.2.2) hc'

end L3.DigitQuiet

#print axioms L3.DigitQuiet.laneRow_correct
