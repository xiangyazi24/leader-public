import Leader.L3.Top.OldGhost

/-!
# Q7: the physical input row and the ghost input rule, jointly

`input_link` gives the audit atoms of the outputs of the first-match input row.  The labelled
window of the final mobile phase also needs the physical input token of a pending output, and
the converse for the port: a recorded export is exactly an acceptance of the physical row.

Consumer: `Leader/L3/TopFinalMobileBridge.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- The input rows (`inputs`) of `digitLaneReplay`, verbatim with their look flags. -/
private def jointReplayInputs {c : Compiled} {n : Nat}
    (lane : DigitLane) (time : Nat)
    (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) : DigitInputGhost n × Bool :=
  let stamp : DigitStamp n :=
    { time := time, site := source, lane := lane }
  let roots := x.leader || y.leader
  let terminal := y.leader || y.marker
  let success :=
    x.carryLive && !terminal && !y.carryLive && y.input.isS
  let launch :=
    !x.leader && x.marker && !x.carryLive &&
      x.input.isS && !y.leader
  let offer := x.out.isD && y.marker
  let inputs : DigitInputGhost n × Bool :=
    if roots then
      ({ x := none, y := none, fx := true, fy := true }, false)
    else
      let s : DigitInputGhost n :=
        { x := gx.input, y := gy.input, fx := false, fy := false }
      let s :=
        if !s.fx && x.carryLive then
          { s with x := none, fx := true }
        else s
      let s :=
        if !s.fy && y.carryLive then
          { s with y := none, fy := true }
        else s
      let s :=
        if !s.fx && x.input.isS && inT x.input && !x.marker then
          { s with x := gx.input, fx := true }
        else s
      let s :=
        if !s.fx && x.input.isX then
          let s := { s with x := none, fx := true }
          if !s.fy && !y.leader && !y.marker && y.input.isS then
            { s with y := gx.input, fy := true }
          else s
        else s
      let s :=
        if success && !s.fy then
          { s with y := none, fy := true }
        else s
      let s :=
        if launch && !s.fx then
          { s with x := none, fx := true }
        else s
      let s :=
        if !s.fx && x.input.isP then
          if terminal then
            if !inT x.input then
              { s with x := gx.input, fx := true }
            else if !x.marker then
              { s with x := none, fx := true }
            else s
          else if !y.leader && !y.marker &&
              y.input.isE && !y.carryLive && !s.fy then
            { x := none, y := gx.input, fx := true, fy := true }
          else if y.input.isS && !y.carryLive then
            { s with x := gx.input, fx := true }
          else s
        else s
      let accepted :=
        !s.fy && offer && y.input.isE && !y.carryLive
      let s :=
        if accepted then
          { s with y := gx.out.atom, fy := true }
        else s
      (s, accepted)
  inputs

private theorem jointReplay_x_input {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) :
    (digitLaneReplay lane time source destination x y gx gy).x.input =
      (jointReplayInputs lane time source destination x y gx gy).1.x := rfl

private theorem jointReplay_y_input {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) :
    (digitLaneReplay lane time source destination x y gx gy).y.input =
      (jointReplayInputs lane time source destination x y gx gy).1.y := rfl


private theorem jointReplay_exported {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n) (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n) :
    (digitLaneReplay lane time source destination x y gx gy).exported =
      (if (jointReplayInputs lane time source destination x y gx gy).2 then
        some
          { time := time
            lane := lane
            source := source
            destination := destination
            operand := gx.out.atom
            value := outV c x.out
            tail := outT x.out }
      else none) := rfl

/-- **Joint link of the input row.**  A pending source output is the source input and keeps its
atom; a pending responder output is the responder input, or the source input moved into an empty
carry-free interior responder, or the packet accepted at a marker; and a recorded export is
exactly an acceptance.

Consumer: `window_bridge`, `port_bridge`. -/
theorem qi_joint {c : Compiled} {n : Nat} (time : Nat) (src dst : Fin n)
    (x y : Agent c) (hxl : x.l = false) (hyl : y.l = false)
    (gx gy : DigitLaneGhost c n) :
    ((qiPhys c x y).1.iX.isP = true →
      (qiPhys c x y).1.iX = x.qIn ∧ x.qIn.isP = true ∧
      (digitLaneReplay .comparison time src dst
        (digitLaneView .comparison (ProjD.ofAgent x) x.beta)
        (digitLaneView .comparison (ProjD.ofAgent y) y.beta) gx gy).x.input = gx.input) ∧
    ((qiPhys c x y).1.iY.isP = true →
      (y.qIn.isP = true ∧ (qiPhys c x y).1.iY = y.qIn ∧
        (digitLaneReplay .comparison time src dst
          (digitLaneView .comparison (ProjD.ofAgent x) x.beta)
          (digitLaneView .comparison (ProjD.ofAgent y) y.beta) gx gy).y.input = gy.input) ∨
      (y.beta = false ∧ y.qIn = .E ∧ y.qCarry = .OFF ∧ x.qIn.isP = true ∧
        (qiPhys c x y).1.iY = x.qIn ∧
        (digitLaneReplay .comparison time src dst
          (digitLaneView .comparison (ProjD.ofAgent x) x.beta)
          (digitLaneView .comparison (ProjD.ofAgent y) y.beta) gx gy).y.input = gx.input) ∨
      (y.beta = true ∧ y.qIn = .E ∧ y.qCarry = .OFF ∧ (qiPhys c x y).2 = true ∧
        (qiPhys c x y).1.iY = .P (outV c x.qOut) (outT x.qOut) ∧
        (digitLaneReplay .comparison time src dst
          (digitLaneView .comparison (ProjD.ofAgent x) x.beta)
          (digitLaneView .comparison (ProjD.ofAgent y) y.beta) gx gy).y.input = gx.out.atom)) ∧
    (((digitLaneReplay .comparison time src dst
        (digitLaneView .comparison (ProjD.ofAgent x) x.beta)
        (digitLaneView .comparison (ProjD.ofAgent y) y.beta) gx gy).exported ≠ none) ↔
      (qiPhys c x y).2 = true) := by
  simp only [jointReplay_x_input, jointReplay_y_input, jointReplay_exported]
  -- Split the carries, the source input and both markers first and simplify once; the guards of
  -- both rows that read them are then decided, and the remaining splits work on the residual.
  rcases hxk : x.qCarry with _ | ⟨xcc, xce⟩ <;>
  rcases hyk : y.qCarry with _ | ⟨ycc, yce⟩ <;>
  rcases hxq : x.qIn with _ | _ | ⟨xv, xt⟩ | ⟨xv, xt⟩ <;>
  cases hxb : x.beta <;> cases hyb : y.beta <;>
  (try simp
    [qiPhys, jointReplayInputs, digitLaneView, ProjD.ofAgent, ProjW.ofAgent, hxl, hyl, hxq,
     hxk, hyk, hxb, hyb, topTerminal, topInternal, topBorder, QCarry.isOff, QCarry.isL,
     InTok.isP, InTok.isS, InTok.isX, InTok.isE, inT, inV, Agent.certNative, -not_imp, Decidable.not_imp_iff_and_not]) <;>
  rcases hyq : y.qIn with _ | _ | ⟨yv, yt⟩ | ⟨yv, yt⟩ <;>
  cases hd : x.qOut.isD <;>
  (try cases xt) <;> (try cases yt) <;>
  simp
    [qiPhys, jointReplayInputs, digitLaneView, ProjD.ofAgent, ProjW.ofAgent, hxl, hyl, hxq, hyq,
     hxk, hyk, hxb, hyb, hd, topTerminal, topInternal, topBorder, QCarry.isOff, QCarry.isL,
     InTok.isP, InTok.isS, InTok.isX, InTok.isE, inT, inV, Agent.certNative, -not_imp,
     Decidable.not_imp_iff_and_not]

end MarkedCells
end L3

#print axioms L3.MarkedCells.qi_joint
