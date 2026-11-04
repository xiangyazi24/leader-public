import Leader.L3.Top.SuffixLinv
import Leader.L3.Top.MarkedLink
import Leader.L3.Top.GhostInput

/-!
# Q7 (P.12 race): a settled non-tail pair is framed by one real service

Physical rows and audit rows for an edge whose source holds a settled non-tail input with no
carry: the source checker input and carry are kept, the ghost comparison input of the source
is kept; if the responder also holds a settled non-tail input with no carry (and is not a
marker), the responder input, carry and ghost input are kept as well.

Consumer: `Leader/L3/Top/PinnedRaceStep.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The QI rows keep a settled non-tail source.

Consumer: `step_settled_x`. -/
theorem qi_settled_x (c : Compiled) (x y : Agent c) (hxl : x.l = false) (hyl : y.l = false)
    (v : Fin c.topA) (hxq : x.qIn = .S v false) (hxk : x.qCarry = .OFF) (hxb : x.beta = false) :
    (qiPhys c x y).1.iX = x.qIn := by
  rcases hyq : y.qIn with _ | _ | ⟨yv, yt⟩ | ⟨yv, yt⟩ <;>
  rcases hyk : y.qCarry with _ | ⟨ycc, yce⟩ <;>
  cases hyb : y.beta <;>
  cases hd : x.qOut.isD <;>
  simp (config := { decide := true })
    [qiPhys, hxl, hyl, hxq, hxk, hxb, hyq, hyk, hyb, hd, topTerminal, topInternal, topBorder,
     QCarry.isOff, QCarry.isL, InTok.isP, InTok.isS, InTok.isX, InTok.isE, inT, inV]

/-- The QI rows keep a settled non-tail responder behind a settled non-tail source.

Consumer: `step_settled_pair`. -/
theorem qi_settled_y (c : Compiled) (x y : Agent c) (hxl : x.l = false) (hyl : y.l = false)
    (v w : Fin c.topA) (hxq : x.qIn = .S v false) (hxk : x.qCarry = .OFF) (hxb : x.beta = false)
    (hyq : y.qIn = .S w false) (hyk : y.qCarry = .OFF) (hyb : y.beta = false) :
    (qiPhys c x y).1.iY = y.qIn := by
  cases hd : x.qOut.isD <;>
  simp (config := { decide := true })
    [qiPhys, hxl, hyl, hxq, hxk, hxb, hyq, hyk, hyb, hd, topTerminal, topInternal, topBorder,
     QCarry.isOff, QCarry.isL, InTok.isP, InTok.isS, InTok.isX, InTok.isE, inT, inV]

/-- The QC rows keep the carries of a carry-free non-marker source.

Consumer: `step_settled_x`. -/
theorem qc_off_off (c : Compiled) (x y : Agent c) (hxk : x.qCarry = .OFF) (hxb : x.beta = false) :
    (qcPhys c x y).1 = .OFF ∧ (qcPhys c x y).2.1 = y.qCarry := by
  simp [qcPhys, hxk, hxb, topTerminal, topBorder, QCarry.isL, QCarry.isOff]

/-- The ghost chain keeps the source input of a settled carry-free non-marker source.

Consumer: `audit_settled_x`. -/
theorem replayChain_settled_x {c : Compiled} {n : Nat} (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) (hxl : x.leader = false) (hyl : y.leader = false)
    (hxs : x.input.isS = true) (hxc : x.carryLive = false) (hxm : x.marker = false) :
    (replayChain x y gx gy).1.x = gx.input := by
  have hP : x.input.isP = false := by
    rcases hx : x.input with _ | _ | ⟨v, t⟩ | ⟨v, t⟩ <;> simp_all [InTok.isS, InTok.isP]
  have hX : x.input.isX = false := by
    rcases hx : x.input with _ | _ | ⟨v, t⟩ | ⟨v, t⟩ <;> simp_all [InTok.isS, InTok.isX]
  unfold replayChain
  simp [hxl, hyl, hxs, hxc, hxm, hP, hX, stepPending, stepLaunch, stepSuccess, stepFront,
    stepSettled, stepCarryY, stepCarryX]
  all_goals (repeat' split)
  all_goals simp_all

/-- The ghost chain keeps the responder input behind a settled carry-free source.

Consumer: `audit_settled_y`. -/
theorem replayChain_settled_y {c : Compiled} {n : Nat} (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) (hxl : x.leader = false) (hyl : y.leader = false)
    (hxs : x.input.isS = true) (hxc : x.carryLive = false) (hxm : x.marker = false)
    (hyc : y.carryLive = false) (hye : y.input.isE = false) :
    (replayChain x y gx gy).1.y = gy.input := by
  have hP : x.input.isP = false := by
    rcases hx : x.input with _ | _ | ⟨v, t⟩ | ⟨v, t⟩ <;> simp_all [InTok.isS, InTok.isP]
  have hX : x.input.isX = false := by
    rcases hx : x.input with _ | _ | ⟨v, t⟩ | ⟨v, t⟩ <;> simp_all [InTok.isS, InTok.isX]
  unfold replayChain
  simp [hxl, hyl, hxs, hxc, hxm, hyc, hye, hP, hX, stepPending, stepLaunch, stepSuccess,
    stepFront, stepSettled, stepCarryY, stepCarryX]
  all_goals (repeat' split)
  all_goals simp_all

/-- The ghost input of the source after one real service, as the first chain output.

Consumer: `step_settled_x`. -/
theorem ghost_input_x_eq {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n) :
    ((topFixedTraceNext ring C Z e).1.2.current e).comparison.input =
      (replayChain
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
          (Z.1.1 (ring.rightNeighbor e)).beta)
        (Z.1.2.current e).comparison
        (Z.1.2.current (ring.rightNeighbor e)).comparison).1.x := by
  rw [← replay_input_x_eq .comparison (Z.1.2.clock + 1) e (ring.rightNeighbor e)]
  simp [topFixedTraceNext, digitAuditStep, digitGhostStep, digitService, piD, ProjD.ofAgent,
    ProjW.ofAgent]

/-- The ghost input of the responder after one real service, as the second chain output.

Consumer: `step_settled_pair`. -/
theorem ghost_input_y_eq {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n) (hne : ring.rightNeighbor e ≠ e) :
    ((topFixedTraceNext ring C Z e).1.2.current (ring.rightNeighbor e)).comparison.input =
      (replayChain
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
          (Z.1.1 (ring.rightNeighbor e)).beta)
        (Z.1.2.current e).comparison
        (Z.1.2.current (ring.rightNeighbor e)).comparison).1.y := by
  rw [← replay_input_y_eq .comparison (Z.1.2.clock + 1) e (ring.rightNeighbor e)]
  simp [topFixedTraceNext, digitAuditStep, digitGhostStep, digitService, piD, ProjD.ofAgent,
    ProjW.ofAgent, hne]

/-- **A settled non-tail source is framed by one real service**: its checker input and carry
and its ghost comparison input are kept.

Consumer: `Leader/L3/Top/PinnedRaceStep.lean`. -/
theorem step_settled_x {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA) (hxq : (Z.1.1 e).qIn = .S v false)
    (hxk : (Z.1.1 e).qCarry = .OFF) (hxb : (Z.1.1 e).beta = false) :
    ((topFixedTraceNext ring C Z e).1.1 e).qIn = .S v false ∧
    ((topFixedTraceNext ring C Z e).1.1 e).qCarry = .OFF ∧
    ((topFixedTraceNext ring C Z e).1.2.current e).comparison.input =
      (Z.1.2.current e).comparison.input := by
  have hsrc := topPortLiteralSourceFields ring C Z.1.1 e
  have hq := owner_qIn ring Z.1.1 e hxl hyl
  have hk := owner_qCarry ring Z.1.1 e hxl hyl
  have hqi := qi_settled_x (compileAdvice (ceilLogTwo n)) (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e))
    hxl hyl v hxq hxk hxb
  have hqc := qc_off_off (compileAdvice (ceilLogTwo n)) (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e))
    hxk hxb
  refine ⟨?_, ?_, ?_⟩
  · change (topFixedPublicNext ring C Z.1.1 e e).qIn = _
    rw [hsrc.1, hq.1, hqi, hxq]
  · change (topFixedPublicNext ring C Z.1.1 e e).qCarry = _
    rw [hsrc.2.1, hk.1, hqc.1]
  · rw [ghost_input_x_eq]
    apply replayChain_settled_x
    · exact hxl
    · exact hyl
    · simp [digitLaneView, ProjD.ofAgent, hxq, InTok.isS]
    · simp [digitLaneView, ProjD.ofAgent, hxk, QCarry.isL]
    · simp [digitLaneView, hxb]
    
/-- **A settled non-tail pair is framed by one real service**: the responder keeps its checker
input, carry and ghost comparison input.

Consumer: `Leader/L3/Top/PinnedRaceStep.lean`. -/
theorem step_settled_y {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (Z : TopFixedTraceState n) (e : Fin n)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (v w : Fin (compileAdvice (ceilLogTwo n)).topA) (hxq : (Z.1.1 e).qIn = .S v false)
    (hxk : (Z.1.1 e).qCarry = .OFF) (hxb : (Z.1.1 e).beta = false)
    (hyq : (Z.1.1 (ring.rightNeighbor e)).qIn = .S w false)
    (hyk : (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF)
    (hyb : (Z.1.1 (ring.rightNeighbor e)).beta = false) :
    ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qIn = .S w false ∧
    ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qCarry = .OFF ∧
    ((topFixedTraceNext ring C Z e).1.2.current (ring.rightNeighbor e)).comparison.input =
      (Z.1.2.current (ring.rightNeighbor e)).comparison.input := by
  have hne : ring.rightNeighbor e ≠ e := rightNeighbor_ne ring hn e
  have hresp := topPortLiteralResponderFields ring hn C Z.1.1 e
  have hq := owner_qIn ring Z.1.1 e hxl hyl
  have hk := owner_qCarry ring Z.1.1 e hxl hyl
  have hqi := qi_settled_y (compileAdvice (ceilLogTwo n)) (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e))
    hxl hyl v w hxq hxk hxb hyq hyk hyb
  have hqc := qc_off_off (compileAdvice (ceilLogTwo n)) (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e))
    hxk hxb
  refine ⟨?_, ?_, ?_⟩
  · change (topFixedPublicNext ring C Z.1.1 e (ring.rightNeighbor e)).qIn = _
    rw [hresp.1, hq.2, hqi, hyq]
  · change (topFixedPublicNext ring C Z.1.1 e (ring.rightNeighbor e)).qCarry = _
    rw [hresp.2.1, hk.2, hqc.2, hyk]
  · rw [ghost_input_y_eq ring C Z e hne]
    apply replayChain_settled_y
    · exact hxl
    · exact hyl
    · simp [digitLaneView, ProjD.ofAgent, hxq, InTok.isS]
    · simp [digitLaneView, ProjD.ofAgent, hxk, QCarry.isL]
    · simp [digitLaneView, hxb]
    · simp [digitLaneView, ProjD.ofAgent, hyk, QCarry.isL]
    · simp [digitLaneView, ProjD.ofAgent, hyq, InTok.isE]

/-- **An unrelated site keeps its checker input, carry and ghost comparison input.**

Consumer: `Leader/L3/Top/PinnedRaceStep.lean`. -/
theorem step_away {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e v : Fin n) (hx : v ≠ e) (hy : v ≠ ring.rightNeighbor e) :
    ((topFixedTraceNext ring C Z e).1.1 v).qIn = (Z.1.1 v).qIn ∧
    ((topFixedTraceNext ring C Z e).1.1 v).qCarry = (Z.1.1 v).qCarry ∧
    ((topFixedTraceNext ring C Z e).1.2.current v).comparison.input =
      (Z.1.2.current v).comparison.input := by
  have haway := topPortLiteralAwayFields ring C Z.1.1 e v hx hy
  refine ⟨haway.1, haway.2.1, ?_⟩
  rw [next_ghost_away ring C Z e v hx hy]

end MarkedCells
end L3

#print axioms L3.MarkedCells.qi_settled_x
#print axioms L3.MarkedCells.qi_settled_y
#print axioms L3.MarkedCells.qc_off_off
#print axioms L3.MarkedCells.replayChain_settled_x
#print axioms L3.MarkedCells.replayChain_settled_y
#print axioms L3.MarkedCells.step_settled_x
#print axioms L3.MarkedCells.step_settled_y
#print axioms L3.MarkedCells.step_away
