import Leader.L3.Top.SettledPotentialPhase

/-!
# Q7 (P.12 race): physical rows that keep a settled non-tail input

On a window edge whose source holds a settled input with tail `false`, no carry and no marker,
the source keeps its checker input, stays carry-free, and keeps its audit input atom; a settled
responder with no carry does the same.  These are the rows of the race induction that make an
off-race edge leave the settled right suffix alone.

Consumer: `Leader/L3/TopPinnedRaceKeep.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- The QI/QC rows leave a carry-free settled non-tail source alone.

Consumer: `race_source_keep`. -/
theorem race_qi_source (c : Compiled) (ox oy : Agent c) (v : Fin c.topA)
    (hxl : ox.l = false) (hxb : ox.beta = false)
    (hxq : ox.qIn = .S v false) (hxk : ox.qCarry = .OFF) :
    (qiPhys c ox oy).1.iX = ox.qIn ∧ (qcPhys c ox oy).1 = .OFF := by
  rcases hyk : oy.qCarry with _ | ⟨a, b⟩ <;> rcases hyi : oy.qIn.isE <;>
    rcases hd : ox.qOut.isD <;> rcases hyb : oy.beta <;>
  simp [qiPhys, qcPhys, hxq, hxk, hxl, hxb, hyk, hyi, hd, hyb, inT, QCarry.isOff, QCarry.isL,
    topBorder, topTerminal, InTok.isS, InTok.isP, InTok.isX]

/-- The QI/QC rows leave a carry-free settled responder alone, under a carry-free settled
non-tail source.

Consumer: `race_resp_keep`. -/
theorem race_qi_resp (c : Compiled) (ox oy : Agent c) (v w : Fin c.topA) (t : Bool)
    (hxl : ox.l = false) (hyl : oy.l = false) (hxb : ox.beta = false)
    (hxq : ox.qIn = .S v false) (hxk : ox.qCarry = .OFF)
    (hyq : oy.qIn = .S w t) (hyk : oy.qCarry = .OFF) :
    (qiPhys c ox oy).1.iY = oy.qIn ∧ (qcPhys c ox oy).2.1 = .OFF := by
  simp [qiPhys, qcPhys, hxq, hxk, hyq, hyk, hxl, hxb, inT, QCarry.isOff, QCarry.isL, topBorder,
    topTerminal, InTok.isS, InTok.isP, InTok.isX, InTok.isE]

/-- The audit input atom of a carry-free settled non-tail source is kept.

Consumer: `race_source_keep`. -/
theorem race_chain_source {c : Compiled} {n : Nat} (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) (v : Fin c.topA) (hxl : x.leader = false)
    (hyl : y.leader = false) (hxi : x.input = .S v false) (hxk : x.carryLive = false)
    (hxm : x.marker = false) : (replayChain x y gx gy).1.x = gx.input := by
  unfold replayChain
  simp [hxl, hyl, hxi, hxk, hxm, stepSettled, stepCarryX, stepCarryY, stepFront, stepSuccess,
    stepLaunch, stepPending, inT, InTok.isS, InTok.isP, InTok.isX]
  split <;> split <;> simp

/-- The audit input atom of a carry-free settled responder is kept.

Consumer: `race_resp_keep`. -/
theorem race_chain_resp {c : Compiled} {n : Nat} (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) (v : Fin c.topA) (hxl : x.leader = false)
    (hyl : y.leader = false) (hxi : x.input = .S v false) (hxk : x.carryLive = false)
    (hxm : x.marker = false) (hyk : y.carryLive = false) (hys : y.input.isS = true) :
    (replayChain x y gx gy).1.y = gy.input := by
  unfold replayChain
  have hye : y.input.isE = false := by cases hh : y.input <;> simp_all [InTok.isS, InTok.isE]
  simp [hxl, hyl, hxi, hxk, hxm, hyk, hye, stepSettled, stepCarryX, stepCarryY, stepFront,
    stepSuccess, stepLaunch, stepPending, inT, InTok.isS, InTok.isP, InTok.isX]

/-- The view of an agent in the comparison lane.

Consumer: `race_source_keep`. -/
theorem race_view_fields {c : Compiled} (a : Agent c) :
    (digitLaneView .comparison (ProjD.ofAgent a) a.beta).leader = a.l ∧
    (digitLaneView .comparison (ProjD.ofAgent a) a.beta).marker = a.beta ∧
    (digitLaneView .comparison (ProjD.ofAgent a) a.beta).input = a.qIn ∧
    (digitLaneView .comparison (ProjD.ofAgent a) a.beta).carryLive = a.qCarry.isL := by
  simp [digitLaneView, ProjD.ofAgent, ProjW.ofAgent, Agent.certNative]

/-- **A carry-free settled non-tail source keeps its input, carry and audit atom** on its own
edge.

Consumer: `Leader/L3/TopPinnedRaceKeep.lean`. -/
theorem race_source_keep {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hxb : (Z.1.1 e).beta = false) (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hxq : (Z.1.1 e).qIn = .S v false) (hxk : (Z.1.1 e).qCarry = .OFF) :
    ((topFixedTraceNext ring C Z e).1.1 e).qIn = (Z.1.1 e).qIn ∧
    ((topFixedTraceNext ring C Z e).1.1 e).qCarry = .OFF ∧
    ((topFixedTraceNext ring C Z e).1.2.current e).comparison.input =
      (Z.1.2.current e).comparison.input := by
  have hsrc := topPortLiteralSourceFields ring C Z.1.1 e
  have hq := owner_qIn ring Z.1.1 e hxl hyl
  have hk := owner_qCarry ring Z.1.1 e hxl hyl
  have hphys : (topFixedTraceNext ring C Z e).1.1 e = topFixedPublicNext ring C Z.1.1 e e := rfl
  obtain ⟨h1, h2⟩ := race_qi_source _ (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e)) v hxl hxb hxq hxk
  refine ⟨?_, ?_, ?_⟩
  · rw [hphys, hsrc.1, hq.1, h1]
  · rw [hphys, hsrc.2.1, hk.1, h2]
  · rw [next_input_source ring C Z e]
    have hv := race_view_fields (Z.1.1 e)
    have hw := race_view_fields (Z.1.1 (ring.rightNeighbor e))
    have := race_chain_source
      (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
      (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
        (Z.1.1 (ring.rightNeighbor e)).beta)
      (Z.1.2.current e).comparison (Z.1.2.current (ring.rightNeighbor e)).comparison v
      (by rw [hv.1]; exact hxl) (by rw [hw.1]; exact hyl) (by rw [hv.2.2.1]; exact hxq)
      (by rw [hv.2.2.2, hxk]; rfl) (by rw [hv.2.1]; exact hxb)
    rw [replay_input_x_eq]
    exact this

/-- **A carry-free settled responder keeps its input, carry and audit atom** under a
carry-free settled non-tail source.

Consumer: `Leader/L3/TopPinnedRaceKeep.lean`. -/
theorem race_resp_keep {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (Z : TopFixedTraceState n) (e : Fin n)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hxb : (Z.1.1 e).beta = false) (v w : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool)
    (hxq : (Z.1.1 e).qIn = .S v false) (hxk : (Z.1.1 e).qCarry = .OFF)
    (hyq : (Z.1.1 (ring.rightNeighbor e)).qIn = .S w t)
    (hyk : (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF) :
    ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qIn =
      (Z.1.1 (ring.rightNeighbor e)).qIn ∧
    ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qCarry = .OFF ∧
    ((topFixedTraceNext ring C Z e).1.2.current (ring.rightNeighbor e)).comparison.input =
      (Z.1.2.current (ring.rightNeighbor e)).comparison.input := by
  have hresp := topPortLiteralResponderFields ring hn C Z.1.1 e
  have hq := owner_qIn ring Z.1.1 e hxl hyl
  have hk := owner_qCarry ring Z.1.1 e hxl hyl
  have hphys : (topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e) =
      topFixedPublicNext ring C Z.1.1 e (ring.rightNeighbor e) := rfl
  obtain ⟨h1, h2⟩ := race_qi_resp _ (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e)) v w t hxl hyl hxb
    hxq hxk hyq hyk
  refine ⟨?_, ?_, ?_⟩
  · rw [hphys, hresp.1, hq.2, h1]
  · rw [hphys, hresp.2.1, hk.2, h2]
  · have hne := rightNeighbor_ne ring hn e
    rw [next_input_responder ring C Z e hne]
    have hv := race_view_fields (Z.1.1 e)
    have hw := race_view_fields (Z.1.1 (ring.rightNeighbor e))
    have := race_chain_resp
      (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
      (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
        (Z.1.1 (ring.rightNeighbor e)).beta)
      (Z.1.2.current e).comparison (Z.1.2.current (ring.rightNeighbor e)).comparison v
      (by rw [hv.1]; exact hxl) (by rw [hw.1]; exact hyl) (by rw [hv.2.2.1]; exact hxq)
      (by rw [hv.2.2.2, hxk]; rfl) (by rw [hv.2.1]; exact hxb)
      (by rw [hw.2.2.2, hyk]; rfl) (by rw [hw.2.2.1, hyq]; rfl)
    rw [replay_input_y_eq]
    exact this

end MarkedCells
end L3

#print axioms L3.MarkedCells.race_source_keep
#print axioms L3.MarkedCells.race_resp_keep
