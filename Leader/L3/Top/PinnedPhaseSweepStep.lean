import Leader.L3.Top.PinnedCarryReplay
import Leader.L3.Top.PinnedCarryLedger
import Leader.L3.Top.PinnedRaceRows
import Leader.L3.Top.PinnedPhaseFillPort

/-!
# Q7 (P.12 preparation, lemma 2): the single services of the carry sweep

The services that build the ledger of the aligned carry sweep, with all their fields:

* the launch at the border opens the ledger `[u]` with the atom, value and tail of the border
  input, and leaves the responder register alone (`trace_launch_full`, `launch_resp_keep`);
* the advance appends the use of the responder register with its atom, value and tail
  (`trace_advance_full`);
* a service into the host from the left keeps the ledger (`trace_host_keep`).

Consumer: `Leader/L3/Top/PinnedPhaseSweep.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The QI row keeps a settled non-tail responder behind a settled border source.

Consumer: `launch_resp_keep`. -/
theorem qi_launch_y (c : Compiled) (x y : Agent c) (hxl : x.l = false) (hyl : y.l = false)
    (v : Fin c.topA) (t : Bool) (w : Fin c.topA) (u : Bool) (hxq : x.qIn = .S v t)
    (hxk : x.qCarry = .OFF) (hxb : x.beta = true) (hyq : y.qIn = .S w u)
    (hyk : y.qCarry = .OFF) (hyb : y.beta = false) :
    (qiPhys c x y).1.iY = y.qIn := by
  cases hd : x.qOut.isD <;> cases t <;>
  simp (config := { decide := true })
    [qiPhys, hxl, hyl, hxq, hxk, hxb, hyq, hyk, hyb, hd, topTerminal, topInternal, topBorder,
     QCarry.isOff, QCarry.isL, InTok.isP, InTok.isS, InTok.isX, InTok.isE, inT, inV]

/-- The QC row keeps the carry of the responder behind a carry-free border source.

Consumer: `launch_resp_keep`. -/
theorem qc_launch_y (c : Compiled) (x y : Agent c) (hyl : y.l = false) (hxk : x.qCarry = .OFF) :
    (qcPhys c x y).2.1 = y.qCarry := by
  simp [qcPhys, hxk, hyl, topTerminal, topBorder, QCarry.isL, QCarry.isOff]

/-- **A launch keeps the responder register**: its checker input and carry and its ghost
comparison input.

Consumer: `sweep_step`. -/
theorem launch_resp_keep {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (Z : TopFixedTraceState n) (e : Fin n)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool) (w : Fin (compileAdvice (ceilLogTwo n)).topA)
    (u : Bool) (hxq : (Z.1.1 e).qIn = .S v t) (hxk : (Z.1.1 e).qCarry = .OFF)
    (hxb : (Z.1.1 e).beta = true) (hyq : (Z.1.1 (ring.rightNeighbor e)).qIn = .S w u)
    (hyk : (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF)
    (hyb : (Z.1.1 (ring.rightNeighbor e)).beta = false) :
    ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qIn = .S w u ∧
    ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qCarry = .OFF ∧
    ((topFixedTraceNext ring C Z e).1.2.current (ring.rightNeighbor e)).comparison.input =
      (Z.1.2.current (ring.rightNeighbor e)).comparison.input := by
  have hne : ring.rightNeighbor e ≠ e := rightNeighbor_ne ring hn e
  have hresp := topPortLiteralResponderFields ring hn C Z.1.1 e
  have hq := owner_qIn ring Z.1.1 e hxl hyl
  have hk := owner_qCarry ring Z.1.1 e hxl hyl
  have hqi := qi_launch_y (compileAdvice (ceilLogTwo n)) (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e))
    hxl hyl v t w u hxq hxk hxb hyq hyk hyb
  have hqc := qc_launch_y (compileAdvice (ceilLogTwo n)) (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e))
    hyl hxk
  refine ⟨?_, ?_, ?_⟩
  · change (topFixedPublicNext ring C Z.1.1 e (ring.rightNeighbor e)).qIn = _
    rw [hresp.1, hq.2, hqi, hyq]
  · change (topFixedPublicNext ring C Z.1.1 e (ring.rightNeighbor e)).qCarry = _
    rw [hresp.2.1, hk.2, hqc, hyk]
  · rw [trace_ghost_responder ring C Z e hne]
    apply replay_input_launch_resp
    · exact hxl
    · exact hyl
    · simp [digitLaneView, hyb]
    · simp [digitLaneView, hxb]
    · simp [digitLaneView, ProjD.ofAgent, hxk, QCarry.isL]
    · simp [digitLaneView, ProjD.ofAgent, hxq, InTok.isS]
    · simp [digitLaneView, ProjD.ofAgent, hxq, InTok.isX]
    · simp [digitLaneView, ProjD.ofAgent, hxq, InTok.isP]
    · simp [digitLaneView, ProjD.ofAgent, hyk, QCarry.isL]

/-- **A launch on the trace opens the ledger `[u]` with the fields of the border input.**

Consumer: `sweep_step`. -/
theorem trace_launch_full {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hb : (Z.1.1 e).beta = true) (hk : (Z.1.1 e).qCarry = .OFF)
    (hs : (Z.1.1 e).qIn.isS = true) :
    ∃ u : DigitUse (compileAdvice (ceilLogTwo n)) n,
      ((topFixedTraceNext ring C Z e).1.2.current e).comparison.carry =
        some { inherited := none, uses := [u] } ∧
      u.time = Z.1.2.clock + 1 ∧ u.target = e ∧
      u.operand = (Z.1.2.current e).comparison.input ∧
      u.value = inV (compileAdvice (ceilLogTwo n)) (Z.1.1 e).qIn ∧
      u.tail = inT (Z.1.1 e).qIn := by
  have hv := race_view_fields (Z.1.1 e)
  have hw := race_view_fields (Z.1.1 (ring.rightNeighbor e))
  rw [trace_ghost_source]
  obtain ⟨h1, h2⟩ := replay_carry_launch .comparison (Z.1.2.clock + 1) e (ring.rightNeighbor e)
    (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
    (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
      (Z.1.1 (ring.rightNeighbor e)).beta)
    (Z.1.2.current e).comparison (Z.1.2.current (ring.rightNeighbor e)).comparison
    (by rw [hv.1]; exact hxl) (by rw [hw.1]; exact hyl) (by rw [hv.2.1]; exact hb)
    (by rw [hv.2.2.2, hk]; rfl) (by rw [hv.2.2.1]; exact hs)
  refine ⟨_, h1, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [hv.2.2.1]
  · simp only [hv.2.2.1]

/-- **An advance on the trace appends the use of the responder register with its fields.**

Consumer: `sweep_step`. -/
theorem trace_advance_full {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hyb : (Z.1.1 (ring.rightNeighbor e)).beta = false)
    (hxk : (Z.1.1 e).qCarry.isL = true)
    (hyk : (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF)
    (hys : (Z.1.1 (ring.rightNeighbor e)).qIn.isS = true)
    (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
    (hL : (Z.1.2.current e).comparison.carry = some L) :
    ∃ u : DigitUse (compileAdvice (ceilLogTwo n)) n,
      ((topFixedTraceNext ring C Z e).1.2.current e).comparison.carry = none ∧
      ((topFixedTraceNext ring C Z e).1.2.current (ring.rightNeighbor e)).comparison.carry =
        some { L with uses := L.uses ++ [u] } ∧
      u.time = Z.1.2.clock + 1 ∧ u.target = ring.rightNeighbor e ∧
      u.operand = (Z.1.2.current (ring.rightNeighbor e)).comparison.input ∧
      u.value = inV (compileAdvice (ceilLogTwo n)) (Z.1.1 (ring.rightNeighbor e)).qIn ∧
      u.tail = inT (Z.1.1 (ring.rightNeighbor e)).qIn := by
  have hv := race_view_fields (Z.1.1 e)
  have hw := race_view_fields (Z.1.1 (ring.rightNeighbor e))
  rw [trace_ghost_source, trace_ghost_responder ring C Z e hne]
  obtain ⟨h1, h2⟩ := replay_carry_advance .comparison (Z.1.2.clock + 1) e (ring.rightNeighbor e)
    (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
    (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
      (Z.1.1 (ring.rightNeighbor e)).beta)
    (Z.1.2.current e).comparison (Z.1.2.current (ring.rightNeighbor e)).comparison L
    (by rw [hv.1]; exact hxl) (by rw [hw.1]; exact hyl) (by rw [hw.2.1]; exact hyb)
    (by rw [hv.2.2.2]; exact hxk) (by rw [hw.2.2.2, hyk]; rfl)
    (by rw [hw.2.2.1]; exact hys) hL
  refine ⟨_, h1, h2, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [hw.2.2.1]
  · simp only [hw.2.2.1]

/-- **A service into the host from the left keeps the ledger of the host.**

Consumer: `sweep_step`. -/
theorem trace_host_keep {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hyk : (Z.1.1 (ring.rightNeighbor e)).qCarry.isL = true) :
    ((topFixedTraceNext ring C Z e).1.2.current (ring.rightNeighbor e)).comparison.carry =
      (Z.1.2.current (ring.rightNeighbor e)).comparison.carry := by
  have hv := race_view_fields (Z.1.1 e)
  have hw := race_view_fields (Z.1.1 (ring.rightNeighbor e))
  rw [trace_ghost_responder ring C Z e hne]
  apply replay_carry_keep_resp
  · rw [hv.1]; exact hxl
  · rw [hw.1]; exact hyl
  · rw [hw.2.2.2]; exact hyk

end MarkedCells
end L3

#print axioms L3.MarkedCells.launch_resp_keep
#print axioms L3.MarkedCells.trace_launch_full
#print axioms L3.MarkedCells.trace_advance_full
#print axioms L3.MarkedCells.trace_host_keep
