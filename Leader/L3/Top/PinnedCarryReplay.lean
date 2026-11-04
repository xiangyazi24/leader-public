import Leader.L3.Top.PinnedSweepCells
import Leader.L3.Top.FinalMobileCost
import Leader.L3.Top.PinnedClasses

/-!
# Q7 (P.12 preparation): the carry ledger of a lane replay

The audit ghost of the comparison carry: a launch at a non-leader marker with a settled input
opens a fresh ledger with one use, each successful advance appends one use at the responder, and
a carry that meets the next marker records a terminal carrying the ledger.  This is the carry
part (`J.carry`) of the preparation certificate, at the level of one service.

Consumer: the aligned-completion half of `TopClockFavourablePhase` (not yet proved).
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- **A launch opens a fresh ledger with one use.**

Consumer: `audit_carry_launch`. -/
theorem replay_carry_launch {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n) (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n)
    (hxl : x.leader = false) (hyl : y.leader = false) (hm : x.marker = true)
    (hk : x.carryLive = false) (hs : x.input.isS = true) :
    (digitLaneReplay lane time source destination x y gx gy).x.carry =
      some { inherited := none
             uses := [{ time := time, target := source, operand := gx.input,
                        value := inV c x.input, tail := inT x.input, targetDigit := x.digit,
                        carryIn := true, errorIn := false }] } ∧
    (digitLaneReplay lane time source destination x y gx gy).y.carry = gy.carry := by
  unfold digitLaneReplay
  simp [hxl, hyl, hm, hk, hs]

/-- **A successful advance appends one use at the responder and empties the host.**

Consumer: `audit_carry_advance`. -/
theorem replay_carry_advance {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n) (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n)
    (L : DigitCarryGhost c n)
    (hxl : x.leader = false) (hyl : y.leader = false) (hym : y.marker = false)
    (hxk : x.carryLive = true) (hyk : y.carryLive = false) (hys : y.input.isS = true)
    (hL : gx.carry = some L) :
    (digitLaneReplay lane time source destination x y gx gy).x.carry = none ∧
    (digitLaneReplay lane time source destination x y gx gy).y.carry =
      some { L with
        uses := L.uses ++ [{ time := time, target := destination, operand := gy.input,
                             value := inV c y.input, tail := inT y.input,
                             targetDigit := y.digit, carryIn := x.carryBit,
                             errorIn := x.carryError }] } := by
  unfold digitLaneReplay
  simp [hxl, hyl, hym, hxk, hyk, hys, hL]

/-- **A carry that meets the next marker records a terminal carrying its ledger.**

Consumer: `audit_carry_terminal`. -/
theorem replay_carry_terminal {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n) (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n)
    (hxl : x.leader = false) (hyl : y.leader = false) (hym : y.marker = true)
    (hxk : x.carryLive = true) :
    (digitLaneReplay lane time source destination x y gx gy).terminal =
      some { time := time, lane := lane, source := source, destination := destination,
             ledger := gx.carry, carryBit := x.carryBit, errorBit := x.carryError } := by
  unfold digitLaneReplay
  simp [hxl, hyl, hym, hxk]

/-- The comparison ghost of the source after a service is the source half of the replay.

Consumer: `trace_carry_launch`. -/
theorem trace_ghost_source {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n) :
    ((topFixedTraceNext ring C Z e).1.2.current e).comparison =
      (digitLaneReplay .comparison (Z.1.2.clock + 1) e (ring.rightNeighbor e)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
          (Z.1.1 (ring.rightNeighbor e)).beta)
        (Z.1.2.current e).comparison (Z.1.2.current (ring.rightNeighbor e)).comparison).x := by
  simp [topFixedTraceNext, digitAuditStep, digitGhostStep, digitService, piD]
  rfl

/-- The comparison ghost of the responder after a service is the responder half of the replay.

Consumer: `trace_carry_advance`. -/
theorem trace_ghost_responder {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n) (hne : ring.rightNeighbor e ≠ e) :
    ((topFixedTraceNext ring C Z e).1.2.current (ring.rightNeighbor e)).comparison =
      (digitLaneReplay .comparison (Z.1.2.clock + 1) e (ring.rightNeighbor e)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
          (Z.1.1 (ring.rightNeighbor e)).beta)
        (Z.1.2.current e).comparison (Z.1.2.current (ring.rightNeighbor e)).comparison).y := by
  simp [topFixedTraceNext, digitAuditStep, digitGhostStep, digitService, piD, hne]
  rfl

/-- **A launch on the trace opens a fresh ledger with one use.**

Consumer: the aligned-completion half of `TopClockFavourablePhase` (not yet proved). -/
theorem trace_carry_launch {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hb : (Z.1.1 e).beta = true) (hk : (Z.1.1 e).qCarry = .OFF)
    (hs : (Z.1.1 e).qIn.isS = true) :
    ∃ u : DigitUse (compileAdvice (ceilLogTwo n)) n,
      ((topFixedTraceNext ring C Z e).1.2.current e).comparison.carry =
        some { inherited := none, uses := [u] } ∧
      u.time = Z.1.2.clock + 1 ∧ u.target = e ∧
      u.operand = (Z.1.2.current e).comparison.input := by
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
  exact ⟨_, h1, rfl, rfl, rfl⟩

/-- **An advance on the trace appends one use at the responder and empties the host.**

Consumer: the aligned-completion half of `TopClockFavourablePhase` (not yet proved). -/
theorem trace_carry_advance {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
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
      u.operand = (Z.1.2.current (ring.rightNeighbor e)).comparison.input := by
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
  exact ⟨_, h1, h2, rfl, rfl, rfl⟩

/-- **A carry that meets the next marker records a terminal on the trace, carrying the ledger of
the host.**

Consumer: the aligned-completion half of `TopClockFavourablePhase` (not yet proved). -/
theorem trace_carry_terminal {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hyb : (Z.1.1 (ring.rightNeighbor e)).beta = true)
    (hxk : (Z.1.1 e).qCarry.isL = true) :
    ∃ t : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
      DigitRecordedTerminal (topFixedTraceNext ring C Z e).1.2 t ∧
      t.lane = .comparison ∧ t.time = Z.1.2.clock + 1 ∧ t.source = e ∧
      t.destination = ring.rightNeighbor e ∧
      t.ledger = (Z.1.2.current e).comparison.carry := by
  have hv := race_view_fields (Z.1.1 e)
  have hw := race_view_fields (Z.1.1 (ring.rightNeighbor e))
  have h1 := replay_carry_terminal .comparison (Z.1.2.clock + 1) e (ring.rightNeighbor e)
    (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
    (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
      (Z.1.1 (ring.rightNeighbor e)).beta)
    (Z.1.2.current e).comparison (Z.1.2.current (ring.rightNeighbor e)).comparison
    (by rw [hv.1]; exact hxl) (by rw [hw.1]; exact hyl) (by rw [hw.2.1]; exact hyb)
    (by rw [hv.2.2.2]; exact hxk)
  obtain ⟨t, ht⟩ : ∃ t : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
      (digitLaneReplay .comparison (Z.1.2.clock + 1) e (ring.rightNeighbor e)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
          (Z.1.1 (ring.rightNeighbor e)).beta)
        (Z.1.2.current e).comparison (Z.1.2.current (ring.rightNeighbor e)).comparison).terminal
        = some t := ⟨_, h1⟩
  have ht0 := ht
  rw [h1] at ht
  have ht' := Option.some.inj ht
  have hl : t.lane = DigitLane.comparison := by rw [← ht']
  refine ⟨t, ?_, hl, ?_, ?_, ?_, ?_⟩
  · refine ⟨_, List.mem_cons_self .., ?_, ?_, ?_⟩
    · rw [← ht']
    · rw [← ht']
    · rw [hl]; exact ht0
  all_goals rw [← ht']

end MarkedCells
end L3

#print axioms L3.MarkedCells.trace_carry_launch
#print axioms L3.MarkedCells.trace_carry_advance
#print axioms L3.MarkedCells.trace_carry_terminal
