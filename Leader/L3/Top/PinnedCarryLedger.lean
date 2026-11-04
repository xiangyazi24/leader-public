import Leader.L3.Top.PinnedExportList

/-!
# Q7 (P.12 preparation): row lemmas for the carry ledger sweep

Which lane-replay rows keep the carry ledger of a host, the carry ledger of a non-host, and the
ghost input atom of a settled register.

Consumer: `Leader/L3/TopPinnedCarrySweep.lean` (not yet written).
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- A live carry at the responder keeps its ledger.

Consumer: the ledger sweep. -/
theorem replay_carry_keep_resp {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n) (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n)
    (hxl : x.leader = false) (hyl : y.leader = false) (hyk : y.carryLive = true) :
    (digitLaneReplay lane time source destination x y gx gy).y.carry = gy.carry := by
  unfold digitLaneReplay
  by_cases hxk : x.carryLive = true
  · simp [hxl, hyl, hyk, hxk]
  · have hxk' : x.carryLive = false := by simpa using hxk
    simp [hxl, hyl, hyk, hxk']

/-- A register without a live carry that is not a launching source keeps its ledger, and so
does its responder.

Consumer: the ledger sweep. -/
theorem replay_carry_frame {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n) (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n)
    (hxl : x.leader = false) (hyl : y.leader = false) (hxk : x.carryLive = false)
    (hxm : x.marker = false) :
    (digitLaneReplay lane time source destination x y gx gy).x.carry = gx.carry ∧
    (digitLaneReplay lane time source destination x y gx gy).y.carry = gy.carry := by
  unfold digitLaneReplay
  simp [hxl, hyl, hxk, hxm]

/-- A launch leaves the input atom of a non-marker responder alone.

Consumer: the ledger sweep. -/
theorem replay_input_launch_resp {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n) (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n)
    (hxl : x.leader = false) (hyl : y.leader = false) (hym : y.marker = false)
    (hxm : x.marker = true) (hxk : x.carryLive = false) (hxs : x.input.isS = true)
    (hxi : x.input.isX = false) (hxp : x.input.isP = false) (hyk : y.carryLive = false) :
    (digitLaneReplay lane time source destination x y gx gy).y.input = gy.input := by
  rw [replay_input_y_eq]
  unfold replayChain
  simp [hxl, hyl, hym, hxm, hxk, hxs, hxi, hxp, hyk, stepSettled, stepCarryX, stepCarryY,
    stepFront, stepSuccess, stepLaunch, stepPending]

/-- A settled marker responder without a carry keeps its input atom, whatever the source is.

Consumer: the ledger sweep. -/
theorem replay_input_marker_resp {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n) (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n)
    (hxl : x.leader = false) (hyl : y.leader = false) (hym : y.marker = true)
    (hys : y.input.isS = true) (hyk : y.carryLive = false) (hye : y.input.isE = false) :
    (digitLaneReplay lane time source destination x y gx gy).y.input = gy.input := by
  rw [replay_input_y_eq]
  unfold replayChain
  rcases hxm : x.marker <;> rcases hxk : x.carryLive <;> rcases hxi : x.input with _ | _ | ⟨a, t⟩ | ⟨a, t⟩ <;>
    (try cases t) <;>
    simp [hxl, hyl, hym, hye, hyk, hxm, hxk, hxi, stepSettled, stepCarryX, stepCarryY, stepFront,
      stepSuccess, stepLaunch, stepPending, inT, InTok.isS, InTok.isP, InTok.isX]

end MarkedCells
end L3

#print axioms L3.MarkedCells.replay_carry_keep_resp
#print axioms L3.MarkedCells.replay_carry_frame
#print axioms L3.MarkedCells.replay_input_launch_resp
#print axioms L3.MarkedCells.replay_input_marker_resp
