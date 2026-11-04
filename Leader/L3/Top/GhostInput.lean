import Leader.L3.Target

/-!
# Q7: where a ghost comparison input atom can come from

The audit ghost keeps, for every site, the atom of its comparison input.  The pending
clause of the repaired coloured cut (`TopRepairedClasses`) is a statement about these atoms,
so the P.4--P.5 potential with the old-pending term has to know how one service moves
them.  `digitLaneReplay` computes the input atoms by a chain of nine guarded updates; the
chain is restated here step by step (`replayChain`; equality with the original is `rfl`) and
the provenance of the result is proved:

* the x slot is empty or keeps the old x atom;
* the y slot is empty, keeps the old y atom, receives the old x atom (a pending move or an
  erasure front), or receives the old x *output* atom, and then the service is an accepted
  offer and the export recorded in the same service has exactly this operand, the service
  time, source and destination.

`auditStep_input_x`, `auditStep_input_other`, `auditStep_input_y` transfer this to
`digitAuditStep`: every other site is unchanged, and the export of an accepted offer is a
recorded export at time `clock + 1`.

This is the ghost half of the link between the audit and the abstract cells; the physical
half (which physical row moves a pending token) is not proved here.

Consumer: the old-pending term of the P.4--P.5 potential (not yet written).
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- Provenance of a ghost input pair: the x slot is empty or the old x atom `ax`; the y slot
is empty, the old y atom `ay`, or `ax`.

Consumer: `replayChain_good`. -/
def GhostInputProv {n : Nat} (ax ay : Option (DigitAtom n)) (s : DigitInputGhost n) : Prop :=
  (s.x = none ∨ s.x = ax) ∧ (s.y = none ∨ s.y = ay ∨ s.y = ax)

/-- Carry host of x clears the x input.

Consumer: `replayChain`. -/
def stepCarryX {c : Compiled} {n : Nat} (x : DigitLaneView c) (s : DigitInputGhost n) :
    DigitInputGhost n :=
  if !s.fx && x.carryLive then { s with x := none, fx := true } else s

/-- Carry host of y clears the y input.

Consumer: `replayChain`. -/
def stepCarryY {c : Compiled} {n : Nat} (y : DigitLaneView c) (s : DigitInputGhost n) :
    DigitInputGhost n :=
  if !s.fy && y.carryLive then { s with y := none, fy := true } else s

/-- A settled non-marker tail keeps its atom.

Consumer: `replayChain`. -/
def stepSettled {c : Compiled} {n : Nat} (x : DigitLaneView c) (gx : DigitLaneGhost c n)
    (s : DigitInputGhost n) : DigitInputGhost n :=
  if !s.fx && x.input.isS && inT x.input && !x.marker then
    { s with x := gx.input, fx := true } else s

/-- An erasure front clears x and hands its atom to a settled interior y.

Consumer: `replayChain`. -/
def stepFront {c : Compiled} {n : Nat} (x y : DigitLaneView c) (gx : DigitLaneGhost c n)
    (s : DigitInputGhost n) : DigitInputGhost n :=
  if !s.fx && x.input.isX then
    let s := { s with x := none, fx := true }
    if !s.fy && !y.leader && !y.marker && y.input.isS then
      { s with y := gx.input, fy := true }
    else s
  else s

/-- A carry success clears y.

Consumer: `replayChain`. -/
def stepSuccess {c : Compiled} {n : Nat} (x y : DigitLaneView c)
    (s : DigitInputGhost n) : DigitInputGhost n :=
  if (x.carryLive && !(y.leader || y.marker) && !y.carryLive && y.input.isS) && !s.fy then
    { s with y := none, fy := true } else s

/-- A carry launch clears x.

Consumer: `replayChain`. -/
def stepLaunch {c : Compiled} {n : Nat} (x y : DigitLaneView c)
    (s : DigitInputGhost n) : DigitInputGhost n :=
  if (!x.leader && x.marker && !x.carryLive && x.input.isS && !y.leader) && !s.fx then
    { s with x := none, fx := true } else s

/-- A pending x: terminal settlement or erasure, a move into an empty carry-free y, or a
settlement before a settled y.

Consumer: `replayChain`. -/
def stepPending {c : Compiled} {n : Nat} (x y : DigitLaneView c) (gx : DigitLaneGhost c n)
    (s : DigitInputGhost n) : DigitInputGhost n :=
  if !s.fx && x.input.isP then
    if y.leader || y.marker then
      if !inT x.input then { s with x := gx.input, fx := true }
      else if !x.marker then { s with x := none, fx := true }
      else s
    else if !y.leader && !y.marker && y.input.isE && !y.carryLive && !s.fy then
      { x := none, y := gx.input, fx := true, fy := true }
    else if y.input.isS && !y.carryLive then
      { s with x := gx.input, fx := true }
    else s
  else s

/-- Consumer: `replayChain_good`. -/
theorem stepCarryX_good {c : Compiled} {n : Nat} (x : DigitLaneView c) (s : DigitInputGhost n)
    (ax ay : Option (DigitAtom n)) (h : GhostInputProv ax ay s) :
    GhostInputProv ax ay (stepCarryX x s) := by
  unfold stepCarryX
  split
  · exact ⟨Or.inl rfl, h.2⟩
  · exact h

/-- Consumer: `replayChain_good`. -/
theorem stepCarryY_good {c : Compiled} {n : Nat} (y : DigitLaneView c) (s : DigitInputGhost n)
    (ax ay : Option (DigitAtom n)) (h : GhostInputProv ax ay s) :
    GhostInputProv ax ay (stepCarryY y s) := by
  unfold stepCarryY
  split
  · exact ⟨h.1, Or.inl rfl⟩
  · exact h

/-- Consumer: `replayChain_good`. -/
theorem stepSettled_good {c : Compiled} {n : Nat} (x : DigitLaneView c)
    (gx : DigitLaneGhost c n) (s : DigitInputGhost n) (ay : Option (DigitAtom n))
    (h : GhostInputProv gx.input ay s) :
    GhostInputProv gx.input ay (stepSettled x gx s) := by
  unfold stepSettled
  split
  · exact ⟨Or.inr rfl, h.2⟩
  · exact h

/-- Consumer: `replayChain_good`. -/
theorem stepFront_good {c : Compiled} {n : Nat} (x y : DigitLaneView c)
    (gx : DigitLaneGhost c n) (s : DigitInputGhost n) (ay : Option (DigitAtom n))
    (h : GhostInputProv gx.input ay s) :
    GhostInputProv gx.input ay (stepFront x y gx s) := by
  unfold stepFront
  split
  · dsimp only
    split
    · exact ⟨Or.inl rfl, Or.inr (Or.inr rfl)⟩
    · exact ⟨Or.inl rfl, h.2⟩
  · exact h

/-- Consumer: `replayChain_good`. -/
theorem stepSuccess_good {c : Compiled} {n : Nat} (x y : DigitLaneView c)
    (s : DigitInputGhost n) (ax ay : Option (DigitAtom n)) (h : GhostInputProv ax ay s) :
    GhostInputProv ax ay (stepSuccess x y s) := by
  unfold stepSuccess
  split
  · exact ⟨h.1, Or.inl rfl⟩
  · exact h

/-- Consumer: `replayChain_good`. -/
theorem stepLaunch_good {c : Compiled} {n : Nat} (x y : DigitLaneView c)
    (s : DigitInputGhost n) (ax ay : Option (DigitAtom n)) (h : GhostInputProv ax ay s) :
    GhostInputProv ax ay (stepLaunch x y s) := by
  unfold stepLaunch
  split
  · exact ⟨Or.inl rfl, h.2⟩
  · exact h

/-- Consumer: `replayChain_good`. -/
theorem stepPending_good {c : Compiled} {n : Nat} (x y : DigitLaneView c)
    (gx : DigitLaneGhost c n) (s : DigitInputGhost n) (ay : Option (DigitAtom n))
    (h : GhostInputProv gx.input ay s) :
    GhostInputProv gx.input ay (stepPending x y gx s) := by
  unfold stepPending
  split
  · split
    · split
      · exact ⟨Or.inr rfl, h.2⟩
      · split
        · exact ⟨Or.inl rfl, h.2⟩
        · exact h
    · split
      · exact ⟨Or.inl rfl, Or.inr (Or.inr rfl)⟩
      · split
        · exact ⟨Or.inr rfl, h.2⟩
        · exact h
  · exact h

/-- The input chain of `digitLaneReplay`, restated step by step; the second component is the
`accepted` flag.

Consumer: `digitLaneReplay_input_x`, `digitLaneReplay_input_y`. -/
def replayChain {c : Compiled} {n : Nat} (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) : DigitInputGhost n × Bool :=
  if x.leader || y.leader then
    ({ x := none, y := none, fx := true, fy := true }, false)
  else
    let s := stepPending x y gx (stepLaunch x y (stepSuccess x y (stepFront x y gx
      (stepSettled x gx (stepCarryY y (stepCarryX x
        { x := gx.input, y := gy.input, fx := false, fy := false } : DigitInputGhost n))))))
    let accepted := !s.fy && (x.out.isD && y.marker) && y.input.isE && !y.carryLive
    ((if accepted then { s with y := gx.out.atom, fy := true } else s), accepted)

/-- The restated chain is the x input of `digitLaneReplay`.

Consumer: `digitLaneReplay_input_x`. -/
theorem replay_input_x_eq {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n) (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n) :
    (digitLaneReplay lane time source destination x y gx gy).x.input =
      (replayChain x y gx gy).1.x := rfl

/-- The restated chain is the y input of `digitLaneReplay`.

Consumer: `digitLaneReplay_input_y`. -/
theorem replay_input_y_eq {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n) (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n) :
    (digitLaneReplay lane time source destination x y gx gy).y.input =
      (replayChain x y gx gy).1.y := rfl

/-- The export of `digitLaneReplay` is made exactly when the chain accepts.

Consumer: `digitLaneReplay_input_y`. -/
theorem replay_exported_eq {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n) (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n) :
    (digitLaneReplay lane time source destination x y gx gy).exported =
      (if (replayChain x y gx gy).2 then
        some { time := time, lane := lane, source := source, destination := destination,
               operand := gx.out.atom, value := outV c x.out, tail := outT x.out }
       else none) := rfl

/-- Provenance of the ghost input pair after one service: the x slot is empty or keeps the
old x atom; the y slot is empty, keeps the old y atom, receives the old x atom (a move or
front), or is the old x output atom in an accepted service.

Consumer: `digitLaneReplay_input_x`, `digitLaneReplay_input_y`. -/
theorem replayChain_good {c : Compiled} {n : Nat} (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) :
    ((replayChain x y gx gy).1.x = none ∨ (replayChain x y gx gy).1.x = gx.input) ∧
    ((replayChain x y gx gy).1.y = none ∨ (replayChain x y gx gy).1.y = gy.input ∨
      (replayChain x y gx gy).1.y = gx.input ∨
      ((replayChain x y gx gy).2 = true ∧
        (replayChain x y gx gy).1.y = gx.out.atom)) := by
  unfold replayChain
  split
  · exact ⟨Or.inl rfl, Or.inl rfl⟩
  · dsimp only
    have h0 : GhostInputProv gx.input gy.input
        ({ x := gx.input, y := gy.input, fx := false, fy := false } : DigitInputGhost n) :=
      ⟨Or.inr rfl, Or.inr (Or.inl rfl)⟩
    have h1 := stepPending_good x y gx _ gy.input
      (stepLaunch_good x y _ _ _
        (stepSuccess_good x y _ _ _
          (stepFront_good x y gx _ gy.input
            (stepSettled_good x gx _ gy.input
              (stepCarryY_good y _ _ _ (stepCarryX_good x _ _ _ h0))))))
    split
    · rename_i hacc
      exact ⟨h1.1, Or.inr (Or.inr (Or.inr ⟨hacc, rfl⟩))⟩
    · exact ⟨h1.1, h1.2.elim Or.inl (fun h => h.elim (fun h => Or.inr (Or.inl h))
        (fun h => Or.inr (Or.inr (Or.inl h))))⟩

/-- Ghost input of the x slot after a service.

Consumer: `auditStep_input_x`. -/
theorem digitLaneReplay_input_x {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n) (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n) :
    (digitLaneReplay lane time source destination x y gx gy).x.input = none ∨
    (digitLaneReplay lane time source destination x y gx gy).x.input = gx.input := by
  rw [replay_input_x_eq]
  exact (replayChain_good x y gx gy).1

/-- Ghost input of the y slot after a service: empty, the old y atom, the old x atom, or
the old x output atom of an accepted offer, in which case the export recorded by the same
service has exactly this operand, the service time, source and destination, and the
responder is a marker with an empty input.

Consumer: `auditStep_input_y`. -/
theorem digitLaneReplay_input_y {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n) (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n) :
    (digitLaneReplay lane time source destination x y gx gy).y.input = none ∨
    (digitLaneReplay lane time source destination x y gx gy).y.input = gy.input ∨
    (digitLaneReplay lane time source destination x y gx gy).y.input = gx.input ∨
    (x.out.isD = true ∧ y.marker = true ∧ y.input.isE = true ∧
      (digitLaneReplay lane time source destination x y gx gy).y.input = gx.out.atom ∧
      ∃ e : DigitExport c n,
        (digitLaneReplay lane time source destination x y gx gy).exported = some e ∧
        e.operand = gx.out.atom ∧ e.time = time ∧ e.source = source ∧
        e.destination = destination ∧ e.lane = lane) := by
  rw [replay_input_y_eq]
  rcases (replayChain_good x y gx gy).2 with h | h | h | ⟨hacc, hy⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr ?_))
    have hexp := replay_exported_eq lane time source destination x y gx gy
    rw [if_pos hacc] at hexp
    have hacc' := hacc
    unfold replayChain at hacc'
    split at hacc'
    · exact absurd hacc' Bool.false_ne_true
    · dsimp only at hacc'
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hacc'
      obtain ⟨⟨⟨_, hd, hm⟩, he⟩, _⟩ := hacc'
      exact ⟨hd, hm, he, hy, _, hexp, rfl, rfl, rfl, rfl, rfl⟩

/-- Audit step, source site: the ghost comparison input is emptied or kept.

Consumer: the no-raise row of the pending potential. -/
theorem auditStep_input_x {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n) :
    ((digitAuditStep ring S A e).current e).comparison.input = none ∨
    ((digitAuditStep ring S A e).current e).comparison.input =
      (A.current e).comparison.input := by
  have h := digitLaneReplay_input_x .comparison (A.clock + 1) e (ring.rightNeighbor e)
    (digitLaneView .comparison (S e) (S e).word.beta)
    (digitLaneView .comparison (S (ring.rightNeighbor e)) (S (ring.rightNeighbor e)).word.beta)
    (A.current e).comparison (A.current (ring.rightNeighbor e)).comparison
  simpa [digitAuditStep, digitGhostStep, digitService] using h

/-- Audit step, other sites keep their ghost input.

Consumer: the no-raise row of the pending potential. -/
theorem auditStep_input_other {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (S : Fin n → ProjD c) (A : DigitAudit c n) (e v : Fin n) (h1 : v ≠ e)
    (h2 : v ≠ ring.rightNeighbor e) :
    ((digitAuditStep ring S A e).current v).comparison.input =
      (A.current v).comparison.input := by
  simp [digitAuditStep, digitGhostStep, h1, h2]

/-- Audit step, responder site (on a non-loop edge): the ghost comparison input is emptied,
kept, received from the source, or is the operand of an export recorded by this very step
(time `clock + 1`, source `e`, destination the responder).

Consumer: the acceptance row of the pending potential. -/
theorem auditStep_input_y {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    (((digitAuditStep ring S A e).current (ring.rightNeighbor e)).comparison.input = none ∨
    ((digitAuditStep ring S A e).current (ring.rightNeighbor e)).comparison.input =
      (A.current (ring.rightNeighbor e)).comparison.input ∨
    ((digitAuditStep ring S A e).current (ring.rightNeighbor e)).comparison.input =
      (A.current e).comparison.input) ∨
    ∃ ex : DigitExport c n,
      DigitRecordedExport (digitAuditStep ring S A e) ex ∧ ex.lane = .comparison ∧
      ex.time = A.clock + 1 ∧ ex.source = e ∧ ex.destination = ring.rightNeighbor e ∧
      ((digitAuditStep ring S A e).current (ring.rightNeighbor e)).comparison.input =
        ex.operand := by
  have h := digitLaneReplay_input_y .comparison (A.clock + 1) e (ring.rightNeighbor e)
    (digitLaneView .comparison (S e) (S e).word.beta)
    (digitLaneView .comparison (S (ring.rightNeighbor e)) (S (ring.rightNeighbor e)).word.beta)
    (A.current e).comparison (A.current (ring.rightNeighbor e)).comparison
  have hcur : ((digitAuditStep ring S A e).current (ring.rightNeighbor e)).comparison =
      (digitLaneReplay .comparison (A.clock + 1) e (ring.rightNeighbor e)
        (digitLaneView .comparison (S e) (S e).word.beta)
        (digitLaneView .comparison (S (ring.rightNeighbor e))
          (S (ring.rightNeighbor e)).word.beta)
        (A.current e).comparison (A.current (ring.rightNeighbor e)).comparison).y := by
    simp [digitAuditStep, digitGhostStep, digitService, hne]
  rw [hcur]
  rcases h with h | h | h | ⟨_, _, _, hy, ex, hex, hop, htime, hsrc, hdst, hlane⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr h))
  · refine Or.inr ⟨ex, ?_, hlane, htime, hsrc, hdst, ?_⟩
    · refine ⟨_, List.mem_cons_self .., htime.symm, hsrc.symm, ?_⟩
      simpa [digitService, digitReceiptLane, hlane] using hex
    · rw [hy, hop]

end MarkedCells
end L3

#print axioms L3.MarkedCells.replayChain_good
#print axioms L3.MarkedCells.digitLaneReplay_input_x
#print axioms L3.MarkedCells.digitLaneReplay_input_y
#print axioms L3.MarkedCells.auditStep_input_x
#print axioms L3.MarkedCells.auditStep_input_other
#print axioms L3.MarkedCells.auditStep_input_y
