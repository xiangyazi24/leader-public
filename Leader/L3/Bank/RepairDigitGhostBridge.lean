import Leader.L3.Bank.RepairDigitRecording

/-!
# T26 items 1-2: lane-view bridge, pass-through ghost rows, one frame per letter

* Item 1: `laneGhost`, `laneMarkerX`/`laneMarkerY` and the lane-generic identification of the
  service receipts with the lane replay on the projected-record fields (`serviceLane`), with the
  writer border bit equal to `word.beta` whenever the pair betas are preserved
  (`laneMarkerXBeta`); the T25 recording lemmas restated on those fields (`recordUnreadReadD`,
  `recordDeliveryD`, `recordCarryUseD`, `recordTerminalD`).
* F1: the ghost rows of the replay as functions of the masked shapes (`replayPipe`,
  `replayDel`, `replayFin`, `replayTerm`, `replayEntry`).
* F2: each audit letter prepends exactly one frame stamped `clock + 1` (`auditStepFrame`), and
  the frame times are strictly decreasing and bounded by the clock along every run from
  `digitAuditInitial` (`AuditFrameOrder`, `auditFrameOrderWord`, `auditFrameTimeInj`).
-/

namespace L3.GhostBridge

set_option autoImplicit false

open L3.RenewalReferenceClock
open L3.Recording

/-! ### Item 1: lane-generic bridge -/

/-- The lane component of a digit ghost. -/
def laneGhost {c : Compiled} {n : Nat} (lane : DigitLane) (g : DigitGhost c n) :
    DigitLaneGhost c n :=
  match lane with
  | .writer => g.writer
  | .comparison => g.comparison

/-- The border bit of the left view used by `digitService` on a lane. -/
def laneMarkerX {c : Compiled} (lane : DigitLane) (X Y : ProjD c) : Bool :=
  match lane with
  | .writer => (workerW X.word Y.word).betaX
  | .comparison => X.word.beta

/-- The border bit of the right view used by `digitService` on a lane. -/
def laneMarkerY {c : Compiled} (lane : DigitLane) (X Y : ProjD c) : Bool :=
  match lane with
  | .writer => (workerW X.word Y.word).betaY
  | .comparison => Y.word.beta

section Bridge

variable {c : Compiled} {n : Nat}

theorem laneViewLeader (lane : DigitLane) (X : ProjD c) (m : Bool) :
    (digitLaneView lane X m).leader = X.word.native.l := by
  cases lane <;> rfl

theorem laneViewMarker (lane : DigitLane) (X : ProjD c) (m : Bool) :
    (digitLaneView lane X m).marker = m := by
  cases lane <;> rfl

theorem laneViewDigit (lane : DigitLane) (X : ProjD c) (m : Bool) :
    (digitLaneView lane X m).digit = X.top.d := by
  cases lane <;> rfl

theorem laneViewOut (lane : DigitLane) (X : ProjD c) (m : Bool) :
    (digitLaneView lane X m).out = bankRepairDigitLaneOut lane X.top := by
  cases lane <;> rfl

theorem laneViewIn (lane : DigitLane) (X : ProjD c) (m : Bool) :
    (digitLaneView lane X m).input = bankRepairDigitLaneIn lane X.top := by
  cases lane <;> rfl

theorem laneViewLive (lane : DigitLane) (X : ProjD c) (m : Bool) :
    (digitLaneView lane X m).carryLive = bankRepairDigitLaneLive lane X.top := by
  cases lane <;> rfl

/-- The service's lane receipt is the lane replay on the lane views of the projected records. -/
theorem serviceLane (lane : DigitLane) (time : Nat) (source destination : Fin n)
    (X Y : ProjD c) (gx gy : DigitGhost c n) :
    digitReceiptLane lane (digitService time source destination X Y gx gy) =
      digitLaneReplay lane time source destination
        (digitLaneView lane X (laneMarkerX lane X Y))
        (digitLaneView lane Y (laneMarkerY lane X Y)) (laneGhost lane gx) (laneGhost lane gy) := by
  cases lane <;> rfl

theorem serviceLaneX (lane : DigitLane) (time : Nat) (source destination : Fin n)
    (X Y : ProjD c) (gx gy : DigitGhost c n) :
    laneGhost lane (digitService time source destination X Y gx gy).x =
      (digitReceiptLane lane (digitService time source destination X Y gx gy)).x := by
  cases lane <;> rfl

theorem serviceLaneY (lane : DigitLane) (time : Nat) (source destination : Fin n)
    (X Y : ProjD c) (gx gy : DigitGhost c n) :
    laneGhost lane (digitService time source destination X Y gx gy).y =
      (digitReceiptLane lane (digitService time source destination X Y gx gy)).y := by
  cases lane <;> rfl

/-- With the pair betas preserved (BANK: `bankRepairDigitLeadBankEdge`), both lanes read the
border bit `word.beta`. -/
theorem laneMarkerXBeta (lane : DigitLane) (X Y : ProjD c)
    (hbX : (pairW X.word Y.word).1.beta = X.word.beta) :
    laneMarkerX lane X Y = X.word.beta := by
  cases lane
  · exact hbX
  · rfl

theorem laneMarkerYBeta (lane : DigitLane) (X Y : ProjD c)
    (hbY : (pairW X.word Y.word).2.beta = Y.word.beta) :
    laneMarkerY lane X Y = Y.word.beta := by
  cases lane
  · exact hbY
  · rfl

/-- Lane-view masked shapes are the masked shapes of the record fields. -/
theorem laneViewOutSh (lane : DigitLane) (X : ProjD c) (m : Bool) :
    bankRepairDigitOutShOf (digitLaneView lane X m).out =
      bankRepairDigitOutShOf (bankRepairDigitLaneOut lane X.top) := by
  rw [laneViewOut]

theorem laneViewInSh (lane : DigitLane) (X : ProjD c) (m : Bool) :
    bankRepairDigitInShOf (digitLaneView lane X m).input =
      bankRepairDigitInShOf (bankRepairDigitLaneIn lane X.top) := by
  rw [laneViewIn]

variable (lane : DigitLane) (time : Nat) (source destination : Fin n) (X Y : ProjD c)
  (gx gy : DigitGhost c n)

/-- `recordUnreadRead` on the record fields. -/
theorem recordUnreadReadD (hlx : X.word.native.l = false) (hly : Y.word.native.l = false)
    (hU : bankRepairDigitOutShOf (bankRepairDigitLaneOut lane X.top) = .U) :
    ∃ s, (digitReceiptLane lane (digitService time source destination X Y gx gy)).sample =
        some s ∧
      s.id = DigitStamp.mk time source lane ∧ s.tail = laneMarkerX lane X Y ∧
      s.value = X.top.d ∧
      (laneGhost lane (digitService time source destination X Y gx gy).x).out =
        .packet (some (.sampled s.id)) := by
  obtain ⟨s, h1, h2, -, h4, h5, -, h7, -⟩ := recordUnreadRead lane time source destination
    (digitLaneView lane X (laneMarkerX lane X Y)) (digitLaneView lane Y (laneMarkerY lane X Y))
    (laneGhost lane gx) (laneGhost lane gy)
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly)
    (by rw [laneViewOutSh]; exact hU)
  rw [serviceLaneX, serviceLane]
  refine ⟨s, h1, h2, ?_, ?_, h7⟩
  · rw [h4, laneViewMarker]
  · rw [h5, laneViewDigit]

/-- `recordDelivery` on the record fields. -/
theorem recordDeliveryD (hlx : X.word.native.l = false) (hly : Y.word.native.l = false)
    (hmy : laneMarkerY lane X Y = true) {T : Bool}
    (hD : bankRepairDigitOutShOf (bankRepairDigitLaneOut lane X.top) = .D T)
    (hiy : bankRepairDigitInShOf (bankRepairDigitLaneIn lane Y.top) = .E)
    (hky : bankRepairDigitLaneLive lane Y.top = false) :
    ∃ ex, (digitReceiptLane lane (digitService time source destination X Y gx gy)).exported =
        some ex ∧
      ex.operand = (laneGhost lane gx).out.atom ∧ ex.time = time ∧ ex.lane = lane ∧
      ex.source = source ∧ ex.destination = destination ∧ ex.tail = T ∧
      (laneGhost lane (digitService time source destination X Y gx gy).y).input =
        (laneGhost lane gx).out.atom := by
  obtain ⟨ex, h1, h2, h3, h4, h5, h6, -, h8, h9⟩ := recordDelivery lane time source destination
    (digitLaneView lane X (laneMarkerX lane X Y)) (digitLaneView lane Y (laneMarkerY lane X Y))
    (laneGhost lane gx) (laneGhost lane gy)
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly)
    (by rw [laneViewMarker]; exact hmy) (by rw [laneViewOutSh]; exact hD)
    (by rw [laneViewInSh]; exact hiy) (by rw [laneViewLive]; exact hky)
  rw [serviceLaneY, serviceLane]
  exact ⟨ex, h1, h2, h3, h4, h5, h6, h8, h9⟩

/-- `recordCarryUseLedger` on the record fields. -/
theorem recordCarryUseD (hlx : X.word.native.l = false) (hly : Y.word.native.l = false)
    (hmy : laneMarkerY lane X Y = false) (hkx : bankRepairDigitLaneLive lane X.top = true)
    (hky : bankRepairDigitLaneLive lane Y.top = false) {T : Bool}
    (hiy : bankRepairDigitInShOf (bankRepairDigitLaneIn lane Y.top) = .S T)
    (L : DigitCarryGhost c n) (hL : (laneGhost lane gx).carry = some L) :
    (laneGhost lane (digitService time source destination X Y gx gy).y).carry =
      some (DigitCarryGhost.mk L.inherited (L.uses ++
        [DigitUse.mk time destination (laneGhost lane gy).input
          (inV c (bankRepairDigitLaneIn lane Y.top)) T Y.top.d
          (digitLaneView lane X (laneMarkerX lane X Y)).carryBit
          (digitLaneView lane X (laneMarkerX lane X Y)).carryError])) := by
  have h := recordCarryUseLedger lane time source destination
    (digitLaneView lane X (laneMarkerX lane X Y)) (digitLaneView lane Y (laneMarkerY lane X Y))
    (laneGhost lane gx) (laneGhost lane gy)
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly)
    (by rw [laneViewMarker]; exact hmy) (by rw [laneViewLive]; exact hkx)
    (by rw [laneViewLive]; exact hky) (by rw [laneViewInSh]; exact hiy) L hL
  rw [serviceLaneY, serviceLane, h, laneViewIn, laneViewDigit]

/-- `recordTerminal` on the record fields. -/
theorem recordTerminalD (hlx : X.word.native.l = false) (hly : Y.word.native.l = false)
    (hmy : laneMarkerY lane X Y = true) (hkx : bankRepairDigitLaneLive lane X.top = true) :
    (digitReceiptLane lane (digitService time source destination X Y gx gy)).terminal =
      some (DigitTerminal.mk time lane source destination (laneGhost lane gx).carry
        (digitLaneView lane X (laneMarkerX lane X Y)).carryBit
        (digitLaneView lane X (laneMarkerX lane X Y)).carryError) := by
  rw [serviceLane]
  exact recordTerminal lane time source destination
    (digitLaneView lane X (laneMarkerX lane X Y)) (digitLaneView lane Y (laneMarkerY lane X Y))
    (laneGhost lane gx) (laneGhost lane gy)
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly)
    (by rw [laneViewMarker]; exact hmy) (by rw [laneViewLive]; exact hkx)

end Bridge

/-! ### F2: one frame per letter -/

section Frames

variable {c : Compiled} {n : Nat}

/-- Each audit letter advances the clock by one and prepends exactly one frame, stamped with the
new clock, recording the edge, the old records, the old ghosts and the service receipt. -/
theorem auditStepFrame (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (e : Fin n) :
    (digitAuditStep ring S A e).clock = A.clock + 1 ∧
    (digitAuditStep ring S A e).start = A.start ∧
    (digitAuditStep ring S A e).current = digitGhostStep ring S A.current (A.clock + 1) e ∧
    (digitAuditStep ring S A e).frames =
      DigitFrame.mk (A.clock + 1) e S A.current
        (digitService (A.clock + 1) e (ring.rightNeighbor e) (S e) (S (ring.rightNeighbor e))
          (A.current e) (A.current (ring.rightNeighbor e))) :: A.frames :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Frame times strictly decrease along the list, are positive and bounded by the clock, and
there are exactly `clock` frames. -/
def AuditFrameOrder (A : DigitAudit c n) : Prop :=
  A.frames.Pairwise (fun f g => g.time < f.time) ∧
  (∀ f, f ∈ A.frames → 0 < f.time ∧ f.time ≤ A.clock) ∧
  A.frames.length = A.clock

theorem auditFrameOrderInitial (S : Fin n → ProjD c) :
    AuditFrameOrder (digitAuditInitial S) :=
  ⟨List.Pairwise.nil, fun _ h => absurd h (List.not_mem_nil), rfl⟩

theorem auditFrameOrderStep (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (e : Fin n) (h : AuditFrameOrder A) : AuditFrameOrder (digitAuditStep ring S A e) := by
  obtain ⟨hp, hb, hl⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show List.Pairwise _ (_ :: A.frames)
    refine List.Pairwise.cons ?_ hp
    intro g hg
    have := hb g hg
    show g.time < A.clock + 1
    omega
  · intro f hf
    have hf' : f ∈ _ :: A.frames := hf
    rcases List.mem_cons.mp hf' with h | h
    · rw [h]
      show 0 < A.clock + 1 ∧ A.clock + 1 ≤ A.clock + 1
      omega
    · have := hb f h
      show 0 < f.time ∧ f.time ≤ A.clock + 1
      omega
  · show (_ :: A.frames).length = A.clock + 1
    rw [List.length_cons, hl]

/-- Two frames with the same time are the same frame. -/
theorem auditFrameTimeInj (A : DigitAudit c n) (h : AuditFrameOrder A) (f g : DigitFrame c n)
    (hf : f ∈ A.frames) (hg : g ∈ A.frames) (ht : f.time = g.time) : f = g := by
  have key : ∀ l : List (DigitFrame c n), l.Pairwise (fun f g => g.time < f.time) →
      f ∈ l → g ∈ l → f = g := by
    intro l
    induction l with
    | nil => intro _ hf _; exact absurd hf (List.not_mem_nil)
    | cons a rest ih =>
        intro hp hf hg
        rcases List.pairwise_cons.mp hp with ⟨ha, hr⟩
        rcases List.mem_cons.mp hf with h1 | h1 <;> rcases List.mem_cons.mp hg with h2 | h2
        · rw [h1, h2]
        · have := ha g h2
          rw [← h1] at this
          omega
        · have := ha f h1
          rw [← h2] at this
          omega
        · exact ih hr h1 h2
  exact key A.frames h.1 hf hg

/-- Old frames survive one letter. -/
theorem auditFrameMemStep (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (e : Fin n) (f : DigitFrame c n) (hf : f ∈ A.frames) :
    f ∈ (digitAuditStep ring S A e).frames :=
  List.mem_cons.mpr (Or.inr hf)

/-- Every frame of the stepped audit is old or the new frame stamped `clock + 1`. -/
theorem auditFrameMemStepCases (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n) (f : DigitFrame c n)
    (hf : f ∈ (digitAuditStep ring S A e).frames) :
    f ∈ A.frames ∨
      f = DigitFrame.mk (A.clock + 1) e S A.current
        (digitService (A.clock + 1) e (ring.rightNeighbor e) (S e) (S (ring.rightNeighbor e))
          (A.current e) (A.current (ring.rightNeighbor e))) := by
  rcases List.mem_cons.mp hf with h | h
  · exact Or.inr h
  · exact Or.inl h

end Frames

section RunFrames

variable {n : Nat} (ring : DirectedRing n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

/-- Run level: the coupled BANK x audit chain keeps the frame order; the clock grows by the
word length, and so does the frame count. -/
theorem auditFrameOrderWord (word : List (Fin n)) :
    ∀ q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      AuditFrameOrder q.2 →
      AuditFrameOrder (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) q).2 ∧
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) q).2.clock =
        q.2.clock + word.length := by
  induction word with
  | nil => intro q h; exact ⟨h, rfl⟩
  | cons e rest ih =>
      intro q h
      obtain ⟨h1, h2⟩ := ih (bankRepairDigitBoundaryAuditNext ring hbank q e)
        (auditFrameOrderStep ring _ q.2 e h)
      refine ⟨h1, ?_⟩
      rw [List.foldl_cons, h2, List.length_cons]
      show q.2.clock + 1 + rest.length = q.2.clock + (rest.length + 1)
      omega

end RunFrames

/-! ### F1: the ghost rows of the replay on masked shapes -/

section Rows

variable {c : Compiled} {n : Nat}

/-- Ghost outputs across a Pipe edge (internal right end). -/
def ghostPipe (stamp : DigitStamp n) (bx : Bool) (ox oy : BankRepairDigitOutSh)
    (gxo gyo : DigitOutGhost n) : DigitOutGhost n × DigitOutGhost n :=
  match ox with
  | .D T =>
      match oy with
      | .E => ((if T then .unread (.afterTail stamp gxo.atom) else .empty), .packet gxo.atom)
      | _ => (gxo, gyo)
  | .U => (.packet (some (.sampled stamp)), gyo)
  | .E => ((if bx then .unread (.bootstrap stamp) else gxo), gyo)

/-- Ghost output of the source and ghost input of the delimiter across the delivery edge. -/
def ghostDel (stamp : DigitStamp n) (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxo : DigitOutGhost n) (gyi : Option (DigitAtom n)) :
    DigitOutGhost n × Option (DigitAtom n) :=
  match ox with
  | .D T =>
      if ky then (gxo, none)
      else
        match iy with
        | .E => ((if T then .unread (.afterTail stamp gxo.atom) else .empty), gxo.atom)
        | _ => (gxo, gyi)
  | .U => (.packet (some (.sampled stamp)), if ky then none else gyi)
  | .E => (gxo, if ky then none else gyi)

/-- The delivery edge accepts (and exports) exactly on a data packet into an empty, carry-free
delimiter input. -/
def delAccept (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool) : Bool :=
  match ox, iy with
  | .D _, .E => !ky
  | _, _ => false

def shS : BankRepairDigitInSh → Bool
  | .S _ => true
  | _ => false

/-- A pending left input moves into an empty right input unless the right carry is live. -/
def finXP (iy : BankRepairDigitInSh) (ky : Bool) (gxi : Option (DigitAtom n)) :
    Option (DigitAtom n) :=
  match iy with
  | .E => if ky then gxi else none
  | _ => gxi

def finYX (iy : BankRepairDigitInSh) (gxi gyi : Option (DigitAtom n)) : Option (DigitAtom n) :=
  match iy with
  | .S _ => gxi
  | _ => gyi

def finYP (iy : BankRepairDigitInSh) (gxi gyi : Option (DigitAtom n)) : Option (DigitAtom n) :=
  match iy with
  | .E => gxi
  | _ => gyi

/-- Left ghost input across a Fin edge. -/
def finInX (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxi : Option (DigitAtom n)) : Option (DigitAtom n) :=
  if kx then none
  else
    match ix with
    | .E => gxi
    | .X => none
    | .S _ => if bx then none else gxi
    | .P _ => finXP iy ky gxi

/-- Right ghost input across a Fin edge, carry-free case. -/
def finInYFree (ix iy : BankRepairDigitInSh) (gxi gyi : Option (DigitAtom n)) :
    Option (DigitAtom n) :=
  match ix with
  | .X => finYX iy gxi gyi
  | .P _ => finYP iy gxi gyi
  | _ => gyi

/-- Right ghost input across a Fin edge. -/
def finInY (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh) (ky : Bool)
    (gxi gyi : Option (DigitAtom n)) : Option (DigitAtom n) :=
  if ky then none
  else if kx then (if shS iy then none else gyi)
  else finInYFree ix iy gxi gyi

/-- Ghost inputs across a Fin edge (internal right end). -/
def ghostFinIn (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxi gyi : Option (DigitAtom n)) : Option (DigitAtom n) × Option (DigitAtom n) :=
  (finInX bx ix kx iy ky gxi, finInY ix kx iy ky gxi gyi)

/-- Ghost input of the last target cell across the terminal edge. -/
def ghostTermIn (ix : BankRepairDigitInSh) (kx : Bool) (gxi : Option (DigitAtom n)) :
    Option (DigitAtom n) :=
  if kx then none
  else
    match ix with
    | .X => none
    | .P T => if T then none else gxi
    | _ => gxi

variable (lane : DigitLane) (time : Nat) (source destination : Fin n)
  (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n)

/-- Pipe row: the ghost outputs (pass-through `D → D` copies `gx.out`, `gy.out`). -/
theorem replayPipe (hlx : x.leader = false) (hly : y.leader = false) (hmy : y.marker = false) :
    ((digitLaneReplay lane time source destination x y gx gy).x.out,
      (digitLaneReplay lane time source destination x y gx gy).y.out) =
    ghostPipe (DigitStamp.mk time source lane) x.marker (bankRepairDigitOutShOf x.out)
      (bankRepairDigitOutShOf y.out) gx.out gy.out := by
  cases hxo : x.out <;> cases hyo : y.out <;> cases hxm : x.marker <;>
    simp [digitLaneReplay, hlx, hly, hmy, hxo, hyo, hxm, ghostPipe, bankRepairDigitOutShOf,
      OutTok.isD, OutTok.isU, OutTok.isE, outT]

/-- Entry row: the delimiter's ghost output is untouched. -/
theorem replayEntry (hlx : x.leader = false) (hly : y.leader = false) (hmy : y.marker = true) :
    (digitLaneReplay lane time source destination x y gx gy).y.out = gy.out := by
  cases hxo : x.out <;> cases hxm : x.marker <;>
    simp [digitLaneReplay, hlx, hly, hmy, hxo, hxm, OutTok.isD, OutTok.isU, OutTok.isE] <;>
    (repeat' split) <;> simp_all

/-- Delivery row: source ghost output, delimiter ghost input (the accepted packet's atom),
the delimiter's ledger is untouched, and an export is recorded exactly on acceptance. -/
theorem replayDel (hlx : x.leader = false) (hly : y.leader = false) (hmx : x.marker = false)
    (hmy : y.marker = true) :
    ((digitLaneReplay lane time source destination x y gx gy).x.out,
      (digitLaneReplay lane time source destination x y gx gy).y.input) =
      ghostDel (DigitStamp.mk time source lane) (bankRepairDigitOutShOf x.out)
        (bankRepairDigitInShOf y.input) y.carryLive gx.out gy.input ∧
    (digitLaneReplay lane time source destination x y gx gy).y.carry = gy.carry ∧
    (digitLaneReplay lane time source destination x y gx gy).exported.isSome =
      delAccept (bankRepairDigitOutShOf x.out) (bankRepairDigitInShOf y.input) y.carryLive := by
  cases hxo : x.out <;> cases hxi : x.input <;> cases hxc : x.carryLive <;>
    cases hyi : y.input <;> cases hyc : y.carryLive <;>
    simp [digitLaneReplay, hlx, hly, hmx, hmy, hxo, hxi, hxc, hyi, hyc, ghostDel, delAccept,
      bankRepairDigitOutShOf, bankRepairDigitInShOf, OutTok.isD, OutTok.isU, OutTok.isE,
      InTok.isX, InTok.isS, InTok.isP, InTok.isE, outT, inT] <;>
    (repeat' split) <;> simp_all

/-- Fin row: both ghost inputs, and which ledgers are present (pass-through cases copy
`gx.input`, `gy.input`, `gx.carry`, `gy.carry`). -/
theorem replayFin (hlx : x.leader = false) (hly : y.leader = false) (hmy : y.marker = false) :
    ((digitLaneReplay lane time source destination x y gx gy).x.input,
      (digitLaneReplay lane time source destination x y gx gy).y.input) =
      ghostFinIn x.marker (bankRepairDigitInShOf x.input) x.carryLive
        (bankRepairDigitInShOf y.input) y.carryLive gx.input gy.input ∧
    (digitLaneReplay lane time source destination x y gx gy).x.carry.isSome =
      (!x.carryLive && ((x.marker && shS (bankRepairDigitInShOf x.input)) ||
        gx.carry.isSome)) ∧
    (digitLaneReplay lane time source destination x y gx gy).y.carry.isSome =
      ((x.carryLive && !y.carryLive && shS (bankRepairDigitInShOf y.input)) ||
        gy.carry.isSome) := by
  rcases hxi : x.input with _ | _ | ⟨v, T⟩ | ⟨v, _ | _⟩ <;> cases hxc : x.carryLive <;>
    cases hyi : y.input <;> cases hyc : y.carryLive <;> cases hxm : x.marker <;>
    simp [digitLaneReplay, hlx, hly, hmy, hxi, hxc, hyi, hyc, hxm, ghostFinIn, finInX, finInY,
      finInYFree, finXP, finYX, finYP, shS,
      bankRepairDigitInShOf, InTok.isX, InTok.isS, InTok.isP, InTok.isE, inT] <;>
    (repeat' split) <;> simp_all

/-- Terminal row: the last target cell's ghost input and ledger, and the terminal receipt is
recorded exactly when the carry is live. -/
theorem replayTerm (hlx : x.leader = false) (hly : y.leader = false) (hmx : x.marker = false)
    (hmy : y.marker = true) :
    (digitLaneReplay lane time source destination x y gx gy).x.input =
      ghostTermIn (bankRepairDigitInShOf x.input) x.carryLive gx.input ∧
    (digitLaneReplay lane time source destination x y gx gy).x.carry.isSome =
      (!x.carryLive && gx.carry.isSome) ∧
    (digitLaneReplay lane time source destination x y gx gy).terminal.isSome = x.carryLive := by
  rcases hxi : x.input with _ | _ | ⟨v, _ | _⟩ | ⟨v, _ | _⟩ <;> cases hxc : x.carryLive <;>
    simp [digitLaneReplay, hlx, hly, hmx, hmy, hxi, hxc, ghostTermIn,
      bankRepairDigitInShOf, InTok.isX, InTok.isS, InTok.isP, InTok.isE, inT] <;>
    (repeat' split) <;> simp_all

end Rows

end L3.GhostBridge

#print axioms L3.GhostBridge.recordUnreadReadD
#print axioms L3.GhostBridge.recordDeliveryD
#print axioms L3.GhostBridge.recordCarryUseD
#print axioms L3.GhostBridge.recordTerminalD
#print axioms L3.GhostBridge.replayDel
#print axioms L3.GhostBridge.replayFin
#print axioms L3.GhostBridge.auditStepFrame
#print axioms L3.GhostBridge.auditFrameOrderWord
