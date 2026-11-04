import Leader.L3.Bank.RepairDigitRearm

/-!
# T25 item 3: per-row recording lemmas on the lane replay

The receipts of `digitService` (Target.lean) are produced lane by lane by `digitLaneReplay`.
For each of the four T22 shape rows, the replay records what the completion receipts need. Each
lemma is stated on the masked shape of the lane view (`bankRepairDigitOutShOf`,
`bankRepairDigitInShOf`, carry-live bit), with the hypotheses of the corresponding row lemma
(no leader at either end; the right end internal or a delimiter):

* `recordUnreadRead`: a `U` read (Pipe / Del row, `x.out = U`) records `sample = some s` with
  `s.id = ⟨time, source, lane⟩` (so `s.id.site` is the edge's source site), `s.tail` the border
  bit `x.marker`, `s.value` the digit, and sets the packet's ghost atom to `sampled s.id`;
* `recordDelivery`: the Del row delivering a packet (`x.out = D T`, delimiter target with empty
  input and no live carry) records `exported = some x` carrying the operand atom `gx.out.atom`,
  and the target's input ghost takes that atom;
* `recordCarryUse`: the Fin row's success case (live carry at `x`, internal target with an `S`
  input and no live carry) appends one use to the carry ledger, now held by the target;
* `recordTerminal`: the terminal row (`cohortTermStep` with a live carry into a delimiter)
  records `terminal = some t` with the ledger `gx.carry`.

`digitServiceWriter` / `digitServiceComparison` identify the service's lane receipts with the
lane replay on the service views.
-/

namespace L3.Recording

set_option autoImplicit false

open L3.RenewalReferenceClock

section Lane

variable {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat) (source destination : Fin n)
  (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n)

theorem outShU {A : Nat} {o : OutTok A} (h : bankRepairDigitOutShOf o = .U) : o = .U := by
  cases o <;> simp_all [bankRepairDigitOutShOf]

theorem outShD {A : Nat} {o : OutTok A} {T : Bool} (h : bankRepairDigitOutShOf o = .D T) :
    ∃ v, o = .D v T := by
  cases o with
  | E => simp [bankRepairDigitOutShOf] at h
  | U => simp [bankRepairDigitOutShOf] at h
  | D v T' =>
    simp only [bankRepairDigitOutShOf, BankRepairDigitOutSh.D.injEq] at h
    exact ⟨v, by rw [h]⟩

theorem inShE {A : Nat} {i : InTok A} (h : bankRepairDigitInShOf i = .E) : i = .E := by
  cases i <;> simp_all [bankRepairDigitInShOf]

theorem inShS {A : Nat} {i : InTok A} {T : Bool} (h : bankRepairDigitInShOf i = .S T) :
    ∃ v, i = .S v T := by
  cases i with
  | E => simp [bankRepairDigitInShOf] at h
  | X => simp [bankRepairDigitInShOf] at h
  | P v T' => simp [bankRepairDigitInShOf] at h
  | S v T' =>
    simp only [bankRepairDigitInShOf, BankRepairDigitInSh.S.injEq] at h
    exact ⟨v, by rw [h]⟩

/-- A `U` read records a sample at the edge's source site with the border bit as its tail bit,
and the read packet's ghost atom is that sample. -/
theorem recordUnreadRead (hlx : x.leader = false) (hly : y.leader = false)
    (hU : bankRepairDigitOutShOf x.out = .U) :
    ∃ s, (digitLaneReplay lane time source destination x y gx gy).sample = some s ∧
      s.id = { time := time, site := source, lane := lane } ∧ s.id.site = source ∧
      s.tail = x.marker ∧ s.value = x.digit ∧ s.cause = gx.out.obligation ∧
      (digitLaneReplay lane time source destination x y gx gy).x.out =
        .packet (some (.sampled s.id)) ∧
      (digitLaneReplay lane time source destination x y gx gy).x.out.atom =
        some (.sampled s.id) := by
  have hxo := outShU hU
  refine ⟨DigitSample.mk (DigitStamp.mk time source lane) x.digit x.marker gx.out.obligation,
    ?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp [digitLaneReplay, hlx, hly, hxo, OutTok.isD, OutTok.isU]
  · simp [digitLaneReplay, hlx, hly, hxo, OutTok.isD, OutTok.isU]
  · simp [digitLaneReplay, hlx, hly, hxo, OutTok.isD, OutTok.isU, DigitOutGhost.atom]

/-- The delivery of a packet into a delimiter with an empty input and no live carry records an
export carrying the packet's operand atom; the delimiter's input ghost takes the atom. -/
theorem recordDelivery (hlx : x.leader = false) (hly : y.leader = false)
    (hmy : y.marker = true) {T : Bool} (hD : bankRepairDigitOutShOf x.out = .D T)
    (hiy : bankRepairDigitInShOf y.input = .E) (hky : y.carryLive = false) :
    ∃ ex, (digitLaneReplay lane time source destination x y gx gy).exported = some ex ∧
      ex.operand = gx.out.atom ∧ ex.time = time ∧ ex.lane = lane ∧ ex.source = source ∧
      ex.destination = destination ∧ ex.value = outV c x.out ∧ ex.tail = T ∧
      (digitLaneReplay lane time source destination x y gx gy).y.input = gx.out.atom := by
  obtain ⟨v, hxo⟩ := outShD hD
  have hyi := inShE hiy
  refine ⟨DigitExport.mk time lane source destination gx.out.atom (outV c x.out) (outT x.out),
    ?_, rfl, rfl, rfl, rfl, rfl, rfl, by rw [hxo]; rfl, ?_⟩
  · cases hxi : x.input <;> cases hxc : x.carryLive <;> cases hxm : x.marker <;>
      simp [digitLaneReplay, hlx, hly, hmy, hxo, hyi, hky, hxi, hxc, hxm, OutTok.isD,
        InTok.isX, InTok.isS, InTok.isP, InTok.isE, inT] <;>
      (repeat' split) <;> simp_all
  · cases hxi : x.input <;> cases hxc : x.carryLive <;> cases hxm : x.marker <;>
      simp [digitLaneReplay, hlx, hly, hmy, hxo, hyi, hky, hxi, hxc, hxm, OutTok.isD,
        InTok.isX, InTok.isS, InTok.isP, InTok.isE, inT] <;>
      (repeat' split) <;> simp_all

/-- The successful carry hop across an internal target appends one use (at the target, with the
target's input atom as operand) to the carry ledger, which moves to the target. -/
theorem recordCarryUse (hlx : x.leader = false) (hly : y.leader = false)
    (hmy : y.marker = false) (hkx : x.carryLive = true) (hky : y.carryLive = false) {T : Bool}
    (hiy : bankRepairDigitInShOf y.input = .S T) :
    (digitLaneReplay lane time source destination x y gx gy).y.carry =
      some (DigitCarryGhost.mk
        (gx.carry.getD (DigitCarryGhost.mk
          (some (.missing (DigitStamp.mk time source lane) .carry)) [])).inherited
        ((gx.carry.getD (DigitCarryGhost.mk
          (some (.missing (DigitStamp.mk time source lane) .carry)) [])).uses ++
          [DigitUse.mk time destination gy.input (inV c y.input) T y.digit x.carryBit
            x.carryError])) := by
  obtain ⟨v, hyi⟩ := inShS hiy
  simp [digitLaneReplay, hlx, hly, hmy, hkx, hky, hyi, InTok.isS, inT]

/-- With an existing ledger the use is appended to it. -/
theorem recordCarryUseLedger (hlx : x.leader = false) (hly : y.leader = false)
    (hmy : y.marker = false) (hkx : x.carryLive = true) (hky : y.carryLive = false) {T : Bool}
    (hiy : bankRepairDigitInShOf y.input = .S T) (L : DigitCarryGhost c n)
    (hL : gx.carry = some L) :
    (digitLaneReplay lane time source destination x y gx gy).y.carry =
      some (DigitCarryGhost.mk L.inherited (L.uses ++
        [DigitUse.mk time destination gy.input (inV c y.input) T y.digit x.carryBit
          x.carryError])) := by
  rw [recordCarryUse lane time source destination x y gx gy hlx hly hmy hkx hky hiy, hL]
  rfl

/-- The terminal row: a live carry meeting the delimiter records the terminal receipt with the
carry ledger. -/
theorem recordTerminal (hlx : x.leader = false) (hly : y.leader = false)
    (hmy : y.marker = true) (hkx : x.carryLive = true) :
    (digitLaneReplay lane time source destination x y gx gy).terminal =
      some (DigitTerminal.mk time lane source destination gx.carry x.carryBit x.carryError) := by
  simp [digitLaneReplay, hlx, hly, hmy, hkx]

end Lane

section Service

variable {c : Compiled} {n : Nat} (time : Nat) (source destination : Fin n) (X Y : ProjD c)
  (gx gy : DigitGhost c n)

theorem digitServiceWriter :
    (digitService time source destination X Y gx gy).writer =
      digitLaneReplay .writer time source destination
        (digitLaneView .writer X (workerW X.word Y.word).betaX)
        (digitLaneView .writer Y (workerW X.word Y.word).betaY) gx.writer gy.writer := rfl

theorem digitServiceComparison :
    (digitService time source destination X Y gx gy).comparison =
      digitLaneReplay .comparison time source destination
        (digitLaneView .comparison X X.word.beta)
        (digitLaneView .comparison Y Y.word.beta) gx.comparison gy.comparison := rfl

theorem digitServiceWriterX :
    (digitService time source destination X Y gx gy).x.writer =
      (digitService time source destination X Y gx gy).writer.x := rfl

theorem digitServiceWriterY :
    (digitService time source destination X Y gx gy).y.writer =
      (digitService time source destination X Y gx gy).writer.y := rfl

theorem digitServiceComparisonX :
    (digitService time source destination X Y gx gy).x.comparison =
      (digitService time source destination X Y gx gy).comparison.x := rfl

theorem digitServiceComparisonY :
    (digitService time source destination X Y gx gy).y.comparison =
      (digitService time source destination X Y gx gy).comparison.y := rfl

end Service

end L3.Recording

#print axioms L3.Recording.recordUnreadRead
#print axioms L3.Recording.recordDelivery
#print axioms L3.Recording.recordCarryUse
#print axioms L3.Recording.recordCarryUseLedger
#print axioms L3.Recording.recordTerminal
