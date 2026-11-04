import Leader.Wu.ShortGap.CaptureReservation

/-!
# The short-gap sanitizer sweep on one latched gap

New file: `Leader/Wu/ShortGap/SanitizerSweep.lean`.

It is shown that `CaptureReady` may not be entered from an arbitrary raw
`C/C` state: the capture proposal shares the physical interior slots with
selection traffic, so stale positive declarations, replies, `FINAL` tokens and
unknown payloads can collide with the proposal rows.  The
repair is a dedicated *sanitizer* sweep, leased before capture ownership, which
erases the whole interior, checks the target's reservation in place, and
returns either readiness or a downgrade.

This file formalises that sweep for **one** latched gap whose interior is
completely arbitrary, including forged sanitizer symbols.

## What is new here

The imported `Node` has no sanitizer alphabet.  As in
`ShortGapCaptureCommitRows`, no imported type is redefined: `SNode` *wraps*
`Node` with a leader bit, an owner-side sanitizer control, a target-side
sanitizer lease, and a four-valued interior carrier `E/S/A/R`.  Every field is
constant-state; no identifier, nonce, generation, coordinate or unbounded
datum is added.

The executable signature is therefore

  `sanRow : SNode -> SNode -> SNode x SNode`

and its ten-rule dispatch is total, deterministic and radius one.  During the
lease the sanitizer table is the *only* dispatcher on the gap: no legacy
selection or capture rewrite is invoked, which is exactly the clause
"every sanitizer-containing pair excludes legacy rewrites".

## What is proved, not assumed

The entry state is **arbitrary**: the `h-1` interior slots carry any `Wire`
(selection or capture) payload together with any carrier in `{E,S,A,R}`.  In
particular a forged `A` or `R` may sit anywhere, and a forged `S` may sit in
the not-yet-swept suffix and even turn around at the target.

Two facts that the design answer only asserts are proved here.

* *Empty prefix.*  The launch row overwrites interior position `1` with the
  real head, and the head erases everything it crosses; the lane invariant
  therefore contains the statement that positions `1 .. j-1` are empty when
  the head is at `j`.  A forged return can never be found strictly left of the
  head, hence never reaches a `waitSan` owner ahead of the real return
  (`no_premature_deposit`).
* *Collision priority.*  The forward row is guarded by `a.carrier = S` and the
  backward row by `a.carrier <> S`, so `S | A` and `S | R` resolve forward and
  the forged return is destroyed (`forward_wins_collision`).  Without that
  priority a forged return crosses the head; `forward_priority_is_load_bearing`
  exhibits the difference on the naive table.

`sanitize_bellman` is a scale-one `NatBellmanSuperSolution` for the potential
`n * debt`, with `debt = 2h-1` at launch, `2h-1-j` at forward position `j`,
`j` at a returning `A`/`R` and `0` at either terminal.  The debt is a function
of the *phase*, not of the interior content, so an unbounded amount of garbage
is charged nothing: this is the form of the remark that a naive
per-token cleanup would cost `O(n h^2)`.

## Scope

One gap, one lease, frozen root choices, no JOIN, no pipelining, no root
deletion.  Whether the ambient dispatcher installs the lease correctly is the
entry contract of `ShortGapCaptureReservation`/`ShortGapCaptureEntry` and is
not re-derived here.  `SanitizeLaws` below is a *derived* bundle: every field
is discharged by a direct proof in this file, so nothing is assumed.
-/

namespace ShortGapSanitizerSweep

open ShortGapLiteralGapRows FiniteUniformStoppingTree
open ShortGapCaptureReservation

set_option autoImplicit false

/-! ## Finite uniform sum helper -/

private theorem ofFn_sum_lt_of_single_lt
    {N : Nat} (f g : Fin N → Nat) (chosen : Fin N)
    (hle : ∀ i, f i ≤ g i) (hlt : f chosen < g chosen) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction N with
  | zero => exact Fin.elim0 chosen
  | succ N ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      by_cases hzero : chosen = 0
      · subst chosen
        have htail := ofFn_sum_le
          (fun i : Fin N => f i.succ) (fun i => g i.succ)
          (fun i => hle i.succ)
        omega
      · have hpos : 0 < chosen.val := by
          have hne : chosen.val ≠ 0 :=
            fun h => hzero (Fin.ext (by simpa using h))
          omega
        have hprev : chosen.val - 1 < N := by
          have := chosen.isLt
          omega
        have hsucc : (⟨chosen.val - 1, hprev⟩ : Fin N).succ = chosen :=
          Fin.ext (by simp only [Fin.val_succ]; omega)
        have htail := ih
          (fun i : Fin N => f i.succ) (fun i => g i.succ)
          ⟨chosen.val - 1, hprev⟩
          (fun i => hle i.succ) (by simpa only [hsucc] using hlt)
        have hhead := hle 0
        omega

private theorem band_true {x y : Bool} (h : (x && y) = true) : x = true ∧ y = true := by
  cases x <;> cases y <;> simp at h ⊢

private theorem bool_of_not_true {x : Bool} (h : ¬ (x = true)) : x = false := by
  cases x <;> simp at h ⊢

/-! ## The sanitizer alphabet, as an extension of the slot alphabet -/

/-- The sanitizer symbols `E`, `S`, `A`, `R`.  None of them is a selection
live marker or a capture proposal: they form a new carrier lane occupying an
interior slot, exactly as `CommitCarrier` does for the post-`FINAL` rows. -/
inductive SanSym where
  | empty
  | sweep
  | ack
  | rejected
  deriving DecidableEq

/-- The owner's sanitizer control.  `idle` is the non-participating value
carried by interior slots. -/
inductive OwnerSan where
  | idle
  | startSan
  | waitSan
  | ready
  | downgraded
  deriving DecidableEq

/-- The target's sanitizer lease.  `reservedSan` is installed at lease entry,
`reservedAck` by the turnaround; both count as the sweep's own exclusive
reservation. -/
inductive TargetSan where
  | unleased
  | reservedSan
  | reservedAck
  deriving DecidableEq

/-- A sanitizer node: the imported `Node`, a leader bit, and the three new
constant-state sanitizer fields.  No imported type is modified. -/
structure SNode where
  raw : Node
  leader : Bool
  owner : OwnerSan
  lease : TargetSan
  carrier : SanSym
  deriving DecidableEq

def emptyRaw : Node := .interior (.selection .empty)

/-- The latched gap owner: the `out1` root whose clockwise port is the
candidate receipt. -/
def rawOwner : Node → Bool
  | .root .out1 .heldCandidate _ _ _ => true
  | _ => false

/-- The latched candidate target: the `in0` root whose counterclockwise port
is the candidate receipt. -/
def rawTarget : Node → Bool
  | .root .in0 _ .heldCandidate _ _ => true
  | _ => false

def rawSlot : Node → Bool
  | .interior _ => true
  | _ => false

def isOwner (n : SNode) : Bool := rawOwner n.raw
def isTarget (n : SNode) : Bool := rawTarget n.raw
def isSlot (n : SNode) : Bool := rawSlot n.raw

def isStart : OwnerSan → Bool
  | .startSan => true
  | _ => false

def isWait : OwnerSan → Bool
  | .waitSan => true
  | _ => false

def isSweepSym : SanSym → Bool
  | .sweep => true
  | _ => false

def isAckSym : SanSym → Bool
  | .ack => true
  | _ => false

def isRejSym : SanSym → Bool
  | .rejected => true
  | _ => false

def leasedB : TargetSan → Bool
  | .unleased => false
  | .reservedSan => true
  | .reservedAck => true

/-- `V` of the answer: the right endpoint is the correct `in0` candidate, is
still a leader, and holds the sweep's own exclusive reservation.  A stale
`COMMITTED` cannot authorise this and `leader = false` is never resurrected. -/
def targetOk (n : SNode) : Bool := isTarget n && n.leader && leasedB n.lease

/-- A canonical interior slot carrying one sanitizer symbol.  Writing it
erases every raw payload at that position. -/
def slotOf (s : SanSym) : SNode := ⟨emptyRaw, false, .idle, .unleased, s⟩

def setOwner (n : SNode) (c : OwnerSan) : SNode := { n with owner := c }

/-- O4/T4: a rejected owner returns its clockwise port to `toSend` and
its capture control to `home`.  `heldDenial` is never written, so no false
`JOIN` can be built out of a rejection. -/
def downRaw : Node → Node
  | .root ch _ ccw _ inc => .root ch .toSend ccw .home inc
  | n => n

def downgrade (n : SNode) : SNode :=
  { n with raw := downRaw n.raw, owner := .downgraded }

def armTarget (n : SNode) : SNode := { n with lease := .reservedAck }

def choiceOf : Node → Option Choice
  | .root ch _ _ _ _ => some ch
  | .interior _ => none

/-! ## The row table -/

inductive Rule where
  | launch | directAck | directReject
  | forward | turnAck | turnReject
  | backward | ackDeposit | rejDeposit | idle
  deriving DecidableEq

/-- The rejection rows are the explicit exception to port framing. -/
def successfulB : Rule → Bool
  | .rejDeposit => false
  | .directReject => false
  | _ => true

/-- The total, deterministic, radius-one sanitizer dispatch.

```
O(startSan,C) | slot(*)   -> O(waitSan,C)     | slot(S)
O(startSan,C) | T(V)      -> O(CaptureReady)  | T(reservedAck)     (h = 1)
O(startSan,C) | T(not V)  -> O(home,toSend)   | T                  (h = 1)
slot(S)       | slot(*)   -> slot(E)          | slot(S)
slot(S)       | T(V)      -> slot(A)          | T(reservedAck)
slot(S)       | T(not V)  -> slot(R)          | T
slot(*)       | slot(A/R) -> slot(A/R)        | slot(E)
O(waitSan,C)  | slot(A)   -> O(CaptureReady)  | slot(E)
O(waitSan,C)  | slot(R)   -> O(home,toSend)   | slot(E)
```

The forward row is tested before the backward row, so `S | A` and `S | R`
resolve forward: the head erases the forged return instead of letting it pass.
Everything else stutters, including empty/empty and any pair at a completed
owner: completed sweeps are never restarted. -/
def sanDispatch (a b : SNode) : Rule × SNode × SNode :=
  if isOwner a && isStart a.owner then
    if isSlot b then (.launch, setOwner a .waitSan, slotOf .sweep)
    else if targetOk b then (.directAck, setOwner a .ready, armTarget b)
    else (.directReject, downgrade a, b)
  else if isOwner a && isWait a.owner then
    if isSlot b && isAckSym b.carrier then (.ackDeposit, setOwner a .ready, slotOf .empty)
    else if isSlot b && isRejSym b.carrier then (.rejDeposit, downgrade a, slotOf .empty)
    else (.idle, a, b)
  else if isSlot a && isSweepSym a.carrier then
    if isSlot b then (.forward, slotOf .empty, slotOf .sweep)
    else if targetOk b then (.turnAck, slotOf .ack, armTarget b)
    else (.turnReject, slotOf .rejected, b)
  else if isSlot a && isSlot b && isAckSym b.carrier then
    (.backward, slotOf .ack, slotOf .empty)
  else if isSlot a && isSlot b && isRejSym b.carrier then
    (.backward, slotOf .rejected, slotOf .empty)
  else (.idle, a, b)

def sanRow (a b : SNode) : SNode × SNode := (sanDispatch a b).2
def sanRule (a b : SNode) : Rule := (sanDispatch a b).1

/-- The specification of the pair updates with their real guards.  `idle`
carries no guard: it is a witness produced by the dispatcher, not a claim
about when the dispatcher stutters. -/
inductive RowStep (a b : SNode) : Rule → SNode → SNode → Prop where
  | launch (h1 : isOwner a = true) (h2 : isStart a.owner = true)
      (h3 : isSlot b = true) :
      RowStep a b .launch (setOwner a .waitSan) (slotOf .sweep)
  | directAck (h1 : isOwner a = true) (h2 : isStart a.owner = true)
      (h3 : isSlot b = false) (h4 : targetOk b = true) :
      RowStep a b .directAck (setOwner a .ready) (armTarget b)
  | directReject (h1 : isOwner a = true) (h2 : isStart a.owner = true)
      (h3 : isSlot b = false) (h4 : targetOk b = false) :
      RowStep a b .directReject (downgrade a) b
  | ackDeposit (h1 : isOwner a = true) (h2 : isWait a.owner = true)
      (h3 : isSlot b = true) (h4 : isAckSym b.carrier = true) :
      RowStep a b .ackDeposit (setOwner a .ready) (slotOf .empty)
  | rejDeposit (h1 : isOwner a = true) (h2 : isWait a.owner = true)
      (h3 : isSlot b = true) (h4 : isRejSym b.carrier = true) :
      RowStep a b .rejDeposit (downgrade a) (slotOf .empty)
  | forward (h1 : isSlot a = true) (h2 : isSweepSym a.carrier = true)
      (h3 : isSlot b = true) :
      RowStep a b .forward (slotOf .empty) (slotOf .sweep)
  | turnAck (h1 : isSlot a = true) (h2 : isSweepSym a.carrier = true)
      (h3 : isSlot b = false) (h4 : targetOk b = true) :
      RowStep a b .turnAck (slotOf .ack) (armTarget b)
  | turnReject (h1 : isSlot a = true) (h2 : isSweepSym a.carrier = true)
      (h3 : isSlot b = false) (h4 : targetOk b = false) :
      RowStep a b .turnReject (slotOf .rejected) b
  | backAck (h1 : isSlot a = true) (h2 : isSweepSym a.carrier = false)
      (h3 : isSlot b = true) (h4 : isAckSym b.carrier = true) :
      RowStep a b .backward (slotOf .ack) (slotOf .empty)
  | backRej (h1 : isSlot a = true) (h2 : isSweepSym a.carrier = false)
      (h3 : isSlot b = true) (h4 : isRejSym b.carrier = true) :
      RowStep a b .backward (slotOf .rejected) (slotOf .empty)
  | idle : RowStep a b .idle a b

theorem sanRow_spec (a b : SNode) :
    RowStep a b (sanRule a b) (sanRow a b).1 (sanRow a b).2 := by
  show RowStep a b (sanDispatch a b).1 (sanDispatch a b).2.1 (sanDispatch a b).2.2
  unfold sanDispatch
  by_cases h1 : (isOwner a && isStart a.owner) = true
  · obtain ⟨ha, hs⟩ := band_true h1
    simp only [if_pos h1]
    by_cases h2 : isSlot b = true
    · simp only [if_pos h2]
      exact .launch ha hs h2
    · simp only [if_neg h2]
      by_cases h3 : targetOk b = true
      · simp only [if_pos h3]
        exact .directAck ha hs (bool_of_not_true h2) h3
      · simp only [if_neg h3]
        exact .directReject ha hs (bool_of_not_true h2) (bool_of_not_true h3)
  · simp only [if_neg h1]
    by_cases h2 : (isOwner a && isWait a.owner) = true
    · obtain ⟨ha, hw⟩ := band_true h2
      simp only [if_pos h2]
      by_cases h3 : (isSlot b && isAckSym b.carrier) = true
      · obtain ⟨hb, hc⟩ := band_true h3
        simp only [if_pos h3]
        exact .ackDeposit ha hw hb hc
      · simp only [if_neg h3]
        by_cases h4 : (isSlot b && isRejSym b.carrier) = true
        · obtain ⟨hb, hc⟩ := band_true h4
          simp only [if_pos h4]
          exact .rejDeposit ha hw hb hc
        · simp only [if_neg h4]
          exact .idle
    · simp only [if_neg h2]
      by_cases h3 : (isSlot a && isSweepSym a.carrier) = true
      · obtain ⟨ha, hc⟩ := band_true h3
        simp only [if_pos h3]
        by_cases h4 : isSlot b = true
        · simp only [if_pos h4]
          exact .forward ha hc h4
        · simp only [if_neg h4]
          by_cases h5 : targetOk b = true
          · simp only [if_pos h5]
            exact .turnAck ha hc (bool_of_not_true h4) h5
          · simp only [if_neg h5]
            exact .turnReject ha hc (bool_of_not_true h4) (bool_of_not_true h5)
      · simp only [if_neg h3]
        by_cases h4 : (isSlot a && isSlot b && isAckSym b.carrier) = true
        · obtain ⟨hab, hc⟩ := band_true h4
          obtain ⟨ha, hb⟩ := band_true hab
          have hsw : isSweepSym a.carrier = false := by
            have hx := bool_of_not_true h3
            rw [ha, Bool.true_and] at hx
            exact hx
          simp only [if_pos h4]
          exact .backAck ha hsw hb hc
        · simp only [if_neg h4]
          by_cases h5 : (isSlot a && isSlot b && isRejSym b.carrier) = true
          · obtain ⟨hab, hc⟩ := band_true h5
            obtain ⟨ha, hb⟩ := band_true hab
            have hsw : isSweepSym a.carrier = false := by
              have hx := bool_of_not_true h3
              rw [ha, Bool.true_and] at hx
              exact hx
            simp only [if_pos h5]
            exact .backRej ha hsw hb hc
          · simp only [if_neg h5]
            exact .idle


/-! ## Structural facts about the three roles -/

theorem rawSlot_of_rawOwner {n : Node} (h : rawOwner n = true) : rawSlot n = false := by
  cases n with
  | interior w => simp [rawOwner] at h
  | root ch cw ccw out inc => rfl

theorem rawOwner_of_rawSlot {n : Node} (h : rawSlot n = true) : rawOwner n = false := by
  cases n with
  | interior w => rfl
  | root ch cw ccw out inc => simp [rawSlot] at h

theorem rawTarget_of_rawSlot {n : Node} (h : rawSlot n = true) : rawTarget n = false := by
  cases n with
  | interior w => rfl
  | root ch cw ccw out inc => simp [rawSlot] at h

theorem rawSlot_downRaw {n : Node} (h : rawSlot n = false) : rawSlot (downRaw n) = false := by
  cases n with
  | interior w => simp [rawSlot] at h
  | root ch cw ccw out inc => rfl

theorem rawOwner_downRaw (n : Node) : rawOwner (downRaw n) = false := by
  cases n with
  | interior w => rfl
  | root ch cw ccw out inc => cases ch <;> rfl

theorem downRaw_cwPort {n : Node} (h : rawSlot n = false) :
    (downRaw n).cwPort = some CwPort.toSend := by
  cases n with
  | interior w => simp [rawSlot] at h
  | root ch cw ccw out inc => rfl

theorem downRaw_choice (n : Node) : choiceOf (downRaw n) = choiceOf n := by
  cases n with
  | interior w => rfl
  | root ch cw ccw out inc => rfl

theorem downRaw_ccwPort (n : Node) : (downRaw n).ccwPort = n.ccwPort := by
  cases n with
  | interior w => rfl
  | root ch cw ccw out inc => rfl

@[simp] theorem isSlot_slotOf (s : SanSym) : isSlot (slotOf s) = true := rfl
@[simp] theorem isOwner_slotOf (s : SanSym) : isOwner (slotOf s) = false := rfl
@[simp] theorem isTarget_slotOf (s : SanSym) : isTarget (slotOf s) = false := rfl
@[simp] theorem targetOk_slotOf (s : SanSym) : targetOk (slotOf s) = false := rfl
@[simp] theorem carrier_slotOf (s : SanSym) : (slotOf s).carrier = s := rfl

theorem targetOk_of_isSlot {n : SNode} (h : isSlot n = true) : targetOk n = false := by
  simp [targetOk, isTarget, isSlot] at h ⊢
  intro hbad
  rw [rawTarget_of_rawSlot h] at hbad
  exact absurd hbad (by simp)

@[simp] theorem isSweepSym_sweep : isSweepSym .sweep = true := rfl
@[simp] theorem isSweepSym_empty : isSweepSym .empty = false := rfl
@[simp] theorem isSweepSym_ack : isSweepSym .ack = false := rfl
@[simp] theorem isSweepSym_rejected : isSweepSym .rejected = false := rfl
@[simp] theorem isAckSym_sweep : isAckSym .sweep = false := rfl
@[simp] theorem isAckSym_empty : isAckSym .empty = false := rfl
@[simp] theorem isAckSym_ack : isAckSym .ack = true := rfl
@[simp] theorem isAckSym_rejected : isAckSym .rejected = false := rfl
@[simp] theorem isRejSym_sweep : isRejSym .sweep = false := rfl
@[simp] theorem isRejSym_empty : isRejSym .empty = false := rfl
@[simp] theorem isRejSym_ack : isRejSym .ack = false := rfl
@[simp] theorem isRejSym_rejected : isRejSym .rejected = true := rfl
@[simp] theorem isStart_startSan : isStart .startSan = true := rfl
@[simp] theorem isStart_waitSan : isStart .waitSan = false := rfl
@[simp] theorem isStart_ready : isStart .ready = false := rfl
@[simp] theorem isStart_downgraded : isStart .downgraded = false := rfl
@[simp] theorem isStart_idle : isStart .idle = false := rfl
@[simp] theorem isWait_startSan : isWait .startSan = false := rfl
@[simp] theorem isWait_waitSan : isWait .waitSan = true := rfl
@[simp] theorem isWait_ready : isWait .ready = false := rfl
@[simp] theorem isWait_downgraded : isWait .downgraded = false := rfl
@[simp] theorem isWait_idle : isWait .idle = false := rfl

theorem isStart_of_isWait {c : OwnerSan} (h : isWait c = true) : isStart c = false := by
  cases c <;> simp at h ⊢

theorem isAckSym_of_isRejSym {c : SanSym} (h : isRejSym c = true) : isAckSym c = false := by
  cases c <;> simp at h ⊢

/-! ## Row-level consequences -/

private theorem step_right_frame {a b x y : SNode} {k : Rule} (h : RowStep a b k x y)
    (hb : isSlot b = false) : y = b ∨ y = armTarget b := by
  cases h with
  | launch _ _ h3 => rw [hb] at h3; exact absurd h3 (by simp)
  | directAck _ _ _ _ => exact Or.inr rfl
  | directReject _ _ _ _ => exact Or.inl rfl
  | ackDeposit _ _ h3 _ => rw [hb] at h3; exact absurd h3 (by simp)
  | rejDeposit _ _ h3 _ => rw [hb] at h3; exact absurd h3 (by simp)
  | forward _ _ h3 => rw [hb] at h3; exact absurd h3 (by simp)
  | turnAck _ _ _ _ => exact Or.inr rfl
  | turnReject _ _ _ _ => exact Or.inl rfl
  | backAck _ _ h3 _ => rw [hb] at h3; exact absurd h3 (by simp)
  | backRej _ _ h3 _ => rw [hb] at h3; exact absurd h3 (by simp)
  | idle => exact Or.inl rfl

/-- At a root right endpoint the only field a sanitizer row can write is the
sanitizer lease.  The target's raw node, leader bit and both selection ports
are framed by every row. -/
theorem sanRow_right_frame (a b : SNode) (hb : isSlot b = false) :
    (sanRow a b).2 = b ∨ (sanRow a b).2 = armTarget b :=
  step_right_frame (sanRow_spec a b) hb

theorem sanRow_right_raw (a b : SNode) (hb : isSlot b = false) :
    (sanRow a b).2.raw = b.raw ∧ (sanRow a b).2.leader = b.leader := by
  rcases sanRow_right_frame a b hb with h | h <;> rw [h] <;> exact ⟨rfl, rfl⟩

private theorem step_left_owner_frame {a b x y : SNode} {k : Rule} (h : RowStep a b k x y)
    (ha : isSlot a = false) (hk : successfulB k = true) :
    x.raw = a.raw ∧ x.leader = a.leader := by
  cases h with
  | launch _ _ _ => exact ⟨rfl, rfl⟩
  | directAck _ _ _ _ => exact ⟨rfl, rfl⟩
  | directReject _ _ _ _ => exact absurd hk (by simp [successfulB])
  | ackDeposit _ _ _ _ => exact ⟨rfl, rfl⟩
  | rejDeposit _ _ _ _ => exact absurd hk (by simp [successfulB])
  | forward h1 _ _ => rw [ha] at h1; exact absurd h1 (by simp)
  | turnAck h1 _ _ _ => rw [ha] at h1; exact absurd h1 (by simp)
  | turnReject h1 _ _ _ => rw [ha] at h1; exact absurd h1 (by simp)
  | backAck h1 _ _ _ => rw [ha] at h1; exact absurd h1 (by simp)
  | backRej h1 _ _ _ => rw [ha] at h1; exact absurd h1 (by simp)
  | idle => exact ⟨rfl, rfl⟩

/-- At a root left endpoint every successful row writes only the owner-side
sanitizer control.  Rejection is the explicit exception. -/
theorem sanRow_left_owner_frame (a b : SNode) (ha : isSlot a = false)
    (hk : successfulB (sanRule a b) = true) :
    (sanRow a b).1.raw = a.raw ∧ (sanRow a b).1.leader = a.leader :=
  step_left_owner_frame (sanRow_spec a b) ha hk

private theorem step_reject {a b x y : SNode} {k : Rule} (h : RowStep a b k x y)
    (ha : isSlot a = false) (hk : successfulB k = false) : x = downgrade a := by
  cases h with
  | launch _ _ _ => exact absurd hk (by simp [successfulB])
  | directAck _ _ _ _ => exact absurd hk (by simp [successfulB])
  | directReject _ _ _ _ => rfl
  | ackDeposit _ _ _ _ => exact absurd hk (by simp [successfulB])
  | rejDeposit _ _ _ _ => rfl
  | forward h1 _ _ => rw [ha] at h1; exact absurd h1 (by simp)
  | turnAck h1 _ _ _ => rw [ha] at h1; exact absurd h1 (by simp)
  | turnReject h1 _ _ _ => rw [ha] at h1; exact absurd h1 (by simp)
  | backAck h1 _ _ _ => rw [ha] at h1; exact absurd h1 (by simp)
  | backRej h1 _ _ _ => rw [ha] at h1; exact absurd h1 (by simp)
  | idle => exact absurd hk (by simp [successfulB])

/-- The rejection rows: `C -> toSend`, capture control `home`, and the owner
control `downgraded`.  `heldDenial` is never written, so no false `JOIN` can
be assembled from a rejected sweep, and readiness is not granted. -/
theorem reject_downgrades_forged_owner (a b : SNode) (ha : isSlot a = false)
    (hk : successfulB (sanRule a b) = false) :
    (sanRow a b).1 = downgrade a ∧
    (sanRow a b).1.raw.cwPort = some CwPort.toSend ∧
    (sanRow a b).1.raw.cwPort ≠ some CwPort.heldDenial ∧
    choiceOf (sanRow a b).1.raw = choiceOf a.raw ∧
    (sanRow a b).1.raw.ccwPort = a.raw.ccwPort ∧
    (sanRow a b).1.leader = a.leader ∧
    (sanRow a b).1.owner = .downgraded ∧
    (sanRow a b).1.owner ≠ .ready := by
  have hrow : (sanRow a b).1 = downgrade a := step_reject (sanRow_spec a b) ha hk
  have hcw : (downgrade a).raw.cwPort = some CwPort.toSend :=
    downRaw_cwPort (n := a.raw) ha
  refine ⟨hrow, by rw [hrow]; exact hcw, ?_, ?_, ?_, by rw [hrow]; rfl, by rw [hrow]; rfl, ?_⟩
  · rw [hrow, hcw]
    intro hbad
    cases hbad
  · rw [hrow]
    exact downRaw_choice a.raw
  · rw [hrow]
    exact downRaw_ccwPort a.raw
  · rw [hrow]
    intro hbad
    cases hbad

/-- No sanitizer row changes a leader bit at either root: the sweep neither
creates nor destroys leaders.  Deletion stays a separate post-commit action. -/
theorem sanRow_leader_frame (a b : SNode) (ha : isSlot a = false) (hb : isSlot b = false) :
    (sanRow a b).1.leader = a.leader ∧ (sanRow a b).2.leader = b.leader := by
  refine ⟨?_, (sanRow_right_raw a b hb).2⟩
  by_cases hk : successfulB (sanRule a b) = true
  · exact (sanRow_left_owner_frame a b ha hk).2
  · exact (reject_downgrades_forged_owner a b ha (bool_of_not_true hk)).2.2.2.2.2.1


/-- **Unconditional left-root framing.**  *Every* row, successful or rejecting,
preserves the left root's frozen choice, its incoming candidate port and its
leader bit.  Only the outgoing pair `(cwPort, outgoing)` can ever move, and by
`reject_downgrades_forged_owner` the rejection row moves it exactly to
`(toSend, home)`.  This is the form the capstone needs: it quantifies over all
rows, not only the successful ones. -/
theorem sanRow_left_choice_frame (a b : SNode) (ha : isSlot a = false) :
    choiceOf (sanRow a b).1.raw = choiceOf a.raw ∧
    (sanRow a b).1.raw.ccwPort = a.raw.ccwPort ∧
    (sanRow a b).1.leader = a.leader := by
  by_cases hk : successfulB (sanRule a b) = true
  · obtain ⟨hraw, hl⟩ := sanRow_left_owner_frame a b ha hk
    exact ⟨by rw [hraw], by rw [hraw], hl⟩
  · obtain ⟨-, -, -, hch, hccw, hl, -⟩ :=
      reject_downgrades_forged_owner a b ha (bool_of_not_true hk)
    exact ⟨hch, hccw, hl⟩

/-! ### Explicit literal rows -/

theorem row_forward (b : SNode) (hb : isSlot b = true) :
    sanRow (slotOf .sweep) b = (slotOf .empty, slotOf .sweep) := by
  show (sanDispatch (slotOf .sweep) b).2 = _
  simp [sanDispatch, hb]

/-- Priority: the head wins every `S | A` and `S | R` collision, so a forged
return is erased instead of crossing the head. -/
theorem forward_wins_collision (s : SanSym) :
    sanRow (slotOf .sweep) (slotOf s) = (slotOf .empty, slotOf .sweep) :=
  row_forward (slotOf s) rfl

theorem row_backward_ack (a : SNode) (ha : isSlot a = true)
    (hs : isSweepSym a.carrier = false) :
    sanRow a (slotOf .ack) = (slotOf .ack, slotOf .empty) := by
  show (sanDispatch a (slotOf .ack)).2 = _
  simp [sanDispatch, ha, hs, rawOwner_of_rawSlot (n := a.raw) ha, isOwner]

theorem row_backward_rej (a : SNode) (ha : isSlot a = true)
    (hs : isSweepSym a.carrier = false) :
    sanRow a (slotOf .rejected) = (slotOf .rejected, slotOf .empty) := by
  show (sanDispatch a (slotOf .rejected)).2 = _
  simp [sanDispatch, ha, hs, rawOwner_of_rawSlot (n := a.raw) ha, isOwner]

theorem row_slot_stutter (a b : SNode) (ha : isSlot a = true)
    (hs : isSweepSym a.carrier = false) (h3 : isAckSym b.carrier = false)
    (h4 : isRejSym b.carrier = false) : sanRow a b = (a, b) := by
  show (sanDispatch a b).2 = _
  simp [sanDispatch, ha, hs, h3, h4, rawOwner_of_rawSlot (n := a.raw) ha, isOwner]

theorem row_slot_root_stutter (a b : SNode) (ha : isSlot a = true)
    (hs : isSweepSym a.carrier = false) (hb : isSlot b = false) : sanRow a b = (a, b) := by
  show (sanDispatch a b).2 = _
  simp [sanDispatch, ha, hs, hb, rawOwner_of_rawSlot (n := a.raw) ha, isOwner]

theorem row_launch (a b : SNode) (ha : isOwner a = true) (ho : isStart a.owner = true)
    (hb : isSlot b = true) : sanRow a b = (setOwner a .waitSan, slotOf .sweep) := by
  show (sanDispatch a b).2 = _
  simp [sanDispatch, ha, ho, hb]

theorem row_direct_ack (a b : SNode) (ha : isOwner a = true) (ho : isStart a.owner = true)
    (hb : isSlot b = false) (hv : targetOk b = true) :
    sanRow a b = (setOwner a .ready, armTarget b) := by
  show (sanDispatch a b).2 = _
  simp [sanDispatch, ha, ho, hb, hv]

theorem row_direct_reject (a b : SNode) (ha : isOwner a = true) (ho : isStart a.owner = true)
    (hb : isSlot b = false) (hv : targetOk b = false) : sanRow a b = (downgrade a, b) := by
  show (sanDispatch a b).2 = _
  simp [sanDispatch, ha, ho, hb, hv]

theorem row_turn_ack (a b : SNode) (ha : isSlot a = true) (hs : isSweepSym a.carrier = true)
    (hb : isSlot b = false) (hv : targetOk b = true) :
    sanRow a b = (slotOf .ack, armTarget b) := by
  show (sanDispatch a b).2 = _
  simp [sanDispatch, ha, hs, hb, hv, rawOwner_of_rawSlot (n := a.raw) ha, isOwner]

theorem row_turn_reject (a b : SNode) (ha : isSlot a = true) (hs : isSweepSym a.carrier = true)
    (hb : isSlot b = false) (hv : targetOk b = false) :
    sanRow a b = (slotOf .rejected, b) := by
  show (sanDispatch a b).2 = _
  simp [sanDispatch, ha, hs, hb, hv, rawOwner_of_rawSlot (n := a.raw) ha, isOwner]

theorem row_ack_deposit (a b : SNode) (ha : isOwner a = true) (hw : isWait a.owner = true)
    (hb : isSlot b = true) (hc : isAckSym b.carrier = true) :
    sanRow a b = (setOwner a .ready, slotOf .empty) := by
  show (sanDispatch a b).2 = _
  simp [sanDispatch, ha, hw, hb, hc, isStart_of_isWait hw]

theorem row_rej_deposit (a b : SNode) (ha : isOwner a = true) (hw : isWait a.owner = true)
    (hb : isSlot b = true) (hc : isRejSym b.carrier = true) :
    sanRow a b = (downgrade a, slotOf .empty) := by
  show (sanDispatch a b).2 = _
  simp [sanDispatch, ha, hw, hb, hc, isStart_of_isWait hw, isAckSym_of_isRejSym hc]

theorem row_wait_stutter (a b : SNode) (ha : isOwner a = true) (hw : isWait a.owner = true)
    (h3 : isAckSym b.carrier = false) (h4 : isRejSym b.carrier = false) :
    sanRow a b = (a, b) := by
  show (sanDispatch a b).2 = _
  simp [sanDispatch, ha, hw, isStart_of_isWait hw, h3, h4]

/-- A completed sweep is never restarted: `ready` and `downgraded` owners
stutter against every right endpoint. -/
theorem row_done_stutter (a b : SNode) (hst : isStart a.owner = false)
    (hw : isWait a.owner = false) (ha : isSlot a = false) : sanRow a b = (a, b) := by
  show (sanDispatch a b).2 = _
  simp [sanDispatch, hst, hw, ha]

/-! ## One latched gap

`ownerRaw` is the latched `out1` owner, `targetRaw` the right root.  Both are
parameters of the sweep, not state produced by it.  The interior is *not* a
parameter: it is an arbitrary function into `SNode`. -/

structure SanFrame where
  h : Nat
  hpos : 0 < h
  ownerRaw : Node
  hOwner : rawOwner ownerRaw = true
  ownerLive : Bool
  targetRaw : Node
  hTargetRoot : rawSlot targetRaw = false
  targetLive : Bool
  lease0 : TargetSan

abbrev SanConfig (S : SanFrame) := Fin (S.h + 1) → SNode

def sanLeftPos (S : SanFrame) : Fin (S.h + 1) := ⟨0, Nat.succ_pos _⟩
def sanRightPos (S : SanFrame) : Fin (S.h + 1) := ⟨S.h, Nat.lt_succ_self _⟩

def sanLeftEnd (S : SanFrame) (j : Fin S.h) : Fin (S.h + 1) :=
  ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩

def sanRightEnd (S : SanFrame) (j : Fin S.h) : Fin (S.h + 1) :=
  ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩

/-- Scheduling gap edge `j`: the sanitizer row is applied to its two physical
endpoints and to nothing else. -/
def sanGapStep (S : SanFrame) (cfg : SanConfig S) (j : Fin S.h) : SanConfig S :=
  fun k =>
    if k.val = j.val then (sanRow (cfg (sanLeftEnd S j)) (cfg (sanRightEnd S j))).1
    else if k.val = j.val + 1 then (sanRow (cfg (sanLeftEnd S j)) (cfg (sanRightEnd S j))).2
    else cfg k

/-- Every position other than the two endpoints of the fired edge is framed. -/
theorem sanGapStep_frame (S : SanFrame) (cfg : SanConfig S) (j : Fin S.h)
    (k : Fin (S.h + 1)) (h1 : k.val ≠ j.val) (h2 : k.val ≠ j.val + 1) :
    sanGapStep S cfg j k = cfg k := by
  simp [sanGapStep, h1, h2]

structure SanEmbedding (S : SanFrame) (n : Nat) where
  edgeAt : Fin S.h → Fin n
  inj : ∀ a b, edgeAt a = edgeAt b → a = b

open Classical in
/-- One ambient scheduler edge acting on the gap.  Edges outside the gap frame
the whole configuration: this is the "frame elsewhere" clause. -/
noncomputable def sanSchedStep {n : Nat} (S : SanFrame) (E : SanEmbedding S n)
    (cfg : SanConfig S) (e : Fin n) : SanConfig S :=
  if hx : ∃ a : Fin S.h, E.edgeAt a = e then sanGapStep S cfg hx.choose else cfg

theorem sanSchedStep_eq {n : Nat} (S : SanFrame) (E : SanEmbedding S n)
    (cfg : SanConfig S) (a : Fin S.h) :
    sanSchedStep S E cfg (E.edgeAt a) = sanGapStep S cfg a := by
  classical
  have hx : ∃ b : Fin S.h, E.edgeAt b = E.edgeAt a := ⟨a, rfl⟩
  rw [sanSchedStep, dif_pos hx]
  have hchoose : E.edgeAt hx.choose = E.edgeAt a := hx.choose_spec
  rw [E.inj _ _ hchoose]

theorem sanSchedStep_id {n : Nat} (S : SanFrame) (E : SanEmbedding S n)
    (cfg : SanConfig S) (e : Fin n) (hne : ∀ a : Fin S.h, E.edgeAt a ≠ e) :
    sanSchedStep S E cfg e = cfg := by
  classical
  rw [sanSchedStep, dif_neg]
  rintro ⟨a, ha⟩
  exact hne a ha

theorem sanSchedStep_cases {n : Nat} (S : SanFrame) (E : SanEmbedding S n)
    (cfg : SanConfig S) (e : Fin n) :
    sanSchedStep S E cfg e = cfg ∨ ∃ a : Fin S.h, sanSchedStep S E cfg e = sanGapStep S cfg a := by
  classical
  by_cases hx : ∃ a : Fin S.h, E.edgeAt a = e
  · obtain ⟨a, ha⟩ := hx
    subst ha
    exact Or.inr ⟨a, sanSchedStep_eq S E cfg a⟩
  · exact Or.inl (sanSchedStep_id S E cfg e (fun a ha => hx ⟨a, ha⟩))

/-! ## The sweep lane -/

inductive Ret where
  | ack
  | rej
  deriving DecidableEq

def retSym : Ret → SanSym
  | .ack => .ack
  | .rej => .rejected

/-- The phases of the sweep.  `fwd 0` is the pre-launch owner state, `fwd j`
(`j >= 1`) has the head `S` at interior position `j`, `back r j` has the return
symbol at interior position `j`, `done r` is terminal. -/
inductive SanPhase where
  | fwd (j : Nat)
  | back (r : Ret) (j : Nat)
  | done (r : Ret)
  deriving DecidableEq

def PhaseOkS (S : SanFrame) : SanPhase → Prop
  | .fwd j => j < S.h
  | .back _ j => 1 ≤ j ∧ j < S.h
  | .done _ => True

def ownerCtl : SanPhase → OwnerSan
  | .fwd 0 => .startSan
  | .fwd (_ + 1) => .waitSan
  | .back _ _ => .waitSan
  | .done .ack => .ready
  | .done .rej => .downgraded

@[simp] theorem ownerCtl_fwd_zero : ownerCtl (.fwd 0) = .startSan := rfl

theorem ownerCtl_fwd_pos {j : Nat} (h : 0 < j) : ownerCtl (.fwd j) = OwnerSan.waitSan := by
  cases j with
  | zero => omega
  | succ _ => rfl

@[simp] theorem ownerCtl_back (r : Ret) (j : Nat) : ownerCtl (.back r j) = OwnerSan.waitSan := rfl

def ownerRawOf (S : SanFrame) : SanPhase → Node
  | .done .rej => downRaw S.ownerRaw
  | _ => S.ownerRaw

def ownerSite (S : SanFrame) (p : SanPhase) : SNode :=
  ⟨ownerRawOf S p, S.ownerLive, ownerCtl p, .unleased, .empty⟩

def targetSite (S : SanFrame) (l : TargetSan) : SNode :=
  ⟨S.targetRaw, S.targetLive, .idle, l, .empty⟩

/-- The interior of the lane.  A forward head has an *empty prefix* and an
arbitrary suffix; a return has an empty interior apart from itself. -/
def interiorSite (g : Nat → SNode) : SanPhase → Nat → SNode
  | .fwd j, k => if k = j then slotOf .sweep else if j < k then g k else slotOf .empty
  | .back r j, k => if k = j then slotOf (retSym r) else slotOf .empty
  | .done _, _ => slotOf .empty

def sanSite (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan) (k : Nat) : SNode :=
  if k = 0 then ownerSite S p
  else if k = S.h then targetSite S l
  else interiorSite g p k

def sanConfigOf (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan) : SanConfig S :=
  fun k => sanSite S g p l k.val

/-- Every interior position of the lane carries a slot; the two roots do not. -/
def GarbageOk (S : SanFrame) (g : Nat → SNode) : Prop :=
  ∀ k, 0 < k → k < S.h → isSlot (g k) = true

/-- The lease may only move from the entry value to `reservedAck`, and only if
the entry value was itself an exclusive reservation. -/
def LeaseStep (S : SanFrame) (l : TargetSan) : Prop :=
  l = S.lease0 ∨ (l = .reservedAck ∧ leasedB S.lease0 = true)

def retOf (S : SanFrame) (l : TargetSan) : Ret :=
  if targetOk (targetSite S l) = true then .ack else .rej

/-! ### Guard values of the lane sites -/

theorem isSlot_ownerSite (S : SanFrame) (p : SanPhase) : isSlot (ownerSite S p) = false := by
  cases p with
  | fwd j => exact rawSlot_of_rawOwner S.hOwner
  | back r j => exact rawSlot_of_rawOwner S.hOwner
  | done r =>
      cases r with
      | ack => exact rawSlot_of_rawOwner S.hOwner
      | rej => exact rawSlot_downRaw (rawSlot_of_rawOwner S.hOwner)

theorem isOwner_ownerSite_fwd (S : SanFrame) (j : Nat) :
    isOwner (ownerSite S (.fwd j)) = true := S.hOwner

theorem isOwner_ownerSite_back (S : SanFrame) (r : Ret) (j : Nat) :
    isOwner (ownerSite S (.back r j)) = true := S.hOwner

theorem isSlot_targetSite (S : SanFrame) (l : TargetSan) :
    isSlot (targetSite S l) = false := S.hTargetRoot

theorem isSlot_interiorSite (S : SanFrame) (g : Nat → SNode) (hg : GarbageOk S g)
    (p : SanPhase) (k : Nat) (h0 : 0 < k) (hh : k < S.h) :
    isSlot (interiorSite g p k) = true := by
  cases p with
  | fwd j =>
      show isSlot (if k = j then slotOf .sweep else if j < k then g k else slotOf .empty) = true
      by_cases h1 : k = j
      · simp [h1]
      · by_cases h2 : j < k
        · simp [h1, h2, hg k h0 hh]
        · simp [h1, h2]
  | back r j =>
      show isSlot (if k = j then slotOf (retSym r) else slotOf .empty) = true
      by_cases h1 : k = j <;> simp [h1]
  | done r => rfl

theorem isSlot_sanSite (S : SanFrame) (g : Nat → SNode) (hg : GarbageOk S g)
    (p : SanPhase) (l : TargetSan) (k : Nat) (h0 : 0 < k) (hh : k < S.h) :
    isSlot (sanSite S g p l k) = true := by
  have h1 : ¬ (k = 0) := by omega
  have h2 : ¬ (k = S.h) := by omega
  simp only [sanSite, if_neg h1, if_neg h2]
  exact isSlot_interiorSite S g hg p k h0 hh

@[simp] theorem sanSite_zero (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan) :
    sanSite S g p l 0 = ownerSite S p := rfl

theorem sanSite_last (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan) :
    sanSite S g p l S.h = targetSite S l := by
  have h : ¬ (S.h = 0) := by have := S.hpos; omega
  simp [sanSite, h]

theorem sanSite_mid (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan)
    (k : Nat) (h0 : k ≠ 0) (hh : k ≠ S.h) :
    sanSite S g p l k = interiorSite g p k := by
  simp [sanSite, h0, hh]

theorem leasedB_of_leaseStep (S : SanFrame) (l : TargetSan) (hl : LeaseStep S l) :
    leasedB l = leasedB S.lease0 := by
  rcases hl with h | ⟨h, h2⟩
  · rw [h]
  · rw [h, h2]
    rfl

theorem retOf_lease_invariant (S : SanFrame) (l : TargetSan) (hl : LeaseStep S l) :
    retOf S l = retOf S S.lease0 := by
  simp only [retOf, targetOk, targetSite, isTarget, leasedB_of_leaseStep S l hl]
  rfl

/-! ### The one-edge transition of the lane -/

def rowAt (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan) (e : Nat) :
    SNode × SNode :=
  sanRow (sanSite S g p l e) (sanSite S g p l (e + 1))

def stepSite (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan)
    (e : Nat) (k : Nat) : SNode :=
  if k = e then (rowAt S g p l e).1
  else if k = e + 1 then (rowAt S g p l e).2
  else sanSite S g p l k

def nextG (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan) (e : Nat) :
    Nat → SNode := fun k => stepSite S g p l e k

def nextL (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan) (e : Nat) :
    TargetSan := (stepSite S g p l e S.h).lease

/-- The phase transition.  Only the head edge of a forward sweep and the
edge immediately left of a return are useful; every other edge keeps the
phase, including all garbage shuffling in the not-yet-swept suffix. -/
def nextP (S : SanFrame) (l : TargetSan) : SanPhase → Nat → SanPhase
  | .fwd j, e =>
      if e = j then
        (if j + 1 = S.h then (if j = 0 then .done (retOf S l) else .back (retOf S l) j)
         else .fwd (j + 1))
      else .fwd j
  | .back r j, e => if e + 1 = j then (if j = 1 then .done r else .back r e) else .back r j
  | .done r, _ => .done r

theorem sanGapStep_apply (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan)
    (j : Fin S.h) (k : Fin (S.h + 1)) :
    sanGapStep S (sanConfigOf S g p l) j k = stepSite S g p l j.val k.val := rfl

theorem interiorSite_idem (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan)
    (k : Nat) (h0 : k ≠ 0) (hh : k ≠ S.h) :
    interiorSite (fun m => sanSite S g p l m) p k = interiorSite g p k := by
  cases p with
  | fwd j =>
      show (if k = j then slotOf .sweep else if j < k then sanSite S g (.fwd j) l k
              else slotOf .empty) =
            (if k = j then slotOf .sweep else if j < k then g k else slotOf .empty)
      by_cases h1 : k = j
      · simp [h1]
      · by_cases h2 : j < k
        · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, sanSite_mid S g _ l k h0 hh]
          show (if k = j then slotOf .sweep else if j < k then g k else slotOf .empty) = g k
          rw [if_neg h1, if_pos h2]
        · simp [h1, h2]
  | back r j => rfl
  | done r => rfl

/-- The generic stuttering step: the row is idle and the phase is unchanged. -/
theorem lane_step_idle (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan)
    (e : Nat)
    (hrow : rowAt S g p l e = (sanSite S g p l e, sanSite S g p l (e + 1)))
    (hnp : nextP S l p e = p) (k : Nat) :
    stepSite S g p l e k = sanSite S (nextG S g p l e) (nextP S l p e) (nextL S g p l e) k := by
  have hstep : ∀ m, stepSite S g p l e m = sanSite S g p l m := by
    intro m
    by_cases h1 : m = e
    · show (if m = e then (rowAt S g p l e).1 else _) = _
      rw [if_pos h1, hrow, h1]
    · by_cases h2 : m = e + 1
      · show (if m = e then _ else if m = e + 1 then (rowAt S g p l e).2 else _) = _
        rw [if_neg h1, if_pos h2, hrow, h2]
      · show (if m = e then _ else if m = e + 1 then _ else sanSite S g p l m) = _
        rw [if_neg h1, if_neg h2]
  have hg' : nextG S g p l e = fun m => sanSite S g p l m := funext hstep
  have hl' : nextL S g p l e = l := by
    show (stepSite S g p l e S.h).lease = l
    rw [hstep S.h, sanSite_last]
    rfl
  rw [hstep k, hnp, hg', hl']
  by_cases h0 : k = 0
  · simp [sanSite, h0]
  · by_cases hh : k = S.h
    · simp [sanSite, hh]
    · rw [sanSite_mid S g p l k h0 hh, sanSite_mid S _ p l k h0 hh,
        interiorSite_idem S g p l k h0 hh]

/-! ### Readback of `nextG`, `nextL` and the site shapes -/

theorem nextG_at (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan) (e : Nat) :
    nextG S g p l e e = (rowAt S g p l e).1 := by
  show stepSite S g p l e e = _
  simp [stepSite]

theorem nextG_at_succ (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan) (e : Nat) :
    nextG S g p l e (e + 1) = (rowAt S g p l e).2 := by
  show stepSite S g p l e (e + 1) = _
  simp [stepSite]

theorem nextG_other (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan)
    (e k : Nat) (h1 : k ≠ e) (h2 : k ≠ e + 1) : nextG S g p l e k = sanSite S g p l k := by
  show stepSite S g p l e k = _
  simp [stepSite, h1, h2]

theorem nextL_of_ne (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan)
    (e : Nat) (he : e < S.h) (h : e + 1 ≠ S.h) : nextL S g p l e = l := by
  show (stepSite S g p l e S.h).lease = l
  have h1 : ¬ (S.h = e) := by omega
  have h2 : ¬ (S.h = e + 1) := by omega
  have hs : stepSite S g p l e S.h = sanSite S g p l S.h := by
    unfold stepSite
    rw [if_neg h1, if_neg h2]
  rw [hs, sanSite_last]
  rfl

theorem nextL_of_eq (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan)
    (e : Nat) (he : e < S.h) (h : e + 1 = S.h) : nextL S g p l e = (rowAt S g p l e).2.lease := by
  show (stepSite S g p l e S.h).lease = _
  have h1 : ¬ (S.h = e) := by omega
  have hs : stepSite S g p l e S.h = (rowAt S g p l e).2 := by
    unfold stepSite
    rw [if_neg h1, if_pos h.symm]
  rw [hs]

theorem sanSite_interior_fwd (S : SanFrame) (g : Nat → SNode) (j : Nat) (l : TargetSan)
    (m : Nat) (h0 : m ≠ 0) (hh : m ≠ S.h) :
    sanSite S g (.fwd j) l m =
      if m = j then slotOf .sweep else if j < m then g m else slotOf .empty := by
  rw [sanSite_mid S g _ l m h0 hh]
  rfl

theorem sanSite_interior_back (S : SanFrame) (g : Nat → SNode) (r : Ret) (j : Nat)
    (l : TargetSan) (m : Nat) (h0 : m ≠ 0) (hh : m ≠ S.h) :
    sanSite S g (.back r j) l m = if m = j then slotOf (retSym r) else slotOf .empty := by
  rw [sanSite_mid S g _ l m h0 hh]
  rfl

theorem sanSite_interior_done (S : SanFrame) (g : Nat → SNode) (r : Ret) (l : TargetSan)
    (m : Nat) (h0 : m ≠ 0) (hh : m ≠ S.h) : sanSite S g (.done r) l m = slotOf .empty := by
  rw [sanSite_mid S g _ l m h0 hh]
  rfl

theorem interiorSite_nextG_same (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan)
    (e k : Nat) (h1 : k ≠ e) (h2 : k ≠ e + 1) (h0 : k ≠ 0) (hh : k ≠ S.h) :
    interiorSite (nextG S g p l e) p k = interiorSite g p k := by
  cases p with
  | fwd j =>
      show (if k = j then slotOf .sweep else if j < k then nextG S g (.fwd j) l e k
              else slotOf .empty) =
            (if k = j then slotOf .sweep else if j < k then g k else slotOf .empty)
      by_cases ha : k = j
      · simp [ha]
      · by_cases hb : j < k
        · rw [if_neg ha, if_pos hb, if_neg ha, if_pos hb,
            nextG_other S g _ l e k h1 h2, sanSite_interior_fwd S g j l k h0 hh,
            if_neg ha, if_pos hb]
        · simp [ha, hb]
  | back r j => rfl
  | done r => rfl

/-- If the row is applied at an edge whose right endpoint is the right root,
the only field it can write there is the sanitizer lease. -/
theorem rowAt_target_form (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan)
    (e : Nat) (hh : e + 1 = S.h) :
    (rowAt S g p l e).2 = targetSite S ((rowAt S g p l e).2.lease) := by
  have hb : sanSite S g p l (e + 1) = targetSite S l := by
    rw [hh, sanSite_last]
  have hbs : isSlot (sanSite S g p l (e + 1)) = false := by
    rw [hb]; exact S.hTargetRoot
  have hrow : (rowAt S g p l e).2 = sanSite S g p l (e + 1) ∨
      (rowAt S g p l e).2 = armTarget (sanSite S g p l (e + 1)) :=
    sanRow_right_frame (sanSite S g p l e) (sanSite S g p l (e + 1)) hbs
  rcases hrow with h' | h'
  · rw [h', hb]
    rfl
  · rw [h', hb]
    rfl

/-- The generic non-stuttering step: the two endpoint obligations plus the
three framing obligations. -/
theorem lane_step_of_row (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan)
    (e : Nat) (he : e < S.h) (p' : SanPhase) (hnp : nextP S l p e = p')
    (hL : (rowAt S g p l e).1 = sanSite S (nextG S g p l e) p' (nextL S g p l e) e)
    (hR : (rowAt S g p l e).2 = sanSite S (nextG S g p l e) p' (nextL S g p l e) (e + 1))
    (hO : e ≠ 0 → ownerSite S p' = ownerSite S p)
    (hI : ∀ k, k ≠ e → k ≠ e + 1 → k ≠ 0 → k ≠ S.h → k ≤ S.h →
        interiorSite (nextG S g p l e) p' k = interiorSite g p k)
    (k : Nat) (hk : k ≤ S.h) :
    stepSite S g p l e k = sanSite S (nextG S g p l e) (nextP S l p e) (nextL S g p l e) k := by
  rw [hnp]
  by_cases h1 : k = e
  · subst h1
    rw [show stepSite S g p l k k = (rowAt S g p l k).1 by simp [stepSite]]
    exact hL
  · by_cases h2 : k = e + 1
    · subst h2
      rw [show stepSite S g p l e (e + 1) = (rowAt S g p l e).2 by simp [stepSite]]
      exact hR
    · have hstep : stepSite S g p l e k = sanSite S g p l k := by
        simp [stepSite, h1, h2]
      rw [hstep]
      by_cases h0 : k = 0
      · subst h0
        have hne : e ≠ 0 := fun hbad => h1 (by omega)
        rw [sanSite_zero, sanSite_zero, hO hne]
      · by_cases hh : k = S.h
        · have hne : e + 1 ≠ S.h := fun hbad => h2 (by omega)
          subst hh
          rw [sanSite_last, sanSite_last, nextL_of_ne S g p l e he hne]
        · rw [sanSite_mid S g p l k h0 hh, sanSite_mid S _ p' _ k h0 hh]
          exact (hI k h1 h2 h0 hh hk).symm

/-! ### The stuttering edges -/

theorem carrier_sanSite_done (S : SanFrame) (g : Nat → SNode) (r : Ret) (l : TargetSan)
    (m : Nat) : (sanSite S g (.done r) l m).carrier = SanSym.empty := by
  by_cases h0 : m = 0
  · subst h0; rfl
  · by_cases hh : m = S.h
    · subst hh; rw [sanSite_last]; rfl
    · rw [sanSite_interior_done S g r l m h0 hh]; rfl

theorem rowAt_done (S : SanFrame) (g : Nat → SNode) (r : Ret) (l : TargetSan)
    (e : Nat) (he : e < S.h) :
    rowAt S g (.done r) l e = (sanSite S g (.done r) l e, sanSite S g (.done r) l (e + 1)) := by
  by_cases h0 : e = 0
  · subst h0
    show sanRow (sanSite S g (.done r) l 0) (sanSite S g (.done r) l 1) = _
    rw [sanSite_zero]
    exact row_done_stutter _ _ (by cases r <;> rfl) (by cases r <;> rfl) (isSlot_ownerSite S _)
  · have hh : e ≠ S.h := by omega
    have ha : sanSite S g (.done r) l e = slotOf .empty := sanSite_interior_done S g r l e h0 hh
    show sanRow (sanSite S g (.done r) l e) (sanSite S g (.done r) l (e + 1)) = _
    rw [ha]
    exact row_slot_stutter _ _ rfl rfl
      (by rw [carrier_sanSite_done]; rfl) (by rw [carrier_sanSite_done]; rfl)

theorem rowAt_back_idle (S : SanFrame) (g : Nat → SNode) (r : Ret) (j : Nat) (l : TargetSan)
    (e : Nat) (hj1 : 1 ≤ j) (hj2 : j < S.h) (he : e < S.h) (hne : e + 1 ≠ j) :
    rowAt S g (.back r j) l e =
      (sanSite S g (.back r j) l e, sanSite S g (.back r j) l (e + 1)) := by
  have hcb : (sanSite S g (.back r j) l (e + 1)).carrier = SanSym.empty := by
    by_cases hh : e + 1 = S.h
    · rw [hh, sanSite_last]; rfl
    · rw [sanSite_interior_back S g r j l (e + 1) (by omega) hh, if_neg hne]; rfl
  by_cases h0 : e = 0
  · subst h0
    show sanRow (sanSite S g (.back r j) l 0) (sanSite S g (.back r j) l 1) = _
    rw [sanSite_zero]
    exact row_wait_stutter _ _ S.hOwner rfl (by rw [hcb]; rfl) (by rw [hcb]; rfl)
  · have hh : e ≠ S.h := by omega
    have ha := sanSite_interior_back S g r j l e h0 hh
    exact row_slot_stutter _ _
      (by rw [ha]; by_cases hm : e = j <;> simp [hm])
      (by rw [ha]
          by_cases hm : e = j
          · rw [if_pos hm]; cases r <;> rfl
          · rw [if_neg hm]; rfl)
      (by rw [hcb]; rfl) (by rw [hcb]; rfl)

theorem rowAt_fwd_before (S : SanFrame) (g : Nat → SNode) (j : Nat) (l : TargetSan)
    (e : Nat) (hj : j < S.h) (hlt : e < j) :
    rowAt S g (.fwd j) l e = (sanSite S g (.fwd j) l e, sanSite S g (.fwd j) l (e + 1)) := by
  have hb : sanSite S g (.fwd j) l (e + 1) =
      if e + 1 = j then slotOf .sweep else slotOf .empty := by
    rw [sanSite_interior_fwd S g j l (e + 1) (by omega) (by omega)]
    by_cases hm : e + 1 = j
    · rw [if_pos hm, if_pos hm]
    · rw [if_neg hm, if_neg hm, if_neg (by omega : ¬ (j < e + 1))]
  have hcb1 : isAckSym (sanSite S g (.fwd j) l (e + 1)).carrier = false := by
    rw [hb]; by_cases hm : e + 1 = j <;> simp [hm]
  have hcb2 : isRejSym (sanSite S g (.fwd j) l (e + 1)).carrier = false := by
    rw [hb]; by_cases hm : e + 1 = j <;> simp [hm]
  by_cases h0 : e = 0
  · subst h0
    show sanRow (sanSite S g (.fwd j) l 0) (sanSite S g (.fwd j) l 1) = _
    rw [sanSite_zero]
    exact row_wait_stutter _ _ S.hOwner
      (by show isWait (ownerCtl (.fwd j)) = true
          rw [ownerCtl_fwd_pos (by omega)]; rfl) hcb1 hcb2
  · have ha : sanSite S g (.fwd j) l e = slotOf .empty := by
      rw [sanSite_interior_fwd S g j l e h0 (by omega),
        if_neg (by omega : ¬ (e = j)), if_neg (by omega : ¬ (j < e))]
    show sanRow (sanSite S g (.fwd j) l e) (sanSite S g (.fwd j) l (e + 1)) = _
    rw [ha]
    exact row_slot_stutter _ _ rfl rfl hcb1 hcb2

/-! ### The useful edges -/

theorem rowAt_back_deposit (S : SanFrame) (g : Nat → SNode) (r : Ret) (l : TargetSan)
    (hS : 1 < S.h) : rowAt S g (.back r 1) l 0 = (ownerSite S (.done r), slotOf .empty) := by
  have hb : sanSite S g (.back r 1) l 1 = slotOf (retSym r) := by
    rw [sanSite_interior_back S g r 1 l 1 (by omega) (by omega), if_pos rfl]
  show sanRow (sanSite S g (.back r 1) l 0) (sanSite S g (.back r 1) l 1) = _
  rw [sanSite_zero, hb]
  cases r with
  | ack => exact row_ack_deposit _ _ S.hOwner rfl rfl rfl
  | rej => exact row_rej_deposit _ _ S.hOwner rfl rfl rfl

theorem rowAt_backward (S : SanFrame) (g : Nat → SNode) (r : Ret) (j : Nat) (l : TargetSan)
    (e : Nat) (hj1 : 2 ≤ j) (hj2 : j < S.h) (hej : e + 1 = j) :
    rowAt S g (.back r j) l e = (slotOf (retSym r), slotOf .empty) := by
  have ha : sanSite S g (.back r j) l e = slotOf .empty := by
    rw [sanSite_interior_back S g r j l e (by omega) (by omega),
      if_neg (by omega : ¬ (e = j))]
  have hb : sanSite S g (.back r j) l (e + 1) = slotOf (retSym r) := by
    rw [sanSite_interior_back S g r j l (e + 1) (by omega) (by omega), if_pos hej]
  show sanRow (sanSite S g (.back r j) l e) (sanSite S g (.back r j) l (e + 1)) = _
  rw [ha, hb]
  cases r with
  | ack => exact row_backward_ack _ rfl rfl
  | rej => exact row_backward_rej _ rfl rfl

theorem rowAt_launch (S : SanFrame) (g : Nat → SNode) (l : TargetSan)
    (hg : GarbageOk S g) (hS : 1 < S.h) :
    rowAt S g (.fwd 0) l 0 = (ownerSite S (.fwd 1), slotOf .sweep) := by
  have hb : sanSite S g (.fwd 0) l 1 = g 1 := by
    rw [sanSite_interior_fwd S g 0 l 1 (by omega) (by omega),
      if_neg (by omega : ¬ ((1 : Nat) = 0)), if_pos (by omega : (0 : Nat) < 1)]
  show sanRow (sanSite S g (.fwd 0) l 0) (sanSite S g (.fwd 0) l 1) = _
  rw [sanSite_zero, hb]
  exact row_launch _ _ S.hOwner rfl (hg 1 (by omega) (by omega))

theorem rowAt_forward (S : SanFrame) (g : Nat → SNode) (j : Nat) (l : TargetSan)
    (hg : GarbageOk S g) (hj1 : 1 ≤ j) (hj2 : j + 1 < S.h) :
    rowAt S g (.fwd j) l j = (slotOf .empty, slotOf .sweep) := by
  have ha : sanSite S g (.fwd j) l j = slotOf .sweep := by
    rw [sanSite_interior_fwd S g j l j (by omega) (by omega), if_pos rfl]
  have hb : sanSite S g (.fwd j) l (j + 1) = g (j + 1) := by
    rw [sanSite_interior_fwd S g j l (j + 1) (by omega) (by omega),
      if_neg (by omega : ¬ (j + 1 = j)), if_pos (by omega : j < j + 1)]
  show sanRow (sanSite S g (.fwd j) l j) (sanSite S g (.fwd j) l (j + 1)) = _
  rw [ha, hb]
  exact row_forward _ (hg (j + 1) (by omega) (by omega))

theorem rowAt_direct (S : SanFrame) (g : Nat → SNode) (l : TargetSan) (hS : 0 + 1 = S.h) :
    (rowAt S g (.fwd 0) l 0).1 = ownerSite S (.done (retOf S l)) := by
  have hb : sanSite S g (.fwd 0) l 1 = targetSite S l := by
    rw [show (1 : Nat) = S.h by omega, sanSite_last]
  show (sanRow (sanSite S g (.fwd 0) l 0) (sanSite S g (.fwd 0) l 1)).1 = _
  rw [sanSite_zero, hb]
  by_cases hv : targetOk (targetSite S l) = true
  · rw [row_direct_ack (ownerSite S (.fwd 0)) (targetSite S l)
        (isOwner_ownerSite_fwd S 0) rfl (isSlot_targetSite S l) hv,
      show retOf S l = Ret.ack by simp [retOf, hv]]
    rfl
  · rw [row_direct_reject (ownerSite S (.fwd 0)) (targetSite S l)
        (isOwner_ownerSite_fwd S 0) rfl (isSlot_targetSite S l) (bool_of_not_true hv),
      show retOf S l = Ret.rej by simp [retOf, hv]]
    rfl

theorem rowAt_turn (S : SanFrame) (g : Nat → SNode) (j : Nat) (l : TargetSan)
    (hj1 : 1 ≤ j) (hj2 : j + 1 = S.h) :
    (rowAt S g (.fwd j) l j).1 = slotOf (retSym (retOf S l)) := by
  have ha : sanSite S g (.fwd j) l j = slotOf .sweep := by
    rw [sanSite_interior_fwd S g j l j (by omega) (by omega), if_pos rfl]
  have hb : sanSite S g (.fwd j) l (j + 1) = targetSite S l := by
    rw [hj2, sanSite_last]
  show (sanRow (sanSite S g (.fwd j) l j) (sanSite S g (.fwd j) l (j + 1))).1 = _
  rw [ha, hb]
  by_cases hv : targetOk (targetSite S l) = true
  · rw [row_turn_ack (slotOf .sweep) (targetSite S l) rfl rfl (isSlot_targetSite S l) hv,
      show retOf S l = Ret.ack by simp [retOf, hv]]
    rfl
  · rw [row_turn_reject (slotOf .sweep) (targetSite S l) rfl rfl (isSlot_targetSite S l)
        (bool_of_not_true hv),
      show retOf S l = Ret.rej by simp [retOf, hv]]
    rfl

/-- At the last gap edge the right endpoint is the right root, so its new
value is the target site of the new lease, whatever phase the sweep enters. -/
theorem lane_row_right_target (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan)
    (e : Nat) (he : e < S.h) (hlast : e + 1 = S.h) (p' : SanPhase) :
    (rowAt S g p l e).2 = sanSite S (nextG S g p l e) p' (nextL S g p l e) (e + 1) := by
  rw [show sanSite S (nextG S g p l e) p' (nextL S g p l e) (e + 1)
        = targetSite S (nextL S g p l e) by rw [hlast, sanSite_last],
    nextL_of_eq S g p l e he hlast]
  exact rowAt_target_form S g p l e hlast

/-! ### The lane is closed under every gap edge

This is the theorem the design answer only asserts.  Note what it quantifies
over: an arbitrary `g`, i.e. arbitrary raw payloads *and* arbitrary forged
sanitizer symbols in the not-yet-swept suffix, including a forged `S` that
turns around at the target and sends a forged `A` back into the suffix. -/
theorem lane_step_site (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan)
    (hp : PhaseOkS S p) (hg : GarbageOk S g) (e : Nat) (he : e < S.h)
    (k : Nat) (hk : k ≤ S.h) :
    stepSite S g p l e k = sanSite S (nextG S g p l e) (nextP S l p e) (nextL S g p l e) k := by
  cases p with
  | done r => exact lane_step_idle S g (.done r) l e (rowAt_done S g r l e he) rfl k
  | back r j =>
      have hj1 : 1 ≤ j := hp.1
      have hj2 : j < S.h := hp.2
      by_cases hej : e + 1 = j
      · by_cases hj : j = 1
        · subst hj
          have he0 : e = 0 := by omega
          subst he0
          refine lane_step_of_row S g (.back r 1) l 0 he (.done r) rfl ?_ ?_ ?_ ?_ k hk
          · rw [rowAt_back_deposit S g r l (by omega), sanSite_zero]
          · rw [rowAt_back_deposit S g r l (by omega),
              sanSite_interior_done S (nextG S g (.back r 1) l 0) r
                (nextL S g (.back r 1) l 0) 1 (by omega) (by omega)]
          · intro hbad; exact absurd rfl hbad
          · intro m h1 h2 h0 hh _
            show slotOf .empty = (if m = 1 then slotOf (retSym r) else slotOf .empty)
            rw [if_neg (by omega : ¬ (m = 1))]
        · have hj2' : 2 ≤ j := by omega
          have he1 : 1 ≤ e := by omega
          refine lane_step_of_row S g (.back r j) l e he (.back r e)
            (by simp [nextP, hej, hj]) ?_ ?_ ?_ ?_ k hk
          · rw [rowAt_backward S g r j l e hj2' hj2 hej,
              sanSite_interior_back S (nextG S g (.back r j) l e) r e
                (nextL S g (.back r j) l e) e (by omega) (by omega), if_pos rfl]
          · rw [rowAt_backward S g r j l e hj2' hj2 hej,
              sanSite_interior_back S (nextG S g (.back r j) l e) r e
                (nextL S g (.back r j) l e) (e + 1) (by omega) (by omega),
              if_neg (by omega : ¬ (e + 1 = e))]
          · intro _; rfl
          · intro m h1 h2 h0 hh _
            show (if m = e then slotOf (retSym r) else slotOf .empty)
              = (if m = j then slotOf (retSym r) else slotOf .empty)
            rw [if_neg h1, if_neg (by omega : ¬ (m = j))]
      · exact lane_step_idle S g (.back r j) l e
          (rowAt_back_idle S g r j l e hj1 hj2 he hej) (by simp [nextP, hej]) k
  | fwd j =>
      have hj : j < S.h := hp
      by_cases hej : e = j
      · subst hej
        by_cases hlast : e + 1 = S.h
        · by_cases h0 : e = 0
          · subst h0
            refine lane_step_of_row S g (.fwd 0) l 0 he (.done (retOf S l))
              (by simp [nextP, hlast]) ?_ ?_ ?_ ?_ k hk
            · rw [rowAt_direct S g l hlast, sanSite_zero]
            · exact lane_row_right_target S g (.fwd 0) l 0 he hlast _
            · intro hbad; exact absurd rfl hbad
            · intro m h1 h2 h0 hh hm; omega
          · refine lane_step_of_row S g (.fwd e) l e he (.back (retOf S l) e)
              (by simp [nextP, hlast, h0]) ?_ ?_ ?_ ?_ k hk
            · rw [rowAt_turn S g e l (by omega) hlast,
                sanSite_interior_back S (nextG S g (.fwd e) l e) (retOf S l) e
                  (nextL S g (.fwd e) l e) e (by omega) (by omega), if_pos rfl]
            · exact lane_row_right_target S g (.fwd e) l e he hlast _
            · intro _
              show (⟨ownerRawOf S (.back (retOf S l) e), S.ownerLive,
                  ownerCtl (.back (retOf S l) e), .unleased, .empty⟩ : SNode)
                = ⟨ownerRawOf S (.fwd e), S.ownerLive, ownerCtl (.fwd e), .unleased, .empty⟩
              rw [ownerCtl_fwd_pos (by omega : 0 < e)]
              rfl
            · intro m h1 h2 h0 hh hm
              show (if m = e then slotOf (retSym (retOf S l)) else slotOf .empty)
                = (if m = e then slotOf .sweep else if e < m then g m else slotOf .empty)
              rw [if_neg h1, if_neg h1, if_neg (by omega : ¬ (e < m))]
        · by_cases h0 : e = 0
          · subst h0
            refine lane_step_of_row S g (.fwd 0) l 0 he (.fwd 1)
              (by simp [nextP, hlast]) ?_ ?_ ?_ ?_ k hk
            · rw [rowAt_launch S g l hg (by omega), sanSite_zero]
            · rw [rowAt_launch S g l hg (by omega),
                sanSite_interior_fwd S (nextG S g (.fwd 0) l 0) 1
                  (nextL S g (.fwd 0) l 0) 1 (by omega) (by omega), if_pos rfl]
            · intro hbad; exact absurd rfl hbad
            · intro m h1 h2 h0 hh hm
              show (if m = 1 then slotOf .sweep else if 1 < m then nextG S g (.fwd 0) l 0 m
                      else slotOf .empty)
                = (if m = 0 then slotOf .sweep else if 0 < m then g m else slotOf .empty)
              rw [if_neg h2, if_pos (by omega : 1 < m), if_neg h0, if_pos (by omega : 0 < m),
                nextG_other S g (.fwd 0) l 0 m h1 h2,
                sanSite_interior_fwd S g 0 l m h0 hh, if_neg h0, if_pos (by omega : 0 < m)]
          · refine lane_step_of_row S g (.fwd e) l e he (.fwd (e + 1))
              (by simp [nextP, hlast]) ?_ ?_ ?_ ?_ k hk
            · rw [rowAt_forward S g e l hg (by omega) (by omega),
                sanSite_interior_fwd S (nextG S g (.fwd e) l e) (e + 1)
                  (nextL S g (.fwd e) l e) e (by omega) (by omega),
                if_neg (by omega : ¬ (e = e + 1)), if_neg (by omega : ¬ (e + 1 < e))]
            · rw [rowAt_forward S g e l hg (by omega) (by omega),
                sanSite_interior_fwd S (nextG S g (.fwd e) l e) (e + 1)
                  (nextL S g (.fwd e) l e) (e + 1) (by omega) (by omega), if_pos rfl]
            · intro _
              show (⟨ownerRawOf S (.fwd (e + 1)), S.ownerLive,
                  ownerCtl (.fwd (e + 1)), .unleased, .empty⟩ : SNode)
                = ⟨ownerRawOf S (.fwd e), S.ownerLive, ownerCtl (.fwd e), .unleased, .empty⟩
              rw [ownerCtl_fwd_pos (by omega : 0 < e), ownerCtl_fwd_pos (by omega : 0 < e + 1)]
              rfl
            · intro m h1 h2 h0 hh hm
              show (if m = e + 1 then slotOf .sweep
                      else if e + 1 < m then nextG S g (.fwd e) l e m else slotOf .empty)
                = (if m = e then slotOf .sweep else if e < m then g m else slotOf .empty)
              rw [if_neg h2, if_neg h1]
              by_cases hlt : e < m
              · rw [if_pos hlt, if_pos (by omega : e + 1 < m),
                  nextG_other S g (.fwd e) l e m h1 h2,
                  sanSite_interior_fwd S g e l m h0 hh, if_neg h1, if_pos hlt]
              · rw [if_neg hlt, if_neg (by omega : ¬ (e + 1 < m))]
      · by_cases hlt : e < j
        · exact lane_step_idle S g (.fwd j) l e (rowAt_fwd_before S g j l e hj hlt)
            (by simp [nextP, hej]) k
        · have hgt : j < e := by omega
          have he0 : e ≠ 0 := by omega
          refine lane_step_of_row S g (.fwd j) l e he (.fwd j)
            (by simp [nextP, hej]) ?_ ?_ ?_ ?_ k hk
          · rw [sanSite_interior_fwd S (nextG S g (.fwd j) l e) j (nextL S g (.fwd j) l e) e
              he0 (by omega), if_neg (by omega : ¬ (e = j)), if_pos hgt, nextG_at]
          · by_cases hlast : e + 1 = S.h
            · exact lane_row_right_target S g (.fwd j) l e he hlast _
            · rw [sanSite_interior_fwd S (nextG S g (.fwd j) l e) j (nextL S g (.fwd j) l e)
                (e + 1) (by omega) hlast, if_neg (by omega : ¬ (e + 1 = j)),
                if_pos (by omega : j < e + 1), nextG_at_succ]
          · intro _; rfl
          · intro m h1 h2 h0 hh _
            exact interiorSite_nextG_same S g (.fwd j) l e m h1 h2 h0 hh

theorem lane_step (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan)
    (hp : PhaseOkS S p) (hg : GarbageOk S g) (j : Fin S.h) :
    sanGapStep S (sanConfigOf S g p l) j =
      sanConfigOf S (nextG S g p l j.val) (nextP S l p j.val) (nextL S g p l j.val) := by
  funext k
  rw [sanGapStep_apply]
  exact lane_step_site S g p l hp hg j.val j.isLt k.val (by omega)

/-! ### The lane invariants are preserved -/

theorem rawSlot_downRaw_eq (n : Node) : rawSlot (downRaw n) = rawSlot n := by
  cases n with
  | interior w => rfl
  | root ch cw ccw out inc => rfl

private theorem step_left_slot {a b x y : SNode} {k : Rule} (h : RowStep a b k x y)
    (ha : isSlot a = true) : isSlot x = true := by
  cases h with
  | launch _ _ _ => exact ha
  | directAck _ _ _ _ => exact ha
  | directReject _ _ _ _ => show rawSlot (downRaw a.raw) = true; rw [rawSlot_downRaw_eq]; exact ha
  | ackDeposit _ _ _ _ => exact ha
  | rejDeposit _ _ _ _ => show rawSlot (downRaw a.raw) = true; rw [rawSlot_downRaw_eq]; exact ha
  | forward _ _ _ => rfl
  | turnAck _ _ _ _ => rfl
  | turnReject _ _ _ _ => rfl
  | backAck _ _ _ _ => rfl
  | backRej _ _ _ _ => rfl
  | idle => exact ha

private theorem step_right_slot {a b x y : SNode} {k : Rule} (h : RowStep a b k x y)
    (hb : isSlot b = true) : isSlot y = true := by
  cases h with
  | launch _ _ _ => rfl
  | directAck _ _ _ _ => exact hb
  | directReject _ _ _ _ => exact hb
  | ackDeposit _ _ _ _ => rfl
  | rejDeposit _ _ _ _ => rfl
  | forward _ _ _ => rfl
  | turnAck _ _ _ _ => exact hb
  | turnReject _ _ _ _ => exact hb
  | backAck _ _ _ _ => rfl
  | backRej _ _ _ _ => rfl
  | idle => exact hb

private theorem step_right_lease {a b x y : SNode} {k : Rule} (h : RowStep a b k x y)
    (hb : isSlot b = false) :
    y.lease = b.lease ∨ (y.lease = TargetSan.reservedAck ∧ targetOk b = true) := by
  cases h with
  | launch _ _ h3 => rw [hb] at h3; exact absurd h3 (by simp)
  | directAck _ _ _ h4 => exact Or.inr ⟨rfl, h4⟩
  | directReject _ _ _ _ => exact Or.inl rfl
  | ackDeposit _ _ h3 _ => rw [hb] at h3; exact absurd h3 (by simp)
  | rejDeposit _ _ h3 _ => rw [hb] at h3; exact absurd h3 (by simp)
  | forward _ _ h3 => rw [hb] at h3; exact absurd h3 (by simp)
  | turnAck _ _ _ h4 => exact Or.inr ⟨rfl, h4⟩
  | turnReject _ _ _ _ => exact Or.inl rfl
  | backAck _ _ h3 _ => rw [hb] at h3; exact absurd h3 (by simp)
  | backRej _ _ h3 _ => rw [hb] at h3; exact absurd h3 (by simp)
  | idle => exact Or.inl rfl

theorem phaseOk_next (S : SanFrame) (l : TargetSan) (p : SanPhase) (hp : PhaseOkS S p)
    (e : Nat) (he : e < S.h) : PhaseOkS S (nextP S l p e) := by
  cases p with
  | fwd j =>
      have hj : j < S.h := hp
      by_cases hej : e = j
      · subst hej
        by_cases hlast : e + 1 = S.h
        · by_cases h0 : e = 0
          · subst h0
            show PhaseOkS S (if (0 : Nat) = 0 then
              (if 0 + 1 = S.h then (if (0 : Nat) = 0 then SanPhase.done (retOf S l)
                else SanPhase.back (retOf S l) 0) else SanPhase.fwd (0 + 1))
              else SanPhase.fwd 0)
            rw [if_pos rfl, if_pos hlast, if_pos rfl]
            trivial
          · show PhaseOkS S (if e = e then
              (if e + 1 = S.h then (if e = 0 then SanPhase.done (retOf S l)
                else SanPhase.back (retOf S l) e) else SanPhase.fwd (e + 1))
              else SanPhase.fwd e)
            rw [if_pos rfl, if_pos hlast, if_neg h0]
            exact ⟨by omega, by omega⟩
        · show PhaseOkS S (if e = e then
            (if e + 1 = S.h then (if e = 0 then SanPhase.done (retOf S l)
              else SanPhase.back (retOf S l) e) else SanPhase.fwd (e + 1))
            else SanPhase.fwd e)
          rw [if_pos rfl, if_neg hlast]
          show e + 1 < S.h
          omega
      · simpa [nextP, hej, PhaseOkS] using hj
  | back r j =>
      have hj1 : 1 ≤ j := hp.1
      have hj2 : j < S.h := hp.2
      by_cases hej : e + 1 = j
      · show PhaseOkS S (if e + 1 = j then
          (if j = 1 then SanPhase.done r else SanPhase.back r e) else SanPhase.back r j)
        rw [if_pos hej]
        by_cases hj : j = 1
        · rw [if_pos hj]; trivial
        · rw [if_neg hj]
          exact ⟨by omega, by omega⟩
      · simpa [nextP, hej, PhaseOkS] using ⟨hj1, hj2⟩
  | done r => trivial

theorem garbageOk_next (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan)
    (hg : GarbageOk S g) (e : Nat) : GarbageOk S (nextG S g p l e) := by
  intro k h0 hh
  by_cases h1 : k = e
  · have hslot : isSlot (sanSite S g p l e) = true := by
      rw [← h1]; exact isSlot_sanSite S g hg p l k h0 hh
    show isSlot (stepSite S g p l e k) = true
    rw [show stepSite S g p l e k = (rowAt S g p l e).1 by simp [stepSite, h1]]
    exact step_left_slot (sanRow_spec _ _) hslot
  · by_cases h2 : k = e + 1
    · have hslot : isSlot (sanSite S g p l (e + 1)) = true := by
        rw [← h2]; exact isSlot_sanSite S g hg p l k h0 hh
      show isSlot (stepSite S g p l e k) = true
      rw [show stepSite S g p l e k = (rowAt S g p l e).2 by simp [stepSite, h2]]
      exact step_right_slot (sanRow_spec _ _) hslot
    · show isSlot (stepSite S g p l e k) = true
      rw [show stepSite S g p l e k = sanSite S g p l k by simp [stepSite, h1, h2]]
      exact isSlot_sanSite S g hg p l k h0 hh

theorem leaseStep_next (S : SanFrame) (g : Nat → SNode) (p : SanPhase) (l : TargetSan)
    (hl : LeaseStep S l) (e : Nat) (he : e < S.h) : LeaseStep S (nextL S g p l e) := by
  by_cases hlast : e + 1 = S.h
  · rw [nextL_of_eq S g p l e he hlast]
    have hb : sanSite S g p l (e + 1) = targetSite S l := by rw [hlast, sanSite_last]
    have hbs : isSlot (sanSite S g p l (e + 1)) = false := by rw [hb]; exact S.hTargetRoot
    have h := step_right_lease (sanRow_spec (sanSite S g p l e) (sanSite S g p l (e + 1))) hbs
    have h' : (rowAt S g p l e).2.lease = (sanSite S g p l (e + 1)).lease ∨
        ((rowAt S g p l e).2.lease = TargetSan.reservedAck ∧
          targetOk (sanSite S g p l (e + 1)) = true) := h
    rcases h' with h'' | ⟨h'', hv⟩
    · rw [h'', hb]
      exact hl
    · rw [h'']
      refine Or.inr ⟨rfl, ?_⟩
      rw [hb] at hv
      have hlz : leasedB l = true := by
        have := hv
        simp only [targetOk, Bool.and_eq_true] at this
        exact this.2
      rw [← leasedB_of_leaseStep S l hl]
      exact hlz
  · rw [nextL_of_ne S g p l e he hlast]
    exact hl

/-! ## The sweep as a stopped process -/

structure SweepState (S : SanFrame) where
  garbage : Nat → SNode
  phase : SanPhase
  lease : TargetSan
  hg : GarbageOk S garbage
  hp : PhaseOkS S phase
  hl : LeaseStep S lease

def sweepCfg (S : SanFrame) (s : SweepState S) : SanConfig S :=
  sanConfigOf S s.garbage s.phase s.lease

def sweepAdvance (S : SanFrame) (s : SweepState S) (j : Fin S.h) : SweepState S :=
  ⟨nextG S s.garbage s.phase s.lease j.val,
   nextP S s.lease s.phase j.val,
   nextL S s.garbage s.phase s.lease j.val,
   garbageOk_next S s.garbage s.phase s.lease s.hg j.val,
   phaseOk_next S s.lease s.phase s.hp j.val j.isLt,
   leaseStep_next S s.garbage s.phase s.lease s.hl j.val j.isLt⟩

/-- The abstract sweep state and the physical configuration agree on every
gap edge: the lane really is executed by `sanGapStep`. -/
theorem sweepAdvance_cfg (S : SanFrame) (s : SweepState S) (j : Fin S.h) :
    sweepCfg S (sweepAdvance S s j) = sanGapStep S (sweepCfg S s) j :=
  (lane_step S s.garbage s.phase s.lease s.hp s.hg j).symm

open Classical in
noncomputable def sweepSched {n : Nat} (S : SanFrame) (E : SanEmbedding S n)
    (s : SweepState S) (e : Fin n) : SweepState S :=
  if hx : ∃ a : Fin S.h, E.edgeAt a = e then sweepAdvance S s hx.choose else s

theorem sweepSched_eq {n : Nat} (S : SanFrame) (E : SanEmbedding S n)
    (s : SweepState S) (a : Fin S.h) :
    sweepSched S E s (E.edgeAt a) = sweepAdvance S s a := by
  classical
  have hx : ∃ b : Fin S.h, E.edgeAt b = E.edgeAt a := ⟨a, rfl⟩
  rw [sweepSched, dif_pos hx]
  have hchoose : E.edgeAt hx.choose = E.edgeAt a := hx.choose_spec
  rw [E.inj _ _ hchoose]

theorem sweepSched_cases {n : Nat} (S : SanFrame) (E : SanEmbedding S n)
    (s : SweepState S) (e : Fin n) :
    sweepSched S E s e = s ∨ ∃ a : Fin S.h, sweepSched S E s e = sweepAdvance S s a := by
  classical
  by_cases hx : ∃ a : Fin S.h, E.edgeAt a = e
  · obtain ⟨a, ha⟩ := hx
    subst ha
    exact Or.inr ⟨a, sweepSched_eq S E s a⟩
  · refine Or.inl ?_
    rw [sweepSched, dif_neg hx]

/-- Physical soundness: the abstract scheduler step is the real one. -/
theorem sweepSched_cfg {n : Nat} (S : SanFrame) (E : SanEmbedding S n)
    (s : SweepState S) (e : Fin n) :
    sweepCfg S (sweepSched S E s e) = sanSchedStep S E (sweepCfg S s) e := by
  classical
  by_cases hx : ∃ a : Fin S.h, E.edgeAt a = e
  · unfold sweepSched sanSchedStep
    rw [dif_pos hx, dif_pos hx]
    exact sweepAdvance_cfg S s hx.choose
  · unfold sweepSched sanSchedStep
    rw [dif_neg hx, dif_neg hx]

@[simp] theorem nextP_fwd (S : SanFrame) (l : TargetSan) (j e : Nat) :
    nextP S l (.fwd j) e =
      if e = j then
        (if j + 1 = S.h then (if j = 0 then .done (retOf S l) else .back (retOf S l) j)
         else .fwd (j + 1))
      else .fwd j := rfl

@[simp] theorem nextP_back (S : SanFrame) (l : TargetSan) (r : Ret) (j e : Nat) :
    nextP S l (.back r j) e =
      if e + 1 = j then (if j = 1 then .done r else .back r e) else .back r j := rfl

@[simp] theorem nextP_done (S : SanFrame) (l : TargetSan) (r : Ret) (e : Nat) :
    nextP S l (.done r) e = .done r := rfl

/-! ## The service debt

`2h-1` before launch, `2h-1-j` with the head at `j`, `j` with the return at
`j`, `0` at either terminal.  It is a function of the phase alone: an
arbitrary amount of interior garbage carries no debt. -/
def sanDebt (S : SanFrame) : SanPhase → Nat
  | .fwd j => 2 * S.h - 1 - j
  | .back _ j => j
  | .done _ => 0

@[simp] theorem sanDebt_fwd (S : SanFrame) (j : Nat) : sanDebt S (.fwd j) = 2 * S.h - 1 - j := rfl
@[simp] theorem sanDebt_back (S : SanFrame) (r : Ret) (j : Nat) : sanDebt S (.back r j) = j := rfl
@[simp] theorem sanDebt_done (S : SanFrame) (r : Ret) : sanDebt S (.done r) = 0 := rfl

theorem sanDebt_next_le (S : SanFrame) (l : TargetSan) (p : SanPhase) (hp : PhaseOkS S p)
    (e : Nat) (he : e < S.h) : sanDebt S (nextP S l p e) ≤ sanDebt S p := by
  cases p with
  | fwd j =>
      have hj : j < S.h := hp
      rw [nextP_fwd]
      by_cases hej : e = j
      · rw [if_pos hej]
        by_cases hlast : j + 1 = S.h
        · rw [if_pos hlast]
          by_cases h0 : j = 0
          · rw [if_pos h0]; exact Nat.zero_le _
          · rw [if_neg h0]; simp only [sanDebt_back, sanDebt_fwd]; omega
        · rw [if_neg hlast]; simp only [sanDebt_fwd]; omega
      · rw [if_neg hej]
        exact Nat.le_refl _
  | back r j =>
      have hj1 : 1 ≤ j := hp.1
      rw [nextP_back]
      by_cases hej : e + 1 = j
      · rw [if_pos hej]
        by_cases hj : j = 1
        · rw [if_pos hj]; exact Nat.zero_le _
        · rw [if_neg hj]; simp only [sanDebt_back]; omega
      · rw [if_neg hej]
        exact Nat.le_refl _
  | done r =>
      rw [nextP_done]
      exact Nat.le_refl _

theorem sanDebt_useful (S : SanFrame) (l : TargetSan) (p : SanPhase) (hp : PhaseOkS S p)
    (hpos : 0 < sanDebt S p) :
    ∃ e, e < S.h ∧ sanDebt S (nextP S l p e) + 1 = sanDebt S p := by
  cases p with
  | fwd j =>
      have hj : j < S.h := hp
      refine ⟨j, hj, ?_⟩
      rw [nextP_fwd, if_pos rfl]
      by_cases hlast : j + 1 = S.h
      · rw [if_pos hlast]
        by_cases h0 : j = 0
        · rw [if_pos h0]
          simp only [sanDebt_done, sanDebt_fwd]
          omega
        · rw [if_neg h0]
          simp only [sanDebt_back, sanDebt_fwd]
          omega
      · rw [if_neg hlast]
        simp only [sanDebt_fwd]
        omega
  | back r j =>
      have hj1 : 1 ≤ j := hp.1
      have hj2 : j < S.h := hp.2
      refine ⟨j - 1, by omega, ?_⟩
      rw [nextP_back, if_pos (by omega : j - 1 + 1 = j)]
      by_cases hj : j = 1
      · rw [if_pos hj]
        simp only [sanDebt_done, sanDebt_back]
        omega
      · rw [if_neg hj]
        simp only [sanDebt_back]
        omega
  | done r => exact absurd hpos (by simp)

/-! ## The stopped process and its scale-one Bellman supersolution -/

def ActiveSweep (S : SanFrame) : Type := {s : SweepState S // 0 < sanDebt S s.phase}

noncomputable def sweepNode {n : Nat} (S : SanFrame) (E : SanEmbedding S n) :
    ActiveSweep S → Fin n → StopNode (ActiveSweep S) :=
  fun s e =>
    if hp : 0 < sanDebt S (sweepSched S E s.1 e).phase then
      .active ⟨sweepSched S E s.1 e, hp⟩
    else .success

def sweepPotential {n : Nat} (S : SanFrame) : StopNode (ActiveSweep S) → Nat
  | .active s => n * sanDebt S s.1.phase
  | .success => 0
  | .failure => 0

/-- The sweep never exposes a failure outcome. -/
theorem sanitize_no_failure {n : Nat} (S : SanFrame) (E : SanEmbedding S n) :
    ∀ (s : ActiveSweep S) (e : Fin n), sweepNode S E s e ≠ .failure := by
  intro s e
  simp only [sweepNode]
  split <;> simp

theorem sweep_debt_step_le {n : Nat} (S : SanFrame) (E : SanEmbedding S n)
    (s : SweepState S) (e : Fin n) :
    sanDebt S (sweepSched S E s e).phase ≤ sanDebt S s.phase := by
  rcases sweepSched_cases S E s e with h | ⟨a, h⟩
  · rw [h]
    exact Nat.le_refl _
  · rw [h]
    exact sanDebt_next_le S s.lease s.phase s.hp a.val a.isLt

theorem sweep_debt_useful {n : Nat} (S : SanFrame) (E : SanEmbedding S n)
    (s : SweepState S) (hpos : 0 < sanDebt S s.phase) :
    ∃ e : Fin n, sanDebt S (sweepSched S E s e).phase + 1 = sanDebt S s.phase := by
  obtain ⟨e0, he0, hd⟩ := sanDebt_useful S s.lease s.phase s.hp hpos
  refine ⟨E.edgeAt ⟨e0, he0⟩, ?_⟩
  rw [sweepSched_eq]
  exact hd

theorem sweep_childSum {n : Nat} (S : SanFrame) (E : SanEmbedding S n)
    (s : SweepState S) (hpos : 0 < sanDebt S s.phase) :
    1 + (List.ofFn (fun e : Fin n => sanDebt S (sweepSched S E s e).phase)).sum
      ≤ n * sanDebt S s.phase := by
  obtain ⟨e0, he0⟩ := sweep_debt_useful S E s hpos
  have hlt := ofFn_sum_lt_of_single_lt
    (fun e : Fin n => sanDebt S (sweepSched S E s e).phase)
    (fun _ : Fin n => sanDebt S s.phase) e0
    (fun e => sweep_debt_step_le S E s e)
    (by omega)
  rw [ofFn_sum_const] at hlt
  omega

private theorem sweepPotential_sweepNode {n : Nat} (S : SanFrame) (E : SanEmbedding S n)
    (s : ActiveSweep S) (e : Fin n) :
    sweepPotential (n := n) S (sweepNode S E s e) = n * sanDebt S (sweepSched S E s.1 e).phase := by
  simp only [sweepNode]
  split
  · rfl
  · rename_i hne
    have hz : sanDebt S (sweepSched S E s.1 e).phase = 0 := by omega
    simp [sweepPotential, hz]

/-- Scale one on the physical `n`-edge scheduler: one useful firing per active
interaction, potential `n * debt`, from ANY interior content. -/
theorem sanitize_bellman {n : Nat} (S : SanFrame) (E : SanEmbedding S n) :
    NatBellmanSuperSolution (sweepNode S E) 1 (sweepPotential (n := n) S) := by
  refine ⟨rfl, rfl, ?_⟩
  intro s
  have hdebt := sweep_childSum S E s.1 s.2
  have hscaled := Nat.mul_le_mul_left n hdebt
  have hchildren :
      (List.ofFn (fun e : Fin n => sweepPotential (n := n) S (sweepNode S E s e))).sum
        = n * (List.ofFn (fun e : Fin n => sanDebt S (sweepSched S E s.1 e).phase)).sum := by
    rw [← ofFn_sum_mul_left]
    exact ofFn_sum_eq _ _ (fun e => sweepPotential_sweepNode S E s e)
  calc
    1 * n + (List.ofFn (fun e : Fin n => sweepPotential (n := n) S (sweepNode S E s e))).sum
        = n * (1 + (List.ofFn (fun e : Fin n =>
            sanDebt S (sweepSched S E s.1 e).phase)).sum) := by
          rw [hchildren, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    _ ≤ n * (n * sanDebt S s.1.phase) := hscaled
    _ = n * sweepPotential (n := n) S (.active s) := rfl

/-! ## Launch, runs, and the capstones -/

def sweepStart (S : SanFrame) (g : Nat → SNode) (hg : GarbageOk S g) : SweepState S :=
  ⟨g, .fwd 0, S.lease0, hg, S.hpos, Or.inl rfl⟩

def sweepStartActive (S : SanFrame) (g : Nat → SNode) (hg : GarbageOk S g) : ActiveSweep S :=
  ⟨sweepStart S g hg, by
    show 0 < 2 * S.h - 1 - 0
    have := S.hpos
    omega⟩

/-- The launch potential is exactly `n * (2h - 1)`, independently of how much
garbage the interior holds. -/
theorem sanitize_start_le {n : Nat} (S : SanFrame) (g : Nat → SNode) (hg : GarbageOk S g) :
    sweepPotential (n := n) S (.active (sweepStartActive S g hg)) = n * (2 * S.h - 1) ∧
    sweepPotential (n := n) S (.active (sweepStartActive S g hg)) ≤ n * (2 * S.h - 1) := by
  have h : sweepPotential (n := n) S (.active (sweepStartActive S g hg)) = n * (2 * S.h - 1) := by
    show n * (2 * S.h - 1 - 0) = n * (2 * S.h - 1)
    rfl
  exact ⟨h, Nat.le_of_eq h⟩

noncomputable def runWord {n : Nat} (S : SanFrame) (E : SanEmbedding S n)
    (s : SweepState S) : List (Fin n) → SweepState S
  | [] => s
  | e :: w => runWord S E (sweepSched S E s e) w

theorem phase_of_ready {p : SanPhase} (h : ownerCtl p = OwnerSan.ready) : p = .done .ack := by
  cases p with
  | fwd j =>
      cases j with
      | zero => exact absurd h (by simp [ownerCtl])
      | succ m => exact absurd h (by simp [ownerCtl])
  | back r j => exact absurd h (by simp [ownerCtl])
  | done r =>
      cases r with
      | ack => rfl
      | rej => exact absurd h (by simp [ownerCtl])

/-- **`sanitize_erases`.**  Whenever the owner shows `CaptureReady`, every
interior slot of the gap is the canonical empty slot: no selection payload, no
capture payload, no forged sanitizer symbol survives. -/
theorem sanitize_erases_state (S : SanFrame) (s : SweepState S)
    (hready : (sweepCfg S s (sanLeftPos S)).owner = OwnerSan.ready)
    (k : Fin (S.h + 1)) (h0 : 0 < k.val) (hh : k.val < S.h) :
    sweepCfg S s k = slotOf .empty := by
  have hp : s.phase = .done .ack := phase_of_ready hready
  show sanSite S s.garbage s.phase s.lease k.val = _
  rw [hp, sanSite_interior_done S s.garbage .ack s.lease k.val (by omega) (by omega)]

theorem sanitize_erases {n : Nat} (S : SanFrame) (E : SanEmbedding S n) (g : Nat → SNode)
    (hg : GarbageOk S g) (w : List (Fin n))
    (hready : (sweepCfg S (runWord S E (sweepStart S g hg) w) (sanLeftPos S)).owner
      = OwnerSan.ready)
    (k : Fin (S.h + 1)) (h0 : 0 < k.val) (hh : k.val < S.h) :
    sweepCfg S (runWord S E (sweepStart S g hg) w) k = slotOf .empty :=
  sanitize_erases_state S _ hready k h0 hh

/-- **Empty prefix.**  With the head at `j`, every interior position strictly
left of the head is empty.  This is the fact the design answer assumes; it is
here a consequence of the launch row plus `lane_step`. -/
theorem head_empty_prefix (S : SanFrame) (s : SweepState S) (j : Nat) (hj : s.phase = .fwd j)
    (k : Fin (S.h + 1)) (h0 : 0 < k.val) (hlt : k.val < j) : sweepCfg S s k = slotOf .empty := by
  have hph : PhaseOkS S s.phase := s.hp
  rw [hj] at hph
  have hh : k.val < S.h := by
    have : j < S.h := hph
    omega
  show sanSite S s.garbage s.phase s.lease k.val = _
  rw [hj, sanSite_interior_fwd S s.garbage j s.lease k.val (by omega) (by omega),
    if_neg (by omega : ¬ (k.val = j)), if_neg (by omega : ¬ (j < k.val))]

/-- **No premature deposit.**  A `waitSan` owner can only see a return symbol
at its own interior neighbour when the sweep is genuinely in the `back _ 1`
phase.  A forged `A` or `R` never reaches the owner ahead of the real one. -/
theorem no_premature_deposit (S : SanFrame) (s : SweepState S) (hS : 1 < S.h)
    (hw : (sweepCfg S s (sanLeftPos S)).owner = OwnerSan.waitSan)
    (hret : isAckSym (sweepCfg S s ⟨1, by omega⟩).carrier = true ∨
            isRejSym (sweepCfg S s ⟨1, by omega⟩).carrier = true) :
    ∃ r, s.phase = .back r 1 := by
  have hcfg : sweepCfg S s ⟨1, by omega⟩ = interiorSite s.garbage s.phase 1 :=
    sanSite_mid S s.garbage s.phase s.lease 1 (by omega) (by omega)
  have hw' : ownerCtl s.phase = OwnerSan.waitSan := hw
  rw [hcfg] at hret
  cases hp : s.phase with
  | fwd j =>
      exfalso
      rw [hp] at hw' hret
      cases j with
      | zero => exact absurd hw' (by simp [ownerCtl])
      | succ m =>
          have : interiorSite s.garbage (.fwd (m + 1)) 1 =
              if (1 : Nat) = m + 1 then slotOf .sweep
                else if m + 1 < 1 then s.garbage 1 else slotOf .empty := rfl
          rw [this] at hret
          by_cases hm : (1 : Nat) = m + 1
          · rw [if_pos hm] at hret
            rcases hret with h | h <;> exact absurd h (by simp)
          · rw [if_neg hm, if_neg (by omega : ¬ (m + 1 < 1))] at hret
            rcases hret with h | h <;> exact absurd h (by simp)
  | back r j =>
      rw [hp] at hret
      have hi : interiorSite s.garbage (.back r j) 1 =
          if (1 : Nat) = j then slotOf (retSym r) else slotOf .empty := rfl
      rw [hi] at hret
      by_cases hm : (1 : Nat) = j
      · exact ⟨r, by rw [← hm]⟩
      · exfalso
        rw [if_neg hm] at hret
        rcases hret with h | h <;> exact absurd h (by simp)
  | done r =>
      exfalso
      rw [hp] at hw'
      cases r <;> exact absurd hw' (by simp [ownerCtl])

/-! ### An invalid target can never produce readiness -/

def SweepInvalid (S : SanFrame) : Prop := targetOk (targetSite S S.lease0) = false

def NoAckPhase : SanPhase → Prop
  | .fwd _ => True
  | .back .ack _ => False
  | .back .rej _ => True
  | .done .ack => False
  | .done .rej => True

theorem retOf_rej (S : SanFrame) (l : TargetSan) (hl : LeaseStep S l) (hinv : SweepInvalid S) :
    retOf S l = Ret.rej := by
  have h : targetOk (targetSite S S.lease0) = false := hinv
  rw [retOf_lease_invariant S l hl]
  simp [retOf, h]

theorem noAck_advance (S : SanFrame) (s : SweepState S) (hinv : SweepInvalid S)
    (hno : NoAckPhase s.phase) (j : Fin S.h) : NoAckPhase (sweepAdvance S s j).phase := by
  have hr : retOf S s.lease = Ret.rej := retOf_rej S s.lease s.hl hinv
  show NoAckPhase (nextP S s.lease s.phase j.val)
  cases hp : s.phase with
  | fwd i =>
      rw [nextP_fwd, hr]
      by_cases hej : j.val = i
      · rw [if_pos hej]
        by_cases hlast : i + 1 = S.h
        · rw [if_pos hlast]
          by_cases h0 : i = 0
          · rw [if_pos h0]; trivial
          · rw [if_neg h0]; trivial
        · rw [if_neg hlast]; trivial
      · rw [if_neg hej]; trivial
  | back r i =>
      rw [hp] at hno
      cases r with
      | ack => exact absurd hno (fun h => h)
      | rej =>
          rw [nextP_back]
          by_cases hej : j.val + 1 = i
          · rw [if_pos hej]
            by_cases hi : i = 1
            · rw [if_pos hi]; trivial
            · rw [if_neg hi]; trivial
          · rw [if_neg hej]; trivial
  | done r =>
      rw [hp] at hno
      cases r with
      | ack => exact absurd hno (fun h => h)
      | rej => rw [nextP_done]; trivial

theorem noAck_sched {n : Nat} (S : SanFrame) (E : SanEmbedding S n) (s : SweepState S)
    (hinv : SweepInvalid S) (hno : NoAckPhase s.phase) (e : Fin n) :
    NoAckPhase (sweepSched S E s e).phase := by
  rcases sweepSched_cases S E s e with h | ⟨a, h⟩
  · rw [h]; exact hno
  · rw [h]; exact noAck_advance S s hinv hno a

theorem noAck_run {n : Nat} (S : SanFrame) (E : SanEmbedding S n) (w : List (Fin n)) :
    ∀ (s : SweepState S), SweepInvalid S → NoAckPhase s.phase →
      NoAckPhase (runWord S E s w).phase := by
  induction w with
  | nil => intro s _ hno; exact hno
  | cons e w ih =>
      intro s hinv hno
      exact ih (sweepSched S E s e) hinv (noAck_sched S E s hinv hno e)

/-- **`reject_downgrades_forged_owner`, run level.**  If the target fails `V`
at lease entry, no schedule ever puts the owner into `CaptureReady`: the sweep
can only terminate in the downgraded `home`/`toSend` state. -/
theorem invalid_never_ready {n : Nat} (S : SanFrame) (E : SanEmbedding S n) (g : Nat → SNode)
    (hg : GarbageOk S g) (hinv : SweepInvalid S) (w : List (Fin n)) :
    (sweepCfg S (runWord S E (sweepStart S g hg) w) (sanLeftPos S)).owner ≠ OwnerSan.ready := by
  intro hbad
  have hno := noAck_run S E w (sweepStart S g hg) hinv trivial
  rw [phase_of_ready hbad] at hno
  exact hno

/-- A terminal downgraded owner really is `home`/`toSend` and not `heldDenial`. -/
theorem downgraded_owner_ports (S : SanFrame) (s : SweepState S) (hd : s.phase = .done .rej) :
    (sweepCfg S s (sanLeftPos S)).raw.cwPort = some CwPort.toSend ∧
    (sweepCfg S s (sanLeftPos S)).raw.cwPort ≠ some CwPort.heldDenial ∧
    choiceOf (sweepCfg S s (sanLeftPos S)).raw = choiceOf S.ownerRaw ∧
    (sweepCfg S s (sanLeftPos S)).raw.ccwPort = S.ownerRaw.ccwPort ∧
    (sweepCfg S s (sanLeftPos S)).owner ≠ OwnerSan.ready := by
  have hcfg : sweepCfg S s (sanLeftPos S) = ownerSite S (.done .rej) := by
    show sanSite S s.garbage s.phase s.lease 0 = _
    rw [sanSite_zero, hd]
  have hraw : (ownerSite S (.done .rej)).raw = downRaw S.ownerRaw := rfl
  have hslot : rawSlot S.ownerRaw = false := rawSlot_of_rawOwner S.hOwner
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcfg, hraw]; exact downRaw_cwPort hslot
  · rw [hcfg, hraw, downRaw_cwPort hslot]; intro hbad; cases hbad
  · rw [hcfg, hraw]; exact downRaw_choice S.ownerRaw
  · rw [hcfg, hraw]; exact downRaw_ccwPort S.ownerRaw
  · rw [hcfg]; intro hbad; cases hbad

/-! ### Idempotence -/

theorem nextL_done (S : SanFrame) (g : Nat → SNode) (r : Ret) (l : TargetSan) (e : Nat)
    (he : e < S.h) : nextL S g (.done r) l e = l := by
  by_cases hlast : e + 1 = S.h
  · rw [nextL_of_eq S g (.done r) l e he hlast, rowAt_done S g r l e he,
      show sanSite S g (.done r) l (e + 1) = targetSite S l by rw [hlast, sanSite_last]]
    rfl
  · exact nextL_of_ne S g (.done r) l e he hlast

theorem done_advance_cfg (S : SanFrame) (s : SweepState S) (r : Ret) (hd : s.phase = .done r)
    (j : Fin S.h) : sweepCfg S (sweepAdvance S s j) = sweepCfg S s := by
  show sanConfigOf S (nextG S s.garbage s.phase s.lease j.val)
      (nextP S s.lease s.phase j.val) (nextL S s.garbage s.phase s.lease j.val)
    = sanConfigOf S s.garbage s.phase s.lease
  rw [hd, nextP_done, nextL_done S s.garbage r s.lease j.val j.isLt]
  funext k
  show sanSite S _ (.done r) s.lease k.val = sanSite S s.garbage (.done r) s.lease k.val
  by_cases h0 : k.val = 0
  · rw [h0, sanSite_zero, sanSite_zero]
  · by_cases hh : k.val = S.h
    · rw [hh, sanSite_last, sanSite_last]
    · rw [sanSite_mid S _ (.done r) s.lease k.val h0 hh,
        sanSite_mid S s.garbage (.done r) s.lease k.val h0 hh]
      rfl

theorem done_sched_cfg {n : Nat} (S : SanFrame) (E : SanEmbedding S n) (s : SweepState S)
    (r : Ret) (hd : s.phase = .done r) (e : Fin n) :
    sweepCfg S (sweepSched S E s e) = sweepCfg S s ∧ (sweepSched S E s e).phase = .done r := by
  rcases sweepSched_cases S E s e with h | ⟨a, h⟩
  · rw [h]; exact ⟨rfl, hd⟩
  · rw [h]
    refine ⟨done_advance_cfg S s r hd a, ?_⟩
    show nextP S s.lease s.phase a.val = .done r
    rw [hd, nextP_done]

/-- **`sanitize_idempotent`.**  A completed sweep is stationary: an explicitly
requested repeat over any finite schedule returns the same empty interior and
the same framed endpoints.  Completed sweeps are never restarted. -/
theorem sanitize_idempotent {n : Nat} (S : SanFrame) (E : SanEmbedding S n) (w : List (Fin n)) :
    ∀ (s : SweepState S) (r : Ret), s.phase = .done r →
      sweepCfg S (runWord S E s w) = sweepCfg S s ∧ (runWord S E s w).phase = .done r := by
  induction w with
  | nil => intro s r hd; exact ⟨rfl, hd⟩
  | cons e w ih =>
      intro s r hd
      obtain ⟨hc, hp⟩ := done_sched_cfg S E s r hd e
      obtain ⟨hc2, hp2⟩ := ih (sweepSched S E s e) r hp
      exact ⟨by
        show sweepCfg S (runWord S E (sweepSched S E s e) w) = sweepCfg S s
        rw [hc2, hc], hp2⟩

/-! ### Port framing -/

/-- **`sanitize_frames_ports`.**  *Every* sweep row -- successful or rejecting
-- leaves both roots' frozen choices, both incoming candidate ports and both
leader bits exactly as they were, and leaves the right root's raw node
untouched altogether.  On a successful row the left root's raw node, hence all
four selection ports, is untouched as well; the rejection row is the only
writer there, and `reject_downgrades_forged_owner` pins what it writes
(`cwPort := toSend`, `outgoing := home`, never `heldDenial`).  The
unconditional half is what the capture interface needs: no sweep outcome can
retarget a root or forge a candidate port. -/
theorem sanitize_frames_ports (S : SanFrame) (cfg : SanConfig S) (j : Fin S.h)
    (hleft : isSlot (cfg (sanLeftPos S)) = false)
    (hright : isSlot (cfg (sanRightPos S)) = false) :
    choiceOf (sanGapStep S cfg j (sanLeftPos S)).raw = choiceOf (cfg (sanLeftPos S)).raw ∧
    choiceOf (sanGapStep S cfg j (sanRightPos S)).raw = choiceOf (cfg (sanRightPos S)).raw ∧
    (sanGapStep S cfg j (sanLeftPos S)).raw.ccwPort = (cfg (sanLeftPos S)).raw.ccwPort ∧
    (sanGapStep S cfg j (sanRightPos S)).raw.ccwPort = (cfg (sanRightPos S)).raw.ccwPort ∧
    (sanGapStep S cfg j (sanLeftPos S)).leader = (cfg (sanLeftPos S)).leader ∧
    (sanGapStep S cfg j (sanRightPos S)).leader = (cfg (sanRightPos S)).leader ∧
    (sanGapStep S cfg j (sanRightPos S)).raw = (cfg (sanRightPos S)).raw ∧
    (sanGapStep S cfg j (sanRightPos S)).raw.cwPort = (cfg (sanRightPos S)).raw.cwPort ∧
    (successfulB (sanRule (cfg (sanLeftEnd S j)) (cfg (sanRightEnd S j))) = true →
      (sanGapStep S cfg j (sanLeftPos S)).raw = (cfg (sanLeftPos S)).raw ∧
      (sanGapStep S cfg j (sanLeftPos S)).raw.cwPort = (cfg (sanLeftPos S)).raw.cwPort) := by
  have hj : j.val < S.h := j.isLt
  have hLcase : sanGapStep S cfg j (sanLeftPos S) = cfg (sanLeftPos S) ∨
      (sanLeftEnd S j = sanLeftPos S ∧ sanGapStep S cfg j (sanLeftPos S)
        = (sanRow (cfg (sanLeftEnd S j)) (cfg (sanRightEnd S j))).1) := by
    by_cases h0 : j.val = 0
    · refine Or.inr ⟨Fin.ext h0, ?_⟩
      show (if (0 : Nat) = j.val then
        (sanRow (cfg (sanLeftEnd S j)) (cfg (sanRightEnd S j))).1 else _) = _
      rw [if_pos h0.symm]
    · exact Or.inl (sanGapStep_frame S cfg j (sanLeftPos S)
        (by show (0 : Nat) ≠ j.val; omega) (by show (0 : Nat) ≠ j.val + 1; omega))
  have hRcase : sanGapStep S cfg j (sanRightPos S) = cfg (sanRightPos S) ∨
      (sanRightEnd S j = sanRightPos S ∧ sanGapStep S cfg j (sanRightPos S)
        = (sanRow (cfg (sanLeftEnd S j)) (cfg (sanRightEnd S j))).2) := by
    by_cases h1 : S.h = j.val + 1
    · refine Or.inr ⟨Fin.ext h1.symm, ?_⟩
      show (if S.h = j.val then _ else if S.h = j.val + 1 then
        (sanRow (cfg (sanLeftEnd S j)) (cfg (sanRightEnd S j))).2 else _) = _
      rw [if_neg (by omega : ¬ (S.h = j.val)), if_pos h1]
    · exact Or.inl (sanGapStep_frame S cfg j (sanRightPos S)
        (by show S.h ≠ j.val; omega) (by show S.h ≠ j.val + 1; omega))
  have hR : (sanGapStep S cfg j (sanRightPos S)).raw = (cfg (sanRightPos S)).raw ∧
      (sanGapStep S cfg j (sanRightPos S)).leader = (cfg (sanRightPos S)).leader := by
    rcases hRcase with h | ⟨hreq, hstep⟩
    · rw [h]; exact ⟨rfl, rfl⟩
    · rw [hstep, hreq]; exact sanRow_right_raw _ _ hright
  have hL : choiceOf (sanGapStep S cfg j (sanLeftPos S)).raw
        = choiceOf (cfg (sanLeftPos S)).raw ∧
      (sanGapStep S cfg j (sanLeftPos S)).raw.ccwPort = (cfg (sanLeftPos S)).raw.ccwPort ∧
      (sanGapStep S cfg j (sanLeftPos S)).leader = (cfg (sanLeftPos S)).leader := by
    rcases hLcase with h | ⟨hleq, hstep⟩
    · rw [h]; exact ⟨rfl, rfl, rfl⟩
    · rw [hstep, hleq]; exact sanRow_left_choice_frame _ _ hleft
  refine ⟨hL.1, by rw [hR.1], hL.2.1, by rw [hR.1], hL.2.2, hR.2, hR.1, by rw [hR.1], ?_⟩
  intro hs
  rcases hLcase with h | ⟨hleq, hstep⟩
  · rw [h]; exact ⟨rfl, rfl⟩
  · rw [hleq] at hs
    rw [hstep, hleq]
    have hraw := (sanRow_left_owner_frame _ _ hleft hs).1
    exact ⟨hraw, by rw [hraw]⟩

/-! ## The sanitizer obligations, discharged rather than assumed

`SanitizeLaws` is stated as requested, but it is a *derived* bundle: the
instance below is proved from the literal table of this file, so nothing in
this development rests on an unproved dispatcher assumption. -/
structure SanitizeLaws (S : SanFrame) : Prop where
  /-- Barrier: the head's prefix is empty, so no return can be left of it. -/
  barrier : ∀ (g : Nat → SNode) (j m : Nat), 0 < m → m < j →
    interiorSite g (.fwd j) m = slotOf .empty
  /-- Collision priority: the forward row wins `S | A` and `S | R`. -/
  priority : ∀ s : SanSym, sanRow (slotOf .sweep) (slotOf s) = (slotOf .empty, slotOf .sweep)
  /-- No endpoint reinjection: at a root right endpoint only the lease moves. -/
  injection : ∀ a b : SNode, isSlot b = false →
    (sanRow a b).2 = b ∨ (sanRow a b).2 = armTarget b
  /-- Lease discipline: `reservedAck` is only ever installed on a real lease. -/
  lease : ∀ (g : Nat → SNode) (p : SanPhase) (l : TargetSan) (e : Nat),
    LeaseStep S l → e < S.h → LeaseStep S (nextL S g p l e)
  /-- Framing: no row changes a root's leader bit. -/
  framing : ∀ a b : SNode, isSlot a = false → isSlot b = false →
    (sanRow a b).1.leader = a.leader ∧ (sanRow a b).2.leader = b.leader

theorem sanitizeLaws_holds (S : SanFrame) : SanitizeLaws S where
  barrier := by
    intro g j m h0 hm
    show (if m = j then slotOf .sweep else if j < m then g m else slotOf .empty) = slotOf .empty
    rw [if_neg (by omega : ¬ (m = j)), if_neg (by omega : ¬ (j < m))]
  priority := forward_wins_collision
  injection := sanRow_right_frame
  lease := fun g p l e hl he => leaseStep_next S g p l hl e he
  framing := sanRow_leader_frame

/-! ## A worked positive instance and two counterexamples -/

def exOwnerRaw : Node := .root .out1 .heldCandidate .free .home .reserved
def exTargetRaw : Node := .root .in0 .toSend .heldCandidate .home .reserved

/-- `h = 2`, a valid leased target. -/
def exFrame : SanFrame where
  h := 2
  hpos := by decide
  ownerRaw := exOwnerRaw
  hOwner := rfl
  ownerLive := true
  targetRaw := exTargetRaw
  hTargetRoot := rfl
  targetLive := true
  lease0 := .reservedSan

/-- The single interior slot carries a live capture proposal payload *and* a
forged sanitizer acknowledgement: exactly the residue warned about above. -/
def exGarbage : Nat → SNode := fun _ =>
  ⟨.interior (.capture .proposal), false, .idle, .unleased, .ack⟩

theorem exGarbage_ok : GarbageOk exFrame exGarbage := by
  intro k h0 hh
  rfl

/-- The forged `A` is destroyed by the launch row, the head reaches the target,
the target is acknowledged, and the owner becomes `CaptureReady` with an empty
interior.  Three real gap firings, matching `debt = 2h-1 = 3`. -/
theorem example_sanitizes_forged_interior :
    (sweepAdvance exFrame (sweepStart exFrame exGarbage exGarbage_ok) ⟨0, by decide⟩).phase
        = .fwd 1 ∧
    (sweepAdvance exFrame (sweepAdvance exFrame
        (sweepStart exFrame exGarbage exGarbage_ok) ⟨0, by decide⟩) ⟨1, by decide⟩).phase
        = .back .ack 1 ∧
    (sweepAdvance exFrame (sweepAdvance exFrame (sweepAdvance exFrame
        (sweepStart exFrame exGarbage exGarbage_ok) ⟨0, by decide⟩) ⟨1, by decide⟩)
        ⟨0, by decide⟩).phase = .done .ack ∧
    (sweepAdvance exFrame (sweepAdvance exFrame (sweepAdvance exFrame
        (sweepStart exFrame exGarbage exGarbage_ok) ⟨0, by decide⟩) ⟨1, by decide⟩)
        ⟨0, by decide⟩).lease = TargetSan.reservedAck ∧
    sweepCfg exFrame (sweepAdvance exFrame (sweepAdvance exFrame (sweepAdvance exFrame
        (sweepStart exFrame exGarbage exGarbage_ok) ⟨0, by decide⟩) ⟨1, by decide⟩)
        ⟨0, by decide⟩) ⟨1, by decide⟩ = slotOf .empty ∧
    (sweepCfg exFrame (sweepAdvance exFrame (sweepAdvance exFrame (sweepAdvance exFrame
        (sweepStart exFrame exGarbage exGarbage_ok) ⟨0, by decide⟩) ⟨1, by decide⟩)
        ⟨0, by decide⟩) (sanLeftPos exFrame)).owner = OwnerSan.ready :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The debts really are `3, 2, 1, 0`. -/
theorem example_debt_descends :
    sanDebt exFrame (sweepStart exFrame exGarbage exGarbage_ok).phase = 3 ∧
    sanDebt exFrame (sweepAdvance exFrame
      (sweepStart exFrame exGarbage exGarbage_ok) ⟨0, by decide⟩).phase = 2 ∧
    sanDebt exFrame (sweepAdvance exFrame (sweepAdvance exFrame
      (sweepStart exFrame exGarbage exGarbage_ok) ⟨0, by decide⟩) ⟨1, by decide⟩).phase = 1 ∧
    sanDebt exFrame (sweepAdvance exFrame (sweepAdvance exFrame (sweepAdvance exFrame
      (sweepStart exFrame exGarbage exGarbage_ok) ⟨0, by decide⟩) ⟨1, by decide⟩)
      ⟨0, by decide⟩).phase = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The naive table, in which the backward row is tested before the forward
row.  It is total and radius one, and it differs from `sanRow` on exactly the
`S | A` and `S | R` collisions. -/
def naiveRow (a b : SNode) : SNode × SNode :=
  if isSlot a && isSlot b && isAckSym b.carrier then (slotOf .ack, slotOf .empty)
  else if isSlot a && isSlot b && isRejSym b.carrier then (slotOf .rejected, slotOf .empty)
  else sanRow a b

/-- **Counterexample 1: the collision priority is load bearing.**  Under the
naive table the forged `A` crosses the head and continues towards the owner;
under `sanRow` the head erases it and advances. -/
theorem forward_priority_is_load_bearing :
    sanRow (slotOf .sweep) (slotOf .ack) = (slotOf .empty, slotOf .sweep) ∧
    naiveRow (slotOf .sweep) (slotOf .ack) = (slotOf .ack, slotOf .empty) ∧
    sanRow (slotOf .sweep) (slotOf .rejected) = (slotOf .empty, slotOf .sweep) ∧
    naiveRow (slotOf .sweep) (slotOf .rejected) = (slotOf .rejected, slotOf .empty) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A frame whose target fails `V`: no leader bit and no exclusive reservation. -/
def forgedFrame : SanFrame :=
  { exFrame with targetLive := false, lease0 := .unleased }

theorem forgedFrame_invalid : SweepInvalid forgedFrame := rfl

/-- **Counterexample 2: the empty prefix is load bearing.**  The deposit row
itself grants `CaptureReady` to any `waitSan` owner facing an `A`, even when
the target is invalid.  Local guards cannot exclude a forged `A`; only the lane
invariant does, and `invalid_never_ready` is the theorem that closes the hole. -/
theorem forged_ack_would_fake_readiness :
    targetOk (targetSite forgedFrame forgedFrame.lease0) = false ∧
    (sanRow (ownerSite forgedFrame (.back .ack 1)) (slotOf .ack)).1.owner = OwnerSan.ready :=
  ⟨rfl, rfl⟩

/-- The lane closes that hole: with an invalid target no schedule at all can
reach readiness, whatever the interior residue is. -/
theorem forgedFrame_never_ready {n : Nat} (E : SanEmbedding forgedFrame n)
    (g : Nat → SNode) (hg : GarbageOk forgedFrame g) (w : List (Fin n)) :
    (sweepCfg forgedFrame (runWord forgedFrame E (sweepStart forgedFrame g hg) w)
      (sanLeftPos forgedFrame)).owner ≠ OwnerSan.ready :=
  invalid_never_ready forgedFrame E g hg forgedFrame_invalid w

/-- `h = 1`: launch, reservation check and readiness are a single atomic
root/root row, and the rejection alternative downgrades instead. -/
def exFrame1 : SanFrame := { exFrame with h := 1, hpos := by decide }
def forgedFrame1 : SanFrame := { forgedFrame with h := 1, hpos := by decide }

theorem example_direct_row :
    (sweepAdvance exFrame1 (sweepStart exFrame1 exGarbage (fun _ _ _ => rfl))
        ⟨0, by decide⟩).phase = .done .ack ∧
    (sweepAdvance exFrame1 (sweepStart exFrame1 exGarbage (fun _ _ _ => rfl))
        ⟨0, by decide⟩).lease = TargetSan.reservedAck ∧
    (sweepAdvance forgedFrame1 (sweepStart forgedFrame1 exGarbage (fun _ _ _ => rfl))
        ⟨0, by decide⟩).phase = .done .rej :=
  ⟨rfl, rfl, rfl⟩

theorem example_direct_reject_downgrades :
    (sweepCfg forgedFrame1 (sweepAdvance forgedFrame1
      (sweepStart forgedFrame1 exGarbage (fun _ _ _ => rfl)) ⟨0, by decide⟩)
      (sanLeftPos forgedFrame1)).raw.cwPort = some CwPort.toSend ∧
    (sweepCfg forgedFrame1 (sweepAdvance forgedFrame1
      (sweepStart forgedFrame1 exGarbage (fun _ _ _ => rfl)) ⟨0, by decide⟩)
      (sanLeftPos forgedFrame1)).owner = OwnerSan.downgraded :=
  ⟨rfl, rfl⟩

#print axioms sanRow_spec
#print axioms sanitize_frames_ports
#print axioms sanitize_erases
#print axioms sanitize_bellman
#print axioms sanitize_no_failure
#print axioms sanitize_start_le
#print axioms reject_downgrades_forged_owner
#print axioms invalid_never_ready
#print axioms downgraded_owner_ports
#print axioms sanitize_idempotent
#print axioms lane_step
#print axioms head_empty_prefix
#print axioms no_premature_deposit
#print axioms forward_wins_collision
#print axioms sweepSched_cfg
#print axioms sanitizeLaws_holds
#print axioms example_sanitizes_forged_interior
#print axioms forward_priority_is_load_bearing
#print axioms forgedFrame_never_ready

end ShortGapSanitizerSweep
