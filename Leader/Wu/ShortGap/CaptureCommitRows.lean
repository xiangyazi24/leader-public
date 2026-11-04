import Leader.Wu.ShortGap.CaptureReservation

namespace ShortGapCaptureCommitRows

open ShortGapLiteralGapRows ShortGapLiteralRingRows ShortGapOwnerRoundSlice
open ShortGapCaptureReservation

set_option autoImplicit false

/-!
# Literal post-FINAL capture rows

New file: Leader/Wu/ShortGap/CaptureCommitRows.lean.

The imported Node has neither a leader bit nor post-FINAL controls/messages.
Consequently the executable signature is

  commitRow : CNode -> CNode -> CNode x CNode.

CNode wraps the original Node, without redefining any imported type. The
additional fields are a leader bit, an outgoing lifecycle, an incoming commit
lease/lifecycle, and a three-valued physical-slot carrier. They contain no
identifier, nonce, generation, shared mover, or unbounded data.

Important distinction: the imported TGT row consumes InControl.reserved and
writes InControl.accepted. Our distinct CommitIn.reserved is the *unconsumed
commit lease* installed by that very transition. COMMIT therefore tests BOTH
raw incoming = accepted AND extended incoming = reserved, as well as
heldCandidate and a live target. Testing raw incoming = reserved at COMMIT
would prevent every ordinary TGT/FINAL execution from committing.

Once a post-FINAL lifecycle is active, outgoing/incoming below are its
operational controls. The raw terminal codes finalReady/accepted are retained
as the imported capture-lane substate; cleanup does NOT reset them to
home/open. CaptureView prevents the old dispatcher from executing against a
postcommit overlay. A new generation/reset is deliberately not implemented.

The extra carrier occupies an otherwise empty interior slot. A non-none
carrier blocks the old capture lane on that pair. It is not ghost state.

The rule tag and RowStep certificate are observations/proofs, NOT node state.
Source acknowledgement and target cleanup are independent local services:
each uses its root as the left endpoint and frames the other endpoint. The
three-site theorem discharges_either_order gives both actual firing orders.
The h=1 direct row counts as a commit-at-target event in the flag theorem.

Frame scope: the legacy case is exactly the imported captureRow on raw Node,
with only monotone lifecycle observation added. Every new row preserves raw
Node entirely. The explicit write masks cover every field of the wrapper;
they do not purport to re-audit the imported row's internal selection proof.

These are local row safety results, not a global freshness, reachability,
fairness, selection-runtime composition, or completion-time theorem.
-/

inductive CommitCtl where
  | capturing | protectedFinal | committing | committedReceived | clean
  deriving DecidableEq

inductive CommitIn where
  | unreserved | reserved | committed | clean
  deriving DecidableEq

inductive CommitCarrier where
  | none | commit | committedBack
  deriving DecidableEq

structure CNode where
  raw : Node
  leader : Bool
  outgoing : CommitCtl
  incoming : CommitIn
  carrier : CommitCarrier
  deriving DecidableEq

def emptyRaw : Node := .interior (.selection .empty)

def rawFinal : Node -> Bool
  | .root _ _ _ .finalReady _ => true
  | _ => false

def rawReserved : Node -> Bool
  | .root _ _ _ _ .reserved => true
  | _ => false

def rawAccepted : Node -> Bool
  | .root _ _ _ _ .accepted => true
  | _ => false

def observeOut (old : CommitCtl) (new : Node) : CommitCtl :=
  match old with
  | .capturing => if rawFinal new = true then .protectedFinal else .capturing
  | _ => old

def observeIn (old : CommitIn) (before after : Node) : CommitIn :=
  match old with
  | .unreserved =>
      if rawReserved before = true ∧ rawAccepted after = true then
        .reserved
      else .unreserved
  | _ => old

def seedOut (n : Node) : CommitCtl := observeOut .capturing n

def seedIn (n : Node) : CommitIn :=
  if rawAccepted n = true then .reserved else .unreserved

/-- A snapshot embedding, not a runtime reset operation. -/
def embed (n : Node) (leader : Bool) : CNode :=
  ⟨n, leader, seedOut n, seedIn n, .none⟩

def projectPair (p : CNode × CNode) : Node × Node := (p.1.raw, p.2.raw)

/-- Observe an actual old-lane update without ever rearming a spent control. -/
def liftCapture (before : CNode) (after : Node) : CNode :=
  { before with
    raw := after
    outgoing := observeOut before.outgoing after
    incoming := observeIn before.incoming before.raw after }

def setOut (n : CNode) (v : CommitCtl) : CNode := { n with outgoing := v }
def setIn (n : CNode) (v : CommitIn) : CNode := { n with incoming := v }
def setCarrier (n : CNode) (v : CommitCarrier) : CNode := { n with carrier := v }

/-- The only primitive that clears a leader; the lease is consumed atomically. -/
def consumeCommit (n : CNode) : CNode :=
  { n with leader := false, incoming := .committed }

def rawOwner : Node -> Bool
  | .root .out1 .heldCandidate _ .finalReady _ => true
  | _ => false

def rawTarget : Node -> Bool
  | .root .in0 _ .heldCandidate _ .accepted => true
  | _ => false

abbrev Owner (n : CNode) : Prop := rawOwner n.raw = true ∧ n.carrier = .none
abbrev Target (n : CNode) : Prop := rawTarget n.raw = true ∧ n.carrier = .none
abbrev Empty (n : CNode) : Prop := n.raw = emptyRaw ∧ n.carrier = .none
abbrev CommitSlot (n : CNode) : Prop := n.raw = emptyRaw ∧ n.carrier = .commit
abbrev BackSlot (n : CNode) : Prop := n.raw = emptyRaw ∧ n.carrier = .committedBack

abbrev CaptureView (n : CNode) : Prop :=
  n.outgoing = seedOut n.raw ∧ n.incoming = seedIn n.raw

abbrev Legacy (a b : CNode) : Prop :=
  CaptureView a ∧ CaptureView b ∧ a.carrier = .none ∧ b.carrier = .none ∧
    captureRow a.raw b.raw ≠ (a.raw, b.raw)

abbrev SourceAck (a : CNode) : Prop :=
  Owner a ∧ a.outgoing = .committedReceived

abbrev TargetCleanup (a : CNode) : Prop :=
  Target a ∧ a.incoming = .committed ∧ a.leader = false

abbrev Launch (a b : CNode) : Prop :=
  Owner a ∧ a.outgoing = .protectedFinal ∧ Empty b

abbrev Forward (a b : CNode) : Prop := CommitSlot a ∧ Empty b

abbrev AtTarget (a b : CNode) : Prop :=
  CommitSlot a ∧ Target b ∧ b.incoming = .reserved ∧ b.leader = true

abbrev Backward (a b : CNode) : Prop := Empty a ∧ BackSlot b

abbrev Deposit (a b : CNode) : Prop :=
  Owner a ∧ a.outgoing = .committing ∧ BackSlot b

abbrev Direct (a b : CNode) : Prop :=
  Owner a ∧ a.outgoing = .protectedFinal ∧ Target b ∧
    b.incoming = .reserved ∧ b.leader = true

inductive Rule where
  | capture | commitLaunch | commitForward | commitAtTarget
  | committedBackward | committedDeposit | directCommit
  | sourceAck | targetCleanup | idle
  deriving DecidableEq

/-- An explicit specification of the pair updates, with their real guards. -/
inductive RowStep (a b : CNode) : Rule -> CNode -> CNode -> Prop where
  | capture (h : Legacy a b) :
      RowStep a b .capture
        (liftCapture a (captureRow a.raw b.raw).1)
        (liftCapture b (captureRow a.raw b.raw).2)
  | commitLaunch (h : Launch a b) :
      RowStep a b .commitLaunch
        (setOut a .committing) (setCarrier b .commit)
  | commitForward (h : Forward a b) :
      RowStep a b .commitForward
        (setCarrier a .none) (setCarrier b .commit)
  | commitAtTarget (h : AtTarget a b) :
      RowStep a b .commitAtTarget
        (setCarrier a .committedBack) (consumeCommit b)
  | committedBackward (h : Backward a b) :
      RowStep a b .committedBackward
        (setCarrier a .committedBack) (setCarrier b .none)
  | committedDeposit (h : Deposit a b) :
      RowStep a b .committedDeposit
        (setOut a .committedReceived) (setCarrier b .none)
  | directCommit (h : Direct a b) :
      RowStep a b .directCommit
        (setOut a .committedReceived) (consumeCommit b)
  | sourceAck (h : SourceAck a) :
      RowStep a b .sourceAck (setOut a .clean) b
  | targetCleanup (h : TargetCleanup a) :
      RowStep a b .targetCleanup (setIn a .clean) b
  | idle : RowStep a b .idle a b

structure Result (a b : CNode) where
  rule : Rule
  left : CNode
  right : CNode
  valid : RowStep a b rule left right

/-- Total, deterministic, radius-one dispatch; certificates erase at runtime. -/
def run (a b : CNode) : Result a b :=
  if h : SourceAck a then
    ⟨.sourceAck, setOut a .clean, b, .sourceAck h⟩
  else if h : TargetCleanup a then
    ⟨.targetCleanup, setIn a .clean, b, .targetCleanup h⟩
  else if h : Legacy a b then
    ⟨.capture, liftCapture a (captureRow a.raw b.raw).1,
      liftCapture b (captureRow a.raw b.raw).2, .capture h⟩
  else if h : Launch a b then
    ⟨.commitLaunch, setOut a .committing, setCarrier b .commit, .commitLaunch h⟩
  else if h : Forward a b then
    ⟨.commitForward, setCarrier a .none, setCarrier b .commit, .commitForward h⟩
  else if h : AtTarget a b then
    ⟨.commitAtTarget, setCarrier a .committedBack, consumeCommit b,
      .commitAtTarget h⟩
  else if h : Backward a b then
    ⟨.committedBackward, setCarrier a .committedBack, setCarrier b .none,
      .committedBackward h⟩
  else if h : Deposit a b then
    ⟨.committedDeposit, setOut a .committedReceived, setCarrier b .none,
      .committedDeposit h⟩
  else if h : Direct a b then
    ⟨.directCommit, setOut a .committedReceived, consumeCommit b, .directCommit h⟩
  else
    ⟨.idle, a, b, .idle⟩

def commitRow (a b : CNode) : CNode × CNode :=
  ((run a b).left, (run a b).right)

def commitRule (a b : CNode) : Rule := (run a b).rule

theorem commitRow_spec (a b : CNode) :
    RowStep a b (commitRule a b) (commitRow a b).1 (commitRow a b).2 :=
  (run a b).valid

private theorem seedOut_not_received (n : Node) : seedOut n ≠ .committedReceived := by
  change
    (if rawFinal n = true then CommitCtl.protectedFinal else CommitCtl.capturing) ≠
      CommitCtl.committedReceived
  split
  · intro hbad
    cases hbad
  · intro hbad
    cases hbad

private theorem seedIn_not_committed (n : Node) : seedIn n ≠ .committed := by
  change
    (if rawAccepted n = true then CommitIn.reserved else CommitIn.unreserved) ≠
      CommitIn.committed
  split
  · intro hbad
    cases hbad
  · intro hbad
    cases hbad

/-- Reduce only the three dispatch guards, before projecting the endpoints. -/
private theorem capture_dispatch (a b : CNode)
    (hs : ¬ SourceAck a) (ht : ¬ TargetCleanup a) (hc : Legacy a b) :
    commitRow a b =
      (liftCapture a (captureRow a.raw b.raw).1,
       liftCapture b (captureRow a.raw b.raw).2) := by
  have hr : run a b =
      { rule := .capture
        left := liftCapture a (captureRow a.raw b.raw).1
        right := liftCapture b (captureRow a.raw b.raw).2
        valid := .capture hc } := by
    simp only [run, dif_neg hs, dif_neg ht, dif_pos hc]
  exact congrArg (fun r : Result a b => (r.left, r.right)) hr

/-- All nontrivial imported patterns, not just a selected list of six rows.
    Equality is through the explicit projection required by the extension. -/
theorem commitRow_agrees_captureRow (a b : Node) (la lb : Bool)
    (h : captureRow a b ≠ (a, b)) :
    projectPair (commitRow (embed a la) (embed b lb)) = captureRow a b := by
  have hs : ¬ SourceAck (embed a la) := by
    intro hh
    exact seedOut_not_received a hh.2
  have ht : ¬ TargetCleanup (embed a la) := by
    intro hh
    exact seedIn_not_committed a hh.2.1
  have hl : Legacy (embed a la) (embed b lb) :=
    ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, h⟩
  calc
    projectPair (commitRow (embed a la) (embed b lb)) =
        ((captureRow a b).1, (captureRow a b).2) :=
      congrArg projectPair (capture_dispatch (embed a la) (embed b lb) hs ht hl)
    _ = captureRow a b := rfl

/-! ## Literal row equations -/

/-- Only the two post-FINAL legacy stutters below need imported internals. -/
@[simp] private theorem capture_final_empty (ccw : CcwPort) (inc : InControl) :
    captureRow (.root .out1 .heldCandidate ccw .finalReady inc) emptyRaw =
      (.root .out1 .heldCandidate ccw .finalReady inc, emptyRaw) := by
  simp [emptyRaw, captureRow, decodeLeft, decodeRight, decodeWire, encodeAgent,
    encodeSlot, outgoingOf, incomingOf, virtualCw, environmentOf, row,
    resolveInit, resolveResp, resCw, resCcw, res, Verdict.cw, Verdict.ccw]

@[simp] private theorem capture_final_target (ccw : CcwPort) (inc : InControl)
    (cw : CwPort) (out : OutControl) :
    captureRow (.root .out1 .heldCandidate ccw .finalReady inc)
      (.root .in0 cw .heldCandidate out .accepted) =
      (.root .out1 .heldCandidate ccw .finalReady inc,
       .root .in0 cw .heldCandidate out .accepted) := by
  simp [captureRow, decodeLeft, decodeRight, decodeWire, encodeAgent,
    encodeSlot, outgoingOf, incomingOf, virtualCw, environmentOf, row,
    resolveInit, resolveResp, resCw, resCcw, res, Verdict.cw, Verdict.ccw]

def ownerNode (ccw : CcwPort) (inc : InControl) (ctl : CommitCtl)
    (lease : CommitIn) (live : Bool) : CNode :=
  ⟨.root .out1 .heldCandidate ccw .finalReady inc, live, ctl, lease, .none⟩

def targetNode (cw : CwPort) (out : OutControl) (ctl : CommitCtl)
    (lease : CommitIn) (live : Bool) : CNode :=
  ⟨.root .in0 cw .heldCandidate out .accepted, live, ctl, lease, .none⟩

def slotNode (carrier : CommitCarrier) : CNode :=
  ⟨emptyRaw, false, .capturing, .unreserved, carrier⟩

private theorem root_ne_empty (ch : Choice) (cw : CwPort) (ccw : CcwPort)
    (out : OutControl) (inc : InControl) :
    Node.root ch cw ccw out inc ≠ emptyRaw := by
  intro h
  cases h

theorem commit_launch (ccw : CcwPort) (inc : InControl)
    (lease : CommitIn) (live : Bool) :
    commitRow (ownerNode ccw inc .protectedFinal lease live) (slotNode .none) =
      (ownerNode ccw inc .committing lease live, slotNode .commit) := by
  let a := ownerNode ccw inc .protectedFinal lease live
  let b := slotNode .none
  have hs : ¬ SourceAck a := by
    intro h
    have he : CommitCtl.protectedFinal = .committedReceived := h.2
    cases he
  have ht : ¬ TargetCleanup a := by
    intro h
    have he : false = true := h.1.1
    cases he
  have hc : ¬ Legacy a b := by
    intro h
    exact h.2.2.2.2 (capture_final_empty ccw inc)
  have hg : Launch a b := ⟨⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩⟩
  have hr : run a b =
      { rule := .commitLaunch
        left := setOut a .committing
        right := setCarrier b .commit
        valid := .commitLaunch hg } := by
    simp only [run, dif_neg hs, dif_neg ht, dif_neg hc, dif_pos hg]
  exact congrArg (fun r : Result a b => (r.left, r.right)) hr

theorem commit_forward :
    commitRow (slotNode .commit) (slotNode .none) =
      (slotNode .none, slotNode .commit) := by
  rfl

theorem commit_at_target (cw : CwPort) (out : OutControl) (ctl : CommitCtl) :
    commitRow (slotNode .commit) (targetNode cw out ctl .reserved true) =
      (slotNode .committedBack, targetNode cw out ctl .committed false) := by
  let a := slotNode .commit
  let b := targetNode cw out ctl .reserved true
  have hs : ¬ SourceAck a := by
    intro h
    have he : false = true := h.1.1
    cases he
  have ht : ¬ TargetCleanup a := by
    intro h
    have he : false = true := h.1.1
    cases he
  have hc : ¬ Legacy a b := by
    intro h
    have he : CommitCarrier.commit = .none := h.2.2.1
    cases he
  have hlaunch : ¬ Launch a b := by
    intro h
    have he : false = true := h.1.1
    cases he
  have hforward : ¬ Forward a b := by
    intro h
    exact root_ne_empty .in0 cw .heldCandidate out .accepted h.2.1
  have hg : AtTarget a b := ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
  have hr : run a b =
      { rule := .commitAtTarget
        left := setCarrier a .committedBack
        right := consumeCommit b
        valid := .commitAtTarget hg } := by
    simp only [run, dif_neg hs, dif_neg ht, dif_neg hc,
      dif_neg hlaunch, dif_neg hforward, dif_pos hg]
  exact congrArg (fun r : Result a b => (r.left, r.right)) hr

theorem committed_backward :
    commitRow (slotNode .none) (slotNode .committedBack) =
      (slotNode .committedBack, slotNode .none) := by
  rfl

theorem committed_deposit (ccw : CcwPort) (inc : InControl)
    (lease : CommitIn) (live : Bool) :
    commitRow (ownerNode ccw inc .committing lease live) (slotNode .committedBack) =
      (ownerNode ccw inc .committedReceived lease live, slotNode .none) := by
  let a := ownerNode ccw inc .committing lease live
  let b := slotNode .committedBack
  have hs : ¬ SourceAck a := by
    intro h
    have he : CommitCtl.committing = .committedReceived := h.2
    cases he
  have ht : ¬ TargetCleanup a := by
    intro h
    have he : false = true := h.1.1
    cases he
  have hc : ¬ Legacy a b := by
    intro h
    have he : CommitCarrier.committedBack = .none := h.2.2.2.1
    cases he
  have hlaunch : ¬ Launch a b := by
    intro h
    have he : CommitCtl.committing = .protectedFinal := h.2.1
    cases he
  have hslot : a.raw ≠ emptyRaw :=
    root_ne_empty .out1 .heldCandidate ccw .finalReady inc
  have hforward : ¬ Forward a b := fun h => hslot h.1.1
  have hat : ¬ AtTarget a b := fun h => hslot h.1.1
  have hback : ¬ Backward a b := fun h => hslot h.1.1
  have hg : Deposit a b := ⟨⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩⟩
  have hr : run a b =
      { rule := .committedDeposit
        left := setOut a .committedReceived
        right := setCarrier b .none
        valid := .committedDeposit hg } := by
    simp only [run, dif_neg hs, dif_neg ht, dif_neg hc, dif_neg hlaunch,
      dif_neg hforward, dif_neg hat, dif_neg hback, dif_pos hg]
  exact congrArg (fun r : Result a b => (r.left, r.right)) hr

/-- h=1: launch, target clearing, and the committed receipt are one firing. -/
theorem commit_direct (ccw : CcwPort) (inc : InControl)
    (lease : CommitIn) (live : Bool) (cw : CwPort) (out : OutControl)
    (ctl : CommitCtl) :
    commitRow (ownerNode ccw inc .protectedFinal lease live)
      (targetNode cw out ctl .reserved true) =
      (ownerNode ccw inc .committedReceived lease live,
       targetNode cw out ctl .committed false) := by
  let a := ownerNode ccw inc .protectedFinal lease live
  let b := targetNode cw out ctl .reserved true
  have hs : ¬ SourceAck a := by
    intro h
    have he : CommitCtl.protectedFinal = .committedReceived := h.2
    cases he
  have ht : ¬ TargetCleanup a := by
    intro h
    have he : false = true := h.1.1
    cases he
  have hc : ¬ Legacy a b := by
    intro h
    exact h.2.2.2.2 (capture_final_target ccw inc cw out)
  have hlaunch : ¬ Launch a b := by
    intro h
    exact root_ne_empty .in0 cw .heldCandidate out .accepted h.2.2.1
  have hslot : a.raw ≠ emptyRaw :=
    root_ne_empty .out1 .heldCandidate ccw .finalReady inc
  have hforward : ¬ Forward a b := fun h => hslot h.1.1
  have hat : ¬ AtTarget a b := fun h => hslot h.1.1
  have hback : ¬ Backward a b := fun h => hslot h.1.1
  have hdeposit : ¬ Deposit a b := by
    intro h
    have he : CommitCtl.protectedFinal = .committing := h.2.1
    cases he
  have hg : Direct a b :=
    ⟨⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
  have hr : run a b =
      { rule := .directCommit
        left := setOut a .committedReceived
        right := consumeCommit b
        valid := .directCommit hg } := by
    simp only [run, dif_neg hs, dif_neg ht, dif_neg hc, dif_neg hlaunch,
      dif_neg hforward, dif_neg hat, dif_neg hback, dif_neg hdeposit, dif_pos hg]
  exact congrArg (fun r : Result a b => (r.left, r.right)) hr

private theorem owner_target_exclusive (n : Node) :
    ¬ (rawOwner n = true ∧ rawTarget n = true) := by
  cases n with
  | interior w => simp [rawOwner, rawTarget]
  | root ch cw ccw out inc =>
      cases ch <;> simp [rawOwner, rawTarget]

/-- The neighbour is not tested or changed. -/
theorem source_ack (a b : CNode) (h : SourceAck a) :
    commitRow a b = (setOut a .clean, b) := by
  have hr : run a b =
      { rule := .sourceAck
        left := setOut a .clean
        right := b
        valid := .sourceAck h } := by
    simp only [run, dif_pos h]
  exact congrArg (fun r : Result a b => (r.left, r.right)) hr

/-- The target's outgoing lifecycle and its neighbour are not tested or changed. -/
theorem target_cleanup (a b : CNode) (h : TargetCleanup a) :
    commitRow a b = (setIn a .clean, b) := by
  have hn : ¬ SourceAck a := by
    intro hs
    exact owner_target_exclusive a.raw ⟨hs.1.1, h.1.1⟩
  have hr : run a b =
      { rule := .targetCleanup
        left := setIn a .clean
        right := b
        valid := .targetCleanup h } := by
    simp only [run, dif_neg hn, dif_pos h]
  exact congrArg (fun r : Result a b => (r.left, r.right)) hr

abbrev ThreeSites := CNode × CNode × CNode

def fireSource (s : ThreeSites) : ThreeSites :=
  let p := commitRow s.1 s.2.1
  (p.1, p.2, s.2.2)

def fireTarget (s : ThreeSites) : ThreeSites :=
  let p := commitRow s.2.1 s.2.2
  (s.1, p.1, p.2)

/-- Actual pair firings at source|target and target|next, in both orders. -/
theorem discharges_either_order (a b r : CNode)
    (ha : SourceAck a) (hb : TargetCleanup b) :
    fireTarget (fireSource (a, b, r)) = (setOut a .clean, setIn b .clean, r) ∧
    fireSource (fireTarget (a, b, r)) = (setOut a .clean, setIn b .clean, r) := by
  constructor
  · simp only [fireSource, fireTarget, source_ack a b ha, target_cleanup b r hb]
  · simp only [fireSource, fireTarget, target_cleanup b r hb,
      source_ack a (setIn b .clean) ha]

/-! ## The old TGT/FINAL seam installs the new authority in the same firing. -/

theorem TGT_installs_commit_lease (cw : CwPort) (out : OutControl) (live : Bool) :
    let p := commitRow (embed (.interior (.capture .proposal)) false)
      (embed (.root .in0 cw .heldCandidate out .reserved) live)
    p.2.raw = .root .in0 cw .heldCandidate out .accepted ∧
      p.2.incoming = .reserved ∧ p.2.leader = live := by
  let a := embed (.interior (.capture .proposal)) false
  let b := embed (.root .in0 cw .heldCandidate out .reserved) live
  have hs : ¬ SourceAck a := by
    intro h
    have he : false = true := h.1.1
    cases he
  have ht : ¬ TargetCleanup a := by
    intro h
    have he : false = true := h.1.1
    cases he
  have hne :
      captureRow (.interior (.capture .proposal))
        (.root .in0 cw .heldCandidate out .reserved) ≠
      (.interior (.capture .proposal), .root .in0 cw .heldCandidate out .reserved) := by
    intro he
    have he' := congrArg (fun p : Node × Node => p.1) he
    rw [ShortGapCaptureReservation.TGT_row] at he'
    cases he'
  have hc : Legacy a b := ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, hne⟩
  have hp := congrArg (fun p : CNode × CNode => p.2)
    (capture_dispatch a b hs ht hc)
  exact ⟨congrArg CNode.raw hp, congrArg CNode.incoming hp, congrArg CNode.leader hp⟩

theorem FINAL_installs_protection (ccw : CcwPort) (inc : InControl) (live : Bool) :
    let p := commitRow (embed (.root .out1 .heldCandidate ccw .proposal inc) live)
      (embed (.interior (.capture .finalBack)) false)
    p.1.raw = .root .out1 .heldCandidate ccw .finalReady inc ∧
      p.1.outgoing = .protectedFinal ∧ p.1.leader = live := by
  let a := embed (.root .out1 .heldCandidate ccw .proposal inc) live
  let b := embed (.interior (.capture .finalBack)) false
  have hs : ¬ SourceAck a := by
    intro h
    have he : CommitCtl.capturing = .committedReceived := h.2
    cases he
  have ht : ¬ TargetCleanup a := by
    intro h
    have he : false = true := h.1.1
    cases he
  have hne :
      captureRow (.root .out1 .heldCandidate ccw .proposal inc)
        (.interior (.capture .finalBack)) ≠
      (.root .out1 .heldCandidate ccw .proposal inc, .interior (.capture .finalBack)) := by
    intro he
    have he' := congrArg (fun p : Node × Node => p.1) he
    rw [ShortGapCaptureReservation.FINAL_deposit_row] at he'
    cases he'
  have hc : Legacy a b := ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, hne⟩
  have hp := congrArg (fun p : CNode × CNode => p.1)
    (capture_dispatch a b hs ht hc)
  exact ⟨congrArg CNode.raw hp, congrArg CNode.outgoing hp, congrArg CNode.leader hp⟩

/-! ## Safety of every branch, including the total function's fallback -/

def outRank : CommitCtl -> Nat
  | .capturing => 0
  | .protectedFinal => 1
  | .committing => 2
  | .committedReceived => 3
  | .clean => 4

def inRank : CommitIn -> Nat
  | .unreserved => 0
  | .reserved => 1
  | .committed => 2
  | .clean => 3

private theorem observeOut_rank (c : CommitCtl) (n : Node) :
    outRank c ≤ outRank (observeOut c n) := by
  cases c with
  | capturing => exact Nat.zero_le _
  | protectedFinal => exact Nat.le_refl _
  | committing => exact Nat.le_refl _
  | committedReceived => exact Nat.le_refl _
  | clean => exact Nat.le_refl _

private theorem observeIn_rank (c : CommitIn) (n m : Node) :
    inRank c ≤ inRank (observeIn c n m) := by
  cases c with
  | unreserved => exact Nat.zero_le _
  | reserved => exact Nat.le_refl _
  | committed => exact Nat.le_refl _
  | clean => exact Nat.le_refl _

private theorem step_out_rank {a b x y : CNode} {k : Rule}
    (h : RowStep a b k x y) :
    outRank a.outgoing ≤ outRank x.outgoing ∧
      outRank b.outgoing ≤ outRank y.outgoing := by
  cases h with
  | capture _ =>
      exact ⟨observeOut_rank _ _, observeOut_rank _ _⟩
  | commitLaunch hg => simp [setOut, setCarrier, hg.2.1, outRank]
  | commitForward _ => simp [setCarrier]
  | commitAtTarget _ => simp [setCarrier, consumeCommit]
  | committedBackward _ => simp [setCarrier]
  | committedDeposit hg => simp [setOut, setCarrier, hg.2.1, outRank]
  | directCommit hg => simp [setOut, consumeCommit, hg.2.1, outRank]
  | sourceAck hg => simp [setOut, hg.2, outRank]
  | targetCleanup _ => simp [setIn]
  | idle => simp

private theorem step_in_rank {a b x y : CNode} {k : Rule}
    (h : RowStep a b k x y) :
    inRank a.incoming ≤ inRank x.incoming ∧
      inRank b.incoming ≤ inRank y.incoming := by
  cases h with
  | capture _ => exact ⟨observeIn_rank _ _ _, observeIn_rank _ _ _⟩
  | commitLaunch _ => simp [setOut, setCarrier]
  | commitForward _ => simp [setCarrier]
  | commitAtTarget hg => simp [setCarrier, consumeCommit, hg.2.2.1, inRank]
  | committedBackward _ => simp [setCarrier]
  | committedDeposit _ => simp [setOut, setCarrier]
  | directCommit hg => simp [setOut, consumeCommit, hg.2.2.2.1, inRank]
  | sourceAck _ => simp [setOut]
  | targetCleanup hg => simp [setIn, hg.2.1, inRank]
  | idle => simp

theorem commitRow_controls_monotone (a b : CNode) :
    (outRank a.outgoing ≤ outRank (commitRow a b).1.outgoing ∧
     outRank b.outgoing ≤ outRank (commitRow a b).2.outgoing) ∧
    (inRank a.incoming ≤ inRank (commitRow a b).1.incoming ∧
     inRank b.incoming ≤ inRank (commitRow a b).2.incoming) :=
  ⟨step_out_rank (commitRow_spec a b), step_in_rank (commitRow_spec a b)⟩

/-- The direct h=1 case is a fused instance of the same semantic commit event. -/
def IsCommitLiteral (k : Rule) : Prop :=
  k = .commitAtTarget ∨ k = .directCommit

private theorem step_needs_lease {a b x y : CNode} {k : Rule}
    (h : RowStep a b k x y) :
    IsCommitLiteral k -> Target b ∧ b.incoming = .reserved ∧ b.leader = true := by
  cases h with
  | commitAtTarget hg => exact fun _ => ⟨hg.2.1, hg.2.2.1, hg.2.2.2⟩
  | directCommit hg => exact fun _ => ⟨hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2⟩
  | capture _ => simp [IsCommitLiteral]
  | commitLaunch _ => simp [IsCommitLiteral]
  | commitForward _ => simp [IsCommitLiteral]
  | committedBackward _ => simp [IsCommitLiteral]
  | committedDeposit _ => simp [IsCommitLiteral]
  | sourceAck _ => simp [IsCommitLiteral]
  | targetCleanup _ => simp [IsCommitLiteral]
  | idle => simp [IsCommitLiteral]

private theorem rawTarget_iff (n : Node) :
    rawTarget n = true ↔
      ∃ (cw : CwPort) (out : OutControl),
        n = .root .in0 cw .heldCandidate out .accepted := by
  cases n with
  | interior w => simp [rawTarget]
  | root ch cw ccw out inc =>
      cases ch <;> cases ccw <;> cases inc <;> simp [rawTarget]

/-- The extended reserved lease, raw accepted state, and heldCandidate are
    all necessary. raw accepted is NOT a second proposal authorization. -/
theorem commit_needs_lease (a b : CNode) (h : IsCommitLiteral (commitRule a b)) :
    b.incoming = .reserved ∧ b.carrier = .none ∧ b.leader = true ∧
      ∃ (cw : CwPort) (out : OutControl),
        b.raw = .root .in0 cw .heldCandidate out .accepted := by
  have hb := step_needs_lease (commitRow_spec a b) h
  exact ⟨hb.2.1, hb.1.2, hb.2.2, (rawTarget_iff b.raw).mp hb.1.1⟩

@[simp] private theorem bool_no_fall (v : Bool) :
    (v = true ∧ v = false) ↔ False := by
  cases v <;> simp

private theorem step_leader {a b x y : CNode} {k : Rule}
    (h : RowStep a b k x y) :
    x.leader = a.leader ∧
    (y.leader ≠ b.leader ↔ IsCommitLiteral k) ∧
    ((b.leader = true ∧ y.leader = false) ↔ IsCommitLiteral k) := by
  cases h with
  | capture _ => simp [liftCapture, IsCommitLiteral]
  | commitLaunch _ => simp [setOut, setCarrier, IsCommitLiteral]
  | commitForward _ => simp [setCarrier, IsCommitLiteral]
  | commitAtTarget hg =>
      simp [setCarrier, consumeCommit, IsCommitLiteral, hg.2.2.2]
  | committedBackward _ => simp [setCarrier, IsCommitLiteral]
  | committedDeposit _ => simp [setOut, setCarrier, IsCommitLiteral]
  | directCommit hg =>
      simp [setOut, consumeCommit, IsCommitLiteral, hg.2.2.2.2]
  | sourceAck _ => simp [setOut, IsCommitLiteral]
  | targetCleanup _ => simp [setIn, IsCommitLiteral]
  | idle => simp [IsCommitLiteral]

/-- No pair row clears its left endpoint's leader flag. -/
theorem sourceLeader_frame_literal (a b : CNode) :
    (commitRow a b).1.leader = a.leader :=
  (step_leader (commitRow_spec a b)).1

/-- Both arbitrary flag change and true-to-false change are characterized.
    An already-false target is not an enabled commit-at-target row. -/
theorem targetLeader_falls_iff_commit_literal (a b : CNode) :
    ((commitRow a b).2.leader ≠ b.leader ↔ IsCommitLiteral (commitRule a b)) ∧
    ((b.leader = true ∧ (commitRow a b).2.leader = false) ↔
      IsCommitLiteral (commitRule a b)) :=
  (step_leader (commitRow_spec a b)).2

/-- capturing is the sole pre-FINAL extension control; clean is terminal. -/
theorem protected_no_abort_literal (a b : CNode) :
    (a.outgoing = .protectedFinal -> (commitRow a b).1.outgoing ≠ .capturing) ∧
    (b.outgoing = .protectedFinal -> (commitRow a b).2.outgoing ≠ .capturing) := by
  have hm := step_out_rank (commitRow_spec a b)
  constructor
  · intro ha hpre
    have hbad := hm.1
    rw [ha, hpre] at hbad
    simp [outRank] at hbad
  · intro hb hpre
    have hbad := hm.2
    rw [hb, hpre] at hbad
    simp [outRank] at hbad

private theorem step_never_rises {a b x y : CNode} {k : Rule}
    (h : RowStep a b k x y) :
    (a.leader = false -> x.leader = false) ∧
    (b.leader = false -> y.leader = false) := by
  cases h <;> simp [liftCapture, setOut, setIn, setCarrier, consumeCommit]

abbrev PostCommitted (n : CNode) : Prop :=
  2 ≤ inRank n.incoming ∧ n.leader = false

abbrev ReceiptDone (n : CNode) : Prop := 3 ≤ outRank n.outgoing

theorem committed_rank_iff (c : CommitIn) :
    2 ≤ inRank c ↔ c = .committed ∨ c = .clean := by
  cases c <;> decide

theorem receipt_rank_iff (c : CommitCtl) :
    3 ≤ outRank c ↔ c = .committedReceived ∨ c = .clean := by
  cases c <;> decide

/-- Both endpoints preserve spent target state and completed source receipt.
    Iteration gives the same irreversibility for every finite schedule. -/
theorem postcommit_irreversible_literal (a b : CNode) :
    (PostCommitted a -> PostCommitted (commitRow a b).1) ∧
    (PostCommitted b -> PostCommitted (commitRow a b).2) ∧
    (ReceiptDone a -> ReceiptDone (commitRow a b).1) ∧
    (ReceiptDone b -> ReceiptDone (commitRow a b).2) := by
  have hi := step_in_rank (commitRow_spec a b)
  have ho := step_out_rank (commitRow_spec a b)
  have hl := step_never_rises (commitRow_spec a b)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact ⟨Nat.le_trans h.1 hi.1, hl.1 h.2⟩
  · intro h
    exact ⟨Nat.le_trans h.1 hi.2, hl.2 h.2⟩
  · intro h
    exact Nat.le_trans h ho.1
  · intro h
    exact Nat.le_trans h ho.2

/-- A consumed or cleaned target cannot commit again, even with a stray message. -/
theorem postcommit_no_second_literal (a b : CNode) (hb : PostCommitted b) :
    ¬ IsCommitLiteral (commitRule a b) := by
  intro hc
  have hr := (commit_needs_lease a b hc).1
  have hbad := hb.1
  rw [hr] at hbad
  simp [inRank] at hbad

/-! ## Exhaustive field-level write masks for the wrapper

Rule                  left writes              right writes
capture               raw,outgoing,incoming    raw,outgoing,incoming
commitLaunch          outgoing                 carrier
commitForward         carrier                  carrier
commitAtTarget        carrier                  leader,incoming
committedBackward     carrier                  carrier
committedDeposit      outgoing                 carrier
directCommit          outgoing                 leader,incoming
sourceAck             outgoing                 none
targetCleanup         incoming                 none
idle                  none                     none

For capture, the raw pair is additionally pinned to the exact imported
captureRow result. For every other rule, the complete raw pair is framed.
-/

structure Writes where
  raw : Bool := false
  leader : Bool := false
  outgoing : Bool := false
  incoming : Bool := false
  carrier : Bool := false

def noWrites : Writes := {}

def writeMasks : Rule -> Writes × Writes
  | .capture =>
      ({ raw := true, outgoing := true, incoming := true },
       { raw := true, outgoing := true, incoming := true })
  | .commitLaunch => ({ outgoing := true }, { carrier := true })
  | .commitForward => ({ carrier := true }, { carrier := true })
  | .commitAtTarget => ({ carrier := true }, { leader := true, incoming := true })
  | .committedBackward => ({ carrier := true }, { carrier := true })
  | .committedDeposit => ({ outgoing := true }, { carrier := true })
  | .directCommit => ({ outgoing := true }, { leader := true, incoming := true })
  | .sourceAck => ({ outgoing := true }, noWrites)
  | .targetCleanup => ({ incoming := true }, noWrites)
  | .idle => (noWrites, noWrites)

def FrameOne (w : Writes) (before after : CNode) : Prop :=
  (w.raw = false -> after.raw = before.raw) ∧
  (w.leader = false -> after.leader = before.leader) ∧
  (w.outgoing = false -> after.outgoing = before.outgoing) ∧
  (w.incoming = false -> after.incoming = before.incoming) ∧
  (w.carrier = false -> after.carrier = before.carrier)

def RowFrame (k : Rule) (a b x y : CNode) : Prop :=
  FrameOne (writeMasks k).1 a x ∧ FrameOne (writeMasks k).2 b y ∧
  (k = .capture -> (x.raw, y.raw) = captureRow a.raw b.raw) ∧
  (k ≠ .capture -> (x.raw, y.raw) = (a.raw, b.raw))

private theorem step_frame {a b x y : CNode} {k : Rule}
    (h : RowStep a b k x y) : RowFrame k a b x y := by
  cases h <;>
    simp [RowFrame, FrameOne, writeMasks, noWrites, liftCapture,
      setOut, setIn, setCarrier, consumeCommit]

theorem commitRow_frame (a b : CNode) :
    RowFrame (commitRule a b) a b (commitRow a b).1 (commitRow a b).2 :=
  step_frame (commitRow_spec a b)

#print axioms commitRow_agrees_captureRow
#print axioms commit_needs_lease
#print axioms targetLeader_falls_iff_commit_literal
#print axioms protected_no_abort_literal
#print axioms postcommit_irreversible_literal
#print axioms postcommit_no_second_literal
#print axioms commitRow_controls_monotone
#print axioms commitRow_frame
#print axioms discharges_either_order

end ShortGapCaptureCommitRows
