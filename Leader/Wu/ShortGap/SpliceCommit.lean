import Leader.Wu.ShortGap.CaptureCommitRows

namespace ShortGapSpliceCommit

open ShortGapLiteralGapRows ShortGapCaptureReservation ShortGapCaptureCommitRows
open FiniteUniformStoppingTree

set_option autoImplicit false

/-!
# The local SPLICE commit: rows, frames, debt, and the splice tail

New file: `Leader/Wu/ShortGap/SpliceCommit.lean`.

It is shown that a whole-corridor two-pass repair cannot be globally
`O(n^2)`: a commit that reruns a `2*L-1` repair over the merged corridor
recreates order `n*L` debt, and the exact deficit `2*n*(x+y-1)` is reproduced
below as `commit_merge_deficit`.  A *local splice* replaces it:

1. commit-at-B clears only B's leader bit and snapshots `B.cw`'s phase into an
   interior `bridge`; every `(B,C)` token and `C.ccw` stay unchanged;
2. the COMMITTED receipt returns over the `x-1` capture cells, carrying the
   snapshot as its `payload`;
3. deposit-at-A overwrites `A.cw = heldCandidate` by `adopt` of that snapshot,
   which is never a verdict;
4. outstanding `(B,C)` traffic finishes under its own lineage, and its reply is
   converted at the bridge into a *retirement witness*, never a denial for A;
5. after retirement `A.cw := toSend`, and the first fresh `A -> C` declaration
   must consume any stale `C.ccw` `heldDenial` before it can count.

Nothing here is a global freshness, reachability, fairness or completion-time
theorem.  These are local row equations, local frames, an exact splice debt on
the phase machine, and the scale-one Bellman certificate of the splice tail.

The `bridge`, `payload`, `witness` and flush marks are physical constant-size
fields of the wrapper; no identifier, nonce, generation or unbounded datum
occurs in any of them.  The retirement witness type has no verdict payload at
all, which is what makes `splice_never_retags_denial` a statement about the
carrier and not only about the current table.
-/

/-! ## Snapshot of the committed root's outgoing phase -/

/-- The physical `(B.cw, B.outgoing)` pair recorded at the commit.  This is
`B`'s old `(B,C)` phase; no generation is stored. -/
structure SnapPhase where
  cw : CwPort
  out : OutControl
  deriving DecidableEq

def snapNode : Node -> SnapPhase
  | .root _ cw _ out _ => ⟨cw, out⟩
  | .interior _ => ⟨.toSend, .home⟩

/-- `adopt`: A takes over B's position, never B's verdict.  A settled or
outstanding old episode becomes `waiting` (A must await the retirement
witness); an old episode that never launched becomes `toSend`. -/
def adoptCw (s : SnapPhase) : CwPort :=
  match s.cw with
  | .toSend => .toSend
  | _ => .waiting

def adoptCwOf : Option SnapPhase -> CwPort
  | none => .waiting
  | some s => adoptCw s

theorem adoptCw_ne_denial (s : SnapPhase) : adoptCw s ≠ .heldDenial := by
  unfold adoptCw
  cases s.cw <;> simp

theorem adoptCw_ne_candidate (s : SnapPhase) : adoptCw s ≠ .heldCandidate := by
  unfold adoptCw
  cases s.cw <;> simp

theorem adoptCwOf_ne_denial (s : Option SnapPhase) : adoptCwOf s ≠ .heldDenial := by
  cases s with
  | none => simp [adoptCwOf]
  | some v => exact adoptCw_ne_denial v

theorem adoptCwOf_ne_candidate (s : Option SnapPhase) : adoptCwOf s ≠ .heldCandidate := by
  cases s with
  | none => simp [adoptCwOf]
  | some v => exact adoptCw_ne_candidate v

/-! ## The wrapped node -/

/-- A-side lifecycle of one splice, plus the bridge marks of former B. -/
inductive SpliceCtl where
  | inactive | bridged | drained | adopted | retired | armed
  deriving DecidableEq

/-- The retirement witness.  It has no verdict payload: the constructor list
below is the complete carrier alphabet of the retirement lane. -/
inductive RetireWitness where
  | none | token
  deriving DecidableEq

/-- Flush state of the first fresh `A -> C` declaration. -/
inductive DeclFlush where
  | none | unflushed | flushed
  deriving DecidableEq

structure SNode where
  core : CNode
  bridge : Option SnapPhase
  payload : Option SnapPhase
  splice : SpliceCtl
  witness : RetireWitness
  flush : DeclFlush
  deriving DecidableEq

def sembed (n : Node) (leader : Bool) : SNode :=
  ⟨embed n leader, none, none, .inactive, .none, .none⟩

def projectCore (p : SNode × SNode) : CNode × CNode := (p.1.core, p.2.core)

def projectRaw (p : SNode × SNode) : Node × Node := (p.1.core.raw, p.2.core.raw)

/-- Every splice field of a node is at its pre-splice value. -/
abbrev Neutral (n : SNode) : Prop :=
  n.bridge = none ∧ n.payload = none ∧ n.splice = .inactive ∧
    n.witness = .none ∧ n.flush = .none

/-! ## Raw port surgery -/

def setRawCw (n : Node) (v : CwPort) : Node :=
  match n with
  | .root ch _ ccw out inc => .root ch v ccw out inc
  | .interior w => .interior w

def setRawCcw (n : Node) (v : CcwPort) : Node :=
  match n with
  | .root ch cw _ out inc => .root ch cw v out inc
  | .interior w => .interior w

@[simp] theorem ccwPort_setRawCw (n : Node) (v : CwPort) :
    (setRawCw n v).ccwPort = n.ccwPort := by
  cases n <;> rfl

@[simp] theorem cwPort_setRawCcw (n : Node) (v : CcwPort) :
    (setRawCcw n v).cwPort = n.cwPort := by
  cases n <;> rfl

@[simp] theorem ccwPort_setRawCcw_root (ch : Choice) (cw : CwPort) (ccw : CcwPort)
    (out : OutControl) (inc : InControl) (v : CcwPort) :
    (setRawCcw (.root ch cw ccw out inc) v).ccwPort = some v := rfl

theorem cwPort_setRawCw_le (n : Node) (v : CwPort) :
    (setRawCw n v).cwPort = none ∨ (setRawCw n v).cwPort = some v := by
  cases n with
  | root => exact Or.inr rfl
  | interior => exact Or.inl rfl

/-- The declaration wire of a fresh selection episode. -/
def declRaw : Node := .interior (.selection (.decl .out1))

@[simp] theorem cwPort_declRaw : declRaw.cwPort = none := rfl
@[simp] theorem ccwPort_declRaw : declRaw.ccwPort = none := rfl
@[simp] theorem cwPort_emptyRaw : emptyRaw.cwPort = none := rfl
@[simp] theorem ccwPort_emptyRaw : emptyRaw.ccwPort = none := rfl

/-- The old `(B,C)` reply has landed at former B. -/
def settledCw : Node -> Bool
  | .root _ .heldDenial _ _ _ => true
  | .root _ .heldCandidate _ _ _ => true
  | _ => false

/-! ## Guards of the splice table -/

abbrev SEmpty (n : SNode) : Prop := n.core.raw = emptyRaw ∧ n.core.carrier = .none

abbrev FreshFlush (a b : SNode) : Prop :=
  a.flush = .unflushed ∧ b.core.raw.ccwPort = some .heldDenial ∧ b.flush = .none

abbrev FreshLaunch (a b : SNode) : Prop :=
  a.splice = .armed ∧ a.flush = .unflushed ∧ a.core.raw.cwPort = some .toSend ∧
    SEmpty b ∧ b.flush = .none

abbrev FreshForward (a b : SNode) : Prop :=
  a.flush = .unflushed ∧ a.core.raw = declRaw ∧ SEmpty b ∧ b.flush = .none

abbrev RetireLaunch (a b : SNode) : Prop :=
  SEmpty a ∧ a.witness = .none ∧ b.splice = .bridged ∧ b.core.leader = false ∧
    settledCw b.core.raw = true ∧ b.witness = .none

abbrev RetireBackward (a b : SNode) : Prop :=
  SEmpty a ∧ a.witness = .none ∧ SEmpty b ∧ b.witness = .token

abbrev RetireDeposit (a b : SNode) : Prop :=
  a.splice = .adopted ∧ SEmpty b ∧ b.witness = .token

abbrev AdoptDeposit (a b : SNode) : Prop :=
  Deposit a.core b.core ∧ b.payload ≠ none ∧ a.splice = .inactive

abbrev DirectAdopt (a : SNode) : Prop :=
  a.splice = .inactive ∧ a.payload ≠ none ∧ rawOwner a.core.raw = true ∧
    a.core.outgoing = .clean

abbrev HandoffArm (a : SNode) : Prop :=
  a.splice = .retired ∧ a.core.raw.cwPort ≠ none

/-! ## Effects -/

def flushL (a : SNode) : SNode := { a with flush := .flushed }

def flushR (b : SNode) : SNode :=
  { b with core := { b.core with raw := setRawCcw b.core.raw .free } }

def launchL (a : SNode) : SNode :=
  { a with core := { a.core with raw := setRawCw a.core.raw .waiting }, flush := .none }

def declR (b : SNode) : SNode :=
  { b with core := { b.core with raw := declRaw }, flush := .unflushed }

def fwdL (a : SNode) : SNode :=
  { a with core := { a.core with raw := emptyRaw }, flush := .none }

def witnessL (a : SNode) : SNode := { a with witness := .token }

def drainR (b : SNode) : SNode := { b with splice := .drained }

def clearWitnessR (b : SNode) : SNode := { b with witness := .none }

def retiredL (a : SNode) : SNode := { a with splice := .retired }

def adoptL (a : SNode) (s : Option SnapPhase) : SNode :=
  { a with
    core := { a.core with
                raw := setRawCw a.core.raw (adoptCwOf s),
                outgoing := .committedReceived },
    splice := .adopted }

def adoptR (b : SNode) : SNode :=
  { b with core := setCarrier b.core .none, payload := none }

def directAdoptL (a : SNode) : SNode :=
  { a with
    core := { a.core with raw := setRawCw a.core.raw (adoptCwOf a.payload) },
    splice := .adopted, payload := none }

def armL (a : SNode) : SNode :=
  { a with
    core := { a.core with raw := setRawCw a.core.raw .toSend },
    splice := .armed, flush := .unflushed }

/-! ## Conservative lift of the imported commit row -/

def isBack (c : CommitCarrier) : Bool := match c with | .committedBack => true | _ => false
def isClear (c : CommitCarrier) : Bool := match c with | .none => true | _ => false

/-- The commit is exactly the firing at which the target's leader bit falls. -/
def committedNow (b b' : CNode) : Bool := b.leader && !b'.leader

/-- The COMMITTED receipt moved one cell towards A. -/
def receiptMoved (b a' b' : CNode) : Bool :=
  isBack b.carrier && isClear b'.carrier && isBack a'.carrier

def liftLeft (a b : SNode) (a' b' : CNode) : SNode :=
  { a with
    core := a'
    payload :=
      if committedNow b.core b' then some (snapNode b.core.raw)
      else if receiptMoved b.core a' b' then b.payload else a.payload }

def liftRight (b : SNode) (a' b' : CNode) : SNode :=
  { b with
    core := b'
    bridge := if committedNow b.core b' then some (snapNode b.core.raw) else b.bridge
    payload := if receiptMoved b.core a' b' then none else b.payload
    splice := if committedNow b.core b' then .bridged else b.splice }

def liftPair (a b : SNode) (p : CNode × CNode) : SNode × SNode :=
  (liftLeft a b p.1 p.2, liftRight b p.1 p.2)

/-! ## The table -/

inductive SRule where
  | core (k : Rule)
  | freshFlush | freshLaunch | freshForward
  | retireLaunch | retireBackward | retireDeposit
  | adoptDeposit | directAdopt | handoffArm
  deriving DecidableEq

def IsNew : SRule -> Bool
  | .core _ => false
  | _ => true

inductive SRowStep (a b : SNode) : SRule -> SNode -> SNode -> Prop where
  | core :
      SRowStep a b (.core (commitRule a.core b.core))
        (liftPair a b (commitRow a.core b.core)).1
        (liftPair a b (commitRow a.core b.core)).2
  | freshFlush (h : FreshFlush a b) :
      SRowStep a b .freshFlush (flushL a) (flushR b)
  | freshLaunch (h : FreshLaunch a b) :
      SRowStep a b .freshLaunch (launchL a) (declR b)
  | freshForward (h : FreshForward a b) :
      SRowStep a b .freshForward (fwdL a) (declR b)
  | retireLaunch (h : RetireLaunch a b) :
      SRowStep a b .retireLaunch (witnessL a) (drainR b)
  | retireBackward (h : RetireBackward a b) :
      SRowStep a b .retireBackward (witnessL a) (clearWitnessR b)
  | retireDeposit (h : RetireDeposit a b) :
      SRowStep a b .retireDeposit (retiredL a) (clearWitnessR b)
  | adoptDeposit (h : AdoptDeposit a b) :
      SRowStep a b .adoptDeposit (adoptL a b.payload) (adoptR b)
  | directAdopt (h : DirectAdopt a) :
      SRowStep a b .directAdopt (directAdoptL a) b
  | handoffArm (h : HandoffArm a) :
      SRowStep a b .handoffArm (armL a) b

structure SResult (a b : SNode) where
  rule : SRule
  left : SNode
  right : SNode
  valid : SRowStep a b rule left right

/-- Total, deterministic, radius-one dispatch.  The flush is checked first, so
a stale `C.ccw` receipt is consumed before any comparison can read it. -/
def srun (a b : SNode) : SResult a b :=
  if h : FreshFlush a b then
    ⟨.freshFlush, flushL a, flushR b, .freshFlush h⟩
  else if h : FreshLaunch a b then
    ⟨.freshLaunch, launchL a, declR b, .freshLaunch h⟩
  else if h : FreshForward a b then
    ⟨.freshForward, fwdL a, declR b, .freshForward h⟩
  else if h : RetireLaunch a b then
    ⟨.retireLaunch, witnessL a, drainR b, .retireLaunch h⟩
  else if h : RetireBackward a b then
    ⟨.retireBackward, witnessL a, clearWitnessR b, .retireBackward h⟩
  else if h : RetireDeposit a b then
    ⟨.retireDeposit, retiredL a, clearWitnessR b, .retireDeposit h⟩
  else if h : AdoptDeposit a b then
    ⟨.adoptDeposit, adoptL a b.payload, adoptR b, .adoptDeposit h⟩
  else if h : DirectAdopt a then
    ⟨.directAdopt, directAdoptL a, b, .directAdopt h⟩
  else if h : HandoffArm a then
    ⟨.handoffArm, armL a, b, .handoffArm h⟩
  else
    ⟨.core (commitRule a.core b.core),
      (liftPair a b (commitRow a.core b.core)).1,
      (liftPair a b (commitRow a.core b.core)).2, .core⟩

def spliceRow (a b : SNode) : SNode × SNode := ((srun a b).left, (srun a b).right)

def spliceRule (a b : SNode) : SRule := (srun a b).rule

theorem spliceRow_spec (a b : SNode) :
    SRowStep a b (spliceRule a b) (spliceRow a b).1 (spliceRow a b).2 :=
  (srun a b).valid


/-! ## Conservativity: on a neutral pair the imported commit row is executed -/

private theorem neutral_no_new (a b : SNode) (hna : Neutral a) (hnb : Neutral b) :
    (¬ FreshFlush a b) ∧ (¬ FreshLaunch a b) ∧ (¬ FreshForward a b) ∧
    (¬ RetireLaunch a b) ∧ (¬ RetireBackward a b) ∧ (¬ RetireDeposit a b) ∧
    (¬ AdoptDeposit a b) ∧ (¬ DirectAdopt a) ∧ (¬ HandoffArm a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hx := h.1
    rw [hna.2.2.2.2] at hx
    cases hx
  · intro h
    have hx := h.1
    rw [hna.2.2.1] at hx
    cases hx
  · intro h
    have hx := h.1
    rw [hna.2.2.2.2] at hx
    cases hx
  · intro h
    have hx := h.2.2.1
    rw [hnb.2.2.1] at hx
    cases hx
  · intro h
    have hx := h.2.2.2
    rw [hnb.2.2.2.1] at hx
    cases hx
  · intro h
    have hx := h.1
    rw [hna.2.2.1] at hx
    cases hx
  · intro h
    exact h.2.1 hnb.2.1
  · intro h
    exact h.2.1 hna.2.1
  · intro h
    have hx := h.1
    rw [hna.2.2.1] at hx
    cases hx

theorem splice_core_dispatch (a b : SNode) (hna : Neutral a) (hnb : Neutral b) :
    srun a b =
      { rule := .core (commitRule a.core b.core)
        left := (liftPair a b (commitRow a.core b.core)).1
        right := (liftPair a b (commitRow a.core b.core)).2
        valid := .core } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := neutral_no_new a b hna hnb
  simp only [srun, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5,
    dif_neg h6, dif_neg h7, dif_neg h8, dif_neg h9]

theorem spliceRule_core (a b : SNode) (hna : Neutral a) (hnb : Neutral b) :
    spliceRule a b = .core (commitRule a.core b.core) :=
  congrArg SResult.rule (splice_core_dispatch a b hna hnb)

theorem spliceRow_core (a b : SNode) (hna : Neutral a) (hnb : Neutral b) :
    spliceRow a b = liftPair a b (commitRow a.core b.core) :=
  congrArg (fun r : SResult a b => (r.left, r.right)) (splice_core_dispatch a b hna hnb)

/-- The splice table is conservative over `commitRow`: on a pre-splice pair the
whole imported core pair transition is executed unchanged. -/
theorem spliceRow_agrees_commitRow (a b : SNode) (hna : Neutral a) (hnb : Neutral b) :
    projectCore (spliceRow a b) = commitRow a.core b.core := by
  rw [spliceRow_core a b hna hnb]
  rfl

/-- The full chain down to the imported literal capture row. -/
theorem spliceRow_agrees_captureRow (a b : Node) (la lb : Bool)
    (h : captureRow a b ≠ (a, b)) :
    projectRaw (spliceRow (sembed a la) (sembed b lb)) = captureRow a b := by
  have hn : Neutral (sembed a la) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hm : Neutral (sembed b lb) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hcore := spliceRow_agrees_commitRow (sembed a la) (sembed b lb) hn hm
  have hraw := commitRow_agrees_captureRow a b la lb h
  have h1 : (spliceRow (sembed a la) (sembed b lb)).1.core = (commitRow (embed a la) (embed b lb)).1 :=
    congrArg (fun p : CNode × CNode => p.1) hcore
  have h2 : (spliceRow (sembed a la) (sembed b lb)).2.core = (commitRow (embed a la) (embed b lb)).2 :=
    congrArg (fun p : CNode × CNode => p.2) hcore
  calc projectRaw (spliceRow (sembed a la) (sembed b lb))
      = projectPair (commitRow (embed a la) (embed b lb)) := by
        unfold projectRaw projectPair
        rw [h1, h2]
    _ = captureRow a b := hraw

/-! ## commit-at-B installs the bridge and the returning snapshot -/

private theorem committedNow_iff (b b' : CNode) :
    committedNow b b' = true ↔ (b.leader = true ∧ b'.leader = false) := by
  unfold committedNow
  cases hb : b.leader <;> cases hb' : b'.leader <;> simp

/-- Commit-at-B clears only B's leader bit (imported), snapshots `B.cw`'s old
phase into the interior bridge, and hands the same snapshot to the returning
COMMITTED receipt.  Nothing else installs a bridge. -/
theorem commit_installs_bridge (a b : SNode) (hna : Neutral a) (hnb : Neutral b) :
    ((spliceRow a b).2.bridge = some (snapNode b.core.raw) ∧
      (spliceRow a b).2.splice = .bridged ∧
      (spliceRow a b).1.payload = some (snapNode b.core.raw)) ↔
      IsCommitLiteral (commitRule a.core b.core) := by
  have hrow := spliceRow_core a b hna hnb
  have hfall := (targetLeader_falls_iff_commit_literal a.core b.core).2
  constructor
  · intro h
    have hbridge : (spliceRow a b).2.bridge =
        (if committedNow b.core (commitRow a.core b.core).2 then
          some (snapNode b.core.raw) else b.bridge) := by
      rw [hrow]; rfl
    rw [hnb.1] at hbridge
    by_cases hc : committedNow b.core (commitRow a.core b.core).2 = true
    · exact hfall.mp ((committedNow_iff _ _).mp hc)
    · rw [if_neg hc] at hbridge
      rw [hbridge] at h
      exact absurd h.1 (by simp)
  · intro h
    have hc : committedNow b.core (commitRow a.core b.core).2 = true :=
      (committedNow_iff _ _).mpr (hfall.mpr h)
    refine ⟨?_, ?_, ?_⟩
    · rw [hrow]
      show (if committedNow b.core (commitRow a.core b.core).2 then
            some (snapNode b.core.raw) else b.bridge) = some (snapNode b.core.raw)
      rw [if_pos hc]
    · rw [hrow]
      show (if committedNow b.core (commitRow a.core b.core).2 then
            SpliceCtl.bridged else b.splice) = .bridged
      rw [if_pos hc]
    · rw [hrow]
      show (if committedNow b.core (commitRow a.core b.core).2 then
            some (snapNode b.core.raw)
            else if receiptMoved b.core (commitRow a.core b.core).1
              (commitRow a.core b.core).2 then b.payload else a.payload) =
          some (snapNode b.core.raw)
      rw [if_pos hc]


/-! ## OPEN item (ii): a stale `C.ccw` receipt is inert until consumed -/

private theorem ccwPort_setRawCcw_of_some (n : Node) (v w : CcwPort)
    (h : n.ccwPort = some w) : (setRawCcw n v).ccwPort = some v := by
  cases n with
  | root => rfl
  | interior => cases h

private theorem cwPort_setRawCw_ne (n : Node) (v w : CwPort) (hvw : v ≠ w) :
    (setRawCw n v).cwPort ≠ some w := by
  cases n with
  | root =>
      intro h
      exact hvw (Option.some.inj h)
  | interior =>
      intro h
      cases h

theorem splice_flush_dispatch (a b : SNode) (h : FreshFlush a b) :
    srun a b = { rule := .freshFlush, left := flushL a, right := flushR b,
                 valid := .freshFlush h } := by
  simp only [srun, dif_pos h]

/-- OPEN item (ii) of the local splice, as a row-level statement on this table.

If a fresh `A -> C` declaration meets a `C` whose `ccw` still holds the stale
`heldDenial` of the retired episode, then the *only* enabled row is the flush.
The flush overwrites that receipt by `free`, marks the declaration as flushed,
executes no core row, and writes no verdict, no leader bit, no lease and no
carrier.  Hence no comparison can ever read the stale denial: the first fresh
declaration consumes it first, and the flush cannot fire twice. -/
theorem stale_receipt_inert (a b : SNode) (h : FreshFlush a b) :
    spliceRule a b = .freshFlush ∧
    (∀ k : Rule, spliceRule a b ≠ .core k) ∧
    spliceRow a b = (flushL a, flushR b) ∧
    (spliceRow a b).2.core.raw.ccwPort = some .free ∧
    (spliceRow a b).2.core.raw.ccwPort ≠ some .heldDenial ∧
    (spliceRow a b).1.flush = .flushed ∧
    (spliceRow a b).1.core = a.core ∧
    (spliceRow a b).2.core.leader = b.core.leader ∧
    (spliceRow a b).2.core.incoming = b.core.incoming ∧
    (spliceRow a b).2.core.carrier = b.core.carrier ∧
    (spliceRow a b).2.core.raw.cwPort = b.core.raw.cwPort ∧
    ¬ FreshFlush (spliceRow a b).1 (spliceRow a b).2 := by
  have hd := splice_flush_dispatch a b h
  have hrule : spliceRule a b = .freshFlush := congrArg SResult.rule hd
  have hrow : spliceRow a b = (flushL a, flushR b) :=
    congrArg (fun r : SResult a b => (r.left, r.right)) hd
  have hccw : (flushR b).core.raw.ccwPort = some .free :=
    ccwPort_setRawCcw_of_some b.core.raw .free .heldDenial h.2.1
  refine ⟨hrule, ?_, hrow, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [hrule] at hk
    cases hk
  · rw [hrow]; exact hccw
  · rw [hrow]
    intro hbad
    rw [hccw] at hbad
    cases hbad
  · rw [hrow]; rfl
  · rw [hrow]; rfl
  · rw [hrow]; rfl
  · rw [hrow]; rfl
  · rw [hrow]; rfl
  · rw [hrow]
    show (setRawCcw b.core.raw .free).cwPort = b.core.raw.cwPort
    exact cwPort_setRawCcw _ _
  · rw [hrow]
    intro hbad
    have hx : DeclFlush.flushed = .unflushed := hbad.1
    cases hx

/-! ## Frames of the next gap and of the A-side verdict slots -/

def RetireRule : SRule -> Prop
  | .retireLaunch => True
  | .retireBackward => True
  | .retireDeposit => True
  | _ => False

/-- The retirement witness alphabet carries no verdict at all. -/
theorem witness_carries_no_verdict (w : RetireWitness) : w = .none ∨ w = .token := by
  cases w
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem step_raw_frame {a b x y : SNode} {k : SRule} (h : SRowStep a b k x y) :
    (RetireRule k -> x.core.raw = a.core.raw ∧ y.core.raw = b.core.raw) ∧
    (IsNew k = true -> k ≠ .freshFlush -> y.core.raw.ccwPort = b.core.raw.ccwPort) ∧
    (IsNew k = true -> x.core.raw.ccwPort = a.core.raw.ccwPort) ∧
    (IsNew k = true -> x.core.raw.cwPort = some .heldDenial ->
        a.core.raw.cwPort = some .heldDenial) ∧
    (IsNew k = true -> y.core.raw.cwPort = some .heldDenial ->
        b.core.raw.cwPort = some .heldDenial) := by
  cases h with
  | core =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hk; cases hk
      · intro hk; cases hk
      · intro hk; cases hk
      · intro hk; cases hk
      · intro hk; cases hk
  | freshFlush hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hk; cases hk
      · intro _ hne; exact absurd rfl hne
      · intro _; rfl
      · intro _ hx; exact hx
      · intro _ hx
        have hx' : (setRawCcw b.core.raw .free).cwPort = some .heldDenial := hx
        rwa [cwPort_setRawCcw] at hx' 
  | freshLaunch hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hk; cases hk
      · intro _ _
        show declRaw.ccwPort = b.core.raw.ccwPort
        rw [hg.2.2.2.1.1]
        rfl
      · intro _
        exact ccwPort_setRawCw a.core.raw .waiting
      · intro _ hx
        exact absurd hx (cwPort_setRawCw_ne a.core.raw .waiting .heldDenial (by simp))
      · intro _ hx
        cases hx
  | freshForward hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hk; cases hk
      · intro _ _
        show declRaw.ccwPort = b.core.raw.ccwPort
        rw [hg.2.2.1.1]
        rfl
      · intro _
        show emptyRaw.ccwPort = a.core.raw.ccwPort
        rw [hg.2.1]
        rfl
      · intro _ hx
        cases hx
      · intro _ hx
        cases hx
  | retireLaunch hg =>
      exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ => rfl, fun _ hx => hx, fun _ hx => hx⟩
  | retireBackward hg =>
      exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ => rfl, fun _ hx => hx, fun _ hx => hx⟩
  | retireDeposit hg =>
      exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ => rfl, fun _ hx => hx, fun _ hx => hx⟩
  | adoptDeposit hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hk; cases hk
      · intro _ _; rfl
      · intro _
        exact ccwPort_setRawCw a.core.raw (adoptCwOf b.payload)
      · intro _ hx
        exact absurd hx (cwPort_setRawCw_ne a.core.raw (adoptCwOf b.payload) .heldDenial
          (adoptCwOf_ne_denial b.payload))
      · intro _ hx; exact hx
  | directAdopt hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hk; cases hk
      · intro _ _; rfl
      · intro _
        exact ccwPort_setRawCw a.core.raw (adoptCwOf a.payload)
      · intro _ hx
        exact absurd hx (cwPort_setRawCw_ne a.core.raw (adoptCwOf a.payload) .heldDenial
          (adoptCwOf_ne_denial a.payload))
      · intro _ hx; exact hx
  | handoffArm hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hk; cases hk
      · intro _ _; rfl
      · intro _
        exact ccwPort_setRawCw a.core.raw .toSend
      · intro _ hx
        exact absurd hx (cwPort_setRawCw_ne a.core.raw .toSend .heldDenial (by simp))
      · intro _ hx; exact hx

private theorem step_guards {a b x y : SNode} {k : SRule} (h : SRowStep a b k x y) :
    (k = .freshFlush -> a.flush = .unflushed) ∧
    (k = .freshLaunch -> a.splice = .armed ∧ a.flush = .unflushed) ∧
    (k = .freshForward -> a.flush = .unflushed) ∧
    (k = .handoffArm -> a.splice = .retired) ∧
    (k = .retireDeposit -> a.splice = .adopted ∧ b.witness = .token) := by
  cases h with
  | core =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | freshFlush hg =>
      refine ⟨fun _ => hg.1, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | freshLaunch hg =>
      refine ⟨?_, fun _ => ⟨hg.1, hg.2.1⟩, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | freshForward hg =>
      refine ⟨?_, ?_, fun _ => hg.1, ?_, ?_⟩ <;> (intro hk; cases hk)
  | retireLaunch hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | retireBackward hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | retireDeposit hg =>
      refine ⟨?_, ?_, ?_, ?_, fun _ => ⟨hg.1, hg.2.2⟩⟩ <;> (intro hk; cases hk)
  | adoptDeposit hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | directAdopt hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | handoffArm hg =>
      refine ⟨?_, ?_, ?_, fun _ => hg.1, ?_⟩ <;> (intro hk; cases hk)


private theorem step_flush_created {a b x y : SNode} {k : SRule} (h : SRowStep a b k x y)
    (ha : a.flush = .none) (hb : b.flush = .none) :
    x.flush ≠ .none ∨ y.flush ≠ .none -> k = .handoffArm := by
  cases h with
  | core =>
      intro hx
      exfalso
      rcases hx with h1 | h1
      · exact h1 ha
      · exact h1 hb
  | freshFlush hg =>
      intro _
      exfalso
      have hz := hg.1
      rw [ha] at hz
      cases hz
  | freshLaunch hg =>
      intro _
      exfalso
      have hz := hg.2.1
      rw [ha] at hz
      cases hz
  | freshForward hg =>
      intro _
      exfalso
      have hz := hg.1
      rw [ha] at hz
      cases hz
  | retireLaunch hg =>
      intro hx
      exfalso
      rcases hx with h1 | h1
      · exact h1 ha
      · exact h1 hb
  | retireBackward hg =>
      intro hx
      exfalso
      rcases hx with h1 | h1
      · exact h1 ha
      · exact h1 hb
  | retireDeposit hg =>
      intro hx
      exfalso
      rcases hx with h1 | h1
      · exact h1 ha
      · exact h1 hb
  | adoptDeposit hg =>
      intro hx
      exfalso
      rcases hx with h1 | h1
      · exact h1 ha
      · exact h1 hb
  | directAdopt hg =>
      intro hx
      exfalso
      rcases hx with h1 | h1
      · exact h1 ha
      · exact h1 hb
  | handoffArm hg => intro _; rfl

private theorem step_retired_created {a b x y : SNode} {k : SRule} (h : SRowStep a b k x y)
    (ha : a.splice ≠ .retired) (hb : b.splice ≠ .retired) :
    x.splice = .retired ∨ y.splice = .retired -> k = .retireDeposit ∧ b.witness = .token := by
  cases h with
  | core =>
      intro hx
      exfalso
      rcases hx with h1 | h1
      · exact ha h1
      · have h2 : (if committedNow b.core (commitRow a.core b.core).2 then
            SpliceCtl.bridged else b.splice) = .retired := h1
        split at h2
        · cases h2
        · exact hb h2
  | freshFlush hg =>
      intro hx
      exfalso
      rcases hx with h1 | h1
      · exact ha h1
      · exact hb h1
  | freshLaunch hg =>
      intro hx
      exfalso
      rcases hx with h1 | h1
      · exact ha h1
      · exact hb h1
  | freshForward hg =>
      intro hx
      exfalso
      rcases hx with h1 | h1
      · exact ha h1
      · exact hb h1
  | retireLaunch hg =>
      intro hx
      exfalso
      rcases hx with h1 | h1
      · exact ha h1
      · have h2 : SpliceCtl.drained = .retired := h1
        cases h2
  | retireBackward hg =>
      intro hx
      exfalso
      rcases hx with h1 | h1
      · exact ha h1
      · exact hb h1
  | retireDeposit hg => intro _; exact ⟨rfl, hg.2.2⟩
  | adoptDeposit hg =>
      intro hx
      exfalso
      rcases hx with h1 | h1
      · have h2 : SpliceCtl.adopted = .retired := h1
        cases h2
      · exact hb h1
  | directAdopt hg =>
      intro hx
      exfalso
      rcases hx with h1 | h1
      · have h2 : SpliceCtl.adopted = .retired := h1
        cases h2
      · exact hb h1
  | handoffArm hg =>
      intro hx
      exfalso
      rcases hx with h1 | h1
      · have h2 : SpliceCtl.armed = .retired := h1
        cases h2
      · exact hb h1

/-- A fresh declaration mark is created only by the post-retirement handoff. -/
theorem unflushed_only_from_arm (a b : SNode) (ha : a.flush = .none) (hb : b.flush = .none)
    (h : (spliceRow a b).1.flush ≠ .none ∨ (spliceRow a b).2.flush ≠ .none) :
    spliceRule a b = .handoffArm :=
  step_flush_created (spliceRow_spec a b) ha hb h

/-- The `.retired` mark is created only by the arrival of a retirement witness. -/
theorem retired_only_from_witness (a b : SNode)
    (ha : a.splice ≠ .retired) (hb : b.splice ≠ .retired)
    (h : (spliceRow a b).1.splice = .retired ∨ (spliceRow a b).2.splice = .retired) :
    spliceRule a b = .retireDeposit ∧ b.witness = .token :=
  step_retired_created (spliceRow_spec a b) ha hb h

/-- The `(B,C)` side is framed by the splice.

1. Every retirement row frames the complete raw pair: the outstanding `(B,C)`
   traffic and `C.ccw` are untouched while the witness travels.
2. No new row except the flush writes the right endpoint's incoming selection
   port, so no `C.ccw` is written before the fresh episode exists.
3. The flush needs an unflushed fresh declaration; a fresh declaration mark is
   created only by `handoffArm`, which needs `.retired` at A; and `.retired` is
   created only by the arrival of the retirement witness.

Together: no `C.ccw` write and no new-lane raw write happens before the
retirement witness has arrived at A. -/
theorem splice_frames_next_gap (a b : SNode) :
    (RetireRule (spliceRule a b) ->
      (spliceRow a b).1.core.raw = a.core.raw ∧ (spliceRow a b).2.core.raw = b.core.raw) ∧
    (IsNew (spliceRule a b) = true -> spliceRule a b ≠ .freshFlush ->
      (spliceRow a b).2.core.raw.ccwPort = b.core.raw.ccwPort) ∧
    (spliceRule a b = .freshFlush -> a.flush = .unflushed) ∧
    (spliceRule a b = .freshLaunch -> a.splice = .armed ∧ a.flush = .unflushed) ∧
    (spliceRule a b = .freshForward -> a.flush = .unflushed) ∧
    (spliceRule a b = .handoffArm -> a.splice = .retired) ∧
    (spliceRule a b = .retireDeposit -> a.splice = .adopted ∧ b.witness = .token) := by
  have hf := step_raw_frame (spliceRow_spec a b)
  have hg := step_guards (spliceRow_spec a b)
  exact ⟨hf.1, hf.2.1, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2⟩

/-- No splice row turns an old `(B,C)` verdict into an A-side verdict.

The left endpoint's incoming port is framed by every new row, its outgoing
verdict slot is never *written* to `heldDenial` (the `adopt` write is
`toSend`/`waiting` by construction), and the retirement carrier has no verdict
payload to retag in the first place. -/
theorem splice_never_retags_denial (a b : SNode) (h : IsNew (spliceRule a b) = true) :
    ((spliceRow a b).1.core.raw.cwPort = some .heldDenial ->
        a.core.raw.cwPort = some .heldDenial) ∧
    ((spliceRow a b).2.core.raw.cwPort = some .heldDenial ->
        b.core.raw.cwPort = some .heldDenial) ∧
    (spliceRow a b).1.core.raw.ccwPort = a.core.raw.ccwPort ∧
    (∀ w : RetireWitness, w = .none ∨ w = .token) := by
  have hf := step_raw_frame (spliceRow_spec a b)
  exact ⟨hf.2.2.2.1 h, hf.2.2.2.2 h, hf.2.2.1 h, witness_carries_no_verdict⟩


/-! ## Why the whole-corridor repair fails, and the splice inequality -/

/-- The structural reserve of a live gap of positive length `l`. -/
def spanPot (n l : Nat) : Nat := n * (2 * l - 1)

/-- A commit that reruns a full `2*L-1` repair over the merged
corridor pays the whole new interval a second time.  The exact identity below
exhibits the surplus `2*n*(x+y-1)`, which no `O(n*x)` capture reserve and no
fixed multiple of the per-gap reserve can pay: hence there is no
`commit_merge_potential_le` for that architecture. -/
theorem commit_merge_deficit (n x y : Nat) (hx : 0 < x) (hy : 0 < y) :
    spanPot n (x + y) + spanPot n (x + y) =
      spanPot n x + spanPot n y + 2 * n + 2 * n * (x + y - 1) := by
  have hkey : (2 * (x + y) - 1) + (2 * (x + y) - 1) =
      ((2 * x - 1) + (2 * y - 1) + 2) + 2 * (x + y - 1) := by omega
  show n * (2 * (x + y) - 1) + n * (2 * (x + y) - 1) =
      n * (2 * x - 1) + n * (2 * y - 1) + 2 * n + 2 * n * (x + y - 1)
  rw [← Nat.mul_add, hkey, Nat.mul_add, Nat.mul_add, Nat.mul_add,
    ← Nat.mul_assoc n 2 (x + y - 1), Nat.mul_comm n 2]

theorem commit_merge_deficit_pos (n x y : Nat) (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) :
    0 < 2 * n * (x + y - 1) := by
  have h2 : 1 ≤ x + y - 1 := by omega
  have hstep : 2 * n * 1 ≤ 2 * n * (x + y - 1) :=
    Nat.mul_le_mul (Nat.le_refl (2 * n)) h2
  omega

/-- With a local splice the affected contribution is monotone.
`d` is the splice debt, `n*d` the transport it costs, and the deleted live root
releases exactly `2*n`. -/
theorem commit_splice_potential_le
    (n d rMerged rAB rBC capBefore capAfter liveBefore liveAfter : Nat)
    (hrestart : rMerged ≤ rAB + rBC + n * d + 2 * n)
    (hcapture : capAfter + n * d ≤ capBefore)
    (hlive : liveAfter + 1 = liveBefore) :
    rMerged + capAfter + 2 * n * liveAfter ≤
      rAB + rBC + capBefore + 2 * n * liveBefore := by
  subst hlive
  have hexp : 2 * n * (liveAfter + 1) = 2 * n * liveAfter + 2 * n := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [hexp]
  omega

/-! ## The splice tail: COMMITTED return over the `x-1` cells, then handoff -/

/-- Phases of the tail created by one commit on a capture corridor of physical
length `x`.  `convert` is the single bridge firing that turns the old `(B,C)`
reply into a retirement witness; `back j` is the COMMITTED receipt, carrying
that witness and the phase snapshot, `j` firings away from its deposit at A. -/
inductive TailPhase (x : Nat) where
  | convert (hx : 0 < x)
  | back (j : Nat) (hj : 1 ≤ j ∧ j ≤ x)
  | landed

namespace TailPhase

def debt {x : Nat} : TailPhase x -> Nat
  | .convert _ => x + 1
  | .back j _ => j
  | .landed => 0

def advanceEdge {x : Nat} : TailPhase x -> Option (Fin x)
  | .convert hx => some ⟨x - 1, by omega⟩
  | .back j hj => some ⟨j - 1, by omega⟩
  | .landed => none

def advance {x : Nat} : TailPhase x -> TailPhase x
  | .convert hx => .back x ⟨by omega, Nat.le_refl x⟩
  | .back j hj => if h : 2 ≤ j then .back (j - 1) ⟨by omega, by omega⟩ else .landed
  | .landed => .landed

theorem debt_advance {x : Nat} (s : TailPhase x) : s.advance.debt = s.debt - 1 := by
  cases s with
  | convert hx => simp [advance, debt]
  | back j hj =>
      simp only [advance]
      split <;> simp only [debt] <;> omega
  | landed => rfl

theorem advanceEdge_of_debt_pos {x : Nat} (s : TailPhase x) (h : 0 < s.debt) :
    ∃ a, s.advanceEdge = some a := by
  cases s with
  | convert hx => exact ⟨⟨x - 1, by omega⟩, rfl⟩
  | back j hj => exact ⟨⟨j - 1, by omega⟩, rfl⟩
  | landed => exact absurd h (by simp [debt])

theorem debt_eq_zero {x : Nat} (s : TailPhase x) (h : s.debt = 0) : s = .landed := by
  cases s with
  | convert hx => exact absurd h (by simp [debt])
  | back j hj => exact absurd h (by simp only [debt]; omega)
  | landed => rfl

def localStep {n x : Nat} (edgeAt : Fin x -> Fin n) (s : TailPhase x) (e : Fin n) :
    TailPhase x :=
  match s.advanceEdge with
  | some a => if edgeAt a = e then s.advance else s
  | none => s

theorem debt_localStep_le {n x : Nat} (edgeAt : Fin x -> Fin n) (s : TailPhase x)
    (e : Fin n) : (localStep edgeAt s e).debt ≤ s.debt := by
  unfold localStep
  split
  · split
    · rw [debt_advance]; omega
    · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem localStep_advance {n x : Nat} (edgeAt : Fin x -> Fin n) (s : TailPhase x)
    (a : Fin x) (ha : s.advanceEdge = some a) :
    localStep edgeAt s (edgeAt a) = s.advance := by
  simp [localStep, ha]

theorem debt_localStep_advance {n x : Nat} (edgeAt : Fin x -> Fin n) (s : TailPhase x)
    (a : Fin x) (ha : s.advanceEdge = some a) (hs : 0 < s.debt) :
    (localStep edgeAt s (edgeAt a)).debt + 1 = s.debt := by
  rw [localStep_advance edgeAt s a ha, debt_advance]
  omega

def iter {x : Nat} : Nat -> TailPhase x -> TailPhase x
  | 0, s => s
  | k + 1, s => iter k s.advance

theorem debt_iter {x : Nat} (k : Nat) (s : TailPhase x) :
    (iter k s).debt = s.debt - k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      show (iter k s.advance).debt = s.debt - (k + 1)
      rw [ih s.advance, debt_advance]
      omega

end TailPhase

/-- The transport a single commit creates, as a function of the capture
corridor length `x` alone: one bridge conversion, `x-1` COMMITTED-back cell
transfers, and the deposit at A.  The residual `(B,C)` travel is *not* here:
it stays charged to the old `(B,C)` debt. -/
def spliceDebt (x : Nat) : Nat := x + 1

def spliceTailConst : Nat := 1

/-- The exact splice debt, on the phase machine.  Nothing in the count refers
to the next gap's length `y`. -/
theorem commit_splice_debt {x : Nat} (hx : 0 < x) :
    (TailPhase.convert hx).debt = spliceDebt x ∧
    TailPhase.iter (spliceDebt x) (TailPhase.convert hx) = TailPhase.landed ∧
    (∀ k, k < spliceDebt x ->
      TailPhase.iter k (TailPhase.convert hx) ≠ TailPhase.landed) ∧
    (∀ (n : Nat) (edgeAt : Fin x -> Fin n) (s : TailPhase x) (e : Fin n),
      (TailPhase.localStep edgeAt s e).debt ≤ s.debt) ∧
    (∀ (n : Nat) (edgeAt : Fin x -> Fin n) (s : TailPhase x) (a : Fin x),
      s.advanceEdge = some a -> 0 < s.debt ->
        (TailPhase.localStep edgeAt s (edgeAt a)).debt + 1 = s.debt) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · apply TailPhase.debt_eq_zero
    rw [TailPhase.debt_iter]
    show x + 1 - spliceDebt x = 0
    unfold spliceDebt
    omega
  · intro k hk hbad
    have hd : (TailPhase.iter k (TailPhase.convert hx)).debt = x + 1 - k :=
      TailPhase.debt_iter k _
    rw [hbad] at hd
    unfold spliceDebt at hk
    have : (TailPhase.landed : TailPhase x).debt = 0 := rfl
    omega
  · intro n edgeAt s e
    exact TailPhase.debt_localStep_le edgeAt s e
  · intro n edgeAt s a ha hs
    exact TailPhase.debt_localStep_advance edgeAt s a ha hs

/-- The splice debt is a function of `x` only; the discarded whole-corridor
repair charges the merged length `x+y` instead. -/
theorem splice_debt_lt_merge_repair (n x y : Nat) (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) :
    n * spliceDebt x < spanPot n (x + y) := by
  have hle : x + 1 + 1 ≤ 2 * (x + y) - 1 := by omega
  have hmul : n * (x + 1 + 1) ≤ n * (2 * (x + y) - 1) :=
    Nat.mul_le_mul (Nat.le_refl n) hle
  have hexp : n * (x + 1 + 1) = n * (x + 1) + n := by
    rw [Nat.mul_add, Nat.mul_one]
  show n * (x + 1) < n * (2 * (x + y) - 1)
  omega


/-! ## Scale-one Bellman certificate of the splice tail -/

private theorem ofFn_sum_lt_of_single_lt
    {n : Nat} (f g : Fin n -> Nat) (chosen : Fin n)
    (hle : ∀ i, f i ≤ g i) (hlt : f chosen < g chosen) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 chosen
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      by_cases hzero : chosen = 0
      · subst chosen
        have htail := ofFn_sum_le
          (fun i : Fin n => f i.succ) (fun i => g i.succ)
          (fun i => hle i.succ)
        omega
      · have hpos : 0 < chosen.val := by
          have hne : chosen.val ≠ 0 :=
            fun h => hzero (Fin.ext (by simpa using h))
          omega
        let previous : Fin n := ⟨chosen.val - 1, by omega⟩
        have hsucc : previous.succ = chosen :=
          Fin.ext (by simp [previous]; omega)
        have htail := ih
          (fun i : Fin n => f i.succ) (fun i => g i.succ) previous
          (fun i => hle i.succ) (by simpa only [hsucc] using hlt)
        have hhead := hle 0
        omega

/-- An undischarged splice tail. -/
structure TailState (x : Nat) where
  phase : TailPhase x
  active : 0 < phase.debt

/-- The tail runs on the physical `n`-edge scheduler through the corridor's own
edge set; every edge other than the unique advancing edge stutters. -/
def spliceTailStep {n x : Nat} (edgeAt : Fin x -> Fin n) :
    TailState x -> Fin n -> StopNode (TailState x) :=
  fun s e =>
    if h : 0 < (TailPhase.localStep edgeAt s.phase e).debt then
      .active ⟨TailPhase.localStep edgeAt s.phase e, h⟩
    else .success

def spliceTailPotential (n : Nat) {x : Nat} : StopNode (TailState x) -> Nat
  | .active s => n * s.phase.debt
  | .success => 0
  | .failure => 0

private theorem tail_potential_step_le {n x : Nat} (edgeAt : Fin x -> Fin n)
    (s : TailState x) (e : Fin n) :
    spliceTailPotential n (spliceTailStep edgeAt s e) ≤
      n * (TailPhase.localStep edgeAt s.phase e).debt := by
  unfold spliceTailStep
  split <;> simp [spliceTailPotential]

private theorem tail_childSum {n x : Nat} (edgeAt : Fin x -> Fin n) (s : TailState x) :
    1 + (List.ofFn (fun e : Fin n =>
      (TailPhase.localStep edgeAt s.phase e).debt)).sum ≤ n * s.phase.debt := by
  obtain ⟨a, ha⟩ := TailPhase.advanceEdge_of_debt_pos s.phase s.active
  have hlt := TailPhase.debt_localStep_advance edgeAt s.phase a ha s.active
  have hsumlt := ofFn_sum_lt_of_single_lt
    (fun e : Fin n => (TailPhase.localStep edgeAt s.phase e).debt)
    (fun _ : Fin n => s.phase.debt) (edgeAt a)
    (fun e => TailPhase.debt_localStep_le edgeAt s.phase e)
    (by omega)
  rw [ofFn_sum_const] at hsumlt
  omega

/-- Scale one on the physical `n`-edge scheduler: the exact splice-tail debt is
charged `n` times, with one useful edge per live token. -/
theorem splice_bellman {n x : Nat} (edgeAt : Fin x -> Fin n) :
    NatBellmanSuperSolution (spliceTailStep edgeAt) 1 (spliceTailPotential n) := by
  refine ⟨rfl, rfl, ?_⟩
  intro s
  have hdebt := tail_childSum edgeAt s
  have hscaled := Nat.mul_le_mul_left n hdebt
  have hchildren :
      (List.ofFn (fun e : Fin n =>
        spliceTailPotential n (spliceTailStep edgeAt s e))).sum ≤
        n * (List.ofFn (fun e : Fin n =>
          (TailPhase.localStep edgeAt s.phase e).debt)).sum := by
    calc
      (List.ofFn (fun e : Fin n =>
          spliceTailPotential n (spliceTailStep edgeAt s e))).sum ≤
        (List.ofFn (fun e : Fin n =>
          n * (TailPhase.localStep edgeAt s.phase e).debt)).sum := by
            apply ofFn_sum_le
            intro e
            exact tail_potential_step_le edgeAt s e
      _ = n * (List.ofFn (fun e : Fin n =>
          (TailPhase.localStep edgeAt s.phase e).debt)).sum :=
        ofFn_sum_mul_left n _
  calc
    1 * n + (List.ofFn (fun e : Fin n =>
        spliceTailPotential n (spliceTailStep edgeAt s e))).sum ≤
      n + n * (List.ofFn (fun e : Fin n =>
        (TailPhase.localStep edgeAt s.phase e).debt)).sum := by
          simpa using Nat.add_le_add_left hchildren n
    _ = n * (1 + (List.ofFn (fun e : Fin n =>
        (TailPhase.localStep edgeAt s.phase e).debt)).sum) := by
      rw [Nat.mul_add, Nat.mul_one]
    _ ≤ n * (n * s.phase.debt) := hscaled
    _ = n * spliceTailPotential n (.active s) := rfl

theorem spliceTailStep_ne_failure {n x : Nat} (edgeAt : Fin x -> Fin n) :
    ∀ (s : TailState x) (e : Fin n), spliceTailStep edgeAt s e ≠ .failure := by
  intro s e
  unfold spliceTailStep
  split <;> simp

def spliceStart {x : Nat} (hx : 0 < x) : TailState x :=
  ⟨.convert hx, by show 0 < x + 1; omega⟩

theorem splice_start_potential {n x : Nat} (hx : 0 < x) :
    spliceTailPotential n (.active (spliceStart hx)) = n * (x + 1) := rfl

/-- Start potential of the splice tail: `n * (x + c)` with the explicit
constant `c = spliceTailConst = 1`. -/
theorem splice_start_potential_le {n x : Nat} (hx : 0 < x) :
    spliceTailPotential n (.active (spliceStart (x := x) hx)) ≤
      n * (x + spliceTailConst) := by
  rw [splice_start_potential]
  exact Nat.le_refl _

theorem splice_truncatedCost_le {n x : Nat} (edgeAt : Fin x -> Fin n) (hx : 0 < x)
    (T : Nat) :
    truncatedActiveCostNumerator (spliceTailStep edgeAt) (.active (spliceStart hx)) T ≤
      n ^ T * (n * (x + spliceTailConst)) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (spliceTailStep edgeAt) 1 (spliceTailPotential n) (splice_bellman edgeAt)
    (.active (spliceStart hx)) T
  have hstart : spliceTailPotential n (.active (spliceStart (x := x) hx)) =
      n * (x + spliceTailConst) := rfl
  rw [Nat.one_mul, hstart] at h
  exact h

/-- The local-splice commit inequality with the splice debt substituted. -/
theorem commit_splice_potential_le_of_spliceDebt
    (n x rMerged rAB rBC capBefore capAfter liveBefore liveAfter : Nat)
    (hrestart : rMerged ≤ rAB + rBC + n * spliceDebt x + 2 * n)
    (hcapture : capAfter + n * spliceDebt x ≤ capBefore)
    (hlive : liveAfter + 1 = liveBefore) :
    rMerged + capAfter + 2 * n * liveAfter ≤
      rAB + rBC + capBefore + 2 * n * liveBefore :=
  commit_splice_potential_le n (spliceDebt x) rMerged rAB rBC capBefore capAfter
    liveBefore liveAfter hrestart hcapture hlive


/-! ## Literal firings of the splice pipeline

Explicit node builders, and the actual pair firings of every new row.  These
are the positive half: the table is not vacuous, and the pipeline

  bridge conversion -> witness return -> retirement at A -> handoff ->
  fresh declaration -> stale-receipt flush

executes in exactly that order on literal states. -/

def sCell (carrier : CommitCarrier) (wit : RetireWitness) (fl : DeclFlush)
    (pay : Option SnapPhase) : SNode :=
  ⟨⟨emptyRaw, false, .capturing, .unreserved, carrier⟩, none, pay, .inactive, wit, fl⟩

def sBridge (cw : CwPort) (out : OutControl) (ctl : CommitCtl) (snap : SnapPhase) : SNode :=
  ⟨⟨.root .in0 cw .heldCandidate out .accepted, false, ctl, .committed, .none⟩,
    some snap, none, .bridged, .none, .none⟩

def sOwner (ccw : CcwPort) (inc : InControl) (ctl : CommitCtl) (lease : CommitIn)
    (live : Bool) : SNode :=
  ⟨ownerNode ccw inc ctl lease live, none, none, .inactive, .none, .none⟩

def sRootAt (cw : CwPort) (ccw : CcwPort) (inc : InControl) (ctl : CommitCtl)
    (lease : CommitIn) (sp : SpliceCtl) (fl : DeclFlush) : SNode :=
  ⟨⟨.root .out1 cw ccw .finalReady inc, false, ctl, lease, .none⟩,
    none, none, sp, .none, fl⟩

private theorem no_fresh_of_cell_none (b : SNode) (a : SNode)
    (ha : a.flush = .none) : ¬ FreshFlush a b := by
  intro h
  have hx := h.1
  rw [ha] at hx
  cases hx

private theorem no_fresh_forward_of_none (b : SNode) (a : SNode)
    (ha : a.flush = .none) : ¬ FreshForward a b := by
  intro h
  have hx := h.1
  rw [ha] at hx
  cases hx

private theorem no_fresh_launch_of_splice (b : SNode) (a : SNode) (v : SpliceCtl)
    (ha : a.splice = v) (hv : v ≠ .armed) : ¬ FreshLaunch a b := by
  intro h
  have hx := h.1
  rw [ha] at hx
  exact hv hx

/-- Step 4 of the local splice: the landed old `(B,C)` denial is converted at the bridge
into a retirement witness.  No verdict is produced and no raw field moves. -/
theorem splice_retire_launch (out : OutControl) (ctl : CommitCtl) (snap : SnapPhase) :
    spliceRow (sCell .none .none .none none) (sBridge .heldDenial out ctl snap) =
      (sCell .none .token .none none,
        ⟨⟨.root .in0 .heldDenial .heldCandidate out .accepted, false, ctl, .committed, .none⟩,
          some snap, none, .drained, .none, .none⟩) := by
  let a := sCell .none .none .none none
  let b := sBridge .heldDenial out ctl snap
  have h1 : ¬ FreshFlush a b := no_fresh_of_cell_none b a rfl
  have h2 : ¬ FreshLaunch a b := no_fresh_launch_of_splice b a .inactive rfl (by simp)
  have h3 : ¬ FreshForward a b := no_fresh_forward_of_none b a rfl
  have hg : RetireLaunch a b := ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
  have hr : srun a b =
      { rule := .retireLaunch, left := witnessL a, right := drainR b,
        valid := .retireLaunch hg } := by
    simp only [srun, dif_neg h1, dif_neg h2, dif_neg h3, dif_pos hg]
  exact congrArg (fun r : SResult a b => (r.left, r.right)) hr

/-- The witness travels one cell towards A over the cleaned short corridor. -/
theorem splice_retire_backward :
    spliceRow (sCell .none .none .none none) (sCell .none .token .none none) =
      (sCell .none .token .none none, sCell .none .none .none none) := by
  let a := sCell .none .none .none none
  let b := sCell .none .token .none none
  have h1 : ¬ FreshFlush a b := no_fresh_of_cell_none b a rfl
  have h2 : ¬ FreshLaunch a b := no_fresh_launch_of_splice b a .inactive rfl (by simp)
  have h3 : ¬ FreshForward a b := no_fresh_forward_of_none b a rfl
  have h4 : ¬ RetireLaunch a b := by
    intro h
    have hx : SpliceCtl.inactive = .bridged := h.2.2.1
    cases hx
  have hg : RetireBackward a b := ⟨⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl⟩
  have hr : srun a b =
      { rule := .retireBackward, left := witnessL a, right := clearWitnessR b,
        valid := .retireBackward hg } := by
    simp only [srun, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_pos hg]
  exact congrArg (fun r : SResult a b => (r.left, r.right)) hr

/-- Retirement lands at the adopted A.  Only the A-side lifecycle is written. -/
theorem splice_retire_deposit (cw : CwPort) (ccw : CcwPort) (inc : InControl)
    (ctl : CommitCtl) (lease : CommitIn) :
    spliceRow (sRootAt cw ccw inc ctl lease .adopted .none) (sCell .none .token .none none) =
      (sRootAt cw ccw inc ctl lease .retired .none, sCell .none .none .none none) := by
  let a := sRootAt cw ccw inc ctl lease .adopted .none
  let b := sCell .none .token .none none
  have h1 : ¬ FreshFlush a b := no_fresh_of_cell_none b a rfl
  have h2 : ¬ FreshLaunch a b := no_fresh_launch_of_splice b a .adopted rfl (by simp)
  have h3 : ¬ FreshForward a b := no_fresh_forward_of_none b a rfl
  have h4 : ¬ RetireLaunch a b := by
    intro h
    have hx : SpliceCtl.inactive = .bridged := h.2.2.1
    cases hx
  have h5 : ¬ RetireBackward a b := by
    intro h
    have hx : (Node.root .out1 cw ccw .finalReady inc) = emptyRaw := h.1.1
    cases hx
  have hg : RetireDeposit a b := ⟨rfl, ⟨rfl, rfl⟩, rfl⟩
  have hr : srun a b =
      { rule := .retireDeposit, left := retiredL a, right := clearWitnessR b,
        valid := .retireDeposit hg } := by
    simp only [srun, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5, dif_pos hg]
  exact congrArg (fun r : SResult a b => (r.left, r.right)) hr

/-- Step 3 of the local splice: deposit-at-A overwrites `A.cw = heldCandidate` by
`adopt` of the transported snapshot.  A settled old `(B,C)` verdict, denial or
candidate, becomes `waiting` -- never an A-side verdict. -/
theorem splice_adopt_deposit (ccw : CcwPort) (inc : InControl) (lease : CommitIn)
    (live : Bool) (snap : SnapPhase) :
    spliceRow (sOwner ccw inc .committing lease live) (sCell .committedBack .none .none (some snap)) =
      (⟨⟨.root .out1 (adoptCw snap) ccw .finalReady inc, live, .committedReceived, lease, .none⟩,
         none, none, .adopted, .none, .none⟩,
       sCell .none .none .none none) := by
  let a := sOwner ccw inc .committing lease live
  let b := sCell .committedBack .none .none (some snap)
  have h1 : ¬ FreshFlush a b := no_fresh_of_cell_none b a rfl
  have h2 : ¬ FreshLaunch a b := no_fresh_launch_of_splice b a .inactive rfl (by simp)
  have h3 : ¬ FreshForward a b := no_fresh_forward_of_none b a rfl
  have hroot : (Node.root .out1 .heldCandidate ccw .finalReady inc) ≠ emptyRaw := by
    intro h; cases h
  have h4 : ¬ RetireLaunch a b := fun h => hroot h.1.1
  have h5 : ¬ RetireBackward a b := fun h => hroot h.1.1
  have h6 : ¬ RetireDeposit a b := by
    intro h
    have hx : SpliceCtl.inactive = .adopted := h.1
    cases hx
  have hg : AdoptDeposit a b := ⟨⟨⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩⟩, (by intro hz; cases hz), rfl⟩
  have hr : srun a b =
      { rule := .adoptDeposit, left := adoptL a b.payload, right := adoptR b,
        valid := .adoptDeposit hg } := by
    simp only [srun, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5,
      dif_neg h6, dif_pos hg]
  exact congrArg (fun r : SResult a b => (r.left, r.right)) hr

/-- Step 5 of the local splice: after retirement `A.cw := toSend`, and the fresh
episode is marked unflushed. -/
theorem splice_handoff_arm (cw : CwPort) (ccw : CcwPort) (inc : InControl)
    (ctl : CommitCtl) (lease : CommitIn) :
    spliceRow (sRootAt cw ccw inc ctl lease .retired .none) (sCell .none .none .none none) =
      (sRootAt .toSend ccw inc ctl lease .armed .unflushed, sCell .none .none .none none) := by
  let a := sRootAt cw ccw inc ctl lease .retired .none
  let b := sCell .none .none .none none
  have h1 : ¬ FreshFlush a b := no_fresh_of_cell_none b a rfl
  have h2 : ¬ FreshLaunch a b := no_fresh_launch_of_splice b a .retired rfl (by simp)
  have h3 : ¬ FreshForward a b := no_fresh_forward_of_none b a rfl
  have hroot : (Node.root .out1 cw ccw .finalReady inc) ≠ emptyRaw := by
    intro h; cases h
  have h4 : ¬ RetireLaunch a b := fun h => hroot h.1.1
  have h5 : ¬ RetireBackward a b := fun h => hroot h.1.1
  have h6 : ¬ RetireDeposit a b := by
    intro h
    have hx : SpliceCtl.retired = .adopted := h.1
    cases hx
  have h7 : ¬ AdoptDeposit a b := by
    intro h
    exact h.2.1 rfl
  have h8 : ¬ DirectAdopt a := by
    intro h
    have hx : SpliceCtl.retired = .inactive := h.1
    cases hx
  have hg : HandoffArm a := ⟨rfl, (by intro hz; cases hz)⟩
  have hr : srun a b =
      { rule := .handoffArm, left := armL a, right := b, valid := .handoffArm hg } := by
    simp only [srun, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5,
      dif_neg h6, dif_neg h7, dif_neg h8, dif_pos hg]
  exact congrArg (fun r : SResult a b => (r.left, r.right)) hr

/-- The armed A emits the fresh declaration, which carries the unflushed mark. -/
theorem splice_fresh_launch (ccw : CcwPort) (inc : InControl) (ctl : CommitCtl)
    (lease : CommitIn) :
    spliceRow (sRootAt .toSend ccw inc ctl lease .armed .unflushed)
        (sCell .none .none .none none) =
      (sRootAt .waiting ccw inc ctl lease .armed .none,
        ⟨⟨declRaw, false, .capturing, .unreserved, .none⟩, none, none, .inactive,
          .none, .unflushed⟩) := by
  let a := sRootAt .toSend ccw inc ctl lease .armed .unflushed
  let b := sCell .none .none .none none
  have h1 : ¬ FreshFlush a b := by
    intro h
    have hx : (none : Option CcwPort) = some .heldDenial := h.2.1
    cases hx
  have hg : FreshLaunch a b := ⟨rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl⟩
  have hr : srun a b =
      { rule := .freshLaunch, left := launchL a, right := declR b,
        valid := .freshLaunch hg } := by
    simp only [srun, dif_neg h1, dif_pos hg]
  exact congrArg (fun r : SResult a b => (r.left, r.right)) hr

/-- The fresh declaration keeps its unflushed mark while it walks. -/
theorem splice_fresh_forward :
    spliceRow ⟨⟨declRaw, false, .capturing, .unreserved, .none⟩, none, none, .inactive,
        .none, .unflushed⟩ (sCell .none .none .none none) =
      (sCell .none .none .none none,
        ⟨⟨declRaw, false, .capturing, .unreserved, .none⟩, none, none, .inactive,
          .none, .unflushed⟩) := by
  let a : SNode := ⟨⟨declRaw, false, .capturing, .unreserved, .none⟩, none, none, .inactive,
    .none, .unflushed⟩
  let b := sCell .none .none .none none
  have h1 : ¬ FreshFlush a b := by
    intro h
    have hx : (none : Option CcwPort) = some .heldDenial := h.2.1
    cases hx
  have h2 : ¬ FreshLaunch a b := by
    intro h
    have hx : (none : Option CwPort) = some .toSend := h.2.2.1
    cases hx
  have hg : FreshForward a b := ⟨rfl, rfl, ⟨rfl, rfl⟩, rfl⟩
  have hr : srun a b =
      { rule := .freshForward, left := fwdL a, right := declR b,
        valid := .freshForward hg } := by
    simp only [srun, dif_neg h1, dif_neg h2, dif_pos hg]
  exact congrArg (fun r : SResult a b => (r.left, r.right)) hr

/-- The literal flush at a `C` whose `ccw` still holds the stale denial. -/
theorem splice_fresh_flush (ch : Choice) (cw : CwPort) (out : OutControl) (inc : InControl)
    (live : Bool) (ctl : CommitCtl) (lease : CommitIn) (carrier : CommitCarrier) :
    spliceRow ⟨⟨declRaw, false, .capturing, .unreserved, .none⟩, none, none, .inactive,
        .none, .unflushed⟩
        ⟨⟨.root ch cw .heldDenial out inc, live, ctl, lease, carrier⟩, none, none,
          .inactive, .none, .none⟩ =
      (⟨⟨declRaw, false, .capturing, .unreserved, .none⟩, none, none, .inactive,
          .none, .flushed⟩,
        ⟨⟨.root ch cw .free out inc, live, ctl, lease, carrier⟩, none, none,
          .inactive, .none, .none⟩) := by
  let a : SNode := ⟨⟨declRaw, false, .capturing, .unreserved, .none⟩, none, none, .inactive,
    .none, .unflushed⟩
  let b : SNode := ⟨⟨.root ch cw .heldDenial out inc, live, ctl, lease, carrier⟩, none, none,
    .inactive, .none, .none⟩
  have hg : FreshFlush a b := ⟨rfl, rfl, rfl⟩
  exact (stale_receipt_inert a b hg).2.2.1


/-! ## The bridge conversion happens at most once per commit -/

private theorem step_witness {a b x y : SNode} {k : SRule} (h : SRowStep a b k x y) :
    (k = .retireLaunch ->
      x.witness = .token ∧ y.witness = .none ∧ y.splice = .drained) ∧
    (k = .retireBackward -> x.witness = .token ∧ y.witness = .none) ∧
    (k = .retireDeposit -> y.witness = .none) := by
  cases h with
  | core =>
      refine ⟨?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | freshFlush hg =>
      refine ⟨?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | freshLaunch hg =>
      refine ⟨?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | freshForward hg =>
      refine ⟨?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | retireLaunch hg =>
      refine ⟨fun _ => ⟨rfl, hg.2.2.2.2.2, rfl⟩, ?_, ?_⟩ <;> (intro hk; cases hk)
  | retireBackward hg =>
      refine ⟨?_, fun _ => ⟨rfl, rfl⟩, ?_⟩ <;> (intro hk; cases hk)
  | retireDeposit hg =>
      refine ⟨?_, ?_, fun _ => rfl⟩ <;> (intro hk; cases hk)
  | adoptDeposit hg =>
      refine ⟨?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | directAdopt hg =>
      refine ⟨?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | handoffArm hg =>
      refine ⟨?_, ?_, ?_⟩ <;> (intro hk; cases hk)

/-- Exactly one retirement witness exists per commit, and it is never
duplicated: the conversion row spends the bridge (`bridged -> drained`) and so
cannot fire twice, while every transport row clears the source cell.  This is
the `O(1)` half of `spliceDebt`; the `x` half is the return walk. -/
theorem retire_witness_conservation (a b : SNode) :
    (spliceRule a b = .retireLaunch ->
      (spliceRow a b).1.witness = .token ∧ (spliceRow a b).2.witness = .none ∧
        (spliceRow a b).2.splice = .drained ∧
        ¬ RetireLaunch (spliceRow a b).1 (spliceRow a b).2) ∧
    (spliceRule a b = .retireBackward ->
      (spliceRow a b).1.witness = .token ∧ (spliceRow a b).2.witness = .none) ∧
    (spliceRule a b = .retireDeposit -> (spliceRow a b).2.witness = .none) := by
  have hw := step_witness (spliceRow_spec a b)
  refine ⟨?_, hw.2.1, hw.2.2⟩
  intro hk
  obtain ⟨h1, h2, h3⟩ := hw.1 hk
  refine ⟨h1, h2, h3, ?_⟩
  intro hbad
  have hx := hbad.2.2.1
  rw [h3] at hx
  cases hx

#print axioms retire_witness_conservation
#print axioms spliceRow_agrees_commitRow
#print axioms spliceRow_agrees_captureRow
#print axioms commit_installs_bridge
#print axioms stale_receipt_inert
#print axioms splice_frames_next_gap
#print axioms splice_never_retags_denial
#print axioms unflushed_only_from_arm
#print axioms retired_only_from_witness
#print axioms commit_splice_debt
#print axioms commit_merge_deficit
#print axioms commit_merge_deficit_pos
#print axioms commit_splice_potential_le
#print axioms commit_splice_potential_le_of_spliceDebt
#print axioms splice_debt_lt_merge_repair
#print axioms splice_bellman
#print axioms splice_start_potential_le
#print axioms splice_truncatedCost_le
#print axioms spliceTailStep_ne_failure
#print axioms splice_retire_launch
#print axioms splice_retire_backward
#print axioms splice_retire_deposit
#print axioms splice_adopt_deposit
#print axioms splice_handoff_arm
#print axioms splice_fresh_launch
#print axioms splice_fresh_forward
#print axioms splice_fresh_flush

end ShortGapSpliceCommit
