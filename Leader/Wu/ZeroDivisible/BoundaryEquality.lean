import Leader.Wu.Comparison.PostElectionCheckGuard

/-! Frozen BEQ round-1 definitions. Only the namespace is changed.
This preserves the R2 transition semantics while current APIs evolve. -/

/-!
# Boundary comparison with equality births (board G6.2)

Design input for the closure census; no proof content, no existing module is
edited.  The pipeline restates `PPLLPostElectionGuard.pipeline` with the
COMPARE stage (Algorithms 6-8, thesis pp.22-24) and the token part of SIGMOVE
(Algorithm 10 lines 7-27, p.25) replaced by the mechanism below, and CHECK's
ready assignment (Algorithm 11 line 2) additionally refusing the three wave
states.  Everything is expressed in the fields Algorithm 1 declares; the
census carrier is unchanged.

## The mechanism (BEQ = boundary equality)

1. **No `congest` at the head.**  CMP_UPDATE line 1 (`l.label = 0 →
   l.state ← congest`) is removed.  A generated signal keeps the `depart`
   that GENSIG wrote on its cells, so CHECK line 2 never readies it in place:
   ERRATA T9's in-place self-check disappears without a moved bit, because the
   thesis's own "at source" marker (`depart`) is no longer erased.
2. **The comparison starts at the boundary.**  On an edge whose initiator holds
   the tail `s_{ψ-1}` of a waiting signal S (`depart`, or itself locked) and
   whose responder holds the head `s'_0` of a waiting signal S' (`depart`), the
   head is put into `lock`.  The lock is propagated along S' by *sub-signal*
   index (`r.path[1] = l.path[1] + 1`), the last sub-signal answers `compare1`,
   the answer is propagated back to the head, and the boundary edge then marks
   the tail of S `compare2` and emits the comparison token of Algorithm 8.
   A lock is kept only while its locker is adjacent (the tail of S for the head
   of S', the previous locked sub-signal otherwise) and while the next
   sub-signal of S' is adjacent; otherwise the cell returns to `depart`.  A
   `compare2` tail whose head-ahead is no longer locked returns to `depart`.
   This is the T18 repair in a form that never writes onto S's own cells except
   its tail, so `depart` on the head survives every comparison.
3. **Equality creates a leader.**  Algorithm 8's final branch ("all bits equal:
   eliminate S", line 7-8) becomes `r.leader ← 1` at the last sub-signal of S'.
   Two adjacent complete signals with equal IDs witness an imperfection
   (thesis p.15 definition): S has passed every group between its source and
   the group of S' without being eliminated, so no greater ID or leader lies
   between two equal groups.  On the one-group ring n = ψ the tail of S is
   adjacent to its own head, S locks itself, compares equal with itself, and a
   leader is born: the ring-size case p.15 counts as an imperfection but the
   printed algorithms never resolve.  A covering argument shows this rule is
   forced: any local rule creating a leader on the ψ-ring from the
   fresh-signal state also fires on the 2ψ-ring with two identical fresh
   groups, so it must compare the two IDs, i.e. it is a boundary comparison
   whose equal case is a birth.
4. **Tokens never overwrite and are consumed at their destination.**  The
   Algorithm-8/10 control tokens (`path2`) queue when moving in the same
   direction, swap when moving in opposite directions, and a token on its
   destination cell (position 0 for actions 1/2, label ψ-1 for 3/4/5, label 0
   for 6) does not move before it is applied (completes the ERRATA T29 repair,
   whose `consume` half only clears an applied token).  Forward tokens carry
   the sub-signal bit of S (`l.path[2]`, read at the source side) and compare
   it with the agent bit `r.bit` of S' (Algorithm 8 line 2), on a locked cell
   whose sub-signal index matches the token's label.  (v2 compared with the
   sub-signal bit held on S'; a mixed or forged carrier on S' could then match
   itself.)  Stale `equal` next to a `depart` sub-signal is turned back into
   `depart` (Algorithm 10 lines 28-30 extended from `CHECK_ready` to `equal`).

Optional `detect` gate (from P_PL's barometer): both
birth rules also require `r.count = κ` at the terminal cell of the group that
elects, i.e. the group has not been reset since its counter last filled.  In a
leaderless ring the saturated counter never leaves κ (`waitSaturated`), so the
gate is inert there; with a leader it is the `CGC` gate of the guard census.

Variants `fab<wall><detect><elim>`: wall `W` = probe wall + leader wall + reset
kill before and after CHECK (the guard census's `Wall`), `LW` = leader wall
only, `N` = none; detect `D`/`-`; elim `K4`/`K2`.  `fabWNoEqK4` is the control
with the thesis's equal outcome (eliminate S) instead of a birth.
-/

set_option autoImplicit false

namespace PPLLFableDesignR1

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLElimVariants PPLLPostElectionGuard

def waveState (s : MainState) : Bool :=
  match s with
  | .lock | .compare1 | .compare2 => true
  | _ => false

def lockedState (s : MainState) : Bool :=
  match s with
  | .lock | .compare1 => true
  | _ => false

/-- States of a tail that may lock the head ahead of it and start a comparison. -/
def lockerState (s : MainState) : Bool :=
  match s with
  | .depart | .lock | .compare1 | .compare2 => true
  | _ => false

/-! ## Lock maintenance, boundary lock, propagation, acknowledgement, emission -/

/-- Release rules (run on every edge, before the wave rules). -/
def maintain {ψ : Nat} (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let last := ψ - 1
  let r := match r.path with
    | .bot => if lockedState r.state then { r with state := .none } else r
    | .some rl _ =>
      if lockedState r.state then
        let ok : Bool := match l.path with
          | .some ll _ =>
            decide (ll = (rl + ψ - 1) % ψ) &&
              (if rl = 0 then lockerState l.state else lockedState l.state)
          | .bot => false
        if ok then r else { r with state := .depart }
      else r
  let l := match l.path with
    | .bot => if waveState l.state then { l with state := .none } else l
    | .some ll _ =>
      if lockedState l.state then
        if ll = last then l else
        let ok : Bool := match r.path with
          | .some rl _ => decide (rl = ll + 1) && (decide (r.state = .depart) || waveState r.state)
          | .bot => false
        if ok then l else { l with state := .depart }
      else if l.state = .compare2 then
        if ll ≠ last then { l with state := .none } else
        match r.path with
        | .some rl _ => if rl = 0 ∧ lockedState r.state then l else { l with state := .depart }
        | .bot => l
      else l
  (l, r)

/-- Boundary lock, lock propagation, acknowledgement and token emission. -/
def wave {ψ : Nat} (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let last := ψ - 1
  match l.path, r.path with
  | .some ll _, .some rl _ =>
    let r := if ll = last ∧ rl = 0 ∧ r.state = .depart ∧ lockerState l.state then
      { r with state := .lock } else r
    let r := if l.state = .lock ∧ rl = ll + 1 ∧ r.state = .depart then
      { r with state := if rl = last then .compare1 else .lock } else r
    let l := if r.state = .compare1 ∧ rl = ll + 1 ∧ l.state = .lock then
      { l with state := .compare1 } else l
    let l := if ll = last ∧ rl = 0 ∧ r.state = .compare1 ∧
        (l.state = .depart ∨ lockedState l.state) then
      { l with state := .compare2, path2 := some ⟨0, 0, ψ - 1, 2⟩ } else l
    -- re-emission: an emitted tail facing an acknowledged head with no token on
    -- either boundary cell starts the comparison again (duplicates are idempotent)
    let l := if ll = last ∧ rl = 0 ∧ r.state = .compare1 ∧ l.state = .compare2 ∧
        l.path2 = none ∧ r.path2 = none then
      { l with path2 := some ⟨0, 0, ψ - 1, 2⟩ } else l
    (l, r)
  | _, _ => (l, r)

/-! ## Token comparison (Algorithm 8 on sub-signal bits) -/

/-- Forward token at position 0 on the responder: compare, decide, or drop. -/
def landForward {ψ : Nat} (κ : Nat) (detect eqBirth : Bool) (r : AgentState ψ) : AgentState ψ :=
  match r.path2, r.path with
  | some t, .some rl _ =>
    -- v3: compare with the agent's own ID bit (Algorithm 8 line 2, `r.bit`),
    -- not the bit of whatever sub-signal the cell holds: a forged or mixed
    -- carrier on S' then cannot fake an equality with the ID of S'.
    let rb : Nat := if r.bit then 1 else 0
    if t.action = 1 ∧ t.position = 0 then
      if t.label = rl ∧ waveState r.state then
        if t.bit = rb then
          if rl = ψ - 1 then
            if eqBirth ∧ (!detect || decide (r.count = κ)) then
              { r with leader := true, path2 := none }
            else { r with path2 := some ⟨0, 0, 0, 3⟩ }
          else { r with path2 := some ⟨rl + 1, 0, ψ - 1, 2⟩ }
        else if t.bit > rb then { r with path2 := some ⟨0, 0, 0, 4⟩ }
        else { r with path2 := some ⟨0, 0, 0, 3⟩ }
      else { r with path2 := none }
    else r
  | some t, .bot => if t.action = 1 ∧ t.position = 0 then { r with path2 := none } else r
  | none, _ => r

/-- Backward token at position 0 on the initiator: emit the next forward token. -/
def landBackward {ψ : Nat} (l : AgentState ψ) : AgentState ψ :=
  match l.path2, l.path with
  | some t, .some ll lb =>
    if t.action = 2 ∧ t.position = 0 then
      if t.label = ll then { l with path2 := some ⟨ll, lb, ψ, 1⟩ }
      else { l with path2 := none }
    else l
  | some t, .bot => if t.action = 2 ∧ t.position = 0 then { l with path2 := none } else l
  | none, _ => l

/-- Stray position-0 tokens on the wrong side are dropped. -/
def dropStray {ψ : Nat} (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let l := match l.path2 with
    | some t => if t.action = 1 ∧ t.position = 0 then { l with path2 := none } else l
    | none => l
  let r := match r.path2 with
    | some t => if t.action = 2 ∧ t.position = 0 then { r with path2 := none } else r
    | none => r
  (l, r)

/-- The COMPARE stage: Algorithm 6 line 1-2, then the rules above. -/
def compareSigF {ψ : Nat} (κ : Nat) (detect eqBirth : Bool) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := compareSigInit l
  let (l, r) := maintain l r
  let (l, r) := wave l r
  let (l, r) := dropStray l r
  (landBackward l, landForward κ detect eqBirth r)

/-! ## SIGMOVE with queueing, swapping, destination-anchored tokens -/

def rightward (t : Path2Info) : Bool := t.action = 1 ∨ t.action = 4 ∨ t.action = 5
def leftward (t : Path2Info) : Bool := t.action = 2 ∨ t.action = 3 ∨ t.action = 6

/-- A token leaves a cell only if the cell is not its destination. -/
def canMoveR {ψ : Nat} (u : AgentState ψ) (t : Path2Info) : Bool :=
  (t.action = 1 && t.position != 0) ||
  ((t.action = 4 || t.action = 5) && u.label.val != ψ - 1)

def canMoveL {ψ : Nat} (u : AgentState ψ) (t : Path2Info) : Bool :=
  (t.action = 2 && t.position != 0) ||
  (t.action = 3 && u.label.val != ψ - 1) ||
  (t.action = 6 && u.label.val != 0)

def dec (t : Path2Info) : Path2Info :=
  if t.action = 1 ∨ t.action = 2 then { t with position := t.position - 1 } else t

/-- Two tokens on one edge: opposite directions swap; a token blocked behind a
same-direction token still in transit is dropped (the boundary re-emits a lost
comparison token, `wave`); a token blocked behind one on its destination waits
for that one to be applied in this interaction. -/
def moveTokens {ψ : Nat} (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  match l.path2, r.path2 with
  | some tl, some tr =>
    if canMoveR l tl ∧ canMoveL r tr then
      ({ l with path2 := some (dec tr) }, { r with path2 := some (dec tl) })
    else if canMoveR l tl ∧ rightward tr ∧ canMoveR r tr then
      ({ l with path2 := none }, r)
    else if canMoveL r tr ∧ leftward tl ∧ canMoveL l tl then
      (l, { r with path2 := none })
    else (l, r)
  | some tl, none =>
    if canMoveR l tl then ({ l with path2 := none }, { r with path2 := some (dec tl) })
    else (l, r)
  | none, some tr =>
    if canMoveL r tr then ({ l with path2 := some (dec tr) }, { r with path2 := none })
    else (l, r)
  | none, none => (l, r)

/-- SIGMOVE: the leader-wall preclear and wall of `sigMoveWalled` (when `wall`),
step 1 with the M2 blocking rule, token movement, control application
(consuming), Algorithm 10 lines 28-30. -/
def sigMoveF {ψ : Nat} (hψ : ψ > 0) (wall : Bool) (m : M2) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let nextLabel : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let l := if wall ∧ (l.leader = true ∨ (r.leader = true ∧ r.label ≠ nextLabel)) then
    clearCmp l else l
  let r := if wall ∧ r.leader = true then clearCmp r else r
  let (l, r) := sigMoveStep1With m l r
  let (l, r) := moveTokens l r
  let (l, r) := if wall then leaderWall l r else (l, r)
  let l := sigMoveApplyControlConsume hψ l
  let r := sigMoveApplyControlConsume hψ r
  let l := if r.state = MainState.depart then
    if l.label.val < ψ - 1 ∧ l.state = MainState.CHECK_ready then
      { l with state := MainState.depart }
    else l
  else l
  (l, r)

/-! ## CHECK with the wave states excluded from readiness -/

def readyF {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  if waveState u.state ∨ u.state = .congest then u else checkSigSetReadyGuarded u

def checkSigF {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (detect : Bool) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := readyF l
  let r := readyF r
  -- v3: Algorithm 10 lines 28-30 extended to a decided `equal`: while the
  -- responder's sub-signal is still `depart` (at source), the initiator's
  -- half of the group is at source too and is never checked.  (v2 instead
  -- readied the `depart` half after a stale `equal`, which is an in-place
  -- self-check of the group's own sub-signal: 41 births in the fresh clean
  -- n = 4 closure, class 1333366.)
  let l := if r.state = .depart ∧ aligned r ∧ l.state = .equal ∧ aligned l ∧
      l.label.val < ψ - 1 then { l with state := .depart } else l
  let l := checkSigCheckL hψ l
  let r := checkSigCheckR hψ l r
  let l := checkSigSetResult l
  let r := checkSigSetResult r
  if r.label = ⟨ψ - 1, by omega⟩ ∧ r.state = .equal then
    if !detect || decide (r.count = κ) then (l, { r with leader := true })
    else (clearCmp l, clearCmp r)
  else (l, r)

/-! ## Pipeline -/

inductive WallV where
  | none | leaderOnly | full
  deriving DecidableEq

structure Cfg where
  wall : WallV := .full
  detect : Bool := false
  eqBirth : Bool := true
  elim : ElimG := .k4

def pipeline {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : Cfg) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let full : Bool := decide (c.wall = .full)
  let lw : Bool := decide (c.wall ≠ .none)
  let q := if full then pPsiProbeWall hψ l r else pPsi hψ l r
  let q := genSigSaturated hψ κ q.1 q.2
  let q := cleanSig hψ q.1 q.2
  let q := eliminateSig hψ q.1 q.2
  let q := sigMoveF hψ lw .dropMisaligned q.1 q.2
  let q := (dropStale q.1, dropStale q.2)
  let q := if full then preCheckReset q.1 q.2 else q
  let q := checkSigF hψ κ c.detect q.1 q.2
  let q := disappear hψ q.1 q.2
  let q := compareSigF κ c.detect c.eqBirth q.1 q.2
  let q := if full then suppressSigResetKill hψ q.1 q.2 else suppressSig hψ q.1 q.2
  let q := elimG hψ c.elim q.1 q.2
  writeSeq hψ q.1 q.2

def variants : List (String × Cfg) :=
  [ ("fabWK4", {})
  , ("fabWK2", { elim := .base .k2 })
  , ("fabWDK4", { detect := true })
  , ("fabLWK4", { wall := .leaderOnly })
  , ("fabNK4", { wall := .none })
  , ("fabNDK4", { wall := .none, detect := true })
  , ("fabWNoEqK4", { eqBirth := false }) ]

def run {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : Cfg) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  pipeline hψ κ c l r

end PPLLFableDesignR1
