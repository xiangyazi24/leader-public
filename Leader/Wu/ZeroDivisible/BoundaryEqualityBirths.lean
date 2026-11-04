import Leader.Wu.Comparison.PostElectionCheckGuard

/-!
# Boundary comparison with equality births (board G6.2 design)

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

## Round 2 (`fab2…`, switches `elimSafe`, `roundTrip`, `srcBlock`)

* `elimSafe`: every newborn leader is shielded (`shieldNew`) and Algorithm 16's
  migration carries the shield (`migrateShield`); see the section
  "Elimination safety" below for the sector Σ this protects.
* `roundTrip`: the terminal equality does not create the leader at the last
  cell of S'; it sends a birth request (backward token with bit 1) to the
  head of S', and the boundary edge creates the leader at the head only while
  the tail of S is still `compare2` with its carrier present.  A comparison
  whose source was rewritten or cleared while the token was in flight (the
  72 token-in-flight births of the round-1 clean closures) then dies with its
  lock chain.
* `srcBlock` (ψ > 2): `produce`/`done` cells are at source: CHECK never readies
  them and SIGMOVE never moves their sub-signal (Algorithm 4's reverse wave
  completes before anything departs).
* `prodHold` (ψ > 2): Algorithm 6 lines 1-2 (`compareSigInit`) reset every
  pathless initiator to `none`.  For ψ = 2 the head of a group always holds a
  sub-signal by the time COMPARE runs (Algorithm 4 completes on one edge); for
  ψ > 2 the head is pathless in `produce` while its forward wave runs, and the
  printed COMPARE erases it on the same interaction (ψ = 3 empty-ring closure:
  every generation is headless, the ring n = 3 never elects, walks on n = 6
  end leaderless in 48/64 fresh and 194/200 random seeds).  `prodHold` keeps a
  pathless `produce` head.
* `chainInt`: the emitting tail of S (`compare2`, label ψ-1) departs when the
  cell before it no longer carries sub-signal ψ-2 (the head of S was cleared
  by the leader's reset sweep while the round trip was in flight), and a birth
  request on the head of S' facing a tail that is not `compare2` is dropped.
  Without it the n = 5 Σ-family closure under `fab2WK4` has 1335 births whose
  source class holds a birth request next to a `reset_cmd` cell: the request
  survives the tail's release and fires on the tail's next emission.
* `cleanFix` (ψ > 2): Algorithm 5's clean command survives the neighbour's
  fresh connect (see `cleanSigF`); `srcRel` (ψ > 2): a `done` cell whose
  predecessor is not generating departs (see `srcRelease`).
* `srcDone` (ψ > 2): `srcBlock` restricted to `done` cells (see `sigMoveF`);
  a producing head that receives a foreign sub-signal lets it pass and be
  checked.

## Round 3 (`fab3…`, switch `elimSafe2`)

* `elimSafe2`: see `shieldFix`.  The never-zero sector S1 = (≥ 2 leaders) ∨
  (one leader, and it is shielded or no live bullet exists) leaks under
  `fab2WK4R` only through Algorithm 15's responder fire (a shielded leader
  unshields while a live bullet is in flight) and through Algorithm 16's
  migration merging two adjacent unshielded leaders; `shieldFix` closes the
  first, `noMerge` the second (`fab3M`).
* `lockFix` (`fab3L`): see `maintain`; answers the all-lock traps.
* `headConserve` (`fab3H`): the Head pair conservation of `PPLLAstraDesign2.conserve` as the final stage.
* `fullRing` (`fab3F` = `fab3H` + it, `fab3LF` = `fab3L` + it): see `maintain`;
  the residual all-lock traps of `fab3L`/`fab3H` are full rings of paths with
  no cell free, no cell aligned and no boundary at source (ψ = 2, n = 2:
  3/32 seeds; ψ = 3, n = 3), where neither SIGMOVE, CHECK nor the boundary
  comparison can fire.
* `chainFix` (`fab3G3` = `fab3G` + it, `fab3F3` = `fab3F` + it): see `maintain`;
  the two ψ = 3 traps left by `fullRing` in the census walks (orphan
  `produce` behind a foreign sub-signal ψ-1; `compare1, compare1, depart`
  chain on the 2ψ-ring).
* `fab3G` = `fab2WK4R` + `lockFix` + `fullRing` + `headConserve` (no
  `elimSafe2`, no `noMerge`): see the note at `variants`.

### Request authentication

A birth request is a token; in the arbitrary-initial-state model every finite
local pattern (token plus any flag a re-check would store) is a legal initial
state, so no pair rule can authenticate a request: the (l, r) pair on a forged
birth edge is identical to the pair on a genuine one (28/28 pairs
at n = 5).  Provenance therefore lives in the invariant, not the rule: S5b of
`stabilizedB` requires every comparison token to be consistent with the
carriers it summarizes (forward token bit = the left run's carrier bit at that
label, and equal prefix; no request at all, since S3 + S5 exclude an equality),
and a forged request is a one-step excursion to two leaders that K4 removes.
-/

set_option autoImplicit false

namespace PPLLFableDesign

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
def maintain {ψ : Nat} (ci lf fr cf : Bool) (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let last := ψ - 1
  -- `cf` (chain fix; two rare ψ = 3 traps of the census walks under
  -- `fab3F`, 1/98 lock-census seeds at n = 6 and 3/9 shifted seeds at n = 9):
  -- (i) a `produce` cell that is not the head of its group and whose
  -- predecessor is neither `produce` nor `done` is an orphan (Algorithm 4's
  -- forward wave writes `produce` from the head rightward and the reverse wave
  -- `done` from the tail leftward, so a live wave always has one of the two on
  -- the predecessor); it reads as `none`.  Algorithm 10 never moves a
  -- sub-signal ψ-1 onto a `produce` cell, so an orphan `produce` behind a
  -- foreign sub-signal ψ-1 is a permanent block (`srcRelease` is the same
  -- repair for `done`).  (ii) a `compare1` cell whose successor sub-signal is
  -- still `depart` has no valid answer from the tail (the answer propagates
  -- from the tail leftward through `compare1` cells only); it returns to
  -- `lock` and the tail answers again.  Without it two adjacent groups on the
  -- 2ψ-ring lock each other with one chain `compare1, compare1, depart`: the
  -- forward token of the other comparison is dropped on the `depart` tail
  -- (`landForward`), the boundary re-emits it, and the ring cycles leaderless.
  let (l, r) := if cf ∧ r.state = .produce ∧ r.label.val ≠ 0 ∧ l.state ≠ .produce ∧
      l.state ≠ .done then (l, { r with state := .none }) else (l, r)
  let l := match l.path, r.path with
    | .some ll _, .some rl _ =>
      if cf ∧ l.state = .compare1 ∧ ll ≠ last ∧ rl = ll + 1 ∧ r.state = .depart then
        { l with state := .lock }
      else l
    | _, _ => l
  -- (iii) a `compare2` tail whose predecessor is still `lock` was overwritten
  -- by the boundary emission before its own acknowledgement had propagated
  -- back (it is also the tail of a locked S'); it answers `compare1` first and
  -- is emitted again once its chain is acknowledged (on the ψ-ring S = S':
  -- `compare2, lock, lock` is a permanent leaderless bottom of `fab3G3`,
  -- lock census p3-n3 seed 28).
  let r := match l.path, r.path with
    | .some ll _, .some rl _ =>
      if cf ∧ r.state = .compare2 ∧ rl = last ∧ ll + 1 = rl ∧ l.state = .lock then
        { r with state := .compare1 }
      else r
    | _, _ => r
  -- `fr` (full ring): (i) `congest` is dead in this pipeline (CMP_UPDATE
  -- line 1 is the only printed writer and is replaced), so a `congest` cell is
  -- an initial-state artefact and reads as `none`; (ii) on a boundary edge
  -- (tail `s_{ψ-1}` of S, head `s'_0` of S') on which the two signals are not
  -- both at source (`depart`/`depart` is the boundary comparison), the tail of
  -- S is dropped (CLEAN_SIG removes the rest of S).  An aligned holder in
  -- `none` is readied by CHECK on the same edge before this stage, so in a
  -- label-consistent ring the pattern is never a signal blocked behind a source
  -- signal; it is the full-ring garbage (every cell holds a
  -- path, no cell is free, no cell is aligned or at source: ψ = 2, n = 2 and
  -- ψ = 3, n = 3 leaderless bottoms under `fab3L`/`fab3H`).
  let dead (u : AgentState ψ) : AgentState ψ :=
    if fr ∧ u.state = .congest then { u with state := .none } else u
  let l := dead l
  let r := dead r
  let l := match l.path, r.path with
    | .some ll _, .some rl _ =>
      if fr ∧ ll = last ∧ rl = 0 ∧ (l.state = .none ∨ l.state = .depart) ∧
          (r.state = .none ∨ r.state = .depart) ∧ ¬(l.state = .depart ∧ r.state = .depart) then
        { l with path := .bot, state := .none, path2 := none }
      else l
    | _, _ => l
  -- `lf` (lock fix): the wave never puts the last cell of a group into
  -- `lock` (the head locks, propagation turns the tail into `compare1`), so a
  -- `lock` at label ψ-1 is an initial-state artefact; it departs.  An aligned
  -- all-`lock` ring has no `depart` to start the acknowledgement, no ready cell
  -- and no free cell to generate into (permanent leaderless
  -- bottoms at ψ = 2, n = 2/4/6 and ψ = 3, n = 3 under every fab variant).
  let lockTail (u : AgentState ψ) : AgentState ψ :=
    match u.path with
    | .some ul _ => if lf ∧ last ≥ 1 ∧ ul = last ∧ u.state = .lock then { u with state := .depart } else u
    | .bot => u
  let l := lockTail l
  let r := lockTail r
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
      -- `ci` (chain integrity): the emitting tail of S (`compare2`,
      -- label ψ-1 ≥ 1) needs the cell before it to still carry sub-signal
      -- ψ-2 of S; a tail whose head was cleared (the leader's reset sweep,
      -- `clearCmp`) departs, and its comparison dies with it.
      else if ci ∧ r.state = .compare2 ∧ rl = last ∧ rl ≥ 1 then
        let ok : Bool := match l.path with
          | .some ll _ => decide (ll + 1 = rl)
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

/-- A birth request: a backward token for the head (label 0) with
bit 1 (every comparison's backward token carries bit 0, `landForward`), emitted
by the last cell of S' on a terminal equality and carried back to the head. -/
def birthRequest (ψ : Nat) : Path2Info := ⟨0, 1, ψ - 1, 2⟩

def isBirthRequest (t : Path2Info) : Bool :=
  t.action = 2 && t.label = 0 && t.bit = 1 && t.position = 0

/-- Boundary lock, lock propagation, acknowledgement and token emission; with
`rt` (round trip) also the boundary birth: the head of S' holding a birth
request, still locked, facing the emitting tail of S still in `compare2` with
its carrier present, becomes the leader. -/
def wave {ψ : Nat} (κ : Nat) (detect rt ci : Bool) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let last := ψ - 1
  match l.path, r.path with
  | .some ll _, .some rl _ =>
    let req : Bool := match r.path2 with | some t => isBirthRequest t | none => false
    -- `ci` (chain integrity): a request on the head of S' facing a
    -- tail of S that is no longer `compare2` (its chain broke, `maintain`)
    -- is dropped instead of waiting for the tail's next emission.
    let r := if ci ∧ ll = last ∧ rl = 0 ∧ req ∧ l.state ≠ .compare2 then
      { r with path2 := none } else r
    let req : Bool := req && decide (r.path2 ≠ none)
    let (l, r) : AgentState ψ × AgentState ψ :=
      if rt ∧ ll = last ∧ rl = 0 ∧ lockedState r.state ∧ l.state = .compare2 ∧ req then
        if !detect || decide (r.count = κ) then
          ({ l with state := .depart }, { r with leader := true, path2 := none })
        else ({ l with state := .depart }, { r with state := .depart, path2 := none })
      else (l, r)
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

/-- Forward token at position 0 on the responder: compare, decide, or drop.
With `rt` the terminal equality emits a birth request instead of a birth. -/
def landForward {ψ : Nat} (κ : Nat) (detect eqBirth rt : Bool) (r : AgentState ψ) : AgentState ψ :=
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
            if eqBirth ∧ rt then { r with path2 := some (birthRequest ψ) }
            else if eqBirth ∧ (!detect || decide (r.count = κ)) then
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
      if t.bit = 1 then (if ll = 0 ∧ lockedState l.state then l else { l with path2 := none })
      else if t.label = ll then { l with path2 := some ⟨ll, lb, ψ, 1⟩ }
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
    | some t => if t.action = 2 ∧ t.position = 0 ∧ t.bit ≠ 1 then { r with path2 := none } else r
    | none => r
  (l, r)

/-- The COMPARE stage: Algorithm 6 line 1-2, then the rules above. -/
def compareSigF {ψ : Nat} (κ : Nat) (detect eqBirth rt hold ci lf fr cf : Bool) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  -- `hold` (ψ > 2): Algorithm 6 lines 1-2 reset every pathless
  -- initiator to `none`; a head in `produce` has no sub-signal until the
  -- reverse wave of Algorithm 4 returns, so for ψ > 2 the printed COMPARE
  -- erases the generating head on the same interaction that started it.
  let l := match l.path with
    | .bot => if hold ∧ l.state = .produce then l else { l with state := .none }
    | .some _ _ => l
  let (l, r) := maintain ci lf fr cf l r
  let (l, r) := wave κ detect rt ci l r
  let (l, r) := dropStray l r
  (landBackward l, landForward κ detect eqBirth rt r)

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
def sigMoveF {ψ : Nat} (hψ : ψ > 0) (wall src srcDone : Bool) (m : M2) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let nextLabel : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let l := if wall ∧ (l.leader = true ∨ (r.leader = true ∧ r.label ≠ nextLabel)) then
    clearCmp l else l
  let r := if wall ∧ r.leader = true then clearCmp r else r
  -- `src` (ψ > 2): a sub-signal whose group is still generating
  -- (`produce`/`done`, Algorithm 4) is at source and does not depart
  -- `srcDone`: only a `done` cell holds its own sub-signal; a
  -- `produce` cell carrying a path carries a foreign sub-signal in transit,
  -- which must keep moving (ψ = 3, n = 6: a signal straddling two groups
  -- froze on the second group's producing head, 54/64 fresh walks leaderless).
  let (l, r) := if src ∧ (l.state = .done ∨ (!srcDone ∧ l.state = .produce)) then (l, r)
    else sigMoveStep1With m l r
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

/-! ## CLEAN_SIG with the clean command protected (ψ > 2)

Algorithm 5 line 9 (13) writes the clean command `(-1, _)` into `r.path5`
(`l.path4`) of the connect carrier; lines 23-25 (15-17) then overwrite that
very field with the neighbour's freshly regenerated connect whenever the
neighbour holds a sub-signal of label `≠ ψ-1` (`≠ 0`).  For ψ = 2 the only
sub-signal that can detect a mismatch on its left is label 1 = ψ-1, so the
command survives; for ψ > 2 a torn signal whose nearest path-holding
neighbour has a middle label is never cleaned (ψ = 3, n = 6 walks: both
groups' label-1 cells hold sub-signal 1 in `CHECK_ready` forever, 48/64 fresh
seeds under `fabWK4`).  `cleanSigF true` lets a clean command on the target
field block the propagation instead of being overwritten. -/

def isCleanCmd (t : Option (Int × Nat)) : Bool :=
  match t with | some (lbl, _) => decide (lbl = (-1 : Int)) | none => false

def cleanSigF {ψ : Nat} (hψ : ψ > 0) (fix : Bool) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := cleanSigGenConnect l
  let r := cleanSigGenConnect r
  let (l, r) := cleanSigStep3 l r
  let (l, r) := cleanSigStep4 l r
  let (l, r) := if fix ∧ isCleanCmd l.path4 then (l, { r with path4 := none })
    else cleanSigStep5 hψ l r
  let (l, r) := if fix ∧ isCleanCmd r.path5 then ({ l with path5 := none }, r)
    else cleanSigStep6 hψ l r
  (cleanSigCleanApply l, cleanSigCleanApply r)

/-- `srcRel` (ψ > 2): a `done` cell held at source by `srcBlock`
whose predecessor cell is neither `produce` nor `done` can never be released
by Algorithm 4 line 9-12 (the reverse wave has no head to reach); it departs
as an ordinary sub-signal. -/
def srcRelease {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if r.state = .done ∧ r.label ≠ ⟨0, hψ⟩ ∧ l.label.val + 1 = r.label.val ∧
      l.state ≠ .produce ∧ l.state ≠ .done then
    (l, { r with state := .depart })
  else (l, r)

/-! ## CHECK with the wave states excluded from readiness -/

def readyF {ψ : Nat} (src srcDone : Bool) (u : AgentState ψ) : AgentState ψ :=
  if waveState u.state ∨ u.state = .congest ∨
      (src ∧ (u.state = .done ∨ (!srcDone ∧ u.state = .produce)))
  then u else checkSigSetReadyGuarded u

def checkSigF {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (detect src srcDone : Bool) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := readyF src srcDone l
  let r := readyF src srcDone r
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

/-! ## Elimination safety

Never-zero is targeted from the sector Σ (thesis pp.42-47, `CPB`): every live
bullet's first leader to its right (the direction it came from) is shielded.
A kill (Algorithm 15 line 6-8) needs an unshielded initiator leader and a live
bullet at the responder; under Σ the bullet's first leader to the right is
shielded, hence a different leader, which survives.  Two printed rules break Σ:

* Algorithm 16's migration prefix moves the leader bit one cell left and
  leaves the shield behind (`writeSeqLeaderMove`); a shielded leader with a
  live bullet out becomes unshielded and is killed by its own bullet (a
  witness with n = 3).  `migrateShield` moves the shield with the bit.
* Every birth rule creates an unshielded leader (Algorithms 2, 11, and BEQ);
  a forged live bullet next to it kills the only leader in one edge (a
  witness with n = 2).  `shieldNew` makes every newborn shielded with
  `signal_B = 0`: it unshields only by firing a dummy, which needs the absence
  field to reach it, and a live bullet between the field and the newborn blocks
  the field (Algorithm 15 line 16, `signal_B := 0` at a live bullet).

Unconditional never-zero is not claimed: any local kill rule fires on the pair
state it reads, and that pair with a unique leader is a legal initial
configuration.  What is claimed is Σ-closure plus recovery (births) from the
states outside Σ. -/

/-- The Algorithm-16 migration (`writeSeqLeaderMove`) carrying the shield. -/
def migrateShield {ψ : Nat} (hψ : ψ > 0) (l0 r0 l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  if r0.leader = true ∧ r0.label ≠ ⟨0, hψ⟩ ∧ l.leader = true ∧ r.leader = false then
    ({ l with shield := (l0.leader && l0.shield) || r0.shield },
     { r with shield := false, signal_B := ⟨0, by omega⟩ })
  else (l, r)

/-- A cell whose leader bit was just set is born shielded. -/
def shieldNew {ψ : Nat} (l0 r0 l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let l := if l0.leader = false ∧ l.leader = true then
    { l with shield := true, signal_B := ⟨0, by omega⟩ } else l
  let r := if r0.leader = false ∧ r.leader = true then
    { r with shield := true, signal_B := ⟨0, by omega⟩ } else r
  (l, r)

/-! ## Pipeline -/

inductive WallV where
  | none | leaderOnly | full
  deriving DecidableEq

/-- `elimSafe2`: the shield is the record "my live bullet is out".
Algorithm 15's responder fire (`r.leader ∧ r.signal_B = 1`: dummy bullet and
`shield := false`) drops that record while the bullet is still travelling, and
nothing in K4 restores it: a lone shielded leader whose absence signal comes
back around the ring unshields and is killed by its own bullet (S1 leak kind
(1,1), s2 n = 2 class 32 edge 1→0).  `shieldFix` keeps the responder's shield,
and instead unshields a leader when it absorbs a live bullet
(`absorbAnyMove`), i.e. when a live bullet has come back to it. -/
def shieldFix {ψ : Nat} (l0 r0 l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let r := if r0.leader = true ∧ r.leader = true then { r with shield := r0.shield } else r
  let l := if l0.leader = true ∧ l0.shield = true ∧ r0.bullet = (2 : Fin 3) ∧
      l0.signal_B ≠ (1 : Fin 2) ∧ l.leader = true ∧ r.bullet = (0 : Fin 3) then
    { l with shield := false } else l
  (l, r)

structure Cfg where
  wall : WallV := .full
  detect : Bool := false
  eqBirth : Bool := true
  elim : ElimG := .k4
  /-- Shielded births and shield-carrying migration -/
  elimSafe : Bool := false
  /-- The terminal equality returns to the boundary before the birth -/
  roundTrip : Bool := false
  /-- `produce`/`done` cells are at source (no CHECK ready, no departure) -/
  srcBlock : Bool := false
  /-- For ψ > 2: COMPARE keeps a pathless `produce` head (Algorithm 6 lines 1-2) -/
  prodHold : Bool := false
  /-- Chain integrity of the emitting tail; a birth request facing a released tail dies -/
  chainInt : Bool := false
  /-- For ψ > 2: Algorithm 5's clean command is not overwritten by a fresh connect -/
  cleanFix : Bool := false
  /-- For ψ > 2: a `done` cell with no generating predecessor departs -/
  srcRel : Bool := false
  /-- For ψ > 2: `srcBlock` holds `done` cells only; a `produce` cell's path is foreign -/
  srcDone : Bool := false
  /-- Responder fire keeps the shield; absorbing a live bullet drops it (`shieldFix`) -/
  elimSafe2 : Bool := false
  /-- Algorithm 16's migration does not move a leader bit onto a leader (no merge) -/
  noMerge : Bool := false
  /-- A `lock` at label ψ-1 departs (all-lock rings progress) -/
  lockFix : Bool := false
  /-- The Head pair conservation of `PPLLAstraDesign2.conserve` as the last stage -/
  headConserve : Bool := false
  /-- `congest` reads as `none`; a boundary tail not at source with its head is dropped (`maintain`) -/
  fullRing : Bool := false
  /-- Orphan `produce` reads as `none`; `compare1` before a `depart` successor returns to `lock` (`maintain`) -/
  chainFix : Bool := false

def pipeline {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : Cfg) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let full : Bool := decide (c.wall = .full)
  let lw : Bool := decide (c.wall ≠ .none)
  let sh (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
      (a b : AgentState ψ) : AgentState ψ × AgentState ψ :=
    let q := f a b
    if c.elimSafe then shieldNew a b q.1 q.2 else q
  let q := sh (fun a b => if full then pPsiProbeWall hψ a b else pPsi hψ a b) l r
  let q := genSigSaturated hψ κ q.1 q.2
  let q := cleanSigF hψ c.cleanFix q.1 q.2
  let q := if c.srcRel then srcRelease hψ q.1 q.2 else q
  let q := eliminateSig hψ q.1 q.2
  let q := sigMoveF hψ lw c.srcBlock c.srcDone .dropMisaligned q.1 q.2
  let q := (dropStale q.1, dropStale q.2)
  let q := if full then preCheckReset q.1 q.2 else q
  let q := sh (checkSigF hψ κ c.detect c.srcBlock c.srcDone) q.1 q.2
  let q := disappear hψ q.1 q.2
  let q := sh (compareSigF κ c.detect c.eqBirth c.roundTrip c.prodHold c.chainInt c.lockFix c.fullRing c.chainFix) q.1 q.2
  let q := if full then suppressSigResetKill hψ q.1 q.2 else suppressSig hψ q.1 q.2
  let (e0, f0) := q
  let q := elimG hψ c.elim e0 f0
  let q := if c.elimSafe2 then shieldFix e0 f0 q.1 q.2 else q
  let (l0, r0) := q
  let q := writeSeq hψ l0 r0
  -- `noMerge`: `writeSeqLeaderMove` moves r's leader bit onto l even
  -- when l is a leader, merging two leaders (S1 leak kind (2,1): the survivor
  -- is unshielded with a live bullet in flight, p3two n = 3: 137 edges).
  let q := if c.noMerge ∧ l0.leader = true ∧ r0.leader = true ∧ q.2.leader = false then
    (q.1, { q.2 with leader := true }) else q
  let q := if c.elimSafe then migrateShield hψ l0 r0 q.1 q.2 else q
  -- `headConserve`: the pair conservation of `PPLLAstraDesign2.conserve` (Head policy):
  -- a pair that held a leader keeps one; on a
  -- fatal hit the responder becomes a shielded label-0 leader.  Unconditional
  -- never-zero at no state cost; convergence is the census's question.
  if c.headConserve ∧ (l.leader || r.leader) ∧ !(q.1.leader || q.2.leader) then
    let u := clearCmp q.2
    (q.1, { u with leader := true, shield := true, bullet := 0, signal_B := 0, label := ⟨0, hψ⟩ })
  else q

def variants : List (String × Cfg) :=
  [ ("fabWK4", {})
  , ("fabWK2", { elim := .base .k2 })
  , ("fabWDK4", { detect := true })
  , ("fabLWK4", { wall := .leaderOnly })
  , ("fabNK4", { wall := .none })
  , ("fabNDK4", { wall := .none, detect := true })
  , ("fabWNoEqK4", { eqBirth := false })
  -- fab2 variants
  , ("fab2WK4", { elimSafe := true, roundTrip := true, srcBlock := true })
  , ("fab2WDK4", { elimSafe := true, roundTrip := true, srcBlock := true, detect := true })
  , ("fab2ES", { elimSafe := true })
  , ("fab2RT", { roundTrip := true })
  , ("fab2SB", { srcBlock := true })
  , ("fab2NoSB", { elimSafe := true, roundTrip := true })
  , ("fab2WK4P", { elimSafe := true, roundTrip := true, srcBlock := true, prodHold := true })
  , ("fab2P", { prodHold := true })
  , ("fab2WK4Q", { elimSafe := true, roundTrip := true, srcBlock := true, prodHold := true,
                   chainInt := true, cleanFix := true, srcRel := true })
  , ("fab2WDK4Q", { elimSafe := true, roundTrip := true, srcBlock := true, prodHold := true,
                    chainInt := true, cleanFix := true, srcRel := true, detect := true })
  , ("fab2WK4R", { elimSafe := true, roundTrip := true, srcBlock := true, prodHold := true,
                   chainInt := true, cleanFix := true, srcRel := true, srcDone := true })
  , ("fab2WDK4R", { elimSafe := true, roundTrip := true, srcBlock := true, prodHold := true,
                    chainInt := true, cleanFix := true, srcRel := true, srcDone := true,
                    detect := true })
  -- fab3 variants
  , ("fab3WK4R", { elimSafe := true, roundTrip := true, srcBlock := true, prodHold := true,
                   chainInt := true, cleanFix := true, srcRel := true, srcDone := true,
                   elimSafe2 := true })
  , ("fab3WDK4R", { elimSafe := true, roundTrip := true, srcBlock := true, prodHold := true,
                    chainInt := true, cleanFix := true, srcRel := true, srcDone := true,
                    elimSafe2 := true, detect := true })
  , ("fab3M", { elimSafe := true, roundTrip := true, srcBlock := true, prodHold := true,
                chainInt := true, cleanFix := true, srcRel := true, srcDone := true,
                elimSafe2 := true, noMerge := true })
  , ("fab3L", { elimSafe := true, roundTrip := true, srcBlock := true, prodHold := true,
                chainInt := true, cleanFix := true, srcRel := true, srcDone := true,
                elimSafe2 := true, noMerge := true, lockFix := true })
  , ("fab3H", { elimSafe := true, roundTrip := true, srcBlock := true, prodHold := true,
                chainInt := true, cleanFix := true, srcRel := true, srcDone := true,
                elimSafe2 := true, noMerge := true, lockFix := true, headConserve := true })
  , ("fab3F", { elimSafe := true, roundTrip := true, srcBlock := true, prodHold := true,
                chainInt := true, cleanFix := true, srcRel := true, srcDone := true,
                elimSafe2 := true, noMerge := true, lockFix := true, headConserve := true,
                fullRing := true })
  , ("fab3LF", { elimSafe := true, roundTrip := true, srcBlock := true, prodHold := true,
                 chainInt := true, cleanFix := true, srcRel := true, srcDone := true,
                 elimSafe2 := true, noMerge := true, lockFix := true, fullRing := true })
  -- `fab3G`: the round-2 candidate plus the three round-3 liveness/never-zero
  -- repairs only (`lockFix`, `fullRing`, `headConserve`); `elimSafe2` and
  -- `noMerge` are dropped: the s2 n = 2 closure lineage has 0 two-leader
  -- bottoms under `fab2WK4R`, 3 under `fab3WK4R` (`elimSafe2`) and 29 under
  -- `fab3M` (`noMerge`), i.e. the two S1 repairs cost convergence at n = ψ = 2
  -- while Head conservation makes S1 unnecessary.  `fab3G2` keeps `elimSafe2`.
  , ("fab3G", { elimSafe := true, roundTrip := true, srcBlock := true, prodHold := true,
                chainInt := true, cleanFix := true, srcRel := true, srcDone := true,
                lockFix := true, fullRing := true, headConserve := true })
  , ("fab3G2", { elimSafe := true, roundTrip := true, srcBlock := true, prodHold := true,
                 chainInt := true, cleanFix := true, srcRel := true, srcDone := true,
                 elimSafe2 := true, lockFix := true, fullRing := true, headConserve := true })
  , ("fab3G3", { elimSafe := true, roundTrip := true, srcBlock := true, prodHold := true,
                 chainInt := true, cleanFix := true, srcRel := true, srcDone := true,
                 lockFix := true, fullRing := true, headConserve := true, chainFix := true })
  , ("fab3F3", { elimSafe := true, roundTrip := true, srcBlock := true, prodHold := true,
                 chainInt := true, cleanFix := true, srcRel := true, srcDone := true,
                 elimSafe2 := true, noMerge := true, lockFix := true, headConserve := true,
                 fullRing := true, chainFix := true })
  , ("fab2C", { cleanFix := true })
  , ("fab2CI", { elimSafe := true, roundTrip := true, srcBlock := true, prodHold := true,
                 chainInt := true }) ]

def run {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : Cfg) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  pipeline hψ κ c l r

/-! ## The stabilized set S*: a decidable sketch

`stabilizedB c` reads a configuration `c` (cell `i`'s right neighbour is
`(i+1) % n`) with `ψ ∣ n`.  Conjuncts, with the fields each reads:

* S1 `leader`: exactly one leader, at cell `L`.
* S2 `label`: cell `L + k` has label `k % ψ` (labels consistent from the leader).
* S3 `bit`: the `n/ψ` group IDs are pairwise distinct (the thesis's ruler
  sequence, Lemma 4.1.11, is one such assignment; distinctness is what the
  birth rules read).
* S4 `probe`: no probe anywhere (probe wall).
* S5 carrier coherence (`path`, `state`, `path2`): every cell holding a path is
  part of a maximal run of consecutive cells whose path labels are `0,…,ψ-1` in
  order (complete signals only), and the run's ID equals the ID of a follower
  group lying strictly between the leader and the run going right from the
  leader (the wall deletes signals at the leader, so every carrier came from
  its left inside the leader-free arc); a cell without a path has `state = none`
  and no token; a `depart` cell holds its own group's sub-signal; tokens sit
  only on wave-state cells.  (The lock-chain shape of `maintain` and the CHECK
  states are not encoded here.)
* S5b token consistency: see the code comment; forged tokens that
  contradict the carriers they summarize are outside S*.
* S6 elimination sector Σ (`bullet`, `shield`, `signal_B`): at most one live
  bullet; if there is one, the leader is shielded and `signal_B = 0` on the
  leader and on every cell from the bullet to the leader going right
  (Algorithm 15 lines 16-17 block the absence field at a live bullet).
* S7 free fields: `count`, `wait`, `phase`, `reset_cmd`, `echo` (lottery and
  suppression traffic) and the WRITE fields (`path3`, `write*`, `gen_ws`,
  `signal_ws`, `ws_echo`, `last*`, `carry`, `b_carry`, `h_field`, `p`,
  `p_carry`, `reset`), not constrained by this sketch.

Closure of S1-S4, S6 under the pipeline and of S5 under SIGMOVE/CHECK/COMPARE
is what the one-leader closures test; the census cannot enumerate S7. -/
def stabilizedB {ψ : Nat} (c : Array (AgentState ψ)) : Bool := Id.run do
  let n := c.size
  if n = 0 ∨ ψ = 0 ∨ n % ψ ≠ 0 then return false
  let some c0 := c[0]? | return false
  let cell (i : Nat) : AgentState ψ := match c[i]? with | some a => a | none => c0
  let leaders := (List.range n).filter fun i => (cell i).leader
  let some L := leaders.head? | return false
  if leaders.length ≠ 1 then return false
  let at_ (k : Nat) : AgentState ψ := cell ((L + k) % n)
  -- S2, S4
  for k in [0:n] do
    if (at_ k).label.val ≠ k % ψ then return false
    if (at_ k).probe then return false
  -- S3
  let g := n / ψ
  let gid (j : Nat) : List Bool := (List.range ψ).map fun t => (at_ (j * ψ + t)).bit
  for a in [0:g] do
    for b in [0:g] do
      if a < b ∧ gid a = gid b then return false
  -- S5: runs of paths, checked from the leader rightward
  let mut k := 0
  while k < n do
    match (at_ k).path with
    | .bot =>
      if (at_ k).state ≠ .none ∨ (at_ k).path2 ≠ none then return false
      k := k + 1
    | .some lab _ =>
      if lab ≠ 0 ∨ k + ψ > n then return false
      let runId : List Bool := (List.range ψ).map fun t =>
        match (at_ (k + t)).path with | .some _ b => b = 1 | .bot => false
      for t in [0:ψ] do
        let u := at_ (k + t)
        match u.path with
        | .some l' _ => if l' ≠ t then return false
        | .bot => return false
        if u.state = .depart ∧ (u.label.val ≠ t ∨ runId ≠ gid ((k + t) / ψ)) then return false
        if u.path2 ≠ none ∧ !waveState u.state then return false
      -- the source: a follower group strictly left of the run inside the arc
      let src := (List.range g).any fun j => decide (j ≥ 1) && decide (j * ψ + ψ ≤ k) && decide (gid j = runId)
      if !src then return false
      -- S5b: token consistency.  A token on cell `k + t` of this run
      -- summarizes the comparison of the run immediately to the left (its
      -- carrier bits, `lid`) with this run's agent bits: the forward bit is the
      -- left run's bit at the token's label, the prefix below that label is
      -- equal, and no birth request exists (S3 + S5 exclude an equality).
      let lid : List Bool := (List.range ψ).map fun t =>
        match (at_ (k + n - ψ + t)).path with | .some _ b => b = 1 | .bot => false
      let leftRun : Bool := k ≥ ψ && (List.range ψ).all fun t =>
        match (at_ (k - ψ + t)).path with | .some l' _ => l' = t | .bot => false
      for t in [0:ψ] do
        match (at_ (k + t)).path2 with
        | none => pure ()
        | some tok =>
          if isBirthRequest tok then return false
          if tok.action = 1 ∨ tok.action = 2 then
            if !leftRun ∨ tok.label ≥ ψ then return false
            let prefixOk := (List.range tok.label).all fun j =>
              decide (lid[j]? = some (at_ (k + j)).bit)
            if !prefixOk then return false
            if tok.action = 1 ∧ lid[tok.label]? ≠ some (decide (tok.bit = 1)) then return false
      k := k + ψ
  -- S6
  let live := (List.range n).filter fun i => (at_ i).bullet = (2 : Fin 3)
  if live.length > 1 then return false
  match live.head? with
  | none => pure ()
  | some b =>
    if !(at_ 0).shield then return false
    -- the leader endpoint itself and every cell from the
    -- bullet rightward to it: a signal there reaches the leader as responder
    -- before the bullet is absorbed
    if (at_ 0).signal_B ≠ (0 : Fin 2) then return false
    for i in [b:n] do
      if (at_ i).signal_B ≠ (0 : Fin 2) then return false
  return true

end PPLLFableDesign
