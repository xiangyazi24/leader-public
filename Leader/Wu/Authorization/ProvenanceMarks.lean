import Leader.Wu.ZeroDivisible.OverwritingGeneration

/-!
# AuthF: provenance marks on top of zdivOWF

Executable transcription of the provenance design (summary:
`run/verification/g62/fab/ZDIV.md` §20); section numbers `§k` below refer to that design.
Design exploration for the closure census only; no proof content, and no accepted module
is edited: the base is `PPLLFableZDiv.pipeline {wave, outcome, arrive}` (zdivOWF), whose
stages are restated here stage by stage on a state that carries six sidecar fields.

## State

`AuthState ψ` is an `AgentState ψ` (`core`) plus the six sidecars of the design (§3):
`path_mark`, `ctrl_mark`, `path2_mark`, `path4_mark`, `path5_mark : Fin 3` and
`path2_scope : P2Scope` (line | session).  A sidecar whose payload is absent is kept
(its value is then ignored except where the answer reads it, e.g. `fresh3` at a head
whose path is `⊥`).  `path3` and every writer field are not stamped.

## What changes relative to zdivOWF (the answer's explicit rule changes)

* GENSIG (§5.1): `wipeProduceAuth γ` scrubs path/path2/path4/path5/p/p_carry and stamps
  every mark with `γ`; the head chooses `γ = fresh3(head.path_mark, succ.path_mark)`,
  recruited cells take the producer's `γ`, emitted and propagated paths carry `γ`.
* Arrival (§9): a moved path never inherits local control: the receiver gets
  `state := none`, `ctrl_mark = path_mark := sender's path_mark`, and loses
  path2/path4/path5/p/p_carry.
* Tokens (§6): holder validation (`sanitizeP2`) before movement; entry validation per
  token in `moveTokensAuth` (line tokens need a same-`path_mark` path, session tokens a
  same-`ctrl_mark` cell; A2 may claim a lifecycle cell); marked control application
  `applyControlAuth` (ownership check, then the R1 action; a fired action sets
  `ctrl_mark` to the token mark).
* CHECK (§7): verdict certificates (`validateCheck`): a head verdict needs
  `ctrl_mark = path_mark`, a non-head verdict an equal, same-lineage, consecutive
  predecessor; uncertified verdicts are demoted to `none` (larger/less also lose path2).
  Results are issued only by certified issuers into an empty path2 slot; terminal equality
  births only at the end of a certified chain.
* BEQ (§5.2, §8): a new session starts only between two lineage-authenticated `depart`
  endpoints with `σ = fresh3` of their control marks; lock/ack copy and require `σ`;
  A2 carries the rear-train claim; landings check `path2_mark = ctrl_mark`.
* CLEAN (§10): path4/path5 records carry their marks; comparison and command application
  check lineage.
* DISAPPEAR (§11): the A5 token is line-scoped with the toss cell's `ctrl_mark`.
* Reset/leader walls (§12): `clearCmpAuth` = `clearCmp` plus canonical marks 0.

Choices where the answer is ambiguous are marked "ambiguity A<k>" in the docstrings and
listed with reasons in `run/verification/g62/authf/README.md`.
-/

set_option autoImplicit false

namespace PPLLAuthF

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3

/-! ## Marks -/

abbrev ProvColor := Fin 3

/-- Design §2: a colour different from both arguments. -/
def fresh3 (a b : ProvColor) : ProvColor :=
  if a != 0 && b != 0 then 0
  else if a != 1 && b != 1 then 1
  else 2

theorem fresh3_ne_left (a b : ProvColor) : fresh3 a b ≠ a := by
  revert a b; decide

theorem fresh3_ne_right (a b : ProvColor) : fresh3 a b ≠ b := by
  revert a b; decide

inductive P2Scope where
  | line     -- CHECK / DISAPPEAR token of a main-train lineage
  | session  -- BEQ token of one two-train comparison session
  deriving DecidableEq, Repr, Inhabited

/-- An `AgentState` with the six provenance sidecars of the design (§3). -/
structure AuthState (ψ : Nat) where
  core : AgentState ψ
  path_mark : ProvColor := 0
  ctrl_mark : ProvColor := 0
  path2_scope : P2Scope := .line
  path2_mark : ProvColor := 0
  path4_mark : ProvColor := 0
  path5_mark : ProvColor := 0
  deriving DecidableEq, Repr

namespace AuthState
variable {ψ : Nat}

@[inline] def st (u : AuthState ψ) : MainState := u.core.state
@[inline] def hasPath (u : AuthState ψ) : Bool :=
  match u.core.path with | .bot => false | .some _ _ => true
@[inline] def withCore (u : AuthState ψ) (c : AgentState ψ) : AuthState ψ := { u with core := c }
@[inline] def setState (u : AuthState ψ) (s : MainState) : AuthState ψ :=
  { u with core := { u.core with state := s } }
/-- Enter a lineage (non-session) control state: `ctrl_mark := path_mark`. -/
@[inline] def lineage (u : AuthState ψ) (s : MainState) : AuthState ψ :=
  { u with core := { u.core with state := s }, ctrl_mark := u.path_mark }
@[inline] def dropP2 (u : AuthState ψ) : AuthState ψ :=
  { u with core := { u.core with path2 := none } }

end AuthState

open AuthState

variable {ψ : Nat}

/-- Lift a one-cell core map; a newly written `depart` is a lineage state. -/
def liftLife (f : AgentState ψ → AgentState ψ) (u : AuthState ψ) : AuthState ψ :=
  let v := f u.core
  if v.state ≠ u.core.state ∧ v.state = .depart then
    { u with core := v, ctrl_mark := u.path_mark }
  else { u with core := v }

/-- Lift a pair map that never touches comparison provenance. -/
def lift2 (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let q := f l.core r.core
  ({ l with core := q.1 }, { r with core := q.2 })

/-- Lift a pair map whose only provenance-relevant writes are `depart` assignments. -/
def lift2Life (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let q := f l.core r.core
  let fix (u : AuthState ψ) (v : AgentState ψ) : AuthState ψ :=
    if v.state ≠ u.core.state ∧ v.state = .depart then
      { u with core := v, ctrl_mark := u.path_mark }
    else { u with core := v }
  (fix l q.1, fix r q.2)

/-- Design §12: `clearCmp` with the now-unused marks set to the canonical colour 0. -/
def clearCmpAuth (u : AuthState ψ) : AuthState ψ :=
  { core := clearCmp u.core, path_mark := 0, ctrl_mark := 0, path2_scope := .line,
    path2_mark := 0, path4_mark := 0, path5_mark := 0 }

/-! ## Switches for the readings of ambiguous clauses -/

structure Cfg where
  /-- §10: a CLEAN record may compare with the neighbouring path only if its mark agrees
  with that path's lineage (literal reading).  `false`: records compare with any
  neighbour; only command application is lineage-checked. -/
  cleanNbr : Bool := true
  /-- §7.2 literal: a non-head cell becomes CHECK_ready only through its certified equal
  predecessor.  `false` (default): independent readiness is kept (needed by the clean
  CHECK birth words, see the report); only verdicts are certified. -/
  strictReady : Bool := false
  /-- Not in the design (tested repair, see the report): a CLEAN record whose mark differs from
  the neighbouring path's mark treats the pair as broken, exactly like a label mismatch,
  and issues a `-1` command on its own lineage.  A label-consistent train whose cells carry
  different `path_mark`s is otherwise never normalised. -/
  markClean : Bool := false
  /-- Not in the design (tested repair): an A2 may also claim a rear cell in a lineage CHECK
  state `CHECK_ready`/`equal` (BEQ takes precedence over an unfinished CHECK chain).  The
  answer drops the A2 there, which deadlocks a session whose rear head is `equal`. -/
  claimCheck : Bool := false
  /-- AuthF+ (§8.1): sender retirement.  At the cut after Step1 and before token
  transfer, a holder-authenticated line A4 that cannot enter the occupied successor because
  that path carries a different `path_mark`, or a holder-authenticated session A2 that is
  refused by an active wave/CHECK cell of a different colour that it may not claim, clears
  the *sending holder* with `clearCmpAuth` (a main-path hole) instead of dropping only the
  token.  Both conditions are evaluated on the same pre-transfer pair. -/
  retire : Bool := false
  deriving Repr

/-! ## GENSIG (design §5.1) -/

def wipeProduceAuth (γ : ProvColor) (u : AuthState ψ) : AuthState ψ :=
  { core := { u.core with path := .bot, path2 := none, path4 := none, path5 := none,
                          p := false, p_carry := false, state := .produce }
    ctrl_mark := γ, path_mark := γ, path2_scope := .line, path2_mark := γ,
    path4_mark := γ, path5_mark := γ }

/-- `PPLLFableZDiv.genSigOverwrite hψ κ true 0` with the marked generator claim. -/
def genSigAuth (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let (l, r) := lift2 (waitSaturated hψ κ) l r
  -- line 2 (head start, only on an empty head as in zdivOWF); a head already in
  -- `produce` keeps its generation colour (see ambiguity A1)
  let l :=
    if l.core.leader = false ∧ l.core.label = ⟨0, hψ⟩ ∧ l.core.wait = false ∧
        l.core.path = .bot then
      wipeProduceAuth (if l.st = .produce then l.ctrl_mark else fresh3 l.path_mark r.path_mark) l
    else l
  -- line 4 (overwriting wave): recruited cells are scrubbed with the producer's colour;
  -- a produce/done cell of another colour is not part of this generation (ambiguity A2)
  let r :=
    if r.core.label ≠ ⟨0, hψ⟩ ∧ l.st = .produce ∧
        (r.core.path = .bot ∨ (r.st ≠ .produce ∧ r.st ≠ .done) ∨ r.ctrl_mark ≠ l.ctrl_mark) then
      wipeProduceAuth l.ctrl_mark r
    else r
  -- emission: the terminal path carries the generation colour
  let r :=
    if r.core.label = ⟨ψ - 1, by omega⟩ ∧ r.st = .produce then
      { r with core := { r.core with state := .done,
                                     path := .some r.core.label.val (if r.core.bit then 1 else 0) },
               path_mark := r.ctrl_mark }
    else r
  -- backward propagation copies the colour of the done successor (ambiguity A3)
  let (l, r) :=
    if l.core.label ≠ ⟨ψ - 1, by omega⟩ ∧ l.st = .produce ∧ r.st = .done then
      ({ l with core := { l.core with state := .done,
                                      path := .some l.core.label.val (if l.core.bit then 1 else 0) },
                path_mark := r.path_mark, ctrl_mark := r.path_mark },
       r.setState .depart)
    else (l, r)
  let l :=
    if l.core.label = ⟨0, hψ⟩ ∧ l.st = .done then
      { l with core := { l.core with state := .depart, wait := true } }
    else l
  (l, r)

/-! ## CLEAN (design §10) -/

def isCmd (t : Option (Int × Nat)) : Bool :=
  match t with | some (lbl, _) => decide (lbl = (-1 : Int)) | none => false

def genConnectAuth (u : AuthState ψ) : AuthState ψ :=
  match u.core.path with
  | .some pl _ =>
    { u with core := cleanSigGenConnect u.core,
             path4_mark := if pl ≠ 0 then u.path_mark else u.path4_mark,
             path5_mark := if pl ≠ ψ - 1 then u.path_mark else u.path5_mark }
  | .bot => u

def step3Auth (nbr mc : Bool) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  match r.core.path4, l.core.path with
  | some (p4Label, p4Bit), .some lLabel _ =>
    if p4Label ≠ (-1 : Int) then
      if !nbr || mc || r.path4_mark == l.path_mark then
        let r := if p4Label ≠ Int.ofNat (lLabel + 1) ∨ (mc ∧ r.path4_mark ≠ l.path_mark) then
          { r with core := { r.core with path5 := some ((-1 : Int), 1 - p4Bit) },
                   path5_mark := r.path4_mark } else r
        (l, { r with core := { r.core with path4 := none } })
      else (l, { r with core := { r.core with path4 := none } })
    else (l, r)
  | _, _ => (l, r)

def step4Auth (nbr mc : Bool) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  match l.core.path5, r.core.path with
  | some (p5Label, p5Bit), .some rLabel _ =>
    if p5Label ≠ (-1 : Int) then
      if !nbr || mc || l.path5_mark == r.path_mark then
        let l := if p5Label ≠ Int.ofNat rLabel - 1 ∨ (mc ∧ l.path5_mark ≠ r.path_mark) then
          { l with core := { l.core with path4 := some ((-1 : Int), 1 - p5Bit) },
                   path4_mark := l.path5_mark } else l
        ({ l with core := { l.core with path5 := none } }, r)
      else ({ l with core := { l.core with path5 := none } }, r)
    else (l, r)
  | _, _ => (l, r)

/-- `cleanSigStep5` with the record mark moving along. -/
def step5Auth (hψ : ψ > 0) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  match r.core.path4 with
  | some p4 =>
    let r' := { r with core := { r.core with path4 := none } }
    if l.core.label = (⟨0, hψ⟩ : Fin ψ) then
      if p4.2 = 1 then
        ({ l with core := { l.core with path4 := some (p4.1, 0) }, path4_mark := r.path4_mark }, r')
      else ({ l with core := { l.core with path4 := none } }, r')
    else ({ l with core := { l.core with path4 := some p4 }, path4_mark := r.path4_mark }, r')
  | none => (l, r)

def step6Auth (hψ : ψ > 0) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  match l.core.path5 with
  | some p5 =>
    let l' := { l with core := { l.core with path5 := none } }
    if r.core.label = (⟨ψ - 1, by omega⟩ : Fin ψ) then
      if p5.2 = 1 then
        (l', { r with core := { r.core with path5 := some (p5.1, 0) }, path5_mark := l.path5_mark })
      else (l', { r with core := { r.core with path5 := none } })
    else (l', { r with core := { r.core with path5 := some p5 }, path5_mark := l.path5_mark })
  | none => (l, r)

/-- `cleanSigCleanApply`: a `-1` command deletes a main path only of its own lineage;
otherwise the command itself is cleared. -/
def cleanApplyAuth (u : AuthState ψ) : AuthState ψ :=
  match u.core.path with
  | .bot => u
  | .some pathLabel _ =>
    let u := match u.core.path4 with
      | some (lbl, _) =>
        if lbl = (-1 : Int) then
          if u.path4_mark == u.path_mark then
            let c := if pathLabel = 0 then { u.core with path4 := none } else u.core
            { u with core := { c with path := .bot } }
          else { u with core := { u.core with path4 := none } }
        else u
      | none => u
    match u.core.path5 with
    | some (lbl, _) =>
      if lbl = (-1 : Int) then
        if u.path5_mark == u.path_mark then
          let c := if pathLabel = ψ - 1 then { u.core with path5 := none } else u.core
          { u with core := { c with path := .bot } }
        else { u with core := { u.core with path5 := none } }
      else u
    | none => u

/-- `PPLLAstraDesign3.cleanSource` with marked records. -/
def cleanSourceAuth (hψ : ψ > 0) (c : Cfg) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let l := genConnectAuth l
  let r := genConnectAuth r
  let (l, r) := step3Auth c.cleanNbr c.markClean l r
  let (l, r) := step4Auth c.cleanNbr c.markClean l r
  let (l, r) := if isCmd l.core.path4 then (l, { r with core := { r.core with path4 := none } })
    else step5Auth hψ l r
  let (l, r) := if isCmd r.core.path5 then ({ l with core := { l.core with path5 := none } }, r)
    else step6Auth hψ l r
  (cleanApplyAuth l, cleanApplyAuth r)

/-! ## Token validation, movement and control application (design §6, §11) -/

/-- §6.1 holder validation. -/
def p2Valid (u : AuthState ψ) : Bool :=
  match u.core.path2 with
  | none => true
  | some _ =>
    u.hasPath &&
      (match u.path2_scope with
       | .line => u.path2_mark == u.path_mark
       | .session => u.path2_mark == u.ctrl_mark)

def sanitizeP2 (u : AuthState ψ) : AuthState ψ := if p2Valid u then u else u.dropP2

/-- Lifecycle/neutral material that an A2 may claim (§5.2; ambiguity A5). -/
def claimable (cc : Bool) (u : AuthState ψ) : Bool :=
  u.st == .depart || u.st == .none || (cc && (u.st == .CHECK_ready || u.st == .equal))

inductive Entry where
  | ok | claim | reject
  deriving DecidableEq

/-- §6.2 entry test of the token held by `src` into `dst`. -/
def entry (cc : Bool) (src dst : AuthState ψ) (t : Path2Info) : Entry :=
  if !dst.hasPath then .reject else
  match src.path2_scope with
  | .line => if dst.path_mark == src.path2_mark then .ok else .reject
  | .session =>
    if t.action = 2 then
      if dst.ctrl_mark == src.path2_mark && (waveState dst.st || dst.st == .depart) then .ok
      else if claimable cc dst then .claim else .reject
    else if dst.ctrl_mark == src.path2_mark then .ok else .reject

/-- Destructive A2 claim of a rear-train cell (§5.2); path2 is set by the move. -/
def claimA2 (σ : ProvColor) (u : AuthState ψ) : AuthState ψ :=
  { u with core := { u.core with path4 := none, path5 := none, p := false, p_carry := false,
                                  state := if u.ctrl_mark == σ && waveState u.st then u.st else .depart },
           ctrl_mark := σ }

/-- Place a token (with the sender's scope and mark) on `dst`, claiming if needed. -/
def receive (e : Entry) (src dst : AuthState ψ) (t : Path2Info) : AuthState ψ :=
  let dst := if e = .claim then claimA2 src.path2_mark dst else dst
  { dst with core := { dst.core with path2 := some t },
             path2_scope := src.path2_scope, path2_mark := src.path2_mark }

/-- `PPLLFableDesignR1.moveTokens` with §6.2 entry validation: a token that would move
into a cell it may not enter is deleted first; then the R1 queue/drop/swap logic runs
with scope and mark moving atomically with the token. -/
def moveTokensAuth (c : Cfg) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let cc := c.claimCheck
  -- AuthF+ §8.1 sender retirement, evaluated on the common pre-transfer cut
  let failA4 : Bool := match l.core.path2 with
    | some tl => c.retire && tl.action == 4 && l.path2_scope == .line && p2Valid l &&
        canMoveR l.core tl && r.hasPath && l.path2_mark != r.path_mark
    | none => false
  let failA2 : Bool := match r.core.path2 with
    | some tr => c.retire && tr.action == 2 && r.path2_scope == .session && p2Valid r &&
        canMoveL r.core tr && l.hasPath &&
        (waveState l.st || l.st == .CHECK_ready || l.st == .equal || l.st == .larger || l.st == .less) &&
        l.ctrl_mark != r.path2_mark && !claimable cc l
    | none => false
  if failA4 || failA2 then
    ((if failA4 then clearCmpAuth l else l), (if failA2 then clearCmpAuth r else r))
  else
  let eR : Entry := match l.core.path2 with
    | some tl => if canMoveR l.core tl then entry cc l r tl else .ok
    | none => .ok
  let eL : Entry := match r.core.path2 with
    | some tr => if canMoveL r.core tr then entry cc r l tr else .ok
    | none => .ok
  let l := if eR = .reject then l.dropP2 else l
  let r := if eL = .reject then r.dropP2 else r
  match l.core.path2, r.core.path2 with
  | some tl, some tr =>
    if canMoveR l.core tl ∧ canMoveL r.core tr then
      (receive eL r l (dec tr), receive eR l r (dec tl))
    else if canMoveR l.core tl ∧ rightward tr ∧ canMoveR r.core tr then
      (l.dropP2, r)
    else if canMoveL r.core tr ∧ leftward tl ∧ canMoveL l.core tl then
      (l, r.dropP2)
    else (l, r)
  | some tl, none =>
    if canMoveR l.core tl then (l.dropP2, receive eR l r (dec tl)) else (l, r)
  | none, some tr =>
    if canMoveL r.core tr then (receive eL r l (dec tr), r.dropP2) else (l, r)
  | none, none => (l, r)

/-- §6.3: `sigMoveApplyControlConsume` behind an ownership check for actions 3-6. -/
def applyControlAuth (hψ : ψ > 0) (u : AuthState ψ) : AuthState ψ :=
  match u.core.path2 with
  | some p2 =>
    if p2.action = 3 ∨ p2.action = 4 ∨ p2.action = 5 ∨ p2.action = 6 then
      let ok : Bool := match u.path2_scope with
        | .line => u.hasPath && u.path2_mark == u.path_mark
        | .session => u.path2_mark == u.ctrl_mark
      if !ok then u.dropP2 else
      let v := sigMoveApplyControlConsume hψ u.core
      if v.path2 = none then { u with core := v, ctrl_mark := u.path2_mark }
      else { u with core := v }
    else u
  | none => u

/-! ## CHECK certificates (design §7) -/

def isHead (u : AuthState ψ) : Bool := u.core.label.val == 0 && aligned u.core
def verdict (u : AuthState ψ) : Bool := u.st == .equal || u.st == .larger || u.st == .less
def checkState (u : AuthState ψ) : Bool := u.st == .CHECK_ready || verdict u

/-- `l` certifies its successor `r`: consecutive aligned labels, `l` an equal of its own
lineage, `r` in the same lineage (§7.2). -/
def certPred (l r : AuthState ψ) : Bool :=
  match l.core.path, r.core.path with
  | .some ll _, .some rl _ =>
    l.st == .equal && l.ctrl_mark == l.path_mark && r.path_mark == l.path_mark &&
      aligned l.core && aligned r.core && rl == ll + 1
  | _, _ => false

def demote (u : AuthState ψ) : AuthState ψ :=
  let res := u.st == .larger || u.st == .less
  { u with core := { u.core with state := .none, path2 := if res then none else u.core.path2 } }

def headBad (u : AuthState ψ) : Bool := isHead u && checkState u && u.ctrl_mark != u.path_mark

/-- Verdict validator: head verdicts need their root stamp, a non-head verdict on the
responder needs a certified equal predecessor (the initiator's predecessor is not visible
on this edge).  Uncertified verdicts become `none`; larger/less lose path2. -/
def validateCheck (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let l := if headBad l then demote l else l
  let r := if headBad r then demote r else r
  let r := if !isHead r && aligned r.core && verdict r &&
      !(certPred l r && r.ctrl_mark == r.path_mark) then demote r else r
  (l, r)

/-- Readiness of `u` (the `checkSource` rule), stamping a new CHECK_ready with the lineage. -/
def readyAuth (u : AuthState ψ) : AuthState ψ :=
  if waveState u.st ∨ u.st = .congest ∨ u.st = .done then u
  else
    let v := checkSigSetReadyGuarded u.core
    if v.state = .CHECK_ready ∧ u.st ≠ .CHECK_ready then { u with core := v, ctrl_mark := u.path_mark }
    else { u with core := v }

/-- Result issue by a certified issuer, never overwriting a token. -/
def issue (u : AuthState ψ) : AuthState ψ :=
  if u.core.path2 = none ∧ (u.st = .larger ∨ u.st = .less) then
    { u with core := checkSigSetResult u.core, path2_scope := .line, path2_mark := u.path_mark }
  else u

/-- `PPLLAstraDesign3.checkSource` as a certified chain (§7). -/
def checkSourceAuth (hψ : ψ > 0) (c : Cfg) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let (l, r) := validateCheck l r
  let l := if !c.strictReady || isHead l then readyAuth l else l
  let r := if !c.strictReady || isHead r then readyAuth r else r
  let l := if r.st = .depart ∧ aligned r.core ∧ l.st = .equal ∧ aligned l.core ∧
      l.core.label.val < ψ - 1 then l.lineage .depart else l
  let l := l.withCore (checkSigCheckL hψ l.core)
  let cert := certPred l r
  -- strict reading: the certified predecessor arms its successor
  let r := if c.strictReady && cert && !isHead r then
      let v := checkSigSetReadyGuarded r.core
      if v.state = .CHECK_ready ∧ r.st ≠ .CHECK_ready ∧ ¬ waveState r.st ∧ r.st ≠ .congest ∧ r.st ≠ .done then
        { r with core := v, ctrl_mark := r.path_mark } else r
    else r
  let r := if cert then r.withCore (checkSigCheckR hψ l.core r.core) else r
  let l := if isHead l && l.ctrl_mark == l.path_mark then issue l else l
  let r := if (isHead r && r.ctrl_mark == r.path_mark) ||
      (cert && r.ctrl_mark == r.path_mark) then issue r else r
  let birthOK : Bool := cert || (ψ == 1 && isHead r && r.ctrl_mark == r.path_mark)
  if r.core.label = ⟨ψ - 1, by omega⟩ ∧ r.st = .equal ∧ birthOK then
    (l, { r with core := { r.core with leader := true } }) else (l, r)

/-! ## SIGMOVE (arrival scrub, validation before movement) -/

/-- SIGMOVE line 1 with F1 and the §9 arrival scrub. -/
def step1Auth (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  match l.core.path, r.core.path with
  | .some pathLabel _, .bot =>
    let blocked : Bool := blockingState l.core || PPLLFableZDiv.outcomePending false l.core
    if !blocked then
      if r.st ≠ MainState.produce ∨ pathLabel ≠ ψ - 1 then
        ({ l with core := { l.core with path := .bot, state := .none } },
         { r with core := { r.core with path := l.core.path, state := .none, path2 := none,
                                        path4 := none, path5 := none, p := false, p_carry := false },
                  path_mark := l.path_mark, ctrl_mark := l.path_mark })
      else (l, r)
    else (l, r)
  | _, _ => (l, r)

def leaderWallAuth (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let l := if l.core.leader = true ∨ r.core.leader = true then clearCmpAuth l else l
  let r := if r.core.leader = true then clearCmpAuth r else r
  (l, r)

def moveSourceAuth (hψ : ψ > 0) (c : Cfg) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let nextLabel : Fin ψ := ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let l := if l.core.leader = true ∨ (r.core.leader = true ∧ r.core.label ≠ nextLabel) then
    clearCmpAuth l else l
  let r := if r.core.leader = true then clearCmpAuth r else r
  let (l, r) := validateCheck l r
  let l := sanitizeP2 l
  let r := sanitizeP2 r
  let (l, r) := if l.st = .done then (l, r) else step1Auth l r
  let (l, r) := moveTokensAuth c l r
  let (l, r) := leaderWallAuth l r
  let l := applyControlAuth hψ l
  let r := applyControlAuth hψ r
  let l := if r.st = .depart ∧ l.core.label.val < ψ - 1 ∧ l.st = .CHECK_ready then
    l.lineage .depart else l
  (l, r)

/-! ## DISAPPEAR (design §11) -/

def disappearAuth (hψ : ψ > 0) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let r :=
    if r.st = .toss ∧ r.core.label = ⟨0, hψ⟩ then
      { r with core := { r.core with state := .toss_done, path2 := some ⟨0, 0, 0, 5⟩, p := false },
               path2_scope := .line, path2_mark := r.ctrl_mark }
    else r
  -- the rest of Algorithm 13 (initiator counter and p-carry) touches no provenance
  let (l, r) := lift2 (disappearStartL hψ) l r
  lift2 (disappearCarry hψ) l r

/-! ## BEQ (design §5.2, §8) -/

def sessionTokenOn (u : AuthState ψ) : Bool :=
  u.core.path2.isSome && u.path2_scope == .session && p2Valid u

/-- `PPLLFableDesignR1.maintain` with marked support, plus the release of a
session-stamped `depart` that has lost its session (ambiguity A6). -/
def maintainAuth (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let last := ψ - 1
  let r := match r.core.path with
    | .bot => if lockedState r.st then r.setState .none else r
    | .some rl _ =>
      if lockedState r.st then
        let ok : Bool := match l.core.path with
          | .some ll _ =>
            decide (ll = (rl + ψ - 1) % ψ) &&
              (if rl = 0 then lockerState l.st else lockedState l.st) &&
              l.ctrl_mark == r.ctrl_mark
          | .bot => false
        if ok then r else r.lineage .depart
      else r
  let l := match l.core.path with
    | .bot => if waveState l.st then l.setState .none else l
    | .some ll _ =>
      if lockedState l.st then
        if ll = last then l else
        let ok : Bool := match r.core.path with
          | .some rl _ => decide (rl = ll + 1) &&
              (decide (r.st = .depart) || (waveState r.st && r.ctrl_mark == l.ctrl_mark))
          | .bot => false
        if ok then l else l.lineage .depart
      else if l.st = .compare2 then
        if ll ≠ last then l.setState .none else
        match r.core.path with
        | .some rl _ =>
          if rl = 0 ∧ lockedState r.st ∧ r.ctrl_mark = l.ctrl_mark then l else l.lineage .depart
        | .bot => l
      else if l.st = .depart ∧ l.ctrl_mark ≠ l.path_mark then
        -- support must itself be session material: a same-σ locked head across the
        -- boundary, the same-σ compare2 tail, or a same-σ stamped depart successor
        -- (a lineage cell whose colour happens to equal σ does not count; the first
        -- version accepted it and left a psi=n=4 leaderless bottom, see the report)
        let ok : Bool := match r.core.path with
          | .some rl _ =>
            r.ctrl_mark == l.ctrl_mark &&
              ((decide (ll = last) && decide (rl = 0) && lockedState r.st) ||
               (decide (rl = ll + 1) &&
                 ((r.st == .depart && r.ctrl_mark != r.path_mark) || r.st == .compare2)))
          | .bot => false
        if ok then l else l.lineage .depart
      else l
  (l, r)

/-- `PPLLAstraDesign3.completeWave` requiring and copying the session mark. -/
def completeWaveAuth (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  match l.core.path, r.core.path with
  | .some ll _, .some rl _ =>
    let r := if lockedState l.st ∧ rl = ll + 1 ∧ r.st = .depart then
      { (r.setState (if rl = ψ - 1 then .compare1 else .lock)) with ctrl_mark := l.ctrl_mark } else r
    let l := if l.st = .lock ∧ r.st = .compare2 ∧ rl = ψ - 1 ∧
        (rl = ll + 1 ∨ (ψ = 1 ∧ ll = 0 ∧ rl = 0)) ∧ l.ctrl_mark = r.ctrl_mark then
      l.setState .compare1 else l
    (l, r)
  | _, _ => (l, r)

def a2Token : Path2Info := ⟨0, 0, ψ - 1, 2⟩

/-- `PPLLFableDesignR1.wave` with the fresh-session root rule (§5.2). -/
def waveAuth (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let last := ψ - 1
  match l.core.path, r.core.path with
  | .some ll _, .some rl _ =>
    let start : Bool := decide (ll = last) && decide (rl = 0) && l.st == .depart &&
      r.st == .depart && l.ctrl_mark == l.path_mark && r.ctrl_mark == r.path_mark &&
      !sessionTokenOn l && !sessionTokenOn r
    let (l, r) := if start then
      let σ := fresh3 l.ctrl_mark r.ctrl_mark
      ({ l with ctrl_mark := σ },
       { r with core := { r.core with state := .lock, path2 := none, path4 := none, path5 := none },
                ctrl_mark := σ })
      else (l, r)
    let r := if l.st = .lock ∧ rl = ll + 1 ∧ r.st = .depart then
      { (r.setState (if rl = last then .compare1 else .lock)) with ctrl_mark := l.ctrl_mark } else r
    let l := if r.st = .compare1 ∧ rl = ll + 1 ∧ l.st = .lock ∧ r.ctrl_mark = l.ctrl_mark then
      l.setState .compare1 else l
    let l := if ll = last ∧ rl = 0 ∧ r.st = .compare1 ∧
        (l.st = .depart ∨ lockedState l.st) ∧ l.ctrl_mark = r.ctrl_mark then
      { l with core := { l.core with state := .compare2, path2 := some (a2Token (ψ := ψ)) },
               path2_scope := .session, path2_mark := r.ctrl_mark } else l
    let l := if ll = last ∧ rl = 0 ∧ r.st = .compare1 ∧ l.st = .compare2 ∧
        l.core.path2 = none ∧ r.core.path2 = none ∧ l.ctrl_mark = r.ctrl_mark then
      { l with core := { l.core with path2 := some (a2Token (ψ := ψ)) },
               path2_scope := .session, path2_mark := r.ctrl_mark } else l
    (l, r)
  | _, _ => (l, r)

/-- `PPLLFableDesignR1.landForward κ false true` with the session check. -/
def landForwardAuth (κ : Nat) (r : AuthState ψ) : AuthState ψ :=
  match r.core.path2, r.core.path with
  | some t, .some rl _ =>
    if t.action = 1 ∧ t.position = 0 then
      if t.label = rl ∧ waveState r.st ∧ r.path2_scope = .session ∧ r.path2_mark = r.ctrl_mark then
        r.withCore (PPLLFableDesignR1.landForward κ false true r.core)
      else r.dropP2
    else r
  | some t, .bot => if t.action = 1 ∧ t.position = 0 then r.dropP2 else r
  | none, _ => r

/-- `PPLLFableDesignR1.landBackward` with the session check. -/
def landBackwardAuth (l : AuthState ψ) : AuthState ψ :=
  match l.core.path2, l.core.path with
  | some t, .some ll _ =>
    if t.action = 2 ∧ t.position = 0 then
      if t.label = ll ∧ l.path2_scope = .session ∧ l.path2_mark = l.ctrl_mark then
        l.withCore (PPLLFableDesignR1.landBackward l.core)
      else l.dropP2
    else l
  | some t, .bot => if t.action = 2 ∧ t.position = 0 then l.dropP2 else l
  | none, _ => l

def compareLifecycleAuth (κ : Nat) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let l := match l.core.path with
    | .bot => if l.st = .produce then l else l.setState .none
    | .some _ _ => l
  let (l, r) := maintainAuth l r
  let (l, r) := completeWaveAuth l r
  let (l, r) := waveAuth l r
  let (l, r) := lift2 PPLLFableDesignR1.dropStray l r
  (landBackwardAuth l, landForwardAuth κ r)

/-- `PPLLAstraDesign3.ackTail` requiring one session mark. -/
def ackTailAuth (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  if l.ctrl_mark = r.ctrl_mark then lift2 ackTail l r else (l, r)

/-- `PPLLAstraDesign3.repair .readyAck` with lineage stamps on released cells. -/
def repairAuth (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let l := liftLife (fun u => normalizeCarrier (normalizeOrphan u)) l
  let r := liftLife (fun u => normalizeCarrier (normalizeOrphan u)) r
  let (l, r) := lift2Life releaseReadySuffix l r
  ackTailAuth l r

/-! ## Walls and reset -/

def preCheckResetAuth (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let send : Bool := l.core.leader || l.core.reset_cmd
  let l' := if send then clearCmpAuth l else l
  let r' := if send || r.core.reset_cmd then clearCmpAuth r else r
  (l', r')

def suppressSigResetKillAuth (hψ : ψ > 0) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let kill (u : AuthState ψ) : AuthState ψ := if u.core.reset_cmd then clearCmpAuth u else u
  let q0 := lift2 suppressSigStart l r
  let q0 := (kill q0.1, kill q0.2)
  let q1 := lift2 suppressSigMoveReset q0.1 q0.2
  let q1 := (kill q1.1, kill q1.2)
  let q2 := lift2 (suppressSigTerminal hψ) q1.1 q1.2
  let q3 := lift2 suppressSigEcho q2.1 q2.2
  lift2 suppressSigFinish q3.1 q3.2

/-- `PPLLAstraDesign2.conserve .head`; a replacement cell gets canonical marks. -/
def conserveAuth (l r : AuthState ψ) (q : AuthState ψ × AuthState ψ) : AuthState ψ × AuthState ψ :=
  let q' := conserve .head l.core r.core (q.1.core, q.2.core)
  let fired : Bool := (l.core.leader || r.core.leader) && !(q.1.core.leader || q.2.core.leader)
  ({ q.1 with core := q'.1 },
   if fired then { clearCmpAuth q.2 with core := q'.2 } else { q.2 with core := q'.2 })

/-! ## Pipeline (stage order of `PPLLFableZDiv.beforeElimination`, design §19 item 8) -/

def beforeElimination (hψ : ψ > 0) (κ : Nat) (c : Cfg) (l r : AuthState ψ) :
    AuthState ψ × AuthState ψ :=
  let q := lift2 (pPsiProbeWall hψ) l r
  let q := genSigAuth hψ κ q.1 q.2
  let q := cleanSourceAuth hψ c q.1 q.2
  let q := lift2Life (releaseSource hψ) q.1 q.2
  let q := lift2 (eliminateSig hψ) q.1 q.2
  let q := moveSourceAuth hψ c q.1 q.2
  let q := (liftLife dropStale q.1, liftLife dropStale q.2)
  let q := preCheckResetAuth q.1 q.2
  let q := (liftLife normalizeReady q.1, liftLife normalizeReady q.2)
  let q := checkSourceAuth hψ c q.1 q.2
  let q := disappearAuth hψ q.1 q.2
  let q := repairAuth q.1 q.2
  let q := compareLifecycleAuth κ q.1 q.2
  suppressSigResetKillAuth hψ q.1 q.2

def pipeline (hψ : ψ > 0) (κ : Nat) (c : Cfg) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let q := beforeElimination hψ κ c l r
  let q := lift2 (k4Kernel hψ) q.1 q.2
  let q := lift2 (writeWithBundle hψ) q.1 q.2
  conserveAuth l r q

/-- Control: zdivOWF on the cores, marks carried unchanged. -/
def zdivOWFLift (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  lift2 (PPLLFableZDiv.pipeline hψ κ { wave := true, outcome := true, arrive := true }) l r

/-- Variants: `authF` (primary reading), `authFnoNbr` (CLEAN compares with any neighbour),
`authFstrict` (literal §7.2 readiness), `authFmc` (AuthF + mark-mismatch CLEAN, not in
the design), `authFcc` (AuthF + A2 claims CHECK_ready/equal, not in the design), `authFmcc` (both),
`authFplus` (AuthF+ = AuthF + sender retirement, §8.1), `authFplusmcc` (AuthF+ with
both repairs above), `zdivOWFlift` (control). -/
def variants : List (String × Option Cfg) :=
  [ ("authF", some {}), ("authFnoNbr", some { cleanNbr := false })
  , ("authFstrict", some { strictReady := true }), ("authFmc", some { markClean := true })
  , ("authFcc", some { claimCheck := true }), ("authFmcc", some { markClean := true, claimCheck := true })
  , ("authFplus", some { retire := true })
  , ("authFplusmcc", some { retire := true, markClean := true, claimCheck := true })
  , ("zdivOWFlift", none) ]

end PPLLAuthF
