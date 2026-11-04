import Leader.Wu.Comparison.PostElectionCheckGuard

/-!
# Per-signal moved bit for CHECK births (board G6.2 design input, not a proof)

The G6.2 guard census (run/verification/g62/guard) found that in-place CHECK
(ERRATA T9: a signal CHECKs its own source group after CMP_UPDATE line 1 re-arms
it to `congest`) is both the post-election birth route at every follower group
and the only leaderless birth route observed at n = 2 and in full-ring COMPARE
deadlocks, and that the census carrier has no field separating a source-local
sub-signal from a moved one.

The thesis states method 2 in terms of a *moved* signal: "when a signal moves to
a group with the same ID, a leader will be created.  The most time-consuming
scenario for this method is when a signal with the greatest ID needs to
traverse the whole ring and return to the group that sent the signal"
(Lemma 4.1.4 proof, p.45 / PDF p.58).  ERRATA T18's required correction asks
for "a separately specified executable phase/authorization rule that
distinguishes a genuinely moved carrier from a source-local one and does not
overwrite active `lock`/return states".

This module adds one Boolean per agent, attached to the sub-signal held in
`path` (prior art: `PPLLAuthorizedComparisonRepair.path0Crossed`,
AuthorizedComparisonRepair.lean:29-33, which attaches such a bit to the
payload-zero component only and sets it on a stable terminal-to-zero crossing):

* every stage except SIGMOVE keeps the bit only while `path` is unchanged and
  non-empty (fail closed, as `reconcilePermit`, AuthorizedComparisonRepair.lean:44-46);
* SIGMOVE's path transfer (`pathMovedRight`, AuthorizedComparisonRepair.lean:98-100)
  sets the receiver's bit to `sender.moved || sender.label = ψ - 1`, i.e. the
  sub-signal has crossed a terminal-to-next edge (left its source group) at
  least once; the sender's bit is cleared.

Switches, all on top of `PPLLPostElectionGuard` base `I`, M2 `dropMisaligned`,
guard `Wall` (probe wall, leader wall, reset kill before and after CHECK) and
elimination kernel `K4` (the best partial of the guard round, minus `NC`):

* `ready`: CHECK's ready assignment (Algorithm 11 line 2) as in the base
  (`checkSigSetReadyGuarded`), without `congest` (`NC`), or without any active
  Algorithm-7 wave state `congest/lock/compare1/compare2` (`NA`);
* `gate`: none; `ready` — an unmoved holder is never made `CHECK_ready`;
  `birth` — the terminal equality creates a leader only if both endpoints are
  moved, otherwise the checking signal is deleted (as `checkSigGuarded`);
  `off` — no CHECK birth at all (method 1 only), the equal signal is deleted;
* `cmp`: the M2 CMP_UPDATE of the base; `rp` — the T18 return-priority
  restatement `PPLLPostElectionGuard.compareSigRP`; `rpm` — `rp` whose fresh
  start additionally requires the label-0 holder to be moved (the
  authorized-lane start rule `freshComparisonStart`, without consuming the bit);
* `track = false` never sets the bit (control: must reproduce the guard
  census of `pegIDropMisWall{,NC}K4` exactly).

The census carrier is `BoundedAgentState ψ κ × Bool`: `BoundedAgentState` has
no field with spare values (every field is read by some pipeline stage and every
bounded payload is exhausted by its protocol domain), so the bit is carried
beside the state, and a separate census executable (`PPLLMovedCensus`)
interns the pair.
-/

set_option autoImplicit false

namespace PPLLMovedBit

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLElimVariants
  PPLLPostElectionGuard

/-- An agent with the moved bit of the sub-signal it holds. -/
abbrev MS (ψ : Nat) := AgentState ψ × Bool

/-- Fail-closed bit update for a stage that does not move paths: the bit
survives only on an unchanged, present path. -/
def keepBit {ψ : Nat} (old : MS ψ) (out : AgentState ψ) : Bool :=
  old.2 && decide (out.path = old.1.path) && decide (out.path ≠ .bot)

def lift {ψ : Nat} (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : MS ψ) : MS ψ × MS ψ :=
  let q := f l.1 r.1
  ((q.1, keepBit l q.1), (q.2, keepBit r q.2))

/-- The Algorithm-10 transfer in the computed result (restatement of
`PPLLAuthorizedComparisonRepair.pathMovedRight`). -/
def pathMovedRight {ψ : Nat} (l r outL outR : AgentState ψ) : Bool :=
  decide (l.path ≠ .bot) && decide (r.path = .bot) &&
    decide (outL.path = .bot) && decide (outR.path = l.path)

/-- SIGMOVE with the moved bit: a transfer sets the receiver's bit when the
sender had it or the edge leaves the sender's group (sender label ψ - 1). -/
def sigMoveBit {ψ : Nat} (track : Bool)
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : MS ψ) : MS ψ × MS ψ :=
  let q := f l.1 r.1
  if track && pathMovedRight l.1 r.1 q.1 q.2 then
    ((q.1, false), (q.2, l.2 || decide (l.1.label.val = ψ - 1)))
  else ((q.1, keepBit l q.1), (q.2, keepBit r q.2))

inductive Ready where
  | base | noCongest | noActive
  deriving DecidableEq

inductive Gate where
  | none | ready | birth | off
  deriving DecidableEq

inductive CmpV where
  | m2 | rp | rpm
  deriving DecidableEq

structure Cfg where
  track : Bool := true
  ready : Ready := .base
  gate : Gate := .none
  cmp : CmpV := .m2
  deriving DecidableEq

def readyFn {ψ : Nat} (c : Cfg) (u : MS ψ) : AgentState ψ :=
  if c.gate = .ready ∧ u.2 = false then u.1 else
  match c.ready with
  | .base => checkSigSetReadyGuarded u.1
  | .noCongest => checkSigSetReadyNoCongest u.1
  | .noActive => if comparisonActive u.1.state then u.1 else checkSigSetReadyGuarded u.1

/-- Algorithm 11 with the chosen ready assignment and birth gate. -/
def checkBit' {ψ : Nat} (hψ : ψ > 0) (c : Cfg) (l r : MS ψ) : MS ψ × MS ψ :=
  let l1 := readyFn c l
  let r1 := readyFn c r
  let l1 := checkSigCheckL hψ l1
  let r1 := checkSigCheckR hψ l1 r1
  let l1 := checkSigSetResult l1
  let r1 := checkSigSetResult r1
  let (l1, r1) :=
    if r1.label = ⟨ψ - 1, by omega⟩ ∧ r1.state = .equal then
      let allow : Bool := match c.gate with
        | .off => false
        | .birth => l.2 && r.2
        | _ => true
      if allow then (l1, { r1 with leader := true }) else (clearCmp l1, clearCmp r1)
    else (l1, r1)
  ((l1, keepBit l l1), (r1, keepBit r r1))

/-- COMPARE stage: M2 base, the T18 return-priority restatement, or the latter
with a moved-only fresh start. -/
def compareBit' {ψ : Nat} (hψ : ψ > 0) (c : Cfg) (l r : MS ψ) : MS ψ × MS ψ :=
  match c.cmp with
  | .m2 => lift (compareSigM2 hψ .leaderlessRearm .dropMisaligned) l r
  | .rp => lift (compareSigRP hψ .leaderlessRearm) l r
  | .rpm =>
    let f := fun (a b : AgentState ψ) =>
      let a := compareSigInit a
      match a.path with
      | .bot => (a, b)
      | .some _ _ =>
        match b.path with
        | .some _ _ =>
          let start : Bool := decide (a.label = ⟨0, hψ⟩) && l.2
          let a' := if start && !comparisonActive a.state then { a with state := .congest } else a
          let q := cmpUpdateReturnPriority a' b
          let q := (cmpUpdateSetPath2 hψ q.1, q.2)
          let q := (keepElim a q.1, keepElim b q.2)
          compareSigDispatch hψ q.1 q.2
        | .bot => (a, b)
    lift f l r

/-- The pipeline as named stages (for birth attribution and tracing). -/
def stages {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : Cfg) :
    List (String × (MS ψ → MS ψ → MS ψ × MS ψ)) :=
  [ ("pPsi", lift (pPsiProbeWall hψ))
  , ("genSig", lift (genSigSaturated hψ κ))
  , ("cleanSig", lift (cleanSig hψ))
  , ("eliminateSig", lift (eliminateSig hψ))
  , ("sigMove", sigMoveBit c.track (sigMoveWalled hψ .dropMisaligned))
  , ("dropStale", lift fun a b => (dropStale a, dropStale b))
  , ("preReset", lift preCheckReset)
  , ("checkSig", checkBit' hψ c)
  , ("disappear", lift (disappear hψ))
  , ("compareSig", compareBit' hψ c)
  , ("suppressSig", lift (suppressSigResetKill hψ))
  , ("elim", lift (k4Kernel hψ))
  , ("writeSeq", lift (writeSeq hψ)) ]

def nLeaders {ψ : Nat} (l r : MS ψ) : Nat :=
  (if l.1.leader then 1 else 0) + (if r.1.leader then 1 else 0)

/-- One interaction, with a birth tag: empty if no stage raised the pair's
leader count, else `<stage>` of the first raising stage; for CHECK the moved
bits of the two endpoints at CHECK input are appended (`checkSig:10` = initiator
moved, responder not).  A trailing `+` marks a net increase over the whole
interaction. -/
def stepTagged {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : Cfg) (l r : MS ψ) :
    MS ψ × MS ψ × String := Id.run do
  let mut a := l
  let mut b := r
  let mut tag := ""
  for (name, f) in stages hψ κ c do
    let before := nLeaders a b
    let q := f a b
    if tag.isEmpty && nLeaders q.1 q.2 > before then
      tag := if name == "checkSig" then
        s!"checkSig:{if a.2 then 1 else 0}{if b.2 then 1 else 0}" else name
    a := q.1
    b := q.2
  if !tag.isEmpty && nLeaders a b > nLeaders l r then tag := tag ++ "+"
  return (a, b, tag)

/-- Named variants `mv<ready><gate><cmp>[T]`: ready `B`/`NC`/`NA`, gate
`G0` (none) / `GR` (ready) / `GB` (birth) / `Off`, cmp `M2`/`RP`/`RPM`;
suffix `U` = untracked control (bit never set). -/
def variants : List (String × Cfg) :=
  let rs : List (String × Ready) := [("B", .base), ("NC", .noCongest), ("NA", .noActive)]
  let gs : List (String × Gate) := [("G0", .none), ("GR", .ready), ("GB", .birth), ("Off", .off)]
  let cs : List (String × CmpV) := [("M2", .m2), ("RP", .rp), ("RPM", .rpm)]
  (rs.flatMap fun (rn, r) => gs.flatMap fun (gn, g) => cs.map fun (cn, cm) =>
    (s!"mv{rn}{gn}{cn}", { ready := r, gate := g, cmp := cm : Cfg })) ++
  (rs.flatMap fun (rn, r) => cs.map fun (cn, cm) =>
    (s!"mv{rn}G0{cn}U", { track := false, ready := r, cmp := cm : Cfg }))

end PPLLMovedBit
