import Lean.Data.Json
import Leader.Wu.Protocol.State
import Leader.Wu.Authorization.ProvenanceMarks
import Leader.Wu.Sim.RawCodec

/-!
# Simulation test of the stage-2 writer-normalisation claim on `authFplusmcc`
(`run/verification/g62/fab/ZDIV.md` §25)

Design-exploration tool, not a proof certificate.  Tests, on the real `AuthState ψ` domain and the real
`PPLLAuthF.pipeline` transition for the `authFplusmcc` variant (no reimplementation), the
claim:

> From a random reset-free, leaderless, in-domain configuration with perfect labels, apply
> `W_wr = D ++ F*_0 ++ ... ++ F*_(m-1)` (`ZZSimClaims.wordDFStar`).  Either a leader appears
> somewhere along the word, or the endpoint is `LeaderlessBitFrozen` and every
> further leaderless interaction preserves both the bit vector and `LeaderlessBitFrozen`.

This module reuses `ZZSimClaims`'s PRNG, in-domain core generator (`randAgentState`, which
draws every `AgentState` field independently within its declared `inProtocolDomain` range)
and word builders (`wordDFStar`) *verbatim*, copied byte-for-byte into the `ZZSimClaimsAuth`
namespace below rather than `import`ed: `ZZSimClaims.lean` is itself a `lean_exe` root module
with a top-level `def main`, and Lean does not allow a second top-level `main` to coexist
with one already brought into scope by `import` (the two would collide as the same
`_root_.main` declaration), so this file cannot `import Leader.Wu.Sim.OverwritingGenerationClaims` and also declare
its own `main`.  Only the local transition and the leaderless-bit predicate are new.
`reset_cmd` and `echo` are forced to `false` on every generated core
(reset-free ambient assumption; `echo` is not part of the tested mechanism and is held
inert), `leader` is forced to `false` (leaderless), and the six `AuthF` provenance sidecars
(`path_mark`, `ctrl_mark`, `path2_mark`, `path4_mark`, `path5_mark`, `path2_scope`) are drawn
independently at random on top of the in-domain core.

`LeaderlessBitFrozen` is implemented literally from its field definition (terminal
safety, a persistent head overwrite source, a pending in-flight overwrite, no increment
debt); see `leaderlessBitFrozen` below.  The provenance sidecars play no role in the
predicate.
-/

set_option autoImplicit false

open Lean

namespace ZZSimClaimsAuth

open PPLLAuthF (AuthState Cfg pipeline variants ProvColor P2Scope)

/-! ## PRNG, in-domain core generator and `D ++ F*` word builder

Copied verbatim from `Leader.Wu.Sim.OverwritingGenerationClaims` (same generator, same words), for the reason given
in the module docstring: importing that file would collide its `main` with this file's.  Any
future change to `ZZSimClaims`'s PRNG or these builders should be mirrored here by hand. -/

def K : Nat := 2

abbrev Rng := UInt64

def xorshift (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

def nextNat (g : Rng) (bound : Nat) : Rng × Nat :=
  let g := xorshift g
  (g, (g % UInt64.ofNat (max bound 1)).toNat)

def nextBool (g : Rng) : Rng × Bool :=
  let (g, v) := nextNat g 2
  (g, v == 1)

/-- Uniform in `[-1, ψ-1]` (ψ+1 choices), the `path4`/`path5` label domain. -/
def nextPath45Label (g : Rng) (ψ : Nat) : Rng × Int :=
  let (g, v) := nextNat g (ψ + 1)
  (g, Int.ofNat v - 1)

def finOfNatBound (k v : Nat) (hk : 0 < k) : Fin k := ⟨v % k, Nat.mod_lt v hk⟩

instance : Inhabited MainState := ⟨.none⟩
instance : Inhabited WriteState := ⟨.none⟩
instance : Inhabited WriteAction := ⟨.none⟩

/-- A trivial, well-formed `AgentState` (needed only as an `Array.getD` fallback that is never
actually returned, since every index used is in bounds by construction). -/
def defaultAgentState {ψ : Nat} (hψ : ψ > 0) : AgentState ψ :=
  { leader := false, probe := false, phase := false, bit := false, wait := false
    , state := .none, path := .bot, reset := false, carry := false, count := 0
    , label := ⟨0, hψ⟩, h_field := false, path2 := none, path3 := none, path4 := none
    , path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false
    , signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩, shield := false
    , write_state := .none, write := .none, last := false, last_set := false
    , last_unset := false, b_carry := false, gen_ws := false, ws_echo := false
    , signal_ws := false }

def allMainStates : Array MainState :=
  #[.produce, .done, .depart, .none, .congest, .lock, .compare1, .compare2,
    .eliminate_signal, .CHECK_ready, .equal, .larger, .less, .toss, .toss_done]

def allWriteStates : Array WriteState :=
  #[.depart, .ready, .increment_WS, .increment_WS_done, .done, .equal, .larger, .less,
    .produce, .overwrite, .move_flip, .move, .increment_group, .none]

def allWriteActions : Array WriteAction :=
  #[.overwrite, .move_flip, .move, .increment_group, .none]

def randMainState (g : Rng) : Rng × MainState :=
  let (g, i) := nextNat g allMainStates.size; (g, allMainStates[i]!)

def randWriteState (g : Rng) : Rng × WriteState :=
  let (g, i) := nextNat g allWriteStates.size; (g, allWriteStates[i]!)

def randWriteAction (g : Rng) : Rng × WriteAction :=
  let (g, i) := nextNat g allWriteActions.size; (g, allWriteActions[i]!)

def randPathInfo (g : Rng) (ψ : Nat) : Rng × PathInfo :=
  let (g, z) := nextBool g
  if z then (g, .bot)
  else
    let (g, l) := nextNat g ψ
    let (g, b) := nextNat g 2
    (g, .some l b)

def randPath2 (g : Rng) (ψ : Nat) : Rng × Option Path2Info :=
  let (g, z) := nextBool g
  if z then (g, none)
  else
    let (g, l) := nextNat g ψ
    let (g, b) := nextNat g 2
    let (g, p) := nextNat g (ψ + 1)
    let (g, a) := nextNat g 6
    (g, some { label := l, bit := b, position := p, action := a + 1 })

def randPath3 (g : Rng) (ψ : Nat) : Rng × Option Path3Info :=
  let (g, z) := nextBool g
  if z then (g, none)
  else
    let (g, l) := nextNat g ψ
    let (g, b) := nextNat g 2
    let (g, f) := nextNat g 2
    (g, some { label := l, bit := b, flag := f })

def randPath45 (g : Rng) (ψ : Nat) : Rng × Option (Int × Nat) :=
  let (g, z) := nextBool g
  if z then (g, none)
  else
    let (g, l) := nextPath45Label g ψ
    let (g, b) := nextNat g 2
    (g, some (l, b))

/-- A fully random `AgentState`, all fields within their declared domain ranges, with
`label`/`leader` fixed by the caller (perfectly labelled, leaderless). -/
def randAgentState (g : Rng) (ψ κ : Nat) (lbl : Fin ψ) (leader : Bool) : Rng × AgentState ψ :=
  let (g, probe) := nextBool g
  let (g, phase) := nextBool g
  let (g, bit) := nextBool g
  let (g, wait) := nextBool g
  let (g, state) := randMainState g
  let (g, path) := randPathInfo g ψ
  let (g, reset) := nextBool g
  let (g, carry) := nextBool g
  let (g, count) := nextNat g (κ + 1)
  let (g, h_field) := nextBool g
  let (g, path2) := randPath2 g ψ
  let (g, path3) := randPath3 g ψ
  let (g, path4) := randPath45 g ψ
  let (g, path5) := randPath45 g ψ
  let (g, p) := nextBool g
  let (g, p_carry) := nextBool g
  let (g, reset_cmd) := nextBool g
  let (g, echo) := nextBool g
  let (g, sbv) := nextNat g 2
  let (g, blv) := nextNat g 3
  let (g, shield) := nextBool g
  let (g, write_state) := randWriteState g
  let (g, write) := randWriteAction g
  let (g, last) := nextBool g
  let (g, last_set) := nextBool g
  let (g, last_unset) := nextBool g
  let (g, b_carry) := nextBool g
  let (g, gen_ws) := nextBool g
  let (g, ws_echo) := nextBool g
  let (g, signal_ws) := nextBool g
  (g, { leader := leader, probe, phase, bit, wait, state, path, reset, carry, count,
        label := lbl, h_field, path2, path3, path4, path5, p, p_carry, reset_cmd, echo,
        signal_B := finOfNatBound 2 sbv (by decide), bullet := finOfNatBound 3 blv (by decide),
        shield, write_state, write, last, last_set, last_unset, b_carry, gen_ws, ws_echo,
        signal_ws })

/-- `F_G` relative to a group base: `e0,…,e(ψ-2)`, `ψ-1` edges. -/
def fwdEdges (base ψ : Nat) : Array Nat := ((List.range (ψ - 1)).map (base + ·)).toArray

/-- `E(g,k)`, the edge from cell `g*ψ+k` to `g*ψ+k+1`. -/
def egk (base k : Nat) : Nat := base + k

/-- `B_g`, the edge from the previous group's terminal into `g`'s head. -/
def bGEdge (base n : Nat) : Nat := (base + n - 1) % n

/-- `D_g = E(g,0),…,E(g,ψ-2),E(g,ψ-2)` (forward sweep, terminal edge served twice), `ψ` edges. -/
def dG (base ψ : Nat) : Array Nat := (fwdEdges base ψ).push (egk base (ψ - 2))

/-- `F_g = [E(g,0), B_g] ++ D_g`, `ψ+2` edges. -/
def fG (base ψ n : Nat) : Array Nat := #[egk base 0, bGEdge base n] ++ dG base ψ

/-- `D = ⋃_g D_g`, length `n`. -/
def wordD (m ψ : Nat) : Array Nat := (List.range m).foldl (fun acc g => acc ++ dG (g * ψ) ψ) #[]

/-- `F*_g = F_g` repeated `ψ-1` times (the repaired finite word: enough whole
attempts to survive up to `ψ-2` distinct interior `CheckLast` blockers). -/
def fGStar (base ψ n : Nat) : Array Nat :=
  (List.range (ψ - 1)).foldl (fun acc _ => acc ++ fG base ψ n) #[]

/-- `F* = ⋃_g F*_g`. -/
def wordFStar (m ψ n : Nat) : Array Nat :=
  (List.range m).foldl (fun acc g => acc ++ fGStar (g * ψ) ψ n) #[]

/-- `D ++ F*`, the repaired form of the ZDIV §14 writer-drain word (`W_wr`). -/
def wordDFStar (m ψ n : Nat) : Array Nat := wordD m ψ ++ wordFStar m ψ n

/-- `authFplusmcc`'s `Cfg`, looked up by name from `PPLLAuthF.variants` (rather than
hard-coded) so this test tracks the census's naming if the variant list ever changes; the
fallback is unreachable since `"authFplusmcc"` is a fixed entry of `variants`. -/
def authCfg : Cfg :=
  match variants.find? (fun t => t.1 == "authFplusmcc") with
  | some (_, some c) => c
  | _ => {}

/-! ## Random `AuthState`: in-domain core (reset-free, leaderless, `echo = false`) plus
independently random provenance sidecars -/

/-- A uniformly random provenance colour in `Fin 3`. -/
def randColor (g : Rng) : Rng × ProvColor :=
  let (g, v) := nextNat g 3
  (g, finOfNatBound 3 v (by decide))

def randScope (g : Rng) : Rng × P2Scope :=
  let (g, b) := nextBool g
  (g, if b then P2Scope.session else P2Scope.line)

/-- A random `AuthState`: the core is `ZZSimClaims.randAgentState`'s in-domain, leaderless
draw with `reset_cmd`/`echo` forced to `false`; the six sidecars are drawn independently. -/
def randAuthState {ψ : Nat} (g : Rng) (κ : Nat) (lbl : Fin ψ) : Rng × AuthState ψ :=
  let (g, core0) := randAgentState g ψ κ lbl false
  let core : AgentState ψ := { core0 with echo := false, reset_cmd := false }
  let (g, pm) := randColor g
  let (g, cm) := randColor g
  let (g, sc) := randScope g
  let (g, p2m) := randColor g
  let (g, p4m) := randColor g
  let (g, p5m) := randColor g
  (g, { core := core, path_mark := pm, ctrl_mark := cm, path2_scope := sc, path2_mark := p2m,
        path4_mark := p4m, path5_mark := p5m })

/-- A leaderless, perfectly labelled, reset-free ring of `n` cells with independently random
cores (in domain) and provenance sidecars. -/
def randRingAuth {ψ : Nat} (g0 : Rng) (n κ : Nat) (hψ : ψ > 0) : Rng × Array (AuthState ψ) :=
  (List.range n).foldl
    (fun (acc : Rng × Array (AuthState ψ)) i =>
      let (g, arr) := acc
      let lbl : Fin ψ := ⟨i % ψ, Nat.mod_lt i hψ⟩
      let (g', s) := randAuthState (ψ := ψ) g κ lbl
      (g', arr.push s))
    (g0, #[])

/-! ## The protocol step (`authFplusmcc`) and JSON codec -/

/-- A trivial well-formed `AuthState` (needed only as an `Array.getD` fallback that is never
actually returned, since every index used is in bounds by construction). -/
def defaultAuthState {ψ : Nat} (hψ : ψ > 0) : AuthState ψ := { core := defaultAgentState hψ }

def getA {ψ : Nat} (hψ : ψ > 0) (c : Array (AuthState ψ)) (i : Nat) : AuthState ψ :=
  c.getD i (defaultAuthState hψ)

def anyLeader {ψ : Nat} (c : Array (AuthState ψ)) : Bool := c.any (·.core.leader)

def bitsOf {ψ : Nat} (c : Array (AuthState ψ)) : Array Bool := c.map (·.core.bit)

def stepArr {ψ : Nat} (hψ : ψ > 0) (c : Array (AuthState ψ)) (e : Nat) : Array (AuthState ψ) :=
  let n := c.size
  let e1 := (e + 1) % n
  let (l', r') := pipeline hψ K authCfg (getA hψ c e) (getA hψ c e1)
  (c.set! e l').set! e1 r'

def encodeAuthState {ψ : Nat} (a : AuthState ψ) : Json :=
  Json.mkObj [("core", PPLLSimRawCodec.encodeState a.core),
    ("path_mark", toJson a.path_mark.val), ("ctrl_mark", toJson a.ctrl_mark.val),
    ("path2_scope", toJson (match a.path2_scope with | .session => "session" | .line => "line")),
    ("path2_mark", toJson a.path2_mark.val), ("path4_mark", toJson a.path4_mark.val),
    ("path5_mark", toJson a.path5_mark.val)]

def ringJsonAuth {ψ : Nat} (c : Array (AuthState ψ)) : Json := Json.arr (c.map encodeAuthState)

/-! ## `LeaderlessBitFrozen`, implemented literally from the field definition -/

/-- `target(p) := (p.bit = 1)`. -/
def target3 (p : Path3Info) : Bool := p.bit == 1

/-- `TerminalSafe_g(C)`: the group terminal has no resident `path3`, or its resident
`path3`'s target agrees with the physical `bit` (the idempotence condition for
`writeActionApplyOverwrite`). -/
def terminalSafe {ψ : Nat} (u : AuthState ψ) : Bool :=
  match u.core.path3 with
  | none => true
  | some p => u.core.bit == target3 p

/-- `HeadOW_g(C)`: the physical head carries a persistent overwrite source (`path3 = some p`,
`p.label = 0`, `p.flag = 1`, `core.bit = true`, `p.bit = 0`). -/
def headOW {ψ : Nat} (u : AuthState ψ) : Bool :=
  match u.core.path3 with
  | some p => p.label == 0 && p.flag == 1 && u.core.bit && p.bit == 0
  | none => false

/-- `PendingOW_g(C)`: some cell of group `g` (base `base`, size `ψ`) has `write = overwrite`
in flight. -/
def pendingOWGroup {ψ : Nat} (hψ : ψ > 0) (base : Nat) (c : Array (AuthState ψ)) : Bool :=
  (List.range ψ).any fun k => decide ((getA hψ c (base + k)).core.write = WriteAction.overwrite)

/-- `NoInc(C)`: no cell has a pending `write = increment_group` or `write_state =
increment_group`. -/
def noIncAll {ψ : Nat} (hψ : ψ > 0) (n : Nat) (c : Array (AuthState ψ)) : Bool :=
  (List.range n).all fun i =>
    let u := (getA hψ c i).core
    decide (u.write ≠ WriteAction.increment_group) &&
    decide (u.write_state ≠ WriteState.increment_group)

/-- `LeaderlessBitFrozen(C)`: `NoInc(C)` and, for every group `g < m`,
`TerminalSafe_g(C) ∨ (¬HeadOW_g(C) ∧ ¬PendingOW_g(C))`.  Ambient assumptions (leaderless,
perfect labels, `ψ ≥ 2`) are the caller's responsibility. -/
def leaderlessBitFrozen {ψ : Nat} (hψ : ψ > 0) (m n : Nat) (c : Array (AuthState ψ)) : Bool :=
  noIncAll hψ n c &&
  (List.range m).all fun g =>
    let base := g * ψ
    terminalSafe (getA hψ c (base + (ψ - 1))) ||
      (!headOW (getA hψ c base) && !pendingOWGroup hψ base c)

/-! ## The test: `W_wr` then a long random leaderless walk -/

structure FailAuth (ψ : Nat) where
  pre : Array (AuthState ψ)
  word : Array Nat
  step : Nat
  edge : Nat
  postWord : Array (AuthState ψ)
  schedule : Array Nat

/-- Runs `edges` further random-edge interactions from `c0`, stopping the moment a leader
appears (the freezing claim is then vacuous) or the moment some leaderless interaction
changes a cell's `bit` (a counterexample).  Returns whether a leader appeared during the
walk, the final configuration, and the failure record (if any). -/
def walkCheck {ψ : Nat} (hψ : ψ > 0) (n : Nat) (c0 : Array (AuthState ψ)) (edges : Nat)
    (g0 : Rng) : Rng × Array (AuthState ψ) × Bool × Option (Nat × Nat × Array Nat) := Id.run do
  let mut c := c0
  let mut g := g0
  let mut sched : Array Nat := #[]
  for step in [0:edges] do
    if anyLeader c then
      return (g, c, true, none)
    let bitsPre := bitsOf c
    let (g', e) := nextNat g n
    g := g'
    sched := sched.push e
    c := stepArr hψ c e
    if anyLeader c then
      return (g, c, true, none)
    if bitsOf c != bitsPre then
      return (g, c, false, some (step + 1, e, sched))
  return (g, c, false, none)

structure SeedResult (ψ : Nat) where
  /-- A leader appeared while applying `W_wr` itself (the claim's first disjunct). -/
  leaderDuringWord : Bool
  /-- A leader appeared later, during the post-word random walk (bits were frozen up to
  that point; the claim's freezing obligation is then discharged, not violated). -/
  walkLeaderAppeared : Bool := false
  /-- `LeaderlessBitFrozen` holds right after `W_wr` (meaningful iff `!leaderDuringWord`). -/
  predicateAtWordEnd : Bool := false
  /-- `LeaderlessBitFrozen` still holds at the walk's end, given the walk finished with no
  bit change and no leader ever appearing (meaningful iff `!leaderDuringWord ∧
  !walkLeaderAppeared`; the closure claim, second sentence). -/
  predicateAtWalkEnd : Bool := false
  fail : Option (FailAuth ψ) := none

/-- One seed's test: apply `W_wr = wordDFStar m ψ n`, then check the walk. -/
def testSeed {ψ : Nat} (hψ : ψ > 0) (m n : Nat) (orig : Array (AuthState ψ)) (edges : Nat)
    (g0 : Rng) : Rng × SeedResult ψ := Id.run do
  let word := wordDFStar m ψ n
  let mut c := orig
  let mut leaderSeen := anyLeader c
  for e in word do
    c := stepArr hψ c e
    leaderSeen := leaderSeen || anyLeader c
  if leaderSeen then
    return (g0, { leaderDuringWord := true })
  let postWord := c
  let predWordEnd := leaderlessBitFrozen hψ m n c
  let (g, cFinal, walkLeader, fail) := walkCheck hψ n c edges g0
  match fail with
  | some (step, edge, sched) =>
    return (g, { leaderDuringWord := false, predicateAtWordEnd := predWordEnd,
                 fail := some { pre := orig, word := word, step := step, edge := edge,
                                postWord := postWord, schedule := sched } })
  | none =>
    let predWalkEnd := !walkLeader && leaderlessBitFrozen hψ m n cFinal
    return (g, { leaderDuringWord := false, walkLeaderAppeared := walkLeader,
                 predicateAtWordEnd := predWordEnd, predicateAtWalkEnd := predWalkEnd })

/-! ## Grid driver -/

def runGrid (ψ n states edges seed : Nat) (out : System.FilePath) : IO UInt32 := do
  if hψ : ψ > 0 then
    if hn : n % ψ = 0 then
      if ψ ≥ 2 then
        let m := n / ψ
        let h ← IO.FS.Handle.mk out .write
        let mut leaderCount : Nat := 0
        let mut frozenCount : Nat := 0
        let mut failCount : Nat := 0
        let mut predWordEndCount : Nat := 0
        let mut predWalkEndCount : Nat := 0
        let mut walkLeaderCount : Nat := 0
        let mut g : Rng := (UInt64.ofNat (seed * 1000003 + 41)) ||| 1
        for si in [0:states] do
          let (g', ring) := randRingAuth g n K hψ
          g := g'
          let (g'', res) := testSeed hψ m n ring edges g
          g := g''
          if res.leaderDuringWord then
            leaderCount := leaderCount + 1
          else
            match res.fail with
            | some f =>
              failCount := failCount + 1
              h.putStrLn (Json.mkObj [("kind", toJson "failure"), ("psi", toJson ψ),
                ("n", toJson n), ("state_index", toJson si), ("step", toJson f.step),
                ("edge", toJson f.edge), ("pre", ringJsonAuth f.pre),
                ("post_word", ringJsonAuth f.postWord), ("schedule", toJson f.schedule)]).compress
              h.flush
            | none =>
              frozenCount := frozenCount + 1
              if res.predicateAtWordEnd then predWordEndCount := predWordEndCount + 1
              if res.predicateAtWalkEnd then predWalkEndCount := predWalkEndCount + 1
              if res.walkLeaderAppeared then walkLeaderCount := walkLeaderCount + 1
          if si % 200 == 0 && si > 0 then
            IO.eprintln s!"authwr psi={ψ} n={n} progress {si}/{states}"
        h.putStrLn (Json.mkObj [("kind", toJson "summary"), ("psi", toJson ψ), ("n", toJson n),
          ("states", toJson states), ("edges_per_state", toJson edges),
          ("leader_during_word", toJson leaderCount), ("frozen", toJson frozenCount),
          ("failures", toJson failCount),
          ("predicate_holds_at_word_end_of_frozen", toJson predWordEndCount),
          ("frozen_walk_leader_appeared", toJson walkLeaderCount),
          ("predicate_holds_at_walk_end_of_frozen", toJson predWalkEndCount)]).compress
        h.flush
        return 0
      else throw (IO.userError "psi must be >= 2")
    else throw (IO.userError "n must be a multiple of psi")
  else throw (IO.userError "psi must be positive")

/-! ## Lifting `ZZSimClaims`'s saved `zdivOWF` `D ++ F` failure (ψ=3, n=12) into `AuthState`
with every provenance mark at its canonical colour 0 / scope `line`, replayed through
`W_wr` and `authFplusmcc` (a different word and a different transition, so this is a fresh
test, not a rerun) -/

def runLiftOld (ψ n edges seed : Nat) (ringPath out : System.FilePath) : IO UInt32 := do
  if hψ : ψ > 0 then
    if hn : n % ψ = 0 then
      let m := n / ψ
      let raw ← IO.FS.readFile ringPath
      let j ← IO.ofExcept (Json.parse raw)
      let arr ← IO.ofExcept j.getArr?
      let mut c : Array (AuthState ψ) := #[]
      for je in arr do
        let core ← IO.ofExcept (PPLLSimRawCodec.decodeState (psi := ψ) je)
        c := c.push ({ core := core } : AuthState ψ)
      if c.size != n then
        throw (IO.userError s!"ring has {c.size} cells, expected {n}")
      else
        let g0 : Rng := (UInt64.ofNat (seed * 1000003 + 97)) ||| 1
        let (_, res) := testSeed hψ m n c edges g0
        let h ← IO.FS.Handle.mk out .write
        h.putStrLn (Json.mkObj [("kind", toJson "liftold"), ("psi", toJson ψ), ("n", toJson n),
          ("leader_during_word", toJson res.leaderDuringWord),
          ("walk_leader_appeared", toJson res.walkLeaderAppeared),
          ("predicate_at_word_end", toJson res.predicateAtWordEnd),
          ("predicate_at_walk_end", toJson res.predicateAtWalkEnd),
          ("failed", toJson res.fail.isSome)]).compress
        match res.fail with
        | some f =>
          h.putStrLn (Json.mkObj [("kind", toJson "liftold_failure"), ("step", toJson f.step),
            ("edge", toJson f.edge), ("pre", ringJsonAuth f.pre),
            ("post_word", ringJsonAuth f.postWord), ("schedule", toJson f.schedule)]).compress
        | none => pure ()
        h.flush
        return 0
    else throw (IO.userError "n must be a multiple of psi")
  else throw (IO.userError "psi must be positive")

end ZZSimClaimsAuth

open ZZSimClaimsAuth in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["grid", ψ, n, states, edges, seed, out] =>
    match ψ.toNat?, n.toNat?, states.toNat?, edges.toNat?, seed.toNat? with
    | some ψ, some n, some states, some edges, some seed => runGrid ψ n states edges seed out
    | _, _, _, _, _ => IO.eprintln "numeric arguments expected"; return 2
  | ["liftold", ψ, n, edges, seed, ringPath, out] =>
    match ψ.toNat?, n.toNat?, edges.toNat?, seed.toNat? with
    | some ψ, some n, some edges, some seed => runLiftOld ψ n edges seed ringPath out
    | _, _, _, _ => IO.eprintln "numeric arguments expected"; return 2
  | _ =>
    IO.eprintln "usage: sim-claims-auth grid PSI N STATES EDGES SEED OUT
       | liftold PSI N EDGES SEED RING.json OUT"
    return 2
