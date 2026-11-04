import Lean.Data.Json
import Leader.Wu.Protocol.State
import Leader.Wu.Authorization.ProvenanceMarks
import Leader.Wu.Authorization.DebrisHygiene
import Leader.Wu.Sim.RawCodec

/-!
# `authFchampNF` regression: the same D++F* writer-normalisation battery as `ZZSimClaimsAuth`

`authFchampNF`-variant twin of `Leader/Wu/Sim/AuthWriterNormalisationHygiene.lean` (identical apart from
`champCfg`), for the `authFchampNF` variant of the `authFchamp` regression
(`run/verification/g62/champ/REGRESSION.md`): `authFchamp` with `seamFenceOn := false`.

Design-exploration tool, not a proof certificate (Task B(ii) of
the `Leader/Wu/Authorization/DebrisHygiene.lean` regression, `run/verification/g62/champ/REGRESSION.md`).
Byte-for-byte the same PRNG, in-domain core generator, `W_wr = D ++ F*` word, and
`LeaderlessBitFrozen` predicate as `Leader.Wu.Sim.AuthWriterNormalisation` (copied verbatim for the same
reason that file gives for copying from `Leader.Wu.Sim.OverwritingGenerationClaims`: it declares its own
top-level `main`, so it cannot be `import`ed here without colliding `_root_.main`). The
only substantive change is `stepArr`, which now runs `PPLLAuthChamp.champStep` under
`PPLLAuthChamp.authFchampNF` instead of `PPLLAuthF.pipeline` under `authFplusmcc`.

This battery is mandatory: `emptyScrub` is a real departure from Wu's CLEAN
semantics that can let CLEAN-killable disconnected fragments persist, so the same grid
this file's twin already ran clean on `authFplusmcc` (8 (psi,n) pairs, 2000 seeds each,
`run/verification/g62/fab/ZDIV.md` §28) is rerun here on `authFchampNF`.
-/

set_option autoImplicit false

open Lean

namespace ZZSimClaimsAuthChampNF

open PPLLAuthF (AuthState variants)
open PPLLAuthChamp (ChampCfg champStep authFchampNF)

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

def nextPath45Label (g : Rng) (ψ : Nat) : Rng × Int :=
  let (g, v) := nextNat g (ψ + 1)
  (g, Int.ofNat v - 1)

def finOfNatBound (k v : Nat) (hk : 0 < k) : Fin k := ⟨v % k, Nat.mod_lt v hk⟩

instance : Inhabited MainState := ⟨.none⟩
instance : Inhabited WriteState := ⟨.none⟩
instance : Inhabited WriteAction := ⟨.none⟩

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

def fwdEdges (base ψ : Nat) : Array Nat := ((List.range (ψ - 1)).map (base + ·)).toArray
def egk (base k : Nat) : Nat := base + k
def bGEdge (base n : Nat) : Nat := (base + n - 1) % n
def dG (base ψ : Nat) : Array Nat := (fwdEdges base ψ).push (egk base (ψ - 2))
def fG (base ψ n : Nat) : Array Nat := #[egk base 0, bGEdge base n] ++ dG base ψ
def wordD (m ψ : Nat) : Array Nat := (List.range m).foldl (fun acc g => acc ++ dG (g * ψ) ψ) #[]
def fGStar (base ψ n : Nat) : Array Nat :=
  (List.range (ψ - 1)).foldl (fun acc _ => acc ++ fG base ψ n) #[]
def wordFStar (m ψ n : Nat) : Array Nat :=
  (List.range m).foldl (fun acc g => acc ++ fGStar (g * ψ) ψ n) #[]
def wordDFStar (m ψ n : Nat) : Array Nat := wordD m ψ ++ wordFStar m ψ n

/-- `authFchamp`'s `ChampCfg` (`authFplusmcc` base plus the three flags), fixed
directly rather than looked up (`PPLLAuthF.variants` does not carry `ChampCfg` entries). -/
def champCfg : ChampCfg := authFchampNF

def randColor (g : Rng) : Rng × Fin 3 :=
  let (g, v) := nextNat g 3
  (g, finOfNatBound 3 v (by decide))

def randScope (g : Rng) : Rng × PPLLAuthF.P2Scope :=
  let (g, b) := nextBool g
  (g, if b then PPLLAuthF.P2Scope.session else PPLLAuthF.P2Scope.line)

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

def randRingAuth {ψ : Nat} (g0 : Rng) (n κ : Nat) (hψ : ψ > 0) : Rng × Array (AuthState ψ) :=
  (List.range n).foldl
    (fun (acc : Rng × Array (AuthState ψ)) i =>
      let (g, arr) := acc
      let lbl : Fin ψ := ⟨i % ψ, Nat.mod_lt i hψ⟩
      let (g', s) := randAuthState (ψ := ψ) g κ lbl
      (g', arr.push s))
    (g0, #[])

def defaultAuthState {ψ : Nat} (hψ : ψ > 0) : AuthState ψ := { core := defaultAgentState hψ }

def getA {ψ : Nat} (hψ : ψ > 0) (c : Array (AuthState ψ)) (i : Nat) : AuthState ψ :=
  c.getD i (defaultAuthState hψ)

def anyLeader {ψ : Nat} (c : Array (AuthState ψ)) : Bool := c.any (·.core.leader)

def bitsOf {ψ : Nat} (c : Array (AuthState ψ)) : Array Bool := c.map (·.core.bit)

/-- The one substantive change relative to `ZZSimClaimsAuth.stepArr`: `champStep` under
`authFchamp` instead of `PPLLAuthF.pipeline` under `authFplusmcc`. -/
def stepArr {ψ : Nat} (hψ : ψ > 0) (c : Array (AuthState ψ)) (e : Nat) : Array (AuthState ψ) :=
  let n := c.size
  let e1 := (e + 1) % n
  let (l', r') := champStep hψ K champCfg (getA hψ c e) (getA hψ c e1)
  (c.set! e l').set! e1 r'

def encodeAuthState {ψ : Nat} (a : AuthState ψ) : Json :=
  Json.mkObj [("core", PPLLSimRawCodec.encodeState a.core),
    ("path_mark", toJson a.path_mark.val), ("ctrl_mark", toJson a.ctrl_mark.val),
    ("path2_scope", toJson (match a.path2_scope with | .session => "session" | .line => "line")),
    ("path2_mark", toJson a.path2_mark.val), ("path4_mark", toJson a.path4_mark.val),
    ("path5_mark", toJson a.path5_mark.val)]

def ringJsonAuth {ψ : Nat} (c : Array (AuthState ψ)) : Json := Json.arr (c.map encodeAuthState)

def target3 (p : Path3Info) : Bool := p.bit == 1

def terminalSafe {ψ : Nat} (u : AuthState ψ) : Bool :=
  match u.core.path3 with
  | none => true
  | some p => u.core.bit == target3 p

def headOW {ψ : Nat} (u : AuthState ψ) : Bool :=
  match u.core.path3 with
  | some p => p.label == 0 && p.flag == 1 && u.core.bit && p.bit == 0
  | none => false

def pendingOWGroup {ψ : Nat} (hψ : ψ > 0) (base : Nat) (c : Array (AuthState ψ)) : Bool :=
  (List.range ψ).any fun k => decide ((getA hψ c (base + k)).core.write = WriteAction.overwrite)

def noIncAll {ψ : Nat} (hψ : ψ > 0) (n : Nat) (c : Array (AuthState ψ)) : Bool :=
  (List.range n).all fun i =>
    let u := (getA hψ c i).core
    decide (u.write ≠ WriteAction.increment_group) &&
    decide (u.write_state ≠ WriteState.increment_group)

def leaderlessBitFrozen {ψ : Nat} (hψ : ψ > 0) (m n : Nat) (c : Array (AuthState ψ)) : Bool :=
  noIncAll hψ n c &&
  (List.range m).all fun g =>
    let base := g * ψ
    terminalSafe (getA hψ c (base + (ψ - 1))) ||
      (!headOW (getA hψ c base) && !pendingOWGroup hψ base c)

structure FailAuth (ψ : Nat) where
  pre : Array (AuthState ψ)
  word : Array Nat
  step : Nat
  edge : Nat
  postWord : Array (AuthState ψ)
  schedule : Array Nat

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
  leaderDuringWord : Bool
  walkLeaderAppeared : Bool := false
  predicateAtWordEnd : Bool := false
  predicateAtWalkEnd : Bool := false
  fail : Option (FailAuth ψ) := none

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
            IO.eprintln s!"authwr-champ psi={ψ} n={n} progress {si}/{states}"
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

end ZZSimClaimsAuthChampNF

open ZZSimClaimsAuthChampNF in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["grid", ψ, n, states, edges, seed, out] =>
    match ψ.toNat?, n.toNat?, states.toNat?, edges.toNat?, seed.toNat? with
    | some ψ, some n, some states, some edges, some seed => runGrid ψ n states edges seed out
    | _, _, _, _, _ => IO.eprintln "numeric arguments expected"; return 2
  | _ =>
    IO.eprintln "usage: sim-claims-auth-champ grid PSI N STATES EDGES SEED OUT"
    return 2
