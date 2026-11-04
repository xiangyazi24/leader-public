import Std.Data.HashMap
import Leader.Wu.Sim.AuthHygieneTransition

/-!
# Shared library of `ZZAuthChampCensus` (no `main`)

Verbatim copy of `Leader/Wu/Sim/AuthHygieneClosure.lean` lines 35–547 (namespace renamed to
`ZZAuthChampLib`), so that other `--run` tools can import the interning BFS, the random
dirty-ring generator, `closureHasLeader`, `cell`, `parseBits`/`parseT`, and the
`compareWith` / ablation helpers without importing that file's root-level `main`
(Lean forbids a second `main` declaration).  Design-exploration tool, not a proof.
-/

set_option autoImplicit false

open Lean PPLLAuthF PPLLAuthSim

namespace ZZAuthChampLib

abbrev Agent (ψ κ : Nat) := PPLLAuthSim.AuthB ψ κ

@[inline] def finOfNat (bound : Nat) (hbound : 0 < bound) (v : Nat) : Fin bound :=
  ⟨v % bound, Nat.mod_lt v hbound⟩

/-! ## Interned closure graph over the bounded carrier (`ZZStage3Global.Ag`, generalised to
any transition function rather than a hard-coded `"authFplusmcc"` lookup). -/

structure Ag (ψ κ : Nat) where
  arr : Array (Agent ψ κ) := #[]
  ix : Std.HashMap String Nat := {}
  memo : Std.HashMap UInt64 UInt64 := {}

def Ag.intern {ψ κ : Nat} (g : Ag ψ κ) (a : Agent ψ κ) : Ag ψ κ × Nat :=
  let key := PPLLAuthSim.key a
  match g.ix[key]? with
  | some i => (g, i)
  | none => let i := g.arr.size; ({ g with arr := g.arr.push a, ix := g.ix.insert key i }, i)

def Ag.step {ψ κ : Nat} (g : Ag ψ κ)
    (tr : Agent ψ κ → Agent ψ κ → Except String (Agent ψ κ × Agent ψ κ)) (x y : Nat) :
    Except String (Ag ψ κ × Nat × Nat) :=
  let key := (x.toUInt64 <<< 32) ||| y.toUInt64
  match g.memo[key]? with
  | some r => .ok (g, (r >>> 32).toNat, (r &&& 0xFFFFFFFF).toNat)
  | none =>
    match g.arr[x]?, g.arr[y]? with
    | some u, some v => do
      let q ← tr u v
      let (g1, ia) := g.intern q.1
      let (g2, ib) := g1.intern q.2
      pure ({ g2 with memo := g2.memo.insert key ((ia.toUInt64 <<< 32) ||| ib.toUInt64) }, ia, ib)
    | _, _ => .error "agent index out of range"

def pathInfo {ψ κ : Nat} (a : Agent ψ κ) : Option (Nat × Nat) :=
  match a.core.path with
  | .some l b => some (l.val, b.val)
  | .bot => none

def cellStr {ψ κ : Nat} (a : Agent ψ κ) : String :=
  let p := match pathInfo a with | some (l, b) => s!"{l}/{b}" | none => "--"
  let st := (reprStr a.core.state).replace "MainState." ""
  let t := match a.core.path2 with | some t => s!" A{t.action.val}@{t.position.val}" | none => ""
  s!"[{if a.core.bit then 1 else 0} {p} {st}{t} c{a.m.ctrl.val}]"

def variantTransition (variant : String) {ψ : Nat} (hψ : ψ > 0) (κ : Nat) :
    Except String (Agent ψ κ → Agent ψ κ → Except String (Agent ψ κ × Agent ψ κ)) :=
  PPLLAuthSimChamp.localTransition variant hψ κ

/-! ## `cell`: a hand-specified Fresh cell on the bounded carrier (`ZZStage3Global.cell`). -/

def cell (psi kappa i : Nat) (hpsi : 0 < psi) (bit : Bool) (tb : Option Bool) (mark : Fin 3) :
    AuthB psi kappa :=
  let label : Fin psi := finOfNat psi hpsi (i % psi)
  let core : BoundedAgentState psi kappa :=
    { leader := false, probe := false, phase := false, bit := bit, wait := false,
      state := (if tb.isSome then .depart else .none),
      path := (match tb with
        | some tbit => .some label (finOfNat 2 (by omega) (if tbit then 1 else 0))
        | none => .bot),
      reset := false, carry := false, count := finOfNat (kappa + 1) (by omega) 0,
      label := label, h_field := false, path2 := none,
      path3 := none, path4 := none, path5 := none, p := false, p_carry := false,
      reset_cmd := false, echo := false, signal_B := finOfNat 2 (by omega) 0,
      bullet := finOfNat 3 (by omega) 0, shield := false, write_state := .none,
      write := .none, last := false, last_set := false, last_unset := false,
      b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }
  let m : Marks := { path := mark, ctrl := mark, p2 := mark, p4 := 0, p5 := 0, scope := .line }
  ⟨core, m⟩

def parseBits (s : String) : Array Bool := s.toList.toArray.map (· == '1')
def parseT (s : String) : Array (Option Bool) :=
  s.toList.toArray.map fun c => if c == '_' then none else some (c == '1')

/-! ## `word`: the exact BFS closure of `ZZStage3Global.run`, generic in the variant. -/

def word (psi n kappa : Nat) (bitsS tbitsS : String) (cap : Nat) (variant : String)
    (early : Bool := false) : IO UInt32 := do
  if hpsi : psi > 0 then
    let tr ← match variantTransition variant hpsi kappa with
      | .ok t => pure t
      | .error e => throw (IO.userError e)
    let bits := parseBits bitsS
    let tbits := parseT tbitsS
    let mut g : Ag psi kappa := {}
    let mut phys0 : Array Nat := #[]
    for i in [0:n] do
      let mark : Fin 3 := ⟨(i / psi) % 3, by omega⟩
      let (g', k) := g.intern (cell psi kappa i hpsi bits[i]! tbits[i]! mark)
      g := g'
      phys0 := phys0.push k
    let mut visited : Std.HashMap (Array Nat) Nat := {}
    let mut nodes : Array (Array Nat) := #[phys0]
    let mut parent : Array (Nat × Nat) := #[(0, 0)]
    let mut isLeader : Array Bool := #[false]
    visited := visited.insert phys0 0
    let mut succ : Array (Array Nat) := #[]
    let mut qi := 0
    let mut firstLeader : Option Nat := none
    let mut capped := false
    while qi < nodes.size do
      if early && firstLeader.isSome then break
      let phys := nodes[qi]!
      let mut out : Array Nat := #[]
      if isLeader[qi]! then
        succ := succ.push out; qi := qi + 1; continue
      if nodes.size > cap then
        capped := true; succ := succ.push out; qi := qi + 1; continue
      for e in [0:n] do
        let jx := (e + 1) % n
        match g.step tr phys[e]! phys[jx]! with
        | .error err => IO.eprintln s!"err {err}"
        | .ok (g', a', b') =>
          g := g'
          let phys' := (phys.set! e a').set! jx b'
          match visited[phys']? with
          | some id => out := out.push id
          | none =>
            let id := nodes.size
            visited := visited.insert phys' id
            nodes := nodes.push phys'
            parent := parent.push (qi, e)
            let ld := phys'.any fun k => (g.arr[k]?.map (·.core.leader)).getD false
            isLeader := isLeader.push ld
            if ld && firstLeader.isNone then firstLeader := some id
            out := out.push id
      succ := succ.push out
      qi := qi + 1
    IO.println s!"variant={variant} psi={psi} n={n} kappa={kappa} bits={bitsS} tbits={tbitsS}"
    IO.println s!"nodes={nodes.size} capped={capped} leaders={(isLeader.filter id).size}"
    match firstLeader with
    | none => IO.println "no leader found"
    | some t =>
      let mut chain : Array (Nat × Nat) := #[]
      let mut cur := t
      while cur != 0 do
        let (p, e) := parent[cur]!
        chain := chain.push (cur, e)
        cur := p
      chain := chain.reverse
      IO.println s!"shortest word to leader: length {chain.size}, edges {chain.toList.map (·.2)}"
      IO.println s!"  0: {String.join (nodes[0]!.toList.filterMap fun k => g.arr[k]?.map cellStr)}"
      let mut idx := 1
      for (v, e) in chain do
        IO.println s!"  {idx} e{e}: {String.join (nodes[v]!.toList.filterMap fun k => g.arr[k]?.map cellStr)}"
        idx := idx + 1
    return 0
  else throw (IO.userError "psi must be positive")

/-! ## `compare`: random dirty seeds, both variants, from the bounded random generator
(`ZZSimClaimsAuth`'s PRNG and `randAgentState`, copied verbatim for the reason its own
docstring gives: that file is a `lean_exe` root with its own top-level `main`, so it
cannot be `import`ed alongside another `main`). -/

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

/-- Dirty in-domain leaderless core: every field the census domain declares, drawn
independently; `reset_cmd`/`echo` forced `false` (reset-free ambient assumption, matching
`ZZSimClaimsAuth.randAuthState`), `leader` forced `false`. -/
def randAgentState (g : Rng) (ψ κ : Nat) (lbl : Fin ψ) : Rng × AgentState ψ :=
  let (g, probe) := nextBool g
  let (g, phase) := nextBool g
  let (g, bit) := nextBool g
  let (g, wait) := nextBool g
  let (g, state) := randMainState g
  let (g, path) := randPathInfo g ψ
  let (g, carry) := nextBool g
  let (g, count) := nextNat g (κ + 1)
  let (g, h_field) := nextBool g
  let (g, path2) := randPath2 g ψ
  let (g, path3) := randPath3 g ψ
  let (g, path4) := randPath45 g ψ
  let (g, path5) := randPath45 g ψ
  let (g, p) := nextBool g
  let (g, p_carry) := nextBool g
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
  (g, { leader := false, probe, phase, bit, wait, state, path, reset := false, carry, count,
        label := lbl, h_field, path2, path3, path4, path5, p, p_carry, reset_cmd := false,
        echo := false, signal_B := finOfNatBound 2 sbv (by decide),
        bullet := finOfNatBound 3 blv (by decide), shield, write_state, write, last, last_set,
        last_unset, b_carry, gen_ws, ws_echo, signal_ws })

def randColor (g : Rng) : Rng × Fin 3 :=
  let (g, v) := nextNat g 3
  (g, finOfNatBound 3 v (by decide))

def randScope (g : Rng) : Rng × P2Scope :=
  let (g, b) := nextBool g
  (g, if b then P2Scope.session else P2Scope.line)

/-- The all-neutral bounded core at `lbl` (no reification needed: every field is already
at its default value in its bounded type). Used only as `randAuthB`'s fuel-exhausted
fallback, which is never actually reached in practice (`reifyCore` accepts every draw of
`randAgentState`, whose ranges are exactly the bounded domain). -/
def neutralCore {ψ κ : Nat} (lbl : Fin ψ) : BoundedAgentState ψ κ :=
  { leader := false, probe := false, phase := false, bit := false, wait := false,
    state := .none, path := .bot, reset := false, carry := false, count := ⟨0, by omega⟩,
    label := lbl, h_field := false, path2 := none, path3 := none, path4 := none,
    path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false,
    signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩, shield := false,
    write_state := .none, write := .none, last := false, last_set := false,
    last_unset := false, b_carry := false, gen_ws := false, ws_echo := false,
    signal_ws := false }

/-- A random dirty `AuthB` cell: the core reified from a random in-domain `AgentState`,
sidecars drawn independently. `fuel` bounds the retry loop on the rare out-of-domain draw
(structural recursion, no `partial`); the fallback (`fuel = 0`) is `neutralCore`. -/
def randAuthB {ψ κ : Nat} (hψ : ψ > 0) (fuel : Nat) (g : Rng) (lbl : Fin ψ) : Rng × AuthB ψ κ :=
  match fuel with
  | 0 =>
    let (g, pm) := randColor g
    let (g, cm) := randColor g
    let (g, sc) := randScope g
    let (g, p2m) := randColor g
    let (g, p4m) := randColor g
    let (g, p5m) := randColor g
    (g, ⟨neutralCore lbl, { path := pm, ctrl := cm, p2 := p2m, p4 := p4m, p5 := p5m, scope := sc }⟩)
  | fuel + 1 =>
    let (g, core0) := randAgentState g ψ κ lbl
    match PPLLAuthSim.reifyCore (κ := κ) core0 with
    | .error _ => randAuthB hψ fuel (xorshift g) lbl
    | .ok core =>
      let (g, pm) := randColor g
      let (g, cm) := randColor g
      let (g, sc) := randScope g
      let (g, p2m) := randColor g
      let (g, p4m) := randColor g
      let (g, p5m) := randColor g
      (g, ⟨core, { path := pm, ctrl := cm, p2 := p2m, p4 := p4m, p5 := p5m, scope := sc }⟩)

def randRing {ψ κ : Nat} (hψ : ψ > 0) (g0 : Rng) (n : Nat) : Rng × Array (AuthB ψ κ) :=
  (List.range n).foldl
    (fun (acc : Rng × Array (AuthB ψ κ)) i =>
      let (g, arr) := acc
      let lbl : Fin ψ := ⟨i % ψ, Nat.mod_lt i hψ⟩
      let (g', s) := randAuthB (κ := κ) hψ 20 g lbl
      (g', arr.push s))
    (g0, #[])

/-- Capped BFS from a bounded configuration under one transition: does the capped
reachable set contain a leader, and was the cap hit? Reuses no `Ag` state across calls
(fresh interning per seed, matching `word`). -/
def closureHasLeader {ψ κ : Nat} (n : Nat)
    (tr : Agent ψ κ → Agent ψ κ → Except String (Agent ψ κ × Agent ψ κ))
    (g0 : Ag ψ κ) (phys0 : Array Nat) (cap : Nat) : Bool × Bool × Nat := Id.run do
  let mut g := g0
  let mut visited : Std.HashMap (Array Nat) Unit := {}
  visited := visited.insert phys0 ()
  let mut q : Array (Array Nat) := #[phys0]
  let mut qi := 0
  let mut leaderFound := false
  while qi < q.size do
    if q.size > cap then
      return (leaderFound, true, q.size)
    let phys := q[qi]!
    qi := qi + 1
    if phys.any (fun k => (g.arr[k]?.map (·.core.leader)).getD false) then
      leaderFound := true
      continue
    for e in [0:n] do
      let jx := (e + 1) % n
      match g.step tr phys[e]! phys[jx]! with
      | .error _ => pure ()
      | .ok (g', a', b') =>
        g := g'
        let phys' := (phys.set! e a').set! jx b'
        if !visited.contains phys' then
          visited := visited.insert phys' ()
          q := q.push phys'
  return (leaderFound, false, q.size)

def encodeAuthB {ψ κ : Nat} (a : AuthB ψ κ) : Json := PPLLAuthSim.encode a

/-- The full `authFchamp` config plus each of its four flags individually
disabled, for the seed regression ablation
(`run/verification/g62/champ/REGRESSION.md`). -/
def ablationConfigs : List (String × PPLLAuthChamp.ChampCfg) :=
  let a := PPLLAuthChamp.authFchamp
  [ ("full", a),
    ("no_emptyScrub", { a with emptyScrub := false }),
    ("no_seamFence", { a with seamFenceOn := false }),
    ("no_lotteryScrub", { a with lotteryScrub := false }),
    ("no_strictScope", { a with strictScope := false }) ]

/-- All 16 on/off combinations of the four flags (the full power set, not just
each singly removed): `e`=emptyScrub, `sf`=seamFenceOn, `l`=lotteryScrub, `sc`=strictScope.
The all-`false` entry's `champStep` reduces definitionally to `PPLLAuthF.beforeElimination`
under the same `base` Cfg, i.e. exactly `authFplusmcc`'s own pipeline — a built-in sanity
check that the ablation harness is wired correctly (it must reproduce `authFplusmcc`'s
verdict). Used when a single-flag ablation at a given cap does not resolve a seed (every
`no_X` config still shows `capped=true, leader=false`), to check whether some *combination*
of two or more flags is responsible. -/
def ablationPowerSet : List (String × PPLLAuthChamp.ChampCfg) :=
  let a := PPLLAuthChamp.authFchamp
  let bits := [true, false]
  bits.flatMap fun e => bits.flatMap fun sf => bits.flatMap fun l => bits.flatMap fun sc =>
    [(s!"e={e},sf={sf},l={l},sc={sc}",
      { a with emptyScrub := e, seamFenceOn := sf, lotteryScrub := l, strictScope := sc })]

/-- Shared body: rebuild `compare`'s seed exactly, report `authFplusmcc`'s closure, then
report every `(name, cfg)` in `configs` under `champTransitionCfg`. -/
def ablateWith (configs : List (String × PPLLAuthChamp.ChampCfg)) (psi n kappa cap seed : Nat) :
    IO UInt32 := do
  if hpsi : psi > 0 then
    let trPlus ← match variantTransition "authFplusmcc" hpsi kappa with
      | .ok t => pure t
      | .error e => throw (IO.userError e)
    let g0 : Rng := (UInt64.ofNat (seed * 1000003 + 17)) ||| 1
    let (_, ring) := randRing (κ := kappa) hpsi g0 n
    let mut gg : Ag psi kappa := {}
    let mut phys0 : Array Nat := #[]
    for a in ring do
      let (gg', k) := gg.intern a
      gg := gg'
      phys0 := phys0.push k
    let (leaderPlus, capPlus, nodesPlus) := closureHasLeader n trPlus gg phys0 cap
    IO.println s!"seed={seed} cap={cap} authFplusmcc: leader={leaderPlus} capped={capPlus} nodes={nodesPlus}"
    for (name, cfg) in configs do
      let tr := PPLLAuthSimChamp.champTransitionCfg hpsi kappa cfg
      let (leader, capped, nodes) := closureHasLeader n tr gg phys0 cap
      IO.println s!"seed={seed} cap={cap} authFchamp[{name}]: leader={leader} capped={capped} nodes={nodes}"
    return 0
  else throw (IO.userError "psi must be positive")

def ablate (psi n kappa cap seed : Nat) : IO UInt32 :=
  ablateWith ablationConfigs psi n kappa cap seed

def ablateAll (psi n kappa cap seed : Nat) : IO UInt32 :=
  ablateWith ablationPowerSet psi n kappa cap seed

def compare (psi n kappa cap seeds seed0 : Nat) : IO UInt32 := do
  if hpsi : psi > 0 then
    let trPlus ← match variantTransition "authFplusmcc" hpsi kappa with
      | .ok t => pure t
      | .error e => throw (IO.userError e)
    let trChamp ← match variantTransition "authFchamp" hpsi kappa with
      | .ok t => pure t
      | .error e => throw (IO.userError e)
    let mut noLeaderPlus := 0
    let mut noLeaderChamp := 0
    let mut cappedPlus := 0
    let mut cappedChamp := 0
    let mut regressions : Array Nat := #[]
    for s in [0:seeds] do
      let seed := seed0 + s
      let g0 : Rng := (UInt64.ofNat (seed * 1000003 + 17)) ||| 1
      let (_, ring) := randRing (κ := kappa) hpsi g0 n
      let mut gg : Ag psi kappa := {}
      let mut phys0 : Array Nat := #[]
      for a in ring do
        let (gg', k) := gg.intern a
        gg := gg'
        phys0 := phys0.push k
      let (leaderPlus, capPlus, _) := closureHasLeader n trPlus gg phys0 cap
      let (leaderChamp, capChamp, _) := closureHasLeader n trChamp gg phys0 cap
      if !leaderPlus then noLeaderPlus := noLeaderPlus + 1
      if !leaderChamp then noLeaderChamp := noLeaderChamp + 1
      if capPlus then cappedPlus := cappedPlus + 1
      if capChamp then cappedChamp := cappedChamp + 1
      if leaderPlus && !leaderChamp then
        regressions := regressions.push seed
        IO.println s!"REGRESSION seed={seed}: authFplusmcc reaches a leader, authFchamp does not"
        IO.println s!"  config: {Json.arr (ring.map encodeAuthB)}"
      if s % 200 == 0 && s > 0 then
        IO.eprintln s!"compare psi={psi} n={n} kappa={kappa} progress {s}/{seeds}"
    IO.println s!"compare psi={psi} n={n} kappa={kappa} cap={cap} seeds={seeds} seed0={seed0}"
    IO.println s!"authFplusmcc: no_leader={noLeaderPlus} capped={cappedPlus}"
    IO.println s!"authFchamp:   no_leader={noLeaderChamp} capped={cappedChamp}"
    IO.println s!"regressions (plusmcc electable, champ not): {regressions.size}"
    return 0
  else throw (IO.userError "psi must be positive")

/-- Generic version of `compare`, right-hand side is any named `ChampCfg` rather than the
hardcoded `authFchamp` (added for the `authFchampNF` round, `run/verification/g62/champ/
REGRESSION.md`: same random-dirty-seed comparison, same seed construction, against
`PPLLAuthChamp.authFchampNF` — `authFchamp` with `seamFenceOn := false` — instead of
`authFchamp` itself). -/
def compareWith (name : String) (cfg : PPLLAuthChamp.ChampCfg)
    (psi n kappa cap seeds seed0 : Nat) : IO UInt32 := do
  if hpsi : psi > 0 then
    let trPlus ← match variantTransition "authFplusmcc" hpsi kappa with
      | .ok t => pure t
      | .error e => throw (IO.userError e)
    let trOther := PPLLAuthSimChamp.champTransitionCfg hpsi kappa cfg
    let mut noLeaderPlus := 0
    let mut noLeaderOther := 0
    let mut cappedPlus := 0
    let mut cappedOther := 0
    let mut regressions : Array Nat := #[]
    for s in [0:seeds] do
      let seed := seed0 + s
      let g0 : Rng := (UInt64.ofNat (seed * 1000003 + 17)) ||| 1
      let (_, ring) := randRing (κ := kappa) hpsi g0 n
      let mut gg : Ag psi kappa := {}
      let mut phys0 : Array Nat := #[]
      for a in ring do
        let (gg', k) := gg.intern a
        gg := gg'
        phys0 := phys0.push k
      let (leaderPlus, capPlus, _) := closureHasLeader n trPlus gg phys0 cap
      let (leaderOther, capOther, _) := closureHasLeader n trOther gg phys0 cap
      if !leaderPlus then noLeaderPlus := noLeaderPlus + 1
      if !leaderOther then noLeaderOther := noLeaderOther + 1
      if capPlus then cappedPlus := cappedPlus + 1
      if capOther then cappedOther := cappedOther + 1
      if leaderPlus && !leaderOther then
        regressions := regressions.push seed
        IO.println s!"REGRESSION seed={seed}: authFplusmcc reaches a leader, {name} does not"
        IO.println s!"  config: {Json.arr (ring.map encodeAuthB)}"
      if s % 200 == 0 && s > 0 then
        IO.eprintln s!"compareWith {name} psi={psi} n={n} kappa={kappa} progress {s}/{seeds}"
    IO.println s!"compareWith {name} psi={psi} n={n} kappa={kappa} cap={cap} seeds={seeds} seed0={seed0}"
    IO.println s!"authFplusmcc: no_leader={noLeaderPlus} capped={cappedPlus}"
    IO.println s!"{name}:   no_leader={noLeaderOther} capped={cappedOther}"
    IO.println s!"regressions (plusmcc electable, {name} not): {regressions.size}"
    return 0
  else throw (IO.userError "psi must be positive")

def compareChampNF (psi n kappa cap seeds seed0 : Nat) : IO UInt32 :=
  compareWith "authFchampNF" PPLLAuthChamp.authFchampNF psi n kappa cap seeds seed0

end ZZAuthChampLib
