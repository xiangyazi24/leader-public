import Leader.Wu.Sim.AuthHygieneClosureLib
import Leader.Wu.Sim.AuthSeamTransition
import Leader.Wu.Sim.RawCodec

/-!
# Battery for the `PPLLAuthSeam` variants (design study, not a proof)

Commands (interpreter: `lake env lean --run Leader/Wu/Sim/AuthSeamBattery.lean ...`):

* `sword PSI N KAPPA BITS TBITS CAP VARIANT [early]` — `ZZAuthChampLib.word` with
  the seam variant names (`PPLLAuthSeam.variants`) resolvable.
* `scompare VARIANT PSI N KAPPA CAP SEEDS SEED0` — `ZZAuthChampLib.compareWith`
  against a seam variant: regressions (authFplusmcc elects within the cap, VARIANT does
  not) and improvements (the converse), same seed construction.
* `sseed PSI N KAPPA CAP SEED VARIANT...` — one seed under each listed variant.
* `sall PSI N KAPPA CAP SEED` — one seed under every named seam variant and the three
  champ anchors.
* `sconfig PSI N KAPPA SEED` — dump the seed's initial random-dirty ring as JSON
  (`seedRing`'s construction, `PPLLAuthSim.encode` per cell), for archiving a persisting
  regression's exact configuration.
-/

set_option autoImplicit false

namespace ZZAuthSeamBattery

open Lean PPLLAuthSim ZZAuthChampLib PPLLAuthF PPLLFableDesignR1 PPLL

def tr (variant : String) {ψ : Nat} (hψ : ψ > 0) (κ : Nat) :
    IO (AuthB ψ κ → AuthB ψ κ → Except String (AuthB ψ κ × AuthB ψ κ)) :=
  match PPLLAuthSimSeam.localTransition variant hψ κ with
  | .ok t => pure t
  | .error e => throw (IO.userError e)

def allNames : List String :=
  ["authFplusmcc", "authFchamp", "authFchampNF"] ++ PPLLAuthSeam.variants.map (·.1)

def sword (psi n kappa : Nat) (bitsS tbitsS : String) (cap : Nat) (variant : String)
    (early : Bool := false) : IO UInt32 := do
  if hpsi : psi > 0 then
    let tr ← tr variant hpsi kappa
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
    let mut qi := 0
    let mut firstLeader : Option Nat := none
    let mut capped := false
    while qi < nodes.size do
      if early && firstLeader.isSome then break
      let phys := nodes[qi]!
      if isLeader[qi]! then
        qi := qi + 1; continue
      if nodes.size > cap then
        capped := true; qi := qi + 1; continue
      for e in [0:n] do
        let jx := (e + 1) % n
        match g.step tr phys[e]! phys[jx]! with
        | .error err => IO.eprintln s!"err {err}"
        | .ok (g', a', b') =>
          g := g'
          let phys' := (phys.set! e a').set! jx b'
          match visited[phys']? with
          | some _ => pure ()
          | none =>
            let id := nodes.size
            visited := visited.insert phys' id
            nodes := nodes.push phys'
            parent := parent.push (qi, e)
            let ld := phys'.any fun k => (g.arr[k]?.map (·.core.leader)).getD false
            isLeader := isLeader.push ld
            if ld && firstLeader.isNone then firstLeader := some id
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
    return 0
  else throw (IO.userError "psi must be positive")

def seedRing (psi n kappa seed : Nat) (hpsi : psi > 0) : Ag psi kappa × Array Nat :=
  let g0 : Rng := (UInt64.ofNat (seed * 1000003 + 17)) ||| 1
  let (_, ring) := randRing (κ := kappa) hpsi g0 n
  Id.run do
    let mut gg : Ag psi kappa := {}
    let mut phys0 : Array Nat := #[]
    for a in ring do
      let (gg', k) := gg.intern a
      gg := gg'
      phys0 := phys0.push k
    return (gg, phys0)

/-- Dump seed `seed`'s initial random-dirty ring as JSON, same construction as
`seedRing`/`ZZAuthChampCensus.compare`'s config dumps. -/
def sconfig (psi n kappa seed : Nat) : IO UInt32 := do
  if hpsi : psi > 0 then
    let (gg, phys0) := seedRing psi n kappa seed hpsi
    let ring := phys0.filterMap (fun k => gg.arr[k]?)
    IO.println s!"config psi={psi} n={n} kappa={kappa} seed={seed}:"
    IO.println s!"{Json.arr (ring.map PPLLAuthSim.encode)}"
    return 0
  else throw (IO.userError "psi must be positive")

def scompare (variant : String) (psi n kappa cap seeds seed0 : Nat) : IO UInt32 := do
  if hpsi : psi > 0 then
    let trPlus ← tr "authFplusmcc" hpsi kappa
    let trOther ← tr variant hpsi kappa
    let mut regressions : Array Nat := #[]
    let mut improvements : Array Nat := #[]
    let mut noLeaderPlus := 0
    let mut noLeaderOther := 0
    for s in [0:seeds] do
      let seed := seed0 + s
      let (gg, phys0) := seedRing psi n kappa seed hpsi
      let (leaderPlus, _, _) := closureHasLeader n trPlus gg phys0 cap
      let (leaderOther, _, _) := closureHasLeader n trOther gg phys0 cap
      if !leaderPlus then noLeaderPlus := noLeaderPlus + 1
      if !leaderOther then noLeaderOther := noLeaderOther + 1
      if leaderPlus && !leaderOther then
        regressions := regressions.push seed
        IO.println s!"REGRESSION seed={seed}: authFplusmcc elects, {variant} does not (cap {cap})"
      if !leaderPlus && leaderOther then improvements := improvements.push seed
      if s % 100 == 0 && s > 0 then
        IO.eprintln s!"scompare {variant} progress {s}/{seeds}"
    IO.println s!"scompare {variant} psi={psi} n={n} kappa={kappa} cap={cap} seeds={seeds} seed0={seed0}"
    IO.println s!"authFplusmcc: no_leader={noLeaderPlus}; {variant}: no_leader={noLeaderOther}"
    IO.println s!"regressions={regressions.size} {regressions.toList}"
    IO.println s!"improvements={improvements.size} {improvements.toList}"
    return 0
  else throw (IO.userError "psi must be positive")

def sseed (psi n kappa cap seed : Nat) (names : List String) : IO UInt32 := do
  if hpsi : psi > 0 then
    let (gg, phys0) := seedRing psi n kappa seed hpsi
    for v in names do
      let t ← tr v hpsi kappa
      let (leader, capped, nodes) := closureHasLeader n t gg phys0 cap
      IO.println s!"seed={seed} cap={cap} {v}: leader={leader} capped={capped} nodes={nodes}"
    return 0
  else throw (IO.userError "psi must be positive")

/-- Early-stopping BFS from the random dirty seed `seed` under one variant: reports the
first leader found and the shortest word to it (depth), or `no leader` within `cap`. -/
def sseedword (variant : String) (psi n kappa cap seed : Nat) : IO UInt32 := do
  if hpsi : psi > 0 then
    let tr ← tr variant hpsi kappa
    let (g0, phys0) := seedRing psi n kappa seed hpsi
    let mut g := g0
    let mut visited : Std.HashMap (Array Nat) Nat := {}
    let mut nodes : Array (Array Nat) := #[phys0]
    let mut parent : Array (Nat × Nat) := #[(0, 0)]
    let mut depth : Array Nat := #[0]
    visited := visited.insert phys0 0
    let mut qi := 0
    let mut firstLeader : Option Nat := none
    let mut capped := false
    while qi < nodes.size do
      if firstLeader.isSome then break
      if nodes.size > cap then
        capped := true; break
      let phys := nodes[qi]!
      for e in [0:n] do
        if firstLeader.isSome then break
        let jx := (e + 1) % n
        match g.step tr phys[e]! phys[jx]! with
        | .error err => IO.eprintln s!"err {err}"
        | .ok (g', a', b') =>
          g := g'
          let phys' := (phys.set! e a').set! jx b'
          match visited[phys']? with
          | some _ => pure ()
          | none =>
            let id := nodes.size
            visited := visited.insert phys' id
            nodes := nodes.push phys'
            parent := parent.push (qi, e)
            depth := depth.push (depth[qi]! + 1)
            let ld := phys'.any fun k => (g.arr[k]?.map (·.core.leader)).getD false
            if ld && firstLeader.isNone then firstLeader := some id
      qi := qi + 1
    let maxDepth := depth[nodes.size - 1]!
    IO.println s!"sseedword variant={variant} seed={seed} psi={psi} n={n} kappa={kappa} cap={cap}"
    IO.println s!"nodes={nodes.size} capped={capped} maxDepthReached={maxDepth}"
    match firstLeader with
    | none => IO.println "no leader found"
    | some t =>
      let mut chain : Array Nat := #[]
      let mut cur := t
      while cur != 0 do
        let (p, e) := parent[cur]!
        chain := chain.push e
        cur := p
      chain := chain.reverse
      IO.println s!"first leader at depth {depth[t]!}: word {chain.toList}"
    return 0
  else throw (IO.userError "psi must be positive")

/-! ## Phase A probes: block classification, goal-directed
BFS, random-scheduler stuck states, hand-built phantom fixtures -/

/-- Block `g` classification on the raw states of a ring. -/
inductive BlockClass where
  | fresh | ewait | parkedToss | parkedDepart | checking | session | part | other
  deriving Repr, DecidableEq, BEq

def blockClassOf {ψ : Nat} (n : Nat) (ring : Array (AuthState ψ)) (g : Nat) : BlockClass :=
  match ring[0]? with
  | none => .other
  | some d =>
  let cells := (List.range ψ).map fun k => ring.getD (g * ψ + k) d
  let head := cells.headD d
  let full := cells.all (·.hasPath)
  let aligned := cells.all fun u => match u.core.path with
    | .some pl _ => pl == u.core.label.val | .bot => false
  let allDepart := cells.all (·.st == .depart)
  let anyProdDone := cells.any fun u => u.st == .produce || u.st == .done
  let headPathless := !head.hasPath
  let payloadOK := cells.all fun u => match u.core.path with
    | .some _ b => b == (if u.core.bit then 1 else 0) | .bot => false
  let γ := head.path_mark
  let mono := cells.all fun u => u.path_mark == γ && u.ctrl_mark == γ
  let clean := cells.all fun u => u.core.path2 == none && !isCmd u.core.path4 && !isCmd u.core.path5
  let headSt := head.st
  let tailDepart := (cells.drop 1).all (·.st == .depart)
  let _ := n
  if full && aligned && allDepart && payloadOK && mono && clean then .fresh
  else if headPathless && !anyProdDone then .ewait
  else if full && aligned && headSt == .toss_done && tailDepart then .parkedToss
  else if full && aligned && allDepart then .parkedDepart
  else if full && cells.any (fun u => checkState u) then .checking
  else if cells.any (fun u => waveState u.st) then .session
  else if !full then .part
  else .other

def classStr : BlockClass → String
  | .fresh => "F" | .ewait => "W" | .parkedToss => "T" | .parkedDepart => "D"
  | .checking => "C" | .session => "S" | .part => "p" | .other => "o"

def ringStates {ψ κ : Nat} (g : Ag ψ κ) (phys : Array Nat) : Array (AuthState ψ) :=
  phys.filterMap fun k => (g.arr[k]?).map toState

def mixedEntrance {ψ κ : Nat} (n : Nat) (g : Ag ψ κ) (phys : Array Nat) : Bool :=
  let ring := ringStates g phys
  let m := n / ψ
  (List.range m).all fun b =>
    let c := blockClassOf n ring b
    c == .fresh || c == .ewait

def classLine {ψ κ : Nat} (n : Nat) (g : Ag ψ κ) (phys : Array Nat) : String :=
  let ring := ringStates g phys
  let m := n / ψ
  String.join ((List.range m).map fun b => classStr (blockClassOf n ring b))

def ringLine {ψ κ : Nat} (g : Ag ψ κ) (phys : Array Nat) : String :=
  String.intercalate " " ((List.range phys.size).map fun i =>
    let k := phys.getD i 0
    match g.arr[k]? with
    | some a =>
      let u := toState a
      let st := (reprStr u.st).replace "MainState." ""
      let pth := match u.core.path with | .some l b => s!"{l}/{b}" | .bot => "--"
      let t := match u.core.path2 with | some t => s!"A{t.action}@{t.position}{if u.path2_scope == P2Scope.session then "s" else "l"}{u.path2_mark.val}" | none => ""
      let c4 := match u.core.path4 with | some (l, b) => s!" p4={l}/{b}" | none => ""
      let c5 := match u.core.path5 with | some (l, b) => s!" p5={l}/{b}" | none => ""
      let ep := if a.m.episodes.val = 0 then "" else s!" e{a.m.episodes.val}"
      s!"{i}:[{if u.core.bit then 1 else 0} {pth} {st}{t} m{u.path_mark.val}c{u.ctrl_mark.val} w{if u.core.wait then 1 else 0}{if u.core.p then " p" else ""}{if u.core.p_carry then " pc" else ""}{c4}{c5}{ep}]"
    | none => s!"{i}:?")

/-- Early-stop BFS from `phys0` to the first configuration satisfying `goal`
(leaders are also goals).  Returns (found depth+word, capped, nodes). -/
def bfsGoal {ψ κ : Nat} (n cap : Nat)
    (tr : Agent ψ κ → Agent ψ κ → Except String (Agent ψ κ × Agent ψ κ))
    (g0 : Ag ψ κ) (phys0 : Array Nat) (goal : Ag ψ κ → Array Nat → Bool) :
    Ag ψ κ × Option (Nat × List Nat) × Bool × Nat := Id.run do
  let mut g := g0
  let mut visited : Std.HashMap (Array Nat) Nat := {}
  let mut nodes : Array (Array Nat) := #[phys0]
  let mut parent : Array (Nat × Nat) := #[(0, 0)]
  let mut depth : Array Nat := #[0]
  visited := visited.insert phys0 0
  let mut qi := 0
  let mut found : Option Nat := none
  let mut capped := false
  if goal g phys0 then found := some 0
  while qi < nodes.size do
    if found.isSome then break
    if nodes.size > cap then
      capped := true; break
    let phys := nodes[qi]!
    for e in [0:n] do
      if found.isSome then break
      let jx := (e + 1) % n
      match g.step tr phys[e]! phys[jx]! with
      | .error _ => pure ()
      | .ok (g', a', b') =>
        g := g'
        let phys' := (phys.set! e a').set! jx b'
        match visited[phys']? with
        | some _ => pure ()
        | none =>
          let id := nodes.size
          visited := visited.insert phys' id
          nodes := nodes.push phys'
          parent := parent.push (qi, e)
          depth := depth.push (depth[qi]! + 1)
          let ld := phys'.any fun k => (g.arr[k]?.map (·.core.leader)).getD false
          if found.isNone && (ld || goal g phys') then found := some id
    qi := qi + 1
  match found with
  | none => return (g, none, capped, nodes.size)
  | some t =>
    let mut chain : Array Nat := #[]
    let mut cur := t
    while cur != 0 do
      let (p, e) := parent[cur]!
      chain := chain.push e
      cur := p
    return (g, some (depth[t]!, chain.reverse.toList), capped, nodes.size)

def hasLeaderPhys {ψ κ : Nat} (g : Ag ψ κ) (phys : Array Nat) : Bool :=
  phys.any fun k => (g.arr[k]?.map (·.core.leader)).getD false

/-- Hand-built ψ=2 cell on the raw carrier. -/
def mkS (i : Nat) (bit : Bool) (st : MainState) (path : PathInfo) (mark ctrl : ProvColor)
    (wait : Bool := false) (path2 : Option Path2Info := none) (scope : P2Scope := .line)
    (p2mark : ProvColor := 0) (p : Bool := false) (pc : Bool := false) : AuthState 2 :=
  { core :=
      { leader := false, probe := false, phase := false, bit := bit, wait := wait,
        state := st, path := path, reset := false, carry := false, count := 0,
        label := ⟨i % 2, Nat.mod_lt i (by decide : (0:Nat) < 2)⟩, h_field := false,
        path2 := path2, path3 := none, path4 := none, path5 := none,
        p := p, p_carry := pc, reset_cmd := false, echo := false,
        signal_B := 0, bullet := 0, shield := false,
        write_state := .none, write := .none,
        last := false, last_set := false, last_unset := false,
        b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false },
    path_mark := mark, ctrl_mark := ctrl, path2_scope := scope, path2_mark := p2mark,
    path4_mark := 0, path5_mark := 0 }

def toB (κ : Nat) (u : AuthState 2) : IO (AuthB 2 κ) :=
  match reifyCore (κ := κ) u.core with
  | .ok c => pure ⟨c, marksOf u⟩
  | .error e => throw (IO.userError s!"reify: {e}")

/-- Phantom fixtures: block 0 (IDs 00) hosts a parked payload 11 signal of colour 1;
block 1 (ID 01) is Fresh at home / empty / etc. -/
def fixtures : List (String × List (AuthState 2)) :=
  [ ("phantomFresh",
      [ mkS 0 false .toss_done (.some 0 1) 1 1, mkS 1 false .depart (.some 1 1) 1 1,
        mkS 2 false .depart (.some 0 0) 0 0 true, mkS 3 true .depart (.some 1 1) 0 0 ]),
    ("phantomFreshW0",
      [ mkS 0 false .toss_done (.some 0 1) 1 1, mkS 1 false .depart (.some 1 1) 1 1,
        mkS 2 false .depart (.some 0 0) 0 0, mkS 3 true .depart (.some 1 1) 0 0 ]),
    ("phantomEmpty",
      [ mkS 0 false .toss_done (.some 0 1) 1 1, mkS 1 false .depart (.some 1 1) 1 1,
        mkS 2 false .none .bot 0 0, mkS 3 true .none .bot 0 0 ]),
    ("phantomDepartHead",
      [ mkS 0 false .depart (.some 0 1) 1 1, mkS 1 false .depart (.some 1 1) 1 1,
        mkS 2 false .depart (.some 0 0) 0 0 true, mkS 3 true .depart (.some 1 1) 0 0 ]),
    ("phantomCheck",
      [ mkS 0 false .CHECK_ready (.some 0 1) 1 1, mkS 1 false .CHECK_ready (.some 1 1) 1 1,
        mkS 2 false .depart (.some 0 0) 0 0 true, mkS 3 true .depart (.some 1 1) 0 0 ]),
    ("cstar",
      [ mkS 0 false .depart (.some 0 1) 0 0, mkS 1 false .depart (.some 1 1) 0 0,
        mkS 2 false .CHECK_ready (.some 0 0) 0 0, mkS 3 false .CHECK_ready (.some 1 0) 0 0 ]),
    ("cstarFresh",
      [ mkS 0 false .depart (.some 0 1) 0 0, mkS 1 false .depart (.some 1 1) 0 0,
        mkS 2 false .depart (.some 0 0) 0 0 true, mkS 3 false .depart (.some 1 0) 0 0 ]) ]

/-- `sfix NAME VARIANT CAP`: early-stop BFS to leader, early-stop BFS to
leader-or-MixedEntrance, and the leaderless closure (exhausted / capped). -/
def sfix (name variant : String) (cap : Nat) : IO UInt32 := do
  match fixtures.find? (·.1 == name) with
  | none => IO.eprintln s!"unknown fixture {name}"; return 2
  | some (_, cells) =>
    let hpsi : (2:Nat) > 0 := by decide
    let tr ← tr variant hpsi 1
    let mut gg : Ag 2 1 := {}
    let mut phys0 : Array Nat := #[]
    for u in cells do
      let a ← toB 1 u
      let (gg', k) := gg.intern a
      gg := gg'
      phys0 := phys0.push k
    let n := cells.length
    IO.println s!"fixture={name} variant={variant} cap={cap}"
    IO.println s!"  start classes={classLine n gg phys0} ring: {ringLine gg phys0}"
    let (g1, r1, c1, n1) := bfsGoal n cap tr gg phys0 (fun _ _ => false)
    match r1 with
    | some (d, w) => IO.println s!"  leader: depth {d} word {w} (nodes {n1})"
    | none => IO.println s!"  leader: none (capped={c1}, nodes {n1}){if !c1 then "  *** EXHAUSTED WITHOUT LEADER ***" else ""}"
    let (_, r2, c2, n2) := bfsGoal n cap tr g1 phys0 (fun g p => mixedEntrance n g p)
    match r2 with
    | some (d, w) => IO.println s!"  leader-or-MixedEntrance: depth {d} word {w} (nodes {n2})"
    | none => IO.println s!"  leader-or-MixedEntrance: none (capped={c2}, nodes {n2})"
    return 0

/-- Random ring builders on the bounded carrier. -/
def freshRing (psi kappa n : Nat) (hpsi : 0 < psi) (g0 : Rng) : Rng × Array (Agent psi kappa) := Id.run do
  let mut g := g0
  let mut ring : Array (Agent psi kappa) := #[]
  for i in [0:n] do
    let (g', bit) := nextBool g
    g := g'
    let mark : Fin 3 := ⟨(i / psi) % 3, by omega⟩
    ring := ring.push (cell psi kappa i hpsi bit (some bit) mark)
  return (g, ring)

/-- Initial latch from the environment (memo §10.8.4, self-stabilization probes of the latch
variants): `LATCH=all` sets `Marks.armed := LATCHVAL` (default 1) on every cell of a start
ring, `LATCH=rand` on a random subset (one bit per cell from `seed`); unset: no change. -/
def latchInit {ψ κ : Nat} (seed : Nat) (ring : Array (AuthB ψ κ)) : IO (Array (AuthB ψ κ)) := do
  let mode ← IO.getEnv "LATCH"
  let v := ((← IO.getEnv "LATCHVAL").bind String.toNat?).getD 1
  match mode with
  | some "all" => pure (ring.map fun a => { a with m := { a.m with armed := v } })
  | some "rand" =>
    let mut g : Rng := (UInt64.ofNat (seed * 7919 + 3)) ||| 1
    let mut out := #[]
    for a in ring do
      let (g', b) := nextNat g 2
      g := g'
      out := out.push (if b = 1 then { a with m := { a.m with armed := v } } else a)
    pure out
  | _ => pure ring

/-- `sstuck VARIANT PSI M KAPPA RUNS SEED0 MAXSTEPS BFSCAP [dirty]`: uniform-random
scheduler walk from a Fresh (or dirty) ring; every non-electing run is classified and
searched (early-stop BFS) for a word to leader-or-MixedEntrance. -/
def sstuck (variant : String) (psi m kappa runs seed0 maxSteps bfsCap : Nat) (dirty : Bool) :
    IO UInt32 := do
  if hpsi : psi > 0 then
    let n := psi * m
    let tr ← tr variant hpsi kappa
    let mut stuck := 0
    let mut hist : Std.HashMap String Nat := {}
    let mut goalFound := 0
    let mut goalCapped := 0
    let mut goalExhausted := 0
    let mut depthSum := 0
    let mut parkedTossRuns := 0
    for s in [0:runs] do
      let seed := seed0 + s
      let g0 : Rng := (UInt64.ofNat (seed * 1000003 + 17)) ||| 1
      let (g1, ring0) :=
        if dirty then randRing (κ := kappa) hpsi g0 n else freshRing psi kappa n hpsi g0
      let ring0 ← latchInit seed ring0
      let dflt ← match ring0[0]? with
        | some d => pure d
        | none => throw (IO.userError "empty ring")
      let mut rng := g1
      let mut ring := ring0
      let mut t := 0
      let mut hit : Option Nat := none
      while t < maxSteps && hit.isNone do
        t := t + 1
        let (rng', ev) := nextNat rng n
        rng := rng'
        let e1 := (ev + 1) % n
        match tr (ring.getD ev dflt) (ring.getD e1 dflt) with
        | .error _ => pure ()
        | .ok (a', b') =>
          ring := (ring.set! ev a').set! e1 b'
          if ring.any (·.core.leader) then hit := some t
      if hit.isNone then
        stuck := stuck + 1
        let mut gg : Ag psi kappa := {}
        let mut phys : Array Nat := #[]
        for a in ring do
          let (gg', k) := gg.intern a
          gg := gg'
          phys := phys.push k
        let cl := classLine n gg phys
        hist := hist.insert cl (hist.getD cl 0 + 1)
        if cl.any (· == 'T') then parkedTossRuns := parkedTossRuns + 1
        let (_, r, capped, nodes) := bfsGoal n bfsCap tr gg phys (fun g p => mixedEntrance n g p)
        let mut verdict := ""
        match r with
        | some (d, w) =>
          depthSum := depthSum + d
          goalFound := goalFound + 1
          verdict := s!"goal depth {d} word {w}"
        | none =>
          if capped then
            goalCapped := goalCapped + 1
            verdict := s!"CAPPED nodes {nodes}"
          else
            goalExhausted := goalExhausted + 1
            verdict := s!"EXHAUSTED nodes {nodes} ***"
        IO.println s!"STUCK seed={seed} classes={cl} {verdict}"
        IO.println s!"  ring: {ringLine gg phys}"
    IO.println s!"sstuck variant={variant} psi={psi} m={m} n={n} kappa={kappa} runs={runs} seed0={seed0} maxSteps={maxSteps} bfsCap={bfsCap} dirty={dirty}"
    IO.println s!"stuck={stuck} parkedTossRuns={parkedTossRuns} goalFound={goalFound} goalCapped={goalCapped} goalExhausted={goalExhausted} meanDepth={if goalFound > 0 then depthSum / goalFound else 0}"
    IO.println s!"class histogram: {hist.toList}"
    return 0
  else throw (IO.userError "psi must be positive")


/-- Replay a single random-scheduler walk (same RNG as `sstuck`) and return the final ring. -/
def walkOne (psi kappa n seed maxSteps : Nat) (hpsi : 0 < psi) (dirty : Bool)
    (tr : Agent psi kappa → Agent psi kappa → Except String (Agent psi kappa × Agent psi kappa)) :
    IO (Array (Agent psi kappa) × Option Nat) := do
  let g0 : Rng := (UInt64.ofNat (seed * 1000003 + 17)) ||| 1
  let (g1, ring0) :=
    if dirty then randRing (κ := kappa) hpsi g0 n else freshRing psi kappa n hpsi g0
  let ring0 ← latchInit seed ring0
  let dflt ← match ring0[0]? with
    | some d => pure d
    | none => throw (IO.userError "empty ring")
  let mut rng := g1
  let mut ring := ring0
  let mut t := 0
  let mut hit : Option Nat := none
  while t < maxSteps && hit.isNone do
    t := t + 1
    let (rng', ev) := nextNat rng n
    rng := rng'
    let e1 := (ev + 1) % n
    match tr (ring.getD ev dflt) (ring.getD e1 dflt) with
    | .error _ => pure ()
    | .ok (a', b') =>
      ring := (ring.set! ev a').set! e1 b'
      if ring.any (·.core.leader) then hit := some t
  return (ring, hit)

/-- Leaderless closure census from a ring: (nodes, capped, class histogram). -/
def closureCensus {ψ κ : Nat} (n cap : Nat)
    (tr : Agent ψ κ → Agent ψ κ → Except String (Agent ψ κ × Agent ψ κ))
    (g0 : Ag ψ κ) (phys0 : Array Nat) : Nat × Bool × List (String × Nat) := Id.run do
  let mut g := g0
  let mut visited : Std.HashMap (Array Nat) Unit := {}
  let mut nodes : Array (Array Nat) := #[phys0]
  visited := visited.insert phys0 ()
  let mut hist : Std.HashMap String Nat := {}
  let mut qi := 0
  let mut capped := false
  while qi < nodes.size do
    if nodes.size > cap then
      capped := true; break
    let phys := nodes[qi]!
    let cl := classLine n g phys
    hist := hist.insert cl (hist.getD cl 0 + 1)
    for e in [0:n] do
      let jx := (e + 1) % n
      match g.step tr phys[e]! phys[jx]! with
      | .error _ => pure ()
      | .ok (g', a', b') =>
        g := g'
        let phys' := (phys.set! e a').set! jx b'
        if !(visited.contains phys') then
          visited := visited.insert phys' ()
          nodes := nodes.push phys'
    qi := qi + 1
  return (nodes.size, capped, hist.toList)

/-- `sstuckone VARIANT PSI M KAPPA SEED MAXSTEPS BFSCAP DIRTY ALT...`: replay one
`sstuck` seed, print the final ring, its enabled edges with successors, the
leaderless closure census, and the goal BFS from that ring under VARIANT and each ALT. -/
def sstuckone (variant : String) (psi m kappa seed maxSteps bfsCap : Nat) (dirty : Bool)
    (alts : List String) : IO UInt32 := do
  if hpsi : psi > 0 then
    let n := psi * m
    let tr0 ← tr variant hpsi kappa
    let (ring, hit) ← walkOne psi kappa n seed maxSteps hpsi dirty tr0
    IO.println s!"sstuckone variant={variant} psi={psi} n={n} kappa={kappa} seed={seed} dirty={dirty} hit={hit}"
    -- an ALT named `LEADER` switches the goal BFS to leader-only (a self-deletion under
    -- EpisodeCap makes MixedEntrance trivially reachable)
    let leaderOnly := alts.contains "LEADER"
    let goal : Ag psi kappa → Array Nat → Bool :=
      if leaderOnly then (fun g p => hasLeaderPhys g p) else (fun g p => mixedEntrance n g p)
    for v in variant :: (alts.filter (· != "LEADER")) do
      let trv ← tr v hpsi kappa
      let mut gg : Ag psi kappa := {}
      let mut phys : Array Nat := #[]
      for a in ring do
        let (gg', k) := gg.intern a
        gg := gg'
        phys := phys.push k
      IO.println s!"== {v}: classes={classLine n gg phys}"
      IO.println s!"  ring: {ringLine gg phys}"
      if v == variant then
        IO.println s!"  json: {(Json.arr (ring.map PPLLAuthSim.encode)).compress}"
      for e in [0:n] do
        let jx := (e + 1) % n
        match gg.step trv (phys.getD e 0) (phys.getD jx 0) with
        | .error _ => pure ()
        | .ok (g', a', b') =>
          gg := g'
          let phys' := (phys.set! e a').set! jx b'
          IO.println s!"  edge {e} -> classes={classLine n gg phys'} {ringLine gg phys'}"
      let (g1, r, capped, nodes) := bfsGoal n bfsCap trv gg phys goal
      match r with
      | some (d, w) => IO.println s!"  goal{if leaderOnly then "(leader)" else ""}: depth {d} word {w} (nodes {nodes})"
      | none => IO.println s!"  goal{if leaderOnly then "(leader)" else ""}: none capped={capped} nodes {nodes}{if !capped then " *** EXHAUSTED ***" else ""}"
      let (cn, cc, hist) := closureCensus n bfsCap trv g1 phys
      IO.println s!"  closure: nodes={cn} capped={cc} classes={hist}"
    return 0
  else throw (IO.userError "psi must be positive")


/-- `spost VARIANT REF PSI M KAPPA RUNS SEED0 MAXSTEPS MULT [dirty]`: post-election behaviour.
For each seed: random schedule until the FIRST leader birth (or MAXSTEPS), then MULT times
that election time more steps (at least 1000).  Records, after the first election: EpisodeCap
breaks (a served responder with counter 2 at a physical head whose path becomes `⊥` under
VARIANT but not under REF on the same inputs), later leader births by channel — `probe`
(the served responder carried `probe = true`: the P'_ψ birth of `Algorithm.pPsi`, reached
through `pPsiProbeWall`), `check` (every other row whose pair gains a leader: the CHECK
`equal` birth at label ψ-1 of `checkSourceAuth`, which `writeWithBundle` may migrate to
the label-0 initiator inside the same row); a row that moves the leader flag between the
two cells without changing their leader count is a `move`, not a birth — and, for check births, how many happened after at least one break in the
same run (`checkAfterBreak`), the step (after the election) of the last break and the number
of breaks in the last tenth of the horizon (`lastBreak`, `tailBreaks`: persistent
post-election churn), the breaks split by `reset_cmd` on the served pair (`breaksRF` both
false, `breaksRT` at least one true), the number of cells with `reset_cmd = true` at the
election, the first step at which all `n` have it, the first later step at which some cell
lost it, the max and final counts (`rcElect`, `resetAllAt`, `resetLost`, `rcMax`, `rcFinal`), the same for
the `Marks.armed` latch of `sVplusETL` (`breaksLatched`: breaks with a latched cell in the
pair, `latchAllAt`, `lcMax`, `lcFinal`; `breaksWaitT`: breaks whose head has `wait = true`),
max simultaneous leaders, final leader count, and the first step at which
the ring is quiescent (every main state `none`) and whether the final ring is quiescent. -/
def spost (variant refv : String) (psi m kappa runs seed0 maxSteps mult : Nat) (dirty : Bool) :
    IO UInt32 := do
  if hpsi : psi > 0 then
    let n := psi * m
    let trV ← tr variant hpsi kappa
    let trR ← tr refv hpsi kappa
    IO.println s!"spost variant={variant} ref={refv} psi={psi} n={n} kappa={kappa} runs={runs} seed0={seed0} maxSteps={maxSteps} mult={mult} dirty={dirty}"
    let mut noElect := 0
    let mut totBreaks := 0
    let mut totBirths := 0
    let mut totProbe := 0
    let mut totCheck := 0
    let mut totCheckAB := 0
    let mut endZero := 0
    let mut endMulti := 0
    let mut quiesced := 0
    let mut endQuiet := 0
    for sIdx in [0:runs] do
      let seed := seed0 + sIdx
      let g0 : Rng := (UInt64.ofNat (seed * 1000003 + 17)) ||| 1
      let (g1, ring0) :=
        if dirty then randRing (κ := kappa) hpsi g0 n else freshRing psi kappa n hpsi g0
      let ring0 ← latchInit seed ring0
      let dflt ← match ring0[0]? with
        | some d => pure d
        | none => throw (IO.userError "empty ring")
      let mut rng := g1
      let mut ring := ring0
      let mut t := 0
      let mut t1 : Option Nat := none
      while t < maxSteps && t1.isNone do
        t := t + 1
        let (rng', ev) := nextNat rng n
        rng := rng'
        let e1 := (ev + 1) % n
        match trV (ring.getD ev dflt) (ring.getD e1 dflt) with
        | .error _ => pure ()
        | .ok (a', b') =>
          ring := (ring.set! ev a').set! e1 b'
          if ring.any (·.core.leader) then t1 := some t
      match t1 with
      | none =>
        noElect := noElect + 1
        IO.println s!"seed={seed} NO-ELECTION within {maxSteps}"
      | some te =>
        let horizon := max 1000 (mult * te)
        let mut breaks := 0
        let mut births := 0
        let mut probeB := 0
        let mut checkB := 0
        let mut checkAB := 0
        let mut moves := 0
        let mut lastBreak := 0
        let mut tailBreaks := 0
        let mut breaksRF := 0
        let mut breaksRT := 0
        let mut maxRc := (ring.filter (·.core.reset_cmd)).size
        let rcElect := maxRc
        let mut resetAllAt : Option Nat := if maxRc = n then some te else none
        let mut resetLost : Option Nat := none
        let mut breaksLatched := 0
        let mut breaksWaitT := 0
        let mut maxLc := (ring.filter (·.m.armed > 0)).size
        let mut latchAllAt : Option Nat := if maxLc = n then some te else none
        let mut maxL := (ring.filter (·.core.leader)).size
        let mut prevL := maxL
        let mut quietAt : Option Nat := none
        let mut h := 0
        while h < horizon do
          h := h + 1
          let (rng', ev) := nextNat rng n
          rng := rng'
          let e1 := (ev + 1) % n
          let a := ring.getD ev dflt
          let b := ring.getD e1 dflt
          match trV a b with
          | .error _ => pure ()
          | .ok (a', b') =>
            if b.m.episodes.val = 2 && b.core.label.val = 0 && b'.hole && !b.hole then
              match trR a b with
              | .ok (_, bR) =>
                if !bR.hole then
                  breaks := breaks + 1
                  lastBreak := h
                  if h * 10 > horizon * 9 then tailBreaks := tailBreaks + 1
                  if !a.core.reset_cmd && !b.core.reset_cmd then breaksRF := breaksRF + 1
                  else breaksRT := breaksRT + 1
                  if a.m.armed > 0 || b.m.armed > 0 then breaksLatched := breaksLatched + 1
                  if b.core.wait then breaksWaitT := breaksWaitT + 1
              | .error _ => pure ()
            let before := (if a.core.leader then 1 else 0) + (if b.core.leader then 1 else 0)
            let after := (if a'.core.leader then 1 else 0) + (if b'.core.leader then 1 else 0)
            if after > before then
              if b.core.probe && !b.core.leader then probeB := probeB + 1
              else
                checkB := checkB + 1
                if breaks > 0 then checkAB := checkAB + 1
            else if after = before && (a'.core.leader != a.core.leader) then moves := moves + 1
            ring := (ring.set! ev a').set! e1 b'
            let cntL := (ring.filter (·.core.leader)).size
            if cntL > prevL then births := births + (cntL - prevL)
            prevL := cntL
            if cntL > maxL then maxL := cntL
            if quietAt.isNone && ring.all (·.core.state == .none) then quietAt := some (te + h)
            let rc := (ring.filter (·.core.reset_cmd)).size
            if rc > maxRc then maxRc := rc
            if rc = n && resetAllAt.isNone then resetAllAt := some (te + h)
            if rc < n && resetAllAt.isSome && resetLost.isNone then resetLost := some (te + h)
            let lc := (ring.filter (·.m.armed > 0)).size
            if lc > maxLc then maxLc := lc
            if lc = n && latchAllAt.isNone then latchAllAt := some (te + h)
        let rcFinal := (ring.filter (·.core.reset_cmd)).size
        let lcFinal := (ring.filter (·.m.armed > 0)).size
        let finalL := (ring.filter (·.core.leader)).size
        let finalQuiet := ring.all (·.core.state == .none)
        totBreaks := totBreaks + breaks
        totBirths := totBirths + births
        totProbe := totProbe + probeB
        totCheck := totCheck + checkB
        totCheckAB := totCheckAB + checkAB
        if finalL = 0 then endZero := endZero + 1
        if finalL > 1 then endMulti := endMulti + 1
        if quietAt.isSome then quiesced := quiesced + 1
        if finalQuiet then endQuiet := endQuiet + 1
        IO.println s!"seed={seed} elect={te} horizon={horizon} breaks={breaks} births={births} probe={probeB} check={checkB} moves={moves} checkAfterBreak={checkAB} lastBreak={lastBreak} tailBreaks={tailBreaks} breaksRF={breaksRF} breaksRT={breaksRT} rcElect={rcElect} resetAllAt={resetAllAt} resetLost={resetLost} rcMax={maxRc} rcFinal={rcFinal} breaksLatched={breaksLatched} breaksWaitT={breaksWaitT} latchAllAt={latchAllAt} lcMax={maxLc} lcFinal={lcFinal} maxLeaders={maxL} finalLeaders={finalL} quietAt={quietAt} finalQuiet={finalQuiet}{if finalL = 0 then " *** ZERO LEADERS ***" else ""}"
    IO.println s!"summary variant={variant}: runs={runs} noElection={noElect} breaksAfterElection={totBreaks} laterBirths={totBirths} probeBirths={totProbe} checkBirths={totCheck} checkAfterBreak={totCheckAB} endZeroLeaders={endZero} endMultiLeaders={endMulti} quiesced={quiesced} finalQuiet={endQuiet}"
    return 0
  else throw (IO.userError "psi must be positive")

/-- `sstuckword VARIANT PSI M KAPPA SEED MAXSTEPS DIRTY RVARIANT WORD`: replay one
`sstuck` seed under VARIANT, then replay the edge word on the final ring under RVARIANT. -/
def sstuckword (variant : String) (psi m kappa seed maxSteps : Nat) (dirty : Bool)
    (rvariant wordS : String) (bfsCap : Nat := 0) : IO UInt32 := do
  if hpsi : psi > 0 then
    let n := psi * m
    let tr0 ← tr variant hpsi kappa
    let (ring, _) ← walkOne psi kappa n seed maxSteps hpsi dirty tr0
    let trv ← tr rvariant hpsi kappa
    let mut gg : Ag psi kappa := {}
    let mut phys : Array Nat := #[]
    for a in ring do
      let (gg', k) := gg.intern a
      gg := gg'
      phys := phys.push k
    let word := (wordS.splitOn ",").filterMap (·.trimAscii.toString.toNat?)
    IO.println s!"sstuckword variant={variant} seed={seed} replay={rvariant} word={word}"
    IO.println s!"  step 0 classes={classLine n gg phys} {ringLine gg phys}"
    let mut i := 0
    for e in word do
      i := i + 1
      let jx := (e + 1) % n
      match gg.step trv (phys.getD e 0) (phys.getD jx 0) with
      | .error err => IO.println s!"  step {i} edge {e}: error {err}"
      | .ok (g', a', b') =>
        gg := g'
        phys := (phys.set! e a').set! jx b'
        IO.println s!"  step {i} edge {e} classes={classLine n gg phys} leader={hasLeaderPhys gg phys} {ringLine gg phys}"
    if bfsCap > 0 then
      -- goal BFS (leader-or-MixedEntrance) and closure census from the replay endpoint
      let (g1, r, capped, nodes) := bfsGoal n bfsCap trv gg phys (fun g p => mixedEntrance n g p)
      match r with
      | some (d, w) => IO.println s!"  goal: depth {d} word {w} (nodes {nodes})"
      | none => IO.println s!"  goal: none capped={capped} nodes {nodes}{if !capped then " *** EXHAUSTED ***" else ""}"
      let (cn, cc, hist) := closureCensus n bfsCap trv g1 phys
      IO.println s!"  closure: nodes={cn} capped={cc} classes={hist}"
    return 0
  else throw (IO.userError "psi must be positive")


/-- Family-b raw cell (`ZZHitTime.encodeAuthStateRaw` schema) to the bounded carrier. -/
def decodeRawB (psi kappa : Nat) (j : Json) : Except String (AuthB psi kappa) := do
  let core ← PPLLSimRawCodec.decodeState (psi := psi) (← j.getObjVal? "core")
  let pm ← (← j.getObjVal? "path_mark").getNat?
  let cm ← (← j.getObjVal? "ctrl_mark").getNat?
  let scS ← (← j.getObjVal? "path2_scope").getStr?
  let p2m ← (← j.getObjVal? "path2_mark").getNat?
  let p4m ← (← j.getObjVal? "path4_mark").getNat?
  let p5m ← (← j.getObjVal? "path5_mark").getNat?
  let u : AuthState psi :=
    { core := core, path_mark := finOfNat 3 (by decide) pm, ctrl_mark := finOfNat 3 (by decide) cm,
      path2_scope := if scS = "session" then .session else .line,
      path2_mark := finOfNat 3 (by decide) p2m, path4_mark := finOfNat 3 (by decide) p4m,
      path5_mark := finOfNat 3 (by decide) p5m }
  let c ← reifyCore (κ := kappa) u.core
  let ep ← match j.getObjVal? "episodes" with
    | .ok e => do let v ← e.getNat?; pure (finOfNat 3 (by decide) v)
    | .error _ => pure 0
  return ⟨c, { marksOf u with episodes := ep }⟩

/-- `sdump FILE PSI KAPPA BFSCAP VARIANT...`: load a `ZZHitTime dump` (family a or b from
its `meta`), print classes and ring, and run the leader-or-MixedEntrance BFS under each
variant. -/
def sdump (file : String) (psi kappa bfsCap : Nat) (variants : List String) : IO UInt32 := do
  if hpsi : psi > 0 then
    let txt ← IO.FS.readFile file
    let j ← match Json.parse txt with
      | .ok j => pure j
      | .error e => throw (IO.userError s!"json: {e}")
    let fam ← match j.getObjVal? "meta" >>= (·.getObjVal? "family") >>= Json.getStr? with
      | .ok f => pure f
      | .error e => throw (IO.userError s!"meta.family: {e}")
    let arrJ ← match j.getObjVal? "ring" >>= Json.getArr? with
      | .ok a => pure a
      | .error e => throw (IO.userError s!"ring: {e}")
    let n := arrJ.size
    let mut ring : Array (AuthB psi kappa) := #[]
    for cj in arrJ do
      let a ← match (if fam == "a" then PPLLAuthSim.decode (ψ := psi) (κ := kappa) cj
                     else decodeRawB psi kappa cj) with
        | .ok a => pure a
        | .error e => throw (IO.userError s!"decode: {e}")
      ring := ring.push a
    IO.println s!"sdump file={file} family={fam} psi={psi} n={n} kappa={kappa}"
    for v in variants do
      let trv ← tr v hpsi kappa
      let mut gg : Ag psi kappa := {}
      let mut phys : Array Nat := #[]
      for a in ring do
        let (gg', k) := gg.intern a
        gg := gg'
        phys := phys.push k
      IO.println s!"== {v}: classes={classLine n gg phys} leader={hasLeaderPhys gg phys}"
      IO.println s!"  ring: {ringLine gg phys}"
      let (_, r, capped, nodes) := bfsGoal n bfsCap trv gg phys (fun g p => mixedEntrance n g p)
      match r with
      | some (d, w) => IO.println s!"  goal: depth {d} word {w} (nodes {nodes})"
      | none => IO.println s!"  goal: none capped={capped} nodes {nodes}{if !capped then " *** EXHAUSTED ***" else ""}"
    return 0
  else throw (IO.userError "psi must be positive")


/-- `sfreshword VARIANT PSI N KAPPA BITS WORD [BFSCAP]`: replay an edge word from the
all-Fresh ring with resident bits BITS (all blocks colour 0, `wait = true`), printing the
ring after every step, then the goal BFS from the endpoint. -/
def sfreshwordC (variant : String) (psi n kappa : Nat) (bitsS : String) (carS : Option String)
    (marksS : String) (wordS : String) (bfsCap : Nat) : IO UInt32 := do
  if hpsi : psi > 0 then
    let tr ← tr variant hpsi kappa
    let bits := parseBits bitsS
    let mut gg : Ag psi kappa := {}
    let mut phys : Array Nat := #[]
    for i in [0:n] do
      -- carried payload: default = resident (Fresh); with CARBITS, '-' = pathless,
      -- '0'/'1' = parked carried bit; MARKS gives block g's path/ctrl colour (digit g,
      -- default 0), as in the C*, produce-neighbour and BEQ fixtures
      let tb : Option Bool := match carS with
        | none => some (bits.getD i false)
        | some cs => match cs.toList.getD i '-' with
          | '0' => some false
          | '1' => some true
          | _ => none
      let mk : Nat := (marksS.toList.getD (i / psi) '0').toNat - '0'.toNat
      let a := cell psi kappa i hpsi (bits.getD i false) tb (finOfNat 3 (by omega) (mk % 3))
      let a := { a with core := { a.core with wait := true } }
      let (gg', k) := gg.intern a
      gg := gg'
      phys := phys.push k
    let word := (wordS.splitOn ",").filterMap (·.trimAscii.toString.toNat?)
    IO.println s!"sfreshword variant={variant} psi={psi} n={n} kappa={kappa} bits={bitsS} carried={carS.getD bitsS} marks={marksS} word={word}"
    IO.println s!"  step 0 classes={classLine n gg phys} {ringLine gg phys}"
    let mut i := 0
    for e in word do
      i := i + 1
      let jx := (e + 1) % n
      match gg.step tr (phys.getD e 0) (phys.getD jx 0) with
      | .error err => IO.println s!"  step {i} edge {e}: error {err}"
      | .ok (g', a', b') =>
        gg := g'
        phys := (phys.set! e a').set! jx b'
        IO.println s!"  step {i} edge {e} classes={classLine n gg phys} leader={hasLeaderPhys gg phys} {ringLine gg phys}"
    let (_, r, capped, nodes) := bfsGoal n bfsCap tr gg phys (fun g p => mixedEntrance n g p)
    match r with
    | some (d, w) => IO.println s!"  goal: depth {d} word {w} (nodes {nodes})"
    | none => IO.println s!"  goal: none capped={capped} nodes {nodes}{if !capped then " *** EXHAUSTED ***" else ""}"
    return 0
  else throw (IO.userError "psi must be positive")

def sfreshword (variant : String) (psi n kappa : Nat) (bitsS wordS : String) (bfsCap : Nat) :
    IO UInt32 := sfreshwordC variant psi n kappa bitsS none "0" wordS bfsCap

/-- `sdirtyword VARIANT PSI N KAPPA RESBITS CARBITS MARKS WORD [BFSCAP]`: like `sfreshword`
but the carried payload is CARBITS ('-' = pathless cell) and block g's path/ctrl colour is
digit g of MARKS (default 0). Used for the fixtures (C*, the produce-neighbour
fixture, the BEQ outcome words). -/
def sdirtyword (variant : String) (psi n kappa : Nat) (bitsS carS marksS wordS : String)
    (bfsCap : Nat) : IO UInt32 :=
  sfreshwordC variant psi n kappa bitsS (some carS) marksS wordS bfsCap

/-- Parse a main state name for `sspecword`. -/
def parseState (s : String) : Option MainState :=
  match s with
  | "depart" | "d" => some .depart | "compare2" | "c2" => some .compare2
  | "compare1" | "c1" => some .compare1 | "lock" | "l" => some .lock
  | "ready" | "R" | "CHECK_ready" => some .CHECK_ready | "toss" => some .toss
  | "toss_done" => some .toss_done | "none" | "n" => some .none | "less" => some .less
  | "E" | "eliminate_signal" => some .eliminate_signal | "produce" => some .produce
  | "equal" => some .equal | "larger" => some .larger | "congest" => some .congest
  | _ => none

/-- `sspecword VARIANT PSI N KAPPA SPEC WORD [BFSCAP]`: SPEC is a comma-separated list of
cells `RES:CAR:STATE:PM:CM[:CL[:EP]]` (RES resident bit, CAR carried bit or `-` for
pathless, STATE a `parseState` name, PM/CM path and control marks, CL the carried label,
default = physical label (`-` keeps it); a uniformly shifted full train is
`CL = (i + s) % ψ`; EP the EpisodeCap counter, default 0).
Replays WORD, prints the ring after every step, then runs the goal BFS from the endpoint.
Used for the compare2 families C2A/C2B/C2C of PHASEA_WHOLERING_FABLE.md. -/
def sspecword (variant : String) (psi n kappa : Nat) (specS wordS : String) (bfsCap : Nat) :
    IO UInt32 := do
  if hpsi : psi > 0 then
    let tr ← tr variant hpsi kappa
    let specs := (specS.splitOn ",").map (·.splitOn ":")
    let mut gg : Ag psi kappa := {}
    let mut phys : Array Nat := #[]
    for i in [0:n] do
      let f := specs.getD i []
      let res := f.getD 0 "0" == "1"
      let carS := f.getD 1 "-"
      let tb : Option Bool := if carS == "-" then none else some (carS == "1")
      let st := (parseState (f.getD 2 "depart")).getD .depart
      let pm := ((f.getD 3 "0").toNat?.getD 0) % 3
      let cm := ((f.getD 4 "0").toNat?.getD 0) % 3
      let cl : Option Nat := (f.getD 5 "").toNat?
      let a := cell psi kappa i hpsi res tb (finOfNat 3 (by decide) pm)
      let path := match a.core.path, cl with
        | .some _ b, some l => .some (finOfNat psi hpsi (l % psi)) b
        | q, _ => q
      let core := { a.core with wait := true, path := path, state := if tb.isSome then st else a.core.state }
      let ep := ((f.getD 6 "0").toNat?.getD 0) % 3
      let a := { a with core := core, m := { a.m with ctrl := finOfNat 3 (by decide) cm, episodes := finOfNat 3 (by decide) ep } }
      let (gg', k) := gg.intern a
      gg := gg'
      phys := phys.push k
    let word := (wordS.splitOn ",").filterMap (·.trimAscii.toString.toNat?)
    IO.println s!"sspecword variant={variant} psi={psi} n={n} kappa={kappa} spec={specS} word={word}"
    IO.println s!"  step 0 classes={classLine n gg phys} {ringLine gg phys}"
    let mut i := 0
    for e in word do
      i := i + 1
      let jx := (e + 1) % n
      match gg.step tr (phys.getD e 0) (phys.getD jx 0) with
      | .error err => IO.println s!"  step {i} edge {e}: error {err}"
      | .ok (g', a', b') =>
        gg := g'
        phys := (phys.set! e a').set! jx b'
        IO.println s!"  step {i} edge {e} classes={classLine n gg phys} leader={hasLeaderPhys gg phys} {ringLine gg phys}"
    -- closure census: exact BFS over all edges (leader / MixedEntrance early stop)
    let (_, r, capped, nodes) := bfsGoal n bfsCap tr gg phys (fun g p => mixedEntrance n g p)
    match r with
    | some (d, w) => IO.println s!"  goal: depth {d} word {w} (nodes {nodes})"
    | none => IO.println s!"  goal: none capped={capped} nodes {nodes}{if !capped then " *** EXHAUSTED: closed leaderless family ***" else ""}"
    return 0
  else throw (IO.userError "psi must be positive")

/-! ## The four-cell abort/restart cycle (`seamRun sTG2 loopC [2,1] = loopC`) -/

/-- `loopC` (ψ=2, n=4, κ=1): cells 0,1 depart, cell 2 lock (reset, ctrl 1),
cell 3 CHECK_ready (count 1); path4 (1,1) at cell 1; ctrl_mark 1 at cells 1,2. -/
def loopC (i : Nat) : AuthState 2 :=
  let u := mkS i false (if i = 2 then .lock else if i = 3 then .CHECK_ready else .depart)
    (.some (i % 2) 0) 0 (if i = 1 ∨ i = 2 then 1 else 0) (wait := decide (i ≠ 2))
  let p4 : Option (Int × Nat) := if i = 1 then some ((1 : Int), 1) else none
  let ws : WriteState := if i = 2 ∨ i = 3 then .depart else .none
  let cnt : Nat := if i = 3 then 1 else 0
  { u with core := { u.core with reset := decide (i = 2), count := cnt, path4 := p4, write_state := ws } }

/-- `sloop VARIANT LAPS BFSCAP`: replay `[2,1]` LAPS times on `loopC` under VARIANT (the
abort/restart 2-cycle; under EpisodeCap the head at cell 2 self-deletes on its
third counted start), printing the ring after every edge, then the leader BFS, the
leader-or-MixedEntrance BFS and the closure census from the endpoint. -/
def sloop (variant : String) (laps bfsCap : Nat) : IO UInt32 := do
  let hpsi : (2:Nat) > 0 := by decide
  let tr ← tr variant hpsi 1
  let n := 4
  let mut gg : Ag 2 1 := {}
  let mut phys : Array Nat := #[]
  let mut cells : Array (AuthB 2 1) := #[]
  for i in [0:n] do
    cells := cells.push (← toB 1 (loopC i))
  for a in (← latchInit 0 cells) do
    let (gg', k) := gg.intern a
    gg := gg'
    phys := phys.push k
  IO.println s!"sloop variant={variant} laps={laps} latch={(← IO.getEnv "LATCH").getD "none"}"
  IO.println s!"  step 0 classes={classLine n gg phys} {ringLine gg phys}"
  let mut i := 0
  for e in (List.replicate laps [2, 1]).flatten do
    i := i + 1
    let jx := (e + 1) % n
    match gg.step tr (phys.getD e 0) (phys.getD jx 0) with
    | .error err => IO.println s!"  step {i} edge {e}: error {err}"
    | .ok (g', a', b') =>
      gg := g'
      phys := (phys.set! e a').set! jx b'
      IO.println s!"  step {i} edge {e} classes={classLine n gg phys} leader={hasLeaderPhys gg phys} {ringLine gg phys}"
  let (g1, r, capped, nodes) := bfsGoal n bfsCap tr gg phys (fun g p => hasLeaderPhys g p)
  match r with
  | some (d, w) => IO.println s!"  leader: depth {d} word {w} (nodes {nodes})"
  | none => IO.println s!"  leader: none capped={capped} nodes {nodes}{if !capped then " *** EXHAUSTED ***" else ""}"
  let (g2, r, capped, nodes) := bfsGoal n bfsCap tr g1 phys (fun g p => mixedEntrance n g p)
  match r with
  | some (d, w) => IO.println s!"  goal: depth {d} word {w} (nodes {nodes})"
  | none => IO.println s!"  goal: none capped={capped} nodes {nodes}{if !capped then " *** EXHAUSTED: closed leaderless family ***" else ""}"
  let (cn, cc, hist) := closureCensus n bfsCap tr g2 phys
  IO.println s!"  closure: nodes={cn} capped={cc} classes={hist}"
  return 0

/-- `sreplay NAME VARIANT WORD`: replay a comma-separated edge word on a fixture, printing
the block classes and the ring after every step. -/
def sreplay (name variant wordS : String) : IO UInt32 := do
  match fixtures.find? (·.1 == name) with
  | none => IO.eprintln s!"unknown fixture {name}"; return 2
  | some (_, cells) =>
    let hpsi : (2:Nat) > 0 := by decide
    let tr ← tr variant hpsi 1
    let mut gg : Ag 2 1 := {}
    let mut phys : Array Nat := #[]
    for u in cells do
      let a ← toB 1 u
      let (gg', k) := gg.intern a
      gg := gg'
      phys := phys.push k
    let n := cells.length
    let word := (wordS.splitOn ",").filterMap (·.trimAscii.toString.toNat?)
    IO.println s!"replay fixture={name} variant={variant} word={word}"
    IO.println s!"  step 0 classes={classLine n gg phys} {ringLine gg phys}"
    let mut i := 0
    for e in word do
      i := i + 1
      let jx := (e + 1) % n
      match gg.step tr (phys.getD e 0) (phys.getD jx 0) with
      | .error err => IO.println s!"  step {i} edge {e}: error {err}"
      | .ok (g', a', b') =>
        gg := g'
        phys := (phys.set! e a').set! jx b'
        IO.println s!"  step {i} edge {e} classes={classLine n gg phys} leader={hasLeaderPhys gg phys} {ringLine gg phys}"
    return 0

end ZZAuthSeamBattery

def main (args : List String) : IO UInt32 := do
  match args with
  | ["sword", p, n, k, b, t, c, v] =>
    ZZAuthSeamBattery.sword p.toNat! n.toNat! k.toNat! b t c.toNat! v
  | ["sword", p, n, k, b, t, c, v, "early"] =>
    ZZAuthSeamBattery.sword p.toNat! n.toNat! k.toNat! b t c.toNat! v true
  | ["scompare", v, p, n, k, c, sd, sd0] =>
    ZZAuthSeamBattery.scompare v p.toNat! n.toNat! k.toNat! c.toNat! sd.toNat! sd0.toNat!
  | "sseed" :: p :: n :: k :: c :: sd :: names =>
    ZZAuthSeamBattery.sseed p.toNat! n.toNat! k.toNat! c.toNat! sd.toNat! names
  | ["sseedword", v, p, n, k, c, sd] =>
    ZZAuthSeamBattery.sseedword v p.toNat! n.toNat! k.toNat! c.toNat! sd.toNat!
  | ["sfix", name, v, c] => ZZAuthSeamBattery.sfix name v c.toNat!
  | ["spost", v, rv, p, m, k, r, sd0, ms, mu] =>
    ZZAuthSeamBattery.spost v rv p.toNat! m.toNat! k.toNat! r.toNat! sd0.toNat! ms.toNat! mu.toNat! false
  | ["spost", v, rv, p, m, k, r, sd0, ms, mu, "dirty"] =>
    ZZAuthSeamBattery.spost v rv p.toNat! m.toNat! k.toNat! r.toNat! sd0.toNat! ms.toNat! mu.toNat! true
  | ["sreplay", name, v, w] => ZZAuthSeamBattery.sreplay name v w
  | ["sloop", v, laps, bc] => ZZAuthSeamBattery.sloop v laps.toNat! bc.toNat!
  | ["sstuck", v, p, m, k, r, sd0, ms, bc] =>
    ZZAuthSeamBattery.sstuck v p.toNat! m.toNat! k.toNat! r.toNat! sd0.toNat! ms.toNat! bc.toNat! false
  | ["sstuck", v, p, m, k, r, sd0, ms, bc, "dirty"] =>
    ZZAuthSeamBattery.sstuck v p.toNat! m.toNat! k.toNat! r.toNat! sd0.toNat! ms.toNat! bc.toNat! true
  | ["sstuckword", v, p, m, k, sd, ms, d, rv, w] =>
    ZZAuthSeamBattery.sstuckword v p.toNat! m.toNat! k.toNat! sd.toNat! ms.toNat! (d == "dirty") rv w
  | ["sstuckword", v, p, m, k, sd, ms, d, rv, w, bc] =>
    ZZAuthSeamBattery.sstuckword v p.toNat! m.toNat! k.toNat! sd.toNat! ms.toNat! (d == "dirty") rv w bc.toNat!
  | ["sfreshword", v, p, n, k, b, w] =>
    ZZAuthSeamBattery.sfreshword v p.toNat! n.toNat! k.toNat! b w 300000
  | ["sfreshword", v, p, n, k, b, w, bc] =>
    ZZAuthSeamBattery.sfreshword v p.toNat! n.toNat! k.toNat! b w bc.toNat!
  | ["sdirtyword", v, p, n, k, b, c, m, w] =>
    ZZAuthSeamBattery.sdirtyword v p.toNat! n.toNat! k.toNat! b c m w 300000
  | ["sdirtyword", v, p, n, k, b, c, m, w, bc] =>
    ZZAuthSeamBattery.sdirtyword v p.toNat! n.toNat! k.toNat! b c m w bc.toNat!
  | ["sspecword", v, p, n, k, sp, w] =>
    ZZAuthSeamBattery.sspecword v p.toNat! n.toNat! k.toNat! sp w 300000
  | ["sspecword", v, p, n, k, sp, w, bc] =>
    ZZAuthSeamBattery.sspecword v p.toNat! n.toNat! k.toNat! sp w bc.toNat!
  | "sdump" :: f :: p :: k :: bc :: vs =>
    ZZAuthSeamBattery.sdump f p.toNat! k.toNat! bc.toNat! vs
  | "sstuckone" :: v :: p :: m :: k :: sd :: ms :: bc :: d :: alts =>
    ZZAuthSeamBattery.sstuckone v p.toNat! m.toNat! k.toNat! sd.toNat! ms.toNat! bc.toNat! (d == "dirty") alts
  | ["sall", p, n, k, c, sd] =>
    ZZAuthSeamBattery.sseed p.toNat! n.toNat! k.toNat! c.toNat! sd.toNat! ZZAuthSeamBattery.allNames
  | ["sconfig", p, n, k, sd] =>
    ZZAuthSeamBattery.sconfig p.toNat! n.toNat! k.toNat! sd.toNat!
  | _ =>
    IO.eprintln "usage: sword PSI N KAPPA BITS TBITS CAP VARIANT [early]
       | scompare VARIANT PSI N KAPPA CAP SEEDS SEED0
       | sseed PSI N KAPPA CAP SEED VARIANT...
       | sall PSI N KAPPA CAP SEED
       | sseedword VARIANT PSI N KAPPA CAP SEED
       | sconfig PSI N KAPPA SEED"
    return 2
