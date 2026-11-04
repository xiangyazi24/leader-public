import Std.Data.HashMap
import Leader.Wu.Sim.AuthCarrier

/-!
# Moving-frontier restricted walk and exact closure (authFplusmcc)

Design-exploration tool, not a proof certificate.  Third walk of the
FULL-DISCHARGE sampling campaign (`run/verification/g62/fab/ZDIV.md` §34): tests the *moving-frontier* fix to
the false closed-single-block reduction, on seeds from
`Leader/Wu/Sim/AuthFrontierSeeds.lean` (`B = G_0` SerialPlus, `X = G_1` dirty,
`U = G_2` SerialPlus-or-dirty, `n = 3ψ`).

Only these edges may ever fire (the active macro), recomputed every step
because the one exception is state-dependent:

* every internal edge of `B` (physical `0 .. ψ-2 -> +1`);
* every internal edge of `X` (physical `ψ .. 2ψ-2 -> +1`);
* the seam `B_terminal -> X_head` (edge `ψ-1`);
* the outgoing edge `X_terminal -> U_head` (edge `2ψ-1`);
* the wraparound edge into `B_head` (edge `n-1`, i.e. `U_terminal -> B_head`
  since `m = 3` has no further blocks) **only** when `B_head` (physical `0`)
  currently holds an `A3` token (the one exception: "if an A3 traverses B
  and reaches B_head, serve that boundary once").

`U`'s interior (everything strictly after its head cell) is therefore never
touched by any served edge and stays byte-for-byte as generated — exactly
`ZDIV.md` §34's "right collar . . . may absorb exported debris" picture, here
inert unless `X_terminal -> U_head` fires.

Stop at the first of a leader anywhere, a path deletion (`core.path = bot`)
anywhere, or `B` and `X` both SerialPlus (`p`/`p_carry` unconstrained, unlike
the exact serial). Copies `Agent`/`localTransition`/`mix64`/`Ag`
(interning + memoised `step`) verbatim from `Leader/Wu/Sim/AuthWalk.lean` for the
same reason that file gives for not importing `Leader.Wu.Sim.DiskClosureCensus`: a
top-level `def main` collision.

Usage:
`zz-auth-frontier walk PSI KAPPA SEEDS.jsonl OUTDIR [--only i,j,..] [--steps S]
   [--rngseed R] [--heartbeat K]`   (`n := 3*PSI`)
`zz-auth-frontier census PSI KAPPA SEED.json CAP`   (one JSON line to stdout)
-/

set_option autoImplicit false

open Lean

namespace ZZAuthFrontierWalk

abbrev Agent (ψ κ : Nat) := PPLLAuthSim.AuthB ψ κ

def localTransition (variant : String) {ψ : Nat} (hψ : ψ > 0) (κ : Nat) :
    Except String (Agent ψ κ → Agent ψ κ → Except String (Agent ψ κ × Agent ψ κ)) :=
  PPLLAuthSim.localTransition variant hψ κ

@[inline] def mix64 (x : UInt64) : UInt64 :=
  let x := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
  let x := (x ^^^ (x >>> 27)) * 0x94d049bb133111eb
  x ^^^ (x >>> 31)

@[inline] def splitmix (s : UInt64) : UInt64 × UInt64 :=
  let s' := s + 0x9E3779B97F4A7C15
  (s', mix64 s')

structure Ag (ψ κ : Nat) where
  arr : Array (Agent ψ κ) := #[]
  ix : Std.HashMap String Nat := {}
  lead : Array Bool := #[]
  hole : Array Bool := #[]
  memo : Std.HashMap UInt64 UInt64 := {}

def Ag.intern {ψ κ : Nat} (g : Ag ψ κ) (a : Agent ψ κ) : Ag ψ κ × Nat :=
  let key := PPLLAuthSim.key a
  match g.ix[key]? with
  | some i => (g, i)
  | none =>
    let i := g.arr.size
    let g' : Ag ψ κ :=
      { arr := g.arr.push a, ix := g.ix.insert key i, lead := g.lead.push a.leader
        hole := g.hole.push (PPLLAuthSim.AuthB.hole a), memo := g.memo }
    (g', i)

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

/-! ## SerialPlus check and the restricted edge set -/

/-- `PPLLAuthF.issue`'s printed-action encoding: `Fin 6` value `v` is printed
action `v+1`. `A3` prints `3`, so its internal value is `2`. -/
def isA3 {ψ κ : Nat} (a : Agent ψ κ) : Bool :=
  match a.core.path2 with
  | some p2 => p2.action.val == 2
  | none => false

/-- One cell of a SerialPlus block: own aligned path, departed, no path2, no
`-1` command in path4/path5; `p`/`p_carry` unconstrained. -/
def isSerialPlusCell {ψ κ : Nat} (a : Agent ψ κ) (j : Nat) : Bool :=
  a.core.label.val == j &&
  (match a.core.path with | .some l _ => l.val == j | .bot => false) &&
  (match a.core.state with | .depart => true | _ => false) &&
  (match a.core.path2 with | none => true | some _ => false) &&
  a.m.path.val == a.m.ctrl.val &&
  (match a.core.path4 with | none => true | some (.normal _, _) => true | some (.clean, _) => false) &&
  (match a.core.path5 with | none => true | some (.normal _, _) => true | some (.clean, _) => false)

/-- Safe lookup (no `Inhabited (Agent ψ κ)` instance is available, so `!`
indexing into `g.arr` cannot be used). -/
def getAg {ψ κ : Nat} (g : Ag ψ κ) (phys : Array Nat) (idx : Nat) : Option (Agent ψ κ) :=
  phys[idx]?.bind (fun i => g.arr[i]?)

/-- Is the block of `ψ` physical cells starting at `base` entirely SerialPlus
with one shared `path_mark = ctrl_mark`? -/
def isSerialPlusBlock {ψ κ : Nat} (g : Ag ψ κ) (phys : Array Nat) (base psi : Nat) : Bool := Id.run do
  if psi == 0 then return true
  match getAg g phys base with
  | none => return false
  | some a0 =>
    if !isSerialPlusCell a0 0 then return false
    let gamma0 := a0.m.path.val
    for j in [1:psi] do
      match getAg g phys (base + j) with
      | none => return false
      | some a =>
        if !(isSerialPlusCell a j) then return false
        if a.m.path.val != gamma0 then return false
    return true

inductive Outcome where
  | leader | deletion | serial | neither
  deriving DecidableEq, Repr

def Outcome.toStr : Outcome → String
  | .leader => "leader" | .deletion => "deletion" | .serial => "serial" | .neither => "neither"

/-- The three positive stop conditions, in priority order (a leader takes
priority over a hole, which takes priority over SerialPlus, though these are
generated to be mutually exclusive in practice). -/
def checkStop {ψ κ : Nat} (g : Ag ψ κ) (phys : Array Nat) (psi : Nat) : Option Outcome :=
  if phys.any (fun idx => g.lead[idx]!) then some .leader
  else if phys.any (fun idx => g.hole[idx]!) then some .deletion
  else if isSerialPlusBlock g phys 0 psi && isSerialPlusBlock g phys psi psi then some .serial
  else none

/-- The allowed edges (§4's active macro plus the one §4 exception), indexed
by left endpoint (`edge i` moves `phys[i] -> phys[(i+1)%n]`). Recomputed every
step since the `A3`-at-`B_head` exception is state-dependent. -/
def allowedEdges {ψ κ : Nat} (g : Ag ψ κ) (phys : Array Nat) (psi n : Nat) : Array Nat := Id.run do
  let mut es : Array Nat := #[]
  for i in [0:psi - 1] do es := es.push i          -- B internal
  for i in [psi:2 * psi - 1] do es := es.push i    -- X internal
  es := es.push (psi - 1)                           -- seam B_terminal -> X_head
  es := es.push (2 * psi - 1)                       -- outgoing X_terminal -> U_head
  if (getAg g phys 0).elim false isA3 then es := es.push (n - 1)  -- exception: U_terminal -> B_head
  return es

/-! ## Restricted random walk -/

structure WalkResult where
  outcome : Outcome := .neither
  steps : Nat := 0
  finalConfig : Json := Json.null
  deriving Inhabited

def oneRestrictedWalk {ψ κ : Nat} (g0 : Ag ψ κ)
    (tr : Agent ψ κ → Agent ψ κ → Except String (Agent ψ κ × Agent ψ κ)) (psi n : Nat)
    (phys0 : Array Nat) (steps : Nat) (rngSeed : UInt64) :
    IO (Ag ψ κ × WalkResult) := do
  let mut g := g0
  let mut phys := phys0
  let mut rng := rngSeed
  let report (g : Ag ψ κ) (phys : Array Nat) (o : Outcome) (i : Nat) : WalkResult :=
    { outcome := o, steps := i,
      finalConfig := Json.arr ((phys.filterMap fun idx => g.arr[idx]?).map PPLLAuthSim.encode) }
  if let some o := checkStop g phys psi then return (g, report g phys o 0)
  for i in [0:steps] do
    let edges := allowedEdges g phys psi n
    let (rng', v) := splitmix rng
    rng := rng'
    let e := edges[v.toNat % edges.size]!
    let jx := (e + 1) % n
    let (g', a', b') ← IO.ofExcept (g.step tr phys[e]! phys[jx]!)
    g := g'
    phys := (phys.set! e a').set! jx b'
    if let some o := checkStop g phys psi then return (g, report g phys o (i + 1))
  return (g, report g phys .neither steps)

def parseSeed {ψ κ : Nat} (g : Ag ψ κ) (n : Nat) (line : String) : IO (Ag ψ κ × Array Nat) := do
  let j ← IO.ofExcept (Json.parse line)
  let cfg ← IO.ofExcept (PPLLAuthSim.decodeConfig (ψ := ψ) (κ := κ) n j)
  let mut g := g
  let mut c : Array Nat := #[]
  for a in cfg do
    let (g', i) := g.intern a
    g := g'
    c := c.push i
  return (g, c)

def runWalk (psi kappa : Nat) (seedPath outDir : System.FilePath) (only : Array Nat)
    (steps : Nat) (rngSeed0 : UInt64) (heartbeat : Nat) : IO UInt32 := do
  if hpsi : psi > 0 then
    let n := 3 * psi
    let tr ← match localTransition "authFplusmcc" hpsi kappa with
      | .ok t => pure t
      | .error e => throw (IO.userError e)
    IO.FS.createDirAll outDir
    let resPath := outDir / "results.jsonl"
    IO.FS.writeFile resPath ""
    let mut g : Ag psi kappa := {}
    let lines := (← IO.FS.lines seedPath).filter (fun l => !l.trimAscii.toString.isEmpty)
    let t0 ← IO.monoMsNow
    for si in [0:lines.size] do
      if !only.isEmpty && !only.contains si then continue
      let (g', phys0) ← parseSeed g n lines[si]!
      g := g'
      let rngSeed : UInt64 := rngSeed0 + si.toUInt64 * 0x2545F4914F6CDD1D
      let (g', r) ← oneRestrictedWalk g tr psi n phys0 steps rngSeed
      g := g'
      let row := Json.mkObj
        [ ("seed", si), ("psi", psi), ("n", n), ("kappa", kappa)
        , ("outcome", r.outcome.toStr), ("steps", r.steps), ("final_config", r.finalConfig) ]
      let h ← IO.FS.Handle.mk resPath .append
      h.putStrLn row.compress
      h.flush
      if (si + 1) % heartbeat == 0 || si + 1 == lines.size then
        let el := ((← IO.monoMsNow) - t0).toFloat / 1000.0
        IO.eprintln s!"seed {si + 1}/{lines.size} elapsed={el}s outcome={r.outcome.toStr}"
    return 0
  else throw (IO.userError "psi must be positive")

/-! ## Exact closure (BFS), restricted to the same allowed edges -/

def runCensus (psi kappa : Nat) (seedPath : System.FilePath) (cap : Nat) : IO UInt32 := do
  if hpsi : psi > 0 then
    let n := 3 * psi
    let tr ← match localTransition "authFplusmcc" hpsi kappa with
      | .ok t => pure t
      | .error e => throw (IO.userError e)
    let j ← IO.ofExcept (Json.parse (← IO.FS.readFile seedPath))
    let cfg ← IO.ofExcept (PPLLAuthSim.decodeConfig (ψ := psi) (κ := kappa) n j)
    let mut g : Ag psi kappa := {}
    let mut phys0 : Array Nat := #[]
    for a in cfg do
      let (g', i) := g.intern a
      g := g'
      phys0 := phys0.push i
    let keyOf (phys : Array Nat) : String :=
      String.intercalate "," (phys.toList.map toString)
    let mut visited : Std.HashMap String Unit := {}
    let mut frontier : Array (Array Nat) := #[phys0]
    visited := visited.insert (keyOf phys0) ()
    -- NOTE (fixed after the seed-1997 diagnostic): this used to stop the
    -- *entire* BFS the moment any target-satisfying node was dequeued, so
    -- `classes` reported only the early-exit prefix, not the true closure
    -- size — misleadingly small next to a random walk that can wander into
    -- a disjoint, target-free absorbing region and stay there. A
    -- target-satisfying node is still a sink (not expanded, matching a word
    -- that stops there), but the BFS now always runs to completion (or the
    -- cap), and `classes`/`reachable` describe the *whole* explored closure.
    let mut firstOutcome : Outcome := .neither
    let mut sawOutcome := false
    let mut leaderCount : Nat := 0
    let mut deletionCount : Nat := 0
    let mut serialCount : Nat := 0
    let mut capped := false
    let mut qi := 0
    while qi < frontier.size do
      let phys := frontier[qi]!
      qi := qi + 1
      match checkStop g phys psi with
      | some o =>
        if !sawOutcome then
          sawOutcome := true
          firstOutcome := o
        match o with
        | .leader => leaderCount := leaderCount + 1
        | .deletion => deletionCount := deletionCount + 1
        | .serial => serialCount := serialCount + 1
        | .neither => pure ()
        -- sink: do not expand further, but keep draining the frontier
      | none =>
        if visited.size > cap then
          capped := true
          qi := frontier.size
        else
          let edges := allowedEdges g phys psi n
          for e in edges do
            let jx := (e + 1) % n
            match g.step tr phys[e]! phys[jx]! with
            | .error _ => pure ()
            | .ok (g', a', b') =>
              g := g'
              let phys' := (phys.set! e a').set! jx b'
              let key' := keyOf phys'
              if !visited.contains key' then
                visited := visited.insert key' ()
                frontier := frontier.push phys'
    let classes := visited.size
    let outStr := if capped then "cap" else if sawOutcome then firstOutcome.toStr else "neither"
    IO.println (Json.mkObj [
      ("outcome", outStr), ("reachable", sawOutcome), ("classes", classes),
      ("leader_count", leaderCount), ("deletion_count", deletionCount),
      ("serial_count", serialCount), ("explored", qi), ("cap", cap)]).compress
    return 0
  else throw (IO.userError "psi must be positive")

/-- Diagnostic: dump the *entire* reachable multigraph from one seed, without
`runCensus`'s early exit at the first target hit (this is what a bottom-SCC /
trap check needs: `runCensus` alone only proves "not a counterexample", it
cannot rule out a disjoint trap region reachable from the same seed). A node
satisfying `checkStop` is a sink (not expanded, matching the real experiment:
the word stops there); every other node's *every* allowed outgoing edge is
recorded, so the result is the true nondeterministic transition graph, ready
for an offline SCC computation. -/
def runGraph (psi kappa : Nat) (seedPath : System.FilePath) (cap : Nat)
    (outPath : System.FilePath) : IO UInt32 := do
  if hpsi : psi > 0 then
    let n := 3 * psi
    let tr ← match localTransition "authFplusmcc" hpsi kappa with
      | .ok t => pure t
      | .error e => throw (IO.userError e)
    let j ← IO.ofExcept (Json.parse (← IO.FS.readFile seedPath))
    let cfg ← IO.ofExcept (PPLLAuthSim.decodeConfig (ψ := psi) (κ := kappa) n j)
    let mut g : Ag psi kappa := {}
    let mut phys0 : Array Nat := #[]
    for a in cfg do
      let (g', i) := g.intern a
      g := g'
      phys0 := phys0.push i
    let keyOf (phys : Array Nat) : String :=
      String.intercalate "," (phys.toList.map toString)
    let mut visited : Std.HashMap String Nat := {}
    let mut nodePhys : Array (Array Nat) := #[phys0]
    let mut nodeOutcome : Array String := #["start"]
    visited := visited.insert (keyOf phys0) 0
    let mut edgeList : Array (Nat × Nat × Nat) := #[]
    let mut capped := false
    let mut qi := 0
    while qi < nodePhys.size do
      let fromId := qi
      let phys := nodePhys[qi]!
      qi := qi + 1
      match checkStop g phys psi with
      | some o => nodeOutcome := nodeOutcome.set! fromId o.toStr  -- sink: no expansion
      | none =>
        if nodePhys.size > cap then
          capped := true
        else
          let edges := allowedEdges g phys psi n
          for e in edges do
            let jx := (e + 1) % n
            match g.step tr phys[e]! phys[jx]! with
            | .error _ => pure ()
            | .ok (g', a', b') =>
              g := g'
              let phys' := (phys.set! e a').set! jx b'
              let key' := keyOf phys'
              let toId ← match visited[key']? with
                | some id => pure id
                | none =>
                  let id := nodePhys.size
                  visited := visited.insert key' id
                  nodePhys := nodePhys.push phys'
                  nodeOutcome := nodeOutcome.push "none"
                  pure id
              edgeList := edgeList.push (fromId, e, toId)
    let nodesJson := Json.arr (Array.ofFn (n := nodePhys.size) fun i =>
      Json.mkObj [ ("id", i.val), ("outcome", nodeOutcome[i.val]!)
                 , ("config", Json.arr ((nodePhys[i.val]!.filterMap fun idx => g.arr[idx]?).map PPLLAuthSim.encode)) ])
    let edgesJson := Json.arr (edgeList.map fun (a, e, b) => Json.arr #[toJson a, toJson e, toJson b])
    IO.FS.writeFile outPath
      (Json.mkObj [("capped", capped), ("nodes", nodesJson), ("edges", edgesJson)]).compress
    IO.eprintln s!"nodes={nodePhys.size} edges={edgeList.size} capped={capped}"
    return 0
  else throw (IO.userError "psi must be positive")

/-- Same as `runGraph`, but with the frontier-restricted `allowedEdges` swapped
for the full unrestricted ring: every edge `0..n-1` is allowed at every step
(the actual `authFplusmcc` scheduler, no B/X/U macro discipline). Used to ask
whether a config found only reachable inside a *restricted-edge* trap is also
trapped under the real, unrestricted scheduler (a target-free bottom SCC here
would be a genuine zero-leader-liveness counterexample, not a walk artifact). -/
def runGraphFull (psi kappa : Nat) (seedPath : System.FilePath) (cap : Nat)
    (outPath : System.FilePath) : IO UInt32 := do
  if hpsi : psi > 0 then
    let n := 3 * psi
    let tr ← match localTransition "authFplusmcc" hpsi kappa with
      | .ok t => pure t
      | .error e => throw (IO.userError e)
    let j ← IO.ofExcept (Json.parse (← IO.FS.readFile seedPath))
    let cfg ← IO.ofExcept (PPLLAuthSim.decodeConfig (ψ := psi) (κ := kappa) n j)
    let mut g : Ag psi kappa := {}
    let mut phys0 : Array Nat := #[]
    for a in cfg do
      let (g', i) := g.intern a
      g := g'
      phys0 := phys0.push i
    let keyOf (phys : Array Nat) : String :=
      String.intercalate "," (phys.toList.map toString)
    let mut visited : Std.HashMap String Nat := {}
    let mut nodePhys : Array (Array Nat) := #[phys0]
    let mut nodeOutcome : Array String := #["start"]
    visited := visited.insert (keyOf phys0) 0
    let mut edgeList : Array (Nat × Nat × Nat) := #[]
    let mut capped := false
    let mut qi := 0
    let allEdges : Array Nat := Id.run do
      let mut es : Array Nat := #[]
      for i in [0:n] do es := es.push i
      return es
    while qi < nodePhys.size do
      let fromId := qi
      let phys := nodePhys[qi]!
      qi := qi + 1
      match checkStop g phys psi with
      | some o => nodeOutcome := nodeOutcome.set! fromId o.toStr  -- sink: no expansion
      | none =>
        if nodePhys.size > cap then
          capped := true
        else
          for e in allEdges do
            let jx := (e + 1) % n
            match g.step tr phys[e]! phys[jx]! with
            | .error _ => pure ()
            | .ok (g', a', b') =>
              g := g'
              let phys' := (phys.set! e a').set! jx b'
              let key' := keyOf phys'
              let toId ← match visited[key']? with
                | some id => pure id
                | none =>
                  let id := nodePhys.size
                  visited := visited.insert key' id
                  nodePhys := nodePhys.push phys'
                  nodeOutcome := nodeOutcome.push "none"
                  pure id
              edgeList := edgeList.push (fromId, e, toId)
    let nodesJson := Json.arr (Array.ofFn (n := nodePhys.size) fun i =>
      Json.mkObj [ ("id", i.val), ("outcome", nodeOutcome[i.val]!)
                 , ("config", Json.arr ((nodePhys[i.val]!.filterMap fun idx => g.arr[idx]?).map PPLLAuthSim.encode)) ])
    let edgesJson := Json.arr (edgeList.map fun (a, e, b) => Json.arr #[toJson a, toJson e, toJson b])
    IO.FS.writeFile outPath
      (Json.mkObj [("capped", capped), ("nodes", nodesJson), ("edges", edgesJson)]).compress
    IO.eprintln s!"nodes={nodePhys.size} edges={edgeList.size} capped={capped}"
    return 0
  else throw (IO.userError "psi must be positive")

end ZZAuthFrontierWalk

def main (args : List String) : IO UInt32 := do
  match args with
  | "walk" :: psiS :: kappaS :: seedPath :: outDir :: rest =>
    let rec parseFlags : List String → List (String × String)
      | flag :: value :: xs => (flag, value) :: parseFlags xs
      | _ => []
    let flags := parseFlags rest
    let getS (k : String) : Option String := (flags.find? (fun p => p.1 == k)).map (fun p => p.2)
    let getN (k : String) (d : Nat) : Nat := (getS k).map (fun s => s.toNat!) |>.getD d
    let only : Array Nat := match getS "--only" with
      | some s => (s.splitOn ",").toArray.map (fun t => t.toNat!)
      | none => #[]
    ZZAuthFrontierWalk.runWalk psiS.toNat! kappaS.toNat! seedPath outDir only
      (getN "--steps" 1000000) (UInt64.ofNat (getN "--rngseed" 1)) (getN "--heartbeat" 500)
  | "census" :: psiS :: kappaS :: seedPath :: capS :: [] =>
    ZZAuthFrontierWalk.runCensus psiS.toNat! kappaS.toNat! seedPath capS.toNat!
  | "graph" :: psiS :: kappaS :: seedPath :: capS :: outPath :: [] =>
    ZZAuthFrontierWalk.runGraph psiS.toNat! kappaS.toNat! seedPath capS.toNat! outPath
  | "graphfull" :: psiS :: kappaS :: seedPath :: capS :: outPath :: [] =>
    ZZAuthFrontierWalk.runGraphFull psiS.toNat! kappaS.toNat! seedPath capS.toNat! outPath
  | _ =>
    IO.eprintln "usage: zz-auth-frontier walk PSI KAPPA SEEDS.jsonl OUTDIR [--only i,j,..] [--steps S] [--rngseed R] [--heartbeat K]"
    IO.eprintln "       zz-auth-frontier census PSI KAPPA SEED.json CAP"
    IO.eprintln "       zz-auth-frontier graph PSI KAPPA SEED.json CAP OUT.json"
    IO.eprintln "       zz-auth-frontier graphfull PSI KAPPA SEED.json CAP OUT.json"
    return 2
