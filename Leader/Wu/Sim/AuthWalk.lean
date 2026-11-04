import Std.Data.HashMap
import Leader.Wu.Sim.AuthCarrier

/-!
# Random-walk search for AuthF (copy of `PPLLZDivWalk`)

Copy of `Leader/Wu/Sim/ZeroDivisibleWalk.lean` with the agent carrier replaced by
`PPLLAuthSim.AuthB` (bounded core + AuthF sidecars), its codec and local transition,
and the tail-dedup key forced to fingerprint mode (agent indices may exceed 16 bits).
Search logic unchanged except `--target leader_or_hole`, which also stops a walk at a main-path hole, and `--record`, which outputs the edge word of the last walk; the original documentation follows.


Design-exploration tool, not a proof certificate.  Deliberately does **not**
import `Leader.Wu.Sim.DiskClosureCensus`: that file declares a top-level `def main` (it
is itself an executable root), which would collide with this file's own
`main`.  Instead `Agent`, `reify`, `localTransition`, `mix64`, `KeyMode`,
`keyOf`, `canon`, `Ag` (interning + memoised `step`), `leaders` and
`isTarget` are copied verbatim from `PPLLDiskCensus` below (shadow copy, per
the house rule against appending to an accepted module); any semantic change
there must be mirrored here by hand.

Reuses that agent interning, memoised local transition (`Ag.step`),
rotation-class canonicalisation (`canon`) and leader test (`isTarget`)
verbatim; only the search strategy differs: instead of exhaustive BFS with a
disk-backed visited set, this tool runs many independent long random walks
from each seed on the *physical* configuration (no visited-set bookkeeping
at all, hence "cheap").

Two edge-choice policies, both on the same real `localTransition`:

* `unbiased`: at each step pick an edge `e ∈ [0, n)` uniformly (a single
  transition is computed).  A run of `4n` consecutive no-op picks triggers an
  explicit check of all `n` edges to confirm a genuine deadlock (a
  configuration whose every edge is a no-op is an absolute fixed point, not
  an artifact of the sampler).
* `biased`: at each step compute all `n` edges' outcomes, then pick uniformly
  among the edges that actually change the configuration (skipping no-ops
  outright); if none change, the configuration is a genuine deadlock.

A walk stops at the first configuration with a leader (`isTarget` mode 1,
rotation-independent) and records the word length.  For the *last* walk of
each (seed, mode) that never finds a leader, the set of distinct rotation
classes (`canon` + `keyOf`, same 128-bit exact key as the disk census for
`n ≤ 8`) visited in its final `--tail` steps is recorded, to flag a small
recurring trap worth an exact closure.

Usage:
`ppll-zdiv-walk VARIANT N PSI KAPPA SEEDS.jsonl OUTDIR
   [--only i,j,…] [--walks W] [--steps S] [--tail T] [--rngseed R]
   [--modes unbiased,biased] [--heartbeat K]`
-/

set_option autoImplicit false

open Lean

namespace PPLLAuthWalk

/-! ## Shadow copy of the `PPLLDiskCensus` pieces this tool needs (see module
docstring for why this is a copy rather than an import). -/

abbrev Agent (ψ κ : Nat) := PPLLAuthSim.AuthB ψ κ

def localTransition (variant : String) {ψ : Nat} (hψ : ψ > 0) (κ : Nat) :
    Except String (Agent ψ κ → Agent ψ κ → Except String (Agent ψ κ × Agent ψ κ)) :=
  PPLLAuthSim.localTransition variant hψ κ

@[inline] def mix64 (x : UInt64) : UInt64 :=
  let x := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
  let x := (x ^^^ (x >>> 27)) * 0x94d049bb133111eb
  x ^^^ (x >>> 31)

/-- Key mode: `exact` packs the `n` agent fields (index + 1, `w` bits each,
`per` fields per word) into 128 bits; otherwise a 128-bit fingerprint. -/
structure KeyMode where
  exact : Bool
  w : Nat
  per : Nat

def keyOf (km : KeyMode) (c : Array Nat) : UInt64 × UInt64 := Id.run do
  if km.exact then
    let mut lo : UInt64 := 0
    let mut hi : UInt64 := 0
    for j in [0:c.size] do
      let v := (c[j]! + 1).toUInt64
      if j < km.per then lo := (lo <<< km.w.toUInt64) ||| v
      else hi := (hi <<< km.w.toUInt64) ||| v
    return (lo, hi)
  else
    let mut h1 : UInt64 := 0x243F6A8885A308D3
    let mut h2 : UInt64 := 0x13198A2E03707344
    for j in [0:c.size] do
      let v := (c[j]! + 1).toUInt64
      h1 := mix64 (h1 ^^^ (v * 0x9E3779B97F4A7C15))
      h2 := mix64 (h2 + v * 0xC2B2AE3D27D4EB4F + 0x165667B19E3779F9)
    if h1 == 0 && h2 == 0 then return (1, 0) else return (h1, h2)

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
    let isHole : Bool := a.hole
    let g' : Ag ψ κ :=
      { arr := g.arr.push a, ix := g.ix.insert key i, lead := g.lead.push a.leader
        hole := g.hole.push isHole, memo := g.memo }
    (g', i)

/-- Interned local transition on the pair of agent indices `(x, y)`, memoised. -/
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

def leaders {ψ κ : Nat} (g : Ag ψ κ) (c : Array Nat) : Nat :=
  c.foldl (fun acc i => if g.lead[i]! then acc + 1 else acc) 0

/-- Stop predicate of a class: `mode = 1` some cell is a leader. -/
def isTarget {ψ κ : Nat} (g : Ag ψ κ) (mode : Nat) (c : Array Nat) : Bool :=
  mode != 0 && c.any fun i => g.lead[i]! || (mode == 2 && g.hole[i]!)

/-- Is rotation `k` of `c` lexicographically smaller than rotation `b`? -/
def rotLess (c : Array Nat) (k b : Nat) : Bool := Id.run do
  let n := c.size
  for j in [0:n] do
    let x := c[(k + j) % n]!
    let y := c[(b + j) % n]!
    if x < y then return true
    if y < x then return false
  return false

/-- Least rotation, same as `PPLLDiskCensus.canon`. -/
def canon (c : Array Nat) : Array Nat := Id.run do
  let n := c.size
  let mut best := 0
  for k in [1:n] do
    if rotLess c k best then best := k
  if best == 0 then return c
  return Array.ofFn (n := n) fun j => c[(best + j.val) % n]!

/-- splitmix64: `s` is the running state, the second component is a
pseudo-random `UInt64` output (reuses `PPLLDiskCensus.mix64`). -/
@[inline] def splitmix (s : UInt64) : UInt64 × UInt64 :=
  let s' := s + 0x9E3779B97F4A7C15
  (s', mix64 s')

/-- Result of the `walks` runs of one (seed, mode) combination. -/
structure ModeResult where
  mode : String
  walks : Nat
  stepsPerWalk : Nat
  found : Bool := false
  foundWalk : Option Nat := none
  wordLength : Option Nat := none
  deadlock : Bool := false
  deadlockWalk : Option Nat := none
  deadlockStep : Option Nat := none
  totalSteps : Nat := 0
  tailWindow : Nat := 0
  tailDistinct : Option Nat := none
  seconds : Float := 0.0
  finalConfig : Option Json := none
  /-- `--record`: the edge word of the last walk run (replayable with ppll-authf-replay). -/
  word : Option (Array Nat) := none
  deriving Inhabited

def ModeResult.toJson2 (r : ModeResult) : Json :=
  Json.mkObj
    [ ("mode", r.mode), ("walks", r.walks), ("steps_per_walk", r.stepsPerWalk)
    , ("found", r.found)
    , ("found_walk", match r.foundWalk with | some w => toJson w | none => Json.null)
    , ("word_length", match r.wordLength with | some l => toJson l | none => Json.null)
    , ("final_config", r.finalConfig.getD Json.null)
    , ("word", match r.word with | some w => toJson w | none => Json.null)
    , ("deadlock", r.deadlock)
    , ("deadlock_walk", match r.deadlockWalk with | some w => toJson w | none => Json.null)
    , ("deadlock_step", match r.deadlockStep with | some s => toJson s | none => Json.null)
    , ("total_steps", r.totalSteps)
    , ("tail_window", r.tailWindow)
    , ("tail_distinct", match r.tailDistinct with | some d => toJson d | none => Json.null)
    , ("seconds", toJson r.seconds) ]

/-- All `n` local transitions from `phys` at once: `succA e`, `succB e` are
the two outputs of firing edge `e`; `changed` lists the edges that actually
change their pair.  Threads `Ag` through the memoised transition. -/
def allEdges {ψ κ : Nat} (g : Ag ψ κ)
    (tr : Agent ψ κ → Agent ψ κ → Except String (Agent ψ κ × Agent ψ κ)) (n : Nat)
    (phys : Array Nat) :
    IO (Ag ψ κ × Array Nat × Array Nat × Array Nat) := do
  let mut g := g
  let mut succA := Array.ofFn (n := n) (fun _ => 0)
  let mut succB := Array.ofFn (n := n) (fun _ => 0)
  let mut changed : Array Nat := #[]
  for e in [0:n] do
    let jx := (e + 1) % n
    let (g', a', b') ← IO.ofExcept (g.step tr phys[e]! phys[jx]!)
    g := g'
    succA := succA.set! e a'
    succB := succB.set! e b'
    if a' != phys[e]! || b' != phys[jx]! then changed := changed.push e
  return (g, succA, succB, changed)

/-- One walk of at most `steps` steps from `phys0`.  Returns the updated `Ag`,
whether a leader was found (and the word length, i.e. the 1-based step index),
whether a deadlock was hit (and at which step), the number of steps actually
run, and — only when `collect` is true — the set of 128-bit keys of the
distinct `canon` classes visited in the trailing `tail` steps. -/
def oneWalk {ψ κ : Nat} (g0 : Ag ψ κ)
    (tr : Agent ψ κ → Agent ψ κ → Except String (Agent ψ κ × Agent ψ κ)) (n : Nat)
    (biased : Bool) (phys0 : Array Nat) (steps tail : Nat) (rngSeed : UInt64)
    (km : KeyMode) (collect : Bool) (tmode : Nat := 1) (record : Bool := false) :
    IO (Ag ψ κ × Bool × Option Nat × Bool × Option Nat × Nat × Nat × Array Nat × Array Nat) := do
  let mut g := g0
  let mut phys := phys0
  let mut rng := rngSeed
  let collectFrom := if steps > tail then steps - tail else 0
  -- dedup key for the tail-distinct count: the disk census's 128-bit exact
  -- key, folded into one `UInt64` (collision-negligible at tail-window scale)
  let mut tailSet : Std.HashMap UInt64 Unit := {}
  let mut found : Option Nat := none
  let mut deadlockAt : Option Nat := none
  let mut stalled := 0
  let mut ran := 0
  let mut word : Array Nat := #[]
  for i in [0:steps] do
    if biased then
      let (g', succA, succB, changed) ← allEdges g tr n phys
      g := g'
      if changed.isEmpty then
        deadlockAt := some i
      else
        let (rng', v) := splitmix rng
        rng := rng'
        let e := changed[v.toNat % changed.size]!
        let jx := (e + 1) % n
        phys := (phys.set! e (succA[e]!)).set! jx (succB[e]!)
        if record then word := word.push e
    else
      let (rng', v) := splitmix rng
      rng := rng'
      let e := v.toNat % n
      let jx := (e + 1) % n
      if record then word := word.push e
      let (g', a', b') ← IO.ofExcept (g.step tr phys[e]! phys[jx]!)
      g := g'
      if a' == phys[e]! && b' == phys[jx]! then stalled := stalled + 1 else stalled := 0
      phys := (phys.set! e a').set! jx b'
      if stalled ≥ 4 * n then
        let (g2, _, _, changed2) ← allEdges g tr n phys
        g := g2
        if changed2.isEmpty then deadlockAt := some i
        stalled := 0
    ran := ran + 1
    if deadlockAt.isSome then break
    if collect && i ≥ collectFrom then
      let (lo, hi) := keyOf km (canon phys)
      let key := mix64 lo ^^^ mix64 hi
      tailSet := tailSet.insert key ()
    if isTarget g tmode phys then
      found := some (i + 1)
      break
  return (g, found.isSome, found, deadlockAt.isSome, deadlockAt, ran, tailSet.size, phys, word)

/-- `walks` independent walks of `steps` steps each for one (seed, mode)
combination; stops early once a leader is found.  Tail-distinct bookkeeping
is only done for the *last* walk actually run (cheapest, and it is the one
`ZDIV.md §17`-style reporting wants: a trap in the final walk). -/
def runMode {ψ κ : Nat} (g0 : Ag ψ κ)
    (tr : Agent ψ κ → Agent ψ κ → Except String (Agent ψ κ × Agent ψ κ)) (n : Nat)
    (mode : String) (phys0 : Array Nat) (walks steps tail : Nat) (rngBase : UInt64)
    (km : KeyMode) (heartbeat : Nat) (label : String) (tmode : Nat := 1) (record : Bool := false) :
    IO (Ag ψ κ × ModeResult) := do
  let biased := mode == "biased"
  let mut g := g0
  let mut res : ModeResult := { mode := mode, walks := walks, stepsPerWalk := steps, tailWindow := min tail steps }
  let t0 ← IO.monoMsNow
  for w in [0:walks] do
    if res.found || res.deadlock then break
    let last := w == walks - 1
    -- decorrelate walk seeds: must NOT be an arithmetic-progression offset by
    -- `splitmix`'s own step increment (0x9E3779B97F4A7C15), or walk `w`'s
    -- stream is exactly walk 0's stream shifted by `w` steps (near-duplicate
    -- trajectories from the same `phys0`, not independent samples) — bug
    -- caught by rngseed diagnostics on seed 4 biased (2026-09-26)
    let rngSeed : UInt64 := mix64 (rngBase ^^^ mix64 (w.toUInt64 + 1))
    let (g', fnd, foundAt, dl, dlAt, ran, tdist, finalPhys, wd) ←
      oneWalk g tr n biased phys0 steps tail rngSeed km last tmode (record && last)
    if record && last then res := { res with word := some wd }
    g := g'
    res := { res with totalSteps := res.totalSteps + ran }
    -- the last configuration of the final walk is also reported when nothing was found,
    -- so an unreached seed can be re-seeded into the exact census (reproducible via --rngseed)
    if fnd || dl || last then
      let cfgJson := Json.arr ((finalPhys.filterMap fun i => g.arr[i]?).map PPLLAuthSim.encode)
      res := { res with finalConfig := some cfgJson }
    if fnd then
      res := { res with found := true, foundWalk := some w, wordLength := foundAt }
    else if dl then
      res := { res with deadlock := true, deadlockWalk := some w, deadlockStep := dlAt }
    else if last then
      res := { res with tailDistinct := some tdist }
    if (w + 1) % heartbeat == 0 || w + 1 == walks then
      let el := ((← IO.monoMsNow) - t0).toFloat / 1000.0
      IO.eprintln s!"{label} [{mode}] walk {w + 1}/{walks} totalSteps={res.totalSteps} elapsed={el}s"
  let secs := ((← IO.monoMsNow) - t0).toFloat / 1000.0
  return (g, { res with seconds := secs })

/-- Parse one seed line into an interned physical configuration, exactly as
`PPLLDiskCensus.run` does. -/
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

def run (variant : String) (n ψ κ : Nat) (seedPath outDir : System.FilePath) (only : Array Nat)
    (walks steps tail : Nat) (rngSeed0 : UInt64) (modes : Array String) (heartbeat : Nat)
    (tmode : Nat := 1) (record : Bool := false) :
    IO UInt32 := do
  if hψ : ψ > 0 then
    let tr ← match localTransition variant hψ κ with
      | .ok t => pure t
      | .error e => throw (IO.userError e)
    if n < 2 then throw (IO.userError "n must be at least 2")
    let km : KeyMode := ⟨false, 16, 4⟩
    IO.FS.createDirAll outDir
    let resPath := outDir / "results.jsonl"
    IO.FS.writeFile resPath ""
    let mut g : Ag ψ κ := {}
    let lines := (← IO.FS.lines seedPath).filter (fun l => !l.trimAscii.toString.isEmpty)
    for si in [0:lines.size] do
      if !only.isEmpty && !only.contains si then continue
      let (g', phys0) ← parseSeed g n lines[si]!
      g := g'
      IO.eprintln s!"=== seed {si} ({variant} n={n} psi={ψ} kappa={κ}) ==="
      let mut modeResults : Array Json := #[]
      for mode in modes do
        let rngBase : UInt64 := rngSeed0 + si.toUInt64 * 0x2545F4914F6CDD1D
          + (if mode == "biased" then 0x9E3779B97F4A7C15 else 0)
        let (g', r) ← runMode g tr n mode phys0 walks steps tail rngBase km heartbeat s!"seed {si}" tmode record
        g := g'
        modeResults := modeResults.push r.toJson2
        IO.eprintln s!"seed {si} [{mode}] done: {r.toJson2.compress}"
      let res := Json.mkObj
        [ ("seed", si), ("variant", variant), ("n", n), ("psi", ψ), ("kappa", κ)
        , ("modes", Json.arr modeResults) ]
      let h ← IO.FS.Handle.mk resPath .append
      h.putStrLn res.compress
      h.flush
      IO.println res.compress
    return 0
  else throw (IO.userError "psi must be positive")

end PPLLAuthWalk

def main (args : List String) : IO UInt32 := do
  match args with
  | variant :: n :: ψ :: κ :: seeds :: out :: flags =>
    match n.toNat?, ψ.toNat?, κ.toNat? with
    | some n, some ψ, some κ =>
      let rec opt (fs : List String) (k : String) : Option Nat :=
        match fs with
        | a :: b :: rest => if a == k then b.toNat? else opt (b :: rest) k
        | _ => none
      let rec sopt (fs : List String) (k : String) : Option String :=
        match fs with
        | a :: b :: rest => if a == k then some b else sopt (b :: rest) k
        | _ => none
      let known := ["--only", "--walks", "--steps", "--tail", "--rngseed", "--modes", "--heartbeat", "--target", "--record"]
      let flagsList := flags
      if flagsList.any (fun f => f.startsWith "--" && !known.contains f) then
        IO.eprintln s!"unknown flag in {flagsList}"; return 2
      let only : Array Nat := match sopt flagsList "--only" with
        | some l => ((l.splitOn ",").filterMap String.toNat?).toArray
        | none => #[]
      let modes : Array String := match sopt flagsList "--modes" with
        | some l => (l.splitOn ",").toArray
        | none => #["unbiased", "biased"]
      PPLLAuthWalk.run variant n ψ κ seeds out only
        ((opt flagsList "--walks").getD 1000) ((opt flagsList "--steps").getD 1000000)
        ((opt flagsList "--tail").getD 100000)
        (UInt64.ofNat ((opt flagsList "--rngseed").getD 1)) modes
        ((opt flagsList "--heartbeat").getD 50)
        (if sopt flagsList "--target" == some "leader_or_hole" then 2 else 1)
        (flagsList.contains "--record")
    | _, _, _ => IO.eprintln "numeric arguments expected"; return 2
  | _ =>
    IO.eprintln "usage: ppll-authf-walk VARIANT N PSI KAPPA SEEDS.jsonl OUTDIR [--only i,j,..] [--walks W] [--steps S] [--tail T] [--rngseed R] [--modes unbiased,biased] [--heartbeat K] [--target leader|leader_or_hole] [--record]"
    return 2
