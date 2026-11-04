import Leader.Wu.Sim.AuthHygieneClosureLib
import Leader.Wu.Sim.AuthCarrier
import Leader.Wu.Sim.AuthHygieneTransition
import Leader.Wu.Authorization.DebrisHygiene
import Leader.Wu.Sim.AuthSeamTransition

/-!
# Full-field seed-309 diagnosis: `authFplusmcc` vs `authFchamp`/`authFchampNF`/ablations

Design-exploration tool, not a proof certificate. Diagnoses the seed-309 regression
(`ψ=2 n=4 κ=1`, `run/verification/g62/champ/REGRESSION.md` §"Seed 309": `authFplusmcc`
elects within cap 300000, `authFchamp`/`authFchampNF` do not) by dumping *every* field of
every cell along the electing word, not just the compact `cellStr` summary
`ZZAuthChampCensus`/`ZZAuthChampLib` print.

**Does not `import Leader.Wu.Sim.AuthHygieneClosure`.** That file declares a top-level `def main`
(its own docstring: "that file is a `lean_exe` root with its own top-level `main`, so it
cannot be `import`ed alongside another `main`" — the reason it itself copies
`ZZSimClaimsAuth`'s RNG verbatim instead of importing it; `Leader/Wu/Sim/AuthWalk.lean` states
the identical rule about `PPLLDiskCensus`). Instead this file imports
`Leader.Wu.Sim.AuthHygieneClosureLib`, a `main`-free shadow copy of `ZZAuthChampCensus`'s body (lines
35–547, namespace renamed), and reuses its `Agent`/`Ag`/`Ag.intern`/`Ag.step`/
`variantTransition`/`randRing`/`ablationConfigs`/`ablationPowerSet` directly.

## Commands (interpreter: `lake env lean --run Leader/Wu/Sim/AuthSeamSeedDiagnosis.lean ...`)

* `seedcfg PSI N KAPPA SEED` — dump the initial random-dirty seed ring (full per-cell
  field dump), built exactly as `ZZAuthChampCensus.compare`/`ablate` build it
  (`g0 := (UInt64.ofNat (seed * 1000003 + 17)) ||| 1`, then `ZZAuthChampLib.randRing`).
* `seedword PSI N KAPPA CAP SEED VARIANT` — rebuild the same seed ring, then run the
  capped BFS under VARIANT (`ZZAuthChampLib.variantTransition`/`PPLLAuthSimChamp.
  champTransitionCfg`) with parent pointers, stopping at the first configuration
  containing a leader (or the cap). Prints the initial configuration (full field dump),
  the shortest electing word as a list of edges, and the full trace: after each edge, a
  full field dump (old -> new) of every cell whose fields changed, plus a one-line
  `cellStrExt` summary of all cells.
* `seedreplay PSI N KAPPA SEED VARIANT WORD` — WORD a comma-separated edge list (e.g.
  `1,0,2,1`). Replays WORD under VARIANT, and in parallel, at each step, computes what
  `authFplusmcc` would produce from the *same* input configuration; prints VARIANT's
  per-step trace (changed fields, old -> new) and, at the first step where VARIANT's
  output differs from `authFplusmcc`'s output on that same input, prints
  `DIVERGENCE step k edge e` with the differing fields of both served cells; continues
  replaying VARIANT (its own transition, not `authFplusmcc`'s) to the end of WORD and
  reports whether a leader appears. `VARIANT = all` replays WORD under every one of
  `authFplusmcc`, `authFchamp`, `authFchampNF`, `ZZAuthChampLib.ablationConfigs`'s four
  single-flag ablations (`no_emptyScrub`/`no_seamFence`/`no_lotteryScrub`/
  `no_strictScope`), and `ZZAuthChampLib.ablationPowerSet`'s 16 power-set names
  (`e=..,sf=..,l=..,sc=..`) — 23 variants total — each reported against `authFplusmcc` on
  its own copy of the starting configuration (compact `cellStrExt` summaries per step
  rather than full field dumps, to keep the output bounded across 23 variants).

## Field dump

`dumpFields` prints, per cell: `label`, `bit`, `state`, `path`, `path2` (with its
`path2_scope` and `path2_mark`), `path4` and `path4_mark`, `path5` and `path5_mark`, `p`,
`p_carry`, `path_mark`, `ctrl_mark`, `wait`, `count`, `write_state`, `write`, `leader`,
`reset_cmd`, `echo` — every field the task names, read off `PPLLAuthSim.toState` (the
erased `AuthState`, so `path4`/`path5` print as `Int × Nat` with `-1` for the CLEAN
sentinel, matching `PPLLAuthChamp`'s own `isCmd` convention) plus the six `Marks`
sidecars.
-/

set_option autoImplicit false

open Lean PPLLAuthF PPLLAuthSim ZZAuthChampLib

namespace ZZAuthSeamCensus

abbrev Agent (ψ κ : Nat) := ZZAuthChampLib.Agent ψ κ

/-! ## Formatting helpers for the full field dump -/

def fmtBool (b : Bool) : String := if b then "1" else "0"
def fmtMain (s : MainState) : String := (reprStr s).replace "MainState." ""
def fmtWS (s : WriteState) : String := (reprStr s).replace "WriteState." ""
def fmtWA (s : WriteAction) : String := (reprStr s).replace "WriteAction." ""
def fmtScope (s : P2Scope) : String := match s with | .line => "line" | .session => "session"

def fmtPathInfo : PathInfo → String
  | .bot => "bot"
  | .some l b => s!"{l}/{b}"

def fmtCleanPath (p : Option (Int × Nat)) : String :=
  match p with
  | none => "none"
  | some (l, b) => s!"{l}/{b}"

def fmtPath2 (p : Option Path2Info) : String :=
  match p with
  | none => "none"
  | some t => s!"{t.label}/{t.bit}@{t.position}A{t.action}"

def fmtCleaningLabel {ψ : Nat} : CleaningLabel ψ → String
  | .normal l => s!"{l.val}"
  | .clean => "CLEAN"

/-- Every field the task names, read off the erased `AuthState` (`PPLLAuthSim.toState`)
plus the six `Marks` sidecars, as `(fieldName, value)` pairs in a fixed order. -/
def dumpFields {ψ κ : Nat} (a : Agent ψ κ) : Array (String × String) :=
  let u := PPLLAuthSim.toState a
  #[("label", s!"{u.core.label.val}"),
    ("bit", fmtBool u.core.bit),
    ("state", fmtMain u.core.state),
    ("path", fmtPathInfo u.core.path),
    ("path2", fmtPath2 u.core.path2),
    ("path2_scope", fmtScope u.path2_scope),
    ("path2_mark", s!"{u.path2_mark.val}"),
    ("path4", fmtCleanPath u.core.path4),
    ("path4_mark", s!"{u.path4_mark.val}"),
    ("path5", fmtCleanPath u.core.path5),
    ("path5_mark", s!"{u.path5_mark.val}"),
    ("p", fmtBool u.core.p),
    ("p_carry", fmtBool u.core.p_carry),
    ("path_mark", s!"{u.path_mark.val}"),
    ("ctrl_mark", s!"{u.ctrl_mark.val}"),
    ("wait", fmtBool u.core.wait),
    ("count", s!"{u.core.count}"),
    ("write_state", fmtWS u.core.write_state),
    ("write", fmtWA u.core.write),
    ("leader", fmtBool u.core.leader),
    ("reset_cmd", fmtBool u.core.reset_cmd),
    ("echo", fmtBool u.core.echo)]

def dumpCellLine {ψ κ : Nat} (i : Nat) (a : Agent ψ κ) : String :=
  s!"cell{i}: " ++ String.intercalate " " ((dumpFields a).toList.map fun p => s!"{p.1}={p.2}")

/-- Fields that differ between two cells, as `(fieldName, oldValue, newValue)`. Empty iff
`dumpFields old = dumpFields new_` fieldwise. -/
def diffFields {ψ κ : Nat} (old new_ : Agent ψ κ) : Array (String × String × String) :=
  let fo := dumpFields old
  let fn := dumpFields new_
  Id.run do
    let mut out : Array (String × String × String) := #[]
    for i in [0:fo.size] do
      let (k, vo) := fo[i]!
      let (_, vn) := fn[i]!
      if vo != vn then out := out.push (k, vo, vn)
    return out

/-- `ZZAuthChampLib.cellStr` extended with `path4`/`path5`/`p`/`p_carry` (task's requested
compact per-step summary), read off the interned bounded core directly (not the erased
`AuthState`, matching `cellStr`'s own convention). -/
def cellStrExt {ψ κ : Nat} (a : Agent ψ κ) : String :=
  let p := match ZZAuthChampLib.pathInfo a with | some (l, b) => s!"{l}/{b}" | none => "--"
  let st := (reprStr a.core.state).replace "MainState." ""
  let t := match a.core.path2 with | some t => s!" A{t.action.val}@{t.position.val}" | none => ""
  let p4 := match a.core.path4 with
    | some (cl, b) => s!" p4={fmtCleaningLabel cl}/{b.val}"
    | none => ""
  let p5 := match a.core.path5 with
    | some (cl, b) => s!" p5={fmtCleaningLabel cl}/{b.val}"
    | none => ""
  s!"[{if a.core.bit then 1 else 0} {p} {st}{t}{p4}{p5} p={if a.core.p then 1 else 0} pc={if a.core.p_carry then 1 else 0} c{a.m.ctrl.val}]"

/-! ## Variant resolution: `authFplusmcc`/`authFchamp`/`authFchampNF`/ablation names -/

/-- Every variant name `seedreplay ... all` iterates: the three champ anchors, the four
single-flag ablations (`ZZAuthChampLib.ablationConfigs` minus its `"full"` = `authFchamp`
duplicate), and the 16 power-set names (`ZZAuthChampLib.ablationPowerSet`). 23 total. -/
def allVariantNames : List String :=
  ["authFplusmcc", "authFchamp", "authFchampNF"] ++
  (ZZAuthChampLib.ablationConfigs.filter (fun p => p.1 != "full")).map (·.1) ++
  ZZAuthChampLib.ablationPowerSet.map (·.1) ++
  PPLLAuthSeam.variants.map (·.1)

/-- Resolve a variant name to its bounded-carrier transition. Tries
`PPLLAuthSimSeam.localTransition` first: it resolves every named `PPLLAuthSeam.SeamCfg`
(`sPlus`/`sChamp`/`sChampNF`/`sIRS`/`sIRSkeepCmd`/`sIRSonly`/`sIRSend`/`sCmdFence`/
`sCmdFenceOnly`/`sIRSendKeepCmd`/`sFenceCmdHalf`/`sFenceNoGenHalf`/`sOccCmdOnly`/
`sImpWitOnly`/`sLotScope`) directly, then falls back to `PPLLAuthSimChamp.localTransition`
(`"authFchamp"`, `"authFchampNF"`, `"authFplusmcc"`, and every other
`PPLLAuthF.variants` name). Only the ablation power-set/singleton names
(`ZZAuthChampLib.ablationConfigs`/`ablationPowerSet`, e.g. `no_seamFence` or
`e=..,sf=..,l=..,sc=..`) are unknown to it; those are resolved as a fallback exactly as
before. -/
def resolveVariant (name : String) {psi : Nat} (hpsi : psi > 0) (kappa : Nat) :
    Except String (Agent psi kappa → Agent psi kappa → Except String (Agent psi kappa × Agent psi kappa)) :=
  match PPLLAuthSimSeam.localTransition name hpsi kappa with
  | .ok t => .ok t
  | .error _ =>
    match (ZZAuthChampLib.ablationConfigs ++ ZZAuthChampLib.ablationPowerSet).find?
        (fun p => p.1 = name) with
    | some (_, cfg) => .ok (PPLLAuthSimChamp.champTransitionCfg hpsi kappa cfg)
    | none => .error s!"unknown variant {name}"

/-! ## Seed reconstruction (verbatim `ZZAuthChampCensus.compare`/`ablate` seed) -/

/-- The raw random-dirty seed ring, unintemed: exactly `ZZAuthChampCensus.compare`'s
`g0 := (UInt64.ofNat (seed * 1000003 + 17)) ||| 1` then `ZZAuthChampLib.randRing`. -/
def buildSeedRing (psi n kappa seed : Nat) (hpsi : psi > 0) : Array (Agent psi kappa) :=
  let g0 : ZZAuthChampLib.Rng := (UInt64.ofNat (seed * 1000003 + 17)) ||| 1
  (ZZAuthChampLib.randRing (κ := kappa) hpsi g0 n).2

/-- The same ring, interned into a fresh `Ag` table (for the BFS in `seedword`). -/
def buildSeedInterned (psi n kappa seed : Nat) (hpsi : psi > 0) :
    ZZAuthChampLib.Ag psi kappa × Array Nat :=
  let ring0 := buildSeedRing psi n kappa seed hpsi
  Id.run do
    let mut g : ZZAuthChampLib.Ag psi kappa := {}
    let mut phys0 : Array Nat := #[]
    for a in ring0 do
      let (g', k) := g.intern a
      g := g'
      phys0 := phys0.push k
    return (g, phys0)

def parseWord (s : String) : Array Nat :=
  ((s.splitOn ",").map (fun t => t.trim.toNat!)).toArray

/-- Canonical filler cell (all-neutral bounded core at label 0), only ever used as the
out-of-bounds default of `agetD` below; `Agent psi kappa` derives no `Inhabited` instance
(unsound for `psi = 0`, which `BoundedAgentState`'s own fields correctly refuse to paper
over), so every `Array (Agent psi kappa)` lookup in this file goes through `Array.getD`
with this explicit witness instead of panic-indexing `[i]!`. -/
def defaultAgent {psi kappa : Nat} (hpsi : psi > 0) : Agent psi kappa :=
  ⟨ZZAuthChampLib.neutralCore ⟨0, hpsi⟩, {}⟩

/-- `Array.getD` on an `Agent`-array with `defaultAgent hpsi` as the out-of-bounds
fallback (never actually hit: every call site indexes within a known-size ring/word). -/
def agetD {psi kappa : Nat} (hpsi : psi > 0) (a : Array (Agent psi kappa)) (i : Nat) :
    Agent psi kappa :=
  a.getD i (defaultAgent hpsi)

/-! ## `seedcfg`: dump the initial configuration only -/

def seedcfg (psi n kappa seed : Nat) : IO UInt32 := do
  if hpsi : psi > 0 then
    let ring0 := buildSeedRing psi n kappa seed hpsi
    IO.println s!"=== seedcfg psi={psi} n={n} kappa={kappa} seed={seed} ==="
    for i in [0:n] do IO.println (dumpCellLine i (agetD hpsi ring0 i))
    return 0
  else throw (IO.userError "psi must be positive")

/-! ## `seedword`: exact capped BFS to the first leader, with full trace -/

def seedword (psi n kappa cap seed : Nat) (variant : String) : IO UInt32 := do
  if hpsi : psi > 0 then
    let tr ← match resolveVariant variant hpsi kappa with
      | .ok t => pure t
      | .error e => throw (IO.userError e)
    let ring0 := buildSeedRing psi n kappa seed hpsi
    IO.println s!"=== seedword psi={psi} n={n} kappa={kappa} seed={seed} variant={variant} cap={cap} ==="
    IO.println "-- initial configuration --"
    for i in [0:n] do IO.println (dumpCellLine i (agetD hpsi ring0 i))
    let mut g : ZZAuthChampLib.Ag psi kappa := {}
    let mut phys0 : Array Nat := #[]
    for a in ring0 do
      let (g', k) := g.intern a
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
      if firstLeader.isSome then break
      let phys := nodes[qi]!
      if isLeader[qi]! then
        qi := qi + 1; continue
      if nodes.size > cap then
        capped := true; break
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
    IO.println s!"bfs nodes={nodes.size} capped={capped}"
    match firstLeader with
    | none =>
      IO.println "no leader found within cap"
      return 0
    | some t =>
      let mut chain : Array (Nat × Nat) := #[]
      let mut cur := t
      while cur != 0 do
        let (p, e) := parent[cur]!
        chain := chain.push (cur, e)
        cur := p
      chain := chain.reverse
      IO.println s!"shortest electing word: length {chain.size} edges {chain.toList.map (·.2)}"
      IO.println "-- trace --"
      let mut prevPhys := phys0
      let mut step := 0
      for (v, e) in chain do
        step := step + 1
        let curPhys := nodes[v]!
        let jx := (e + 1) % n
        IO.println s!"step {step} edge {e} (initiator cell{e}, responder cell{jx}):"
        for i in [0:n] do
          if prevPhys[i]! != curPhys[i]! then
            let oldA := agetD hpsi g.arr prevPhys[i]!
            let newA := agetD hpsi g.arr curPhys[i]!
            let diffs := diffFields oldA newA
            if !diffs.isEmpty then
              IO.println s!"  cell{i} changed:"
              for (k, vo, vn) in diffs do
                IO.println s!"    {k}: {vo} -> {vn}"
        let summary :=
          String.intercalate " "
            ((List.range n).map fun i => s!"{i}:{cellStrExt (agetD hpsi g.arr curPhys[i]!)}")
        IO.println s!"  summary: {summary}"
        prevPhys := curPhys
      IO.println "leader reached: true"
      return 0
  else throw (IO.userError "psi must be positive")

/-! ## `seedreplay`: replay a fixed word under VARIANT, diverging against `authFplusmcc` -/

/-- Replay `word` under `tr` starting from `ring0`, comparing at every step against what
`trPlus` (`authFplusmcc`) would produce from the *same* input configuration. `verbose`
turns on the full per-step field-changed dump (used for a single named VARIANT); the
`all`-variant sweep passes `verbose := false` and gets only the compact `cellStrExt`
summary line plus the divergence report, to keep 23-variant output bounded. -/
def replayVariant {psi kappa : Nat} (hpsi : psi > 0) (n : Nat)
    (trPlus : Agent psi kappa → Agent psi kappa → Except String (Agent psi kappa × Agent psi kappa))
    (name : String)
    (tr : Agent psi kappa → Agent psi kappa → Except String (Agent psi kappa × Agent psi kappa))
    (ring0 : Array (Agent psi kappa)) (word : Array Nat) (verbose : Bool) : IO Unit := do
  IO.println s!"--- variant {name} ---"
  let mut C := ring0
  let mut diverged := false
  let mut step := 0
  let mut leaderStep : Option Nat := none
  for e in word do
    step := step + 1
    let jx := (e + 1) % n
    let a0 := agetD hpsi C e
    let b0 := agetD hpsi C jx
    match tr a0 b0, trPlus a0 b0 with
    | .ok (a', b'), .ok (ap', bp') =>
      if !diverged then
        let da := diffFields a' ap'
        let db := diffFields b' bp'
        if !da.isEmpty || !db.isEmpty then
          diverged := true
          IO.println s!"DIVERGENCE step {step} edge {e}"
          if !da.isEmpty then
            IO.println s!"  cell{e} ({name} vs authFplusmcc):"
            for (k, vo, vn) in da do IO.println s!"    {k}: {vo} vs {vn}"
          if !db.isEmpty then
            IO.println s!"  cell{jx} ({name} vs authFplusmcc):"
            for (k, vo, vn) in db do IO.println s!"    {k}: {vo} vs {vn}"
      let newC := (C.set! e a').set! jx b'
      if verbose then
        let da2 := diffFields a0 a'
        let db2 := diffFields b0 b'
        IO.println s!"step {step} edge {e}:"
        if !da2.isEmpty then
          IO.println s!"  cell{e} changed:"
          for (k, vo, vn) in da2 do IO.println s!"    {k}: {vo} -> {vn}"
        if !db2.isEmpty then
          IO.println s!"  cell{jx} changed:"
          for (k, vo, vn) in db2 do IO.println s!"    {k}: {vo} -> {vn}"
        let summary :=
          String.intercalate " "
            ((List.range n).map fun i => s!"{i}:{cellStrExt (agetD hpsi newC i)}")
        IO.println s!"  summary: {summary}"
      C := newC
      if (a'.core.leader || b'.core.leader) && leaderStep.isNone then leaderStep := some step
    | .error err, _ =>
      IO.eprintln s!"{name} step {step} edge {e}: transition error {err}"
      break
    | _, .error errP =>
      IO.eprintln s!"authFplusmcc step {step} edge {e}: transition error {errP}"
      break
  if !diverged then IO.println s!"{name}: no divergence from authFplusmcc along this word"
  let leaderNow := C.any (fun a => a.core.leader)
  IO.println s!"{name}: leader={leaderNow} first_leader_step={leaderStep}"

def seedreplay (psi n kappa seed : Nat) (variant word : String) : IO UInt32 := do
  if hpsi : psi > 0 then
    let trPlus ← match ZZAuthChampLib.variantTransition "authFplusmcc" hpsi kappa with
      | .ok t => pure t
      | .error e => throw (IO.userError e)
    let ring0 := buildSeedRing psi n kappa seed hpsi
    let wordArr := parseWord word
    IO.println s!"=== seedreplay psi={psi} n={n} kappa={kappa} seed={seed} variant={variant} word={wordArr.toList} ==="
    IO.println "-- initial configuration --"
    for i in [0:n] do IO.println (dumpCellLine i (agetD hpsi ring0 i))
    if variant = "all" then
      for name in allVariantNames do
        match resolveVariant name hpsi kappa with
        | .error e => IO.eprintln s!"{name}: {e}"
        | .ok tr => replayVariant hpsi n trPlus name tr ring0 wordArr false
    else
      match resolveVariant variant hpsi kappa with
      | .error e => throw (IO.userError e)
      | .ok tr => replayVariant hpsi n trPlus variant tr ring0 wordArr true
    return 0
  else throw (IO.userError "psi must be positive")

end ZZAuthSeamCensus

def main (args : List String) : IO UInt32 := do
  match args with
  | ["seedword", p, n, k, c, sd, v] =>
    ZZAuthSeamCensus.seedword p.toNat! n.toNat! k.toNat! c.toNat! sd.toNat! v
  | ["seedreplay", p, n, k, sd, v, w] =>
    ZZAuthSeamCensus.seedreplay p.toNat! n.toNat! k.toNat! sd.toNat! v w
  | ["seedcfg", p, n, k, sd] =>
    ZZAuthSeamCensus.seedcfg p.toNat! n.toNat! k.toNat! sd.toNat!
  | _ =>
    IO.eprintln "usage: seedword PSI N KAPPA CAP SEED VARIANT
       | seedreplay PSI N KAPPA SEED VARIANT WORD
       | seedcfg PSI N KAPPA SEED"
    return 2
