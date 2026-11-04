import Lean.Data.Json
import Std.Data.HashMap
import Leader.Wu.Sim.BoundedCodec
import Leader.Wu.Sim.RawCodec
import Leader.Wu.Comparison.MovedBitCheck

/-!
# Closure census on the moved-bit carrier (board G6.2, design input)

Same algorithm and output format as `PPLLClosureCensus` (rotation classes,
`nodes.txt`, `edges.txt`, `agents.jsonl`, `unexpanded.txt`, `seedlog.json`,
`summary.json`), on the carrier `BoundedAgentState ψ κ × Bool` of
`PPLLMovedBit`.  An agent is encoded as the `ppll-bounded-agent-state-32.v1`
object plus a field `moved`; seeds without `moved` start with `moved = false`
(fail closed: an in-flight signal of a seed has not moved).

Every memoised pair transition also carries the birth tag of
`PPLLMovedBit.stepTagged`; `births.json` counts expanded class edges by source
leader count and tag, and each walk row counts birth events by tag.

Usage:
* `ppll-moved-census VARIANT N PSI KAPPA CAP SEEDCAP SEEDS OUTDIR`
* `ppll-moved-census walk VARIANT N PSI KAPPA STEPS RNG SEEDS OUT`
* `ppll-moved-census trace VARIANT PSI KAPPA PAIRS` (pairs `[a, b]` per line;
  prints each stage that changes the pair)
-/

set_option autoImplicit false

open Lean

namespace PPLLMovedCensus

open PPLLMovedBit

abbrev Agent (ψ κ : Nat) := BoundedAgentState ψ κ × Bool

def reify {ψ κ : Nat} (s : AgentState ψ) : Except String (BoundedAgentState ψ κ) :=
  PPLLSimCodec.decodeState (psi := ψ) (kappa := κ) (PPLLSimRawCodec.encodeState s)

def encodeAgent {ψ κ : Nat} (a : Agent ψ κ) : Json :=
  (PPLLSimCodec.encodeState a.1).setObjVal! "moved" (Json.bool a.2)

def decodeAgent {ψ κ : Nat} (j : Json) : Except String (Agent ψ κ) := do
  match j with
  | .obj kvs =>
    let m : Bool := match kvs.get? "moved" with
      | some (.bool b) => b
      | _ => false
    let s ← PPLLSimCodec.decodeState (psi := ψ) (kappa := κ) (.obj (kvs.erase "moved"))
    pure (s, m)
  | _ => throw "object expected"

def decodeCfg {ψ κ : Nat} (n : Nat) (j : Json) : Except String (Array (Agent ψ κ)) := do
  let a ← j.getArr?
  if a.size ≠ n then throw s!"configuration length {a.size}, expected {n}"
  a.mapM decodeAgent

def localTransition (variant : String) {ψ : Nat} (hψ : ψ > 0) (κ : Nat) :
    Except String (Agent ψ κ → Agent ψ κ → Except String (Agent ψ κ × Agent ψ κ × String)) :=
  match PPLLMovedBit.variants.find? (fun t => t.1 == variant) with
  | some (_, c) => .ok fun a b => do
      let (l, r, tag) := stepTagged hψ κ c (a.1.erase, a.2) (b.1.erase, b.2)
      let a' ← (reify (κ := κ) l.1).mapError fun e => s!"{variant}: left output out of domain ({e})"
      let b' ← (reify (κ := κ) r.1).mapError fun e => s!"{variant}: right output out of domain ({e})"
      pure ((a', l.2), (b', r.2), tag)
  | none => .error s!"unknown variant {variant}"

structure St (ψ κ : Nat) where
  agents : Array (Agent ψ κ) := #[]
  agentIx : Std.HashMap String Nat := {}
  memo : Std.HashMap (Nat × Nat) (Nat × Nat × String) := {}
  nodes : Array (Array Nat) := #[]
  nodeIx : Std.HashMap (Array Nat) Nat := {}

def intern {ψ κ : Nat} (st : St ψ κ) (a : Agent ψ κ) : St ψ κ × Nat :=
  let key := (encodeAgent a).compress
  match st.agentIx[key]? with
  | some i => (st, i)
  | none =>
    let i := st.agents.size
    ({ st with agents := st.agents.push a, agentIx := st.agentIx.insert key i }, i)

def addNode {ψ κ : Nat} (st : St ψ κ) (c : Array Nat) : St ψ κ × Nat × Bool :=
  match st.nodeIx[c]? with
  | some i => (st, i, false)
  | none =>
    let i := st.nodes.size
    ({ st with nodes := st.nodes.push c, nodeIx := st.nodeIx.insert c i }, i, true)

def canon (c : Array Nat) : Array Nat := Id.run do
  let n := c.size
  let mut best := c
  for k in [1:n] do
    let r := (c.extract k n) ++ (c.extract 0 k)
    if r.toList < best.toList then best := r
  return best

def leadersOf {ψ κ : Nat} (st : St ψ κ) (c : Array Nat) : Nat :=
  c.foldl (fun acc i => if (st.agents[i]?.map (·.1.leader)).getD false then acc + 1 else acc) 0

/-- Memoised pair step. -/
def pairStep {ψ κ : Nat}
    (tr : Agent ψ κ → Agent ψ κ → Except String (Agent ψ κ × Agent ψ κ × String))
    (st : St ψ κ) (i j : Nat) : Except String (St ψ κ × Nat × Nat × String) := do
  match st.memo[(i, j)]? with
  | some (a, b, t) => pure (st, a, b, t)
  | none =>
    let (some u, some v) := (st.agents[i]?, st.agents[j]?)
      | throw "agent index out of range"
    let (a, b, t) ← tr u v
    let (st1, ia) := intern st a
    let (st2, ib) := intern st1 b
    pure ({ st2 with memo := st2.memo.insert (i, j) (ia, ib, t) }, ia, ib, t)

def bump (m : Std.HashMap String Nat) (k : String) : Std.HashMap String Nat :=
  m.insert k (m.getD k 0 + 1)

def countsJson (m : Std.HashMap String Nat) : Json :=
  Json.mkObj ((m.toList.mergeSort (fun a b => a.1 ≤ b.1)).map fun (k, v) => (k, toJson v))

def run (variant : String) (n ψ κ cap seedCap : Nat) (seedPath outDir : System.FilePath) :
    IO UInt32 := do
  if hψ : ψ > 0 then
    let tr ← IO.ofExcept (localTransition variant hψ κ)
    if n < 2 then throw (IO.userError "n must be at least 2")
    let mut st : St ψ κ := {}
    let mut seedIds : Array Nat := #[]
    for line in (← IO.FS.lines seedPath) do
      if line.trimAscii.toString.isEmpty then continue
      let j ← IO.ofExcept (Json.parse line)
      let cfg ← IO.ofExcept (decodeCfg (ψ := ψ) (κ := κ) n j)
      let mut c : Array Nat := #[]
      for a in cfg do
        let (st', i) := intern st a
        st := st'
        c := c.push i
      let (st', i, _) := addNode st (canon c)
      st := st'
      seedIds := seedIds.push i
    let edgesH ← IO.FS.Handle.mk (outDir / "edges.txt") .write
    let mut expanded : Array Bool := Array.replicate st.nodes.size false
    let mut unexpanded : Array Nat := #[]
    let mut seedLog : Array Json := #[]
    let mut stopped := false
    -- births: key "<source leaders>|<tag>"
    let mut births : Std.HashMap String Nat := {}
    for si in [0:seedIds.size] do
      let s0 := seedIds[si]!
      if stopped then
        seedLog := seedLog.push (Json.mkObj [("seed", si), ("status", "not_started")])
        continue
      let before := st.nodes.size
      let mut queue : Array Nat := #[s0]
      let mut qh := 0
      let mut status := "complete"
      while qh < queue.size do
        let x := queue[qh]!
        qh := qh + 1
        if expanded[x]! then continue
        if st.nodes.size - before > seedCap || st.nodes.size > cap then
          status := if st.nodes.size > cap then "global_cap" else "seed_cap"
          for y in queue.extract (qh - 1) queue.size do
            if !expanded[y]! then unexpanded := unexpanded.push y
          break
        let c := st.nodes[x]!
        let lx := leadersOf st c
        let mut succ : Array Nat := #[]
        for e in [0:n] do
          let jx := (e + 1) % n
          let (st1, ia, ib, tag) ← IO.ofExcept (pairStep tr st c[e]! c[jx]!)
          st := st1
          if !tag.isEmpty then births := bump births s!"{lx}|{tag}"
          let (st', k, fresh) := addNode st (canon ((c.set! e ia).set! jx ib))
          st := st'
          if fresh then expanded := expanded.push false
          succ := succ.push k
          if !expanded[k]! then queue := queue.push k
        expanded := expanded.set! x true
        edgesH.putStrLn (" ".intercalate (toString x :: succ.toList.map toString))
      seedLog := seedLog.push (Json.mkObj
        [("seed", si), ("node", s0), ("status", status), ("new_classes", st.nodes.size - before)])
      if status == "global_cap" then stopped := true
    edgesH.flush
    let nodesH ← IO.FS.Handle.mk (outDir / "nodes.txt") .write
    for c in st.nodes do
      nodesH.putStrLn (" ".intercalate (toString (leadersOf st c) :: c.toList.map toString))
    nodesH.flush
    let agentsH ← IO.FS.Handle.mk (outDir / "agents.jsonl") .write
    for a in st.agents do
      agentsH.putStrLn (encodeAgent a).compress
    agentsH.flush
    IO.FS.writeFile (outDir / "seeds.txt") ("\n".intercalate (seedIds.toList.map toString) ++ "\n")
    let notExpanded := (List.range st.nodes.size).filter (fun i => !expanded[i]!)
    IO.FS.writeFile (outDir / "unexpanded.txt") ("\n".intercalate (notExpanded.map toString) ++ "\n")
    IO.FS.writeFile (outDir / "seedlog.json") ((Json.arr seedLog).compress ++ "\n")
    IO.FS.writeFile (outDir / "births.json") ((countsJson births).compress ++ "\n")
    let summary := Json.mkObj
      [ ("variant", variant), ("carrier", "bounded+moved"), ("n", n), ("psi", ψ), ("kappa", κ)
      , ("cap", cap), ("seed_cap", seedCap), ("quotient", "rotation classes")
      , ("classes", st.nodes.size), ("unexpanded", notExpanded.length)
      , ("agents", st.agents.size), ("pair_memo", st.memo.size), ("seeds", seedIds.size)
      , ("seeds_complete", (seedLog.filter fun j => j.getObjValD "status" == Json.str "complete").size) ]
    IO.FS.writeFile (outDir / "summary.json") (summary.compress ++ "\n")
    IO.println summary.compress
    return 0
  else throw (IO.userError "psi must be positive")

def xorshift (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

/-- Random walk, same generator and row format as `PPLLClosureCensus.walk`, plus
`births` (tag counts over the walk, keyed by the leader count before the step)
and `first_birth_tag`. -/
def walk (variant : String) (n ψ κ steps rng : Nat) (seedPath out : System.FilePath) :
    IO UInt32 := do
  if hψ : ψ > 0 then
    let tr ← IO.ofExcept (localTransition variant hψ κ)
    if n < 2 then throw (IO.userError "n must be at least 2")
    let h ← IO.FS.Handle.mk out .write
    let mut si : Nat := 0
    for line in (← IO.FS.lines seedPath) do
      if line.trimAscii.toString.isEmpty then continue
      let j ← IO.ofExcept (Json.parse line)
      let cfg ← IO.ofExcept (decodeCfg (ψ := ψ) (κ := κ) n j)
      let mut st : St ψ κ := {}
      let mut c : Array Nat := #[]
      for a in cfg do
        let (st', i) := intern st a
        st := st'
        c := c.push i
      let mut x : UInt64 := (UInt64.ofNat (rng * 1000003 + si + 1)) ||| 1
      let mut firstLeader : Int := -1
      let mut firstTag : String := ""
      let mut leaderlessLate : Nat := 0
      let mut maxLate : Nat := 0
      let mut births : Std.HashMap String Nat := {}
      if leadersOf st c > 0 then firstLeader := 0
      for t in [0:steps] do
        x := xorshift x
        let e := (x % (UInt64.ofNat n)).toNat
        let e1 := (e + 1) % n
        let k0 := leadersOf st c
        let (st1, ia, ib, tag) ← IO.ofExcept (pairStep tr st c[e]! c[e1]!)
        st := st1
        if !tag.isEmpty then
          births := bump births s!"{k0}|{tag}"
          if firstTag.isEmpty then firstTag := tag
        c := (c.set! e ia).set! e1 ib
        let k := leadersOf st c
        if k > 0 ∧ firstLeader < 0 then firstLeader := Int.ofNat (t + 1)
        if 2 * t ≥ steps then
          if k == 0 then leaderlessLate := leaderlessLate + 1
          if k > maxLate then maxLate := k
      let fin : Json := Json.arr (c.filterMap fun i => st.agents[i]? |>.map encodeAgent)
      h.putStrLn (Json.mkObj
        [ ("seed", toJson si), ("steps", toJson steps), ("first_leader_step", toJson firstLeader)
        , ("first_birth_tag", toJson firstTag)
        , ("late_leaderless_steps", toJson leaderlessLate), ("late_max_leaders", toJson maxLate)
        , ("final_leaders", toJson (leadersOf st c)), ("births", countsJson births)
        , ("final", fin) ]).compress
      h.flush
      si := si + 1
    return 0
  else throw (IO.userError "psi must be positive")

def brief {ψ : Nat} (u : MS ψ) : String :=
  let j := PPLLSimRawCodec.encodeState u.1
  let g (k : String) := (j.getObjValD k).compress
  s!"L{g "leader"} lab{g "label"} bit{g "bit"} mv{u.2} st{g "state"} path{g "path"} p2{g "path2"} p4{g "path4"} p5{g "path5"} rc{g "reset_cmd"} cnt{g "count"} w{g "wait"} sh{g "shield"} b{g "bullet"} sB{g "signal_B"}"

def trace (variant : String) (ψ κ : Nat) (pairs : System.FilePath) : IO UInt32 := do
  if hψ : ψ > 0 then
    let some (_, c) := PPLLMovedBit.variants.find? (·.1 == variant)
      | throw (IO.userError s!"unknown variant {variant}")
    let mut k := 0
    for line in (← IO.FS.lines pairs) do
      if line.trimAscii.toString.isEmpty then continue
      let j ← IO.ofExcept (Json.parse line)
      let arr ← IO.ofExcept j.getArr?
      let a ← IO.ofExcept (decodeAgent (ψ := ψ) (κ := κ) arr[0]!)
      let b ← IO.ofExcept (decodeAgent (ψ := ψ) (κ := κ) arr[1]!)
      IO.println s!"pair {k}"
      let mut l : MS ψ := (a.1.erase, a.2)
      let mut r : MS ψ := (b.1.erase, b.2)
      IO.println s!"  input: l=[{brief l}]\n         r=[{brief r}]"
      for (name, f) in stages hψ κ c do
        let q := f l r
        if q.1 != l || q.2 != r then
          IO.println s!"  {name}: l=[{brief q.1}]\n         r=[{brief q.2}]"
        l := q.1
        r := q.2
      k := k + 1
    return 0
  else throw (IO.userError "psi must be positive")

end PPLLMovedCensus

def main (args : List String) : IO UInt32 := do
  match args with
  | ["trace", v, ψ, κ, pairs] =>
    match ψ.toNat?, κ.toNat? with
    | some ψ, some κ => PPLLMovedCensus.trace v ψ κ pairs
    | _, _ => IO.eprintln "numeric arguments expected"; return 2
  | ["walk", variant, n, ψ, κ, steps, rng, seeds, out] =>
    match n.toNat?, ψ.toNat?, κ.toNat?, steps.toNat?, rng.toNat? with
    | some n, some ψ, some κ, some steps, some rng =>
      PPLLMovedCensus.walk variant n ψ κ steps rng seeds out
    | _, _, _, _, _ => IO.eprintln "numeric arguments expected"; return 2
  | [variant, n, ψ, κ, cap, seedCap, seeds, out] =>
    match n.toNat?, ψ.toNat?, κ.toNat?, cap.toNat?, seedCap.toNat? with
    | some n, some ψ, some κ, some cap, some seedCap =>
      PPLLMovedCensus.run variant n ψ κ cap seedCap seeds out
    | _, _, _, _, _ => IO.eprintln "numeric arguments expected"; return 2
  | _ => IO.eprintln "usage: ppll-moved-census VARIANT N PSI KAPPA CAP SEEDCAP SEEDS OUTDIR"; return 2
