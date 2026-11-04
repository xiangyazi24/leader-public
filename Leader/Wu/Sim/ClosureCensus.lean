import Lean.Data.Json
import Std.Data.HashMap
import Leader.Wu.Protocol.BoundedProtocol
import Leader.Wu.Sim.BoundedCodec
import Leader.Wu.Sim.RawCodec
import Leader.Wu.Birth.ChannelVariants
import Leader.Wu.Birth.TransitShiftVariants
import Leader.Wu.Elimination.CensusVariants
import Leader.Wu.Comparison.PostElectionCheckGuard
import Leader.Wu.ZeroDivisible.BoundaryEqualityBirths

/-!
# Exact reachable-closure census for the bounded P_PLL variants

Design-exploration tool (board G6.2), not a proof certificate.  Given a variant
on the bounded carrier (`bounded` = `PPLLRepair.boundedProtocol`, `integrated` =
`PPLLRepair.integratedBoundedProtocol`), ring size `n`, `ψ`, `κ` and a list of
seed configurations, it enumerates the union of the forward closures of the
seeds under `PopulationProtocol.step` on the directed ring and writes the
graph to disk for SCC analysis.

Each successor is `PopulationProtocol.step P ring C e` computed through
`P.transition` on the pair `(C e, C (e+1 mod n))`; since for `n ≥ 2` the step
changes exactly those two cells, agent states are interned and the local
transition is memoised on pairs of interned indices.  This changes only the
cost, not the successor.

Usage: `ppll-closure-census VARIANT N PSI KAPPA CAP SEEDCAP SEEDS.jsonl OUTDIR`
(one seed configuration per line in `ppll-bounded-agent-state-32.v1` JSON).
Configurations are identified up to rotation (see `canon`).
Output: `agents.jsonl` (agent index → state), `nodes.txt` (one line per class:
leader count then agent indices of the least rotation), `edges.txt` (one line
per expanded class: its id then its `n` successor classes), `unexpanded.txt`,
`seeds.txt`, `seedlog.json`, `summary.json`.
-/

set_option autoImplicit false

open Lean

namespace PPLLClosureCensus

abbrev Agent (ψ κ : Nat) := BoundedAgentState ψ κ

/-- Checked reification of a raw state into the bounded carrier: raw JSON
encoding followed by the bounded decoder, which rejects any state outside the
declared protocol domain.  Used only for the patched variants, which have no
domain-closure theorem. -/
def reify {ψ κ : Nat} (s : AgentState ψ) : Except String (Agent ψ κ) :=
  PPLLSimCodec.decodeState (psi := ψ) (kappa := κ) (PPLLSimRawCodec.encodeState s)

/-- The local transition of the chosen variant.  `bounded` / `integrated` are
exactly the `transition` field of `boundedProtocol` / `integratedBoundedProtocol`;
the names in `PPLLBirthPatch.variants` run `PPLLBirthPatch.pipeline` on the
erased states and reify the result (an out-of-domain output aborts the run). -/
def localTransition (variant : String) {ψ : Nat} (hψ : ψ > 0) (κ : Nat) :
    Except String (Agent ψ κ → Agent ψ κ → Except String (Agent ψ κ × Agent ψ κ)) :=
  match variant with
  | "bounded" => .ok fun u v => .ok ((PPLLRepair.boundedProtocol hψ κ).transition u v)
  | "integrated" => .ok fun u v =>
      .ok ((PPLLRepair.integratedBoundedProtocol hψ κ).transition u v)
  | v =>
    match PPLLBirthPatch.variants.find? (fun t => t.1 == v) with
    | some (_, consume, cmp, protect, readyGuard) => .ok fun a b => do
        let q := PPLLBirthPatch.pipeline hψ κ consume cmp protect readyGuard a.erase b.erase
        let a' ← (reify q.1).mapError fun e =>
          s!"{v}: left output out of domain ({e}) on {(PPLLSimCodec.encodeState a).compress} {(PPLLSimCodec.encodeState b).compress}"
        let b' ← (reify q.2).mapError fun e =>
          s!"{v}: right output out of domain ({e}) on {(PPLLSimCodec.encodeState a).compress} {(PPLLSimCodec.encodeState b).compress}"
        pure (a', b')
    | none =>
    match PPLLBirthPatchM2.variants.find? (fun t => t.1 == v) with
    | some (_, cmp, m) => .ok fun a b => do
        let q := PPLLBirthPatchM2.pipeline hψ κ cmp m a.erase b.erase
        let a' ← (reify q.1).mapError fun e =>
          s!"{v}: left output out of domain ({e}) on {(PPLLSimCodec.encodeState a).compress} {(PPLLSimCodec.encodeState b).compress}"
        let b' ← (reify q.2).mapError fun e =>
          s!"{v}: right output out of domain ({e}) on {(PPLLSimCodec.encodeState a).compress} {(PPLLSimCodec.encodeState b).compress}"
        pure (a', b')
    | none =>
    match PPLLElimVariants.variants.find? (fun t => t.1 == v) with
    | some (_, t) => .ok fun a b => do
        let q := PPLLElimVariants.run hψ κ t a.erase b.erase
        let a' ← (reify q.1).mapError fun e =>
          s!"{v}: left output out of domain ({e}) on {(PPLLSimCodec.encodeState a).compress} {(PPLLSimCodec.encodeState b).compress}"
        let b' ← (reify q.2).mapError fun e =>
          s!"{v}: right output out of domain ({e}) on {(PPLLSimCodec.encodeState a).compress} {(PPLLSimCodec.encodeState b).compress}"
        pure (a', b')
    | none =>
    match PPLLPostElectionGuard.variants.find? (fun t => t.1 == v) with
    | some (_, cmp, m, e, g) => .ok fun a b => do
        let q := PPLLPostElectionGuard.run hψ κ (cmp, m, e, g) a.erase b.erase
        let a' ← (reify q.1).mapError fun e =>
          s!"{v}: left output out of domain ({e}) on {(PPLLSimCodec.encodeState a).compress} {(PPLLSimCodec.encodeState b).compress}"
        let b' ← (reify q.2).mapError fun e =>
          s!"{v}: right output out of domain ({e}) on {(PPLLSimCodec.encodeState a).compress} {(PPLLSimCodec.encodeState b).compress}"
        pure (a', b')
    | none =>
    match PPLLFableDesign.variants.find? (fun t => t.1 == v) with
    | some (_, c) => .ok fun a b => do
        let q := PPLLFableDesign.run hψ κ c a.erase b.erase
        let a' ← (reify q.1).mapError fun e =>
          s!"{v}: left output out of domain ({e}) on {(PPLLSimCodec.encodeState a).compress} {(PPLLSimCodec.encodeState b).compress}"
        let b' ← (reify q.2).mapError fun e =>
          s!"{v}: right output out of domain ({e}) on {(PPLLSimCodec.encodeState a).compress} {(PPLLSimCodec.encodeState b).compress}"
        pure (a', b')
    | none => .error s!"unknown variant {v}"

structure St (ψ κ : Nat) where
  agents : Array (Agent ψ κ) := #[]
  agentIx : Std.HashMap String Nat := {}
  memo : Std.HashMap (Nat × Nat) (Nat × Nat) := {}
  nodes : Array (Array Nat) := #[]
  nodeIx : Std.HashMap (Array Nat) Nat := {}

def intern {ψ κ : Nat} (st : St ψ κ) (a : Agent ψ κ) : St ψ κ × Nat :=
  let key := (PPLLSimCodec.encodeState a).compress
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

/-- Least rotation of a configuration.  The directed-ring step commutes with
rotation (`step` at edge `e` of the rotated configuration is the rotation of
`step` at the shifted edge), so the census works on rotation classes. -/
def canon (c : Array Nat) : Array Nat := Id.run do
  let n := c.size
  let mut best := c
  for k in [1:n] do
    let r := (c.extract k n) ++ (c.extract 0 k)
    if r.toList < best.toList then best := r
  return best

/-- Incremental union census.  Seeds are processed in file order; each seed's
forward closure (on rotation classes) is expanded before the next seed starts.
A seed whose closure adds more than `seedCap` new classes is abandoned: its
remaining frontier stays unexpanded and is listed in `unexpanded.txt`, so the
analysis can mark every class that reaches it as incomplete.  The run stops
adding seeds once `cap` classes exist. -/
def run (variant : String) (n ψ κ cap seedCap : Nat) (seedPath outDir : System.FilePath) :
    IO UInt32 := do
  if hψ : ψ > 0 then
    let tr ← match localTransition variant hψ κ with
      | .ok t => pure t
      | .error e => throw (IO.userError e)
    if n < 2 then throw (IO.userError "n must be at least 2")
    let mut st : St ψ κ := {}
    let mut seedIds : Array Nat := #[]
    for line in (← IO.FS.lines seedPath) do
      if line.trimAscii.toString.isEmpty then continue
      let j ← IO.ofExcept (Json.parse line)
      let cfg ← IO.ofExcept (PPLLSimCodec.decodeConfig (n := n) (psi := ψ) (kappa := κ) j)
      let mut c : Array Nat := #[]
      for a in cfg.toArray do
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
    for h : si in [0:seedIds.size] do
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
        let mut succ : Array Nat := #[]
        for e in [0:n] do
          let i := e
          let jx := (e + 1) % n
          let key := (c[i]!, c[jx]!)
          let (a', b') ← match st.memo[key]? with
            | some r => pure r
            | none => do
              let (some u, some v) := (st.agents[c[i]!]?, st.agents[c[jx]!]?)
                | throw (IO.userError "agent index out of range")
              let q ← IO.ofExcept (tr u v)
              let (st1, ia) := intern st q.1
              let (st2, ib) := intern st1 q.2
              st := { st2 with memo := st2.memo.insert key (ia, ib) }
              pure (ia, ib)
          let (st', k, fresh) := addNode st (canon ((c.set! i a').set! jx b'))
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
      let leaders := c.foldl (fun acc i => if (st.agents[i]?.map (·.leader)).getD false then acc + 1 else acc) 0
      nodesH.putStrLn (" ".intercalate (toString leaders :: c.toList.map toString))
    nodesH.flush
    let agentsH ← IO.FS.Handle.mk (outDir / "agents.jsonl") .write
    for a in st.agents do
      agentsH.putStrLn (PPLLSimCodec.encodeState a).compress
    agentsH.flush
    IO.FS.writeFile (outDir / "seeds.txt") ("\n".intercalate (seedIds.toList.map toString) ++ "\n")
    let notExpanded := (List.range st.nodes.size).filter (fun i => !expanded[i]!)
    IO.FS.writeFile (outDir / "unexpanded.txt") ("\n".intercalate (notExpanded.map toString) ++ "\n")
    IO.FS.writeFile (outDir / "seedlog.json") ((Json.arr seedLog).compress ++ "\n")
    let summary := Json.mkObj
      [ ("variant", variant), ("n", n), ("psi", ψ), ("kappa", κ), ("cap", cap)
      , ("seed_cap", seedCap), ("quotient", "rotation classes")
      , ("classes", st.nodes.size), ("unexpanded", notExpanded.length)
      , ("agents", st.agents.size), ("pair_memo", st.memo.size), ("seeds", seedIds.size)
      , ("seeds_complete", (seedLog.filter fun j => j.getObjValD "status" == Json.str "complete").size) ]
    IO.FS.writeFile (outDir / "summary.json") (summary.compress ++ "\n")
    IO.println summary.compress
    return 0
  else throw (IO.userError "psi must be positive")

/-! ## Birth-channel probe

For a pair `(l, r)` of bounded agents, report the two leader-creation rules of
the shared pipeline prefix and the conjuncts of their guards:

* B1, `pPsi` (Leader/Wu/Protocol/Algorithm.lean:30-34): fires iff `r.label ≠ l.label + 1`
  and `r.probe`, evaluated on the transition input.
* B2, `checkSig` (Leader/Wu/Protocol/Algorithm.lean:276-288): fires iff after
  `checkSigSetReady` and `checkSigCheckL/R` the responder has label `ψ - 1` and
  state `.equal`.  Its input is `ppllSaturatedBeforeCheck` (Leader/Wu/Protocol/Repairs.lean:920),
  which both `boundedProtocol` and `integratedBoundedProtocol` apply first.

`writeSeqLeaderMove` (Leader/Wu/Protocol/Algorithm.lean:1000-1004) only moves a leader. -/

open PPLL PPLLRepair in
def probePair {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (a b : Agent ψ κ) : Json :=
  let l := BoundedAgentState.erase a
  let r := BoundedAgentState.erase b
  let nextLabel : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let b1Mismatch := decide (r.label ≠ nextLabel)
  let pre := ppllSaturatedBeforeCheck hψ κ l r
  let l1 := checkSigSetReady pre.1
  let r1 := checkSigSetReady pre.2
  let l2 := checkSigCheckL hψ l1
  let r2 := checkSigCheckR hψ l2 r1
  let b2 := decide (r2.label = ⟨ψ - 1, by omega⟩ ∧ r2.state = .equal)
  let q := (checkSig hψ pre.1 pre.2).2.leader
  Json.mkObj
    [ ("b1_label_mismatch", b1Mismatch), ("b1_r_probe", r.probe)
    , ("b1_fires", b1Mismatch && r.probe)
    , ("pre_l", PPLLSimRawCodec.encodeState pre.1)
    , ("pre_r", PPLLSimRawCodec.encodeState pre.2)
    , ("ready_l_state", PPLLSimRawCodec.encodeState l1 |>.getObjValD "state")
    , ("ready_r_state", PPLLSimRawCodec.encodeState r1 |>.getObjValD "state")
    , ("checked_l_state", PPLLSimRawCodec.encodeState l2 |>.getObjValD "state")
    , ("checked_r_state", PPLLSimRawCodec.encodeState r2 |>.getObjValD "state")
    , ("b2_fires", b2), ("checkSig_r_leader", q) ]

def probe (ψ κ : Nat) (pairs out : System.FilePath) : IO UInt32 := do
  if hψ : ψ > 0 then
    let h ← IO.FS.Handle.mk out .write
    for line in (← IO.FS.lines pairs) do
      if line.trimAscii.toString.isEmpty then continue
      let j ← IO.ofExcept (Json.parse line)
      let arr ← IO.ofExcept j.getArr?
      let a ← IO.ofExcept (PPLLSimCodec.decodeState (psi := ψ) (kappa := κ) arr[0]!)
      let b ← IO.ofExcept (PPLLSimCodec.decodeState (psi := ψ) (kappa := κ) arr[1]!)
      h.putStrLn (probePair hψ κ a b).compress
    h.flush
    return 0
  else throw (IO.userError "psi must be positive")

/-! ## Random-walk descent

Bottom SCCs are absorbing, so a long uniformly random schedule from a seed ends,
with high probability, inside a bottom SCC.  `walk` runs `steps` uniformly
random edge interactions from every seed (xorshift64 generator, fixed seed) and
writes, per seed, the final configuration and the leader-count history: the
first step with a leader, the number of steps in the last half with no leader,
and the final leader count.  The final configurations then seed an exact
closure census; a small complete closure with a leaderless bottom SCC is a
witness, a large one is not evidence of anything. -/

def xorshift (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

def walk (variant : String) (n ψ κ steps rng : Nat) (seedPath out : System.FilePath) :
    IO UInt32 := do
  if hψ : ψ > 0 then
    let tr ← match localTransition variant hψ κ with
      | .ok t => pure t
      | .error e => throw (IO.userError e)
    if n < 2 then throw (IO.userError "n must be at least 2")
    let h ← IO.FS.Handle.mk out .write
    let mut si : Nat := 0
    for line in (← IO.FS.lines seedPath) do
      if line.trimAscii.toString.isEmpty then continue
      let j ← IO.ofExcept (Json.parse line)
      let cfg ← IO.ofExcept (PPLLSimCodec.decodeConfig (n := n) (psi := ψ) (kappa := κ) j)
      -- interned walk: the local transition is memoised on agent-index pairs
      -- (per seed), exactly as in `run`; this changes only the cost.
      let mut st : St ψ κ := {}
      let mut c : Array Nat := #[]
      for a in cfg.toArray do
        let (st', i) := intern st a
        st := st'
        c := c.push i
      let mut x : UInt64 := (UInt64.ofNat (rng * 1000003 + si + 1)) ||| 1
      let mut firstLeader : Int := -1
      let mut leaderlessLate : Nat := 0
      let mut maxLate : Nat := 0
      let isLeader : St ψ κ → Nat → Bool := fun st i => (st.agents[i]?.map (·.leader)).getD false
      let count : St ψ κ → Array Nat → Nat := fun st c =>
        c.foldl (fun (a : Nat) i => if isLeader st i then a + 1 else a) 0
      if count st c > 0 then firstLeader := 0
      for t in [0:steps] do
        x := xorshift x
        let e := (x % (UInt64.ofNat n)).toNat
        let e1 := (e + 1) % n
        let key := (c[e]!, c[e1]!)
        let (ia, ib) ← match st.memo[key]? with
          | some r => pure r
          | none => do
            let (some u, some v) := (st.agents[key.1]?, st.agents[key.2]?)
              | throw (IO.userError "agent index out of range")
            let q ← IO.ofExcept (tr u v)
            let (st1, ia) := intern st q.1
            let (st2, ib) := intern st1 q.2
            st := { st2 with memo := st2.memo.insert key (ia, ib) }
            pure (ia, ib)
        c := (c.set! e ia).set! e1 ib
        let k : Nat := count st c
        if k > 0 ∧ firstLeader < 0 then firstLeader := Int.ofNat (t + 1)
        if 2 * t ≥ steps then
          if k == 0 then leaderlessLate := leaderlessLate + 1
          if k > maxLate then maxLate := k
      let cfgOut : Array (Agent ψ κ) := c.filterMap fun i => st.agents[i]?
      let fin : Json := Json.arr (cfgOut.map PPLLSimCodec.encodeState)
      h.putStrLn (Json.mkObj
        [ ("seed", toJson si), ("steps", toJson steps), ("first_leader_step", toJson firstLeader)
        , ("late_leaderless_steps", toJson leaderlessLate), ("late_max_leaders", toJson maxLate)
        , ("final_leaders", toJson (count st c)), ("final", fin) ]).compress
      h.flush
      si := si + 1
    return 0
  else throw (IO.userError "psi must be positive")

end PPLLClosureCensus

def main (args : List String) : IO UInt32 := do
  match args with
  | ["probe", ψ, κ, pairs, out] =>
    match ψ.toNat?, κ.toNat? with
    | some ψ, some κ => PPLLClosureCensus.probe ψ κ pairs out
    | _, _ => IO.eprintln "numeric arguments expected"; return 2
  | ["walk", variant, n, ψ, κ, steps, rng, seeds, out] =>
    match n.toNat?, ψ.toNat?, κ.toNat?, steps.toNat?, rng.toNat? with
    | some n, some ψ, some κ, some steps, some rng =>
      PPLLClosureCensus.walk variant n ψ κ steps rng seeds out
    | _, _, _, _, _ => IO.eprintln "numeric arguments expected"; return 2
  | [variant, n, ψ, κ, cap, seedCap, seeds, out] =>
    match n.toNat?, ψ.toNat?, κ.toNat?, cap.toNat?, seedCap.toNat? with
    | some n, some ψ, some κ, some cap, some seedCap =>
      PPLLClosureCensus.run variant n ψ κ cap seedCap seeds out
    | _, _, _, _, _ => IO.eprintln "numeric arguments expected"; return 2
  | _ => IO.eprintln "usage: ppll-closure-census VARIANT N PSI KAPPA CAP SEEDCAP SEEDS OUTDIR"; return 2
