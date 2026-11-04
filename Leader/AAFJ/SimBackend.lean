import Lean.Data.Json
import Init.Data.Vector.OfFn
import Leader.AAFJ.Protocol
import Leader.AAFJ.Centered.Protocol
import Leader.AAFJ.OneBarrier.Sanitation
import Leader.AAFJ.SimBuildInfo

set_option autoImplicit false
set_option Elab.async false

open Lean PopulationProtocol

namespace AAFJSimBackend

private def exactFields (j : Json) (keys : List String) : Except String Unit := do
  let o ← j.getObj?
  for k in keys do if !o.contains k then throw s!"missing field: {k}"
  for k in o.keys do if !keys.contains k then throw s!"unexpected field: {k}"

private def field (j : Json) (k : String) := j.getObjVal? k
private def natField (j : Json) (k : String) : Except String Nat := do (← field j k).getNat?
private def strField (j : Json) (k : String) : Except String String := do (← field j k).getStr?
private def jNat (n : Nat) : Json := n
private def jStr (s : String) : Json := s

private def optBoolField (j : Json) (k : String) : Except String Bool := do
  let o ← j.getObj?
  if o.contains k then (← field j k).getBool? else pure false

private def decodeAAFJState {k : Nat} (j : Json) : Except String (AAFJPK.State k) := do
  exactFields j ["bullet", "leader", "label", "probe", "phase"]
  let label ← natField j "label"
  if h : label < k then
    let bullet ← (← field j "bullet").getBool?
    let leader ← (← field j "leader").getBool?
    let probe ← (← field j "probe").getBool?
    let phase ← (← field j "phase").getBool?
    return AAFJPK.State.mk bullet leader ⟨label, h⟩ probe phase
  else throw s!"label {label} is outside 0..{k - 1}"

private def encodeAAFJState {k : Nat} (q : AAFJPK.State k) : Json :=
  Json.mkObj [("bullet", q.bullet), ("leader", q.leader), ("label", q.label.val),
    ("probe", q.probe), ("phase", q.phase)]

private def decodeOne (j : Json) : Except String AAFJSmallRings.OneState := do
  exactFields j ["leader"]
  if ← (← field j "leader").getBool? then return .leader
  else throw "the one-agent branch has only leader=true"
private def encodeOne (_ : AAFJSmallRings.OneState) : Json := Json.mkObj [("leader", true)]

private def decodeTwo (j : Json) : Except String Bool := do
  exactFields j ["leader"]
  (← field j "leader").getBool?
private def encodeTwo (q : Bool) : Json := Json.mkObj [("leader", q)]

private def decodeConfig {Q : Type} {n : Nat} (decode : Json → Except String Q)
    (j : Json) : Except String (Vector Q n) := do
  let a ← j.getArr?
  if h : a.size = n then
    let v : Vector Json n := ⟨a, h⟩
    Vector.ofFnM fun i => match decode (v.get i) with
      | .ok q => .ok q | .error e => .error s!"states[{i.val}]: {e}"
  else throw s!"states length {a.size} does not equal n={n}"

private def encodeConfig {Q : Type} {n : Nat} (encode : Q → Json)
    (c : Vector Q n) : Json := Json.arr (c.toArray.map encode)

private def key {Q : Type} {n : Nat} (encode : Q → Json) (c : Vector Q n) : String :=
  (encodeConfig encode c).compress

private def metrics {Q : Type} {n : Nat} (leader : Q → Bool)
    (extra : Vector Q n → List (String × Json)) (c : Vector Q n) : Json :=
  let sites := (List.range n).filter fun i => if h : i < n then leader (c.get ⟨i,h⟩) else false
  Json.mkObj (([("leader_count", (sites.length : Json)),
    ("exactly_one_leader", (sites.length == 1 : Bool)),
    ("leader_sites", Json.arr (sites.toArray.map jNat))] : List (String × Json)) ++ extra c)

private def barrierSites {n k : Nat} (hn : 0 < n) (hk : 0 < k)
    (c : Vector (AAFJPK.State k) n) : List Nat :=
  let ring : DirectedRing n := ⟨hn⟩
  (List.range n).filter fun i =>
    if hi : i < n then
      decide (AAFJPK.IsBarrier hk (c.get ⟨i, hi⟩)
        (c.get (ring.rightNeighbor ⟨i, hi⟩)))
    else false

private def barrierMetrics {n k : Nat} (hn : 0 < n) (hk : 0 < k)
    (c : Vector (AAFJPK.State k) n) : List (String × Json) :=
  let sites := barrierSites hn hk c
  [("barrier_count", (sites.length : Json)),
   ("one_barrier", (sites.length == 1 : Bool)),
   ("barrier_sites", Json.arr (sites.toArray.map jNat))]

private def hasOneBarrier {n k : Nat} (hn : 0 < n) (hk : 0 < k)
    (c : Vector (AAFJPK.State k) n) : Bool :=
  (barrierSites hn hk c).length == 1

/-- Literal physical Clean, searched as the definition says:
    exists leader, exists barrier, CleanAt barrier leader. -/
private def cleanMetric {n k : Nat} (hn : 0 < n) (hk : 0 < k)
    (c : Vector (AAFJPK.State k) n) : Bool :=
  let ring : DirectedRing n := ⟨hn⟩
  (List.range n).any fun leader =>
    if hl : leader < n then
      (List.range n).any fun barrier =>
        if hb : barrier < n then
          decide (AAFJPK.SingleBarrierSanitation.CleanAt
            hk ring c.get ⟨barrier, hb⟩ ⟨leader, hl⟩)
        else false
    else false

/-- The three added token counts are one pass over the state. -/
private def stateMetrics {n k : Nat} (hn : 0 < n) (hk : 0 < k)
    (c : Vector (AAFJPK.State k) n) : List (String × Json) := Id.run do
  let mut bullets : Nat := 0
  let mut probes : Nat := 0
  let mut marked : Nat := 0
  for i in [0:n] do
    if h : i < n then
      let q := c.get ⟨i, h⟩
      if q.bullet then bullets := bullets + 1
      if q.probe then probes := probes + 1
      if decide (AAFJPK.SingleBarrierSanitation.Marked q) then
        marked := marked + 1
  return [("bullet_count", (bullets : Json)),
    ("probe_count", (probes : Json)),
    ("marked_count", (marked : Json)),
    ("clean", (cleanMetric hn hk c : Json))]

private def fullAAFJMetrics {n k : Nat} (hn : 0 < n) (hk : 0 < k)
    (c : Vector (AAFJPK.State k) n) : List (String × Json) :=
  barrierMetrics hn hk c ++ stateMetrics hn hk c

/-! SplitMix64 finalizer, evaluated in Nat and masked after every 64-bit stage.
    The counter gives each sampled field its own deterministic PRNG word. -/
private def u64Mask : Nat := 18446744073709551615

private def splitmix64 (seed counter : Nat) : Nat :=
  let z0 := (seed + 11400714819323198485 * (counter + 1)) &&& u64Mask
  let z1 := ((z0 ^^^ (z0 >>> 30)) * 13787848793156543929) &&& u64Mask
  let z2 := ((z1 ^^^ (z1 >>> 27)) * 10723151780598845931) &&& u64Mask
  (z2 ^^^ (z2 >>> 31)) &&& u64Mask

private def sampledBool (seed counter : Nat) : Bool :=
  splitmix64 seed counter % 2 == 1

private def sampleOneConfig (_seed _sampleIndex : Nat) :
    Vector AAFJSmallRings.OneState 1 :=
  Vector.ofFn fun _ => AAFJSmallRings.OneState.leader

private def sampleTwoConfig (seed sampleIndex : Nat) : Vector Bool 2 :=
  Vector.ofFn fun i =>
    sampledBool seed (2 * sampleIndex + i.val)

private def sampleAAFJConfig {n k : Nat} (hk : 0 < k)
    (seed sampleIndex : Nat) : Vector (AAFJPK.State k) n :=
  Vector.ofFn fun i =>
    let base := 5 * (sampleIndex * n + i.val)
    AAFJPK.State.mk
      (sampledBool seed base)
      (sampledBool seed (base + 1))
      ⟨splitmix64 seed (base + 2) % k, Nat.mod_lt _ hk⟩
      (sampledBool seed (base + 3))
      (sampledBool seed (base + 4))

private def stepConfig {Q : Type} {n : Nat} (hn : 0 < n)
    (transition : Q → Q → Q × Q) (c : Vector Q n) (e : Fin n) : Vector Q n :=
  let ring : DirectedRing n := ⟨hn⟩
  let P : PopulationProtocol := PopulationProtocol.mk Q Bool transition (fun _ => false)
  Vector.ofFn (PopulationProtocol.step P ring c.get e)

private def diff {Q : Type} [DecidableEq Q] {n : Nat} (encode : Q → Json)
    (a b : Vector Q n) : Json :=
  Json.arr <| ((List.range n).filterMap fun i => if h : i < n then
    let x := a.get ⟨i,h⟩; let y := b.get ⟨i,h⟩
    if x = y then none else some (Json.mkObj [("position",i),("before",encode x),("after",encode y)])
  else none).toArray

private def record {Q : Type} [DecidableEq Q] {n : Nat} (hn : 0 < n)
    (transition : Q → Q → Q × Q) (encode : Q → Json) (leader : Q → Bool)
    (extra : Vector Q n → List (String × Json))
    (before : Vector Q n) (e : Fin n) : Vector Q n × Json :=
  let after := stepConfig hn transition before e
  (after, Json.mkObj [("action",e.val),("edge",e.val),("state",encodeConfig encode after),
    ("state_key",key encode after),("metrics",metrics leader extra after),("diff",diff encode before after)])

private def finAction {n : Nat} (j : Json) : Except String (Fin n) := do
  let x ← j.getNat?
  if h : x < n then return ⟨x,h⟩ else throw s!"action {x} outside 0..{n-1}"

private def bindings : Json := Json.mkObj
  [("source_manifest_sha256",AAFJSimBuildInfo.sourceDigest),("lean_version",AAFJSimBuildInfo.leanVersion),
   ("exact_family_entrypoint","Leader/AAFJ/Protocol.lean:AAFJExactFamily.protocolFor"),
   ("centered_entrypoint","Leader/AAFJ/Centered/Protocol.lean:AAFJPK.CenteredRenewal.protocol")]

private def describe (provider protocol codec : String) (n : Nat)
    (metricNames : List String) (extra : List (String × Json)) : Json :=
  Json.mkObj (([ ("ok",(true : Json)),("provider_id",(provider : Json)),
    ("protocol_id",(protocol : Json)),("state_codec",(codec : Json)),
    ("transport",("persistent-jsonl" : Json)),("source_bindings",bindings),
    ("action_space",Json.arr ((List.range n).toArray.map jNat)),
    ("metrics",Json.arr ((["leader_count","exactly_one_leader","leader_sites"] ++
      metricNames).toArray.map jStr)),
    ("evidence_kind",("exact-source executable exploration" : Json)) ] : List (String × Json)) ++ extra)

private def operate {Q : Type} [DecidableEq Q] {n : Nat} (hn : 0 < n)
    (transition : Q → Q → Q × Q)
    (decode : Json → Except String Q) (encode : Q → Json) (leader : Q → Bool)
    (extraMetrics : Vector Q n → List (String × Json))
    (extraMetricNames : List String)
    (sampleConfig : Nat → Nat → Vector Q n)
    (oneBarrierSample : Option (Vector Q n → Bool))
    (provider protocol codec operation : String) (request : Json)
    (extra : List (String × Json)) : Except String Json := do
  match operation with
  | "describe" =>
    exactFields request ["op","params"]
    return describe provider protocol codec n extraMetricNames extra
  | "validate" =>
    exactFields request ["op","params","state"]
    let c ← decodeConfig (n:=n) decode (← field request "state")
    return Json.mkObj [("ok",true),("state",encodeConfig encode c),("state_key",key encode c),("metrics",metrics leader extraMetrics c)]
  | "run" =>
    exactFields request ["op","params","state","word","include_states"]
    if !(← (← field request "include_states").getBool?) then throw "run requires include_states=true"
    let initial ← decodeConfig (n:=n) decode (← field request "state")
    let words ← (← field request "word").getArr?
    let mut current := initial
    let mut steps := #[]
    for h : i in *...words.size do
      let e ← finAction words[i]
      let r := record hn transition encode leader extraMetrics current e
      current := r.1; steps := steps.push r.2
    return Json.mkObj [("ok",true),("initial",encodeConfig encode initial),("initial_key",key encode initial),
      ("initial_metrics",metrics leader extraMetrics initial),("steps",Json.arr steps),("final",encodeConfig encode current),
      ("final_key",key encode current),("final_metrics",metrics leader extraMetrics current)]
  | "expand" =>
    exactFields request ["op","params","states"]
    let inputs ← (← field request "states").getArr?
    let mut items := #[]
    for h : i in *...inputs.size do
      let c ← decodeConfig (n:=n) decode inputs[i]
      let successors := Array.ofFn fun e : Fin n => (record hn transition encode leader extraMetrics c e).2
      items := items.push (Json.mkObj [("state_key",key encode c),("metrics",metrics leader extraMetrics c),
        ("successors",Json.arr successors)])
    return Json.mkObj [("ok",true),("items",Json.arr items)]
  | "sample" =>
    let o ← request.getObj?
    let hasOneBarrierField := o.contains "one_barrier"
    if hasOneBarrierField then
      exactFields request ["op","params","seed","count","one_barrier"]
    else
      exactFields request ["op","params","seed","count"]
    let seed ← natField request "seed"
    let count ← natField request "count"
    let oneBarrierOnly ← optBoolField request "one_barrier"
    if oneBarrierOnly then
      match oneBarrierSample with
      | none => throw "one_barrier sampling is unavailable for this provider"
      | some _ => pure ()
    let accept : Vector Q n → Bool :=
      if oneBarrierOnly then
        match oneBarrierSample with
        | some p => p
        | none => fun _ => false
      else
        fun _ => true
    let cap := if oneBarrierOnly then 10000 * count else count
    let mut attempts := 0
    let mut states : Array Json := #[]
    while states.size < count && attempts < cap do
      let c := sampleConfig seed attempts
      if accept c then states := states.push (encodeConfig encode c)
      attempts := attempts + 1
    if states.size = count then
      return Json.mkObj [("ok",true),("states",Json.arr states)]
    else
      throw s!"one_barrier rejection limit exceeded after {cap} attempts"
  | _ => throw s!"unsupported operation: {operation}"

private def dispatch (request : Json) : Except String Json := do
  let operation ← strField request "op"
  let params ← field request "params"
  let variant ← strField params "variant"
  let n ← natField params "n"
  if hn : 0 < n then
    match variant with
    | "original-journal-pk" =>
      exactFields params ["variant","n"]
      if h1 : n = 1 then
        match n, h1 with
        | 1, rfl =>
          operate (Q:=AAFJSmallRings.OneState) (n:=1) (by decide)
            (fun _ _ => (AAFJSmallRings.OneState.leader, AAFJSmallRings.OneState.leader))
            decodeOne encodeOne (fun _ => true) (fun _ => []) []
            sampleOneConfig none
            "aafj.exact-family.one.v1"
            "AAFJSmallRings.oneProtocol" "aafj-one-state.v1" operation request []
      else if h2 : n = 2 then
        match n, h2 with
        | 2, rfl =>
          operate (Q:=Bool) (n:=2) (by decide) AAFJSmallRings.twoTransition
            decodeTwo encodeTwo id (fun _ => []) []
            sampleTwoConfig none
            "aafj.exact-family.two.v1"
            "AAFJSmallRings.twoProtocol" "aafj-two-bool.v1" operation request []
      else
        let k := AAFJExactN.leastNonDivisor n
        have hk : 0 < k := by have := AAFJExactN.leastNonDivisor_ge_two hn; omega
        operate hn (AAFJPK.transition hk) decodeAAFJState encodeAAFJState
          (fun q => q.leader) (fullAAFJMetrics hn hk)
          ["barrier_count","one_barrier","barrier_sites",
           "bullet_count","probe_count","marked_count","clean"]
          (sampleAAFJConfig hk) (some (hasOneBarrier hn hk))
          "aafj.exact-family.journal-pk.v1" "AAFJPK.protocol"
          "aafj-five-field.v1" operation request [("k",k),("selector","leastNonDivisor(n)")]
    | "centered-renewal" =>
      exactFields params ["variant","n","k"]
      let k ← natField params "k"
      if hk : 0 < k then
        if hlarge : 3 ≤ n then
          if hndvd : ¬ k ∣ n then
            operate hn (AAFJPK.CenteredRenewal.transition hk) decodeAAFJState encodeAAFJState
              (fun q => q.leader) (fullAAFJMetrics hn hk)
              ["barrier_count","one_barrier","barrier_sites",
               "bullet_count","probe_count","marked_count","clean"]
              (sampleAAFJConfig hk) (some (hasOneBarrier hn hk))
              "aafj.centered-renewal.v1" "AAFJPK.CenteredRenewal.protocol"
              "aafj-five-field.v1" operation request [("k",k),("semantic_scope","n>=3, k>0, k does not divide n")]
          else throw "centered-renewal requires k not dividing n"
        else throw "centered-renewal requires n >= 3; it has no unified small-ring selector"
      else throw "centered-renewal requires k > 0"
    | _ => throw s!"unsupported variant: {variant}"
  else throw "n must be positive"

private def handleLine (line : String) : Json := match Json.parse line with
  | .error e => Json.mkObj [("ok",false),("error","invalid JSON: " ++ e)]
  | .ok j => match dispatch j with | .ok r => r | .error e => Json.mkObj [("ok",false),("error",e)]

partial def serve (input : IO.FS.Stream) (output : IO.FS.Stream) : IO Unit := do
  let line ← input.getLine
  if line.isEmpty then return
  output.putStrLn (handleLine line.trimAscii.toString).compress
  output.flush
  serve input output

end AAFJSimBackend

def main : IO Unit := do
  AAFJSimBackend.serve (← IO.getStdin) (← IO.getStdout)
