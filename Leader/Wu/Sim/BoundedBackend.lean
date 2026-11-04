import Lean.Data.Json
import Leader.Wu.Protocol.BoundedProtocol
import Leader.Wu.Sim.BoundedCodec
import Leader.Wu.Sim.BuildInfo
import Leader.Wu.Sim.VariantCatalog

/-!
# Persistent exact-source exploration backend for repaired bounded P_PLL

This executable evaluates the repository's `PPLLRepair.boundedProtocol` directly.
It is an exploration backend, not a proof certificate.

The optional `variant` parameter selects the transition among the variants on
the bounded carrier: `bounded` (the default, `PPLLRepair.boundedProtocol`) and
`integrated` (`PPLLRepair.integratedBoundedProtocol`, which
`CorrectedFormulation.physicalProtocol` abbreviates).  When `variant` is absent
every response is exactly the one the variant-free backend produced.  The raw
`AgentState` variants of `PPLLSimVariantCatalog` are refused here with a pointer
to the process that serves them.  One process accepts a
stream of JSON requests, so a long schedule or batched graph expansion does not
compile Lean or reconnect for each transition.
-/

set_option autoImplicit false
set_option Elab.async false

open Lean PopulationProtocol

namespace PPLLSimBackend

private def exactFields (j : Json) (keys : List String) : Except String Unit := do
  let object ← j.getObj?
  for key in keys do
    if !object.contains key then throw s!"missing field: {key}"
  for key in object.keys do
    if !keys.contains key then throw s!"unexpected field: {key}"

private def field (j : Json) (key : String) : Except String Json :=
  j.getObjVal? key

private def natField (j : Json) (key : String) : Except String Nat := do
  (← field j key).getNat?

private def stringField (j : Json) (key : String) : Except String String := do
  (← field j key).getStr?

private def jsonNat (value : Nat) : Json := value
private def jsonString (value : String) : Json := value

/-- Transition variants on the bounded carrier. -/
private inductive Variant where
  | bounded
  | integrated
  deriving DecidableEq

private def variantName : Variant → String
  | .bounded => "bounded"
  | .integrated => "integrated"

/-- `n`, `psi`, `kappa` are required; `variant` is optional.  The second
component records whether `variant` was supplied, so that the variant-free
request keeps its original `describe` response. -/
private def decodeParams (j : Json) :
    Except String ((Nat × Nat × Nat) × Option Variant) := do
  let object ← j.getObj?
  for key in ["n", "psi", "kappa"] do
    if !object.contains key then throw s!"missing field: {key}"
  for key in object.keys do
    if !["n", "psi", "kappa", "variant"].contains key then
      throw s!"unexpected field: {key}"
  let base := (← natField j "n", ← natField j "psi", ← natField j "kappa")
  if !object.contains "variant" then return (base, none)
  match ← stringField j "variant" with
  | "bounded" => return (base, some .bounded)
  | "integrated" => return (base, some .integrated)
  | other => throw (PPLLSimVariantCatalog.wrongServer other)

private def finOfNat (name : String) (bound value : Nat) : Except String (Fin bound) :=
  if h : value < bound then .ok ⟨value, h⟩
  else .error s!"{name}: {value} is outside 0..{bound - 1}"

private abbrev Config (n psi kappa : Nat) :=
  PPLLSimCodec.Config n psi kappa

private def stepConfig {n psi kappa : Nat} (v : Variant) (hn : 0 < n) (hpsi : 0 < psi)
    (state : Config n psi kappa) (edge : Fin n) : Config n psi kappa :=
  let ring : DirectedRing n := ⟨hn⟩
  match v with
  | .bounded =>
      let protocol := PPLLRepair.boundedProtocol hpsi kappa
      Vector.ofFn (PopulationProtocol.step protocol ring state.get edge)
  | .integrated =>
      let protocol := PPLLRepair.integratedBoundedProtocol hpsi kappa
      Vector.ofFn (PopulationProtocol.step protocol ring state.get edge)

private def stateJson {n psi kappa : Nat} (state : Config n psi kappa) : Json :=
  PPLLSimCodec.encodeConfig state

private def stateKey {n psi kappa : Nat} (state : Config n psi kappa) : String :=
  (stateJson state).compress

private def metrics {n psi kappa : Nat} (state : Config n psi kappa) : Json :=
  let leaders := (List.range n).filter fun i =>
    if hi : i < n then (state.get ⟨i, hi⟩).leader else false
  let outputs := (List.range n).map fun i =>
    if hi : i < n then
      if (state.get ⟨i, hi⟩).leader then "leader" else "follower"
    else "unreachable"
  Json.mkObj
    [ ("leader_count", leaders.length)
    , ("exactly_one_leader", leaders.length == 1)
    , ("leader_sites", Json.arr (leaders.toArray.map jsonNat))
    , ("outputs", Json.arr (outputs.toArray.map jsonString))
    ]

private def stateDiff {n psi kappa : Nat}
    (before after : Config n psi kappa) : Json :=
  let changes := (List.range n).filterMap fun i =>
    if hi : i < n then
      let old := before.get ⟨i, hi⟩
      let new := after.get ⟨i, hi⟩
      if old = new then none else
        some <| Json.mkObj
          [ ("position", i)
          , ("before", PPLLSimCodec.encodeState old)
          , ("after", PPLLSimCodec.encodeState new)
          ]
    else none
  Json.arr changes.toArray

private def stateRecord {n psi kappa : Nat} (v : Variant) (hn : 0 < n) (hpsi : 0 < psi)
    (before : Config n psi kappa) (edge : Fin n) : Config n psi kappa × Json :=
  let after := stepConfig v hn hpsi before edge
  (after, Json.mkObj
    [ ("action", edge.val)
    , ("edge", edge.val)
    , ("state", stateJson after)
    , ("state_key", stateKey after)
    , ("metrics", metrics after)
    , ("diff", stateDiff before after)
    ])

private def decodeWord {n : Nat} (j : Json) : Except String (Array (Fin n)) := do
  let input ← j.getArr?
  let mut result := Array.mkEmpty input.size
  for h : i in *...input.size do
    let value ← input[i].getNat?
    result := result.push (← finOfNat s!"word[{i}]" n value)
  return result

private def bindings : Json := Json.mkObj
  [ ("source_manifest_sha256", PPLLSimBuildInfo.sourceDigest)
  , ("lean_version", PPLLSimBuildInfo.leanVersion)
  , ("protocol_entrypoint", "Leader/Wu/Protocol/BoundedProtocol.lean:PPLLRepair.boundedProtocol")
  , ("transition_entrypoint", "Leader/Wu/Protocol/Repairs.lean:PPLLRepair.ppllSaturatedNoCollision")
  ]

private def describeDefault (n psi kappa : Nat) : Json :=
  Json.mkObj
    [ ("ok", true)
    , ("provider_id", "ppll.repaired.bounded.v1")
    , ("protocol_id", "PPLLRepair.boundedProtocol")
    , ("state_codec", "ppll-bounded-agent-state-32.v1")
    , ("transport", "persistent-jsonl")
    , ("parameters", Json.mkObj [("n", n), ("psi", psi), ("kappa", kappa)])
    , ("source_bindings", bindings)
    , ("action_space", Json.arr ((List.range n).toArray.map jsonNat))
    , ("successor_contract", "expand returns each action in action_space exactly once")
    , ("metrics", Json.arr #["leader_count", "exactly_one_leader", "leader_sites", "outputs"])
    , ("evidence_kind", "exact-source executable exploration")
    ]

/-- `describe` for an explicitly named variant: the variant's own identity and
source bindings, plus the whole variant catalogue. -/
private def describeVariant (v : Variant) (n psi kappa : Nat) : Json :=
  match PPLLSimVariantCatalog.find? (variantName v) with
  | none => Json.mkObj [("ok", false), ("error", "variant missing from catalogue")]
  | some e =>
    Json.mkObj
      [ ("ok", true)
      , ("provider_id", e.providerId)
      , ("protocol_id", e.protocolId)
      , ("variant", e.name)
      , ("variants", PPLLSimVariantCatalog.catalogueJson)
      , ("state_codec", e.stateCodec)
      , ("transport", "persistent-jsonl")
      , ("parameters", Json.mkObj
          [("n", n), ("psi", psi), ("kappa", kappa), ("variant", e.name)])
      , ("source_bindings", Json.mkObj
          [ ("source_manifest_sha256", PPLLSimBuildInfo.sourceDigest)
          , ("lean_version", PPLLSimBuildInfo.leanVersion)
          , ("protocol_entrypoint", e.protocolEntrypoint)
          , ("transition_entrypoint", e.transitionEntrypoint) ])
      , ("action_space", Json.arr ((List.range n).toArray.map jsonNat))
      , ("successor_contract", "expand returns each action in action_space exactly once")
      , ("metrics", Json.arr #["leader_count", "exactly_one_leader", "leader_sites", "outputs"])
      , ("evidence_kind", "exact-source executable exploration")
      ]

private def describe (v : Option Variant) (n psi kappa : Nat) : Json :=
  match v with
  | none => describeDefault n psi kappa
  | some v => describeVariant v n psi kappa

private def validateTyped {n psi kappa : Nat} (state : Config n psi kappa) : Json :=
  Json.mkObj
    [ ("ok", true), ("state", stateJson state), ("state_key", stateKey state)
    , ("metrics", metrics state) ]

private def runTyped {n psi kappa : Nat} (v : Variant) (hn : 0 < n) (hpsi : 0 < psi)
    (initial : Config n psi kappa) (word : Array (Fin n)) : Json := Id.run do
  let mut current := initial
  let mut steps := #[]
  for edge in word do
    let record := stateRecord v hn hpsi current edge
    current := record.1
    steps := steps.push record.2
  return Json.mkObj
    [ ("ok", true), ("initial", stateJson initial), ("initial_key", stateKey initial)
    , ("initial_metrics", metrics initial), ("steps", Json.arr steps)
    , ("final", stateJson current), ("final_key", stateKey current)
    , ("final_metrics", metrics current) ]

private def expandTyped {n psi kappa : Nat} (v : Variant) (hn : 0 < n) (hpsi : 0 < psi)
    (states : Array Json) : Except String Json := do
  let mut items := Array.mkEmpty states.size
  for h : i in *...states.size do
    let state ← PPLLSimCodec.decodeConfig (n:=n) (psi:=psi) (kappa:=kappa) states[i]
    let successors := (Array.ofFn fun edge : Fin n =>
      (stateRecord v hn hpsi state edge).2)
    items := items.push <| Json.mkObj
      [ ("state_key", stateKey state), ("metrics", metrics state)
      , ("successors", Json.arr successors) ]
  return Json.mkObj [("ok", true), ("items", Json.arr items)]

private def dispatchTyped {n psi kappa : Nat} (named : Option Variant)
    (hn : 0 < n) (hpsi : 0 < psi)
    (operation : String) (request : Json) : Except String Json := do
  let v := named.getD .bounded
  match operation with
  | "describe" =>
      exactFields request ["op", "params"]
      return describe named n psi kappa
  | "validate" =>
      exactFields request ["op", "params", "state"]
      let state ← PPLLSimCodec.decodeConfig (n:=n) (psi:=psi) (kappa:=kappa)
        (← field request "state")
      return validateTyped state
  | "run" =>
      exactFields request ["op", "params", "state", "word", "include_states"]
      let includeStates ← (← field request "include_states").getBool?
      if !includeStates then throw "run requires include_states=true"
      let state ← PPLLSimCodec.decodeConfig (n:=n) (psi:=psi) (kappa:=kappa)
        (← field request "state")
      let word ← decodeWord (n:=n) (← field request "word")
      return runTyped v hn hpsi state word
  | "expand" =>
      exactFields request ["op", "params", "states"]
      let states ← (← field request "states").getArr?
      expandTyped (kappa:=kappa) v hn hpsi states
  | _ => throw s!"unsupported operation: {operation}"

private def dispatch (request : Json) : Except String Json := do
  let operation ← stringField request "op"
  let params ← field request "params"
  let ((n, psi, kappa), named) ← decodeParams params
  if hn : 0 < n then
    if hpsi : 0 < psi then dispatchTyped (kappa:=kappa) named hn hpsi operation request
    else throw "psi must be positive"
  else throw "n must be positive"

private def errorJson (message : String) : Json :=
  Json.mkObj [("ok", false), ("error", message)]

private def handleLine (line : String) : Json :=
  match Json.parse line with
  | .error message => errorJson ("invalid JSON: " ++ message)
  | .ok request =>
      match dispatch request with
      | .ok response => response
      | .error message => errorJson message

partial def serve (input : IO.FS.Stream) (output : IO.FS.Stream) : IO Unit := do
  let line ← input.getLine
  if line.isEmpty then return
  output.putStrLn (handleLine line.trimAscii.toString).compress
  output.flush
  serve input output

end PPLLSimBackend

def main : IO Unit := do
  PPLLSimBackend.serve (← IO.getStdin) (← IO.getStdout)
