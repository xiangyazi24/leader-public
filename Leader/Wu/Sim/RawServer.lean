import Lean.Data.Json
import Leader.Core.Basic
import Leader.Wu.Sim.RawCodec
import Leader.Wu.Sim.VariantCatalog
import Leader.Wu.Sim.BuildInfo

/-!
# Persistent JSONL server for P_PLL variants on the raw carrier `AgentState ψ`

Same wire protocol as `Leader/Wu/Sim/BoundedBackend.lean` (`describe`, `validate`,
`run`, `expand`), for the kernel-experiment variants whose population protocol
has local state `AgentState ψ`.  A driver module imports the modules that
define those variants and passes a table of transition functions to `serve`.

Each variant's transition is referenced by its exact Lean name and applied
through `PopulationProtocol.step` on the directed ring, so a run is the same
computation as the kernel's `protocol.step ring C e`.  For `ψ = 2`, `κ = 2`
the protocol built here is definitionally the named one (e.g.
`ZZRepairAll8.protocolAll8`); other `ψ`, `κ` use the same transition function
at other parameters.  This is exploration evidence, not a proof certificate.
-/

set_option autoImplicit false

open Lean PopulationProtocol

namespace PPLLSimRawServer

/-- A variant served by a raw backend: its catalogue row and its transition. -/
structure RawVariant where
  entry : PPLLSimVariantCatalog.Entry
  transition : {ψ : Nat} → ψ > 0 → Nat → AgentState ψ → AgentState ψ →
    AgentState ψ × AgentState ψ

/-- The population protocol of a raw variant at parameters `ψ`, `κ`; the same
record shape as `ZZRepairAll8.protocolAll8` and its siblings. -/
def rawProtocol (v : RawVariant) {ψ : Nat} (hψ : ψ > 0) (κ : Nat) :
    PopulationProtocol where
  Q := AgentState ψ
  Y := LeaderOutput
  transition := v.transition hψ κ
  output := AgentState.outputFn

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

private def finOfNat (name : String) (bound value : Nat) : Except String (Fin bound) :=
  if h : value < bound then .ok ⟨value, h⟩
  else .error s!"{name}: {value} is outside 0..{bound - 1}"

private abbrev Config (n psi : Nat) := PPLLSimRawCodec.Config n psi

private def stepConfig (v : RawVariant) {n psi : Nat} (kappa : Nat)
    (hn : 0 < n) (hpsi : 0 < psi) (state : Config n psi) (edge : Fin n) :
    Config n psi :=
  let ring : DirectedRing n := ⟨hn⟩
  Vector.ofFn (PopulationProtocol.step (rawProtocol v hpsi kappa) ring state.get edge)

private def stateJson {n psi : Nat} (state : Config n psi) : Json :=
  PPLLSimRawCodec.encodeConfig state

private def stateKey {n psi : Nat} (state : Config n psi) : String :=
  (stateJson state).compress

private def metrics {n psi : Nat} (kappa : Nat) (state : Config n psi) : Json :=
  let leaders := (List.range n).filter fun i =>
    if hi : i < n then (state.get ⟨i, hi⟩).leader else false
  let outputs := (List.range n).map fun i =>
    if hi : i < n then
      if (state.get ⟨i, hi⟩).leader then "leader" else "follower"
    else "unreachable"
  let inDomain := (List.range n).all fun i =>
    if hi : i < n then PPLLSimRawCodec.inProtocolDomainB kappa (state.get ⟨i, hi⟩)
    else true
  Json.mkObj
    [ ("leader_count", leaders.length)
    , ("exactly_one_leader", leaders.length == 1)
    , ("leader_sites", Json.arr (leaders.toArray.map jsonNat))
    , ("outputs", Json.arr (outputs.toArray.map jsonString))
    , ("in_protocol_domain", inDomain)
    ]

private def stateDiff {n psi : Nat} (before after : Config n psi) : Json :=
  let changes := (List.range n).filterMap fun i =>
    if hi : i < n then
      let old := before.get ⟨i, hi⟩
      let new := after.get ⟨i, hi⟩
      if old = new then none else
        some <| Json.mkObj
          [ ("position", i)
          , ("before", PPLLSimRawCodec.encodeState old)
          , ("after", PPLLSimRawCodec.encodeState new)
          ]
    else none
  Json.arr changes.toArray

private def stateRecord (v : RawVariant) {n psi : Nat} (kappa : Nat)
    (hn : 0 < n) (hpsi : 0 < psi) (before : Config n psi) (edge : Fin n) :
    Config n psi × Json :=
  let after := stepConfig v kappa hn hpsi before edge
  (after, Json.mkObj
    [ ("action", edge.val)
    , ("edge", edge.val)
    , ("state", stateJson after)
    , ("state_key", stateKey after)
    , ("metrics", metrics kappa after)
    , ("diff", stateDiff before after)
    ])

private def decodeWord {n : Nat} (j : Json) : Except String (Array (Fin n)) := do
  let input ← j.getArr?
  let mut result := Array.mkEmpty input.size
  for h : i in *...input.size do
    let value ← input[i].getNat?
    result := result.push (← finOfNat s!"word[{i}]" n value)
  return result

private def describe (v : RawVariant) (n psi kappa : Nat) : Json :=
  let e := v.entry
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
    , ("metrics", Json.arr
        #["leader_count", "exactly_one_leader", "leader_sites", "outputs",
          "in_protocol_domain"])
    , ("evidence_kind", "exact-source interpreted exploration")
    ]

private def dispatchTyped (v : RawVariant) {n psi : Nat} (kappa : Nat)
    (hn : 0 < n) (hpsi : 0 < psi) (operation : String) (request : Json) :
    Except String Json := do
  match operation with
  | "describe" =>
      exactFields request ["op", "params"]
      return describe v n psi kappa
  | "validate" =>
      exactFields request ["op", "params", "state"]
      let state ← PPLLSimRawCodec.decodeConfig (n:=n) (psi:=psi) (← field request "state")
      return Json.mkObj
        [ ("ok", true), ("state", stateJson state), ("state_key", stateKey state)
        , ("metrics", metrics kappa state) ]
  | "run" =>
      exactFields request ["op", "params", "state", "word", "include_states"]
      let includeStates ← (← field request "include_states").getBool?
      if !includeStates then throw "run requires include_states=true"
      let initial ← PPLLSimRawCodec.decodeConfig (n:=n) (psi:=psi) (← field request "state")
      let word ← decodeWord (n:=n) (← field request "word")
      let mut current := initial
      let mut steps := #[]
      for edge in word do
        let record := stateRecord v kappa hn hpsi current edge
        current := record.1
        steps := steps.push record.2
      return Json.mkObj
        [ ("ok", true), ("initial", stateJson initial), ("initial_key", stateKey initial)
        , ("initial_metrics", metrics kappa initial), ("steps", Json.arr steps)
        , ("final", stateJson current), ("final_key", stateKey current)
        , ("final_metrics", metrics kappa current) ]
  | "expand" =>
      exactFields request ["op", "params", "states"]
      let states ← (← field request "states").getArr?
      let mut items := Array.mkEmpty states.size
      for h : i in *...states.size do
        let state ← PPLLSimRawCodec.decodeConfig (n:=n) (psi:=psi) states[i]
        let successors := (Array.ofFn fun edge : Fin n =>
          (stateRecord v kappa hn hpsi state edge).2)
        items := items.push <| Json.mkObj
          [ ("state_key", stateKey state), ("metrics", metrics kappa state)
          , ("successors", Json.arr successors) ]
      return Json.mkObj [("ok", true), ("items", Json.arr items)]
  | _ => throw s!"unsupported operation: {operation}"

/-- Raw backends require an explicit `variant`: there is no default on this
carrier, so a variant-free request cannot silently run a different protocol. -/
private def dispatch (table : List RawVariant) (request : Json) : Except String Json := do
  let operation ← stringField request "op"
  let params ← field request "params"
  exactFields params ["n", "psi", "kappa", "variant"]
  let n ← natField params "n"
  let psi ← natField params "psi"
  let kappa ← natField params "kappa"
  let name ← stringField params "variant"
  match table.find? (·.entry.name == name) with
  | none => throw (PPLLSimVariantCatalog.wrongServer name)
  | some v =>
      if hn : 0 < n then
        if hpsi : 0 < psi then dispatchTyped v kappa hn hpsi operation request
        else throw "psi must be positive"
      else throw "n must be positive"

private def errorJson (message : String) : Json :=
  Json.mkObj [("ok", false), ("error", message)]

private def handleLine (table : List RawVariant) (line : String) : Json :=
  match Json.parse line with
  | .error message => errorJson ("invalid JSON: " ++ message)
  | .ok request =>
      match dispatch table request with
      | .ok response => response
      | .error message => errorJson message

partial def serve (table : List RawVariant) (input : IO.FS.Stream)
    (output : IO.FS.Stream) : IO Unit := do
  let line ← input.getLine
  if line.isEmpty then return
  output.putStrLn (handleLine table line.trimAscii.toString).compress
  output.flush
  serve table input output

/-- Catalogue row by name; drivers use it so their table cannot drift from the
catalogue. -/
def entry! (name : String) : PPLLSimVariantCatalog.Entry :=
  match PPLLSimVariantCatalog.find? name with
  | some e => e
  | none =>
    { name, providerId := "missing", protocolId := "missing"
      protocolEntrypoint := "missing", transitionEntrypoint := "missing"
      carrier := "missing", stateCodec := "missing", server := .raw
      note := "missing from catalogue" }

end PPLLSimRawServer
