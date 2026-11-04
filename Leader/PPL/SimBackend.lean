import Lean.Data.Json
import Init.Data.Vector.OfFn
import Leader.PPL.Transition
import Leader.PPL.SimPredicates

/-!
# Persistent JSONL simulator backend for literal P_PL

The wire state is scripts/ppl_reference.py codec ppl-alg1-13-field.v1.
All protocol evolution goes through PopulationProtocol.step on PPL.protocol;
this file contains no duplicate transition semantics.
-/

set_option autoImplicit false
set_option Elab.async false

open Lean PopulationProtocol

namespace PPLSimBackend

instance validOffsetDecidable (psi : Nat) (z : Int) : Decidable (PPL.ValidOffset psi z) := by
  unfold PPL.ValidOffset; infer_instance

private abbrev Config (n psi kappa : Nat) :=
  Vector (PPL.State psi kappa) n

private def exactFields (j : Json) (keys : List String) : Except String Unit := do
  let object ← j.getObj?
  for key in keys do
    if !object.contains key then
      throw s!"missing field: {key}"
  for key in object.keys do
    if !keys.contains key then
      throw s!"unexpected field: {key}"

private def field (j : Json) (key : String) : Except String Json :=
  j.getObjVal? key

private def natField (j : Json) (key : String) : Except String Nat := do
  (← field j key).getNat?

private def stringField (j : Json) (key : String) : Except String String := do
  (← field j key).getStr?

private def jsonNat (value : Nat) : Json := value
private def jsonInt (value : Int) : Json := value
private def jsonString (value : String) : Json := value

private def bitJson (value : Bool) : Json :=
  if value then jsonNat 1 else jsonNat 0

private def bitField (j : Json) (key : String) : Except String Bool := do
  let value ← natField j key
  match value with
  | 0 => return false
  | 1 => return true
  | _ => throw s!"{key} must be 0 or 1"

private def finOfNat (name : String) (bound value : Nat) :
    Except String (Fin bound) :=
  if h : value < bound then
    .ok ⟨value, h⟩
  else
    .error s!"{name}: {value} is outside 0..{bound - 1}"

private def decodeParams (j : Json) : Except String (Nat × Nat × Nat) := do
  let object ← j.getObj?
  if !object.contains "n" then
    throw "params must contain n"
  if !object.contains "psi" then
    throw "params must contain psi"
  for key in object.keys do
    if key != "n" && key != "psi" && key != "c1" then
      throw s!"unexpected params field: {key}"
  let n ← natField j "n"
  let psi ← natField j "psi"
  let c1 ←
    if object.contains "c1" then
      natField j "c1"
    else
      pure 48
  return (n, psi, c1)

private def decodeMode (j : Json) : Except String Bool := do
  match ← j.getStr? with
  | "Detect" => return true
  | "Construct" => return false
  | other => throw s!"mode must be Detect or Construct, got {other}"

private def encodeMode (mode : Bool) : Json :=
  jsonString (if mode then "Detect" else "Construct")

private def decodeToken (psi : Nat) (name : String) (j : Json) :
    Except String (PPL.Token psi) := do
  match j with
  | .null => return none
  | _ =>
      let input ← j.getArr?
      if hsize : input.size = 3 then
        let v : Vector Json 3 := ⟨input, hsize⟩
        let offset ← (v.get (0 : Fin 3)).getInt?
        let bit2Value ← (v.get (1 : Fin 3)).getNat?
        let bit3Value ← (v.get (2 : Fin 3)).getNat?
        let bit2 ← finOfNat s!"{name}[1]" 2 bit2Value
        let bit3 ← finOfNat s!"{name}[2]" 2 bit3Value
        if hoffset : PPL.ValidOffset psi offset then
          return some ((PPL.encodeOffset psi offset hoffset, bit2), bit3)
        else
          throw s!"{name}[0]: invalid signed offset {offset} for psi={psi}"
      else
        throw s!"{name} must be null or [offset, bit2, bit3]"

private def encodeToken {psi : Nat} (token : PPL.Token psi) : Json :=
  match token with
  | none => .null
  | some data =>
      Json.arr #[
        jsonInt (PPL.decodeOffset psi data.1.1),
        jsonNat data.1.2.val,
        jsonNat data.2.val
      ]

private def decodeState {psi kappa : Nat} (j : Json) :
    Except String (PPL.State psi kappa) := do
  exactFields j [
    "leader", "b", "dist", "last", "tokenB", "tokenW", "mode",
    "clock", "signalR", "hits", "bullet", "shield", "signalB"
  ]
  let leader ← bitField j "leader"
  let id ← bitField j "b"
  let distValue ← natField j "dist"
  let dist ← finOfNat "dist" (2 * psi) distValue
  let last ← bitField j "last"
  let tokenB ← decodeToken psi "tokenB" (← field j "tokenB")
  let tokenW ← decodeToken psi "tokenW" (← field j "tokenW")
  let mode ← decodeMode (← field j "mode")
  let clockValue ← natField j "clock"
  let clock ← finOfNat "clock" (kappa + 1) clockValue
  let signalRValue ← natField j "signalR"
  let signalR ← finOfNat "signalR" (kappa + 1) signalRValue
  let hitsValue ← natField j "hits"
  let hits ← finOfNat "hits" (psi + 1) hitsValue
  let bulletValue ← natField j "bullet"
  let bullet ← finOfNat "bullet" 3 bulletValue
  let shield ← bitField j "shield"
  let signalB ← bitField j "signalB"
  return {
    leader := leader
    id := id
    dist := dist
    last := last
    tokenB := tokenB
    tokenW := tokenW
    mode := mode
    clock := clock
    signalR := signalR
    hits := hits
    bullet := bullet
    shield := shield
    signalB := signalB
  }

/-- The keys are emitted in canonical lexical order. Lean Json objects are
objects semantically, while this order also makes state_key agree with
ppl_reference.py canonical_json(sort_keys=True). -/
private def encodeState {psi kappa : Nat} (q : PPL.State psi kappa) : Json :=
  Json.mkObj [
    ("b", bitJson q.id),
    ("bullet", jsonNat q.bullet.val),
    ("clock", jsonNat q.clock.val),
    ("dist", jsonNat q.dist.val),
    ("hits", jsonNat q.hits.val),
    ("last", bitJson q.last),
    ("leader", bitJson q.leader),
    ("mode", encodeMode q.mode),
    ("shield", bitJson q.shield),
    ("signalB", bitJson q.signalB),
    ("signalR", jsonNat q.signalR.val),
    ("tokenB", encodeToken q.tokenB),
    ("tokenW", encodeToken q.tokenW)
  ]

private def decodeConfig {n psi kappa : Nat} (j : Json) :
    Except String (Config n psi kappa) := do
  let input ← j.getArr?
  if hsize : input.size = n then
    let v : Vector Json n := ⟨input, hsize⟩
    Vector.ofFnM fun i =>
      match decodeState (psi := psi) (kappa := kappa) (v.get i) with
      | .ok state => .ok state
      | .error message => .error s!"state[{i.val}]: {message}"
  else
    throw s!"state must be a list of exactly n={n} agents"

private def encodeConfig {n psi kappa : Nat}
    (state : Config n psi kappa) : Json :=
  Json.arr (state.toArray.map encodeState)

private def stateKey {n psi kappa : Nat}
    (state : Config n psi kappa) : String :=
  (encodeConfig state).compress

private def metrics {n psi kappa : Nat} (hn : 0 < n)
    (state : Config n psi kappa) : Json := Id.run do
  let ring : DirectedRing n := ⟨hn⟩
  let mut leaders : Nat := 0
  let mut detectAgents : Nat := 0
  let mut signals : Nat := 0
  let mut liveBullets : Nat := 0
  let mut tokens : Nat := 0
  let mut distInconsistentEdges : Nat := 0
  for i in [0:n] do
    if hi : i < n then
      let site : Fin n := ⟨i, hi⟩
      let q := state.get site
      if q.leader then
        leaders := leaders + 1
      if q.mode then
        detectAgents := detectAgents + 1
      if 0 < q.signalR.val then
        signals := signals + 1
      if q.bullet.val = 2 then
        liveBullets := liveBullets + 1
      if q.tokenB.isSome then
        tokens := tokens + 1
      if q.tokenW.isSome then
        tokens := tokens + 1
      let r := state.get (ring.rightNeighbor site)
      if r.leader = false ∧
          r.dist.val ≠ (q.dist.val + 1) % (2 * psi) then
        distInconsistentEdges := distInconsistentEdges + 1
  let safeCandidate :=
    leaders == 1 && distInconsistentEdges == 0
  return Json.mkObj [
    ("leaders", jsonNat leaders),
    ("detect_agents", jsonNat detectAgents),
    ("signals", jsonNat signals),
    ("live_bullets", jsonNat liveBullets),
    ("tokens", jsonNat tokens),
    ("dist_inconsistent_edges", jsonNat distInconsistentEdges),
    ("safe_candidate", safeCandidate)
  ]

private def stateDiff {n psi kappa : Nat}
    (before after : Config n psi kappa) : Json :=
  let changes := (List.range n).filterMap fun i =>
    if hi : i < n then
      let old := before.get ⟨i, hi⟩
      let new := after.get ⟨i, hi⟩
      if old = new then
        none
      else
        some <| Json.mkObj [
          ("position", jsonNat i),
          ("before", encodeState old),
          ("after", encodeState new)
        ]
    else
      none
  Json.arr changes.toArray

private def stepConfig {n psi kappa : Nat} (hn : 0 < n)
    (state : Config n psi kappa) (edge : Fin n) : Config n psi kappa :=
  let ring : DirectedRing n := ⟨hn⟩
  Vector.ofFn
    (PopulationProtocol.step (PPL.protocol psi kappa) ring state.get edge)

private def stateRecord {n psi kappa : Nat} (hn : 0 < n)
    (before : Config n psi kappa) (edge : Fin n) :
    Config n psi kappa × Json :=
  let after := stepConfig hn before edge
  (after, Json.mkObj [
    ("action", jsonNat edge.val),
    ("edge", jsonNat edge.val),
    ("state", encodeConfig after),
    ("state_key", jsonString (stateKey after)),
    ("diff", stateDiff before after),
    ("metrics", metrics hn after)
  ])

private def decodeWord {n : Nat} (j : Json) :
    Except String (Array (Fin n)) := do
  let input ← j.getArr?
  let mut result := Array.mkEmpty input.size
  for h : i in *...input.size do
    let value ← input[i].getNat?
    result := result.push (← finOfNat s!"word[{i}]" n value)
  return result

private def bindings (sourceDigest : String) : Json :=
  Json.mkObj [
    ("source_manifest_sha256", jsonString sourceDigest),
    ("lean_version", jsonString "4.33.0"),
    ("protocol_entrypoint",
      jsonString "Leader/PPL/Transition.lean:PPL.protocol"),
    ("step_entrypoint",
      jsonString "Leader/Core/Basic.lean:PopulationProtocol.step")
  ]

private def describe (sourceDigest : String) (n psi c1 : Nat) : Json :=
  let kappa := c1 * psi
  Json.mkObj [
    ("ok", true),
    ("provider_id", jsonString "ppl.lean.v1"),
    ("protocol_id", jsonString "PPL.protocol"),
    ("state_codec", jsonString "ppl-alg1-13-field.v1"),
    ("transport", jsonString "persistent-jsonl"),
    ("source_bindings", bindings sourceDigest),
    ("action_space", Json.arr ((List.range n).toArray.map jsonNat)),
    ("metrics", Json.arr (([
      "leaders", "detect_agents", "signals", "live_bullets", "tokens",
      "dist_inconsistent_edges", "safe_candidate"
    ] : List String).toArray.map jsonString)),
    ("evidence_kind",
      jsonString "exact-source Lean execution of PPL.protocol"),
    ("semantic_scope",
      jsonString "P_PL directed ring, n>=3, psi>=2"),
    ("psi", jsonNat psi),
    ("c1", jsonNat c1),
    ("kmax", jsonNat kappa),
    ("extensions",
      Json.arr ((["run.include_states=false"] : List String).toArray.map jsonString))
  ]

private def validateTyped {n psi kappa : Nat} (hn : 0 < n)
    (state : Config n psi kappa) : Json :=
  Json.mkObj [
    ("ok", true),
    ("state", encodeConfig state),
    ("state_key", jsonString (stateKey state)),
    ("metrics", metrics hn state)
  ]

private def runWithStates {n psi kappa : Nat} (hn : 0 < n)
    (initial : Config n psi kappa) (word : Array (Fin n)) : Json := Id.run do
  let mut current := initial
  let mut steps := #[]
  for edge in word do
    let record := stateRecord hn current edge
    current := record.1
    steps := steps.push record.2
  return Json.mkObj [
    ("ok", true),
    ("initial", encodeConfig initial),
    ("initial_key", jsonString (stateKey initial)),
    ("initial_metrics", metrics hn initial),
    ("steps", Json.arr steps),
    ("final", encodeConfig current),
    ("final_key", jsonString (stateKey current)),
    ("final_metrics", metrics hn current)
  ]

private def runFinalOnly {n psi kappa : Nat} (hn : 0 < n)
    (initial : Config n psi kappa) (word : Array (Fin n)) : Json := Id.run do
  let mut current := initial
  for edge in word do
    current := stepConfig hn current edge
  return Json.mkObj [
    ("ok", true),
    ("steps", Json.arr #[]),
    ("final", encodeConfig current),
    ("final_key", jsonString (stateKey current)),
    ("final_metrics", metrics hn current),
    ("hit_step", Json.null),
    ("steps_executed", jsonNat word.size)
  ]

private def dispatchTyped {n psi kappa : Nat} (hn : 0 < n)
    (sourceDigest : String) (c1 : Nat)
    (operation : String) (request : Json) : Except String Json := do
  match operation with
  | "describe" =>
      exactFields request ["op", "params"]
      return describe sourceDigest n psi c1
  | "validate" =>
      exactFields request ["op", "params", "state"]
      let state ← decodeConfig (n := n) (psi := psi) (kappa := kappa)
        (← field request "state")
      return validateTyped hn state
  | "run" =>
      exactFields request ["op", "params", "state", "word", "include_states"]
      let includeStates ← (← field request "include_states").getBool?
      let state ← decodeConfig (n := n) (psi := psi) (kappa := kappa)
        (← field request "state")
      let word ← decodeWord (n := n) (← field request "word")
      if includeStates then
        return runWithStates hn state word
      else
        return runFinalOnly hn state word
  | _ => PPLSimPredicates.dispatchOrUnsupported (psi := psi) (kappa := kappa) hn operation request

private def dispatch (sourceDigest : String)
    (request : Json) : Except String Json := do
  let operation ← stringField request "op"
  let params ← field request "params"
  let (n, psi, c1) ← decodeParams params
  if hn3 : 3 ≤ n then
    if hpsi2 : 2 ≤ psi then
      if hc1 : 1 ≤ c1 then
        have hn : 0 < n := by omega
        dispatchTyped (n := n) (psi := psi) (kappa := c1 * psi)
          hn sourceDigest c1 operation request
      else
        throw "c1 must be at least 1"
    else
      throw "psi must be at least 2"
  else
    throw "n must be at least 3"

private def errorJson (message : String) : Json :=
  Json.mkObj [
    ("ok", false),
    ("error", jsonString message)
  ]

private def handleLine (sourceDigest line : String) : Json :=
  match Json.parse line with
  | .error message =>
      errorJson ("invalid JSON: " ++ message)
  | .ok request =>
      match dispatch sourceDigest request with
      | .ok response => response
      | .error message => errorJson message

partial def serve (sourceDigest : String)
    (input : IO.FS.Stream) (output : IO.FS.Stream) : IO Unit := do
  let line ← input.getLine
  if line.isEmpty then
    return
  output.putStrLn
    (handleLine sourceDigest line.trimAscii.toString).compress
  output.flush
  serve sourceDigest input output

end PPLSimBackend

def main : IO Unit := do
  let sourceDigest :=
    (← IO.getEnv "PPL_SIM_SOURCE_DIGEST").getD "UNBUILT"
  PPLSimBackend.serve sourceDigest (← IO.getStdin) (← IO.getStdout)
