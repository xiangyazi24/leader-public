import Lean.Data.Json
import Init.Data.Array.OfFn
import Init.Data.Vector.OfFn
import Leader.PPL.Predicates


/-!
# JSON adapter for executable P_PL predicates


This module contains only wire decoding and observation code.  Every Boolean
predicate result is obtained by `decide` on the definitions and Decidable
instances in `Leader/PPL/Predicates.lean`; no predicate semantics are copied
into the simulator backend.
-/


set_option autoImplicit false
set_option Elab.async false


open Lean


namespace PPLSimPredicates


private instance validOffsetDecidable (psi : Nat) (z : Int) :
    Decidable (PPL.ValidOffset psi z) := by
  unfold PPL.ValidOffset
  infer_instance


private abbrev WireConfig (n psi kappa : Nat) :=
  Vector (PPL.State psi kappa) n


private def field (j : Json) (key : String) : Except String Json :=
  j.getObjVal? key


private def natField (j : Json) (key : String) : Except String Nat := do
  (← field j key).getNat?


private def jsonNat (value : Nat) : Json := value
private def jsonBool (value : Bool) : Json := value
private def jsonString (value : String) : Json := value


private def exactPredicateFields (j : Json) : Except String Unit := do
  let object ← j.getObj?
  for key in ["op", "params", "state"] do
    if !object.contains key then
      throw s!"missing field: {key}"
  for key in object.keys do
    if !(["op", "params", "state", "root"].contains key) then
      throw s!"unexpected field: {key}"


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


private def decodeMode (j : Json) : Except String Bool := do
  match ← j.getStr? with
  | "Detect" => return true
  | "Construct" => return false
  | other => throw s!"mode must be Detect or Construct, got {other}"


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


private def decodeState {psi kappa : Nat} (j : Json) :
    Except String (PPL.State psi kappa) := do
  let object ← j.getObj?
  let required := [
    "leader", "b", "dist", "last", "tokenB", "tokenW", "mode",
    "clock", "signalR", "hits", "bullet", "shield", "signalB"
  ]
  for key in required do
    if !object.contains key then
      throw s!"missing field: {key}"
  for key in object.keys do
    if !required.contains key then
      throw s!"unexpected field: {key}"


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


private def decodeConfig {n psi kappa : Nat} (j : Json) :
    Except String (WireConfig n psi kappa) := do
  let input ← j.getArr?
  if hsize : input.size = n then
    let v : Vector Json n := ⟨input, hsize⟩
    Vector.ofFnM fun i =>
      match decodeState (psi := psi) (kappa := kappa) (v.get i) with
      | .ok state => .ok state
      | .error message => .error s!"state[{i.val}]: {message}"
  else
    throw s!"state must be a list of exactly n={n} agents"


private def decodeRoot {n : Nat} (request : Json) :
    Except String (Fin n) := do
  let object ← request.getObj?
  let value ←
    if object.contains "root" then
      natField request "root"
    else
      pure 0
  finOfNat "root" n value


private def optionNatJson : Option Nat → Json
  | none => .null
  | some value => jsonNat value


private def correctArray {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : PPL.Config n psi kappa) (i : Fin n)
    (kind : PPL.TokenKind) (interiorCount : Nat) : Json :=
  Json.arr ((List.range interiorCount).toArray.map fun seg =>
    jsonBool (decide (PPL.CorrectToken ring root C i kind seg)))


private def evaluate {n psi kappa : Nat} (hn : 0 < n)
    (root : Fin n) (state : WireConfig n psi kappa) : Json :=
  let ring : DirectedRing n := ⟨hn⟩
  let C : PPL.Config n psi kappa := state.get
  let zeta := (n + psi - 1) / psi
  let interiorCount := zeta - 2


  let dll := Json.arr (Array.ofFn fun i : Fin n =>
    optionNatJson (PPL.dLL ring C i))


  let peaceful := Json.arr (Array.ofFn fun i : Fin n =>
    jsonBool (decide (PPL.Peaceful ring C i)))


  let validToken := Json.arr (Array.ofFn fun i : Fin n =>
    Json.mkObj [
      ("tokenB", jsonBool (decide (PPL.ValidToken .black C i))),
      ("tokenW", jsonBool (decide (PPL.ValidToken .white C i)))
    ])


  let correctToken := Json.arr (Array.ofFn fun i : Fin n =>
    Json.mkObj [
      ("tokenB", correctArray ring root C i .black interiorCount),
      ("tokenW", correctArray ring root C i .white interiorCount)
    ])


  let risky := Json.arr (Array.ofFn fun i : Fin n =>
    jsonBool (decide (PPL.Risky ring root C i)))


  Json.mkObj [
    ("ok", true),
    ("root", jsonNat root.val),
    ("interior_segments",
      Json.arr ((List.range interiorCount).toArray.map jsonNat)),
    ("dLL", dll),
    ("Peaceful", peaceful),
    ("CPB", jsonBool (decide (PPL.CPB ring C))),
    ("CDLAt", jsonBool (decide (PPL.CDLAt ring root C))),
    ("ValidToken", validToken),
    ("CorrectToken", correctToken),
    ("Risky", risky),
    ("SPLAt", jsonBool (decide (PPL.SPLAt ring root C))),
    ("Perfect", jsonBool (decide (PPL.Perfect ring C)))
  ]


/-- Fallback target for SimBackend's one-line default dispatch hook.  Unknown
operations retain the existing error string; only "predicates" is intercepted. -/
def dispatchOrUnsupported {n psi kappa : Nat} (hn : 0 < n)
    (operation : String) (request : Json) : Except String Json := do
  if operation != "predicates" then
    throw s!"unsupported operation: {operation}"
  exactPredicateFields request
  let state ← decodeConfig (n := n) (psi := psi) (kappa := kappa)
    (← field request "state")
  let root ← decodeRoot (n := n) request
  return evaluate hn root state


end PPLSimPredicates


