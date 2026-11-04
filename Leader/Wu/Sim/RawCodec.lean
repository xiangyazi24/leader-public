import Leader.Wu.Protocol.State
import Lean.Data.Json
import Init.Data.Vector.OfFn

/-!
# JSON codec for the raw audit carrier `AgentState ψ`

The kernel-experiment variants (`protocolAll8`, `protocolAll9R7`,
`protocolAll10Consume`) are population protocols on `AgentState ψ`, whose
payload fields are unbounded `Nat`/`Int`.  This codec uses the same 32-field
JSON schema as `PPLLSimCodec` (codec `ppll-bounded-agent-state-32.v1`), and on
every state in the declared value domain it produces exactly the same JSON:
`path2.action` is written as the raw stored value, which is what the bounded
codec writes for an erased state (`action.val + 1`), and a `path4`/`path5`
label is the raw integer, with `-1` the cleaning sentinel.  Consequently an
initial configuration written for the bounded backend can be sent unchanged to
a raw backend.

The decoder accepts values outside the declared domain (for example
`count > κ`), because the raw variants have no domain-closure theorem and the
explorer must be able to re-expand whatever state they produce.  Membership in
the declared domain is reported separately by `inProtocolDomainB`.
-/

set_option autoImplicit false

open Lean

namespace PPLLSimRawCodec

abbrev Config (n psi : Nat) := Vector (AgentState psi) n

private def objN (n : Nat) (j : Json) : Except String Unit := do
  let o <- j.getObj?
  if o.size = n then pure () else
    throw s!"expected object with {n} fields, got {o.size}"

private def fld (j : Json) (k : String) : Except String Json := j.getObjVal? k

private def dFin (n : Nat) (j : Json) : Except String (Fin n) := do
  let x <- j.getNat?
  if h : x < n then pure <| ⟨x, h⟩ else
    throw s!"Fin value {x} out of range 0..{n-1}"

private def dMain (j : Json) : Except String MainState := do
  match <- j.getStr? with
  | "produce" => pure .produce | "done" => pure .done
  | "depart" => pure .depart | "none" => pure .none
  | "congest" => pure .congest | "lock" => pure .lock
  | "compare1" => pure .compare1 | "compare2" => pure .compare2
  | "eliminate_signal" => pure .eliminate_signal
  | "CHECK_ready" => pure .CHECK_ready | "equal" => pure .equal
  | "larger" => pure .larger | "less" => pure .less
  | "toss" => pure .toss | "toss_done" => pure .toss_done
  | s => throw s!"unknown MainState tag: {s}"

private def eMain : MainState -> String
  | .produce => "produce" | .done => "done" | .depart => "depart"
  | .none => "none" | .congest => "congest" | .lock => "lock"
  | .compare1 => "compare1" | .compare2 => "compare2"
  | .eliminate_signal => "eliminate_signal" | .CHECK_ready => "CHECK_ready"
  | .equal => "equal" | .larger => "larger" | .less => "less"
  | .toss => "toss" | .toss_done => "toss_done"

private def dWS (j : Json) : Except String WriteState := do
  match <- j.getStr? with
  | "depart" => pure .depart | "ready" => pure .ready
  | "increment_WS" => pure .increment_WS
  | "increment_WS_done" => pure .increment_WS_done
  | "done" => pure .done | "equal" => pure .equal
  | "larger" => pure .larger | "less" => pure .less
  | "produce" => pure .produce | "overwrite" => pure .overwrite
  | "move_flip" => pure .move_flip | "move" => pure .move
  | "increment_group" => pure .increment_group | "none" => pure .none
  | s => throw s!"unknown WriteState tag: {s}"

private def eWS : WriteState -> String
  | .depart => "depart" | .ready => "ready" | .increment_WS => "increment_WS"
  | .increment_WS_done => "increment_WS_done" | .done => "done"
  | .equal => "equal" | .larger => "larger" | .less => "less"
  | .produce => "produce" | .overwrite => "overwrite"
  | .move_flip => "move_flip" | .move => "move"
  | .increment_group => "increment_group" | .none => "none"

private def dWA (j : Json) : Except String WriteAction := do
  match <- j.getStr? with
  | "overwrite" => pure .overwrite | "move_flip" => pure .move_flip
  | "move" => pure .move | "increment_group" => pure .increment_group
  | "none" => pure .none
  | s => throw s!"unknown WriteAction tag: {s}"

private def eWA : WriteAction -> String
  | .overwrite => "overwrite" | .move_flip => "move_flip" | .move => "move"
  | .increment_group => "increment_group" | .none => "none"

private def dPath : Json -> Except String PathInfo
  | .null => pure .bot
  | j => do
      objN 2 j
      return .some (← (← fld j "label").getNat?) (← (← fld j "bit").getNat?)

def ePath : PathInfo -> Json
  | .bot => .null
  | .some l b => Json.mkObj [("label", l), ("bit", b)]

private def dP2 : Json -> Except String (Option Path2Info)
  | .null => pure none
  | j => do
      objN 4 j
      return some
        { label := ← (← fld j "label").getNat?
          bit := ← (← fld j "bit").getNat?
          position := ← (← fld j "position").getNat?
          action := ← (← fld j "action").getNat? }

def eP2 : Option Path2Info -> Json
  | none => .null
  | some p => Json.mkObj [("label", p.label), ("bit", p.bit),
      ("position", p.position), ("action", p.action)]

private def dP3 : Json -> Except String (Option Path3Info)
  | .null => pure none
  | j => do
      objN 3 j
      return some
        { label := ← (← fld j "label").getNat?
          bit := ← (← fld j "bit").getNat?
          flag := ← (← fld j "flag").getNat? }

def eP3 : Option Path3Info -> Json
  | none => .null
  | some p => Json.mkObj [("label", p.label), ("bit", p.bit), ("flag", p.flag)]

private def dClean : Json -> Except String (Option (Int × Nat))
  | .null => pure none
  | j => do
      objN 2 j
      return some (← (← fld j "label").getInt?, ← (← fld j "bit").getNat?)

def eClean : Option (Int × Nat) -> Json
  | none => .null
  | some (l, b) => Json.mkObj [("label", l), ("bit", b)]

def decodeState {psi : Nat} (j : Json) : Except String (AgentState psi) := do
  objN 32 j
  let leader <- (← fld j "leader").getBool?
  let probe <- (← fld j "probe").getBool?
  let phase <- (← fld j "phase").getBool?
  let bit <- (← fld j "bit").getBool?
  let wait <- (← fld j "wait").getBool?
  let state <- dMain (← fld j "state")
  let path <- dPath (← fld j "path")
  let reset <- (← fld j "reset").getBool?
  let carry <- (← fld j "carry").getBool?
  let count <- (← fld j "count").getNat?
  let label <- dFin psi (← fld j "label")
  let h_field <- (← fld j "h_field").getBool?
  let path2 <- dP2 (← fld j "path2")
  let path3 <- dP3 (← fld j "path3")
  let path4 <- dClean (← fld j "path4")
  let path5 <- dClean (← fld j "path5")
  let p <- (← fld j "p").getBool?
  let p_carry <- (← fld j "p_carry").getBool?
  let reset_cmd <- (← fld j "reset_cmd").getBool?
  let echo <- (← fld j "echo").getBool?
  let signal_B <- dFin 2 (← fld j "signal_B")
  let bullet <- dFin 3 (← fld j "bullet")
  let shield <- (← fld j "shield").getBool?
  let write_state <- dWS (← fld j "write_state")
  let write <- dWA (← fld j "write")
  let last <- (← fld j "last").getBool?
  let last_set <- (← fld j "last_set").getBool?
  let last_unset <- (← fld j "last_unset").getBool?
  let b_carry <- (← fld j "b_carry").getBool?
  let gen_ws <- (← fld j "gen_ws").getBool?
  let ws_echo <- (← fld j "ws_echo").getBool?
  let signal_ws <- (← fld j "signal_ws").getBool?
  return {
    leader := leader, probe := probe, phase := phase, bit := bit, wait := wait,
    state := state, path := path, reset := reset, carry := carry, count := count,
    label := label, h_field := h_field, path2 := path2, path3 := path3,
    path4 := path4, path5 := path5, p := p, p_carry := p_carry,
    reset_cmd := reset_cmd, echo := echo, signal_B := signal_B, bullet := bullet,
    shield := shield, write_state := write_state, write := write, last := last,
    last_set := last_set, last_unset := last_unset, b_carry := b_carry,
    gen_ws := gen_ws, ws_echo := ws_echo, signal_ws := signal_ws }

def encodeState {psi : Nat} (s : AgentState psi) : Json :=
  Json.mkObj [
    ("leader", s.leader), ("probe", s.probe), ("phase", s.phase), ("bit", s.bit),
    ("wait", s.wait), ("state", eMain s.state), ("path", ePath s.path),
    ("reset", s.reset), ("carry", s.carry), ("count", s.count),
    ("label", s.label.val), ("h_field", s.h_field), ("path2", eP2 s.path2),
    ("path3", eP3 s.path3), ("path4", eClean s.path4), ("path5", eClean s.path5),
    ("p", s.p), ("p_carry", s.p_carry), ("reset_cmd", s.reset_cmd),
    ("echo", s.echo), ("signal_B", s.signal_B.val), ("bullet", s.bullet.val),
    ("shield", s.shield), ("write_state", eWS s.write_state), ("write", eWA s.write),
    ("last", s.last), ("last_set", s.last_set), ("last_unset", s.last_unset),
    ("b_carry", s.b_carry), ("gen_ws", s.gen_ws), ("ws_echo", s.ws_echo),
    ("signal_ws", s.signal_ws) ]

def decodeConfig {n psi : Nat} (j : Json) : Except String (Config n psi) := do
  let a <- j.getArr?
  if h : a.size = n then
    let v : Vector Json n := ⟨a, h⟩
    Vector.ofFnM fun i =>
      match decodeState (psi:=psi) (v.get i) with
      | .ok state => .ok state
      | .error message => .error s!"states[{i.val}]: {message}"
  else throw s!"configuration length {a.size}, expected {n}"

def encodeConfig {n psi : Nat} (C : Config n psi) : Json :=
  Json.arr <| C.toArray.map encodeState

/-- Boolean mirror of `AgentState.inProtocolDomain` (Leader/Wu/Protocol/State.lean:151),
used only as a reported metric: does the state lie in the value ranges that
the bounded carrier `BoundedAgentState ψ κ` can represent? -/
def inProtocolDomainB {psi : Nat} (kappa : Nat) (s : AgentState psi) : Bool :=
  decide (s.count ≤ kappa) &&
  (match s.path with
   | .bot => true
   | .some label bit => decide (label < psi) && decide (bit ≤ 1)) &&
  (match s.path2 with
   | none => true
   | some p => decide (p.label < psi) && decide (p.bit ≤ 1) &&
       decide (p.position ≤ psi) && decide (1 ≤ p.action) && decide (p.action ≤ 6)) &&
  (match s.path3 with
   | none => true
   | some p => decide (p.label < psi) && decide (p.bit ≤ 1) && decide (p.flag ≤ 1)) &&
  (match s.path4 with
   | none => true
   | some (label, bit) =>
       decide ((-1 : Int) ≤ label) && decide (label < Int.ofNat psi) && decide (bit ≤ 1)) &&
  (match s.path5 with
   | none => true
   | some (label, bit) =>
       decide ((-1 : Int) ≤ label) && decide (label < Int.ofNat psi) && decide (bit ≤ 1))

end PPLLSimRawCodec
