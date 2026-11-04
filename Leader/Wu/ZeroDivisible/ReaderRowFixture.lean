import Leader.Wu.ZeroDivisible.CheckRepair
import Leader.Wu.Sim.RawCodec
import Lean.Data.Json

/-! Two exact-row probes for the reader audit. -/

set_option autoImplicit false
open Lean

namespace PPLLAstraR5ReaderAuditProbe

def cell (label : Fin 4) (state : MainState) : AgentState 4 :=
  { leader := false, probe := false, phase := false, bit := false,
    wait := false, state := state, path := .some label.val 0,
    reset := false, carry := false, count := 0,
    label := label, h_field := false,
    path2 := none, path3 := none, path4 := none, path5 := none,
    p := false, p_carry := false, reset_cmd := false, echo := false,
    signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩,
    shield := false, write_state := .none, write := .none,
    last := false, last_set := false, last_unset := false,
    b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }

def a1 (label position : Nat) : Path2Info :=
  { label := label, bit := 0, position := position, action := 1 }

def seedHead : Array (AgentState 4) :=
  #[{cell 0 .lock with path2 := some (a1 0 2)},
    cell 1 .compare1, cell 2 .equal, cell 3 .compare2]

def seedBoundary : Array (AgentState 4) :=
  #[cell 0 .compare1, cell 1 .depart,
    {cell 2 .equal with path2 := some (a1 2 2)}, cell 3 .compare2,
    cell 0 .lock, cell 1 .depart, cell 2 .equal, cell 3 .compare2]

def step (selective : Bool) (a : Array (AgentState 4)) (edge : Nat) :
    Array (AgentState 4) := Id.run do
  let l := a[edge]?.getD (cell 0 .depart)
  let r := a[(edge+1)%a.size]?.getD (cell 0 .depart)
  let out := PPLLAstraR5Repair.pipeline (by decide : 4 > 0) 0
    { selective := selective } l r
  return (a.set! edge out.1).set! ((edge+1)%a.size) out.2

def tokens (a : Array (AgentState 4)) : Array Nat := Id.run do
  let mut indices := #[]
  for i in [:a.size] do
    if (a[i]?.getD (cell 0 .depart)).path2.isSome then indices := indices.push i
  return indices

def encodeRow (a : Array (AgentState 4)) : Json :=
  toJson (a.map PPLLSimRawCodec.encodeState)

def report (name : String) (selective : Bool)
    (a : Array (AgentState 4)) (edge : Nat) : Json := Id.run do
  let b := step selective a edge
  return Json.mkObj [
    ("name", toJson name), ("selective", toJson selective),
    ("edge", toJson edge), ("input", encodeRow a), ("output", encodeRow b),
    ("tokens_before", toJson (tokens a)),
    ("tokens_after", toJson (tokens b))]

def main : IO Unit := do
  for selective in [true, false] do
    IO.println (report "head_forward_lock" selective seedHead 0).compress
    IO.println (report "unrelated_boundary" selective seedBoundary 7).compress

end PPLLAstraR5ReaderAuditProbe

def main : IO Unit := PPLLAstraR5ReaderAuditProbe.main
