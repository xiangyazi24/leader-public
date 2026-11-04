import Leader.Wu.ZeroDivisible.CheckRepair
import Leader.Wu.Sim.RawCodec
import Lean.Data.Json

/-! Source-exact two-cell probes for the occupied-path holder frame. -/

set_option autoImplicit false
open Lean

namespace PPLLAstraR5PathFrameProbe

def cell (label : Fin 4) (state : MainState) (path : PathInfo) : AgentState 4 :=
  { leader := false, probe := false, phase := false, bit := false,
    wait := false, state := state, path := path,
    reset := false, carry := false, count := 0,
    label := label, h_field := false,
    path2 := none, path3 := none, path4 := none, path5 := none,
    p := false, p_carry := false, reset_cmd := false, echo := false,
    signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩,
    shield := false, write_state := .none, write := .none,
    last := false, last_set := false, last_unset := false,
    b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }

def cases : List (String × AgentState 4 × AgentState 4) :=
  [("left_produce", cell 1 .produce (.some 1 1), cell 2 .done (.some 2 0)),
   ("right_produce", cell 2 .depart (.some 2 0), cell 3 .produce (.some 3 1)),
   ("nonproduce", cell 1 .depart (.some 1 0), cell 2 .depart (.some 2 0))]

def report (name : String) (selective : Bool) (l r : AgentState 4) : Json := Id.run do
  let out := PPLLAstraR5Repair.pipeline (by decide : 4 > 0) 0
    { selective := selective } l r
  let holes := out.1.path == .bot || out.2.path == .bot
  let frame := out.1.path == l.path && out.2.path == r.path &&
    out.1.state != .produce && out.2.state != .produce
  return Json.mkObj [
    ("name", toJson name), ("selective", toJson selective),
    ("input", toJson #[PPLLSimRawCodec.encodeState l, PPLLSimRawCodec.encodeState r]),
    ("output", toJson #[PPLLSimRawCodec.encodeState out.1, PPLLSimRawCodec.encodeState out.2]),
    ("holes", toJson holes), ("frame", toJson frame)]

def main : IO Unit := do
  for (name, l, r) in cases do
    for selective in [true, false] do
      IO.println (report name selective l r).compress

end PPLLAstraR5PathFrameProbe

def main : IO Unit := PPLLAstraR5PathFrameProbe.main
