import Leader.Wu.ZeroDivisible.SuffixSurvival
import Leader.Wu.Sim.RawCodec
import Lean.Data.Json

/-! Exact R5 cut and suffix fixtures; no reachability claim for an arbitrary cut. -/

set_option autoImplicit false
open Lean

namespace PPLLAstraR5SuffixProbe

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

def encodePair (p : AgentState 4 × AgentState 4) : Json :=
  toJson #[PPLLSimRawCodec.encodeState p.1, PPLLSimRawCodec.encodeState p.2]

def hasLeader (p : AgentState 4 × AgentState 4) : Bool :=
  p.1.leader || p.2.leader

def cutFixture (name : String) (selective : Bool)
    (l r : AgentState 4) : Json := Id.run do
  let c : PPLLAstraR5Repair.Cfg := { selective := selective }
  let hp : 4 > 0 := by decide
  let check := PPLLAstraR5Repair.SuffixInterfaces.throughCheck hp 0 c l r
  let compare := PPLLAstraR5Repair.SuffixInterfaces.throughCompare hp 0 c l r
  let finished := PPLLAstraR5Repair.pipeline hp 0 c l r
  let fromCheck := PPLLAstraR5Repair.SuffixInterfaces.finishAfterCheck
    hp 0 l r check.1 check.2
  let fromCompare := PPLLAstraR5Repair.SuffixInterfaces.finishAfterCompare
    hp l r compare.1 compare.2
  return Json.mkObj [
    ("name", toJson name), ("selective", toJson selective),
    ("input", encodePair (l,r)), ("check", encodePair check),
    ("compare", encodePair compare), ("output", encodePair finished),
    ("check_right_leader", toJson check.2.leader),
    ("compare_right_leader", toJson compare.2.leader),
    ("output_leader", toJson (hasLeader finished)),
    ("from_check_exact", toJson (fromCheck == finished)),
    ("from_compare_exact", toJson (fromCompare == finished))]

def suffixFixture (selective : Bool) : Json := Id.run do
  let _ := selective
  let hp : 4 > 0 := by decide
  let origL := cell 2 .depart
  let origR := cell 3 .depart
  let cutL := { origL with reset_cmd := true }
  let cutR := { origR with path2 := some ⟨0, 0, 0, 4⟩ }
  let out := PPLLAstraR5Repair.SuffixInterfaces.finishAfterCompare
    hp origL origR cutL cutR
  return Json.mkObj [
    ("name", toJson "arbitrary_compare_cut_reset"),
    ("selective", toJson selective),
    ("original", encodePair (origL,origR)),
    ("compare_cut", encodePair (cutL,cutR)),
    ("output", encodePair out),
    ("cut_right_token", toJson cutR.path2.isSome),
    ("output_right_token", toJson out.2.path2.isSome),
    ("output_right_hole", toJson (out.2.path == .bot))]

def leftBirthFixture (selective : Bool) : Json := Id.run do
  let hp : 4 > 0 := by decide
  let origL := cell 2 .depart
  let origR := cell 3 .depart
  let cutL := { origL with leader := true }
  let cutR := { origR with bullet := 2 }
  let out := PPLLAstraR5Repair.SuffixInterfaces.finishAfterCompare
    hp origL origR cutL cutR
  return Json.mkObj [
    ("name", toJson "arbitrary_left_birth_bullet"),
    ("selective", toJson selective),
    ("original", encodePair (origL,origR)),
    ("compare_cut", encodePair (cutL,cutR)),
    ("output", encodePair out),
    ("cut_left_leader", toJson cutL.leader),
    ("output_leader", toJson (hasLeader out))]

def main : IO Unit := do
  for selective in [true, false] do
    IO.println (cutFixture "check_birth" selective
      (cell 2 .depart) (cell 3 .equal)).compress
    IO.println (cutFixture "compare_birth" selective
      {cell 2 .compare1 with path2 := some ⟨3, 0, 1, 1⟩}
      (cell 3 .compare2)).compress
    IO.println (suffixFixture selective).compress
    IO.println (leftBirthFixture selective).compress

end PPLLAstraR5SuffixProbe

def main : IO Unit := PPLLAstraR5SuffixProbe.main
