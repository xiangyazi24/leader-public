import Leader.Wu.ZeroDivisible.CheckRepair
import Leader.Wu.Sim.RawCodec
import Lean.Data.Json

/-! Source-exact finite tests of neutral, uniformly rotated main-path labels. -/
namespace PPLLAstraR5MisindexedProbe
open PPLL Lean

def seed (ψ q shift : Nat) (hψ : 0 < ψ) : Array (AgentState ψ) := Id.run do
  let mut a := #[]
  for i in [:q*ψ] do
    let j := i%ψ
    a := a.push {
      leader := false, probe := false, phase := false, bit := false,
      wait := false, state := .depart, path := .some ((j+shift)%ψ) 0,
      reset := false, carry := false, count := 0,
      label := ⟨j,Nat.mod_lt i hψ⟩, h_field := false,
      path2 := none, path3 := none, path4 := none, path5 := none,
      p := false, p_carry := false, reset_cmd := false, echo := false,
      signal_B := ⟨0,by decide⟩, bullet := ⟨0,by decide⟩,
      shield := false, write_state := .none, write := .none,
      last := false, last_set := false, last_unset := false,
      b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }
  return a

def target {ψ : Nat} (a : Array (AgentState ψ)) : String :=
  if a.any (·.leader) then "leader"
  else if a.any (fun u => u.path == .bot) then "hole"
  else "none"

def step {ψ : Nat} (hψ : 0 < ψ) (κ : Nat) (selective : Bool)
    (a : Array (AgentState ψ)) (e : Nat) : Array (AgentState ψ) := Id.run do
  let n := a.size
  let some l := a[e%n]? | return a
  let some r := a[(e+1)%n]? | return a
  let z := PPLLAstraR5Repair.pipeline hψ κ { selective := selective }
    l r
  return (a.set! (e%n) z.1).set! ((e+1)%n) z.2

def runWord {ψ : Nat} (hψ : 0 < ψ) (κ : Nat) (selective : Bool)
    (a : Array (AgentState ψ)) (word : List Nat) :
    Array (AgentState ψ) × List Nat := Id.run do
  let mut r := a
  let mut used := []
  for e in word do
    if target r != "none" then break
    r := step hψ κ selective r e
    used := used ++ [e]
  return (r,used)

def projection {ψ : Nat} (a : Array (AgentState ψ)) : Json :=
  Json.mkObj [
    ("states",toJson (a.map (fun u => reprStr u.state))),
    ("paths",toJson (a.map (fun u => match u.path with
      | .bot => "bot" | .some j b => s!"{j}:{b}"))),
    ("tokens",toJson (a.map (fun u => match u.path2 with
      | none => "none" | some t => s!"{t.label}:{t.bit}:{t.position}:{t.action}")))]

def report (ψ q shift : Nat) (hψ : 0 < ψ) (selective : Bool) : Json := Id.run do
  let init := seed ψ q shift hψ
  let e := ψ-shift-1
  let n := q*ψ
  let first := step hψ 2 selective init e
  let candidates := [
    ("double_boundary",[e,e]),
    ("forward_cycles",(List.range 128).map (fun k => k%n)),
    ("reverse_cycles",(List.range 128).map (fun k => (n-1)-(k%n)))]
  let results := candidates.map fun (name,word) =>
    let (r,used) := runWord hψ 2 selective init word
    Json.mkObj [
      ("schedule",toJson name), ("status",toJson (target r)),
      ("word",toJson used), ("steps",toJson used.length),
      ("endpoint_domain",toJson (r.all (PPLLSimRawCodec.inProtocolDomainB 2))),
      ("projection",projection r)]
  return Json.mkObj [
    ("psi",toJson ψ), ("q",toJson q), ("shift",toJson shift),
    ("selective",toJson selective),
    ("seed_domain",toJson (init.all (PPLLSimRawCodec.inProtocolDomainB 2))),
    ("seed_shape",toJson ((List.range n).all fun i =>
      match init[i]? with
      | none => false
      | some u =>
        !u.leader && u.state == .depart && u.label.val == i%ψ &&
        (match u.path with
         | .bot => false
         | .some j b => j == (i%ψ+shift)%ψ && b == 0 && j != u.label.val))),
    ("first_step_status",toJson (target first)),
    ("seed",toJson (init.map PPLLSimRawCodec.encodeState)),
    ("runs",Json.arr results.toArray)]

def reportA5 (selective : Bool) : Json := Id.run do
  let a := seed 4 1 1 (by decide)
  let tok : Option Path2Info := some ⟨0,0,0,5⟩
  let some u2 := a[2]? | return Json.null
  let some u3 := a[3]? | return Json.null
  let a := (a.set! 2 { u2 with path2 := tok }).set! 3
    { u3 with path2 := tok }
  let (r2,w2) := runWord (by decide : 0<4) 2 selective a [2,2]
  let (r3,w3) := runWord (by decide : 0<4) 2 selective a [2,2,2]
  return Json.mkObj [
    ("fixture",toJson "double_A5"), ("selective",toJson selective),
    ("seed_domain",toJson (a.all (PPLLSimRawCodec.inProtocolDomainB 2))),
    ("seed",toJson (a.map PPLLSimRawCodec.encodeState)),
    ("after2",Json.mkObj [("word",toJson w2), ("status",toJson (target r2)),
      ("endpoint_domain",toJson (r2.all (PPLLSimRawCodec.inProtocolDomainB 2))),
      ("projection",projection r2)]),
    ("after3",Json.mkObj [("word",toJson w3), ("status",toJson (target r3)),
      ("endpoint_domain",toJson (r3.all (PPLLSimRawCodec.inProtocolDomainB 2))),
      ("projection",projection r3)])]

def main : IO Unit := do
  for ψ in [4,5] do
    if hψ : 0 < ψ then
      for q in [1,2] do
        for shift in [1:ψ] do
          for selective in [false,true] do
            IO.println (report ψ q shift hψ selective).compress
  for selective in [false,true] do
    IO.println (reportA5 selective).compress

end PPLLAstraR5MisindexedProbe

def main : IO Unit := PPLLAstraR5MisindexedProbe.main
