import Leader.Wu.ZeroDivisible.CheckRepair
import Leader.Wu.ZeroDivisible.ResetDrain
import Leader.Wu.Sim.RawCodec
import Lean.Data.Json

/-! Finite source-exact replays of four neutral ψ=qψ=4 examples.
Every eager pair update is cross-checked against PopulationProtocol.step. -/
namespace PPLLAstraR5EntranceExamples
open PPLL Lean
set_option autoImplicit false

def ring : DirectedRing 4 := ⟨by decide⟩
def edge (i : Nat) : Fin 4 := ⟨i%4,Nat.mod_lt _ (by decide)⟩
def indices : List (Fin 4) := (List.range 4).map edge

def neutral (i : Fin 4) (s : MainState) : AgentState 4 :=
  { leader := false, probe := false, phase := false, bit := false,
    wait := false, state := s, path := .some i.val 0,
    reset := false, carry := false, count := 0,
    label := i, h_field := false,
    path2 := none, path3 := none, path4 := none, path5 := none,
    p := false, p_carry := false, reset_cmd := false, echo := false,
    signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩,
    shield := false, write_state := .none, write := .none,
    last := false, last_set := false, last_unset := false,
    b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }

def seed (name : String) (i : Fin 4) : AgentState 4 := Id.run do
  let s := if name == "all_lock" then MainState.lock else MainState.depart
  let u := neutral i s
  if name == "a5" && i.val == 1 then
    return { u with path2 := some ⟨0,0,0,5⟩ }
  if name == "a6_all_ones" then
    let v := { u with p := true }
    return { v with path2 := (if i.val == 2 then some ⟨0,0,0,6⟩ else none) }
  return u

instance : Inhabited (AgentState 4) := ⟨neutral (edge 0) .depart⟩

def terminalSeed (s : MainState) (i : Fin 4) : AgentState 4 :=
  neutral i (if i.val == 3 then s else .depart)

def asConfig (a : Array (AgentState 4)) : Fin 4 → AgentState 4 :=
  fun i => a[i.val]!

def rawEqual (C D : Fin 4 → AgentState 4) : Bool :=
  indices.all (fun i =>
    PPLLSimRawCodec.encodeState (C i) == PPLLSimRawCodec.encodeState (D i))

def stepArray (selective : Bool) (κ : Nat)
    (a : Array (AgentState 4)) (e : Nat) : Array (AgentState 4) :=
  let l := a[e%4]!
  let r := a[(e+1)%4]!
  let z := PPLLAstraR5Repair.pipeline (by decide : 0<4) κ
    { selective := selective } l r
  (a.set! (e%4) z.1).set! ((e+1)%4) z.2

def trace (selective : Bool) (κ : Nat) (initial : Fin 4 → AgentState 4)
    (word : List Nat) : Array (Array (AgentState 4)) :=
  word.foldl (fun rows e =>
    rows.push (stepArray selective κ rows[rows.size-1]! e))
    #[(indices.map initial).toArray]

def exactSteps (selective : Bool) (κ : Nat)
    (rows : Array (Array (AgentState 4))) (word : List Nat) : Bool :=
  (List.range word.length).all (fun k =>
    let e := word.getD k 4
    let p := PPLLAstraR5ResetDrain.protocol (by decide : 0<4) κ
      { selective := selective }
    rawEqual (asConfig rows[k+1]!)
      (p.step ring (asConfig rows[k]!) (edge e)))

def leader (C : Fin 4 → AgentState 4) : Bool :=
  indices.any (fun i => (C i).leader)
def hole (C : Fin 4 → AgentState 4) : Bool :=
  indices.any (fun i => (C i).path == .bot)
def terminalE (C : Fin 4 → AgentState 4) : Bool :=
  (C (edge 3)).state == .eliminate_signal
def tokenFree (C : Fin 4 → AgentState 4) : Bool :=
  indices.all (fun i => (C i).path2.isNone)
def fullOwn (C : Fin 4 → AgentState 4) : Bool :=
  indices.all (fun i =>
    (C i).label.val == i.val &&
    match (C i).path with
    | .some j b => j == i.val && b ≤ 1
    | .bot => false)
def bState (j : Nat) (s : MainState) : Bool :=
  if j == 0 then s == .lock || s == .compare1
  else if j == 3 then s == .compare2
  else if j == 2 then
    s == .equal || s == .depart || s == .lock || s == .compare1
  else s == .depart || s == .lock || s == .compare1
def globalB (C : Fin 4 → AgentState 4) : Bool :=
  fullOwn C && indices.all (fun i =>
    bState i.val (C i).state &&
    (match (C i).path2 with
    | none => true
    | some t => 1 ≤ t.action && t.action ≤ 4))

def encodeRow (C : Fin 4 → AgentState 4) : Json :=
  Json.arr ((indices.map (fun i => PPLLSimRawCodec.encodeState (C i))).toArray)

def caseReport (name : String) (selective : Bool) (κ : Nat)
    (initial : Fin 4 → AgentState 4) (word : List Nat) : Json := Id.run do
  let rows := trace selective κ initial word
  let last := asConfig rows[rows.size-1]!
  let checkpoints := (List.range rows.size).map (fun k =>
    let C := asConfig rows[k]!
    Json.mkObj [
      ("k",toJson k), ("leader",toJson (leader C)),
      ("hole",toJson (hole C)), ("terminal_E",toJson (terminalE C)),
      ("states",toJson ((indices.map (fun i => reprStr (C i).state)).toArray)),
      ("tokens",toJson ((indices.map (fun i =>
        match (C i).path2 with
        | none => Json.null
        | some t => toJson (t.label,t.bit,t.position,t.action))).toArray)),
      ("p",toJson ((indices.map (fun i => (C i).p)).toArray)),
      ("p_carry",toJson ((indices.map (fun i => (C i).p_carry)).toArray)),
      ("raw",encodeRow C)])
  return Json.mkObj [
    ("name",toJson name), ("selective",toJson selective),
    ("kappa",toJson κ), ("word",toJson word),
    ("initial_domain",toJson (indices.all (fun i =>
      PPLLSimRawCodec.inProtocolDomainB κ (initial i)))),
    ("all_edges_match_protocol_step",toJson (exactSteps selective κ rows word)),
    ("final_leader",toJson (leader last)),
    ("final_hole",toJson (hole last)),
    ("final_terminal_E",toJson (terminalE last)),
    ("final_full_own",toJson (fullOwn last)),
    ("final_B",toJson (globalB last)),
    ("final_token_free",toJson (tokenFree last)),
    ("rows",Json.arr checkpoints.toArray)]

def main : IO Unit := do
  for selective in [false,true] do
    IO.println (caseReport "all_lock" selective 2 (seed "all_lock")
      [2,1,0,3]).compress
    IO.println (caseReport "all_depart" selective 2 (seed "all_depart")
      [3,0,1,2,1,0,3]).compress
    IO.println (caseReport "a5" selective 2 (seed "a5") [1,2]).compress
    IO.println (caseReport "a6_all_ones" selective 2 (seed "a6_all_ones")
      [1,0,1,2,2]).compress
    for (n,s) in [("none",MainState.none), ("check_ready",MainState.CHECK_ready),
        ("congest",MainState.congest), ("lock",MainState.lock),
        ("compare1",MainState.compare1), ("equal",MainState.equal),
        ("compare2",MainState.compare2), ("E",MainState.eliminate_signal)] do
      IO.println (caseReport ("terminal_"++n) selective 2
        (terminalSeed s) [2]).compress

end PPLLAstraR5EntranceExamples

def main : IO Unit := PPLLAstraR5EntranceExamples.main
