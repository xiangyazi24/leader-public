import Leader.Wu.ZeroDivisible.ResetDrain
import Leader.Wu.ZeroDivisible.GroupPreparationWord
import Leader.Wu.ZeroDivisible.CompareBState
import Leader.Wu.Sim.RawCodec
import Lean.Data.Json

/-!
Source-exact finite replay of the fresh-reader silent-loss word.
Every eager array edge calls the production R5 pipeline on the physical pair;
every materialized successor is also compared with the actual
`PopulationProtocol.step` on its materialized predecessor.
The JSON result records all 23 full raw rows.
-/
namespace PPLLAstraR5FreshReaderWitness

open PPLL Lean

set_option autoImplicit false

def ring : DirectedRing 8 := ⟨by decide⟩

def cell (i : Fin 8) : AgentState 4 :=
  let j : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩
  let s : MainState :=
    match i.val with
    | 0 => .compare1 | 1 => .compare1 | 2 => .compare1 | 3 => .compare2
    | 4 => .compare1 | 5 => .depart | 6 => .equal | _ => .compare2
  { leader := false, probe := false, phase := false, bit := false,
    wait := false, state := s, path := .some j.val 0,
    reset := false, carry := false, count := 0,
    label := j, h_field := false,
    path2 := none, path3 := none, path4 := none, path5 := none,
    p := false, p_carry := false, reset_cmd := false, echo := false,
    signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩,
    shield := false, write_state := .none, write := .none,
    last := false, last_set := false, last_unset := false,
    b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }

def seed : Fin 8 → AgentState 4 := cell

instance : Inhabited (AgentState 4) := ⟨seed ⟨0, by decide⟩⟩

def sourceGroup : Fin 2 := ⟨0, by decide⟩
def targetGroup : Fin 2 := ⟨1, by decide⟩

private theorem role_cases {j : Nat} (hj : j < 4) :
    j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega

theorem seed_source_prepared :
    PPLLAstraR5PrepWord.Prepared (q:=2) (ψ:=4) ring sourceGroup seed seed := by
  unfold PPLLAstraR5PrepWord.Prepared PPLLAstraR5PrepWord.Frame
  constructor
  · intro j hj
    rcases role_cases hj with h | h | h | h <;>
      subst j <;> simp [PPLLAstraR5PrepWord.cell, seed, cell, sourceGroup]
  · constructor
    · intro j hj
      have h4 : j < 4 := by omega
      rcases role_cases h4 with h | h | h | h <;>
        subst j <;> simp [PPLLAstraR5PrepWord.cell, seed, cell, sourceGroup] at * <;> decide
    · simp [PPLLAstraR5PrepWord.cell, seed, cell, sourceGroup] <;> decide

theorem seed_target_B :
    ∀ j, j < 4 →
      let u := seed (PPLLAstraR5PrepWord.cell (q:=2) (ψ:=4) ring targetGroup j)
      u.label.val=j ∧ u.path=.some j 0 ∧ u.path2=none ∧
      PPLLAstraR5CompareB.BState 4 j u.state := by
  intro j hj
  rcases role_cases hj with h | h | h | h <;>
    subst j <;> simp [PPLLAstraR5PrepWord.cell, seed, cell,
      targetGroup, PPLLAstraR5CompareB.BState,
      PPLLAstraR5CompareB.HeadState,
      PPLLAstraR5CompareB.MidState,
      PPLLAstraR5CompareB.PenState] <;> decide

theorem seed_bounded : ∀ i : Fin 8, AgentState.inProtocolDomain 2 (seed i) := by
  intro ⟨i,hi⟩
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;>
    subst i <;> simp [seed, cell, AgentState.inProtocolDomain]

def edge (i : Nat) : Fin 8 := ⟨i % 8, Nat.mod_lt _ (by decide)⟩

def wordNat : List Nat :=
  [3,2,1,0,0,1,2,3,3,2,1,1,2,3,4,4,3,2,2,3,4,5]

def word : List (Fin 8) := wordNat.map edge

def row (selective : Bool) (k : Nat) : Fin 8 → AgentState 4 :=
  PPLLAstraR5ResetDrain.run (by decide : 0 < 4) 2
    { selective := selective } ring seed (word.take k)

def seedArray : Array (AgentState 4) :=
  ((List.range 8).map (fun i => seed (edge i))).toArray

def stepArray (selective : Bool) (a : Array (AgentState 4)) (e : Nat) :
    Array (AgentState 4) :=
  let l := a[e]!
  let r := a[(e+1)%8]!
  let z := PPLLAstraR5Repair.pipeline (by decide : 0 < 4) 2
    { selective := selective } l r
  (a.set! e z.1).set! ((e+1)%8) z.2

def trace (selective : Bool) : Array (Array (AgentState 4)) :=
  wordNat.foldl (fun rows e =>
    rows.push (stepArray selective rows[rows.size-1]! e)) #[seedArray]

def asConfig (a : Array (AgentState 4)) : Fin 8 → AgentState 4 :=
  fun i => a[i.val]!

def indices : List (Fin 8) := (List.range 8).map edge

def sameRaw (C D : Fin 8 → AgentState 4) : Bool :=
  indices.all (fun i =>
    PPLLSimRawCodec.encodeState (C i) == PPLLSimRawCodec.encodeState (D i))

def stepMatchesProtocol (selective : Bool)
    (a b : Array (AgentState 4)) (e : Nat) : Bool :=
  let protocol := PPLLAstraR5ResetDrain.protocol (by decide : 0 < 4) 2
    { selective := selective }
  sameRaw (asConfig b) (protocol.step ring (asConfig a) (edge e))

def leader (C : Fin 8 → AgentState 4) : Bool :=
  indices.any (fun i => (C i).leader)

def hole (C : Fin 8 → AgentState 4) : Bool :=
  indices.any (fun i => (C i).path == .bot)

def terminalE (C : Fin 8 → AgentState 4) : Bool :=
  indices.any (fun i => (C i).label.val + 1 == 4 &&
    (C i).state == MainState.eliminate_signal)

def tokenFree (C : Fin 8 → AgentState 4) : Bool :=
  indices.all (fun i => (C i).path2.isNone)

def tokenCount (C : Fin 8 → AgentState 4) : Nat :=
  (indices.filter (fun i => (C i).path2.isSome)).length

def indicated (C : Fin 8 → AgentState 4) (e : Nat) : Bool :=
  tokenCount C == 1 && indices.any (fun i =>
    match (C i).path2 with
    | none => false
    | some t =>
      if t.action == 1 || t.action == 4 then e == i.val
      else if t.action == 2 || t.action == 3 then e == (i.val+7)%8
      else false)

def fullOwn (C : Fin 8 → AgentState 4) : Bool :=
  indices.all (fun i =>
    (C i).label.val == i.val % 4 &&
    (match (C i).path with
      | .some j b => j == i.val % 4 && b ≤ 1
      | .bot => false))

def followers (C : Fin 8 → AgentState 4) : Bool :=
  indices.all (fun i => !(C i).leader)

def bStateB (j : Nat) (s : MainState) : Bool :=
  if j == 0 then s == .lock || s == .compare1
  else if j + 1 == 4 then s == .compare2
  else if j + 2 == 4 then
    s == .equal || s == .depart || s == .lock || s == .compare1
  else s == .depart || s == .lock || s == .compare1

def allB (C : Fin 8 → AgentState 4) : Bool :=
  indices.all (fun i => bStateB (i.val % 4) (C i).state)

def sourcePrepared : Bool :=
  (List.range 4).all (fun j =>
    (seed (edge j)).state ==
      (if j == 3 then MainState.compare2 else MainState.compare1) &&
    (seed (edge j)).path2.isNone) && fullOwn seed

def otherB : Bool :=
  (List.range 4).all (fun j =>
    bStateB j (seed (edge (j+4))).state &&
    (seed (edge (j+4))).path2.isNone)

def encodeRow (C : Fin 8 → AgentState 4) : Json :=
  Json.arr ((indices.map (fun i => PPLLSimRawCodec.encodeState (C i))).toArray)

def check (selective : Bool) : Json := Id.run do
  let rows := trace selective
  let prefixes := rows.toList.map asConfig
  let final := asConfig rows[rows.size-1]!
  let bootstrap := asConfig rows[1]!
  let milestones := [1,4,8,11,15,18,21,22]
  let milestoneRows := milestones.map (fun k =>
    Json.mkObj [
      ("k",toJson k),
      ("tokens",Json.arr ((indices.filter (fun i => ((asConfig rows[k]!) i).path2.isSome)).map
        (fun i => Json.mkObj [("site",toJson i.val),
          ("token",match ((asConfig rows[k]!) i).path2 with
            | none => Json.null
            | some t => toJson (t.label,t.bit,t.position,t.action))])).toArray)])
  return Json.mkObj [
    ("selective",toJson selective),
    ("word",toJson wordNat),
    ("word_length",toJson word.length),
    ("seed_bounded",toJson (indices.all (fun i => PPLLSimRawCodec.inProtocolDomainB 2 (seed i)))),
    ("source_prepared_shape",toJson sourcePrepared),
    ("other_B_tokenfree",toJson otherB),
    ("bootstrap_canonical_A2",toJson
      (tokenCount bootstrap == 1 &&
        (bootstrap (edge 3)).path2 ==
          some ⟨0,0,3,2⟩)),
    ("post_bootstrap_edges_indicated",toJson
      ((List.range (wordNat.length-1)).all (fun k =>
        indicated (asConfig rows[k+1]!) (wordNat.getD (k+1) 8)))),
    ("all_prefixes_no_leader",toJson (prefixes.all (fun C => !(leader C)))),
    ("all_prefixes_no_hole",toJson (prefixes.all (fun C => !(hole C)))),
    ("all_prefixes_no_terminal_E",toJson (prefixes.all (fun C => !(terminalE C)))),
    ("final_tokenfree",toJson (tokenFree final)),
    ("final_full_own",toJson (fullOwn final)),
    ("final_followers",toJson (followers final)),
    ("final_B",toJson (allB final)),
    ("all_steps_match_protocol_step",toJson
      ((List.range wordNat.length).all (fun k =>
        stepMatchesProtocol selective rows[k]! rows[k+1]!
          (wordNat.getD k 8)))),
    ("milestones",Json.arr milestoneRows.toArray),
    ("raw_rows",Json.arr ((prefixes.map encodeRow).toArray))]

def main : IO Unit := do
  let out := Json.arr #[check false, check true]
  IO.println out.compress

#check seed_bounded
#check seed_source_prepared
#check seed_target_B
#print axioms seed_bounded
#print axioms seed_source_prepared
#print axioms seed_target_B

end PPLLAstraR5FreshReaderWitness

def main : IO Unit := PPLLAstraR5FreshReaderWitness.main
