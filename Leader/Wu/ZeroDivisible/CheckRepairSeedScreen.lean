import Lean.Data.Json
import Leader.Wu.Sim.RawCodec
import Leader.Wu.ZeroDivisible.CheckRepair

/-!
Bounded, executable screen of the fixed R4 raw-state archive against both actual
R5 CHECK variants. This is not a reachability proof or a closed-trap census.
Each seed is decoded once per variant, immediate physical edges are tried until
the first target or exhaustion, and a fixed-seed UInt64 walk of at most `cap`
further rows is run if necessary.
-/

namespace PPLLAstraR5ArchiveScreen

open Lean PPLL

def stepArr {ψ : Nat} (hψ : 0 < ψ) (selective : Bool)
    (c : Array (AgentState ψ)) (edge : Nat) : Array (AgentState ψ) :=
  let n := c.size
  match c[edge]?, c[(edge + 1) % n]? with
  | some left, some right =>
      let (l, r) := PPLLAstraR5Repair.pipeline hψ 2
        { selective := selective } left right
      (c.set! edge l).set! ((edge + 1) % n) r
  | _, _ => c

def hasTarget {ψ : Nat} (c : Array (AgentState ψ)) : Bool :=
  c.any (fun u => u.leader || decide (u.path = .bot))

def isFull {ψ : Nat} (c : Array (AgentState ψ)) : Bool :=
  c.all (fun u => decide (u.path ≠ .bot))

def isAligned {ψ : Nat} (c : Array (AgentState ψ)) : Bool :=
  (List.range c.size).all fun i =>
    match c[i]? with
    | none => false
    | some u =>
        u.label.val == i % ψ &&
        match u.path with
        | .bot => false
        | .some label bit => label == i % ψ && bit <= 1

def isResetFree {ψ : Nat} (c : Array (AgentState ψ)) : Bool :=
  c.all (fun u => !u.reset_cmd)

def isLeaderless {ψ : Nat} (c : Array (AgentState ψ)) : Bool :=
  c.all (fun u => !u.leader)

def isBounded {ψ : Nat} (c : Array (AgentState ψ)) : Bool :=
  c.all (PPLLSimRawCodec.inProtocolDomainB 2)

structure Flags where
  full : Bool := false
  aligned : Bool := false
  resetFree : Bool := false
  leaderless : Bool := false
  bounded : Bool := false
  deriving Inhabited

def flags {ψ : Nat} (c : Array (AgentState ψ)) : Flags :=
  { full := isFull c, aligned := isAligned c, resetFree := isResetFree c
    leaderless := isLeaderless c, bounded := isBounded c }

structure Result where
  status : String
  word : Array Nat := #[]
  flags : Flags := {}
  deriving Inhabited

/-- A deterministic walk seed shared by both guard variants. -/
def walkSeed (ψ n index : Nat) : UInt64 :=
  (UInt64.ofNat (index * 1000003 + ψ * 8191 + n * 131 + 1)) ||| 1

def nextRng (rng : UInt64) : UInt64 :=
  let x := rng ^^^ (rng <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

def screen {ψ : Nat} (hψ : 0 < ψ) (selective : Bool)
    (n index cap : Nat) (seed : Array (AgentState ψ)) : Result := Id.run do
  let f := flags seed
  if seed.size != n || !f.bounded then
    return { status := "invalid", flags := f }
  if hasTarget seed then
    return { status := "initial_target", flags := f }
  for edge in [:n] do
    let next := stepArr hψ selective seed edge
    if hasTarget next then
      return { status := "one_step_target", word := #[edge], flags := f }
  let mut current := seed
  let mut rng := walkSeed ψ n index
  let mut word : Array Nat := #[]
  for _ in [:cap] do
    rng := nextRng rng
    let edge := (rng % UInt64.ofNat n).toNat
    current := stepArr hψ selective current edge
    word := word.push edge
    if hasTarget current then
      return { status := "multi_step_target", word := word, flags := f }
  return { status := "cap", word := word, flags := f }

structure Stats where
  total : Nat := 0
  invalid : Nat := 0
  initialTarget : Nat := 0
  oneStepTarget : Nat := 0
  multiStepTarget : Nat := 0
  cap : Nat := 0
  full : Nat := 0
  aligned : Nat := 0
  resetFree : Nat := 0
  leaderless : Nat := 0
  bounded : Nat := 0
  core : Nat := 0
  deriving Inhabited

def count (s : Stats) (r : Result) : Stats :=
  { total := s.total + 1
    invalid := s.invalid + if r.status == "invalid" then 1 else 0
    initialTarget := s.initialTarget + if r.status == "initial_target" then 1 else 0
    oneStepTarget := s.oneStepTarget + if r.status == "one_step_target" then 1 else 0
    multiStepTarget := s.multiStepTarget + if r.status == "multi_step_target" then 1 else 0
    cap := s.cap + if r.status == "cap" then 1 else 0
    full := s.full + if r.flags.full then 1 else 0
    aligned := s.aligned + if r.flags.aligned then 1 else 0
    resetFree := s.resetFree + if r.flags.resetFree then 1 else 0
    leaderless := s.leaderless + if r.flags.leaderless then 1 else 0
    bounded := s.bounded + if r.flags.bounded then 1 else 0
    core := s.core + if r.flags.full && r.flags.aligned &&
      r.flags.resetFree && r.flags.leaderless then 1 else 0 }

def statsJson (s : Stats) : Json := Json.mkObj
  [("total", toJson s.total), ("invalid", toJson s.invalid),
   ("initial_target", toJson s.initialTarget),
   ("one_step_target", toJson s.oneStepTarget),
   ("multi_step_target", toJson s.multiStepTarget), ("cap", toJson s.cap),
   ("initial_full", toJson s.full), ("initial_aligned", toJson s.aligned),
   ("initial_resetfree", toJson s.resetFree),
   ("initial_leaderless", toJson s.leaderless),
   ("initial_bounded", toJson s.bounded),
   ("initial_core", toJson s.core)]

def resultJson (index : Nat) (tag : String) (r : Result) : Json :=
  Json.mkObj
    [("index", toJson index), ("tag", toJson tag),
     ("status", toJson r.status), ("depth", toJson r.word.size),
     ("word", toJson (if r.status == "cap" then #[] else r.word)),
     ("word_omitted", toJson (r.status == "cap")),
     ("initial_full", toJson r.flags.full),
     ("initial_aligned", toJson r.flags.aligned),
     ("initial_resetfree", toJson r.flags.resetFree),
     ("initial_leaderless", toJson r.flags.leaderless),
     ("initial_bounded", toJson r.flags.bounded),
     ("initial_core", toJson (r.flags.full && r.flags.aligned &&
       r.flags.resetFree && r.flags.leaderless))]

def decodeSeed {ψ : Nat} (line : String) : Except String (Array (AgentState ψ)) := do
  let j ← Json.parse line
  let a ← j.getArr?
  a.mapM PPLLSimRawCodec.decodeState

def stratum (tag : String) : String :=
  (tag.splitOn ":").head!

def screenFile (selective : Bool) (ψ n cap : Nat)
    (seedPath metaPath outputPath : System.FilePath) : IO UInt32 := do
  if hψ : 0 < ψ then
    if n == 0 then
      IO.eprintln "n must be positive"
      return 2
    let input ← IO.FS.Handle.mk seedPath .read
    let metadata ← IO.FS.Handle.mk metaPath .read
    let output ← IO.FS.Handle.mk outputPath .write
    let mut all : Stats := {}
    let mut uniform : Stats := {}
    let mut mixed : Stats := {}
    let mut token : Stats := {}
    let mut random : Stats := {}
    let mut other : Stats := {}
    let mut index := 0
    repeat
      let line ← input.getLine
      if line.isEmpty then break
      let tag := (← metadata.getLine).trimAscii.toString
      let result : Result :=
        match decodeSeed (ψ := ψ) line with
        | .ok c => screen hψ selective n index cap c
        | .error _ => { status := "invalid" }
      output.putStrLn (resultJson index tag result).compress
      all := count all result
      match stratum tag with
      | "uniform" => uniform := count uniform result
      | "mixed" => mixed := count mixed result
      | "token" => token := count token result
      | "random" => random := count random result
      | _ => other := count other result
      index := index + 1
      if index % 10000 == 0 then
        IO.eprintln s!"screen ψ={ψ} n={n} selective={selective}: {index} seeds"
    let spare ← metadata.getLine
    if !spare.isEmpty then
      IO.eprintln "metadata has extra lines"
      return 2
    let summary := Json.mkObj
      [("psi", toJson ψ), ("n", toJson n), ("selective", toJson selective),
       ("walk_cap", toJson cap), ("all", statsJson all),
       ("uniform", statsJson uniform), ("mixed", statsJson mixed),
       ("token", statsJson token), ("random", statsJson random),
       ("other", statsJson other)]
    IO.println summary.compress
    return if all.invalid == 0 && other.total == 0 then 0 else 1
  else
    IO.eprintln "ψ must be positive"
    return 2

end PPLLAstraR5ArchiveScreen

open PPLLAstraR5ArchiveScreen in
def main (args : List String) : IO UInt32 := do
  match args with
  | [mode, ψ, n, cap, seedPath, metaPath, outputPath] =>
    match ψ.toNat?, n.toNat?, cap.toNat? with
    | some ψ, some n, some cap =>
      if mode != "selective" && mode != "broad" then
        IO.eprintln "mode must be selective or broad"
        return 2
      screenFile (mode == "selective") ψ n cap seedPath metaPath outputPath
    | _, _, _ => return 2
  | _ =>
    IO.eprintln "usage: MODE PSI N CAP SEEDS.jsonl META OUTPUT.jsonl"
    return 2
