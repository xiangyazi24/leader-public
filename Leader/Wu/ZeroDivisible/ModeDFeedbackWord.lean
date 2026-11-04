import Leader.Wu.ZeroDivisible.CheckRepair
import Leader.Wu.Sim.RawCodec
import Lean.Data.Json

/-! Executable, source-exact finite check of the feedback word.
The only varied fields are the source group's carried bits and target group's
resident bits. Every interaction calls the complete Candidate E pipeline. -/

set_option autoImplicit false
open Lean

namespace PPLLAstraR5ModeDWord

def bitAt (mask j : Nat) : Nat := (mask / 2^j) % 2

def getCell? {ψ : Nat} (a : Array (AgentState ψ)) (i : Nat) : Option (AgentState ψ) :=
  a[i]?

def initial (ψ q sourceBits targetBits : Nat) (hψ : ψ > 0) : Array (AgentState ψ) := Id.run do
  let n := q * ψ
  let mut a := #[]
  for i in [:n] do
    let j := i % ψ
    let group := i / ψ
    let carried := if group == 0 then bitAt sourceBits j else 0
    let resident := if group == q - 1 then bitAt targetBits j == 1 else false
    let state : MainState :=
      if j == 0 then .lock else if j == ψ - 1 then .compare2
      else if j == ψ - 2 then .equal else .depart
    a := a.push {
      leader := false, probe := false, phase := false, bit := resident,
      wait := false, state := state, path := .some j carried,
      reset := false, carry := false, count := 0,
      label := ⟨j, Nat.mod_lt i hψ⟩, h_field := false,
      path2 := none, path3 := none, path4 := none, path5 := none,
      p := false, p_carry := false, reset_cmd := false, echo := false,
      signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩,
      shield := false, write_state := .none, write := .none,
      last := false, last_set := false, last_unset := false,
      b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }
  return a

def target {ψ : Nat} (a : Array (AgentState ψ)) : String :=
  if a.any (fun u => u.leader) then "leader"
  else if a.any (fun u => u.path == .bot) then "hole"
  else "none"

def wave {ψ : Nat} (a : Array (AgentState ψ)) (h ψn : Nat) : Bool :=
  (List.range ψn).all fun j =>
    match getCell? a (h+j) with
    | none => false
    | some u => u.state == (if j == ψn-1 then .compare2 else .compare1) &&
        (match u.path with | .some label bit => label == j && bit ≤ 1 | .bot => false)

def tokenCount {ψ : Nat} (a : Array (AgentState ψ)) : Nat :=
  a.foldl (fun k u => k + if u.path2.isSome then 1 else 0) 0

def checkpoint {ψ : Nat} (a : Array (AgentState ψ)) (p h ψn j sourceBits : Nat) : Bool :=
  wave a h ψn && tokenCount a == 1 &&
  (getCell? a (p+j)).bind (fun u => u.path2) == some {
    label := j, bit := bitAt sourceBits j, position := ψn, action := 1 } &&
  a.all (fun u => u.path != .bot)

structure Run (ψ : Nat) where
  row : Array (AgentState ψ)
  word : Array Nat := #[]
  status : String := "running"
  failure : String := ""
  checks : Nat := 0
  phase : String := "initial"
  stopPhase : String := ""
  verdictAction : Nat := 0

def fail {ψ : Nat} (r : Run ψ) (msg : String) : Run ψ :=
  if r.status == "running" then { r with status := "checkpoint_failure", failure := msg } else r

def expect {ψ : Nat} (r : Run ψ) (b : Bool) (msg : String) : Run ψ :=
  if b then { r with checks := r.checks + 1 } else fail r msg

def step {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg)
    (r : Run ψ) (e : Nat) : Run ψ := Id.run do
  if r.status != "running" then return r
  let n := r.row.size
  let some l := getCell? r.row e | return fail r s!"bad_edge_{e}"
  let some rr := getCell? r.row ((e+1)%n) | return fail r s!"bad_successor_{e}"
  let out := PPLLAstraR5Repair.pipeline hψ κ c l rr
  let a := (r.row.set! e out.1).set! ((e+1)%n) out.2
  let t := target a
  let updated : Run ψ := { r with row := a }
  let updated : Run ψ := { updated with word := updated.word.push e }
  let updated : Run ψ := { updated with status := (if t == "none" then "running" else t) }
  return { updated with stopPhase := (if t == "none" then "" else r.phase) }

def runCase (ψ q κ sourceBits targetBits : Nat) (selective : Bool)
    (hψ : ψ > 0) : Run ψ := Id.run do
  let h := (q-1)*ψ
  let p := 0
  let l := ψ-1
  let c : PPLLAstraR5Repair.Cfg := { selective := selective }
  let mut r : Run ψ := { row := initial ψ q sourceBits targetBits hψ }
  if !(r.row.all (PPLLSimRawCodec.inProtocolDomainB κ)) then
    return fail r "initial_domain"
  -- Release, propagate lock, convert terminal predecessor, acknowledge back.
  r := { r with phase := "prepare" }
  r := step hψ κ c r (h+l-1)
  for j in [:l-1] do r := step hψ κ c r (h+j)
  r := step hψ κ c r (h+l-1)
  for k in [:l-1] do r := step hψ κ c r (h+l-2-k)
  r := expect r (wave r.row h ψ && tokenCount r.row == 0) "W(H)"
  -- Boundary re-emission and the leftward return to C_0.
  r := { r with phase := "emit_return" }
  r := step hψ κ c r (p+l)
  for k in [:l] do r := step hψ κ c r (p+l-1-k)
  r := expect r (checkpoint r.row p h ψ 0 sourceBits) "C_0"
  for j in [:ψ] do
    if r.status != "running" then break
    -- F_j has exactly ψ directed interactions.
    r := { r with phase := s!"forward_{j}" }
    for x in [j:ψ] do r := step hψ κ c r (p+x)
    for x in [:j] do r := step hψ κ c r (h+x)
    if r.status != "running" then break
    let s := bitAt sourceBits j
    let b := bitAt targetBits j
    if s == b then
      if j == l then
        r := fail r "terminal_equal_no_leader"
      else
        r := expect r (wave r.row h ψ && tokenCount r.row == 1 &&
          (getCell? r.row (h+j)).bind (fun u => u.path2) == some {
            label := j+1, bit := 0, position := l, action := 2 })
          s!"A2_after_F_{j}"
        r := { r with phase := s!"backward_{j}" }
        for k in [:j] do r := step hψ κ c r (h+j-1-k)
        for k in [:l-j] do r := step hψ κ c r (p+l-k)
        r := expect r (checkpoint r.row p h ψ (j+1) sourceBits) s!"C_{j+1}"
    else
      let action := if s > b then 4 else 3
      r := { r with verdictAction := action }
      r := expect r (tokenCount r.row == 1 &&
        ((getCell? r.row (h+j)).bind (fun u => u.path2)).map (fun t => t.action) == some action)
        s!"A{action}_after_F_{j}"
      if r.status != "running" then break
      let terminal := if action == 4 || j == l then h+l else p+l
      r := { r with phase := s!"discharge_A{action}_{j}" }
      if j == l then
        r := step hψ κ c r (h+l-1)
      else if action == 4 then
        for x in [j:l] do r := step hψ κ c r (h+x)
      else
        for k in [:j] do r := step hψ κ c r (h+j-1-k)
        r := step hψ κ c r (p+l)
      r := expect r ((getCell? r.row terminal).map (fun u => u.state) == some .eliminate_signal)
        s!"eliminate_A{action}_j{j}"
      r := { r with phase := s!"hole_A{action}_{j}" }
      r := step hψ κ c r (terminal-1)
      if r.status == "running" then r := fail r s!"A{action}_no_hole_j{j}"
      break
  if r.status == "running" then r := fail r "word_end_no_target"
  return r

def resultJson {ψ : Nat} (hψ : ψ > 0) (q κ s b : Nat) (selective : Bool)
    (r : Run ψ) : Json := Json.mkObj [
  ("psi", toJson ψ), ("q", toJson q), ("kappa", toJson κ),
  ("selective", toJson selective), ("source_bits", toJson s),
  ("target_bits", toJson b), ("status", toJson r.status),
  ("failure", toJson r.failure), ("checks", toJson r.checks),
  ("stop_phase", toJson r.stopPhase),
  ("verdict_action", toJson r.verdictAction),
  ("length", toJson r.word.size), ("word", toJson r.word),
  ("initial", Json.arr ((initial ψ q s b hψ).map PPLLSimRawCodec.encodeState)),
  ("endpoint", Json.arr (r.row.map PPLLSimRawCodec.encodeState)) ]

def runAll (ψ q κ : Nat) (cs out : String) (hψ : ψ > 0) : IO UInt32 := do
  if ψ < 4 || (q != 1 && q != 2) then throw (IO.userError "require PSI>=4,Q=1|2")
  let selective := cs == "selective"
  if cs != "selective" && cs != "broad" then throw (IO.userError "bad guard")
  let mut counts : List (String × Nat) := []
  let mut firstFail : Option Json := none
  let mut firstLeader : Option Json := none
  let mut firstHole : Option Json := none
  let mut maxLength := 0
  let mut maxChecks := 0
  let mut earlyHoles := 0
  let mut equalLeader := 0
  let mut equalLengthBad := 0
  let mut overBound := 0
  let mut a3 := 0
  let mut a4 := 0
  let mut firstA3 : Option Json := none
  let mut firstA4 : Option Json := none
  let mut firstEarlyHole : Option Json := none
  let mut stopPhases : List (String × Nat) := []
  for s in [:2^ψ] do
    for b in [:2^ψ] do
      let mut r := runCase ψ q κ s b selective hψ
      if r.word.size > 2*ψ*ψ+ψ+1 then
        r := { r with status := "checkpoint_failure", failure := "length_over_bound" }
      if s == b && (r.status != "leader" || r.word.size != 2*ψ*ψ+ψ-1) then
        r := { r with status := "checkpoint_failure", failure := "equal_word_claim" }
      counts := (r.status, (counts.lookup r.status).getD 0 + 1) :: counts.filter (fun x => x.1 != r.status)
      stopPhases := (r.stopPhase, (stopPhases.lookup r.stopPhase).getD 0 + 1) ::
        stopPhases.filter (fun x => x.1 != r.stopPhase)
      maxLength := max maxLength r.word.size
      maxChecks := max maxChecks r.checks
      if r.word.size > 2*ψ*ψ+ψ+1 then overBound := overBound + 1
      if r.status == "hole" && !(r.stopPhase.startsWith "hole_A") then
        earlyHoles := earlyHoles + 1
        if firstEarlyHole.isNone then firstEarlyHole := some (resultJson hψ q κ s b selective r)
      if r.verdictAction == 3 then
        a3 := a3 + 1
        if firstA3.isNone then firstA3 := some (resultJson hψ q κ s b selective r)
      if r.verdictAction == 4 then
        a4 := a4 + 1
        if firstA4.isNone then firstA4 := some (resultJson hψ q κ s b selective r)
      if s == b && r.status == "leader" then
        equalLeader := equalLeader + 1
        if r.word.size != 2*ψ*ψ+ψ-1 then equalLengthBad := equalLengthBad + 1
      if r.status == "checkpoint_failure" && firstFail.isNone then
        firstFail := some (resultJson hψ q κ s b selective r)
      if r.status == "leader" && firstLeader.isNone then
        firstLeader := some (resultJson hψ q κ s b selective r)
      if r.status == "hole" && firstHole.isNone then
        firstHole := some (resultJson hψ q κ s b selective r)
  let receipt := Json.mkObj [
    ("psi", toJson ψ), ("q", toJson q), ("kappa", toJson κ),
    ("selective", toJson selective), ("seeds", toJson (2^ψ * 2^ψ)),
    ("counts", Json.mkObj (counts.map fun (k,v) => (k, toJson v))),
    ("max_length", toJson maxLength), ("max_checks", toJson maxChecks),
    ("stop_phases", Json.mkObj (stopPhases.map fun (k,v) => (k, toJson v))),
    ("a3_cases", toJson a3), ("a4_cases", toJson a4),
    ("early_holes", toJson earlyHoles), ("equal_leaders", toJson equalLeader),
    ("equal_length_bad", toJson equalLengthBad), ("over_bound", toJson overBound),
    ("claimed_equal_length", toJson (2*ψ*ψ+ψ-1)),
    ("claimed_upper_bound", toJson (2*ψ*ψ+ψ+1)),
    ("first_failure", firstFail.getD Json.null),
    ("first_a3", firstA3.getD Json.null), ("first_a4", firstA4.getD Json.null),
    ("first_early_hole", firstEarlyHole.getD Json.null),
    ("first_leader", firstLeader.getD Json.null),
    ("first_hole", firstHole.getD Json.null) ]
  IO.FS.writeFile out receipt.compress
  IO.println s!"psi={ψ} q={q} kappa={κ} selective={selective} counts={counts} max_length={maxLength}"
  return if firstFail.isSome then 1 else 0

def main (args : List String) : IO UInt32 := do
  let [ψs, qs, κs, cs, out] := args | throw (IO.userError "usage: PSI Q KAPPA selective|broad OUT.json")
  let some ψ := ψs.toNat? | throw (IO.userError "bad PSI")
  let some q := qs.toNat? | throw (IO.userError "bad Q")
  let some κ := κs.toNat? | throw (IO.userError "bad KAPPA")
  if hψ : ψ > 0 then runAll ψ q κ cs out hψ
  else throw (IO.userError "PSI must be positive")

end PPLLAstraR5ModeDWord

def main (args : List String) : IO UInt32 := PPLLAstraR5ModeDWord.main args
