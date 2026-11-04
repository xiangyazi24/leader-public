import Leader.Wu.ZeroDivisible.CheckRepair
import Leader.Wu.Sim.RawCodec
import Lean.Data.Json

/-! Finite one-reader feedback validator. Every edge uses the full
Candidate-E pipeline. This executable does not prove arbitrary-ψ liveness. -/

set_option autoImplicit false
open Lean

namespace PPLLAstraR5OneReader

def at? {ψ : Nat} (a : Array (AgentState ψ)) (i : Nat) : Option (AgentState ψ) := a[i]?

def seed (ψ q holder action label bit position pattern : Nat)
    (hψ : ψ > 0) : Array (AgentState ψ) := Id.run do
  let n := q*ψ
  let mut a := #[]
  for i in [:n] do
    let j := i % ψ
    let st : MainState := if j == 0 then .lock
      else if j == ψ-1 then .compare2
      else if j == ψ-2 then .equal else .depart
    let carryBit := if pattern == 0 then 0 else i % 2
    let resident := pattern != 0 && (i+1)%2 == 1
    let token : Option Path2Info := if i == holder then
      some { label := label, bit := bit, position := position, action := action }
      else none
    a := a.push {
      leader := false, probe := false, phase := false, bit := resident,
      wait := false, state := st, path := .some j carryBit,
      reset := false, carry := false, count := 0,
      label := ⟨j, Nat.mod_lt i hψ⟩, h_field := false,
      path2 := token, path3 := none, path4 := none, path5 := none,
      p := false, p_carry := false, reset_cmd := false, echo := false,
      signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩,
      shield := false, write_state := .none, write := .none,
      last := false, last_set := false, last_unset := false,
      b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }
  return a

def target {ψ : Nat} (a : Array (AgentState ψ)) : String :=
  if a.any (fun u => u.leader) then "leader"
  else if a.any (fun u => u.path == .bot) then "hole"
  else "running"

def liveToken {ψ : Nat} (a : Array (AgentState ψ)) : Option (Nat × Path2Info) := Id.run do
  for i in [:a.size] do
    if let some t := (at? a i).bind (fun u => u.path2) then return some (i,t)
  return none

def tokenCount {ψ : Nat} (a : Array (AgentState ψ)) : Nat :=
  a.foldl (fun z u => z + if u.path2.isSome then 1 else 0) 0

def basin {ψ : Nat} (ψn : Nat) (a : Array (AgentState ψ)) : Bool :=
  a.all fun u =>
    let j := u.label.val
    let aligned := match u.path with
      | .some label bit => label == j && bit ≤ 1
      | .bot => false
    let stateOK :=
      if j == 0 then u.state == .lock || u.state == .compare1
      else if j == ψn-1 then u.state == .compare2
      else if j == ψn-2 then u.state == .equal || u.state == .depart ||
        u.state == .lock || u.state == .compare1
      else u.state == .depart || u.state == .lock || u.state == .compare1
    aligned && stateOK && !u.leader

def wave {ψ : Nat} (a : Array (AgentState ψ)) (g ψn : Nat) : Bool :=
  (List.range ψn).all fun j =>
    match at? a (g+j) with
    | none => false
    | some u => u.state == (if j == ψn-1 then .compare2 else .compare1) &&
        (match u.path with | .some label bit => label == j && bit ≤ 1 | .bot => false)

def rank (ψ : Nat) (t : Path2Info) : Nat :=
  (2*ψ-1)*(ψ-1-t.label) + t.position + (if t.action == 2 then ψ else 0) + 1

structure Run (ψ : Nat) where
  row : Array (AgentState ψ)
  word : Array Nat := #[]
  status : String := "running"
  failure : String := ""
  phase : String := "initial"
  stopPhase : String := ""
  checks : Nat := 0
  rankChecks : Nat := 0
  readerSteps : Nat := 0
  verdictAction : Nat := 0

def fail {ψ : Nat} (r : Run ψ) (msg : String) : Run ψ :=
  if r.status == "running" then { r with status := "checkpoint_failure", failure := msg } else r

def expect {ψ : Nat} (r : Run ψ) (ok : Bool) (msg : String) : Run ψ :=
  if r.status != "running" then r
  else if ok then { r with checks := r.checks + 1 }
  else fail r msg

def step {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (c : PPLLAstraR5Repair.Cfg) (r : Run ψ) (e : Nat) : Run ψ := Id.run do
  if r.status != "running" then return r
  let n := r.row.size
  let some l := at? r.row e | return fail r s!"bad_edge_{e}"
  let some rr := at? r.row ((e+1)%n) | return fail r s!"bad_successor_{e}"
  let v := PPLLAstraR5Repair.pipeline hψ κ c l rr
  let a := (r.row.set! e v.1).set! ((e+1)%n) v.2
  let t := target a
  let next : Run ψ := { r with row := a }
  let next : Run ψ := { next with word := next.word.push e }
  let next : Run ψ := { next with status := t }
  return { next with stopPhase := if t == "running" then "" else r.phase }

def setPhase {ψ : Nat} (r : Run ψ) (s : String) : Run ψ := { r with phase := s }

def dispose {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (c : PPLLAstraR5Repair.Cfg) (ψn : Nat) (r0 : Run ψ) : Run ψ := Id.run do
  let mut r := setPhase r0 "dispose"
  let n := r.row.size
  for _ in [:ψn+3] do
    if r.status != "running" then break
    -- A destination already in eliminate_signal needs its incoming edge.
    let mut terminal : Option Nat := none
    for i in [:n] do
      if i % ψn == ψn-1 && ((at? r.row i).map (fun u => u.state) == some .eliminate_signal) then
        terminal := some i
        break
    if let some t := terminal then
      if r.row.any (fun u => u.state == .produce) then
        return fail r "produce_before_terminal_drain"
      r := step hψ κ c r ((t+n-1)%n)
      if r.status == "running" then r := fail r "terminal_drain_failed"
      break
    match liveToken r.row with
    | none =>
      r := fail r "verdict_lost_without_target"
      break
    | some (holder,t) =>
      if tokenCount r.row != 1 || !(t.action == 3 || t.action == 4) then
        r := fail r "dispose_token_shape"
        break
      let e := if t.action == 4 && holder % ψn != ψn-1 then holder
        else (holder+n-1)%n
      r := step hψ κ c r e
  if r.status == "running" then r := fail r "dispose_exhausted"
  return r

def normGroup {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (c : PPLLAstraR5Repair.Cfg) (ψn g : Nat) (r0 : Run ψ) : Run ψ := Id.run do
  let l := ψn-1
  let mut r := setPhase r0 s!"normalize_{g}"
  r := step hψ κ c r (g+l-1)
  r := expect r (tokenCount r.row == 0) s!"T_token_free_{g}_start"
  for j in [:l-1] do
    r := step hψ κ c r (g+j)
    r := expect r (tokenCount r.row == 0) s!"T_token_free_{g}_forward_{j}"
  r := step hψ κ c r (g+l-1)
  r := expect r (tokenCount r.row == 0) s!"T_token_free_{g}_terminal"
  for k in [:l-1] do
    r := step hψ κ c r (g+l-2-k)
    r := expect r (tokenCount r.row == 0) s!"T_token_free_{g}_reverse_{k}"
  r := expect r (wave r.row g ψn && tokenCount r.row == 0) s!"W_{g}"
  return r

def serial (ψ q κ : Nat) (hψ : ψ > 0)
    (c : PPLLAstraR5Repair.Cfg) (r0 : Run ψ) : Run ψ := Id.run do
  let p := 0
  let h := if q == 1 then 0 else ψ
  let l := ψ-1
  let mut r := r0
  for j in [:ψ] do
    if r.status != "running" then break
    r := setPhase r s!"forward_{j}"
    for x in [j:ψ] do
      r := step hψ κ c r (p+x)
      r := expect r (wave r.row p ψ && wave r.row h ψ && tokenCount r.row == 1)
        s!"forward_frame_{j}_{x}"
    for x in [:j] do
      r := step hψ κ c r (h+x)
      r := expect r (wave r.row p ψ && wave r.row h ψ && tokenCount r.row == 1)
        s!"forward_frame_{j}_H{x}"
    if r.status != "running" then break
    let some u := at? r.row (h+j) | return fail r s!"missing_H_{j}"
    let some t := u.path2 | return fail r s!"missing_landing_{j}"
    if t.action == 2 && j < l then
      r := expect r (t.label == j+1 && t.position == l && tokenCount r.row == 1)
        s!"A2_after_F_{j}"
      r := setPhase r s!"backward_{j}"
      for k in [:j] do
        r := step hψ κ c r (h+j-1-k)
        r := expect r (wave r.row p ψ && wave r.row h ψ && tokenCount r.row == 1)
          s!"backward_frame_{j}_H{k}"
      for k in [:l-j] do
        r := step hψ κ c r (p+l-k)
        r := expect r (wave r.row p ψ && wave r.row h ψ && tokenCount r.row == 1)
          s!"backward_frame_{j}_P{k}"
      let some src := at? r.row (p+j+1) | return fail r "missing_source"
      let payload := match src.path with | .some _ b => b | .bot => 2
      let expected : Path2Info := { label := j+1, bit := payload, position := ψ, action := 1 }
      r := expect r (src.path2 == some expected) s!"C_{j+1}"
    else if t.action == 3 || t.action == 4 then
      r := { r with verdictAction := t.action }
      r := dispose hψ κ c ψ r
      break
    else
      r := fail r s!"unexpected_landing_{j}_A{t.action}"
      break
  if r.status == "running" then r := fail r "serial_no_target"
  return r

def runCase (ψ q κ holder action label bit position pattern : Nat)
    (selective : Bool) (hψ : ψ > 0) : Run ψ := Id.run do
  let p := 0
  let h := if q == 1 then 0 else ψ
  let l := ψ-1
  let c : PPLLAstraR5Repair.Cfg := { selective := selective }
  let a := seed ψ q holder action label bit position pattern hψ
  let mut r : Run ψ := { row := a }
  if !(a.all (PPLLSimRawCodec.inProtocolDomainB κ)) then return fail r "initial_domain"
  r := expect r (basin ψ a && tokenCount a == 1) "initial_basin_reader"
  -- Normalize the one arbitrary reader by the actual whole-row token result.
  for _ in [:2*ψ*ψ-ψ+3] do
    if r.status != "running" then break
    let some (holder,t) := liveToken r.row | break
    if !(t.action == 1 || t.action == 2) then break
    let oldRank := rank ψ t
    let n := r.row.size
    let e := if t.action == 1 then holder else (holder+n-1)%n
    r := setPhase r "reader"
    r := step hψ κ c r e
    r := { r with readerSteps := r.readerSteps+1 }
    if r.status != "running" then break
    r := expect r (basin ψ r.row) "reader_basin"
    r := expect r (tokenCount r.row ≤ 1) "reader_unique"
    if r.status != "running" then break
    match liveToken r.row with
    | none => break
    | some (_,next) =>
      if next.action == 1 || next.action == 2 then
        r := expect r (next.label < ψ && rank ψ next < oldRank)
          s!"rank_{oldRank}_to_{rank ψ next}"
        r := { r with rankChecks := r.rankChecks+1 }
      else if next.action == 3 || next.action == 4 then break
      else r := fail r s!"reader_bad_action_{next.action}"
  if r.status != "running" then return r
  match liveToken r.row with
  | some (_,t) =>
    if t.action == 3 || t.action == 4 then
      r := { r with verdictAction := t.action }
      return dispose hψ κ c ψ r
    return fail r "reader_rank_exhausted"
  | none => pure ()
  r := normGroup hψ κ c ψ p r
  if q != 1 then r := normGroup hψ κ c ψ h r
  if r.status != "running" then return r
  r := setPhase r "bootstrap"
  r := step hψ κ c r (p+l)
  let expectedA2 : Path2Info := { label := 0, bit := 0, position := l, action := 2 }
  r := expect r (tokenCount r.row == 1 &&
    (at? r.row (p+l)).bind (fun u => u.path2) == some expectedA2 &&
    wave r.row p ψ && wave r.row h ψ) "emit_A2"
  for k in [:l] do
    r := step hψ κ c r (p+l-1-k)
    r := expect r (wave r.row p ψ && wave r.row h ψ && tokenCount r.row == 1)
      s!"return_A2_{k}"
  let some src := at? r.row p | return fail r "missing_P0"
  let payload := match src.path with | .some _ b => b | .bot => 2
  let expectedA1 : Path2Info := { label := 0, bit := payload, position := ψ, action := 1 }
  r := expect r (src.path2 == some expectedA1) "C0"
  if r.status == "running" then r := serial ψ q κ hψ c r
  return r

def caseJson (ψ q κ holder action label bit position pattern : Nat)
    (selective : Bool) (hψ : ψ > 0) (r : Run ψ) : Json := Json.mkObj [
  ("psi", toJson ψ), ("q", toJson q), ("kappa", toJson κ),
  ("selective", toJson selective), ("holder", toJson holder),
  ("action", toJson action), ("label", toJson label),
  ("bit", toJson bit), ("position", toJson position),
  ("pattern", toJson pattern), ("status", toJson r.status),
  ("failure", toJson r.failure), ("stop_phase", toJson r.stopPhase),
  ("length", toJson r.word.size), ("word", toJson r.word),
  ("checks", toJson r.checks), ("rank_checks", toJson r.rankChecks),
  ("reader_steps", toJson r.readerSteps),
  ("verdict_action", toJson r.verdictAction),
  ("seed", Json.arr ((seed ψ q holder action label bit position pattern hψ).map
    PPLLSimRawCodec.encodeState)),
  ("endpoint", Json.arr (r.row.map PPLLSimRawCodec.encodeState)) ]

def runAll (ψ q κ pattern : Nat) (selective : Bool)
    (hψ : ψ > 0) (out : String) : IO UInt32 := do
  let mut counts : List (String × Nat) := []
  let mut phases : List (String × Nat) := []
  let mut maxLength := 0
  let mut maxReader := 0
  let mut rankChecks := 0
  let mut firstFailure : Option Json := none
  let mut firstLeader : Option Json := none
  let mut firstHole : Option Json := none
  let mut cases := #[]
  for holder in [:q*ψ] do
    for action in [1:3] do
      for label in [:ψ] do
        for bit in [:2] do
          for position in [:ψ+1] do
            let mut r := runCase ψ q κ holder action label bit position pattern selective hψ
            let bound := if q == 1 then 4*ψ*ψ+ψ+2 else 4*ψ*ψ+3*ψ
            if r.word.size > bound then
              let rr : Run ψ := { r with status := "checkpoint_failure" }
              r := { rr with failure := "length_over_bound" }
            counts := (r.status, (counts.lookup r.status).getD 0+1) ::
              counts.filter (fun x => x.1 != r.status)
            phases := (r.stopPhase, (phases.lookup r.stopPhase).getD 0+1) ::
              phases.filter (fun x => x.1 != r.stopPhase)
            maxLength := max maxLength r.word.size
            maxReader := max maxReader r.readerSteps
            rankChecks := rankChecks + r.rankChecks
            cases := cases.push (Json.mkObj [
              ("holder", toJson holder), ("action", toJson action),
              ("label", toJson label), ("bit", toJson bit),
              ("position", toJson position), ("status", toJson r.status),
              ("failure", toJson r.failure), ("length", toJson r.word.size),
              ("reader_steps", toJson r.readerSteps) ])
            let j := caseJson ψ q κ holder action label bit position pattern selective hψ r
            if r.status == "checkpoint_failure" &&
                (firstFailure.isNone ||
                  r.word.size < ((firstFailure.getD Json.null).getObjValAs? Nat "length").toOption.getD 100000) then
              firstFailure := some j
            if r.status == "leader" && firstLeader.isNone then firstLeader := some j
            if r.status == "hole" && firstHole.isNone then firstHole := some j
  let receipt := Json.mkObj [
    ("psi", toJson ψ), ("q", toJson q), ("kappa", toJson κ),
    ("selective", toJson selective), ("pattern", toJson pattern),
    ("seeds", toJson cases.size),
    ("counts", Json.mkObj (counts.map fun (k,v) => (k,toJson v))),
    ("stop_phases", Json.mkObj (phases.map fun (k,v) => (k,toJson v))),
    ("max_length", toJson maxLength), ("max_reader_steps", toJson maxReader),
    ("rank_checks", toJson rankChecks),
    ("bound", toJson (if q == 1 then 4*ψ*ψ+ψ+2 else 4*ψ*ψ+3*ψ)),
    ("first_failure", firstFailure.getD Json.null),
    ("first_leader", firstLeader.getD Json.null),
    ("first_hole", firstHole.getD Json.null),
    ("cases", Json.arr cases) ]
  IO.FS.writeFile out receipt.compress
  IO.println s!"psi={ψ} q={q} kappa={κ} selective={selective} pattern={pattern} cases={cases.size} counts={counts} max={maxLength}"
  return if firstFailure.isSome then 1 else 0

def main (args : List String) : IO UInt32 := do
  let [ψs, qs, κs, cs, ps, out] := args |
    throw (IO.userError "usage: PSI Q KAPPA selective|broad PATTERN OUT.json")
  let some ψ := ψs.toNat? | throw (IO.userError "bad PSI")
  let some q := qs.toNat? | throw (IO.userError "bad Q")
  let some κ := κs.toNat? | throw (IO.userError "bad KAPPA")
  let some pattern := ps.toNat? | throw (IO.userError "bad PATTERN")
  if ψ < 4 || q == 0 || pattern > 1 then throw (IO.userError "bad ψ/q/pattern")
  if cs != "selective" && cs != "broad" then throw (IO.userError "bad guard")
  if hψ : ψ > 0 then runAll ψ q κ pattern (cs == "selective") hψ out
  else throw (IO.userError "ψ=0")

end PPLLAstraR5OneReader

def main (args : List String) : IO UInt32 := PPLLAstraR5OneReader.main args
