import Leader.Wu.ZeroDivisible.CheckRepair
import Leader.Wu.Sim.RawCodec
import Lean.Data.Json

namespace PPLLAstraR5DebrisBase

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

end PPLLAstraR5DebrisBase


/-! Finite exact-pipeline test of the drain-augmented Mode-D word.
This is an executable probe, not a proof of the arbitrary-debris claim. -/

set_option autoImplicit false
open Lean

namespace PPLLAstraR5ModeDDebris

open PPLLAstraR5DebrisBase

def miniSeed : Array (AgentState 4) := Id.run do
  let a := initial 4 1 0 0 (by decide)
  let some u1 := a[1]? | return a
  let some u2 := a[2]? | return a
  let some u3 := a[3]? | return a
  return ((a.set! 1 { u1 with p_carry := true }).set! 2 { u2 with p := true }).set! 3 { u3 with p := true }

def coreJson {ψ : Nat} (a : Array (AgentState ψ)) : Json :=
  Json.arr <| a.map fun u => Json.mkObj [
    ("state", toJson (toString (repr u.state))),
    ("path", PPLLSimRawCodec.encodeState u |>.getObjValAs? Json "path" |>.toOption |>.getD Json.null),
    ("leader", toJson u.leader), ("p", toJson u.p),
    ("p_carry", toJson u.p_carry),
    ("path2", PPLLSimRawCodec.encodeState u |>.getObjValAs? Json "path2" |>.toOption |>.getD Json.null) ]

def miniReceipt (selective : Bool) : Json := Id.run do
  let c : PPLLAstraR5Repair.Cfg := { selective := selective }
  let mut r : Run 4 := { row := miniSeed }
  let mut prefixes := #[coreJson r.row]
  for e in #[2, 0, 1, 2] do
    r := step (by decide) 0 c r e
    prefixes := prefixes.push (coreJson r.row)
  let r4 := r
  let penultimateCheck :=
    ((getCell? r4.row 2).map (fun u => u.state) == some .compare1) &&
    ((getCell? r4.row 3).map (fun u => u.state) == some .compare2)
  let r5 := step (by decide) 0 c r4 2
  prefixes := prefixes.push (coreJson r5.row)
  let r6 := step (by decide) 0 c (step (by decide) 0 c r4 1) 0
  return Json.mkObj [
    ("selective", toJson selective), ("initial", Json.arr (miniSeed.map PPLLSimRawCodec.encodeState)),
    ("word_four", toJson (#[2,0,1,2] : Array Nat)),
    ("status_four", toJson r4.status), ("penultimate_check_four", toJson penultimateCheck),
    ("after_four", Json.arr (r4.row.map PPLLSimRawCodec.encodeState)),
    ("word_six", toJson r6.word), ("status_six", toJson r6.status),
    ("wave_six", toJson (wave r6.row 0 4)),
    ("after_six", Json.arr (r6.row.map PPLLSimRawCodec.encodeState)),
    ("word_five", toJson r5.word), ("status_five", toJson r5.status),
    ("after_five", Json.arr (r5.row.map PPLLSimRawCodec.encodeState)),
    ("trace_core", Json.arr prefixes) ]

def drainCounterReceipt (selective : Bool) : Json := Id.run do
  let a := initial 4 1 0 0 (by decide)
  let some u2 := a[2]? | return Json.null
  let some u3 := a[3]? | return Json.null
  let seed := (a.set! 2 { u2 with state := .produce }).set! 3
    { u3 with state := .eliminate_signal }
  let c : PPLLAstraR5Repair.Cfg := { selective := selective }
  let r := step (by decide) 0 c ({ row := seed } : Run 4) 2
  return Json.mkObj [
    ("selective", toJson selective),
    ("seed", Json.arr (seed.map PPLLSimRawCodec.encodeState)),
    ("word", toJson r.word), ("status", toJson r.status),
    ("endpoint", Json.arr (r.row.map PPLLSimRawCodec.encodeState)),
    ("core", coreJson r.row) ]

def mix64 (x : UInt64) : UInt64 :=
  let x := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
  let x := (x ^^^ (x >>> 27)) * 0x94d049bb133111eb
  x ^^^ (x >>> 31)

def pseudo (seed : Nat) : Nat :=
  (mix64 (seed.toUInt64 + 0x9e3779b97f4a7c15)).toNat
def flip (seed : Nat) : Bool := pseudo seed % 2 == 1
def pick (seed n : Nat) : Nat := pseudo seed % n

def varied (ψ q κ s b sample : Nat) (stratum : String)
    (hψ : ψ > 0) : Array (AgentState ψ) := Id.run do
  let mut a := initial ψ q s b hψ
  for i in [:a.size] do
    let some u := a[i]? | continue
    let z := sample * 1009 + i * 127
    let lottery := stratum == "lottery" || stratum == "all"
    let writer := stratum == "writer" || stratum == "all"
    let clean := stratum == "all"
    let v : AgentState ψ := {
      u with
      probe := flip (z+1), phase := flip (z+2),
      wait := flip (z+3), reset := flip (z+4), carry := flip (z+5),
      count := pick (z+6) (κ+1), h_field := flip (z+7),
      p := lottery && flip (z+8), p_carry := lottery && flip (z+9),
      echo := flip (z+10),
      signal_B := ⟨pick (z+11) 2, Nat.mod_lt _ (by decide)⟩,
      bullet := ⟨pick (z+12) 3, Nat.mod_lt _ (by decide)⟩,
      shield := flip (z+13),
      path3 := if writer && flip (z+14) then some {
        label := pick (z+15) ψ, bit := pick (z+16) 2,
        flag := pick (z+17) 2 } else none,
      write_state := if writer then
        (#[WriteState.none, .depart, .ready, .increment_WS, .increment_WS_done,
           .done, .equal, .larger, .less, .produce, .overwrite, .move_flip,
           .move, .increment_group])[pick (z+18) 14]?.getD .none
        else .none,
      write := if writer then
        (#[WriteAction.none, .overwrite, .move_flip, .move,
           .increment_group])[pick (z+19) 5]?.getD .none else .none,
      last := writer && flip (z+20),
      last_set := writer && flip (z+21),
      last_unset := writer && flip (z+22),
      b_carry := writer && flip (z+23),
      gen_ws := writer && flip (z+24),
      ws_echo := writer && flip (z+25),
      signal_ws := writer && flip (z+26),
      path4 := if clean && flip (z+27) then
        some ((if flip (z+28) then -1 else Int.ofNat (pick (z+29) ψ)), pick (z+30) 2)
        else none,
      path5 := if clean && flip (z+31) then
        some ((if flip (z+32) then -1 else Int.ofNat (pick (z+33) ψ)), pick (z+34) 2)
        else none }
    a := a.set! i v
  return a

structure DRun (ψ : Nat) where
  core : Run ψ
  drains : Nat := 0
  checks : Nat := 0

def expectD {ψ : Nat} (r : DRun ψ) (ok : Bool) (msg : String) : DRun ψ :=
  if r.core.status != "running" then r
  else if ok then { r with checks := r.checks + 1 }
  else { r with core := fail r.core msg }

def stepD {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (c : PPLLAstraR5Repair.Cfg) (p h l : Nat)
    (r : DRun ψ) (e : Nat) : DRun ψ := Id.run do
  if r.core.status != "running" then return r
  let core := step hψ κ c r.core e
  let mut out : DRun ψ := { r with core := core }
  if core.status != "running" then return out
  for t in #[h+l, p+l] do
    if out.core.status != "running" then break
    let some cell := getCell? out.core.row t | return { out with core := fail out.core "bad_terminal" }
    if cell.state == .eliminate_signal then
      let prior := out.core.phase
      let dren : Run ψ := { out.core with phase := "lottery_drain" }
      let drained := step hψ κ c dren (t-1)
      out := { out with core := drained, drains := out.drains + 1 }
      if drained.status == "running" then
        return { out with core := fail drained s!"terminal_drain_failed_{t}" }
      -- Preserve the phase of the intervention in the complete witness.
      if drained.status == "hole" then
        let updated : Run ψ := { drained with stopPhase := s!"lottery_drain_after_{prior}" }
        out := { out with core := updated }
  return out

def runDebris (ψ q κ : Nat) (selective : Bool) (seed : Array (AgentState ψ))
    (hψ : ψ > 0) : DRun ψ := Id.run do
  let h := (q-1)*ψ
  let p := 0
  let l := ψ-1
  let c : PPLLAstraR5Repair.Cfg := { selective := selective }
  let mut r : DRun ψ := { core := { row := seed } }
  if !(seed.all (PPLLSimRawCodec.inProtocolDomainB κ)) then
    return { r with core := fail r.core "initial_domain" }
  r := { r with core := { r.core with phase := "prepare" } }
  r := stepD hψ κ c p h l r (h+l-1)
  for j in [:l-1] do r := stepD hψ κ c p h l r (h+j)
  r := stepD hψ κ c p h l r (h+l-1)
  for k in [:l-1] do r := stepD hψ κ c p h l r (h+l-2-k)
  r := expectD r (wave r.core.row h ψ && tokenCount r.core.row == 0) "W(H)"
  r := { r with core := { r.core with phase := "emit_return" } }
  r := stepD hψ κ c p h l r (p+l)
  for k in [:l] do r := stepD hψ κ c p h l r (p+l-1-k)
  let some u0 := getCell? r.core.row p | return { r with core := fail r.core "missing_P0" }
  let pathBit0 := match u0.path with | .some _ b => b | _ => 2
  let expected0 : Path2Info := { label := 0, bit := pathBit0, position := ψ, action := 1 }
  let c0 := wave r.core.row h ψ && tokenCount r.core.row == 1 &&
    u0.path2 == some expected0
  r := expectD r c0 "C0"
  for j in [:ψ] do
    if r.core.status != "running" then break
    r := { r with core := { r.core with phase := s!"forward_{j}" } }
    for x in [j:ψ] do r := stepD hψ κ c p h l r (p+x)
    for x in [:j] do r := stepD hψ κ c p h l r (h+x)
    if r.core.status != "running" then break
    let some v := getCell? r.core.row (h+j) |
      return { r with core := fail r.core s!"missing_H_{j}" }
    let some tok := v.path2 |
      return { r with core := fail r.core s!"missing_verdict_{j}" }
    if tok.action == 2 && j < l then
      r := expectD r (wave r.core.row h ψ && tokenCount r.core.row == 1 &&
        tok.label == j+1 && tok.position == l) s!"A2_after_F_{j}"
      r := { r with core := { r.core with phase := s!"backward_{j}" } }
      for k in [:j] do r := stepD hψ κ c p h l r (h+j-1-k)
      for k in [:l-j] do r := stepD hψ κ c p h l r (p+l-k)
      let some source := getCell? r.core.row (p+j+1) |
        return { r with core := fail r.core s!"missing_P_{j+1}" }
      let pathBit := match source.path with | .some _ b => b | _ => 2
      let expected : Path2Info := { label := j+1, bit := pathBit, position := ψ, action := 1 }
      let next := wave r.core.row h ψ && tokenCount r.core.row == 1 &&
        source.path2 == some expected
      r := expectD r next s!"C_{j+1}"
    else if tok.action == 3 || tok.action == 4 then
      r := expectD r (tokenCount r.core.row == 1) s!"verdict_unique_{j}"
      let terminal := if tok.action == 4 || j == l then h+l else p+l
      let core : Run ψ := { r.core with verdictAction := tok.action }
      r := { r with core := { core with phase := s!"discharge_A{tok.action}_{j}" } }
      if j == l then
        r := stepD hψ κ c p h l r (h+l-1)
      else if tok.action == 4 then
        for x in [j:l] do r := stepD hψ κ c p h l r (h+x)
      else
        for k in [:j] do r := stepD hψ κ c p h l r (h+j-1-k)
        r := stepD hψ κ c p h l r (p+l)
      if r.core.status == "running" then
        -- If the verdict has just been consumed, stepD already drained it.
        let some tcell := getCell? r.core.row terminal |
          return { r with core := fail r.core "missing_verdict_terminal" }
        if tcell.state == .eliminate_signal then
          r := stepD hψ κ c p h l r (terminal-1)
      if r.core.status == "running" then
        r := { r with core := fail r.core s!"A{tok.action}_no_target_{j}" }
      break
    else
      r := { r with core := fail r.core s!"unexpected_action_{tok.action}_at_{j}" }
  if r.core.status == "running" then r := { r with core := fail r.core "word_end_no_target" }
  return r

def resultJson {ψ : Nat} (ψn q κ sample : Nat) (selective : Bool)
    (stratum : String) (seed : Array (AgentState ψ)) (r : DRun ψ) : Json :=
  Json.mkObj [
    ("psi", toJson ψn), ("q", toJson q), ("kappa", toJson κ),
    ("selective", toJson selective), ("sample", toJson sample),
    ("stratum", toJson stratum), ("status", toJson r.core.status),
    ("failure", toJson r.core.failure), ("stop_phase", toJson r.core.stopPhase),
    ("drains", toJson r.drains), ("checks", toJson r.checks),
    ("verdict_action", toJson r.core.verdictAction),
    ("length", toJson r.core.word.size), ("word", toJson r.core.word),
    ("seed", Json.arr (seed.map PPLLSimRawCodec.encodeState)),
    ("endpoint", Json.arr (r.core.row.map PPLLSimRawCodec.encodeState)) ]

def runAll (ψ q κ : Nat) (selective : Bool) (mode : String)
    (samples : Nat) (hψ : ψ > 0) (out : String) : IO UInt32 := do
  let mut counts : List (String × Nat) := []
  let mut stratumCounts : List (String × Nat) := []
  let mut stratumDrains : List (String × Nat) := []
  let mut phases : List (String × Nat) := []
  let mut maxLength := 0
  let mut drains := 0
  let mut a3 := 0
  let mut a4 := 0
  let mut firstFailure : Option Json := none
  let mut firstDrain : Option Json := none
  let mut firstLeader : Option Json := none
  let mut firstHole : Option Json := none
  let mut firstWriter : Option Json := none
  for sample in [:samples] do
    let s := if mode == "lottery_exhaustive" then 0 else pick (sample*283+17) (2^ψ)
    let b := if mode == "lottery_exhaustive" then 0 else pick (sample*353+23) (2^ψ)
    let stratum := if mode == "lottery_exhaustive" then "lottery"
      else if sample % 3 == 0 then "lottery"
      else if sample % 3 == 1 then "writer" else "all"
    let mut seed := varied ψ q κ s b sample stratum hψ
    if mode == "lottery_exhaustive" then
      for i in [:seed.size] do
        let some u := seed[i]? | continue
        let v : AgentState ψ := { u with probe := false, phase := false, wait := false, reset := false, carry := false, count := 0, h_field := false, echo := false, signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩, shield := false, p := (sample / 2^i) % 2 == 1, p_carry := (sample / 2^(i+ψ*q)) % 2 == 1 }
        seed := seed.set! i v
    let mut r := runDebris ψ q κ selective seed hψ
    if r.core.word.size > 2*ψ*ψ+ψ+1 then
      let core : Run ψ := { r.core with status := "checkpoint_failure" }
      let core : Run ψ := { core with failure := "length_over_bound" }
      r := { r with core := core }
    let status := r.core.status
    counts := (status, (counts.lookup status).getD 0 + 1) :: counts.filter (fun x => x.1 != status)
    let skey := stratum ++ ":" ++ status
    stratumCounts := (skey, (stratumCounts.lookup skey).getD 0 + 1) ::
      stratumCounts.filter (fun x => x.1 != skey)
    stratumDrains := (stratum, (stratumDrains.lookup stratum).getD 0 + r.drains) ::
      stratumDrains.filter (fun x => x.1 != stratum)
    phases := (r.core.stopPhase, (phases.lookup r.core.stopPhase).getD 0 + 1) ::
      phases.filter (fun x => x.1 != r.core.stopPhase)
    maxLength := max maxLength r.core.word.size
    drains := drains + r.drains
    if r.core.verdictAction == 3 then a3 := a3 + 1
    if r.core.verdictAction == 4 then a4 := a4 + 1
    let j := resultJson ψ q κ sample selective stratum seed r
    if status == "checkpoint_failure" &&
        (firstFailure.isNone ||
          r.core.word.size < ((firstFailure.getD Json.null).getObjValAs? Nat "length").toOption.getD 100000) then
      firstFailure := some j
    if r.drains > 0 && firstDrain.isNone then firstDrain := some j
    if status == "leader" && firstLeader.isNone then firstLeader := some j
    if status == "hole" && firstHole.isNone then firstHole := some j
    if stratum == "writer" && firstWriter.isNone then firstWriter := some j
  let receipt := Json.mkObj [
    ("psi", toJson ψ), ("q", toJson q), ("kappa", toJson κ),
    ("selective", toJson selective), ("mode", toJson mode),
    ("samples", toJson samples),
    ("counts", Json.mkObj (counts.map fun (k,v) => (k,toJson v))),
    ("stratum_counts", Json.mkObj (stratumCounts.map fun (k,v) => (k,toJson v))),
    ("stratum_drains", Json.mkObj (stratumDrains.map fun (k,v) => (k,toJson v))),
    ("stop_phases", Json.mkObj (phases.map fun (k,v) => (k,toJson v))),
    ("drains", toJson drains), ("a3_cases", toJson a3),
    ("a4_cases", toJson a4), ("max_length", toJson maxLength),
    ("bound", toJson (2*ψ*ψ+ψ+1)),
    ("first_failure", firstFailure.getD Json.null),
    ("first_drain", firstDrain.getD Json.null),
    ("first_leader", firstLeader.getD Json.null),
    ("first_hole", firstHole.getD Json.null),
    ("first_writer", firstWriter.getD Json.null) ]
  IO.FS.writeFile out receipt.compress
  IO.println s!"psi={ψ} q={q} kappa={κ} selective={selective} mode={mode} counts={counts} drains={drains} max={maxLength}"
  return if firstFailure.isSome then 1 else 0

def main (args : List String) : IO UInt32 := do
  if args == ["mini"] then
    for selective in #[true,false] do
      IO.println (miniReceipt selective).compress
      IO.println (drainCounterReceipt selective).compress
    return 0
  let [ψs, qs, κs, cs, mode, samplesS, out] := args |
    throw (IO.userError "usage: PSI Q KAPPA selective|broad MODE SAMPLES OUT")
  let some ψ := ψs.toNat? | throw (IO.userError "bad PSI")
  let some q := qs.toNat? | throw (IO.userError "bad Q")
  let some κ := κs.toNat? | throw (IO.userError "bad KAPPA")
  let some samples := samplesS.toNat? | throw (IO.userError "bad samples")
  if ψ < 4 || (q != 1 && q != 2) then throw (IO.userError "bad ψ/q")
  if cs != "selective" && cs != "broad" then throw (IO.userError "bad guard")
  if mode != "lottery_exhaustive" && mode != "sample" then throw (IO.userError "bad mode")
  if hψ : ψ > 0 then runAll ψ q κ (cs == "selective") mode samples hψ out
  else throw (IO.userError "ψ=0")

end PPLLAstraR5ModeDDebris

def main (args : List String) : IO UInt32 := PPLLAstraR5ModeDDebris.main args
