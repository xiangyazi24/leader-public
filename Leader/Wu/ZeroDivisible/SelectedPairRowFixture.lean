import Leader.Wu.ZeroDivisible.CheckRepair
import Leader.Wu.Sim.RawCodec
import Lean.Data.Json

/-! Adversarial finite falsification of the selected pair-row claim. -/

set_option autoImplicit false
open Lean

namespace PPLLAstraR5PairRowProbe

def mix64 (x : UInt64) : UInt64 :=
  let x := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
  let x := (x ^^^ (x >>> 27)) * 0x94d049bb133111eb
  x ^^^ (x >>> 31)

def pseudo (seed : Nat) : Nat :=
  (mix64 (seed.toUInt64 + 0x9e3779b97f4a7c15)).toNat
def flip (seed : Nat) : Bool := pseudo seed % 2 == 1
def pick (seed n : Nat) : Nat := pseudo seed % n

def stateAt (ψ j code : Nat) : MainState :=
  if j == 0 then if code % 2 == 0 then .lock else .compare1
  else if j == ψ-1 then .compare2
  else if j == ψ-2 then
    (#[MainState.equal,.depart,.lock,.compare1])[code%4]?.getD .equal
  else (#[MainState.depart,.lock,.compare1])[code%3]?.getD .depart

def base (ψ κ j code : Nat) (hψ : ψ > 0) : AgentState ψ :=
  { leader := false, probe := false, phase := false,
    bit := flip (code+2), wait := false,
    state := stateAt ψ j (pseudo (code+3)),
    path := .some j (pick (code+4) 2),
    reset := false, carry := false, count := 0,
    label := ⟨j%ψ, Nat.mod_lt _ hψ⟩, h_field := false,
    path2 := none, path3 := none, path4 := none, path5 := none,
    p := false, p_carry := false, reset_cmd := false, echo := false,
    signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩,
    shield := false, write_state := .none, write := .none,
    last := false, last_set := false, last_unset := false,
    b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }

def varied (ψ κ stratum code : Nat) (u : AgentState ψ) : AgentState ψ := Id.run do
  let activeWait := stratum == 1 || stratum == 5
  let lottery := stratum == 2 || stratum == 5
  let writer := stratum == 3 || stratum == 5
  let clean := stratum == 4 || stratum == 5
  return {
    u with
    probe := activeWait && flip (code+11),
    phase := activeWait && flip (code+12),
    wait := activeWait && flip (code+13),
    reset := activeWait && flip (code+14),
    carry := activeWait && flip (code+15),
    count := if activeWait then pick (code+16) (κ+1) else 0,
    h_field := activeWait && flip (code+17),
    reset_cmd := activeWait && flip (code+18),
    echo := activeWait && flip (code+19),
    p := lottery && flip (code+20),
    p_carry := lottery && flip (code+21),
    signal_B := ⟨(if lottery then pick (code+22) 2 else 0)%2,
      Nat.mod_lt _ (by decide : 0 < 2)⟩,
    bullet := ⟨(if lottery then pick (code+23) 3 else 0)%3,
      Nat.mod_lt _ (by decide : 0 < 3)⟩,
    shield := lottery && flip (code+24),
    path3 := if writer && flip (code+25) then some {
      label := pick (code+26) ψ, bit := pick (code+27) 2,
      flag := pick (code+28) 2 } else none,
    write_state := if writer then
      (#[WriteState.none, .depart, .ready, .increment_WS, .increment_WS_done,
         .done, .equal, .larger, .less, .produce, .overwrite, .move_flip,
         .move, .increment_group])[pick (code+29) 14]?.getD .none
      else .none,
    write := if writer then
      (#[WriteAction.none, .overwrite, .move_flip, .move,
         .increment_group])[pick (code+30) 5]?.getD .none else .none,
    last := writer && flip (code+31),
    last_set := writer && flip (code+32),
    last_unset := writer && flip (code+33),
    b_carry := writer && flip (code+34),
    gen_ws := writer && flip (code+35),
    ws_echo := writer && flip (code+36),
    signal_ws := writer && flip (code+37),
    path4 := if clean && flip (code+38) then
      some ((if flip (code+39) then -1 else Int.ofNat (pick (code+40) ψ)), pick (code+41) 2)
      else none,
    path5 := if clean && flip (code+42) then
      some ((if flip (code+43) then -1 else Int.ofNat (pick (code+44) ψ)), pick (code+45) 2)
      else none }

def token (action label bit position : Nat) : Path2Info :=
  { action := action, label := label, bit := bit, position := position }

def selectedAction (code : Nat) : Nat :=
  (#[1,4,2,3])[code%4]?.getD 1

def position (ψ code : Nat) : Nat :=
  (#[0,1,ψ])[code%3]?.getD 0

def makePair (ψ κ edge sel other pos1 pos2 stratum : Nat)
    (hψ : ψ > 0) : AgentState ψ × AgentState ψ := Id.run do
  let right := (edge+1)%ψ
  let code := edge*1000003 + sel*1000033 + other*1000037 +
    pos1*1000039 + pos2*1000081 + stratum*1000099 + ψ*1000117 + κ*1000121
  let l := varied ψ κ stratum (code+1009) (base ψ κ edge (code+101) hψ)
  let r := varied ψ κ stratum (code+2003) (base ψ κ right (code+211) hψ)
  let action := selectedAction sel
  let t := token action (pick (code+301) ψ) (pick (code+302) 2) (position ψ pos1)
  let blocker := if other == 0 then none else
    some (token other (pick (code+401) ψ) (pick (code+402) 2) (position ψ pos2))
  if action == 1 || action == 4 then
    return ({ l with path2 := some t }, { r with path2 := blocker })
  else return ({ l with path2 := blocker }, { r with path2 := some t })

def readerRank (ψ : Nat) (t : Path2Info) : Nat :=
  (2*ψ-1)*(ψ-1-t.label) + t.position +
    (if t.action == 2 then ψ else 0) + 1

def weight (ψ j : Nat) (t : Path2Info) : Nat :=
  if t.action == 1 || t.action == 2 then (ψ+1)*readerRank ψ t
  else if t.action == 3 then (if j == ψ-1 then 0 else j+1)+1
  else if t.action == 4 then ψ-1-j+1 else 0

def potential {ψ : Nat} (ψn : Nat) (l r : AgentState ψ) : Nat × Nat :=
  let p := (match l.path2 with | none => 0 | some t => weight ψn l.label.val t) +
    (match r.path2 with | none => 0 | some t => weight ψn r.label.val t)
  let z := (match l.path2 with
    | some t => if (t.action == 1 || t.action == 2) && t.position == 0 then 1 else 0
    | none => 0) + (match r.path2 with
    | some t => if (t.action == 1 || t.action == 2) && t.position == 0 then 1 else 0
    | none => 0)
  (p,z)

def count {ψ : Nat} (l r : AgentState ψ) : Nat :=
  (if l.path2.isSome then 1 else 0) + (if r.path2.isSome then 1 else 0)

def stateOK (ψ j : Nat) (s : MainState) : Bool :=
  if j == 0 then s == .lock || s == .compare1
  else if j == ψ-1 then s == .compare2
  else if j == ψ-2 then s == .equal || s == .depart || s == .lock || s == .compare1
  else s == .depart || s == .lock || s == .compare1

def tokenOK (ψ : Nat) (o : Option Path2Info) : Bool :=
  match o with
  | none => true
  | some t => 1 ≤ t.action && t.action ≤ 4 && t.label < ψ &&
      t.bit ≤ 1 && t.position ≤ ψ

def frame (ψ : Nat) (oldl oldr l r : AgentState ψ) : Bool :=
  l.path == oldl.path && r.path == oldr.path &&
  l.label == oldl.label && r.label == oldr.label &&
  l.state != .produce && r.state != .produce &&
  stateOK ψ l.label.val l.state && stateOK ψ r.label.val r.state &&
  tokenOK ψ l.path2 && tokenOK ψ r.path2

def outcome (ψ : Nat) (oldl oldr l r : AgentState ψ) : String :=
  if l.leader || r.leader then "leader"
  else if l.path == .bot || r.path == .bot then "hole"
  else if (l.label.val == ψ-1 && l.state == .eliminate_signal) ||
      (r.label.val == ψ-1 && r.state == .eliminate_signal) then "terminal_E"
  else if !frame ψ oldl oldr l r then "failure_frame"
  else if count l r > count oldl oldr then "failure_token_increase"
  else
    let a := potential ψ oldl oldr
    let b := potential ψ l r
    if b.1 < a.1 then "P_drop"
    else if b.1 == a.1 && b.2 < a.2 then "Z_stutter"
    else "failure_rank"

def encode (ψ κ edge sel other pos1 pos2 stratum : Nat) (selective : Bool)
    (l r l' r' : AgentState ψ) : Json :=
  let a := potential ψ l r
  let b := potential ψ l' r'
  Json.mkObj [
    ("psi", toJson ψ), ("kappa", toJson κ), ("edge", toJson edge),
    ("selected_action", toJson (selectedAction sel)),
    ("other_action", toJson other),
    ("selected_position", toJson (position ψ pos1)),
    ("other_position", toJson (position ψ pos2)),
    ("stratum", toJson stratum), ("selective", toJson selective),
    ("input", toJson #[PPLLSimRawCodec.encodeState l,PPLLSimRawCodec.encodeState r]),
    ("output", toJson #[PPLLSimRawCodec.encodeState l',PPLLSimRawCodec.encodeState r']),
    ("old_potential", toJson #[a.1,a.2]),
    ("new_potential", toJson #[b.1,b.2]),
    ("outcome", toJson (outcome ψ l r l' r'))]

def addCount (cs : List (String × Nat)) (k : String) : List (String × Nat) :=
  (k, (cs.lookup k).getD 0+1) :: cs.filter (fun x => x.1 != k)

def stateTag (ψ : Nat) (u : AgentState ψ) : String :=
  let j := u.label.val
  let st := if u.state == .lock then "lock"
    else if u.state == .compare1 then "C1"
    else if u.state == .compare2 then "C2"
    else if u.state == .equal then "equal"
    else if u.state == .depart then "depart" else "other"
  let site := if j == 0 then "head"
    else if j == ψ-1 then "tail"
    else if j == ψ-2 then "penultimate" else "internal"
  s!"{site}_{st}"

def validInput (ψ edge action : Nat) (l r : AgentState ψ) : Bool :=
  !l.leader && !r.leader && l.label.val == edge &&
  r.label.val == (edge+1)%ψ &&
  l.path == .some edge (match l.path with | .some _ b => b | .bot => 2) &&
  r.path == .some ((edge+1)%ψ) (match r.path with | .some _ b => b | .bot => 2) &&
  stateOK ψ edge l.state && stateOK ψ ((edge+1)%ψ) r.state &&
  tokenOK ψ l.path2 && tokenOK ψ r.path2 &&
  (if action == 1 || action == 4 then
    (l.path2.map (fun t => t.action)) == some action
   else (r.path2.map (fun t => t.action)) == some action)

def direction (a : Nat) : String :=
  if a == 1 || a == 4 then "R" else "L"

def addCoverage (cs : List (String × Nat)) (ψ edge action other pos1 pos2 stratum : Nat)
    (l r : AgentState ψ) : List (String × Nat) := Id.run do
  let mut cs := cs
  for key in [s!"edge_{edge}",s!"selected_A{action}",s!"other_A{other}",
      s!"selected_pos_{position ψ pos1}",s!"other_pos_{position ψ pos2}",
      s!"stratum_{stratum}",stateTag ψ l,stateTag ψ r] do
    cs := addCount cs key
  if other > 0 then
    cs := addCount cs (if direction action == direction other then
      "same_direction" else "opposite_direction")
  else cs := addCount cs "single_token"
  if (action == 4 && edge == ψ-1) ||
      (action == 3 && (edge+1)%ψ == ψ-1) then
    cs := addCount cs "selected_terminal_control"
  if l.probe || r.probe then cs := addCount cs "probe_true"
  if l.reset_cmd || r.reset_cmd then cs := addCount cs "reset_cmd_true"
  if l.p || r.p then cs := addCount cs "lottery_p_true"
  if l.p_carry || r.p_carry then cs := addCount cs "lottery_p_carry_true"
  if l.bullet.val > 0 || r.bullet.val > 0 then cs := addCount cs "bullet_nonzero"
  if l.path3.isSome || r.path3.isSome then cs := addCount cs "path3_present"
  if l.path4.isSome || r.path4.isSome then cs := addCount cs "path4_present"
  if l.path5.isSome || r.path5.isSome then cs := addCount cs "path5_present"
  if l.write_state != .none || r.write_state != .none then
    cs := addCount cs "write_state_active"
  return cs

def run (ψ κ : Nat) (selective : Bool) (hψ : ψ > 0) (out : String) : IO UInt32 := do
  let mut counts : List (String × Nat) := []
  let mut coverage : List (String × Nat) := []
  let mut processed := 0
  let mut firstFailure : Option Json := none
  let mut firstStutter : Option Json := none
  let mut firstTerminal : Option Json := none
  let mut firstHole : Option Json := none
  for edge in [:ψ] do
    for sel in [:4] do
      for other in [:5] do
        for pos1 in [:3] do
          for pos2 in [:3] do
            for stratum in [:6] do
              let (l,r) := makePair ψ κ edge sel other pos1 pos2 stratum hψ
              if !(PPLLSimRawCodec.inProtocolDomainB κ l &&
                   PPLLSimRawCodec.inProtocolDomainB κ r) then
                IO.eprintln "generator_domain_failure"
                return 2
              if !validInput ψ edge (selectedAction sel) l r then
                IO.eprintln "generator_premise_failure"
                return 2
              coverage := addCoverage coverage ψ edge (selectedAction sel)
                other pos1 pos2 stratum l r
              let v := PPLLAstraR5Repair.pipeline hψ κ
                { selective := selective } l r
              let status := outcome ψ l r v.1 v.2
              processed := processed+1
              counts := addCount counts status
              if status.startsWith "failure" && firstFailure.isNone then
                firstFailure := some (encode ψ κ edge sel other pos1 pos2 stratum
                  selective l r v.1 v.2)
              if status == "Z_stutter" && firstStutter.isNone then
                firstStutter := some (encode ψ κ edge sel other pos1 pos2 stratum
                  selective l r v.1 v.2)
              if status == "terminal_E" && firstTerminal.isNone then
                firstTerminal := some (encode ψ κ edge sel other pos1 pos2 stratum
                  selective l r v.1 v.2)
              if status == "hole" && firstHole.isNone then
                firstHole := some (encode ψ κ edge sel other pos1 pos2 stratum
                  selective l r v.1 v.2)
              if firstFailure.isSome then break
            if firstFailure.isSome then break
          if firstFailure.isSome then break
        if firstFailure.isSome then break
      if firstFailure.isSome then break
    if firstFailure.isSome then break
  let expected := ψ*4*5*3*3*6
  let summary := Json.mkObj [
    ("psi", toJson ψ), ("kappa", toJson κ),
    ("selective", toJson selective),
    ("expected", toJson expected), ("processed", toJson processed),
    ("counts", toJson counts),
    ("coverage", toJson coverage),
    ("first_failure", firstFailure.getD Json.null),
    ("first_stutter", firstStutter.getD Json.null),
    ("first_terminal_E", firstTerminal.getD Json.null),
    ("first_hole", firstHole.getD Json.null)]
  IO.FS.writeFile out summary.compress
  IO.println s!"psi={ψ} kappa={κ} selective={selective} processed={processed}/{expected} counts={counts}"
  return if firstFailure.isSome || processed != expected then 1 else 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [psiS,kS,guardS,out] =>
    let some ψ := psiS.toNat? | return 2
    let some κ := kS.toNat? | return 2
    let some guard := guardS.toNat? | return 2
    if ψ < 4 || guard > 1 then return 2
    if hψ : ψ > 0 then run ψ κ (guard == 1) hψ out else return 2
  | _ => return 2

end PPLLAstraR5PairRowProbe

def main (args : List String) : IO UInt32 := PPLLAstraR5PairRowProbe.main args
