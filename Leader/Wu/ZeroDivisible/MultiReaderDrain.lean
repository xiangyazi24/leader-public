import Leader.Wu.ZeroDivisible.CheckRepair
import Leader.Wu.Sim.RawCodec
import Lean.Data.Json

/-! Finite, full-row test of the deterministic multi-reader drain. -/

set_option autoImplicit false
open Lean

namespace PPLLAstraR5MultiReader

def at? {ψ : Nat} (a : Array (AgentState ψ)) (i : Nat) : Option (AgentState ψ) := a[i]?

def token (action label bit position : Nat) : Path2Info :=
  { action := action, label := label, bit := bit, position := position }

def seed (ψ q pattern : Nat) (holders : Array (Nat × Path2Info))
    (hψ : ψ > 0) : Array (AgentState ψ) := Id.run do
  let mut a := #[]
  for i in [:q*ψ] do
    let j := i % ψ
    let st : MainState := if j == 0 then .lock
      else if j == ψ-1 then .compare2
      else if j == ψ-2 then .equal else .depart
    let carried := if pattern == 0 then 0 else i % 2
    let resident := pattern != 0 && (i+1)%2 == 1
    let tok := (holders.find? fun x => x.1 == i).map Prod.snd
    a := a.push {
      leader := false, probe := false, phase := false, bit := resident,
      wait := false, state := st, path := .some j carried,
      reset := false, carry := false, count := 0,
      label := ⟨j, Nat.mod_lt i hψ⟩, h_field := false,
      path2 := tok, path3 := none, path4 := none, path5 := none,
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

def tokenCount {ψ : Nat} (a : Array (AgentState ψ)) : Nat :=
  a.foldl (fun z u => z + if u.path2.isSome then 1 else 0) 0

def basin {ψ : Nat} (ψn : Nat) (a : Array (AgentState ψ)) : Bool := Id.run do
  for i in [:a.size] do
    let some u := at? a i | return false
    let j := i % ψn
    if u.label.val != j || u.state == .produce then return false
    match u.path with
    | .some lbl bit => if lbl != j || bit > 1 then return false
    | .bot => return false
    let stateOK :=
      if j == 0 then u.state == .lock || u.state == .compare1
      else if j == ψn-1 then u.state == .compare2
      else if j == ψn-2 then
        u.state == .equal || u.state == .depart ||
          u.state == .lock || u.state == .compare1
      else u.state == .depart || u.state == .lock || u.state == .compare1
    if !stateOK then return false
  return true

def holderFrame {ψ : Nat} (ψn : Nat)
    (initial a : Array (AgentState ψ)) : Bool := Id.run do
  if initial.size != a.size then return false
  for i in [:a.size] do
    let some old := at? initial i | return false
    let some u := at? a i | return false
    if u.path != old.path || u.label.val != i % ψn || u.state == .produce then
      return false
  return true

def alphabet {ψ : Nat} (ψn : Nat) (a : Array (AgentState ψ)) : Bool :=
  a.all fun u => match u.path2 with
    | none => true
    | some t => 1 ≤ t.action && t.action ≤ 4 && t.label < ψn &&
        t.bit ≤ 1 && t.position ≤ ψn

def readerRank (ψ : Nat) (t : Path2Info) : Nat :=
  (2*ψ-1)*(ψ-1-t.label) + t.position +
    (if t.action == 2 then ψ else 0) + 1

def weight (ψ physical : Nat) (t : Path2Info) : Nat :=
  if t.action == 1 || t.action == 2 then (ψ+1)*readerRank ψ t
  else if t.action == 3 then (if physical == ψ-1 then 0 else physical+1)+1
  else if t.action == 4 then ψ-1-physical+1
  else 0

def potential {ψ : Nat} (ψn : Nat) (a : Array (AgentState ψ)) : Nat × Nat := Id.run do
  let mut p := 0
  let mut z := 0
  for i in [:a.size] do
    if let some t := (at? a i).bind (fun u => u.path2) then
      p := p + weight ψn (i%ψn) t
      if (t.action == 1 || t.action == 2) && t.position == 0 then z := z+1
  return (p,z)

def firstToken {ψ : Nat} (a : Array (AgentState ψ)) : Option (Nat × Path2Info) := Id.run do
  for i in [:a.size] do
    if let some t := (at? a i).bind (fun u => u.path2) then return some (i,t)
  return none

def terminalE {ψ : Nat} (ψn : Nat) (a : Array (AgentState ψ)) : Option Nat := Id.run do
  for i in [:a.size] do
    if i % ψn == ψn-1 && ((at? a i).map (fun u => u.state) == some .eliminate_signal) then
      return some i
  return none

structure Run (ψ : Nat) where
  row : Array (AgentState ψ)
  word : Array Nat := #[]
  status : String := "running"
  failure : String := ""
  oldPotential : Nat × Nat := (0,0)
  newPotential : Nat × Nat := (0,0)
  rankChecks : Nat := 0
  pDrops : Nat := 0
  zStutters : Nat := 0
  d1Drains : Nat := 0
  stutterWord : Array Nat := #[]
  stutterOld : Nat × Nat := (0,0)
  stutterNew : Nat × Nat := (0,0)
  maxTokens : Nat := 0
  minTokens : Nat := 0

def fail {ψ : Nat} (r : Run ψ) (why : String) : Run ψ :=
  { r with status := "failure", failure := why }

def step {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (cfg : PPLLAstraR5Repair.Cfg) (r : Run ψ) (edge : Nat) : Run ψ := Id.run do
  let n := r.row.size
  let some l := at? r.row edge | return fail r "bad_edge"
  let some rr := at? r.row ((edge+1)%n) | return fail r "bad_successor"
  let v := PPLLAstraR5Repair.pipeline hψ κ cfg l rr
  let row := (r.row.set! edge v.1).set! ((edge+1)%n) v.2
  return { r with row := row, word := r.word.push edge }

def run (ψ q κ pattern : Nat) (selective : Bool)
    (holders : Array (Nat × Path2Info)) (hψ : ψ > 0) : Run ψ := Id.run do
  let cfg : PPLLAstraR5Repair.Cfg := { selective := selective }
  let a := seed ψ q pattern holders hψ
  let mut r : Run ψ := { row := a, maxTokens := tokenCount a, minTokens := tokenCount a }
  if !(a.all (PPLLSimRawCodec.inProtocolDomainB κ)) then return fail r "initial_domain"
  if !(basin ψ a && alphabet ψ a) then return fail r "initial_basin_or_alphabet"
  let initialRank := potential ψ a
  let cap := (a.size+1)*initialRank.1+initialRank.2+2
  for _ in [:cap] do
    let t := target r.row
    if t != "none" then return { r with status := t }
    if let some terminal := terminalE ψ r.row then
      r := step hψ κ cfg r ((terminal+r.row.size-1)%r.row.size)
      let some drained := at? r.row terminal | return fail r "D1_missing_terminal"
      if drained.path != .bot then return fail r "D1_terminal_not_hole"
      let afterCount := tokenCount r.row
      r := { r with maxTokens := max r.maxTokens afterCount }
      r := { r with minTokens := min r.minTokens afterCount }
      r := { r with d1Drains := r.d1Drains+1 }
      return { r with status := target r.row }
    let some (holder,tok) := firstToken r.row |
      return { r with status := "token_free" }
    let oldCount := tokenCount r.row
    let oldRank := potential ψ r.row
    let edge := if tok.action == 1 || tok.action == 4 then holder
      else (holder+r.row.size-1)%r.row.size
    r := step hψ κ cfg r edge
    if r.status == "failure" then return r
    let nowTarget := target r.row
    let nextCount := tokenCount r.row
    let nextRank := potential ψ r.row
    r := { r with maxTokens := max r.maxTokens nextCount }
    r := { r with minTokens := min r.minTokens nextCount }
    r := { r with oldPotential := oldRank }
    r := { r with newPotential := nextRank }
    if nowTarget != "none" then return { r with status := nowTarget }
    if !holderFrame ψ a r.row then return fail r "holder_frame"
    if nextCount > oldCount then return fail r "token_count_increased"
    if !alphabet ψ r.row then return fail r "alphabet"
    if let some _ := terminalE ψ r.row then
      continue
    if !basin ψ r.row then return fail r "basin"
    if !(nextRank.1 < oldRank.1 ||
         (nextRank.1 == oldRank.1 && nextRank.2 < oldRank.2)) then
      return fail r "potential_not_decreased"
    r := { r with rankChecks := r.rankChecks+1 }
    if nextRank.1 < oldRank.1 then
      r := { r with pDrops := r.pDrops+1 }
    else
      r := { r with zStutters := r.zStutters+1 }
      if r.zStutters == 1 then
        r := { r with stutterWord := r.word }
        r := { r with stutterOld := oldRank }
        r := { r with stutterNew := nextRank }
  return fail r s!"schedule_cap_{cap}"

def encodeRow {ψ : Nat} (a : Array (AgentState ψ)) : Json :=
  Json.arr (a.map PPLLSimRawCodec.encodeState)

def caseJson (ψ q κ pattern : Nat) (selective : Bool)
    (holders : Array (Nat × Path2Info)) (hψ : ψ > 0) (r : Run ψ) : Json :=
  Json.mkObj [
    ("psi", toJson ψ), ("q", toJson q), ("kappa", toJson κ),
    ("pattern", toJson pattern), ("selective", toJson selective),
    ("holders", toJson (holders.map fun x => Json.mkObj [
      ("site", toJson x.1), ("action", toJson x.2.action),
      ("label", toJson x.2.label), ("bit", toJson x.2.bit),
      ("position", toJson x.2.position)])),
    ("status", toJson r.status), ("failure", toJson r.failure),
    ("word", toJson r.word), ("length", toJson r.word.size),
    ("rank_checks", toJson r.rankChecks),
    ("p_drops", toJson r.pDrops), ("z_stutters", toJson r.zStutters),
    ("d1_drains", toJson r.d1Drains),
    ("first_stutter_word", toJson r.stutterWord),
    ("first_stutter_old", toJson #[r.stutterOld.1,r.stutterOld.2]),
    ("first_stutter_new", toJson #[r.stutterNew.1,r.stutterNew.2]),
    ("old_potential", toJson #[r.oldPotential.1,r.oldPotential.2]),
    ("new_potential", toJson #[r.newPotential.1,r.newPotential.2]),
    ("seed", encodeRow (seed ψ q pattern holders hψ)),
    ("endpoint", encodeRow r.row)]

def valuation (ψ code : Nat) : Path2Info :=
  let position := code % (ψ+1)
  let bit := (code / (ψ+1)) % 2
  let label := (code / ((ψ+1)*2)) % ψ
  let action := (code / ((ψ+1)*2*ψ)) % 2 + 1
  token action label bit position

def valuationCode (ψ : Nat) (t : Path2Info) : Nat :=
  t.position + (ψ+1)*(t.bit + 2*(t.label + ψ*(t.action-1)))

def addCount (cs : List (String × Nat)) (k : String) : List (String × Nat) :=
  (k, (cs.lookup k).getD 0+1) :: cs.filter (fun x => x.1 != k)

/-- SplitMix64 finalizer expressed on Nat for reproducible independent draws. -/
def mix64 (x : Nat) : Nat := Id.run do
  let modulus := 2^64
  let z := (x + 11400714819323198485) % modulus
  let z := (Nat.xor z (z / 2^30) * 13787848793156543929) % modulus
  let z := (Nat.xor z (z / 2^27) * 10723151780598845931) % modulus
  return Nat.xor z (z / 2^31)

def sampleHolders (ψ q κ pattern sample : Nat) (selective : Bool) :
    Array (Nat × Path2Info) := Id.run do
  let n := ψ*q
  let base := sample + 1000003*ψ + 1000033*q + 1000037*κ +
    1000039*pattern + (if selective then 1000081 else 0)
  let m := if sample % 5 == 0 then n else 2 + mix64 base % (n-1)
  let mut sites : Array Nat := #[]
  for d in [:n*8] do
    if sites.size == m then break
    let i := mix64 (base + 6364136223846793005*(d+1)) % n
    if !sites.contains i then sites := sites.push i
  for i in [:n] do
    if sites.size == m then break
    if !sites.contains i then sites := sites.push i
  let mut holders := #[]
  for slot in [:sites.size] do
    let i := sites[slot]?.getD 0
    let key := mix64 (base + 2862933555777941757*(slot+1) + 17*i)
    let action := 1 + mix64 (key+11) % 2
    let label := mix64 (key+23) % ψ
    let bit := mix64 (key+37) % 2
    let position := if slot == 0 then 0 else if slot == 1 then 1
      else if slot == 2 then ψ else mix64 (key+53) % (ψ+1)
    holders := holders.push (i, token action label bit position)
  return holders

def holderKey (holders : Array (Nat × Path2Info)) : Json :=
  toJson (holders.map fun x => Json.mkObj [
    ("site", toJson x.1), ("action", toJson x.2.action),
    ("label", toJson x.2.label), ("bit", toJson x.2.bit),
    ("position", toJson x.2.position)])

def sampleBatch (ψ q κ pattern : Nat) (selective : Bool)
    (hψ : ψ > 0) (count : Nat) (out : String) : IO UInt32 := do
  let mut counts : List (String × Nat) := []
  let mut processed := 0
  let mut maxLength := 0
  let mut maxTokens := 0
  let mut rankChecks := 0
  let mut pDrops := 0
  let mut zStutters := 0
  let mut d1Drains := 0
  let mut firstFailure : Option Json := none
  let mut firstStutter : Option Json := none
  let mut rows : Array Json := #[]
  for sample in [:count] do
    let holders := sampleHolders ψ q κ pattern sample selective
    let r := run ψ q κ pattern selective holders hψ
    processed := processed+1
    counts := addCount counts r.status
    maxLength := max maxLength r.word.size
    maxTokens := max maxTokens r.maxTokens
    rankChecks := rankChecks+r.rankChecks
    pDrops := pDrops+r.pDrops
    zStutters := zStutters+r.zStutters
    d1Drains := d1Drains+r.d1Drains
    rows := rows.push (Json.mkObj [
      ("index", toJson sample), ("holders", holderKey holders),
      ("status", toJson r.status), ("length", toJson r.word.size)])
    if r.status == "failure" && firstFailure.isNone then
      firstFailure := some (caseJson ψ q κ pattern selective holders hψ r)
    if r.zStutters > 0 && firstStutter.isNone then
      firstStutter := some (caseJson ψ q κ pattern selective holders hψ r)
    if firstFailure.isSome then break
  let summary := Json.mkObj [
    ("mode", toJson "sample_many"), ("psi", toJson ψ), ("q", toJson q),
    ("kappa", toJson κ), ("pattern", toJson pattern),
    ("selective", toJson selective), ("expected", toJson count),
    ("processed", toJson processed), ("counts", toJson counts),
    ("max_length", toJson maxLength), ("max_tokens", toJson maxTokens),
    ("rank_checks", toJson rankChecks), ("p_drops", toJson pDrops),
    ("z_stutters", toJson zStutters), ("d1_drains", toJson d1Drains),
    ("cases", toJson rows), ("first_failure", firstFailure.getD Json.null),
    ("first_stutter", firstStutter.getD Json.null)]
  IO.FS.writeFile out summary.compress
  IO.println s!"sample processed={processed} expected={count} counts={counts} max_length={maxLength} rank_checks={rankChecks} p_drops={pDrops} z_stutters={zStutters} d1_drains={d1Drains}"
  return if firstFailure.isSome || processed != count then 1 else 0

def exhaustiveTwo (ψ q κ pattern : Nat) (selective : Bool)
    (hψ : ψ > 0) (out : String) : IO UInt32 := do
  let n := ψ*q
  let v := 2*ψ*2*(ψ+1)
  let mut counts : List (String × Nat) := []
  let mut processed := 0
  let mut maxLength := 0
  let mut maxTokens := 0
  let mut rankChecks := 0
  let mut pDrops := 0
  let mut zStutters := 0
  let mut d1Drains := 0
  let mut firstLeader : Option Json := none
  let mut firstHole : Option Json := none
  let mut firstZero : Option Json := none
  let mut firstFailure : Option Json := none
  let mut firstStutter : Option Json := none
  for x in [:v] do
    let t := valuation ψ x
    if valuationCode ψ t != x || t.action < 1 || t.action > 2 ||
        t.label ≥ ψ || t.bit > 1 || t.position > ψ then
      IO.eprintln s!"valuation_decode_failed_{x}"
      return 2
  for h1 in [:n] do
    for h2 in [h1+1:n] do
      for x in [:v] do
        for y in [:v] do
          let holders := #[(h1,valuation ψ x),(h2,valuation ψ y)]
          let r := run ψ q κ pattern selective holders hψ
          processed := processed+1
          counts := addCount counts r.status
          maxLength := max maxLength r.word.size
          maxTokens := max maxTokens r.maxTokens
          rankChecks := rankChecks + r.rankChecks
          pDrops := pDrops + r.pDrops
          zStutters := zStutters + r.zStutters
          d1Drains := d1Drains + r.d1Drains
          if r.status == "failure" && firstFailure.isNone then
            firstFailure := some (caseJson ψ q κ pattern selective holders hψ r)
          if r.status == "leader" && firstLeader.isNone then
            firstLeader := some (caseJson ψ q κ pattern selective holders hψ r)
          if r.status == "hole" && firstHole.isNone then
            firstHole := some (caseJson ψ q κ pattern selective holders hψ r)
          if r.status == "token_free" && firstZero.isNone then
            firstZero := some (caseJson ψ q κ pattern selective holders hψ r)
          if r.zStutters > 0 && firstStutter.isNone then
            firstStutter := some (caseJson ψ q κ pattern selective holders hψ r)
          if firstFailure.isSome then break
        if firstFailure.isSome then break
      if firstFailure.isSome then break
    if firstFailure.isSome then break
  let summary := Json.mkObj [
    ("mode", toJson "exhaustive_two"), ("psi", toJson ψ), ("q", toJson q),
    ("kappa", toJson κ), ("pattern", toJson pattern),
    ("selective", toJson selective), ("valuations_per_holder", toJson v),
    ("expected", toJson (n*(n-1)/2*v*v)),
    ("processed", toJson processed), ("counts", toJson counts),
    ("max_length", toJson maxLength), ("max_tokens", toJson maxTokens),
    ("rank_checks", toJson rankChecks),
    ("p_drops", toJson pDrops), ("z_stutters", toJson zStutters),
    ("d1_drains", toJson d1Drains),
    ("first_failure", firstFailure.getD Json.null),
    ("first_leader", firstLeader.getD Json.null),
    ("first_hole", firstHole.getD Json.null),
    ("first_token_free", firstZero.getD Json.null),
    ("first_stutter", firstStutter.getD Json.null)]
  IO.FS.writeFile out summary.compress
  IO.println s!"processed={processed} expected={n*(n-1)/2*v*v} counts={counts} max_length={maxLength} rank_checks={rankChecks} p_drops={pDrops} z_stutters={zStutters} d1_drains={d1Drains}"
  return if firstFailure.isSome || processed != n*(n-1)/2*v*v then 1 else 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["sample",psiS,qS,kS,patternS,guardS,countS,out] =>
    let some ψ := psiS.toNat? | return 2
    let some q := qS.toNat? | return 2
    let some κ := kS.toNat? | return 2
    let some pattern := patternS.toNat? | return 2
    let some guard := guardS.toNat? | return 2
    let some count := countS.toNat? | return 2
    if ψ < 4 || q == 0 || pattern > 1 || guard > 1 then return 2
    if hψ : ψ > 0 then
      sampleBatch ψ q κ pattern (guard == 1) hψ count out
    else return 2
  | [psiS,qS,kS,patternS,guardS,out] =>
    let some ψ := psiS.toNat? | return 2
    let some q := qS.toNat? | return 2
    let some κ := kS.toNat? | return 2
    let some pattern := patternS.toNat? | return 2
    let some guard := guardS.toNat? | return 2
    if ψ < 4 || q == 0 || pattern > 1 || guard > 1 then return 2
    if hψ : ψ > 0 then
      exhaustiveTwo ψ q κ pattern (guard == 1) hψ out
    else return 2
  | _ =>
    IO.eprintln "usage: ... PSI Q KAPPA PATTERN SELECTIVE OUTPUT"
    return 2

end PPLLAstraR5MultiReader

def main (args : List String) : IO UInt32 := PPLLAstraR5MultiReader.main args
