import Lean.Data.Json
import Leader.Wu.ZeroDivisible.OverwritingGeneration
import Leader.Wu.Sim.RawCodec
import Leader.Wu.ZeroDivisible.CheckRepair

/-!
Finite regression harness for the round-5 CHECK repair. Word builders mirror
the source formulas in `ZZSimClaims`; this file does not import that executable
module because it defines a root `main`. Candidate transition bindings and
fixtures use `PPLLAstraR5Repair.pipeline` directly.
-/

namespace PPLLAstraR5Regression

open PPLL

instance : Inhabited MainState := ⟨.none⟩

def fwdEdges (base ψ : Nat) : List Nat :=
  (List.range (ψ - 1)).map (base + ·)

def revEdges (base ψ : Nat) : List Nat :=
  ((List.range (ψ - 2)).map (base + ·)).reverse

/-- ZDIV §11's internal-edge Recruitable word. -/
def wB (base ψ : Nat) : List Nat :=
  fwdEdges base ψ ++ (List.range (ψ - 1)).flatMap (fun _ => revEdges base ψ)

/-- ZDIV §10's fresh-signal generation word. -/
def genWord (base ψ : Nat) : List Nat :=
  fwdEdges base ψ ++ revEdges base ψ

def dG (base ψ : Nat) : List Nat :=
  fwdEdges base ψ ++ [base + (ψ - 2)]

def fG (base ψ n : Nat) : List Nat :=
  [base, (base + n - 1) % n] ++ dG base ψ

/-- The repaired writer word `D ++ F*`; D++F alone has a known failure. -/
def wordDFStar (n ψ : Nat) : List Nat :=
  let m := n / ψ
  (List.range m).flatMap (fun g => dG (g * ψ) ψ) ++
    (List.range m).flatMap (fun g =>
      (List.range (ψ - 1)).flatMap (fun _ => fG (g * ψ) ψ n))

/-- Physical-edge evaluator using the supplied candidate's actual local pair
transition. `Nat` words are converted to physical ring indices modulo `n`. -/
def runWord {n ψ : Nat} (hn : 0 < n)
    (tr : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (C : Fin n → AgentState ψ) (w : List Nat) : Fin n → AgentState ψ :=
  let protocol : PopulationProtocol :=
    { Q := AgentState ψ, Y := Bool, transition := tr, output := fun u => u.leader }
  w.foldl (fun D e => protocol.step (⟨hn⟩ : DirectedRing n) D
    ⟨e % n, Nat.mod_lt e hn⟩) C

def recruitable {ψ : Nat} (u : AgentState ψ) : Prop :=
  u.path = .bot ∨ (u.state ≠ .produce ∧ u.state ≠ .done)

def freshShape {ψ n : Nat} (C : Fin n → AgentState ψ)
    (base : Nat) (hn : 0 < n) : Prop :=
  (C ⟨base % n, Nat.mod_lt _ hn⟩).wait = true ∧
  ∀ k : Fin ψ,
    let u := C ⟨(base + k.val) % n, Nat.mod_lt _ hn⟩
    (∃ b ≤ 1, u.path = .some k.val b) ∧
    u.path2 = none ∧ u.state = .depart

def sourceCfg : PPLLFableZDiv.Cfg :=
  { wave := true, outcome := true, arrive := true }

def pairStep {ψ : Nat} (hψ : 0 < ψ) (selective : Bool)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  PPLLAstraR5Repair.pipeline hψ 2 { selective := selective } l r

def sourceStep {ψ : Nat} (hψ : 0 < ψ)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  PPLLFableZDiv.pipeline hψ 2 sourceCfg l r

def defaultAgent {ψ : Nat} (_hψ : 0 < ψ) (label : Fin ψ) : AgentState ψ :=
  { leader := false, probe := false, phase := false, bit := false, wait := false
    state := .none, path := .bot, reset := false, carry := false, count := 0
    label := label, h_field := false
    path2 := none, path3 := none, path4 := none, path5 := none
    p := false, p_carry := false, reset_cmd := false, echo := false
    signal_B := 0, bullet := 0, shield := false
    write_state := .none, write := .none
    last := false, last_set := false, last_unset := false
    b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }

/-- Array version of the physical pair interaction, with no copied pipeline. -/
def stepArr {ψ : Nat} (hψ : 0 < ψ) (selective : Bool)
    (c : Array (AgentState ψ)) (e : Nat) : Array (AgentState ψ) :=
  let n := c.size
  let fallback := defaultAgent hψ ⟨0, hψ⟩
  let (l, r) := pairStep hψ selective (c.getD e fallback)
    (c.getD ((e + 1) % n) fallback)
  (c.set! e l).set! ((e + 1) % n) r

def sourceStepArr {ψ : Nat} (hψ : 0 < ψ)
    (c : Array (AgentState ψ)) (e : Nat) : Array (AgentState ψ) :=
  let n := c.size
  let fallback := defaultAgent hψ ⟨0, hψ⟩
  let (l, r) := sourceStep hψ (c.getD e fallback)
    (c.getD ((e + 1) % n) fallback)
  (c.set! e l).set! ((e + 1) % n) r

def anyLeader {ψ : Nat} (c : Array (AgentState ψ)) : Bool :=
  c.any (·.leader)

def allBounded {ψ : Nat} (c : Array (AgentState ψ)) : Bool :=
  c.all (PPLLSimRawCodec.inProtocolDomainB 2)

def leaderCount {ψ : Nat} (c : Array (AgentState ψ)) : Nat :=
  c.foldl (fun count u => count + if u.leader then 1 else 0) 0

def bitsOf {ψ : Nat} (c : Array (AgentState ψ)) : Array Bool :=
  c.map (·.bit)

def recruitableB {ψ : Nat} (u : AgentState ψ) : Bool :=
  decide (u.path = .bot) ||
    (!decide (u.state = .produce) && !decide (u.state = .done))

def freshShapeB {ψ : Nat} (hψ : 0 < ψ)
    (c : Array (AgentState ψ)) (base : Nat) : Bool :=
  let fallback := defaultAgent hψ ⟨0, hψ⟩
  (c.getD base fallback).wait &&
    (List.range ψ).all (fun k =>
      let u := c.getD (base + k) fallback
      (match u.path with
        | .some l b => l == k && (b == 0 || b == 1)
        | .bot => false) &&
      decide (u.path2 = none) && decide (u.state = .depart))

/-- A deterministic small-domain sample with all payloads in protocol range.
This covers control/writer debris without claiming statistical completeness. -/
def sampleState {ψ : Nat} (hψ : 0 < ψ) (seed i : Nat) : AgentState ψ :=
  let label : Fin ψ := ⟨i % ψ, Nat.mod_lt i hψ⟩
  let u := defaultAgent hψ label
  let x := seed * 1103515245 + i * 2654435761 + 17
  let states : Array MainState :=
    #[.produce, .done, .depart, .none, .lock, .compare1,
      .compare2, .CHECK_ready, .equal, .larger, .less,
      .eliminate_signal, .toss, .toss_done]
  { u with
    bit := x % 2 == 0
    wait := x % 3 == 0
    state := states[x % states.size]!
    path := if x % 4 == 0 then .bot else .some (i % ψ) (x % 2)
    count := x % 3
    reset_cmd := x % 11 == 0
    echo := x % 7 == 0
    p_carry := x % 13 == 0
    path2 := if x % 3 == 0 then
      some ⟨x % ψ, x % 2, x % (ψ + 1), 1 + x % 6⟩ else none
    path3 := if x % 5 == 0 then some ⟨x % ψ, x % 2, x % 2⟩ else none
    write := if x % 3 == 0 then .overwrite else .none
    bullet := ⟨x % 3, Nat.mod_lt x (by decide)⟩
    signal_B := ⟨x % 2, Nat.mod_lt x (by decide)⟩ }

def sampleRing {ψ : Nat} (hψ : 0 < ψ) (n seed : Nat) :
    Array (AgentState ψ) :=
  ((List.range n).map (sampleState hψ seed)).toArray

def runWordArr {ψ : Nat} (hψ : 0 < ψ) (selective : Bool)
    (c : Array (AgentState ψ)) (w : List Nat) :
    Array (AgentState ψ) × Bool :=
  w.foldl (fun (q : Array (AgentState ψ) × Bool) e =>
    let q' := stepArr hψ selective q.1 e
    (q', q.2 || anyLeader q')) (c, anyLeader c)

def enforceL3 {ψ : Nat} (hψ : 0 < ψ)
    (c : Array (AgentState ψ)) : Array (AgentState ψ) := Id.run do
  let mut c := c
  for k in [:ψ] do
    let u := c.getD k (defaultAgent hψ ⟨0, hψ⟩)
    let u := { u with reset_cmd := false, p_carry := (if k < ψ - 1 then false else u.p_carry) }
    let u := if k == 0 then { u with wait := false, path := .bot }
      else if !recruitableB u then { u with path := .bot } else u
    c := c.set! k u
  return c

/-- One sample per word family; a failure is an observed counterexample,
whereas a pass is only a bounded sample. -/
def sampleChecks {ψ : Nat} (hψ : 0 < ψ) (selective : Bool)
    (n seed tailSteps : Nat) : Bool × Bool × Bool := Id.run do
  let c := sampleRing hψ n seed
  let (wbPost, wbLeader) := runWordArr hψ selective c (wB 0 ψ)
  let wbOK := wbLeader || (List.range ψ).all
    (fun k => recruitableB (wbPost.getD k (defaultAgent hψ ⟨0, hψ⟩)))
  let entrance := enforceL3 hψ c
  let (genPost, genLeader) := runWordArr hψ selective entrance (genWord 0 ψ)
  let genOK := genLeader || freshShapeB hψ genPost 0
  let wordResult := runWordArr hψ selective c (wordDFStar n ψ)
  let mut afterWord := wordResult.1
  let leaderSeen := wordResult.2
  let mut writerOK := true
  if !leaderSeen then
    let mut rng : UInt64 := UInt64.ofNat (seed * 1000003 + 1)
    for _ in [:tailSteps] do
      if anyLeader afterWord then break
      rng := rng ^^^ (rng <<< 13)
      rng := rng ^^^ (rng >>> 7)
      rng := rng ^^^ (rng <<< 17)
      let bits := bitsOf afterWord
      afterWord := stepArr hψ selective afterWord ((rng % UInt64.ofNat n).toNat)
      if !anyLeader afterWord && bitsOf afterWord != bits then
        writerOK := false
        break
  return (wbOK, genOK, writerOK)

def runSample (selective : Bool) (ψ n samples tailSteps : Nat) : IO UInt32 := do
  if hψ : 0 < ψ then
    if ψ < 2 || n == 0 || n % ψ != 0 then
      IO.eprintln "requires ψ>=2 and positive n divisible by ψ"
      return 2
    let mut failW := 0
    let mut failG := 0
    let mut failF := 0
    let mut invalidSeeds := 0
    for seed in [:samples] do
      if !allBounded (sampleRing hψ n seed) then
        invalidSeeds := invalidSeeds + 1
        continue
      let (w, g, f) := sampleChecks hψ selective n seed tailSteps
      if !w then failW := failW + 1
      if !g then failG := failG + 1
      if !f then failF := failF + 1
    IO.println s!"sample ψ={ψ} n={n} selective={selective} seeds={samples} invalid_seeds={invalidSeeds} tail={tailSteps} W_B_fail={failW} L3_fail={failG} DFstar_fail={failF}"
    return if failW + failG + failF + invalidSeeds == 0 then 0 else 1
  else
    IO.eprintln "ψ must be positive"
    return 2

/-- Read a raw-state fixture using the same codec as the source simulator. -/
def readFixture (ψ : Nat) (path : System.FilePath) : IO (Array (AgentState ψ)) := do
  let raw ← IO.FS.readFile path
  let j ← IO.ofExcept (Lean.Json.parse raw)
  let arr ← IO.ofExcept j.getArr?
  let mut c := #[]
  for je in arr do
    c := c.push (← IO.ofExcept (PPLLSimRawCodec.decodeState (psi := ψ) je))
  return c

def readSchedule (path : System.FilePath) : IO (Array Nat) := do
  let raw ← IO.FS.readFile path
  let j ← IO.ofExcept (Lean.Json.parse raw)
  let arr ← IO.ofExcept j.getArr?
  let mut w := #[]
  for je in arr do
    w := w.push (← IO.ofExcept je.getNat?)
  return w

def parseWord (s : String) : Array Nat :=
  (s.splitOn ",").toArray.filterMap (·.trimAscii.toString.toNat?)

def clean2n4 : Array (AgentState 2) :=
  let hψ : 0 < 2 := by decide
  #[defaultAgent hψ 0, defaultAgent hψ 1,
    defaultAgent hψ 0, defaultAgent hψ 1]

def clean2n2 : Array (AgentState 2) :=
  let hψ : 0 < 2 := by decide
  #[{ defaultAgent hψ 0 with state := .depart, path := .some 0 0 },
    { defaultAgent hψ 1 with state := .depart, path := .some 1 0 }]

def clean2n4Word : Array Nat := #[0,1,0,2,1,2]
def clean2n2Word : Array Nat := #[1,0,1,0,0,1,1,1,0]

def replaySeed {ψ : Nat} (hψ : 0 < ψ) (selective : Bool)
    (seed : Array (AgentState ψ)) (word : Array Nat) : IO UInt32 := do
  let mut candidate := seed
  let mut original := seed
  let initialLeaders := leaderCount seed
  let mut firstDifference : Option Nat := none
  let mut candidateGain : Option Nat := none
  let mut originalGain : Option Nat := none
  for t in [:word.size] do
    let e := word[t]!
    candidate := stepArr hψ selective candidate e
    original := sourceStepArr hψ original e
    if firstDifference.isNone && !decide (candidate = original) then
      firstDifference := some (t + 1)
    if candidateGain.isNone && leaderCount candidate > initialLeaders then
      candidateGain := some (t + 1)
    if originalGain.isNone && leaderCount original > initialLeaders then
      originalGain := some (t + 1)
  IO.println s!"replay ψ={ψ} n={seed.size} selective={selective} steps={word.size} initial_leaders={initialLeaders} first_difference={firstDifference} candidate_gain={candidateGain} original_gain={originalGain} candidate_final_leaders={leaderCount candidate} original_final_leaders={leaderCount original}"
  return if candidateGain.isSome then 0 else 1

/-- A fixed clean word is replayed through the candidate and the original
zdivOWF; the first complete-state divergence is reported, including its
physical edge. A shared trace certifies unchanged behavior for that word. -/
def replayWord (selective : Bool) (ψ : Nat) (path : System.FilePath)
    (word : Array Nat) : IO UInt32 := do
  if hψ : 0 < ψ then
    let seed ← readFixture ψ path
    if seed.isEmpty then
      IO.eprintln "empty fixture"
      return 2
    replaySeed hψ selective seed word
  else
    IO.eprintln "ψ must be positive"
    return 2

/-- Saved ψ=3,n=12 D++F failure fixture replayed through corrected D++F*
and its recorded random tail. -/
def replayDFStar (selective : Bool) (ringPath schedulePath : System.FilePath) :
    IO UInt32 := do
  let c ← readFixture 3 ringPath
  let sched ← readSchedule schedulePath
  if c.size != 12 then
    IO.eprintln "saved fixture must have n=12"
    return 2
  let mut q := c
  let mut leaderSeen := anyLeader q
  for e in wordDFStar 12 3 do
    q := stepArr (by decide : 0 < 3) selective q e
    leaderSeen := leaderSeen || anyLeader q
  let mut failure : Option Nat := none
  if !leaderSeen then
    for t in [:sched.size] do
      let before := bitsOf q
      q := stepArr (by decide : 0 < 3) selective q sched[t]!
      if anyLeader q then break
      if bitsOf q != before then
        failure := some (t + 1)
        break
  IO.println s!"saved-dfstar selective={selective} word_len={(wordDFStar 12 3).length} tail_len={sched.size} leader_in_word={leaderSeen} leader_at_stop={anyLeader q} first_leaderless_bit_change={failure}"
  return if failure.isNone then 0 else 1

/-- One-row terminal F1 hold using the actual pre-CHECK moveSourceF. -/
def terminalF1Check (_selective : Bool) : Bool :=
  let hψ : 0 < 4 := by decide
  let head := defaultAgent hψ ⟨0, by decide⟩
  let held (s : MainState) :=
    let last := { defaultAgent hψ ⟨3, by decide⟩ with
      state := s, path := .some 3 0 }
    let moved := PPLLFableZDiv.moveSourceF hψ PPLLAstraR5Repair.sourceCfg last head
    moved.1.path == .some 3 0
  held .larger && held .less

end PPLLAstraR5Regression

open PPLLAstraR5Regression in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["sample", mode, ψ, n, count, tail] =>
    match ψ.toNat?, n.toNat?, count.toNat?, tail.toNat? with
    | some ψ, some n, some count, some tail =>
      runSample (mode == "selective") ψ n count tail
    | _, _, _, _ => return 2
  | ["replay", mode, ψ, path, word] =>
    match ψ.toNat? with
    | some ψ => replayWord (mode == "selective") ψ path (parseWord word)
    | none => return 2
  | ["clean2", mode] =>
    let a ← replaySeed (by decide : 0 < 2) (mode == "selective")
      clean2n4 clean2n4Word
    let b ← replaySeed (by decide : 0 < 2) (mode == "selective")
      clean2n2 clean2n2Word
    return if a == 0 && b == 0 then 0 else 1
  | ["dfstar", mode, ringPath, schedPath] =>
    replayDFStar (mode == "selective") ringPath schedPath
  | ["f1", mode] =>
    IO.println s!"terminal F1 hold: {terminalF1Check (mode == "selective")}"
    return if terminalF1Check (mode == "selective") then 0 else 1
  | _ =>
    IO.eprintln "usage: sample MODE PSI N COUNT TAIL | replay MODE PSI FIXTURE WORD | clean2 MODE | dfstar MODE RING_JSON SCHED_JSON | f1 MODE"
    return 2
