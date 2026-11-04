import Leader.Wu.Birth.ReacquirePhaseMass
import Std.Data.HashMap

set_option autoImplicit false

/-! # Exact census of the ring-four Reacquire cone

Scope: the public B4 Reacquire fixture `BirthB1ReacquirePhaseMass.ringFourReacquire`
(n = 4, psi = 2, kappa = 2, tau = 3, anchor 0) and every configuration reachable from it under the
literal physical step `currentStep2` before an exit.  An exit is absorbing:
* a cap letter: `RowCap2` holds on the served edge (the first-cap target fires on that letter), or
* a Carrier successor: `Carrier` at the tracked anchor (Local3 at anchor 0, tracked count < 2).

`census` is an executable breadth-first enumeration.  The Boolean tests are tied to the
propositions by `capB_iff` and `carrierB_iff`.  States are deduplicated by a 128-bit fingerprint of
their `repr` (two string hashes), so the result is a finite computation, not a kernel proof.

Recorded run (Lean 4.33.1 interpreter, `lean --run`): 88,099 non-exit states, complete;
no non-exit state has tracked count >= 2; every state has an exit word of length <= 5; the exact
exit probability over uniform letters is >= 0.9683 within 32 letters and >= 0.99995 within 64 letters
for every state of the cone (the B4 Reacquire leaf asks for 1/8 within 16 n^2 = 256 letters).

`endpointCensus` evaluates the leaf's own success event (cap within the block, or Carrier at the block
endpoint), with only caps absorbing: the pre-cap reachable set has 102,576 configurations (12,352 of them
Carrier), none has tracked count >= 2, and the minimum over all of them of P(cap within T or Carrier after
T letters) is 0.228 at T = 16, 0.594 at T = 64 and 0.997 at T = 256; the cap alone has probability
0.996 within 256 letters from every state.
Receipt: run/verification/b4-reacquire-ring4-cone-census.txt. -/

namespace B4ReacquireRingFourConeCensus

open PPLL PPLLRepair PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthWaitPassive

abbrev Cfg := BirthB1ReacquirePhaseMass.FC 4 2 2 3
abbrev VCfg := Vector (ExpiringAgentState 2 2 3) 4

theorem hpsi2 : 0 < 2 := by decide
theorem h2 : 2 <= 2 := by decide
theorem hn4 : 4 <= 4 := by decide

abbrev R4 : DirectedRing 4 := BirthPhaseWait2Transfer.boundaryRing4
abbrev A4 : Fin 4 := BirthPhaseWait2Transfer.boundaryAnchor4
abbrev C0 : Cfg := BirthB1ReacquirePhaseMass.ringFourReacquire

def step (C : Cfg) (e : Fin 4) : Cfg :=
  BirthPhaseWait2BlockProgress.currentStep2 hpsi2 h2 R4 C e

/-- Materialize a configuration so that successive steps do not nest closures. -/
def mat (C : Cfg) : VCfg := Vector.ofFn C

def stepV (v : VCfg) (e : Fin 4) : VCfg := mat (step v.get e)

theorem mat_get (C : Cfg) : (mat C).get = C := by
  funext i
  simp only [mat, Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn]
  rfl

theorem stepV_get (v : VCfg) (e : Fin 4) : (stepV v e).get = step v.get e :=
  mat_get _

instance (u : AgentState 2) : Decidable (Metadata u) := by
  unfold Metadata; infer_instance

instance (C : Cfg) (e : Fin 4) :
    Decidable (BirthShortDoneTerminalPassiveR4.RowCap2 hpsi2 h2 2 R4 C e) := by
  unfold BirthShortDoneTerminalPassiveR4.RowCap2; infer_instance

def passiveB (u : AgentState 2) : Bool :=
  decide (Metadata u) && u.wait && (decide (u.write_state = .none) || decide (u.write_state = .depart))

theorem passiveB_iff (u : AgentState 2) : passiveB u = true ↔ Passive u := by
  unfold passiveB Passive InertWriter
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hm, hw⟩, hi⟩
    exact ⟨hm, hw, hi⟩
  · rintro ⟨hm, hw, hi⟩
    exact ⟨⟨hm, hw⟩, hi⟩

def localCarrierB (C : Cfg) : Bool :=
  passiveB (raw (C A4)) && passiveB (raw (C (R4.rightNeighbor A4))) &&
    passiveB (raw (C (R4.rightNeighbor (R4.rightNeighbor A4)))) &&
    (raw (C A4)).label.val == 0 && (raw (C (R4.rightNeighbor A4))).label.val == 1 &&
    (raw (C (R4.rightNeighbor (R4.rightNeighbor A4)))).label.val == 2 % 2

def countB (C : Cfg) : Nat := BirthPhaseWait2BlockProgress.shortCountAt R4 A4 C

def carrierB (C : Cfg) : Bool := localCarrierB C && decide (countB C < 2)

def capB (C : Cfg) (e : Fin 4) : Bool :=
  decide (BirthShortDoneTerminalPassiveR4.RowCap2 hpsi2 h2 2 R4 C e)

theorem capB_iff (C : Cfg) (e : Fin 4) :
    capB C e = true ↔ BirthShortDoneTerminalPassiveR4.RowCap2 hpsi2 h2 2 R4 C e := by
  simp [capB]

theorem localCarrierB_iff (C : Cfg) :
    localCarrierB C = true ↔
      BirthPhaseWait2BlockProgress.LocalCarrier hpsi2 h2 hn4 R4 A4 C := by
  unfold localCarrierB BirthPhaseWait2BlockProgress.LocalCarrier
    BirthPhaseWait2Transfer.LocalWait2Carrier
  simp only [Bool.and_eq_true, beq_iff_eq, passiveB_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨h0, h1⟩, h2'⟩, l0⟩, l1⟩, l2⟩
    exact ⟨h0, h1, h2', l0, l1, l2⟩
  · intro h
    exact ⟨⟨⟨⟨⟨h.pass0, h.pass1⟩, h.pass2⟩, h.lab0⟩, h.lab1⟩, h.lab2⟩

theorem carrierB_iff (C : Cfg) :
    carrierB C = true ↔ BirthPhaseWait2BlockProgress.Carrier hpsi2 h2 hn4 R4 A4 C := by
  unfold carrierB BirthPhaseWait2BlockProgress.Carrier
  simp only [Bool.and_eq_true, decide_eq_true_eq, localCarrierB_iff]
  rfl

def key (C : Cfg) : UInt64 × UInt64 :=
  let s := toString (repr (List.ofFn C))
  (s.hash, (String.ofList s.toList.reverse).hash)

def brief (u : AgentState 2) : String :=
  s!"L={u.leader} st={repr u.state} lab={u.label.val} cnt={u.count} wait={u.wait} bul={u.bullet} sh={u.shield} rc={u.reset_cmd} echo={u.echo} meta={decide (Metadata u)}"

/-- Breadth-first census of the non-exit cone of `C0`, then shortest exit distances and exact exit
probabilities (uniform letters) at dyadic horizons.  Writes `reacq-census.txt`. -/
def census (maxStates : Nat) : IO Unit := do
  let out ← IO.FS.Handle.mk "reacq-census.txt" .write
  let say (s : String) : IO Unit := do out.putStrLn s; out.flush; IO.println s
  let V0 := mat C0
  let mut idx : Std.HashMap (UInt64 × UInt64) Nat := {}
  let mut states : Array VCfg := #[V0]
  idx := idx.insert (key V0.get) 0
  let mut succ : Array (Array Int) := #[]
  let mut i := 0
  while h : i < states.size ∧ states.size < maxStates do
    let V := states[i]'h.1
    let C := V.get
    let mut row : Array Int := #[]
    for e in List.finRange 4 do
      if capB C e then
        row := row.push (-1)
      else
        let DV := stepV V e
        let D := DV.get
        if carrierB D then
          row := row.push (-2)
        else
          let k := key D
          match idx[k]? with
          | some j => row := row.push j
          | none =>
            idx := idx.insert k states.size
            row := row.push states.size
            states := states.push DV
    succ := succ.push row
    i := i + 1
  let N := succ.size
  say s!"expanded={N} discovered={states.size} complete={N == states.size}"
  let highCount := (states.toList.filter (fun V => countB V.get >= 2)).length
  say s!"nonexit states with tracked count>=2: {highCount}"
  let inf := 1000000000
  let mut dist : Array Nat := Array.replicate states.size inf
  let mut changed := true
  while changed do
    changed := false
    for s in [0:N] do
      let row := succ[s]!
      let mut best := dist[s]!
      for v in row.toList do
        let c := if v < 0 then 1 else (let d := dist[v.toNat]!; if d >= inf then inf else d + 1)
        if c < best then best := c
      if best < dist[s]! then
        dist := dist.set! s best
        changed := true
  let trapped := ((List.range N).filter (fun s => dist[s]! >= inf)).length
  let maxd := (List.range N).foldl (fun m s => if dist[s]! < inf && dist[s]! > m then dist[s]! else m) 0
  say s!"dist(C0)={dist[0]!} max finite dist={maxd} trapped={trapped}"
  let mut p : Array Float := Array.replicate states.size 0.0
  let checkpoints := [4, 8, 16, 32, 64, 128, 256]
  for t in [1:257] do
    let mut q : Array Float := Array.replicate states.size 0.0
    for s in [0:N] do
      let row := succ[s]!
      let mut acc : Float := 0.0
      for v in row.toList do
        acc := acc + (if v < 0 then 1.0 else p[v.toNat]!)
      q := q.set! s (acc / 4.0)
    p := q
    if checkpoints.contains t then
      let minp := (List.range N).foldl (fun m s => if p[s]! < m then p[s]! else m) 1.0
      say s!"T={t}: P_exit(C0)={p[0]!} min over cone={minp}"
  let capEdges := (succ.toList.map (fun r => (r.toList.filter (· == -1)).length)).foldl (· + ·) 0
  let carEdges := (succ.toList.map (fun r => (r.toList.filter (· == -2)).length)).foldl (· + ·) 0
  say s!"cap letters={capEdges} carrier successors={carEdges}"
  for j in List.finRange 4 do
    say s!"C0 site {j.val}: {brief (raw (C0 j))} stall={(C0 j).stall}"


instance : Inhabited VCfg := ⟨mat C0⟩

/-- Endpoint form of the Reacquire leaf (`FallbackReacquireExit`: cap within the block, or Carrier at the
block endpoint).  Only cap letters are absorbing; the whole pre-cap reachable set of `C0` is enumerated
and `p_T(s) = P(cap within T letters or Carrier after T letters)` is computed by value iteration from
`p_0 = [Carrier]`.  Also reports the pure cap probability.  Writes `reacq-endpoint.txt`. -/
def endpointCensus (maxStates : Nat) : IO Unit := do
  let out ← IO.FS.Handle.mk "reacq-endpoint.txt" .write
  let say (s : String) : IO Unit := do out.putStrLn s; out.flush; IO.println s
  let V0 := mat C0
  let mut idx : Std.HashMap (UInt64 × UInt64) Nat := {}
  let mut states : Array VCfg := #[V0]
  idx := idx.insert (key V0.get) 0
  let mut succ : Array (Array Int) := #[]
  let mut i := 0
  while h : i < states.size ∧ states.size < maxStates do
    let V := states[i]'h.1
    let C := V.get
    let mut row : Array Int := #[]
    for e in List.finRange 4 do
      if capB C e then
        row := row.push (-1)
      else
        let DV := stepV V e
        let k := key DV.get
        match idx[k]? with
        | some j => row := row.push j
        | none =>
          idx := idx.insert k states.size
          row := row.push states.size
          states := states.push DV
    succ := succ.push row
    i := i + 1
  let N := succ.size
  say s!"expanded={N} discovered={states.size} complete={N == states.size}"
  let car : Array Bool := states.map (fun V => carrierB V.get)
  let nCar := (car.toList.filter id).length
  let bad := (states.toList.filter (fun V => countB V.get >= 2)).length
  say s!"carrier states={nCar}; pre-cap states with tracked count>=2 (neither Carrier nor Reacquire)={bad}"
  let checkpoints := [4, 8, 16, 32, 64, 128, 256]
  let mut p : Array Float := car.map (fun b => if b then 1.0 else 0.0)
  for t in [1:257] do
    let mut q : Array Float := Array.replicate states.size 0.0
    for s in [0:N] do
      let row := succ[s]!
      let mut acc : Float := 0.0
      for v in row.toList do
        acc := acc + (if v < 0 then 1.0 else p[v.toNat]!)
      q := q.set! s (acc / 4.0)
    p := q
    if checkpoints.contains t then
      let mut minR : Float := 1.0
      let mut minAll : Float := 1.0
      for s in [0:N] do
        if p[s]! < minAll then minAll := p[s]!
        if !car[s]! && countB (states[s]!).get < 2 && p[s]! < minR then minR := p[s]!
      say s!"T={t}: endpoint leaf P(C0)={p[0]!} min over Reacquire states={minR} min over all={minAll}"
  let mut c : Array Float := Array.replicate states.size 0.0
  for t in [1:257] do
    let mut q : Array Float := Array.replicate states.size 0.0
    for s in [0:N] do
      let row := succ[s]!
      let mut acc : Float := 0.0
      for v in row.toList do
        acc := acc + (if v < 0 then 1.0 else c[v.toNat]!)
      q := q.set! s (acc / 4.0)
    c := q
    if checkpoints.contains t then
      let minc := (List.range N).foldl (fun m s => if c[s]! < m then c[s]! else m) 1.0
      say s!"T={t}: P(cap within T | C0)={c[0]!} min over all={minc}"

end B4ReacquireRingFourConeCensus
