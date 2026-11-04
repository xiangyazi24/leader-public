import Lean.Data.Json
import Leader.Wu.Protocol.State
import Leader.Wu.ZeroDivisible.OverwritingGeneration
import Leader.Wu.Sim.RawCodec

/-!
# Simulation falsification of three zdivOWF claims

Design-exploration tool (G6.2 Z-div, `run/verification/g62/fab/ZDIV.md`), not a proof
certificate.  Random + adversarial Monte-Carlo testing of three claims about
`zdivOWF = PPLLFableZDiv.pipeline hψ κ {wave := true, outcome := true, arrive := true}`
(the same variant as the `zdivOWF` census entry), on the real `AgentState ψ` domain and the
real `pipeline` transition (no reimplementation).  κ is fixed to 2, matching the rest of the
G6.2 census family.

* Claim 1 (ZDIV §11, "B"): `W_B(G) = F_G ++ R_G^(ψ-1)` on one group's internal
  edges only, `F_G = e0,…,e(ψ-2)`, `R_G = e(ψ-3),…,e0`, ends in a leader somewhere on the ring
  or with every cell of `G` `Recruitable` (`path = ⊥ ∨ state ∉ {produce, done}`).
* Claim 2 (ZDIV §14, writer drain): `D ++ F` (`D` = per-group forward sweep with the
  terminal edge repeated, `F` = per-group `[E(g,0), B_g] ++ D_g`) either births on some prefix or
  leaves the ring `WriterBitFrozen`: no later leaderless interaction changes any cell's `bit`.
  Tested by a long random schedule after `D ++ F` (stopping the bit check once a leader
  appears). `psi = 1` is reported separately (expected six-service bit-flip cycle, ZDIV §14).
* Claim 3 (ZDIV §10, "L3-shape"): under `FreshShape`'s hypotheses (head
  `wait = false ∧ path = ⊥`, every other cell of the group `Recruitable`, no `reset_cmd` in the
  group, no `p_carry` on a non-terminal cell), the word
  `GEN = e_h,…,e_{t-1},e_{t-2},…,e_h` (`2ψ-3` edges) ends in a leader somewhere or in
  `FreshShape` (head `wait = true`, every cell `i`: `path = some i.val b` for some `b ≤ 1`,
  `path2 = none`, `state = depart`).

All three words touch only internal or one-group-boundary edges; states outside the tested
group(s) are otherwise-arbitrary debris (random field values within the declared domain
ranges of `AgentState.inProtocolDomain`, or a fixed adversarial pattern), always leaderless and
perfectly labelled (`label i = i mod ψ`).
-/

set_option autoImplicit false

open Lean

namespace ZZSimClaims

/-- The variant under test: `zdivOWF` (census name), `PPLLFableZDiv.variants` entry
`("zdivOWF", { wave := true, outcome := true, arrive := true })`. -/
def cfg : PPLLFableZDiv.Cfg := { wave := true, outcome := true, arrive := true }

def K : Nat := 2

/-! ## PRNG (xorshift64, same generator as `RulerWalk.xorshift`) -/

abbrev Rng := UInt64

def xorshift (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

def nextNat (g : Rng) (bound : Nat) : Rng × Nat :=
  let g := xorshift g
  (g, (g % UInt64.ofNat (max bound 1)).toNat)

def nextBool (g : Rng) : Rng × Bool :=
  let (g, v) := nextNat g 2
  (g, v == 1)

/-- Uniform in `[-1, ψ-1]` (ψ+1 choices), the `path4`/`path5` label domain. -/
def nextPath45Label (g : Rng) (ψ : Nat) : Rng × Int :=
  let (g, v) := nextNat g (ψ + 1)
  (g, Int.ofNat v - 1)

def finOfNatBound (k v : Nat) (hk : 0 < k) : Fin k := ⟨v % k, Nat.mod_lt v hk⟩

instance : Inhabited MainState := ⟨.none⟩
instance : Inhabited WriteState := ⟨.none⟩
instance : Inhabited WriteAction := ⟨.none⟩

/-- A trivial, well-formed `AgentState` (needed only as an `Array.getD` fallback that is never
actually returned, since every index used is in bounds by construction; `AgentState ψ` has no
blanket `Inhabited ψ` instance since `AgentState 0` is empty). -/
def defaultAgentState {ψ : Nat} (hψ : ψ > 0) : AgentState ψ :=
  { leader := false, probe := false, phase := false, bit := false, wait := false
    , state := .none, path := .bot, reset := false, carry := false, count := 0
    , label := ⟨0, hψ⟩, h_field := false, path2 := none, path3 := none, path4 := none
    , path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false
    , signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩, shield := false
    , write_state := .none, write := .none, last := false, last_set := false
    , last_unset := false, b_carry := false, gen_ws := false, ws_echo := false
    , signal_ws := false }

/-- Bounds-safe accessor for an `AgentState` array (see `defaultAgentState`). -/
def getA {ψ : Nat} (hψ : ψ > 0) (c : Array (AgentState ψ)) (i : Nat) : AgentState ψ :=
  c.getD i (defaultAgentState hψ)

/-! ## Random / adversarial fields within `inProtocolDomain` ranges -/

def allMainStates : Array MainState :=
  #[.produce, .done, .depart, .none, .congest, .lock, .compare1, .compare2,
    .eliminate_signal, .CHECK_ready, .equal, .larger, .less, .toss, .toss_done]

def allWriteStates : Array WriteState :=
  #[.depart, .ready, .increment_WS, .increment_WS_done, .done, .equal, .larger, .less,
    .produce, .overwrite, .move_flip, .move, .increment_group, .none]

def allWriteActions : Array WriteAction :=
  #[.overwrite, .move_flip, .move, .increment_group, .none]

def randMainState (g : Rng) : Rng × MainState :=
  let (g, i) := nextNat g allMainStates.size; (g, allMainStates[i]!)

def randWriteState (g : Rng) : Rng × WriteState :=
  let (g, i) := nextNat g allWriteStates.size; (g, allWriteStates[i]!)

def randWriteAction (g : Rng) : Rng × WriteAction :=
  let (g, i) := nextNat g allWriteActions.size; (g, allWriteActions[i]!)

def randPathInfo (g : Rng) (ψ : Nat) : Rng × PathInfo :=
  let (g, z) := nextBool g
  if z then (g, .bot)
  else
    let (g, l) := nextNat g ψ
    let (g, b) := nextNat g 2
    (g, .some l b)

def randPath2 (g : Rng) (ψ : Nat) : Rng × Option Path2Info :=
  let (g, z) := nextBool g
  if z then (g, none)
  else
    let (g, l) := nextNat g ψ
    let (g, b) := nextNat g 2
    let (g, p) := nextNat g (ψ + 1)
    let (g, a) := nextNat g 6
    (g, some { label := l, bit := b, position := p, action := a + 1 })

def randPath3 (g : Rng) (ψ : Nat) : Rng × Option Path3Info :=
  let (g, z) := nextBool g
  if z then (g, none)
  else
    let (g, l) := nextNat g ψ
    let (g, b) := nextNat g 2
    let (g, f) := nextNat g 2
    (g, some { label := l, bit := b, flag := f })

def randPath45 (g : Rng) (ψ : Nat) : Rng × Option (Int × Nat) :=
  let (g, z) := nextBool g
  if z then (g, none)
  else
    let (g, l) := nextPath45Label g ψ
    let (g, b) := nextNat g 2
    (g, some (l, b))

/-- A fully random `AgentState`, all fields within their declared domain ranges, with
`label`/`leader` fixed by the caller (perfectly labelled, leaderless). -/
def randAgentState (g : Rng) (ψ κ : Nat) (lbl : Fin ψ) (leader : Bool) : Rng × AgentState ψ :=
  let (g, probe) := nextBool g
  let (g, phase) := nextBool g
  let (g, bit) := nextBool g
  let (g, wait) := nextBool g
  let (g, state) := randMainState g
  let (g, path) := randPathInfo g ψ
  let (g, reset) := nextBool g
  let (g, carry) := nextBool g
  let (g, count) := nextNat g (κ + 1)
  let (g, h_field) := nextBool g
  let (g, path2) := randPath2 g ψ
  let (g, path3) := randPath3 g ψ
  let (g, path4) := randPath45 g ψ
  let (g, path5) := randPath45 g ψ
  let (g, p) := nextBool g
  let (g, p_carry) := nextBool g
  let (g, reset_cmd) := nextBool g
  let (g, echo) := nextBool g
  let (g, sbv) := nextNat g 2
  let (g, blv) := nextNat g 3
  let (g, shield) := nextBool g
  let (g, write_state) := randWriteState g
  let (g, write) := randWriteAction g
  let (g, last) := nextBool g
  let (g, last_set) := nextBool g
  let (g, last_unset) := nextBool g
  let (g, b_carry) := nextBool g
  let (g, gen_ws) := nextBool g
  let (g, ws_echo) := nextBool g
  let (g, signal_ws) := nextBool g
  (g, { leader := leader, probe, phase, bit, wait, state, path, reset, carry, count,
        label := lbl, h_field, path2, path3, path4, path5, p, p_carry, reset_cmd, echo,
        signal_B := finOfNatBound 2 sbv (by decide), bullet := finOfNatBound 3 blv (by decide),
        shield, write_state, write, last, last_set, last_unset, b_carry, gen_ws, ws_echo,
        signal_ws })

/-- A leaderless, perfectly labelled ring of `n` cells with independently random fields. -/
def randRing (g0 : Rng) (n ψ κ : Nat) (hψ : ψ > 0) : Rng × Array (AgentState ψ) :=
  (List.range n).foldl
    (fun (acc : Rng × Array (AgentState ψ)) i =>
      let (g, arr) := acc
      let lbl : Fin ψ := ⟨i % ψ, Nat.mod_lt i hψ⟩
      let (g', s) := randAgentState g ψ κ lbl false
      (g', arr.push s))
    (g0, #[])

/-- Number of deterministic adversarial rings tried before the random sweep. -/
def advCount : Nat := 30

/-- Deterministic adversarial ring, parameterised by `which < advCount`; cycles every enum
field through its full range and every optional field through a fixed non-default pattern,
phase-shifted by `which` so consecutive cells differ. Always leaderless, perfectly labelled. -/
def advRing (ψ κ n which : Nat) (hψ : ψ > 0) : Array (AgentState ψ) :=
  ((List.range n).map fun i =>
    let lbl : Fin ψ := ⟨i % ψ, Nat.mod_lt i hψ⟩
    let st := allMainStates[(i + which) % allMainStates.size]!
    let pathBot := (i + which) % 3 == 0
    let path : PathInfo := if pathBot then .bot else .some (i % ψ) ((i + which) % 2)
    ({ leader := false, probe := which % 2 == 0, phase := which % 3 == 0
       , bit := (i + which) % 2 == 0, wait := which % 2 == 1, state := st, path := path
       , reset := which % 4 == 0, carry := which % 5 == 0, count := which % (κ + 1)
       , label := lbl, h_field := which % 2 == 0
       , path2 := if which % 5 == 0 then
           some { label := i % ψ, bit := which % 2, position := which % (ψ + 1)
                , action := 1 + which % 6 } else none
       , path3 := if which % 6 == 0 then
           some { label := i % ψ, bit := which % 2, flag := which % 2 } else none
       , path4 := if which % 7 == 0 then some (Int.ofNat (i % ψ), which % 2) else none
       , path5 := if which % 7 == 3 then some (Int.ofNat (i % ψ), which % 2) else none
       , p := which % 2 == 0, p_carry := which % 3 == 1, reset_cmd := which % 3 == 2
       , echo := which % 2 == 1, signal_B := finOfNatBound 2 which (by decide)
       , bullet := finOfNatBound 3 which (by decide), shield := which % 2 == 0
       , write_state := allWriteStates[which % allWriteStates.size]!
       , write := allWriteActions[which % allWriteActions.size]!
       , last := which % 2 == 1, last_set := which % 3 == 0, last_unset := which % 3 == 1
       , b_carry := which % 2 == 0, gen_ws := which % 2 == 1, ws_echo := which % 3 == 2
       , signal_ws := which % 2 == 0 } : AgentState ψ)).toArray

/-! ## The protocol step and predicates -/

def stepArr {ψ : Nat} (hψ : ψ > 0) (c : Array (AgentState ψ)) (e : Nat) : Array (AgentState ψ) :=
  let n := c.size
  let e1 := (e + 1) % n
  let (l', r') := PPLLFableZDiv.pipeline hψ K cfg (getA hψ c e) (getA hψ c e1)
  (c.set! e l').set! e1 r'

def anyLeader {ψ : Nat} (c : Array (AgentState ψ)) : Bool := c.any (·.leader)

def bitsOf {ψ : Nat} (c : Array (AgentState ψ)) : Array Bool := c.map (·.bit)

def recruitable {ψ : Nat} (u : AgentState ψ) : Bool :=
  decide (u.path = PathInfo.bot) || (!decide (u.state = .produce) && !decide (u.state = .done))

/-! ## Word builders (all edge indices are absolute ring positions) -/

/-- `F_G` relative to a group base: `e0,…,e(ψ-2)`, `ψ-1` edges. -/
def fwdEdges (base ψ : Nat) : Array Nat := ((List.range (ψ - 1)).map (base + ·)).toArray

/-- `R_G` relative to a group base: `e(ψ-3),…,e0`, `ψ-2` edges (empty for `ψ ≤ 2`). -/
def revEdges (base ψ : Nat) : Array Nat := (((List.range (ψ - 2)).map (base + ·)).toArray).reverse

/-- `W_B(G) = F_G ++ R_G^(ψ-1)`, length `(ψ-1)^2`. -/
def wB (base ψ : Nat) : Array Nat :=
  let f := fwdEdges base ψ
  let r := revEdges base ψ
  (List.range (ψ - 1)).foldl (fun acc _ => acc ++ r) f

/-- `GEN = F_G ++ R_G` (one reverse sweep), length `2ψ-3` (ZDIV §2 L3). -/
def genWord (base ψ : Nat) : Array Nat := fwdEdges base ψ ++ revEdges base ψ

/-- `E(g,k)`, the edge from cell `g*ψ+k` to `g*ψ+k+1`. -/
def egk (base k : Nat) : Nat := base + k

/-- `B_g`, the edge from the previous group's terminal into `g`'s head. -/
def bGEdge (base n : Nat) : Nat := (base + n - 1) % n

/-- `D_g = E(g,0),…,E(g,ψ-2),E(g,ψ-2)` (forward sweep, terminal edge served twice), `ψ` edges. -/
def dG (base ψ : Nat) : Array Nat := (fwdEdges base ψ).push (egk base (ψ - 2))

/-- `F_g = [E(g,0), B_g] ++ D_g`, `ψ+2` edges. -/
def fG (base ψ n : Nat) : Array Nat := #[egk base 0, bGEdge base n] ++ dG base ψ

/-- `D = ⋃_g D_g`, length `n`. -/
def wordD (m ψ : Nat) : Array Nat := (List.range m).foldl (fun acc g => acc ++ dG (g * ψ) ψ) #[]

/-- `F = ⋃_g F_g`, length `n + 2m`. -/
def wordF (m ψ n : Nat) : Array Nat :=
  (List.range m).foldl (fun acc g => acc ++ fG (g * ψ) ψ n) #[]

/-- `D ++ F`, length `2n + 2n/ψ` (ZDIV §14). -/
def wordDF (m ψ n : Nat) : Array Nat := wordD m ψ ++ wordF m ψ n

/-- `F*_g = F_g` repeated `ψ-1` times (the repaired finite word: enough whole
attempts to survive up to `ψ-2` distinct interior `CheckLast` blockers). -/
def fGStar (base ψ n : Nat) : Array Nat :=
  (List.range (ψ - 1)).foldl (fun acc _ => acc ++ fG base ψ n) #[]

/-- `F* = ⋃_g F*_g`. -/
def wordFStar (m ψ n : Nat) : Array Nat :=
  (List.range m).foldl (fun acc g => acc ++ fGStar (g * ψ) ψ n) #[]

/-- `D ++ F*`, the repaired form of the §14 word. -/
def wordDFStar (m ψ n : Nat) : Array Nat := wordD m ψ ++ wordFStar m ψ n

/-! ## JSON helpers -/

def ringJson {ψ : Nat} (c : Array (AgentState ψ)) : Json :=
  Json.arr (c.map (fun s => PPLLSimRawCodec.encodeState s))

/-! ## Claim 1 : W_B ends in a leader or Recruitable -/

structure Fail1 (ψ : Nat) where
  group : Nat
  word : Array Nat
  post : Array (AgentState ψ)

/-- Applies `W_B` to every group of `orig` in turn (disjoint internal edges, so processing
order does not matter); returns the first group that ends neither with a leader anywhere on
the ring nor fully `Recruitable`. -/
def testRingClaim1 {ψ : Nat} (hψ : ψ > 0) (m : Nat) (orig : Array (AgentState ψ)) :
    Option (Fail1 ψ) := Id.run do
  let mut c := orig
  for g in List.range m do
    let base := g * ψ
    let w := wB base ψ
    let mut leaderSeen := anyLeader c
    for e in w do
      c := stepArr hψ c e
      leaderSeen := leaderSeen || anyLeader c
    let ok := leaderSeen || (List.range ψ).all (fun k => recruitable (getA hψ c (base + k)))
    if !ok then
      return some { group := g, word := w, post := c }
  return none

def runClaim1 (ψ n states seed : Nat) (out : System.FilePath) : IO UInt32 := do
  if hψ : ψ > 0 then
    if hn : n % ψ = 0 then
      let m := n / ψ
      let h ← IO.FS.Handle.mk out .write
      let mut fails : Nat := 0
      let mut checked : Nat := 0
      let mut g : Rng := (UInt64.ofNat (seed * 1000003 + 1)) ||| 1
      -- adversarial sweep first
      for which in [0:advCount] do
        let ring := advRing ψ K n which hψ
        checked := checked + 1
        match testRingClaim1 hψ m ring with
        | some f =>
          fails := fails + 1
          h.putStrLn (Json.mkObj [("claim", toJson 1), ("kind", toJson "adversarial"),
            ("psi", toJson ψ), ("n", toJson n), ("which", toJson which), ("group", toJson f.group),
            ("word", toJson f.word), ("pre", ringJson ring), ("post", ringJson f.post)]).compress
          h.flush
        | none => pure ()
        if fails > 0 then break
      if fails == 0 then
        for si in [0:states] do
          let (g', ring) := randRing g n ψ K hψ
          g := g'
          checked := checked + 1
          match testRingClaim1 hψ m ring with
          | some f =>
            fails := fails + 1
            h.putStrLn (Json.mkObj [("claim", toJson 1), ("kind", toJson "random"),
              ("psi", toJson ψ), ("n", toJson n), ("state_index", toJson si), ("group", toJson f.group),
              ("word", toJson f.word), ("pre", ringJson ring), ("post", ringJson f.post)]).compress
            h.flush
            break
          | none => pure ()
          if si % 2000 == 0 && si > 0 then
            IO.eprintln s!"claim1 psi={ψ} n={n} progress {si}/{states}"
      h.putStrLn (Json.mkObj [("claim", toJson 1), ("summary", toJson true), ("psi", toJson ψ),
        ("n", toJson n), ("checked", toJson checked), ("failures", toJson fails)]).compress
      h.flush
      return 0
    else throw (IO.userError "n must be a multiple of psi")
  else throw (IO.userError "psi must be positive")

/-! ## Claim 3 : GEN ends in a leader or FreshShape, under L3-shape's hypotheses -/

/-- Overwrite one group of `orig` to satisfy L3-shape's hypotheses: head `wait = false`,
`path = ⊥`; every other cell `Recruitable`; no `reset_cmd` anywhere in the group; no `p_carry`
on a non-terminal cell (`label < ψ-1`). Everything else in the group is left as generated. -/
def enforceL3Hyp {ψ : Nat} (hψ : ψ > 0) (base ψv : Nat) (c : Array (AgentState ψ)) :
    Array (AgentState ψ) :=
  Id.run do
    let mut c := c
    for k in [0:ψv] do
      let i := base + k
      let u := getA hψ c i
      let u := { u with reset_cmd := false }
      let u := if k < ψv - 1 then { u with p_carry := false } else u
      let u := if k == 0 then { u with wait := false, path := .bot } else u
      let u := if k != 0 && !recruitable u then { u with path := .bot } else u
      c := c.set! i u
    return c

def freshShapeOk {ψ : Nat} (hψ : ψ > 0) (base ψv : Nat) (c : Array (AgentState ψ)) : Bool :=
  decide ((getA hψ c base).wait = true) &&
  (List.range ψv).all fun k =>
    let u := getA hψ c (base + k)
    (match u.path with
      | .some l b => l == k && (b == 0 || b == 1)
      | .bot => false) &&
    decide (u.path2 = none) &&
    decide (u.state = .depart)

structure Fail3 (ψ : Nat) where
  group : Nat
  word : Array Nat
  pre : Array (AgentState ψ)
  post : Array (AgentState ψ)

def testRingClaim3 {ψ : Nat} (hψ : ψ > 0) (m : Nat) (orig : Array (AgentState ψ)) :
    Option (Fail3 ψ) := Id.run do
  let mut c := orig
  for g in List.range m do
    let base := g * ψ
    c := enforceL3Hyp hψ base ψ c
    let pre := c
    let w := genWord base ψ
    let mut leaderSeen := anyLeader c
    for e in w do
      c := stepArr hψ c e
      leaderSeen := leaderSeen || anyLeader c
    let ok := leaderSeen || freshShapeOk hψ base ψ c
    if !ok then
      return some { group := g, word := w, pre := pre, post := c }
  return none

def runClaim3 (ψ n states seed : Nat) (out : System.FilePath) : IO UInt32 := do
  if hψ : ψ > 0 then
    if hn : n % ψ = 0 then
      if ψ ≥ 2 then
        let m := n / ψ
        let h ← IO.FS.Handle.mk out .write
        let mut fails : Nat := 0
        let mut checked : Nat := 0
        let mut g : Rng := (UInt64.ofNat (seed * 1000003 + 3)) ||| 1
        for which in [0:advCount] do
          let ring := advRing ψ K n which hψ
          checked := checked + 1
          match testRingClaim3 hψ m ring with
          | some f =>
            fails := fails + 1
            h.putStrLn (Json.mkObj [("claim", toJson 3), ("kind", toJson "adversarial"),
              ("psi", toJson ψ), ("n", toJson n), ("which", toJson which), ("group", toJson f.group),
              ("word", toJson f.word), ("pre", ringJson f.pre), ("post", ringJson f.post)]).compress
            h.flush
          | none => pure ()
          if fails > 0 then break
        if fails == 0 then
          for si in [0:states] do
            let (g', ring) := randRing g n ψ K hψ
            g := g'
            checked := checked + 1
            match testRingClaim3 hψ m ring with
            | some f =>
              fails := fails + 1
              h.putStrLn (Json.mkObj [("claim", toJson 3), ("kind", toJson "random"),
                ("psi", toJson ψ), ("n", toJson n), ("state_index", toJson si), ("group", toJson f.group),
                ("word", toJson f.word), ("pre", ringJson f.pre), ("post", ringJson f.post)]).compress
              h.flush
              break
            | none => pure ()
            if si % 2000 == 0 && si > 0 then
              IO.eprintln s!"claim3 psi={ψ} n={n} progress {si}/{states}"
        h.putStrLn (Json.mkObj [("claim", toJson 3), ("summary", toJson true), ("psi", toJson ψ),
          ("n", toJson n), ("checked", toJson checked), ("failures", toJson fails)]).compress
        h.flush
        return 0
      else throw (IO.userError "psi must be >= 2 for claim 3")
    else throw (IO.userError "n must be a multiple of psi")
  else throw (IO.userError "psi must be positive")

/-! ## Claim 2 : D ++ F ends in a leader (some prefix) or WriterBitFrozen -/

structure Fail2 (ψ : Nat) where
  pre : Array (AgentState ψ)
  df : Array Nat
  step : Nat
  edge : Nat
  postDF : Array (AgentState ψ)
  schedule : Array Nat

/-- Runs a fixed word (`D ++ F` or `D ++ F*`) on `orig`, tracking whether a leader ever
appears; if not, runs up to `edges` further random-edge interactions, stopping the moment a
leader appears (the claim no longer constrains bits) or the moment some leaderless
interaction changes a cell's `bit` (a counterexample). -/
def testRingClaim2With {ψ : Nat} (hψ : ψ > 0) (word : Array Nat) (n : Nat)
    (orig : Array (AgentState ψ)) (edges : Nat) (g0 : Rng) : Rng × Option (Fail2 ψ) := Id.run do
  let mut c := orig
  let mut leaderSeen := anyLeader c
  for e in word do
    c := stepArr hψ c e
    leaderSeen := leaderSeen || anyLeader c
  if leaderSeen then
    return (g0, none)
  let postDF := c
  let mut g := g0
  let mut sched : Array Nat := #[]
  for step in [0:edges] do
    if anyLeader c then
      return (g, none)
    let bitsPre := bitsOf c
    let (g', e) := nextNat g n
    g := g'
    sched := sched.push e
    c := stepArr hψ c e
    -- a leader born by this very interaction absorbs it into the "leader appeared" disjunct,
    -- even if the same step also changed a bit (task instructions: "stop if a leader appears").
    if anyLeader c then
      return (g, none)
    if bitsOf c != bitsPre then
      return (g, some { pre := orig, df := word, step := step + 1, edge := e, postDF := postDF
                       , schedule := sched })
  return (g, none)

/-- `D ++ F`, ZDIV §14's original (refuted at ψ=3,n=12) word. -/
def testRingClaim2 {ψ : Nat} (hψ : ψ > 0) (m n : Nat) (orig : Array (AgentState ψ))
    (edges : Nat) (g0 : Rng) : Rng × Option (Fail2 ψ) :=
  testRingClaim2With hψ (wordDF m ψ n) n orig edges g0

/-- Claim (a): `D ++ F*` (the repaired word) — same predicate, corrected word. -/
def testRingClaimA {ψ : Nat} (hψ : ψ > 0) (m n : Nat) (orig : Array (AgentState ψ))
    (edges : Nat) (g0 : Rng) : Rng × Option (Fail2 ψ) :=
  testRingClaim2With hψ (wordDFStar m ψ n) n orig edges g0

def runClaim2 (ψ n states edges seed : Nat) (out : System.FilePath) : IO UInt32 := do
  if hψ : ψ > 0 then
    if hn : n % ψ = 0 then
      if ψ ≥ 2 then
        let m := n / ψ
        let h ← IO.FS.Handle.mk out .write
        let mut fails : Nat := 0
        let mut checked : Nat := 0
        let mut g : Rng := (UInt64.ofNat (seed * 1000003 + 2)) ||| 1
        for which in [0:advCount] do
          let ring := advRing ψ K n which hψ
          checked := checked + 1
          let (g', res) := testRingClaim2 hψ m n ring edges g
          g := g'
          match res with
          | some f =>
            fails := fails + 1
            h.putStrLn (Json.mkObj [("claim", toJson 2), ("kind", toJson "adversarial"),
              ("psi", toJson ψ), ("n", toJson n), ("which", toJson which), ("step", toJson f.step),
              ("edge", toJson f.edge), ("pre", ringJson f.pre), ("post_df", ringJson f.postDF),
              ("schedule", toJson f.schedule)]).compress
            h.flush
          | none => pure ()
          if fails > 0 then break
        if fails == 0 then
          for si in [0:states] do
            let (g', ring) := randRing g n ψ K hψ
            g := g'
            checked := checked + 1
            let (g'', res) := testRingClaim2 hψ m n ring edges g
            g := g''
            match res with
            | some f =>
              fails := fails + 1
              h.putStrLn (Json.mkObj [("claim", toJson 2), ("kind", toJson "random"),
                ("psi", toJson ψ), ("n", toJson n), ("state_index", toJson si), ("step", toJson f.step),
                ("edge", toJson f.edge), ("pre", ringJson f.pre), ("post_df", ringJson f.postDF),
                ("schedule", toJson f.schedule)]).compress
              h.flush
              break
            | none => pure ()
            if si % 200 == 0 && si > 0 then
              IO.eprintln s!"claim2 psi={ψ} n={n} progress {si}/{states}"
        h.putStrLn (Json.mkObj [("claim", toJson 2), ("summary", toJson true), ("psi", toJson ψ),
          ("n", toJson n), ("checked", toJson checked), ("edges_per_state", toJson edges),
          ("failures", toJson fails)]).compress
        h.flush
        return 0
      else throw (IO.userError "psi must be >= 2 for claim 2 (see psi1 command)")
    else throw (IO.userError "n must be a multiple of psi")
  else throw (IO.userError "psi must be positive")

/-- Claim (a): `D ++ F*` — no leaderless bit change at all, ever
(not merely eventually-idempotent). Same driver as `runClaim2`, swapped word/test. -/
def runClaimA (ψ n states edges seed : Nat) (out : System.FilePath) : IO UInt32 := do
  if hψ : ψ > 0 then
    if hn : n % ψ = 0 then
      if ψ ≥ 2 then
        let m := n / ψ
        let h ← IO.FS.Handle.mk out .write
        let mut fails : Nat := 0
        let mut checked : Nat := 0
        let mut g : Rng := (UInt64.ofNat (seed * 1000003 + 11)) ||| 1
        for which in [0:advCount] do
          let ring := advRing ψ K n which hψ
          checked := checked + 1
          let (g', res) := testRingClaimA hψ m n ring edges g
          g := g'
          match res with
          | some f =>
            fails := fails + 1
            h.putStrLn (Json.mkObj [("claim", toJson "a"), ("kind", toJson "adversarial"),
              ("psi", toJson ψ), ("n", toJson n), ("which", toJson which), ("step", toJson f.step),
              ("edge", toJson f.edge), ("pre", ringJson f.pre), ("post_df", ringJson f.postDF),
              ("schedule", toJson f.schedule)]).compress
            h.flush
          | none => pure ()
          if fails > 0 then break
        if fails == 0 then
          for si in [0:states] do
            let (g', ring) := randRing g n ψ K hψ
            g := g'
            checked := checked + 1
            let (g'', res) := testRingClaimA hψ m n ring edges g
            g := g''
            match res with
            | some f =>
              fails := fails + 1
              h.putStrLn (Json.mkObj [("claim", toJson "a"), ("kind", toJson "random"),
                ("psi", toJson ψ), ("n", toJson n), ("state_index", toJson si), ("step", toJson f.step),
                ("edge", toJson f.edge), ("pre", ringJson f.pre), ("post_df", ringJson f.postDF),
                ("schedule", toJson f.schedule)]).compress
              h.flush
              break
            | none => pure ()
            if si % 200 == 0 && si > 0 then
              IO.eprintln s!"claimA psi={ψ} n={n} progress {si}/{states}"
        h.putStrLn (Json.mkObj [("claim", toJson "a"), ("summary", toJson true), ("psi", toJson ψ),
          ("n", toJson n), ("checked", toJson checked), ("edges_per_state", toJson edges),
          ("failures", toJson fails)]).compress
        h.flush
        return 0
      else throw (IO.userError "psi must be >= 2 for claim a")
    else throw (IO.userError "n must be a multiple of psi")
  else throw (IO.userError "psi must be positive")

/-! ## Claim (b): after D alone, every leaderless bit change is an overwrite
on a terminal cell, and each terminal's bit changes at most once while its resident `path3`
identity `(label, bit)` stays fixed (the K = 1 bound). -/

structure FailB (ψ : Nat) where
  pre : Array (AgentState ψ)
  d : Array Nat
  step : Nat
  edge : Nat
  postD : Array (AgentState ψ)
  schedule : Array Nat
  cell : Nat
  reason : String

/-- Is ring index `i` a group terminal (label `ψ-1`) for group size `ψ`? -/
def isTerminalIdx (ψ i : Nat) : Bool := i % ψ == ψ - 1

/-- `(label, bit)` of a cell's resident `path3`, dropping the mutable `flag` (the overwrite
target: `path3.bit` is fixed by an overwrite, only `path3.flag` moves). -/
def path3Id {ψ : Nat} (u : AgentState ψ) : Option (Nat × Nat) :=
  match u.path3 with
  | some p => some (p.label, p.bit)
  | none => none

def path3IdEq (a b : Option (Nat × Nat)) : Bool :=
  match a, b with
  | some (l0, b0), some (l1, b1) => l0 == l1 && b0 == b1
  | none, none => true
  | _, _ => false

/-- Runs `D` on `orig`; if a leader appears during `D` the claim is vacuous for this state.
Otherwise runs up to `edges` further random leaderless interactions. For each step that
changes any cell's bit, checks: (1) the changed cell is a group terminal, (2) its resident
`path3` `(label,bit)` identity is unchanged by the step (the overwrite signature — `flag` may
still move). If both hold, tallies the change against that terminal's running count of
effective changes against the same resident identity (resets to 1 if the identity itself just
changed, i.e. a fresh resident payload). Returns the max count seen across all terminals, plus
a failure record on the first violation of (1)/(2) or a count that exceeds 1 (falsifying K=1). -/
def testRingClaimB {ψ : Nat} (hψ : ψ > 0) (m n : Nat) (orig : Array (AgentState ψ))
    (edges : Nat) (g0 : Rng) : Rng × Nat × Option (FailB ψ) := Id.run do
  let d := wordD m ψ
  let mut c := orig
  let mut leaderSeen := anyLeader c
  for e in d do
    c := stepArr hψ c e
    leaderSeen := leaderSeen || anyLeader c
  if leaderSeen then
    return (g0, 0, none)
  let postD := c
  let mut g := g0
  let mut sched : Array Nat := #[]
  -- per-terminal-group running tally: (last resident (label,bit) identity, its run count)
  let mut lastId : Array (Option (Nat × Nat)) := Array.replicate m none
  let mut runCount : Array Nat := Array.replicate m 0
  let mut maxCount : Nat := 0
  for step in [0:edges] do
    if anyLeader c then
      return (g, maxCount, none)
    let pre := c
    let (g', e) := nextNat g n
    g := g'
    sched := sched.push e
    c := stepArr hψ c e
    if anyLeader c then
      return (g, maxCount, none)
    let mut failure : Option (Nat × String) := none
    for i in [0:n] do
      if failure.isNone then
        let b0 := (getA hψ pre i).bit
        let b1 := (getA hψ c i).bit
        if b0 != b1 then
          if !isTerminalIdx ψ i then
            failure := some (i, "non-terminal-bit-change")
          else
            let idPre := path3Id (getA hψ pre i)
            let idPost := path3Id (getA hψ c i)
            if !path3IdEq idPre idPost then
              failure := some (i, "path3-identity-changed-by-overwrite")
            else
              match idPre with
              | none => failure := some (i, "no-resident-path3")
              | some _ =>
                let grp := i / ψ
                let sameAsLast := path3IdEq (lastId.getD grp none) idPre
                let cnt := if sameAsLast then (runCount.getD grp 0) + 1 else 1
                lastId := lastId.set! grp idPre
                runCount := runCount.set! grp cnt
                maxCount := max maxCount cnt
                if cnt > 1 then
                  failure := some (i, "k1-bound-violated")
    match failure with
    | some (i, reason) =>
      return (g, maxCount,
        some { pre := orig, d := d, step := step + 1, edge := e, postD := postD
             , schedule := sched, cell := i, reason := reason })
    | none => pure ()
  return (g, maxCount, none)

def runClaimB (ψ n states edges seed : Nat) (out : System.FilePath) : IO UInt32 := do
  if hψ : ψ > 0 then
    if hn : n % ψ = 0 then
      if ψ ≥ 2 then
        let m := n / ψ
        let h ← IO.FS.Handle.mk out .write
        let mut fails : Nat := 0
        let mut checked : Nat := 0
        let mut globalMax : Nat := 0
        let mut g : Rng := (UInt64.ofNat (seed * 1000003 + 13)) ||| 1
        for which in [0:advCount] do
          let ring := advRing ψ K n which hψ
          checked := checked + 1
          let (g', mx, res) := testRingClaimB hψ m n ring edges g
          g := g'
          globalMax := max globalMax mx
          match res with
          | some f =>
            fails := fails + 1
            h.putStrLn (Json.mkObj [("claim", toJson "b"), ("kind", toJson "adversarial"),
              ("psi", toJson ψ), ("n", toJson n), ("which", toJson which), ("step", toJson f.step),
              ("edge", toJson f.edge), ("cell", toJson f.cell), ("reason", toJson f.reason),
              ("pre", ringJson f.pre), ("post_d", ringJson f.postD),
              ("schedule", toJson f.schedule)]).compress
            h.flush
          | none => pure ()
          if fails > 0 then break
        if fails == 0 then
          for si in [0:states] do
            let (g', ring) := randRing g n ψ K hψ
            g := g'
            checked := checked + 1
            let (g'', mx, res) := testRingClaimB hψ m n ring edges g
            g := g''
            globalMax := max globalMax mx
            match res with
            | some f =>
              fails := fails + 1
              h.putStrLn (Json.mkObj [("claim", toJson "b"), ("kind", toJson "random"),
                ("psi", toJson ψ), ("n", toJson n), ("state_index", toJson si), ("step", toJson f.step),
                ("edge", toJson f.edge), ("cell", toJson f.cell), ("reason", toJson f.reason),
                ("pre", ringJson f.pre), ("post_d", ringJson f.postD),
                ("schedule", toJson f.schedule)]).compress
              h.flush
              break
            | none => pure ()
            if si % 200 == 0 && si > 0 then
              IO.eprintln s!"claimB psi={ψ} n={n} progress {si}/{states}"
        h.putStrLn (Json.mkObj [("claim", toJson "b"), ("summary", toJson true), ("psi", toJson ψ),
          ("n", toJson n), ("checked", toJson checked), ("edges_per_state", toJson edges),
          ("failures", toJson fails), ("max_count_per_terminal", toJson globalMax)]).compress
        h.flush
        return 0
      else throw (IO.userError "psi must be >= 2 for claim b")
    else throw (IO.userError "n must be a multiple of psi")
  else throw (IO.userError "psi must be positive")

/-! ## psi = 1 special case: is there a six-service bit-flip cycle? -/

/-- For `ψ = 1` every group is a single cell and every ring edge is a boundary edge; test
whether servicing one fixed edge six times in a row from a random leaderless state flips a
bit at some intermediate step and restores it by the sixth (ZDIV §14's claimed six-service
writer-projection cycle). -/
def runPsi1 (n states seed : Nat) (out : System.FilePath) : IO UInt32 := do
  if hψ : (1 : Nat) > 0 then
    let h ← IO.FS.Handle.mk out .write
    let mut g : Rng := (UInt64.ofNat (seed * 1000003 + 5)) ||| 1
    let mut cycles : Nat := 0
    for si in [0:states] do
      let (g', ring0) := randRing g n 1 K hψ
      g := g'
      let (g', e) := nextNat g n
      g := g'
      let bits0 := bitsOf ring0
      let mut c := ring0
      let mut sawDiff := false
      let mut restored := false
      for s in [0:6] do
        c := stepArr hψ c e
        let d := bitsOf c != bits0
        if d then sawDiff := true
        if s == 5 && !d then restored := true
      if sawDiff && restored then
        cycles := cycles + 1
    h.putStrLn (Json.mkObj [("psi1_six_service_cycle", toJson true), ("states", toJson states),
      ("n", toJson n), ("cycles_observed", toJson cycles)]).compress
    h.flush
    return 0
  else throw (IO.userError "unreachable")

/-- Force a cell to the exact `ψ = 1` writer-neutral / precondition fields needed by the
six-service cycle (`path3 = some(0,0,0)`, `bit = false`, `write = none`,
`write_state = depart`, `last/last_set/last_unset/ws_echo/signal_ws = false`, `wait = true`
and `count = 0` to keep GENSIG dormant so only the writer subsystem is exercised). -/
def psi1DangerCell {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) : AgentState ψ :=
  { u with
      leader := false, wait := true, count := 0,
      path3 := some { label := 0, bit := 0, flag := 0 },
      bit := false, write := .none, write_state := .depart,
      last := false, last_set := false, last_unset := false,
      ws_echo := false, signal_ws := false }

/-- Writer-neutral (and, to keep the projection isolated, main-path-neutral) neighbour cell:
same writer fields as `psi1DangerCell` minus the `bit`/`path3` payload, plus `state = none`,
`path = ⊥`, `path2 = none`, no comparison/reset/write-source debris. -/
def psi1NeutralCell {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) : AgentState ψ :=
  { u with
      leader := false, wait := true, count := 0, state := .none, path := .bot, path2 := none,
      p := false, p_carry := false, reset := false, reset_cmd := false, path3 := none,
      write := .none, write_state := .depart, last := false, last_set := false,
      last_unset := false, ws_echo := false, signal_ws := false, gen_ws := false, b_carry := false }

/-- Exact replay of the `ψ = 1` writer-projection cycle: cell `0` gets
`psi1DangerCell`, its predecessor (`n-1`) and successor (`1 mod n`) get `psi1NeutralCell`
(other cells, if `n > 2`, keep independently random fields), then the word
`R^3 = [O, I]^3` (`O` = cell 0's outgoing edge `0`, `I` = the incoming edge `n-1`) is applied,
6 services. Reports the bit trace; the source claims `x.bit` flips twice and the six-tuple
returns to the same writer projection. -/
def runPsi1Exact (n states seed : Nat) (out : System.FilePath) : IO UInt32 := do
  if hψ : (1 : Nat) > 0 then
    if hn2 : n ≥ 2 then
      let h ← IO.FS.Handle.mk out .write
      let mut g : Rng := (UInt64.ofNat (seed * 1000003 + 7)) ||| 1
      let mut cycles : Nat := 0
      let sched : Array Nat := #[0, n - 1, 0, n - 1, 0, n - 1]
      for si in [0:states] do
        let (g', ring0) := randRing g n 1 K hψ
        g := g'
        let succIdx := 1 % n
        let predIdx := n - 1
        let mut c := ring0.set! 0 (psi1DangerCell hψ (ring0.getD 0 (defaultAgentState hψ)))
        c := c.set! succIdx (psi1NeutralCell hψ (c.getD succIdx (defaultAgentState hψ)))
        c := c.set! predIdx (psi1NeutralCell hψ (c.getD predIdx (defaultAgentState hψ)))
        let start := c
        let bits0 := bitsOf c
        let mut trace : Array Bool := #[(getA hψ c 0).bit]
        for e in sched do
          c := stepArr hψ c e
          trace := trace.push (getA hψ c 0).bit
        let restored := bitsOf c == bits0
        let flips := (List.range (trace.size - 1)).countP (fun i => trace[i]! != trace[i+1]!)
        if restored && flips ≥ 2 then
          cycles := cycles + 1
        if si < 5 then
          h.putStrLn (Json.mkObj [("state_index", toJson si), ("start", ringJson start),
            ("bit_trace", toJson trace), ("restored", toJson restored), ("flips", toJson flips)]).compress
      h.putStrLn (Json.mkObj [("psi1exact_six_service_cycle", toJson true), ("n", toJson n),
        ("states", toJson states), ("cycles_observed", toJson cycles)]).compress
      h.flush
      return 0
    else throw (IO.userError "n must be >= 2")
  else throw (IO.userError "unreachable")

/-! ## Debug replay of a recorded claim-2 counterexample -/

/-- Loads a ring from a JSON array of `PPLLSimRawCodec`-encoded states (the `pre` field of a
counterexample line), replays `D ++ F` (`variant = "df"`) or `D ++ F*` (`variant = "dfstar"`)
then the given comma-separated edge schedule one edge at a time, and prints a JSON line per
step: leader status, bits, and (only when bits changed) the full pre/post states of the two
cells touched by that step. Debug tool, not part of the claim-testing pipeline. -/
def debugReplay2 (ψ n : Nat) (ringPath : System.FilePath) (schedStr : String)
    (out : System.FilePath) (variant : String := "df") : IO UInt32 := do
  if hψ : ψ > 0 then
    if hn : n % ψ = 0 then
      let m := n / ψ
      let raw ← IO.FS.readFile ringPath
      let j ← IO.ofExcept (Json.parse raw)
      let arr ← IO.ofExcept j.getArr?
      let mut c : Array (AgentState ψ) := #[]
      for je in arr do
        let s ← IO.ofExcept (PPLLSimRawCodec.decodeState (psi := ψ) je)
        c := c.push s
      let h ← IO.FS.Handle.mk out .write
      let df := if variant == "dfstar" then wordDFStar m ψ n else wordDF m ψ n
      h.putStrLn (Json.mkObj [("phase", toJson "start"), ("variant", toJson variant),
        ("leader", toJson (anyLeader c)), ("bits", toJson (bitsOf c))]).compress
      for e in df do
        c := stepArr hψ c e
        h.putStrLn (Json.mkObj [("phase", toJson "df"), ("edge", toJson e),
          ("leader", toJson (anyLeader c)), ("bits", toJson (bitsOf c))]).compress
      let sched : Array Nat := (schedStr.splitOn ",").toArray.filterMap (·.trimAscii.toString.toNat?)
      for e in sched do
        let bitsPre := bitsOf c
        let leaderPre := anyLeader c
        let e1 := (e + 1) % n
        let preL := getA hψ c e
        let preR := getA hψ c e1
        c := stepArr hψ c e
        let changed := bitsOf c != bitsPre
        h.putStrLn (Json.mkObj ([("phase", toJson "sched"), ("edge", toJson e),
          ("leader_pre", toJson leaderPre), ("leader", toJson (anyLeader c)),
          ("bits", toJson (bitsOf c)), ("changed", toJson changed)] ++
          (if changed then
            [("pre_l", PPLLSimRawCodec.encodeState preL), ("pre_r", PPLLSimRawCodec.encodeState preR),
             ("post_l", PPLLSimRawCodec.encodeState (getA hψ c e)),
             ("post_r", PPLLSimRawCodec.encodeState (getA hψ c e1))]
          else []))).compress
      h.flush
      return 0
    else throw (IO.userError "n must be a multiple of psi")
  else throw (IO.userError "psi must be positive")

end ZZSimClaims

open ZZSimClaims in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["claim1", ψ, n, states, seed, out] =>
    match ψ.toNat?, n.toNat?, states.toNat?, seed.toNat? with
    | some ψ, some n, some states, some seed => runClaim1 ψ n states seed out
    | _, _, _, _ => IO.eprintln "numeric arguments expected"; return 2
  | ["claim3", ψ, n, states, seed, out] =>
    match ψ.toNat?, n.toNat?, states.toNat?, seed.toNat? with
    | some ψ, some n, some states, some seed => runClaim3 ψ n states seed out
    | _, _, _, _ => IO.eprintln "numeric arguments expected"; return 2
  | ["claim2", ψ, n, states, edges, seed, out] =>
    match ψ.toNat?, n.toNat?, states.toNat?, edges.toNat?, seed.toNat? with
    | some ψ, some n, some states, some edges, some seed => runClaim2 ψ n states edges seed out
    | _, _, _, _, _ => IO.eprintln "numeric arguments expected"; return 2
  | ["claima", ψ, n, states, edges, seed, out] =>
    match ψ.toNat?, n.toNat?, states.toNat?, edges.toNat?, seed.toNat? with
    | some ψ, some n, some states, some edges, some seed => runClaimA ψ n states edges seed out
    | _, _, _, _, _ => IO.eprintln "numeric arguments expected"; return 2
  | ["claimb", ψ, n, states, edges, seed, out] =>
    match ψ.toNat?, n.toNat?, states.toNat?, edges.toNat?, seed.toNat? with
    | some ψ, some n, some states, some edges, some seed => runClaimB ψ n states edges seed out
    | _, _, _, _, _ => IO.eprintln "numeric arguments expected"; return 2
  | ["psi1", n, states, seed, out] =>
    match n.toNat?, states.toNat?, seed.toNat? with
    | some n, some states, some seed => runPsi1 n states seed out
    | _, _, _ => IO.eprintln "numeric arguments expected"; return 2
  | ["psi1exact", n, states, seed, out] =>
    match n.toNat?, states.toNat?, seed.toNat? with
    | some n, some states, some seed => runPsi1Exact n states seed out
    | _, _, _ => IO.eprintln "numeric arguments expected"; return 2
  | ["debug2", ψ, n, ringPath, sched, out] =>
    match ψ.toNat?, n.toNat? with
    | some ψ, some n => debugReplay2 ψ n ringPath sched out
    | _, _ => IO.eprintln "numeric arguments expected"; return 2
  | ["debug2", ψ, n, ringPath, sched, out, variant] =>
    match ψ.toNat?, n.toNat? with
    | some ψ, some n => debugReplay2 ψ n ringPath sched out variant
    | _, _ => IO.eprintln "numeric arguments expected"; return 2
  | _ =>
    IO.eprintln "usage: sim-claims claim1|claim3 PSI N STATES SEED OUT
       | claim2|claima|claimb PSI N STATES EDGES SEED OUT | psi1 N STATES SEED OUT
       | debug2 PSI N RING.json SCHEDULE OUT"
    return 2
