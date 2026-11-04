import Leader.Wu.Sim.AuthCarrier

/-!
# FULL-DISCHARGE structured ("hard") seed generator (authFplusmcc)

Design-exploration tool, not a proof certificate.  Second generator of the FULL-DISCHARGE
sampling campaign (`Leader/Wu/Sim/AuthDischargeSeeds.lean` is the first, an i.i.d.-field
ensemble found "too easy": almost every seed self-destructs into a hole in ≤ 3
steps because independently random marks are already CLEAN-inconsistent).  This
file builds *CLEAN-consistent* ensembles instead: every ring is divided into
`n / ψ` physical **blocks** of `ψ` consecutive positions; within a block the
`path_mark`/`ctrl_mark` are a single shared colour `γ_g` and `path.label`
normally runs `0, 1, …, ψ-1` in step with the physical offset ("aligned").
`path4`/`path5` stay empty everywhere, so the CLEAN comparator (`step3Auth` /
`step4Auth` in `Leader/Wu/Authorization/ProvenanceMarks.lean`, which only fires on an existing
`path4`/`path5` record) has nothing to react to at block boundaries — no
immediate deletion is available purely from mark noise, unlike the i.i.d. ensemble.

Every cell still satisfies the FULL-DISCHARGE precondition exactly as in the i.i.d. ensemble
(leaderless, perfect `core.label = i % ψ`, `inProtocolDomain κ` automatic by
construction, `reset_cmd = echo = false`, full `path`, no `produce`/`done`).

Four ensembles (Leaf C, Xiang's spec):

* **a** (`serial`): every block departed, single mark `γ_g` and one resident bit
  per block, `path2 = path4 = path5 = none` everywhere.  The "canonical clean
  ring" family (`t3-zc` in `run/verification/g62/authf/README.md`).
* **b** (`episode`): as (a), but 1–3 random blocks each get a coherent
  comparison episode overwriting a random contiguous sub-run of that block:
  `lock`, `compare1`+`compare2`, a `CHECK_ready` run, `equal`, or `larger`/`less`
  with a matching `path2` token (action 4/6, scope `session`, mark `γ_g`) —
  the same `(state, path2 action)` pairing `run/…/mkseeds.py`'s `battery`
  uses, so the episode is one already-exercised in the campaign.
* **c** (`shift`, Leaf C step 7, "physically shifted train"): as (a),
  but a random contiguous span of `1 .. n/ψ - 1` blocks — "one train" — gets a
  single shared mark `γ'` and its `path.label` rotated by a random `r ∈
  [1, ψ)` relative to the physical offset (`core.label` is *never* rotated:
  the perfect-label precondition is untouched).  The train is internally
  coherent (labels still cycle `0..ψ-1` seamlessly across its own block
  boundaries) but misaligned with the physical ring it sits on.
* **d** (`alleq`, generalised Leaf C mechanism, for sizes with no matching
  real witness): one *global* mark for the whole ring (the documented hardest
  case: README "all marks 0" families B3/B3′/B4 survive under weaker variants)
  and one comparison episode from the same menu as (b) at a random block.
  The real recorded traps (`witnesses/zcp4n8-81`, `witnesses/t2p4n8-2702-plus`,
  …) are replayed separately (colour/rotation variants of the actual JSON,
  not regenerated here) since they only exist at ψ=4,n=8.

Usage: `zz-auth-full-discharge-hard ENSEMBLE PSI N KAPPA COUNT RNGSEED OUTFILE`,
`ENSEMBLE ∈ {a, b, c, d}`.
-/

set_option autoImplicit false

open Lean PPLLAuthF PPLLAuthSim

namespace ZZAuthFullDischargeHard

-- Shadow copy of the small `Inhabited`/PRNG helpers from `ZZAuthFullDischarge`
-- (not imported: that file has its own top-level `def main`, which would
-- collide with this file's, exactly the reason `PPLLAuthWalk` shadow-copies
-- `PPLLDiskCensus` instead of importing it).
deriving instance Inhabited for MainState

@[inline] def mix64 (x : UInt64) : UInt64 :=
  let x := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
  let x := (x ^^^ (x >>> 27)) * 0x94d049bb133111eb
  x ^^^ (x >>> 31)

structure RNG where
  s : UInt64
  deriving Inhabited

@[inline] def RNG.next (r : RNG) : UInt64 × RNG :=
  let s' := r.s + 0x9E3779B97F4A7C15
  (mix64 s', ⟨s'⟩)

@[inline] def RNG.nextNat (r : RNG) (bound : Nat) : Nat × RNG :=
  let (v, r') := r.next
  (v.toNat % bound, r')

@[inline] def RNG.nextBool (r : RNG) : Bool × RNG :=
  let (v, r') := r.nextNat 2
  (v == 1, r')

@[inline] def finOfNat (bound : Nat) (hbound : 0 < bound) (v : Nat) : Fin bound :=
  ⟨v % bound, Nat.mod_lt v hbound⟩

@[inline] def RNG.nextFin (r : RNG) (bound : Nat) (hbound : 0 < bound) : Fin bound × RNG :=
  let (v, r') := r.nextNat bound
  (finOfNat bound hbound v, r')

/-- Fisher–Yates: a random permutation of `[0, m)`, used to pick `k` distinct
random blocks (take the first `k` entries). -/
def randPerm (r0 : RNG) (m : Nat) : Array Nat × RNG := Id.run do
  let mut a : Array Nat := Array.ofFn (n := m) (fun i => i.val)
  let mut r := r0
  for i in [0:m] do
    let j := m - 1 - i
    if j > 0 then
      let (k, r1) := r.nextNat (j + 1)
      r := r1
      let tmp := a[j]!
      a := a.set! j a[k]!
      a := a.set! k tmp
  return (a, r)

/-! ## A quiescent cell at physical position `i`, then the four ensembles. -/

/-- The base "departed, quiescent" cell at physical position `i` of an `n`-ring,
label `i % ψ`, resident bit `bit`, path label `pathLabel` (aligned = `i % ψ`,
rotated for ensemble `c`), single mark colour `mark`, state `st`, and an
optional `path2` token (`action`, scope `session`, same colour). Every field
FULL-DISCHARGE does not constrain is a fixed quiescent default, not random:
this is a *structured*, not i.i.d., ensemble. -/
def cell (psi kappa i : Nat) (hpsi : 0 < psi) (pathLabel : Fin psi) (bit : Bool)
    (mark : Fin 3) (st : MainState) (path2Action : Option (Fin 6)) (wait : Bool) :
    AuthB psi kappa :=
  let label : Fin psi := finOfNat psi hpsi (i % psi)
  let core : BoundedAgentState psi kappa :=
    { leader := false, probe := false, phase := false, bit := bit, wait := wait,
      state := st, path := .some pathLabel (finOfNat 2 (by omega) (if bit then 1 else 0)),
      reset := false, carry := false, count := finOfNat (kappa + 1) (by omega) 0,
      label := label, h_field := false,
      path2 := path2Action.map (fun act =>
        { label := pathLabel, bit := finOfNat 2 (by omega) (if bit then 1 else 0),
          position := finOfNat (psi + 1) (by omega) 0, action := act }),
      path3 := none, path4 := none, path5 := none, p := false, p_carry := false,
      reset_cmd := false, echo := false, signal_B := finOfNat 2 (by omega) 0,
      bullet := finOfNat 3 (by omega) 0, shield := false, write_state := .none,
      write := .none, last := false, last_set := false, last_unset := false,
      b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }
  -- `PPLLAuthF.issue` is the canonical constructor of a larger/less result
  -- token and always stamps it `path2_scope := .line, path2_mark := path_mark`;
  -- match that here rather than guessing a `.session` (BEQ two-train) token,
  -- which this generator does not attempt to construct.
  let m : Marks :=
    { path := mark, ctrl := mark, p2 := mark, p4 := 0, p5 := 0, scope := .line }
  ⟨core, m⟩

/-- A departed cell, aligned or rotated by `rot` within its own block. -/
def departCell (psi kappa i g : Nat) (hpsi : 0 < psi) (rot : Nat) (bit : Bool)
    (mark : Fin 3) (wait : Bool) : AuthB psi kappa :=
  let j := i - g * psi
  let pathLabel := finOfNat psi hpsi ((j + rot) % psi)
  cell psi kappa i hpsi pathLabel bit mark .depart none wait

/-- The comparison-episode menu shared by ensembles `b` and `d`: `(states,
path2 action per cell)`, at most `ψ` cells long. `larger`/`less` carry the
`Path2Info.action` values 4/6 seen throughout the campaign
(`run/…/mkseeds.py`'s `battery`, `ZDIV.md`'s B1/B4 mechanism write-up). -/
def episodeMenu : Array (Array (MainState × Option (Fin 6))) :=
  #[ #[(.lock, none)]
   , #[(.compare1, none), (.compare2, none)]
   , #[(.CHECK_ready, none), (.CHECK_ready, none), (.CHECK_ready, none)]
   , #[(.equal, none)]
   , #[(.larger, some (finOfNat 6 (by omega) 3))]
   , #[(.less, some (finOfNat 6 (by omega) 5))] ]

/-- Overwrite a random contiguous sub-run of block `g` (length ≤ ψ) with a
random episode from `episodeMenu`, keeping every other cell of the block
departed; both departed and episode cells share the block's mark `γ_g`. -/
def buildBlockWithEpisode (psi kappa g : Nat) (hpsi : 0 < psi) (bit : Bool)
    (mark : Fin 3) (whead : Bool) (r0 : RNG) : Array (AuthB psi kappa) × RNG := Id.run do
  let (mi, r1) := r0.nextNat episodeMenu.size
  let pat := episodeMenu[mi]!
  let len := min pat.size psi
  let (off, r2) := r1.nextNat (psi - len + 1)
  let mut out : Array (AuthB psi kappa) := #[]
  let mut r := r2
  for j in [0:psi] do
    let i := g * psi + j
    if j ≥ off && j < off + len then
      let (st, act) := pat[j - off]!
      out := out.push (cell psi kappa i hpsi (finOfNat psi hpsi j) bit mark st act false)
    else
      out := out.push (departCell psi kappa i g hpsi 0 bit mark (j == 0 && whead))
  return (out, r)

/-- **(a)** every block departed, aligned, one mark and one resident bit per
block. -/
def ensembleA (psi kappa n : Nat) (hpsi : 0 < psi) (r0 : RNG) :
    Array (AuthB psi kappa) × RNG := Id.run do
  let numBlocks := n / psi
  let mut out : Array (AuthB psi kappa) := #[]
  let mut r := r0
  for g in [0:numBlocks] do
    let (mark, r1) := r.nextFin 3 (by omega)
    let (bit, r2) := r1.nextBool
    let (whead, r3) := r2.nextBool
    r := r3
    for j in [0:psi] do
      let i := g * psi + j
      out := out.push (departCell psi kappa i g hpsi 0 bit mark (j == 0 && whead))
  return (out, r)

/-- **(b)** ensemble (a) plus 1–3 random blocks carrying a coherent comparison
episode. -/
def ensembleB (psi kappa n : Nat) (hpsi : 0 < psi) (r0 : RNG) :
    Array (AuthB psi kappa) × RNG := Id.run do
  let numBlocks := n / psi
  let (numEp0, r1) := r0.nextNat 3
  let numEp := min (numEp0 + 1) numBlocks
  let (order, r2) := randPerm r1 numBlocks
  let episodeBlocks : Array Nat := order.extract 0 numEp
  let mut out : Array (AuthB psi kappa) := #[]
  let mut r := r2
  for g in [0:numBlocks] do
    let (mark, r3) := r.nextFin 3 (by omega)
    let (bit, r4) := r3.nextBool
    let (whead, r5) := r4.nextBool
    r := r5
    if episodeBlocks.contains g then
      let (blk, r6) := buildBlockWithEpisode psi kappa g hpsi bit mark whead r
      r := r6
      out := out ++ blk
    else
      for j in [0:psi] do
        let i := g * psi + j
        out := out.push (departCell psi kappa i g hpsi 0 bit mark (j == 0 && whead))
  return (out, r)

/-- **(c)** ensemble (a) plus one contiguous "train" of `1 .. numBlocks-1`
blocks whose `path.label` is rotated by a shared `r ∈ [1,ψ)` relative to the
physical offset; `core.label` is untouched (perfect labels preserved). -/
def ensembleC (psi kappa n : Nat) (hpsi : 0 < psi) (r0 : RNG) :
    Array (AuthB psi kappa) × RNG := Id.run do
  let numBlocks := n / psi
  let (span0, r1) := r0.nextNat (max 1 (numBlocks - 1))
  let span := min (span0 + 1) (numBlocks - 1)
  let (start, r2) := r1.nextNat numBlocks
  let (rot0, r3) := r2.nextNat (psi - 1)
  let rot := rot0 + 1
  let (trainMark, r4) := r3.nextFin 3 (by omega)
  let (trainBit, r5) := r4.nextBool
  let mut out : Array (AuthB psi kappa) := #[]
  let mut r := r5
  for g in [0:numBlocks] do
    let inTrain := (g + numBlocks - start) % numBlocks < span
    let (mark, bit, blockRot, r') :=
      if inTrain then (trainMark, trainBit, rot, r)
      else Id.run do
        let (m1, ra) := r.nextFin 3 (by omega)
        let (b1, rb) := ra.nextBool
        return (m1, b1, 0, rb)
    r := r'
    for j in [0:psi] do
      let i := g * psi + j
      out := out.push (departCell psi kappa i g hpsi blockRot bit mark false)
  return (out, r)

/-- **(d)** generalised Leaf-C episode under a single ring-wide mark (the
documented hardest, "all marks equal", case): one comparison episode at a
random block, everything else departed, one global colour. -/
def ensembleD (psi kappa n : Nat) (hpsi : 0 < psi) (r0 : RNG) :
    Array (AuthB psi kappa) × RNG := Id.run do
  let numBlocks := n / psi
  let (mark, r1) := r0.nextFin 3 (by omega)
  let (epBlock, r2) := r1.nextNat numBlocks
  let mut out : Array (AuthB psi kappa) := #[]
  let mut r := r2
  for g in [0:numBlocks] do
    let (bit, r') := r.nextBool
    r := r'
    if g == epBlock then
      let (blk, r'') := buildBlockWithEpisode psi kappa g hpsi bit mark false r
      r := r''
      out := out ++ blk
    else
      for j in [0:psi] do
        let i := g * psi + j
        out := out.push (departCell psi kappa i g hpsi 0 bit mark false)
  return (out, r)

def encodeConfig {psi kappa : Nat} (cfg : Array (AuthB psi kappa)) : Json :=
  Json.arr (cfg.map PPLLAuthSim.encode)

def run (ensemble : String) (psi kappa n count : Nat) (rngSeed : UInt64)
    (outPath : System.FilePath) : IO UInt32 := do
  if hpsi : 0 < psi then
    if n % psi != 0 then
      IO.eprintln "n must be a multiple of psi (blocks tile the ring)"
      return 2
    let gen : RNG → Array (AuthB psi kappa) × RNG :=
      match ensemble with
      | "a" => ensembleA psi kappa n hpsi
      | "b" => ensembleB psi kappa n hpsi
      | "c" => ensembleC psi kappa n hpsi
      | "d" => ensembleD psi kappa n hpsi
      | _ => fun r => (#[], r)
    if ensemble ∉ (["a", "b", "c", "d"] : List String) then
      IO.eprintln "ensemble must be a, b, c or d"
      return 2
    let h ← IO.FS.Handle.mk outPath .write
    let mut r : RNG := ⟨rngSeed⟩
    for _ in [0:count] do
      let (cfg, r1) := gen r
      r := r1
      h.putStrLn (encodeConfig cfg).compress
    h.flush
    return 0
  else
    IO.eprintln "psi must be positive"
    return 2

end ZZAuthFullDischargeHard

def main (args : List String) : IO UInt32 := do
  match args with
  | [ensemble, psiS, nS, kappaS, countS, rngS, outS] =>
    ZZAuthFullDischargeHard.run ensemble psiS.toNat! kappaS.toNat! nS.toNat! countS.toNat!
      (UInt64.ofNat rngS.toNat!) outS
  | _ =>
    IO.eprintln "usage: zz-auth-full-discharge-hard ENSEMBLE(a|b|c|d) PSI N KAPPA COUNT RNGSEED OUTFILE"
    return 2
