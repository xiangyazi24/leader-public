import Leader.Wu.Sim.AuthCarrier

/-!
# Moving-frontier seed generator (authFplusmcc), ZDIV §34

Design-exploration tool, not a proof certificate.  Third generator of the FULL-DISCHARGE
sampling campaign.  Builds `m = 3` blocks (`n = 3ψ`, the whole grid here
has `n/ψ = 3`):

* `B = G_0` ("buffer"): **SerialPlus**:
  the serial configuration (`core.label = j`, `path = some j _`, `state = depart`,
  `path2 = none`, `path_mark = ctrl_mark = γ_g` shared within the block, no
  `-1` command initially in `path4`/`path5`) but with `p`/`p_carry` arbitrary
  instead of forced `false` (a relaxation forced by the inert-`p`
  counterexample).
* `X = G_1` ("dirty"): one of three mechanisms, uniformly at random —
  `episode` (ensemble b of `Leader/Wu/Sim/AuthDischargeStructuredSeeds.lean` restricted to one block: a coherent
  `lock`/`compare1`+`compare2`/`CHECK_ready`-run/`equal`/`larger`/`less`
  episode), `shift` (ensemble c of `Leader/Wu/Sim/AuthDischargeStructuredSeeds.lean` restricted to one block: `path.label`
  rotated within the block, `core.label` untouched), or `boundary` (the
  smallest counterexample: `X_head` gets an `A2` token and `X_terminal` an
  `A1` token, both at maximal `position = ψ`, line scope). Ensemble d of the Hard generator
  (a single global mark plus an episode) collapses into `episode` once
  restricted to a single block (a single shared block mark is already what
  `episode` uses), so it is not a fourth mechanism here.
* `U = G_2`: SerialPlus or dirty (same three mechanisms), 50/50.

Usage: `zz-auth-frontier-gen PSI KAPPA COUNT RNGSEED OUTFILE` (`n := 3 * PSI`).
-/

set_option autoImplicit false

open Lean PPLLAuthF PPLLAuthSim

namespace ZZAuthFrontierGen

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

/-- One cell at physical position `i`, label `i % ψ`, path label `pathLabel`
(aligned = `i % ψ`, rotated for `shift`), resident bit, single block mark
`mark`, state `st`, an optional `path2` token (`action`, `position`, line
scope, mark = `path_mark`, matching `PPLLAuthF.issue`'s own construction of a
larger/less result and the literal A1/A2 example), and
`p`/`p_carry` (arbitrary — the "Plus" of SerialPlus). -/
def cell (psi kappa i : Nat) (hpsi : 0 < psi) (pathLabel : Fin psi) (bit : Bool)
    (mark : Fin 3) (st : MainState) (path2 : Option (Fin 6 × Fin (psi + 1))) (p pcarry : Bool) :
    AuthB psi kappa :=
  let label : Fin psi := finOfNat psi hpsi (i % psi)
  let bitF : Fin 2 := finOfNat 2 (by omega) (if bit then 1 else 0)
  let core : BoundedAgentState psi kappa :=
    { leader := false, probe := false, phase := false, bit := bit, wait := false,
      state := st, path := .some pathLabel bitF,
      reset := false, carry := false, count := finOfNat (kappa + 1) (by omega) 0,
      label := label, h_field := false,
      path2 := path2.map (fun (act, pos) =>
        { label := pathLabel, bit := bitF, position := pos, action := act }),
      path3 := none, path4 := none, path5 := none, p := p, p_carry := pcarry,
      reset_cmd := false, echo := false, signal_B := finOfNat 2 (by omega) 0,
      bullet := finOfNat 3 (by omega) 0, shield := false, write_state := .none,
      write := .none, last := false, last_set := false, last_unset := false,
      b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }
  let m : Marks := { path := mark, ctrl := mark, p2 := mark, p4 := 0, p5 := 0, scope := .line }
  ⟨core, m⟩

def departCell (psi kappa i : Nat) (hpsi : 0 < psi) (rot : Nat) (bit : Bool) (mark : Fin 3)
    (p pcarry : Bool) : AuthB psi kappa :=
  let j := i % psi
  cell psi kappa i hpsi (finOfNat psi hpsi ((j + rot) % psi)) bit mark .depart none p pcarry

/-- A comparison-episode menu, as `Leader/Wu/Sim/AuthDischargeStructuredSeeds.lean`'s
`episodeMenu`; `larger`/`less` carry the `Path2Info.action` values 4/6
(internal `Fin 6` values 3/5) at the default position `0`. -/
def episodeMenu : Array (Array (MainState × Option (Fin 6))) :=
  #[ #[(.lock, none)]
   , #[(.compare1, none), (.compare2, none)]
   , #[(.CHECK_ready, none), (.CHECK_ready, none), (.CHECK_ready, none)]
   , #[(.equal, none)]
   , #[(.larger, some (finOfNat 6 (by omega) 3))]
   , #[(.less, some (finOfNat 6 (by omega) 5))] ]

/-- SerialPlus block: aligned departed cells, one shared mark, `p`/`p_carry`
arbitrary per cell. -/
def serialPlusBlock (psi kappa g : Nat) (hpsi : 0 < psi) (r0 : RNG) :
    Array (AuthB psi kappa) × RNG := Id.run do
  let (mark, r1) := r0.nextFin 3 (by omega)
  let mut out : Array (AuthB psi kappa) := #[]
  let mut r := r1
  for j in [0:psi] do
    let i := g * psi + j
    let (bit, r2) := r.nextBool
    let (p, r3) := r2.nextBool
    let (pc, r4) := r3.nextBool
    r := r4
    out := out.push (departCell psi kappa i hpsi 0 bit mark p pc)
  return (out, r)

/-- `episode`: a random comparison episode overwrites a random contiguous
sub-run of the block (ensemble b of the Hard generator restricted to one block). -/
def dirtyEpisode (psi kappa g : Nat) (hpsi : 0 < psi) (r0 : RNG) :
    Array (AuthB psi kappa) × RNG := Id.run do
  let (mark, r1) := r0.nextFin 3 (by omega)
  let (bit, r2) := r1.nextBool
  let (mi, r3) := r2.nextNat episodeMenu.size
  let pat := episodeMenu[mi]!
  let len := min pat.size psi
  let (off, r4) := r3.nextNat (psi - len + 1)
  let mut out : Array (AuthB psi kappa) := #[]
  let mut r := r4
  for j in [0:psi] do
    let i := g * psi + j
    if j ≥ off && j < off + len then
      let (st, act) := pat[j - off]!
      let (p, r5) := r.nextBool
      let (pc, r6) := r5.nextBool
      r := r6
      out := out.push
        (cell psi kappa i hpsi (finOfNat psi hpsi j) bit mark st
          (act.map (fun a => (a, finOfNat (psi + 1) (by omega) 0))) p pc)
    else
      let (p, r5) := r.nextBool
      let (pc, r6) := r5.nextBool
      r := r6
      out := out.push (departCell psi kappa i hpsi 0 bit mark p pc)
  return (out, r)

/-- `shift`: `path.label` rotated within the block by `rot ∈ [1,ψ)`, `core.label`
untouched (ensemble c of the Hard generator restricted to one block). -/
def dirtyShift (psi kappa g : Nat) (hpsi : 0 < psi) (r0 : RNG) :
    Array (AuthB psi kappa) × RNG := Id.run do
  let (mark, r1) := r0.nextFin 3 (by omega)
  let (bit, r2) := r1.nextBool
  let (rot0, r3) := r2.nextNat (psi - 1)
  let rot := rot0 + 1
  let mut out : Array (AuthB psi kappa) := #[]
  let mut r := r3
  for j in [0:psi] do
    let i := g * psi + j
    let (p, r4) := r.nextBool
    let (pc, r5) := r4.nextBool
    r := r5
    out := out.push (departCell psi kappa i hpsi rot bit mark p pc)
  return (out, r)

/-- `boundary`: the smallest closed-block
counterexample, restricted to this block — `X_head` gets `A2` (internal
action `1` = printed `2`), `X_terminal` gets `A1` (internal action `0` =
printed `1`), both at maximal `position = ψ`, everything else departed
aligned. This is exactly the case the moving-frontier fix (buffer `B` on the
left, `U` on the right) is supposed to resolve that a closed single block
cannot. -/
def dirtyBoundary (psi kappa g : Nat) (hpsi : 0 < psi) (r0 : RNG) :
    Array (AuthB psi kappa) × RNG := Id.run do
  let (mark, r1) := r0.nextFin 3 (by omega)
  let (bit, r2) := r1.nextBool
  let posMax : Fin (psi + 1) := finOfNat (psi + 1) (by omega) psi
  let mut out : Array (AuthB psi kappa) := #[]
  let mut r := r2
  for j in [0:psi] do
    let i := g * psi + j
    let (p, r3) := r.nextBool
    let (pc, r4) := r3.nextBool
    r := r4
    if j == 0 then
      out := out.push (cell psi kappa i hpsi (finOfNat psi hpsi j) bit mark .depart
        (some (finOfNat 6 (by omega) 1, posMax)) p pc)
    else if j == psi - 1 then
      out := out.push (cell psi kappa i hpsi (finOfNat psi hpsi j) bit mark .depart
        (some (finOfNat 6 (by omega) 0, posMax)) p pc)
    else
      out := out.push (departCell psi kappa i hpsi 0 bit mark p pc)
  return (out, r)

/-- Pick one of the three dirty mechanisms uniformly. -/
def dirtyBlock (psi kappa g : Nat) (hpsi : 0 < psi) (r0 : RNG) :
    Array (AuthB psi kappa) × RNG := Id.run do
  let (choice, r1) := r0.nextNat 3
  match choice with
  | 0 => dirtyEpisode psi kappa g hpsi r1
  | 1 => dirtyShift psi kappa g hpsi r1
  | _ => dirtyBoundary psi kappa g hpsi r1

/-- `B = G_0` SerialPlus, `X = G_1` dirty, `U = G_2` SerialPlus-or-dirty
(50/50). `n = 3ψ` (`m = 3`, the whole round-3 grid). -/
def frontierConfig (psi kappa : Nat) (hpsi : 0 < psi) (r0 : RNG) :
    Array (AuthB psi kappa) × RNG := Id.run do
  let (bBlk, r1) := serialPlusBlock psi kappa 0 hpsi r0
  let (xBlk, r2) := dirtyBlock psi kappa 1 hpsi r1
  let (uDirty, r3) := r2.nextBool
  let (uBlk, r4) := if uDirty then dirtyBlock psi kappa 2 hpsi r3 else serialPlusBlock psi kappa 2 hpsi r3
  return (bBlk ++ xBlk ++ uBlk, r4)

def encodeConfig {psi kappa : Nat} (cfg : Array (AuthB psi kappa)) : Json :=
  Json.arr (cfg.map PPLLAuthSim.encode)

def run (psi kappa count : Nat) (rngSeed : UInt64) (outPath : System.FilePath) : IO UInt32 := do
  if hpsi : 0 < psi then
    let h ← IO.FS.Handle.mk outPath .write
    let mut r : RNG := ⟨rngSeed⟩
    for _ in [0:count] do
      let (cfg, r1) := frontierConfig psi kappa hpsi r
      r := r1
      h.putStrLn (encodeConfig cfg).compress
    h.flush
    return 0
  else
    IO.eprintln "psi must be positive"
    return 2

end ZZAuthFrontierGen

def main (args : List String) : IO UInt32 := do
  match args with
  | [psiS, kappaS, countS, rngS, outS] =>
    ZZAuthFrontierGen.run psiS.toNat! kappaS.toNat! countS.toNat! (UInt64.ofNat rngS.toNat!) outS
  | _ =>
    IO.eprintln "usage: zz-auth-frontier-gen PSI KAPPA COUNT RNGSEED OUTFILE (n := 3*PSI)"
    return 2
