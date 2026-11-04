import Leader.Wu.Sim.AuthCarrier

/-!
# FULL-DISCHARGE random seed generator (authFplusmcc)

Design-exploration tool, not a proof certificate.  Generates random
`authFplusmcc` configurations satisfying the FULL-DISCHARGE precondition
(`ZDIV.md` §27, Leaf C) for the
`ppll-authf-walk` / `ppll-authf-census` tools:

* leaderless (`core.leader = false` on every cell);
* perfect labels (`core.label = i % ψ`, cell position `i` in the ring);
* every core lies in `AgentState.inProtocolDomain κ` — automatic here, since
  every field below is built directly as a value of its already-bounded
  `Fin`/`Option`-of-bounded type, the same construction `BoundedAgentState`
  uses to witness the domain predicate;
* `reset_cmd = false`, `echo = false` on every cell;
* full (`core.path = some _`, never `.bot`) on every cell;
* free of generation debris (`core.state` never `produce` or `done`).

Every other field (the 13 remaining `MainState` values, `path` itself —
which may be *misaligned*, i.e. its own `label` need not equal `i % ψ`,
`path2`, `path3`, `path4`, `path5`, `write_state`, `write`, every plain
`Bool`/`Fin` field, and the six AuthF marks/scope) is drawn uniformly at
random, independently per cell.

Usage: `zz-auth-full-discharge PSI N KAPPA COUNT RNGSEED OUTFILE`, writes
`COUNT` JSONL lines to `OUTFILE`, each an `n`-cell configuration in the
`PPLLAuthSim.encode` schema consumed by `ppll-authf-walk` and
`ppll-authf-census`.
-/

set_option autoImplicit false

open Lean PPLLAuthF PPLLAuthSim

namespace ZZAuthFullDischarge

-- Retroactive `Inhabited` instances (needed for `Array.get!` below); these do
-- not touch `Leader/Wu/Protocol/State.lean` itself.
deriving instance Inhabited for MainState
deriving instance Inhabited for WriteState
deriving instance Inhabited for WriteAction

/-! ## Minimal splitmix64 PRNG (copy of the pattern in `PPLLAuthWalk.splitmix`) -/

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

/-- Uniform in `[0, bound)`; caller guarantees `bound > 0`. Slight modulo bias
is immaterial for this exploration tool (bounds here are all small: ≤ ψ+1 ≤ 13). -/
@[inline] def RNG.nextNat (r : RNG) (bound : Nat) : Nat × RNG :=
  let (v, r') := r.next
  (v.toNat % bound, r')

@[inline] def RNG.nextBool (r : RNG) : Bool × RNG :=
  let (v, r') := r.nextNat 2
  (v == 1, r')

/-- `Fin bound` for `bound > 0`, from a random `Nat`. -/
@[inline] def finOfNat (bound : Nat) (hbound : 0 < bound) (v : Nat) : Fin bound :=
  ⟨v % bound, Nat.mod_lt v hbound⟩

@[inline] def RNG.nextFin (r : RNG) (bound : Nat) (hbound : 0 < bound) : Fin bound × RNG :=
  let (v, r') := r.nextNat bound
  (finOfNat bound hbound v, r')

/-! ## Random field builders -/

/-- The 13 `MainState` values other than `produce`/`done` (generation debris). -/
def nonDebrisStates : Array MainState :=
  #[.depart, .none, .congest, .lock, .compare1, .compare2, .eliminate_signal,
    .CHECK_ready, .equal, .larger, .less, .toss, .toss_done]

def writeStates : Array WriteState :=
  #[.depart, .ready, .increment_WS, .increment_WS_done, .done, .equal, .larger,
    .less, .produce, .overwrite, .move_flip, .move, .increment_group, .none]

def writeActions : Array WriteAction :=
  #[.overwrite, .move_flip, .move, .increment_group, .none]

def RNG.nextState (r : RNG) : MainState × RNG :=
  let (i, r') := r.nextNat nonDebrisStates.size
  (nonDebrisStates[i]!, r')

def RNG.nextWriteState (r : RNG) : WriteState × RNG :=
  let (i, r') := r.nextNat writeStates.size
  (writeStates[i]!, r')

def RNG.nextWriteAction (r : RNG) : WriteAction × RNG :=
  let (i, r') := r.nextNat writeActions.size
  (writeActions[i]!, r')

/-- A random `path` value that is always `some _` ("full"); its `label` is an
independent random `Fin ψ`, so it need not equal the cell's own `label`
("paths may be misaligned"). -/
def RNG.nextPath (r : RNG) (psi : Nat) (hpsi : 0 < psi) : BoundedPathInfo psi × RNG :=
  let (lab, r1) := r.nextFin psi hpsi
  let (bit, r2) := r1.nextFin 2 (by omega)
  (.some lab bit, r2)

def RNG.nextPath2 (r : RNG) (psi : Nat) (hpsi : 0 < psi) :
    Option (BoundedPath2Info psi) × RNG :=
  let (present, r0) := r.nextBool
  if present then
    let (lab, r1) := r0.nextFin psi hpsi
    let (bit, r2) := r1.nextFin 2 (by omega)
    let (pos, r3) := r2.nextFin (psi + 1) ((by omega : 0 < psi + 1))
    let (act, r4) := r3.nextFin 6 (by omega)
    (some { label := lab, bit := bit, position := pos, action := act }, r4)
  else (none, r0)

def RNG.nextPath3 (r : RNG) (psi : Nat) (hpsi : 0 < psi) :
    Option (BoundedPath3Info psi) × RNG :=
  let (present, r0) := r.nextBool
  if present then
    let (lab, r1) := r0.nextFin psi hpsi
    let (bit, r2) := r1.nextFin 2 (by omega)
    let (flag, r3) := r2.nextFin 2 (by omega)
    (some { label := lab, bit := bit, flag := flag }, r3)
  else (none, r0)

/-- `path4`/`path5`: `Option (CleaningLabel ψ × Fin 2)`, where `CleaningLabel`
adds Algorithm 5's `-1` clean sentinel to the plain `Fin ψ` label. -/
def RNG.nextCleanPath (r : RNG) (psi : Nat) (hpsi : 0 < psi) :
    Option (CleaningLabel psi × Fin 2) × RNG :=
  let (present, r0) := r.nextBool
  if present then
    let (isClean, r1) := r0.nextBool
    let (lab, r2) := r1.nextFin psi hpsi
    let (bit, r3) := r2.nextFin 2 (by omega)
    let cl : CleaningLabel psi := if isClean then .clean else .normal lab
    (some (cl, bit), r3)
  else (none, r0)

/-- One random cell at ring position `i`, satisfying every FULL-DISCHARGE
precondition field. -/
def randomCell (psi kappa : Nat) (hpsi : 0 < psi) (i : Nat) (r0 : RNG) :
    AuthB psi kappa × RNG := Id.run do
  let mut r := r0
  let (state, r1) := r.nextState; r := r1
  let (path, r1) := r.nextPath psi hpsi; r := r1
  let (path2, r1) := r.nextPath2 psi hpsi; r := r1
  let (path3, r1) := r.nextPath3 psi hpsi; r := r1
  let (path4, r1) := r.nextCleanPath psi hpsi; r := r1
  let (path5, r1) := r.nextCleanPath psi hpsi; r := r1
  let (probe, r1) := r.nextBool; r := r1
  let (phase, r1) := r.nextBool; r := r1
  let (bit, r1) := r.nextBool; r := r1
  let (wait, r1) := r.nextBool; r := r1
  let (reset, r1) := r.nextBool; r := r1
  let (carry, r1) := r.nextBool; r := r1
  let (h_field, r1) := r.nextBool; r := r1
  let (p, r1) := r.nextBool; r := r1
  let (p_carry, r1) := r.nextBool; r := r1
  let (shield, r1) := r.nextBool; r := r1
  let (last, r1) := r.nextBool; r := r1
  let (last_set, r1) := r.nextBool; r := r1
  let (last_unset, r1) := r.nextBool; r := r1
  let (b_carry, r1) := r.nextBool; r := r1
  let (gen_ws, r1) := r.nextBool; r := r1
  let (ws_echo, r1) := r.nextBool; r := r1
  let (signal_ws, r1) := r.nextBool; r := r1
  let (count, r1) := r.nextFin (kappa + 1) ((by omega : 0 < kappa + 1)); r := r1
  let (signal_B, r1) := r.nextFin 2 (by omega); r := r1
  let (bullet, r1) := r.nextFin 3 (by omega); r := r1
  let (write_state, r1) := r.nextWriteState; r := r1
  let (write, r1) := r.nextWriteAction; r := r1
  let label : Fin psi := finOfNat psi hpsi (i % psi)
  let core : BoundedAgentState psi kappa :=
    { leader := false, probe := probe, phase := phase, bit := bit, wait := wait,
      state := state, path := path, reset := reset, carry := carry, count := count,
      label := label, h_field := h_field, path2 := path2, path3 := path3,
      path4 := path4, path5 := path5, p := p, p_carry := p_carry,
      reset_cmd := false, echo := false, signal_B := signal_B, bullet := bullet,
      shield := shield, write_state := write_state, write := write, last := last,
      last_set := last_set, last_unset := last_unset, b_carry := b_carry,
      gen_ws := gen_ws, ws_echo := ws_echo, signal_ws := signal_ws }
  let (path_mark, r1) := r.nextFin 3 (by omega); r := r1
  let (ctrl_mark, r1) := r.nextFin 3 (by omega); r := r1
  let (p2, r1) := r.nextFin 3 (by omega); r := r1
  let (p4, r1) := r.nextFin 3 (by omega); r := r1
  let (p5, r1) := r.nextFin 3 (by omega); r := r1
  let (sessionScope, r1) := r.nextBool; r := r1
  let m : PPLLAuthSim.Marks :=
    { path := path_mark, ctrl := ctrl_mark, p2 := p2, p4 := p4, p5 := p5,
      scope := if sessionScope then .session else .line }
  return (⟨core, m⟩, r)

/-- One random `n`-cell configuration. -/
def randomConfig (psi kappa n : Nat) (hpsi : 0 < psi) (r0 : RNG) :
    Array (AuthB psi kappa) × RNG := Id.run do
  let mut r := r0
  let mut out : Array (AuthB psi kappa) := #[]
  for i in [0:n] do
    let (a, r1) := randomCell psi kappa hpsi i r
    out := out.push a
    r := r1
  return (out, r)

def encodeConfig {psi kappa : Nat} (cfg : Array (AuthB psi kappa)) : Json :=
  Json.arr (cfg.map PPLLAuthSim.encode)

def run (psi kappa n count : Nat) (rngSeed : UInt64) (outPath : System.FilePath) :
    IO UInt32 := do
  if hpsi : 0 < psi then
    IO.FS.writeFile outPath ""
    let h ← IO.FS.Handle.mk outPath .write
    let mut r : RNG := ⟨rngSeed⟩
    for _ in [0:count] do
      let (cfg, r1) := randomConfig psi kappa n hpsi r
      r := r1
      h.putStrLn (encodeConfig cfg).compress
    h.flush
    return 0
  else
    IO.eprintln "psi must be positive"
    return 2

end ZZAuthFullDischarge

def main (args : List String) : IO UInt32 := do
  match args with
  | [psiS, nS, kappaS, countS, rngS, outS] =>
    let psi := psiS.toNat!
    let n := nS.toNat!
    let kappa := kappaS.toNat!
    let count := countS.toNat!
    let rngSeed := UInt64.ofNat rngS.toNat!
    if n % psi != 0 then
      IO.eprintln "n must be a multiple of psi (perfect i % psi labels tile the ring)"
      return 2
    ZZAuthFullDischarge.run psi kappa n count rngSeed outS
  | _ =>
    IO.eprintln "usage: zz-auth-full-discharge PSI N KAPPA COUNT RNGSEED OUTFILE"
    return 2
