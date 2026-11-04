import Leader.L3.CertRows
import Leader.L3.Protocol

/-!
# L3 differential-test driver (PLAN module M6)

`lean --run Leader/L3/SimDiff.lean < cases.txt > lean_out.txt` reads one test case per line
and writes one result line per case.  Run by `scripts/l3_simdiff_slurm.sh`; compared with the
JS reference by `scripts/l3_lean_vs_js.mjs`.

Line format: `MODE q <agent x> <agent y>`, all numbers decimal, space separated.

## Agent vector (63 numbers, fixed order, fixed width)

```
 0 l  1 b  2 sh  3 sg  4 pack  5 mode  6 bit  7 tok  8 lease
 9 small.kind(OFF=0,SPENT=1,RUN=2)  10 small.j (0 unless RUN)
11 req 12 grant 13 C 14 alpha 15 m 16 EU 17 ED 18 u 19 beta 20 d
21 ser.phase 22 ser.out 23 ser.probe 24 ser.cert 25 ser.wphase
26 siLease
27 si.kind 28 si.busy 29 si.cur 30 si.j 31 si.z 32 si.p 33 si.a
34 rawKick
35 rawTok.present 36 rawTok.j (JS index 1..t, 0 if absent) 37 z 38 p 39 a 40 h 41 m
42 h  43 kH  44 wBase
45 wOut.tag(E=0,U=1,D=2) 46 wOut.v 47 wOut.T
48 wIn.tag(E=0,X=1,P=2,S=3) 49 wIn.v 50 wIn.T
51 wCarry.tag(OFF=0,W=1) 52 wCarry.c
53 qOut.tag 54 qOut.v 55 qOut.T
56 qIn.tag 57 qIn.v 58 qIn.T
59 qCarry.tag(OFF=0,L=1) 60 qCarry.c 61 qCarry.e
62 topDirty
```
Enums use the constructor order of `Alphabet.lean`; `Fin` by value; `Bool` as `0/1`; payload slots
of tokens without payload are `0`.  An out-of-range or non-canonical vector decodes to `none`
and the line is answered `ERR`.

## Modes

* `cert`: `certificateStep`; output `x' y' d1Reject topReject duX duY ddX ddY | serRow siRow rawRow`
* `hk`: `hKStep`; output `x' y' | row report`
* `pair`: `transition` (the `pairFull` assembly of `Protocol.lean`); output `x' y'`
-/

namespace L3

set_option autoImplicit false

/-! ## Encoding of enums -/

def boolN (b : Bool) : Nat := if b then 1 else 0

def Mode.idx : Mode → Nat
  | .RESET => 0 | .RWAIT => 1 | .ARMED => 2 | .IWAIT => 3 | .CSTART => 4 | .CWAIT => 5
def Mode.ofIdx? : Nat → Option Mode
  | 0 => some .RESET | 1 => some .RWAIT | 2 => some .ARMED | 3 => some .IWAIT
  | 4 => some .CSTART | 5 => some .CWAIT | _ => none

def BTok.idx : BTok → Nat
  | .E => 0 | .RR => 1 | .RL => 2 | .IR => 3 | .AL => 4 | .CR0 => 5 | .CR1 => 6
  | .CL0 => 7 | .CL1 => 8
def BTok.ofIdx? : Nat → Option BTok
  | 0 => some .E | 1 => some .RR | 2 => some .RL | 3 => some .IR | 4 => some .AL
  | 5 => some .CR0 | 6 => some .CR1 | 7 => some .CL0 | 8 => some .CL1 | _ => none

def SerPhase.idx : SerPhase → Nat | .C => 0 | .B => 1 | .F => 2
def SerPhase.ofIdx? : Nat → Option SerPhase | 0 => some .C | 1 => some .B | 2 => some .F | _ => none
def SerOut.idx : SerOut → Nat | .NEW => 0 | .WAIT => 1 | .DONE => 2
def SerOut.ofIdx? : Nat → Option SerOut | 0 => some .NEW | 1 => some .WAIT | 2 => some .DONE | _ => none
def SerProbe.idx : SerProbe → Nat | .NONE => 0 | .PENDING => 1 | .INTERNAL_OK => 2 | .LEAF_OK => 3
def SerProbe.ofIdx? : Nat → Option SerProbe
  | 0 => some .NONE | 1 => some .PENDING | 2 => some .INTERNAL_OK | 3 => some .LEAF_OK | _ => none
def SerCert.idx : SerCert → Nat | .IDLE => 0 | .REQUESTED => 1 | .RUNNING => 2
def SerCert.ofIdx? : Nat → Option SerCert
  | 0 => some .IDLE | 1 => some .REQUESTED | 2 => some .RUNNING | _ => none
def SerWPhase.idx : SerWPhase → Nat | .OFF => 0 | .QUARANTINE => 1 | .VALIDATING => 2 | .CURRENT => 3
def SerWPhase.ofIdx? : Nat → Option SerWPhase
  | 0 => some .OFF | 1 => some .QUARANTINE | 2 => some .VALIDATING | 3 => some .CURRENT | _ => none
def SIKind.idx : SIKind → Nat | .OFF => 0 | .PREFIX => 1 | .ROOT => 2
def SIKind.ofIdx? : Nat → Option SIKind | 0 => some .OFF | 1 => some .PREFIX | 2 => some .ROOT | _ => none
def SICur.idx : SICur → Nat | .NONE => 0 | .BACK => 1 | .SUM => 2
def SICur.ofIdx? : Nat → Option SICur | 0 => some .NONE | 1 => some .BACK | 2 => some .SUM | _ => none
def WBase.idx : WBase → Nat | .NONE => 0 | .SEEK => 1 | .ZERO => 2
def WBase.ofIdx? : Nat → Option WBase | 0 => some .NONE | 1 => some .SEEK | 2 => some .ZERO | _ => none

/-! ## Encoder -/

def encSmall : Small → List Nat
  | .OFF => [0, 0]
  | .SPENT => [1, 0]
  | .RUN j => [2, j.val]

def encSer (s : Ser) : List Nat :=
  [s.phase.idx, s.out.idx, s.probe.idx, s.cert.idx, s.wphase.idx]

def encSI {t : Nat} (s : SI t) : List Nat :=
  [s.kind.idx, boolN s.busy, s.cur.idx, s.j.val, boolN s.z, boolN s.p, boolN s.a]

/-- `rawTok`: present flag, JS index `j = jm1+1`, then `z p a h m`; all zero when absent. -/
def encRaw {t : Nat} : Option (RawTok t) → List Nat
  | none => [0, 0, 0, 0, 0, 0, 0]
  | some r => [1, r.j, boolN r.z, boolN r.p, boolN r.a, boolN r.h, boolN r.m]

def encOut {A : Nat} : OutTok A → List Nat
  | .E => [0, 0, 0]
  | .U => [1, 0, 0]
  | .D v T => [2, v.val, boolN T]

def encIn {A : Nat} : InTok A → List Nat
  | .E => [0, 0, 0]
  | .X => [1, 0, 0]
  | .P v T => [2, v.val, boolN T]
  | .S v T => [3, v.val, boolN T]

def encWC : WCarry → List Nat
  | .OFF => [0, 0]
  | .W c => [1, boolN c]

def encQC : QCarry → List Nat
  | .OFF => [0, 0, 0]
  | .L c e => [1, boolN c, boolN e]

/-- The 63-number vector of an agent (order in the module docstring). -/
def encodeAgent (c : Compiled) (a : Agent c) : List Nat :=
  [boolN a.l, a.b.val, boolN a.sh, boolN a.sg, a.pack.val, a.mode.idx, boolN a.bit, a.tok.idx,
   a.lease.val] ++ encSmall a.small ++
  [boolN a.req, boolN a.grant, boolN a.C, boolN a.alpha, boolN a.m, boolN a.EU, boolN a.ED,
   boolN a.u, boolN a.beta, a.d.val] ++ encSer a.ser ++ [a.siLease.val] ++ encSI a.si ++
  [boolN a.rawKick] ++ encRaw a.rawTok ++ [a.h.val, a.kH.val, a.wBase.idx] ++
  encOut a.wOut ++ encIn a.wIn ++ encWC a.wCarry ++
  encOut a.qOut ++ encIn a.qIn ++ encQC a.qCarry ++ [boolN a.topDirty]

/-! ## Decoder (reader over the number list) -/

abbrev Rd := StateT (List Nat) Option

def rd : Rd Nat := fun l => match l with | [] => none | x :: xs => some (x, xs)

def rdBool : Rd Bool := do
  let v ← rd
  if v == 0 then pure false else if v == 1 then pure true else failure

def rdFin (n : Nat) : Rd (Fin n) := do
  let v ← rd
  if h : v < n then pure ⟨v, h⟩ else failure

def rdEnum {α : Type} (f : Nat → Option α) : Rd α := do
  let v ← rd
  match f v with
  | some a => pure a
  | none => failure

def rdZero : Rd Unit := do
  let v ← rd
  if v == 0 then pure () else failure

def rdSmall : Rd Small := do
  let k ← rd
  let j ← rdFin kStar
  if k == 0 then (if j.val == 0 then pure .OFF else failure)
  else if k == 1 then (if j.val == 0 then pure .SPENT else failure)
  else if k == 2 then pure (.RUN j)
  else failure

def rdSer : Rd Ser := do
  let phase ← rdEnum SerPhase.ofIdx?
  let out ← rdEnum SerOut.ofIdx?
  let probe ← rdEnum SerProbe.ofIdx?
  let cert ← rdEnum SerCert.ofIdx?
  let wphase ← rdEnum SerWPhase.ofIdx?
  pure { phase := phase, out := out, probe := probe, cert := cert, wphase := wphase }

def rdSI (t : Nat) : Rd (SI t) := do
  let kind ← rdEnum SIKind.ofIdx?
  let busy ← rdBool
  let cur ← rdEnum SICur.ofIdx?
  let j ← rdFin (t + 1)
  let z ← rdBool
  let p ← rdBool
  let a ← rdBool
  pure { kind := kind, busy := busy, cur := cur, j := j, z := z, p := p, a := a }

def rdRaw (t : Nat) : Rd (Option (RawTok t)) := do
  let f ← rd
  let j ← rd
  let z ← rdBool
  let p ← rdBool
  let a ← rdBool
  let h ← rdBool
  let m ← rdBool
  if f == 0 then
    (if j == 0 && !z && !p && !a && !h && !m then pure none else failure)
  else if f == 1 then
    (if hj : 1 ≤ j ∧ j - 1 < t then
      pure (some { jm1 := ⟨j - 1, hj.2⟩, z := z, p := p, a := a, h := h, m := m })
     else failure)
  else failure

def rdOut (A : Nat) : Rd (OutTok A) := do
  let tag ← rd
  let v ← rdFin A
  let T ← rdBool
  if tag == 0 then (if v.val == 0 && !T then pure .E else failure)
  else if tag == 1 then (if v.val == 0 && !T then pure .U else failure)
  else if tag == 2 then pure (.D v T)
  else failure

def rdIn (A : Nat) : Rd (InTok A) := do
  let tag ← rd
  let v ← rdFin A
  let T ← rdBool
  if tag == 0 then (if v.val == 0 && !T then pure .E else failure)
  else if tag == 1 then (if v.val == 0 && !T then pure .X else failure)
  else if tag == 2 then pure (.P v T)
  else if tag == 3 then pure (.S v T)
  else failure

def rdWC : Rd WCarry := do
  let tag ← rd
  let c ← rdBool
  if tag == 0 then (if !c then pure .OFF else failure)
  else if tag == 1 then pure (.W c)
  else failure

def rdQC : Rd QCarry := do
  let tag ← rd
  let c ← rdBool
  let e ← rdBool
  if tag == 0 then (if !c && !e then pure .OFF else failure)
  else if tag == 1 then pure (.L c e)
  else failure

/-- Read one agent (63 numbers) from the front of the list. -/
def rdAgent (c : Compiled) : Rd (Agent c) := do
  let l ← rdBool
  let b ← rdFin 3
  let sh ← rdBool
  let sg ← rdBool
  let pack ← rdFin (c.b + 2)
  let mode ← rdEnum Mode.ofIdx?
  let bit ← rdBool
  let tok ← rdEnum BTok.ofIdx?
  let lease ← rdFin (c.bankLeaseCap + 1)
  let small ← rdSmall
  let req ← rdBool
  let grant ← rdBool
  let C ← rdBool
  let alpha ← rdBool
  let m ← rdBool
  let EU ← rdBool
  let ED ← rdBool
  let u ← rdBool
  let beta ← rdBool
  let d ← rdFin c.topA
  let ser ← rdSer
  let siLease ← rdFin (c.siLeaseMax + 1)
  let si ← rdSI c.t
  let rawKick ← rdBool
  let rawTok ← rdRaw c.t
  let h ← rdFin (34 * c.t + 3)
  let kH ← rdFin (c.t + 1)
  let wBase ← rdEnum WBase.ofIdx?
  let wOut ← rdOut c.topA
  let wIn ← rdIn c.topA
  let wCarry ← rdWC
  let qOut ← rdOut c.topA
  let qIn ← rdIn c.topA
  let qCarry ← rdQC
  let topDirty ← rdBool
  pure { l := l, b := b, sh := sh, sg := sg, pack := pack, mode := mode, bit := bit, tok := tok,
         lease := lease, small := small, req := req, grant := grant, C := C, alpha := alpha,
         m := m, EU := EU, ED := ED, u := u, beta := beta, d := d, ser := ser,
         siLease := siLease, si := si, rawKick := rawKick, rawTok := rawTok, h := h, kH := kH,
         wBase := wBase, wOut := wOut, wIn := wIn, wCarry := wCarry, qOut := qOut, qIn := qIn,
         qCarry := qCarry, topDirty := topDirty }

/-- Decode a whole 63-number vector (no trailing numbers). -/
def decodeAgent (c : Compiled) (l : List Nat) : Option (Agent c) :=
  match (rdAgent c).run l with
  | some (a, []) => some a
  | _ => none

/-! ## Driver -/

def evBits (e : CertEvent) : List Nat :=
  [boolN e.d1Reject, boolN e.topReject, boolN e.duX, boolN e.duY, boolN e.ddX, boolN e.ddY]

def joinNums (l : List Nat) : String := " ".intercalate (l.map toString)

/-- One case line to one result line; `none` is a malformed line. -/
def runLine (line : String) : Option String :=
  match (line.splitOn " ").filter (fun s => s != "") with
  | mode :: qs :: rest => do
    let q ← qs.toNat?
    let nums ← rest.mapM String.toNat?
    let c := compileAdvice q
    let ((x, y), tail) ← (do
      let x ← rdAgent c
      let y ← rdAgent c
      pure (x, y) : Rd (Agent c × Agent c)).run nums
    if !tail.isEmpty then none else
    if mode == "cert" then
      let r := certificateStepFull c x y
      some (joinNums (encodeAgent c r.x ++ encodeAgent c r.y ++ evBits r.event) ++ " | " ++
            r.rows.serializer ++ " " ++ r.rows.si ++ " " ++ r.rows.raw)
    else if mode == "hk" then
      let r := hKStepFull c x y
      let (x', y') := hKStep c x y
      some (joinNums (encodeAgent c x' ++ encodeAgent c y') ++ " | " ++ r.row ++ " " ++
            toString (boolN r.report))
    else if mode == "pair" then
      -- full transition `pairFull` (`composed-full.mjs:744-757`) = `L3.transition`
      let (x', y') := transition c x y
      some (joinNums (encodeAgent c x' ++ encodeAgent c y'))
    else none
  | _ => none

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  for _ in [0:100000000] do
    let line ← stdin.getLine
    if line.isEmpty then break
    let t := line.trimAscii.toString
    if t.isEmpty then continue
    match runLine t with
    | some s => stdout.putStrLn s
    | none => stdout.putStrLn "ERR"
  stdout.flush

end L3

def main : IO Unit := L3.main
