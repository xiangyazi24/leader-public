import Leader.L3.Alphabet

/-!
# L3 certificate rows

Literal transcription of the certificate namespaces of
`research/method-review/l3-machine/composed-full.mjs`, lines 204-760:
H code (`packHBits` ... `advanceH`, 258-285), `postEInfo` (286), `serializerStep` (295-384),
`siStep` (385-445), `rawD1Step` (446-480), `hKStep` (481-505), LIVE-TOP (506-698),
`leasePair` (699-710), `certificateStep` (711-743), with the helpers `freeSI`, `offSI`,
`launchPrefix`, `launchRootBack`, `clearCursor`, `setCursor` (248-253) and the token
constructors (207-215), plus `base.literalEPair` of `composed-gpt.mjs:53-69`.

Conventions.  JS bits `0/1` are `Bool`; `bit(x)` is the identity on `Bool` and is not written.
JS string tags are the enums of `Alphabet.lean`.  `state[x]`, `state[y]` are passed as the two
agents `ox`, `oy`.  Evaluation order, priorities and early exits of the JS are kept; mutation
is rendered by `let` shadowing in the same order.  JS `row` strings are kept as `String`
(diagnostic only).  Out-of-range `Fin` constructions use an explicit fallback branch, stated in
the docstring of the construction.
-/

namespace L3

set_option autoImplicit false

/-! ## Base native owner: `literalEPair` -/

/-- The native record `{l,b,sh,sg}` (`composed-gpt.mjs:56`, `nativeMk`).  Named `CertNative`
to avoid a clash with `Base.lean`. -/
structure CertNative where
  l : Bool
  b : Fin 3
  sh : Bool
  sg : Bool
  deriving DecidableEq, Repr

/-- The native part of an agent. -/
def Agent.certNative {c : Compiled} (a : Agent c) : CertNative :=
  { l := a.l, b := a.b, sh := a.sh, sg := a.sg }

/-- `Fin 3` from a number; the fallback `0` is reached only if `v ≥ 3`.  In `certLiteralEPair`
every value passed is `2`, `1`, or an input `b`, hence `< 3`. -/
def certFinThree (v : Nat) : Fin 3 := if h : v < 3 then ⟨v, h⟩ else ⟨0, by omega⟩

/-- `literalEPair` (`composed-gpt.mjs:53-69`), arrays `l = [l,b,sh,sg]`, `r = [l,b,sh,sg]`
rendered as separate variables updated in the same order. -/
def certLiteralEPair (ax ay : CertNative) : CertNative × CertNative :=
  -- let l=[ax.l,ax.b,ax.sh,ax.sg]; let r=[ay.l,ay.b,ay.sh,ay.sg];
  let lL := ax.l
  let lB : Nat := ax.b.val
  let lSh := ax.sh
  let lSg := ax.sg
  let rL := ay.l
  let rB : Nat := ay.b.val
  let rSh := ay.sh
  let rSg := ay.sg
  -- if(l[0] && l[3]){ l[1]=2; l[2]=1; l[3]=0; }
  let (lB, lSh, lSg) : Nat × Bool × Bool :=
    if lL && lSg then (2, true, false) else (lB, lSh, lSg)
  -- if(r[0] && r[3]){ r[1]=1; r[2]=0; r[3]=0; }
  let (rB, rSh, rSg) : Nat × Bool × Bool :=
    if rL && rSg then (1, false, false) else (rB, rSh, rSg)
  -- if(l[1]>0){ if(r[0]){ if(l[1]===2 && r[2]===0) r[0]=0; }
  --             else { if(r[1]===0) r[1]=l[1]; r[3]=0; }  l[1]=0; }
  let (rL, rB, rSg, lB) : Bool × Nat × Bool × Nat :=
    if lB > 0 then
      if rL then
        (if lB == 2 && !rSh then (false, rB, rSg, 0) else (rL, rB, rSg, 0))
      else
        (rL, (if rB == 0 then lB else rB), false, 0)
    else (rL, rB, rSg, lB)
  -- l[3]=Math.max(l[3],r[3],r[0]);
  let lSg := lSg || rSg || rL
  ({ l := lL, b := certFinThree lB, sh := lSh, sg := lSg },
   { l := rL, b := certFinThree rB, sh := rSh, sg := rSg })

/-! ## Token constructors, SI records (`composed-full.mjs:207-253`) -/

/-- `WC(c)` (`composed-full.mjs:214`). -/
def WC (c : Bool) : WCarry := WCarry.W c
/-- `QC(c,e)` (`composed-full.mjs:215`). -/
def QC (c e : Bool) : QCarry := QCarry.L c e

/-- `Fin (t+1)` from a number.  The fallback `0` is reached only if `v > t`.  Call sites:
`siStep` P1 (`j = L.j+1` under guard `L.j < t`), B0 (`R.j-1`, `R.j ≤ t`), S0 (`L.j+1` under
`L.j+1 < t`); in each the guard gives `v ≤ t`. -/
def siJ (t v : Nat) : Fin (t + 1) := if h : v < t + 1 then ⟨v, h⟩ else ⟨0, by omega⟩

/-- `freeSI` (`composed-full.mjs:248`). -/
def freeSI {t : Nat} (s : SI t) : Bool := s.kind == .OFF && s.cur == .NONE

/-- `offSI`, i.e. `si0()` (`composed-full.mjs:205`, `249`). -/
def offSI (t : Nat) : SI t :=
  { kind := .OFF, busy := false, cur := .NONE, j := ⟨0, by omega⟩, z := false, p := false, a := true }

/-- `launchPrefix` (`composed-full.mjs:250`). -/
def launchPrefix (t : Nat) : SI t :=
  { kind := .PREFIX, busy := false, cur := .NONE, j := ⟨0, by omega⟩, z := false, p := false,
    a := true }

/-- `launchRootBack(t)` (`composed-full.mjs:251`); `j = t` is in `Fin (t+1)`. -/
def launchRootBack (t : Nat) : SI t :=
  { kind := .ROOT, busy := true, cur := .BACK, j := ⟨t, by omega⟩, z := false, p := false,
    a := true }

/-- `clearCursor` (`composed-full.mjs:252`). -/
def clearCursor {t : Nat} (s : SI t) : SI t :=
  { s with cur := .NONE, j := ⟨0, by omega⟩, z := false, p := false, a := true }

/-- `setCursor` (`composed-full.mjs:253`); `j` goes through `siJ`. -/
def setCursor {t : Nat} (s : SI t) (cur : SICur) (j : Nat) (z p a : Bool) : SI t :=
  { s with cur := cur, j := siJ t j, z := z, p := p, a := a }

/-! ## H code (`composed-full.mjs:255-284`) -/

/-- Decoded `h` value: `WAIT(k,dirty)` or `SCAN(j,z,p,a,m,dirty)`; `none` is EMPTY. -/
inductive HCode
  | wait (k : Nat) (dirty : Bool)
  | scan (j : Nat) (z p a m dirty : Bool)
  deriving DecidableEq, Repr

/-- `HCode.dirty`: JS `h.dirty`. -/
def HCode.dirty : HCode → Bool
  | .wait _ d => d
  | .scan _ _ _ _ _ d => d

/-- `packHBits(xs)` = `xs.reduce((v,x)=>2*v+bit(x),0)` (`composed-full.mjs:258`). -/
def packHBits (xs : List Bool) : Nat :=
  xs.foldl (fun v x => 2 * v + (if x then 1 else 0)) 0

/-- Loop of `unpackHBits` (`composed-full.mjs:259`): `n` counts `i = n-1 ... 0`; each step
sets `a[i] = v&1` and `v = floor(v/2)`; `acc` holds `a[i+1..n-1]`. -/
def unpackHBitsAux : Nat → Nat → List Bool → List Bool
  | 0, _, acc => acc
  | n + 1, v, acc => unpackHBitsAux n (v / 2) ((v % 2 == 1) :: acc)

/-- `unpackHBits(v,n)` (`composed-full.mjs:259`). -/
def unpackHBits (v n : Nat) : List Bool := unpackHBitsAux n v []

/-- `hScanOffset(t) = 1 + 2(t+1)` (`composed-full.mjs:260`). -/
def hScanOffset (t : Nat) : Nat := 1 + 2 * (t + 1)

/-- `encodeH(h,t)` (`composed-full.mjs:261-265`); `none` is `!h`.  For SCAN the JS computes
`32*(h.j-1)`; `h.j ≥ 1` always for decoded and advanced codes, so `Nat` subtraction agrees. -/
def encodeH (t : Nat) (h : Option HCode) : Nat :=
  match h with
  | none => 0
  | some (.wait k dirty) => 1 + 2 * k + (if dirty then 1 else 0)
  | some (.scan j z p a m dirty) => hScanOffset t + 32 * (j - 1) + packHBits [z, p, a, m, dirty]

/-- `decodeH(code,t)` (`composed-full.mjs:266-273`).  The JS assertion
`0 ≤ code < 34t+3` is discharged by the `Fin` type of `Agent.h`; it is not re-checked here.
The `none` fallback of the five-element pattern is unreachable (`unpackHBits _ 5` has length 5). -/
def decodeH (t code : Nat) : Option HCode :=
  if code == 0 then none
  else
    let off := hScanOffset t
    if code < off then some (.wait ((code - 1) / 2) ((code - 1) % 2 == 1))
    else
      let v := code - off
      match unpackHBits (v % 32) 5 with
      | [z, p, a, m, dirty] => some (.scan (1 + v / 32) z p a m dirty)
      | _ => none

/-- `advanceH(h,u,beta,cfg)` (`composed-full.mjs:274-284`); `B[j]` is `c.taps j`. -/
def advanceH (c : Compiled) (h : HCode) (u beta : Bool) : HCode :=
  let t := c.t
  let u0 := u
  let b0 := beta
  match h with
  | .wait k dirty =>
    if k > 0 then .wait (k - 1) dirty
    else .scan 1 u0 (c.taps 0 && u0) u0 false dirty
  | .scan j z p a m dirty =>
    if j < t then
      let j' := j + 1
      let a' := a && u0
      .scan j' (z || u0) (Bool.xor p (c.taps j && u0)) a' (if j' == t then (b0 != a') else m) dirty
    else .wait 0 (dirty || m || !z || (u0 != p))

/-! ## Post-E info, `serializerStep` -/

/-- `postEInfo` result `{eX,eY}` (`composed-full.mjs:286-289`). -/
structure PostE where
  eX : CertNative
  eY : CertNative
  deriving DecidableEq, Repr

/-- `postEInfo(state,x,y)` (`composed-full.mjs:286-289`): `literalEPair` of the two agents. -/
def postEInfo {c : Compiled} (ox oy : Agent c) : PostE :=
  let r := certLiteralEPair ox.certNative oy.certNative
  { eX := r.1, eY := r.2 }

/-- The `hard` record returned by `serializerStep` (`composed-full.mjs:378`). -/
structure HardFlags where
  hardS1 : Bool
  hardChallenge : Bool
  hardAccept : Bool
  softAccept : Bool
  hardLeft : Bool
  hardRight : Bool
  deriving DecidableEq, Repr

/-- Result `{x,y,row,hard}` of `serializerStep`. -/
structure SerResult where
  x : Ser
  y : Ser
  row : String
  hard : HardFlags
  deriving DecidableEq, Repr

/-- Closure `canonicalC` of `serializerStep` (`composed-full.mjs:312`). -/
def serCanonicalC (z : Ser) : Ser :=
  { z with phase := .C, out := .NEW, probe := .NONE, wphase := .OFF }

/-- Closure `enterB` (`composed-full.mjs:313-314`). -/
def serEnterB (z : Ser) (parentPhase : SerWPhase) : Ser :=
  { z with phase := .B, out := .NEW, probe := .NONE,
           wphase := if parentPhase == .VALIDATING then .VALIDATING else .CURRENT }

/-- Closure `enterF` (`composed-full.mjs:315`). -/
def serEnterF (z : Ser) : Ser := { z with phase := .F, probe := .NONE }

/-- Closure `challengeWrite(l,r)` (`composed-full.mjs:316-320`); returns `(l,r)`.  `r.wphase`
reads `l.wphase` (unchanged by `l.out='WAIT'`). -/
def serChallengeWrite (l r : Ser) : Ser × Ser :=
  ({ l with out := .WAIT },
   { r with phase := .C, out := .NEW, probe := .PENDING,
            wphase := if l.wphase == .VALIDATING then .VALIDATING else .CURRENT })

/-- Closure `tbStar(l,r,fresh)` (`composed-full.mjs:321-325`); `lease0` is `ox.siLease===0`. -/
def serTbStar (lease0 : Bool) (l r : Ser) (fresh : Bool) : Ser × Ser :=
  let wp : SerWPhase :=
    if fresh then (if lease0 then .VALIDATING else .CURRENT) else .QUARANTINE
  ({ l with phase := .B, out := .WAIT, wphase := wp, cert := if fresh then .RUNNING else .IDLE },
   { r with phase := .C, out := .NEW, probe := .PENDING, wphase := if fresh then wp else .OFF })

/-- `serializerStep(state,x,y,post,cfg)` (`composed-full.mjs:295-379`).  The `cfg` argument
is unused in the JS body; `c` is kept only to fix the agent type. -/
def serializerStep (c : Compiled) (ox oy : Agent c) (post : PostE) : SerResult :=
  let sx := ox.ser
  let sy := oy.ser
  let X := sx
  let Y := sy
  let postLX := post.eX.l
  let postLY := post.eY.l
  let validProbe : SerProbe → Bool :=
    fun p => p == .PENDING || p == .INTERNAL_OK || p == .LEAF_OK
  let challenge :=
    sx.phase == .B && (
      (sy.phase == .C && !(sx.out == .WAIT && validProbe sy.probe)) ||
      ((sy.phase == .B || sy.phase == .F) && sx.out != .DONE))
  let hardS1 := postLX && sx.cert == .REQUESTED && ox.siLease.val == 0
  let hardChallenge := sx.wphase == .VALIDATING && challenge
  let hardAccept := postLX && sx.cert == .RUNNING && sx.wphase == .VALIDATING &&
    sx.phase == .B && sx.out == .DONE && sy.phase == .F
  let softAccept := postLX && sx.cert == .RUNNING && sx.wphase == .CURRENT &&
    sx.phase == .B && sx.out == .DONE && sy.phase == .F
  let hardLeft := hardS1 || sx.wphase == .VALIDATING
  let hardRight := hardS1 || hardChallenge || sy.wphase == .VALIDATING
  let lease0 := ox.siLease.val == 0
  let r : Ser × Ser × String :=
    if postLY && !postLX then -- ROOT_IN
      if sy.cert == .IDLE then
        (X, { Y with cert := .REQUESTED, wphase := .QUARANTINE }, "S0")
      else
        let X :=
          if sx.phase == .C && sx.probe == .PENDING then { X with probe := .LEAF_OK, wphase := .OFF }
          else if sx.phase == .B then serCanonicalC X
          else X
        (X, Y, "S5")
    else if postLX && !postLY then -- ROOT_OUT
      if sx.cert == .REQUESTED then
        let p := serTbStar lease0 X Y true
        (p.1, p.2, "S1")
      else if (sx.cert == .IDLE || sx.cert == .RUNNING) && (sx.phase == .C || sx.phase == .F) then
        let p := serTbStar lease0 X Y false
        (p.1, p.2, "SR")
      else if sx.phase == .B && sx.out == .DONE && sy.phase == .F then
        ({ X with phase := .C, out := .NEW, cert := .IDLE, wphase := .CURRENT }, Y, "S6")
      else
        -- row='S2R'
        let p : Ser × Ser :=
          if sy.phase == .C then
            if sx.out == .WAIT && sy.probe == .PENDING then (X, Y)
            else if sx.out == .WAIT && sy.probe == .INTERNAL_OK then
              ({ X with out := .DONE }, serEnterB Y sx.wphase)
            else if sx.out == .WAIT && sy.probe == .LEAF_OK then
              ({ X with out := .DONE }, serEnterF Y)
            else serChallengeWrite X Y
          else if sy.phase == .B then
            if sx.out != .DONE then serChallengeWrite X Y else (X, Y)
          else if sy.phase == .F then serChallengeWrite X Y
          else (X, Y)
        (p.1, p.2, "S2R")
    else if !postLX && !postLY then -- INTERNAL (11 falls to S7)
      if sx.phase == .B then
        -- row='S2N'
        let p : Ser × Ser :=
          if sy.phase == .C then
            if sx.out == .WAIT && sy.probe == .PENDING then (X, Y)
            else if sx.out == .WAIT && sy.probe == .INTERNAL_OK then
              ({ X with out := .DONE }, serEnterB Y sx.wphase)
            else if sx.out == .WAIT && sy.probe == .LEAF_OK then
              ({ X with out := .DONE }, serEnterF Y)
            else serChallengeWrite X Y
          else if sy.phase == .B then
            if sx.out != .DONE then serChallengeWrite X Y else (X, Y)
          else if sy.phase == .F then
            if sx.out == .DONE then ({ serEnterF X with wphase := .CURRENT }, Y)
            else serChallengeWrite X Y
          else (X, Y)
        (p.1, p.2, "S2N")
      else if sx.phase == .C then
        -- row='S3'
        let Y : Ser :=
          if sx.probe == .PENDING then
            if sy.phase == .C then Y
            else if sy.phase == .B || sy.phase == .F then serCanonicalC Y
            else Y
          else if sy.phase == .B || sy.phase == .F then serCanonicalC Y
          else Y
        let X : Ser :=
          if sx.probe == .PENDING then
            if sy.phase == .C then { X with probe := .INTERNAL_OK } else X
          else X
        (X, Y, "S3")
      else if sx.phase == .F then
        -- row='S4'
        (X, (if sy.phase == .B || sy.phase == .F then serCanonicalC Y else Y), "S4")
      else (X, Y, "S7")
    else (X, Y, "S7")
  { x := r.1, y := r.2.1, row := r.2.2,
    hard := { hardS1 := hardS1, hardChallenge := hardChallenge, hardAccept := hardAccept,
              softAccept := softAccept, hardLeft := hardLeft, hardRight := hardRight } }


/-! ## `siStep` -/

/-- Result `{x,y,uX,uY,betaX,betaY,done,row}` of `siStep`. -/
structure SIResult (t : Nat) where
  x : SI t
  y : SI t
  uX : Bool
  uY : Bool
  betaX : Bool
  betaY : Bool
  done : Bool
  row : String
  deriving DecidableEq, Repr

/-- `siStep(state,x,y,post,cfg,hard)` (`composed-full.mjs:385-440`).  Guards read the OLD SI
records `L`, `R` (the JS mutates them only inside the selected branch, after all guards).
`j === t-1` and `j < t-1` are written `j+1 = t`, `j+1 < t` (identical for integers `j ≥ 0`,
and also correct at `t = 0` where `Nat` subtraction would differ).  `taps[j]` is `c.taps j`. -/
def siStep (c : Compiled) (ox oy : Agent c) (post : PostE) (hard : HardFlags) : SIResult c.t :=
  let t := c.t
  let L := ox.si
  let R := oy.si
  let uX := ox.u
  let uY := oy.u
  let bX := ox.beta
  let bY := oy.beta
  let init : SIResult t :=
    { x := L, y := R, uX := uX, uY := uY, betaX := bX, betaY := bY, done := false, row := "F" }
  if hard.hardAccept then
    { init with x := launchPrefix t, y := (if hard.hardRight then offSI t else R), row := "I0" }
  else if hard.hardLeft || hard.hardRight then
    { init with x := (if hard.hardLeft then offSI t else L),
                y := (if hard.hardRight then offSI t else R), row := "I1" }
  else if L.kind == .PREFIX && !L.busy && L.cur == .NONE && L.j.val < t && post.eY.l && freeSI R then
    { init with x := offSI t, done := true, row := "P0" }
  else if L.kind == .PREFIX && !L.busy && L.cur == .NONE && L.j.val < t && !post.eY.l && freeSI R then
    let j := L.j.val + 1
    let z := L.z || uY
    let a := L.a && uY
    let bY := if j < t then false else bY
    { init with
        x := offSI t,
        y := { kind := .PREFIX, busy := false, cur := .NONE, j := siJ t j, z := z, p := false, a := a },
        betaY := bY, row := "P1" }
  else if L.kind == .PREFIX && !L.busy && L.cur == .NONE && L.j.val == t && post.eY.l && freeSI R then
    { init with betaX := L.a, x := offSI t, done := true, row := "P2" }
  else if L.kind == .PREFIX && !L.busy && L.cur == .NONE && L.j.val == t && !post.eY.l && freeSI R then
    { init with uX := (if L.z == false then true else uX), betaX := L.a,
                x := offSI t, y := launchRootBack t, row := "P3" }
  else if R.cur == .BACK && R.j.val > 1 && R.kind != .PREFIX && freeSI L then
    let jOld := R.j.val
    { init with y := clearCursor R, x := setCursor L .BACK (jOld - 1) false false true, row := "B0" }
  else if R.cur == .BACK && R.j.val == 1 && R.kind != .PREFIX && freeSI L then
    { init with y := clearCursor R, x := setCursor L .SUM 0 false false true, row := "B1" }
  else if L.kind == .OFF && L.cur == .SUM && L.j.val + 1 < t && freeSI R then
    let z := L.z || uX
    let p := Bool.xor L.p (c.taps L.j.val && uX)
    let a := if L.j.val == 0 then true else (L.a && uX)
    { init with y := setCursor R .SUM (L.j.val + 1) z p a, x := clearCursor L, row := "S0" }
  else if L.kind == .OFF && L.cur == .SUM && L.j.val + 1 == t && R.kind == .ROOT && R.busy then
    let z := L.z || uX
    let p := Bool.xor L.p (c.taps L.j.val && uX)
    let a := if L.j.val == 0 then true else (L.a && uX)
    let v := if z == false then true else p
    { init with uY := v, betaY := (a && v), x := clearCursor L,
                y := { R with busy := false, cur := .NONE }, row := "S1" }
  else if L.kind == .ROOT && !L.busy && L.cur == .NONE && post.eY.l && freeSI R then
    { init with x := offSI t, done := true, row := "A0" }
  else if L.kind == .ROOT && !L.busy && L.cur == .NONE && !post.eY.l && freeSI R then
    { init with x := offSI t, y := launchRootBack t, row := "A1" }
  else init

/-! ## `rawD1Step` -/

/-- Result `{kickX,kickY,tokX,tokY,reject,row}` of `rawD1Step`. -/
structure RawResult (t : Nat) where
  kickX : Bool
  kickY : Bool
  tokX : Option (RawTok t)
  tokY : Option (RawTok t)
  reject : Bool
  row : String
  deriving DecidableEq, Repr

/-- `rawD1Step(state,x,y,cfg,post)` (`composed-full.mjs:446-475`).  Token index `j` is
`jm1 + 1`.  R0b creates a token of index `j1 = tx.j+1`, i.e. `jm1 = tx.j`; the `dite` on
`tx.j < t` (the JS guard) supplies `tx.j < t`, so no fallback.  R1c creates index `1`
(`jm1 = 0`), which needs `0 < t`; the fallback `none` (no token) is reached only at `t = 0`,
which production (`t ≥ 2`) never has. -/
def rawD1Step (c : Compiled) (ox oy : Agent c) (post : PostE) : RawResult c.t :=
  let t := c.t
  let _kx := ox.rawKick
  let ky := oy.rawKick
  let tx := ox.rawTok
  let ty := oy.rawTok
  match tx with
  | some txv =>
    -- kx=0; ky=0;
    if ty.isSome then
      { kickX := false, kickY := false, tokX := none, tokY := ty, reject := false, row := "R0a" }
    else if h : txv.j < t then
      let v := oy.u
      let g := post.eY.l
      let j1 := txv.j + 1
      let z := txv.z || v
      let p := Bool.xor txv.p (c.taps txv.j && v)
      let a := txv.a && v
      let hh := txv.h || g
      let m := if j1 == t then (!hh && (oy.beta != a)) else false
      { kickX := false, kickY := false, tokX := none,
        tokY := some { jm1 := ⟨txv.j, h⟩, z := z, p := p, a := a, h := hh, m := m },
        reject := false, row := "R0b" }
    else
      let lowerBad := !(txv.h || post.eY.l) && (!txv.z || (oy.u != txv.p))
      { kickX := false, kickY := false, tokX := none, tokY := none,
        reject := (txv.m || lowerBad), row := "R0c" }
  | none =>
    -- kx=0;
    if ty.isSome then
      { kickX := false, kickY := false, tokX := none, tokY := ty, reject := false, row := "R1a" }
    else if !ky then
      { kickX := false, kickY := true, tokX := none, tokY := ty, reject := false, row := "R1b" }
    else
      let v := oy.u
      let g := post.eY.l
      { kickX := false, kickY := false, tokX := none,
        tokY := (if h : 0 < t then
                  some { jm1 := ⟨0, h⟩, z := v, p := (c.taps 0 && v), a := v, h := g, m := false }
                else none),
        reject := false, row := "R1c" }

/-! ## `hKStep` -/

/-- Result of `hKStep`: new `h`/`kH` of both agents, `row`, and the diagnostic `report`. -/
structure HKResult (c : Compiled) where
  hX : Fin (34 * c.t + 3)
  hY : Fin (34 * c.t + 3)
  kX : Fin (c.t + 1)
  kY : Fin (c.t + 1)
  row : String
  report : Bool

/-- `Fin (34t+3)` from a code; fallback is the agent's old code `old`.  Reached only if the
code is `≥ 34t+3`.  Codes come from `encodeH` of `advanceH` of a decoded code or of
`WAIT(kH,false)` with `kH ≤ t`: WAIT gives `≤ 2t+2 < hScanOffset`, SCAN has `j ≤ t` (the
increment is under `j < t`; decoded `j = 1 + v/32` with `v < 32t`), so code `≤ 34t+2`. -/
def hCodeFin (t code : Nat) (old : Fin (34 * t + 3)) : Fin (34 * t + 3) :=
  if h : code < 34 * t + 3 then ⟨code, h⟩ else old

/-- `hKStep(state,x,y,cfg)` with row and report (`composed-full.mjs:481-501`).  `hx`/`hy` are
`Option`; the JS uses `hx.k`, `advanceH(hx,...)` only in branches whose guard has `hx` truthy,
so the default `wait 0 false` of `getD` is never used there.  `kX = (kX+1)%(t+1)`. -/
def hKStepFull (c : Compiled) (ox oy : Agent c) : HKResult c :=
  let t := c.t
  let hx := decodeH t ox.h.val
  let hy := decodeH t oy.h.val
  let hxv : HCode := hx.getD (.wait 0 false)
  let kXold : Fin (c.t + 1) := ox.kH
  let r : Nat × Nat × Fin (c.t + 1) × String × Bool :=
    if hx.isSome && oy.l then
      -- H0 ROOT-SINK
      (0, 0, kXold, "H0",
        (hxv.dirty || (match hxv with | .scan j _ _ _ m _ => j == t && m | _ => false)))
    else if hx.isSome && !oy.l && !hy.isSome then
      -- H1 MOVE
      (0, encodeH t (some (advanceH c hxv oy.u oy.beta)), kXold, "H1", false)
    else if hx.isSome && !oy.l && hy.isSome then
      -- H2 BLOCK
      (ox.h.val, oy.h.val, kXold, "H2", false)
    else if !hx.isSome && ox.l && !oy.l && !hy.isSome then
      -- H3 LAUNCH
      (ox.h.val,
       encodeH t (some (advanceH c (.wait kXold.val false) oy.u oy.beta)),
       ⟨(kXold.val + 1) % (t + 1), Nat.mod_lt _ (by omega)⟩, "H3", false)
    else (ox.h.val, oy.h.val, kXold, "H4", false)
  { hX := hCodeFin t r.1 ox.h
    hY := hCodeFin t r.2.1 oy.h
    kX := r.2.2.1
    kY := oy.kH
    row := r.2.2.2.1
    report := r.2.2.2.2 }

/-- `hKStep(state,x,y,cfg)` (`composed-full.mjs:481-505`): the `{x:{h,kH}, y:{h,kH}}` update,
applied to the two agents; no other field is written. -/
def hKStep (c : Compiled) (x y : Agent c) : Agent c × Agent c :=
  let r := hKStepFull c x y
  ({ x with h := r.hX, kH := r.kX }, { y with h := r.hY, kH := r.kY })

/-! ## LIVE-TOP (`composed-full.mjs:503-698`) -/

/-- `topInternal` (`composed-full.mjs:506`). -/
def topInternal {c : Compiled} (a : Agent c) : Bool := !a.l && !a.beta
/-- `topBorder` (`composed-full.mjs:507`). -/
def topBorder {c : Compiled} (a : Agent c) : Bool := !a.l && a.beta
/-- `topTerminal` (`composed-full.mjs:508`). -/
def topTerminal {c : Compiled} (_x y : Agent c) : Bool := y.l || y.beta
/-- `mod(v,a)` (`composed-full.mjs:509`).  The JS wraps negative remainders; all arguments in
this file are sums of non-negative numbers, so the wrap branch is dead and `Nat` `%` is used. -/
def mod (v a : Nat) : Nat := v % a

/-- Digit `0`. -/
def Compiled.zeroDigit (c : Compiled) : Fin c.topA := ⟨0, c.topA_pos⟩
/-- Digit `mod(v, topA)` as an element of `Fin topA` (always in range). -/
def Compiled.digitMod (c : Compiled) (v : Nat) : Fin c.topA := ⟨mod v c.topA, Nat.mod_lt _ c.topA_pos⟩

/-- `isTag(o,'OFF')` etc. for writer carry. -/
def WCarry.isOff : WCarry → Bool | .OFF => true | _ => false
def WCarry.isW : WCarry → Bool | .W _ => true | _ => false
def QCarry.isOff : QCarry → Bool | .OFF => true | _ => false
def QCarry.isL : QCarry → Bool | .L _ _ => true | _ => false
def OutTok.isE {A : Nat} : OutTok A → Bool | .E => true | _ => false
def OutTok.isU {A : Nat} : OutTok A → Bool | .U => true | _ => false
def OutTok.isD {A : Nat} : OutTok A → Bool | .D _ _ => true | _ => false
def InTok.isE {A : Nat} : InTok A → Bool | .E => true | _ => false
def InTok.isX {A : Nat} : InTok A → Bool | .X => true | _ => false
def InTok.isP {A : Nat} : InTok A → Bool | .P _ _ => true | _ => false
def InTok.isS {A : Nat} : InTok A → Bool | .S _ _ => true | _ => false

/-- Payload accessors (JS `.v`, `.T`, `.c`, `.e`).  On a token without that field the JS reads
`undefined`; here the value is `0`/`false`.  Every use below is under a guard `isTag(·,tag)` of
a tag that has the field, so the default is never read. -/
def outV (c : Compiled) : OutTok c.topA → Fin c.topA | .D v _ => v | _ => c.zeroDigit
def outT {A : Nat} : OutTok A → Bool | .D _ T => T | _ => false
def inV (c : Compiled) : InTok c.topA → Fin c.topA | .P v _ => v | .S v _ => v | _ => c.zeroDigit
def inT {A : Nat} : InTok A → Bool | .P _ T => T | .S _ T => T | _ => false
def wcC : WCarry → Bool | .W x => x | _ => false
def qcC : QCarry → Bool | .L x _ => x | _ => false
def qcE : QCarry → Bool | .L _ e => e | _ => false

/-- The `d, wBase, wOut, wIn, wCarry, qOut, qIn, qCarry, topDirty` record of one side returned
by `liveTopPair` (`composed-full.mjs:684-685`). -/
structure TopFields (c : Compiled) where
  wBase : WBase
  wOut : OutTok c.topA
  wIn : InTok c.topA
  wCarry : WCarry
  qOut : OutTok c.topA
  qIn : InTok c.topA
  qCarry : QCarry
  d : Fin c.topA
  topDirty : Bool
  deriving DecidableEq, Repr

/-- Result of `liveTopPair`. -/
structure TopResult (c : Compiled) where
  x : TopFields c
  y : TopFields c
  topReject : Bool
  deriving DecidableEq, Repr

/-- Overwrite the LIVE-TOP fields of an agent (`...top.x`). -/
def TopFields.applyTo {c : Compiled} (f : TopFields c) (a : Agent c) : Agent c :=
  { a with wBase := f.wBase, wOut := f.wOut, wIn := f.wIn, wCarry := f.wCarry,
           qOut := f.qOut, qIn := f.qIn, qCarry := f.qCarry, d := f.d, topDirty := f.topDirty }

/-- The pair `(wInX/qInX, wInY/qInY)` together with the flags `wix/wiy` (`qix/qiy`) of the
WI (QI) block (`composed-full.mjs:578`, `641`). -/
structure InSt (A : Nat) where
  iX : InTok A
  iY : InTok A
  fx : Bool
  fy : Bool

/-- `liveTopPair(ox,oy,cfg,resolvedBeta)` (`composed-full.mjs:523-688`).  `betaX`/`betaY` are
`resolvedBeta` (default the old betas).  The assertion on `cfg.topOwner` is not represented.
The `site` tags of `baseWrite`, `launch`, `advance` are constant at their construction
(`x`, `x`, `y`) and are dropped; each is `Option` of its value. -/
def liveTopPair (c : Compiled) (ox oy : Agent c) (betaX : Bool := ox.beta)
    (betaY : Bool := oy.beta) : TopResult c :=
  let a := c.topA
  let wox : Agent c := { ox with beta := betaX }
  let woy : Agent c := { oy with beta := betaY }
  let rootX := ox.l
  let rootY := oy.l
  let wTerminal := topTerminal wox woy
  let qTerminal := topTerminal ox oy
  -- LOOK: writer carry and checker carry.
  let wc2Live := ox.wCarry.isW && !wTerminal
  let wc2Success := wc2Live && oy.wCarry.isOff && oy.wIn.isS
  let wc3 := topBorder wox && ox.wCarry.isOff && ox.wIn.isS && !rootY
  let qc2Live := ox.qCarry.isL && !qTerminal
  let qc2Success := qc2Live && oy.qCarry.isOff && oy.qIn.isS
  let qc3 := topBorder ox && ox.qCarry.isOff && ox.qIn.isS && !rootY
  let wo1 := ox.wOut.isD && woy.beta
  let qo1 := ox.qOut.isD && oy.beta
  -- WB.  (wBaseX, wBaseY, baseWrite)
  let wb : WBase × WBase × Option (Fin c.topA) :=
    if rootY then (.NONE, oy.wBase, none)
    else if rootX && !rootY then
      (.NONE, (if oy.wBase == .NONE then .SEEK else oy.wBase), none)
    else if !rootX && ox.wBase == .ZERO then
      (.NONE, (if !rootY && !woy.beta && oy.wBase == .NONE then .ZERO else oy.wBase),
       some c.zeroDigit)
    else if !rootX && ox.wBase == .SEEK then
      (.NONE, (if !rootY && oy.wBase == .NONE then (if woy.beta then .ZERO else .SEEK) else oy.wBase),
       none)
    else (ox.wBase, oy.wBase, none)
  let wBaseX := wb.1
  let wBaseY := wb.2.1
  let baseWrite := wb.2.2
  -- WC look/commit.  (wCarryX, wCarryY, launch, advance)
  let wcr : WCarry × WCarry × Option (Fin c.topA) × Option (Fin c.topA) :=
    if rootX || rootY then
      ((if ox.wCarry.isW then .OFF else ox.wCarry), (if oy.wCarry.isW then .OFF else oy.wCarry),
       none, none)
    else if ox.wCarry.isW then
      if !wTerminal && wc2Success then
        let v := (inV c oy.wIn).val
        let cc := wcC ox.wCarry
        (.OFF, WC (cc && v + 1 == a), none, some (c.digitMod (v + (if cc then 1 else 0))))
      else (.OFF, oy.wCarry, none, none)
    else if wc3 then
      let v := (inV c ox.wIn).val
      (WC (v + 1 == a), oy.wCarry, some (c.digitMod (v + 1)), none)
    else (ox.wCarry, oy.wCarry, none, none)
  let wCarryX := wcr.1
  let wCarryY := wcr.2.1
  let launch := wcr.2.2.1
  let advance := wcr.2.2.2
  -- WI0-WI7: per-coordinate first-match OLD priorities.  (slots, acceptWO)
  let wi : InSt c.topA × Bool :=
    if rootX || rootY then ({ iX := .E, iY := .E, fx := true, fy := true }, false)
    else
      let s : InSt c.topA := { iX := ox.wIn, iY := oy.wIn, fx := false, fy := false }
      let s := if !s.fx && !ox.wCarry.isOff then { s with iX := .E, fx := true } else s
      let s := if !s.fy && !oy.wCarry.isOff then { s with iY := .E, fy := true } else s
      let s := if !s.fx && ox.wIn.isS && inT ox.wIn && !wox.beta then
                 { s with iX := .X, fx := true } else s
      let s := if !s.fx && ox.wIn.isX then
                 let s := { s with iX := .E, fx := true }
                 if !s.fy && topInternal woy && oy.wIn.isS then { s with iY := .X, fy := true } else s
               else s
      let s := if wc2Success && !s.fy then { s with iY := .E, fy := true } else s
      let s := if wc3 && !s.fx then { s with iX := .E, fx := true } else s
      let s := if !s.fx && ox.wIn.isP then
                 if wTerminal then
                   if !inT ox.wIn then { s with iX := .S (inV c ox.wIn) false, fx := true }
                   else if !wox.beta then { s with iX := .E, fx := true }
                   else s
                 else if topInternal woy && oy.wIn.isE && oy.wCarry.isOff && !s.fy then
                   { iX := .E, iY := .P (inV c ox.wIn) (inT ox.wIn), fx := true, fy := true }
                 else if oy.wIn.isS && oy.wCarry.isOff then
                   { s with iX := .S (inV c ox.wIn) (inT ox.wIn), fx := true }
                 else s
               else s
      let acc := !s.fy && wo1 && oy.wIn.isE && oy.wCarry.isOff
      let s := if acc then { s with iY := .P (outV c ox.wOut) (outT ox.wOut), fy := true } else s
      (s, acc)
  let wInX := wi.1.iX
  let wInY := wi.1.iY
  let acceptWO := wi.2
  -- WO.  (wOutX, wOutY)
  let wo : OutTok c.topA × OutTok c.topA :=
    if rootX || rootY then (.E, .E)
    else if wo1 then
      (if acceptWO then ((if outT ox.wOut then .U else .E), oy.wOut) else (ox.wOut, oy.wOut))
    else if ox.wOut.isD && !woy.beta && oy.wOut.isE then
      ((if outT ox.wOut then .U else .E), .D (outV c ox.wOut) (outT ox.wOut))
    else if ox.wOut.isU then (.D ox.d wox.beta, oy.wOut)
    else if wox.beta && ox.wOut.isE && !rootX then (.U, oy.wOut)
    else (ox.wOut, oy.wOut)
  let wOutX := wo.1
  let wOutY := wo.2
  -- WD, with emission-first dirty gate.
  let propX : Option (Fin c.topA) :=
    match baseWrite with
    | some v => some v
    | none => launch
  let propY : Option (Fin c.topA) := advance
  let dX : Fin c.topA :=
    match propX with
    | some v => if !ox.topDirty then v else ox.d
    | none => ox.d
  let dY : Fin c.topA :=
    match propY with
    | some v => if !oy.topDirty then v else oy.d
    | none => oy.d
  -- Checker carry.  (qCarryX, qCarryY, topReject)
  let qcr : QCarry × QCarry × Bool :=
    if rootX || rootY then
      ((if ox.qCarry.isL then .OFF else ox.qCarry), (if oy.qCarry.isL then .OFF else oy.qCarry),
       false)
    else if ox.qCarry.isL then
      if qTerminal then (.OFF, oy.qCarry, qcE ox.qCarry)
      else if qc2Success then
        let v := (inV c oy.qIn).val
        let cc := qcC ox.qCarry
        let e := qcE ox.qCarry
        let c1 := cc && v + 1 == a
        let e1 := e || (oy.d.val != mod (v + (if cc then 1 else 0)) a)
        (.OFF, QC c1 e1, false)
      else (.OFF, oy.qCarry, false)
    else if qc3 then
      let v := (inV c ox.qIn).val
      (QC (v + 1 == a) (ox.d.val != mod (v + 1) a), oy.qCarry, false)
    else (ox.qCarry, oy.qCarry, false)
  let qCarryX := qcr.1
  let qCarryY := qcr.2.1
  let topRejectCarry := qcr.2.2
  -- QI.  (slots, acceptQO)
  let qi : InSt c.topA × Bool :=
    if rootX || rootY then ({ iX := .E, iY := .E, fx := true, fy := true }, false)
    else
      let s : InSt c.topA := { iX := ox.qIn, iY := oy.qIn, fx := false, fy := false }
      let s := if !s.fx && !ox.qCarry.isOff then { s with iX := .E, fx := true } else s
      let s := if !s.fy && !oy.qCarry.isOff then { s with iY := .E, fy := true } else s
      let s := if !s.fx && ox.qIn.isS && inT ox.qIn && !ox.beta then
                 { s with iX := .X, fx := true } else s
      let s := if !s.fx && ox.qIn.isX then
                 let s := { s with iX := .E, fx := true }
                 if !s.fy && topInternal oy && oy.qIn.isS then { s with iY := .X, fy := true } else s
               else s
      let s := if qc2Success && !s.fy then { s with iY := .E, fy := true } else s
      let s := if qc3 && !s.fx then { s with iX := .E, fx := true } else s
      let s := if !s.fx && ox.qIn.isP then
                 if qTerminal then
                   if !inT ox.qIn then { s with iX := .S (inV c ox.qIn) false, fx := true }
                   else if !ox.beta then { s with iX := .E, fx := true }
                   else s
                 else if topInternal oy && oy.qIn.isE && oy.qCarry.isOff && !s.fy then
                   { iX := .E, iY := .P (inV c ox.qIn) (inT ox.qIn), fx := true, fy := true }
                 else if oy.qIn.isS && oy.qCarry.isOff then
                   { s with iX := .S (inV c ox.qIn) (inT ox.qIn), fx := true }
                 else s
               else s
      let acc := !s.fy && qo1 && oy.qIn.isE && oy.qCarry.isOff
      let s := if acc then { s with iY := .P (outV c ox.qOut) (outT ox.qOut), fy := true } else s
      (s, acc)
  let qInX := qi.1.iX
  let qInY := qi.1.iY
  let acceptQO := qi.2
  -- QO.  (qOutX, qOutY)
  let qo : OutTok c.topA × OutTok c.topA :=
    if rootX || rootY then (.E, .E)
    else if qo1 then
      (if acceptQO then ((if outT ox.qOut then .U else .E), oy.qOut) else (ox.qOut, oy.qOut))
    else if ox.qOut.isD && !oy.beta && oy.qOut.isE then
      ((if outT ox.qOut then .U else .E), .D (outV c ox.qOut) (outT ox.qOut))
    else if ox.qOut.isU then (.D ox.d ox.beta, oy.qOut)
    else if ox.beta && ox.qOut.isE && !rootX then (.U, oy.qOut)
    else (ox.qOut, oy.qOut)
  let qOutX := qo.1
  let qOutY := qo.2
  -- Emission-first DIRTY: old dirty reports before any new digit change.
  let dx : Bool × Bool := if ox.topDirty then (false, true) else (dX != ox.d, topRejectCarry)
  let dirtyX := dx.1
  let topRejectX := dx.2
  let dy : Bool × Bool := if oy.topDirty then (false, true) else (dY != oy.d, topRejectX)
  let dirtyY := dy.1
  let topReject := dy.2
  { x := { wBase := wBaseX, wOut := wOutX, wIn := wInX, wCarry := wCarryX, qOut := qOutX,
           qIn := qInX, qCarry := qCarryX, d := dX, topDirty := dirtyX }
    y := { wBase := wBaseY, wOut := wOutY, wIn := wInY, wCarry := wCarryY, qOut := qOutY,
           qIn := qInY, qCarry := qCarryY, d := dY, topDirty := dirtyY }
    topReject := topReject }

/-- `liveTopStep(state,x,y,cfg,resolvedBeta)` (`composed-full.mjs:692-694`): array adapter. -/
def liveTopStep (c : Compiled) (ox oy : Agent c) (betaX : Bool := ox.beta)
    (betaY : Bool := oy.beta) : TopResult c :=
  liveTopPair c ox oy betaX betaY

/-! ## `leasePair`, `certificateStep` -/

/-- `leasePair(leaseX,leaseY,cfg,hardAccept,softAccept,done)` (`composed-full.mjs:699-705`).
Values: `siLeaseMax`, `0`, `max(lease-1,0)` or unchanged, all `≤ siLeaseMax`. -/
def leasePair (c : Compiled) (leaseX leaseY : Fin (c.siLeaseMax + 1))
    (hardAccept softAccept done : Bool) : Fin (c.siLeaseMax + 1) × Fin (c.siLeaseMax + 1) :=
  let nextX := leaseX
  let nextY := leaseY
  have hx := leaseX.isLt
  if hardAccept then (⟨c.siLeaseMax, by omega⟩, nextY)
  else if done then (nextX, ⟨0, by omega⟩)
  else if softAccept then (⟨max (nextX.val - 1) 0, by omega⟩, nextY)
  else (nextX, nextY)

/-- The `event` record of `certificateStep` (`composed-full.mjs:736`). -/
structure CertEvent where
  d1Reject : Bool
  topReject : Bool
  duX : Bool
  duY : Bool
  ddX : Bool
  ddY : Bool
  deriving DecidableEq, Repr

/-- The `rows` record of `certificateStep` (`composed-full.mjs:737`). -/
structure CertRows where
  serializer : String
  si : String
  raw : String
  deriving DecidableEq, Repr

/-- Full result `{x,y,post,event,rows}` of `certificateStep`. -/
structure CertResult (c : Compiled) where
  x : Agent c
  y : Agent c
  post : PostE
  event : CertEvent
  rows : CertRows

/-- `certificateStep(state,x,y,cfg)` with `post` and `rows` (`composed-full.mjs:711-739`).
Order: E, serializer, SI, LIVE-TOP (with the SI-resolved betas), raw D1, lease. -/
def certificateStepFull (c : Compiled) (x y : Agent c) : CertResult c :=
  let post := postEInfo x y
  let ser := serializerStep c x y post
  let si := siStep c x y post ser.hard
  let top := liveTopStep c x y si.betaX si.betaY
  let raw := rawD1Step c x y post
  let lease := leasePair c x.siLease y.siLease ser.hard.hardAccept ser.hard.softAccept si.done
  let nx : Agent c :=
    top.x.applyTo
      { x with ser := ser.x, siLease := lease.1, si := si.x, u := si.uX, beta := si.betaX,
               rawKick := raw.kickX, rawTok := raw.tokX }
  let ny : Agent c :=
    top.y.applyTo
      { y with ser := ser.y, siLease := lease.2, si := si.y, u := si.uY, beta := si.betaY,
               rawKick := raw.kickY, rawTok := raw.tokY }
  let duX := si.uX != x.u || si.betaX != x.beta
  let duY := si.uY != y.u || si.betaY != y.beta
  let ddX := top.x.d != x.d
  let ddY := top.y.d != y.d
  { x := nx, y := ny, post := post
    event := { d1Reject := raw.reject, topReject := top.topReject, duX := duX, duY := duY,
               ddX := ddX, ddY := ddY }
    rows := { serializer := ser.row, si := si.row, raw := raw.row } }

/-- `certificateStep(state,x,y,cfg)` (`composed-full.mjs:711-739`): the two updated agents
(fields `ser, siLease, si, u, beta, rawKick, rawTok` and the LIVE-TOP fields replaced, all
others unchanged) and the DCC event. -/
def certificateStep (c : Compiled) (x y : Agent c) : Agent c × Agent c × CertEvent :=
  let r := certificateStepFull c x y
  (r.x, r.y, r.event)

end L3
