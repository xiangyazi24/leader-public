import Leader.L3.CertRows

/-!
# L3 base step

Literal transcription of the base owner of
`research/method-review/l3-machine/composed-gpt.mjs`: the helpers `packNext` ... `tokenStep`
(lines 85-302) and the function `step` (lines 334-397), as `composed-full.mjs` `pairFull`
(lines 744-757) calls it: on the two-record carrier `[x, y]` (initiator `x`, responder `y`), with
the SMALL selection fixed by the compile-time pin `c.useSmall` (never derived from `n`;
`composed-gpt.mjs:318-321`, `composed-full.mjs:744-752`), threshold `c.K`, carrier capacity
`kStar`, lease cap `c.bankLeaseCap = 13 (b+2)`, theta `c.theta j`, and the DCC event `ev` supplied
as a parameter (in `pairFull` it comes from the certificate step).

The native owner `literalEPair` (`composed-gpt.mjs:53-69`) is `certLiteralEPair` of `CertRows.lean`
(checked literal against the JS); `CertNative` and `CertEvent` are reused from there.

Conventions.  JS bits `0/1` are `Bool`; JS string tags are the enums of `Alphabet.lean`
(`'CR'+String(x)` is `BTok.CR1` if `x` else `BTok.CR0`; `startsWith('CR')` is `CR0 ∨ CR1`).  JS
object mutation is rendered by `let`/`let mut` shadowing in the same order; JS early returns are
`return` inside `Id.run do`.  Where a JS value could leave a `Fin` range, a fallback branch is used
and stated in the docstring (production never reaches any of them).
-/

namespace L3

set_option autoImplicit false

/-! ## PACK -/

/-- `packNext(a,c,b)` (`composed-gpt.mjs:85-90`): the responder's new PACK role from the initiator's
pack `a`, the responder's pack `c` and the width `b`. -/
def packNext (a c b : Nat) : Nat :=
  if a < b then a + 1
  else if a = b then (if c = 0 then 0 else b + 1)
  else 0

/-! ## BANK -/

/-- The record `{role,mode,bit,tok,lease,grant}` built by `bankCell` (`composed-gpt.mjs:91-93`). -/
structure BankCell where
  role : Nat
  mode : Mode
  bit : Bool
  tok : BTok
  lease : Nat
  grant : Bool
  deriving DecidableEq, Repr

/-- `bankCell(a,role)` (`composed-gpt.mjs:91-93`). -/
def bankCell {c : Compiled} (a : Agent c) (role : Nat) : BankCell :=
  { role := role, mode := a.mode, bit := a.bit, tok := a.tok, lease := a.lease.val,
    grant := a.grant }

/-- `copyBank(dst,src)` (`composed-gpt.mjs:94-97`): copies `mode, bit, tok, lease` of `src` into
`dst`.  The lease is a `Fin (bankLeaseCap+1)`; the fallback `0` is reached only if `src.lease`
exceeds the cap.  `bankPair` produces leases that are input leases (`≤ cap`), `L = 13 (b+2) = cap`,
or `lease - 1`, hence always `≤ cap`. -/
def copyBank {c : Compiled} (dst : Agent c) (src : BankCell) : Agent c :=
  { dst with
    mode := src.mode
    bit := src.bit
    tok := src.tok
    lease := if h : src.lease < c.bankLeaseCap + 1 then ⟨src.lease, h⟩ else ⟨0, by omega⟩ }

/-- `WAIT` (`composed-gpt.mjs:45`). -/
def isWaitMode (m : Mode) : Bool :=
  match m with
  | .RWAIT => true
  | .IWAIT => true
  | .CWAIT => true
  | _ => false

/-- `RET` (`composed-gpt.mjs:46`). -/
def isRetTok (t : BTok) : Bool :=
  match t with
  | .RL => true
  | .AL => true
  | .CL0 => true
  | .CL1 => true
  | _ => false

/-- `bankPair(x0,y0,postYRole,b,theta)` (`composed-gpt.mjs:98-178`).  `L = 13 (b+2)` is computed
inside, as in the JS (it equals `c.bankLeaseCap`).  `theta j` is `c.theta j`; the JS reads
`theta[0]` and `theta[y.role-1]` with `1 ≤ y.role - 1 < b`, in range.  The local closure `wait`
is the `let wait` below; every early `return` of the JS is a `return` here. -/
def bankPair (x0 y0 : BankCell) (postYRole b : Nat) (theta : Nat → Bool) : BankCell × BankCell :=
  Id.run do
    let L := 13 * (b + 2)
    let mut x := x0
    let mut y := y0
    let changed := postYRole != y.role
    y := { y with role := postYRole }
    if changed then
      y := { y with mode := .RESET, bit := false, tok := .E, lease := 0 }
    if x.role != 0 then
      x := { x with mode := .RESET, lease := 0 }
    if y.role != 0 then
      y := { y with mode := .RESET, lease := 0 }
    if !(1 ≤ x.role && x.role ≤ b) then
      x := { x with tok := .E }
    if !(1 ≤ y.role && y.role ≤ b) then
      y := { y with tok := .E }
    let wait : BankCell → BankCell := fun z =>
      if isWaitMode z.mode then
        (if z.lease > 1 then { z with lease := z.lease - 1 }
         else { z with mode := .RESET, lease := 0 })
      else z
    if y.role == 0 && !changed then
      if y.grant then y := { y with mode := .RESET, lease := 0 }
      else if y.mode == .ARMED then y := { y with mode := .RESET, lease := 0 }
      else y := wait y
    if x.role == 0 then
      if x.grant then
        x := { x with mode := .RESET, lease := 0 }
        if !changed && y.role == 1 then y := { y with tok := .E }
        return (x, y)
      if changed then
        if x.mode == .ARMED || x.mode == .CSTART then x := { x with mode := .RESET, lease := 0 }
        else x := wait x
        return (x, y)
      if y.role != 1 then return (wait x, y)
      if x.mode == .RESET then
        return ({ x with mode := .RWAIT, lease := L }, { y with bit := false, tok := .RR })
      if isRetTok y.tok then
        let t := y.tok
        y := { y with tok := .E }
        if t == .RL && x.mode == .RWAIT then return ({ x with mode := .ARMED, lease := 0 }, y)
        if t == .AL && x.mode == .IWAIT then return ({ x with mode := .CSTART, lease := 0 }, y)
        if (t == .CL0 || t == .CL1) && x.mode == .CWAIT then
          return ({ x with mode := (if t == .CL1 then Mode.RESET else Mode.ARMED), lease := 0 }, y)
        return (wait x, y)
      if x.mode == .ARMED then
        if y.tok != .E then return ({ x with mode := .RESET, lease := 0 }, { y with tok := .E })
        if y.bit == false then return ({ x with mode := .CSTART, lease := 0 }, { y with bit := true })
        return ({ x with mode := .IWAIT, lease := L }, { y with bit := false, tok := .IR })
      if x.mode == .CSTART then
        if y.tok != .E then return ({ x with mode := .RESET, lease := 0 }, { y with tok := .E })
        return ({ x with mode := .CWAIT, lease := L },
                { y with tok := (if y.bit == theta 0 then BTok.CR1 else BTok.CR0) })
      if b == 1 then
        if y.tok == .RR then y := { y with tok := .RL }
        else if y.tok == .CR0 || y.tok == .CR1 then
          y := { y with tok := (if y.tok == .CR1 then BTok.CL1 else BTok.CL0) }
        else if y.tok == .IR then y := { y with tok := .E }
      return (wait x, y)
    if changed then
      if 1 ≤ x.role && x.role < b && (x.tok == .IR || x.tok == .CR0 || x.tok == .CR1) then
        x := { x with tok := .E }
      return (x, y)
    if x.role == b && x.tok == .IR then x := { x with tok := .E }
    if y.role == b && y.tok == .IR then y := { y with tok := .E }
    if 1 ≤ x.role && x.role < b && y.role == x.role + 1 then
      if x.tok == .RR then
        return ({ x with tok := .E }, { y with bit := false, tok := .RR })
      if y.role == b && y.tok == .RR then
        return ({ x with bit := false, tok := .RL }, { y with tok := .E })
      if y.tok == .RL then
        return ({ x with bit := false, tok := .RL }, { y with tok := .E })
      if x.tok != .E && y.tok != .E then
        return ({ x with tok := .E }, { y with tok := .E })
      if y.role == b && (y.tok == .CR0 || y.tok == .CR1) then
        return ({ x with tok := (if y.tok == .CR1 then BTok.CL1 else BTok.CL0) }, { y with tok := .E })
      if y.tok == .AL || y.tok == .CL0 || y.tok == .CL1 then
        return ({ x with tok := y.tok }, { y with tok := .E })
      if x.tok == .IR then
        return ({ x with tok := .E },
                { y with bit := !y.bit, tok := (if y.bit then BTok.IR else BTok.AL) })
      if x.tok == .CR0 || x.tok == .CR1 then
        let eq := (x.tok == .CR1) && (y.bit == theta (y.role - 1))
        return ({ x with tok := .E }, { y with tok := (if eq then BTok.CR1 else BTok.CR0) })
    return (x, y)

/-- `bankSuccess(oldx,oldy,postYRole,b)` (`composed-gpt.mjs:179-183`); `b` is unused in the JS. -/
def bankSuccess (oldx oldy : BankCell) (postYRole : Nat) (_b : Nat) : Bool :=
  oldx.role == 0 && !oldx.grant && oldx.mode == .CWAIT &&
    oldy.role == postYRole && postYRole == 1 && oldy.tok == .CL1

/-! ## SMALL -/

/-- `parseRun(s)` (`composed-gpt.mjs:184-188`): `some j` for `RUN j`, `none` for `OFF`/`SPENT`. -/
def parseRun (s : Small) : Option Nat :=
  match s with
  | .RUN j => some j.val
  | _ => none

/-- `'RUN'+String(v)` as a `Small`.  Fallback (reached only if `v ≥ kStar`): saturates at
`RUN (kStar-1)`.  `smallPair` builds `RUN (j+1)` only under `j < K-1`, so `v ≤ K-1`; production
SMALL band has `K = 2q + kappa ≤ 175 ≤ 199 = kStar`, hence `v < kStar`. -/
def smallRun (v : Nat) : Small :=
  if h : v < kStar then Small.RUN ⟨v, h⟩ else Small.RUN ⟨kStar - 1, by decide⟩

/-- `'RUN0'`. -/
def smallRunZero : Small := Small.RUN ⟨0, by decide⟩

/-- `smallPair(ax,ay,k,Kstar)` (`composed-gpt.mjs:189-205`), returning `[sx, sy, successX]`.
`Kstar` is unused in the JS body.  Comparisons `j < k-1`, `j === k-1` are done over `Int` as in JS
(`j + 1 < k`, `j + 1 = k`). -/
def smallPair {c : Compiled} (ax ay : Agent c) (k : Nat) : Small × Small × Bool :=
  Id.run do
    let mut sx := ax.small
    let mut sy := ay.small
    let mut successX := false
    let mut hx := false
    let mut hy := false
    let jx := parseRun sx
    let jy := parseRun sy
    match jx with
    | some j =>
      if j ≥ k then
        sx := smallRunZero
        hx := true
    | none => pure ()
    match jy with
    | some j =>
      if j ≥ k then
        sy := smallRunZero
        hy := true
    | none => pure ()
    if !hy then
      sy := smallRunZero
      hy := true
    if !hx then
      match parseRun sx with
      | some j =>
        if j + 1 < k then sx := smallRun (j + 1)
        else if j + 1 == k then
          sx := Small.SPENT
          successX := true
      | none => pure ()
    return (sx, sy, successX)

/-! ## C owner -/

/-- `outBullet(a)` (`composed-gpt.mjs:206`), on the native part of `a`. -/
def outBullet (a : CertNative) : Nat :=
  if a.l && a.sg then 2 else a.b.val

/-- C-owner selection tags (`composed-gpt.mjs:207-218`). -/
inductive CSel
  | SAN | K2 | PROM | DP2 | DP1 | KEEP | EMPTY
  deriving DecidableEq, Repr

/-- `cSelect(old,postE,enter)` (`composed-gpt.mjs:207-218`); priority order kept. -/
def cSelect {c : Compiled} (old : Agent c) (postE : CertNative) (enter : Bool) : CSel :=
  let k2 := old.C && old.alpha && postE.b.val == 0 && postE.sg
  let safe := !postE.l && postE.b.val == 0
  if old.C && postE.l then CSel.SAN
  else if k2 then CSel.K2
  else if old.C && old.m && safe then CSel.PROM
  else if old.C && enter && !postE.sg && old.alpha then CSel.DP2
  else if old.C && enter && !postE.sg && !old.alpha then CSel.DP1
  else if old.C then CSel.KEEP
  else CSel.EMPTY

/-- The private record `{C,alpha,m}` returned by `cPrivate`. -/
structure CPriv where
  C : Bool
  alpha : Bool
  m : Bool
  deriving DecidableEq, Repr

/-- `cPrivate(old,sel)` (`composed-gpt.mjs:219-226`). -/
def cPrivate {c : Compiled} (old : Agent c) (sel : CSel) : CPriv :=
  match sel with
  | .SAN => { C := false, alpha := false, m := false }
  | .K2 => { C := false, alpha := false, m := false }
  | .PROM => { C := false, alpha := false, m := false }
  | .DP2 => { C := true, alpha := true, m := true }
  | .DP1 => { C := true, alpha := true, m := old.m }
  | .KEEP => { C := old.C, alpha := old.alpha, m := old.m }
  | .EMPTY => { C := false, alpha := false, m := false }

/-! ## DCC -/

/-- Result `{request, x:{EU,ED}, y:{EU,ED}, row}` of `dccStep`. -/
structure DccOut where
  request : Bool
  xEU : Bool
  xED : Bool
  yEU : Bool
  yED : Bool
  row : String
  deriving DecidableEq, Repr

/-- `dccStep(oldx,oldy,ev)` (`composed-gpt.mjs:228-245`). -/
def dccStep {c : Compiled} (oldx oldy : Agent c) (ev : CertEvent) : DccOut :=
  let oldDebt := oldx.EU || oldx.ED || oldy.EU || oldy.ED
  let raw := ev.d1Reject || ev.topReject
  let newChange := ev.duX || ev.ddX || ev.duY || ev.ddY
  if oldDebt || raw then
    { request := true, xEU := ev.duX, xED := ev.ddX, yEU := ev.duY, yED := ev.ddY, row := "D0" }
  else if newChange then
    { request := true, xEU := false, xED := false, yEU := false, yED := false, row := "D1" }
  else
    { request := false, xEU := false, xED := false, yEU := false, yED := false, row := "D2" }

/-! ## FIRE -/

/-- FIRE kind tags `'F0' | 'F1' | 'F2'` (`composed-gpt.mjs:246-254`). -/
inductive FireKind
  | F0 | F1 | F2
  deriving DecidableEq, Repr

/-- FIRE site tags `'x' | 'y'`. -/
inductive FireSite
  | siteX | siteY
  deriving DecidableEq, Repr

/-- The record `{kind,site,reqX,grantX,reqY,grantY}` of `fireSelect`; fields absent in the JS
object are `false` (JS `undefined`, read as falsy by `tokenStep`). -/
structure FireSel where
  kind : FireKind
  site : FireSite
  reqX : Bool := false
  reqY : Bool := false
  grantX : Bool := false
  grantY : Bool := false
  deriving DecidableEq, Repr

/-- `fireSelect(oldx,oldy,eX,eY)` (`composed-gpt.mjs:246-254`); `null` is `none`. -/
def fireSelect {c : Compiled} (oldx oldy : Agent c) (eX eY : CertNative) : Option FireSel :=
  let eligX := !eX.l && eX.b.val == 0
  let eligY := !eY.l && eY.b.val == 0
  if oldx.req && oldx.grant && eligX then
    some { kind := .F0, site := .siteX, reqX := true, grantX := true }
  else if oldy.req && oldy.grant && eligY then
    some { kind := .F1, site := .siteY, reqY := true, grantY := true }
  else if oldx.req && oldy.grant && eligX then
    some { kind := .F2, site := .siteX, reqX := true, grantY := true }
  else none

/-! ## Tokens -/

/-- The pair `{req,grant}` returned per site by `tokenStep`. -/
structure TokPair where
  req : Bool
  grant : Bool
  deriving DecidableEq, Repr

/-- The meta record `{prodReqY,prodGrantX,holdX,holdY}` of `tokenStep`. -/
structure TokMeta where
  prodReqY : Bool
  prodGrantX : Bool
  holdX : Bool
  holdY : Bool
  deriving DecidableEq, Repr

/-- `fire&&fire.site===s` of `tokenStep`. -/
def fireAtSite (fire : Option FireSel) (s : FireSite) : Bool :=
  match fire with
  | some f => f.site == s
  | none => false

/-- `tokenStep(oldx,oldy,finalX,finalY,fire,dccRequest,bankSuccessX)`
(`composed-gpt.mjs:255-302`), segments T0 FIRE, T1 sinks, T2 producers, HOLD, REQ, GRANT, final
sinks, in JS order. -/
def tokenStep {c : Compiled} (oldx oldy : Agent c) (finalX finalY : CertNative)
    (fire : Option FireSel) (dccRequest bankSuccessX : Bool) : TokPair × TokPair × TokMeta :=
  Id.run do
    let mut rx := oldx.req
    let mut ry := oldy.req
    let mut gx := oldx.grant
    let mut gy := oldy.grant
    let mut reqConsumedX := false
    let mut reqConsumedY := false
    let mut grantConsumedX := false
    let mut grantConsumedY := false
    -- T0 FIRE consumption.
    match fire with
    | some f =>
      if f.reqX then
        rx := false
        reqConsumedX := true
      if f.reqY then
        ry := false
        reqConsumedY := true
      if f.grantX then
        gx := false
        grantConsumedX := true
      if f.grantY then
        gy := false
        grantConsumedY := true
    | none => pure ()
    -- T1 final leader sinks, including moving tokens trying to enter a leader.
    if finalX.l then
      rx := false
      gx := false
      reqConsumedX := true
      grantConsumedX := true
    if finalY.l then
      ry := false
      gy := false
      reqConsumedY := true
      grantConsumedY := true
    if finalY.l && oldx.req then
      rx := false
      reqConsumedX := true
    if finalX.l && oldy.grant then
      gy := false
      grantConsumedY := true
    -- T2 producers.
    let mut prodReqY := false
    let mut prodGrantX := false
    if dccRequest && !finalY.l && !reqConsumedY then
      ry := true
      prodReqY := true
    if bankSuccessX && !finalX.l && !grantConsumedX then
      gx := true
      prodGrantX := true
    -- HOLD for old co-located pairs not consumed by FIRE/sink.
    let holdX := oldx.req && oldx.grant && !(fireAtSite fire .siteX) &&
                 !reqConsumedX && !grantConsumedX
    let holdY := oldy.req && oldy.grant && !(fireAtSite fire .siteY) &&
                 !reqConsumedY && !grantConsumedY
    if holdX then
      rx := true
      gx := true
    if holdY then
      ry := true
      gy := true
    -- REQ clockwise x -> y.
    if oldx.req && !reqConsumedX && !holdX && !finalY.l then
      rx := false
      if !reqConsumedY then ry := true
    -- GRANT counterclockwise y -> x.
    if oldy.grant && !grantConsumedY && !holdY && !finalX.l then
      gy := false
      if !grantConsumedX then gx := true
    if finalX.l then
      rx := false
      gx := false
    if finalY.l then
      ry := false
      gy := false
    return ({ req := rx, grant := gx }, { req := ry, grant := gy },
            { prodReqY := prodReqY, prodGrantX := prodGrantX, holdX := holdX, holdY := holdY })

/-! ## The base step -/

/-- `nativeMk(1,0,1,0)` (`composed-gpt.mjs:52`, used at line 376-377 of `step`): the fired leader. -/
def firedNative : CertNative := { l := true, b := 0, sh := true, sg := false }

/-- PACK value as a `Fin (b+2)`.  Fallback `0` is reached only if `v > b+1`; `packNext` returns
`a+1 ≤ b` (for `a < b`), `0`, or `b+1`, so `v ≤ b+1` always. -/
def packFin (c : Compiled) (v : Nat) : Fin (c.b + 2) :=
  if h : v < c.b + 2 then ⟨v, h⟩ else ⟨0, by omega⟩

/-- Write the native fields `{l,b,sh,sg}` (`Object.assign(nx,fX)`, `composed-gpt.mjs:376-378`). -/
def Agent.setNative {c : Compiled} (a : Agent c) (n : CertNative) : Agent c :=
  { a with l := n.l, b := n.b, sh := n.sh, sg := n.sg }

/-- Write the private record (`Object.assign(nx,{C,alpha,m})`, `composed-gpt.mjs:381-387`). -/
def Agent.setCPriv {c : Compiled} (a : Agent c) (p : CPriv) : Agent c :=
  { a with C := p.C, alpha := p.alpha, m := p.m }

/-- `step(state,edge,cfg,hooks)` (`composed-gpt.mjs:334-397`) on the carrier `[x, y]`, with
`smallActive = c.useSmall`, `cfg.K = c.K`, `cfg.b = c.b`, `cfg.theta = c.theta`, and the DCC hook
returning `ev`.  Returns the new initiator and responder; it writes exactly `l b sh sg`, `pack`,
`mode bit tok lease` (spatial branch only), `small`, `req grant`, `C alpha m`, `EU ED` and
leaves all other fields unchanged (the `meta` record is not returned). -/
def baseStep (c : Compiled) (ev : CertEvent) (x y : Agent c) : Agent c × Agent c :=
  let oldx := x
  let oldy := y
  let nx := oldx
  let ny := oldy
  -- PACK.
  let postYRole := packNext oldx.pack.val oldy.pack.val c.b
  let ny := { ny with pack := packFin c postYRole }
  -- BANK / SMALL.
  let (nx, ny, bankSuccessX) : Agent c × Agent c × Bool :=
    if c.useSmall then
      let r := smallPair oldx oldy c.K
      -- Spatial BANK is disabled in the small branch.
      ({ nx with small := r.1 }, { ny with small := r.2.1 }, r.2.2)
    else
      let nx := if oldx.small ≠ Small.OFF then { nx with small := Small.OFF } else nx
      let ny := if oldy.small ≠ Small.OFF then { ny with small := Small.OFF } else ny
      let succ := bankSuccess (bankCell oldx oldx.pack.val) (bankCell oldy oldy.pack.val)
        postYRole c.b
      let r := bankPair (bankCell oldx oldx.pack.val) (bankCell oldy oldy.pack.val)
        postYRole c.b c.theta
      (copyBank nx r.1, copyBank ny r.2, succ)
  -- literal E.
  let (eX, eY) := certLiteralEPair oldx.certNative oldy.certNative
  -- DCC before token production.
  let dcc := dccStep oldx oldy ev
  let nx := { nx with EU := dcc.xEU, ED := dcc.xED }
  let ny := { ny with EU := dcc.yEU, ED := dcc.yED }
  -- C-owner selection from OLD / ENTER / post-E.
  let enterX := false
  let enterY := !oldy.l && decide (outBullet oldx.certNative > 0)
  let selX := cSelect oldx eX enterX
  let selY := cSelect oldy eY enterY
  -- FIRE from OLD tokens and post-E native.
  let fire := fireSelect oldx oldy eX eY
  let fX := if fireAtSite fire .siteX then firedNative else eX
  let fY := if fireAtSite fire .siteY then firedNative else eY
  let nx := nx.setNative fX
  let ny := ny.setNative fY
  -- PROM gate private C0/C1/C2.
  let zeroC : CPriv := { C := false, alpha := false, m := false }
  let nx :=
    if fireAtSite fire .siteX then nx.setCPriv zeroC
    else if selX == CSel.PROM then nx.setCPriv zeroC
    else nx.setCPriv (cPrivate oldx selX)
  let ny :=
    if fireAtSite fire .siteY then ny.setCPriv zeroC
    else if selY == CSel.PROM then ny.setCPriv zeroC
    else ny.setCPriv (cPrivate oldy selY)
  -- Token owner T0/T1/T2/HOLD/movement.
  let (tx, ty, _tmeta) := tokenStep oldx oldy fX fY fire dcc.request bankSuccessX
  let nx := { nx with req := tx.req, grant := tx.grant }
  let ny := { ny with req := ty.req, grant := ty.grant }
  (nx, ny)

end L3
