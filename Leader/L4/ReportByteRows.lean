import Leader.L4.ReportDigitArithmetic
import Leader.L4.MISByteCodec

/-! Report work. One symbolic program serves either radius.
Off/cache publishers are outside this work patch. -/
namespace L4.ReportByteRows
open AllSizeProtocol

structure Params where
  beta : Nat
  digits : Nat
  radius : Nat
  streak : Nat

def Params.w (p : Params) : Nat := reportWidth p.beta p.digits p.streak

def d (p : Params) := ell p.beta
def o (p : Params) := ell (5+4*p.digits)
def payW (p : Params) := max 7 (2+2*d p)
def tokenW (p : Params) := 9+o p+payW p
def tail (p : Params) := ell p.streak+3
def sourceBase (p : Params) := tail p+3*tokenW p
def sourceW (p : Params) := 21+o p+2*d p
def sealBase (p : Params) := sourceBase p+sourceW p
def bankW (p : Params) := 3+2*d p
def grantBase (p : Params) := sealBase p+5+2*bankW p
def workW (p : Params) := grantBase p+4

theorem layout_size (p : Params) :
    p.w=workW p+1+ell (max 3 p.digits+1) := by
  unfold Params.w reportWidth workW grantBase bankW sealBase sourceW sourceBase tail tokenW payW o d
  omega

private def get {w : Nat} (x : BitVec w) (k b : Nat) : Nat := (x.extractLsb' k b).toNat
private def bit (x k : Nat) : Bool := (x >>> k)%2==1
private def field (p : Params) (k b v : Nat) : Patch (workW p) :=
  ⟨(BitVec.allOnes b).setWidth (workW p) <<< k, (BitVec.ofNat b v).setWidth (workW p) <<< k⟩

private def geomOff (p : Params) (h : Bool) (x : BitVec p.w) : Nat :=
  if h then 0 else min (max 3 p.digits) (get x (workW p+1) (ell (max 3 p.digits+1)))

def Z (p : Params) (x : BitVec p.w) : Bool := x.getLsbD (ell p.streak+2)

def admitOp (p : Params) := p.digits+1
def acqOp (p : Params) := p.digits+2
def cmpOp (p : Params) := p.digits+3
def readOp (p : Params) := 2*p.digits+3
def writeOp (p : Params) := 3*p.digits+3
def sealOp (p : Params) := 4*p.digits+3
def commitOp (p : Params) := 4*p.digits+4
private def legalDesc (x : Nat) : Bool := bit x 3 != bit x 2
private def digitPair (p : Params) (z : Nat) : Bool :=
  z%2^d p<p.beta && (z/2^d p)%2^d p<p.beta

abbrev Tok := MISByteCodec.Token
private abbrev F := MISByteCodec.faultToken
private abbrev E := MISByteCodec.E
private abbrev T := MISByteCodec.T

/-- Decode a padded message; invalid live digits fault whereas padding of
smaller alternatives and E/T is ignored. -/
def decode (p : Params) (gate : Bool) (raw : BitVec (tokenW p)) : Tok :=
  let b := payW p
  let tag := get raw (7+o p+b) 2
  let ft := raw.getLsbD (6+o p+b)
  let op := get raw (b+6) (o p)
  let race := get raw (b+3) 3
  let outcome := get raw (b+1) 2
  let q := get raw 0 b
  let atGate := gate && op==admitOp p
  if tag==0 then E else if tag==1 then T
  else if ft || commitOp p<op then F tag
  else if tag==2 then
    if outcome != 0 || (if atGate then race<1 || 5<race else race != 0) then F tag
    else
      let k := if op==acqOp p then 7 else if op==admitOp p then 1 else
        if cmpOp p≤op && op<sealOp p then 2+2*d p else if sealOp p≤op then 4 else 0
      let q := q%2^k
      if (cmpOp p≤op && op<sealOp p && !digitPair p q) ||
         (writeOp p≤op && op<sealOp p && bit q (2*d p)==bit q (2*d p+1)) ||
         (sealOp p≤op && !legalDesc q) then F tag
      else ⟨tag,op,q,race,0,false,op==commitOp p && raw.getLsbD b⟩
  else if race != 0 || (outcome != 0 && !(op==acqOp p && outcome==1)) then F tag
  else
    let k := if op==acqOp p then 6 else if op==admitOp p then 1 else
      if cmpOp p≤op && op<writeOp p then 2*d p else 0
    let q := if outcome==1 then 0 else q%2^k
    if cmpOp p≤op && op<writeOp p && !digitPair p q then F tag
    else ⟨tag,op,q,0,outcome,false,false⟩

private def encode (p : Params) (t : Tok) : Nat :=
  let b := payW p
  t.tag*2^(7+o p+b)+t.fault.toNat*2^(6+o p+b)+
    t.opcode*2^(b+6)+t.race*2^(b+3)+t.outcome*2^(b+1)+t.applied.toNat*2^b+t.payload

private def kOffset (p : Params) (j : Fin 3) : Nat := tail p+(2-j.val)*tokenW p
private def writeK (p : Params) (j : Fin 3) (t : Tok) := field p (kOffset p j) (tokenW p) (encode p t)
private def gate (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3) :=
  j.val==1 && geomOff p h x==2
private def oldK (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3) :=
  decode p (gate p h x j) (x.extractLsb' (kOffset p j) (tokenW p))

private def pc (p : Params) := sourceBase p+19+2*d p
private def ctrl (p : Params) (phase op : Nat) :=
  field p (pc p) (o p+2) (phase*2^o p+op)
private def reset (p : Params) := field p (sourceBase p) (sourceW p) (2^(sourceW p-2))
private def sf (p : Params) (k b v : Nat) := field p (sourceBase p+k) b v
private def rf (p : Params) (x : BitVec p.w) (k b : Nat) := get x (sourceBase p+k) b
private def cmp (a b prior : Nat) : Nat := if a<b then 1 else if b<a then 2 else prior

/-- Source-side control with old captures, comparisons and digit-file
assignments. Indexed opcodes have separate contiguous families. -/
def source (p : Params) (raw : BitVec p.w) (t : Tok) :
    Patch (workW p) × Option Tok :=
  let n := d p
  let phase := get raw (pc p+o p) 2
  let op := get raw (pc p) (o p)
  let capIx := rf p raw (16+2*n) 3
  let capHd := rf p raw (13+2*n) 3
  let outCmp := rf p raw (5+2*n) 4
  let inpCmp := rf p raw (9+2*n) 4
  let carry := rf p raw (3+2*n) 2
  let sendDigits := rf p raw 3 (2*n)
  let go := fun i => (ctrl p 1 i,some E)
  let restart := (reset p,some E)
  if phase==0 || phase==3 || commitOp p<op then restart
  else if phase==1 then
    let body := if op==0 then reset p else .empty _
    let old := (capIx/2)%2
    let alt := 2*old+(1-old)
    let pairIx := 2*(capIx/4)+capIx%2
    let pld := if op==acqOp p then 64 else
      if cmpOp p≤op && op<writeOp p then pairIx*2^(2*n)
      else if writeOp p≤op && op<sealOp p then alt*2^(2*n)+sendDigits
      else if sealOp p≤op then 4*alt+2*(outCmp/4==1).toNat+(outCmp%4==1).toNat
      else 0
    if (writeOp p≤op && op<sealOp p && !digitPair p sendDigits) ||
       (sealOp p≤op && (outCmp/4==3 || outCmp%4==3)) then restart
    else (body.compose (field p (pc p+o p) 2 2),some {tag:=2,opcode:=op,payload:=pld})
  else if t.tag==1 || t.tag==2 then (.empty _,none)
  else if t.tag != 3 || t.opcode != op || t.fault || t.outcome==1 then restart
  else if op==0 then go 1
  else if op<admitOp p then go (op+1)
  else if op==admitOp p then if t.payload==1 then go (acqOp p) else restart
  else if op==acqOp p then
    (((ctrl p 1 (cmpOp p)).compose (sf p (13+2*n) 6 t.payload)).compose
      (sf p (9+2*n) 4 0),some E)
  else if op<writeOp p then
    let isCmp := op<readOp p
    let j := op-(if isCmp then cmpOp p else readOp p)
    let kd := (p.radius/p.beta^j)%p.beta
    let a := t.payload/2^n
    let b := t.payload%2^n
    if inpCmp/4==3 || inpCmp%4==3 ||
      (!isCmp && (outCmp/4==3 || outCmp%4==3)) then restart
    else if isCmp then
      let pair := 4*cmp a kd (inpCmp/4)+cmp b kd (inpCmp%4)
      let s := sf p (9+2*n) 4 pair
      if j+1<p.digits then ((ctrl p 1 (op+1)).compose s,some E)
      else ((((ctrl p 1 (readOp p)).compose s).compose (sf p (5+2*n) 4 0)).compose
              (sf p (3+2*n) 2 3),some E)
    else
      let compute := fun digit comparison c root =>
        if root then (0,c) else if comparison != 1 then (kd,c)
        else ((digit+c)%p.beta,(digit+c)/p.beta)
      let (a,ca) := compute a (inpCmp/4) (carry/2) (bit capHd 2)
      let (b,cb) := compute b (inpCmp%4) (carry%2) (bit capHd 0)
      let out := 4*cmp a kd (outCmp/4)+cmp b kd (outCmp%4)
      ((((ctrl p 1 (writeOp p+j)).compose (sf p 3 (2*n) (2^n*a+b))).compose
        (sf p (3+2*n) 2 (2*ca+cb))).compose (sf p (5+2*n) 4 out),some E)
  else if op<sealOp p then
    let j := op-writeOp p
    go (if j+1<p.digits then readOp p+j+1 else sealOp p)
  else if op==sealOp p then go (commitOp p)
  else restart

private def bankOffset (p : Params) (ix : Nat) := sealBase p+5+(1-ix)*bankW p
private def selected (p : Params) (x : BitVec p.w) := get x (grantBase p+3) 1
private def stored (p : Params) (x : BitVec p.w) (ix : Nat) := get x (bankOffset p ix) (bankW p)
private def aBit (p : Params) (x : BitVec p.w) (ix : Nat) := bit (stored p x ix) (2+2*d p)
private def bPair (p : Params) (x : BitVec p.w) (ix : Nat) :=
  (stored p x ix / 2^(2*d p))%4
private def readSeal (p : Params) (x : BitVec p.w) : Option Nat :=
  let y := get x (sealBase p) 5
  if 16≤y && legalDesc (y%16) then some (y%16) else none
private def writeSeal (p : Params) (x : Option Nat) :=
  field p (sealBase p) 5 (match x with | none=>0 | some v=>16+v)
private def gBit (p : Params) (x : BitVec p.w) (j : Fin 3) :=
  x.getLsbD (grantBase p+2-j.val)
private def canonical (p : Params) (x : BitVec p.w) (j : Fin 3) : Bool :=
  if gBit p x 1 then j==1 else gBit p x j
private def grants (p : Params) (g : Fin 3 → Bool) :=
  field p (grantBase p) 3 (4*(g 0).toNat+2*(g 1).toNat+(g 2).toNat)
private def writeBit (x j : Nat) (b : Bool) : Nat :=
  if bit x j then if b then x else x-2^j else if b then x+2^j else x

/-- A report completion reads the selected old Bminus/Bplus, never
either a new incoming-COMMIT threshold or a new selector. Counter/pulse
fields are explicit intents, with raw held streak except on completion. -/
def pulse (p : Params) (header : Bool) (side : Nat) (x : BitVec p.w) : Patch (workW p) :=
  let w := ell p.streak
  let r := get x w 2
  let k := get x 0 w
  let r := if r==3 then 0 else r
  let k := if k<p.streak then k else 0
  if !header then (field p w 2 0).compose (field p 0 w 0)
  else if r==0 then field p w 2 side
  else if r==side then .empty _
  else
    let paint := r==2 && k+1==p.streak
    let nr := if r==1 || paint then 0 else k+1
    let pad := (field p w 2 0).compose (field p 0 w nr)
    if paint then pad.compose (field p (w+2) 1 ((bPair p x (selected p x)==0).toNat))
    else pad

private def parked (p : Params) (t : Tok) (h : Bool) (x : BitVec p.w) (j : Fin 3) : Bool :=
  t.tag==2 && !t.fault && t.opcode==admitOp p && gate p h x j
private def ready (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3) (t : Tok) : Bool :=
  t.tag==2 && !(parked p t h x j && t.race<4)
private def advanceRace (t : Tok) (side : Nat) : Tok :=
  if t.race==1 then {t with race:=side} else {t with race:=t.race+2}

private def terminal (p : Params) (t : Tok) : Tok :=
  if t.fault || (t.opcode==commitOp p && !t.applied) then F 3
  else if t.opcode==acqOp p then
    if bit t.payload 6 then {tag:=3,opcode:=t.opcode,payload:=t.payload%64}
    else {tag:=3,opcode:=t.opcode,outcome:=1}
  else {tag:=3,opcode:=t.opcode,payload:=
    if t.opcode==admitOp p then t.payload else
    if cmpOp p≤t.opcode && t.opcode<writeOp p then t.payload%2^(2*d p) else 0}

private def arrival (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3) (t : Tok) : Tok :=
  if !t.fault && t.opcode==admitOp p && gate p h x j then {t with race:=1} else t

/-- Exact outgoing effect; incoming COMMIT alone writes the old right
bank's report and selector, using old grant, seal and Z. -/
def effect (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) (t : Tok) :
    Patch (workW p) × Patch (workW p) × Tok :=
  let nil := Patch.empty (workW p)
  let op := t.opcode
  let w := d p
  let s := geomOff p hu u
  if t.fault then (nil,nil,t)
  else if op==commitOp p && hv && j==0 && k==some 1 then
    let ix := (t.payload/4)%2
    if !t.applied && gBit p v 1 && selected p v==t.payload/8 &&
        readSeal p v==some t.payload then
      let patch := ((field p (grantBase p+3) 1 ix).compose (writeSeal p none)).compose
          (field p (bankOffset p ix+2*w) 3 (4*(Z p v).toNat+t.payload%4))
      (nil,patch,{t with applied:=true})
    else (nil,nil,F 2)
  else if parked p t hu u j then (nil,nil,{t with race:=0,payload:=t.race-4})
  else if hu && j==1 && op==0 then (writeSeal p none,nil,t)
  else if hu && op==acqOp p then
    let pl := if win then writeBit (writeBit t.payload (5-j.val) (selected p u==1))
        (2-j.val) (aBit p u (selected p u)) else writeBit t.payload 6 false
    (nil,nil,{t with payload:=pl})
  else if cmpOp p≤op && op<writeOp p && (j==0 || j==2) &&
       s==op-(if op<readOp p then cmpOp p else readOp p) then
    let side := j.val/2
    let ix := if side==0 then bit t.payload (2*w+1) else bit t.payload (2*w)
    let shift := if side==0 then w else 0
    let dg := min (p.beta-1) (get u (bankOffset p ix.toNat+shift) w)
    let old := (t.payload/2^shift)%2^w
    let pl := t.payload-old*2^shift+dg*2^shift
    (nil,nil,{t with payload:=pl})
  else if writeOp p≤op && op<sealOp p && j==1 && s==op-writeOp p then
    if hu && !(gBit p u 1 && selected p u==t.payload/2^(2*w+1)) then (nil,nil,F 2)
    else
      let ix := (t.payload/2^(2*w))%2
      (field p (bankOffset p ix) (2*w) (t.payload%2^(2*w)),nil,t)
  else if op==sealOp p && j==1 && hu then
    if gBit p u 1 && selected p u==t.payload/8 then (writeSeal p (some t.payload),nil,t)
    else (nil,nil,F 2)
  else (nil,nil,t)

private def links (h : Bool) : List (Fin 3 × Option (Fin 3)) :=
  if h then [(0,some 1),(1,some 2),(2,none)]
  else [(0,some 0),(1,some 1),(2,some 2)]

private def body (p : Params) (headers : Pair Bool) (old : Pair (BitVec p.w)) : Pair (Patch (workW p)) :=
  let hu:=headers.1
  let hv:=headers.2
  let u:=old.1
  let v:=old.2
  let fu := oldK p hu u
  let fv := oldK p hv v
  let action := fun (j : Fin 3) (op : Nat) =>
    let t := fu j
    hu && ready p hu u j t && !t.fault && t.opcode==op
  let rel := fun j => action j 0
  let ask := fun j => action j (acqOp p)
  let w := !canonical p u 0 && !canonical p u 1 && !canonical p u 2 && ask 1 && !rel 1
  let win := fun j : Fin 3 =>
    if j==1 then w
    else !w && !canonical p u 1 && ask j && !canonical p u j && !rel j
  let gg := fun j => (canonical p u j && !rel j) || win j
  let clear := ((reset p).compose (writeSeal p none)).compose (grants p fun _ => false)
  let a := (if hu then grants p gg else clear).compose (pulse p hu 2 u)
  let b := (if hv then
    if gBit p v 1 && (gBit p v 0 || gBit p v 2) then grants p (canonical p v) else .empty _
    else clear).compose (pulse p hv 1 v)
  let ru := fun (j : Fin 3) =>
    let t := fu j
    if t.fault then writeK p j t
    else if parked p t hu u j && (t.race==1 || t.race==2) then writeK p j (advanceRace t 3)
    else .empty _
  let rv := fun (j : Fin 3) =>
    let t := fv j
    if t.fault then writeK p j t
    else if parked p t hv v j && (t.race==1 || t.race==3) then writeK p j (advanceRace t 2)
    else .empty _
  let a := ((a.compose (ru 0)).compose (ru 1)).compose (ru 2)
  let b := ((b.compose (rv 0)).compose (rv 1)).compose (rv 2)
  let routed := (links hv).foldl (fun (a,b) (j,port) =>
    let t := fu j
    if ready p hu u j t then
      let (d,e,t') := effect p u v hu hv j port (win j) t
      match port with
      | none => ((a.compose d).compose (writeK p j (terminal p t')),b.compose e)
      | some k => ((a.compose d).compose (writeK p j T),
        (b.compose e).compose (writeK p k (arrival p hv v k t')))
    else
      if t.tag==2 then (a,b)
      else match port with
      | none => (if t.tag==1 then a.compose (writeK p j E) else a,b)
      | some k =>
        let reply := fv k
        if reply.tag==3 then (a.compose (writeK p j reply),b.compose (writeK p k E))
        else if t.tag==1 && reply.tag==0 then (a.compose (writeK p j E),b)
        else (a,b)
    ) (a,b)
  if hv then
    let (pc,t) := source p v (fv 0)
    (routed.1,(routed.2.compose pc).compose (match t with | none=>.empty _ | some t=>writeK p 0 t))
  else routed

private def widen (p : Params) (w : Patch (workW p)) : Patch p.w :=
  ⟨w.mask.setWidth p.w,w.value.setWidth p.w⟩

/-- Uniform-width work row for both reports; no access to high geometry
write lanes even for malformed raw controls. -/
def row (p : Params) (h : Pair Bool) (x : Pair (BitVec p.w)) : Pair (Patch p.w) :=
  let r := body p h x
  (widen p r.1,widen p r.2)

theorem work_only (p : Params) (h : Pair Bool) (x : Pair (BitVec p.w)) (i : Nat)
    (hh : workW p≤i) :
    (row p h x).1.mask.getLsbD i=false ∧ (row p h x).2.mask.getLsbD i=false := by
  simp [row,widen,BitVec.getLsbD_of_ge _ i hh]

def report1 (a : LargeParams) :
    Pair Bool → Pair (BitVec (reportWidth (a.k1+1) 1 a.J1)) →
      Pair (Patch (reportWidth (a.k1+1) 1 a.J1)) :=
  row ⟨a.k1+1,1,a.k1,a.J1⟩

def report2 (a : LargeParams) :
    Pair Bool → Pair (BitVec (reportWidth 2 a.t2 a.J2)) →
      Pair (Patch (reportWidth 2 a.t2 a.J2)) :=
  row ⟨2,a.t2,a.k2,a.J2⟩

/-- An incoming mark completes a right-header pulse and a COMMIT
on the very same old pair. Pulse flips Z from 0 to 1 using the old
zero thresholds; COMMIT stores **old** Z=0 with its new threshold
pair (0,1) in the target bank. Both idempotent and changing bits use
their declared masks, and no target digit or other bank is assigned. -/
theorem shared_pulse_commit_fixture :
    let p : Params := ⟨3,1,2,3⟩
    let f : Tok := {tag:=2, opcode:=commitOp p, payload:=5}
    let u : BitVec p.w := BitVec.ofNat _ (encode p f * 2^(kOffset p 0))
    let v : BitVec p.w := BitVec.ofNat _
      (2^(grantBase p+1) + 21*2^(sealBase p) +
       2^(bankOffset p 1+2+2*d p) + 2^(pc p+o p+1) +
       encode p T * 2^(kOffset p 0) + 2*2^(ell p.streak)+2)
    let out := row p (true,true) (u,v)
    let y := out.2.apply v
    Z p v=false ∧ Z p y=true ∧ selected p y=1 ∧ aBit p y 1=false ∧ bPair p y 1=1 ∧
      (oldK p true y 1).applied=true ∧
      out.2.mask.toNat=
        (2^(ell p.streak+3)-1)+2^(grantBase p+3)+31*2^(sealBase p)+
        7*2^(bankOffset p 1+2*d p)+(2^(tokenW p)-1)*2^(kOffset p 1) := by
  decide

/-- A live spare radix-3 digit is a fault; dormant payload of E is
not rejected or materialized by the token decoder. -/
theorem radix_spare_fixture :
    let p : Params := ⟨3,1,2,3⟩
    decode p false (BitVec.ofNat _ (encode p {tag:=2,opcode:=readOp p,payload:=3})) =
      F 2 ∧
    decode p false (BitVec.ofNat _ 31)=E := by decide

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- The condition used by the literal pulse body, including the old
race normalization and clipping of an inherited streak counter. -/
def paints (p : Params) (h : Bool) (side : Nat) (x : BitVec p.w) : Bool :=
  let w := ell p.streak
  let r := get x w 2
  let k := get x 0 w
  let r := if r==3 then 0 else r
  let k := if k<p.streak then k else 0
  h && r==2 && r != side && k+1==p.streak

private def pulseWiden (p : Params) (q : Patch (workW p)) : Patch p.w :=
  widen p q

private theorem pulse_field_out (p : Params) (k b v i : Nat)
    (P : i<k ∨ k+b≤i) : (field p k b v).mask.getLsbD i=false := by
  rcases P with H|H
  · simp [field,BitVec.getLsbD_shiftLeft,show ¬ k≤i by omega]
  · have B : b≤i-k := by omega
    simp [field,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_of_ge _ _ B]

private theorem pulse_comp_out {w : Nat} {a b : Patch w} {i : Nat}
    (A : a.mask.getLsbD i=false) (B : b.mask.getLsbD i=false) :
    (a.compose b).mask.getLsbD i=false := by simp [Patch.compose,A,B]

private theorem pulse_field_write (p : Params) (k b v i : Nat)
    (A : k≤i) (B : i<k+b) (C : i<workW p) :
    (field p k b v).mask.getLsbD i=true ∧
    (field p k b v).value.getLsbD i=(BitVec.ofNat b v).getLsbD (i-k) := by
  have D : i-k<b := by omega
  have E : i-k<workW p := by omega
  simp [field,A,C,D]

private theorem pulse_widen_apply (p : Params) (a b : Patch (workW p)) (x : BitVec p.w) :
    (pulseWiden p (a.compose b)).apply x=(pulseWiden p b).apply ((pulseWiden p a).apply x) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  by_cases L : i<workW p
  · simp only [pulseWiden,widen,Patch.compose,Patch.apply,BitVec.getLsbD_or,
      BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_setWidth,I,L,
      decide_true,Bool.true_and]
    cases a.mask.getLsbD i <;> cases b.mask.getLsbD i <;> simp
  · have H : workW p≤i := by omega
    have P (q : Patch (workW p)) : (pulseWiden p q).mask.getLsbD i=false := by
      simp [pulseWiden,widen,BitVec.getLsbD_of_ge _ _ H]
    rw [Patch.hold _ _ _ (P _),Patch.hold _ _ _ (P _),Patch.hold _ _ _ (P _)]

private theorem pulse_widen_frame (p : Params) (a : Patch (workW p)) (x : BitVec p.w)
    (i : Nat) (A : a.mask.getLsbD i=false) :
    ((pulseWiden p a).apply x).getLsbD i=x.getLsbD i := by
  apply Patch.hold
  simp [pulseWiden,widen,A]

/-- The pulse patch cannot touch a controller, token, seal, grant,
bank or geometry field. -/
theorem pulse_mask_below_tail (p : Params) (h : Bool) (side : Nat) (x : BitVec p.w)
    (i : Nat) (I : tail p≤i) : (pulse p h side x).mask.getLsbD i=false := by
  have L (v : Nat) : (field p 0 (ell p.streak) v).mask.getLsbD i=false :=
    pulse_field_out p _ _ _ _ (.inr (by unfold tail at I; omega))
  have R (v : Nat) : (field p (ell p.streak) 2 v).mask.getLsbD i=false :=
    pulse_field_out p _ _ _ _ (.inr (by unfold tail at I; omega))
  have Z' (v : Nat) : (field p (ell p.streak+2) 1 v).mask.getLsbD i=false :=
    pulse_field_out p _ _ _ _ (.inr (by unfold tail at I; omega))
  let w := ell p.streak
  let r0 := get x w 2
  let r := if r0==3 then 0 else r0
  let k0 := get x 0 w
  let k := if k0<p.streak then k0 else 0
  let paint := r==2 && k+1==p.streak
  let pad := (field p w 2 0).compose (field p 0 w (if r==1 || paint then 0 else k+1))
  change (if !h then (field p w 2 0).compose (field p 0 w 0)
    else if r==0 then field p w 2 side
    else if r==side then Patch.empty _
    else if paint then pad.compose (field p (w+2) 1 ((bPair p x (selected p x)==0).toNat))
    else pad).mask.getLsbD i=false
  split
  · exact pulse_comp_out (R _) (L _)
  split
  · exact R _
  split
  · simp [Patch.empty]
  split
  · exact pulse_comp_out (pulse_comp_out (R _) (L _)) (Z' _)
  · exact pulse_comp_out (R _) (L _)

/-- A healthy decoded COMMIT is either denied with an empty patch,
or writes only above the pulse tail. -/
theorem commit_effect_mask_above_tail (p : Params) (u v : BitVec p.w) (hu win : Bool)
    (t : Tok) (healthy : t.fault=false) (op : t.opcode=commitOp p)
    (i : Nat) (I : i<tail p) :
    (effect p u v hu true 0 (some 1) win t).2.1.mask.getLsbD i=false := by
  have E : (Patch.empty (workW p)).mask.getLsbD i=false := by simp [Patch.empty]
  have low (n b m : Nat) (H : tail p≤n) : (field p n b m).mask.getLsbD i=false :=
    pulse_field_out p n b m i (.inl (by omega))
  have S (v : Option Nat) : (writeSeal p v).mask.getLsbD i=false :=
    low _ _ _ (by unfold sealBase sourceBase; omega)
  have B (ix z b val : Nat) : (field p (bankOffset p ix+z) b val).mask.getLsbD i=false :=
    low _ _ _ (by unfold bankOffset sealBase sourceBase; omega)
  have G (ix : Nat) : (field p (grantBase p+3) 1 ix).mask.getLsbD i=false :=
    low _ _ _ (by unfold grantBase sealBase sourceBase; omega)
  simp only [effect,healthy,op,beq_self_eq_true,Bool.true_and,Bool.false_eq_true,if_false,if_true]
  split
  · exact pulse_comp_out (pulse_comp_out (G _) (S _)) (B _ _ _ _)
  · exact E

/-- These are two intents computed from the same old pair, not two
successive protocol steps with newly recomputed guards. -/
theorem pulse_disjoint_right_commit (p : Params) (u v : BitVec p.w) (hu win : Bool)
    (t : Tok) (healthy : t.fault=false) (op : t.opcode=commitOp p) :
    (pulse p true 1 v).disjoint (effect p u v hu true 0 (some 1) win t).2.1 := by
  intro i H
  apply commit_effect_mask_above_tail p u v hu win t healthy op i
  by_cases L : i<tail p
  · exact L
  · rw [pulse_mask_below_tail p true 1 v i (by omega)] at H
    contradiction

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Evaluate the pulse's Z write on any base bytes. The sampled result
is a function of the snapshot x, not the current selected bank in base. -/
theorem pulse_Z_from_old (p : Params) (h : Bool) (side : Nat) (x base : BitVec p.w) :
    Z p ((pulseWiden p (pulse p h side x)).apply base)=
      if paints p h side x then bPair p x (selected p x)==0 else Z p base := by
  let w := ell p.streak
  let r0 := get x w 2
  let r := if r0==3 then 0 else r0
  let k0 := get x 0 w
  let k := if k0<p.streak then k0 else 0
  let paint := r==2 && k+1==p.streak
  let pad := (field p w 2 0).compose (field p 0 w (if r==1 || paint then 0 else k+1))
  let write := field p (w+2) 1 ((bPair p x (selected p x)==0).toNat)
  have C : w+2<workW p := by
    dsimp [w]
    unfold workW grantBase sealBase sourceBase tail
    omega
  have CW : w+2<p.w := by rw [layout_size]; omega
  have L (v : Nat) : (field p 0 w v).mask.getLsbD (w+2)=false :=
    pulse_field_out p _ _ _ _ (.inr (by omega))
  have R (v : Nat) : (field p w 2 v).mask.getLsbD (w+2)=false :=
    pulse_field_out p _ _ _ _ (.inr (by omega))
  have P : pad.mask.getLsbD (w+2)=false := pulse_comp_out (R _) (L _)
  change ((pulseWiden p (if !h then (field p w 2 0).compose (field p 0 w 0)
    else if r==0 then field p w 2 side
    else if r==side then Patch.empty _
    else if paint then pad.compose write else pad)).apply base).getLsbD (w+2)=
      if h && (r==2) && (r != side) && (k+1==p.streak) then
        bPair p x (selected p x)==0 else base.getLsbD (w+2)
  by_cases H : h=true
  · have notH : (!h)=false := by simp [H]
    rw [notH]
    simp only [Bool.false_eq_true,if_false]
    by_cases R0 : r=0
    · simp only [H,R0,show ((0:Nat)==2)=false by decide,beq_self_eq_true,
        Bool.true_and,Bool.false_and,if_true]
      exact pulse_widen_frame p _ base _ (R _)
    · have R0' : (r==0)=false := beq_eq_false_iff_ne.mpr R0
      by_cases RS : r=side
      · simp only [H,RS,beq_self_eq_true,bne_self_eq_false,Bool.true_and,
          Bool.and_false,Bool.false_and,Bool.false_eq_true,if_false,if_true]
        apply pulse_widen_frame
        by_cases T : side=0 <;> simp [T,R,Patch.empty]
      · have RS' : (r==side)=false := beq_eq_false_iff_ne.mpr RS
        have RS'' : (r != side)=true := by simp [bne,RS']
        simp only [H,R0',RS',RS'',Bool.false_eq_true,if_false,Bool.true_and,Bool.and_true]
        change ((pulseWiden p (if paint then pad.compose write else pad)).apply base).getLsbD (w+2)=
          if paint then _ else _
        by_cases T : paint=true
        · rw [if_pos T,if_pos T,pulse_widen_apply]
          obtain ⟨M,V⟩ := pulse_field_write p (w+2) 1 ((bPair p x (selected p x)==0).toNat)
            (w+2) (by omega) (by omega) C
          have MW : (pulseWiden p write).mask.getLsbD (w+2)=true := by
            simp [pulseWiden,widen,write,M,CW]
          rw [Patch.write _ _ _ MW]
          have V' : (pulseWiden p write).value.getLsbD (w+2)=
              (BitVec.ofNat 1 ((bPair p x (selected p x)==0).toNat)).getLsbD 0 := by
            simpa [pulseWiden,widen,write,CW] using V
          rw [V']
          cases (bPair p x (selected p x)==0) <;> rfl
        · rw [if_neg T,if_neg T]
          exact pulse_widen_frame p _ base _ P
  · have H' : h=false := Bool.eq_false_iff.mpr H
    simp only [H',Bool.not_false,if_true,Bool.false_and,Bool.false_eq_true,if_false]
    exact pulse_widen_frame p _ base _ (pulse_comp_out (R _) (L _))

/-- Z after the two same-snapshot intents is still the pulse result;
the COMMIT cannot write its tail bit. -/
theorem pulse_commit_Z (p : Params) (u v : BitVec p.w) (hu win : Bool)
    (t : Tok) (healthy : t.fault=false) (op : t.opcode=commitOp p) :
    let q := (effect p u v hu true 0 (some 1) win t).2.1
    Z p ((pulseWiden p (pulse p true 1 v)).apply ((pulseWiden p q).apply v)) =
      if paints p true 1 v then bPair p v (selected p v)==0 else Z p v := by
  dsimp only
  rw [pulse_Z_from_old]
  have I : ell p.streak+2<tail p := by unfold tail; omega
  have F := commit_effect_mask_above_tail p u v hu win t healthy op _ I
  rw [show Z p ((pulseWiden p (effect p u v hu true 0 (some 1) win t).2.1).apply v)=Z p v
     from pulse_widen_frame p _ v _ F]

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

/-- The effect's payload uses the old right Z even when the pulse on
the same pair repaints Z. Source/routing masks are handled separately. -/
theorem commit_effect_payload (p : Params) (hu : Bool) (u v : BitVec p.w)
    (dsc : Nat) (G : gBit p v 1=true) (S : selected p v=dsc/8)
    (R : readSeal p v=some dsc) (win : Bool) :
    let t : Tok := {tag:=2,opcode:=commitOp p,payload:=dsc}
    let ix := (dsc/4)%2
    effect p u v hu true 0 (some 1) win t =
      (.empty _,((field p (grantBase p+3) 1 ix).compose (writeSeal p none)).compose
        (field p (bankOffset p ix+2*d p) 3 (4*(Z p v).toNat+dsc%4)),
        {t with applied:=true}) := by
  simp [effect,G,S,R]

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

set_option maxRecDepth 8192
set_option maxHeartbeats 3500000

abbrev publicationSelector := selected
abbrev publicationA := aBit
abbrev publicationPair := bPair
abbrev publicationToken := oldK
abbrev publicationGrant := gBit
abbrev publicationSeal := readSeal

private def cmtIndex (p : Params) (i : Nat) : Prop :=
  (sealBase p + 5 ≤ i ∧ i < grantBase p) ∨ i=grantBase p+3

private theorem cmtWork (p : Params) (i : Nat) (I : cmtIndex p i) : i<workW p := by
  unfold cmtIndex at I
  unfold workW
  omega

private def cmtFrame (p : Params) (f : Patch (workW p)) : Prop :=
  ∀ i, cmtIndex p i → f.mask.getLsbD i=false

private theorem cmtEmpty (p : Params) : cmtFrame p (.empty _) := by
  intro i _
  simp [Patch.empty]

private theorem cmtCompose {p : Params} {f g : Patch (workW p)}
    (F : cmtFrame p f) (G : cmtFrame p g) : cmtFrame p (f.compose g) := by
  intro i I
  simp [Patch.compose,F i I,G i I]

private theorem cmtField (p : Params) (k b v : Nat)
    (H : ∀ i, cmtIndex p i → i<k ∨ k+b≤i) : cmtFrame p (field p k b v) := by
  intro i I
  rcases H i I with E|E
  · simp [field,BitVec.getLsbD_shiftLeft,show ¬ k≤i by omega]
  · have B : b≤i-k := by omega
    simp [field,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_of_ge _ _ B]

private theorem cmtEarly (p : Params) (k b v : Nat)
    (H : k+b≤sealBase p+5) : cmtFrame p (field p k b v) := by
  apply cmtField
  intro i I
  unfold cmtIndex at I
  have : sealBase p+5≤grantBase p := by unfold grantBase; omega
  omega

private theorem cmtK (p : Params) (j : Fin 3) (t : Tok) :
    cmtFrame p (writeK p j t) := by
  apply cmtEarly
  have F := j.isLt
  have G : 2-j.val≤2 := by omega
  have H := Nat.mul_le_mul_right (tokenW p) G
  simp only [kOffset,sealBase,sourceBase]
  omega

private theorem cmtSeal (p : Params) (n : Option Nat) :
    cmtFrame p (writeSeal p n) := cmtEarly p _ _ _ (by omega)

private theorem cmtReset (p : Params) : cmtFrame p (reset p) := by
  apply cmtEarly
  unfold sealBase
  omega

private theorem cmtCtrl (p : Params) (a b : Nat) : cmtFrame p (ctrl p a b) := by
  apply cmtEarly
  unfold pc sealBase sourceW
  omega

private theorem cmtSF (p : Params) (k b v : Nat) (H : k+b≤sourceW p) :
    cmtFrame p (sf p k b v) := by
  apply cmtEarly
  unfold sealBase
  omega

private theorem cmtIfPair (p : Params) (Q : Prop) [Decidable Q]
    (a b : Patch (workW p) × Option Tok)
    (A : cmtFrame p a.1) (B : cmtFrame p b.1) :
    cmtFrame p (if Q then a else b).1 := by
  by_cases H : Q
  · rwa [if_pos H]
  · rwa [if_neg H]

private theorem cmtSource (p : Params) (x : BitVec p.w) (t : Tok) :
    cmtFrame p (source p x t).1 := by
  have C := cmtCtrl p
  have R := cmtReset p
  have E := cmtEmpty p
  have hPhase : cmtFrame p (field p (pc p+o p) 2 2) := by
    apply cmtEarly
    unfold pc sealBase sourceW
    omega
  have fld (j b v : Nat) (F : j+b≤21+2*d p) : cmtFrame p (sf p j b v) :=
    cmtSF p _ _ _ (by unfold sourceW; omega)
  have hInit (op : Nat) : cmtFrame p (if op==0 then reset p else .empty _) := by
    split
    · exact R
    · exact E
  unfold source
  dsimp only
  apply cmtIfPair
  · exact R
  apply cmtIfPair
  · apply cmtIfPair
    · exact R
    · exact cmtCompose (hInit _) hPhase
  apply cmtIfPair
  · exact E
  apply cmtIfPair
  · exact R
  apply cmtIfPair
  · exact C _ _
  apply cmtIfPair
  · exact C _ _
  apply cmtIfPair
  · apply cmtIfPair
    · exact C _ _
    · exact R
  apply cmtIfPair
  · exact cmtCompose (cmtCompose (C _ _) (fld _ _ _ (by omega))) (fld _ _ _ (by omega))
  apply cmtIfPair
  · apply cmtIfPair
    · exact R
    apply cmtIfPair
    · apply cmtIfPair
      · exact cmtCompose (C _ _) (fld _ _ _ (by omega))
      · exact cmtCompose (cmtCompose (cmtCompose (C _ _) (fld _ _ _ (by omega)))
          (fld _ _ _ (by omega))) (fld _ _ _ (by omega))
    · exact cmtCompose (cmtCompose (cmtCompose (C _ _) (fld _ _ _ (by omega)))
        (fld _ _ _ (by omega))) (fld _ _ _ (by omega))
  apply cmtIfPair
  · exact C _ _
  apply cmtIfPair
  · exact C _ _
  · exact R

private def cmtNorm (p : Params) (h : Bool) (v : BitVec p.w) (j : Fin 3) :
    Patch (workW p) :=
  let t := oldK p h v j
  if t.fault then writeK p j t
  else if parked p t h v j && (t.race==1 || t.race==3) then writeK p j (advanceRace t 2)
  else .empty _

private def cmtRoute (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3 → Bool) (ab : Pair (Patch (workW p))) (l : Fin 3 × Option (Fin 3)) :
    Pair (Patch (workW p)) :=
  let (a,b) := ab
  let (j,port) := l
  let t := oldK p hu u j
  if ready p hu u j t then
    let (d,e,t') := effect p u v hu hv j port (win j) t
    match port with
    | none => ((a.compose d).compose (writeK p j (terminal p t')),b.compose e)
    | some k => ((a.compose d).compose (writeK p j T),
      (b.compose e).compose (writeK p k (arrival p hv v k t')))
  else
    if t.tag==2 then (a,b)
    else match port with
    | none => (if t.tag==1 then a.compose (writeK p j E) else a,b)
    | some k =>
      let reply := oldK p hv v k
      if reply.tag==3 then (a.compose (writeK p j reply),b.compose (writeK p k E))
      else if t.tag==1 && reply.tag==0 then (a.compose (writeK p j E),b)
      else (a,b)

private theorem cmtEffectOther (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) (t : Tok) (J : j≠0) :
    (effect p u v hu hv j k win t).2.1=.empty _ := by
  unfold effect
  dsimp only
  simp only [beq_false_of_ne J,Bool.and_false,Bool.false_and,Bool.false_eq_true,if_false]
  repeat' first | rfl | split

private theorem cmtRouteOther (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3 → Bool) (a b : Patch (workW p))
    (j : Fin 3) (k : Option (Fin 3)) (J : j≠0) (i : Nat) (I : cmtIndex p i) :
    (cmtRoute p hu hv u v win (a,b) (j,k)).2.mask.getLsbD i=b.mask.getLsbD i ∧
    (cmtRoute p hu hv u v win (a,b) (j,k)).2.value.getLsbD i=b.value.getLsbD i := by
  have iden (b c : Patch (workW p)) (C : cmtFrame p c) :
      (b.compose c).mask.getLsbD i=b.mask.getLsbD i ∧
      (b.compose c).value.getLsbD i=b.value.getLsbD i := by
    exact ⟨by simp [Patch.compose,C i I], Patch.hold _ _ _ (C i I)⟩
  unfold cmtRoute
  dsimp only
  split
  · have E := cmtEffectOther p u v hu hv j k (win j) (oldK p hu u j) J
    cases k with
    | none => exact iden b _ (by rw [E]; exact cmtEmpty p)
    | some k =>
      change ((b.compose _).compose _).mask.getLsbD i=_ ∧
        ((b.compose _).compose _).value.getLsbD i=_
      have F : cmtFrame p ((effect p u v hu hv j (some k) (win j) (oldK p hu u j)).2.1) := by
        rw [E]
        exact cmtEmpty p
      have L := iden b _ F
      let e := effect p u v hu hv j (some k) (win j) (oldK p hu u j)
      have R := iden (b.compose e.2.1) (writeK p k (arrival p hv v k e.2.2))
        (cmtK p k (arrival p hv v k e.2.2))
      exact ⟨R.1.trans L.1,R.2.trans L.2⟩
  · split
    · exact ⟨rfl,rfl⟩
    · cases k with
      | none => exact ⟨rfl,rfl⟩
      | some k =>
        by_cases J' : ((oldK p hv v k).tag==3)=true
        · simp only [if_pos J']
          exact iden b _ (cmtK p k E)
        · simp only [if_neg J']
          split <;> exact ⟨rfl,rfl⟩

private theorem cmtUnfold (p : Params) (hu hv : Bool) (u v : BitVec p.w) :
    body p (hu,hv) (u,v) =
  let fu := oldK p hu u
  let fv := oldK p hv v
  let action := fun (j : Fin 3) (op : Nat) =>
    hu && ready p hu u j (fu j) && !(fu j).fault && (fu j).opcode==op
  let rel := fun j => action j 0
  let ask := fun j => action j (acqOp p)
  let w := !canonical p u 0 && !canonical p u 1 && !canonical p u 2 && ask 1 && !rel 1
  let win := fun j : Fin 3 =>
    if j==1 then w
    else !w && !canonical p u 1 && ask j && !canonical p u j && !rel j
  let gg := fun j => (canonical p u j && !rel j) || win j
  let clear := ((reset p).compose (writeSeal p none)).compose (grants p fun _ => false)
  let a := (if hu then grants p gg else clear).compose (pulse p hu 2 u)
  let b := (if hv then
    if gBit p v 1 && (gBit p v 0 || gBit p v 2) then grants p (canonical p v) else .empty _
    else clear).compose (pulse p hv 1 v)
  let ru := fun (j : Fin 3) =>
    let t := fu j
    if t.fault then writeK p j t
    else if parked p t hu u j && (t.race==1 || t.race==2) then writeK p j (advanceRace t 3)
    else .empty _
  let a := ((a.compose (ru 0)).compose (ru 1)).compose (ru 2)
  let b := ((b.compose (cmtNorm p hv v 0)).compose (cmtNorm p hv v 1)).compose (cmtNorm p hv v 2)
  let routed := (links hv).foldl (cmtRoute p hu hv u v win) (a,b)
  if hv then
    let (pc,t) := source p v (fv 0)
    (routed.1,(routed.2.compose pc).compose (match t with | none=>.empty _ | some t=>writeK p 0 t))
  else routed := rfl

private def cmtPatch (p : Params) (v : BitVec p.w) (dsc : Nat) : Patch (workW p) :=
  let ix := (dsc/4)%2
  ((field p (grantBase p+3) 1 ix).compose (writeSeal p none)).compose
    (field p (bankOffset p ix+2*d p) 3 (4*(Z p v).toNat+dsc%4))

/-- A literal guarded incoming COMMIT uses the old right grant, selector,
seal and descriptor. Its bank payload is formed from the old pulse Z. -/
def CommitGuard (p : Params) (hu : Bool) (u v : BitVec p.w) (dsc : Nat) : Prop :=
  oldK p hu u 0 = {tag:=2, opcode:=commitOp p, payload:=dsc} ∧
  gBit p v 1=true ∧ selected p v=dsc/8 ∧ readSeal p v=some dsc

private theorem cmtCore (p : Params) (hu : Bool) (u v : BitVec p.w) (dsc : Nat)
    (H : CommitGuard p hu u v dsc) (win : Fin 3 → Bool) (a b : Patch (workW p)) :
    (cmtRoute p hu true u v win (a,b) (0,some 1)).2 =
      (b.compose (cmtPatch p v dsc)).compose
        (writeK p 1 (arrival p true v 1
          {tag:=2,opcode:=commitOp p,payload:=dsc,applied:=true})) := by
  rcases H with ⟨F,G,S,A⟩
  simp [cmtRoute,F,ready,parked,gate,effect,G,S,A,cmtPatch]

private theorem cmtMask_after (p : Params) (i : Nat) (I : cmtIndex p i)
    (a b : Patch (workW p)) (B : cmtFrame p b) :
    (a.compose b).mask.getLsbD i=a.mask.getLsbD i ∧
    (a.compose b).value.getLsbD i=a.value.getLsbD i := by
  exact ⟨by simp [Patch.compose,B i I],Patch.hold _ _ _ (B i I)⟩

private theorem cmtSourceToken (p : Params) (ot : Option Tok) :
    cmtFrame p (match ot with | none => .empty _ | some t => writeK p 0 t) := by
  cases ot
  · exact cmtEmpty p
  · exact cmtK p _ _

private theorem cmtPatch_writes (p : Params) (v : BitVec p.w) (dsc i : Nat)
    (I : cmtIndex p i)
    (hit : (cmtPatch p v dsc).mask.getLsbD i=true)
    (hu : Bool) (u : BitVec p.w) (H : CommitGuard p hu u v dsc) :
    (row p (hu,true) (u,v)).2.mask.getLsbD i=true ∧
    (row p (hu,true) (u,v)).2.value.getLsbD i=(cmtPatch p v dsc).value.getLsbD i := by
  have E : i<workW p := cmtWork p i I
  have W := layout_size p
  have inW : i<p.w := by omega
  unfold row widen
  simp only [BitVec.getLsbD_setWidth, inW, decide_true, Bool.true_and]
  rw [cmtUnfold]
  simp only [links, if_true, List.foldl_cons, List.foldl_nil]
  cases HS : (source p v (oldK p true v 0)) with
  | mk srcP srcT =>
  have S : cmtFrame p srcP := by
    have T := cmtSource p v (oldK p true v 0)
    rwa [HS] at T
  have K := cmtSourceToken p srcT
  dsimp only
  rw [(cmtMask_after p i I _ _ K).1, (cmtMask_after p i I _ _ K).2]
  rw [(cmtMask_after p i I _ _ S).1, (cmtMask_after p i I _ _ S).2]
  rw [(cmtRouteOther p _ _ _ _ _ _ _ (2 : Fin 3) none (by decide) i I).1,
    (cmtRouteOther p _ _ _ _ _ _ _ (2 : Fin 3) none (by decide) i I).2]
  rw [(cmtRouteOther p _ _ _ _ _ _ _ (1 : Fin 3) (some 2) (by decide) i I).1,
    (cmtRouteOther p _ _ _ _ _ _ _ (1 : Fin 3) (some 2) (by decide) i I).2]
  rw [cmtCore p hu u v dsc H]
  rw [(cmtMask_after p i I _ _ (cmtK p 1 _)).1,
    (cmtMask_after p i I _ _ (cmtK p 1 _)).2]
  exact ⟨by simp [Patch.compose,hit], Patch.write _ _ _ hit⟩

private theorem cmtFieldMask (p : Params) (k b v i : Nat)
    (fit : k+b≤workW p) (L : k≤i) (R : i<k+b) :
    (field p k b v).mask.getLsbD i=true := by
  let F : Field (workW p) b := ⟨k,fit⟩
  exact (F.inMask (BitVec.ofNat b v) i).mpr ⟨L,R⟩

private theorem cmtFieldVal (p : Params) (k b v j : Nat)
    (fit : k+b≤workW p) (J : j<b) :
    (field p k b v).value.getLsbD (k+j)=(BitVec.ofNat b v).getLsbD j := by
  have W : j<workW p := by omega
  have I : k+j<workW p := by omega
  simp [field,I,show ¬k+j<k by omega]

private theorem cmtBankRange (p : Params) (ix j : Nat)
    (X : ix≤1) (J : j<3) :
    cmtIndex p (bankOffset p ix+2*d p+j) := by
  unfold cmtIndex bankOffset grantBase bankW
  have I : ix=0 ∨ ix=1 := by omega
  rcases I with rfl|rfl <;> simp <;> omega

private theorem cmtBankOut (p : Params) (x : BitVec p.w) (ix : Nat) :
    ((x.extractLsb' (bankOffset p ix) (bankW p)).extractLsb' (2*d p) 3) =
      x.extractLsb' (bankOffset p ix+2*d p) 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  have J : 2*d p+i<bankW p := by unfold bankW; omega
  simp [I,J,Nat.add_assoc]

private theorem cmtObsBank (p : Params) (x : BitVec p.w) (ix q : Nat)
    (z : Bool)
    (H : x.extractLsb' (bankOffset p ix+2*d p) 3=BitVec.ofNat 3 (4*z.toNat+q))
    (L : q<4) :
    aBit p x ix=z ∧ bPair p x ix=q := by
  have Q := cmtBankOut p x ix
  rw [H] at Q
  have U := congrArg BitVec.toNat (congrArg (fun q : BitVec 3 => q.extractLsb' 0 2) Q)
  have U' : bPair p x ix=q := by
    unfold bPair stored get
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one,
      BitVec.toNat_ofNat] at U
    have Z : 4*z.toNat+q<8 := by cases z <;> simp at * <;> omega
    have K : (4*z.toNat+q)%4=q := by omega
    rw [Nat.mod_eq_of_lt Z,K] at U
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    omega
  refine ⟨?_,U'⟩
  have V := congrArg (fun q : BitVec 3 => q.getLsbD 2) Q
  have R : aBit p x ix=(x.extractLsb' (bankOffset p ix) (bankW p)).getLsbD (2*d p+2) := by
    unfold aBit stored get bit
    simp only [BitVec.getLsbD,show 2+2*d p=2*d p+2 by omega, Nat.testBit]
    have fm (a : Nat) : (a%2==1) = (a &&& 1 != 0) := by
      have E : a &&& 1 = a%2 := by simp
      rw [E]
      have D := Nat.mod_two_eq_zero_or_one a
      rcases D with F|F <;> simp [F]
    rw [Nat.and_comm]
    exact fm _
  rw [R]
  rw [BitVec.getLsbD_extractLsb'] at V
  simp only [show 2<3 by decide,decide_true,Bool.true_and] at V
  rw [V]
  have E : (BitVec.ofNat 3 (4*z.toNat+q)).getLsbD 2=z := by
    have Q : ∃ j : Fin 4, j.val=q := ⟨⟨q,L⟩,rfl⟩
    obtain ⟨j,rfl⟩ := Q
    exact (show ∀ (zz : Bool) (k : Fin 4),
      (BitVec.ofNat 3 (4*zz.toNat+k.val)).getLsbD 2=zz by decide) z j
  exact E

private theorem cmtObserve (p : Params) (hu : Bool) (u v : BitVec p.w) (dsc : Nat)
    (G : CommitGuard p hu u v dsc)
    (k b q : Nat)
    (I : ∀ j, j<b → cmtIndex p (k+j))
    (B : ∀ j, j<b → (cmtPatch p v dsc).mask.getLsbD (k+j)=true)
    (V : ∀ j, j<b → (cmtPatch p v dsc).value.getLsbD (k+j)=(BitVec.ofNat b q).getLsbD j) :
    ((row p (hu,true) (u,v)).2.apply v).extractLsb' k b=BitVec.ofNat b q := by
  apply BitVec.eq_of_getLsbD_eq
  intro j J
  have F := cmtPatch_writes p v dsc (k+j) (I j J) (B j J) hu u G
  rw [BitVec.getLsbD_extractLsb']
  simp only [J,decide_true,Bool.true_and]
  rw [Patch.write _ _ _ F.1,F.2,V j J]

theorem commit_publication (p : Params) (hu : Bool) (u v : BitVec p.w)
    (dsc : Nat) (H : CommitGuard p hu u v dsc) :
    let y := (row p (hu,true) (u,v)).2.apply v
    let ix := (dsc/4)%2
    publicationSelector p y=ix ∧ publicationA p y ix=Z p v ∧
      publicationPair p y ix=dsc%4 := by
  dsimp only
  let ix := (dsc/4)%2
  let k := bankOffset p ix+2*d p
  let off := grantBase p+3
  let q := 4*(Z p v).toNat+dsc%4
  have ixL : ix<2 := Nat.mod_lt _ (by decide)
  have idx : cmtIndex p off := .inr rfl
  have capS : off+1≤workW p := by unfold off workW; omega
  have capB : k+3≤workW p := by
    have W := cmtWork p _ (cmtBankRange p ix 2 (by omega) (by decide))
    dsimp only [k]
    omega
  have kHi : k+3≤grantBase p := by
    have E := cmtBankRange p ix 2 (by omega) (by decide)
    rcases E with ⟨_,E⟩|E
    · dsimp only [k]; omega
    · exfalso
      unfold bankOffset grantBase bankW at E
      have O : ix=0 ∨ ix=1 := by omega
      rcases O with L|L <;> simp [L] at E <;> omega
  have kLo : sealBase p+5≤k := by unfold k bankOffset; omega
  have slotS : selected p ((row p (hu,true) (u,v)).2.apply v)=ix := by
    have X := cmtObserve p hu u v dsc H off 1 ix (fun j J=>by
      have E : j=0 := by omega
      simpa [E] using idx) (fun j J=>by
      have E : j=0 := by omega
      subst j
      unfold cmtPatch
      dsimp only
      have W := cmtFieldMask p off 1 ix off capS (by omega) (by omega)
      simp [Patch.compose,off,ix,W]) (fun j J=>by
      have E : j=0 := by omega
      subst j
      unfold cmtPatch
      dsimp only
      have W := cmtFieldVal p off 1 ix 0 capS (by decide)
      have F1 := cmtSeal p none off idx
      have F2 : (field p k 3 q).mask.getLsbD off=false := by
        have A : k+3≤off := by unfold off; omega
        have B : 3≤off-k := by omega
        simp [field,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_of_ge _ _ B]
      change ((((field p off 1 ix).compose (writeSeal p none)).compose
        (field p k 3 q)).value.getLsbD (off+0))=_
      simp only [Nat.add_zero] at W ⊢
      change ((field p k 3 q).apply ((writeSeal p none).apply (field p off 1 ix).value)).getLsbD off=_
      rw [Patch.hold _ _ _ F2,Patch.hold _ _ _ F1,W])
    unfold selected get
    rw [X]
    simp [Nat.mod_eq_of_lt ixL]
  have slotB := cmtObserve p hu u v dsc H k 3 q
    (fun j J=>cmtBankRange p ix j (by omega) J)
    (fun j J=>by
      unfold cmtPatch
      dsimp only
      change ((((field p off 1 ix).compose (writeSeal p none)).compose
        (field p k 3 q)).mask.getLsbD (k+j))=true
      have W := cmtFieldMask p k 3 q (k+j) capB (by omega) (by omega)
      simp [Patch.compose,W])
    (fun j J=>by
      unfold cmtPatch
      dsimp only
      change ((field p k 3 q).apply ((writeSeal p none).apply (field p off 1 ix).value)).getLsbD (k+j)=_
      have W := cmtFieldMask p k 3 q (k+j) capB (by omega) (by omega)
      rw [Patch.write _ _ _ W,cmtFieldVal p k 3 q j capB J])
  exact ⟨slotS,cmtObsBank p _ ix (dsc%4) (Z p v) slotB (Nat.mod_lt _ (by decide))⟩

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private def lowFrame (p : Params) (q : Patch (workW p)) : Prop :=
  ∀ i, i<tail p → q.mask.getLsbD i=false

private theorem lowEmpty (p : Params) : lowFrame p (.empty _) :=
  fun i _=>by simp [Patch.empty]

private theorem lowComp {p : Params} {a b : Patch (workW p)}
    (A : lowFrame p a) (B : lowFrame p b) : lowFrame p (a.compose b) :=
  fun i I=>pulse_comp_out (A i I) (B i I)

private theorem lowField (p : Params) (k b v : Nat) (K : tail p≤k) :
    lowFrame p (field p k b v) :=
  fun i I=>pulse_field_out p k b v i (.inl (by omega))

private theorem lowK (p : Params) (j : Fin 3) (t : Tok) :
    lowFrame p (writeK p j t) := lowField p _ _ _ (by unfold kOffset; omega)

private theorem lowSeal (p : Params) (v : Option Nat) :
    lowFrame p (writeSeal p v) := lowField p _ _ _ (by unfold sealBase sourceBase; omega)

private theorem lowGrants (p : Params) (v : Fin 3 → Bool) :
    lowFrame p (grants p v) := lowField p _ _ _ (by unfold grantBase sealBase sourceBase; omega)

private theorem lowIfPair (p : Params) (Q : Prop) [Decidable Q]
    (a b : Patch (workW p) × Option Tok)
    (A : lowFrame p a.1) (B : lowFrame p b.1) :
    lowFrame p (if Q then a else b).1 := by
  by_cases H : Q
  · rwa [if_pos H]
  · rwa [if_neg H]

private theorem lowSource (p : Params) (x : BitVec p.w) (t : Tok) :
    lowFrame p (source p x t).1 := by
  have resetOk : lowFrame p (reset p) := lowField p _ _ _ (by unfold sourceBase; omega)
  have ctrlOk (a b : Nat) : lowFrame p (ctrl p a b) :=
    lowField p _ _ _ (by unfold pc sourceBase; omega)
  have sfOk (a b c : Nat) : lowFrame p (sf p a b c) :=
    lowField p _ _ _ (by unfold sourceBase; omega)
  have phaseOk : lowFrame p (field p (pc p+o p) 2 2) :=
    lowField p _ _ _ (by unfold pc sourceBase; omega)
  have initOk (op : Nat) : lowFrame p (if op==0 then reset p else .empty _) := by
    split
    · exact resetOk
    · exact lowEmpty p
  unfold source
  dsimp only
  apply lowIfPair
  · exact resetOk
  apply lowIfPair
  · apply lowIfPair
    · exact resetOk
    · exact lowComp (initOk _) phaseOk
  apply lowIfPair
  · exact lowEmpty p
  apply lowIfPair
  · exact resetOk
  apply lowIfPair
  · exact ctrlOk _ _
  apply lowIfPair
  · exact ctrlOk _ _
  apply lowIfPair
  · apply lowIfPair
    · exact ctrlOk _ _
    · exact resetOk
  apply lowIfPair
  · exact lowComp (lowComp (ctrlOk _ _) (sfOk _ _ _)) (sfOk _ _ _)
  apply lowIfPair
  · apply lowIfPair
    · exact resetOk
    apply lowIfPair
    · apply lowIfPair
      · exact lowComp (ctrlOk _ _) (sfOk _ _ _)
      · exact lowComp (lowComp (lowComp (ctrlOk _ _) (sfOk _ _ _))
          (sfOk _ _ _)) (sfOk _ _ _)
    · exact lowComp (lowComp (lowComp (ctrlOk _ _) (sfOk _ _ _))
        (sfOk _ _ _)) (sfOk _ _ _)
  apply lowIfPair
  · exact ctrlOk _ _
  apply lowIfPair
  · exact ctrlOk _ _
  · exact resetOk

private theorem lowNorm (p : Params) (hv : Bool) (v : BitVec p.w) (j : Fin 3) :
    lowFrame p (cmtNorm p hv v j) := by
  unfold cmtNorm
  dsimp only
  split
  · exact lowK p _ _
  split
  · exact lowK p _ _
  · exact lowEmpty p

private theorem lowIfRight (p : Params) (P : Prop) [Decidable P]
    (a b : Patch (workW p) × Patch (workW p) × Tok)
    (A : lowFrame p a.2.1) (B : lowFrame p b.2.1) :
    lowFrame p (if P then a else b).2.1 := by
  split
  · exact A
  · exact B

private theorem lowEffectR (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) (t : Tok) :
    lowFrame p (effect p u v hu hv j k win t).2.1 := by
  have B (ix n val : Nat) : lowFrame p (field p (bankOffset p ix+2*d p) n val) :=
    lowField p _ _ _ (by unfold bankOffset sealBase sourceBase; omega)
  have G (ix : Nat) : lowFrame p (field p (grantBase p+3) 1 ix) :=
    lowField p _ _ _ (by unfold grantBase sealBase sourceBase; omega)
  let em := lowEmpty p
  unfold effect
  dsimp only
  apply lowIfRight
  · exact em
  apply lowIfRight
  · apply lowIfRight
    · exact lowComp (lowComp (G _) (lowSeal p _)) (B _ _ _)
    · exact em
  apply lowIfRight
  · exact em
  apply lowIfRight
  · exact em
  apply lowIfRight
  · exact em
  apply lowIfRight
  · exact em
  apply lowIfRight
  · apply lowIfRight <;> exact em
  apply lowIfRight
  · apply lowIfRight <;> exact em
  · exact em

private theorem lowComposeRead (p : Params) (a b : Patch (workW p)) (x : BitVec p.w)
    (B : lowFrame p b) (i : Nat) (I : i<tail p) :
    ((pulseWiden p (a.compose b)).apply x).getLsbD i=((pulseWiden p a).apply x).getLsbD i := by
  rw [pulse_widen_apply]
  exact pulse_widen_frame p _ _ i (B i I)

private theorem lowRouteR (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (win : Fin 3 → Bool) (ab : Pair (Patch (workW p))) (l : Fin 3 × Option (Fin 3))
    (i : Nat) (I : i<tail p) :
    ((pulseWiden p (cmtRoute p hu hv u v win ab l).2).apply v).getLsbD i=
      ((pulseWiden p ab.2).apply v).getLsbD i := by
  rcases ab with ⟨a,b⟩
  rcases l with ⟨j,k⟩
  have E (port : Option (Fin 3)) :=
    lowEffectR p u v hu hv j port (win j) (oldK p hu u j)
  unfold cmtRoute
  dsimp only
  split
  · cases k with
    | none => exact lowComposeRead p _ _ v (E none) i I
    | some k =>
      let ep := effect p u v hu hv j (some k) (win j) (oldK p hu u j)
      let aft := writeK p k (arrival p hv v k ep.2.2)
      change ((pulseWiden p ((b.compose ep.2.1).compose aft)).apply v).getLsbD i=_
      exact (lowComposeRead p (b.compose ep.2.1) aft v (lowK p _ _) i I).trans
        (lowComposeRead p b ep.2.1 v (E (some k)) i I)
  · split
    · rfl
    · cases k with
      | none => rfl
      | some k =>
        by_cases J : ((oldK p hv v k).tag==3)=true
        · simp only [if_pos J]
          exact lowComposeRead p b (writeK p k MISByteCodec.E) v (lowK p _ _) i I
        · simp only [if_neg J]
          split <;> rfl

private theorem lowFoldR (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (win : Fin 3 → Bool) (xs : List (Fin 3 × Option (Fin 3)))
    (ab : Pair (Patch (workW p))) (i : Nat) (I : i<tail p) :
    ((pulseWiden p (xs.foldl (cmtRoute p hu hv u v win) ab).2).apply v).getLsbD i=
      ((pulseWiden p ab.2).apply v).getLsbD i := by
  induction xs generalizing ab with
  | nil => rfl
  | cons l xs ih => exact (ih _).trans (lowRouteR p u v hu hv win ab l i I)

/-- The entire right raw work row reads its pulse from the old
snapshot. Routing and door operations do not touch the pulse bit. -/
theorem row_right_Z (p : Params) (hu hv : Bool) (u v : BitVec p.w) :
    Z p ((row p (hu,hv) (u,v)).2.apply v) =
      if paints p hv 1 v then bPair p v (selected p v)==0 else Z p v := by
  unfold row
  rw [cmtUnfold]
  dsimp only
  let i := ell p.streak+2
  have I : i<tail p := by unfold tail i; omega
  have clear : lowFrame p (((reset p).compose (writeSeal p none)).compose (grants p fun _=>false)) :=
    lowComp (lowComp (lowField p _ _ _ (by unfold sourceBase; omega)) (lowSeal p _)) (lowGrants p _)
  have base : lowFrame p (if hv then
      if gBit p v 1 && (gBit p v 0 || gBit p v 2) then grants p (canonical p v) else .empty _
      else ((reset p).compose (writeSeal p none)).compose (grants p fun _=>false)) := by
    split
    · split
      · exact lowGrants p _
      · exact lowEmpty p
    · exact clear
  have src := lowSource p v (oldK p hv v 0)
  have dest : lowFrame p (match (source p v (oldK p hv v 0)).2 with
      | none => .empty _ | some t=>writeK p 0 t) := by
    split
    · exact lowEmpty p
    · exact lowK p _ _
  -- First eliminate source, routing, and normalizer writes at this bit.
  have norm (a : Patch (workW p)) :
      ((pulseWiden p (((a.compose (cmtNorm p hv v 0)).compose (cmtNorm p hv v 1)).compose
          (cmtNorm p hv v 2))).apply v).getLsbD i=((pulseWiden p a).apply v).getLsbD i :=
    (lowComposeRead p _ _ v (lowNorm p hv v 2) i I).trans
      ((lowComposeRead p _ _ v (lowNorm p hv v 1) i I).trans
        (lowComposeRead p _ _ v (lowNorm p hv v 0) i I))
  have result (b : Patch (workW p)) (B : lowFrame p b) :
      ((pulseWiden p (b.compose (pulse p hv 1 v))).apply v).getLsbD i=
        if paints p hv 1 v then bPair p v (selected p v)==0 else Z p v := by
    rw [pulse_widen_apply]
    have E := pulse_Z_from_old p hv 1 v ((pulseWiden p b).apply v)
    change ((pulseWiden p (pulse p hv 1 v)).apply ((pulseWiden p b).apply v)).getLsbD i=_ at E
    rw [E,show Z p ((pulseWiden p b).apply v)=Z p v from pulse_widen_frame p _ _ i (B i I)]
  change ((pulseWiden p _).apply v).getLsbD i=_
  split
  · rename_i H
    dsimp only
    rw [lowComposeRead p _ _ v dest i I,lowComposeRead p _ _ v src i I,
      lowFoldR p u v hu hv _ _ _ i I,norm]
    exact result _ (by simpa only [if_pos H] using base)
  · rename_i H
    rw [lowFoldR p u v hu hv _ _ _ i I,norm]
    exact result _ (by simpa only [if_neg H] using base)

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

/-- COMMIT and pulse read the *same pre-mark word*. Neither output is
defined from the newly selected bank or the newly painted Z. -/
theorem same_mark_publication (p : Params) (hu : Bool) (u v : BitVec p.w)
    (dsc : Nat) (G : CommitGuard p hu u v dsc) :
    let y := (row p (hu,true) (u,v)).2.apply v
    let ix := (dsc/4)%2
    publicationSelector p y=ix ∧ publicationA p y ix=Z p v ∧
      publicationPair p y ix=dsc%4 ∧
      Z p y=(if paints p true 1 v then publicationPair p v (publicationSelector p v)==0 else Z p v) := by
  have C := commit_publication p hu u v dsc G
  exact ⟨C.1,C.2.1,C.2.2,row_right_Z p hu true u v⟩

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

def sourcePhase (p : Params) (x : BitVec p.w) : Nat := get x (pc p+o p) 2
def sourceOpcode (p : Params) (x : BitVec p.w) : Nat := get x (pc p) (o p)

def resetIssue (p : Params) : Patch (workW p) :=
  (reset p).compose (field p (pc p+o p) 2 2)
def resetWaitDone (p : Params) : Patch (workW p) := ctrl p 1 1
def resetRestart (p : Params) : Patch (workW p) := reset p

/-- At the canonical ISSUE0 PC, the old root K0 does not gate launch.
The source file is cleared and WAIT0 overrides the phase field. -/
theorem source_reset0_issue (p : Params) (x : BitVec p.w) (t : Tok)
    (P : sourcePhase p x=1) (O : sourceOpcode p x=0) :
    source p x t=(resetIssue p,some {tag:=2,opcode:=0}) := by
  unfold sourcePhase at P
  unfold sourceOpcode at O
  have A : ¬cmpOp p≤0 := by unfold cmpOp; omega
  have B : ¬writeOp p≤0 := by unfold writeOp; omega
  have C : ¬sealOp p≤0 := by unfold sealOp; omega
  have D : 0≠acqOp p := by unfold acqOp; omega
  simp [source,P,O,resetIssue,A,B,C,D]

/-- A canonical positive D0 response consumed in WAIT0 writes ISSUE1 and
clears the root token on the same source action. -/
theorem source_reset0_consume (p : Params) (x : BitVec p.w)
    (P : sourcePhase p x=2) (O : sourceOpcode p x=0) :
    source p x {tag:=3,opcode:=0}=(resetWaitDone p,some MISByteCodec.E) := by
  unfold sourcePhase at P
  unfold sourceOpcode at O
  simp [source,P,O,resetWaitDone]

theorem source_reset0_hold (p : Params) (x : BitVec p.w) (t : Tok)
    (P : sourcePhase p x=2) (O : sourceOpcode p x=0)
    (T : t.tag=1 ∨ t.tag=2) :
    source p x t=(.empty _,none) := by
  unfold sourcePhase at P
  unfold sourceOpcode at O
  rcases T with T|T <;> simp [source,P,O,T]

theorem source_reset0_fault (p : Params) (x : BitVec p.w)
    (P : sourcePhase p x=2) (O : sourceOpcode p x=0) :
    source p x (MISByteCodec.faultToken 3)=(resetRestart p,some MISByteCodec.E) := by
  unfold sourcePhase at P
  unfold sourceOpcode at O
  simp [source,P,O,resetRestart,MISByteCodec.faultToken]

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

def reportToken (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3) : Tok := oldK p h x j

def resetSourceSuffix (p : Params) (q : Patch (workW p)) (t : Tok) :
    Patch (workW p) := q.compose (writeK p 0 t)

def liftSourcePatch (p : Params) (q : Patch (workW p)) : Patch p.w := widen p q

/-- Joined within the report row: the canonical ISSUE0 source write is
strictly after routing and all other responder writes. -/
theorem row_reset0_issue_suffix (p : Params) (hu : Bool) (u v : BitVec p.w)
    (P : sourcePhase p v=1) (O : sourceOpcode p v=0) :
    ∃ a : Patch (workW p),
      (row p (hu,true) (u,v)).2 =
        liftSourcePatch p (a.compose (resetIssue p) |>.compose (writeK p 0 {tag:=2,opcode:=0})) := by
  unfold row
  rw [cmtUnfold]
  dsimp only
  simp only [source_reset0_issue p v _ P O]
  exact ⟨_,rfl⟩

/-- Consuming the canonical reply has the same final priority, even
when the routed prefix uses the other lanes of this old pair. -/
theorem row_reset0_consume_suffix (p : Params) (hu : Bool) (u v : BitVec p.w)
    (P : sourcePhase p v=2) (O : sourceOpcode p v=0)
    (R : reportToken p true v 0={tag:=3,opcode:=0}) :
    ∃ a : Patch (workW p),
      (row p (hu,true) (u,v)).2 =
        liftSourcePatch p (a.compose (resetWaitDone p) |>.compose (writeK p 0 MISByteCodec.E)) := by
  unfold reportToken at R
  unfold row
  rw [cmtUnfold]
  dsimp only
  simp only [R,source_reset0_consume p v P O]
  exact ⟨_,rfl⟩

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

/-- The actual decoded RESET0 forward and reply tokens. -/
def reset0Forward : Tok := {tag:=2}
def reset0Reply : Tok := {tag:=3}

def resetTokenWire (p : Params) (t : Tok) : BitVec (tokenW p) :=
  BitVec.ofNat (tokenW p) (encode p t)

def resetTokenRead (p : Params) (x : BitVec p.w) (j : Fin 3) : BitVec (tokenW p) :=
  x.extractLsb' (kOffset p j) (tokenW p)

private theorem reset0_admit_ne (p : Params) : (0 : Nat) ≠ admitOp p := by
  unfold admitOp
  omega

private theorem reset0_commit_ne (p : Params) : (0 : Nat) ≠ commitOp p := by
  unfold commitOp
  omega

private theorem reset0_acq_ne (p : Params) : (0 : Nat) ≠ acqOp p := by
  unfold acqOp
  omega

private theorem reset0_seal_ne (p : Params) : (0 : Nat) ≠ sealOp p := by
  unfold sealOp
  omega

/-- An actual decoded healthy RESET0 writes no right effect and clears
the old owner’s seal exactly on a header lane 1 departure. -/
theorem reset0_effect (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) :
    effect p u v hu hv j k win reset0Forward =
      (if hu && j==1 then writeSeal p none else .empty _, .empty _, reset0Forward) := by
  have C : ¬cmpOp p≤0 := by unfold cmpOp; omega
  have W : ¬writeOp p≤0 := by unfold writeOp; omega
  cases hu <;> by_cases J : j=1 <;>
    simp [effect,reset0Forward,parked,reset0_commit_ne,reset0_admit_ne,reset0_acq_ne,
      reset0_seal_ne,J,C,W]

private theorem reset0_ready (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3) :
    ready p h x j reset0Forward=true := by
  simp [ready,parked,reset0Forward,reset0_admit_ne]

private theorem reset0_arrival (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3) :
    arrival p h x j reset0Forward=reset0Forward := by
  simp [arrival,reset0Forward,reset0_admit_ne]

private theorem reset0_terminal (p : Params) : terminal p reset0Forward=reset0Reply := by
  have C : ¬cmpOp p≤0 := by unfold cmpOp; omega
  simp [terminal,reset0Forward,reset0Reply,reset0_admit_ne,reset0_commit_ne,
    reset0_acq_ne,C]

private theorem reset0_empty_comp {w : Nat} (b : Patch w) : b.compose (.empty _)=b := by
  cases b
  simp [Patch.compose,Patch.apply,Patch.empty]

/-- Exact selected old-pair RESET0 transit routing under arbitrary
preceding patch accumulation. The destination gets F0, old slot T. -/
theorem reset0_route_hop (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3 → Bool) (a b : Patch (workW p)) (j k : Fin 3)
    (H : oldK p hu u j=reset0Forward) :
    cmtRoute p hu hv u v win (a,b) (j,some k)=
      ((a.compose (if hu && j==1 then writeSeal p none else .empty _)).compose (writeK p j T),
       b.compose (writeK p k reset0Forward)) := by
  simp only [cmtRoute,H,reset0_ready,if_true,reset0_effect,reset0_arrival,reset0_empty_comp]

/-- Exact selected old-pair RESET0 terminal routing: replace F0 with
D0 locally, and do not modify the responder’s accumulated patch. -/
theorem reset0_route_turn (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3 → Bool) (a b : Patch (workW p)) (j : Fin 3)
    (H : oldK p hu u j=reset0Forward) :
    cmtRoute p hu hv u v win (a,b) (j,none)=
      ((a.compose (if hu && j==1 then writeSeal p none else .empty _)).compose (writeK p j reset0Reply),b) := by
  simp only [cmtRoute,H,reset0_ready,if_true,reset0_effect,reset0_terminal,reset0_empty_comp]

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

/-- The selected reverse link copies exactly the old decoded reply.
This applies to an inherited D as well as an authentic D0; it is not
an origin test. -/
theorem reset_drain_reverse_link (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3 → Bool) (a b : Patch (workW p)) (j k : Fin 3)
    (noF : (oldK p hu u j).tag≠2) (isD : (oldK p hv v k).tag=3) :
    cmtRoute p hu hv u v win (a,b) (j,some k) =
      (a.compose (writeK p j (oldK p hv v k)),b.compose (writeK p k MISByteCodec.E)) := by
  simp [cmtRoute,ready,noF,isD]

/-- T facing a clear successor disappears without inventing a reply. -/
theorem reset_drain_clear_link (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3 → Bool) (a b : Patch (workW p)) (j k : Fin 3)
    (isT : (oldK p hu u j).tag=1) (empty : (oldK p hv v k).tag=0) :
    cmtRoute p hu hv u v win (a,b) (j,some k) =
      (a.compose (writeK p j MISByteCodec.E),b) := by
  simp [cmtRoute,ready,isT,empty]

theorem reset_drain_terminal_trail (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3 → Bool) (a b : Patch (workW p)) (j : Fin 3)
    (isT : (oldK p hu u j).tag=1) :
    cmtRoute p hu hv u v win (a,b) (j,none) =
      (a.compose (writeK p j MISByteCodec.E),b) := by
  simp [cmtRoute,ready,isT]

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

private def reset0Frame (p : Params) (q : Patch (workW p)) : Prop :=
  ∀ i, i<sourceBase p → q.mask.getLsbD i=false

private theorem reset0Empty (p : Params) : reset0Frame p (.empty _) :=
  fun i _=>by simp [Patch.empty]

private theorem reset0Comp {p : Params} {a b : Patch (workW p)}
    (A : reset0Frame p a) (B : reset0Frame p b) : reset0Frame p (a.compose b) :=
  fun i I=>pulse_comp_out (A i I) (B i I)

private theorem reset0Field (p : Params) (k b v : Nat) (K : sourceBase p≤k) :
    reset0Frame p (field p k b v) :=
  fun i I=>pulse_field_out p k b v i (.inl (by omega))

private theorem reset0Seal (p : Params) (v : Option Nat) :
    reset0Frame p (writeSeal p v) := reset0Field p _ _ _ (by unfold sealBase; omega)

private theorem reset0IfPair (p : Params) (Q : Prop) [Decidable Q]
    (a b : Patch (workW p) × Option Tok)
    (A : reset0Frame p a.1) (B : reset0Frame p b.1) :
    reset0Frame p (if Q then a else b).1 := by
  by_cases H : Q
  · rwa [if_pos H]
  · rwa [if_neg H]

private theorem reset0Source (p : Params) (x : BitVec p.w) (t : Tok) :
    reset0Frame p (source p x t).1 := by
  have resetOk : reset0Frame p (reset p) := reset0Field p _ _ _ (by omega)
  have ctrlOk (a b : Nat) : reset0Frame p (ctrl p a b) :=
    reset0Field p _ _ _ (by unfold pc; omega)
  have sfOk (a b c : Nat) : reset0Frame p (sf p a b c) :=
    reset0Field p _ _ _ (by omega)
  have phaseOk : reset0Frame p (field p (pc p+o p) 2 2) :=
    reset0Field p _ _ _ (by unfold pc; omega)
  have initOk (op : Nat) : reset0Frame p (if op==0 then reset p else .empty _) := by
    split
    · exact resetOk
    · exact reset0Empty p
  unfold source
  dsimp only
  apply reset0IfPair
  · exact resetOk
  apply reset0IfPair
  · apply reset0IfPair
    · exact resetOk
    · exact reset0Comp (initOk _) phaseOk
  apply reset0IfPair
  · exact reset0Empty p
  apply reset0IfPair
  · exact resetOk
  apply reset0IfPair
  · exact ctrlOk _ _
  apply reset0IfPair
  · exact ctrlOk _ _
  apply reset0IfPair
  · apply reset0IfPair
    · exact ctrlOk _ _
    · exact resetOk
  apply reset0IfPair
  · exact reset0Comp (reset0Comp (ctrlOk _ _) (sfOk _ _ _)) (sfOk _ _ _)
  apply reset0IfPair
  · apply reset0IfPair
    · exact resetOk
    apply reset0IfPair
    · apply reset0IfPair
      · exact reset0Comp (ctrlOk _ _) (sfOk _ _ _)
      · exact reset0Comp (reset0Comp (reset0Comp (ctrlOk _ _) (sfOk _ _ _))
          (sfOk _ _ _)) (sfOk _ _ _)
    · exact reset0Comp (reset0Comp (reset0Comp (ctrlOk _ _) (sfOk _ _ _))
        (sfOk _ _ _)) (sfOk _ _ _)
  apply reset0IfPair
  · exact ctrlOk _ _
  apply reset0IfPair
  · exact ctrlOk _ _
  · exact resetOk

private theorem reset0IfRight (p : Params) (P : Prop) [Decidable P]
    (a b : Patch (workW p) × Patch (workW p) × Tok)
    (A : reset0Frame p a.2.1) (B : reset0Frame p b.2.1) :
    reset0Frame p (if P then a else b).2.1 := by
  split
  · exact A
  · exact B

private theorem reset0EffectR (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) (t : Tok) :
    reset0Frame p (effect p u v hu hv j k win t).2.1 := by
  have B (ix n val : Nat) : reset0Frame p (field p (bankOffset p ix+2*d p) n val) :=
    reset0Field p _ _ _ (by unfold bankOffset sealBase; omega)
  have G (ix : Nat) : reset0Frame p (field p (grantBase p+3) 1 ix) :=
    reset0Field p _ _ _ (by unfold grantBase sealBase; omega)
  let em := reset0Empty p
  unfold effect
  dsimp only
  apply reset0IfRight
  · exact em
  apply reset0IfRight
  · apply reset0IfRight
    · exact reset0Comp (reset0Comp (G _) (reset0Seal p _)) (B _ _ _)
    · exact em
  apply reset0IfRight
  · exact em
  apply reset0IfRight
  · exact em
  apply reset0IfRight
  · exact em
  apply reset0IfRight
  · exact em
  apply reset0IfRight
  · apply reset0IfRight <;> exact em
  apply reset0IfRight
  · apply reset0IfRight <;> exact em
  · exact em

private theorem reset0IfLeft (p : Params) (P : Prop) [Decidable P]
    (a b : Patch (workW p) × Patch (workW p) × Tok)
    (A : reset0Frame p a.1) (B : reset0Frame p b.1) :
    reset0Frame p (if P then a else b).1 := by
  split
  · exact A
  · exact B

private theorem reset0EffectL (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) (t : Tok) :
    reset0Frame p (effect p u v hu hv j k win t).1 := by
  have B (ix n val : Nat) : reset0Frame p (field p (bankOffset p ix) n val) :=
    reset0Field p _ _ _ (by unfold bankOffset sealBase; omega)
  let em := reset0Empty p
  unfold effect
  dsimp only
  apply reset0IfLeft
  · exact em
  apply reset0IfLeft
  · apply reset0IfLeft <;> exact em
  apply reset0IfLeft
  · exact em
  apply reset0IfLeft
  · exact reset0Seal p none
  apply reset0IfLeft
  · exact em
  apply reset0IfLeft
  · exact em
  apply reset0IfLeft
  · apply reset0IfLeft
    · exact em
    · exact B _ _ _
  apply reset0IfLeft
  · apply reset0IfLeft
    · exact reset0Seal p (some t.payload)
    · exact em
  · exact em

private theorem reset0SlotBound (p : Params) (j : Fin 3) :
    kOffset p j+tokenW p≤sourceBase p := by
  have J := j.isLt
  have M := Nat.mul_le_mul_right (tokenW p) (show 2-j.val≤2 by omega)
  unfold kOffset sourceBase
  omega

private theorem reset0_widen_apply (p : Params) (a b : Patch (workW p)) (x : BitVec p.w) :
    (widen p (a.compose b)).apply x=(widen p b).apply ((widen p a).apply x) :=
  pulse_widen_apply p a b x

private theorem reset0_read_hold (p : Params) (j : Fin 3)
    (q : Patch (workW p)) (x : BitVec p.w)
    (F : ∀ i, i<tokenW p → q.mask.getLsbD (kOffset p j+i)=false) :
    resetTokenRead p ((widen p q).apply x) j=resetTokenRead p x j := by
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  have G : ((widen p q).apply x).getLsbD (kOffset p j+i) = x.getLsbD (kOffset p j+i) :=
    pulse_widen_frame p q x (kOffset p j+i) (F i I)
  simpa [resetTokenRead,I] using G

private theorem reset0_read_frame (p : Params) (j : Fin 3)
    (q : Patch (workW p)) (x : BitVec p.w) (F : reset0Frame p q) :
    resetTokenRead p ((widen p q).apply x) j=resetTokenRead p x j :=
  reset0_read_hold p j q x (fun i I => F _ (Nat.lt_of_lt_of_le (by omega) (reset0SlotBound p j)))

private theorem reset0_read_kOther (p : Params) (j l : Fin 3)
    (T : j≠l) (t : Tok) (x : BitVec p.w) :
    resetTokenRead p ((widen p (writeK p l t)).apply x) j=resetTokenRead p x j := by
  apply reset0_read_hold
  intro i I
  apply pulse_field_out
  unfold kOffset
  have J := j.isLt
  have L := l.isLt
  have M : j.val≠l.val := fun E=>T (Fin.ext E)
  have JL : 2-j.val<2-l.val ∨ 2-l.val<2-j.val := by omega
  rcases JL with A|A
  · have H := Nat.mul_le_mul_right (tokenW p) (Nat.succ_le_of_lt A)
    rw [Nat.succ_mul] at H
    exact .inl (by omega)
  · have H := Nat.mul_le_mul_right (tokenW p) (Nat.succ_le_of_lt A)
    rw [Nat.succ_mul] at H
    exact .inr (by omega)

private theorem reset0_read_kSame (p : Params) (j : Fin 3) (t : Tok) (x : BitVec p.w) :
    resetTokenRead p ((widen p (writeK p j t)).apply x) j=resetTokenWire p t := by
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  have B := reset0SlotBound p j
  have work : sourceBase p≤workW p := by unfold workW grantBase sealBase; omega
  have fit : kOffset p j + tokenW p ≤ workW p := by omega
  have W := layout_size p
  have K : kOffset p j+i<p.w := by omega
  have H := pulse_field_write p (kOffset p j) (tokenW p) (encode p t) (kOffset p j+i)
    (by omega) (by omega) (by omega)
  have M : (widen p (writeK p j t)).mask.getLsbD (kOffset p j+i)=true := by
    simp [widen,writeK,K,H.1]
  rw [resetTokenRead,BitVec.getLsbD_extractLsb']
  simp only [I,decide_true,Bool.true_and]
  rw [Patch.write _ _ _ M]
  simp [widen,writeK,resetTokenWire,K,H.2]

private theorem reset0_compKOther (p : Params) (j k : Fin 3)
    (J : j≠k) (t : Tok) (a : Patch (workW p)) (x : BitVec p.w) :
    resetTokenRead p ((widen p (a.compose (writeK p k t))).apply x) j=
      resetTokenRead p ((widen p a).apply x) j := by
  rw [reset0_widen_apply]
  exact reset0_read_kOther p j k J t _

private theorem reset0_compFrame (p : Params) (j : Fin 3)
    (a b : Patch (workW p)) (x : BitVec p.w) (F : reset0Frame p b) :
    resetTokenRead p ((widen p (a.compose b)).apply x) j=
      resetTokenRead p ((widen p a).apply x) j := by
  rw [reset0_widen_apply]
  exact reset0_read_frame p j b _ F

private theorem reset0_tailL (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3 → Bool) (ab : Pair (Patch (workW p))) (l : Fin 3 × Option (Fin 3))
    (j : Fin 3) (J : j≠l.1) :
    resetTokenRead p ((widen p (cmtRoute p hu hv u v win ab l).1).apply u) j =
      resetTokenRead p ((widen p ab.1).apply u) j := by
  rcases ab with ⟨a,b⟩
  rcases l with ⟨l,k⟩
  have hold (t : Tok) (q : Patch (workW p)) :=
    reset0_compKOther p j l J t q u
  unfold cmtRoute
  dsimp only
  split
  · let ef := effect p u v hu hv l k (win l) (oldK p hu u l)
    have H (t : Tok) :
        resetTokenRead p ((widen p ((a.compose ef.1).compose (writeK p l t))).apply u) j =
          resetTokenRead p ((widen p a).apply u) j := by
      exact (hold t (a.compose ef.1)).trans
        (reset0_compFrame p j a ef.1 u (reset0EffectL p u v hu hv l k _ _))
    cases k
    · exact H _
    · exact H _
  · split
    · rfl
    · cases k with
      | none =>
        by_cases H : ((oldK p hu u l).tag==1)=true
        · simp only [if_pos H]
          exact hold _ _
        · simp only [if_neg H]
      | some k =>
        by_cases H : ((oldK p hv v k).tag==3)=true
        · simp only [if_pos H]
          exact hold _ _
        · simp only [if_neg H]
          split
          · exact hold _ _
          · rfl

private theorem reset0_tailR (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3 → Bool) (ab : Pair (Patch (workW p))) (l : Fin 3 × Option (Fin 3))
    (j : Fin 3) (J : some j≠l.2) :
    resetTokenRead p ((widen p (cmtRoute p hu hv u v win ab l).2).apply v) j =
      resetTokenRead p ((widen p ab.2).apply v) j := by
  rcases ab with ⟨a,b⟩
  rcases l with ⟨l,k⟩
  unfold cmtRoute
  dsimp only
  split
  · cases k with
    | none =>
      exact reset0_compFrame p j b _ v (reset0EffectR p u v hu hv l none _ _)
    | some k =>
      let ef := effect p u v hu hv l (some k) (win l) (oldK p hu u l)
      let t := arrival p hv v k ef.2.2
      change resetTokenRead p ((widen p ((b.compose ef.2.1).compose (writeK p k t))).apply v) j=_
      exact (reset0_compKOther p j k (fun h=>J (congrArg some h)) t (b.compose ef.2.1) v).trans
        (reset0_compFrame p j b ef.2.1 v (reset0EffectR p u v hu hv l (some k) _ _))
  · split
    · rfl
    · cases k with
      | none => rfl
      | some k =>
        by_cases H : ((oldK p hv v k).tag==3)=true
        · simp only [if_pos H]
          exact reset0_compKOther p j k (fun h=>J (congrArg some h)) _ b v
        · simp only [if_neg H]
          split <;> rfl

private def reset0Post (p : Params) (hv : Bool) (v : BitVec p.w)
    (a : Pair (Patch (workW p))) : Pair (Patch (workW p)) :=
  if hv then
    let (pc,t) := source p v (oldK p hv v 0)
    (a.1,(a.2.compose pc).compose (match t with | none=>.empty _ | some t=>writeK p 0 t))
  else a

private theorem reset0Post_left (p : Params) (hv : Bool) (v : BitVec p.w)
    (a : Pair (Patch (workW p))) : (reset0Post p hv v a).1=a.1 := by
  cases hv
  · rfl
  · unfold reset0Post
    simp only [if_true]

private theorem reset0Post_right (p : Params) (hv : Bool) (v : BitVec p.w)
    (a : Pair (Patch (workW p))) (k : Fin 3) (K : hv=true→k≠0) :
    resetTokenRead p ((widen p (reset0Post p hv v a).2).apply v) k =
      resetTokenRead p ((widen p a.2).apply v) k := by
  cases hv
  · rfl
  · have F := reset0Source p v (oldK p true v 0)
    unfold reset0Post
    simp only [if_true]
    cases H : source p v (oldK p true v 0) with
    | mk q t =>
      rw [H] at F
      cases t
      · change resetTokenRead p ((widen p ((a.2.compose q).compose (.empty _))).apply v) k=_
        rw [reset0_empty_comp]
        exact reset0_compFrame p k a.2 q v F
      · exact (reset0_compKOther p k 0 (K rfl) _ (a.2.compose q) v).trans
          (reset0_compFrame p k a.2 q v F)

private theorem reset0Unfold (p : Params) (hu hv : Bool) (u v : BitVec p.w) :
    body p (hu,hv) (u,v) =
  let fu := oldK p hu u
  let action := fun (j : Fin 3) (op : Nat) =>
    hu && ready p hu u j (fu j) && !(fu j).fault && (fu j).opcode==op
  let rel := fun j => action j 0
  let ask := fun j => action j (acqOp p)
  let w := !canonical p u 0 && !canonical p u 1 && !canonical p u 2 && ask 1 && !rel 1
  let win := fun j : Fin 3 =>
    if j==1 then w
    else !w && !canonical p u 1 && ask j && !canonical p u j && !rel j
  let gg := fun j => (canonical p u j && !rel j) || win j
  let clear := ((reset p).compose (writeSeal p none)).compose (grants p fun _ => false)
  let a := (if hu then grants p gg else clear).compose (pulse p hu 2 u)
  let b := (if hv then
    if gBit p v 1 && (gBit p v 0 || gBit p v 2) then grants p (canonical p v) else .empty _
    else clear).compose (pulse p hv 1 v)
  let ru := fun (j : Fin 3) =>
    let t := fu j
    if t.fault then writeK p j t
    else if parked p t hu u j && (t.race==1 || t.race==2) then writeK p j (advanceRace t 3)
    else .empty _
  let a := ((a.compose (ru 0)).compose (ru 1)).compose (ru 2)
  let b := ((b.compose (cmtNorm p hv v 0)).compose (cmtNorm p hv v 1)).compose (cmtNorm p hv v 2)
  reset0Post p hv v ((links hv).foldl (cmtRoute p hu hv u v win) (a,b)) := rfl

private theorem reset0_foldL (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3 → Bool) (suf : List (Fin 3 × Option (Fin 3)))
    (a : Pair (Patch (workW p))) (j : Fin 3)
    (J : ∀ l∈suf, j≠l.1) :
    resetTokenRead p ((widen p (suf.foldl (cmtRoute p hu hv u v win) a).1).apply u) j =
      resetTokenRead p ((widen p a.1).apply u) j := by
  induction suf generalizing a with
  | nil => rfl
  | cons l suf ih =>
    exact (ih _ (fun t T=>J t (List.mem_cons_of_mem _ T))).trans
       (reset0_tailL p hu hv u v win a l j (J l List.mem_cons_self))

private theorem reset0_foldR (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3 → Bool) (suf : List (Fin 3 × Option (Fin 3)))
    (a : Pair (Patch (workW p))) (j : Fin 3)
    (J : ∀ l∈suf, some j≠l.2) :
    resetTokenRead p ((widen p (suf.foldl (cmtRoute p hu hv u v win) a).2).apply v) j =
      resetTokenRead p ((widen p a.2).apply v) j := by
  induction suf generalizing a with
  | nil => rfl
  | cons l suf ih =>
    exact (ih _ (fun t T=>J t (List.mem_cons_of_mem _ T))).trans
       (reset0_tailR p hu hv u v win a l j (J l List.mem_cons_self))

/-- Literal destination of lane j in the raw report work row. -/
def reset0Destination (hv : Bool) (j : Fin 3) : Option (Fin 3) :=
  if hv then if j=2 then none else some (j+1) else some j

private theorem reset0_list_split (hv : Bool) (j : Fin 3) :
    ∃ pre suf : List (Fin 3 × Option (Fin 3)),
      links hv=pre++(j,reset0Destination hv j)::suf ∧
      (∀ l∈suf,j≠l.1) ∧
      (∀ k, reset0Destination hv j=some k →
        (hv=true→k≠0) ∧ ∀ l∈suf,some k≠l.2) := by
  have J : j=0 ∨ j=1 ∨ j=2 := by
    have A := j.isLt
    have B (z : Fin 3) : j.val=z.val → j=z := Fin.ext
    by_cases E : j.val=0
    · exact .inl (B 0 E)
    · by_cases E' : j.val=1
      · exact .inr (.inl (B 1 E'))
      · exact .inr (.inr (B 2 (by omega)))
  rcases J with rfl|rfl|rfl <;> cases hv
  · refine ⟨[],[(1,some 1),(2,some 2)],rfl,?_,?_⟩
    · decide
    · decide
  · refine ⟨[],[(1,some 2),(2,none)],rfl,?_,?_⟩
    · decide
    · decide
  · refine ⟨[(0,some 0)],[(2,some 2)],rfl,?_,?_⟩
    · decide
    · decide
  · refine ⟨[(0,some 1)],[(2,none)],rfl,?_,?_⟩
    · decide
    · decide
  · refine ⟨[(0,some 0),(1,some 1)],[],rfl,?_,?_⟩
    · decide
    · decide
  · refine ⟨[(0,some 1),(1,some 2)],[],rfl,?_,?_⟩
    · decide
    · decide

private theorem reset0_compKSame (p : Params) (j : Fin 3)
    (a : Patch (workW p)) (u : BitVec p.w) (t : Tok) :
    resetTokenRead p ((widen p (a.compose (writeK p j t))).apply u) j=resetTokenWire p t := by
  rw [reset0_widen_apply]
  exact reset0_read_kSame p j t _

private theorem reset0_at_hop (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3 → Bool) (a : Pair (Patch (workW p))) (j k : Fin 3)
    (H : oldK p hu u j=reset0Forward) :
    let b := cmtRoute p hu hv u v win a (j,some k)
    resetTokenRead p ((widen p b.1).apply u) j=resetTokenWire p T ∧
      resetTokenRead p ((widen p b.2).apply v) k=resetTokenWire p reset0Forward := by
  rcases a with ⟨a,b⟩
  dsimp only
  rw [reset0_route_hop p hu hv u v win a b j k H]
  exact ⟨reset0_compKSame p j _ u T,reset0_compKSame p k b v reset0Forward⟩

private theorem reset0_at_turn (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3 → Bool) (a : Pair (Patch (workW p))) (j : Fin 3)
    (H : oldK p hu u j=reset0Forward) :
    let b := cmtRoute p hu hv u v win a (j,none)
    resetTokenRead p ((widen p b.1).apply u) j=resetTokenWire p reset0Reply := by
  rcases a with ⟨a,b⟩
  dsimp only
  rw [reset0_route_turn p hu hv u v win a b j H]
  exact reset0_compKSame p j _ u reset0Reply

theorem reset0_row_hop (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (H : publicationToken p hu u j=reset0Forward)
    (K : reset0Destination hv j=some k) :
    resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j=resetTokenWire p T ∧
      resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k=resetTokenWire p reset0Forward := by
  obtain ⟨pre,suf,L,J,R⟩ := reset0_list_split hv j
  obtain ⟨head,port⟩ := R k K
  unfold row
  rw [reset0Unfold]
  dsimp only
  rw [reset0Post_left,reset0Post_right _ _ _ _ _ head,L,List.foldl_append,List.foldl_cons,K,
    reset0_foldL _ _ _ _ _ _ _ _ _ J,reset0_foldR _ _ _ _ _ _ _ _ _ port]
  exact reset0_at_hop p hu hv u v _ _ j k H

theorem reset0_row_turn (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (H : publicationToken p hu u j=reset0Forward)
    (K : reset0Destination hv j=none) :
    resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j=resetTokenWire p reset0Reply := by
  obtain ⟨pre,suf,L,J,_⟩ := reset0_list_split hv j
  unfold row
  rw [reset0Unfold]
  dsimp only
  rw [reset0Post_left,L,List.foldl_append,List.foldl_cons,K,reset0_foldL _ _ _ _ _ _ _ _ _ J]
  exact reset0_at_turn p hu hv u v _ _ j H

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

private theorem reset0_decode_tags (p : Params) (gate : Bool) (tag : Nat)
    (H : tag=2 ∨ tag=3) :
    decode p gate (resetTokenWire p ({tag:=tag} : Tok)) = ({tag:=tag} : Tok) := by
  let n := 7+o p+payW p
  have W : tokenW p=n+2 := by unfold n tokenW; omega
  have lt : tag<4 := by rcases H with H|H <;> omega
  have sh : resetTokenWire p ({tag:=tag} : Tok) =
      (BitVec.ofNat (tokenW p) tag) <<< n := by
    apply BitVec.eq_of_toNat_eq
    unfold resetTokenWire encode
    simp only [Bool.toNat_false,Nat.zero_mul,Nat.add_zero,
      BitVec.toNat_ofNat,BitVec.toNat_shiftLeft]
    rw [Nat.shiftLeft_eq]
    have L : tag < 2^(tokenW p) := by
      have M : (2:Nat)^2≤2^(tokenW p) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    rw [Nat.mod_eq_of_lt L]
  have below (i : Nat) (I : i<n) :
      ((BitVec.ofNat (tokenW p) tag) <<< n).getLsbD i=false := by
    simp [BitVec.getLsbD_shiftLeft,show ¬n≤i by omega]
  have extBelow (i b : Nat) (I : i+b≤n) :
      (((BitVec.ofNat (tokenW p) tag) <<< n).extractLsb' i b)=0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j J
    simp [J,below (i+j) (by omega)]
  have extTag :
      (((BitVec.ofNat (tokenW p) tag) <<< n).extractLsb' n 2)=BitVec.ofNat 2 tag := by
    apply BitVec.eq_of_getLsbD_eq
    intro j J
    have K : n+j<tokenW p := by omega
    have JD : j<tokenW p := by omega
    simp [J,K,show ¬n+j<n by omega]
    simp [BitVec.getElem_eq_testBit_toNat, Nat.testBit_mod_two_pow,JD,Nat.mod_eq_of_lt lt]
  rw [sh]
  unfold decode
  dsimp only
  unfold get
  have A : (payW p+6)+o p≤n := by unfold n; omega
  have B : payW p+3+3≤n := by unfold n; omega
  have C : payW p+1+2≤n := by unfold n; omega
  have D : 0+payW p≤n := by unfold n; omega
  have E : 6+o p+payW p<n := by unfold n; omega
  rw [extTag,extBelow _ _ A,extBelow _ _ B,extBelow _ _ C,extBelow _ _ D,below _ E]
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt lt]
  rcases H with rfl|rfl <;>
    simp [admitOp,acqOp,cmpOp,sealOp,commitOp,writeOp,
      show ¬p.digits + 3 ≤ 0 by omega]

theorem reset0_decode_forward (p : Params) (gate : Bool) :
    decode p gate (resetTokenWire p reset0Forward)=reset0Forward :=
  reset0_decode_tags p gate 2 (.inl rfl)

theorem reset0_decode_reply (p : Params) (gate : Bool) :
    decode p gate (resetTokenWire p reset0Reply)=reset0Reply :=
  reset0_decode_tags p gate 3 (.inr rfl)

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def pulseApply (p : Params) (h : Bool) (side : Nat) (x : BitVec p.w) : BitVec p.w :=
  (pulseWiden p (pulse p h side x)).apply x

private theorem pulseBase (p : Params) (a : Patch (workW p)) (A : lowFrame p a)
    (h : Bool) (side : Nat) (x : BitVec p.w) (i : Nat) (I : i<tail p) :
    ((pulseWiden p (a.compose (pulse p h side x))).apply x).getLsbD i =
      ((pulseWiden p (pulse p h side x)).apply x).getLsbD i := by
  rw [pulse_widen_apply]
  cases hmask : (pulseWiden p (pulse p h side x)).mask.getLsbD i
  · rw [Patch.hold _ _ _ hmask,Patch.hold _ _ _ hmask]
    exact pulse_widen_frame p _ _ _ (A i I)
  · rw [Patch.write _ _ _ hmask,Patch.write _ _ _ hmask]

/-- Every low work bit of the responder equals the incoming pulse patch on old bytes. -/
theorem row_right_pulse_bits (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (i : Nat) (I : i<tail p) :
    ((row p (hu,hv) (u,v)).2.apply v).getLsbD i =
      (pulseApply p hv 1 v).getLsbD i := by
  unfold row pulseApply
  rw [cmtUnfold]
  dsimp only
  have clear : lowFrame p (((reset p).compose (writeSeal p none)).compose (grants p fun _=>false)) :=
    lowComp (lowComp (lowField p _ _ _ (by unfold sourceBase; omega)) (lowSeal p _)) (lowGrants p _)
  have base : lowFrame p (if hv then
      if gBit p v 1 && (gBit p v 0 || gBit p v 2) then grants p (canonical p v) else .empty _
      else ((reset p).compose (writeSeal p none)).compose (grants p fun _=>false)) := by
    split
    · split
      · exact lowGrants p _
      · exact lowEmpty p
    · exact clear
  have src := lowSource p v (oldK p hv v 0)
  have dest : lowFrame p (match (source p v (oldK p hv v 0)).2 with
      | none => .empty _ | some t=>writeK p 0 t) := by
    split
    · exact lowEmpty p
    · exact lowK p _ _
  have norm (a : Patch (workW p)) :
      ((pulseWiden p (((a.compose (cmtNorm p hv v 0)).compose (cmtNorm p hv v 1)).compose
          (cmtNorm p hv v 2))).apply v).getLsbD i=((pulseWiden p a).apply v).getLsbD i :=
    (lowComposeRead p _ _ v (lowNorm p hv v 2) i I).trans
      ((lowComposeRead p _ _ v (lowNorm p hv v 1) i I).trans
        (lowComposeRead p _ _ v (lowNorm p hv v 0) i I))
  change ((pulseWiden p _).apply v).getLsbD i=_
  split
  · rename_i H
    dsimp only
    rw [lowComposeRead p _ _ v dest i I,lowComposeRead p _ _ v src i I,
      lowFoldR p u v hu hv _ _ _ i I,norm]
    exact pulseBase p _ (by simpa only [if_pos H] using base) _ _ _ _ I
  · rename_i H
    rw [lowFoldR p u v hu hv _ _ _ i I,norm]
    exact pulseBase p _ (by simpa only [if_neg H] using base) _ _ _ _ I

private theorem lowIfLeft (p : Params) (P : Prop) [Decidable P]
    (a b : Patch (workW p) × Patch (workW p) × Tok)
    (A : lowFrame p a.1) (B : lowFrame p b.1) :
    lowFrame p (if P then a else b).1 := by
  split
  · exact A
  · exact B

private theorem lowEffectL (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) (t : Tok) :
    lowFrame p (effect p u v hu hv j k win t).1 := by
  have B (ix n val : Nat) : lowFrame p (field p (bankOffset p ix) n val) :=
    lowField p _ _ _ (by unfold bankOffset sealBase sourceBase; omega)
  let em := lowEmpty p
  unfold effect
  dsimp only
  apply lowIfLeft
  · exact em
  apply lowIfLeft
  · apply lowIfLeft <;> exact em
  apply lowIfLeft
  · exact em
  apply lowIfLeft
  · exact lowSeal p _
  apply lowIfLeft
  · exact em
  apply lowIfLeft
  · exact em
  apply lowIfLeft
  · apply lowIfLeft
    · exact em
    · exact B _ _ _
  apply lowIfLeft
  · apply lowIfLeft
    · exact lowSeal p _
    · exact em
  · exact em

private theorem lowRouteL (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (win : Fin 3 → Bool) (ab : Pair (Patch (workW p))) (l : Fin 3 × Option (Fin 3))
    (i : Nat) (I : i<tail p) :
    ((pulseWiden p (cmtRoute p hu hv u v win ab l).1).apply u).getLsbD i=
      ((pulseWiden p ab.1).apply u).getLsbD i := by
  rcases ab with ⟨a,b⟩
  rcases l with ⟨j,k⟩
  have E (port : Option (Fin 3)) :=
    lowEffectL p u v hu hv j port (win j) (oldK p hu u j)
  unfold cmtRoute
  dsimp only
  split
  · cases k with
    | none =>
      let ep := effect p u v hu hv j none (win j) (oldK p hu u j)
      let aft := writeK p j (terminal p ep.2.2)
      change ((pulseWiden p ((a.compose ep.1).compose aft)).apply u).getLsbD i=_
      exact (lowComposeRead p (a.compose ep.1) aft u (lowK p _ _) i I).trans
        (lowComposeRead p a ep.1 u (E none) i I)
    | some k =>
      let ep := effect p u v hu hv j (some k) (win j) (oldK p hu u j)
      let aft := writeK p j MISByteCodec.T
      change ((pulseWiden p ((a.compose ep.1).compose aft)).apply u).getLsbD i=_
      exact (lowComposeRead p (a.compose ep.1) aft u (lowK p _ _) i I).trans
        (lowComposeRead p a ep.1 u (E (some k)) i I)
  · split
    · rfl
    · cases k with
      | none =>
        change ((pulseWiden p (if (oldK p hu u j).tag==1 then a.compose (writeK p j MISByteCodec.E) else a)).apply u).getLsbD i=_
        split
        · exact lowComposeRead p a (writeK p j MISByteCodec.E) u (lowK p j _) i I
        · rfl
      | some k =>
        let t := oldK p hu u j
        let reply := oldK p hv v k
        by_cases J : (reply.tag==3)=true
        · simp only [show ((oldK p hv v k).tag==3)=true from J,if_pos]
          exact lowComposeRead p a (writeK p j reply) u (lowK p j _) i I
        · simp only [show ¬((oldK p hv v k).tag==3)=true from J,Bool.false_eq_true,if_false]
          by_cases K : (t.tag==1 && reply.tag==0)=true
          · simp only [show (((oldK p hu u j).tag==1) && ((oldK p hv v k).tag==0))=true from K,if_pos]
            exact lowComposeRead p a (writeK p j MISByteCodec.E) u (lowK p j _) i I
          · simp only [show ¬(((oldK p hu u j).tag==1) && ((oldK p hv v k).tag==0))=true from K,Bool.false_eq_true,if_false]

private theorem lowFoldL (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (win : Fin 3 → Bool) (xs : List (Fin 3 × Option (Fin 3)))
    (ab : Pair (Patch (workW p))) (i : Nat) (I : i<tail p) :
    ((pulseWiden p (xs.foldl (cmtRoute p hu hv u v win) ab).1).apply u).getLsbD i=
      ((pulseWiden p ab.1).apply u).getLsbD i := by
  induction xs generalizing ab with
  | nil => rfl
  | cons l xs ih => exact (ih _).trans (lowRouteL p u v hu hv win ab l i I)

private theorem lowLeftNorm (p : Params) (hu : Bool) (u : BitVec p.w) (j : Fin 3) :
    lowFrame p (if (oldK p hu u j).fault then writeK p j (oldK p hu u j)
      else if parked p (oldK p hu u j) hu u j &&
           ((oldK p hu u j).race==1 || (oldK p hu u j).race==2)
        then writeK p j (advanceRace (oldK p hu u j) 3) else .empty _) := by
  split
  · exact lowK p _ _
  split
  · exact lowK p _ _
  · exact lowEmpty p

/-- Every low work bit of the initiator equals the outgoing pulse patch on old bytes. -/
theorem row_left_pulse_bits (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (i : Nat) (I : i<tail p) :
    ((row p (hu,hv) (u,v)).1.apply u).getLsbD i =
      (pulseApply p hu 2 u).getLsbD i := by
  unfold row pulseApply
  rw [cmtUnfold]
  dsimp only
  have clear : lowFrame p (((reset p).compose (writeSeal p none)).compose (grants p fun _=>false)) :=
    lowComp (lowComp (lowField p _ _ _ (by unfold sourceBase; omega)) (lowSeal p _)) (lowGrants p _)
  have base (gg : Fin 3 → Bool) : lowFrame p (if hu then grants p gg else
      ((reset p).compose (writeSeal p none)).compose (grants p fun _=>false)) := by
    split
    · exact lowGrants p _
    · exact clear
  have norm (a : Patch (workW p)) :
      let f := fun j => if (oldK p hu u j).fault then writeK p j (oldK p hu u j)
        else if parked p (oldK p hu u j) hu u j &&
             ((oldK p hu u j).race==1 || (oldK p hu u j).race==2)
          then writeK p j (advanceRace (oldK p hu u j) 3) else .empty _
      ((pulseWiden p (((a.compose (f 0)).compose (f 1)).compose (f 2))).apply u).getLsbD i=
      ((pulseWiden p a).apply u).getLsbD i :=
    (lowComposeRead p _ _ u (lowLeftNorm p hu u 2) i I).trans
      ((lowComposeRead p _ _ u (lowLeftNorm p hu u 1) i I).trans
        (lowComposeRead p _ _ u (lowLeftNorm p hu u 0) i I))
  change ((pulseWiden p _).apply u).getLsbD i=_
  split
  · dsimp only
    rw [lowFoldL p u v hu hv _ _ _ i I,norm]
    exact pulseBase p _ (base _) _ _ _ _ I
  · rw [lowFoldL p u v hu hv _ _ _ i I,norm]
    exact pulseBase p _ (base _) _ _ _ _ I

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 300000

def oldReportToken (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3) : Tok :=
  oldK p h x j

def reportOldGrant (p : Params) (x : BitVec p.w) (j : Fin 3) : Bool := gBit p x j

def reportOldSeal (p : Params) (x : BitVec p.w) : Option Nat := readSeal p x

def reportOldOffset (p : Params) (h : Bool) (x : BitVec p.w) : Nat := geomOff p h x

def packetCommitGuard (p : Params) (v : BitVec p.w) (t : Tok) : Bool :=
  !t.applied && gBit p v 1 && selected p v==t.payload/8 && readSeal p v==some t.payload

theorem commit_effect_snapshot (p : Params) (hu w : Bool)
    (u v : BitVec p.w) (t : Tok) (op : t.opcode=commitOp p) (live : t.fault=false) :
    effect p u v hu true 0 (some 1) w t =
      if packetCommitGuard p v t then
        (.empty _, cmtPatch p v t.payload, {t with applied:=true})
      else (.empty _,.empty _,F 2) := by
  simp [effect,packetCommitGuard,cmtPatch,op,live]

/-- The local ACQUIRE effect is a function of the old selected header,
and denial only changes payload bit six. -/
theorem acquire_capture_old (p : Params) (hv : Bool)
    (u v : BitVec p.w) (j : Fin 3) (k : Option (Fin 3))
    (w : Bool) (t : Tok) (op : t.opcode=acqOp p) (live : t.fault=false) :
    effect p u v true hv j k w t =
      (.empty _,.empty _,{t with payload :=
        (if w then (writeBit (writeBit t.payload (5-j.val) (selected p u==1))
          (2-j.val) (aBit p u (selected p u)))
        else (writeBit t.payload 6 false))}) := by
  have C : acqOp p ≠ commitOp p := by unfold acqOp commitOp; omega
  have A : acqOp p ≠ admitOp p := by unfold acqOp admitOp; omega
  have Z : acqOp p ≠ 0 := by unfold acqOp; omega
  simp [effect,parked,op,live,C,A,Z]

/-- A digit reader at the actual old offset changes exactly its half
of the forward payload, using the packet's captured bank index. -/
theorem reader_digit_old (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (j : Fin p.digits) (port : Fin 3) (k : Option (Fin 3))
    (w : Bool) (t : Tok) (P : port=0 ∨ port=2)
    (H : reportOldOffset p hu u=j.val) (live : t.fault=false)
    (op : t.opcode=cmpOp p+j.val ∨ t.opcode=readOp p+j.val) :
    let ix := if port=0 then bit t.payload (2*d p+1) else bit t.payload (2*d p)
    let shift := if port=0 then d p else 0
    let dg := min (p.beta-1) (get u (bankOffset p ix.toNat+shift) (d p))
    let old := (t.payload/2^shift)%2^(d p)
    effect p u v hu hv port k w t =
      (.empty _,.empty _,{t with payload:=t.payload-old*2^shift+dg*2^shift}) := by
  have J := j.isLt
  have C : t.opcode≠commitOp p := by unfold cmpOp readOp commitOp at *; omega
  have A : t.opcode≠admitOp p := by unfold cmpOp readOp admitOp at *; omega
  have K : t.opcode≠acqOp p := by unfold cmpOp readOp acqOp at *; omega
  have R : cmpOp p≤t.opcode ∧ t.opcode<writeOp p := by
    unfold cmpOp readOp writeOp at *; omega
  have O : geomOff p hu u=t.opcode-(if t.opcode<readOp p then cmpOp p else readOp p) := by
    change geomOff p hu u=j.val at H
    rw [H]
    rcases op with L|L
    · rw [if_pos (by unfold readOp cmpOp at *; omega)]
      omega
    · rw [if_neg (by omega)]
      omega
  rcases P with P|P <;> subst port <;>
    simp [effect,parked,live,C,A,K,R.1,R.2,O]

/-- The local WRITE patch has the exact staged bank/digit footprint.
At a nonheader the old grant/selector branch is intentionally bypassed. -/
theorem write_digit_old (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (j : Fin p.digits) (k : Option (Fin 3))
    (w : Bool) (t : Tok) (H : reportOldOffset p hu u=j.val)
    (live : t.fault=false) (op : t.opcode=writeOp p+j.val)
    (permit : hu=false ∨
      (reportOldGrant p u 1=true ∧ publicationSelector p u=t.payload/2^(2*d p+1))) :
    effect p u v hu hv 1 k w t =
      (field p (bankOffset p ((t.payload/2^(2*d p))%2)) (2*d p)
        (t.payload%2^(2*d p)),.empty _,t) := by
  have J := j.isLt
  have C : t.opcode≠commitOp p := by unfold writeOp commitOp at *; omega
  have A : t.opcode≠admitOp p := by unfold writeOp admitOp at *; omega
  have K : t.opcode≠acqOp p := by unfold writeOp acqOp at *; omega
  have Z0 : t.opcode≠0 := by unfold writeOp at *; omega
  have R : writeOp p≤t.opcode ∧ t.opcode<sealOp p := by
    unfold writeOp sealOp at *; omega
  have O : geomOff p hu u=t.opcode-writeOp p := by
    change geomOff p hu u=j.val at H
    omega
  rcases permit with L|⟨G,S⟩
  · subst hu
    simp [effect,parked,live,C,A,K,Z0,R.1,R.2,O]
  · change gBit p u 1=true at G
    change selected p u=t.payload/2^(2*d p+1) at S
    simp [effect,parked,live,C,A,K,Z0,R.1,R.2,O,G,S]

theorem seal_effect_old (p : Params) (hv : Bool) (u v : BitVec p.w)
    (k : Option (Fin 3)) (w : Bool) (t : Tok)
    (live : t.fault=false) (op : t.opcode=sealOp p) :
    effect p u v true hv 1 k w t =
      if reportOldGrant p u 1 && publicationSelector p u==t.payload/8 then
        (writeSeal p (some t.payload),.empty _,t) else (.empty _,.empty _,F 2) := by
  have C : sealOp p≠commitOp p := by unfold sealOp commitOp; omega
  have A : sealOp p≠admitOp p := by unfold sealOp admitOp; omega
  have K : sealOp p≠acqOp p := by unfold sealOp acqOp; omega
  have Z0 : sealOp p≠0 := by unfold sealOp; omega
  have R : ¬sealOp p<writeOp p := by unfold writeOp sealOp; omega
  simp [effect,parked,live,op,C,A,K,Z0,R,reportOldGrant,publicationSelector]

theorem terminal_commit_requires_applied (p : Params) (t : Tok)
    (op : t.opcode=commitOp p) :
    terminal p t =
      if t.fault || !t.applied then F 3 else {tag:=3,opcode:=commitOp p} := by
  have A : commitOp p≠acqOp p := by unfold commitOp acqOp; omega
  have B : commitOp p≠admitOp p := by unfold commitOp admitOp; omega
  have C : ¬commitOp p<writeOp p := by unfold commitOp writeOp; omega
  simp [terminal,op,A,B,C]

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

private theorem q12781_extract_congr (p : Params) (a b : BitVec p.w) (k w : Nat)
    (R : k+w≤workW p)
    (H : ∀ i, i<workW p → a.getLsbD i=b.getLsbD i) :
    a.extractLsb' k w=b.extractLsb' k w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  simp only [BitVec.getLsbD_extractLsb', I, decide_true, Bool.true_and]
  exact H _ (by omega)

theorem publication_work_congr (p : Params) (a b : BitVec p.w) (ix : Nat)
    (H : ∀ i, i<workW p → a.getLsbD i=b.getLsbD i) :
    publicationSelector p a=publicationSelector p b ∧
      publicationA p a ix=publicationA p b ix ∧
      publicationPair p a ix=publicationPair p b ix ∧ Z p a=Z p b := by
  have S := q12781_extract_congr p a b (grantBase p+3) 1 (by unfold workW; omega) H
  have B := q12781_extract_congr p a b (bankOffset p ix) (bankW p)
    (by
      have L : 1-ix≤1 := by omega
      have M := Nat.mul_le_mul_right (bankW p) L
      unfold bankOffset workW grantBase
      simp only [Nat.one_mul] at M
      omega) H
  have C : stored p a ix=stored p b ix := congrArg BitVec.toNat B
  refine ⟨congrArg BitVec.toNat S,?_,?_,?_⟩
  · simp only [publicationA,aBit,C]
  · simp only [publicationPair,bPair,C]
  · exact H _ (by unfold workW grantBase sealBase sourceBase tail; omega)

theorem row_left_Z (p : Params) (hu hv : Bool) (u v : BitVec p.w) :
    Z p ((row p (hu,hv) (u,v)).1.apply u) =
      if paints p hu 2 u then publicationPair p u (publicationSelector p u)==0 else Z p u := by
  have H := row_left_pulse_bits p hu hv u v (ell p.streak+2) (by unfold tail; omega)
  exact H.trans (pulse_Z_from_old p hu 2 u u)

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxHeartbeats 3000000

def reportDigitPair (p : Params) (x : BitVec p.w) (ix : Nat) : BitVec (2*d p) :=
  x.extractLsb' (bankOffset p ix) (2*d p)

private theorem cmt_digit_frame (p : Params) (v : BitVec p.w) (dsc ix j : Nat)
    (J : j<2*d p) :
    (cmtPatch p v dsc).mask.getLsbD (bankOffset p ix+j)=false := by
  let i := bankOffset p ix+j
  let dest := (dsc/4)%2
  have L : 1-ix≤1 := by omega
  have M := Nat.mul_le_mul_right (bankW p) L
  simp only [Nat.one_mul] at M
  have A : i<grantBase p := by unfold i bankOffset grantBase bankW at *; omega
  have B : sealBase p+5≤i := by unfold i bankOffset; omega
  have D : i<bankOffset p dest+2*d p ∨ bankOffset p dest+2*d p+3≤i := by
    have Dst : dest≤1 := by unfold dest; omega
    have I0 : 1-ix=0 ∨ 1-ix=1 := by omega
    have I1 : 1-dest=0 ∨ 1-dest=1 := by omega
    unfold i bankOffset bankW
    rcases I0 with P|P <;> rcases I1 with Q|Q <;> simp [P,Q] <;> omega
  unfold cmtPatch
  apply pulse_comp_out
  · apply pulse_comp_out
    · exact pulse_field_out p _ _ _ _ (.inl (by omega))
    · exact pulse_field_out p _ _ _ _ (.inr B)
  · exact pulse_field_out p _ _ _ _ D

/-- Even an accepted COMMIT frames both staged digit fields on its right
physical site, through all three links, pulse and source postpatch. -/
theorem commit_keeps_digit_pair (p : Params) (hu : Bool) (u v : BitVec p.w)
    (dsc ix : Nat) (G : CommitGuard p hu u v dsc) :
    reportDigitPair p ((row p (hu,true) (u,v)).2.apply v) ix=reportDigitPair p v ix := by
  apply BitVec.eq_of_getLsbD_eq
  intro j J
  let i := bankOffset p ix+j
  have L : 1-ix≤1 := by omega
  have M := Nat.mul_le_mul_right (bankW p) L
  simp only [Nat.one_mul] at M
  have A : i<grantBase p := by unfold i bankOffset grantBase bankW at *; omega
  have B : sealBase p+5≤i := by unfold i bankOffset; omega
  have I : cmtIndex p i := .inl ⟨B,A⟩
  have E : i<workW p := cmtWork p i I
  have W := layout_size p
  have inW : i<p.w := by omega
  simp only [reportDigitPair,BitVec.getLsbD_extractLsb',J,decide_true,Bool.true_and]
  change ((row p (hu,true) (u,v)).2.apply v).getLsbD i=v.getLsbD i
  apply Patch.hold
  unfold row widen
  simp only [BitVec.getLsbD_setWidth, inW, decide_true, Bool.true_and]
  rw [cmtUnfold]
  simp only [links, if_true, List.foldl_cons, List.foldl_nil]
  cases HS : (source p v (oldK p true v 0)) with
  | mk srcP srcT =>
  have S : cmtFrame p srcP := by
    have T := cmtSource p v (oldK p true v 0)
    rwa [HS] at T
  have K := cmtSourceToken p srcT
  dsimp only
  rw [(cmtMask_after p i I _ _ K).1,(cmtMask_after p i I _ _ S).1]
  rw [(cmtRouteOther p _ _ _ _ _ _ _ (2 : Fin 3) none (by decide) i I).1,
    (cmtRouteOther p _ _ _ _ _ _ _ (1 : Fin 3) (some 2) (by decide) i I).1]
  rw [cmtCore p hu u v dsc G]
  rw [(cmtMask_after p i I _ _ (cmtK p 1 _)).1]
  have F : (cmtPatch p v dsc).mask.getLsbD i=false :=
    cmt_digit_frame p v dsc ix j J
  have N (k : Fin 3) : cmtFrame p (cmtNorm p true v k) := by
    unfold cmtNorm
    dsimp only
    split
    · exact cmtK p _ _
    split
    · exact cmtK p _ _
    · exact cmtEmpty p
  have P := pulse_mask_below_tail p true 1 v i (by unfold sealBase sourceBase at B; omega)
  have G0 : (grants p (canonical p v)).mask.getLsbD i=false :=
    pulse_field_out p _ _ _ _ (.inl A)
  have Q : (if gBit p v 1 && (gBit p v 0 || gBit p v 2)
      then grants p (canonical p v) else .empty _).mask.getLsbD i=false := by
    split
    · exact G0
    · simp [Patch.empty]
  exact pulse_comp_out (pulse_comp_out (pulse_comp_out
    (pulse_comp_out (pulse_comp_out Q P) (N 0 i I)) (N 1 i I)) (N 2 i I)) F

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

/-- A proof-facing token view, with the same old-token definition as the router. -/
def healthyAdmit (p : Params) (t : Tok) : Prop :=
  t.tag=2 ∧ t.fault=false ∧ t.opcode=admitOp p

def admitRaceAfter (side race : Nat) : Nat :=
  if race=1 then side else
    if (side=2 ∧ race=3) ∨ (side=3 ∧ race=2) then race+2 else race

def admitNormalize (side : Nat) (t : Tok) : Tok :=
  {t with race:=admitRaceAfter side t.race}

private theorem healthy_admit_parked (p : Params) (u : BitVec p.w) (hu : Bool)
    (j : Fin 3) (t : Tok) (H : healthyAdmit p t) (G : gate p hu u j=true) :
    parked p t hu u j=true := by
  rcases H with ⟨T,F,O⟩
  simp [parked,T,F,O,G]

theorem admit_ready_at_gate (p : Params) (u : BitVec p.w) (hu : Bool)
    (j : Fin 3) (t : Tok) (H : healthyAdmit p t) (G : gate p hu u j=true) :
    ready p hu u j t = decide (4≤t.race) := by
  rw [ready,healthy_admit_parked p u hu j t H G]
  by_cases J : t.race<4
  · have K : ¬4≤t.race := by omega
    simp [H.1,J,K]
  · have K : 4≤t.race := by omega
    simp [H.1,J,K]

theorem admit_arrives_race1 (p : Params) (u : BitVec p.w) (hu : Bool)
    (j : Fin 3) (t : Tok) (H : healthyAdmit p t) (G : gate p hu u j=true) :
    arrival p hu u j t={t with race:=1} := by
  simp [arrival,H.2.1,H.2.2,G]

theorem admit_departure_effect (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) (t : Tok)
    (H : healthyAdmit p t) (G : gate p hu u j=true) :
    effect p u v hu hv j k win t=
      (.empty _, .empty _, {t with race:=0,payload:=t.race-4}) := by
  have E : admitOp p ≠ commitOp p := by unfold admitOp commitOp; omega
  simp [effect,H.2.1,H.2.2,E,healthy_admit_parked p u hu j t H G]

/-- Actual old-byte normalization on a responder: side 2. -/
theorem admit_incoming_normalization (p : Params) (h : Bool) (x : BitVec p.w)
    (j : Fin 3) (H : healthyAdmit p (oldK p h x j))
    (G : gate p h x j=true) :
    cmtNorm p h x j =
      if (oldK p h x j).race=1 ∨ (oldK p h x j).race=3 then
        writeK p j (admitNormalize 2 (oldK p h x j)) else .empty _ := by
  unfold cmtNorm
  dsimp only
  rw [healthy_admit_parked p x h j _ H G]
  by_cases J : (oldK p h x j).race=1
  · simp [H.2.1,J,advanceRace,admitNormalize,admitRaceAfter]
  · by_cases K : (oldK p h x j).race=3
    · simp [H.2.1,K,advanceRace,admitNormalize,admitRaceAfter]
    · simp [H.2.1,J,K]

/-- The selected orientation cannot re-arm its forbidden label using only the
desired incidence. Any full trace using both rows must include the opposite
incidence before current parked ADMIT is ready to depart. -/
theorem admit_opposite_required :
    admitRaceAfter 3 1=3 ∧ admitRaceAfter 3 3=3 ∧ admitRaceAfter 2 3=5 ∧
    admitRaceAfter 2 1=2 ∧ admitRaceAfter 2 2=2 ∧ admitRaceAfter 3 2=4 := by decide

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

/-- These parameters are the old ACQ and RELEASE request bits, not any
post-mark grant observation. -/
def winOld (p : Params) (u : BitVec p.w) (ask rel : Fin 3 → Bool) (j : Fin 3) : Bool :=
  let w := !canonical p u 0 && !canonical p u 1 && !canonical p u 2 && ask 1 && !rel 1
  if j==1 then w else !w && !canonical p u 1 && ask j && !canonical p u j && !rel j

theorem old_grant_free_wins (p : Params) (x : BitVec p.w) (ask rel : Fin 3 → Bool)
    (j : Fin 3) (free : ∀ k, gBit p x k=false) (query : ask j=true) (norel : rel j=false)
    (rival : j≠1 → ask 1=false) : winOld p x ask rel j=true := by
  have C (k : Fin 3) : canonical p x k=false := by simp [canonical,free]
  by_cases J : j=1
  · subst j
    simp [winOld,C,query,norel]
  · simp [winOld,C,J,query,norel,rival J]

theorem old_grant_free_no_query (p : Params) (x : BitVec p.w) (ask rel : Fin 3 → Bool)
    (j : Fin 3) (free : ∀ k, gBit p x k=false) (query : ask j=false) :
    ((canonical p x j && !rel j) || winOld p x ask rel j)=false := by
  have C (k : Fin 3) : canonical p x k=false := by simp [canonical,free]
  by_cases J : j=1
  · subst j
    simp [winOld,C,query]
  · simp [winOld,C,J,query]

/-- The source reads the returned old D, not a race increment or a newly
arrived reply on this mark. A denial emits no ACQ. -/
theorem admit_source_consume (p : Params) (x : BitVec p.w) (t : Tok)
    (phase : sourcePhase p x=2) (op : sourceOpcode p x=admitOp p)
    (T : t.tag=3) (O : t.opcode=admitOp p) (F : t.fault=false) (Q : t.outcome=0) :
    source p x t = if t.payload=1 then (ctrl p 1 (acqOp p),some E) else (reset p,some E) := by
  have P : ¬ commitOp p<admitOp p := by unfold commitOp admitOp; omega
  have A : admitOp p≠0 := by unfold admitOp; omega
  unfold sourcePhase at phase
  unfold sourceOpcode at op
  simp [source,phase,op,P,A,T,O,F,Q]

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol
/-- Exactly the outgoing normalization lambda of the body before routing. -/
private def outgoingNormalize (p : Params) (h : Bool) (x : BitVec p.w)
    (j : Fin 3) : Patch (workW p) :=
  let t := oldK p h x j
  if t.fault then writeK p j t
  else if parked p t h x j && (t.race==1 || t.race==2) then writeK p j (advanceRace t 3)
  else .empty _

theorem admit_outgoing_normalization (p : Params) (h : Bool) (x : BitVec p.w)
    (j : Fin 3) (H : healthyAdmit p (oldK p h x j)) (G : gate p h x j=true) :
    outgoingNormalize p h x j =
      if (oldK p h x j).race=1 ∨ (oldK p h x j).race=2 then
        writeK p j (admitNormalize 3 (oldK p h x j)) else .empty _ := by
  unfold outgoingNormalize
  dsimp only
  rw [healthy_admit_parked p x h j _ H G]
  by_cases J : (oldK p h x j).race=1
  · simp [H.2.1,J,advanceRace,admitNormalize,admitRaceAfter]
  · by_cases K : (oldK p h x j).race=2
    · simp [H.2.1,K,advanceRace,admitNormalize,admitRaceAfter]
    · simp [H.2.1,J,K]

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

/-- Any router effect at this link stutters when a parked initiator
is not ready in OLD bytes. In particular the marking edge that takes
race 2 to race 4 cannot perform the departure itself. -/
theorem admit_outgoing_old_not_ready (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3 → Bool) (ab : Pair (Patch (workW p))) (j : Fin 3) (k : Option (Fin 3))
    (H : healthyAdmit p (oldK p hu u j)) (G : gate p hu u j=true)
    (R : (oldK p hu u j).race<4) :
    cmtRoute p hu hv u v win ab (j,k)=ab := by
  have E := admit_ready_at_gate p u hu j _ H G
  have N : ¬4≤(oldK p hu u j).race := by omega
  cases ab with
  | mk a b =>
    simp [cmtRoute,E,N,H.1]

/-- The receiving gate normalization is not overwritten by this
link on an old T predecessor. The old gate F is neither E nor D.
Without a not-ready premise an inherited upstream F can overwrite it. -/
theorem admit_incoming_old_not_overwritten (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3 → Bool) (ab : Pair (Patch (workW p))) (j k : Fin 3)
    (H : healthyAdmit p (oldK p hv v k))
    (R : ready p hu u j (oldK p hu u j)=false) :
    cmtRoute p hu hv u v win ab (j,some k)=ab := by
  cases ab with
  | mk a b =>
    simp [cmtRoute,R,H.1]

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

private def gFrame (p : Params) (q : Patch (workW p)) : Prop :=
  ∀ i, grantBase p≤i ∧ i<grantBase p+3 → q.mask.getLsbD i=false

private theorem gField (p : Params) (k b v : Nat)
    (H : k+b≤grantBase p ∨ grantBase p+3≤k) : gFrame p (field p k b v) := by
  intro i I
  apply pulse_field_out
  rcases H with H|H
  · exact .inr (by omega)
  · exact .inl (by omega)

private theorem gEarly (p : Params) (k b v : Nat)
    (H : k+b≤sealBase p+5) : gFrame p (field p k b v) :=
  gField p _ _ _ (.inl (by unfold grantBase; omega))
private theorem gEmpty (p : Params) : gFrame p (.empty _) := by
  intro i _
  simp [Patch.empty]

private theorem gCompose {p : Params} {f g : Patch (workW p)}
    (F : gFrame p f) (G : gFrame p g) : gFrame p (f.compose g) := by
  intro i I
  simp [Patch.compose,F i I,G i I]

private theorem gK (p : Params) (j : Fin 3) (t : Tok) :
    gFrame p (writeK p j t) := by
  apply gEarly
  have F := j.isLt
  have G : 2-j.val≤2 := by omega
  have H := Nat.mul_le_mul_right (tokenW p) G
  simp only [kOffset,sealBase,sourceBase]
  omega

private theorem gSeal (p : Params) (n : Option Nat) :
    gFrame p (writeSeal p n) := gEarly p _ _ _ (by omega)

private theorem gReset (p : Params) : gFrame p (reset p) := by
  apply gEarly
  unfold sealBase
  omega

private theorem gCtrl (p : Params) (a b : Nat) : gFrame p (ctrl p a b) := by
  apply gEarly
  unfold pc sealBase sourceW
  omega

private theorem gSF (p : Params) (k b v : Nat) (H : k+b≤sourceW p) :
    gFrame p (sf p k b v) := by
  apply gEarly
  unfold sealBase
  omega

private theorem gIfPair (p : Params) (Q : Prop) [Decidable Q]
    (a b : Patch (workW p) × Option Tok)
    (A : gFrame p a.1) (B : gFrame p b.1) :
    gFrame p (if Q then a else b).1 := by
  by_cases H : Q
  · rwa [if_pos H]
  · rwa [if_neg H]

private theorem gSource (p : Params) (x : BitVec p.w) (t : Tok) :
    gFrame p (source p x t).1 := by
  have C := gCtrl p
  have R := gReset p
  have E := gEmpty p
  have hPhase : gFrame p (field p (pc p+o p) 2 2) := by
    apply gEarly
    unfold pc sealBase sourceW
    omega
  have fld (j b v : Nat) (F : j+b≤21+2*d p) : gFrame p (sf p j b v) :=
    gSF p _ _ _ (by unfold sourceW; omega)
  have hInit (op : Nat) : gFrame p (if op==0 then reset p else .empty _) := by
    split
    · exact R
    · exact E
  unfold source
  dsimp only
  apply gIfPair
  · exact R
  apply gIfPair
  · apply gIfPair
    · exact R
    · exact gCompose (hInit _) hPhase
  apply gIfPair
  · exact E
  apply gIfPair
  · exact R
  apply gIfPair
  · exact C _ _
  apply gIfPair
  · exact C _ _
  apply gIfPair
  · apply gIfPair
    · exact C _ _
    · exact R
  apply gIfPair
  · exact gCompose (gCompose (C _ _) (fld _ _ _ (by omega))) (fld _ _ _ (by omega))
  apply gIfPair
  · apply gIfPair
    · exact R
    apply gIfPair
    · apply gIfPair
      · exact gCompose (C _ _) (fld _ _ _ (by omega))
      · exact gCompose (gCompose (gCompose (C _ _) (fld _ _ _ (by omega)))
          (fld _ _ _ (by omega))) (fld _ _ _ (by omega))
    · exact gCompose (gCompose (gCompose (C _ _) (fld _ _ _ (by omega)))
        (fld _ _ _ (by omega))) (fld _ _ _ (by omega))
  apply gIfPair
  · exact C _ _
  apply gIfPair
  · exact C _ _
  · exact R

private theorem gNorm (p : Params) (hv : Bool) (v : BitVec p.w) (j : Fin 3) :
    gFrame p (cmtNorm p hv v j) := by
  unfold cmtNorm
  dsimp only
  split
  · exact gK p _ _
  split
  · exact gK p _ _
  · exact gEmpty p

private theorem gIfRight (p : Params) (P : Prop) [Decidable P]
    (a b : Patch (workW p) × Patch (workW p) × Tok)
    (A : gFrame p a.2.1) (B : gFrame p b.2.1) :
    gFrame p (if P then a else b).2.1 := by
  split
  · exact A
  · exact B

private theorem gEffectR (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) (t : Tok) :
    gFrame p (effect p u v hu hv j k win t).2.1 := by
  have F (ix : Nat) : (1-ix)*bankW p≤bankW p := by
    simpa using Nat.mul_le_mul_right (bankW p) (Nat.sub_le 1 ix)
  have B (ix val : Nat) : gFrame p (field p (bankOffset p ix+2*d p) 3 val) :=
    gField p _ _ _ (.inl (by have := F ix; unfold bankOffset grantBase bankW at *; omega))
  have G (ix : Nat) : gFrame p (field p (grantBase p+3) 1 ix) :=
    gField p _ _ _ (.inr (by omega))
  let em := gEmpty p
  unfold effect
  dsimp only
  apply gIfRight
  · exact em
  apply gIfRight
  · apply gIfRight
    · exact gCompose (gCompose (G _) (gSeal p _)) (B _ _)
    · exact em
  apply gIfRight
  · exact em
  apply gIfRight
  · exact em
  apply gIfRight
  · exact em
  apply gIfRight
  · exact em
  apply gIfRight
  · apply gIfRight <;> exact em
  apply gIfRight
  · apply gIfRight <;> exact em
  · exact em

private theorem gComposeRead (p : Params) (a b : Patch (workW p)) (x : BitVec p.w)
    (B : gFrame p b) (i : Nat) (I : grantBase p≤i ∧ i<grantBase p+3) :
    ((widen p (a.compose b)).apply x).getLsbD i=((widen p a).apply x).getLsbD i := by
  rw [reset0_widen_apply]
  exact pulse_widen_frame p _ _ i (B i I)

private theorem gRouteR (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (win : Fin 3 → Bool) (ab : Pair (Patch (workW p))) (l : Fin 3 × Option (Fin 3))
    (i : Nat) (I : grantBase p≤i ∧ i<grantBase p+3) :
    ((widen p (cmtRoute p hu hv u v win ab l).2).apply v).getLsbD i=
      ((widen p ab.2).apply v).getLsbD i := by
  rcases ab with ⟨a,b⟩
  rcases l with ⟨j,k⟩
  have E (port : Option (Fin 3)) :=
    gEffectR p u v hu hv j port (win j) (oldK p hu u j)
  unfold cmtRoute
  dsimp only
  split
  · cases k with
    | none => exact gComposeRead p _ _ v (E none) i I
    | some k =>
      let ep := effect p u v hu hv j (some k) (win j) (oldK p hu u j)
      let aft := writeK p k (arrival p hv v k ep.2.2)
      change ((widen p ((b.compose ep.2.1).compose aft)).apply v).getLsbD i=_
      exact (gComposeRead p (b.compose ep.2.1) aft v (gK p _ _) i I).trans
        (gComposeRead p b ep.2.1 v (E (some k)) i I)
  · split
    · rfl
    · cases k with
      | none => rfl
      | some k =>
        by_cases J : ((oldK p hv v k).tag==3)=true
        · simp only [if_pos J]
          exact gComposeRead p b (writeK p k MISByteCodec.E) v (gK p _ _) i I
        · simp only [if_neg J]
          split <;> rfl

private theorem gFoldR (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (win : Fin 3 → Bool) (xs : List (Fin 3 × Option (Fin 3)))
    (ab : Pair (Patch (workW p))) (i : Nat) (I : grantBase p≤i ∧ i<grantBase p+3) :
    ((widen p (xs.foldl (cmtRoute p hu hv u v win) ab).2).apply v).getLsbD i=
      ((widen p ab.2).apply v).getLsbD i := by
  induction xs generalizing ab with
  | nil => rfl
  | cons l xs ih => exact (ih _).trans (gRouteR p u v hu hv win ab l i I)

/-- The entire right raw work row reads its pulse from the old
snapshot. Routing and door operations do not touch the pulse bit. -/
private theorem gIfLeft (p : Params) (P : Prop) [Decidable P]
    (a b : Patch (workW p) × Patch (workW p) × Tok)
    (A : gFrame p a.1) (B : gFrame p b.1) :
    gFrame p (if P then a else b).1 := by
  split
  · exact A
  · exact B

set_option maxHeartbeats 1200000 in
private theorem gEffectL (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) (t : Tok) :
    gFrame p (effect p u v hu hv j k win t).1 := by
  have F (ix : Nat) : (1-ix)*bankW p≤bankW p := by
    simpa using Nat.mul_le_mul_right (bankW p) (Nat.sub_le 1 ix)
  have B (ix val : Nat) : gFrame p (field p (bankOffset p ix) (2*d p) val) :=
    gField p _ _ _ (.inl (by have := F ix; unfold bankOffset grantBase bankW at *; omega))
  let em := gEmpty p
  unfold effect
  dsimp only
  apply gIfLeft
  · exact em
  apply gIfLeft
  · apply gIfLeft <;> exact em
  apply gIfLeft
  · exact em
  apply gIfLeft
  · exact gSeal p _
  apply gIfLeft
  · exact em
  apply gIfLeft
  · exact em
  apply gIfLeft
  · apply gIfLeft
    · exact em
    · exact B _ _
  apply gIfLeft
  · apply gIfLeft
    · exact gSeal p _
    · exact em
  · exact em

private theorem gRouteL (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (win : Fin 3 → Bool) (ab : Pair (Patch (workW p))) (l : Fin 3 × Option (Fin 3))
    (i : Nat) (I : grantBase p≤i ∧ i<grantBase p+3) :
    ((widen p (cmtRoute p hu hv u v win ab l).1).apply u).getLsbD i=
      ((widen p ab.1).apply u).getLsbD i := by
  rcases ab with ⟨a,b⟩
  rcases l with ⟨j,k⟩
  have E (port : Option (Fin 3)) :=
    gEffectL p u v hu hv j port (win j) (oldK p hu u j)
  unfold cmtRoute
  dsimp only
  split
  · cases k with
    | none =>
      let ep := effect p u v hu hv j none (win j) (oldK p hu u j)
      let aft := writeK p j (terminal p ep.2.2)
      change ((widen p ((a.compose ep.1).compose aft)).apply u).getLsbD i=_
      exact (gComposeRead p (a.compose ep.1) aft u (gK p _ _) i I).trans
        (gComposeRead p a ep.1 u (E none) i I)
    | some k =>
      let ep := effect p u v hu hv j (some k) (win j) (oldK p hu u j)
      let aft := writeK p j MISByteCodec.T
      change ((widen p ((a.compose ep.1).compose aft)).apply u).getLsbD i=_
      exact (gComposeRead p (a.compose ep.1) aft u (gK p _ _) i I).trans
        (gComposeRead p a ep.1 u (E (some k)) i I)
  · split
    · rfl
    · cases k with
      | none =>
        change ((widen p (if (oldK p hu u j).tag==1 then a.compose (writeK p j MISByteCodec.E) else a)).apply u).getLsbD i=_
        split
        · exact gComposeRead p a (writeK p j MISByteCodec.E) u (gK p j _) i I
        · rfl
      | some k =>
        let t := oldK p hu u j
        let reply := oldK p hv v k
        by_cases J : (reply.tag==3)=true
        · simp only [show ((oldK p hv v k).tag==3)=true from J,if_pos]
          exact gComposeRead p a (writeK p j reply) u (gK p j _) i I
        · simp only [show ¬((oldK p hv v k).tag==3)=true from J,Bool.false_eq_true,if_false]
          by_cases K : (t.tag==1 && reply.tag==0)=true
          · simp only [show (((oldK p hu u j).tag==1) && ((oldK p hv v k).tag==0))=true from K,if_pos]
            exact gComposeRead p a (writeK p j MISByteCodec.E) u (gK p j _) i I
          · simp only [show ¬(((oldK p hu u j).tag==1) && ((oldK p hv v k).tag==0))=true from K,Bool.false_eq_true,if_false]

private theorem gFoldL (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (win : Fin 3 → Bool) (xs : List (Fin 3 × Option (Fin 3)))
    (ab : Pair (Patch (workW p))) (i : Nat) (I : grantBase p≤i ∧ i<grantBase p+3) :
    ((widen p (xs.foldl (cmtRoute p hu hv u v win) ab).1).apply u).getLsbD i=
      ((widen p ab.1).apply u).getLsbD i := by
  induction xs generalizing ab with
  | nil => rfl
  | cons l xs ih => exact (ih _).trans (gRouteL p u v hu hv win ab l i I)

private theorem gLeftNorm (p : Params) (hu : Bool) (u : BitVec p.w) (j : Fin 3) :
    gFrame p (if (oldK p hu u j).fault then writeK p j (oldK p hu u j)
      else if parked p (oldK p hu u j) hu u j &&
           ((oldK p hu u j).race==1 || (oldK p hu u j).race==2)
        then writeK p j (advanceRace (oldK p hu u j) 3) else .empty _) := by
  split
  · exact gK p _ _
  split
  · exact gK p _ _
  · exact gEmpty p

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

def grantAddr (p : Params) (j : Fin 3) := grantBase p+2-j.val

def grantAsk (p : Params) (h : Bool) (u : BitVec p.w) (op : Nat) (j : Fin 3) : Bool :=
  let t := oldK p h u j
  h && ready p h u j t && !t.fault && t.opcode==op

def grantNext (p : Params) (h : Bool) (u : BitVec p.w) (j : Fin 3) : Bool :=
  if h then (canonical p u j && !grantAsk p h u 0 j) ||
      winOld p u (grantAsk p h u (acqOp p)) (grantAsk p h u 0) j
  else false

def grantReceived (p : Params) (h : Bool) (v : BitVec p.w) (j : Fin 3) : Bool :=
  if h then canonical p v j else false

private theorem gPulse (p : Params) (h : Bool) (side : Nat) (x : BitVec p.w) :
    gFrame p (pulse p h side x) := by
  intro i I
  have H := pulse_mask_below_tail p h side x i
  exact H (by have := I.1; unfold grantBase sealBase sourceBase at *; omega)

private theorem gAddr (p : Params) (j : Fin 3) :
    grantBase p≤grantAddr p j ∧ grantAddr p j<grantBase p+3 := by
  unfold grantAddr
  have := j.isLt
  omega

set_option maxHeartbeats 1500000 in
private theorem gAssign (p : Params) (g : Fin 3 → Bool) (j : Fin 3)
    (a : Patch (workW p)) (u : BitVec p.w) :
    (((widen p (a.compose (grants p g))).apply u).getLsbD (grantAddr p j))=g j := by
  have W := layout_size p
  have I := gAddr p j
  let i := grantAddr p j
  have F : grantBase p+3≤workW p := by unfold workW; omega
  have A : i<p.w := by unfold workW at W; omega
  have M := cmtFieldMask p (grantBase p) 3 (4*(g 0).toNat+2*(g 1).toNat+(g 2).toNat) i F I.1 I.2
  have MW : (widen p (grants p g)).mask.getLsbD i=true := by
    simpa [widen,A,grants] using M
  rw [reset0_widen_apply,Patch.write _ _ _ MW]
  simp only [widen,BitVec.getLsbD_setWidth,A,decide_true,Bool.true_and]
  have Z : 2-j.val<3 := by omega
  have E : i=grantBase p+(2-j.val) := by
    dsimp [i,grantAddr]
    have := j.isLt
    omega
  rw [E]
  unfold grants
  rw [cmtFieldVal p _ _ _ _ F Z]
  have J : j=0 ∨ j=1 ∨ j=2 := by
    rcases j with ⟨v,V⟩
    have : v=0 ∨ v=1 ∨ v=2 := by omega
    rcases this with rfl|rfl|rfl <;> simp
  rcases J with rfl|rfl|rfl
  all_goals
    cases h0 : g 0 <;> cases h1 : g 1 <;> cases h2 : g 2 <;> (try simp only [h0,h1,h2])
  all_goals decide

set_option maxHeartbeats 1500000 in
private theorem gAssignRaw (p : Params) (g : Fin 3 → Bool) (j : Fin 3) (u : BitVec p.w) :
    (((widen p (grants p g)).apply u).getLsbD (grantAddr p j))=g j := by
  have E := gAssign p g j (.empty _) u
  rw [reset0_widen_apply] at E
  simpa [widen,Patch.empty,Patch.apply] using E

set_option maxHeartbeats 1500000 in
theorem row_left_grant (p : Params) (hu hv : Bool) (u v : BitVec p.w) (j : Fin 3) :
    gBit p ((row p (hu,hv) (u,v)).1.apply u) j=grantNext p hu u j := by
  have I := gAddr p j
  unfold gBit row
  change ((widen p (body p (hu,hv) (u,v)).1).apply u).getLsbD (grantAddr p j)=_
  rw [reset0Unfold,reset0Post_left]
  dsimp only
  rw [gFoldL _ _ _ _ _ _ _ _ _ I]
  rw [gComposeRead _ _ _ _ (gLeftNorm p hu u 2) _ I,
    gComposeRead _ _ _ _ (gLeftNorm p hu u 1) _ I,
    gComposeRead _ _ _ _ (gLeftNorm p hu u 0) _ I,
    gComposeRead _ _ _ _ (gPulse p hu 2 u) _ I]
  cases hu
  · exact gAssign p (fun _=>false) j _ u
  · exact gAssignRaw p (grantNext p true u) j u

set_option maxHeartbeats 1500000 in
theorem row_right_grant (p : Params) (hu hv : Bool) (u v : BitVec p.w) (j : Fin 3) :
    gBit p ((row p (hu,hv) (u,v)).2.apply v) j=grantReceived p hv v j := by
  have I := gAddr p j
  unfold gBit row
  change ((widen p (body p (hu,hv) (u,v)).2).apply v).getLsbD (grantAddr p j)=_
  rw [reset0Unfold]
  dsimp only
  have post (a : Pair (Patch (workW p))) :
      ((widen p (reset0Post p hv v a).2).apply v).getLsbD (grantAddr p j)=
      ((widen p a.2).apply v).getLsbD (grantAddr p j) := by
    cases hv
    · rfl
    · unfold reset0Post
      simp only [if_true]
      have C := gSource p v (oldK p true v 0)
      have K' : gFrame p (match (source p v (oldK p true v 0)).2 with
          | none=>.empty _ | some t=>writeK p 0 t) := by
        split
        · exact gEmpty p
        · exact gK p _ _
      rw [gComposeRead _ _ _ _ K' _ I,gComposeRead _ _ _ _ C _ I]
  rw [post,gFoldR _ _ _ _ _ _ _ _ _ I]
  rw [gComposeRead _ _ _ _ (gNorm p hv v 2) _ I,
      gComposeRead _ _ _ _ (gNorm p hv v 1) _ I,
      gComposeRead _ _ _ _ (gNorm p hv v 0) _ I,
      gComposeRead _ _ _ _ (gPulse p hv 1 v) _ I]
  cases hv
  · exact gAssign p (fun _=>false) j _ v
  · simp only [if_true,grantReceived]
    split
    · exact gAssignRaw p _ j v
    · rename_i N
      have E (k : Fin 3) : canonical p v k=gBit p v k := by
        unfold canonical
        cases M : gBit p v 1
        · rfl
        · have O : gBit p v 0=false ∧ gBit p v 2=false := by
            simpa [M] using N
          match k with
          | ⟨0,_⟩ => simp [O.1]
          | ⟨1,_⟩ => simp [M]
          | ⟨2,_⟩ => simp [O.2]
      rw [E]
      exact (pulse_widen_frame p _ _ _ (gEmpty p _ I))

end L4.ReportByteRows

namespace L4.ReportByteRows

theorem plain_departure_ask (p : Params) (u : BitVec p.w) (op : Nat) (j : Fin 3)
    (N : op≠admitOp p) :
    grantAsk p true u op j =
      (((reportToken p true u j).tag==2) && !(reportToken p true u j).fault &&
        (reportToken p true u j).opcode==op) := by
  let t := oldK p true u j
  change (true && ready p true u j t && !t.fault && t.opcode==op) =
    ((t.tag==2) && !t.fault && t.opcode==op)
  by_cases H : t.opcode=op
  · have E : (t.opcode==admitOp p)=false := beq_false_of_ne (fun E => N (H.symm.trans E))
    have P : ready p true u j t=(t.tag==2) := by simp [ready,parked,E]
    rw [P]
    rfl
  · have E : (t.opcode==op)=false := beq_false_of_ne H
    simp [E]

theorem grant_old_view_bridge (p : Params) (h : Bool) (u : BitVec p.w) (j : Fin 3) :
    grantNext p h u j =
      if h then
        let dep := fun op j =>
          let t := reportToken p h u j
          t.tag==2 && !t.fault && t.opcode==op
        (canonical p u j && !dep 0 j) || winOld p u (dep (acqOp p)) (dep 0) j
      else false := by
  cases h
  · rfl
  · have R := funext (fun j => plain_departure_ask p u 0 j (by unfold admitOp; omega))
    have A := funext (fun j => plain_departure_ask p u (acqOp p) j
      (by unfold admitOp acqOp; omega))
    unfold grantNext
    simp only [if_true,R,A]

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol MISByteCodec

private theorem q128_reverse_at (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3 → Bool) (a : Pair (Patch (workW p))) (j k : Fin 3)
    (N : (oldK p hu u j).tag ≠ 2) (D : oldK p hv v k=reset0Reply) :
    let b := cmtRoute p hu hv u v win a (j,some k)
    resetTokenRead p ((widen p b.1).apply u) j=resetTokenWire p reset0Reply ∧
      resetTokenRead p ((widen p b.2).apply v) k=resetTokenWire p E := by
  rcases a with ⟨a,b⟩
  dsimp only
  have tag : (oldK p hv v k).tag=3 := by rw [D]; rfl
  rw [reset_drain_reverse_link p hu hv u v win a b j k N tag,D]
  exact ⟨reset0_compKSame p j a u reset0Reply,reset0_compKSame p k b v E⟩

/-- Both outputs of the reverse link survive the complete report work
row. In particular CMT/source/fault normalization on other lanes
cannot overwrite the canonical D0 or the newly cleared occurrence. -/
theorem reset0_row_reverse (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (N : (publicationToken p hu u j).tag ≠ 2)
    (D : publicationToken p hv v k=reset0Reply)
    (K : reset0Destination hv j=some k) :
    resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j=resetTokenWire p reset0Reply ∧
      resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k=resetTokenWire p E := by
  obtain ⟨pre,suf,L,J,R⟩ := reset0_list_split hv j
  obtain ⟨head,port⟩ := R k K
  unfold row
  rw [reset0Unfold]
  dsimp only
  rw [reset0Post_left,reset0Post_right _ _ _ _ _ head,L,List.foldl_append,List.foldl_cons,K,
    reset0_foldL _ _ _ _ _ _ _ _ _ J,reset0_foldR _ _ _ _ _ _ _ _ _ port]
  exact q128_reverse_at p hu hv u v _ _ j k N D

end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

private theorem drain_decode_small (p : Params) (g : Bool) (tag : Nat)
    (H : tag=0 ∨ tag=1) :
    decode p g (resetTokenWire p ({tag:=tag} : Tok)) =
      ({tag:=tag} : Tok) := by
  let n := 7+o p+payW p
  have W : tokenW p=n+2 := by unfold n tokenW; omega
  have lt : tag<4 := by rcases H with H|H <;> omega
  have sh : resetTokenWire p ({tag:=tag} : Tok) =
      (BitVec.ofNat (tokenW p) tag) <<< n := by
    apply BitVec.eq_of_toNat_eq
    unfold resetTokenWire encode
    simp only [Bool.toNat_false,Nat.zero_mul,Nat.add_zero,
      BitVec.toNat_ofNat,BitVec.toNat_shiftLeft]
    rw [Nat.shiftLeft_eq]
    have L : tag<2^(tokenW p) := by
      have M : (2:Nat)^2≤2^(tokenW p) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    rw [Nat.mod_eq_of_lt L]
  have extTag :
      (((BitVec.ofNat (tokenW p) tag) <<< n).extractLsb' n 2)=
        BitVec.ofNat 2 tag := by
    apply BitVec.eq_of_getLsbD_eq
    intro j J
    have K : n+j<tokenW p := by omega
    have JD : j<tokenW p := by omega
    simp [J,K,show ¬n+j<n by omega]
    simp [BitVec.getElem_eq_testBit_toNat,Nat.testBit_mod_two_pow,JD,
      Nat.mod_eq_of_lt lt]
  rw [sh]
  unfold decode
  dsimp only
  unfold get
  rw [extTag]
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt lt]
  rcases H with rfl|rfl <;> rfl

theorem drain_decode_E (p : Params) (g : Bool) :
    decode p g (resetTokenWire p E)=E :=
  drain_decode_small p g 0 (.inl rfl)

theorem drain_decode_T (p : Params) (g : Bool) :
    decode p g (resetTokenWire p T)=T :=
  drain_decode_small p g 1 (.inr rfl)

theorem drain_read_token (p : Params) (h : Bool) (x : BitVec p.w)
    (j : Fin 3) (t : Tok)
    (D : ∀ g,decode p g (resetTokenWire p t)=t)
    (W : resetTokenRead p x j=resetTokenWire p t) :
    publicationToken p h x j=t := by
  change decode p _ (resetTokenRead p x j)=t
  rw [W]
  exact D _

/-- Canonical four-letter reset rail. All have opcode zero and fault=false. -/
def DrainLetter (t : Tok) : Prop :=
  t=E ∨ t=T ∨ t=reset0Forward ∨ t=reset0Reply

private theorem drain_plain (p : Params) (t : Tok) (H : DrainLetter t) :
    t.fault=false ∧ (t.opcode==admitOp p)=false := by
  rcases H with rfl|rfl|rfl|rfl <;>
    simp [MISByteCodec.E,MISByteCodec.T,reset0Forward,reset0Reply,admitOp]

private theorem dr_norm_left (p : Params) (h : Bool) (x : BitVec p.w)
    (j : Fin 3) (H : DrainLetter (oldK p h x j)) :
    outgoingNormalize p h x j=.empty _ := by
  obtain ⟨F,O⟩ := drain_plain p _ H
  simp [outgoingNormalize,parked,F,O]

private theorem dr_norm_right (p : Params) (h : Bool) (x : BitVec p.w)
    (j : Fin 3) (H : DrainLetter (oldK p h x j)) :
    cmtNorm p h x j=.empty _ := by
  obtain ⟨F,O⟩ := drain_plain p _ H
  simp [cmtNorm,parked,F,O]

private theorem dr_norm_left_shape (p : Params) (h : Bool)
    (x : BitVec p.w) (j : Fin 3) :
    outgoingNormalize p h x j=.empty _ ∨
      ∃ t, outgoingNormalize p h x j=writeK p j t := by
  unfold outgoingNormalize
  dsimp only
  split
  · exact .inr ⟨_,rfl⟩
  · split
    · exact .inr ⟨_,rfl⟩
    · exact .inl rfl

private theorem dr_norm_right_shape (p : Params) (h : Bool)
    (x : BitVec p.w) (j : Fin 3) :
    cmtNorm p h x j=.empty _ ∨ ∃ t,cmtNorm p h x j=writeK p j t := by
  unfold cmtNorm
  dsimp only
  split
  · exact .inr ⟨_,rfl⟩
  · split
    · exact .inr ⟨_,rfl⟩
    · exact .inl rfl

private def drClear (p : Params) : Patch (workW p) :=
  ((reset p).compose (writeSeal p none)).compose (grants p fun _=>false)

private def drBaseL (p : Params) (hu : Bool) (u : BitVec p.w) :
    Patch (workW p) :=
  if hu then grants p (grantNext p true u) else drClear p

private def drBaseR (p : Params) (hv : Bool) (v : BitVec p.w) :
    Patch (workW p) :=
  if hv then
    if gBit p v 1 && (gBit p v 0 || gBit p v 2) then
      grants p (canonical p v) else .empty _
  else drClear p

private def drPrefix (p : Params) (base pulseP : Patch (workW p))
    (norm : Fin 3→Patch (workW p)) : Patch (workW p) :=
  ((((base.compose pulseP).compose (norm 0)).compose (norm 1))).compose (norm 2)

private def drPre (p : Params) (hu hv : Bool) (u v : BitVec p.w) :
    Pair (Patch (workW p)) :=
  (drPrefix p (drBaseL p hu u) (pulse p hu 2 u) (outgoingNormalize p hu u),
   drPrefix p (drBaseR p hv v) (pulse p hv 1 v) (cmtNorm p hv v))

private def drWin (p : Params) (hu : Bool) (u : BitVec p.w) :
    Fin 3→Bool :=
  winOld p u (grantAsk p hu u (acqOp p)) (grantAsk p hu u 0)

private def drRouted (p : Params) (hu hv : Bool) (u v : BitVec p.w) :
    Pair (Patch (workW p)) :=
  (links hv).foldl (cmtRoute p hu hv u v (drWin p hu u))
    (drPre p hu hv u v)

private theorem dr_row_eq (p : Params) (hu hv : Bool) (u v : BitVec p.w) :
    row p (hu,hv) (u,v) =
      (widen p (reset0Post p hv v (drRouted p hu hv u v)).1,
       widen p (reset0Post p hv v (drRouted p hu hv u v)).2) := by
  -- CHECK: reset0Unfold (1899–1923), grantNext (3075–3079),
  -- winOld (2645–2647). These are literally the same lets.
  unfold row
  rw [reset0Unfold]
  cases hu <;> cases hv <;> rfl

private theorem dr_clear_frame (p : Params) : reset0Frame p (drClear p) := by
  unfold drClear reset writeSeal grants
  apply reset0Comp
  · apply reset0Comp
    · exact reset0Field p _ _ _ (by omega)
    · exact reset0Field p _ _ _ (by unfold sealBase; omega)
  · exact reset0Field p _ _ _ (by unfold grantBase sealBase; omega)

private theorem dr_grants_frame (p : Params) (g : Fin 3→Bool) :
    reset0Frame p (grants p g) :=
  reset0Field p _ _ _ (by unfold grantBase sealBase; omega)

private theorem dr_baseL_frame (p : Params) (hu : Bool) (u : BitVec p.w) :
    reset0Frame p (drBaseL p hu u) := by
  unfold drBaseL
  split
  · exact dr_grants_frame p _
  · exact dr_clear_frame p

private theorem dr_baseR_frame (p : Params) (hv : Bool) (v : BitVec p.w) :
    reset0Frame p (drBaseR p hv v) := by
  unfold drBaseR
  split
  · split
    · exact dr_grants_frame p _
    · exact reset0Empty p
  · exact dr_clear_frame p

private theorem dr_norm_comp (p : Params) (j k : Fin 3)
    (norm : Fin 3→Patch (workW p)) (a : Patch (workW p)) (x : BitVec p.w)
    (H : norm j=.empty _)
    (S : ∀ i, norm i=.empty _ ∨ ∃ t,norm i=writeK p i t) :
    resetTokenRead p ((widen p (a.compose (norm k))).apply x) j=
      resetTokenRead p ((widen p a).apply x) j := by
  by_cases J : j=k
  · subst k
    rw [H,reset0_empty_comp]
  · rcases S k with E|⟨t,E⟩
    · rw [E,reset0_empty_comp]
    · rw [E]
      exact reset0_compKOther p j k J t a x

private theorem dr_prefix_read (p : Params) (h : Bool) (side : Nat)
    (x : BitVec p.w) (j : Fin 3) (base : Patch (workW p))
    (norm : Fin 3→Patch (workW p))
    (B : reset0Frame p base) (H : norm j=.empty _)
    (S : ∀ i,norm i=.empty _ ∨ ∃ t,norm i=writeK p i t) :
    resetTokenRead p ((widen p (drPrefix p base (pulse p h side x) norm)).apply x) j =
      resetTokenRead p x j := by
  unfold drPrefix
  rw [dr_norm_comp p j 2 norm _ x H S,
      dr_norm_comp p j 1 norm _ x H S,
      dr_norm_comp p j 0 norm _ x H S,reset0_widen_apply]
  have F : ∀ i,i<tokenW p →
      (pulse p h side x).mask.getLsbD (kOffset p j+i)=false := by
    intro i _
    exact pulse_mask_below_tail p h side x _ (by unfold kOffset; omega)
  exact (reset0_read_hold p j _ _ F).trans (reset0_read_frame p j base x B)

private theorem dr_pre_left (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (H : DrainLetter (oldK p hu u j)) :
    resetTokenRead p ((widen p (drPre p hu hv u v).1).apply u) j =
      resetTokenRead p u j :=
  dr_prefix_read p hu 2 u j _ _ (dr_baseL_frame p hu u)
    (dr_norm_left p hu u j H) (dr_norm_left_shape p hu u)

private theorem dr_pre_right (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (H : DrainLetter (oldK p hv v j)) :
    resetTokenRead p ((widen p (drPre p hu hv u v).2).apply v) j =
      resetTokenRead p v j :=
  dr_prefix_read p hv 1 v j _ _ (dr_baseR_frame p hv v)
    (dr_norm_right p hv v j H) (dr_norm_right_shape p hv v)

private theorem dr_link_dest (h : Bool) (l : Fin 3 × Option (Fin 3))
    (M : l∈links h) : l.2=reset0Destination h l.1 := by
  cases h <;> simp [links] at M
  all_goals rcases M with H|H|H <;> rw [H] <;> decide

private theorem dr_dest_inj (h : Bool) (j l k : Fin 3)
    (A : reset0Destination h j=some k)
    (B : reset0Destination h l=some k) : j=l := by
  cases h
  · exact Option.some.inj (A.trans B.symm)
  · have H : ∀ j l k : Fin 3,
        reset0Destination true j=some k →
        reset0Destination true l=some k → j=l := by decide
    exact H j l k A B

private theorem dr_no_root_dest (j : Fin 3) :
    reset0Destination true j≠some 0 := by
  have H : ∀ j : Fin 3,reset0Destination true j≠some 0 := by decide
  exact H j

/-- A whole selected idle link makes no route write at all. The
normalizers must still be accounted for separately. -/
private theorem dr_route_idle (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (win : Fin 3→Bool) (ab : Pair (Patch (workW p)))
    (j k : Fin 3)
    (H : (oldK p hu u j=T ∧
          (oldK p hv v k=T ∨ oldK p hv v k=reset0Forward)) ∨
        ((oldK p hu u j=E ∨ oldK p hu u j=reset0Reply) ∧
          oldK p hv v k=E)) :
    cmtRoute p hu hv u v win ab (j,some k)=ab := by
  rcases ab with ⟨a,b⟩
  rcases H with ⟨A,B|B⟩|⟨A|A,B⟩ <;>
    simp [cmtRoute,A,B,ready,MISByteCodec.E,MISByteCodec.T,reset0Forward,reset0Reply]

private theorem dr_route_terminal_idle (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (win : Fin 3→Bool) (ab : Pair (Patch (workW p)))
    (j : Fin 3) (H : oldK p hu u j=E ∨ oldK p hu u j=reset0Reply) :
    cmtRoute p hu hv u v win ab (j,none)=ab := by
  rcases ab with ⟨a,b⟩
  rcases H with H|H <;> simp [cmtRoute,H,ready,MISByteCodec.E,reset0Reply]

private theorem dr_fold_idleL (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (win : Fin 3→Bool)
    (xs : List (Fin 3 × Option (Fin 3))) (ab : Pair (Patch (workW p)))
    (j : Fin 3)
    (H : ∀ l∈xs,l.1=j → ∀ a,cmtRoute p hu hv u v win a l=a) :
    resetTokenRead p ((widen p (xs.foldl (cmtRoute p hu hv u v win) ab).1).apply u) j =
      resetTokenRead p ((widen p ab.1).apply u) j := by
  induction xs generalizing ab with
  | nil => rfl
  | cons l xs ih =>
    have Q := ih (cmtRoute p hu hv u v win ab l)
      (fun k K=>H k (List.mem_cons_of_mem _ K))
    change _=_
    apply Q.trans
    by_cases J : j=l.1
    · rw [H l List.mem_cons_self J.symm ab]
    · exact reset0_tailL p hu hv u v win ab l j J

private theorem dr_fold_idleR (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (win : Fin 3→Bool)
    (xs : List (Fin 3 × Option (Fin 3))) (ab : Pair (Patch (workW p)))
    (k : Fin 3)
    (H : ∀ l∈xs,l.2=some k → ∀ a,cmtRoute p hu hv u v win a l=a) :
    resetTokenRead p ((widen p (xs.foldl (cmtRoute p hu hv u v win) ab).2).apply v) k =
      resetTokenRead p ((widen p ab.2).apply v) k := by
  induction xs generalizing ab with
  | nil => rfl
  | cons l xs ih =>
    have Q := ih (cmtRoute p hu hv u v win ab l)
      (fun j J=>H j (List.mem_cons_of_mem _ J))
    apply Q.trans
    by_cases K : some k=l.2
    · rw [H l List.mem_cons_self K.symm ab]
    · exact reset0_tailR p hu hv u v win ab l k K

/-- Both passive owner fields after the *whole* old-pair row. -/
theorem drain_row_idle (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (j k : Fin 3) (dst : reset0Destination hv j=some k)
    (H : (publicationToken p hu u j=T ∧
          (publicationToken p hv v k=T ∨ publicationToken p hv v k=reset0Forward)) ∨
        ((publicationToken p hu u j=E ∨ publicationToken p hu u j=reset0Reply) ∧
          publicationToken p hv v k=E)) :
    resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j=resetTokenRead p u j ∧
    resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k=resetTokenRead p v k := by
  have JL : DrainLetter (oldK p hu u j) := by
    rcases H with ⟨A,_⟩|⟨A|A,_⟩
    · exact .inr (.inl A)
    · exact .inl A
    · exact .inr (.inr (.inr A))
  have JR : DrainLetter (oldK p hv v k) := by
    rcases H with ⟨_,A|A⟩|⟨_,A⟩
    · exact .inr (.inl A)
    · exact .inr (.inr (.inl A))
    · exact .inl A
  have idle (ab : Pair (Patch (workW p))) :=
    dr_route_idle p hu hv u v (drWin p hu u) ab j k H
  have L := dr_fold_idleL p hu hv u v (drWin p hu u) (links hv)
    (drPre p hu hv u v) j (by
      intro l M J ab
      rcases l with ⟨a,b⟩
      change a=j at J
      subst a
      have B := dr_link_dest hv (j,b) M
      change b=reset0Destination hv j at B
      rw [dst] at B
      subst b
      exact idle ab)
  have R := dr_fold_idleR p hu hv u v (drWin p hu u) (links hv)
    (drPre p hu hv u v) k (by
      intro l M K ab
      rcases l with ⟨a,b⟩
      change b=some k at K
      subst b
      have B := (dr_link_dest hv (a,some k) M).symm
      have A := dr_dest_inj hv j a k dst B
      subst a
      exact idle ab)
  have NR : hv=true→k≠0 := by
    intro E K
    subst hv
    subst k
    exact dr_no_root_dest j dst
  rw [dr_row_eq]
  dsimp only
  rw [reset0Post_left p hv v (drRouted p hu hv u v), reset0Post_right p hv v (drRouted p hu hv u v) k NR]
  exact ⟨L.trans (dr_pre_left p hu hv u v j JL),
    R.trans (dr_pre_right p hu hv u v k JR)⟩

theorem drain_row_terminal_hold (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (j : Fin 3) (dst : reset0Destination hv j=none)
    (H : publicationToken p hu u j=E ∨ publicationToken p hu u j=reset0Reply) :
    resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j=resetTokenRead p u j := by
  have J : DrainLetter (oldK p hu u j) := by
    rcases H with A|A
    · exact .inl A
    · exact .inr (.inr (.inr A))
  have L := dr_fold_idleL p hu hv u v (drWin p hu u) (links hv)
    (drPre p hu hv u v) j (by
      intro l M K ab
      rcases l with ⟨a,b⟩
      change a=j at K
      subst a
      have B := dr_link_dest hv (j,b) M
      change b=reset0Destination hv j at B
      rw [dst] at B
      subst b
      exact dr_route_terminal_idle p hu hv u v _ ab j H)
  rw [dr_row_eq]
  dsimp only
  rw [reset0Post_left p hv v (drRouted p hu hv u v)]
  exact L.trans (dr_pre_left p hu hv u v j J)

/-! Source-window framing. Source fields occupy [sourceBase,sealBase).
    Every routed effect writes only token fields or fields at/above sealBase.
    A header's initial grants/pulse also miss that window. -/

private def drSrcFrame (p : Params) (a : Patch (workW p)) : Prop :=
  ∀ i,sourceBase p≤i → i<sealBase p → a.mask.getLsbD i=false

private theorem drSempty (p : Params) : drSrcFrame p (.empty _) :=
  fun i _ _=>by simp [Patch.empty]

private theorem drScomp {p : Params} {a b : Patch (workW p)}
    (A : drSrcFrame p a) (B : drSrcFrame p b) : drSrcFrame p (a.compose b) :=
  fun i L R=>pulse_comp_out (A i L R) (B i L R)

private theorem drSfield (p : Params) (k b v : Nat)
    (H : k+b≤sourceBase p ∨ sealBase p≤k) :
    drSrcFrame p (field p k b v) := by
  intro i L R
  apply pulse_field_out
  rcases H with H|H
  · exact .inr (by omega)
  · exact .inl (by omega)

private theorem drSK (p : Params) (j : Fin 3) (t : Tok) :
    drSrcFrame p (writeK p j t) :=
  drSfield p _ _ _ (.inl (reset0SlotBound p j))

private theorem drSseal (p : Params) (a : Option Nat) :
    drSrcFrame p (writeSeal p a) :=
  drSfield p _ _ _ (.inr (by omega))

private theorem drSgrants (p : Params) (g : Fin 3→Bool) :
    drSrcFrame p (grants p g) :=
  drSfield p _ _ _ (.inr (by unfold grantBase; omega))

private theorem drSpulse (p : Params) (h : Bool) (side : Nat) (x : BitVec p.w) :
    drSrcFrame p (pulse p h side x) :=
  fun i L _=>pulse_mask_below_tail p h side x i (by unfold sourceBase at L; omega)

private theorem drSnormal (p : Params) (j : Fin 3)
    (a : Patch (workW p)) (H : a=.empty _ ∨ ∃ t,a=writeK p j t) :
    drSrcFrame p a := by
  rcases H with rfl|⟨t,rfl⟩
  · exact drSempty p
  · exact drSK p j t

private theorem drSeffect (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) (t : Tok) :
    drSrcFrame p (effect p u v hu hv j k win t).1 ∧
      drSrcFrame p (effect p u v hu hv j k win t).2.1 := by
  have bank' (ix a b z : Nat) : drSrcFrame p (field p (bankOffset p ix+a) b z) :=
    drSfield p _ _ _ (.inr (by unfold bankOffset; omega))
  have sel (ix : Nat) : drSrcFrame p (field p (grantBase p+3) 1 ix) :=
    drSfield p _ _ _ (.inr (by unfold grantBase; omega))
  have nil : drSrcFrame p (.empty _) ∧ drSrcFrame p (.empty _) := ⟨drSempty p, drSempty p⟩
  unfold effect
  dsimp only
  generalize (if t.opcode < readOp p then cmpOp p else readOp p) = opBase
  split
  · exact nil
  split
  · split
    · exact ⟨drSempty p,drScomp (drScomp (sel ((t.payload/4)%2)) (drSseal p none)) (bank' ((t.payload/4)%2) (2*d p) 3 (4*(Z p v).toNat+t.payload%4))⟩
    · exact nil
  split
  · exact nil
  split
  · exact ⟨drSseal p none,drSempty p⟩
  split
  · exact nil
  split
  · exact nil
  split
  · split
    · exact nil
    · exact ⟨bank' _ 0 _ _,drSempty p⟩
  · split
    · split
      · exact ⟨drSseal p (some t.payload),drSempty p⟩
      · exact nil
    · exact nil

private theorem drSroute (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3→Bool) (ab : Pair (Patch (workW p)))
    (l : Fin 3 × Option (Fin 3)) :
    (drSrcFrame p ab.1 → drSrcFrame p (cmtRoute p hu hv u v win ab l).1) ∧
    (drSrcFrame p ab.2 → drSrcFrame p (cmtRoute p hu hv u v win ab l).2) := by
  rcases ab with ⟨a,b⟩
  rcases l with ⟨j,k⟩
  let t := oldK p hu u j
  have EF := drSeffect p u v hu hv j k (win j) t
  unfold cmtRoute
  dsimp only
  by_cases readyK : ready p hu u j t = true
  · rw [if_pos readyK]
    cases k with
    | none =>
      let out := effect p u v hu hv j none (win j) t
      exact ⟨fun H=>drScomp (p:=p) (drScomp (p:=p) H EF.1) (drSK p j (terminal p out.2.2)),
        fun H=>drScomp (p:=p) H EF.2⟩
    | some k =>
      let out := effect p u v hu hv j (some k) (win j) t
      exact ⟨fun H=>drScomp (p:=p) (drScomp (p:=p) H EF.1) (drSK p j T),
        fun H=>drScomp (p:=p) (drScomp (p:=p) H EF.2) (drSK p k (arrival p hv v k out.2.2))⟩
  · rw [if_neg readyK]
    by_cases tag2 : (t.tag == 2) = true
    · rw [if_pos tag2]
      exact ⟨id,id⟩
    · rw [if_neg tag2]
      cases k with
      | none =>
        dsimp only
        by_cases tag1 : (t.tag == 1) = true
        · rw [if_pos tag1]
          exact ⟨fun H=>drScomp (p:=p) H (drSK p j E),id⟩
        · rw [if_neg tag1]
          exact ⟨id,id⟩
      | some k =>
        dsimp only
        let q := oldK p hv v k
        by_cases tag3 : (q.tag == 3) = true
        · rw [if_pos tag3]
          exact ⟨fun H=>drScomp (p:=p) H (drSK p j q),fun H=>drScomp (p:=p) H (drSK p k E)⟩
        · rw [if_neg tag3]
          by_cases trail : (t.tag == 1 && q.tag == 0) = true
          · rw [if_pos trail]
            exact ⟨fun H=>drScomp (p:=p) H (drSK p j E),id⟩
          · rw [if_neg trail]
            exact ⟨id,id⟩

private theorem drSfold (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3→Bool) (xs : List (Fin 3 × Option (Fin 3)))
    (ab : Pair (Patch (workW p))) :
    (drSrcFrame p ab.1 →
      drSrcFrame p (xs.foldl (cmtRoute p hu hv u v win) ab).1) ∧
    (drSrcFrame p ab.2 →
      drSrcFrame p (xs.foldl (cmtRoute p hu hv u v win) ab).2) := by
  induction xs generalizing ab with
  | nil => exact ⟨id,id⟩
  | cons l xs ih =>
    have H := drSroute p hu hv u v win ab l
    exact ⟨fun A=>(ih _).1 (H.1 A),fun A=>(ih _).2 (H.2 A)⟩

private theorem drSprefix (p : Params) (base pulseP : Patch (workW p))
    (norm : Fin 3→Patch (workW p)) (A : drSrcFrame p base)
    (B : drSrcFrame p pulseP) (C : ∀ i,drSrcFrame p (norm i)) :
    drSrcFrame p (drPrefix p base pulseP norm) :=
  drScomp (drScomp (drScomp (drScomp A B) (C 0)) (C 1)) (C 2)

private theorem drSleft (p : Params) (hv : Bool) (u v : BitVec p.w) :
    drSrcFrame p (drRouted p true hv u v).1 := by
  apply (drSfold p true hv u v (drWin p true u) (links hv) _).1
  exact drSprefix p _ _ _ (drSgrants p _) (drSpulse p true 2 u)
    (fun j=>drSnormal p j _ (dr_norm_left_shape p true u j))

private theorem drSright (p : Params) (hu : Bool) (u v : BitVec p.w) :
    drSrcFrame p (drRouted p hu true u v).2 := by
  apply (drSfold p hu true u v (drWin p hu u) (links true) _).2
  have F : drSrcFrame p (drBaseR p true v) := by
    unfold drBaseR
    simp only [if_true]
    split
    · exact drSgrants p _
    · exact drSempty p
  exact drSprefix p _ _ _ F (drSpulse p true 1 v)
    (fun j=>drSnormal p j _ (dr_norm_right_shape p true v j))

private theorem drSget (p : Params) (a : Patch (workW p)) (x : BitVec p.w)
    (F : drSrcFrame p a) (k b : Nat)
    (L : sourceBase p≤k) (R : k+b≤sealBase p) :
    get ((widen p a).apply x) k b=get x k b := by
  unfold get
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  exact pulse_widen_frame p a x _ (F _ (by omega) (by omega))

private theorem drScontrol (p : Params) (a : Patch (workW p)) (x : BitVec p.w)
    (F : drSrcFrame p a) :
    (sourcePhase p ((widen p a).apply x),sourceOpcode p ((widen p a).apply x)) =
      (sourcePhase p x,sourceOpcode p x) := by
  apply Prod.ext
  · exact drSget p a x F _ _ (by unfold pc; omega)
      (by unfold pc sealBase sourceW; omega)
  · exact drSget p a x F _ _ (by unfold pc; omega)
      (by unfold pc sealBase sourceW; omega)

theorem drain_row_left_control (p : Params) (hv : Bool) (u v : BitVec p.w) :
    let y := (row p (true,hv) (u,v)).1.apply u
    (sourcePhase p y,sourceOpcode p y)=(sourcePhase p u,sourceOpcode p u) := by
  dsimp only
  rw [dr_row_eq]
  dsimp only
  rw [reset0Post_left]
  exact drScontrol p _ _ (drSleft p hv u v)

/-- Arbitrary base byte, then a single fitting assignment: a subread
inside that assignment depends only on its value, not old padding. -/
-- CHECK: bit extraction and widening, ReportByteRows.lean:425–450,1758–1772.
private theorem dr_field_sub (p : Params) (x : BitVec p.w)
    (k b v a c : Nat) (F : k+b≤workW p) (S : a+c≤b) :
    ((widen p (field p k b v)).apply x).extractLsb' (k+a) c =
      (BitVec.ofNat b v).extractLsb' a c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  have J : a+i<b := by omega
  have K : k+a+i<workW p := by omega
  have W := layout_size p
  have H := pulse_field_write p k b v (k+(a+i)) (by omega) (by omega) (by omega)
  have M : (widen p (field p k b v)).mask.getLsbD (k+(a+i))=true := by
    simp [widen,show k+(a+i)<p.w by omega,H.1]
  simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and,Nat.add_assoc]
  rw [Patch.write _ _ _ M]
  have V := H.2
  rw [show k+(a+i)-k=a+i by omega] at V
  simpa only [widen,BitVec.getLsbD_setWidth,show k+(a+i)<p.w by omega,
    decide_true,Bool.true_and] using V

private theorem dr_field_get (p : Params) (x : BitVec p.w)
    (k b v a c : Nat) (F : k+b≤workW p) (S : a+c≤b)
    (V : v<2^b) :
    get ((widen p (field p k b v)).apply x) (k+a) c =
      (v/2^a)%2^c := by
  unfold get
  rw [dr_field_sub p x k b v a c F S]
  simp [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt V]

private theorem dr_reset_control (p : Params) (x : BitVec p.w) :
    (sourcePhase p ((widen p (resetIssue p)).apply x),
     sourceOpcode p ((widen p (resetIssue p)).apply x))=(2,0) := by
  have F : sourceBase p+sourceW p≤workW p := by
    unfold workW grantBase sealBase; omega
  have W : 2^(sourceW p-2)<2^sourceW p := by
    calc
      _ < 2^(sourceW p-2)*2^2 := by
        have P : 0<2^(sourceW p-2) := Nat.pow_pos (by decide)
        omega
      _ = _ := by
        rw [←Nat.pow_add,show sourceW p-2+2=sourceW p by unfold sourceW; omega]
  have O := dr_field_get p x (sourceBase p) (sourceW p) (2^(sourceW p-2))
    (19+2*d p) (o p) F (by unfold sourceW; omega) W
  have Exp : sourceW p-2=(19+2*d p)+o p := by unfold sourceW; omega
  have Div : 2^(sourceW p-2)/2^(19+2*d p)=2^o p := by
    rw [Exp,Nat.pow_add]
    exact Nat.mul_div_right _ (Nat.pow_pos (by decide))
  rw [Div,Nat.mod_self] at O
  -- CHECK: sourceOpcode/pc/reset layout, ReportByteRows.lean:102-106,1350-1355.
  have OO : sourceOpcode p ((widen p (reset p)).apply x)=0 := by
    simpa [sourceOpcode,pc,reset,Nat.add_assoc] using O
  unfold resetIssue
  rw [reset0_widen_apply]
  apply Prod.ext
  · have K := dr_field_get p ((widen p (reset p)).apply x) (pc p+o p)
      2 2 0 2 (by unfold pc workW grantBase sealBase sourceW; omega)
      (by decide) (by decide)
    simpa [sourcePhase] using K
  · unfold sourceOpcode get
    have K : ((widen p (field p (pc p+o p) 2 2)).apply
        ((widen p (reset p)).apply x)).extractLsb' (pc p) (o p) =
        ((widen p (reset p)).apply x).extractLsb' (pc p) (o p) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i I
      simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
      exact pulse_widen_frame p _ _ _
        (pulse_field_out p _ _ _ _ (.inl (by omega)))
    rw [K]
    exact OO

private theorem dr_done_control (p : Params) (x : BitVec p.w) :
    (sourcePhase p ((widen p (resetWaitDone p)).apply x),
      sourceOpcode p ((widen p (resetWaitDone p)).apply x))=(1,1) := by
  have P := power_of_ell (5+4*p.digits)
  change 5+4*p.digits≤2^o p at P
  have V : 2^o p+1<2^(o p+2) := by
    rw [Nat.pow_add]
    omega
  have F : pc p+(o p+2)≤workW p := by
    unfold pc workW grantBase sealBase sourceW; omega
  have A := dr_field_get p x (pc p) (o p+2) (2^o p+1)
    (o p) 2 F (by omega) V
  have B := dr_field_get p x (pc p) (o p+2) (2^o p+1)
    0 (o p) F (by omega) V
  have D : (2^o p+1)/2^o p=1 := by
    have L : 1<2^o p := by omega
    calc
      _ = (1+(2^o p)*1)/2^o p := by simp [Nat.add_comm]
      _ = 1/2^o p+1 := Nat.add_mul_div_left 1 1 (by omega : 0<2^o p)
      _ = 1 := by simp [Nat.div_eq_of_lt L]
  have M : (2^o p+1)%2^o p=1 := by
    rw [Nat.add_mod,Nat.mod_self,Nat.zero_add]
    simp [Nat.mod_eq_of_lt (by omega : 1<2^o p)]
  apply Prod.ext
  · simpa [resetWaitDone,ctrl,sourcePhase,D] using A
  · simpa [resetWaitDone,ctrl,sourceOpcode,M] using B

private theorem dr_K_source_frame (p : Params) (j : Fin 3) (t : Tok)
    (x : BitVec p.w) :
    (sourcePhase p ((widen p (writeK p j t)).apply x),
      sourceOpcode p ((widen p (writeK p j t)).apply x))=
      (sourcePhase p x,sourceOpcode p x) :=
  drScontrol p _ _ (drSK p j t)

theorem drain_row_issue (p : Params) (hu : Bool) (u v : BitVec p.w)
    (P : sourcePhase p v=1) (O : sourceOpcode p v=0) :
    let y := (row p (hu,true) (u,v)).2.apply v
    (sourcePhase p y,sourceOpcode p y)=(2,0) ∧
      resetTokenRead p y 0=resetTokenWire p reset0Forward := by
  obtain ⟨a,H⟩ := row_reset0_issue_suffix p hu u v P O
  dsimp only
  rw [H]
  change (sourcePhase p ((widen p ((a.compose (resetIssue p)).compose
      (writeK p 0 reset0Forward))).apply v),sourceOpcode p
      ((widen p ((a.compose (resetIssue p)).compose
        (writeK p 0 reset0Forward))).apply v))=(2,0) ∧ _
  refine ⟨?_,reset0_compKSame p 0 (a.compose (resetIssue p)) v reset0Forward⟩
  rw [reset0_widen_apply,dr_K_source_frame,reset0_widen_apply]
  exact dr_reset_control p _

theorem drain_row_consume (p : Params) (hu : Bool) (u v : BitVec p.w)
    (P : sourcePhase p v=2) (O : sourceOpcode p v=0)
    (D : publicationToken p true v 0=reset0Reply) :
    let y := (row p (hu,true) (u,v)).2.apply v
    (sourcePhase p y,sourceOpcode p y)=(1,1) ∧
      resetTokenRead p y 0=resetTokenWire p E := by
  obtain ⟨a,H⟩ := row_reset0_consume_suffix p hu u v P O D
  dsimp only
  rw [H]
  change (sourcePhase p ((widen p ((a.compose (resetWaitDone p)).compose
      (writeK p 0 E))).apply v),sourceOpcode p
      ((widen p ((a.compose (resetWaitDone p)).compose
        (writeK p 0 E))).apply v))=(1,1) ∧ _
  refine ⟨?_,reset0_compKSame p 0 (a.compose (resetWaitDone p)) v E⟩
  rw [reset0_widen_apply,dr_K_source_frame,reset0_widen_apply]
  exact dr_done_control p _

theorem drain_row_wait_hold (p : Params) (hu : Bool) (u v : BitVec p.w)
    (P : sourcePhase p v=2) (O : sourceOpcode p v=0)
    (H : publicationToken p true v 0=T ∨
      publicationToken p true v 0=reset0Forward) :
    let y := (row p (hu,true) (u,v)).2.apply v
    (sourcePhase p y,sourceOpcode p y)=(2,0) ∧
      resetTokenRead p y 0=resetTokenRead p v 0 := by
  have J : DrainLetter (oldK p true v 0) := by
    rcases H with H|H
    · exact .inr (.inl H)
    · exact .inr (.inr (.inl H))
  have T : (oldK p true v 0).tag=1 ∨ (oldK p true v 0).tag=2 := by
    rcases H with H|H
    · exact .inl (congrArg MISByteCodec.Token.tag H)
    · exact .inr (congrArg MISByteCodec.Token.tag H)
  have R := source_reset0_hold p v (oldK p true v 0) P O T
  dsimp only
  rw [dr_row_eq]
  dsimp only
  unfold reset0Post
  simp only [if_true,R,reset0_empty_comp]
  refine ⟨?_,?_⟩
  · rw [drScontrol p _ _ (drSright p hu u v),P,O]
  · have F : ∀ l∈links true,some (0 : Fin 3)≠l.2 := by
      intro l M X
      exact dr_no_root_dest l.1 ((dr_link_dest true l M).symm.trans X.symm)
    exact (reset0_foldR p hu true u v (drWin p hu u)
      (links true) (drPre p hu true u v) 0 F).trans
      (dr_pre_right p hu true u v 0 J)

/-- Exact cleared source-file value, excluding the live PC. -/
def drainFile (p : Params) (x : BitVec p.w) : Nat :=
  get x (sourceBase p) (19+2*d p)

/-- Raw zero seal, stronger than merely decoding to none. -/
def drainSealZero (p : Params) (x : BitVec p.w) : Prop :=
  ∀ i,sealBase p≤i → i<sealBase p+5 → x.getLsbD i=false

theorem drain_seal_none (p : Params) (x : BitVec p.w)
    (H : drainSealZero p x) : readSeal p x=none := by
  have B : x.extractLsb' (sealBase p) 5=0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i I
    simpa [BitVec.getLsbD_extractLsb',I] using
      H (sealBase p+i) (by omega) (by omega)
  simp [readSeal,get,B]

private theorem dr_file_frame (p : Params) (a : Patch (workW p))
    (x : BitVec p.w) (A : drSrcFrame p a) :
    drainFile p ((widen p a).apply x)=drainFile p x :=
  drSget p a x A _ _ (by omega) (by unfold sealBase sourceW; omega)

private theorem dr_file_late (p : Params) (x : BitVec p.w)
    (k b v : Nat) (K : pc p≤k) :
    drainFile p ((widen p (field p k b v)).apply x)=drainFile p x := by
  unfold drainFile get
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  exact pulse_widen_frame p _ _ _
    (pulse_field_out p k b v _ (.inl (by unfold pc at K; omega)))

private theorem dr_file_reset (p : Params) (x : BitVec p.w) :
    drainFile p ((widen p (reset p)).apply x)=0 := by
  have B : sourceBase p+sourceW p≤workW p := by
    unfold workW grantBase sealBase
    omega
  have W : 2^(sourceW p-2)<2^sourceW p := by
    have P : 0<(2:Nat)^(sourceW p-2) := Nat.pow_pos (by decide)
    calc
      _ < 2^(sourceW p-2)*2^2 := by omega
      _ = _ := by
        rw [←Nat.pow_add,show sourceW p-2+2=sourceW p by unfold sourceW; omega]
  have H := dr_field_get p x (sourceBase p) (sourceW p)
    (2^(sourceW p-2)) 0 (19+2*d p) B (by unfold sourceW; omega) W
  have E : sourceW p-2=(19+2*d p)+o p := by unfold sourceW; omega
  have Z : 2^(sourceW p-2)%2^(19+2*d p)=0 := by
    rw [E,Nat.pow_add,Nat.mul_mod]
    simp
  simpa [drainFile,reset,Z] using H

private theorem dr_file_issue (p : Params) (x : BitVec p.w) :
    drainFile p ((widen p (resetIssue p)).apply x)=0 := by
  unfold resetIssue
  rw [reset0_widen_apply,dr_file_late p _ _ _ _ (by omega)]
  exact dr_file_reset p x

private theorem dr_file_done (p : Params) (x : BitVec p.w) :
    drainFile p ((widen p (resetWaitDone p)).apply x)=drainFile p x :=
  dr_file_late p x _ _ _ (Nat.le_refl _)

theorem drain_row_file_issue (p : Params) (hu : Bool) (u v : BitVec p.w)
    (P : sourcePhase p v=1) (O : sourceOpcode p v=0) :
    drainFile p ((row p (hu,true) (u,v)).2.apply v)=0 := by
  obtain ⟨a,H⟩ := row_reset0_issue_suffix p hu u v P O
  rw [H]
  change drainFile p ((widen p ((a.compose (resetIssue p)).compose
    (writeK p 0 reset0Forward))).apply v)=0
  rw [reset0_widen_apply,dr_file_frame p _ _ (drSK p _ _),reset0_widen_apply]
  exact dr_file_issue p _

theorem drain_row_file_left (p : Params) (hv : Bool) (u v : BitVec p.w) :
    drainFile p ((row p (true,hv) (u,v)).1.apply u)=drainFile p u := by
  rw [dr_row_eq]
  rw [reset0Post_left]
  exact dr_file_frame p _ _ (drSleft p hv u v)

theorem drain_row_file_wait (p : Params) (hu : Bool) (u v : BitVec p.w)
    (P : sourcePhase p v=2) (O : sourceOpcode p v=0)
    (H : publicationToken p true v 0=T ∨
      publicationToken p true v 0=reset0Forward ∨
      publicationToken p true v 0=reset0Reply) :
    drainFile p ((row p (hu,true) (u,v)).2.apply v)=drainFile p v := by
  have F := dr_file_frame p _ v (drSright p hu u v)
  rw [dr_row_eq]
  unfold reset0Post
  simp only [if_true]
  rcases H with H|H|H
  · have R := source_reset0_hold p v (oldK p true v 0) P O
        (.inl (congrArg MISByteCodec.Token.tag H))
    simp only [R,reset0_empty_comp]
    exact F
  · have R := source_reset0_hold p v (oldK p true v 0) P O
        (.inr (congrArg MISByteCodec.Token.tag H))
    simp only [R,reset0_empty_comp]
    exact F
  · change oldK p true v 0=reset0Reply at H
    rw [H,show reset0Reply=({tag:=3,opcode:=0}:Tok) from rfl,
      source_reset0_consume p v P O]
    dsimp only
    rw [reset0_widen_apply,dr_file_frame p _ _ (drSK p _ _),
      reset0_widen_apply,dr_file_done]
    exact F

/-! Seal field: all right effects either hold the seal or clear it.
On the left, only lane 1 can set it. A RESET lane-1 departure forces
zero; after it has passed, its own T/D/E cannot set it. -/

private def drSealFrame (p : Params) (a : Patch (workW p)) : Prop :=
  ∀ i,sealBase p≤i → i<sealBase p+5 → a.mask.getLsbD i=false

private theorem drSealEmptyFrame (p : Params) : drSealFrame p (.empty _) :=
  fun i _ _=>by simp [Patch.empty]

private theorem drSealCompFrame {p : Params} {a b : Patch (workW p)}
    (A : drSealFrame p a) (B : drSealFrame p b) : drSealFrame p (a.compose b) :=
  fun i L U=>pulse_comp_out (A i L U) (B i L U)

private theorem drSealField (p : Params) (k b v : Nat)
    (A : k+b≤sealBase p ∨ sealBase p+5≤k) :
    drSealFrame p (field p k b v) := by
  intro i L U
  apply pulse_field_out
  rcases A with A|A
  · exact .inr (by omega)
  · exact .inl (by omega)

private theorem drSealEarly (p : Params) (k b v : Nat)
    (H : k+b≤sealBase p) : drSealFrame p (field p k b v) :=
  drSealField p k b v (.inl H)

private theorem drSealReset (p : Params) : drSealFrame p (reset p) :=
  drSealEarly p _ _ _ (by unfold sealBase; omega)

private theorem drSealCtrl (p : Params) (a b : Nat) : drSealFrame p (ctrl p a b) :=
  drSealEarly p _ _ _ (by unfold pc sealBase sourceW; omega)

private theorem drSealSF (p : Params) (k b v : Nat) (H : k+b≤sourceW p) :
    drSealFrame p (sf p k b v) :=
  drSealEarly p _ _ _ (by unfold sealBase; omega)

private theorem drSealIfPair (p : Params) (Q : Prop) [Decidable Q]
    (a b : Patch (workW p) × Option Tok)
    (A : drSealFrame p a.1) (B : drSealFrame p b.1) :
    drSealFrame p (if Q then a else b).1 := by
  by_cases H : Q
  · rwa [if_pos H]
  · rwa [if_neg H]

-- CHECK: proof follows cmtSource, ReportByteRows.lean:711–765,
-- with the protected interval changed to the seal's five bits.
private theorem drSealSource (p : Params) (x : BitVec p.w) (t : Tok) :
    drSealFrame p (source p x t).1 := by
  have C := drSealCtrl p
  have R := drSealReset p
  have E := drSealEmptyFrame p
  have hPhase : drSealFrame p (field p (pc p+o p) 2 2) := by
    apply drSealEarly
    unfold pc sealBase sourceW
    omega
  have fld (j b v : Nat) (F : j+b≤21+2*d p) : drSealFrame p (sf p j b v) :=
    drSealSF p _ _ _ (by unfold sourceW; omega)
  have hInit (op : Nat) : drSealFrame p (if op==0 then reset p else .empty _) := by
    split
    · exact R
    · exact E
  unfold source
  dsimp only
  apply drSealIfPair
  · exact R
  apply drSealIfPair
  · apply drSealIfPair
    · exact R
    · exact drSealCompFrame (hInit _) hPhase
  apply drSealIfPair
  · exact E
  apply drSealIfPair
  · exact R
  apply drSealIfPair
  · exact C _ _
  apply drSealIfPair
  · exact C _ _
  apply drSealIfPair
  · apply drSealIfPair
    · exact C _ _
    · exact R
  apply drSealIfPair
  · exact drSealCompFrame (drSealCompFrame (C _ _) (fld _ _ _ (by omega))) (fld _ _ _ (by omega))
  apply drSealIfPair
  · apply drSealIfPair
    · exact R
    apply drSealIfPair
    · apply drSealIfPair
      · exact drSealCompFrame (C _ _) (fld _ _ _ (by omega))
      · exact drSealCompFrame (drSealCompFrame (drSealCompFrame (C _ _) (fld _ _ _ (by omega)))
          (fld _ _ _ (by omega))) (fld _ _ _ (by omega))
    · exact drSealCompFrame (drSealCompFrame (drSealCompFrame (C _ _) (fld _ _ _ (by omega)))
        (fld _ _ _ (by omega))) (fld _ _ _ (by omega))
  apply drSealIfPair
  · exact C _ _
  apply drSealIfPair
  · exact C _ _
  · exact R

private def drSealSafe (p : Params) (a : Patch (workW p)) : Prop :=
  ∀ x : BitVec p.w,drainSealZero p x→drainSealZero p ((widen p a).apply x)

private theorem drSealFrameSafe (p : Params) (a : Patch (workW p))
    (A : drSealFrame p a) : drSealSafe p a := by
  intro x H i L U
  exact (pulse_widen_frame p a x i (A i L U)).trans (H i L U)

private theorem drSealComp {p : Params} {a b : Patch (workW p)}
    (A : drSealSafe p a) (B : drSealSafe p b) : drSealSafe p (a.compose b) := by
  intro x H
  rw [reset0_widen_apply]
  exact B _ (A _ H)

private theorem drSealEmpty (p : Params) : drSealSafe p (.empty _) :=
  drSealFrameSafe p _ (drSealEmptyFrame p)

private theorem drSealK (p : Params) (j : Fin 3) (t : Tok) :
    drSealSafe p (writeK p j t) :=
  drSealFrameSafe p _ (drSealEarly p _ _ _
    (by have := reset0SlotBound p j; unfold sealBase; omega))

private theorem drSealClear (p : Params) (x : BitVec p.w) :
    drainSealZero p ((widen p (writeSeal p none)).apply x) := by
  intro i L U
  have F : i<workW p := by unfold workW grantBase; omega
  have W := layout_size p
  have K : i<p.w := by omega
  have H := pulse_field_write p (sealBase p) 5 0 i L U F
  have M : (widen p (writeSeal p none)).mask.getLsbD i=true := by
    simp [widen,writeSeal,K,H.1]
  rw [Patch.write _ _ _ M]
  simp [widen,writeSeal,K,H.2]

private theorem drSealClearSafe (p : Params) : drSealSafe p (writeSeal p none) :=
  fun x _=>drSealClear p x

private theorem drSealLate (p : Params) (k b v : Nat) (K : sealBase p+5≤k) :
    drSealSafe p (field p k b v) :=
  drSealFrameSafe p _ (drSealField p k b v (.inr K))

private theorem drSealGrants (p : Params) (g : Fin 3→Bool) : drSealSafe p (grants p g) :=
  drSealLate p _ _ _ (by unfold grantBase; omega)

private theorem drSealPulse (p : Params) (h : Bool) (side : Nat) (x : BitVec p.w) :
    drSealSafe p (pulse p h side x) :=
  drSealFrameSafe p _ (fun i L _=>pulse_mask_below_tail p h side x i
    (by unfold sealBase sourceBase at L; omega))

private theorem drSealNorm (p : Params) (j : Fin 3) (a : Patch (workW p))
    (H : a=.empty _ ∨ ∃ t,a=writeK p j t) : drSealSafe p a := by
  rcases H with rfl|⟨t,rfl⟩
  · exact drSealEmpty p
  · exact drSealK p j t

-- CHECK: effect branch projections, ReportByteRows.lean:243–275.
private theorem drSealEffectL (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) (t : Tok)
    (H : j≠1 ∨ DrainLetter t) :
    drSealSafe p (effect p u v hu hv j k win t).1 := by
  rcases H with J|H
  · unfold effect
    dsimp only
    have B : (j==1)=false := by simp [J]
    simp only [B,Bool.and_false,Bool.false_and,Bool.false_eq_true,if_false]
    repeat' first
      | exact drSealEmpty p
      | split
  · have O : t.opcode=0 := by rcases H with rfl|rfl|rfl|rfl <;> rfl
    have F : t.fault=false := by rcases H with rfl|rfl|rfl|rfl <;> rfl
    have C : ¬cmpOp p≤0 := by unfold cmpOp; omega
    have W : ¬writeOp p≤0 := by unfold writeOp; omega
    -- CHECK: the same opcode-zero simplification as reset0_effect (1475).
    cases hu <;> by_cases J : j=1 <;>
      simp [effect,O,F,parked,reset0_commit_ne,reset0_admit_ne,
        reset0_acq_ne,reset0_seal_ne,C,W,J,drSealClearSafe,drSealEmpty]

private theorem drSealEffectR (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) (t : Tok) :
    drSealSafe p (effect p u v hu hv j k win t).2.1 := by
  have S (ix : Nat) : drSealSafe p (field p (grantBase p+3) 1 ix) :=
    drSealLate p _ _ _ (by unfold grantBase; omega)
  have B (ix a : Nat) : drSealSafe p (field p (bankOffset p ix+2*d p) 3 a) :=
    drSealLate p _ _ _ (by unfold bankOffset; omega)
  unfold effect
  dsimp only
  generalize (if t.opcode < readOp p then cmpOp p else readOp p) = opBase
  split
  · exact drSealEmpty p
  split
  · split
    · exact drSealComp (drSealComp (S _) (drSealClearSafe p)) (B _ _)
    · exact drSealEmpty p
  split
  · exact drSealEmpty p
  split
  · exact drSealEmpty p
  split
  · exact drSealEmpty p
  split
  · exact drSealEmpty p
  split
  · split <;> exact drSealEmpty p
  · split
    · split <;> exact drSealEmpty p
    · exact drSealEmpty p

private theorem drSealTransportL (p : Params) (hu hv : Bool) (u v x : BitVec p.w)
    (win : Fin 3→Bool) (ab : Pair (Patch (workW p)))
    (l : Fin 3 × Option (Fin 3))
    (H : l.1≠1 ∨ DrainLetter (oldK p hu u l.1))
    (A : drainSealZero p ((widen p ab.1).apply x)) :
    drainSealZero p ((widen p (cmtRoute p hu hv u v win ab l).1).apply x) := by
  rcases ab with ⟨a,b⟩
  rcases l with ⟨j,k⟩
  have EF := drSealEffectL p u v hu hv j k (win j) (oldK p hu u j) H
  let t := oldK p hu u j
  unfold cmtRoute
  dsimp only
  by_cases R : ready p hu u j t=true
  · rw [if_pos R]
    cases k with
    | none =>
      rw [reset0_widen_apply,reset0_widen_apply]
      exact drSealK p j (terminal p (effect p u v hu hv j none (win j)
        (oldK p hu u j)).2.2) _ (EF _ A)
    | some k =>
      rw [reset0_widen_apply,reset0_widen_apply]
      exact drSealK p j T _ (EF _ A)
  · rw [if_neg R]
    by_cases Fwd : (t.tag==2)=true
    · rw [if_pos Fwd]
      exact A
    · rw [if_neg Fwd]
      cases k with
      | none =>
        dsimp only
        by_cases Trail : (t.tag==1)=true
        · rw [if_pos Trail,reset0_widen_apply]
          exact drSealK p j E _ A
        · rw [if_neg Trail]
          exact A
      | some k =>
        dsimp only
        let q := oldK p hv v k
        by_cases Reply : (q.tag==3)=true
        · rw [if_pos Reply,reset0_widen_apply]
          exact drSealK p j q _ A
        · rw [if_neg Reply]
          by_cases Trail : (t.tag==1 && q.tag==0)=true
          · rw [if_pos Trail,reset0_widen_apply]
            exact drSealK p j E _ A
          · rw [if_neg Trail]
            exact A

private theorem drSealRouteL (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3→Bool) (ab : Pair (Patch (workW p)))
    (l : Fin 3 × Option (Fin 3))
    (H : l.1≠1 ∨ DrainLetter (oldK p hu u l.1)) (A : drSealSafe p ab.1) :
    drSealSafe p (cmtRoute p hu hv u v win ab l).1 := by
  intro x X
  exact drSealTransportL p hu hv u v x win ab l H (A x X)

private theorem drSealRouteR (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3→Bool) (ab : Pair (Patch (workW p)))
    (l : Fin 3 × Option (Fin 3)) (A : drSealSafe p ab.2) :
    drSealSafe p (cmtRoute p hu hv u v win ab l).2 := by
  rcases ab with ⟨a,b⟩
  rcases l with ⟨j,k⟩
  have EF := drSealEffectR p u v hu hv j k (win j) (oldK p hu u j)
  let t := oldK p hu u j
  unfold cmtRoute
  dsimp only
  by_cases R : ready p hu u j t=true
  · rw [if_pos R]
    cases k with
    | none => exact drSealComp (p:=p) A EF
    | some k =>
      let out := effect p u v hu hv j (some k) (win j) (oldK p hu u j)
      exact drSealComp (p:=p) (drSealComp (p:=p) A EF) (drSealK p k (arrival p hv v k out.2.2))
  · rw [if_neg R]
    by_cases Fwd : (t.tag==2)=true
    · rw [if_pos Fwd]
      exact A
    · rw [if_neg Fwd]
      cases k with
      | none => exact A
      | some k =>
        dsimp only
        let q := oldK p hv v k
        by_cases Reply : (q.tag==3)=true
        · rw [if_pos Reply]
          exact drSealComp (p:=p) A (drSealK p k E)
        · rw [if_neg Reply]
          by_cases Trail : (t.tag==1 && q.tag==0)=true
          · rw [if_pos Trail]
            exact A
          · rw [if_neg Trail]
            exact A

private theorem drSealFoldL (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3→Bool) (xs : List (Fin 3 × Option (Fin 3)))
    (ab : Pair (Patch (workW p))) (A : drSealSafe p ab.1)
    (H : DrainLetter (oldK p hu u 1)) :
    drSealSafe p (xs.foldl (cmtRoute p hu hv u v win) ab).1 := by
  induction xs generalizing ab with
  | nil => exact A
  | cons l xs ih =>
    apply ih
    apply drSealRouteL p hu hv u v win ab l _ A
    by_cases J : l.1=1
    · exact .inr (by rw [J]; exact H)
    · exact .inl J

private theorem drSealFoldR (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (win : Fin 3→Bool) (xs : List (Fin 3 × Option (Fin 3)))
    (ab : Pair (Patch (workW p))) (A : drSealSafe p ab.2) :
    drSealSafe p (xs.foldl (cmtRoute p hu hv u v win) ab).2 := by
  induction xs generalizing ab with
  | nil => exact A
  | cons l xs ih => exact ih _ (drSealRouteR p hu hv u v win ab l A)

private theorem drSealPrefix (p : Params) (base pulseP : Patch (workW p))
    (norm : Fin 3→Patch (workW p)) (A : drSealSafe p base)
    (B : drSealSafe p pulseP) (N : ∀ j,drSealSafe p (norm j)) :
    drSealSafe p (drPrefix p base pulseP norm) :=
  drSealComp (drSealComp (drSealComp (drSealComp A B) (N 0)) (N 1)) (N 2)

private theorem drSealPreL (p : Params) (hv : Bool) (u v : BitVec p.w) :
    drSealSafe p (drPre p true hv u v).1 :=
  drSealPrefix p _ _ _ (drSealGrants p _) (drSealPulse p true 2 u)
    (fun j=>drSealNorm p j _ (dr_norm_left_shape p true u j))

private theorem drSealPreR (p : Params) (hu : Bool) (u v : BitVec p.w) :
    drSealSafe p (drPre p hu true u v).2 := by
  have A : drSealSafe p (drBaseR p true v) := by
    unfold drBaseR
    simp only [if_true]
    split
    · exact drSealGrants p _
    · exact drSealEmpty p
  exact drSealPrefix p _ _ _ A (drSealPulse p true 1 v)
    (fun j=>drSealNorm p j _ (dr_norm_right_shape p true v j))

theorem drain_row_seal_hold_left (p : Params) (hv : Bool) (u v : BitVec p.w)
    (H : DrainLetter (publicationToken p true u 1)) (A : drainSealZero p u) :
    drainSealZero p ((row p (true,hv) (u,v)).1.apply u) := by
  rw [dr_row_eq,reset0Post_left]
  exact drSealFoldL p true hv u v (drWin p true u) (links hv)
    (drPre p true hv u v) (drSealPreL p hv u v) H u A

theorem drain_row_seal_hold_right (p : Params) (hu : Bool) (u v : BitVec p.w)
    (A : drainSealZero p v) :
    drainSealZero p ((row p (hu,true) (u,v)).2.apply v) := by
  have F := drSealFoldR p hu true u v (drWin p hu u) (links true)
    (drPre p hu true u v) (drSealPreR p hu u v)
  have G := drSealFrameSafe p _ (drSealSource p v (oldK p true v 0))
  rw [dr_row_eq]
  unfold reset0Post
  simp only [if_true]
  apply drSealComp (drSealComp F G) _ v A
  split
  · exact drSealEmpty p
  · exact drSealK p 0 _

-- CHECK: reset0_route_hop and reset0_widen_apply, ReportByteRows.lean:1510–1519,1726–1729.
private theorem drSealHop (p : Params) (hv : Bool) (u v : BitVec p.w)
    (win : Fin 3→Bool) (ab : Pair (Patch (workW p))) (k : Fin 3)
    (H : oldK p true u 1=reset0Forward) :
    drainSealZero p ((widen p (cmtRoute p true hv u v win ab (1,some k)).1).apply u) := by
  rcases ab with ⟨a,b⟩
  rw [reset0_route_hop p true hv u v win a b 1 k H]
  simp only [Bool.true_and,show ((1 : Fin 3)==1)=true by decide,if_true]
  rw [reset0_widen_apply,reset0_widen_apply]
  exact drSealK p 1 T _ (drSealClear p _)

theorem drain_row_seal_release (p : Params) (hv : Bool) (u v : BitVec p.w)
    (H : publicationToken p true u 1=reset0Forward) :
    drainSealZero p ((row p (true,hv) (u,v)).1.apply u) := by
  rw [dr_row_eq,reset0Post_left]
  let win := drWin p true u
  -- CHECK: links and cmtRoute, ReportByteRows.lean:277–278,767–803.
  -- The lane-1 link is always internal; the final lane 2 cannot set seal.
  cases hv
  · let a := cmtRoute p true false u v win (drPre p true false u v) (0,some 0)
    let b := cmtRoute p true false u v win a (1,some 1)
    change drainSealZero p ((widen p
      (cmtRoute p true false u v win b (2,some 2)).1).apply u)
    have B : drainSealZero p ((widen p b.1).apply u) := drSealHop p false u v win a 1 H
    exact drSealTransportL p true false u v u win b (2,some 2) (.inl (by decide)) B
  · let a := cmtRoute p true true u v win (drPre p true true u v) (0,some 1)
    let b := cmtRoute p true true u v win a (1,some 2)
    change drainSealZero p ((widen p
      (cmtRoute p true true u v win b (2,none)).1).apply u)
    have B : drainSealZero p ((widen p b.1).apply u) := drSealHop p true u v win a 2 H
    exact drSealTransportL p true true u v u win b (2,none) (.inl (by decide)) B

end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

def rankGate (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3) : Bool :=
  gate p h x j

theorem rankGate_iff (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3) :
    rankGate p h x j=true ↔ j=1 ∧
      (if h then 0 else min (max 3 p.digits)
        (x.extractLsb' (workW p+1) (ell (max 3 p.digits+1))).toNat)=2 := by
  unfold rankGate gate geomOff get
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨H,O⟩
    exact ⟨Fin.ext H,O⟩
  · rintro ⟨rfl,O⟩
    exact ⟨rfl,O⟩

theorem rankToken_wire (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3) :
    publicationToken p h x j=decode p (rankGate p h x j) (resetTokenRead p x j) := rfl

def rankReady (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3) : Bool :=
  ready p h x j (oldK p h x j)

theorem rankReady_iff (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3) :
    rankReady p h x j=true ↔
      (publicationToken p h x j).tag=2 ∧
      ¬(healthyAdmit p (publicationToken p h x j) ∧
        rankGate p h x j=true ∧ (publicationToken p h x j).race<4) := by
  -- CHECK: ReportByteRows.lean:215–218,2570–2572.
  change _ ↔ (oldK p h x j).tag=2 ∧
    ¬(healthyAdmit p (oldK p h x j) ∧ gate p h x j=true ∧
      (oldK p h x j).race<4)
  by_cases H : (oldK p h x j).tag=2
  · cases F0 : (oldK p h x j).fault <;> cases G : gate p h x j <;>
      simp [rankReady, ready, parked, healthyAdmit, H, F0, G] <;> omega
  · simp [rankReady, ready, H]

/-- None means preserve the exact old wire, including spare payload bits. -/
def rankNormIntent (p : Params) (side : Nat) (g : Bool) (t : Tok) : Option Tok :=
  if t.fault then some t else
  if t.tag==2 && t.opcode==admitOp p && g &&
      (t.race==1 || t.race==(if side=3 then 2 else 3)) then
    some (advanceRace t side)
  else none

def rankNormWire (p : Params) (side : Nat) (g : Bool)
    (w : BitVec (tokenW p)) : BitVec (tokenW p) :=
  (rankNormIntent p side g (decode p g w)).elim w (resetTokenWire p)

private def rankNormPatch (p : Params) (side : Nat) (h : Bool)
    (x : BitVec p.w) (j : Fin 3) : Patch (workW p) :=
  (rankNormIntent p side (rankGate p h x j) (oldK p h x j)).elim
    (.empty _) (writeK p j)

private theorem rank_normL_patch (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3) :
    outgoingNormalize p h x j=rankNormPatch p 3 h x j := by
  unfold outgoingNormalize rankNormPatch rankNormIntent parked rankGate
  cases H : (oldK p h x j).fault <;> simp [H, Bool.and_assoc]
  split <;> rfl

private theorem rank_normR_patch (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3) :
    cmtNorm p h x j=rankNormPatch p 2 h x j := by
  unfold cmtNorm rankNormPatch rankNormIntent parked rankGate
  cases H : (oldK p h x j).fault <;> simp [H, Bool.and_assoc]
  split <;> rfl

private theorem rank_norm_self (p : Params) (side : Nat) (h : Bool)
    (x : BitVec p.w) (j : Fin 3) (a : Patch (workW p))
    (A : resetTokenRead p ((widen p a).apply x) j=resetTokenRead p x j) :
    resetTokenRead p ((widen p (a.compose (rankNormPatch p side h x j))).apply x) j =
      rankNormWire p side (rankGate p h x j) (resetTokenRead p x j) := by
  unfold rankNormPatch rankNormWire
  change _ = (rankNormIntent p side (rankGate p h x j) (oldK p h x j)).elim
    (resetTokenRead p x j) (resetTokenWire p)
  cases H : rankNormIntent p side (rankGate p h x j) (oldK p h x j) with
  | none => simpa only [Option.elim,reset0_empty_comp] using A
  | some t => exact reset0_compKSame p j a x t

private theorem rank_norm_other (p : Params) (side : Nat) (h : Bool)
    (x : BitVec p.w) (j k : Fin 3) (J : j≠k) (a : Patch (workW p)) :
    resetTokenRead p ((widen p (a.compose (rankNormPatch p side h x k))).apply x) j =
      resetTokenRead p ((widen p a).apply x) j := by
  unfold rankNormPatch
  cases H : rankNormIntent p side (rankGate p h x k) (oldK p h x k) with
  | none => simp only [Option.elim, reset0_empty_comp]
  | some t => exact reset0_compKOther p j k J t a x

private theorem rank_base_read (p : Params) (h : Bool) (side : Nat)
    (x : BitVec p.w) (j : Fin 3) (base : Patch (workW p))
    (B : reset0Frame p base) :
    resetTokenRead p ((widen p (base.compose (pulse p h side x))).apply x) j =
      resetTokenRead p x j := by
  rw [reset0_widen_apply]
  have F : ∀ i,i<tokenW p→(pulse p h side x).mask.getLsbD (kOffset p j+i)=false := by
    intro i _
    exact pulse_mask_below_tail p h side x _ (by unfold kOffset; omega)
  exact (reset0_read_hold p j _ _ F).trans (reset0_read_frame p j base x B)

private theorem rank_prefix_read (p : Params) (h : Bool) (side pulseSide : Nat)
    (x : BitVec p.w) (j : Fin 3) (base : Patch (workW p))
    (B : reset0Frame p base) :
    resetTokenRead p
      ((widen p (drPrefix p base (pulse p h pulseSide x) (rankNormPatch p side h x))).apply x) j =
      rankNormWire p side (rankGate p h x j) (resetTokenRead p x j) := by
  have A := rank_base_read p h pulseSide x j base B
  have J : j=0 ∨ j=1 ∨ j=2 := by
    have H := j.isLt
    rcases (show j.val=0 ∨ j.val=1 ∨ j.val=2 by omega) with H|H|H
    · exact .inl (Fin.ext H)
    · exact .inr (.inl (Fin.ext H))
    · exact .inr (.inr (Fin.ext H))
  unfold drPrefix
  rcases J with rfl|rfl|rfl
  · rw [rank_norm_other p side h x 0 2 (by decide),
        rank_norm_other p side h x 0 1 (by decide)]
    exact rank_norm_self p side h x 0 _ A
  · rw [rank_norm_other p side h x 1 2 (by decide)]
    apply rank_norm_self
    rw [rank_norm_other p side h x 1 0 (by decide)]
    exact A
  · apply rank_norm_self
    rw [rank_norm_other p side h x 2 1 (by decide),
        rank_norm_other p side h x 2 0 (by decide)]
    exact A

private theorem rank_preL (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (j : Fin 3) :
    resetTokenRead p ((widen p (drPre p hu hv u v).1).apply u) j =
      rankNormWire p 3 (rankGate p hu u j) (resetTokenRead p u j) := by
  unfold drPre
  dsimp only
  have H : outgoingNormalize p hu u=rankNormPatch p 3 hu u :=
    funext (rank_normL_patch p hu u)
  rw [H]
  exact rank_prefix_read p hu 3 2 u j _ (dr_baseL_frame p hu u)

private theorem rank_preR (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (k : Fin 3) :
    resetTokenRead p ((widen p (drPre p hu hv u v).2).apply v) k =
      rankNormWire p 2 (rankGate p hv v k) (resetTokenRead p v k) := by
  unfold drPre
  dsimp only
  have H : cmtNorm p hv v=rankNormPatch p 2 hv v :=
    funext (rank_normR_patch p hv v)
  rw [H]
  exact rank_prefix_read p hv 2 1 v k _ (dr_baseR_frame p hv v)

/-- Old router's actual overwrite intents, NOT a second transition of
    the already normalized bytes. The final right source is handled
    separately by reset0Post_right and the selected destination law. -/
def rankRouteL (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (k : Option (Fin 3)) : Option Tok :=
  let t := oldK p hu u j
  if rankReady p hu u j then
    match k with
    | none => some (terminal p (effect p u v hu hv j k (drWin p hu u j) t).2.2)
    | some _ => some T
  else if t.tag==2 then none
  else match k with
  | none => if t.tag==1 then some E else none
  | some r =>
    let z := oldK p hv v r
    if z.tag==3 then some z
    else if t.tag==1 && z.tag==0 then some E else none

def rankRouteR (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) : Option Tok :=
  let t := oldK p hu u j
  if rankReady p hu u j then
    some (arrival p hv v k (effect p u v hu hv j (some k) (drWin p hu u j) t).2.2)
  else if t.tag==2 then none
  else if (oldK p hv v k).tag==3 then some E else none

private theorem rank_routeL_read (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (a : Pair (Patch (workW p))) (j : Fin 3)
    (k : Option (Fin 3)) :
    resetTokenRead p ((widen p (cmtRoute p hu hv u v (drWin p hu u) a (j,k)).1).apply u) j =
      (rankRouteL p hu hv u v j k).elim
        (resetTokenRead p ((widen p a.1).apply u) j) (resetTokenWire p) := by
  rcases a with ⟨a,b⟩
  cases k with
  | none =>
    unfold rankRouteL rankReady cmtRoute
    dsimp only
    by_cases R : ready p hu u j (oldK p hu u j)=true
    · simp only [if_pos R, Option.elim]
      exact reset0_compKSame p j _ u _
    · simp only [if_neg R]
      by_cases F0 : ((oldK p hu u j).tag == 2)=true
      · simp only [if_pos F0, Option.elim]
      · simp only [if_neg F0]
        by_cases T0 : ((oldK p hu u j).tag == 1)=true
        · simp only [if_pos T0, Option.elim]
          exact reset0_compKSame p j a u E
        · simp only [if_neg T0, Option.elim]
  | some k =>
    unfold rankRouteL rankReady cmtRoute
    dsimp only
    by_cases R : ready p hu u j (oldK p hu u j)=true
    · simp only [if_pos R, Option.elim]
      exact reset0_compKSame p j _ u T
    · simp only [if_neg R]
      by_cases F0 : ((oldK p hu u j).tag == 2)=true
      · simp only [if_pos F0, Option.elim]
      · simp only [if_neg F0]
        by_cases D0 : ((oldK p hv v k).tag == 3)=true
        · simp only [if_pos D0, Option.elim]
          exact reset0_compKSame p j a u _
        · simp only [if_neg D0]
          by_cases TE : (((oldK p hu u j).tag == 1) && ((oldK p hv v k).tag == 0))=true
          · simp only [if_pos TE, Option.elim]
            exact reset0_compKSame p j a u E
          · simp only [if_neg TE, Option.elim]

private theorem rank_routeR_read (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (a : Pair (Patch (workW p))) (j k : Fin 3) :
    resetTokenRead p ((widen p (cmtRoute p hu hv u v (drWin p hu u) a (j,some k)).2).apply v) k =
      (rankRouteR p hu hv u v j k).elim
        (resetTokenRead p ((widen p a.2).apply v) k) (resetTokenWire p) := by
  rcases a with ⟨a,b⟩
  unfold rankRouteR rankReady cmtRoute
  dsimp only
  split
  · exact reset0_compKSame p k _ v _
  · split
    · rfl
    · split
      · exact reset0_compKSame p k b v _
      · split <;> rfl

-- Finite six cases; no predicate over unbounded raw words is decided.
private theorem rank_split (hv : Bool) (j : Fin 3) :
    ∃ pre suf : List (Fin 3 × Option (Fin 3)),
      links hv=pre++(j,reset0Destination hv j)::suf ∧
      (∀ l∈pre++suf,j≠l.1) ∧
      (∀ k,reset0Destination hv j=some k→
        (hv=true→k≠0) ∧ ∀ l∈pre++suf,some k≠l.2) := by
  have J : j=0 ∨ j=1 ∨ j=2 := by
    have H := j.isLt
    rcases (show j.val=0 ∨ j.val=1 ∨ j.val=2 by omega) with H|H|H
    · exact .inl (Fin.ext H)
    · exact .inr (.inl (Fin.ext H))
    · exact .inr (.inr (Fin.ext H))
  rcases J with rfl|rfl|rfl <;> cases hv
  · exact ⟨[],[(1,some 1),(2,some 2)],rfl,by decide,by decide⟩
  · exact ⟨[],[(1,some 2),(2,none)],rfl,by decide,by decide⟩
  · exact ⟨[(0,some 0)],[(2,some 2)],rfl,by decide,by decide⟩
  · exact ⟨[(0,some 1)],[(2,none)],rfl,by decide,by decide⟩
  · exact ⟨[(0,some 0),(1,some 1)],[],rfl,by decide,by decide⟩
  · exact ⟨[(0,some 1),(1,some 2)],[],rfl,by decide,by decide⟩

theorem rank_row_left (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) :
    resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j =
      (rankRouteL p hu hv u v j (reset0Destination hv j)).elim
        (rankNormWire p 3 (rankGate p hu u j) (resetTokenRead p u j)) (resetTokenWire p) := by
  obtain ⟨pre,suf,L,A,_⟩ := rank_split hv j
  have P : ∀ l∈pre,j≠l.1 := fun l H=>A l (List.mem_append.mpr (.inl H))
  have S : ∀ l∈suf,j≠l.1 := fun l H=>A l (List.mem_append.mpr (.inr H))
  rw [dr_row_eq]
  dsimp only
  rw [reset0Post_left]
  unfold drRouted
  rw [L,List.foldl_append,List.foldl_cons,reset0_foldL _ _ _ _ _ _ _ _ _ S,
    rank_routeL_read,reset0_foldL _ _ _ _ _ _ _ _ _ P,rank_preL]

theorem rank_row_right (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (D : reset0Destination hv j=some k) :
    resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k =
      (rankRouteR p hu hv u v j k).elim
        (rankNormWire p 2 (rankGate p hv v k) (resetTokenRead p v k)) (resetTokenWire p) := by
  obtain ⟨pre,suf,L,_,A⟩ := rank_split hv j
  obtain ⟨N,A⟩ := A k D
  have P : ∀ l∈pre,some k≠l.2 := fun l H=>A l (List.mem_append.mpr (.inl H))
  have S : ∀ l∈suf,some k≠l.2 := fun l H=>A l (List.mem_append.mpr (.inr H))
  rw [dr_row_eq]
  dsimp only
  rw [reset0Post_right _ _ _ _ _ N]
  unfold drRouted
  rw [L,List.foldl_append,List.foldl_cons,D,reset0_foldR _ _ _ _ _ _ _ _ _ S,
    rank_routeR_read,reset0_foldR _ _ _ _ _ _ _ _ _ P,rank_preR]

-- Export the precise branch equations so downstream code never has to
-- unfold a private production effect or private normalizer.
theorem rank_hop_left (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (D : reset0Destination hv j=some k)
    (R : rankReady p hu u j=true) :
    resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j=resetTokenWire p T := by
  rw [rank_row_left,D]
  simp [rankRouteL,R]

theorem rank_reverse_pair (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (D : reset0Destination hv j=some k)
    (N : (publicationToken p hu u j).tag≠2)
    (R : (publicationToken p hv v k).tag=3) :
    resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j=
      resetTokenWire p (publicationToken p hv v k) ∧
    resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k=resetTokenWire p E := by
  change (oldK p hu u j).tag≠2 at N
  change (oldK p hv v k).tag=3 at R
  have NR : rankReady p hu u j=false := by simp [rankReady,ready,N]
  rw [rank_row_left,D,rank_row_right p hu hv u v j k D]
  simp [rankRouteL,rankRouteR,NR,N,R]

theorem rank_clear_left (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (T0 : (publicationToken p hu u j).tag=1)
    (H : reset0Destination hv j=none ∨
      ∃ k,reset0Destination hv j=some k ∧ (publicationToken p hv v k).tag=0) :
    resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j=resetTokenWire p E := by
  change (oldK p hu u j).tag=1 at T0
  have NR : rankReady p hu u j=false := by simp [rankReady,ready,T0]
  rw [rank_row_left]
  rcases H with D|⟨k,D,Z⟩
  · simp [rankRouteL,D,NR,T0]
  · change (oldK p hv v k).tag=0 at Z
    simp [rankRouteL,D,NR,T0,Z]

theorem rank_idle_left (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (NR : rankReady p hu u j=false)
    (H : (publicationToken p hu u j).tag=2 ∨
      ((publicationToken p hu u j).tag≠2 ∧
        match reset0Destination hv j with
        | none => (publicationToken p hu u j).tag≠1
        | some k => (publicationToken p hv v k).tag≠3 ∧
            ¬((publicationToken p hu u j).tag=1 ∧
              (publicationToken p hv v k).tag=0))) :
    resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j=
      rankNormWire p 3 (rankGate p hu u j) (resetTokenRead p u j) := by
  rw [rank_row_left]
  rcases H with H|⟨H,A⟩
  · change (oldK p hu u j).tag=2 at H
    simp [rankRouteL,NR,H]
  · change (oldK p hu u j).tag≠2 at H
    cases D : reset0Destination hv j with
    | none =>
      rw [D] at A
      change (oldK p hu u j).tag≠1 at A
      simp [rankRouteL,NR,H,A]
    | some k =>
      rw [D] at A
      change (oldK p hv v k).tag≠3 ∧
        ¬((oldK p hu u j).tag=1 ∧ (oldK p hv v k).tag=0) at A
      simp [rankRouteL,NR,H,A.1,A.2, Bool.and_eq_true, beq_iff_eq]

theorem rank_idle_right (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (D : reset0Destination hv j=some k)
    (NR : rankReady p hu u j=false)
    (H : (publicationToken p hu u j).tag=2 ∨ (publicationToken p hv v k).tag≠3) :
    resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k=
      rankNormWire p 2 (rankGate p hv v k) (resetTokenRead p v k) := by
  rw [rank_row_right p hu hv u v j k D]
  rcases H with H|H
  · change (oldK p hu u j).tag=2 at H
    simp [rankRouteR,NR,H]
  · change (oldK p hv v k).tag≠3 at H
    simp [rankRouteR,NR,H]

end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
set_option backward.split false
structure RankFits (p : Params) (t : Tok) : Prop where
  tag : t.tag<4
  op : t.opcode<2^o p
  payload : t.payload<2^payW p
  race : t.race<8
  outcome : t.outcome<4

private def rPack (w l u : Nat) : Nat := l+2^w*u

private theorem rPack_lt {w v l u : Nat}
    (L : l<2^w) (U : u<2^v) : rPack w l u<2^(w+v) := by
  unfold rPack
  rw [Nat.pow_add]
  have B := Nat.mul_le_mul_left (2^w) (show u+1≤2^v by omega)
  rw [Nat.mul_succ] at B
  omega

private theorem rPack_div {w l u : Nat} (L : l<2^w) :
    rPack w l u / 2^w=u := by
  unfold rPack
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt L,Nat.zero_add]

private theorem rPack_mod {w l u : Nat} (L : l<2^w) :
    rPack w l u % 2^w=l := by
  unfold rPack
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt L]

private theorem rPack_extract {w k b l u : Nat} (L : l<2^w) :
    (rPack w l u / 2^(w+k))%2^b=(u/2^k)%2^b := by
  rw [Nat.pow_add,←Nat.div_div_eq_div_mul,rPack_div L]

private def rCode (p : Params) (t : Tok) : Nat :=
  rPack (payW p) t.payload
    (rPack 1 t.applied.toNat
      (rPack 2 t.outcome
        (rPack 3 t.race
          (rPack (o p) t.opcode (rPack 1 t.fault.toNat t.tag)))))

private theorem rCode_eq (p : Params) (t : Tok) : encode p t=rCode p t := by
  unfold encode rCode rPack
  dsimp only
  rw [show 7+o p+payW p=payW p+1+2+3+o p+1 by omega,
    show 6+o p+payW p=payW p+1+2+3+o p by omega,
    show payW p+6=payW p+1+2+3 by omega,
    show payW p+3=payW p+1+2 by omega]
  simp only [Nat.pow_add,Nat.mul_add]
  ac_rfl

private theorem rCode_lt (p : Params) (t : Tok) (H : RankFits p t) :
    rCode p t<2^tokenW p := by
  have f : t.fault.toNat<2^1 := by cases t.fault <;> decide
  have a : t.applied.toNat<2^1 := by cases t.applied <;> decide
  have A := rPack_lt (v:=2) f H.tag
  have B := rPack_lt H.op A
  have C := rPack_lt (show t.race<2^3 from H.race) B
  have D := rPack_lt (show t.outcome<2^2 from H.outcome) C
  have E := rPack_lt a D
  have G := rPack_lt H.payload E
  unfold rCode tokenW
  simpa only [show payW p+(1+(2+(3+(o p+(1+2)))))=9+o p+payW p by omega] using G

private theorem rWire_nat (p : Params) (t : Tok) (H : RankFits p t) :
    (resetTokenWire p t).toNat=rCode p t := by
  rw [resetTokenWire,BitVec.toNat_ofNat,rCode_eq,Nat.mod_eq_of_lt (rCode_lt p t H)]

private theorem rGet_nat {w : Nat} (x : BitVec w) (k b : Nat) :
    get x k b=x.toNat/2^k%2^b := by
  -- CHECK: same extraction identity as dr_field_sub.
  rw [get,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]

/-- The seven exact non-overlapping wire fields. This avoids any
    claim that malformed padding roundtrips to the original raw word. -/
private theorem rReadFields (p : Params) (t : Tok) (H : RankFits p t) :
    get (resetTokenWire p t) (7+o p+payW p) 2=t.tag ∧
    get (resetTokenWire p t) (6+o p+payW p) 1=t.fault.toNat ∧
    get (resetTokenWire p t) (payW p+6) (o p)=t.opcode ∧
    get (resetTokenWire p t) (payW p+3) 3=t.race ∧
    get (resetTokenWire p t) (payW p+1) 2=t.outcome ∧
    get (resetTokenWire p t) (payW p) 1=t.applied.toNat ∧
    get (resetTokenWire p t) 0 (payW p)=t.payload := by
  have f : t.fault.toNat<2^1 := by cases t.fault <;> decide
  have a : t.applied.toNat<2^1 := by cases t.applied <;> decide
  have r : t.race<2^3 := H.race
  have z : t.outcome<2^2 := H.outcome
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [rGet_nat,rWire_nat p t H]
    unfold rCode
    rw [show 7+o p+payW p=payW p+(1+(2+(3+(o p+(1+(0)))))) by omega]
    rw [rPack_extract H.payload]
    rw [rPack_extract a]
    rw [rPack_extract z]
    rw [rPack_extract r]
    rw [rPack_extract H.op]
    rw [rPack_extract f]
    simp only [Nat.pow_zero,Nat.div_one]
    exact Nat.mod_eq_of_lt H.tag
  · rw [rGet_nat,rWire_nat p t H]
    unfold rCode
    rw [show 6+o p+payW p=payW p+(1+(2+(3+(o p+(0))))) by omega]
    rw [rPack_extract H.payload]
    rw [rPack_extract a]
    rw [rPack_extract z]
    rw [rPack_extract r]
    rw [rPack_extract H.op]
    simp only [Nat.pow_zero,Nat.div_one]
    exact rPack_mod f
  · rw [rGet_nat,rWire_nat p t H]
    unfold rCode
    rw [show payW p+6=payW p+(1+(2+(3+(0)))) by omega]
    rw [rPack_extract H.payload]
    rw [rPack_extract a]
    rw [rPack_extract z]
    rw [rPack_extract r]
    simp only [Nat.pow_zero,Nat.div_one]
    exact rPack_mod H.op
  · rw [rGet_nat,rWire_nat p t H]
    unfold rCode
    rw [show payW p+3=payW p+(1+(2+(0))) by omega]
    rw [rPack_extract H.payload]
    rw [rPack_extract a]
    rw [rPack_extract z]
    simp only [Nat.pow_zero,Nat.div_one]
    exact rPack_mod r
  · rw [rGet_nat,rWire_nat p t H]
    unfold rCode
    rw [show payW p+1=payW p+(1+(0)) by omega]
    rw [rPack_extract H.payload]
    rw [rPack_extract a]
    simp only [Nat.pow_zero,Nat.div_one]
    exact rPack_mod z
  · rw [rGet_nat,rWire_nat p t H]
    unfold rCode
    rw [rPack_div H.payload]
    exact rPack_mod a
  · rw [rGet_nat,rWire_nat p t H]
    unfold rCode
    simp only [Nat.pow_zero,Nat.div_one]
    exact rPack_mod H.payload

private theorem rGet_bit {w : Nat} (x : BitVec w) (k : Nat) :
    x.getLsbD k=decide (get x k 1=1) := by
  -- CHECK: BitVec.getLsbD and Nat.testBit_eq_decide_div_mod_eq;
  -- same identity as selector_toNat.
  rw [rGet_nat,BitVec.getLsbD,Nat.testBit_eq_decide_div_mod_eq]

theorem rank_decode_tag (p : Params) (g : Bool) (w : BitVec (tokenW p)) :
    (decode p g w).tag=get w (7+o p+payW p) 2 := by
  unfold decode
  dsimp only
  split
  · rename_i h
    exact (beq_iff_eq.mp h).symm
  · split
    · rename_i h
      exact (beq_iff_eq.mp h).symm
    · repeat' first | rfl | split

theorem rank_tag_lt (p : Params) (g : Bool) (w : BitVec (tokenW p)) :
    (decode p g w).tag<4 := by
  rw [rank_decode_tag]
  exact (w.extractLsb' (7+o p+payW p) 2).isLt

theorem rank_encode_tag (p : Params) (g : Bool) (t : Tok) (H : RankFits p t) :
    (decode p g (resetTokenWire p t)).tag=t.tag := by
  rw [rank_decode_tag,(rReadFields p t H).1]

private theorem rFault_fits (p : Params) (tag : Nat) (H : tag<4) :
    RankFits p (F tag) := by
  refine ⟨H,Nat.two_pow_pos _,Nat.two_pow_pos _,by exact (show (0 : Nat) < 8 by decide),?_⟩
  change (if tag==3 then 2 else 0)<4
  split <;> decide

private theorem rE_fits (p : Params) : RankFits p E :=
  ⟨by decide,Nat.two_pow_pos _,Nat.two_pow_pos _,by decide,by decide⟩

private theorem rT_fits (p : Params) : RankFits p T :=
  ⟨by decide,Nat.two_pow_pos _,Nat.two_pow_pos _,by decide,by decide⟩

theorem rank_decoded_fits (p : Params) (g : Bool) (w : BitVec (tokenW p)) :
    RankFits p (decode p g w) := by
  have T0 : get w (7+o p+payW p) 2<4 := (w.extractLsb' _ 2).isLt
  have O0 : get w (payW p+6) (o p)<2^o p := (w.extractLsb' _ _).isLt
  have R0 : get w (payW p+3) 3<8 := (w.extractLsb' _ 3).isLt
  have U0 : get w (payW p+1) 2<4 := (w.extractLsb' _ 2).isLt
  have Q0 : get w 0 (payW p)<2^payW p := (w.extractLsb' 0 _).isLt
  have Q (k : Nat) : get w 0 (payW p)%2^k<2^payW p :=
    Nat.lt_of_le_of_lt (Nat.mod_le _ _) Q0
  unfold decode
  dsimp only
  repeat' first
  | exact rE_fits p
  | exact rT_fits p
  | exact rFault_fits p _ T0
  | exact ⟨T0,O0,Q _,R0,by change 0 < 4; decide⟩
  | exact ⟨T0,O0,Nat.two_pow_pos _,by change 0 < 8; decide,U0⟩
  | exact ⟨T0,O0,Q _,by change 0 < 8; decide,U0⟩
  | split

theorem rank_reverse_tag (p : Params) (g g' : Bool) (w : BitVec (tokenW p)) :
    (decode p g' (resetTokenWire p (decode p g w))).tag=(decode p g w).tag :=
  rank_encode_tag p g' _ (rank_decoded_fits p g w)

private theorem rDecoded_fault (p : Params) (g : Bool) (w : BitVec (tokenW p))
    (H : (decode p g w).fault=true) :
    decode p g w=F (decode p g w).tag ∧
      ((decode p g w).tag=2 ∨ (decode p g w).tag=3) := by
  revert H
  let P (t : Tok) := t.fault=true → t=F t.tag ∧ (t.tag=2 ∨ t.tag=3)
  change P (decode p g w)
  have B : get w (7+o p+payW p) 2 < 4 := (w.extractLsb' _ 2).isLt
  unfold decode
  dsimp only
  repeat' first
  | (intro H; exact Bool.noConfusion H)
  | (change P (F (get w (7+o p+payW p) 2)); intro _; refine ⟨rfl,?_⟩
     change (get w (7+o p+payW p) 2 = 2 ∨ get w (7+o p+payW p) 2 = 3)
     have N0 : get w (7+o p+payW p) 2 ≠ 0 := fun H => ‹¬(_ == 0) = true› (beq_iff_eq.mpr H)
     have N1 : get w (7+o p+payW p) 2 ≠ 1 := fun H => ‹¬(_ == 1) = true› (beq_iff_eq.mpr H)
     omega)
  | split

private theorem rFault_roundtrip (p : Params) (g : Bool) (tag : Nat)
    (H : tag=2 ∨ tag=3) :
    decode p g (resetTokenWire p (F tag))=F tag := by
  have B : tag<4 := by omega
  have A := rReadFields p (F tag) (rFault_fits p tag B)
  have J : (resetTokenWire p (F tag)).getLsbD (6+o p+payW p)=true := by
    rw [rGet_bit,A.2.1]
    rfl
  have G : get (resetTokenWire p (F tag)) (7+o p+payW p) 2 = tag := A.1
  rcases H with rfl|rfl <;> simp [decode,G,J]

/-- Uniquely valid healthy parked ADMIT syntax at the actual true gate.
    Decoder does not permit race 0, 6 or 7 as live parked races. -/
theorem rank_admit_shape (p : Params) (w : BitVec (tokenW p))
    (H : healthyAdmit p (decode p true w)) :
    ∃ q r : Nat, q<2 ∧ 1≤r ∧ r≤5 ∧
      decode p true w={tag:=2,opcode:=admitOp p,payload:=q,race:=r} := by
  have T0 := H.1
  rw [rank_decode_tag] at T0
  revert H
  let P (t : Tok) := healthyAdmit p t → ∃ q r : Nat, q<2 ∧ 1≤r ∧ r≤5 ∧
      t={tag:=2,opcode:=admitOp p,payload:=q,race:=r}
  change P (decode p true w)
  unfold decode
  simp only [T0,show ((2:Nat)==0)=false by decide,
    show ((2:Nat)==1)=false by decide,beq_self_eq_true,if_true,
    Bool.false_eq_true,if_false,Bool.true_and]
  repeat' first
  | (change P (F 2); intro H; exact Bool.noConfusion H.2.1)
  | (change P ({tag:=2,opcode:=_,payload:=_,race:=_,applied:=_} : Tok);
     intro H
     have O : get w (payW p+6) (o p)=admitOp p := H.2.2
     have A : admitOp p≠acqOp p := by unfold admitOp acqOp; omega
     have C : admitOp p≠commitOp p := by unfold admitOp commitOp; omega
     have RR : 1≤get w (payW p+3) 3 ∧ get w (payW p+3) 3≤5 := by
       first | trivial | simp_all [Bool.or_eq_true,beq_iff_eq] <;> omega
     refine ⟨get w 0 (payW p)%2,get w (payW p+3) 3,
       Nat.mod_lt _ (by decide),RR.1,RR.2,?_⟩
     simp [O,C] <;> simp_all [admitOp,acqOp] <;> omega)
  | split

private theorem rAdmit_roundtrip (p : Params) (q r : Nat)
    (Q : q<2) (R : 1≤r) (S : r≤5) :
    decode p true (resetTokenWire p
      ({tag:=2,opcode:=admitOp p,payload:=q,race:=r} : Tok))=
      {tag:=2,opcode:=admitOp p,payload:=q,race:=r} := by
  let t : Tok := {tag:=2,opcode:=admitOp p,payload:=q,race:=r}
  have O : admitOp p<2^o p := by
    have B := power_of_ell (5+4*p.digits)
    unfold o admitOp
    omega
  have P : q<2^payW p := Nat.lt_of_lt_of_le Q
    (Nat.pow_le_pow_right (show 1 ≤ (2:Nat) by decide) (by unfold payW; omega : 1≤payW p))
  have Fit : RankFits p t := ⟨by change 2 < 4; decide,O,P,by dsimp [t]; omega,by change 0 < 4; decide⟩
  have B := rReadFields p t Fit
  have F0 : (resetTokenWire p t).getLsbD (6+o p+payW p)=false := by
    rw [rGet_bit,B.2.1]
    rfl
  have A : admitOp p≠acqOp p := by unfold admitOp acqOp; omega
  have C : admitOp p≠commitOp p := by unfold admitOp commitOp; omega
  have D : ¬commitOp p<admitOp p := by unfold admitOp commitOp; omega
  have E : ¬cmpOp p≤admitOp p := by unfold admitOp cmpOp; omega
  have W : ¬writeOp p≤admitOp p := by unfold admitOp writeOp; omega
  have V : ¬sealOp p≤admitOp p := by unfold admitOp sealOp; omega
  change decode p true (resetTokenWire p t)=t
  simp [decode,B.1,B.2.2.1,B.2.2.2.1,B.2.2.2.2.1,
    B.2.2.2.2.2.2,F0,t,A,C,D,E,W,V,
    show ¬r<1 by omega,show ¬5<r by omega,Nat.mod_eq_of_lt Q]

/-- Normalization on the SAME true gate. Explicit hypotheses identify
    the two actual progress races of a particular incidence. -/
theorem rank_norm_race (p : Params) (w : BitVec (tokenW p))
    (side : Nat) (S : side=2 ∨ side=3)
    (H : healthyAdmit p (decode p true w))
    (R : (decode p true w).race=1 ∨
        (decode p true w).race=(if side=3 then 2 else 3)) :
    decode p true (rankNormWire p side true w)=
      {(decode p true w) with race:=admitRaceAfter side (decode p true w).race} := by
  obtain ⟨q,r,Q,L,U,E⟩ := rank_admit_shape p w H
  rw [E] at R
  rcases S with rfl|rfl
  · rcases R with R|R
    · have R' : r=1 := R
      subst r
      simp [rankNormWire,rankNormIntent,E,advanceRace,admitRaceAfter,
        rAdmit_roundtrip p q 2 Q (by decide) (by decide)]
    · have R' : r=3 := R
      subst r
      simp [rankNormWire,rankNormIntent,E,advanceRace,admitRaceAfter,
        rAdmit_roundtrip p q 5 Q (by decide) (by decide)]
  · rcases R with R|R
    · have R' : r=1 := R
      subst r
      simp [rankNormWire,rankNormIntent,E,advanceRace,admitRaceAfter,
        rAdmit_roundtrip p q 3 Q (by decide) (by decide)]
    · have R' : r=2 := R
      subst r
      simp [rankNormWire,rankNormIntent,E,advanceRace,admitRaceAfter,
        rAdmit_roundtrip p q 4 Q (by decide) (by decide)]

theorem rank_norm_cases (p : Params) (g : Bool) (w : BitVec (tokenW p))
    (side : Nat) (S : side=2 ∨ side=3) :
    let t := decode p g w
    let t' := decode p g (rankNormWire p side g w)
    t'=t ∨
      (g=true ∧ t.tag=2 ∧ t.fault=false ∧ t'.tag=2 ∧ t'.fault=false ∧
        ((t.race=1 ∧ (t'.race=2 ∨ t'.race=3)) ∨
         (t.race=2 ∧ t'.race=4) ∨ (t.race=3 ∧ t'.race=5))) := by
  dsimp only
  let t := decode p g w
  by_cases F0 : t.fault=true
  · obtain ⟨E,R⟩ := rDecoded_fault p g w F0
    left
    unfold rankNormWire rankNormIntent
    rw [if_pos F0]
    change decode p g (resetTokenWire p t)=t
    have W := congrArg (resetTokenWire p) E
    rw [W]
    exact (rFault_roundtrip p g t.tag R).trans E.symm
  · have F1 : t.fault=false := Bool.eq_false_iff.mpr F0
    by_cases P : t.tag=2 ∧ t.opcode=admitOp p ∧ g=true ∧
        (t.race=1 ∨ t.race=(if side=3 then 2 else 3))
    · obtain ⟨T0,O0,G,R⟩ := P
      subst g
      have H : healthyAdmit p t := ⟨T0,F1,O0⟩
      have E := rank_norm_race p w side S H R
      right
      refine ⟨rfl,T0,F1,?_,?_,?_⟩
      · rw [E]; exact T0
      · rw [E]; exact F1
      · rw [E]
        rcases S with rfl|rfl <;> rcases R with R|R <;>
          simp [admitRaceAfter,show (decode p true w).race = _ from R]
    · left
      unfold rankNormWire rankNormIntent
      have B : (t.tag==2 && t.opcode==admitOp p && g &&
          (t.race==1 || t.race==(if side=3 then 2 else 3)))=false := by
        apply Bool.eq_false_iff.mpr
        intro B
        apply P
        simpa [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,and_assoc] using B
      change decode p g
        ((if t.fault then some t else if
           t.tag==2 && t.opcode==admitOp p && g &&
            (t.race==1 || t.race==(if side=3 then 2 else 3))
          then some (advanceRace t side) else none).elim w (resetTokenWire p))=t
      simp [F1,B,t]
end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol
set_option backward.split false
theorem rank_parked_shape (p : Params) (h : Bool) (u : BitVec p.w)
    (j : Fin 3) (T0 : (publicationToken p h u j).tag=2)
    (R : rankReady p h u j=false) :
    healthyAdmit p (publicationToken p h u j) ∧ rankGate p h u j=true ∧
      1≤(publicationToken p h u j).race ∧ (publicationToken p h u j).race<4 := by
  have A : ¬rankReady p h u j=true := by rw [R]; decide
  rw [rankReady_iff] at A
  have P : healthyAdmit p (publicationToken p h u j) ∧
      rankGate p h u j=true ∧ (publicationToken p h u j).race<4 := by
    apply Classical.byContradiction
    intro X
    exact A ⟨T0,X⟩
  obtain ⟨H,G,L⟩ := P
  rw [rankToken_wire,G] at H
  obtain ⟨q,r,_,P,_,E⟩ := rank_admit_shape p _ H
  refine ⟨?_,G,?_,L⟩
  · rwa [rankToken_wire,G]
  · rw [rankToken_wire,G,E]
    exact P

private theorem rTerminal_dest (hv : Bool) (j : Fin 3)
    (D : reset0Destination hv j=none) : hv=true ∧ j=2 := by
  cases hv
  · simp [reset0Destination] at D
  · refine ⟨rfl,?_⟩
    by_cases J : j=2
    · exact J
    · simp [reset0Destination,J] at D

private theorem rTerminal_effect (p : Params) (hu : Bool) (u v : BitVec p.w)
    (win : Bool) (t : Tok) (H : RankFits p t) :
    let z := (effect p u v hu true 2 none win t).2.2
    z.opcode<2^o p ∧ (z.opcode=admitOp p→z.payload<2^payW p) := by
  dsimp only
  have A : ∀ q : Nat, t.opcode=acqOp p →
      ({t with payload:=q} : Tok).opcode<2^o p ∧
        (({t with payload:=q} : Tok).opcode=admitOp p →
          ({t with payload:=q} : Tok).payload<2^payW p) := by
    intro q O
    refine ⟨H.op,?_⟩
    intro E
    change t.opcode=admitOp p at E
    unfold acqOp at O
    unfold admitOp at E
    omega
  have B : ∀ q : Nat, cmpOp p≤t.opcode →
      ({t with payload:=q} : Tok).opcode<2^o p ∧
        (({t with payload:=q} : Tok).opcode=admitOp p →
          ({t with payload:=q} : Tok).payload<2^payW p) := by
    intro q O
    refine ⟨H.op,?_⟩
    intro E
    change t.opcode=admitOp p at E
    unfold cmpOp at O
    unfold admitOp at E
    omega
  have I : t.opcode<2^o p ∧ (t.opcode=admitOp p→t.payload<2^payW p) :=
    ⟨H.op,fun _=>H.payload⟩
  -- CHECK: effect branches at 243–275; j=2, k=none excludes
  -- COMMIT crossing, ADMIT gate, RESET/WRITE/SEAL at K1.
  by_cases F0 : t.fault=true
  · simpa [effect,F0] using I
  · have F1 : t.fault=false := Bool.eq_false_iff.mpr F0
    simp only [effect,F1,Bool.false_eq_true,if_false,parked,gate,
      show ((2:Fin 3)==0)=false by decide,
      show ((2:Fin 3)==1)=false by decide,
      show ((2:Fin 3).val==1)=false by decide,
      Bool.and_false,Bool.false_and,Bool.and_true,
      show ((2:Fin 3)==2)=true by decide,Bool.or_true]
    split
    · rename_i K
      apply A
      exact beq_iff_eq.mp ((Bool.and_eq_true _ _).mp K).2
    · generalize (if t.opcode<readOp p then cmpOp p else readOp p) = off
      split
      · rename_i K
        apply B
        have X := ((Bool.and_eq_true _ _).mp K).1
        exact of_decide_eq_true ((Bool.and_eq_true _ _).mp X).1
      · exact I

private theorem rTerminal_fit (p : Params) (t : Tok)
    (O : t.opcode<2^o p)
    (P : t.opcode=admitOp p→t.payload<2^payW p) :
    (terminal p t).tag=3 ∧ RankFits p (terminal p t) := by
  have A : 64≤2^payW p := Nat.pow_le_pow_right (show 1≤(2:Nat) by decide)
    (by unfold payW; omega : 6≤payW p)
  have B : 2^(2*d p)≤2^payW p := Nat.pow_le_pow_right (show 1≤(2:Nat) by decide)
    (by unfold payW; omega)
  unfold terminal
  split
  · exact ⟨rfl,rFault_fits p 3 (by decide)⟩
  · split
    · split
      · exact ⟨rfl,⟨by change 3 < 4; decide,O,Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) A,
          by change 0 < 8; decide,by change 0 < 4; decide⟩⟩
      · exact ⟨rfl,⟨by change 3 < 4; decide,O,Nat.two_pow_pos _,by change 0 < 8; decide,by change 1 < 4; decide⟩⟩
    · refine ⟨rfl,⟨by change 3 < 4; decide,O,?_,by change 0 < 8; decide,by change 0 < 4; decide⟩⟩
      split
      · rename_i H
        exact P (beq_iff_eq.mp H)
      · split
        · exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) B
        · exact Nat.two_pow_pos _

theorem rank_turn_tag (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (D : reset0Destination hv j=none)
    (R : rankReady p hu u j=true) (g' : Bool) :
    (decode p g' (resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j)).tag=3 := by
  obtain ⟨rfl,rfl⟩ := rTerminal_dest hv j D
  let t := oldK p hu u 2
  let z := (effect p u v hu true 2 none (drWin p hu u 2) t).2.2
  have H : RankFits p t := rank_decoded_fits p _ _
  have V : z.opcode<2^o p ∧ (z.opcode=admitOp p→z.payload<2^payW p) :=
    rTerminal_effect p hu u v _ t H
  have A := rTerminal_fit p z V.1 V.2
  rw [rank_row_left,D]
  simp only [rankRouteL,R,if_true,Option.elim]
  exact (rank_encode_tag p g' _ A.2).trans A.1

end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxHeartbeats 1000000

/-- Illegal source control restarts, irrespective of the inherited K0 word. -/
theorem prelaunch_invalid_source (p : Params) (raw : BitVec p.w) (t : Tok)
    (H : sourcePhase p raw=0 ∨ sourcePhase p raw=3 ∨ commitOp p<sourceOpcode p raw) :
    source p raw t=(reset p,some E) := by
  unfold source
  dsimp only
  have V : (sourcePhase p raw==0 || sourcePhase p raw==3 ||
      decide (commitOp p<sourceOpcode p raw))=true := by
    rcases H with H|H|H <;> simp [H]
  exact if_pos V

/-- A valid WAIT with old trail/forward does not overwrite the root K lane.
The conditional is on the old token, not the token written by normalization. -/
theorem prelaunch_wait_hold (p : Params) (raw : BitVec p.w) (t : Tok)
    (P : sourcePhase p raw=2) (O : sourceOpcode p raw≤commitOp p)
    (H : t.tag=1 ∨ t.tag=2) :
    source p raw t=(Patch.empty _,none) := by
  have V : ¬commitOp p<sourceOpcode p raw := Nat.not_lt_of_ge O
  unfold sourcePhase at P
  unfold source
  dsimp only
  unfold sourceOpcode at V
  simp only [P,V,decide_false]
  rcases H with H|H <;> simp [H]

/-- On a valid WAIT an empty old K0 always causes a source restart.
This is the local source part of the all-empty-chart nomination. -/
theorem prelaunch_wait_empty (p : Params) (raw : BitVec p.w) (t : Tok)
    (P : sourcePhase p raw=2) (O : sourceOpcode p raw≤commitOp p)
    (H : t.tag=0) : source p raw t=(reset p,some E) := by
  have V : ¬commitOp p<sourceOpcode p raw := Nat.not_lt_of_ge O
  unfold sourcePhase at P
  unfold source
  dsimp only
  unfold sourceOpcode at V
  simp [P,V,H]

/-- Valid WAIT discards anything other than a matching healthy non-denial D
(after ruling out the held forward/trail cases). -/
theorem prelaunch_wait_bad_reply (p : Params) (raw : BitVec p.w) (t : Tok)
    (P : sourcePhase p raw=2) (O : sourceOpcode p raw≤commitOp p)
    (H1 : t.tag≠1) (H2 : t.tag≠2)
    (H : t.tag≠3 ∨ t.opcode≠sourceOpcode p raw ∨ t.fault=true ∨ t.outcome=1) :
    source p raw t=(reset p,some E) := by
  have V : ¬commitOp p<sourceOpcode p raw := Nat.not_lt_of_ge O
  unfold sourcePhase at P
  unfold sourceOpcode at V H
  rcases H with H|H|H|H <;> simp [source,P,V,H1,H2,H]

/-- A valid ISSUE either retries from canonical ISSUE0 (bad file), or
writes a healthy original-opcode F and enters the WAIT phase.
No property of the inherited root K0 is presumed. -/
theorem prelaunch_issue_action (p : Params) (raw : BitVec p.w) (t : Tok)
    (P : sourcePhase p raw=1) (O : sourceOpcode p raw≤commitOp p) :
    source p raw t=(reset p,some E) ∨
      ∃ payload : Nat, source p raw t=
        ((if sourceOpcode p raw=0 then reset p else Patch.empty _).compose
            (field p (pc p+o p) 2 2),
          some ({tag:=2, opcode:=sourceOpcode p raw, payload:=payload} : Tok)) := by
  have V : ¬commitOp p<sourceOpcode p raw := Nat.not_lt_of_ge O
  unfold sourcePhase at P
  unfold sourceOpcode at V ⊢
  unfold source
  dsimp only
  simp only [P,V,decide_false,show ((1:Nat)==0)=false by decide,
    show ((1:Nat)==3)=false by decide, Bool.false_or, Bool.false_eq_true,
    if_false, beq_self_eq_true, if_true]
  split
  · exact .inl rfl
  · apply Or.inr
    simp only [beq_iff_eq]
    exact ⟨_,rfl⟩

/-- Exact responder root normalization before the overriding source write.
The parked healthy 1/3 case uses incoming race 2, while inherited faults
are re-encoded canonically with the same old decoded tag. -/
def prelaunchDoorNormWire (p : Params) (v : BitVec p.w) : BitVec (tokenW p) :=
  let t := oldK p true v 0
  if t.fault then resetTokenWire p t
  else if parked p t true v 0 && (t.race==1 || t.race==3) then
    resetTokenWire p (advanceRace t 2)
  else resetTokenRead p v 0

private theorem prelaunch_door_prefix (p : Params) (hu : Bool) (u v : BitVec p.w) :
    resetTokenRead p ((widen p (drRouted p hu true u v).2).apply v) 0 =
        prelaunchDoorNormWire p v := by
  have fold := reset0_foldR p hu true u v (drWin p hu u) (links true)
    (drPre p hu true u v) 0 (fun l M=>by
      rw [dr_link_dest true l M]
      exact Ne.symm (dr_no_root_dest l.1))
  unfold drRouted
  rw [fold]
  change resetTokenRead p ((widen p (drPrefix p (drBaseR p true v) (pulse p true 1 v)
    (cmtNorm p true v))).apply v) 0 = _
  unfold drPrefix
  let a := (drBaseR p true v).compose (pulse p true 1 v)
  have unaffected (j : Fin 3) (J : (0 : Fin 3)≠j) (a' : Patch (workW p)) :
      resetTokenRead p ((widen p (a'.compose (cmtNorm p true v j))).apply v) 0 =
      resetTokenRead p ((widen p a').apply v) 0 := by
    rcases dr_norm_right_shape p true v j with S|⟨t,S⟩
    · rw [S,reset0_empty_comp]
    · rw [S]
      exact reset0_compKOther p 0 j J t a' v
  rw [unaffected 2 (by decide),unaffected 1 (by decide)]
  change resetTokenRead p ((widen p (a.compose (cmtNorm p true v 0))).apply v) 0 = _
  have base : resetTokenRead p ((widen p a).apply v) 0=resetTokenRead p v 0 := by
    unfold a
    rw [reset0_widen_apply]
    have F : ∀ i,i<tokenW p → (pulse p true 1 v).mask.getLsbD (kOffset p 0+i)=false := by
      intro i _
      exact pulse_mask_below_tail p true 1 v _ (by unfold kOffset; omega)
    exact (reset0_read_hold p 0 _ _ F).trans (reset0_read_frame p 0 _ _ (dr_baseR_frame p true v))
  unfold cmtNorm prelaunchDoorNormWire
  dsimp only
  by_cases F : (oldK p true v 0).fault=true
  · rw [if_pos F,if_pos F]
    exact reset0_compKSame p 0 a v _
  · rw [if_neg F,if_neg F]
    by_cases P : (parked p (oldK p true v 0) true v 0 &&
        ((oldK p true v 0).race==1 || (oldK p true v 0).race==3))=true
    · rw [if_pos P,if_pos P]
      exact reset0_compKSame p 0 a v _
    · rw [if_neg P,if_neg P,reset0_empty_comp]
      exact base

/-- Complete old-pair root K0 wire equation, after normalization, all
routed links and the right source override. The decision uses the old
root token even when that root is normalized on this same mark. -/
theorem prelaunch_door_final_wire (p : Params) (hu : Bool) (u v : BitVec p.w) :
    resetTokenRead p ((row p (hu,true) (u,v)).2.apply v) 0 =
      match (source p v (publicationToken p true v 0)).2 with
      | none => prelaunchDoorNormWire p v
      | some t => resetTokenWire p t := by
  rw [dr_row_eq]
  dsimp only
  change resetTokenRead p ((widen p (reset0Post p true v (drRouted p hu true u v)).2).apply v) 0 = _
  change _ = match (source p v (oldK p true v 0)).2 with
    | none => prelaunchDoorNormWire p v
    | some t => resetTokenWire p t
  have F := reset0Source p v (oldK p true v 0)
  unfold reset0Post
  simp only [if_true]
  cases S : source p v (oldK p true v 0) with
  | mk patch opt =>
    rw [S] at F
    cases opt with
    | none =>
      dsimp only
      rw [reset0_empty_comp]
      exact (reset0_compFrame p 0 (drRouted p hu true u v).2 patch v F).trans
        (prelaunch_door_prefix p hu u v)
    | some t => exact reset0_compKSame p 0 ((drRouted p hu true u v).2.compose patch) v t

private theorem prelaunch_after_controls (p : Params) (a q : Patch (workW p))
    (v : BitVec p.w) (F : drSrcFrame p a) :
    let y := (widen p q).apply ((widen p a).apply v)
    let x := (widen p q).apply v
    (sourcePhase p y,sourceOpcode p y)=(sourcePhase p x,sourceOpcode p x) := by
  have frame (k b : Nat) (L : sourceBase p≤k) (R : k+b≤sealBase p) :
      get ((widen p q).apply ((widen p a).apply v)) k b =
        get ((widen p q).apply v) k b := by
    unfold get
    apply congrArg BitVec.toNat
    apply BitVec.eq_of_getLsbD_eq
    intro j J
    have old := pulse_widen_frame p a v (k+j) (F _ (by omega) (by omega))
    simp only [BitVec.getLsbD_extractLsb',J,decide_true,Bool.true_and]
    change ((widen p a).apply v).getLsbD (k+j)=v.getLsbD (k+j) at old
    let bit := k+j
    let patch := widen p q
    have B (x : BitVec p.w) : (patch.apply x).getLsbD bit =
        ((x.getLsbD bit && (decide (bit<p.w) && !patch.mask.getLsbD bit)) ||
        (patch.value.getLsbD bit && patch.mask.getLsbD bit)) := by
      simp [Patch.apply]
    change (patch.apply ((widen p a).apply v)).getLsbD bit = (patch.apply v).getLsbD bit
    rw [B,B,old]
  dsimp only
  apply Prod.ext
  · exact frame _ _ (by unfold pc; omega) (by unfold pc sealBase sourceW; omega)
  · exact frame _ _ (by unfold pc; omega) (by unfold pc sealBase sourceW; omega)

/-- Complete responder control after the actual immutable-old pair:
the routed prefix frames the source window, and K0's final patch also
frames it. Thus phase/opcode are exactly the selected source action. -/
theorem prelaunch_door_final_control (p : Params) (hu : Bool) (u v : BitVec p.w) :
    let y := (row p (hu,true) (u,v)).2.apply v
    let x := (widen p (source p v (publicationToken p true v 0)).1).apply v
    (sourcePhase p y,sourceOpcode p y)=(sourcePhase p x,sourceOpcode p x) := by
  dsimp only
  rw [dr_row_eq]
  dsimp only
  change _ = (sourcePhase p ((widen p (source p v (oldK p true v 0)).1).apply v),
    sourceOpcode p ((widen p (source p v (oldK p true v 0)).1).apply v))
  unfold reset0Post
  simp only [if_true]
  cases S : source p v (oldK p true v 0) with
  | mk q opt =>
    cases opt with
    | none =>
      dsimp only
      rw [reset0_empty_comp,reset0_widen_apply]
      exact prelaunch_after_controls p _ q v (drSright p hu u v)
    | some t =>
      dsimp only
      rw [reset0_widen_apply,dr_K_source_frame,reset0_widen_apply]
      exact prelaunch_after_controls p _ q v (drSright p hu u v)

/-- Any non-forward/non-trail old WAIT word is consumed or rejected
and clears the root; none of the indexed arithmetic branches can emit F. -/
theorem prelaunch_wait_clears_token (p : Params) (raw : BitVec p.w) (t : Tok)
    (P : sourcePhase p raw=2) (O : sourceOpcode p raw≤commitOp p)
    (H1 : t.tag≠1) (H2 : t.tag≠2) :
    (source p raw t).2=some E := by
  have V : ¬commitOp p<sourceOpcode p raw := Nat.not_lt_of_ge O
  unfold sourcePhase at P
  unfold sourceOpcode at V
  unfold source
  dsimp only
  simp only [P,V,decide_false,show ((2:Nat)==0)=false by decide,
    show ((2:Nat)==3)=false by decide,show ((2:Nat)==1)=false by decide,
    Bool.false_or,Bool.false_eq_true,if_false,beq_false_of_ne H1,beq_false_of_ne H2]
  let a := get raw (pc p) (o p)
  let inp := rf p raw (9+2*d p) 4
  let out := rf p raw (5+2*d p) 4
  by_cases bad : (t.tag != 3 || t.opcode != a || t.fault || t.outcome==1)=true
  · rw [if_pos bad]
  rw [if_neg bad]
  by_cases zero : (a==0)=true
  · rw [if_pos zero]
  rw [if_neg zero]
  by_cases pace : a<admitOp p
  · rw [if_pos pace]
  rw [if_neg pace]
  by_cases adm : (a==admitOp p)=true
  · rw [if_pos adm]
    by_cases A : (t.payload==1)=true
    · rw [if_pos A]
    · rw [if_neg A]
  rw [if_neg adm]
  by_cases acq : (a==acqOp p)=true
  · rw [if_pos acq]
  rw [if_neg acq]
  by_cases rd : a<writeOp p
  · rw [if_pos rd]
    by_cases err : (inp/4==3 || inp%4==3 ||
        (!decide (a<readOp p) && (out/4==3 || out%4==3)))=true
    · rw [if_pos err]
    rw [if_neg err]
    by_cases cmp : a<readOp p
    · rw [if_pos cmp]
      by_cases more : a-(if a<readOp p then cmpOp p else readOp p)+1<p.digits
      · rw [if_pos more]
      · rw [if_neg more]
    · rw [if_neg cmp]
  · rw [if_neg rd]
    by_cases wr : a<sealOp p
    · rw [if_pos wr]
    · rw [if_neg wr]
      by_cases sealLast : (a==sealOp p)=true
      · rw [if_pos sealLast]
      · rw [if_neg sealLast]

/-- A real restart clears both control debts to ISSUE0, without
depending on any prior source bits. -/
theorem prelaunch_restart_controls (p : Params) (v : BitVec p.w) :
    let x := (widen p (reset p)).apply v
    (sourcePhase p x,sourceOpcode p x)=(1,0) := by
  dsimp only
  have F : sourceBase p+sourceW p≤workW p := by unfold workW grantBase sealBase; omega
  have M : 2^(sourceW p-2)<2^sourceW p := by
    apply Nat.pow_lt_pow_right (by decide)
    unfold sourceW
    omega
  have Div : 2^(sourceW p-2)/2^(19+2*d p)=2^o p := by
    rw [show sourceW p-2=(19+2*d p)+o p by unfold sourceW; omega,Nat.pow_add]
    exact Nat.mul_div_right _ (Nat.pow_pos (by decide))
  have S : sourceW p-2=19+2*d p+o p := by unfold sourceW; omega
  have T := dr_field_get p v (sourceBase p) (sourceW p) (2^(sourceW p-2))
    (sourceW p-2) 2 F (by unfold sourceW; omega) M
  have U := dr_field_get p v (sourceBase p) (sourceW p) (2^(sourceW p-2))
     (19+2*d p) (o p) F (by unfold sourceW; omega) M
  rw [Div,Nat.mod_self] at U
  have TT : (2^(sourceW p-2)/2^(sourceW p-2))%2^2=1 := by
    rw [Nat.div_self (Nat.pow_pos (by decide))]
  rw [TT] at T
  apply Prod.ext
  · unfold sourcePhase pc reset
    rw [show sourceBase p+19+2*d p+o p=sourceBase p+(sourceW p-2) by omega]
    exact T
  · simpa only [sourceOpcode,pc,reset,Nat.add_assoc] using U

private def prePostPC (p : Params) (q : Patch (workW p)) (v : BitVec p.w) : Nat × Nat :=
  let x := (widen p q).apply v
  (sourcePhase p x,sourceOpcode p x)

private theorem prelaunch_ctrl_write (p : Params) (v : BitVec p.w) (b : Nat)
    (B : b<4*p.digits+5) : prePostPC p (ctrl p 1 b) v=(1,b) := by
  have P := power_of_ell (5+4*p.digits)
  change 5+4*p.digits≤2^o p at P
  have HB : b<2^o p := by omega
  have V : 2^o p+b<2^(o p+2) := by rw [Nat.pow_add]; omega
  have F : pc p+(o p+2)≤workW p := by unfold pc workW grantBase sealBase sourceW; omega
  have H := dr_field_get p v (pc p) (o p+2) (2^o p+b) (o p) 2 F (by omega) V
  have O := dr_field_get p v (pc p) (o p+2) (2^o p+b) 0 (o p) F (by omega) V
  have D : (2^o p+b)/2^o p=1 := by
    rw [Nat.add_comm]
    calc
      _ = (b+(2^o p)*1)/2^o p := by rw [Nat.mul_one]
      _ = b/2^o p+1 := Nat.add_mul_div_left b 1 (Nat.pow_pos (by decide))
      _ = 1 := by simp [Nat.div_eq_of_lt HB]
  have M : (2^o p+b)%2^o p=b := by
    rw [Nat.add_mod,Nat.mod_self,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt HB]
  exact Prod.ext (by simpa [prePostPC,sourcePhase,ctrl,D] using H)
    (by simpa [prePostPC,sourceOpcode,ctrl,M] using O)

private theorem prelaunch_sf_frames_controls (p : Params) (k b x : Nat)
    (H : k+b≤19+2*d p) (v : BitVec p.w) :
    prePostPC p (sf p k b x) v=(sourcePhase p v,sourceOpcode p v) := by
  have bitFrame (k' b' : Nat) (L : pc p≤k') :
      get ((widen p (sf p k b x)).apply v) k' b'=get v k' b' := by
    unfold get
    apply congrArg BitVec.toNat
    apply BitVec.eq_of_getLsbD_eq
    intro i I
    simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
    exact pulse_widen_frame p _ v _ (pulse_field_out p _ _ _ _ (.inr (by unfold pc at L; omega)))
  exact Prod.ext (bitFrame _ _ (Nat.le_add_right _ _)) (bitFrame _ _ (Nat.le_refl _))

private theorem prelaunch_post_sf (p : Params) (q : Patch (workW p)) (k b x : Nat)
    (H : k+b≤19+2*d p) (v : BitVec p.w) :
    prePostPC p (q.compose (sf p k b x)) v=prePostPC p q v := by
  unfold prePostPC
  rw [reset0_widen_apply]
  exact prelaunch_sf_frames_controls p k b x H _

/-- Numerical op transition classification independent of its consumer. -/
inductive PreviewNextOp (t : Nat) : Nat → Nat → Prop where
  | linear {a : Nat} (H : a+1<2*t+3) : PreviewNextOp t a (a+1)
  | cmpLast (T : 0<t) : PreviewNextOp t (2*t+2) (2*t+3)
  | readWrite {j : Nat} (J : j<t) : PreviewNextOp t (2*t+3+j) (3*t+3+j)
  | writeRead {j : Nat} (J : j+1<t) : PreviewNextOp t (3*t+3+j) (2*t+3+(j+1))
  | writeSeal {j : Nat} (J : j+1=t) : PreviewNextOp t (3*t+3+j) (4*t+3)
  | sealCommit : PreviewNextOp t (4*t+3) (4*t+4)

theorem previewNextOp_bounds {t a b : Nat} (H : PreviewNextOp t a b) :
    a<4*t+5 ∧ b<4*t+5 := by cases H <;> omega

/-- Matching or dirty WAIT replies feed either canonical restart or
one of the six ordinal successor classes, after the real patch. -/
theorem prelaunch_wait_controls (p : Params) (raw : BitVec p.w) (t : Tok)
    (P : sourcePhase p raw=2) (O : sourceOpcode p raw≤commitOp p)
    (H1 : t.tag≠1) (H2 : t.tag≠2) (pos : 0<p.digits) :
    let y := prePostPC p (source p raw t).1 raw
    y=(1,0) ∨ ∃ b, PreviewNextOp p.digits (sourceOpcode p raw) b ∧ y=(1,b) := by
  dsimp only
  have V : ¬commitOp p<sourceOpcode p raw := Nat.not_lt_of_ge O
  unfold sourcePhase at P
  unfold sourceOpcode at V O ⊢
  unfold source
  dsimp only
  simp only [P,V,decide_false,show ((2:Nat)==0)=false by decide,
    show ((2:Nat)==3)=false by decide,show ((2:Nat)==1)=false by decide,
    Bool.false_or,Bool.false_eq_true,if_false,beq_false_of_ne H1,beq_false_of_ne H2]
  let a := get raw (pc p) (o p)
  let inp := rf p raw (9+2*d p) 4
  let out := rf p raw (5+2*d p) 4
  have R : prePostPC p (reset p) raw=(1,0) := prelaunch_restart_controls p raw
  have ctrl_ok (b : Nat) (E : PreviewNextOp p.digits a b) :
      prePostPC p (ctrl p 1 b) raw=(1,0) ∨
        ∃ b', PreviewNextOp p.digits a b' ∧ prePostPC p (ctrl p 1 b) raw=(1,b') := by
    have K : b<4*p.digits+5 := (previewNextOp_bounds E).2
    exact .inr ⟨b,E,prelaunch_ctrl_write p raw b K⟩
  by_cases bad : (t.tag != 3 || t.opcode != a || t.fault || t.outcome==1)=true
  · rw [if_pos bad]
    exact .inl R
  rw [if_neg bad]
  by_cases zero : (a==0)=true
  · rw [if_pos zero]
    have Z : a=0 := beq_iff_eq.mp zero
    have B : a+1=1 := by omega
    exact ctrl_ok 1 (by rw [←B]; exact .linear (by omega))
  rw [if_neg zero]
  by_cases pace : a<admitOp p
  · rw [if_pos pace]
    exact ctrl_ok (a+1) (.linear (by unfold admitOp at pace; omega))
  rw [if_neg pace]
  by_cases adm : (a==admitOp p)=true
  · rw [if_pos adm]
    by_cases A : (t.payload==1)=true
    · rw [if_pos A]
      have E : a=admitOp p := beq_iff_eq.mp adm
      exact ctrl_ok (acqOp p) (by
        rw [E,show acqOp p=admitOp p+1 by unfold acqOp admitOp; omega]
        exact .linear (by unfold admitOp; omega))
    · rw [if_neg A]
      exact .inl R
  rw [if_neg adm]
  by_cases acq : (a==acqOp p)=true
  · rw [if_pos acq]
    dsimp only
    rw [prelaunch_post_sf p _ _ _ _ (by omega),prelaunch_post_sf p _ _ _ _ (by omega)]
    have E : a=acqOp p := beq_iff_eq.mp acq
    exact ctrl_ok (cmpOp p) (by
      rw [E,show cmpOp p=acqOp p+1 by unfold cmpOp acqOp; omega]
      exact .linear (by unfold acqOp; omega))
  rw [if_neg acq]
  have low : cmpOp p≤a := by
    have A : a≠admitOp p := fun E => adm (beq_iff_eq.mpr E)
    have B : a≠acqOp p := fun E => acq (beq_iff_eq.mpr E)
    unfold cmpOp admitOp acqOp at *
    omega
  by_cases rd : a<writeOp p
  · rw [if_pos rd]
    by_cases err : (inp/4==3 || inp%4==3 ||
        (!decide (a<readOp p) && (out/4==3 || out%4==3)))=true
    · rw [if_pos err]
      exact .inl R
    rw [if_neg err]
    by_cases cmpC : a<readOp p
    · rw [if_pos cmpC]
      have K : get raw (pc p) (o p)<readOp p := cmpC
      simp only [if_pos K]
      by_cases more : a-cmpOp p+1<p.digits
      · rw [if_pos more]
        try dsimp only
        rw [prelaunch_post_sf p _ _ _ _ (by omega)]
        exact ctrl_ok (a+1) (.linear (by unfold cmpOp at more low; omega))
      · rw [if_neg more]
        try dsimp only
        rw [prelaunch_post_sf p _ _ _ _ (by omega), prelaunch_post_sf p _ _ _ _ (by omega),
          prelaunch_post_sf p _ _ _ _ (by omega)]
        have A : a=2*p.digits+2 := by unfold cmpOp at more low; unfold readOp at cmpC; omega
        exact ctrl_ok (readOp p) (by rw [A]; exact .cmpLast pos)
    · rw [if_neg cmpC]
      have K : ¬get raw (pc p) (o p)<readOp p := cmpC
      simp only [if_neg K]
      rw [prelaunch_post_sf p _ _ _ _ (by omega),prelaunch_post_sf p _ _ _ _ (by omega),
        prelaunch_post_sf p _ _ _ _ (by omega)]
      have A : a=2*p.digits+3+(a-readOp p) := by unfold readOp at *; omega
      have J : a-readOp p<p.digits := by unfold readOp writeOp at *; omega
      exact ctrl_ok (writeOp p+(a-readOp p)) (by
        simpa only [←A,writeOp] using (PreviewNextOp.readWrite (t:=p.digits) (j:=a-readOp p) J))
  · rw [if_neg rd]
    by_cases wr : a<sealOp p
    · rw [if_pos wr]
      by_cases more : a-writeOp p+1<p.digits
      · rw [if_pos more]
        have A : a=3*p.digits+3+(a-writeOp p) := by unfold writeOp at *; omega
        exact ctrl_ok (readOp p+(a-writeOp p)+1) (by
          rw [Nat.add_assoc]
          simpa only [←A,readOp] using (PreviewNextOp.writeRead (t:=p.digits) (j:=a-writeOp p) more))
      · rw [if_neg more]
        have A : a=3*p.digits+3+(a-writeOp p) := by unfold writeOp at *; omega
        have J : a-writeOp p+1=p.digits := by unfold writeOp sealOp at *; omega
        exact ctrl_ok (sealOp p) (by simpa only [←A,sealOp] using (PreviewNextOp.writeSeal (t:=p.digits) (j:=a-writeOp p) J))
    · rw [if_neg wr]
      by_cases L : (a==sealOp p)=true
      · rw [if_pos L]
        exact ctrl_ok (commitOp p) (by rw [beq_iff_eq.mp L]; exact .sealCommit)
      · rw [if_neg L]
        exact .inl R

theorem prelaunch_phase_bound (p : Params) (v : BitVec p.w) :
    sourcePhase p v<4 := (v.extractLsb' (pc p+o p) 2).isLt

private theorem prelaunch_widen_empty_apply (p : Params) (v : BitVec p.w) :
    (widen p (.empty _)).apply v=v := by simp [widen,Patch.empty,Patch.apply]

/-- Positive legal ISSUE moves to same-op WAIT, unless the raw file
guard forces restart. This measures the actual written PC fields. -/
theorem prelaunch_positive_issue_controls (p : Params) (v : BitVec p.w) (t : Tok)
    (P : sourcePhase p v=1) (O : sourceOpcode p v≤commitOp p)
    (pos : 0<sourceOpcode p v) :
    let y := prePostPC p (source p v t).1 v
    y=(1,0) ∨ y=(2,sourceOpcode p v) := by
  dsimp only
  rcases prelaunch_issue_action p v t P O with R|⟨q,R⟩
  · rw [R]
    exact .inl (prelaunch_restart_controls p v)
  · rw [R]
    simp only [show ¬sourceOpcode p v=0 by omega,if_false]
    apply Or.inr
    unfold prePostPC
    rw [reset0_widen_apply,prelaunch_widen_empty_apply]
    have F : pc p+o p+2≤workW p := by unfold pc workW grantBase sealBase sourceW; omega
    have C := dr_field_get p v (pc p+o p) 2 2 0 2 F (by decide) (by decide)
    have K : (((widen p (field p (pc p+o p) 2 2)).apply v).extractLsb' (pc p) (o p)) =
        v.extractLsb' (pc p) (o p) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i I
      simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
      exact pulse_widen_frame p _ _ _ (pulse_field_out p _ _ _ _ (.inl (by omega)))
    exact Prod.ext (by simpa [prePostPC,sourcePhase] using C)
      (by unfold sourceOpcode get; dsimp only; rw [K])

/-- The root incidence is K0, not the cached K1 position: its
decoder is gate false on both sides of every mark. -/
theorem prelaunch_root_decode (p : Params) (v : BitVec p.w) :
    publicationToken p true v 0 = decode p false (resetTokenRead p v 0) := rfl

theorem prelaunch_door_norm_tag (p : Params) (v : BitVec p.w) :
    (decode p false (prelaunchDoorNormWire p v)).tag=
      (publicationToken p true v 0).tag := by
  unfold prelaunchDoorNormWire
  dsimp only
  by_cases F : (oldK p true v 0).fault=true
  · rw [if_pos F]
    exact rank_reverse_tag p false false (resetTokenRead p v 0)
  · rw [if_neg F]
    change (decode p false (if parked p (oldK p true v 0) true v 0 && _ then _ else _)).tag=_
    have K : parked p (oldK p true v 0) true v 0=false := by simp [parked,gate]
    simp only [K,Bool.false_and,Bool.false_eq_true,if_false]
    exact congrArg MISByteCodec.Token.tag (prelaunch_root_decode p v).symm

theorem prelaunch_empty_wire_tag (p : Params) :
    (decode p false (resetTokenWire p E)).tag=0 := by rw [drain_decode_E]; rfl

theorem prelaunch_hold_controls (p : Params) (v : BitVec p.w) (t : Tok)
    (P : sourcePhase p v=2) (O : sourceOpcode p v≤commitOp p)
    (T : t.tag=1 ∨ t.tag=2) :
    prePostPC p (source p v t).1 v=(sourcePhase p v,sourceOpcode p v) := by
  rw [prelaunch_wait_hold p v t P O T]
  unfold prePostPC
  rw [prelaunch_widen_empty_apply]

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

-- CHECK: private helpers in this SAME file, ReportByteRows.lean:
-- 3408 dr_row_eq, 3799 drSright, 4027 dr_file_frame,
-- 1926 reset0Post_left / reset0Post, 5426 prelaunch_wait_hold.
theorem lease_row_file_wait_live (p : Params) (hu : Bool)
    (u v : BitVec p.w)
    (P : sourcePhase p v=2) (O : sourceOpcode p v≤commitOp p)
    (T : (publicationToken p true v 0).tag=1 ∨
         (publicationToken p true v 0).tag=2) :
    drainFile p ((row p (hu,true) (u,v)).2.apply v)=drainFile p v := by
  have F := dr_file_frame p _ v (drSright p hu u v)
  have R := prelaunch_wait_hold p v (oldK p true v 0) P O T
  rw [dr_row_eq]
  unfold reset0Post
  simp only [if_true,R,reset0_empty_comp]
  exact F

end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxHeartbeats 1000000

private theorem rWriteBit_fit (x j w : Nat) (P : x<2^w) (J : j<w) :
    writeBit x j false<2^w ∧ writeBit x j true<2^w := by
  constructor
  · unfold writeBit
    split
    · exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) P
    · exact P
  · unfold writeBit
    by_cases H : bit x j=true
    · simpa [H] using P
    · have H0 : bit x j=false := Bool.eq_false_iff.mpr H
      simp only [H0,Bool.false_eq_true,if_false,if_true]
      have M : (x/2^j)%2=0 := by
        simpa [bit,Nat.shiftRight_eq_div_pow] using H0
      have P0 : x/2^j<2^(w-j) := by
        apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos j)).2
        rw [←Nat.pow_add,show w-j+j=w by omega]
        exact P
      have Ev : 2^(w-j)=2^(w-j-1)*2 := by rw [←Nat.pow_succ]; congr 1 <;> omega
      have Q : x/2^j+1<2^(w-j) := by omega
      have T : x%2^j<2^j := Nat.mod_lt _ (Nat.two_pow_pos _)
      have K := Nat.mod_add_div x (2^j)
      have A := rPack_lt T Q
      unfold rPack at A
      rw [show j+(w-j)=w by omega] at A
      rw [Nat.mul_add,Nat.mul_one] at A
      omega

private theorem rWriteBit_any_fit (x j w : Nat) (b : Bool) (P : x<2^w) (J : j<w) :
    writeBit x j b<2^w := by
  cases b
  · exact (rWriteBit_fit x j w P J).1
  · exact (rWriteBit_fit x j w P J).2

private theorem rDigit_fit (x q a b w : Nat) (X : x<2^w) (Q : q<2^b) (L : a+b≤w) :
    x - ((x/2^a)%2^b)*2^a + q*2^a < 2^w := by
  have H : x/2^a/2^b<2^(w-(a+b)) := by
    rw [Nat.div_div_eq_div_mul,←Nat.pow_add]
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos (a+b))).2
    rw [←Nat.pow_add,show w-(a+b)+(a+b)=w by omega]
    exact X
  have N := rPack_lt (Nat.mod_lt x (Nat.two_pow_pos a)) (rPack_lt Q H)
  unfold rPack at N
  rw [show a+(b+(w-(a+b)))=w by omega] at N
  have EA := Nat.mod_add_div x (2^a)
  have EB := congrArg (fun y => 2^a*y) (Nat.mod_add_div (x/2^a) (2^b))
  simp only [Nat.mul_add,Nat.mul_comm (2^a) ((x/2^a)%2^b),Nat.mul_comm (2^a) q] at N EB
  omega

private theorem rHop_effect (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (win : Bool) (t : Tok) (H : RankFits p t) (T0 : t.tag=2) :
    let z := (effect p u v hu hv j (some k) win t).2.2
    z.tag=2 ∧ RankFits p z := by
  dsimp only
  have I : t.tag=2 ∧ RankFits p t := ⟨T0,H⟩
  have F0 : (F 2).tag=2 ∧ RankFits p (F 2) := ⟨rfl,rFault_fits p 2 (by decide)⟩
  unfold effect
  dsimp only
  split
  · exact I
  · split
    · split
      · exact ⟨T0,⟨H.tag,H.op,H.payload,H.race,H.outcome⟩⟩
      · exact F0
    · split
      · have W : 8≤2^payW p :=
          Nat.pow_le_pow_right (by decide : 1≤(2:Nat)) (by show 3≤payW p; unfold payW; omega)
        have P : t.race-4<2^payW p := by have A := H.race; omega
        exact ⟨T0,⟨H.tag,H.op,P,by change 0<8; decide,H.outcome⟩⟩
      · split
        · exact I
        · split
          · refine ⟨T0,⟨H.tag,H.op,?_,H.race,H.outcome⟩⟩
            dsimp only
            split
            · exact rWriteBit_any_fit _ _ _ _
                (rWriteBit_any_fit _ _ _ _ H.payload (by unfold payW; omega))
                (by unfold payW; omega)
            · exact (rWriteBit_fit _ _ _ H.payload (by unfold payW; omega)).1
          · generalize (if t.opcode<readOp p then cmpOp p else readOp p) = off
            split
            · refine ⟨T0,⟨H.tag,H.op,?_,H.race,H.outcome⟩⟩
              dsimp only
              apply rDigit_fit _ _ _ (d p)
              · exact H.payload
              · exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (BitVec.isLt _)
              · cases (j.val/2==0) <;> simp <;> unfold payW <;> omega
            · split
              · split
                · exact F0
                · exact I
              · split
                · split
                  · exact I
                  · exact F0
                · exact I

private theorem rHop_arrival (p : Params) (hv : Bool) (v : BitVec p.w)
    (k : Fin 3) (t : Tok) (H : RankFits p t) (T0 : t.tag=2) :
    (arrival p hv v k t).tag=2 ∧ RankFits p (arrival p hv v k t) := by
  unfold arrival
  split
  · exact ⟨T0,⟨H.tag,H.op,H.payload,by change 1<8; decide,H.outcome⟩⟩
  · exact ⟨T0,H⟩

/-- A ready forward hop preserves decoded tag F at the actual routed
destination, even if the effect or target decoder faults it. -/
theorem rank_hop_tag (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (D : reset0Destination hv j=some k)
    (R : rankReady p hu u j=true) (g' : Bool) :
    (decode p g' (resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k)).tag=2 := by
  let t := oldK p hu u j
  have T0 : t.tag=2 := ((rankReady_iff p hu u j).mp R).1
  have H : RankFits p t := rank_decoded_fits p _ _
  have V := rHop_effect p hu hv u v j k (drWin p hu u j) t H T0
  have A := rHop_arrival p hv v k _ V.2 V.1
  rw [rank_row_right p hu hv u v j k D]
  simp only [rankRouteR,R,if_true,Option.elim]
  exact (rank_encode_tag p g' _ A.2).trans A.1

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

def ancestrySelectorAddr (p : Params) : Nat := grantBase p+3

private def ancSelFrame (p : Params) (a : Patch (workW p)) : Prop :=
  a.mask.getLsbD (ancestrySelectorAddr p)=false

private theorem ancSel_empty (p : Params) : ancSelFrame p (.empty _) := by
  simp [ancSelFrame,Patch.empty]

private theorem ancSel_comp {p : Params} {a b : Patch (workW p)}
    (A : ancSelFrame p a) (B : ancSelFrame p b) :
    ancSelFrame p (a.compose b) :=
  pulse_comp_out A B

private theorem ancSel_cmt {p : Params} {a : Patch (workW p)}
    (A : cmtFrame p a) : ancSelFrame p a :=
  A (ancestrySelectorAddr p) (.inr rfl)

private theorem ancSel_early (p : Params) (k b v : Nat)
    (H : k+b≤ancestrySelectorAddr p) : ancSelFrame p (field p k b v) :=
  pulse_field_out p k b v _ (.inr H)

private theorem ancSel_K (p : Params) (j : Fin 3) (t : Tok) :
    ancSelFrame p (writeK p j t) :=
  ancSel_cmt (cmtK p j t)

private theorem ancSel_grants (p : Params) (g : Fin 3→Bool) :
    ancSelFrame p (grants p g) :=
  ancSel_early p _ _ _ (Nat.le_refl _)

private theorem ancSel_clear (p : Params) : ancSelFrame p (drClear p) := by
  unfold drClear
  exact ancSel_comp
    (ancSel_comp (ancSel_cmt (cmtReset p)) (ancSel_cmt (cmtSeal p none)))
    (ancSel_grants p _)

private theorem ancSel_baseL (p : Params) (hu : Bool) (u : BitVec p.w) :
    ancSelFrame p (drBaseL p hu u) := by
  unfold drBaseL
  split
  · exact ancSel_grants p _
  · exact ancSel_clear p

private theorem ancSel_baseR (p : Params) (hv : Bool) (v : BitVec p.w) :
    ancSelFrame p (drBaseR p hv v) := by
  unfold drBaseR
  split
  · split
    · exact ancSel_grants p _
    · exact ancSel_empty p
  · exact ancSel_clear p

private theorem ancSel_pulse (p : Params) (h : Bool) (side : Nat) (x : BitVec p.w) :
    ancSelFrame p (pulse p h side x) :=
  pulse_mask_below_tail p h side x _
    (by unfold ancestrySelectorAddr grantBase sealBase sourceBase; omega)

private theorem ancSel_norm (p : Params) (j : Fin 3) (a : Patch (workW p))
    (H : a=.empty _ ∨ ∃ t,a=writeK p j t) : ancSelFrame p a := by
  rcases H with rfl|⟨t,rfl⟩
  · exact ancSel_empty p
  · exact ancSel_K p j t

private theorem ancSel_prefix (p : Params) (base pulseP : Patch (workW p))
    (norm : Fin 3→Patch (workW p)) (A : ancSelFrame p base)
    (B : ancSelFrame p pulseP) (N : ∀ j,ancSelFrame p (norm j)) :
    ancSelFrame p (drPrefix p base pulseP norm) :=
  ancSel_comp (ancSel_comp (ancSel_comp (ancSel_comp A B) (N 0)) (N 1)) (N 2)

private theorem ancSel_preL (p : Params) (hu hv : Bool) (u v : BitVec p.w) :
    ancSelFrame p (drPre p hu hv u v).1 :=
  ancSel_prefix p _ _ _ (ancSel_baseL p hu u) (ancSel_pulse p hu 2 u)
    (fun j=>ancSel_norm p j _ (dr_norm_left_shape p hu u j))

private theorem ancSel_preR (p : Params) (hu hv : Bool) (u v : BitVec p.w) :
    ancSelFrame p (drPre p hu hv u v).2 :=
  ancSel_prefix p _ _ _ (ancSel_baseR p hv v) (ancSel_pulse p hv 1 v)
    (fun j=>ancSel_norm p j _ (dr_norm_right_shape p hv v j))

private theorem ancSel_bank (p : Params) (ix v : Nat) :
    ancSelFrame p (field p (bankOffset p ix) (2*d p) v) := by
  apply ancSel_early
  have B : (1-ix)*bankW p≤bankW p := by
    simpa using Nat.mul_le_mul_right (bankW p) (show 1-ix≤1 by omega)
  unfold ancestrySelectorAddr bankOffset grantBase bankW at *
  omega

/-- Every outgoing effect, including an inherited unguarded WRITE,
    frames the actual selector bit. -/
private theorem ancSel_effectL (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (w : Bool) (t : Tok) :
    ancSelFrame p (effect p u v hu hv j k w t).1 := by
  unfold effect
  dsimp only
  split
  · exact ancSel_empty p
  · split
    · split <;> exact ancSel_empty p
    · split
      · exact ancSel_empty p
      · split
        · exact ancSel_cmt (cmtSeal p none)
        · split
          · exact ancSel_empty p
          · generalize (if t.opcode<readOp p then cmpOp p else readOp p) = off
            split
            · exact ancSel_empty p
            · split
              · split
                · exact ancSel_empty p
                · exact ancSel_bank p ((t.payload/2^(2*d p))%2) (t.payload%2^(2*d p))
              · split
                · split
                  · exact ancSel_cmt (p:=p) (cmtSeal p (some t.payload))
                  · exact ancSel_empty p
                · exact ancSel_empty p

/-- Exactly the OLD candidate for a right selector update. There is
    no dependence on an observer's generation label. -/
def ancestryCommitOpportunity (p : Params) (hu hv : Bool) (u v : BitVec p.w) : Prop :=
  hv=true ∧ rankReady p hu u 0=true ∧
  (publicationToken p hu u 0).fault=false ∧
  (publicationToken p hu u 0).opcode=commitOp p ∧
  packetCommitGuard p v (publicationToken p hu u 0)=true

private theorem ancSel_effectR (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (w : Bool)
    (R : ready p hu u j (oldK p hu u j)=true)
    (H : ¬ancestryCommitOpportunity p hu hv u v) :
    (effect p u v hu hv j k w (oldK p hu u j)).2.1=.empty _ := by
  unfold effect
  dsimp only
  split
  · rfl
  · rename_i fault
    split
    · rename_i Commit
      simp only [Bool.and_eq_true, beq_iff_eq] at Commit
      obtain ⟨⟨⟨Op,V⟩,J⟩,K⟩ := Commit
      subst j hv
      have F0 : (oldK p hu u 0).fault=false := Bool.eq_false_iff.mpr fault
      have G : packetCommitGuard p v (oldK p hu u 0)=false := by
        apply Bool.eq_false_iff.mpr
        intro Q
        exact H ⟨rfl,R,F0,Op,Q⟩
      unfold packetCommitGuard at G
      simp only [G,Bool.false_eq_true,if_false]
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · generalize (if (oldK p hu u j).opcode<readOp p then cmpOp p else readOp p) = off
            split
            · rfl
            · split
              · split <;> rfl
              · split
                · split <;> rfl
                · rfl

private theorem ancSel_routeL (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (w : Fin 3→Bool) (ab : Pair (Patch (workW p)))
    (l : Fin 3 × Option (Fin 3)) (A : ancSelFrame p ab.1) :
    ancSelFrame p (cmtRoute p hu hv u v w ab l).1 := by
  rcases ab with ⟨a,b⟩
  rcases l with ⟨j,k⟩
  have E0 := ancSel_effectL p u v hu hv j k (w j) (oldK p hu u j)
  cases k with
  | none =>
    unfold cmtRoute
    dsimp only
    split
    · exact ancSel_comp (ancSel_comp A E0) (ancSel_K p _ _)
    · split
      · exact A
      · split
        · exact ancSel_comp A (ancSel_K p _ _)
        · exact A
  | some k =>
    unfold cmtRoute
    dsimp only
    split
    · exact ancSel_comp (ancSel_comp A E0) (ancSel_K p _ _)
    · split
      · exact A
      · split
        · exact ancSel_comp A (ancSel_K p _ _)
        · split
          · exact ancSel_comp A (ancSel_K p _ _)
          · exact A

private theorem ancSel_routeR (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (w : Fin 3→Bool) (ab : Pair (Patch (workW p)))
    (l : Fin 3 × Option (Fin 3)) (A : ancSelFrame p ab.2)
    (H : ¬ancestryCommitOpportunity p hu hv u v) :
    ancSelFrame p (cmtRoute p hu hv u v w ab l).2 := by
  rcases ab with ⟨a,b⟩
  rcases l with ⟨j,k⟩
  have E (R : ready p hu u j (oldK p hu u j)=true) :
      ancSelFrame p (effect p u v hu hv j k (w j) (oldK p hu u j)).2.1 := by
    rw [ancSel_effectR p u v hu hv j k (w j) R H]
    exact ancSel_empty p
  cases k with
  | none =>
    unfold cmtRoute
    dsimp only
    split
    · rename_i R
      exact ancSel_comp A (E R)
    · split
      · exact A
      · exact A
  | some k =>
    unfold cmtRoute
    dsimp only
    split
    · rename_i R
      exact ancSel_comp (ancSel_comp A (E R)) (ancSel_K p _ _)
    · split
      · exact A
      · split
        · exact ancSel_comp A (ancSel_K p _ _)
        · split <;> exact A

private theorem ancSel_foldL (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (w : Fin 3→Bool) (xs : List (Fin 3 × Option (Fin 3)))
    (ab : Pair (Patch (workW p))) (A : ancSelFrame p ab.1) :
    ancSelFrame p (xs.foldl (cmtRoute p hu hv u v w) ab).1 := by
  induction xs generalizing ab with
  | nil => exact A
  | cons l xs ih =>
    exact ih _ (ancSel_routeL p hu hv u v w ab l A)

private theorem ancSel_foldR (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (w : Fin 3→Bool) (xs : List (Fin 3 × Option (Fin 3)))
    (ab : Pair (Patch (workW p))) (A : ancSelFrame p ab.2)
    (H : ¬ancestryCommitOpportunity p hu hv u v) :
    ancSelFrame p (xs.foldl (cmtRoute p hu hv u v w) ab).2 := by
  induction xs generalizing ab with
  | nil => exact A
  | cons l xs ih =>
    exact ih _ (ancSel_routeR p hu hv u v w ab l A H)

theorem ancestry_selector_bit_congr (p : Params) (a b : BitVec p.w)
    (H : a.getLsbD (ancestrySelectorAddr p)=b.getLsbD (ancestrySelectorAddr p)) :
    publicationSelector p a=publicationSelector p b := by
  change (a.extractLsb' (grantBase p+3) 1).toNat = (b.extractLsb' (grantBase p+3) 1).toNat
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro j J
  have E : j=0 := by omega
  subst j
  simpa [ancestrySelectorAddr,BitVec.getLsbD_extractLsb'] using H

private theorem ancSel_apply (p : Params) (a : Patch (workW p)) (x : BitVec p.w)
    (A : ancSelFrame p a) :
    publicationSelector p ((widen p a).apply x)=publicationSelector p x :=
  ancestry_selector_bit_congr p _ _ (pulse_widen_frame p a x _ A)

/-- No old left packet of any opcode changes the left selector. -/
theorem ancestry_row_selector_left (p : Params) (hu hv : Bool) (u v : BitVec p.w) :
    publicationSelector p ((row p (hu,hv) (u,v)).1.apply u)=publicationSelector p u := by
  rw [dr_row_eq,reset0Post_left]
  apply ancSel_apply
  exact ancSel_foldL p hu hv u v (drWin p hu u) (links hv) _
    (ancSel_preL p hu hv u v)

/-- Absence of the literal old ingress condition frames the right
    selector, even when the right site's own source updates its file. -/
theorem ancestry_row_selector_right (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (H : ¬ancestryCommitOpportunity p hu hv u v) :
    publicationSelector p ((row p (hu,hv) (u,v)).2.apply v)=publicationSelector p v := by
  have A : ancSelFrame p (drRouted p hu hv u v).2 :=
    ancSel_foldR p hu hv u v (drWin p hu u) (links hv) _
      (ancSel_preR p hu hv u v) H
  rw [dr_row_eq]
  apply ancSel_apply
  cases hv
  · exact A
  · unfold reset0Post
    simp only [if_true]
    exact ancSel_comp (ancSel_comp A (ancSel_cmt (cmtSource p v (oldK p true v 0))))
      (ancSel_cmt (cmtSourceToken p (source p v (oldK p true v 0)).2))

/-- Public readouts for the exact existing source/packet fields. -/
def ancestrySourceCentre (p : Params) (x : BitVec p.w) : Nat :=
  (rf p x (16+2*d p) 3/2)%2

def ancestrySendDigits (p : Params) (x : BitVec p.w) : Nat :=
  rf p x 3 (2*d p)

def ancestryWriteOld (p : Params) (t : Tok) : Nat :=
  t.payload/2^(2*d p+1)

def ancestryWriteTarget (p : Params) (t : Tok) : Nat :=
  (t.payload/2^(2*d p))%2

def ancestryWritePayload (p : Params) (a q : Nat) : Nat :=
  (2*a+(1-a))*2^(2*d p)+q

theorem ancestry_source_centre_lt (p : Params) (x : BitVec p.w) :
    ancestrySourceCentre p x<2 := Nat.mod_lt _ (by decide)

theorem ancestry_send_digits_lt (p : Params) (x : BitVec p.w) :
    ancestrySendDigits p x<2^(2*d p) :=
  (x.extractLsb' (sourceBase p+3) (2*d p)).isLt

theorem ancestry_selector_lt (p : Params) (x : BitVec p.w) :
    publicationSelector p x<2 :=
  (x.extractLsb' (grantBase p+3) 1).isLt

/-- Exact successful positive WRITE source intent. This is about the
    source's old file, not about a returned WRITE acknowledgement. -/
theorem ancestry_source_write_intent (p : Params) (v : BitVec p.w) (t : Tok)
    (P : sourcePhase p v=1) (W : writeOp p≤sourceOpcode p v)
    (U : sourceOpcode p v<sealOp p)
    (D : digitPair p (ancestrySendDigits p v)=true) :
    (source p v t).2=some ({tag:=2, opcode:=sourceOpcode p v, payload:=ancestryWritePayload p (ancestrySourceCentre p v) (ancestrySendDigits p v)} : Tok) := by
  have P0 : get v (pc p+o p) 2=1 := P
  have W0 : writeOp p≤get v (pc p) (o p) := W
  have U0 : get v (pc p) (o p)<sealOp p := U
  have C : ¬commitOp p<get v (pc p) (o p) := by
    unfold commitOp sealOp at *; omega
  have A : get v (pc p) (o p)≠acqOp p := by
    unfold acqOp writeOp at *; omega
  have S : ¬sealOp p≤get v (pc p) (o p) := by omega
  have N : ¬get v (pc p) (o p)<writeOp p := by omega
  have Z : get v (pc p) (o p)≠0 := by unfold writeOp at W0; omega
  -- CHECK: simp's boolean comparisons for the exact source expression
  -- at ReportByteRows.lean:112–138.
  simp [source,sourceOpcode,P0,C,A,S,N,Z,W0,U0,
    ancestrySourceCentre,ancestrySendDigits,ancestryWritePayload,
    show digitPair p (rf p v 3 (2*d p))=true from D]

theorem ancestry_write_indices (p : Params) (t : Tok) (a q : Nat)
    (A : a<2) (Q : q<2^(2*d p))
    (P : t.payload=ancestryWritePayload p a q) :
    ancestryWriteOld p t=a ∧ ancestryWriteTarget p t=1-a := by
  have E : t.payload/2^(2*d p)=2*a+(1-a) := by
    rw [P,ancestryWritePayload,Nat.add_comm,Nat.mul_comm (2*a+(1-a))]
    exact rPack_div Q
  constructor
  · unfold ancestryWriteOld
    rw [Nat.pow_succ,←Nat.div_div_eq_div_mul,E]
    omega
  · unfold ancestryWriteTarget
    rw [E]
    omega

/-- A matching successful ACQUIRE consumes the actual six-bit reply;
    this is the unique source branch installing the capture file. -/
theorem ancestry_acquire_consume_patch (p : Params) (v : BitVec p.w) (t : Tok)
    (P : sourcePhase p v=2) (O : sourceOpcode p v=acqOp p)
    (T0 : t.tag=3) (T1 : t.opcode=acqOp p) (F0 : t.fault=false)
    (R : t.outcome=0) :
    source p v t=
      (((ctrl p 1 (cmpOp p)).compose (sf p (13+2*d p) 6 t.payload)).compose
        (sf p (9+2*d p) 4 0),some E) := by
  have P0 : get v (pc p+o p) 2=2 := P
  have O0 : get v (pc p) (o p)=acqOp p := O
  have C : ¬commitOp p<acqOp p := by unfold commitOp acqOp; omega
  have Z : acqOp p≠0 := by unfold acqOp; omega
  have A : ¬acqOp p<admitOp p := by unfold acqOp admitOp; omega
  have B : acqOp p≠admitOp p := by unfold acqOp admitOp; omega
  simp [source,P0,O0,T0,T1,F0,R,C,Z,A,B]

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxHeartbeats 1000000

private theorem rWrite_decoded_shape (p : Params) (g : Bool) (raw : BitVec (tokenW p))
    (T0 : (decode p g raw).tag=2) (H : (decode p g raw).fault=false)
    (W : writeOp p≤(decode p g raw).opcode) (S : (decode p g raw).opcode<sealOp p) :
    let t := decode p g raw
    t.race=0 ∧ t.outcome=0 ∧ t.applied=false ∧ t.payload<2^(2+2*d p) ∧
      digitPair p t.payload=true ∧ bit t.payload (2*d p)≠bit t.payload (2*d p+1) := by
  dsimp only
  have Tag : get raw (7+o p+payW p) 2=2 := (rank_decode_tag p g raw).symm.trans T0
  revert H W S
  let P (t : Tok) := t.fault=false → writeOp p≤t.opcode → t.opcode<sealOp p →
    t.race=0 ∧ t.outcome=0 ∧ t.applied=false ∧ t.payload<2^(2+2*d p) ∧
      digitPair p t.payload=true ∧ bit t.payload (2*d p)≠bit t.payload (2*d p+1)
  change P (decode p g raw)
  unfold decode
  simp only [Tag,show ((2:Nat)==0)=false by decide,show ((2:Nat)==1)=false by decide,
    beq_self_eq_true,Bool.false_eq_true,if_false,if_true]
  generalize (get raw (payW p+6) (o p)) = op
  generalize (get raw (payW p+3) 3) = r
  generalize (get raw (payW p+1) 2) = c
  by_cases AD : op=admitOp p
  · have NW : ¬writeOp p≤op := by unfold writeOp admitOp at *; omega
    repeat' first
    | (change P (F 2); intro H; contradiction)
    | (change P ({tag:=2,opcode:=op,payload:=_,race:=r,applied:=_} : Tok)
       intro _ W
       exact False.elim (NW W))
    | split
  · simp only [show (op==admitOp p)=false by simp [AD],Bool.and_false,
      Bool.false_eq_true,if_false]
    generalize B : (if (op==acqOp p) then 7 else
      if cmpOp p≤op && op<sealOp p then 2+2*d p else if sealOp p≤op then 4 else 0) = bits
    split
    · intro H; contradiction
    · split
      · intro H; contradiction
      · rename_i R
        split
        · intro H; contradiction
        · rename_i G
          intro _ W S
          have A : op≠acqOp p := by change writeOp p≤op at W; unfold writeOp acqOp at *; omega
          have C : cmpOp p≤op := by change writeOp p≤op at W; unfold writeOp cmpOp at *; omega
          have CM : op≠commitOp p := by change op<sealOp p at S; unfold sealOp commitOp at *; omega
          change writeOp p≤op at W
          change op<sealOp p at S
          simp [A,C,S] at *
          subst bits
          simp [W,CM] at G ⊢
          exact ⟨R.2,Nat.mod_lt _ (Nat.two_pow_pos _),G.1.1,G.1.2⟩

private theorem rWrite_roundtrip (p : Params) (g g' : Bool) (raw : BitVec (tokenW p))
    (T0 : (decode p g raw).tag=2) (H : (decode p g raw).fault=false)
    (W : writeOp p≤(decode p g raw).opcode) (S : (decode p g raw).opcode<sealOp p) :
    decode p g' (resetTokenWire p (decode p g raw))=decode p g raw := by
  let t := decode p g raw
  obtain ⟨R,U,A,P,D,I⟩ := rWrite_decoded_shape p g raw T0 H W S
  have B := rReadFields p t (rank_decoded_fits p g raw)
  have FV : (resetTokenWire p t).getLsbD (6+o p+payW p)=false := by
    rw [rGet_bit,B.2.1]
    change t.fault = false at H
    simp [H]
  have AC : t.opcode≠acqOp p := by change writeOp p≤t.opcode at W; unfold writeOp acqOp at *; omega
  have AD : t.opcode≠admitOp p := by change writeOp p≤t.opcode at W; unfold writeOp admitOp at *; omega
  have CM : t.opcode≠commitOp p := by change t.opcode<sealOp p at S; unfold sealOp commitOp at *; omega
  have LT : ¬commitOp p<t.opcode := by change t.opcode<sealOp p at S; unfold sealOp commitOp at *; omega
  have CO : cmpOp p≤t.opcode := by change writeOp p≤t.opcode at W; unfold writeOp cmpOp at *; omega
  have SN : ¬sealOp p≤t.opcode := by change t.opcode<sealOp p at S; omega
  change t.tag=2 at T0
  change writeOp p≤t.opcode at W
  change t.opcode<sealOp p at S
  change t.race=0 at R
  change t.outcome=0 at U
  change t.applied=false at A
  change t.payload<2^(2+2*d p) at P
  change digitPair p t.payload=true at D
  change bit t.payload (2*d p)≠bit t.payload (2*d p+1) at I
  change decode p g' (resetTokenWire p t)=t
  simp [decode,B.1,B.2.2.1,B.2.2.2.1,B.2.2.2.2.1,
    B.2.2.2.2.2.2,FV,T0,AC,AD,LT,CO,W,S,SN,R,U,D,I,
    Nat.mod_eq_of_lt P]
  change t.fault=false at H
  cases Eq : t
  simp only [Eq] at T0 R U H A CM
  simp_all

private theorem rWrite_hop_effect (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (win : Bool) (t : Tok)
    (H : t.fault=false) (W : writeOp p≤t.opcode) (S : t.opcode<sealOp p) :
    (effect p u v hu hv j (some k) win t).2.2=t ∨
      (hu=true ∧ (effect p u v hu hv j (some k) win t).2.2=F 2) := by
  have AC : t.opcode≠acqOp p := by unfold writeOp acqOp at *; omega
  have AD : t.opcode≠admitOp p := by unfold writeOp admitOp at *; omega
  have CM : t.opcode≠commitOp p := by unfold sealOp commitOp at *; omega
  have SZ : t.opcode≠sealOp p := Nat.ne_of_lt S
  have Z : t.opcode≠0 := by unfold writeOp at *; omega
  have WL : ¬t.opcode<writeOp p := by omega
  simp [effect,parked,H,AC,AD,CM,SZ,Z,WL,W,S]
  split
  · cases hu <;> simp_all
    by_cases G : gBit p u 1=true <;>
      by_cases B : selected p u=t.payload/2^(2*d p+1) <;> simp_all
  · first
    | exact Or.inl rfl
    | rename_i N
      left
      intro J O
      exact False.elim (N ⟨J,O⟩)

/-- On every internal ready WRITE hop, including non-writing transit
sites, the transported command remains exactly the old decoded WRITE
unless the header guard faults it. No valid WRITE is changed by the
new slot's admit gate. -/
theorem rank_write_hop_token (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (J : reset0Destination hv j=some k)
    (R : rankReady p hu u j=true) (g' : Bool)
    (H : (publicationToken p hu u j).fault=false)
    (W : writeOp p≤(publicationToken p hu u j).opcode)
    (S : (publicationToken p hu u j).opcode<sealOp p) :
    let t := publicationToken p hu u j
    let z := decode p g' (resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k)
    z=t ∨ (hu=true ∧ z=F 2) := by
  dsimp only
  let t := oldK p hu u j
  have T0 : t.tag=2 := ((rankReady_iff p hu u j).mp R).1
  change t.fault=false at H
  change writeOp p≤t.opcode at W
  change t.opcode<sealOp p at S
  have AD : t.opcode≠admitOp p := by unfold writeOp admitOp at *; omega
  obtain Q|⟨QH,Q⟩ := rWrite_hop_effect p hu hv u v j k (drWin p hu u j) t H W S
  all_goals
    rw [rank_row_right p hu hv u v j k J]
    simp only [rankRouteR,R,if_true,Option.elim]
    change decode p g' (resetTokenWire p (arrival p hv v k
      (effect p u v hu hv j (some k) (drWin p hu u j) t).2.2)) = t ∨ _
    rw [Q]
  · left
    have A : arrival p hv v k t=t := by simp [arrival,AD]
    rw [A]
    exact rWrite_roundtrip p _ g' _ T0 H W S
  · right
    refine ⟨QH,?_⟩
    have A : arrival p hv v k (F 2)=F 2 := by simp [arrival,F,MISByteCodec.faultToken]
    rw [A]
    exact rFault_roundtrip p g' 2 (.inl rfl)

/-- The only report work effect which writes the right endpoint is the
COMMIT crossing. An old non-COMMIT opcode cannot do so, even at K0→K1. -/
theorem effect_noncommit_right_empty (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) (t : Tok)
    (H : t.opcode≠commitOp p) :
    (effect p u v hu hv j k win t).2.1=.empty _ := by
  simp [effect,H]
  repeat' first | rfl | split

private theorem rHealthy_forward_op (p : Params) (g : Bool) (w : BitVec (tokenW p))
    (T0 : (decode p g w).tag=2) (H : (decode p g w).fault=false) :
    (decode p g w).opcode=get w (payW p+6) (o p) := by
  have Tag := (rank_decode_tag p g w).symm.trans T0
  revert H
  let P (t : Tok) := t.fault=false→t.opcode=get w (payW p+6) (o p)
  change P (decode p g w)
  unfold decode
  simp only [Tag,show ((2:Nat)==0)=false by decide,show ((2:Nat)==1)=false by decide,
    beq_self_eq_true,Bool.false_eq_true,if_false,if_true]
  repeat' first
  | (change P (F 2); intro H; contradiction)
  | (change P ({tag:=2,opcode:=_,payload:=_,race:=_,applied:=_} : Tok); intro _; rfl)
  | split

private theorem rHop_op (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (win : Bool) (t : Tok) :
    let z := (effect p u v hu hv j (some k) win t).2.2
    z.opcode=t.opcode ∨ z=F 2 := by
  dsimp only
  unfold effect
  dsimp only
  repeat' first
  | exact Or.inl rfl
  | exact Or.inr rfl
  | split

/-- A healthy forward arrival cannot invent a COMMIT opcode (or any
different opcode). Fault arrivals are explicitly excluded. -/
theorem rank_healthy_hop_opcode (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (J : reset0Destination hv j=some k)
    (R : rankReady p hu u j=true) (g' : Bool)
    (H : (decode p g' (resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k)).fault=false) :
    (decode p g' (resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k)).opcode=
      (publicationToken p hu u j).opcode := by
  let t := oldK p hu u j
  let e := (effect p u v hu hv j (some k) (drWin p hu u j) t).2.2
  let z := arrival p hv v k e
  have T0 : t.tag=2 := ((rankReady_iff p hu u j).mp R).1
  have Fit0 : RankFits p t := rank_decoded_fits p _ _
  have EF : e.tag=2 ∧ RankFits p e := rHop_effect p hu hv u v j k _ _ Fit0 T0
  have ZF : z.tag=2 ∧ RankFits p z := rHop_arrival p hv v k _ EF.2 EF.1
  rw [rank_row_right p hu hv u v j k J] at H ⊢
  simp only [rankRouteR,R,if_true,Option.elim] at H ⊢
  change (decode p g' (resetTokenWire p z)).fault=false at H
  change (decode p g' (resetTokenWire p z)).opcode=t.opcode
  have A : z.opcode=e.opcode := by unfold z arrival; split <;> rfl
  have B : e.opcode=t.opcode := by
    rcases rHop_op p hu hv u v j k (drWin p hu u j) t with S|S
    · exact S
    · have ZE : z=F 2 := by
        change e=F 2 at S
        unfold z
        rw [S]
        simp [arrival,F,MISByteCodec.faultToken]
      rw [ZE,rFault_roundtrip p g' 2 (.inl rfl)] at H
      contradiction
  have T1 := (rank_encode_tag p g' z ZF.2).trans ZF.1
  rw [rHealthy_forward_op p g' _ T1 H,(rReadFields p z ZF.2).2.2.1,A,B]

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxHeartbeats 1000000

private theorem rIssue_payload_fit (p : Params) (raw : BitVec p.w) (op : Nat) :
    let w := d p
    let capIx := rf p raw (16+2*w) 3
    let outCmp := rf p raw (5+2*w) 4
    let sendDigits := rf p raw 3 (2*w)
    let old := (capIx/2)%2
    let alt := 2*old+(1-old)
    let pairIx := 2*(capIx/4)+capIx%2
    let pld := if op==acqOp p then 64 else
      if cmpOp p≤op && op<writeOp p then pairIx*2^(2*w)
      else if writeOp p≤op && op<sealOp p then alt*2^(2*w)+sendDigits
      else if sealOp p≤op then 4*alt+2*(outCmp/4==1).toNat+(outCmp%4==1).toNat
      else 0
    pld<2^payW p := by
  dsimp only
  have cap : rf p raw (16+2*d p) 3<8 := (raw.extractLsb' _ 3).isLt
  have D : rf p raw 3 (2*d p)<2^(2*d p) := (raw.extractLsb' _ _).isLt
  have W : 2^(2*d p+2)≤2^payW p :=
    Nat.pow_le_pow_right (by decide : 1≤(2:Nat)) (by unfold payW; omega)
  have B : 128≤2^payW p :=
    Nat.pow_le_pow_right (by decide : 1≤(2:Nat)) (by show 7≤payW p; unfold payW; omega)
  split
  · omega
  · split
    · have N : 2*(rf p raw (16+2*d p) 3/4)+rf p raw (16+2*d p) 3%2<2^2 := by omega
      have H := rPack_lt (show 0<2^(2*d p) by exact Nat.two_pow_pos _) N
      exact Nat.lt_of_lt_of_le (by simpa [rPack, Nat.mul_comm] using H) W
    · split
      · have A : 2*((rf p raw (16+2*d p) 3/2)%2)+(1-(rf p raw (16+2*d p) 3/2)%2)<2^2 := by omega
        have H := rPack_lt D A
        exact Nat.lt_of_lt_of_le (by simpa only [rPack,Nat.mul_comm (2^(2*d p)),Nat.add_comm] using H)
          (by simpa only [Nat.add_comm] using W)
      · split
        · generalize ((rf p raw (5+2*d p) 4/4)==1) = a
          generalize ((rf p raw (5+2*d p) 4%4)==1) = b
          cases a <;> cases b <;> simp <;> omega
        · omega

/-- The exact source-issued F wire always fits the report token codec;
a malformed source file instead returns E via the existing retry row. -/
theorem source_issue_fits (p : Params) (raw : BitVec p.w) (t : Tok)
    (P : sourcePhase p raw=1) (O : sourceOpcode p raw≤commitOp p) :
    (source p raw t).2=some E ∨
      ∃ z, (source p raw t).2=some z ∧ z.tag=2 ∧ RankFits p z := by
  have OP : sourceOpcode p raw<2^o p := (raw.extractLsb' _ _).isLt
  have V : ¬commitOp p<sourceOpcode p raw := Nat.not_lt_of_ge O
  have Fit := rIssue_payload_fit p raw (sourceOpcode p raw)
  unfold sourcePhase at P
  unfold sourceOpcode at V Fit OP
  unfold source
  dsimp only
  simp only [P,V,decide_false,show ((1:Nat)==0)=false by decide,
    show ((1:Nat)==3)=false by decide,Bool.false_or,Bool.false_eq_true,
    if_false,beq_self_eq_true,if_true]
  split
  · exact .inl rfl
  · exact .inr ⟨_,rfl,rfl,⟨by change 2<4; decide,OP,Fit,by change 0<8; decide,by change 0<4; decide⟩⟩

/-- An ISSUE mark jointly determines control and wire, distinguishing an
actual new F from an E retry on the same old pair. -/
theorem source_issue_joint (p : Params) (v : BitVec p.w) (t : Tok)
    (P : sourcePhase p v=1) (O : sourceOpcode p v≤commitOp p) :
    let a := source p v t
    ((sourcePhase p ((liftSourcePatch p a.1).apply v),sourceOpcode p ((liftSourcePatch p a.1).apply v))=(1,0) ∧ a.2=some E) ∨
    ((sourcePhase p ((liftSourcePatch p a.1).apply v),sourceOpcode p ((liftSourcePatch p a.1).apply v))=(2,sourceOpcode p v) ∧
      ∃ z,a.2=some z ∧ z.tag=2 ∧ RankFits p z) := by
  change (prePostPC p (source p v t).1 v=(1,0) ∧ (source p v t).2=some E) ∨
    (prePostPC p (source p v t).1 v=(2,sourceOpcode p v) ∧
      ∃ z,(source p v t).2=some z ∧ z.tag=2 ∧ RankFits p z)
  have Fit := source_issue_fits p v t P O
  by_cases Z : sourceOpcode p v=0
  · have J := source_reset0_issue p v t P Z
    refine .inr ⟨?_,?_⟩
    · rw [J,Z]
      exact dr_reset_control p v
    · rw [J] at Fit ⊢
      rcases Fit with F|F
      · have K := congrArg (Option.map MISByteCodec.Token.tag) F
        change (some 2 : Option Nat)=some 0 at K; contradiction
      · exact F
  · rcases prelaunch_issue_action p v t P O with A|⟨q,A⟩
    · rw [A]
      exact .inl ⟨prelaunch_restart_controls p v,rfl⟩
    · refine .inr ⟨?_,?_⟩
      · rw [A]
        simp only [Z,if_false]
        unfold prePostPC
        rw [reset0_widen_apply,prelaunch_widen_empty_apply]
        have F : pc p+o p+2≤workW p := by unfold pc workW grantBase sealBase sourceW; omega
        have C := dr_field_get p v (pc p+o p) 2 2 0 2 F (by decide) (by decide)
        have K : (((widen p (field p (pc p+o p) 2 2)).apply v).extractLsb' (pc p) (o p)) =
            v.extractLsb' (pc p) (o p) := by
          apply BitVec.eq_of_getLsbD_eq
          intro i I
          simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
          exact pulse_widen_frame p _ _ _ (pulse_field_out p _ _ _ _ (.inl (by omega)))
        exact Prod.ext (by simpa [prePostPC,sourcePhase] using C)
          (by change (((widen p (field p (pc p+o p) 2 2)).apply v).extractLsb' (pc p) (o p)).toNat = (v.extractLsb' (pc p) (o p)).toNat; rw [K])
      · rw [A] at Fit ⊢
        rcases Fit with F|F
        · have K := congrArg (Option.map MISByteCodec.Token.tag) F
          change (some 2 : Option Nat)=some 0 at K; contradiction
        · exact F

end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-- The literal three selector bits, not a live bank read. -/
def acqCaptureIndex (p : Params) (x : BitVec p.w) : Nat :=
  (x.extractLsb' (sourceBase p+(16+2*d p)) 3).toNat

def acqReplyCentre (t : Tok) : Nat := t.payload/16%2

theorem acq_index_low_congr (p : Params) (x y : BitVec p.w)
    (H : ∀ i, i<grantBase p → x.getLsbD i=y.getLsbD i) :
    acqCaptureIndex p x=acqCaptureIndex p y := by
  unfold acqCaptureIndex
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  apply H
  unfold grantBase sealBase sourceW
  omega

/-- The whole-file frame implies the exact three-bit frame. -/
theorem acq_index_of_file (p : Params) (x y : BitVec p.w)
    (H : drainFile p x=drainFile p y) :
    acqCaptureIndex p x=acqCaptureIndex p y := by
  change (x.extractLsb' (sourceBase p) (19+2*d p)).toNat=
    (y.extractLsb' (sourceBase p) (19+2*d p)).toNat at H
  have E : x.extractLsb' (sourceBase p) (19+2*d p)=
      y.extractLsb' (sourceBase p) (19+2*d p) :=
    BitVec.eq_of_toNat_eq H
  unfold acqCaptureIndex
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  have J : 16+2*d p+i<19+2*d p := by omega
  have B := congrArg (fun z : BitVec (19+2*d p) =>
    z.getLsbD (16+2*d p+i)) E
  have J' : 16+(2*d p+i)<19+2*d p := by omega
  simpa only [BitVec.getLsbD_extractLsb',I,J,J',decide_true,
    Bool.true_and,Nat.add_assoc] using B

-- Use the whole six-bit capture region for the mask proof; the exported
-- observation is the index subfield used by WRITE.
private def acqCapFrame (p : Params) (a : Patch (workW p)) : Prop :=
  ∀ i, sourceBase p+(13+2*d p)≤i →
       i<sourceBase p+(19+2*d p) → a.mask.getLsbD i=false

private theorem acq_cap_empty (p : Params) :
    acqCapFrame p (.empty _) := by
  intro i _ _
  simp [Patch.empty]

private theorem acq_cap_comp {p : Params} {a b : Patch (workW p)}
    (A : acqCapFrame p a) (B : acqCapFrame p b) :
    acqCapFrame p (a.compose b) := by
  intro i L R
  exact pulse_comp_out (A i L R) (B i L R)

private theorem acq_cap_src (p : Params) (a : Patch (workW p))
    (A : drSrcFrame p a) : acqCapFrame p a := by
  intro i L R
  apply A i (by omega)
  unfold sealBase sourceW
  omega

private theorem acq_cap_field (p : Params) (k b v : Nat)
    (H : k+b≤sourceBase p+(13+2*d p) ∨
      sourceBase p+(19+2*d p)≤k) :
    acqCapFrame p (field p k b v) := by
  intro i L R
  rcases H with H|H
  · exact pulse_field_out p k b v i (.inr (by omega))
  · exact pulse_field_out p k b v i (.inl (by omega))

private theorem acq_cap_ctrl (p : Params) (a b : Nat) :
    acqCapFrame p (ctrl p a b) := by
  unfold ctrl
  apply acq_cap_field
  right
  unfold pc
  omega

private theorem acq_cap_sf (p : Params) (k b v : Nat)
    (H : k+b≤13+2*d p) : acqCapFrame p (sf p k b v) := by
  unfold sf
  exact acq_cap_field p _ _ _ (.inl (by omega))

private theorem acq_cap_apply (p : Params) (a : Patch (workW p))
    (x : BitVec p.w) (A : acqCapFrame p a) :
    acqCaptureIndex p ((widen p a).apply x)=acqCaptureIndex p x := by
  unfold acqCaptureIndex
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  exact pulse_widen_frame p a x _ (A _ (by omega) (by omega))

private theorem acq_index_write (p : Params) (x : BitVec p.w) (q : Nat) :
    acqCaptureIndex p ((widen p (sf p (13+2*d p) 6 q)).apply x)=q/8%8 := by
  have W := dr_field_sub p x (sourceBase p+(13+2*d p)) 6 q 3 3
    (by unfold workW grantBase sealBase sourceW; omega) (by decide)
  unfold acqCaptureIndex sf
  rw [show sourceBase p+(16+2*d p)=
    sourceBase p+(13+2*d p)+3 by omega,W]
  -- CHECK: ReportByteRows.lean:3863–3870,4972–4976, same extract formula.
  simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  change q % (8*8) / 8 % 8=q/8%8
  rw [Nat.mod_mul_right_div_self,Nat.mod_mod]

/-- Exact successful source action, on the old D. Denial is the
    outcome==1 branch, not an arithmetic return. -/
theorem acq_source_success (p : Params) (v : BitVec p.w) (t : Tok)
    (P : sourcePhase p v=2) (O : sourceOpcode p v=acqOp p)
    (D : t.tag=3) (K : t.opcode=acqOp p) (F : t.fault=false)
    (U : t.outcome≠1) :
    source p v t=
      (((ctrl p 1 (cmpOp p)).compose (sf p (13+2*d p) 6 t.payload)).compose
        (sf p (9+2*d p) 4 0), some MISByteCodec.E) := by
  have V : ¬commitOp p<acqOp p := by unfold commitOp acqOp; omega
  have N : ¬acqOp p<admitOp p := by unfold acqOp admitOp; omega
  have A : acqOp p≠admitOp p := by unfold acqOp admitOp; omega
  have Z : acqOp p≠0 := by unfold acqOp; omega
  unfold sourcePhase at P
  unfold sourceOpcode at O
  simp [source,P,O,D,K,F,U,V,N,A,Z]

/-- Public view of the actual source suffix's post-control. -/
def acqSourcePC (p : Params) (v : BitVec p.w) (t : Tok) : Nat×Nat :=
  let x := (liftSourcePatch p (source p v t).1).apply v
  (sourcePhase p x,sourceOpcode p x)

theorem acq_source_success_pc (p : Params) (v : BitVec p.w) (t : Tok)
    (P : sourcePhase p v=2) (O : sourceOpcode p v=acqOp p)
    (D : t.tag=3) (K : t.opcode=acqOp p) (F : t.fault=false)
    (U : t.outcome≠1) : acqSourcePC p v t=(1,cmpOp p) := by
  change prePostPC p (source p v t).1 v=_
  rw [acq_source_success p v t P O D K F U]
  dsimp only
  rw [prelaunch_post_sf p _ _ _ _ (by omega),
      prelaunch_post_sf p _ _ _ _ (by omega)]
  exact prelaunch_ctrl_write p v (cmpOp p) (by unfold cmpOp; omega)

/-- Exact responder capture after the entire old-pair row. The
    previous prefix can be arbitrary: the full six-bit write kills it.
    The later comparison clear and root E clear are disjoint. -/
theorem acq_row_success_index (p : Params) (hu : Bool) (u v : BitVec p.w)
    (P : sourcePhase p v=2) (O : sourceOpcode p v=acqOp p)
    (D : (publicationToken p true v 0).tag=3)
    (K : (publicationToken p true v 0).opcode=acqOp p)
    (F : (publicationToken p true v 0).fault=false)
    (U : (publicationToken p true v 0).outcome≠1) :
    acqCaptureIndex p ((row p (hu,true) (u,v)).2.apply v)=
      (publicationToken p true v 0).payload/8%8 := by
  let t := oldK p true v 0
  have S := acq_source_success p v t P O D K F U
  rw [dr_row_eq]
  unfold reset0Post
  simp only [if_true,show oldK p true v 0=t from rfl,S]
  rw [reset0_widen_apply]
  rw [acq_cap_apply p _ _ (acq_cap_src p _ (drSK p 0 MISByteCodec.E))]
  rw [reset0_widen_apply]
  rw [reset0_widen_apply]
  rw [acq_cap_apply p _ _ (acq_cap_sf p (9+2*d p) 4 0 (by omega))]
  rw [reset0_widen_apply]
  exact acq_index_write p _ t.payload

theorem acq_row_success_centre (p : Params) (hu : Bool) (u v : BitVec p.w)
    (P : sourcePhase p v=2) (O : sourceOpcode p v=acqOp p)
    (D : (publicationToken p true v 0).tag=3)
    (K : (publicationToken p true v 0).opcode=acqOp p)
    (F : (publicationToken p true v 0).fault=false)
    (U : (publicationToken p true v 0).outcome≠1) :
    acqCaptureIndex p ((row p (hu,true) (u,v)).2.apply v)/2%2=
      acqReplyCentre (publicationToken p true v 0) := by
  rw [acq_row_success_index p hu u v P O D K F U]
  unfold acqReplyCentre
  omega

/-- The initiator endpoint never consumes the source D. This holds
    even if its own old K0 already contains that D. -/
theorem acq_row_left_index (p : Params) (hv : Bool) (u v : BitVec p.w) :
    acqCaptureIndex p ((row p (true,hv) (u,v)).1.apply u)=
      acqCaptureIndex p u :=
  acq_index_of_file p _ _ (drain_row_file_left p hv u v)

/-- All positive source operations reached after successful ACQ,
    before starting the next reset generation. -/
def PostAcqPC (p : Params) (c : Nat×Nat) : Prop :=
  (c.1=1 ∨ c.1=2) ∧ cmpOp p≤c.2 ∧ c.2≤commitOp p

/-- The only branch capable of writing the capture in this opcode
    region is restart, not any legal successful arithmetic operation.
    This mask statement is stronger than comparing two output bits.
    NR does not assert a frame; it excludes the literal reset patch. -/
private theorem acq_source_nonreset_frame (p : Params)
    (v : BitVec p.w) (t : Tok)
    (H : PostAcqPC p (sourcePhase p v,sourceOpcode p v))
    (NR : (source p v t).1≠reset p) :
    acqCapFrame p (source p v t).1 := by
  have O : sourceOpcode p v≤commitOp p := H.2.2
  have L : cmpOp p≤sourceOpcode p v := H.2.1
  rcases H.1 with P|P
  · rcases prelaunch_issue_action p v t P O with R|⟨q,R⟩
    · exact (NR (congrArg Prod.fst R)).elim
    · rw [R]
      have Z : sourceOpcode p v≠0 := by unfold cmpOp at L; omega
      simp only [if_neg Z]
      exact acq_cap_comp (acq_cap_empty p)
        (acq_cap_field p _ _ _ (.inr (by unfold pc; omega)))
  · by_cases T : t.tag=1 ∨ t.tag=2
    · rw [prelaunch_wait_hold p v t P O T]
      exact acq_cap_empty p
    · have H1 : t.tag≠1 := fun A=>T (.inl A)
      have H2 : t.tag≠2 := fun A=>T (.inr A)
      let a := get v (pc p) (o p)
      let inp := rf p v (9+2*d p) 4
      let out := rf p v (5+2*d p) 4
      have LO : cmpOp p≤a := L
      have UO : a≤commitOp p := O
      have V : ¬commitOp p<a := by omega
      have Z : a≠0 := by unfold cmpOp at LO; omega
      have A : ¬a<admitOp p := by unfold cmpOp admitOp at *; omega
      have B : a≠admitOp p := by unfold cmpOp admitOp at *; omega
      have C : a≠acqOp p := by unfold cmpOp acqOp at *; omega
      have PP : get v (pc p+o p) 2=2 := P
      change ¬commitOp p<get v (pc p) (o p) at V
      -- CHECK: ReportByteRows.lean:5769–5874 has the same immutable-old
      -- case split. Here the goal is a mask, not a successor opcode.
      unfold source at NR ⊢
      dsimp only at NR ⊢
      simp only [PP,V,decide_false,
        show ((2:Nat)==0)=false by decide,
        show ((2:Nat)==3)=false by decide,
        show ((2:Nat)==1)=false by decide,
        Bool.false_or,Bool.false_eq_true,if_false,
        beq_false_of_ne H1,beq_false_of_ne H2] at NR ⊢
      by_cases bad : (t.tag != 3 || t.opcode != a || t.fault ||
        t.outcome==1)=true
      · rw [if_pos bad] at NR
        exact (NR rfl).elim
      rw [if_neg bad] at NR ⊢
      rw [if_neg (fun h => Z (beq_iff_eq.mp h)),if_neg A,
        if_neg (fun h => B (beq_iff_eq.mp h)),if_neg (fun h => C (beq_iff_eq.mp h))] at NR ⊢
      by_cases rd : a<writeOp p
      · rw [if_pos rd] at NR ⊢
        by_cases err : (inp/4==3 || inp%4==3 ||
          (!decide (a<readOp p) && (out/4==3 || out%4==3)))=true
        · rw [if_pos err] at NR
          exact (NR rfl).elim
        rw [if_neg err] at NR ⊢
        by_cases cmpC : a<readOp p
        · rw [if_pos cmpC]
          have CP : get v (pc p) (o p)<readOp p := cmpC
          simp only [if_pos CP]
          by_cases more : a-cmpOp p+1<p.digits
          · rw [if_pos more]
            exact acq_cap_comp (acq_cap_ctrl p _ _)
              (acq_cap_sf p (9+2*d p) 4 _ (by omega))
          · rw [if_neg more]
            exact acq_cap_comp
              (acq_cap_comp
                (acq_cap_comp (acq_cap_ctrl p _ _)
                  (acq_cap_sf p (9+2*d p) 4 _ (by omega)))
                (acq_cap_sf p (5+2*d p) 4 _ (by omega)))
              (acq_cap_sf p (3+2*d p) 2 _ (by omega))
        · rw [if_neg cmpC]
          have CP : ¬get v (pc p) (o p)<readOp p := cmpC
          simp only [if_neg CP]
          exact acq_cap_comp
            (acq_cap_comp
              (acq_cap_comp (acq_cap_ctrl p _ _)
                (acq_cap_sf p 3 (2*d p) _ (by omega)))
              (acq_cap_sf p (3+2*d p) 2 _ (by omega)))
            (acq_cap_sf p (5+2*d p) 4 _ (by omega))
      · rw [if_neg rd] at NR ⊢
        by_cases wr : a<sealOp p
        · rw [if_pos wr]
          exact acq_cap_ctrl p _ _
        · rw [if_neg wr] at NR ⊢
          by_cases S : (a==sealOp p)=true
          · rw [if_pos S]
            exact acq_cap_ctrl p _ _
          · rw [if_neg S] at NR
            exact (NR rfl).elim

/-- Nonzero actual post-PC rules out restart. -/
private theorem acq_nonreset_of_pc (p : Params) (v : BitVec p.w) (t : Tok)
    (NZ : (acqSourcePC p v t).2≠0) : (source p v t).1≠reset p := by
  intro R
  apply NZ
  change (prePostPC p (source p v t).1 v).2=0
  rw [R]
  exact congrArg Prod.snd (prelaunch_restart_controls p v)

/-- Any one non-restarting source suffix and both surrounding row
    portions frame the capture, irrespective of other owners' effects. -/
private theorem acq_row_cap_of_source (p : Params) (hu : Bool)
    (u v : BitVec p.w)
    (B : acqCapFrame p (source p v (oldK p true v 0)).1) :
    acqCaptureIndex p ((row p (hu,true) (u,v)).2.apply v)=
      acqCaptureIndex p v := by
  have A := acq_cap_src p _ (drSright p hu u v)
  rw [dr_row_eq]
  unfold reset0Post
  simp only [if_true]
  cases R : source p v (oldK p true v 0) with
  | mk q opt =>
    rw [R] at B
    cases opt with
    | none =>
      dsimp only
      exact acq_cap_apply p _ v
        (acq_cap_comp (acq_cap_comp A B) (acq_cap_empty p))
    | some t =>
      dsimp only
      exact acq_cap_apply p _ v
        (acq_cap_comp (acq_cap_comp A B) (acq_cap_src p _ (drSK p 0 t)))

theorem acq_row_post_index (p : Params) (hu : Bool) (u v : BitVec p.w)
    (H : PostAcqPC p (sourcePhase p v,sourceOpcode p v))
    (NZ : (acqSourcePC p v (publicationToken p true v 0)).2≠0) :
    acqCaptureIndex p ((row p (hu,true) (u,v)).2.apply v)=
      acqCaptureIndex p v :=
  acq_row_cap_of_source p hu u v
    (acq_source_nonreset_frame p v _ H (acq_nonreset_of_pc p v _ NZ))

/-- Positive ISSUE which really emits F, including WRITE, cannot
    reset and does not write the capture. No assumption on the old K0. -/
theorem acq_row_issue_index (p : Params) (hu : Bool) (u v : BitVec p.w)
    (t : Tok) (P : sourcePhase p v=1)
    (O : sourceOpcode p v≤commitOp p) (pos : 0<sourceOpcode p v)
    (T : (source p v (publicationToken p true v 0)).2=some t)
    (F : t.tag=2) :
    acqCaptureIndex p ((row p (hu,true) (u,v)).2.apply v)=
      acqCaptureIndex p v := by
  apply acq_row_cap_of_source
  rcases prelaunch_issue_action p v (oldK p true v 0) P O with R|⟨q,R⟩
  · have X : some t=some MISByteCodec.E := T.symm.trans (congrArg Prod.snd R)
    have E := Option.some.inj X
    rw [E] at F
    simp [MISByteCodec.E] at F
  · rw [R]
    simp only [if_neg (Nat.ne_of_gt pos)]
    exact acq_cap_comp (acq_cap_empty p)
      (acq_cap_field p _ _ _ (.inr (by unfold pc; omega)))

private theorem acq_next_region {t a b : Nat} (E : PreviewNextOp t a b)
    (H : t+3≤a) : t+3≤b := by
  cases E <;> omega

/-- Actual source controls stay in the post-ACQ region if no restart.
    Uses the already checked numerical successor classification, not
    a presumed monotone numerical opcode (WRITE -> READ may decrease). -/
theorem acq_source_post_pc (p : Params) (v : BitVec p.w) (t : Tok)
    (H : PostAcqPC p (sourcePhase p v,sourceOpcode p v))
    (digit : 0<p.digits) (NZ : (acqSourcePC p v t).2≠0) :
    PostAcqPC p (acqSourcePC p v t) := by
  change (prePostPC p (source p v t).1 v).2≠0 at NZ
  change PostAcqPC p (prePostPC p (source p v t).1 v)
  have O : sourceOpcode p v≤commitOp p := H.2.2
  have L : cmpOp p≤sourceOpcode p v := H.2.1
  rcases H.1 with P|P
  · have pos : 0<sourceOpcode p v := by unfold cmpOp at L; omega
    rcases prelaunch_positive_issue_controls p v t P O pos with R|R
    · exact (NZ (congrArg Prod.snd R)).elim
    · rw [R]
      exact ⟨.inr rfl,L,O⟩
  · by_cases T : t.tag=1 ∨ t.tag=2
    · rw [prelaunch_hold_controls p v t P O T]
      exact H
    · rcases prelaunch_wait_controls p v t P O
        (fun A=>T (.inl A)) (fun A=>T (.inr A)) digit with R|⟨b,E,R⟩
      · exact (NZ (congrArg Prod.snd R)).elim
      · rw [R]
        have B := (previewNextOp_bounds E).2
        exact ⟨.inl rfl,acq_next_region E L,by unfold commitOp; omega⟩

/-- Optional exact last reverse-hop codec lemma. The successful
    canonical ACQ D has only its six payload bits; no provenance for
    these bits is asserted. D decoding is independent of the gate. -/
theorem acq_reply_roundtrip (p : Params) (g : Bool) (q : Nat)
    (B : q<64)
    (Fit : RankFits p ({tag:=3,opcode:=acqOp p,payload:=q}:Tok)) :
    decode p g (resetTokenWire p ({tag:=3,opcode:=acqOp p,payload:=q}:Tok))=
      ({tag:=3,opcode:=acqOp p,payload:=q}:Tok) := by
  let t : Tok := {tag:=3,opcode:=acqOp p,payload:=q}
  change decode p g (resetTokenWire p t)=t
  rcases rReadFields p t Fit with ⟨A,F,O,R,U,_,Q⟩
  have ft : (resetTokenWire p t).getLsbD (6+o p+payW p)=false := by
    rw [rGet_bit,F]
    rfl
  have V : ¬commitOp p<acqOp p := by unfold acqOp commitOp; omega
  have L : ¬cmpOp p≤acqOp p := by unfold cmpOp acqOp; omega
  have M : q%2^6=q := Nat.mod_eq_of_lt B
  -- CHECK: ReportByteRows.lean:61–88,4979–5051, decoder and exact wire.
  simp [decode,A,ft,O,R,U,Q,t,V,L,M]

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def reportBankDigitAddress (p : Params) (sel i : Nat) : Nat := bankOffset p sel+i

theorem reportBankDigitAddress_lt (p : Params) (sel i : Nat) (I : i<2*d p) :
    reportBankDigitAddress p sel i<grantBase p := by
  have Q : (1-sel)*bankW p≤bankW p := by
    simpa using Nat.mul_le_mul_right (bankW p) (show 1-sel≤1 by omega)
  unfold reportBankDigitAddress bankOffset grantBase bankW at *
  omega

private theorem rDigitIndex (p : Params) (sel i : Nat) (I : i<2*d p) :
    cmtIndex p (reportBankDigitAddress p sel i) :=
  .inl ⟨by unfold reportBankDigitAddress bankOffset; omega, reportBankDigitAddress_lt p sel i I⟩

private theorem rDigitPrefix (p : Params) (hv : Bool) (u v : BitVec p.w) :
    cmtFrame p (drPre p false hv u v).1 := by
  have B : cmtFrame p (drBaseL p false u) := by
    unfold drBaseL drClear
    simp only [Bool.false_eq_true,if_false]
    apply cmtCompose (cmtCompose (cmtReset p) (cmtSeal p none))
    apply cmtField
    intro i I
    rcases I with ⟨_,I⟩|I
    · exact .inl I
    · exact .inr (by unfold grantBase at *; omega)
  have PP : cmtFrame p (pulse p false 2 u) := by
    intro i I
    apply pulse_mask_below_tail
    rcases I with ⟨I,_⟩|I
    · unfold sealBase sourceBase at I
      omega
    · unfold grantBase sealBase sourceBase at I
      omega
  have NN (j : Fin 3) : cmtFrame p (outgoingNormalize p false u j) := by
    rcases dr_norm_left_shape p false u j with E|⟨t,E⟩
    · rw [E]; exact cmtEmpty p
    · rw [E]; exact cmtK p j t
  change cmtFrame p (drPrefix p (drBaseL p false u) (pulse p false 2 u) (outgoingNormalize p false u))
  exact cmtCompose (cmtCompose (cmtCompose (cmtCompose B PP) (NN 0)) (NN 1)) (NN 2)

/-- The only nonheader initiator effect with a digit-write mask is
a live WRITE from K1 at the opcode-matching offset. -/
private theorem rNonheader_effectL (p : Params) (hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (k : Option (Fin 3)) (w : Bool) (t : Tok) :
    (effect p u v false hv j k w t).1 =
      if t.fault=false ∧ writeOp p≤t.opcode ∧ t.opcode<sealOp p ∧ j=1 ∧
          reportOldOffset p false u=t.opcode-writeOp p then
        field p (bankOffset p ((t.payload/2^(2*d p))%2)) (2*d p) (t.payload%2^(2*d p))
      else .empty _ := by
  have D : t.opcode<sealOp p → t.opcode≠commitOp p := by
    unfold sealOp commitOp
    omega
  unfold reportOldOffset effect
  dsimp only
  cases F : t.fault <;> simp [Bool.and_assoc]
  · by_cases W : writeOp p≤t.opcode ∧ t.opcode<sealOp p ∧ j=1 ∧
        geomOff p false u=t.opcode-writeOp p
    · have N : ¬t.opcode<writeOp p := by omega
      have A : t.opcode≠admitOp p := by unfold writeOp admitOp at *; omega
      simp [W,N,D W.2.1,parked,A]
    · simp [W]
      repeat' first | rfl | split

/-- Per-bit exact nonheader initiator work mask: only the old ready K1
WRITE can set bits in the two digit-pair ranges. -/
def reportNonheaderDigitIntent (p : Params) (u : BitVec p.w) (i : Nat) : Bool :=
  let t := publicationToken p false u 1
  rankReady p false u 1 && !t.fault && decide (writeOp p≤t.opcode) &&
    decide (t.opcode<sealOp p) && (reportOldOffset p false u==t.opcode-writeOp p) &&
    decide (bankOffset p (ancestryWriteTarget p t)≤i) &&
    decide (i<bankOffset p (ancestryWriteTarget p t)+2*d p)

private theorem rNonheader_routeL_mask (p : Params) (hv : Bool) (u v : BitVec p.w)
    (w : Fin 3→Bool) (ab : Pair (Patch (workW p))) (j : Fin 3)
    (k : Option (Fin 3)) (sel i : Nat) (I : i<2*d p) :
    let q := reportBankDigitAddress p sel i
    (cmtRoute p false hv u v w ab (j,k)).1.mask.getLsbD q =
      (ab.1.mask.getLsbD q || ((j==1) && reportNonheaderDigitIntent p u q)) := by
  dsimp only
  rcases ab with ⟨a,b⟩
  let q := reportBankDigitAddress p sel i
  let t := oldK p false u j
  have IX := rDigitIndex p sel i I
  have Q := cmtWork p q IX
  have K (j : Fin 3) (z : Tok) : (writeK p j z).mask.getLsbD q=false := cmtK p j z q IX
  have E := rNonheader_effectL p hv u v j k (w j) t
  unfold cmtRoute
  dsimp only
  by_cases R : rankReady p false u j=true
  · change ready p false u j (oldK p false u j)=true at R
    simp only [R,if_true]
    have EF : (effect p u v false hv j k (w j) t).1.mask.getLsbD q =
        ((j==1) && reportNonheaderDigitIntent p u q) := by
      rw [E]
      by_cases J : j=1
      · subst j
        have RP : rankReady p false u 1=true := R
        simp only [reportNonheaderDigitIntent,RP,beq_self_eq_true,Bool.true_and]
        change (if t.fault=false ∧ writeOp p≤t.opcode ∧ t.opcode<sealOp p ∧
          True ∧ reportOldOffset p false u=t.opcode-writeOp p then
          field p (bankOffset p (ancestryWriteTarget p t)) (2*d p) (t.payload%2^(2*d p))
          else Patch.empty _).mask.getLsbD q = _
        by_cases A : t.fault=false ∧ writeOp p≤t.opcode ∧ t.opcode<sealOp p ∧
            reportOldOffset p false u=t.opcode-writeOp p
        · have J := And.intro A.1 (And.intro A.2.1 (And.intro A.2.2.1
            (And.intro (True.intro) A.2.2.2)))
          rw [if_pos J]
          change _ = (!t.fault && decide (writeOp p≤t.opcode) &&
            decide (t.opcode<sealOp p) &&
            (reportOldOffset p false u==t.opcode-writeOp p) &&
            decide (bankOffset p (ancestryWriteTarget p t)≤q) &&
            decide (q<bankOffset p (ancestryWriteTarget p t)+2*d p))
          simp [A.1,A.2.1,A.2.2.1,A.2.2.2,field,BitVec.getLsbD_shiftLeft,
            BitVec.getLsbD_setWidth,Q]
          let b := bankOffset p (ancestryWriteTarget p t)
          by_cases L : b≤q
          · have N : ¬q<b := by omega
            have E : q-b<2*d p ↔ q<b+2*d p := by omega
            simpa [b] using (show (!decide (q<b) && decide (q-b<2*d p)) = (decide (b≤q) && decide (q<b+2*d p)) by simp [N,L,E])
          · have N : q<b := by omega
            simpa [b] using (show (!decide (q<b) && decide (q-b<2*d p)) = (decide (b≤q) && decide (q<b+2*d p)) by simp [N,L])
        · have J : ¬(t.fault=false ∧ writeOp p≤t.opcode ∧ t.opcode<sealOp p ∧
            True ∧ reportOldOffset p false u=t.opcode-writeOp p) :=
              fun H => A ⟨H.1,H.2.1,H.2.2.1,H.2.2.2.2⟩
          rw [if_neg J]
          change (Patch.empty (workW p)).mask.getLsbD q =
            (!t.fault && decide (writeOp p≤t.opcode) && decide (t.opcode<sealOp p) &&
             (reportOldOffset p false u==t.opcode-writeOp p) && _ && _)
          simp [Patch.empty]
          intro F W L O
          exact (A ⟨F,W,L,O⟩).elim
      · simp [J,Patch.empty]
    dsimp only [q] at K
    dsimp only [q,t] at EF
    cases k <;> simp [Patch.compose,K,EF]
  · change ¬ready p false u j (oldK p false u j)=true at R
    rw [if_neg R]
    have N : ((j==1) && reportNonheaderDigitIntent p u q)=false := by
      by_cases J : j=1
      · subst j
        simp [reportNonheaderDigitIntent,rankReady,t,Bool.eq_false_iff.mpr R]
      · simp [J]
    rw [N]
    dsimp [q] at K
    cases k <;> (repeat' first | simp [Patch.compose,K] | split | rfl)

/-- The complete left row's mask in either digit bank, from arbitrary
old report bytes at a nonheader. No grant or lease predicate is used. -/
theorem report_nonheader_left_digit_mask (p : Params) (hv : Bool) (u v : BitVec p.w)
    (sel i : Nat) (I : i<2*d p) :
    let q := reportBankDigitAddress p sel i
    (row p (false,hv) (u,v)).1.mask.getLsbD q=reportNonheaderDigitIntent p u q := by
  dsimp only
  let q := reportBankDigitAddress p sel i
  have IX := rDigitIndex p sel i I
  have Q := cmtWork p q IX
  have PW : q<p.w := by have L := layout_size p; omega
  rw [dr_row_eq,reset0Post_left]
  change ((drRouted p false hv u v).1.mask.setWidth p.w).getLsbD q = _
  rw [BitVec.getLsbD_setWidth]
  simp only [PW,decide_true,Bool.true_and]
  unfold drRouted links
  have B := rDigitPrefix p hv u v q IX
  change (drPre p false hv u v).1.mask.getLsbD (reportBankDigitAddress p sel i)=false at B
  cases hv <;> simp only [Bool.false_eq_true,if_false,if_true,List.foldl_cons,List.foldl_nil] <;>
    repeat rw [rNonheader_routeL_mask p _ u v _ _ _ _ sel i I] <;>
    simp [B]

theorem report_nonheader_left_bank_frame (p : Params) (hv : Bool) (u v : BitVec p.w)
    (sel : Nat) (S : sel<2)
    (H : rankReady p false u 1=true →
      ancestryWriteTarget p (publicationToken p false u 1)≠sel) :
    reportDigitPair p ((row p (false,hv) (u,v)).1.apply u) sel=reportDigitPair p u sel := by
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  simp only [reportDigitPair,BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  change _ = u.getLsbD (reportBankDigitAddress p sel i)
  apply Patch.hold
  change (row p (false,hv) (u,v)).1.mask.getLsbD (reportBankDigitAddress p sel i)=false
  rw [report_nonheader_left_digit_mask p hv u v sel i I]
  by_cases R : rankReady p false u 1=true
  · have D := H R
    let t := publicationToken p false u 1
    let b := ancestryWriteTarget p t
    have B : b<2 := by unfold b ancestryWriteTarget; exact Nat.mod_lt _ (by decide)
    change b≠sel at D
    have L : reportBankDigitAddress p sel i<bankOffset p b ∨
        bankOffset p b+2*d p≤reportBankDigitAddress p sel i := by
      have T : sel=0 ∨ sel=1 := by omega
      rcases T with rfl|rfl
      · have E : b=1 := by omega
        right; simp [E,reportBankDigitAddress,bankOffset,bankW]; omega
      · have E : b=0 := by omega
        left; simp [E,reportBankDigitAddress,bankOffset,bankW]; omega
    rcases L with L|L
    · have LM : ¬bankOffset p b≤reportBankDigitAddress p sel i := by omega
      simp [reportNonheaderDigitIntent, t, b, LM]
    · have LM : ¬reportBankDigitAddress p sel i<bankOffset p b+2*d p := by omega
      simp [reportNonheaderDigitIntent, t, b, LM]
  · simp [reportNonheaderDigitIntent,Bool.eq_false_iff.mpr R]

end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

private theorem rDigit_effectR (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) (t : Tok)
    (sel i : Nat) (I : i<2*d p) :
    (effect p u v hu hv j k win t).2.1.mask.getLsbD (reportBankDigitAddress p sel i)=false := by
  have A := rDigitIndex p sel i I
  have E := cmtEmpty p _ A
  unfold effect
  dsimp only
  split
  · exact E
  · split
    · split
      · exact cmt_digit_frame p v t.payload sel i I
      · exact E
    · split
      · exact E
      · split
        · exact E
        · split
          · exact E
          · generalize (if t.opcode<readOp p then cmpOp p else readOp p) = off
            split
            · exact E
            · split
              · split <;> exact E
              · split
                · split <;> exact E
                · exact E

private theorem rDigit_routeR (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (w : Fin 3→Bool) (ab : Pair (Patch (workW p))) (r : Fin 3 × Option (Fin 3))
    (sel i : Nat) (I : i<2*d p)
    (B : ab.2.mask.getLsbD (reportBankDigitAddress p sel i)=false) :
    (cmtRoute p hu hv u v w ab r).2.mask.getLsbD (reportBankDigitAddress p sel i)=false := by
  rcases ab with ⟨a,b⟩
  rcases r with ⟨j,k⟩
  have IX := rDigitIndex p sel i I
  have K (j : Fin 3) (z : Tok) := cmtK p j z _ IX
  have F := rDigit_effectR p hu hv u v j k (w j) (oldK p hu u j) sel i I
  unfold cmtRoute
  dsimp only
  cases k with
  | none =>
    split
    · exact pulse_comp_out B F
    · split <;> exact B
  | some k =>
    split
    · exact pulse_comp_out (pulse_comp_out B F) (K _ _)
    · by_cases T : ((oldK p hu u j).tag==2)=true
      · rw [if_pos T]
        exact B
      · rw [if_neg T]
        dsimp only
        by_cases G : ((oldK p hv v k).tag==3)=true
        · rw [if_pos G]
          exact pulse_comp_out B (K _ _)
        · rw [if_neg G]
          split <;> exact B

/-- Every right digit bit is masked off, even if a different lane
has an accepted ingress COMMIT. The COMMIT writes only report metadata. -/
theorem report_right_digit_mask (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (sel i : Nat) (I : i<2*d p) :
    (row p (hu,hv) (u,v)).2.mask.getLsbD (reportBankDigitAddress p sel i)=false := by
  let q := reportBankDigitAddress p sel i
  have IX := rDigitIndex p sel i I
  have Q := cmtWork p q IX
  have PW : q<p.w := by have L := layout_size p; omega
  have QT := reportBankDigitAddress_lt p sel i I
  have E := cmtEmpty p q IX
  have GG (g : Fin 3→Bool) : (grants p g).mask.getLsbD q=false :=
    pulse_field_out p _ _ _ _ (.inl QT)
  have B : (drBaseR p hv v).mask.getLsbD q=false := by
    unfold drBaseR drClear
    split
    · split
      · exact GG _
      · exact E
    · exact pulse_comp_out (pulse_comp_out (cmtReset p q IX) (cmtSeal p none q IX)) (GG _)
  have PP : (pulse p hv 1 v).mask.getLsbD q=false := by
    apply pulse_mask_below_tail
    have L : sealBase p+5≤q := by unfold q reportBankDigitAddress bankOffset; omega
    unfold sealBase sourceBase at L
    omega
  have NN (j : Fin 3) : (cmtNorm p hv v j).mask.getLsbD q=false := by
    rcases dr_norm_right_shape p hv v j with T|⟨t,T⟩
    · rw [T]; exact E
    · rw [T]; exact cmtK p j t q IX
  have Pre : (drPre p hu hv u v).2.mask.getLsbD q=false :=
    pulse_comp_out (pulse_comp_out (pulse_comp_out (pulse_comp_out B PP) (NN 0)) (NN 1)) (NN 2)
  have fold (xs : List (Fin 3 × Option (Fin 3))) (a : Pair (Patch (workW p)))
      (A : a.2.mask.getLsbD q=false) :
      (xs.foldl (cmtRoute p hu hv u v (drWin p hu u)) a).2.mask.getLsbD q=false := by
    induction xs generalizing a with
    | nil => exact A
    | cons r rs IH => exact IH _ (rDigit_routeR p hu hv u v _ a r sel i I A)
  have R : (drRouted p hu hv u v).2.mask.getLsbD q=false := fold _ _ Pre
  rw [dr_row_eq]
  change ((reset0Post p hv v (drRouted p hu hv u v)).2.mask.setWidth p.w).getLsbD q=false
  rw [BitVec.getLsbD_setWidth]
  simp only [PW,decide_true,Bool.true_and]
  cases hv
  · exact R
  · unfold reset0Post
    simp only [if_true]
    exact pulse_comp_out (pulse_comp_out R (cmtSource p v (oldK p true v 0) q IX))
      (cmtSourceToken p (source p v (oldK p true v 0)).2 q IX)

theorem report_nonheader_left_bank_frame_of_enabled (p : Params) (hv : Bool) (u v : BitVec p.w)
    (sel : Nat) (S : sel<2)
    (H : let t := publicationToken p false u 1
      rankReady p false u 1=true → t.fault=false → writeOp p≤t.opcode →
      t.opcode<sealOp p → reportOldOffset p false u=t.opcode-writeOp p →
      ancestryWriteTarget p t≠sel) :
    reportDigitPair p ((row p (false,hv) (u,v)).1.apply u) sel=reportDigitPair p u sel := by
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  simp only [reportDigitPair,BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  change _ = u.getLsbD (reportBankDigitAddress p sel i)
  apply Patch.hold
  change (row p (false,hv) (u,v)).1.mask.getLsbD (reportBankDigitAddress p sel i)=false
  rw [report_nonheader_left_digit_mask p hv u v sel i I]
  by_cases R : rankReady p false u 1=true
  · let t := publicationToken p false u 1
    by_cases E0 : t.fault=false ∧ writeOp p≤t.opcode ∧ t.opcode<sealOp p ∧
        reportOldOffset p false u=t.opcode-writeOp p
    · have D := H R E0.1 E0.2.1 E0.2.2.1 E0.2.2.2
      let b := ancestryWriteTarget p t
      have B : b<2 := by unfold b ancestryWriteTarget; exact Nat.mod_lt _ (by decide)
      change b≠sel at D
      have L : reportBankDigitAddress p sel i<bankOffset p b ∨
          bankOffset p b+2*d p≤reportBankDigitAddress p sel i := by
        have T : sel=0 ∨ sel=1 := by omega
        rcases T with rfl|rfl
        · have E : b=1 := by omega
          right; simp [E,reportBankDigitAddress,bankOffset,bankW]; omega
        · have E : b=0 := by omega
          left; simp [E,reportBankDigitAddress,bankOffset,bankW]; omega
      rcases L with L|L
      · have LM : ¬bankOffset p b≤reportBankDigitAddress p sel i := by omega
        simp [reportNonheaderDigitIntent, t, b, LM]
      · have LM : ¬reportBankDigitAddress p sel i<bankOffset p b+2*d p := by omega
        simp [reportNonheaderDigitIntent, t, b, LM]
    · unfold reportNonheaderDigitIntent
      change (rankReady p false u 1 && !t.fault && decide (writeOp p≤t.opcode) &&
        decide (t.opcode<sealOp p) && (reportOldOffset p false u==t.opcode-writeOp p) && _ && _)=false
      simp only [R,Bool.true_and,Bool.eq_false_iff]
      intro J
      simp only [Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,beq_iff_eq] at J
      exact E0 ⟨J.1.1.1.1.1,J.1.1.1.1.2,J.1.1.1.2,J.1.1.2⟩
  · simp [reportNonheaderDigitIntent,Bool.eq_false_iff.mpr R]

end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

def acqFlightF (p : Params) (q : Nat) : Tok :=
  {tag:=2,opcode:=acqOp p,payload:=q}

def acqFlightD (p : Params) (q : Nat) : Tok :=
  if q/64%2=1 then {tag:=3,opcode:=acqOp p,payload:=q%64}
  else {tag:=3,opcode:=acqOp p,outcome:=1}

@[simp] theorem acqFlightD_tag (p : Params) (q : Nat) :
    (acqFlightD p q).tag=3 := by unfold acqFlightD; split <;> rfl
@[simp] theorem acqFlightD_op (p : Params) (q : Nat) :
    (acqFlightD p q).opcode=acqOp p := by unfold acqFlightD; split <;> rfl
@[simp] theorem acqFlightD_live (p : Params) (q : Nat) :
    (acqFlightD p q).fault=false := by unfold acqFlightD; split <;> rfl

def acqFlightWin (p : Params) (hu : Bool) (u : BitVec p.w) (j : Fin 3) : Bool :=
  drWin p hu u j

def acqFlightNext (p : Params) (hu : Bool) (u : BitVec p.w)
    (j : Fin 3) (q : Nat) : Nat :=
  if hu then
    if acqFlightWin p hu u j then
      writeBit (writeBit q (5-j.val) (selected p u==1))
        (2-j.val) (aBit p u (selected p u))
    else writeBit q 6 false
  else q

private theorem acqFlight_opfit (p : Params) : acqOp p<2^o p := by
  have B := power_of_ell (5+4*p.digits)
  unfold o acqOp
  omega

private theorem acqFlight_payfit (p : Params) {q : Nat} (Q : q<128) :
    q<2^payW p :=
  Nat.lt_of_lt_of_le Q
    (Nat.pow_le_pow_right (show 1≤(2:Nat) by decide)
      (by unfold payW; omega : 7≤payW p))

private theorem acqFlight_edit_low (q j : Nat) (b : Bool) (Q : q<128)
    (J : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5) :
    writeBit q j b<128 ∧ writeBit q j b/64=q/64 ∧
    (j≠4 → writeBit q j b/16%2=q/16%2) ∧
    (j=4 → writeBit q j b/16%2=b.toNat) := by
  rcases J with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;>
    simp [writeBit,bit,Nat.shiftRight_eq_div_pow] <;>
    split <;> omega

private theorem acqFlight_edit_denial (q : Nat) (Q : q<128) :
    writeBit q 6 false<64 ∧ writeBit q 6 false/16%2=q/16%2 := by
  simp [writeBit,bit,Nat.shiftRight_eq_div_pow]
  split <;> omega

/-- The old-pair update is bounded, success is sticky, and exactly
    the winning header lane 1 supplies bit 4. -/
theorem acqFlight_next_spec (p : Params) (hu : Bool) (u : BitVec p.w)
    (j : Fin 3) (q : Nat) (Q : q<128) :
    let r := acqFlightNext p hu u j q
    r<128 ∧ (r/64=1 → q/64=1) ∧
    (hu=true ∧ j=1 → r/64=1 →
      acqFlightWin p hu u j=true ∧ r/16%2=publicationSelector p u) ∧
    (¬(hu=true ∧ j=1) → r/16%2=q/16%2) := by
  dsimp only
  cases hu with
  | false => simp [acqFlightNext,Q]
  | true =>
    cases W : acqFlightWin p true u j with
    | false =>
      have D := acqFlight_edit_denial q Q
      rw [acqFlightNext,if_pos rfl,if_neg (by simp [W])]
      refine ⟨by omega,by omega,?_,fun _=>D.2⟩
      intro _ R
      omega
    | true =>
      rw [acqFlightNext,if_pos rfl,if_pos W]
      let a := writeBit q (5-j.val) (selected p u==1)
      let b := writeBit a (2-j.val) (aBit p u (selected p u))
      have J := j.isLt
      have L := acqFlight_edit_low q (5-j.val) (selected p u==1) Q (by omega)
      have M := acqFlight_edit_low a (2-j.val) (aBit p u (selected p u)) L.1 (by omega)
      change b<128 ∧ (b/64=1→q/64=1) ∧
        (true=true ∧ j=1 → b/64=1 →
          true=true ∧ b/16%2=publicationSelector p u) ∧
        (¬(true=true ∧ j=1)→b/16%2=q/16%2)
      refine ⟨M.1,fun H=>by rw [←L.2.1,←M.2.1]; exact H,?_,?_⟩
      · intro H _
        have X : 5-j.val=4 := by rw [H.2]; decide
        have Y : 2-j.val≠4 := by omega
        refine ⟨rfl,(M.2.2.1 Y).trans ((L.2.2.2 X).trans ?_)⟩
        have S : selected p u<2 := (u.extractLsb' (grantBase p+3) 1).isLt
        rcases (show selected p u=0 ∨ selected p u=1 by omega) with E|E <;>
          simp [publicationSelector,E]
      · intro H
        have N : j≠1 := fun E=>H ⟨rfl,E⟩
        have V : j.val≠1 := fun E=>N (Fin.ext E)
        exact (M.2.2.1 (by omega)).trans (L.2.2.1 (by omega))

theorem acqFlight_win_grant (p : Params) (u : BitVec p.w) (j : Fin 3)
    (W : acqFlightWin p true u j=true) : grantNext p true u j=true := by
  change ((canonical p u j && !grantAsk p true u 0 j) ||
    acqFlightWin p true u j)=true
  rw [W]
  simp

theorem acqFlight_effect (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (k : Option (Fin 3)) (q : Nat) :
    (effect p u v hu hv j k (acqFlightWin p hu u j) (acqFlightF p q)).2.2=
      acqFlightF p (acqFlightNext p hu u j q) := by
  have AD : acqOp p≠admitOp p := by unfold acqOp admitOp; omega
  have CM : acqOp p≠commitOp p := by unfold acqOp commitOp; omega
  have Z : acqOp p≠0 := by unfold acqOp; omega
  have C : ¬cmpOp p≤acqOp p := by unfold acqOp cmpOp; omega
  have W : ¬writeOp p≤acqOp p := by unfold acqOp writeOp; omega
  have S : acqOp p≠sealOp p := by unfold acqOp sealOp; omega
  cases hu <;> simp [effect,acqFlightF,acqFlightNext,parked,AD,CM,Z,C,W,S]

theorem acqFlight_F_roundtrip (p : Params) (g : Bool) (q : Nat) (Q : q<128) :
    decode p g (resetTokenWire p (acqFlightF p q))=acqFlightF p q := by
  let t := acqFlightF p q
  have Fit : RankFits p t :=
    ⟨by change 2<4; decide,acqFlight_opfit p,acqFlight_payfit p Q,by change 0<8; decide,by change 0<4; decide⟩
  rcases rReadFields p t Fit with ⟨A,F,O,R,U,_,V⟩
  have ft : (resetTokenWire p t).getLsbD (6+o p+payW p)=false := by
    rw [rGet_bit,F]
    rfl
  have AD : acqOp p≠admitOp p := by unfold acqOp admitOp; omega
  have CM : acqOp p≠commitOp p := by unfold acqOp commitOp; omega
  have L : ¬commitOp p<acqOp p := by unfold acqOp commitOp; omega
  have C : ¬cmpOp p≤acqOp p := by unfold acqOp cmpOp; omega
  have W : ¬writeOp p≤acqOp p := by unfold acqOp writeOp; omega
  have S : ¬sealOp p≤acqOp p := by unfold acqOp sealOp; omega
  change decode p g (resetTokenWire p t)=t
  -- CHECK: ReportByteRows.lean:61–88,4979–5044 (same simp pattern
  -- as rAdmit_roundtrip at 5169); if necessary dsimp [t,acqFlightF] at A F O R U V.
  simp only [decode,A,ft,O,R,U,V]
  simp [t,acqFlightF,AD,CM,L,C,W,S,Nat.mod_eq_of_lt Q]

private theorem acqFlight_D_good_codec (p : Params) (g : Bool) (q : Nat)
    (Q : q<64) :
    decode p g (resetTokenWire p ({tag:=3,opcode:=acqOp p,payload:=q}:Tok))=
      ({tag:=3,opcode:=acqOp p,payload:=q}:Tok) := by
  let t : Tok := {tag:=3,opcode:=acqOp p,payload:=q}
  have Fit : RankFits p t :=
    ⟨by change 3<4; decide,acqFlight_opfit p,acqFlight_payfit p (show q<128 by omega),by change 0<8; decide,by change 0<4; decide⟩
  exact acq_reply_roundtrip p g q Q Fit

private theorem acqFlight_D_bad_codec (p : Params) (g : Bool) :
    decode p g (resetTokenWire p ({tag:=3,opcode:=acqOp p,outcome:=1}:Tok))=
      ({tag:=3,opcode:=acqOp p,outcome:=1}:Tok) := by
  let t : Tok := {tag:=3,opcode:=acqOp p,outcome:=1}
  have Fit : RankFits p t :=
    ⟨by change 3<4; decide,acqFlight_opfit p,Nat.two_pow_pos _,by change 0<8; decide,by change 1<4; decide⟩
  rcases rReadFields p t Fit with ⟨A,F,O,R,U,_,V⟩
  have ft : (resetTokenWire p t).getLsbD (6+o p+payW p)=false := by
    rw [rGet_bit,F]
    rfl
  have L : ¬commitOp p<acqOp p := by unfold acqOp commitOp; omega
  have C : ¬cmpOp p≤acqOp p := by unfold acqOp cmpOp; omega
  change decode p g (resetTokenWire p t)=t
  simp only [decode,A,ft,O,R,U,V]
  simp [t,L,C]

theorem acqFlight_D_roundtrip (p : Params) (g : Bool) (q : Nat) :
    decode p g (resetTokenWire p (acqFlightD p q))=acqFlightD p q := by
  unfold acqFlightD
  split
  · exact acqFlight_D_good_codec p g _ (Nat.mod_lt _ (by decide))
  · exact acqFlight_D_bad_codec p g

theorem acqFlight_D_success (p : Params) (q : Nat) (Q : q<128)
    (H : (acqFlightD p q).outcome≠1) :
    q/64=1 ∧ (acqFlightD p q).payload/16%2=q/16%2 := by
  unfold acqFlightD at H ⊢
  split
  · rename_i W
    exact ⟨by omega,by change (q%64)/16%2=q/16%2; omega⟩
  · rename_i W
    exact (H (by simp [acqFlightD,W])).elim

theorem acqFlight_issue (p : Params) (v : BitVec p.w) (t : Tok)
    (P : sourcePhase p v=1) (O : sourceOpcode p v=acqOp p) :
    (source p v t).2=some (acqFlightF p 64) := by
  have L : ¬commitOp p<acqOp p := by unfold commitOp acqOp; omega
  have W : ¬writeOp p≤acqOp p := by unfold writeOp acqOp; omega
  have S : ¬sealOp p≤acqOp p := by unfold sealOp acqOp; omega
  have Z : acqOp p≠0 := by unfold acqOp; omega
  unfold sourcePhase at P
  unfold sourceOpcode at O
  simp [source,P,O,L,W,S,Z,acqFlightF]

theorem rankAcq_ready (p : Params) (hu : Bool) (u : BitVec p.w)
    (j : Fin 3) (q : Nat) (A : publicationToken p hu u j=acqFlightF p q) :
    rankReady p hu u j=true := by
  have N : acqOp p≠admitOp p := by unfold acqOp admitOp; omega
  rw [rankReady_iff,A]
  simp [acqFlightF,healthyAdmit,N]

theorem rankAcq_norm (p : Params) (side : Nat) (h : Bool)
    (u : BitVec p.w) (j : Fin 3)
    (H : (publicationToken p h u j).fault=false)
    (O : (publicationToken p h u j).opcode=acqOp p) :
    rankNormWire p side (rankGate p h u j) (resetTokenRead p u j)=resetTokenRead p u j := by
  rw [rankToken_wire] at H O
  have A : acqOp p≠admitOp p := by unfold acqOp admitOp; omega
  simp [rankNormWire,rankNormIntent,H,O,A]

theorem rankAcq_door_norm (p : Params) (v : BitVec p.w)
    (H : (publicationToken p true v 0).fault=false) :
    prelaunchDoorNormWire p v=resetTokenRead p v 0 := by
  change (oldK p true v 0).fault=false at H
  have K : parked p (oldK p true v 0) true v 0=false := by simp [parked,gate]
  simp [prelaunchDoorNormWire,H,K]

theorem rankAcq_hop (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (J : reset0Destination hv j=some k) (g' : Bool)
    (q : Nat) (Q : q<128) (A : publicationToken p hu u j=acqFlightF p q) :
    decode p g' (resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k)=
      acqFlightF p (acqFlightNext p hu u j q) := by
  have R := rankAcq_ready p hu u j q A
  rw [rank_row_right p hu hv u v j k J]
  simp only [rankRouteR,R,if_true,Option.elim]
  change decode p g' (resetTokenWire p (arrival p hv v k
    (effect p u v hu hv j (some k) (acqFlightWin p hu u j)
      (publicationToken p hu u j)).2.2))=_
  rw [A,acqFlight_effect]
  have AD : acqOp p≠admitOp p := by unfold acqOp admitOp; omega
  have B (r : Nat) : arrival p hv v k (acqFlightF p r)=acqFlightF p r := by
    simp [arrival,acqFlightF,AD]
  rw [B]
  exact acqFlight_F_roundtrip p g' _ (acqFlight_next_spec p hu u j q Q).1

theorem rankAcq_turn (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (J : reset0Destination hv j=none) (g' : Bool)
    (q : Nat) (_Q : q<128) (A : publicationToken p hu u j=acqFlightF p q) :
    decode p g' (resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j)=
      acqFlightD p (acqFlightNext p hu u j q) := by
  have R := rankAcq_ready p hu u j q A
  rw [rank_row_left,J]
  simp only [rankRouteL,R,if_true,Option.elim]
  change decode p g' (resetTokenWire p (terminal p
    (effect p u v hu hv j none (acqFlightWin p hu u j)
      (publicationToken p hu u j)).2.2))=_
  rw [A,acqFlight_effect]
  have CM : acqOp p≠commitOp p := by unfold acqOp commitOp; omega
  have B (r : Nat) : terminal p (acqFlightF p r)=acqFlightD p r := by
    simp [terminal,acqFlightF,acqFlightD,CM,bit,Nat.shiftRight_eq_div_pow,beq_iff_eq]
  rw [B]
  exact acqFlight_D_roundtrip p g' _

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

private theorem rHeader_denied_effect (p : Params) (hv : Bool)
    (u v : BitVec p.w) (G : reportOldGrant p u 1=false)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) (t : Tok) :
    cmtFrame p (effect p u v true hv j k win t).1 := by
  change gBit p u 1=false at G
  unfold effect
  dsimp only
  split
  · exact cmtEmpty p
  · split
    · split <;> exact cmtEmpty p
    · split
      · exact cmtEmpty p
      · split
        · exact cmtSeal p none
        · split
          · exact cmtEmpty p
          · generalize (if t.opcode<readOp p then cmpOp p else readOp p) = off
            split
            · exact cmtEmpty p
            · split
              · simp [G]
                exact cmtEmpty p
              · split
                · split
                  · exact cmtSeal p (some t.payload)
                  · exact cmtEmpty p
                · exact cmtEmpty p

private theorem rHeader_denied_route (p : Params) (hv : Bool)
    (u v : BitVec p.w) (G : reportOldGrant p u 1=false)
    (w : Fin 3→Bool) (ab : Pair (Patch (workW p)))
    (l : Fin 3 × Option (Fin 3)) (A : cmtFrame p ab.1) :
    cmtFrame p (cmtRoute p true hv u v w ab l).1 := by
  rcases ab with ⟨a,b⟩
  rcases l with ⟨j,k⟩
  have E0 := rHeader_denied_effect p hv u v G j k (w j) (oldK p true u j)
  cases k with
  | none =>
    unfold cmtRoute
    dsimp only
    split
    · exact cmtCompose (cmtCompose A E0) (cmtK p _ _)
    · split
      · exact A
      · split
        · exact cmtCompose A (cmtK p _ _)
        · exact A
  | some k =>
    unfold cmtRoute
    dsimp only
    split
    · exact cmtCompose (cmtCompose A E0) (cmtK p _ _)
    · split
      · exact A
      · split
        · exact cmtCompose A (cmtK p _ _)
        · split
          · exact cmtCompose A (cmtK p _ _)
          · exact A

/-- A header's outgoing old pair cannot write a digit bank if its old
K1 writer grant is false, even if another incidence has a ready WRITE. -/
theorem report_header_denied_left_digit_mask (p : Params) (hv : Bool)
    (u v : BitVec p.w) (G : reportOldGrant p u 1=false) (sel i : Nat) (I : i<2*d p) :
    (row p (true,hv) (u,v)).1.mask.getLsbD (reportBankDigitAddress p sel i)=false := by
  let q := reportBankDigitAddress p sel i
  have IX := rDigitIndex p sel i I
  have Q := cmtWork p q IX
  have PW : q<p.w := by have L := layout_size p; omega
  have B : cmtFrame p (drBaseL p true u) := by
    unfold drBaseL
    simp only [if_true]
    apply cmtField
    intro i I
    rcases I with ⟨_,I⟩|I
    · exact .inl I
    · exact .inr (by omega)
  have PP : cmtFrame p (pulse p true 2 u) := by
    intro i I
    apply pulse_mask_below_tail
    rcases I with ⟨I,_⟩|I
    · unfold sealBase sourceBase at I; omega
    · unfold grantBase sealBase sourceBase at I; omega
  have NN (j : Fin 3) : cmtFrame p (outgoingNormalize p true u j) := by
    rcases dr_norm_left_shape p true u j with E|⟨t,E⟩
    · rw [E]; exact cmtEmpty p
    · rw [E]; exact cmtK p j t
  have Pre : cmtFrame p (drPre p true hv u v).1 :=
    cmtCompose (cmtCompose (cmtCompose (cmtCompose B PP) (NN 0)) (NN 1)) (NN 2)
  have fold (xs : List (Fin 3 × Option (Fin 3))) (a : Pair (Patch (workW p)))
      (A : cmtFrame p a.1) :
      cmtFrame p (xs.foldl (cmtRoute p true hv u v (drWin p true u)) a).1 := by
    induction xs generalizing a with
    | nil => exact A
    | cons l ls IH => exact IH _ (rHeader_denied_route p hv u v G _ a l A)
  have R : cmtFrame p (drRouted p true hv u v).1 := fold _ _ Pre
  rw [dr_row_eq,reset0Post_left]
  change ((drRouted p true hv u v).1.mask.setWidth p.w).getLsbD q=false
  rw [BitVec.getLsbD_setWidth]
  simp only [PW,decide_true,Bool.true_and]
  exact R q IX

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- WRITE and SEAL ACKs change only the positive controller PC.
COMMIT ACK is deliberately outside the interval: it restarts. -/
def writeSealNext (p : Params) (op : Nat) : Nat :=
  if op<sealOp p then
    if op-writeOp p+1<p.digits then readOp p+(op-writeOp p)+1 else sealOp p
  else commitOp p

theorem write_seal_ack_action (p : Params) (x : BitVec p.w) (t : Tok)
    (I : sourcePhase p x=2) (L : writeOp p≤sourceOpcode p x)
    (U : sourceOpcode p x≤sealOp p)
    (T : t.tag=3) (Op : t.opcode=sourceOpcode p x)
    (Live : t.fault=false) (Ok : t.outcome≠1) :
    source p x t=(ctrl p 1 (writeSealNext p (sourceOpcode p x)),some MISByteCodec.E) := by
  have Z : sourceOpcode p x≠0 := by unfold writeOp at L; omega
  have O : ¬commitOp p<sourceOpcode p x := by unfold sealOp at U; unfold commitOp; omega
  have A : ¬sourceOpcode p x<admitOp p := by unfold writeOp admitOp at *; omega
  have B : sourceOpcode p x≠admitOp p := by unfold writeOp admitOp at *; omega
  have C : sourceOpcode p x≠acqOp p := by unfold writeOp acqOp at *; omega
  have D : ¬sourceOpcode p x<writeOp p := Nat.not_lt_of_ge L
  unfold sourcePhase at I
  by_cases Edge : sourceOpcode p x<sealOp p
  · unfold sourceOpcode at Op Z O A B C D Edge ⊢
    simp [source,I,T,Op,Live,Ok,Z,O,A,B,C,D,Edge,writeSealNext]
  · have E : sourceOpcode p x=sealOp p := by omega
    unfold sourceOpcode at Op Z O A B C D E ⊢
    simp [source,I,T,Op,Live,Ok,E,writeSealNext,show ¬commitOp p<sealOp p by unfold commitOp sealOp; omega,
      show sealOp p≠0 by unfold sealOp; omega,show ¬sealOp p<admitOp p by unfold sealOp admitOp; omega,
      show sealOp p≠admitOp p by unfold sealOp admitOp; omega,
      show sealOp p≠acqOp p by unfold sealOp acqOp; omega,
      show ¬sealOp p<writeOp p by unfold sealOp writeOp; omega]

theorem write_seal_ack_row_file (p : Params) (hu : Bool) (u v : BitVec p.w)
    (I : sourcePhase p v=2) (L : writeOp p≤sourceOpcode p v)
    (U : sourceOpcode p v≤sealOp p)
    (T : (publicationToken p true v 0).tag=3)
    (Op : (publicationToken p true v 0).opcode=sourceOpcode p v)
    (Live : (publicationToken p true v 0).fault=false)
    (Ok : (publicationToken p true v 0).outcome≠1) :
    drainFile p ((row p (hu,true) (u,v)).2.apply v)=drainFile p v := by
  have F := dr_file_frame p _ v (drSright p hu u v)
  have R := write_seal_ack_action p v (oldK p true v 0) I L U T Op Live Ok
  rw [dr_row_eq]
  unfold reset0Post
  simp only [if_true,R]
  rw [reset0_widen_apply,dr_file_frame p _ _ (drSK p _ _),reset0_widen_apply]
  apply Eq.trans (dr_file_late p _ _ _ _ (Nat.le_refl _)) F

theorem write_seal_ack_control (p : Params) (x : BitVec p.w) (t : Tok)
    (I : sourcePhase p x=2) (L : writeOp p≤sourceOpcode p x)
    (U : sourceOpcode p x≤sealOp p)
    (T : t.tag=3) (Op : t.opcode=sourceOpcode p x)
    (Live : t.fault=false) (Ok : t.outcome≠1) :
    acqSourcePC p x t=(1,writeSealNext p (sourceOpcode p x)) := by
  change prePostPC p (source p x t).1 x=_
  rw [write_seal_ack_action p x t I L U T Op Live Ok]
  apply prelaunch_ctrl_write
  unfold writeSealNext
  split
  · split
    · unfold readOp; omega
    · unfold sealOp; omega
  · unfold commitOp; omega

end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

private theorem rSealKFrame (p : Params) (j : Fin 3) (t : Tok) :
    drSealFrame p (writeK p j t) :=
  drSealEarly p _ _ _ (by have := reset0SlotBound p j; unfold sealBase; omega)

private theorem rSealFrame_read (p : Params) (a : Patch (workW p))
    (x : BitVec p.w) (A : drSealFrame p a) :
    reportOldSeal p ((widen p a).apply x)=reportOldSeal p x := by
  have V : ((widen p a).apply x).extractLsb' (sealBase p) 5=x.extractLsb' (sealBase p) 5 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i I
    simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
    exact pulse_widen_frame p a x _ (A _ (by omega) (by omega))
  have T := congrArg BitVec.toNat V
  change get ((widen p a).apply x) (sealBase p) 5=get x (sealBase p) 5 at T
  unfold reportOldSeal readSeal
  rw [T]

private theorem rSeal_routeR_frame_step (p : Params) (hu : Bool) (u v : BitVec p.w)
    (win : Fin 3→Bool) (ab : Pair (Patch (workW p)))
    (l : Fin 3 × Option (Fin 3)) (A : drSealFrame p ab.2)
    (B : ready p hu u l.1 (oldK p hu u l.1)=true →
      drSealFrame p (effect p u v hu true l.1 l.2 (win l.1) (oldK p hu u l.1)).2.1) :
    drSealFrame p (cmtRoute p hu true u v win ab l).2 := by
  rcases ab with ⟨a,b⟩
  rcases l with ⟨j,k⟩
  let t := oldK p hu u j
  unfold cmtRoute
  dsimp only
  by_cases R : ready p hu u j t=true
  · rw [if_pos R]
    cases k with
    | none => exact drSealCompFrame A (B R)
    | some k => exact drSealCompFrame (drSealCompFrame A (B R)) (rSealKFrame p k _)
  · rw [if_neg R]
    by_cases Fwd : (t.tag==2)=true
    · rw [if_pos Fwd]
      exact A
    · rw [if_neg Fwd]
      cases k with
      | none => exact A
      | some k =>
        dsimp only
        let q := oldK p true v k
        by_cases Reply : (q.tag==3)=true
        · rw [if_pos Reply]
          exact drSealCompFrame A (rSealKFrame p k _)
        · rw [if_neg Reply]
          by_cases Trail : (t.tag==1 && q.tag==0)=true
          · rw [if_pos Trail]
            exact A
          · rw [if_neg Trail]
            exact A

private theorem rSeal_preR_frame (p : Params) (hu : Bool) (u v : BitVec p.w) :
    drSealFrame p (drPre p hu true u v).2 := by
  have A : drSealFrame p (drBaseR p true v) := by
    unfold drBaseR
    simp only [if_true]
    split
    · apply drSealField
      right
      unfold grantBase
      omega
    · exact drSealEmptyFrame p
  have B : drSealFrame p (pulse p true 1 v) :=
    fun i L _=>pulse_mask_below_tail p true 1 v i
      (by unfold sealBase sourceBase at L; omega)
  have N (j : Fin 3) : drSealFrame p (cmtNorm p true v j) := by
    rcases dr_norm_right_shape p true v j with H|⟨t,H⟩
    · rw [H]; exact drSealEmptyFrame p
    · rw [H]; exact rSealKFrame p j t
  exact drSealCompFrame (drSealCompFrame (drSealCompFrame
    (drSealCompFrame A B) (N 0)) (N 1)) (N 2)

private theorem rSeal_post_frame (p : Params) (v : BitVec p.w)
    (ab : Pair (Patch (workW p))) (A : drSealFrame p ab.2) :
    drSealFrame p (reset0Post p true v ab).2 := by
  unfold reset0Post
  simp only [if_true]
  apply drSealCompFrame (drSealCompFrame A (drSealSource p v (oldK p true v 0)))
  split
  · exact drSealEmptyFrame p
  · exact rSealKFrame p 0 _

/-- Without an accepted old ingress COMMIT, the right header seal
bits are all masked off in the complete report row. -/
theorem report_header_right_seal_frame (p : Params) (hu : Bool) (u v : BitVec p.w)
    (H : ¬ancestryCommitOpportunity p hu true u v)
    (i : Nat) (L : sealBase p≤i) (U : i<sealBase p+5) :
    (row p (hu,true) (u,v)).2.mask.getLsbD i=false := by
  have fold (xs : List (Fin 3 × Option (Fin 3))) (ab : Pair (Patch (workW p)))
      (A : drSealFrame p ab.2) :
      drSealFrame p (xs.foldl (cmtRoute p hu true u v (drWin p hu u)) ab).2 := by
    induction xs generalizing ab with
    | nil => exact A
    | cons l ls IH =>
      apply IH
      apply rSeal_routeR_frame_step p hu u v _ ab l A
      intro R
      rw [ancSel_effectR p u v hu true l.1 l.2 _ R H]
      exact drSealEmptyFrame p
  have A := rSeal_post_frame p v (drRouted p hu true u v)
    (fold _ _ (rSeal_preR_frame p hu u v))
  rw [dr_row_eq]
  have W := layout_size p
  have F : i<p.w := by unfold workW grantBase at W; omega
  simp [widen,F,A i L U]

theorem report_header_right_seal_hold (p : Params) (hu : Bool) (u v : BitVec p.w)
    (H : ¬ancestryCommitOpportunity p hu true u v) :
    reportOldSeal p ((row p (hu,true) (u,v)).2.apply v)=reportOldSeal p v := by
  have V : ((row p (hu,true) (u,v)).2.apply v).extractLsb' (sealBase p) 5=v.extractLsb' (sealBase p) 5 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i I
    simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
    apply Patch.hold
    exact report_header_right_seal_frame p hu u v H _ (by omega) (by omega)
  have T := congrArg BitVec.toNat V
  change get ((row p (hu,true) (u,v)).2.apply v) (sealBase p) 5=get v (sealBase p) 5 at T
  unfold reportOldSeal readSeal
  rw [T]

private theorem rSeal_routeR_zero (p : Params) (hu : Bool) (u v x : BitVec p.w)
    (win : Fin 3→Bool) (ab : Pair (Patch (workW p)))
    (l : Fin 3 × Option (Fin 3))
    (A : drainSealZero p ((widen p ab.2).apply x)) :
    drainSealZero p ((widen p (cmtRoute p hu true u v win ab l).2).apply x) := by
  rcases ab with ⟨a,b⟩
  rcases l with ⟨j,k⟩
  have EF := drSealEffectR p u v hu true j k (win j) (oldK p hu u j)
  let t := oldK p hu u j
  unfold cmtRoute
  dsimp only
  by_cases R : ready p hu u j t=true
  · rw [if_pos R]
    cases k with
    | none =>
      rw [reset0_widen_apply]
      exact EF _ A
    | some k =>
      rw [reset0_widen_apply,reset0_widen_apply]
      exact drSealK p k _ _ (EF _ A)
  · rw [if_neg R]
    by_cases Fwd : (t.tag==2)=true
    · rw [if_pos Fwd]
      exact A
    · rw [if_neg Fwd]
      cases k with
      | none => exact A
      | some k =>
        dsimp only
        let q := oldK p true v k
        by_cases Reply : (q.tag==3)=true
        · rw [if_pos Reply,reset0_widen_apply]
          exact drSealK p k _ _ A
        · rw [if_neg Reply]
          by_cases Trail : (t.tag==1 && q.tag==0)=true
          · rw [if_pos Trail]
            exact A
          · rw [if_neg Trail]
            exact A

/-- The accepted COMMIT is the exact literal old K0→K1 crossing:
full joined-row application makes all five right seal bits zero. -/
theorem report_header_right_seal_clear_bits (p : Params) (hu : Bool) (u v : BitVec p.w)
    (H : ancestryCommitOpportunity p hu true u v) :
    drainSealZero p ((row p (hu,true) (u,v)).2.apply v) := by
  obtain ⟨_,Ready,Live,Op,Grant⟩ := H
  let w := drWin p hu u
  let z := drPre p hu true u v
  let a := cmtRoute p hu true u v w z (0,some 1)
  let t := oldK p hu u 0
  have E := commit_effect_snapshot p hu (w 0) u v t Op Live
  rw [if_pos Grant] at E
  have A : drainSealZero p ((widen p a.2).apply v) := by
    unfold a cmtRoute
    dsimp only
    change ready p hu u 0 (oldK p hu u 0)=true at Ready
    rw [if_pos Ready,E]
    dsimp only
    rw [reset0_widen_apply]
    apply drSealFrameSafe p _ (rSealKFrame p 1 _) _
    rw [reset0_widen_apply]
    unfold cmtPatch
    rw [reset0_widen_apply,reset0_widen_apply]
    apply drSealLate p _ _ _ (by unfold bankOffset; omega) _
    exact drSealClear p _
  let b := cmtRoute p hu true u v w a (1,some 2)
  let c := cmtRoute p hu true u v w b (2,none)
  have B := rSeal_routeR_zero p hu u v v w a (1,some 2) A
  have C := rSeal_routeR_zero p hu u v v w b (2,none) B
  rw [dr_row_eq]
  change drainSealZero p ((widen p (reset0Post p true v c).2).apply v)
  unfold reset0Post
  simp only [if_true]
  rw [reset0_widen_apply,reset0_widen_apply]
  apply drSealFrameSafe p _ _ _ (drSealFrameSafe p _ (drSealSource p v (oldK p true v 0)) _ C)
  split
  · exact drSealEmptyFrame p
  · exact rSealKFrame p 0 _

theorem report_header_right_seal_clear (p : Params) (hu : Bool) (u v : BitVec p.w)
    (H : ancestryCommitOpportunity p hu true u v) :
    reportOldSeal p ((row p (hu,true) (u,v)).2.apply v)=none :=
  drain_seal_none p _ (report_header_right_seal_clear_bits p hu u v H)

theorem report_seal_of_extract (p : Params) (x y : BitVec p.w)
    (H : x.extractLsb' (sealBase p) 5=y.extractLsb' (sealBase p) 5) :
    reportOldSeal p x=reportOldSeal p y := by
  have V := congrArg BitVec.toNat H
  change get x (sealBase p) 5=get y (sealBase p) 5 at V
  unfold reportOldSeal readSeal
  rw [V]

end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def reportHeaderResetSeal (p : Params) (u : BitVec p.w) : Prop :=
  rankReady p true u 1=true ∧ (publicationToken p true u 1).fault=false ∧
    (publicationToken p true u 1).opcode=0

def reportHeaderSetSeal (p : Params) (u : BitVec p.w) : Prop :=
  let t := publicationToken p true u 1
  rankReady p true u 1=true ∧ t.fault=false ∧ t.opcode=sealOp p ∧
    reportOldGrant p u 1=true ∧ publicationSelector p u=t.payload/8

private theorem rSeal_effectL_frame_no (p : Params) (hv : Bool) (u v : BitVec p.w)
    (w : Fin 3→Bool) (j : Fin 3) (k : Option (Fin 3))
    (R : ready p true u j (oldK p true u j)=true)
    (NR : ¬reportHeaderResetSeal p u) (NS : ¬reportHeaderSetSeal p u) :
    drSealFrame p (effect p u v true hv j k (w j) (oldK p true u j)).1 := by
  let t := oldK p true u j
  change drSealFrame p (effect p u v true hv j k (w j) t).1
  unfold effect
  dsimp only
  split
  · exact drSealEmptyFrame p
  · rename_i healthy
    have Live : t.fault=false := Bool.eq_false_iff.mpr healthy
    split
    · split <;> exact drSealEmptyFrame p
    · split
      · exact drSealEmptyFrame p
      · split
        · rename_i Clear
          simp only [Bool.and_eq_true,beq_iff_eq] at Clear
          obtain ⟨⟨_,J⟩,Op⟩ := Clear
          subst j
          exact (NR ⟨R,Live,Op⟩).elim
        · split
          · exact drSealEmptyFrame p
          · generalize (if t.opcode<readOp p then cmpOp p else readOp p) = off
            split
            · exact drSealEmptyFrame p
            · split
              · split
                · exact drSealEmptyFrame p
                · apply drSealField
                  right
                  unfold bankOffset
                  omega
              · split
                · rename_i Seal
                  simp only [Bool.and_eq_true,beq_iff_eq] at Seal
                  obtain ⟨⟨Op,J⟩,_⟩ := Seal
                  subst j
                  split
                  · rename_i Guard
                    simp only [Bool.and_eq_true,beq_iff_eq] at Guard
                    exact (NS ⟨R,Live,Op,Guard.1,Guard.2⟩).elim
                  · exact drSealEmptyFrame p
                · exact drSealEmptyFrame p

private theorem rSeal_routeL_frame_step (p : Params) (hv : Bool) (u v : BitVec p.w)
    (win : Fin 3→Bool) (ab : Pair (Patch (workW p)))
    (l : Fin 3 × Option (Fin 3)) (A : drSealFrame p ab.1)
    (B : ready p true u l.1 (oldK p true u l.1)=true →
      drSealFrame p (effect p u v true hv l.1 l.2 (win l.1) (oldK p true u l.1)).1) :
    drSealFrame p (cmtRoute p true hv u v win ab l).1 := by
  rcases ab with ⟨a,b⟩
  rcases l with ⟨j,k⟩
  cases k with
  | none =>
    unfold cmtRoute
    dsimp only
    split
    · rename_i R
      exact drSealCompFrame (drSealCompFrame A (B R)) (rSealKFrame p j _)
    · split
      · exact A
      · split
        · exact drSealCompFrame A (rSealKFrame p j _)
        · exact A
  | some k =>
    unfold cmtRoute
    dsimp only
    split
    · rename_i R
      exact drSealCompFrame (drSealCompFrame A (B R)) (rSealKFrame p j _)
    · split
      · exact A
      · split
        · exact drSealCompFrame A (rSealKFrame p j _)
        · split
          · exact drSealCompFrame A (rSealKFrame p j _)
          · exact A

private theorem rSeal_preL_frame (p : Params) (hv : Bool) (u v : BitVec p.w) :
    drSealFrame p (drPre p true hv u v).1 := by
  have A : drSealFrame p (drBaseL p true u) := by
    unfold drBaseL
    simp only [if_true]
    apply drSealField
    right
    unfold grantBase
    omega
  have B : drSealFrame p (pulse p true 2 u) :=
    fun i L _=>pulse_mask_below_tail p true 2 u i
      (by unfold sealBase sourceBase at L; omega)
  have N (j : Fin 3) : drSealFrame p (outgoingNormalize p true u j) := by
    rcases dr_norm_left_shape p true u j with H|⟨t,H⟩
    · rw [H]; exact drSealEmptyFrame p
    · rw [H]; exact rSealKFrame p j t
  exact drSealCompFrame (drSealCompFrame (drSealCompFrame
    (drSealCompFrame A B) (N 0)) (N 1)) (N 2)

theorem report_header_left_seal_hold (p : Params) (hv : Bool) (u v : BitVec p.w)
    (NR : ¬reportHeaderResetSeal p u) (NS : ¬reportHeaderSetSeal p u) :
    reportOldSeal p ((row p (true,hv) (u,v)).1.apply u)=reportOldSeal p u := by
  have fold (xs : List (Fin 3 × Option (Fin 3))) (ab : Pair (Patch (workW p)))
      (A : drSealFrame p ab.1) :
      drSealFrame p (xs.foldl (cmtRoute p true hv u v (drWin p true u)) ab).1 := by
    induction xs generalizing ab with
    | nil => exact A
    | cons l ls IH =>
      apply IH
      apply rSeal_routeL_frame_step p hv u v _ ab l A
      exact fun R=>rSeal_effectL_frame_no p hv u v _ _ _ R NR NS
  rw [dr_row_eq,reset0Post_left]
  exact rSealFrame_read p _ _ (fold _ _ (rSeal_preL_frame p hv u v))

private theorem rSeal_side_empty (p : Params) (hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (k : Option (Fin 3)) (w : Bool) (t : Tok) (J : j≠1) :
    (effect p u v true hv j k w t).1=.empty _ := by
  unfold effect
  dsimp only
  have B : (j==1)=false := by simp [J]
  simp only [B,Bool.and_false,Bool.false_and,Bool.false_eq_true,if_false]
  repeat' first | rfl | split

private theorem rSeal_side_after (p : Params) (hv : Bool) (u v x : BitVec p.w)
    (win : Fin 3→Bool) (ab : Pair (Patch (workW p))) (j : Fin 3)
    (k : Option (Fin 3)) (J : j≠1) :
    reportOldSeal p ((widen p (cmtRoute p true hv u v win ab (j,k)).1).apply x)=
      reportOldSeal p ((widen p ab.1).apply x) := by
  rcases ab with ⟨a,b⟩
  let t := oldK p true u j
  have Fr := rSeal_side_empty p hv u v j k (win j) t J
  unfold cmtRoute
  dsimp only
  by_cases R : ready p true u j t=true
  · rw [if_pos R]
    cases k <;> (
      rw [Fr,reset0_widen_apply,reset0_widen_apply]
      rw [rSealFrame_read p _ _ (rSealKFrame p j _)]
      exact rSealFrame_read p _ _ (drSealEmptyFrame p))
  · rw [if_neg R]
    by_cases Fwd : (t.tag==2)=true
    · rw [if_pos Fwd]
    · rw [if_neg Fwd]
      cases k with
      | none =>
        dsimp only
        by_cases Trail : (t.tag==1)=true
        · rw [if_pos Trail,reset0_widen_apply]
          exact rSealFrame_read p _ _ (rSealKFrame p j _)
        · rw [if_neg Trail]
      | some k =>
        dsimp only
        let q := oldK p hv v k
        by_cases Reply : (q.tag==3)=true
        · rw [if_pos Reply,reset0_widen_apply]
          exact rSealFrame_read p _ _ (rSealKFrame p j _)
        · rw [if_neg Reply]
          by_cases Trail : (t.tag==1 && q.tag==0)=true
          · rw [if_pos Trail,reset0_widen_apply]
            exact rSealFrame_read p _ _ (rSealKFrame p j _)
          · rw [if_neg Trail]

/-- A ready K1 seal action supplies its exact field after the complete
initiator fold; other lanes cannot overwrite that field. -/
private theorem rSeal_left_written (p : Params) (hv : Bool) (u v : BitVec p.w)
    (o : Option Nat) (s0 : Option Nat)
    (R : rankReady p true u 1=true)
    (W : ∀ k,(effect p u v true hv 1 k (drWin p true u 1) (oldK p true u 1)).1=writeSeal p o)
    (P : ∀ x : BitVec p.w, reportOldSeal p ((widen p (writeSeal p o)).apply x)=s0) :
    reportOldSeal p ((row p (true,hv) (u,v)).1.apply u)=s0 := by
  rw [dr_row_eq,reset0Post_left]
  have K (b : Pair (Patch (workW p))) (k : Fin 3) :
      reportOldSeal p ((widen p (cmtRoute p true hv u v (drWin p true u) b (1,some k)).1).apply u)=s0 := by
    rcases b with ⟨a,b⟩
    unfold cmtRoute
    dsimp only
    change ready p true u 1 (oldK p true u 1)=true at R
    rw [if_pos R]
    dsimp only
    rw [W,reset0_widen_apply,reset0_widen_apply,
      rSealFrame_read p _ _ (rSealKFrame p 1 _)]
    exact P _
  cases hv
  · rw [show drRouted p true false u v=
      cmtRoute p true false u v (drWin p true u)
        (cmtRoute p true false u v (drWin p true u)
          (cmtRoute p true false u v (drWin p true u) (drPre p true false u v) (0,some 0))
          (1,some 1)) (2,some 2) from rfl]
    rw [rSeal_side_after p false u v u _ _ (2:Fin 3) (some 2) (by decide)]
    exact K _ 1
  · rw [show drRouted p true true u v=
      cmtRoute p true true u v (drWin p true u)
        (cmtRoute p true true u v (drWin p true u)
          (cmtRoute p true true u v (drWin p true u) (drPre p true true u v) (0,some 1))
          (1,some 2)) (2,none) from rfl]
    rw [rSeal_side_after p true u v u _ _ (2:Fin 3) none (by decide)]
    exact K _ 2

theorem report_header_left_seal_clear (p : Params) (hv : Bool) (u v : BitVec p.w)
    (R : reportHeaderResetSeal p u) :
    reportOldSeal p ((row p (true,hv) (u,v)).1.apply u)=none := by
  obtain ⟨Ready,Live,Op⟩ := R
  apply rSeal_left_written p hv u v none none Ready
  · intro k
    change (oldK p true u 1).opcode=0 at Op
    change (oldK p true u 1).fault=false at Live
    have A : (0:Nat)≠admitOp p := by unfold admitOp; omega
    have B : (0:Nat)≠commitOp p := by unfold commitOp; omega
    simp [effect,Op,Live,A,B,parked]
  · intro x
    exact drain_seal_none p _ (drSealClear p x)

private theorem rSeal_decoded_descriptor (p : Params) (g : Bool) (raw : BitVec (tokenW p))
    (Tag : (decode p g raw).tag=2) (Live : (decode p g raw).fault=false)
    (Op : (decode p g raw).opcode=sealOp p) :
    (decode p g raw).payload<16 ∧ legalDesc (decode p g raw).payload=true := by
  have T0 := (rank_decode_tag p g raw).symm.trans Tag
  revert Live Op
  let P (t : Tok) := t.fault=false → t.opcode=sealOp p →
    t.payload<16 ∧ legalDesc t.payload=true
  change P (decode p g raw)
  unfold decode
  simp only [T0,show ((2:Nat)==0)=false by decide,show ((2:Nat)==1)=false by decide,
    beq_self_eq_true,if_true,Bool.false_eq_true,if_false]
  generalize (get raw (payW p+6) (o p)) = op
  by_cases A : op=sealOp p
  · subst op
    have AC : sealOp p≠acqOp p := by unfold sealOp acqOp; omega
    have AD : sealOp p≠admitOp p := by unfold sealOp admitOp; omega
    have K : ¬commitOp p<sealOp p := by unfold sealOp commitOp; omega
    simp [AC,AD,K]
    split
    · intro H; contradiction
    · split
      · intro H; contradiction
      · split
        · intro H; contradiction
        · rename_i D
          exact fun _ _ => ⟨Nat.mod_lt _ (by decide : 0<(16:Nat)),by simpa using D⟩
  · repeat' first
    | (change P (MISByteCodec.faultToken 2); intro H; contradiction)
    | (change P ({tag:=2,opcode:=op,payload:=_,race:=_,applied:=_} : Tok)
       intro _ H
       exact (A H).elim)
    | split

private theorem rSeal_write_some (p : Params) (x : BitVec p.w) (a : Nat)
    (A : a<16) (V : legalDesc a=true) :
    reportOldSeal p ((widen p (writeSeal p (some a))).apply x)=some a := by
  have K := dr_field_sub p x (sealBase p) 5 (16+a) 0 5
    (by unfold workW grantBase; omega) (by decide)
  have E : (((widen p (writeSeal p (some a))).apply x).extractLsb' (sealBase p) 5).toNat=16+a := by
    change (((widen p (field p (sealBase p) 5 (16+a))).apply x).extractLsb' (sealBase p) 5).toNat=16+a
    have K' := K
    simp only [Nat.add_zero] at K'
    rw [K']
    simp [BitVec.extractLsb'_toNat,Nat.mod_eq_of_lt (show 16+a<32 by omega)]
  change get ((widen p (writeSeal p (some a))).apply x) (sealBase p) 5=16+a at E
  unfold reportOldSeal readSeal
  rw [E]
  have X : (16+a)%16=a := by omega
  simp [X,V]

theorem report_header_left_seal_install (p : Params) (hv : Bool) (u v : BitVec p.w)
    (R : reportHeaderSetSeal p u) :
    reportOldSeal p ((row p (true,hv) (u,v)).1.apply u)=
      some (publicationToken p true u 1).payload := by
  obtain ⟨Ready,Live,Op,G,S⟩ := R
  let t := publicationToken p true u 1
  change t.fault=false at Live
  change t.opcode=sealOp p at Op
  change publicationSelector p u=t.payload/8 at S
  have Tag := ((rankReady_iff p true u 1).mp Ready).1
  have D := rSeal_decoded_descriptor p (rankGate p true u 1) (resetTokenRead p u 1)
    (by rwa [←rankToken_wire]) (by rwa [←rankToken_wire]) (by rwa [←rankToken_wire])
  apply rSeal_left_written p hv u v (some t.payload) (some t.payload) Ready
  · intro k
    have E := seal_effect_old p hv u v k (drWin p true u 1) t Live Op
    have K : (reportOldGrant p u 1 && publicationSelector p u==t.payload/8)=true := by simp [G,S]
    rw [if_pos K] at E
    exact congrArg Prod.fst E
  · exact fun x => rSeal_write_some p x t.payload D.1 D.2

end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
set_option backward.split false
set_option linter.unusedSimpArgs false

def RailAligned (a : Nat) (t : Tok) : Prop :=
  (t.tag=2 ∨ t.tag=3) → t.fault=false → t.opcode=a

private theorem rail_empty (a : Nat) : RailAligned a E := by
  intro T _
  rcases T with T|T <;> contradiction

private theorem rail_trail (a : Nat) : RailAligned a T := by
  intro H _
  rcases H with H|H <;> contradiction

-- CHECK: ReportByteRows.lean:61–88,6645–6659; analogous to
-- rHealthy_forward_op, but the healthy return branch has outcome.
private theorem rail_healthy_return_op (p : Params) (g : Bool)
    (w : BitVec (tokenW p)) (T0 : (decode p g w).tag=3)
    (H : (decode p g w).fault=false) :
    (decode p g w).opcode=get w (payW p+6) (o p) := by
  have Tag := (rank_decode_tag p g w).symm.trans T0
  revert H
  let P (t : Tok) := t.fault=false→t.opcode=get w (payW p+6) (o p)
  change P (decode p g w)
  unfold decode
  simp only [Tag,show ((3:Nat)==0)=false by decide,
    show ((3:Nat)==1)=false by decide,show ((3:Nat)==2)=false by decide,
    Bool.false_eq_true,if_false]
  repeat' first
  | (change P (F 3); intro H; contradiction)
  | (change P ({tag:=3,opcode:=_,payload:=_,outcome:=_} : Tok);
     intro _; rfl)
  | split

/-- No healthy opcode is invented by encoding/decoding a fitted
token. This is true even when the destination's gate differs. -/
theorem rail_encode_aligned (p : Params) (g : Bool) (a : Nat)
    (t : Tok) (Fit : RankFits p t) (A : RailAligned a t) :
    RailAligned a (decode p g (resetTokenWire p t)) := by
  intro Tag H
  have T0 := Tag
  rw [rank_encode_tag p g t Fit] at T0
  have OF : t.fault=false := by
    cases Q : t.fault with
    | false => rfl
    | true =>
      have B : (resetTokenWire p t).getLsbD (6+o p+payW p)=true := by
        rw [rGet_bit,(rReadFields p t Fit).2.1,Q]
        rfl
      have D : decode p g (resetTokenWire p t)=F t.tag := by
        unfold decode
        dsimp only
        rw [(rReadFields p t Fit).1]
        rcases T0 with T2|T3
        · simp [T2,B]
        · simp [T3,B]
      rw [D] at H
      contradiction
  have W : (decode p g (resetTokenWire p t)).opcode=
      get (resetTokenWire p t) (payW p+6) (o p) := by
    rcases Tag with T2|T3
    · exact rHealthy_forward_op p g _ T2 H
    · exact rail_healthy_return_op p g _ T3 H
  rw [W,(rReadFields p t Fit).2.2.1]
  exact A T0 OF

private theorem rail_encoded_empty (p : Params) (g : Bool) (a : Nat) :
    RailAligned a (decode p g (resetTokenWire p E)) :=
  rail_encode_aligned p g a E (rE_fits p) (rail_empty a)

private theorem rail_encoded_trail (p : Params) (g : Bool) (a : Nat) :
    RailAligned a (decode p g (resetTokenWire p T)) :=
  rail_encode_aligned p g a T (rT_fits p) (rail_trail a)

/-- Exact normalizer: same old decoded token, or the existing ADMIT
race update. In particular, normalization cannot revive a fault. -/
theorem rail_norm_aligned (p : Params) (g : Bool)
    (w : BitVec (tokenW p)) (side a : Nat)
    (S : side=2 ∨ side=3) (A : RailAligned a (decode p g w)) :
    RailAligned a (decode p g (rankNormWire p side g w)) := by
  let t := decode p g w
  by_cases F0 : t.fault=true
  · obtain ⟨Q,R⟩ := rDecoded_fault p g w F0
    unfold rankNormWire rankNormIntent
    rw [if_pos F0]
    change RailAligned a (decode p g (resetTokenWire p t))
    exact rail_encode_aligned p g a t (rank_decoded_fits p g w) A
  · have F1 : t.fault=false := Bool.eq_false_iff.mpr F0
    by_cases P : t.tag=2 ∧ t.opcode=admitOp p ∧ g=true ∧
        (t.race=1 ∨ t.race=(if side=3 then 2 else 3))
    · obtain ⟨T0,O0,G,R⟩ := P
      subst g
      have H : healthyAdmit p t := ⟨T0,F1,O0⟩
      rw [rank_norm_race p w side S H R]
      intro J K
      exact A J K
    · have B : (t.tag==2 && t.opcode==admitOp p && g &&
          (t.race==1 || t.race==(if side=3 then 2 else 3)))=false := by
        apply Bool.eq_false_iff.mpr
        intro B
        apply P
        simpa [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,and_assoc] using B
      change RailAligned a (decode p g
        ((if t.fault then some t else if
           t.tag==2 && t.opcode==admitOp p && g &&
            (t.race==1 || t.race==(if side=3 then 2 else 3))
          then some (advanceRace t side) else none).elim w (resetTokenWire p)))
      simpa [F1,B,t] using A

-- CHECK: ReportByteRows.lean:236–275. The projections of a record
-- update reduce; every new token in a rejecting branch is F 2.
private theorem rail_effect_live (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (j : Fin 3) (k : Option (Fin 3))
    (win : Bool) (t : Tok) (a : Nat) (A : t.fault=false→t.opcode=a) :
    let z := (effect p u v hu hv j k win t).2.2
    z.fault=false→z.opcode=a := by
  dsimp only
  by_cases F0 : t.fault=true
  · simp [effect,F0]
  · have O := A (Bool.eq_false_iff.mpr F0)
    unfold effect
    dsimp only
    rw [if_neg F0]
    repeat' first
    | (intro _; exact O)
    | (intro H; contradiction)
    | split

private theorem rail_arrival_live (p : Params) (hv : Bool)
    (v : BitVec p.w) (k : Fin 3) (t : Tok) (a : Nat)
    (A : t.fault=false→t.opcode=a) :
    (arrival p hv v k t).fault=false→(arrival p hv v k t).opcode=a := by
  unfold arrival
  split <;> exact A

-- CHECK: ReportByteRows.lean:222–230; an unapplied COMMIT is F 3.
private theorem rail_terminal_live (p : Params) (t : Tok) (a : Nat)
    (A : t.fault=false→t.opcode=a) :
    (terminal p t).fault=false→(terminal p t).opcode=a := by
  by_cases F0 : t.fault=true
  · simp [terminal,F0,MISByteCodec.faultToken]
  · have O := A (Bool.eq_false_iff.mpr F0)
    unfold terminal
    repeat' first
    | (intro _; exact O)
    | (intro H; contradiction)
    | split

/-- Exact left result, including terminal turn and reverse routing.
The destination premise is required only if it belongs to this route. -/
theorem rail_row_left_aligned (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (j : Fin 3) (a : Nat)
    (A : RailAligned a (publicationToken p hu u j))
    (B : ∀ k,reset0Destination hv j=some k→
      RailAligned a (publicationToken p hv v k)) :
    RailAligned a (decode p (rankGate p hu u j)
      (resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j)) := by
  have NL := rail_norm_aligned p (rankGate p hu u j)
    (resetTokenRead p u j) 3 a (.inr rfl) A
  have Fit : RankFits p (oldK p hu u j) := rank_decoded_fits p _ _
  rw [rank_row_left]
  cases D : reset0Destination hv j with
  | none =>
    by_cases R : rankReady p hu u j=true
    · have Tag := ((rankReady_iff p hu u j).mp R).1
      have OP := rail_effect_live p hu hv u v j none (drWin p hu u j)
        (oldK p hu u j) a (A (.inl Tag))
      obtain ⟨rfl,rfl⟩ := rTerminal_dest hv j D
      let z := (effect p u v hu true 2 none (drWin p hu u 2)
        (oldK p hu u 2)).2.2
      have V := rTerminal_effect p hu u v (drWin p hu u 2) (oldK p hu u 2) Fit
      have TF := rTerminal_fit p z V.1 V.2
      simp only [rankRouteL,R,if_true,Option.elim]
      exact rail_encode_aligned p _ a _ TF.2
        (fun _ => rail_terminal_live p z a OP)
    · unfold rankRouteL
      dsimp only
      rw [if_neg R]
      split
      · exact NL
      · split
        · exact rail_encoded_empty p _ a
        · exact NL
  | some k =>
    by_cases R : rankReady p hu u j=true
    · simp only [rankRouteL,R,if_true,Option.elim]
      exact rail_encoded_trail p _ a
    · have BA := B k D
      have KFit : RankFits p (oldK p hv v k) :=
        rank_decoded_fits p _ _
      unfold rankRouteL
      dsimp only
      rw [if_neg R]
      split
      · exact NL
      · split
        · exact rail_encode_aligned p _ a _ KFit BA
        · split
          · exact rail_encoded_empty p _ a
          · exact NL

/-- Exact right result. In the ready case the only active arrival
comes from the old F, not from the overwritten destination. -/
theorem rail_row_right_aligned (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (j k : Fin 3) (D : reset0Destination hv j=some k)
    (a : Nat) (A : RailAligned a (publicationToken p hu u j))
    (B : RailAligned a (publicationToken p hv v k)) :
    RailAligned a (decode p (rankGate p hv v k)
      (resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k)) := by
  have NR := rail_norm_aligned p (rankGate p hv v k)
    (resetTokenRead p v k) 2 a (.inl rfl) B
  rw [rank_row_right p hu hv u v j k D]
  by_cases R : rankReady p hu u j=true
  · let t := oldK p hu u j
    let z := (effect p u v hu hv j (some k) (drWin p hu u j) t).2.2
    have Tag : t.tag=2 := ((rankReady_iff p hu u j).mp R).1
    have Fit : RankFits p t := rank_decoded_fits p _ _
    have EF := rHop_effect p hu hv u v j k (drWin p hu u j) t Fit Tag
    have ZF := rHop_arrival p hv v k z EF.2 EF.1
    have OP := rail_effect_live p hu hv u v j (some k) (drWin p hu u j)
      t a (A (.inl Tag))
    simp only [rankRouteR,R,if_true,Option.elim]
    exact rail_encode_aligned p _ a _ ZF.2
      (fun _=>rail_arrival_live p hv v k z a OP)
  · unfold rankRouteR
    dsimp only
    rw [if_neg R]
    split
    · exact NR
    · split
      · exact rail_encoded_empty p _ a
      · exact NR

/-- The door's K0 cannot undergo the parked K1 race. -/
theorem rail_door_norm_aligned (p : Params) (v : BitVec p.w)
    (a : Nat) (A : RailAligned a (publicationToken p true v 0)) :
    RailAligned a (decode p false (prelaunchDoorNormWire p v)) := by
  unfold prelaunchDoorNormWire
  dsimp only
  by_cases H : (oldK p true v 0).fault=true
  · rw [if_pos H]
    exact rail_encode_aligned p false a _ (rank_decoded_fits p _ _) A
  · rw [if_neg H]
    have K : parked p (oldK p true v 0) true v 0=false := by
      simp [parked,gate]
    simp only [K,Bool.false_and,Bool.false_eq_true,if_false]
    exact A

/-- ISSUE provenance of a fitted emitted F, even when its encoded
descriptor subsequently faults. -/
theorem rail_issue_opcode (p : Params) (v : BitVec p.w) (t z : Tok)
    (P : sourcePhase p v=1) (O : sourceOpcode p v≤commitOp p)
    (S : (source p v t).2=some z) (T0 : z.tag=2) :
    z.opcode=sourceOpcode p v := by
  rcases prelaunch_issue_action p v t P O with R|⟨q,R⟩
  · have H := congrArg Prod.snd R
    rw [S] at H
    have Z : z=E := Option.some.inj H
    rw [Z] at T0
    contradiction
  · have H := congrArg Prod.snd R
    rw [S] at H
    exact congrArg MISByteCodec.Token.opcode (Option.some.inj H)

theorem rail_door_issue_aligned (p : Params) (v : BitVec p.w) (t : Tok)
    (P : sourcePhase p v=1) (O : sourceOpcode p v≤commitOp p) :
    let act := source p v t
    let pc' := (sourcePhase p ((liftSourcePatch p act.1).apply v),
      sourceOpcode p ((liftSourcePatch p act.1).apply v))
    RailAligned pc'.2 (decode p false
      (match act.2 with
      | none=>prelaunchDoorNormWire p v
      | some z=>resetTokenWire p z)) := by
  dsimp only
  rcases source_issue_joint p v t P O with ⟨PC,S⟩|⟨PC,z,S,Tag,Fit⟩
  · rw [S]
    exact rail_encoded_empty p false _
  · have PC' : sourceOpcode p ((liftSourcePatch p (source p v t).1).apply v)=sourceOpcode p v :=
      congrArg Prod.snd PC
    rw [S,PC']
    exact rail_encode_aligned p false _ z Fit
      (fun _ _=>rail_issue_opcode p v t z P O S Tag)

end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000

def acqCaptureSix (p : Params) (x : BitVec p.w) : Nat :=
  (x.extractLsb' (sourceBase p+(13+2*ReportByteRows.d p)) 6).toNat

def acqCaptureHeader (p : Params) (x : BitVec p.w) : Nat :=
  (x.extractLsb' (sourceBase p+(13+2*ReportByteRows.d p)) 3).toNat

def acqPair (q : Nat) (j : Fin 3) : Nat × Nat :=
  (q/2^(5-j.val)%2,q/2^(2-j.val)%2)

theorem acq_six_bound (p : Params) (x : BitVec p.w) :
    acqCaptureSix p x<64 :=
  (x.extractLsb' (sourceBase p+(13+2*ReportByteRows.d p)) 6).isLt

private theorem acq_lane_cases (j : Fin 3) :
    j=0 ∨ j=1 ∨ j=2 := by
  by_cases A : j.val=0
  · exact .inl (Fin.ext A)
  · by_cases B : j.val=1
    · exact .inr (.inl (Fin.ext B))
    · exact .inr (.inr (Fin.ext (by have := j.isLt; change j.val=2; omega)))

-- CHECK: BitVec.extractLsb'_toNat, same normalization as :6922–6935.
theorem acq_six_index (p : Params) (x : BitVec p.w) :
    acqCaptureIndex p x=acqCaptureSix p x/8%8 := by
  unfold acqCaptureIndex acqCaptureSix
  simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  rw [show sourceBase p+(16+2*ReportByteRows.d p)=
    (sourceBase p+(13+2*ReportByteRows.d p))+3 by omega,Nat.pow_add,
    ←Nat.div_div_eq_div_mul]
  change x.toNat/2^(sourceBase p+(13+2*ReportByteRows.d p))/8%8=
    x.toNat/2^(sourceBase p+(13+2*ReportByteRows.d p))%64/8%8
  omega

theorem acq_six_header (p : Params) (x : BitVec p.w) :
    acqCaptureHeader p x=acqCaptureSix p x%8 := by
  unfold acqCaptureHeader acqCaptureSix
  simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  change x.toNat/2^(sourceBase p+(13+2*ReportByteRows.d p))%8=
    x.toNat/2^(sourceBase p+(13+2*ReportByteRows.d p))%64%8
  omega

theorem acq_pair_fields (p : Params) (x : BitVec p.w) (j : Fin 3) :
    acqPair (acqCaptureSix p x) j =
      (acqCaptureIndex p x/2^(2-j.val)%2,
       acqCaptureHeader p x/2^(2-j.val)%2) := by
  rw [acq_six_index,acq_six_header]
  rcases acq_lane_cases j with rfl|rfl|rfl <;>
    apply Prod.ext <;>
    simp only [acqPair,Fin.val_zero,Fin.val_one,
      show (2:Fin 3).val=2 by decide] <;> omega

theorem acq_pair_mod (q : Nat) (j : Fin 3) :
    acqPair (q%64) j=acqPair q j := by
  rcases acq_lane_cases j with rfl|rfl|rfl <;>
    apply Prod.ext <;>
    simp only [acqPair,Fin.val_zero,Fin.val_one,
      show (2:Fin 3).val=2 by decide] <;> omega

-- Small bit algebra, general in q (no whole-ring enumeration).
private theorem acq_seven_cases (i : Nat) (H : i<7) :
    i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega

private theorem acq_edit_same (q i : Nat) (b : Bool) (I : i<7) :
    writeBit q i b/2^i%2=b.toNat := by
  rcases acq_seven_cases i I with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    cases b <;> simp [writeBit,bit,Nat.shiftRight_eq_div_pow] <;>
    split <;> omega

private theorem acq_edit_other (q i j : Nat) (b : Bool)
    (I : i<7) (J : j<7) (D : i≠j) :
    writeBit q i b/2^j%2=q/2^j%2 := by
  rcases acq_seven_cases i I with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases acq_seven_cases j J with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    first | contradiction | (cases b <;> simp [writeBit,bit,Nat.shiftRight_eq_div_pow] <;> split <;> omega)

/-- Both bits at the real winning old header departure.
    The success condition rules out denial even at the final site. -/
theorem acqFlight_capture_pair (p : Params) (u : BitVec p.w)
    (j : Fin 3) (q : Nat) (Q : q<128)
    (S : acqFlightNext p true u j q/64=1) :
    acqFlightWin p true u j=true ∧
      acqPair (acqFlightNext p true u j q) j =
        (publicationSelector p u,(publicationA p u (publicationSelector p u)).toNat) := by
  have W : acqFlightWin p true u j=true := by
    cases E : acqFlightWin p true u j
    · have D := acqFlight_edit_denial q Q
      rw [acqFlightNext,if_pos rfl,if_neg (by simp [E])] at S
      omega
    · rfl
  refine ⟨W,?_⟩
  rw [acqFlightNext,if_pos rfl,if_pos W]
  let a := (publicationSelector p u==1)
  let b := publicationA p u (publicationSelector p u)
  let x := writeBit q (5-j.val) a
  have J := j.isLt
  have B : a.toNat=publicationSelector p u := by
    have L := ancestry_selector_lt p u
    rcases (show publicationSelector p u=0 ∨ publicationSelector p u=1 by omega) with E|E <;>
      simp [a,E]
  apply Prod.ext
  · change writeBit x (2-j.val) b/2^(5-j.val)%2=publicationSelector p u
    rw [acq_edit_other x (2-j.val) (5-j.val) b (by omega) (by omega) (by omega)]
    exact (acq_edit_same q (5-j.val) a (by omega)).trans B
  · change writeBit x (2-j.val) b/2^(2-j.val)%2=b.toNat
    exact acq_edit_same x (2-j.val) b (by omega)

/-- The other header lanes and all nonheaders frame this pair.
    A denial only clears bit 6 and hence also frames the pair. -/
theorem acqFlight_other_pair (p : Params) (hu : Bool) (u : BitVec p.w)
    (j i : Fin 3) (q : Nat) (D : ¬(hu=true ∧ j=i)) :
    acqPair (acqFlightNext p hu u j q) i=acqPair q i := by
  cases hu with
  | false => rfl
  | true =>
    have N : j.val≠i.val := fun H=>D ⟨rfl,Fin.ext H⟩
    have J := j.isLt
    have I := i.isLt
    cases W : acqFlightWin p true u j with
    | false =>
      rw [acqFlightNext,if_pos rfl,if_neg (by simp [W])]
      apply Prod.ext
      · exact acq_edit_other q 6 (5-i.val) false (by decide) (by omega) (by omega)
      · exact acq_edit_other q 6 (2-i.val) false (by decide) (by omega) (by omega)
    | true =>
      rw [acqFlightNext,if_pos rfl,if_pos W]
      let a := (publicationSelector p u==1)
      let b := publicationA p u (publicationSelector p u)
      let x := writeBit q (5-j.val) a
      apply Prod.ext
      · exact (acq_edit_other x (2-j.val) (5-i.val) b (by omega) (by omega) (by omega)).trans
          (acq_edit_other q (5-j.val) (5-i.val) a (by omega) (by omega) (by omega))
      · exact (acq_edit_other x (2-j.val) (2-i.val) b (by omega) (by omega) (by omega)).trans
          (acq_edit_other q (5-j.val) (2-i.val) a (by omega) (by omega) (by omega))

theorem acqFlight_reply_pair (p : Params) (q : Nat) (Q : q<128)
    (ND : (acqFlightD p q).outcome≠1) (j : Fin 3) :
    q/64=1 ∧ acqPair (acqFlightD p q).payload j=acqPair q j := by
  have S := (acqFlight_D_success p q Q ND).1
  refine ⟨S,?_⟩
  unfold acqFlightD
  rw [if_pos (by rw [S])]
  exact acq_pair_mod q j

-- CHECK: ReportByteRows.lean:6937,5790, the actual denial branch.
theorem acq_source_denied_pc (p : Params) (v : BitVec p.w) (t : Tok)
    (P : sourcePhase p v=2) (O : sourceOpcode p v=acqOp p)
    (Tag : t.tag=3) (Denied : t.outcome=1) :
    acqSourcePC p v t=(1,0) := by
  have U : ¬commitOp p<acqOp p := by unfold commitOp acqOp; omega
  have R : source p v t=(reset p,some MISByteCodec.E) := by
    unfold sourcePhase at P
    unfold sourceOpcode at O
    simp [source,P,O,Tag,Denied,U]
  change prePostPC p (source p v t).1 v=(1,0)
  rw [R]
  exact prelaunch_restart_controls p v

theorem acq_six_low_congr (p : Params) (x y : BitVec p.w)
    (H : ∀ i, i<grantBase p → x.getLsbD i=y.getLsbD i) :
    acqCaptureSix p x=acqCaptureSix p y := by
  unfold acqCaptureSix
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  apply H
  unfold grantBase sealBase sourceW
  omega

theorem acq_six_of_file (p : Params) (x y : BitVec p.w)
    (H : drainFile p x=drainFile p y) :
    acqCaptureSix p x=acqCaptureSix p y := by
  change (x.extractLsb' (sourceBase p) (19+2*ReportByteRows.d p)).toNat=
    (y.extractLsb' (sourceBase p) (19+2*ReportByteRows.d p)).toNat at H
  have E : x.extractLsb' (sourceBase p) (19+2*ReportByteRows.d p)=
      y.extractLsb' (sourceBase p) (19+2*ReportByteRows.d p) :=
    BitVec.eq_of_toNat_eq H
  unfold acqCaptureSix
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  have J : 13+2*ReportByteRows.d p+i<19+2*ReportByteRows.d p := by omega
  have B := congrArg (fun z : BitVec (19+2*ReportByteRows.d p) =>
    z.getLsbD (13+2*ReportByteRows.d p+i)) E
  have J' : 13+(2*ReportByteRows.d p+i)<19+2*ReportByteRows.d p := by omega
  simpa only [BitVec.getLsbD_extractLsb',I,J,J',decide_true,
    Bool.true_and,Nat.add_assoc] using B

private theorem acq_six_apply (p : Params) (a : Patch (workW p))
    (x : BitVec p.w) (A : acqCapFrame p a) :
    acqCaptureSix p ((widen p a).apply x)=acqCaptureSix p x := by
  unfold acqCaptureSix
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  exact pulse_widen_frame p a x _ (A _ (by omega) (by omega))

private theorem acq_six_write (p : Params) (x : BitVec p.w) (q : Nat) :
    acqCaptureSix p ((widen p (sf p (13+2*ReportByteRows.d p) 6 q)).apply x)=q%64 := by
  have W := dr_field_sub p x (sourceBase p+(13+2*ReportByteRows.d p)) 6 q 0 6
    (by unfold workW grantBase sealBase sourceW; omega) (by decide)
  have E : ((widen p (sf p (13+2*ReportByteRows.d p) 6 q)).apply x).extractLsb'
      (sourceBase p+(13+2*ReportByteRows.d p)) 6=(BitVec.ofNat 6 q).extractLsb' 0 6 := by
    simpa only [sf,Nat.add_zero] using W
  unfold acqCaptureSix
  rw [E]
  simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat]
  omega

theorem acq_row_success_six (p : Params) (hu : Bool) (u v : BitVec p.w)
    (P : sourcePhase p v=2) (O : sourceOpcode p v=acqOp p)
    (D : (publicationToken p true v 0).tag=3)
    (K : (publicationToken p true v 0).opcode=acqOp p)
    (F : (publicationToken p true v 0).fault=false)
    (U : (publicationToken p true v 0).outcome≠1) :
    acqCaptureSix p ((row p (hu,true) (u,v)).2.apply v)=
      (publicationToken p true v 0).payload%64 := by
  let t := oldK p true v 0
  have S := acq_source_success p v t P O D K F U
  rw [dr_row_eq]
  unfold reset0Post
  simp only [if_true,show oldK p true v 0=t from rfl,S]
  rw [reset0_widen_apply]
  rw [acq_six_apply p _ _ (acq_cap_src p _ (drSK p 0 MISByteCodec.E))]
  rw [reset0_widen_apply]
  rw [reset0_widen_apply]
  rw [acq_six_apply p _ _ (acq_cap_sf p (9+2*ReportByteRows.d p) 4 0 (by omega))]
  rw [reset0_widen_apply]
  exact acq_six_write p _ t.payload

theorem acq_row_left_six (p : Params) (hv : Bool) (u v : BitVec p.w) :
    acqCaptureSix p ((row p (true,hv) (u,v)).1.apply u)=
      acqCaptureSix p u :=
  acq_six_of_file p _ _ (drain_row_file_left p hv u v)

private theorem acq_row_six_of_source (p : Params) (hu : Bool)
    (u v : BitVec p.w)
    (B : acqCapFrame p (source p v (oldK p true v 0)).1) :
    acqCaptureSix p ((row p (hu,true) (u,v)).2.apply v)=
      acqCaptureSix p v := by
  have A := acq_cap_src p _ (drSright p hu u v)
  rw [dr_row_eq]
  unfold reset0Post
  simp only [if_true]
  cases R : source p v (oldK p true v 0) with
  | mk q opt =>
    rw [R] at B
    cases opt with
    | none =>
      dsimp only
      exact acq_six_apply p _ v
        (acq_cap_comp (acq_cap_comp A B) (acq_cap_empty p))
    | some t =>
      dsimp only
      exact acq_six_apply p _ v
        (acq_cap_comp (acq_cap_comp A B) (acq_cap_src p _ (drSK p 0 t)))

theorem acq_row_post_six (p : Params) (hu : Bool) (u v : BitVec p.w)
    (H : PostAcqPC p (sourcePhase p v,sourceOpcode p v))
    (NZ : (acqSourcePC p v (publicationToken p true v 0)).2≠0) :
    acqCaptureSix p ((row p (hu,true) (u,v)).2.apply v)=
      acqCaptureSix p v :=
  acq_row_six_of_source p hu u v
    (acq_source_nonreset_frame p v _ H (acq_nonreset_of_pc p v _ NZ))

end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem rank_fault2_hop (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (D : reset0Destination hv j=some k)
    (A : publicationToken p hu u j=MISByteCodec.faultToken 2) (g : Bool) :
    decode p g (resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k)=
      MISByteCodec.faultToken 2 := by
  have R : rankReady p hu u j=true := by
    rw [rankReady_iff,A]
    simp [MISByteCodec.faultToken,healthyAdmit]
  rw [rank_row_right p hu hv u v j k D]
  simp only [rankRouteR,R,if_true,Option.elim]
  change decode p g (resetTokenWire p (arrival p hv v k
    (effect p u v hu hv j (some k) (drWin p hu u j) (publicationToken p hu u j)).2.2))=_
  rw [A]
  simp only [effect,arrival,MISByteCodec.faultToken,Bool.true_eq,if_true,Bool.not_true,
    Bool.false_and,Bool.false_eq_true,if_false]
  exact rFault_roundtrip p g 2 (.inl rfl)

/-- For a forward WRITE (or its canonical fault), right normalization is
semantically inert; an ADMIT race is the only nonfault exception. -/
theorem rank_nondadmit_norm_token (p : Params) (side : Nat) (g : Bool)
    (w : BitVec (tokenW p)) (S : side=2 ∨ side=3)
    (A : (decode p g w).opcode≠admitOp p ∨ (decode p g w).fault=true) :
    decode p g (rankNormWire p side g w)=decode p g w := by
  let t := decode p g w
  rcases A with A|A
  · cases F0 : t.fault
    · unfold rankNormWire rankNormIntent
      change decode p g ((if t.fault then some t else if
        t.tag==2 && t.opcode==admitOp p && g &&
          (t.race==1 || t.race==(if side=3 then 2 else 3))
        then some (advanceRace t side) else none).elim w (resetTokenWire p))=t
      change t.opcode≠admitOp p at A
      simp [F0,A]
      rfl
    · rcases rank_norm_cases p g w side S with E|E
      · exact E
      · have L : t.fault=false := E.2.2.1
        rw [F0] at L
        contradiction
  · rcases rank_norm_cases p g w side S with E|E
    · exact E
    · have L : t.fault=false := E.2.2.1
      change t.fault=true at A
      rw [A] at L
      contradiction

theorem rank_root_norm_token (p : Params) (v : BitVec p.w) :
    decode p false (prelaunchDoorNormWire p v)=publicationToken p true v 0 := by
  rw [prelaunch_root_decode]
  let t := oldK p true v 0
  change decode p false (prelaunchDoorNormWire p v)=t
  unfold prelaunchDoorNormWire
  dsimp only
  by_cases H : t.fault=true
  · rw [if_pos H]
    have E : t=decode p false (resetTokenRead p v 0) := prelaunch_root_decode p v
    obtain ⟨F0,T⟩ := rDecoded_fault p false (resetTokenRead p v 0) (E ▸ H)
    rw [←E] at F0 T
    change decode p false (resetTokenWire p t)=t
    rw [F0]
    exact (rFault_roundtrip p false t.tag T)
  · rw [if_neg H]
    have K : parked p t true v 0=false := by simp [parked,gate]
    rw [K]
    simp only [Bool.false_and,Bool.false_eq_true,if_false]
    exact (prelaunch_root_decode p v).symm

private theorem rWrite_issue_fields (p : Params) (raw : BitVec p.w) (old t : Tok)
    (P : sourcePhase p raw=1) (W : writeOp p≤sourceOpcode p raw)
    (U : sourceOpcode p raw<sealOp p)
    (S : (source p raw old).2=some t) (T0 : t.tag=2) :
    t=({tag:=2,opcode:=sourceOpcode p raw,payload:=ancestryWritePayload p (ancestrySourceCentre p raw) (ancestrySendDigits p raw)} : Tok) ∧
    digitPair p (ancestrySendDigits p raw)=true := by
  have A : sourceOpcode p raw≠acqOp p := by unfold writeOp acqOp at *; omega
  have Q : ¬commitOp p<sourceOpcode p raw := by unfold commitOp sealOp at *; omega
  have L : ¬sealOp p≤sourceOpcode p raw := by omega
  have N : ¬sourceOpcode p raw<writeOp p := by omega
  unfold sourcePhase at P
  unfold sourceOpcode at A Q L N W U
  simp only [source,P,Q,decide_false,show ((1:Nat)==0)=false by decide,
    show ((1:Nat)==3)=false by decide,Bool.false_or,Bool.false_eq_true,
    if_false,beq_self_eq_true,if_true,N,W,U,L,decide_true,Bool.and_true,Bool.true_and,
    beq_false_of_ne A,Bool.and_false] at S
  cases HD : digitPair p (ancestrySendDigits p raw)
  · change digitPair p (rf p raw 3 (2*d p))=false at HD
    simp [HD] at S
    subst t
    contradiction
  · change digitPair p (rf p raw 3 (2*d p))=true at HD
    simp [HD] at S
    exact ⟨S.symm,rfl⟩

/-- A literal source-issued WRITE, not just any token fit in the padded
codec, survives reencoding exactly at every possible destination gate. -/
theorem rank_write_issue_roundtrip (p : Params) (v : BitVec p.w) (old t : Tok)
    (P : sourcePhase p v=1) (W : writeOp p≤sourceOpcode p v)
    (U : sourceOpcode p v<sealOp p) (S : (source p v old).2=some t)
    (T0 : t.tag=2) (g : Bool) :
    decode p g (resetTokenWire p t)=t := by
  obtain ⟨Eq,Dig⟩ := rWrite_issue_fields p v old t P W U S T0
  let c := ancestrySourceCentre p v
  let q := ancestrySendDigits p v
  let b := 2*c+(1-c)
  let z := ancestryWritePayload p c q
  have cb : c<2 := ancestry_source_centre_lt p v
  have qb : q<2^(2*d p) := ancestry_send_digits_lt p v
  have bp : b<4 := by omega
  have zd : z/2^(2*d p)=b := by
    unfold z ancestryWritePayload
    rw [Nat.mul_comm (2*c+(1-c)),Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt qb,Nat.add_zero]
  have zm : z%2^(2*d p)=q := by
    unfold z ancestryWritePayload
    rw [Nat.mul_comm (2*c+(1-c)),Nat.add_comm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt qb]
  have zp : z<2^(2+2*d p) := by
    have K := Nat.mod_add_div z (2^(2*d p))
    rw [zm,zd] at K
    rw [Nat.pow_add]
    have M := Nat.mul_le_mul_left (2^(2*d p)) (show b+1≤4 by omega)
    rw [Nat.mul_succ] at M
    rw [Nat.mul_comm 4]
    omega
  have Z0 : bit z (2*d p)≠bit z (2*d p+1) := by
    unfold bit
    simp only [Nat.shiftRight_eq_div_pow]
    rw [Nat.pow_succ,←Nat.div_div_eq_div_mul,zd]
    change ((b%2==1) ≠ ((b/2)%2==1))
    have C : c=0 ∨ c=1 := by omega
    rcases C with C|C <;> simp [b,C]
  have DP : digitPair p z=true := by
    have J : 2^(2*d p)=2^d p*2^d p := by rw [show 2*d p=d p+d p by omega,Nat.pow_add]
    rw [J] at zm
    have A0 : z%2^d p=q%2^d p := by
      rw [←zm, Nat.mod_mul_right_mod]
    have A1 : z/2^d p%2^d p=q/2^d p%2^d p := by
      rw [←Nat.mod_mul_right_div_self,zm]
      symm
      apply Nat.mod_eq_of_lt
      exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by rwa [←J])
    unfold digitPair at Dig ⊢
    rw [A0,A1]
    exact Dig
  have O : sourceOpcode p v≤commitOp p := by unfold sealOp commitOp at *; omega
  have Fit : RankFits p t := by
    rcases source_issue_fits p v old P O with E|⟨a,E,_,R⟩
    · rw [S] at E
      have A:=Option.some.inj E
      rw [A] at T0
      contradiction
    · rw [S] at E
      rwa [←Option.some.inj E] at R
  let op := sourceOpcode p v
  have C : cmpOp p≤op := by unfold cmpOp writeOp at *; exact Nat.le_trans (by omega) W
  have AC : op≠acqOp p := by unfold acqOp writeOp op at *; omega
  have AD : op≠admitOp p := by unfold admitOp writeOp op at *; omega
  have CM : op≠commitOp p := by unfold commitOp sealOp op at *; omega
  have B := rReadFields p t Fit
  have FV : (resetTokenWire p t).getLsbD (6+o p+payW p)=false := by
    rw [rGet_bit,B.2.1,Eq]
    rfl
  simp only [decode,B.1,B.2.2.1,B.2.2.2.1,B.2.2.2.2.1,B.2.2.2.2.2.2,FV]
  rw [Eq]
  have LO : writeOp p≤op := W
  have HI : op<sealOp p := U
  have SN : ¬sealOp p≤op := by omega
  have OK : ¬commitOp p<op := Nat.not_lt_of_ge O
  have ZE : ancestryWritePayload p (ancestrySourceCentre p v) (ancestrySendDigits p v)=z := rfl
  simp [show sourceOpcode p v=op from rfl,ZE,C,AC,AD,CM,OK,LO,HI,SN,DP,Z0,Nat.mod_eq_of_lt zp]

end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000

def fileAfterSource (p : Params) (x : BitVec p.w) (t : Tok) : Nat :=
  drainFile p ((liftSourcePatch p (source p x t).1).apply x)

theorem indexed_file_bound (p : Params) (x : BitVec p.w) :
    drainFile p x<2^(19+2*d p) :=
  (x.extractLsb' (sourceBase p) (19+2*d p)).isLt

private theorem indexed_file_bit (p : Params) (x y : BitVec p.w)
    (E : drainFile p x=drainFile p y) (i : Nat) (I : i<19+2*d p) :
    x.getLsbD (sourceBase p+i)=y.getLsbD (sourceBase p+i) := by
  have A : x.extractLsb' (sourceBase p) (19+2*d p)=
      y.extractLsb' (sourceBase p) (19+2*d p) := BitVec.eq_of_toNat_eq E
  have B := congrArg (fun v : BitVec (19+2*d p)=>v.getLsbD i) A
  simpa only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and] using B

private theorem indexed_rf_congr (p : Params) (x y : BitVec p.w)
    (E : drainFile p x=drainFile p y) (k b : Nat) (K : k+b≤19+2*d p) :
    rf p x k b=rf p y k b := by
  unfold rf get
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and,Nat.add_assoc]
  exact indexed_file_bit p x y E (k+i) (by omega)

/-- The entire source action depends only on the old data file,
    old phase/opcode and supplied decoded old reply. -/
theorem indexed_source_congr (p : Params) (x y : BitVec p.w) (t : Tok)
    (E : drainFile p x=drainFile p y)
    (P : sourcePhase p x=sourcePhase p y)
    (O : sourceOpcode p x=sourceOpcode p y) :
    source p x t=source p y t := by
  have I := indexed_rf_congr p x y E (16+2*d p) 3 (by omega)
  have A := indexed_rf_congr p x y E (13+2*d p) 3 (by omega)
  have B := indexed_rf_congr p x y E (5+2*d p) 4 (by omega)
  have C := indexed_rf_congr p x y E (9+2*d p) 4 (by omega)
  have D := indexed_rf_congr p x y E (3+2*d p) 2 (by omega)
  have V := indexed_rf_congr p x y E 3 (2*d p) (by omega)
  unfold sourcePhase at P
  unfold sourceOpcode at O
  unfold source
  dsimp only
  rw [P,O,I,A,B,C,D,V]

/-- Applying the same work patch to equal data-file slices gives
    equal resulting slices, even if all other raw bits differ. -/
private theorem indexed_patch_file_congr (p : Params) (a : Patch (workW p))
    (x y : BitVec p.w) (E : drainFile p x=drainFile p y) :
    drainFile p ((widen p a).apply x)=drainFile p ((widen p a).apply y) := by
  unfold drainFile get
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  by_cases W : (widen p a).mask.getLsbD (sourceBase p+i)=true
  · rw [Patch.write _ _ _ W,Patch.write _ _ _ W]
  · have H : (widen p a).mask.getLsbD (sourceBase p+i)=false :=
      Bool.eq_false_iff.mpr W
    rw [Patch.hold _ _ _ H,Patch.hold _ _ _ H]
    exact indexed_file_bit p x y E i I

theorem indexed_file_after_congr (p : Params) (x y : BitVec p.w) (t : Tok)
    (E : drainFile p x=drainFile p y)
    (P : sourcePhase p x=sourcePhase p y)
    (O : sourceOpcode p x=sourceOpcode p y) :
    fileAfterSource p x t=fileAfterSource p y t := by
  unfold fileAfterSource liftSourcePatch
  rw [indexed_source_congr p x y t E P O]
  exact indexed_patch_file_congr p _ x y E

/-- Source data file after the full right joined row. This is valid
    even on a bad reply or an actual restart; all pre-source portions
    frame the source and the final K0 write is disjoint. -/
theorem indexed_row_source_file (p : Params) (hu : Bool) (u v : BitVec p.w) :
    drainFile p ((row p (hu,true) (u,v)).2.apply v)=
      fileAfterSource p v (publicationToken p true v 0) := by
  let t := oldK p true v 0
  have Base := dr_file_frame p _ v (drSright p hu u v)
  unfold fileAfterSource liftSourcePatch
  change _=drainFile p ((widen p (source p v t).1).apply v)
  rw [dr_row_eq]
  unfold reset0Post
  simp only [if_true,show oldK p true v 0=t from rfl]
  cases R : source p v t with
  | mk q opt =>
    cases opt with
    | none =>
      dsimp only
      rw [reset0_widen_apply,dr_file_frame p _ _ (drSempty p),
        reset0_widen_apply]
      exact indexed_patch_file_congr p q _ _ Base
    | some a =>
      dsimp only
      rw [reset0_widen_apply,dr_file_frame p _ _ (drSK p 0 a),
        reset0_widen_apply]
      exact indexed_patch_file_congr p q _ _ Base

/-- A replay image, computed without a raw physical snapshot.
    The only control it needs is the WAIT opcode of this ACK. -/
def indexedImage (p : Params) (f op : Nat) : BitVec p.w :=
  (widen p (ctrl p 2 op)).apply
    ((widen p (sf p 0 (19+2*d p) f)).apply (0 : BitVec p.w))

-- CHECK: ReportByteRows.lean:3850–3870,5709–5730. This is the
-- phase-two version of the checked prelaunch_ctrl_write.
theorem indexed_image_fields (p : Params) (f op : Nat)
    (F : f<2^(19+2*d p)) (O : op≤commitOp p) :
    drainFile p (indexedImage p f op)=f ∧
      sourcePhase p (indexedImage p f op)=2 ∧
      sourceOpcode p (indexedImage p f op)=op := by
  let x := (widen p (sf p 0 (19+2*d p) f)).apply (0 : BitVec p.w)
  have A : drainFile p x=f := by
    have K := dr_field_get p (0 : BitVec p.w) (sourceBase p)
      (19+2*d p) f 0 (19+2*d p)
      (by unfold workW grantBase sealBase sourceW; omega) (by omega) F
    simpa [x,sf,drainFile,Nat.mod_eq_of_lt F] using K
  have B : op<2^o p := by
    have L := power_of_ell (5+4*p.digits)
    change 5+4*p.digits≤2^o p at L
    unfold commitOp at O
    omega
  have V : 2*2^o p+op<2^(o p+2) := by
    rw [Nat.pow_add]
    omega
  have K : pc p+(o p+2)≤workW p := by
    unfold pc workW grantBase sealBase sourceW
    omega
  have H := dr_field_get p x (pc p) (o p+2) (2*2^o p+op)
    (o p) 2 K (by omega) V
  have J := dr_field_get p x (pc p) (o p+2) (2*2^o p+op)
    0 (o p) K (by omega) V
  have Div : (2*2^o p+op)/2^o p=2 := by
    rw [Nat.add_comm,Nat.mul_comm 2,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt B]
  have Mod : (2*2^o p+op)%2^o p=op := by
    rw [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_mod,
      Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt B]
  refine ⟨(dr_file_late p x _ _ _ (Nat.le_refl _)).trans A,?_,?_⟩
  · simpa [indexedImage,x,ctrl,sourcePhase,Div] using H
  · simpa [indexedImage,x,ctrl,sourceOpcode,Mod] using J

def replayAck (p : Params) (f op : Nat) (t : Tok) : Nat :=
  fileAfterSource p (indexedImage p f op) t

theorem replayAck_bound (p : Params) (f op : Nat) (t : Tok) :
    replayAck p f op t<2^(19+2*d p) :=
  indexed_file_bound p _

theorem source_file_is_replay (p : Params) (v : BitVec p.w) (t : Tok)
    (P : sourcePhase p v=2) (O : sourceOpcode p v≤commitOp p) :
    fileAfterSource p v t=replayAck p (drainFile p v) (sourceOpcode p v) t := by
  have E := indexed_image_fields p (drainFile p v) (sourceOpcode p v)
    (indexed_file_bound p v) O
  exact indexed_file_after_congr p v _ t E.1.symm (P.trans E.2.1.symm) E.2.2.symm

/-- A real positive ISSUE launch cannot credit a command and cannot
    change the file. The failed-issue branch is excluded by actual
    post-PC, not by a supposition about digit validity. -/
theorem indexed_issue_file (p : Params) (v : BitVec p.w) (t : Tok)
    (P : sourcePhase p v=1) (O : sourceOpcode p v≤commitOp p)
    (Pos : 0<sourceOpcode p v)
    (NZ : (acqSourcePC p v t).2≠0) :
    acqSourcePC p v t=(2,sourceOpcode p v) ∧
    fileAfterSource p v t=drainFile p v := by
  have N : (source p v t).1≠reset p :=
    acq_nonreset_of_pc p v t NZ
  refine ⟨?_,?_⟩
  · rcases prelaunch_positive_issue_controls p v t P O Pos with R|R
    · exact (NZ (congrArg Prod.snd R)).elim
    · exact R
  · rcases prelaunch_issue_action p v t P O with R|⟨q,R⟩
    · exact (N (congrArg Prod.fst R)).elim
    · unfold fileAfterSource liftSourcePatch
      rw [R]
      dsimp only
      rw [if_neg (Nat.ne_of_gt Pos),reset0_widen_apply,
        dr_file_late p _ _ _ _ (by omega)]
      exact dr_file_frame p _ _ (drSempty p)

theorem indexed_wait_file (p : Params) (v : BitVec p.w) (t : Tok)
    (P : sourcePhase p v=2) (O : sourceOpcode p v≤commitOp p)
    (T : t.tag=1 ∨ t.tag=2) :
    acqSourcePC p v t=(sourcePhase p v,sourceOpcode p v) ∧
    fileAfterSource p v t=drainFile p v := by
  refine ⟨prelaunch_hold_controls p v t P O T,?_⟩
  unfold fileAfterSource liftSourcePatch
  rw [prelaunch_wait_hold p v t P O T]
  exact dr_file_frame p _ _ (drSempty p)

theorem indexed_credit (p : Params) (v : BitVec p.w) (t : Tok)
    (P : sourcePhase p v=2) (O : sourceOpcode p v≤commitOp p)
    (T : t.tag=3) (NZ : (acqSourcePC p v t).2≠0)
    (D : 0<p.digits) :
    t.opcode=sourceOpcode p v ∧ t.fault=false ∧ t.outcome≠1 ∧
    ∃ b, PreviewNextOp p.digits (sourceOpcode p v) b ∧
      acqSourcePC p v t=(1,b) := by
  have N : (source p v t).1≠reset p := acq_nonreset_of_pc p v t NZ
  have Bad (B : t.tag≠3 ∨ t.opcode≠sourceOpcode p v ∨
      t.fault=true ∨ t.outcome=1) : False :=
    N (congrArg Prod.fst (prelaunch_wait_bad_reply p v t P O
      (by rw [T]; decide) (by rw [T]; decide) B))
  have Op : t.opcode=sourceOpcode p v :=
    Classical.byContradiction (fun E=>Bad (.inr (.inl E)))
  have Live : t.fault=false := Bool.eq_false_iff.mpr
    (fun E=>Bad (.inr (.inr (.inl E))))
  have Ok : t.outcome≠1 := fun E=>Bad (.inr (.inr (.inr E)))
  refine ⟨Op,Live,Ok,?_⟩
  rcases prelaunch_wait_controls p v t P O (by rw [T]; decide)
      (by rw [T]; decide) D with R|⟨b,E,R⟩
  · exact (NZ (congrArg Prod.snd R)).elim
  · exact ⟨b,E,R⟩

end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol

def indexedReadPack (p : Params) (ix a b : Nat) : Nat :=
  rPack (d p) b (rPack (d p) a ix)

theorem indexed_read_left_half (p : Params) (ix a b : Nat)
    (A : a<2^d p) (B : b<2^d p) :
    indexedReadPack p ix a b/2^d p%2^d p=a := by
  unfold indexedReadPack
  rw [rPack_div B,rPack_mod A]

theorem indexed_read_right_half (p : Params) (ix a b : Nat)
    (B : b<2^d p) :
    indexedReadPack p ix a b%2^d p=b :=
  rPack_mod B

theorem indexed_read_pair_indices (p : Params) (ix a b : Nat)
    (A : a<2^d p) (B : b<2^d p) :
    indexedReadPack p ix a b/2^(2*d p)=ix := by
  unfold indexedReadPack
  rw [show 2*d p=d p+d p by omega,Nat.pow_add,←Nat.div_div_eq_div_mul,
    rPack_div B,rPack_div A]

theorem indexed_read_edit_left (p : Params) (ix a b v : Nat)
    (A : a<2^d p) (B : b<2^d p) :
    let q := indexedReadPack p ix a b
    q-(q/2^d p%2^d p)*2^d p+v*2^d p=indexedReadPack p ix v b := by
  dsimp only
  rw [indexed_read_left_half p ix a b A B]
  unfold indexedReadPack rPack
  simp only [Nat.mul_add]
  rw [Nat.mul_comm a (2^d p),Nat.mul_comm v (2^d p)]
  omega

theorem indexed_read_edit_right (p : Params) (ix a b v : Nat)
    (B : b<2^d p) :
    let q := indexedReadPack p ix a b
    q-q%2^d p+v=indexedReadPack p ix a v := by
  dsimp only
  rw [indexed_read_right_half p ix a b B]
  unfold indexedReadPack rPack
  omega

theorem indexed_read_return_payload (p : Params) (ix a b : Nat)
    (A : a<2^d p) (B : b<2^d p) :
    indexedReadPack p ix a b%2^(2*d p)=rPack (d p) b a := by
  have H : rPack (d p) b a<2^(d p+d p) :=
    rPack_lt B A
  unfold indexedReadPack rPack
  rw [show 2*d p=d p+d p by omega,Nat.pow_add]
  rw [Nat.mul_add,←Nat.add_assoc]
  change (b+2^d p*a+2^d p*(2^d p*ix))%(2^d p*2^d p)=b+2^d p*a
  rw [←Nat.mul_assoc,Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  simpa only [Nat.pow_add,rPack] using H

/-- Non-hit read departure has no payload change. The matching
    hit is handled by reader_digit_old and the two edit lemmas. -/
theorem indexed_reader_nonhit (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (port : Fin 3) (k : Option (Fin 3))
    (win : Bool) (t : Tok) (j : Fin p.digits)
    (Live : t.fault=false)
    (Op : t.opcode=cmpOp p+j.val ∨ t.opcode=readOp p+j.val)
    (NH : ¬((port=0 ∨ port=2) ∧ reportOldOffset p hu u=j.val)) :
    effect p u v hu hv port k win t=(.empty _,.empty _,t) := by
  have J := j.isLt
  have R : cmpOp p≤t.opcode ∧ t.opcode<writeOp p := by
    unfold cmpOp readOp writeOp at *; omega
  have C : t.opcode≠commitOp p := by unfold writeOp commitOp at *; omega
  have A : t.opcode≠admitOp p := by unfold cmpOp admitOp at *; omega
  have K : t.opcode≠acqOp p := by unfold cmpOp acqOp at *; omega
  have Z : t.opcode≠0 := by unfold cmpOp at R; omega
  have S : t.opcode≠sealOp p := by unfold writeOp sealOp at *; omega
  have Offset : t.opcode-(if t.opcode<readOp p then cmpOp p else readOp p)=j.val := by
    rcases Op with E|E
    · rw [if_pos (by unfold cmpOp readOp at *; omega)]
      omega
    · rw [if_neg (by omega)]
      omega
  have N : ¬((port=0 ∨ port=2) ∧ geomOff p hu u=j.val) := NH
  have NW : ¬writeOp p≤t.opcode := by omega
  simp [effect,parked,Live,C,A,K,Z,S,R.1,R.2,N,Offset,NW]

theorem indexed_reader_norm (p : Params) (side : Nat) (hu : Bool)
    (u : BitVec p.w) (j : Fin 3)
    (H : (publicationToken p hu u j).fault=false)
    (O : (publicationToken p hu u j).opcode≠admitOp p) :
    rankNormWire p side (rankGate p hu u j) (resetTokenRead p u j)=resetTokenRead p u j := by
  rw [rankToken_wire] at H O
  simp [rankNormWire,rankNormIntent,H,O]

end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxRecDepth 12000
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

def SealCommitForward (p : Params) (t : Tok) : Prop :=
  t.tag=2 ∧ (t.opcode=sealOp p ∨ t.opcode=commitOp p) ∧
    t.payload<16 ∧ legalDesc t.payload=true ∧ t.race=0 ∧ t.outcome=0 ∧
    t.fault=false ∧ (t.opcode=sealOp p → t.applied=false)

private theorem rSealCommit_admit_ne (p : Params) {t : Tok}
    (A : t.opcode=sealOp p ∨ t.opcode=commitOp p) : t.opcode≠admitOp p := by
  unfold sealOp commitOp admitOp at *
  omega

private theorem rSealCommit_bounds (p : Params) {t : Tok}
    (A : t.opcode=sealOp p ∨ t.opcode=commitOp p) :
    ¬commitOp p<t.opcode ∧ ¬t.opcode<sealOp p ∧ ¬t.opcode<writeOp p ∧
      t.opcode≠acqOp p ∧ t.opcode≠0 := by
  unfold sealOp commitOp writeOp acqOp at *
  omega

theorem seal_commit_decoded_shape (p : Params) (g : Bool)
    (w : BitVec (tokenW p)) (T0 : (decode p g w).tag=2) (FT : (decode p g w).fault=false)
    (O : (decode p g w).opcode=sealOp p ∨ (decode p g w).opcode=commitOp p) :
    SealCommitForward p (decode p g w) := by
  have T := (rank_decode_tag p g w).symm.trans T0
  have Q := rHealthy_forward_op p g w T0 FT
  let t := decode p g w
  have ⟨C,B,_,X,_⟩ := rSealCommit_bounds p (t:=t) O
  have N := rSealCommit_admit_ne p (t:=t) O
  have Q' : t.opcode= get w (payW p+6) (o p) := Q
  rw [Q'] at C B X N
  have NotEarly := Nat.le_of_not_gt B
  let q := get w 0 (payW p) % 16
  have qb : q<16 := Nat.mod_lt _ (by decide)
  revert FT O
  unfold decode
  simp [T,C,B,X,N,NotEarly]
  intro FT O
  by_cases f : w.getLsbD (6+o p+payW p)=true
  · simp only [if_pos f] at FT
    contradiction
  simp only [if_neg f] at FT O ⊢
  split
  · rename_i bad
    simp [bad,MISByteCodec.faultToken] at FT
  · rename_i good
    simp only [if_neg good] at FT O
    have race : get w (payW p+3) 3=0 := by
      have K : ¬(get w (payW p+1) 2≠0 ∨ get w (payW p+3) 3≠0) := good
      omega
    split
    · rename_i bad
      simp [bad,MISByteCodec.faultToken] at FT
    · rename_i valid
      simp only [if_neg valid] at FT O
      have desc : legalDesc q=true := by
        change ¬legalDesc q=false at valid
        cases H : legalDesc q <;> simp_all
      refine ⟨rfl,O,qb,desc,race,rfl,rfl,?_⟩
      intro E
      have NC : sealOp p≠commitOp p := by unfold sealOp commitOp; omega
      change get w (payW p+6) (o p)=sealOp p at E
      simp [E,NC]

theorem seal_commit_wire_roundtrip (p : Params) (t : Tok)
    (A : SealCommitForward p t) (H : RankFits p t) (g : Bool) :
    decode p g (resetTokenWire p t)=t := by
  obtain ⟨tag,op,pay,desc,race,out,fault,appl⟩ := A
  have ⟨B,C,D,X,Z⟩ := rSealCommit_bounds p op
  have N := rSealCommit_admit_ne p op
  have Fd := rReadFields p t H
  have Fbit : (resetTokenWire p t).getLsbD (6+o p+payW p)=false := by
    rw [rGet_bit,Fd.2.1,fault]
    rfl
  have Abit : (resetTokenWire p t).getLsbD (payW p)=t.applied := by
    rw [rGet_bit,Fd.2.2.2.2.2.1]
    cases t.applied <;> rfl
  simp only [decode,Fd.1,Fd.2.2.1,Fd.2.2.2.1,Fd.2.2.2.2.1,Fd.2.2.2.2.2.2,Fbit,Abit]
  have Pay : t.payload % 2^4 = t.payload := Nat.mod_eq_of_lt pay
  rcases op with O|O
  · have S := appl O
    have NC : sealOp p≠commitOp p := by unfold sealOp commitOp; omega
    rw [O] at B C D X N
    simp [tag,race,out,X,N,B,C,D,desc,Pay,Nat.mod_eq_of_lt pay,
      Nat.le_of_not_gt C,O,NC,S]
    cases t
    simp_all
  · rw [O] at B C D X N
    simp [tag,race,out,X,N,B,C,D,desc,Pay,Nat.mod_eq_of_lt pay,
      Nat.le_of_not_gt C,O]
    cases t
    simp_all

theorem seal_commit_held_wire (p : Params) (side : Nat) (g : Bool)
    (w : BitVec (tokenW p)) (H : SealCommitForward p (decode p g w)) :
    rankNormWire p side g w=w := by
  have N := rSealCommit_admit_ne p H.2.1
  simp [rankNormWire,rankNormIntent,H.2.2.2.2.2.2.1,N]

/-- Exact forward SEAL payload: only the held centre grant and old
selected bank decide success; a successful hop does not edit any token bit. -/
theorem seal_effect_token (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) (t : Tok)
    (OP : t.opcode=sealOp p) (FT : t.fault=false) :
    (effect p u v hu hv j k win t).2.2 =
      if hu=true ∧ j=1 ∧ ¬(reportOldGrant p u 1=true ∧ publicationSelector p u=t.payload/8)
      then MISByteCodec.faultToken 2 else t := by
  have ⟨B,C,D,X,Z⟩ := rSealCommit_bounds p (.inl OP)
  have N := rSealCommit_admit_ne p (.inl OP)
  have NC : sealOp p≠commitOp p := by unfold sealOp commitOp; omega
  rw [OP] at B C D X N Z
  by_cases J : j=1 <;> cases hu <;>
    simp [effect,FT,OP,NC,parked,N,X,Z,C,D,reportOldGrant,publicationSelector,J]
  split <;> simp_all

/-- Exact forward COMMIT payload: only the actual incoming 0→1
crossing may set applied. A failed crossing emits the canonical fault. -/
theorem commit_effect_token (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (win : Bool) (t : Tok)
    (OP : t.opcode=commitOp p) (FT : t.fault=false) :
    (effect p u v hu hv j (some k) win t).2.2 =
      if hv=true ∧ j=0 ∧ k=1 then
        if packetCommitGuard p v t then {t with applied:=true} else MISByteCodec.faultToken 2
      else t := by
  have ⟨B,C,D,X,Z⟩ := rSealCommit_bounds p (.inr OP)
  have N := rSealCommit_admit_ne p (.inr OP)
  have NC : commitOp p≠sealOp p := by unfold sealOp commitOp; omega
  by_cases Q : hv=true ∧ j=0 ∧ k=1
  · obtain ⟨rfl,rfl,rfl⟩ := Q
    rw [if_pos ⟨rfl,rfl,rfl⟩,commit_effect_snapshot p hu win u v t OP FT]
    split <;> rfl
  · rw [if_neg Q]
    have L : ¬(hv=true ∧ j=0) ∨ k≠1 := by
      by_cases B : hv=true ∧ j=0
      · exact .inr fun K=>Q ⟨B.1,B.2,K⟩
      · exact .inl B
    rw [OP] at B C D X N Z
    rcases L with L|L <;> simp [effect,FT,OP,parked,N,X,Z,C,D,NC,L]

private theorem seal_commit_ready (p : Params) (hu : Bool) (u : BitVec p.w)
    (j : Fin 3) (H : SealCommitForward p (publicationToken p hu u j)) :
    rankReady p hu u j=true := by
  exact (rankReady_iff p hu u j).mpr ⟨H.1,fun O=>rSealCommit_admit_ne p H.2.1 O.1.2.2⟩

private theorem seal_commit_effect_shape (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (win : Bool) (t : Tok) (H : SealCommitForward p t) :
    let z := (effect p u v hu hv j (some k) win t).2.2
    SealCommitForward p z ∨ z=MISByteCodec.faultToken 2 := by
  dsimp only
  rcases H.2.1 with O|O
  · rw [seal_effect_token p hu hv u v j _ win t O H.2.2.2.2.2.2.1]
    split
    · exact .inr rfl
    · exact .inl H
  · rw [commit_effect_token p hu hv u v j k win t O H.2.2.2.2.2.2.1]
    split
    · split
      · left
        have NE : commitOp p≠sealOp p := by unfold commitOp sealOp; omega
        exact ⟨H.1,H.2.1,H.2.2.1,H.2.2.2.1,H.2.2.2.2.1,H.2.2.2.2.2.1,
          H.2.2.2.2.2.2.1,fun M=>False.elim (NE (O.symm.trans M))⟩
      · exact .inr rfl
    · exact .inl H

theorem seal_commit_hop_pair (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (D : reset0Destination hv j=some k)
    (H : SealCommitForward p (publicationToken p hu u j)) (g : Bool) :
    let z := (effect p u v hu hv j (some k) (drWin p hu u j) (publicationToken p hu u j)).2.2
    resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j=resetTokenWire p MISByteCodec.T ∧
    resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k=resetTokenWire p z ∧
    decode p g (resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k)=z := by
  dsimp only
  let t := publicationToken p hu u j
  let z := (effect p u v hu hv j (some k) (drWin p hu u j) t).2.2
  have RD := seal_commit_ready p hu u j H
  have S := seal_commit_effect_shape p hu hv u v j k (drWin p hu u j) t H
  have Fit : RankFits p t := rank_decoded_fits p (rankGate p hu u j) (resetTokenRead p u j)
  have F := (rHop_effect p hu hv u v j k (drWin p hu u j) t Fit H.1).2
  have ARR : arrival p hv v k z=z := by
    rcases S with S|S
    · change SealCommitForward p z at S
      simp [arrival,rSealCommit_admit_ne p S.2.1]
    · change z=MISByteCodec.faultToken 2 at S
      simp [arrival,S,MISByteCodec.faultToken]
  have RR : resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k=resetTokenWire p z := by
    rw [rank_row_right p hu hv u v j k D]
    simp only [rankRouteR,RD,if_true,Option.elim]
    exact congrArg (resetTokenWire p) ARR
  refine ⟨rank_hop_left p hu hv u v j k D RD,RR,?_⟩
  rw [RR]
  rcases S with S|S
  · exact seal_commit_wire_roundtrip p z S F g
  · change z=MISByteCodec.faultToken 2 at S
    change decode p g (resetTokenWire p z)=z
    rw [S]
    exact rFault_roundtrip p g 2 (.inl rfl)

theorem seal_commit_held_left_row (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (R : rankRouteL p hu hv u v j (reset0Destination hv j)=none)
    (A : SealCommitForward p (publicationToken p hu u j)) :
    resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j=resetTokenRead p u j := by
  rw [rank_row_left,R]
  exact seal_commit_held_wire p 3 _ _ A

theorem seal_commit_held_right_row (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (D : reset0Destination hv j=some k)
    (R : rankRouteR p hu hv u v j k=none)
    (A : SealCommitForward p (publicationToken p hv v k)) :
    resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k=resetTokenRead p v k := by
  rw [rank_row_right p hu hv u v j k D,R]
  exact seal_commit_held_wire p 2 _ _ A

theorem commit_terminal_pair (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (D : reset0Destination hv j=none)
    (H : SealCommitForward p (publicationToken p hu u j))
    (O : (publicationToken p hu u j).opcode=commitOp p) :
    let t := publicationToken p hu u j
    resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j =
      resetTokenWire p (if t.applied then {tag:=3,opcode:=commitOp p} else MISByteCodec.faultToken 3) := by
  dsimp only
  have R := seal_commit_ready p hu u j H
  obtain ⟨HV,J⟩ := rTerminal_dest hv j D
  subst hv
  subst j
  let t := publicationToken p hu u 2
  have FT : t.fault=false := H.2.2.2.2.2.2.1
  have ⟨B,C,L,X,Z⟩ := rSealCommit_bounds p (.inr O)
  have N := rSealCommit_admit_ne p (.inr O)
  have NC : commitOp p≠sealOp p := by unfold sealOp commitOp; omega
  change t.opcode=commitOp p at O
  rw [O] at B C L X Z N
  have E : (effect p u v hu true 2 none (drWin p hu u 2) t).2.2=t := by
    simp [effect,FT,O,parked,N,X,Z,C,L,NC,show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide]
  rw [rank_row_left,D]
  simp only [rankRouteL,R,if_true,Option.elim]
  rw [show oldK p hu u 2=t from rfl,E,terminal_commit_requires_applied p t O,FT]
  cases t.applied <;> rfl

theorem seal_terminal_pair (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (D : reset0Destination hv j=none)
    (H : SealCommitForward p (publicationToken p hu u j))
    (O : (publicationToken p hu u j).opcode=sealOp p) :
    resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j =
      resetTokenWire p {tag:=3,opcode:=sealOp p} := by
  have R := seal_commit_ready p hu u j H
  obtain ⟨HV,J⟩ := rTerminal_dest hv j D
  subst hv
  subst j
  let t := publicationToken p hu u 2
  have FT : t.fault=false := H.2.2.2.2.2.2.1
  have ⟨_,_,L,X,_⟩ := rSealCommit_bounds p (.inl O)
  have N := rSealCommit_admit_ne p (.inl O)
  have NC : sealOp p≠commitOp p := by unfold sealOp commitOp; omega
  change t.opcode=sealOp p at O
  rw [O] at L X N
  have E : (effect p u v hu true 2 none (drWin p hu u 2) t).2.2=t := by
    rw [seal_effect_token p hu true u v _ _ _ t O FT]
    simp [show (2:Fin 3)≠1 by decide]
  rw [rank_row_left,D]
  simp only [rankRouteL,R,if_true,Option.elim]
  rw [show oldK p hu u 2=t from rfl,E]
  simp [terminal,FT,O,NC,X,N,L]

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

def IndexedOp (p : Params) (op : Nat) : Prop :=
  cmpOp p≤op ∧ op<sealOp p

theorem indexed_op_le (p : Params) (op : Nat) (H : IndexedOp p op) :
    op≤commitOp p := by
  have := H.2
  unfold sealOp commitOp at *
  omega

private theorem indexed_opfit (p : Params) (op : Nat) (H : IndexedOp p op) :
    op<2^o p := by
  have B := power_of_ell (5+4*p.digits)
  have := H.2
  unfold o sealOp at *
  omega

private theorem indexed_notadmit (p : Params) (op : Nat) (H : IndexedOp p op) :
    op≠admitOp p := by
  have := H.1
  unfold cmpOp admitOp at *
  omega

private theorem indexed_notacq (p : Params) (op : Nat) (H : IndexedOp p op) :
    op≠acqOp p := by
  have := H.1
  unfold cmpOp acqOp at *
  omega

structure IndexedData where
  banks : Nat
  hi : Nat
  lo : Nat

def indexedPair (p : Params) (a : IndexedData) : Nat :=
  rPack (d p) a.lo a.hi

def indexedPayload (p : Params) (a : IndexedData) : Nat :=
  rPack (d p) a.lo (rPack (d p) a.hi a.banks)

def IndexedData.OK (p : Params) (op : Nat) (a : IndexedData) : Prop :=
  a.banks<4 ∧ a.hi<p.beta ∧ a.lo<p.beta ∧
    (writeOp p≤op → a.banks=1 ∨ a.banks=2)

def IndexedGood (p : Params) (op : Nat) : Option IndexedData→Prop
  | none => True
  | some a => a.OK p op

def indexedF (p : Params) (op : Nat) : Option IndexedData→Tok
  | none => MISByteCodec.faultToken 2
  | some a => {tag:=2,opcode:=op,payload:=indexedPayload p a}

def indexedD (p : Params) (op : Nat) : Option IndexedData→Tok
  | none => MISByteCodec.faultToken 3
  | some a => {tag:=3,opcode:=op,payload:=
      if op<writeOp p then indexedPair p a else 0}

@[simp] theorem indexedF_tag (p : Params) (op : Nat) (q : Option IndexedData) :
    (indexedF p op q).tag=2 := by cases q <;> rfl

@[simp] theorem indexedD_tag (p : Params) (op : Nat) (q : Option IndexedData) :
    (indexedD p op q).tag=3 := by cases q <;> rfl

@[simp] theorem indexedF_race (p : Params) (op : Nat) (q : Option IndexedData) :
    (indexedF p op q).race=0 := by cases q <;> rfl

@[simp] theorem indexedD_race (p : Params) (op : Nat) (q : Option IndexedData) :
    (indexedD p op q).race=0 := by cases q <;> rfl

theorem indexed_beta_bound (p : Params) : p.beta≤2^d p :=
  power_of_ell p.beta

private theorem indexed_hi_bound (p : Params) (op : Nat) (a : IndexedData)
    (A : a.OK p op) : a.hi<2^d p :=
  Nat.lt_of_lt_of_le A.2.1 (indexed_beta_bound p)

private theorem indexed_lo_bound (p : Params) (op : Nat) (a : IndexedData)
    (A : a.OK p op) : a.lo<2^d p :=
  Nat.lt_of_lt_of_le A.2.2.1 (indexed_beta_bound p)

theorem indexed_pair_bound (p : Params) (op : Nat) (a : IndexedData)
    (A : a.OK p op) : indexedPair p a<2^(2*d p) := by
  unfold indexedPair
  rw [show 2*d p=d p+d p by omega]
  exact rPack_lt (indexed_lo_bound p op a A) (indexed_hi_bound p op a A)

private theorem indexed_pack_outer (p : Params) (a : IndexedData) :
    indexedPayload p a=rPack (2*d p) (indexedPair p a) a.banks := by
  unfold indexedPayload indexedPair rPack
  rw [show 2*d p=d p+d p by omega,Nat.pow_add,Nat.mul_add,Nat.mul_assoc,Nat.add_assoc]

theorem indexed_payload_bound (p : Params) (op : Nat) (a : IndexedData)
    (A : a.OK p op) : indexedPayload p a<2^(2+2*d p) := by
  rw [indexed_pack_outer,show 2+2*d p=2*d p+2 by omega]
  exact rPack_lt (indexed_pair_bound p op a A) A.1

theorem indexed_payload_banks (p : Params) (op : Nat) (a : IndexedData)
    (A : a.OK p op) : indexedPayload p a/2^(2*d p)=a.banks := by
  rw [indexed_pack_outer,rPack_div (indexed_pair_bound p op a A)]

theorem indexed_payload_pair (p : Params) (op : Nat) (a : IndexedData)
    (A : a.OK p op) : indexedPayload p a%2^(2*d p)=indexedPair p a := by
  rw [indexed_pack_outer,rPack_mod (indexed_pair_bound p op a A)]

theorem indexed_payload_hi (p : Params) (op : Nat) (a : IndexedData)
    (A : a.OK p op) : indexedPayload p a/2^d p%2^d p=a.hi := by
  unfold indexedPayload
  rw [rPack_div (indexed_lo_bound p op a A),rPack_mod (indexed_hi_bound p op a A)]

theorem indexed_payload_lo (p : Params) (op : Nat) (a : IndexedData)
    (A : a.OK p op) : indexedPayload p a%2^d p=a.lo :=
  rPack_mod (indexed_lo_bound p op a A)

theorem indexed_left_bank (p : Params) (op : Nat) (a : IndexedData)
    (A : a.OK p op) : indexedPayload p a/2^(2*d p+1)%2=a.banks/2 := by
  rw [Nat.pow_add,←Nat.div_div_eq_div_mul,indexed_payload_banks p op a A]
  exact Nat.mod_eq_of_lt (by have := A.1; omega)

theorem indexed_right_bank (p : Params) (op : Nat) (a : IndexedData)
    (A : a.OK p op) : indexedPayload p a/2^(2*d p)%2=a.banks%2 := by
  rw [indexed_payload_banks p op a A]

private theorem indexed_payload_digits (p : Params) (op : Nat) (a : IndexedData)
    (A : a.OK p op) : digitPair p (indexedPayload p a)=true := by
  simp [digitPair,indexed_payload_hi p op a A,indexed_payload_lo p op a A,A.2.1,A.2.2.1]

private theorem indexed_pair_digits (p : Params) (op : Nat) (a : IndexedData)
    (A : a.OK p op) : digitPair p (indexedPair p a)=true := by
  have H := indexed_hi_bound p op a A
  have L := indexed_lo_bound p op a A
  unfold digitPair indexedPair
  rw [rPack_div L,rPack_mod L,Nat.mod_eq_of_lt H]
  simp [A.2.1,A.2.2.1]

private theorem indexed_write_bits (p : Params) (op : Nat) (a : IndexedData)
    (A : a.OK p op) (W : writeOp p≤op) :
    bit (indexedPayload p a) (2*d p)≠bit (indexedPayload p a) (2*d p+1) := by
  unfold bit
  rw [Nat.shiftRight_eq_div_pow,Nat.shiftRight_eq_div_pow,
    indexed_left_bank p op a A,indexed_right_bank p op a A]
  rcases A.2.2.2 W with H|H <;> simp [H]

private theorem indexed_f_fit (p : Params) (op : Nat) (O : IndexedOp p op)
    (a : IndexedData) (A : a.OK p op) : RankFits p (indexedF p op (some a)) := by
  refine ⟨(by decide : 2<4),indexed_opfit p op O,?_,(by decide : 0<8),(by decide : 0<4)⟩
  exact Nat.lt_of_lt_of_le (indexed_payload_bound p op a A)
    (Nat.pow_le_pow_right (by decide : 1≤(2:Nat)) (by unfold payW; omega))

private theorem indexed_d_fit (p : Params) (op : Nat) (O : IndexedOp p op)
    (a : IndexedData) (A : a.OK p op) : RankFits p (indexedD p op (some a)) := by
  refine ⟨(by decide : 3<4),indexed_opfit p op O,?_,(by decide : 0<8),(by decide : 0<4)⟩
  change (if op<writeOp p then indexedPair p a else 0)<2^payW p
  split
  · exact Nat.lt_of_lt_of_le (indexed_pair_bound p op a A)
      (Nat.pow_le_pow_right (by decide : 1≤(2:Nat)) (by unfold payW; omega))
  · exact Nat.two_pow_pos _

-- CHECK: ReportByteRows.lean:7727 (ACQ codec proof), :4979 rReadFields.
theorem indexed_F_roundtrip (p : Params) (op : Nat) (O : IndexedOp p op)
    (g : Bool) (q : Option IndexedData) (Q : IndexedGood p op q) :
    decode p g (resetTokenWire p (indexedF p op q))=indexedF p op q := by
  cases q with
  | none => exact rFault_roundtrip p g 2 (.inl rfl)
  | some a =>
    let t := indexedF p op (some a)
    rcases rReadFields p t (indexed_f_fit p op O a Q) with ⟨A,F,OP,R,U,_,V⟩
    have ft : (resetTokenWire p t).getLsbD (6+o p+payW p)=false := by
      rw [rGet_bit,F]
      rfl
    have AD := indexed_notadmit p op O
    have AC := indexed_notacq p op O
    have CM : op≠commitOp p := by have := O.2; unfold sealOp commitOp at *; omega
    have L : ¬commitOp p<op := Nat.not_lt_of_ge (indexed_op_le p op O)
    have S : ¬sealOp p≤op := Nat.not_le_of_gt O.2
    have B := indexed_payload_digits p op a Q
    have H := Nat.mod_eq_of_lt (indexed_payload_bound p op a Q)
    change decode p g (resetTokenWire p t)=t
    simp only [decode,A,ft,OP,R,U,V]
    by_cases W : writeOp p≤op
    · have I := indexed_write_bits p op a Q W
      simp [t,indexedF,AD,AC,CM,L,S,O.1,O.2,W,B,I,H]
    · simp [t,indexedF,AD,AC,CM,L,S,O.1,O.2,W,B,H]

theorem indexed_D_roundtrip (p : Params) (op : Nat) (O : IndexedOp p op)
    (g : Bool) (q : Option IndexedData) (Q : IndexedGood p op q) :
    decode p g (resetTokenWire p (indexedD p op q))=indexedD p op q := by
  cases q with
  | none => exact rFault_roundtrip p g 3 (.inr rfl)
  | some a =>
    let t := indexedD p op (some a)
    rcases rReadFields p t (indexed_d_fit p op O a Q) with ⟨A,F,OP,R,U,_,V⟩
    have ft : (resetTokenWire p t).getLsbD (6+o p+payW p)=false := by
      rw [rGet_bit,F]
      rfl
    have AD := indexed_notadmit p op O
    have AC := indexed_notacq p op O
    have L : ¬commitOp p<op := Nat.not_lt_of_ge (indexed_op_le p op O)
    have B := indexed_pair_digits p op a Q
    have H := Nat.mod_eq_of_lt (indexed_pair_bound p op a Q)
    change decode p g (resetTokenWire p t)=t
    simp only [decode,A,ft,OP,R,U,V]
    by_cases W : op<writeOp p
    · simp [t,indexedD,AD,AC,L,O.1,W,B,H]
    · simp [t,indexedD,AD,AC,L,O.1,W]

def indexedReadOffset (p : Params) (op : Nat) : Nat :=
  op-(if op<readOp p then cmpOp p else readOp p)

def indexedSample (p : Params) (u : BitVec p.w) (bank : Nat) (port : Fin 3) : Nat :=
  min (p.beta-1) (get u (bankOffset p bank+(if port=0 then d p else 0)) (d p))

/-- Physical forward accumulator, independent of the next site's new
    work bytes. The only fault branch is a denied indexed WRITE.
    Existing fault is absorbing. -/
def indexedNext (p : Params) (op : Nat) (hu : Bool) (u : BitVec p.w)
    (port : Fin 3) : Option IndexedData→Option IndexedData
  | none => none
  | some a =>
    if op<writeOp p then
      if reportOldOffset p hu u=indexedReadOffset p op then
        if port=0 then some {a with hi:=indexedSample p u (a.banks/2) 0}
        else if port=2 then some {a with lo:=indexedSample p u (a.banks%2) 2}
        else some a
      else some a
    else if port=1 ∧ reportOldOffset p hu u=op-writeOp p ∧ hu=true ∧
        ¬(reportOldGrant p u 1=true ∧ publicationSelector p u=a.banks/2)
      then none else some a

theorem indexed_next_good (p : Params) (op : Nat) (_O : IndexedOp p op)
    (hu : Bool) (u : BitVec p.w) (port : Fin 3)
    (q : Option IndexedData) (Q : IndexedGood p op q) :
    IndexedGood p op (indexedNext p op hu u port q) := by
  cases q with
  | none => trivial
  | some a =>
    have B : 0<p.beta := by have := Q.2.1; omega
    have H (b : Nat) (j : Fin 3) : indexedSample p u b j<p.beta := by
      unfold indexedSample
      exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (by omega)
    simp only [indexedNext]
    split
    · split
      · split
        · exact ⟨Q.1,H _ _,Q.2.2.1,Q.2.2.2⟩
        · split
          · exact ⟨Q.1,Q.2.1,H _ _,Q.2.2.2⟩
          · exact Q
      · exact Q
    · split
      · trivial
      · exact Q

private theorem indexed_edit_hi (p : Params) (op : Nat) (a : IndexedData)
    (A : a.OK p op) (v : Nat) :
    indexedPayload p a-(indexedPayload p a/2^d p%2^d p)*2^d p+v*2^d p=
      indexedPayload p {a with hi:=v} := by
  rw [indexed_payload_hi p op a A]
  unfold indexedPayload rPack
  simp only [Nat.mul_add]
  rw [Nat.mul_comm a.hi (2^d p),Nat.mul_comm v (2^d p)]
  omega

private theorem indexed_edit_lo (p : Params) (op : Nat) (a : IndexedData)
    (A : a.OK p op) (v : Nat) :
    indexedPayload p a-indexedPayload p a%2^d p+v=
      indexedPayload p {a with lo:=v} := by
  rw [indexed_payload_lo p op a A]
  unfold indexedPayload rPack
  simp only
  omega

private theorem indexed_left_bit (p : Params) (op : Nat) (a : IndexedData)
    (A : a.OK p op) :
    (bit (indexedPayload p a) (2*d p+1)).toNat=a.banks/2 := by
  unfold bit
  rw [Nat.shiftRight_eq_div_pow,indexed_left_bank p op a A]
  rcases (show a.banks/2=0 ∨ a.banks/2=1 by have := A.1; omega) with H|H <;> simp [H]

private theorem indexed_right_bit (p : Params) (op : Nat) (a : IndexedData)
    (A : a.OK p op) :
    (bit (indexedPayload p a) (2*d p)).toNat=a.banks%2 := by
  unfold bit
  rw [Nat.shiftRight_eq_div_pow,indexed_right_bank p op a A]
  rcases (show a.banks%2=0 ∨ a.banks%2=1 by omega) with H|H <;> simp [H]

/-- The real effect, not just its opcode. The packet projection does
    not depend on the destination or the old arbitration win for
    these indexed non-ACQ opcodes. -/
theorem indexed_effect (p : Params) (op : Nat) (O : IndexedOp p op)
    (hu hv : Bool) (u v : BitVec p.w) (port : Fin 3) (k : Option (Fin 3))
    (win : Bool) (q : Option IndexedData) (Q : IndexedGood p op q) :
    (effect p u v hu hv port k win (indexedF p op q)).2.2=
      indexedF p op (indexedNext p op hu u port q) := by
  cases q with
  | none => rfl
  | some a =>
    have AD := indexed_notadmit p op O
    have AC := indexed_notacq p op O
    have CM : op≠commitOp p := by have := O.2; unfold sealOp commitOp at *; omega
    have SZ : op≠sealOp p := Nat.ne_of_lt O.2
    have Z : op≠0 := by have := O.1; unfold cmpOp at *; omega
    have L := O.1
    have P := indexed_payload_banks p op a Q
    have Prior : indexedPayload p a/2^(2*d p+1)=a.banks/2 := by
      rw [Nat.pow_add,←Nat.div_div_eq_div_mul,P]
    have H0 := indexed_left_bit p op a Q
    have H2 := indexed_right_bit p op a Q
    have ports : port=0 ∨ port=1 ∨ port=2 := acq_lane_cases port
    by_cases R : op<writeOp p
    · have W : ¬writeOp p≤op := Nat.not_le_of_gt R
      by_cases V : op < readOp p <;>
        by_cases H : reportOldOffset p hu u=indexedReadOffset p op <;>
        simp only [reportOldOffset,indexedReadOffset,V,if_true,if_false] at H <;>
        rcases ports with rfl|rfl|rfl <;>
        simp [effect,indexedF,indexedNext,parked,CM,AD,AC,SZ,Z,R,L,W,
          reportOldOffset,indexedReadOffset,V,H,H0,H2,indexedSample,
          indexed_edit_hi p op a Q,indexed_edit_lo p op a Q]
    · have W : writeOp p≤op := by omega
      by_cases H : reportOldOffset p hu u=op-writeOp p <;> unfold reportOldOffset at H
      · rcases ports with rfl|rfl|rfl
        · simp [effect,indexedF,indexedNext,parked,CM,AD,AC,SZ,Z,R,L,W]
        · cases hu with
          | false =>
            simp [effect,indexedF,indexedNext,parked,CM,AD,AC,SZ,Z,R,L,W,O.2,
              reportOldOffset,H,Prior,reportOldGrant,publicationSelector]
          | true =>
            cases GB : gBit p u 1 <;>
              by_cases S : selected p u=a.banks/2 <;>
              simp [effect,indexedF,indexedNext,parked,CM,AD,AC,SZ,Z,R,L,W,O.2,
                reportOldOffset,H,Prior,reportOldGrant,publicationSelector,GB,S]
        · simp [effect,indexedF,indexedNext,parked,CM,AD,AC,SZ,Z,R,L,W]
      · simp [effect,indexedF,indexedNext,parked,CM,AD,AC,SZ,Z,R,L,W,O.2,
          reportOldOffset,H]

private theorem indexed_terminal (p : Params) (op : Nat) (O : IndexedOp p op)
    (q : Option IndexedData) (Q : IndexedGood p op q) :
    terminal p (indexedF p op q)=indexedD p op q := by
  cases q with
  | none => rfl
  | some a =>
    have AD := indexed_notadmit p op O
    have AC := indexed_notacq p op O
    have CM : op≠commitOp p := by have := O.2; unfold sealOp commitOp at *; omega
    by_cases L : op<writeOp p <;> simp [terminal,indexedF,indexedD,AD,AC,CM,O.1,indexed_payload_pair p op a Q,L]

private theorem indexed_arrival (p : Params) (op : Nat) (O : IndexedOp p op)
    (hv : Bool) (v : BitVec p.w) (k : Fin 3) (q : Option IndexedData) :
    arrival p hv v k (indexedF p op q)=indexedF p op q := by
  cases q <;> simp [arrival,indexedF,indexed_notadmit p op O,MISByteCodec.faultToken]

theorem rankIndexed_ready (p : Params) (op : Nat) (O : IndexedOp p op)
    (hu : Bool) (u : BitVec p.w) (j : Fin 3) (q : Option IndexedData)
    (A : publicationToken p hu u j=indexedF p op q) :
    rankReady p hu u j=true := by
  rw [rankReady_iff,A]
  cases q <;> simp [indexedF,healthyAdmit,indexed_notadmit p op O,MISByteCodec.faultToken]

theorem rankIndexed_hop (p : Params) (op : Nat) (O : IndexedOp p op)
    (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (J : reset0Destination hv j=some k) (g' : Bool)
    (q : Option IndexedData) (Q : IndexedGood p op q)
    (A : publicationToken p hu u j=indexedF p op q) :
    decode p g' (resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k)=
      indexedF p op (indexedNext p op hu u j q) := by
  have R := rankIndexed_ready p op O hu u j q A
  rw [rank_row_right p hu hv u v j k J]
  simp only [rankRouteR,R,if_true,Option.elim]
  change decode p g' (resetTokenWire p (arrival p hv v k
    (effect p u v hu hv j (some k) (drWin p hu u j)
      (publicationToken p hu u j)).2.2))=_
  rw [A,indexed_effect p op O hu hv u v j (some k) _ q Q,
    indexed_arrival p op O hv v k]
  exact indexed_F_roundtrip p op O g' _ (indexed_next_good p op O hu u j q Q)

theorem rankIndexed_turn (p : Params) (op : Nat) (O : IndexedOp p op)
    (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (J : reset0Destination hv j=none) (g' : Bool)
    (q : Option IndexedData) (Q : IndexedGood p op q)
    (A : publicationToken p hu u j=indexedF p op q) :
    decode p g' (resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j)=
      indexedD p op (indexedNext p op hu u j q) := by
  have R := rankIndexed_ready p op O hu u j q A
  rw [rank_row_left,J]
  simp only [rankRouteL,R,if_true,Option.elim]
  change decode p g' (resetTokenWire p (terminal p
    (effect p u v hu hv j none (drWin p hu u j)
      (publicationToken p hu u j)).2.2))=_
  rw [A,indexed_effect p op O hu hv u v j none _ q Q,
    indexed_terminal p op O _ (indexed_next_good p op O hu u j q Q)]
  exact indexed_D_roundtrip p op O g' _ (indexed_next_good p op O hu u j q Q)

/-- Full decoded equality on normalization, including an old
    canonical fault. No hypothesis about the unused raw padding. -/
theorem indexed_zero_race_norm (p : Params) (g : Bool)
    (w : BitVec (tokenW p)) (side : Nat) (S : side=2 ∨ side=3)
    (Z : (decode p g w).race=0) :
    decode p g (rankNormWire p side g w)=decode p g w := by
  rcases rank_norm_cases p g w side S with E|⟨_,_,_,_,_,R⟩
  · exact E
  · rcases R with R|R|R <;> have H := R.1 <;> rw [Z] at H <;> contradiction

/-- Root door cannot normalize a parked ADMIT race at K0. -/
theorem indexed_root_norm (p : Params) (v : BitVec p.w) :
    decode p false (prelaunchDoorNormWire p v)=publicationToken p true v 0 := by
  unfold prelaunchDoorNormWire
  dsimp only
  by_cases H : (oldK p true v 0).fault=true
  · rw [if_pos H]
    change decode p false (resetTokenWire p (oldK p true v 0))=oldK p true v 0
    obtain ⟨E,J⟩ := rDecoded_fault p false (resetTokenRead p v 0) H
    have R : oldK p true v 0=MISByteCodec.faultToken (oldK p true v 0).tag := E
    rw [congrArg (resetTokenWire p) R]
    exact (rFault_roundtrip p false _ J).trans R.symm
  · rw [if_neg H]
    have K : parked p (oldK p true v 0) true v 0=false := by simp [parked,gate]
    simp only [K,Bool.false_and,Bool.false_eq_true,if_false]
    exact (prelaunch_root_decode p v).symm

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

set_option maxRecDepth 16000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-- Ready, healthy indexed WRITE at its literal old offset.
    We intentionally omit the header grant guard: excluding this
    larger set of candidates suffices for the frame theorem. -/
def WriteDigitEnabled (p : Params) (hu : Bool) (u : BitVec p.w) : Prop :=
  let t := publicationToken p hu u 1
  rankReady p hu u 1=true ∧ t.fault=false ∧
    writeOp p≤t.opcode ∧ t.opcode<sealOp p ∧
    reportOldOffset p hu u=t.opcode-writeOp p

private theorem writehit_effect_frame (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (j : Fin 3) (k : Option (Fin 3))
    (win : Bool) (t : Tok)
    (H : ¬(t.fault=false ∧ writeOp p≤t.opcode ∧ t.opcode<sealOp p ∧
      j=1 ∧ reportOldOffset p hu u=t.opcode-writeOp p)) :
    cmtFrame p (effect p u v hu hv j k win t).1 := by
  by_cases F0 : t.fault=true
  · simp only [effect,F0,if_true]
    exact cmtEmpty p
  · have L : t.fault=false := Bool.eq_false_iff.mpr F0
    have N : (decide (writeOp p≤t.opcode) && decide (t.opcode<sealOp p) &&
        (j==1) && (geomOff p hu u==t.opcode-writeOp p))=false := by
      apply Bool.eq_false_iff.mpr
      intro A
      simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at A
      exact H ⟨L,A.1.1.1,A.1.1.2,A.1.2,A.2⟩
    unfold effect
    dsimp only
    simp only [L,N,Bool.false_eq_true,if_false]
    generalize (if t.opcode<readOp p then cmpOp p else readOp p) = off
    split
    · split <;> exact cmtEmpty p
    · split
      · exact cmtEmpty p
      · split
        · exact cmtSeal p none
        · split
          · exact cmtEmpty p
          · split
            · exact cmtEmpty p
            · split
              · split
                · exact cmtSeal p (some t.payload)
                · exact cmtEmpty p
              · exact cmtEmpty p

/-- The common left prepatch has no bank/selector bit. Identical
    header argument to the checked denied-writer proof at :7936. -/
private theorem writehit_pre_frame (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) : cmtFrame p (drPre p hu hv u v).1 := by
  cases hu
  · exact rDigitPrefix p hv u v
  · have B : cmtFrame p (drBaseL p true u) := by
      unfold drBaseL
      simp only [if_true]
      apply cmtField
      intro i I
      rcases I with ⟨_,I⟩|I
      · exact .inl I
      · exact .inr (by omega)
    have PP : cmtFrame p (pulse p true 2 u) := by
      intro i I
      apply pulse_mask_below_tail
      rcases I with ⟨I,_⟩|I
      · unfold sealBase sourceBase at I
        omega
      · unfold grantBase sealBase sourceBase at I
        omega
    have NN (j : Fin 3) : cmtFrame p (outgoingNormalize p true u j) := by
      rcases dr_norm_left_shape p true u j with E|⟨t,E⟩
      · rw [E]; exact cmtEmpty p
      · rw [E]; exact cmtK p j t
    change cmtFrame p (drPrefix p (drBaseL p true u) (pulse p true 2 u)
      (outgoingNormalize p true u))
    exact cmtCompose (cmtCompose (cmtCompose (cmtCompose B PP)
      (NN 0)) (NN 1)) (NN 2)

/-- Any route whose ready effect frames the observed bit preserves
    the previous accumulated patch's *applied* value at that bit. -/
private theorem writehit_route_bit_frame (p : Params) (hu hv : Bool)
    (u v base : BitVec p.w) (win : Fin 3→Bool)
    (ab : Pair (Patch (workW p))) (j : Fin 3) (k : Option (Fin 3))
    (i : Nat) (I : cmtIndex p i)
    (H : rankReady p hu u j=true →
      (effect p u v hu hv j k (win j) (oldK p hu u j)).1.mask.getLsbD i=false) :
    ((widen p (cmtRoute p hu hv u v win ab (j,k)).1).apply base).getLsbD i=
      ((widen p ab.1).apply base).getLsbD i := by
  rcases ab with ⟨a,b⟩
  have K (t : Tok) (z : BitVec p.w) :
      ((widen p (writeK p j t)).apply z).getLsbD i=z.getLsbD i :=
    pulse_widen_frame p _ z i (cmtK p j t i I)
  unfold cmtRoute
  dsimp only
  by_cases R : ready p hu u j (oldK p hu u j)=true
  · have F := H R
    rw [if_pos R]
    cases k <;> dsimp only <;>
      rw [reset0_widen_apply,reset0_widen_apply] <;>
      exact (K _ _).trans (pulse_widen_frame p _ _ i F)
  · rw [if_neg R]
    split
    · rfl
    · cases k with
      | none =>
        dsimp only
        split
        · rw [reset0_widen_apply]; exact K _ _
        · rfl
      | some k =>
        dsimp only
        split
        · rw [reset0_widen_apply]; exact K _ _
        · split
          · rw [reset0_widen_apply]; exact K _ _
          · rfl

private theorem writehit_other_route (p : Params) (hu hv : Bool)
    (u v base : BitVec p.w) (win : Fin 3→Bool)
    (ab : Pair (Patch (workW p))) (j : Fin 3) (k : Option (Fin 3))
    (i : Nat) (I : cmtIndex p i)
    (H : j≠1 ∨ ¬WriteDigitEnabled p hu u) :
    ((widen p (cmtRoute p hu hv u v win ab (j,k)).1).apply base).getLsbD i=
      ((widen p ab.1).apply base).getLsbD i := by
  apply writehit_route_bit_frame p hu hv u v base win ab j k i I
  intro R
  have No : ¬((oldK p hu u j).fault=false ∧
      writeOp p≤(oldK p hu u j).opcode ∧ (oldK p hu u j).opcode<sealOp p ∧
      j=1 ∧ reportOldOffset p hu u=(oldK p hu u j).opcode-writeOp p) := by
    intro A
    rcases H with H|H
    · exact H A.2.2.2.1
    · have J := A.2.2.2.1
      subst j
      exact H ⟨R,A.1,A.2.1,A.2.2.1,A.2.2.2.2⟩
  exact writehit_effect_frame p hu hv u v j k (win j) (oldK p hu u j) No i I

/-- One ready K1 route applies exactly the digit patch, followed
    by a token write which frames the observed bit. -/
private theorem writehit_route_value (p : Params) (hu hv : Bool)
    (u v base : BitVec p.w) (win : Fin 3→Bool)
    (ab : Pair (Patch (workW p))) (k : Option (Fin 3))
    (j : Fin p.digits)
    (R : rankReady p hu u 1=true)
    (Live : (publicationToken p hu u 1).fault=false)
    (Op : (publicationToken p hu u 1).opcode=writeOp p+j.val)
    (Off : reportOldOffset p hu u=j.val)
    (Permit : hu=false ∨ (reportOldGrant p u 1=true ∧
      publicationSelector p u=(publicationToken p hu u 1).payload/2^(2*d p+1)))
    (i : Nat) (I : cmtIndex p i) :
    let t := publicationToken p hu u 1
    let a := field p (bankOffset p (ancestryWriteTarget p t))
      (2*d p) (t.payload%2^(2*d p))
    ((widen p (cmtRoute p hu hv u v win ab (1,k)).1).apply base).getLsbD i=
      ((widen p a).apply ((widen p ab.1).apply base)).getLsbD i := by
  dsimp only
  rcases ab with ⟨a,b⟩
  let t := oldK p hu u 1
  have E := write_digit_old p hu hv u v j k (win 1) t Off Live Op Permit
  change ready p hu u 1 t=true at R
  unfold cmtRoute
  dsimp only
  rw [if_pos R]
  rw [E]
  cases k <;> dsimp only <;>
    rw [reset0_widen_apply,reset0_widen_apply] <;>
    exact pulse_widen_frame p _ _ i (cmtK p 1 _ i I)

private theorem writehit_same_bit (p : Params) (a : Patch (workW p))
    (u v : BitVec p.w) (i : Nat)
    (H : u.getLsbD i=v.getLsbD i) :
    ((widen p a).apply u).getLsbD i=((widen p a).apply v).getLsbD i := by
  by_cases W : (widen p a).mask.getLsbD i=true
  · rw [Patch.write _ _ _ W,Patch.write _ _ _ W]
  · have N : (widen p a).mask.getLsbD i=false := Bool.eq_false_iff.mpr W
    rw [Patch.hold _ _ _ N,Patch.hold _ _ _ N,H]

private theorem writehit_links (hv : Bool) :
    links hv =
      [(0,if hv then some 1 else some 0),
       (1,if hv then some 2 else some 1),
       (2,if hv then none else some 2)] := by
  cases hv <;> rfl

/-- Complete joined value equation on all bank/selector fields of
    the outgoing endpoint: the result equals applying precisely the
    old K1 WRITE field, not applying a patch to a new live selector. -/
private theorem writehit_left_observe (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (j : Fin p.digits)
    (R : rankReady p hu u 1=true)
    (Live : (publicationToken p hu u 1).fault=false)
    (Op : (publicationToken p hu u 1).opcode=writeOp p+j.val)
    (Off : reportOldOffset p hu u=j.val)
    (Permit : hu=false ∨ (reportOldGrant p u 1=true ∧
      publicationSelector p u=(publicationToken p hu u 1).payload/2^(2*d p+1)))
    (i : Nat) (I : cmtIndex p i) :
    let t := publicationToken p hu u 1
    ((row p (hu,hv) (u,v)).1.apply u).getLsbD i=
      ((widen p (field p (bankOffset p (ancestryWriteTarget p t))
        (2*d p) (t.payload%2^(2*d p)))).apply u).getLsbD i := by
  dsimp only
  let w := drWin p hu u
  let a := drPre p hu hv u v
  let k0 : Option (Fin 3) := if hv then some 1 else some 0
  let k1 : Option (Fin 3) := if hv then some 2 else some 1
  let k2 : Option (Fin 3) := if hv then none else some 2
  let b := cmtRoute p hu hv u v w a (0,k0)
  let c := cmtRoute p hu hv u v w b (1,k1)
  let z := cmtRoute p hu hv u v w c (2,k2)
  have A := pulse_widen_frame p a.1 u i (writehit_pre_frame p hu hv u v i I)
  have B := writehit_other_route p hu hv u v u w a 0 k0 i I (.inl (by decide))
  have C := writehit_route_value p hu hv u v u w b k1 j R Live Op Off Permit i I
  have D := writehit_other_route p hu hv u v u w c 2 k2 i I (.inl (by decide))
  rw [dr_row_eq,reset0Post_left]
  unfold drRouted
  rw [writehit_links hv]
  simp only [List.foldl_cons,List.foldl_nil]
  change ((widen p z.1).apply u).getLsbD i=_
  exact D.trans (C.trans (writehit_same_bit p _ _ _ i (B.trans A)))

/-- The indexed left write value, in the exact form used by the write ledger. -/
theorem indexed_left_write_value (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (j : Fin p.digits)
    (T : rankReady p hu u 1=true)
    (Live : (publicationToken p hu u 1).fault=false)
    (Op : (publicationToken p hu u 1).opcode=writeOp p+j.val)
    (Off : reportOldOffset p hu u=j.val)
    (Permit : hu=false ∨ (reportOldGrant p u 1=true ∧
      publicationSelector p u=(publicationToken p hu u 1).payload/2^(2*d p+1))) :
    let t := publicationToken p hu u 1
    reportDigitPair p ((row p (hu,hv) (u,v)).1.apply u) (ancestryWriteTarget p t)=
      BitVec.ofNat (2*d p) (t.payload%2^(2*d p)) := by
  dsimp only
  let t := publicationToken p hu u 1
  let b := ancestryWriteTarget p t
  let q := t.payload%2^(2*d p)
  have Eq : reportDigitPair p ((row p (hu,hv) (u,v)).1.apply u) b =
      reportDigitPair p ((widen p (field p (bankOffset p b) (2*d p) q)).apply u) b := by
    apply BitVec.eq_of_getLsbD_eq
    intro i I
    simp only [reportDigitPair,BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
    exact writehit_left_observe p hu hv u v j T Live Op Off Permit _
      (rDigitIndex p b i I)
  have Fit : bankOffset p b+2*d p≤workW p := by
    have L := Nat.mul_le_mul_right (bankW p) (show 1-b≤1 by omega)
    unfold bankOffset workW grantBase bankW at *
    omega
  rw [Eq]
  unfold reportDigitPair
  have A := dr_field_sub p u (bankOffset p b) (2*d p) q 0 (2*d p) Fit (by omega)
  rw [Nat.add_zero] at A
  -- CHECK: dr_field_sub :3850 and BitVec.extractLsb'_toNat.
  rw [A]
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  change ((BitVec.ofNat (2*d p) q).extractLsb' 0 (2*d p)).getLsbD i=
    (BitVec.ofNat (2*d p) q).getLsbD i
  simp [BitVec.getLsbD_extractLsb',I]

/-- The other physical bank is untouched, including on a header.
    No assumption about a particular old digit value. -/
theorem indexed_left_write_other (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (j : Fin p.digits)
    (T : rankReady p hu u 1=true)
    (Live : (publicationToken p hu u 1).fault=false)
    (Op : (publicationToken p hu u 1).opcode=writeOp p+j.val)
    (Off : reportOldOffset p hu u=j.val)
    (Permit : hu=false ∨ (reportOldGrant p u 1=true ∧
      publicationSelector p u=(publicationToken p hu u 1).payload/2^(2*d p+1)))
    (sel : Nat) (S : sel<2)
    (Other : sel≠ancestryWriteTarget p (publicationToken p hu u 1)) :
    reportDigitPair p ((row p (hu,hv) (u,v)).1.apply u) sel=reportDigitPair p u sel := by
  let t := publicationToken p hu u 1
  let b := ancestryWriteTarget p t
  have B : b<2 := Nat.mod_lt _ (by decide)
  have D : sel≠b := Other
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  let a := reportBankDigitAddress p sel i
  simp only [reportDigitPair,BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  change ((row p (hu,hv) (u,v)).1.apply u).getLsbD a=u.getLsbD a
  refine (writehit_left_observe p hu hv u v j T Live Op Off Permit a
    (rDigitIndex p sel i I)).trans ?_
  apply pulse_widen_frame
  have H : a<bankOffset p b ∨ bankOffset p b+2*d p≤a := by
    rcases (show sel=0 ∨ sel=1 by omega) with L|L
    · have E : b=1 := by omega
      right
      simp [a,reportBankDigitAddress,bankOffset,bankW,L,E]
      omega
    · have E : b=0 := by omega
      left
      simp [a,reportBankDigitAddress,bankOffset,bankW,L,E]
      omega
  exact pulse_field_out p _ _ _ _ H

/-- If the matching indexed WRITE branch is absent on old K1,
    every digit bank (and selector) bit is framed. This strictly
    strengthens the no-ready frame and handles later
    completed-prefix instructions at a header, even with held grant. -/
theorem indexed_left_no_write_bank_frame (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (sel : Nat) (H : ¬WriteDigitEnabled p hu u) :
    reportDigitPair p ((row p (hu,hv) (u,v)).1.apply u) sel=reportDigitPair p u sel := by
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  let q := reportBankDigitAddress p sel i
  have IX := rDigitIndex p sel i I
  let w := drWin p hu u
  let a := drPre p hu hv u v
  let k0 : Option (Fin 3) := if hv then some 1 else some 0
  let k1 : Option (Fin 3) := if hv then some 2 else some 1
  let k2 : Option (Fin 3) := if hv then none else some 2
  let b := cmtRoute p hu hv u v w a (0,k0)
  let c := cmtRoute p hu hv u v w b (1,k1)
  let z := cmtRoute p hu hv u v w c (2,k2)
  have A := pulse_widen_frame p a.1 u q (writehit_pre_frame p hu hv u v q IX)
  have B := writehit_other_route p hu hv u v u w a 0 k0 q IX (.inl (by decide))
  have C := writehit_other_route p hu hv u v u w b 1 k1 q IX (.inr H)
  have D := writehit_other_route p hu hv u v u w c 2 k2 q IX (.inl (by decide))
  simp only [reportDigitPair,BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  change ((row p (hu,hv) (u,v)).1.apply u).getLsbD q=u.getLsbD q
  rw [dr_row_eq,reset0Post_left]
  unfold drRouted
  rw [writehit_links hv]
  simp only [List.foldl_cons,List.foldl_nil]
  change ((widen p z.1).apply u).getLsbD q=u.getLsbD q
  exact D.trans (C.trans (B.trans A))

theorem writehit_not_enabled_of_tag (p : Params) (hu : Bool)
    (u : BitVec p.w) (H : (publicationToken p hu u 1).tag≠2) :
    ¬WriteDigitEnabled p hu u := by
  intro E
  exact H ((rankReady_iff p hu u 1).mp E.1).1

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

theorem indexed_write_issue_data (p : Params) (v : BitVec p.w) (old f : Tok)
    (P : sourcePhase p v=1)
    (W : writeOp p≤sourceOpcode p v)
    (U : sourceOpcode p v<sealOp p)
    (T : (source p v old).2=some f) (Tag : f.tag=2) :
    ∃ a : IndexedData,
      a.OK p (sourceOpcode p v) ∧
      f=indexedF p (sourceOpcode p v) (some a) ∧
      ancestryWriteOld p f=acqCaptureIndex p v/2%2 ∧
      ancestryWriteTarget p f=1-(acqCaptureIndex p v/2%2) ∧
      f.payload%2^(2*d p)=ancestrySendDigits p v := by
  let prior := ancestrySourceCentre p v
  let send := ancestrySendDigits p v
  have Prior : prior<2 := ancestry_source_centre_lt p v
  have Send : send<2^(2*d p) := ancestry_send_digits_lt p v
  have Dig : digitPair p send=true := by
    cases H : digitPair p send
    · have P0 : get v (pc p+o p) 2=1 := P
      have W0 : writeOp p≤get v (pc p) (o p) := W
      have U0 : get v (pc p) (o p)<sealOp p := U
      have B : ¬commitOp p<get v (pc p) (o p) := by unfold commitOp sealOp at *; omega
      have Bad : (source p v old).2=some MISByteCodec.E := by
        change digitPair p (rf p v 3 (2*d p))=false at H
        simp [source,P0,W0,U0,B,H]
      rw [Bad] at T
      have E := Option.some.inj T
      rw [←E] at Tag
      contradiction
    · rfl
  have E := ancestry_source_write_intent p v old P W U Dig
  rw [T] at E
  have Packet : f=({tag:=2,opcode:=sourceOpcode p v,payload:=ancestryWritePayload p prior send}:Tok) := Option.some.inj E
  let a : IndexedData := ⟨2*prior+(1-prior),send/2^d p,send%2^d p⟩
  have Hi : send/2^d p<2^d p := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
    rw [←Nat.pow_add,show d p+d p=2*d p by omega]
    exact Send
  have D : send%2^d p<p.beta ∧ send/2^d p%2^d p<p.beta := by
    simpa [digitPair,Bool.and_eq_true] using Dig
  rw [Nat.mod_eq_of_lt Hi] at D
  have A : a.OK p (sourceOpcode p v) := by
    refine ⟨?_,D.2,D.1,?_⟩
    · change 2*prior+(1-prior)<4; omega
    · intro _
      change 2*prior+(1-prior)=1 ∨ 2*prior+(1-prior)=2
      omega
  have Pair : indexedPair p a=send := by
    change send%2^d p+2^d p*(send/2^d p)=send
    exact Nat.mod_add_div _ _
  have Payload : indexedPayload p a=ancestryWritePayload p prior send := by
    rw [indexed_pack_outer,Pair]
    change send+2^(2*d p)*(2*prior+(1-prior))=
      (2*prior+(1-prior))*2^(2*d p)+send
    ac_rfl
  have EQ : f=indexedF p (sourceOpcode p v) (some a) := by
    rw [Packet]
    simp only [indexedF,Payload]
  have Ind := ancestry_write_indices p f prior send Prior Send (congrArg MISByteCodec.Token.payload Packet)
  have Cap : prior=acqCaptureIndex p v/2%2 := rfl
  refine ⟨a,A,EQ,Ind.1.trans Cap,Ind.2.trans (congrArg (fun z : Nat=>1-z) Cap),?_⟩
  rw [EQ]
  exact (indexed_payload_pair p (sourceOpcode p v) a A).trans Pair

/-- Successful WRITE next-state data is exactly its predecessor.
    In particular none cannot turn into some on any later mark. -/
theorem indexed_write_next_some (p : Params) (op : Nat)
    (W : writeOp p≤op) (hu : Bool) (u : BitVec p.w) (port : Fin 3)
    (q : Option IndexedData) (a : IndexedData)
    (H : indexedNext p op hu u port q=some a) : q=some a := by
  cases q with
  | none => contradiction
  | some b =>
    simp only [indexedNext,if_neg (Nat.not_lt_of_ge W)] at H
    split at H
    · contradiction
    · exact H

theorem indexed_write_old_bank (p : Params) (op : Nat) (a : IndexedData)
    (A : a.OK p op) :
    ancestryWriteOld p (indexedF p op (some a))=a.banks/2 := by
  change indexedPayload p a/2^(2*d p+1)=a.banks/2
  rw [Nat.pow_add,←Nat.div_div_eq_div_mul,indexed_payload_banks p op a A]

/-- Successful actual hit cannot have taken the denied header branch.
    Uses the full accumulator step, not its healthy opcode alone. -/
theorem indexed_write_next_permit (p : Params) (op : Nat)
    (W : writeOp p≤op) (hu : Bool) (u : BitVec p.w)
    (a : IndexedData) (A : a.OK p op)
    (Off : reportOldOffset p hu u=op-writeOp p)
    (H : indexedNext p op hu u 1 (some a)=some a) :
    hu=false ∨ (reportOldGrant p u 1=true ∧
      publicationSelector p u=ancestryWriteOld p (indexedF p op (some a))) := by
  rw [indexed_write_old_bank p op a A]
  cases hu with
  | false => exact .inl rfl
  | true =>
    right
    by_cases E : reportOldGrant p u 1=true ∧ publicationSelector p u=a.banks/2
    · exact E
    · simp [indexedNext,Nat.not_lt_of_ge W,Off,E] at H

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem writehit_right_selector_regression :
    let p : Params := ⟨2,3,4,3⟩
    let f : Tok := {tag:=2,opcode:=writeOp p+2,payload:=2^(2*d p)+1}
    let c : Tok := {tag:=2,opcode:=commitOp p,payload:=5}
    let u : BitVec p.w := BitVec.ofNat _
      (encode p c*2^(kOffset p 0)+encode p f*2^(kOffset p 1)+2*2^(workW p+1))
    let v : BitVec p.w := BitVec.ofNat _
      (2^(grantBase p+1)+21*2^(sealBase p)+
       2^(bankOffset p 1+2+2*d p)+2^(pc p+o p+1)+
       encode p MISByteCodec.T*2^(kOffset p 0)+2*2^(ell p.streak)+2)
    let y := row p (false,true) (u,v)
    rankReady p false u 1=true ∧
    reportOldOffset p false u=2 ∧ publicationToken p false u 1=f ∧
    reportDigitPair p (y.1.apply u) 1=BitVec.ofNat (2*d p) 1 ∧
    publicationSelector p v=0 ∧ publicationSelector p (y.2.apply v)=1 := by
  decide

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

inductive ItemNineField where
  | send | carry | output | input | heads | indices
  deriving DecidableEq

def item9Off (p : Params) : ItemNineField → Nat
  | .send => 3
  | .carry => 3+2*d p
  | .output => 5+2*d p
  | .input => 9+2*d p
  | .heads => 13+2*d p
  | .indices => 16+2*d p

def item9Width (p : Params) : ItemNineField → Nat
  | .send => 2*d p
  | .carry => 2
  | .output | .input => 4
  | .heads | .indices => 3

def item9Read (p : Params) (v : BitVec p.w) (k : ItemNineField) : Nat :=
  rf p v (item9Off p k) (item9Width p k)

private def item9Assign (p : Params) (k : ItemNineField) (v : Nat) :=
  sf p (item9Off p k) (item9Width p k) v

private theorem item9_room (p : Params) (k : ItemNineField) :
    item9Off p k+item9Width p k≤19+2*d p := by
  cases k <;> simp [item9Off,item9Width] <;> omega

theorem item9_read_congr (p : Params) (v u : BitVec p.w)
    (F : drainFile p v=drainFile p u) :
    item9Read p v=item9Read p u := by
  funext k
  exact indexed_rf_congr p v u F _ _ (item9_room p k)

private theorem item9_read_assign (p : Params) (x : BitVec p.w)
    (a b : ItemNineField) (q : Nat) :
    item9Read p ((widen p (item9Assign p a q)).apply x) b=
      if b=a then q%2^(item9Width p a) else item9Read p x b := by
  by_cases H : b=a
  · subst b
    rw [if_pos rfl]
    have Fit : sourceBase p+item9Off p a+item9Width p a≤workW p := by
      have R := item9_room p a
      unfold workW grantBase sealBase sourceW
      omega
    have E := dr_field_sub p x (sourceBase p+item9Off p a)
      (item9Width p a) q 0 (item9Width p a) Fit (by omega)
    rw [Nat.add_zero] at E
    unfold item9Read item9Assign sf rf get
    rw [E]
    simp [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  · rw [if_neg H]
    have D : item9Off p b+item9Width p b≤item9Off p a ∨
        item9Off p a+item9Width p a≤item9Off p b := by
      cases a <;> cases b <;> simp_all [item9Off,item9Width] <;> omega
    unfold item9Read item9Assign sf rf get
    apply congrArg BitVec.toNat
    apply BitVec.eq_of_getLsbD_eq
    intro i I
    simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
    apply pulse_widen_frame
    apply pulse_field_out
    rcases D with D|D
    · exact .inl (by omega)
    · exact .inr (by omega)

private theorem item9_read_ctrl (p : Params) (x : BitVec p.w)
    (phase op : Nat) (k : ItemNineField) :
    item9Read p ((widen p (ctrl p phase op)).apply x) k=item9Read p x k := by
  have E := dr_file_late p x (pc p) (o p+2) (phase*2^o p+op) (Nat.le_refl _)
  exact congrFun (item9_read_congr p _ _ E) k

theorem item9_pack_bound (p : Params) (a b : Nat)
    (A : a<2^d p) (B : b<2^d p) :
    2^d p*a+b<2^(2*d p) := by
  rw [Nat.add_comm,show 2*d p=d p+d p by omega]
  exact rPack_lt B A

theorem item9_pack_halves (p : Params) (a b : Nat) (B : b<2^d p) :
    (2^d p*a+b)/2^d p=a ∧ (2^d p*a+b)%2^d p=b := by
  rw [Nat.add_comm]
  exact ⟨rPack_div B,rPack_mod B⟩

/-- Source action on a real healthy CMP reply. The last CMP
    initializes output comparison and BOTH carries. -/
private theorem item9_cmp_action (p : Params) (v : BitVec p.w) (t : Tok)
    (j : Nat) (J : j<p.digits)
    (P : sourcePhase p v=2) (O : sourceOpcode p v=cmpOp p+j)
    (Tag : t.tag=3) (Match : t.opcode=cmpOp p+j)
    (Live : t.fault=false) (ND : t.outcome≠1)
    (C0 : item9Read p v .input/4≠3) (C2 : item9Read p v .input%4≠3) :
    let a := t.payload/2^d p
    let b := t.payload%2^d p
    let kd := ReportDigitArithmetic.digit p.beta j p.radius
    let q := 4*ReportDigitArithmetic.cmp a kd (item9Read p v .input/4)+
      ReportDigitArithmetic.cmp b kd (item9Read p v .input%4)
    source p v t =
      if j+1<p.digits then
        ((ctrl p 1 (cmpOp p+j+1)).compose (item9Assign p .input q),some MISByteCodec.E)
      else
        ((((ctrl p 1 (readOp p)).compose (item9Assign p .input q)).compose
          (item9Assign p .output 0)).compose (item9Assign p .carry 3),some MISByteCodec.E) := by
  dsimp only
  have P0 : get v (pc p+o p) 2=2 := P
  have O0 : get v (pc p) (o p)=cmpOp p+j := O
  have H0 : cmpOp p≠0 := by unfold cmpOp; omega
  have H1 : ¬cmpOp p+j<admitOp p := by unfold cmpOp admitOp; omega
  have H2 : cmpOp p+j≠admitOp p := by unfold cmpOp admitOp; omega
  have H3 : cmpOp p+j≠acqOp p := by unfold cmpOp acqOp; omega
  have H4 : ¬commitOp p<cmpOp p+j := by unfold cmpOp commitOp; omega
  have H5 : cmpOp p+j<readOp p := by unfold cmpOp readOp; omega
  have H6 : cmpOp p+j<writeOp p := by unfold cmpOp writeOp; omega
  change rf p v (9+2*d p) 4/4≠3 at C0
  change rf p v (9+2*d p) 4%4≠3 at C2
  by_cases K : j+1<p.digits <;> simp [source,P0,O0,Tag,Match,Live,ND,H0,H1,H2,H3,H4,H5,H6,C0,C2,K,
    show cmpOp p+j-cmpOp p=j by omega,item9Read,item9Off,item9Width,
    item9Assign,ReportDigitArithmetic.digit,ReportDigitArithmetic.cmp,cmp] <;> rfl

/-- The literal READ action, without asserting that the sample or
    the comparison/carry is correct yet. -/
private theorem item9_read_action (p : Params) (v : BitVec p.w) (t : Tok)
    (j : Nat) (J : j<p.digits)
    (P : sourcePhase p v=2) (O : sourceOpcode p v=readOp p+j)
    (Tag : t.tag=3) (Match : t.opcode=readOp p+j)
    (Live : t.fault=false) (ND : t.outcome≠1)
    (C0 : item9Read p v .input/4≠3) (C2 : item9Read p v .input%4≠3)
    (D0 : item9Read p v .output/4≠3) (D2 : item9Read p v .output%4≠3) :
    let kd := ReportDigitArithmetic.digit p.beta j p.radius
    let compute := fun dg c k root =>
      if root then (0,k) else if c≠1 then (kd,k) else ((dg+k)%p.beta,(dg+k)/p.beta)
    let a := compute (t.payload/2^d p) (item9Read p v .input/4)
      (item9Read p v .carry/2) (bit (item9Read p v .heads) 2)
    let b := compute (t.payload%2^d p) (item9Read p v .input%4)
      (item9Read p v .carry%2) (bit (item9Read p v .heads) 0)
    let out := 4*ReportDigitArithmetic.cmp a.1 kd (item9Read p v .output/4)+
      ReportDigitArithmetic.cmp b.1 kd (item9Read p v .output%4)
    source p v t =
      ((((ctrl p 1 (writeOp p+j)).compose
        (item9Assign p .send (2^d p*a.1+b.1))).compose
        (item9Assign p .carry (2*a.2+b.2))).compose
        (item9Assign p .output out),some MISByteCodec.E) := by
  dsimp only
  have P0 : get v (pc p+o p) 2=2 := P
  have O0 : get v (pc p) (o p)=readOp p+j := O
  have H0 : readOp p≠0 := by unfold readOp; omega
  have H1 : ¬readOp p+j<admitOp p := by unfold readOp admitOp; omega
  have H2 : readOp p+j≠admitOp p := by unfold readOp admitOp; omega
  have H3 : readOp p+j≠acqOp p := by unfold readOp acqOp; omega
  have H4 : ¬commitOp p<readOp p+j := by unfold readOp commitOp; omega
  have H5 : ¬readOp p+j<readOp p := by omega
  have H6 : readOp p+j<writeOp p := by unfold readOp writeOp; omega
  change rf p v (9+2*d p) 4/4≠3 at C0
  change rf p v (9+2*d p) 4%4≠3 at C2
  change rf p v (5+2*d p) 4/4≠3 at D0
  change rf p v (5+2*d p) 4%4≠3 at D2
  by_cases L : rf p v (9+2*d p) 4/4=1 <;>
    by_cases R : rf p v (9+2*d p) 4%4=1 <;>
    simp [source,P0,O0,Tag,Match,Live,ND,H0,H1,H2,H3,H4,H5,H6,C0,C2,D0,D2,L,R,
    show readOp p+j-readOp p=j by omega,item9Read,item9Off,item9Width,
    item9Assign,ReportDigitArithmetic.digit,ReportDigitArithmetic.cmp,cmp]

theorem item9_acq_zero_cmp (p : Params) (v : BitVec p.w) (t : Tok)
    (P : sourcePhase p v=2) (O : sourceOpcode p v=acqOp p)
    (Tag : t.tag=3) (Match : t.opcode=acqOp p)
    (Live : t.fault=false) (ND : t.outcome≠1) :
    item9Read p ((liftSourcePatch p (source p v t).1).apply v) .input=0 := by
  rw [acq_source_success p v t P O Tag Match Live ND]
  unfold liftSourcePatch
  dsimp only
  rw [reset0_widen_apply]
  change item9Read p ((widen p (item9Assign p .input 0)).apply _) .input=0
  rw [item9_read_assign]
  simp [item9Width]

end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol
open ReportDigitArithmetic (digit cmpFold compareCode nextDigit readWriteFold updateDist)

structure ItemNineInputs where
  left : Nat
  right : Nat
  heads : Nat
  indices : Nat

def ItemNineInputs.leftRoot (I : ItemNineInputs) : Bool := bit I.heads 2
def ItemNineInputs.rightRoot (I : ItemNineInputs) : Bool := bit I.heads 0
def ItemNineInputs.prior (I : ItemNineInputs) : Nat := I.indices/2%2

def item9Left (p : Params) (I : ItemNineInputs) (j : Nat) :=
  readWriteFold p.beta p.radius I.left I.leftRoot
    (compareCode I.left p.radius) j

def item9Right (p : Params) (I : ItemNineInputs) (j : Nat) :=
  readWriteFold p.beta p.radius I.right I.rightRoot
    (compareCode I.right p.radius) j

def item9Inp (p : Params) (I : ItemNineInputs) (j : Nat) :=
  4*cmpFold p.beta p.radius I.left j+cmpFold p.beta p.radius I.right j

def item9Out (p : Params) (I : ItemNineInputs) (j : Nat) :=
  4*(item9Left p I j).outCmp+(item9Right p I j).outCmp

def item9Carry (p : Params) (I : ItemNineInputs) (j : Nat) :=
  2*(item9Left p I j).carry+(item9Right p I j).carry

def item9LNext (p : Params) (I : ItemNineInputs) (j : Nat) :=
  nextDigit p.beta p.radius I.left I.leftRoot (compareCode I.left p.radius)
    j (item9Left p I j).carry

def item9RNext (p : Params) (I : ItemNineInputs) (j : Nat) :=
  nextDigit p.beta p.radius I.right I.rightRoot (compareCode I.right p.radius)
    j (item9Right p I j).carry

def item9Send (p : Params) (I : ItemNineInputs) (j : Nat) :=
  2^d p*(item9LNext p I j).1+(item9RNext p I j).1

private theorem item9_cmp_lt (a b c : Nat) (C : c<3) :
    ReportDigitArithmetic.cmp a b c<3 := by
  unfold ReportDigitArithmetic.cmp
  split
  · decide
  · split
    · decide
    · exact C

private theorem item9_cmpFold_lt (beta r x j : Nat) :
    cmpFold beta r x j<3 := by
  induction j with
  | zero => change 0<3; decide
  | succ j IH => exact item9_cmp_lt _ _ _ IH

private theorem item9_next_bounds (beta r x : Nat) (a : Bool) (c j k : Nat)
    (B : 2≤beta) (K : k≤1) :
    (nextDigit beta r x a c j k).1<beta ∧
      (nextDigit beta r x a c j k).2≤1 := by
  unfold nextDigit
  split
  · exact ⟨by omega,K⟩
  · split
    · exact ⟨Nat.mod_lt _ (by omega),K⟩
    · have D : digit beta j x<beta := Nat.mod_lt _ (by omega)
      refine ⟨Nat.mod_lt _ (by omega),?_⟩
      apply Nat.div_le_of_le_mul
      simpa only [Nat.mul_one,Nat.one_mul] using (show digit beta j x+k≤beta by omega)

private theorem item9_fold_bounds (beta r x : Nat) (a : Bool) (c j : Nat)
    (B : 2≤beta) :
    (readWriteFold beta r x a c j).outCmp<3 ∧
      (readWriteFold beta r x a c j).carry≤1 := by
  induction j with
  | zero => change 0<3 ∧ 1≤1; decide
  | succ j IH =>
    have D := item9_next_bounds beta r x a c j
      (readWriteFold beta r x a c j).carry B IH.2
    exact ⟨item9_cmp_lt _ _ _ IH.1,D.2⟩

private theorem item9_inp_bounds (p : Params) (I : ItemNineInputs) (j : Nat) :
    item9Inp p I j<16 ∧
    item9Inp p I j/4=cmpFold p.beta p.radius I.left j ∧
    item9Inp p I j%4=cmpFold p.beta p.radius I.right j := by
  have L := item9_cmpFold_lt p.beta p.radius I.left j
  have R := item9_cmpFold_lt p.beta p.radius I.right j
  unfold item9Inp
  exact ⟨by omega,by omega,by omega⟩

private theorem item9_out_bounds (p : Params) (I : ItemNineInputs) (j : Nat)
    (B : 2≤p.beta) :
    item9Out p I j<16 ∧ item9Out p I j/4=(item9Left p I j).outCmp ∧
      item9Out p I j%4=(item9Right p I j).outCmp := by
  have L := (item9_fold_bounds p.beta p.radius I.left I.leftRoot
    (compareCode I.left p.radius) j B).1
  have R := (item9_fold_bounds p.beta p.radius I.right I.rightRoot
    (compareCode I.right p.radius) j B).1
  change (item9Left p I j).outCmp<3 at L
  change (item9Right p I j).outCmp<3 at R
  unfold item9Out
  exact ⟨by omega,by omega,by omega⟩

private theorem item9_carry_bounds (p : Params) (I : ItemNineInputs) (j : Nat)
    (B : 2≤p.beta) :
    item9Carry p I j<4 ∧ item9Carry p I j/2=(item9Left p I j).carry ∧
      item9Carry p I j%2=(item9Right p I j).carry := by
  have L := (item9_fold_bounds p.beta p.radius I.left I.leftRoot
    (compareCode I.left p.radius) j B).2
  have R := (item9_fold_bounds p.beta p.radius I.right I.rightRoot
    (compareCode I.right p.radius) j B).2
  change (item9Left p I j).carry≤1 at L
  change (item9Right p I j).carry≤1 at R
  unfold item9Carry
  exact ⟨by omega,by omega,by omega⟩

private theorem item9_send_bound (p : Params) (I : ItemNineInputs) (j : Nat)
    (B : 2≤p.beta) : item9Send p I j<2^(2*d p) := by
  have L := (item9_fold_bounds p.beta p.radius I.left I.leftRoot
    (compareCode I.left p.radius) j B).2
  have R := (item9_fold_bounds p.beta p.radius I.right I.rightRoot
    (compareCode I.right p.radius) j B).2
  have A := (item9_next_bounds p.beta p.radius I.left I.leftRoot
    (compareCode I.left p.radius) j _ B L).1
  have C := (item9_next_bounds p.beta p.radius I.right I.rightRoot
    (compareCode I.right p.radius) j _ B R).1
  have H : p.beta≤2^d p := power_of_ell p.beta
  exact item9_pack_bound p _ _ (Nat.lt_of_lt_of_le A H) (Nat.lt_of_lt_of_le C H)

/-- Individual emitted digit theorem, not merely equality of the
    sum at the final index. Compare the two consecutive prefixes. -/
theorem item9_emitted_digit (beta r x : Nat) (a : Bool) (j : Nat)
    (B : 2≤beta) :
    (nextDigit beta r x a (compareCode x r) j
      (readWriteFold beta r x a (compareCode x r) j).carry).1 =
      digit beta j (updateDist r a x) := by
  have A := (ReportDigitArithmetic.emitted_prefix beta r x a j B).1
  have C := (ReportDigitArithmetic.emitted_prefix beta r x a (j+1) B).1
  change (readWriteFold beta r x a (compareCode x r) j).value+
    beta^j*(nextDigit beta r x a (compareCode x r) j
      (readWriteFold beta r x a (compareCode x r) j).carry).1=
    updateDist r a x%beta^(j+1) at C
  rw [A,ReportDigitArithmetic.split_prefix] at C
  have E := Nat.add_left_cancel C
  -- CHECK: core Nat cancellation; same positive-factor cancellation
  -- as ReportDigitArithmetic.split_prefix/increment_step.
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) E

theorem item9_send_digits (p : Params) (I : ItemNineInputs) (j : Nat)
    (B : 2≤p.beta) :
    item9Send p I j=
      2^d p*digit p.beta j (updateDist p.radius I.leftRoot I.left)+
      digit p.beta j (updateDist p.radius I.rightRoot I.right) := by
  unfold item9Send item9LNext item9RNext item9Left item9Right
  rw [item9_emitted_digit _ _ _ _ _ B,item9_emitted_digit _ _ _ _ _ B]

inductive ItemNineStage where
  | cmp (j : Nat)
  | read (j : Nat)
  | write (j : Nat)
  | seal
  | commit

def item9Code (p : Params) : ItemNineStage→Nat
  | .cmp j => cmpOp p+j
  | .read j => readOp p+j
  | .write j => writeOp p+j
  | .seal => sealOp p
  | .commit => commitOp p

def item9StageFit (p : Params) : ItemNineStage→Prop
  | .cmp j | .read j | .write j => j<p.digits
  | .seal | .commit => True

def item9Fields (p : Params) (I : ItemNineInputs) (c : ItemNineStage)
    (v : ItemNineField→Nat) : Prop :=
  v .heads=I.heads ∧ v .indices=I.indices ∧
    match c with
    | .cmp j => v .input=item9Inp p I j
    | .read j => v .input=item9Inp p I p.digits ∧
        v .output=item9Out p I j ∧ v .carry=item9Carry p I j
    | .write j => v .input=item9Inp p I p.digits ∧
        v .output=item9Out p I (j+1) ∧ v .carry=item9Carry p I (j+1) ∧
        v .send=item9Send p I j
    | .seal | .commit => v .input=item9Inp p I p.digits ∧
        v .output=item9Out p I p.digits ∧ v .carry=item9Carry p I p.digits

def ItemNineAt (p : Params) (I : ItemNineInputs) (op : Nat)
    (v : ItemNineField→Nat) : Prop :=
  ∃ c, item9StageFit p c ∧ op=item9Code p c ∧ item9Fields p I c v

def ItemNineReply (p : Params) (I : ItemNineInputs) (op : Nat) (t : Tok) : Prop :=
  ∀ j,j<p.digits→(op=cmpOp p+j ∨ op=readOp p+j) →
    t.payload/2^d p=digit p.beta j I.left ∧
    t.payload%2^d p=digit p.beta j I.right

theorem item9_seed (p : Params) (I : ItemNineInputs) (v : BitVec p.w)
    (M : 0<p.digits) (H : item9Read p v .heads=I.heads)
    (X : item9Read p v .indices=I.indices)
    (Z : item9Read p v .input=0) :
    ItemNineAt p I (cmpOp p) (item9Read p v) := by
  exact ⟨.cmp 0,M,by simp [item9Code],H,X,Z⟩

private theorem item9_preview_unique {m a b c : Nat}
    (H : PreviewNextOp m a b) (K : PreviewNextOp m a c) : b=c := by
  generalize E : a = a' at K
  cases H <;> cases K <;> omega

private theorem item9_cmp_next (p : Params) (j : Nat) (J : j<p.digits) :
    PreviewNextOp p.digits (cmpOp p+j)
      (if j+1<p.digits then cmpOp p+(j+1) else readOp p) := by
  split
  · rename_i H
    have K : cmpOp p+j+1<2*p.digits+3 := by unfold cmpOp; omega
    simpa [Nat.add_assoc] using (PreviewNextOp.linear K)
  · have E : cmpOp p+j=2*p.digits+2 := by unfold cmpOp; omega
    rw [E]
    exact PreviewNextOp.cmpLast (by omega)

private theorem item9_write_next (p : Params) (j : Nat) (J : j<p.digits) :
    PreviewNextOp p.digits (writeOp p+j)
      (if j+1<p.digits then readOp p+(j+1) else sealOp p) := by
  split
  · rename_i H
    exact PreviewNextOp.writeRead H
  · exact PreviewNextOp.writeSeal (by omega)

/-- Main literal arithmetic row induction. It deliberately has no
    physical digit-bank hypothesis; the WRITE staging supplier is
    separate. All field equalities follow from the actual source patch. -/
theorem item9_advance (p : Params) (I : ItemNineInputs) (v : BitVec p.w)
    (t : Tok) (op next : Nat) (B : 2≤p.beta)
    (XL : I.left<p.beta^p.digits) (XR : I.right<p.beta^p.digits)
    (R : p.radius<p.beta^p.digits)
    (P : sourcePhase p v=2) (O : sourceOpcode p v=op)
    (Tag : t.tag=3) (Match : t.opcode=op) (Live : t.fault=false) (ND : t.outcome≠1)
    (N : PreviewNextOp p.digits op next)
    (A : ItemNineAt p I op (item9Read p v))
    (Read : ItemNineReply p I op t) :
    ItemNineAt p I next
      (item9Read p ((liftSourcePatch p (source p v t).1).apply v)) := by
  obtain ⟨c,Fit,E,H,X,C⟩ := A
  rw [E] at O Match N Read
  have FC0 := ReportDigitArithmetic.full_cmp p.beta p.digits p.radius I.left B XL R
  have FC2 := ReportDigitArithmetic.full_cmp p.beta p.digits p.radius I.right B XR R
  cases c with
  | cmp j =>
    change j<p.digits at Fit
    change item9Read p v .input=item9Inp p I j at C
    have IN := item9_inp_bounds p I j
    have L := item9_cmpFold_lt p.beta p.radius I.left j
    have U := item9_cmpFold_lt p.beta p.radius I.right j
    obtain ⟨DL,DR⟩ := Read j Fit (.inl rfl)
    have Patch := item9_cmp_action p v t j Fit P O Tag Match Live ND
      (by rw [C,IN.2.1]; omega) (by rw [C,IN.2.2]; omega)
    dsimp only at Patch
    rw [C,IN.2.1,IN.2.2,DL,DR] at Patch
    change source p v t=
      (if j+1<p.digits then
        ((ctrl p 1 (cmpOp p+j+1)).compose (item9Assign p .input (item9Inp p I (j+1))),some MISByteCodec.E)
      else
        ((((ctrl p 1 (readOp p)).compose (item9Assign p .input (item9Inp p I (j+1)))).compose
          (item9Assign p .output 0)).compose (item9Assign p .carry 3),some MISByteCodec.E)) at Patch
    have U1 := (item9_inp_bounds p I (j+1)).1
    have NN := item9_preview_unique N (item9_cmp_next p j Fit)
    by_cases Last : j+1<p.digits
    · rw [if_pos Last] at Patch NN
      refine ⟨.cmp (j+1),Last,NN,?_⟩
      rw [Patch]
      unfold liftSourcePatch
      dsimp only
      simp only [reset0_widen_apply,item9Fields,item9_read_assign,item9_read_ctrl]
      simp [H,X,item9Width,Nat.mod_eq_of_lt U1]
    · have J : j+1=p.digits := by omega
      rw [if_neg Last] at Patch NN
      refine ⟨.read 0,by change 0<p.digits; omega,by simpa [item9Code] using NN,?_⟩
      rw [Patch]
      unfold liftSourcePatch
      dsimp only
      simp only [reset0_widen_apply,item9Fields,item9_read_assign,item9_read_ctrl]
      rw [J] at U1
      simp [H,X,item9Width,Nat.mod_eq_of_lt U1,J,item9Out,item9Carry,item9Left,item9Right,readWriteFold]
  | read j =>
    change j<p.digits at Fit
    obtain ⟨In,Out,Carry⟩ := C
    have IN := item9_inp_bounds p I p.digits
    have OU := item9_out_bounds p I j B
    have CA := item9_carry_bounds p I j B
    have L0 := item9_cmpFold_lt p.beta p.radius I.left p.digits
    have R0 := item9_cmpFold_lt p.beta p.radius I.right p.digits
    have L1 := (item9_fold_bounds p.beta p.radius I.left I.leftRoot
      (compareCode I.left p.radius) j B).1
    have R1 := (item9_fold_bounds p.beta p.radius I.right I.rightRoot
      (compareCode I.right p.radius) j B).1
    obtain ⟨DL,DR⟩ := Read j Fit (.inr rfl)
    have Patch := item9_read_action p v t j Fit P O Tag Match Live ND
      (by rw [In,IN.2.1]; omega) (by rw [In,IN.2.2]; omega)
      (by rw [Out,OU.2.1]; exact Nat.ne_of_lt L1)
      (by rw [Out,OU.2.2]; exact Nat.ne_of_lt R1)
    dsimp only at Patch
    rw [In,IN.2.1,IN.2.2,FC0,FC2,Out,OU.2.1,OU.2.2,
      Carry,CA.2.1,CA.2.2,H,DL,DR] at Patch
    -- The nextDigit and readWriteFold equations are literal: this
    -- change is a definitional reduction, not an arithmetic guess.
    change source p v t=
      ((((ctrl p 1 (writeOp p+j)).compose (item9Assign p .send (item9Send p I j))).compose
        (item9Assign p .carry (item9Carry p I (j+1)))).compose
        (item9Assign p .output (item9Out p I (j+1))),some MISByteCodec.E) at Patch
    have NN := item9_preview_unique N (PreviewNextOp.readWrite Fit)
    have SB := item9_send_bound p I j B
    have CB := (item9_carry_bounds p I (j+1) B).1
    have OB := (item9_out_bounds p I (j+1) B).1
    refine ⟨.write j,Fit,NN,?_⟩
    rw [Patch]
    unfold liftSourcePatch
    dsimp only
    simp only [reset0_widen_apply,item9Fields,item9_read_assign,item9_read_ctrl]
    simp [H,X,In,item9Width,Nat.mod_eq_of_lt SB,Nat.mod_eq_of_lt CB,Nat.mod_eq_of_lt OB]
  | write j =>
    change j<p.digits at Fit
    obtain ⟨In,Out,Carry,Send⟩ := C
    have W : writeOp p≤sourceOpcode p v := by rw [O]; exact Nat.le_add_right _ _
    have U : sourceOpcode p v≤sealOp p := by rw [O]; change writeOp p+j≤sealOp p; unfold writeOp sealOp; omega
    have Patch := write_seal_ack_action p v t P W U Tag (Match.trans O.symm) Live ND
    have NN := item9_preview_unique N (item9_write_next p j Fit)
    by_cases Last : j+1<p.digits
    · rw [if_pos Last] at NN
      refine ⟨.read (j+1),Last,NN,?_⟩
      rw [Patch]
      unfold liftSourcePatch
      dsimp only
      simp [item9Fields,item9_read_ctrl,H,X,In,Out,Carry]
    · have J : j+1=p.digits := by omega
      rw [if_neg Last] at NN
      refine ⟨.seal,trivial,NN,?_⟩
      rw [Patch]
      unfold liftSourcePatch
      dsimp only
      simp [item9Fields,item9_read_ctrl,H,X,In,Out,Carry,J]
  | «seal» =>
    have W : writeOp p≤sourceOpcode p v := by rw [O]; change writeOp p≤sealOp p; unfold writeOp sealOp; omega
    have U : sourceOpcode p v≤sealOp p := by rw [O]; exact Nat.le_refl _
    have Patch := write_seal_ack_action p v t P W U Tag (Match.trans O.symm) Live ND
    have NN := item9_preview_unique N (PreviewNextOp.sealCommit (t:=p.digits))
    refine ⟨.commit,trivial,NN,?_⟩
    rw [Patch]
    unfold liftSourcePatch
    dsimp only
    simpa [item9Fields,item9_read_ctrl] using (show item9Fields p I .seal (item9Read p v) from ⟨H,X,C⟩)
  | «commit» =>
    have Impossible : False := by
      change PreviewNextOp p.digits (commitOp p) next at N
      generalize E0 : commitOp p = a at N
      unfold commitOp at E0
      cases N <;> omega
    exact Impossible.elim

theorem item9_at_write (p : Params) (I : ItemNineInputs) (v : BitVec p.w)
    (j : Nat) (J : j<p.digits)
    (H : ItemNineAt p I (writeOp p+j) (item9Read p v)) :
    ancestrySendDigits p v=item9Send p I j := by
  obtain ⟨c,F,E,_,_,C⟩ := H
  cases c with
  | cmp k =>
    simp only [item9Code,item9StageFit] at E F
    unfold writeOp cmpOp at E
    omega
  | read k =>
    simp only [item9Code,item9StageFit] at E F
    unfold writeOp readOp at E
    omega
  | write k =>
    simp only [item9Code,item9StageFit] at E F
    have Eq : j=k := by omega
    subst j
    exact C.2.2.2
  | «seal» =>
    simp only [item9Code] at E
    unfold writeOp sealOp at E
    omega
  | «commit» =>
    simp only [item9Code] at E
    unfold writeOp commitOp at E
    omega

theorem item9_at_seal (p : Params) (I : ItemNineInputs) (v : BitVec p.w)
    (H : ItemNineAt p I (sealOp p) (item9Read p v)) :
    item9Read p v .indices=I.indices ∧ item9Read p v .output=item9Out p I p.digits := by
  obtain ⟨c,F,E,_,X,C⟩ := H
  cases c <;> simp only [item9Code,item9StageFit] at E F
  · unfold sealOp cmpOp at E; omega
  · unfold sealOp readOp at E; omega
  · unfold sealOp writeOp at E; omega
  · exact ⟨X,C.2.1⟩
  · unfold sealOp commitOp at E; omega

end L4.ReportByteRows
namespace L4.ReportByteRows
theorem item9_out_components (p : Params) (I : ItemNineInputs) (j : Nat)
    (B : 2≤p.beta) :
    item9Out p I j/4=(item9Left p I j).outCmp ∧
      item9Out p I j%4=(item9Right p I j).outCmp :=
  (item9_out_bounds p I j B).2
end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

/-- A real ISSUE ADMIT emits a healthy forward packet with payload zero. -/
theorem fast_admit_issue_packet (p : Params) (v : BitVec p.w) (t : Tok)
    (P : sourcePhase p v=1) (O : sourceOpcode p v=admitOp p) :
    (source p v t).2=some ({tag:=2,opcode:=admitOp p,payload:=0}:Tok) := by
  have H1 : ¬commitOp p<admitOp p := by unfold commitOp admitOp; omega
  have H2 : admitOp p≠acqOp p := by unfold admitOp acqOp; omega
  have H3 : ¬cmpOp p≤admitOp p := by unfold admitOp cmpOp; omega
  have H4 : ¬writeOp p≤admitOp p := by unfold admitOp writeOp; omega
  have H5 : ¬sealOp p≤admitOp p := by unfold admitOp sealOp; omega
  unfold sourcePhase at P
  unfold sourceOpcode at O
  simp [source,P,O,H1,H2,H3,H4,H5]

end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

theorem fast_admit_off_roundtrip (p : Params) (q : Nat) (Q : q<2) :
    decode p false (resetTokenWire p
      ({tag:=2,opcode:=admitOp p,payload:=q} : Tok)) =
      {tag:=2,opcode:=admitOp p,payload:=q} := by
  let t : Tok := {tag:=2,opcode:=admitOp p,payload:=q}
  have O : admitOp p<2^o p := by
    have B := power_of_ell (5+4*p.digits)
    unfold o admitOp
    omega
  have P : q<2^payW p := Nat.lt_of_lt_of_le Q
    (Nat.pow_le_pow_right (show 1≤(2:Nat) by decide)
      (by unfold payW; omega : 1≤payW p))
  have Fit : RankFits p t :=
    ⟨by change 2<4; decide,O,P,by change 0<8; decide,by change 0<4; decide⟩
  have B := rReadFields p t Fit
  have F0 : (resetTokenWire p t).getLsbD (6+o p+payW p)=false := by
    rw [rGet_bit,B.2.1]
    rfl
  have A : admitOp p≠acqOp p := by unfold admitOp acqOp; omega
  have C : admitOp p≠commitOp p := by unfold admitOp commitOp; omega
  have D : ¬commitOp p<admitOp p := by unfold admitOp commitOp; omega
  have E : ¬cmpOp p≤admitOp p := by unfold admitOp cmpOp; omega
  have W : ¬writeOp p≤admitOp p := by unfold admitOp writeOp; omega
  have V : ¬sealOp p≤admitOp p := by unfold admitOp sealOp; omega
  change decode p false (resetTokenWire p t)=t
  simp [decode,B.1,B.2.2.1,B.2.2.2.1,B.2.2.2.2.1,
    B.2.2.2.2.2.2,F0,t,A,C,D,E,W,V,Nat.mod_eq_of_lt Q]

theorem fast_off_route (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (j k : Fin 3) (q : Nat)
    (H : publicationToken p hu u j=
      ({tag:=2,opcode:=admitOp p,payload:=q} : Tok))
    (G : rankGate p hu u j=false) (G' : rankGate p hv v k=false) :
    rankRouteR p hu hv u v j k =
      some ({tag:=2,opcode:=admitOp p,payload:=q} : Tok) := by
  have H0 : healthyAdmit p (publicationToken p hu u j) := by rw [H]; exact ⟨rfl,rfl,rfl⟩
  have R : rankReady p hu u j=true :=
    (rankReady_iff p hu u j).mpr ⟨H0.1,fun A=>by rw [G] at A; exact Bool.noConfusion A.2.1⟩
  change oldK p hu u j=_ at H
  change gate p hu u j=false at G
  change gate p hv v k=false at G'
  have A : admitOp p≠commitOp p := by unfold admitOp commitOp; omega
  have B : admitOp p≠acqOp p := by unfold admitOp acqOp; omega
  have C : admitOp p≠0 := by unfold admitOp; omega
  have D : ¬cmpOp p≤admitOp p := by unfold admitOp cmpOp; omega
  have E : ¬writeOp p≤admitOp p := by unfold admitOp writeOp; omega
  have F0 : admitOp p≠sealOp p := by unfold admitOp sealOp; omega
  unfold rankRouteR
  dsimp only
  rw [if_pos R,H]
  simp [effect,parked,arrival,G,G',A,B,C,D,E,F0]

theorem fast_off_norm (p : Params) (side : Nat) (w : BitVec (tokenW p))
    (H : healthyAdmit p (decode p false w)) :
    rankNormWire p side false w=w := by
  simp [rankNormWire,rankNormIntent,H.1,H.2.1,H.2.2]

theorem fast_admit_on_roundtrip (p : Params) (q r : Nat)
    (Q : q<2) (R : 1≤r) (S : r≤5) :
    decode p true (resetTokenWire p
      ({tag:=2,opcode:=admitOp p,payload:=q,race:=r} : Tok)) =
      {tag:=2,opcode:=admitOp p,payload:=q,race:=r} :=
  rAdmit_roundtrip p q r Q R S

theorem fast_arrive_route (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (j k : Fin 3) (q : Nat)
    (H : publicationToken p hu u j=
      ({tag:=2,opcode:=admitOp p,payload:=q} : Tok))
    (G : rankGate p hu u j=false) (G' : rankGate p hv v k=true) :
    rankRouteR p hu hv u v j k =
      some ({tag:=2,opcode:=admitOp p,payload:=q,race:=1} : Tok) := by
  have H0 : healthyAdmit p (publicationToken p hu u j) := by rw [H]; exact ⟨rfl,rfl,rfl⟩
  have R : rankReady p hu u j=true :=
    (rankReady_iff p hu u j).mpr ⟨H0.1,fun A=>by rw [G] at A; exact Bool.noConfusion A.2.1⟩
  change oldK p hu u j=_ at H
  change gate p hu u j=false at G
  change gate p hv v k=true at G'
  have A : admitOp p≠commitOp p := by unfold admitOp commitOp; omega
  have B : admitOp p≠acqOp p := by unfold admitOp acqOp; omega
  have C : admitOp p≠0 := by unfold admitOp; omega
  have D : ¬cmpOp p≤admitOp p := by unfold admitOp cmpOp; omega
  have E : ¬writeOp p≤admitOp p := by unfold admitOp writeOp; omega
  have F0 : admitOp p≠sealOp p := by unfold admitOp sealOp; omega
  unfold rankRouteR
  dsimp only
  rw [if_pos R,H]
  simp [effect,parked,arrival,G,G',A,B,C,D,E,F0]

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol
theorem fast_depart_route (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (j k : Fin 3)
    (H : healthyAdmit p (publicationToken p hu u j))
    (G : rankGate p hu u j=true)
    (G' : rankGate p hv v k=false)
    (R : 4≤(publicationToken p hu u j).race) :
    rankRouteR p hu hv u v j k =
      some {(publicationToken p hu u j) with
        race:=0,payload:=(publicationToken p hu u j).race-4} := by
  have Ready : rankReady p hu u j=true :=
    (rankReady_iff p hu u j).mpr ⟨H.1,fun A=>by omega⟩
  change healthyAdmit p (oldK p hu u j) at H
  change gate p hu u j=true at G
  change gate p hv v k=false at G'
  change _ = some {(oldK p hu u j) with race:=0,payload:=(oldK p hu u j).race-4}
  unfold rankRouteR
  dsimp only
  rw [if_pos Ready,admit_departure_effect p u v hu hv j (some k)
    (drWin p hu u j) (oldK p hu u j) H G]
  simp [arrival,G']

theorem fast_admit_consume_control (p : Params) (v : BitVec p.w) (t : Tok)
    (P : sourcePhase p v=2) (O : sourceOpcode p v=admitOp p)
    (T : t.tag=3) (A : t.opcode=admitOp p)
    (F0 : t.fault=false) (Q : t.outcome=0) :
    let y := (liftSourcePatch p (source p v t).1).apply v
    (sourcePhase p y,sourceOpcode p y)=
      (1,if t.payload=1 then acqOp p else 0) ∧
      (source p v t).2=some MISByteCodec.E := by
  dsimp only
  rw [admit_source_consume p v t P O T A F0 Q]
  by_cases H : t.payload=1
  · rw [if_pos H,if_pos H]
    exact ⟨prelaunch_ctrl_write p v (acqOp p)
      (by unfold acqOp; omega),rfl⟩
  · rw [if_neg H,if_neg H]
    exact ⟨prelaunch_restart_controls p v,rfl⟩

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol ReportDigitArithmetic
set_option maxRecDepth 12000
set_option maxHeartbeats 6000000

private theorem item9_assign_pc_frame (p : Params) (q : Patch (workW p))
    (k : ItemNineField) (x : Nat) (v : BitVec p.w) :
    prePostPC p (q.compose (item9Assign p k x)) v=prePostPC p q v := by
  cases k <;> exact prelaunch_post_sf p q _ _ _ (by simp [item9Off,item9Width] <;> omega) v

/-- An authentic healthy matched positive reply cannot take the source's
retry branch in a certified arithmetic file. CMP/READ validity is
proved from the actual comparison fields, not assumed as a positive
successor opcode. COMMIT's intentional terminal reset is out of scope. -/
theorem item9_good_reply_no_retry (p : Params) (I : ItemNineInputs)
    (v : BitVec p.w) (t : Tok) (op : Nat) (B : 2≤p.beta)
    (P : sourcePhase p v=2) (O : sourceOpcode p v=op)
    (Tag : t.tag=3) (Match : t.opcode=op) (Live : t.fault=false) (ND : t.outcome≠1)
    (U : op<commitOp p)
    (A : ItemNineAt p I op (item9Read p v)) :
    (acqSourcePC p v t).2≠0 := by
  obtain ⟨c,Fit,E,_,_,F⟩ := A
  rw [E] at O Match U
  cases c with
  | cmp j =>
    change j<p.digits at Fit
    change item9Read p v .input=item9Inp p I j at F
    have IN := item9_inp_bounds p I j
    have L := item9_cmpFold_lt p.beta p.radius I.left j
    have R := item9_cmpFold_lt p.beta p.radius I.right j
    have Patch := item9_cmp_action p v t j Fit P O Tag Match Live ND
      (by rw [F,IN.2.1]; omega) (by rw [F,IN.2.2]; omega)
    change (prePostPC p (source p v t).1 v).2≠0
    rw [Patch]
    split
    · dsimp only
      rw [item9_assign_pc_frame,prelaunch_ctrl_write]
      · simp [cmpOp]
      · unfold cmpOp; omega
    · dsimp only
      rw [item9_assign_pc_frame,item9_assign_pc_frame,item9_assign_pc_frame,prelaunch_ctrl_write]
      · simp [readOp]
      · unfold readOp; omega
  | read j =>
    change j<p.digits at Fit
    obtain ⟨In,Out,_⟩ := F
    have IN := item9_inp_bounds p I p.digits
    have OU := item9_out_bounds p I j B
    have L := item9_cmpFold_lt p.beta p.radius I.left p.digits
    have R := item9_cmpFold_lt p.beta p.radius I.right p.digits
    have HL := (item9_fold_bounds p.beta p.radius I.left I.leftRoot (compareCode I.left p.radius) j B).1
    have HR := (item9_fold_bounds p.beta p.radius I.right I.rightRoot (compareCode I.right p.radius) j B).1
    have Patch := item9_read_action p v t j Fit P O Tag Match Live ND
      (by rw [In,IN.2.1]; omega) (by rw [In,IN.2.2]; omega)
      (by rw [Out,OU.2.1]; exact Nat.ne_of_lt HL)
      (by rw [Out,OU.2.2]; exact Nat.ne_of_lt HR)
    change (prePostPC p (source p v t).1 v).2≠0
    rw [Patch]
    dsimp only
    rw [item9_assign_pc_frame,item9_assign_pc_frame,item9_assign_pc_frame,prelaunch_ctrl_write]
    · simp [writeOp]
    · unfold writeOp; omega
  | write j =>
    change j<p.digits at Fit
    change sourceOpcode p v=writeOp p+j at O
    change t.opcode=writeOp p+j at Match
    have Low : writeOp p≤sourceOpcode p v := by rw [O]; omega
    have High : sourceOpcode p v≤sealOp p := by rw [O]; unfold writeOp sealOp; omega
    have H := write_seal_ack_control p v t P Low High Tag (Match.trans O.symm) Live ND
    rw [H,O]
    change writeSealNext p (writeOp p+j)≠0
    unfold writeSealNext
    rw [if_pos (by unfold writeOp sealOp; omega)]
    split
    · unfold readOp
      omega
    · unfold sealOp
      omega
  | «seal» =>
    change sourceOpcode p v=sealOp p at O
    change t.opcode=sealOp p at Match
    have H := write_seal_ack_control p v t P (by rw [O]; unfold writeOp sealOp; omega)
      (by rw [O]; exact Nat.le_refl _) Tag (Match.trans O.symm) Live ND
    rw [H,O]
    change writeSealNext p (sealOp p)≠0
    unfold writeSealNext
    rw [if_neg (Nat.lt_irrefl _)]
    unfold commitOp
    omega
  | «commit» =>
    change commitOp p<commitOp p at U
    omega

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol ReportDigitArithmetic
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000

/-- At a certified arithmetic ISSUE, the actual source emits a forward
packet. WRITE's two base digits and the late descriptor's comparison
trits are valid by the source recurrence. -/
theorem item9_good_issue_emits_forward (p : Params) (I : ItemNineInputs)
    (v : BitVec p.w) (old : Tok) (B : 2≤p.beta) (P : sourcePhase p v=1)
    (A : ItemNineAt p I (sourceOpcode p v) (item9Read p v)) :
    ∃ t,(source p v old).2=some t ∧ t.tag=2 := by
  let op := sourceOpcode p v
  have Range : cmpOp p≤op ∧ op≤commitOp p := by
    obtain ⟨c,J,E,_,_,_⟩ := A
    change op=item9Code p c at E
    rw [E]
    cases c <;> simp only [item9Code,item9StageFit,cmpOp,readOp,writeOp,sealOp,commitOp] at J ⊢ <;> omega
  have DW : writeOp p≤op → op<sealOp p →
      digitPair p (ancestrySendDigits p v)=true := by
    intro L U
    let j := op-writeOp p
    have E : op=writeOp p+j := by dsimp [j]; omega
    have J : j<p.digits := by unfold j writeOp sealOp at *; omega
    have W : ItemNineAt p I (writeOp p+j) (item9Read p v) := E ▸ A
    have V := item9_at_write p I v j J W
    have L0 := (item9_fold_bounds p.beta p.radius I.left I.leftRoot
      (compareCode I.left p.radius) j B).2
    have R0 := (item9_fold_bounds p.beta p.radius I.right I.rightRoot
      (compareCode I.right p.radius) j B).2
    have L1 := (item9_next_bounds p.beta p.radius I.left I.leftRoot
      (compareCode I.left p.radius) j (item9Left p I j).carry B L0).1
    have R1 := (item9_next_bounds p.beta p.radius I.right I.rightRoot
      (compareCode I.right p.radius) j (item9Right p I j).carry B R0).1
    change (item9LNext p I j).1<p.beta at L1
    change (item9RNext p I j).1<p.beta at R1
    have DL : (item9LNext p I j).1<2^d p := Nat.lt_of_lt_of_le L1 (indexed_beta_bound p)
    have DR : (item9RNext p I j).1<2^d p := Nat.lt_of_lt_of_le R1 (indexed_beta_bound p)
    have F := (item9_pack_halves p (item9LNext p I j).1 (item9RNext p I j).1 DR).1
    rw [V]
    unfold digitPair
    change ((decide (item9Send p I j%2^d p<p.beta)) &&
      (decide ((item9Send p I j/2^d p)%2^d p<p.beta)))=true
    change item9Send p I j/2^d p=(item9LNext p I j).1 at F
    have M : item9Send p I j%2^d p=(item9RNext p I j).1 :=
      (item9_pack_halves p (item9LNext p I j).1 (item9RNext p I j).1 DR).2
    rw [F,M,Nat.mod_eq_of_lt DL]
    simp [L1,R1]
  have Late : sealOp p≤op →
      item9Read p v .output/4≠3 ∧ item9Read p v .output%4≠3 := by
    intro L
    have EQ : item9Read p v .output=item9Out p I p.digits := by
      obtain ⟨c,Fit,E,_,_,C⟩ := A
      change op=item9Code p c at E
      rw [E] at L
      cases c with
      | cmp j => change j<p.digits at Fit; change sealOp p≤cmpOp p+j at L; unfold sealOp cmpOp at L; omega
      | read j => change j<p.digits at Fit; change sealOp p≤readOp p+j at L; unfold sealOp readOp at L; omega
      | write j => change j<p.digits at Fit; change sealOp p≤writeOp p+j at L; unfold sealOp writeOp at L; omega
      | «seal» => exact C.2.1
      | «commit» => exact C.2.1
    have H := item9_out_bounds p I p.digits B
    have L0 := (item9_fold_bounds p.beta p.radius I.left I.leftRoot
      (compareCode I.left p.radius) p.digits B).1
    have R0 := (item9_fold_bounds p.beta p.radius I.right I.rightRoot
      (compareCode I.right p.radius) p.digits B).1
    rw [EQ,H.2.1,H.2.2]
    exact ⟨Nat.ne_of_lt L0,Nat.ne_of_lt R0⟩
  have WriteNo : (decide (writeOp p≤op) && decide (op<sealOp p) &&
      !digitPair p (ancestrySendDigits p v))=false := by
    by_cases L : writeOp p≤op <;> by_cases U : op<sealOp p <;> simp [L,U,DW]
  have LateNo : (decide (sealOp p≤op) && (item9Read p v .output/4==3 ||
      item9Read p v .output%4==3))=false := by
    by_cases L : sealOp p≤op
    · have N := Late L
      simp [L,beq_false_of_ne N.1,beq_false_of_ne N.2]
    · simp [L]
  have Q : ¬commitOp p<op := Nat.not_lt_of_ge Range.2
  have P0 : get v (pc p+o p) 2=1 := P
  have E : get v (pc p) (o p)=op := rfl
  unfold source
  dsimp only
  simp only [P0,E,Q,decide_false,show ((1:Nat)==0)=false by decide,
    show ((1:Nat)==3)=false by decide,Bool.false_or,Bool.false_eq_true,
    if_false,beq_self_eq_true,if_true]
  change ∃ t : Tok,((if
    (decide (writeOp p≤op) && decide (op<sealOp p) && !digitPair p (ancestrySendDigits p v)) ||
    (decide (sealOp p≤op) && (item9Read p v .output/4==3 || item9Read p v .output%4==3))
    then _ else _):Patch (workW p) × Option Tok).2=some t ∧ t.tag=2
  rw [WriteNo,LateNo]
  exact ⟨_,rfl,rfl⟩

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol

theorem deny_admit_terminal_wire (p : Params) (hu hv : Bool) (u v : BitVec p.w) (j : Fin 3)
    (D : reset0Destination hv j=none) (G : rankGate p hu u j=false)
    (A : publicationToken p hu u j=({tag:=2,opcode:=admitOp p}:Tok)) :
    resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j=resetTokenWire p ({tag:=3,opcode:=admitOp p}:Tok) := by
  have R : rankReady p hu u j=true := (rankReady_iff _ _ _ _).mpr
    ⟨by rw [A],fun H=>Bool.noConfusion (G.symm.trans H.2.1)⟩
  have G0 : gate p hu u j=false := G
  have Z : admitOp p≠0 := by unfold admitOp; omega
  have C : admitOp p≠commitOp p := by unfold admitOp commitOp; omega
  have Q : admitOp p≠acqOp p := by unfold admitOp acqOp; omega
  have L : ¬cmpOp p≤admitOp p := by unfold admitOp cmpOp; omega
  have W : ¬writeOp p≤admitOp p := by unfold admitOp writeOp; omega
  have H : admitOp p≠sealOp p := by unfold admitOp sealOp; omega
  rw [rank_row_left,D]
  unfold rankRouteL
  simp only [R,if_true,Option.elim]
  change oldK p hu u j=({tag:=2,opcode:=admitOp p}:Tok) at A
  rw [A]
  simp [effect,terminal,parked,G0,Z,C,Q,L,W,H]

end L4.ReportByteRows
namespace L4.ReportByteRows
open AllSizeProtocol
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

def earlyF (a q r : Nat) : Tok :=
  {tag:=2, opcode:=a, payload:=q, race:=r}
def earlyD (a q : Nat) : Tok :=
  {tag:=3, opcode:=a, payload:=q}
def earlyQ (p : Params) (a : Nat) : Nat :=
  if a=admitOp p then 1 else 0

theorem earlyQ_bound (p : Params) (a : Nat) : earlyQ p a<2 := by
  unfold earlyQ
  split <;> decide

theorem early_issue_packet (p : Params) (v : BitVec p.w) (t : Tok)
    (a : Nat) (P : sourcePhase p v=1) (O : sourceOpcode p v=a)
    (A : 0<a) (B : a≤admitOp p) :
    (source p v t).2=some (earlyF a 0 0) := by
  have C : ¬commitOp p<a := by unfold admitOp at B; unfold commitOp; omega
  have H2 : a≠acqOp p := by unfold admitOp at B; unfold acqOp; omega
  have H3 : ¬cmpOp p≤a := by unfold admitOp at B; unfold cmpOp; omega
  have H4 : ¬writeOp p≤a := by unfold admitOp at B; unfold writeOp; omega
  have H5 : ¬sealOp p≤a := by unfold admitOp at B; unfold sealOp; omega
  unfold sourcePhase at P
  unfold sourceOpcode at O
  simp [source,P,O,C,H2,H3,H4,H5,Nat.ne_of_gt A,earlyF]

theorem early_consume_control (p : Params) (v : BitVec p.w)
    (a : Nat) (P : sourcePhase p v=2) (O : sourceOpcode p v=a)
    (A : 0<a) (B : a≤admitOp p) :
    let t := earlyD a (earlyQ p a)
    let y := (liftSourcePatch p (source p v t).1).apply v
    (sourcePhase p y,sourceOpcode p y)=(1,a+1) ∧
      (source p v t).2=some MISByteCodec.E := by
  dsimp only
  by_cases J : a=admitOp p
  · rw [J] at O ⊢
    have V := fast_admit_consume_control p v (earlyD (admitOp p) 1)
      P O rfl rfl rfl rfl
    simpa [earlyQ,earlyD,acqOp,admitOp] using V
  · have L : a<admitOp p := by omega
    have C : ¬commitOp p<a := by unfold admitOp at B; unfold commitOp; omega
    have E : source p v (earlyD a (earlyQ p a)) =
        (ctrl p 1 (a+1),some MISByteCodec.E) := by
      unfold sourcePhase at P
      unfold sourceOpcode at O
      simp [source,P,O,C,Nat.ne_of_gt A,L,earlyD,earlyQ,J]
    rw [E]
    exact ⟨prelaunch_ctrl_write p v (a+1)
      (by unfold admitOp at B; omega),rfl⟩

-- The old root normalization is literally an identity on a healthy
-- forward token; tag-only normalization is not sufficient here.
theorem early_root_norm_wire (p : Params) (v : BitVec p.w)
    (H : (publicationToken p true v 0).fault=false) :
    prelaunchDoorNormWire p v=resetTokenRead p v 0 := by
  change (oldK p true v 0).fault=false at H
  simp [prelaunchDoorNormWire,H,parked,gate]

theorem early_F_roundtrip (p : Params) (g : Bool) (a q : Nat)
    (A : 0<a) (B : a≤admitOp p) (Q : q<2)
    (H : a≠admitOp p→q=0) (G : a=admitOp p→g=false) :
    decode p g (resetTokenWire p (earlyF a q 0))=earlyF a q 0 := by
  by_cases AD : a=admitOp p
  · subst a
    rw [G rfl]
    exact fast_admit_off_roundtrip p q Q
  · have Z := H AD
    subst q
    let t := earlyF a 0 0
    have O : a<2^o p := by
      have Z := power_of_ell (5+4*p.digits)
      unfold admitOp at B
      unfold o
      omega
    have Fit : RankFits p t :=
      ⟨by change 2<4; decide,O,Nat.two_pow_pos _,by change 0<8; decide,by change 0<4; decide⟩
    have V := rReadFields p t Fit
    have F0 : (resetTokenWire p t).getLsbD (6+o p+payW p)=false := by
      rw [rGet_bit,V.2.1]
      rfl
    have AC : a≠acqOp p := by unfold admitOp at B; unfold acqOp; omega
    have CM : a≠commitOp p := by unfold admitOp at B; unfold commitOp; omega
    have C : ¬commitOp p<a := by unfold admitOp at B; unfold commitOp; omega
    have M : ¬cmpOp p≤a := by unfold admitOp at B; unfold cmpOp; omega
    have W : ¬writeOp p≤a := by unfold admitOp at B; unfold writeOp; omega
    have S : ¬sealOp p≤a := by unfold admitOp at B; unfold sealOp; omega
    change decode p g (resetTokenWire p t)=t
    simp only [decode,V.1,V.2.2.1,V.2.2.2.1,V.2.2.2.2.1,
      V.2.2.2.2.2.2,F0]
    simp [t,earlyF,AD,AC,CM,C,M,W,S]

-- Gate independent, even when D is physically crossing the ADMIT gate.
theorem early_D_roundtrip (p : Params) (g : Bool) (a : Nat)
    (_A : 0<a) (B : a≤admitOp p) :
    decode p g (resetTokenWire p (earlyD a (earlyQ p a)))=
      earlyD a (earlyQ p a) := by
  let q := earlyQ p a
  let t := earlyD a q
  have O : a<2^o p := by
    have Z := power_of_ell (5+4*p.digits)
    unfold admitOp at B
    unfold o
    omega
  have Q : q<2 := earlyQ_bound p a
  have P : q<2^payW p := Nat.lt_of_lt_of_le Q
    (Nat.pow_le_pow_right (show 1≤(2:Nat) by decide)
      (by unfold payW; omega : 1≤payW p))
  have Fit : RankFits p t :=
    ⟨by change 3<4; decide,O,P,by change 0<8; decide,by change 0<4; decide⟩
  have V := rReadFields p t Fit
  have F0 : (resetTokenWire p t).getLsbD (6+o p+payW p)=false := by
    rw [rGet_bit,V.2.1]
    rfl
  have AC : a≠acqOp p := by unfold admitOp at B; unfold acqOp; omega
  have C : ¬commitOp p<a := by unfold admitOp at B; unfold commitOp; omega
  have M : ¬cmpOp p≤a := by unfold admitOp at B; unfold cmpOp; omega
  have W : ¬writeOp p≤a := by unfold admitOp at B; unfold writeOp; omega
  change decode p g (resetTokenWire p t)=t
  simp only [decode,V.1,V.2.2.1,V.2.2.2.1,V.2.2.2.2.1,
    V.2.2.2.2.2.2,F0]
  by_cases AD : a=admitOp p
  · have C' : ¬commitOp p<admitOp p := by unfold admitOp commitOp; omega
    have M' : ¬cmpOp p≤admitOp p := by unfold admitOp cmpOp; omega
    have AC' : admitOp p≠acqOp p := by unfold admitOp acqOp; omega
    simp [t,q,earlyQ,earlyD,AD,C',M',AC']
  · simp [t,q,earlyQ,earlyD,AC,C,M,AD]

theorem early_norm_fixed (p : Params) (g : Bool) (side : Nat)
    (w : BitVec (tokenW p)) (t : Tok)
    (T : decode p g w=t) (H : rankNormIntent p side g t=none) :
    decode p g (rankNormWire p side g w)=t := by
  rw [rankNormWire,T,H]
  exact T

-- Regular (non-parked) F departure. For HELLO even a true decode
-- gate is harmless. For ADMIT both endpoints must be off the gate.
theorem early_regular_route (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (j k : Fin 3) (a q : Nat)
    (A : 0<a) (B : a≤admitOp p)
    (H : publicationToken p hu u j=earlyF a q 0)
    (G : a=admitOp p→rankGate p hu u j=false)
    (G' : a=admitOp p→rankGate p hv v k=false) :
    rankRouteR p hu hv u v j k=some (earlyF a q 0) := by
  by_cases AD : a=admitOp p
  · subst a
    exact fast_off_route p hu hv u v j k q H (G rfl) (G' rfl)
  · have R : rankReady p hu u j=true := (rankReady_iff _ _ _ _).mpr
      ⟨by rw [H]; rfl,fun K=>AD (by simpa [H,earlyF] using K.1.2.2)⟩
    have CM : a≠commitOp p := by unfold admitOp at B; unfold commitOp; omega
    have AC : a≠acqOp p := by unfold admitOp at B; unfold acqOp; omega
    have M : ¬cmpOp p≤a := by unfold admitOp at B; unfold cmpOp; omega
    have W : ¬writeOp p≤a := by unfold admitOp at B; unfold writeOp; omega
    have S : a≠sealOp p := by unfold admitOp at B; unfold sealOp; omega
    change oldK p hu u j=earlyF a q 0 at H
    unfold rankRouteR
    dsimp only
    rw [if_pos R,H]
    simp [effect,arrival,parked,earlyF,AD,CM,AC,M,W,S,Nat.ne_of_gt A]

-- Terminal old departure, same exact q, including winning ADMIT q=1.
-- This generalizes deny_admit_terminal_wire without using that denial lemma.
-- Terminal old departure, same exact q, including winning ADMIT q=1.
-- This generalizes deny_admit_terminal_wire without using that denial lemma.
theorem early_terminal_wire (p : Params) (hu hv : Bool)
    (u v : BitVec p.w) (j : Fin 3) (a q : Nat)
    (A : 0<a) (B : a≤admitOp p)
    (D : reset0Destination hv j=none)
    (H : publicationToken p hu u j=earlyF a q 0)
    (G : a=admitOp p→rankGate p hu u j=false)
    (Q : a≠admitOp p→q=0) :
    resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j=
      resetTokenWire p (earlyD a q) := by
  have R : rankReady p hu u j=true := (rankReady_iff _ _ _ _).mpr
    ⟨by rw [H]; rfl,fun K=>by
      have E : a=admitOp p := by simpa [H,earlyF] using K.1.2.2
      exact Bool.noConfusion ((G E).symm.trans K.2.1)⟩
  have CM : a≠commitOp p := by unfold admitOp at B; unfold commitOp; omega
  have AC : a≠acqOp p := by unfold admitOp at B; unfold acqOp; omega
  have M : ¬cmpOp p≤a := by unfold admitOp at B; unfold cmpOp; omega
  have W : ¬writeOp p≤a := by unfold admitOp at B; unfold writeOp; omega
  have S : a≠sealOp p := by unfold admitOp at B; unfold sealOp; omega
  rw [rank_row_left,D]
  unfold rankRouteL
  simp only [R,if_true,Option.elim]
  change oldK p hu u j=earlyF a q 0 at H
  rw [H]
  by_cases AD : a=admitOp p
  · subst a
    have G0 : gate p hu u j=false := G rfl
    simp [effect,terminal,parked,G0,earlyF,earlyD,CM,AC,M,W,S,Nat.ne_of_gt A]
  · have Q0 := Q AD
    simp [effect,terminal,parked,earlyF,earlyD,AD,CM,AC,M,W,S,Nat.ne_of_gt A,Q0]

end L4.ReportByteRows

namespace L4.ReportByteRows
open AllSizeProtocol
private def abFrame (p : Params) (a : Patch (workW p)) : Prop :=
  ∀ sel j, j<3 → a.mask.getLsbD (bankOffset p sel+2*d p+j)=false
private theorem ab_empty (p : Params) : abFrame p (.empty _) := by
  intro i j J
  simp [Patch.empty]
private theorem ab_comp {p : Params} {a b : Patch (workW p)}
    (A : abFrame p a) (B : abFrame p b) : abFrame p (a.compose b) := by
  intro i j J
  simp [Patch.compose,A i j J,B i j J]
private theorem ab_range (p : Params) (sel j : Nat) (J : j<3) :
    bankOffset p sel+2*d p+j<grantBase p := by
  have M := Nat.mul_le_mul_right (bankW p) (show 1-sel≤1 by omega)
  unfold bankOffset grantBase
  have B : bankW p=3+2*d p := rfl
  omega
private theorem ab_cmt {p : Params} {a : Patch (workW p)}
    (A : cmtFrame p a) : abFrame p a := by
  intro s j J
  apply A
  left
  exact ⟨by unfold bankOffset; omega,ab_range p s j J⟩
private theorem ab_K (p : Params) (j : Fin 3) (t : Tok) : abFrame p (writeK p j t) :=
  ab_cmt (cmtK p j t)
private theorem ab_grants (p : Params) (g : Fin 3→Bool) : abFrame p (grants p g) := by
  intro i j J
  have H := ab_range p i j J
  simp [grants,field,BitVec.getLsbD_shiftLeft,Nat.not_le_of_gt H]
private theorem ab_pulse (p : Params) (h : Bool) (side : Nat) (x : BitVec p.w) :
    abFrame p (pulse p h side x) := by
  intro i j J
  have L := ab_range p i j J
  apply pulse_mask_below_tail
  unfold bankOffset sealBase sourceBase
  omega
private theorem ab_bank (p : Params) (ix v : Nat) :
    abFrame p (field p (bankOffset p ix) (2*d p) v) := by
  intro sel j J
  let i := bankOffset p sel+2*d p+j
  have D : i<bankOffset p ix ∨ bankOffset p ix+2*d p≤i := by
    dsimp [i]
    unfold bankOffset bankW
    rcases (show 1-sel=0 ∨ 1-sel=1 by omega) with A|A <;>
      rcases (show 1-ix=0 ∨ 1-ix=1 by omega) with B|B <;>
      simp only [A,B,Nat.zero_mul,Nat.one_mul] <;> omega
  change (field p (bankOffset p ix) (2*d p) v).mask.getLsbD i=false
  rcases D with D|D
  · simp [field,BitVec.getLsbD_shiftLeft,Nat.not_le_of_gt D]
  · have L : 2*d p≤i-bankOffset p ix := by omega
    simp [field,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_of_ge _ _ L]
private theorem ab_clear (p : Params) : abFrame p (drClear p) := by
  unfold drClear
  exact ab_comp
    (ab_comp (ab_cmt (cmtReset p)) (ab_cmt (cmtSeal p none)))
    (ab_grants p _)

private theorem ab_baseL (p : Params) (hu : Bool) (u : BitVec p.w) :
    abFrame p (drBaseL p hu u) := by
  unfold drBaseL
  split
  · exact ab_grants p _
  · exact ab_clear p

private theorem ab_baseR (p : Params) (hv : Bool) (v : BitVec p.w) :
    abFrame p (drBaseR p hv v) := by
  unfold drBaseR
  split
  · split
    · exact ab_grants p _
    · exact ab_empty p
  · exact ab_clear p

private theorem ab_norm (p : Params) (j : Fin 3) (a : Patch (workW p))
    (H : a=.empty _ ∨ ∃ t,a=writeK p j t) : abFrame p a := by
  rcases H with rfl|⟨t,rfl⟩
  · exact ab_empty p
  · exact ab_K p j t

private theorem ab_prefix (p : Params) (base pulseP : Patch (workW p))
    (norm : Fin 3→Patch (workW p)) (A : abFrame p base)
    (B : abFrame p pulseP) (N : ∀ j,abFrame p (norm j)) :
    abFrame p (drPrefix p base pulseP norm) :=
  ab_comp (ab_comp (ab_comp (ab_comp A B) (N 0)) (N 1)) (N 2)

private theorem ab_preL (p : Params) (hu hv : Bool) (u v : BitVec p.w) :
    abFrame p (drPre p hu hv u v).1 :=
  ab_prefix p _ _ _ (ab_baseL p hu u) (ab_pulse p hu 2 u)
    (fun j=>ab_norm p j _ (dr_norm_left_shape p hu u j))

private theorem ab_preR (p : Params) (hu hv : Bool) (u v : BitVec p.w) :
    abFrame p (drPre p hu hv u v).2 :=
  ab_prefix p _ _ _ (ab_baseR p hv v) (ab_pulse p hv 1 v)
    (fun j=>ab_norm p j _ (dr_norm_right_shape p hv v j))

private theorem ab_effectL (p : Params) (u v : BitVec p.w) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (w : Bool) (t : Tok) :
    abFrame p (effect p u v hu hv j k w t).1 := by
  unfold effect
  dsimp only
  split
  · exact ab_empty p
  · split
    · split <;> exact ab_empty p
    · split
      · exact ab_empty p
      · split
        · exact ab_cmt (cmtSeal p none)
        · split
          · exact ab_empty p
          · generalize (if t.opcode<readOp p then cmpOp p else readOp p) = off
            split
            · exact ab_empty p
            · split
              · split
                · exact ab_empty p
                · exact ab_bank p ((t.payload/2^(2*d p))%2) (t.payload%2^(2*d p))
              · split
                · split
                  · exact ab_cmt (p:=p) (cmtSeal p (some t.payload))
                  · exact ab_empty p
                · exact ab_empty p

private theorem ab_routeL (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (w : Fin 3→Bool) (ab : Pair (Patch (workW p)))
    (l : Fin 3 × Option (Fin 3)) (A : abFrame p ab.1) :
    abFrame p (cmtRoute p hu hv u v w ab l).1 := by
  rcases ab with ⟨a,b⟩
  rcases l with ⟨j,k⟩
  have E0 := ab_effectL p u v hu hv j k (w j) (oldK p hu u j)
  cases k with
  | none =>
    unfold cmtRoute
    dsimp only
    split
    · exact ab_comp (ab_comp A E0) (ab_K p _ _)
    · split
      · exact A
      · split
        · exact ab_comp A (ab_K p _ _)
        · exact A
  | some k =>
    unfold cmtRoute
    dsimp only
    split
    · exact ab_comp (ab_comp A E0) (ab_K p _ _)
    · split
      · exact A
      · split
        · exact ab_comp A (ab_K p _ _)
        · split
          · exact ab_comp A (ab_K p _ _)
          · exact A

private theorem ab_routeR (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (w : Fin 3→Bool) (ab : Pair (Patch (workW p)))
    (l : Fin 3 × Option (Fin 3)) (A : abFrame p ab.2)
    (H : ¬ancestryCommitOpportunity p hu hv u v) :
    abFrame p (cmtRoute p hu hv u v w ab l).2 := by
  rcases ab with ⟨a,b⟩
  rcases l with ⟨j,k⟩
  have E (R : ready p hu u j (oldK p hu u j)=true) :
      abFrame p (effect p u v hu hv j k (w j) (oldK p hu u j)).2.1 := by
    rw [ancSel_effectR p u v hu hv j k (w j) R H]
    exact ab_empty p
  cases k with
  | none =>
    unfold cmtRoute
    dsimp only
    split
    · rename_i R
      exact ab_comp A (E R)
    · split
      · exact A
      · exact A
  | some k =>
    unfold cmtRoute
    dsimp only
    split
    · rename_i R
      exact ab_comp (ab_comp A (E R)) (ab_K p _ _)
    · split
      · exact A
      · split
        · exact ab_comp A (ab_K p _ _)
        · split <;> exact A

private theorem ab_foldL (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (w : Fin 3→Bool) (xs : List (Fin 3 × Option (Fin 3)))
    (ab : Pair (Patch (workW p))) (A : abFrame p ab.1) :
    abFrame p (xs.foldl (cmtRoute p hu hv u v w) ab).1 := by
  induction xs generalizing ab with
  | nil => exact A
  | cons l xs ih =>
    exact ih _ (ab_routeL p hu hv u v w ab l A)

private theorem ab_foldR (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (w : Fin 3→Bool) (xs : List (Fin 3 × Option (Fin 3)))
    (ab : Pair (Patch (workW p))) (A : abFrame p ab.2)
    (H : ¬ancestryCommitOpportunity p hu hv u v) :
    abFrame p (xs.foldl (cmtRoute p hu hv u v w) ab).2 := by
  induction xs generalizing ab with
  | nil => exact A
  | cons l xs ih =>
    exact ih _ (ab_routeR p hu hv u v w ab l A H)

theorem report_row_left_ab_bits (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (sel j : Nat) (J : j<3) :
    ((row p (hu,hv) (u,v)).1.apply u).getLsbD (bankOffset p sel+2*d p+j)=
      u.getLsbD (bankOffset p sel+2*d p+j) := by
  rw [dr_row_eq,reset0Post_left]
  apply pulse_widen_frame
  exact ab_foldL p hu hv u v (drWin p hu u) (links hv) _ (ab_preL p hu hv u v) sel j J

theorem report_row_right_ab_bits (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (No : ¬ancestryCommitOpportunity p hu hv u v) (sel j : Nat) (J : j<3) :
    ((row p (hu,hv) (u,v)).2.apply v).getLsbD (bankOffset p sel+2*d p+j)=
      v.getLsbD (bankOffset p sel+2*d p+j) := by
  have A : abFrame p (drRouted p hu hv u v).2 :=
    ab_foldR p hu hv u v (drWin p hu u) (links hv) _ (ab_preR p hu hv u v) No
  rw [dr_row_eq]
  apply pulse_widen_frame
  have F : abFrame p (reset0Post p hv v (drRouted p hu hv u v)).2 := by
    cases hv
    · exact A
    · unfold reset0Post
      simp only [if_true]
      exact ab_comp (ab_comp A (ab_cmt (cmtSource p v (oldK p true v 0))))
        (ab_cmt (cmtSourceToken p (source p v (oldK p true v 0)).2))
  exact F sel j J

def abAddress (p : Params) (sel j : Nat) := bankOffset p sel+2*d p+j

theorem ab_bits_below_grants (p : Params) (sel j : Nat) (J : j<3) :
    abAddress p sel j<grantBase p := ab_range p sel j J

theorem ab_bits_lt (p : Params) (sel j : Nat) (J : j<3) :
    bankOffset p sel+2*d p+j<workW p := by
  have H := ab_range p sel j J
  unfold workW
  omega

theorem ab_bit_congr (p : Params) (u v : BitVec p.w) (sel : Nat)
    (H : ∀ j,j<3 → u.getLsbD (bankOffset p sel+2*d p+j)=
      v.getLsbD (bankOffset p sel+2*d p+j)) :
    publicationA p u sel=publicationA p v sel ∧ publicationPair p u sel=publicationPair p v sel := by
  let a := u.extractLsb' (bankOffset p sel) (bankW p)
  let b := v.extractLsb' (bankOffset p sel) (bankW p)
  have G (j : Nat) (J : j<3) : a.getLsbD (2*d p+j)=b.getLsbD (2*d p+j) := by
    have K : 2*d p+j<bankW p := by unfold bankW; omega
    simpa only [a,b,BitVec.getLsbD_extractLsb',K,decide_true,Bool.true_and,Nat.add_assoc] using H j J
  constructor
  · show bit a.toNat (2+2*d p)=bit b.toNat (2+2*d p)
    have E := G 2 (by decide)
    rw [Nat.add_comm (2*d p) 2] at E
    simpa only [bit,Nat.shiftRight_eq_div_pow,←BitVec.testBit_toNat,
      Nat.testBit_eq_decide_div_mod_eq, Bool.beq_eq_decide_eq] using E
  · have E : a.extractLsb' (2*d p) 2=b.extractLsb' (2*d p) 2 := by
      apply BitVec.eq_of_getLsbD_eq
      intro j J
      simp only [BitVec.getLsbD_extractLsb',J,decide_true,Bool.true_and]
      exact G _ (by omega)
    show (a.toNat/2^(2*d p))%4=(b.toNat/2^(2*d p))%4
    have E' := congrArg BitVec.toNat E
    simpa only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] using E'

end L4.ReportByteRows
