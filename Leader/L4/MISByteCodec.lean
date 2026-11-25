import Leader.L4.ShortByteReadouts

/-! The 96-bit short MIS client codec and its literal door source.
No grant arbiter, route, or fake producer is exported here. -/
namespace L4.MISByteCodec
open AllSizeProtocol

def lane (j d : Nat) (h : j+d≤96) : Field 96 d := ⟨j,h⟩
def get (x : BitVec 96) (j d : Nat) (h : j+d≤96) : Nat := ((lane j d h).read x).toNat
def put (j d : Nat) (h : j+d≤96) (a : Nat) : Patch 96 :=
  (lane j d h).assign (BitVec.ofNat d a)

def off (isHeader : Bool) (x : BitVec 96) : Nat :=
  if isHeader then 0 else get x 94 2 (by decide)

def atGate (isHeader : Bool) (x : BitVec 96) (k : Fin 3) : Bool :=
  k.val==1 && off isHeader x==0

def kField (j : Fin 3) : Field 96 19 := ⟨19*(2-j.val),by have := j.isLt; omega⟩

structure Token where
  tag : Nat
  opcode : Nat := 0
  payload : Nat := 0
  race : Nat := 0
  outcome : Nat := 0
  fault : Bool := false
  applied : Bool := false
  deriving DecidableEq, Repr

def faultToken (tag : Nat) : Token := ⟨tag,0,0,0,if tag==3 then 2 else 0,true,false⟩
def E : Token := { tag := 0 }
def T : Token := { tag := 1 }

/-- A descriptor is old selector, complementary target selector, Y. -/
def descValid (p : Nat) : Bool := ((p/4)%2 != (p/2)%2)

def fPayloadSize (op : Nat) : Nat :=
  if op==3 then 7 else if op==2 then 1 else if 4≤op then 3 else 0

def dPayloadSize (op : Nat) : Nat :=
  if op==3 then 6 else if op==2 then 1 else 0

def decode (gate : Bool) (x : BitVec 19) : Token :=
  let tag := (x.extractLsb' 17 2).toNat
  let f := x.getLsbD 16
  let op := (x.extractLsb' 13 3).toNat
  let race := (x.extractLsb' 10 3).toNat
  let outcome := (x.extractLsb' 8 2).toNat
  let payload := (x.extractLsb' 0 7).toNat
  let g := gate && op==2
  if tag==0 then E
  else if tag==1 then T
  else if f || op==7 then faultToken tag
  else if tag==2 then
    if outcome != 0 || (if g then race<1 || 5<race else race != 0) ||
        (4≤op && !descValid payload) then faultToken tag
    else ⟨tag,op,payload%(2^fPayloadSize op),race,0,false,op==6 && x.getLsbD 7⟩
  else
    if race != 0 || (outcome != 0 && !(op==3 && outcome==1)) then faultToken tag
    else ⟨tag,op,(if outcome==1 then 0 else payload%(2^dPayloadSize op)),0,outcome,false,false⟩

def encode (t : Token) : BitVec 19 :=
  BitVec.ofNat 19 (t.tag*2^17+t.fault.toNat*2^16+t.opcode*2^13+
    t.race*2^10+t.outcome*2^8+t.applied.toNat*2^7+t.payload)

def putK (j : Fin 3) (t : Token) : Patch 96 := (kField j).assign (encode t)

def oldK (header : Bool) (x : BitVec 96) (j : Fin 3) : Token :=
  decode (atGate header x j) ((kField j).read x)

def readSeal (x : BitVec 96) : Option Nat :=
  let bits := get x 83 4 (by decide)
  if 8≤bits && descValid (bits%8) then some (bits%8) else none

def phaseOp (phase op : Nat) : Patch 96 := put 78 5 (by decide) (phase*8+op)
def resetSource : Patch 96 := put 57 26 (by decide) (2^24)

def issuedDescriptor (raw : BitVec 96) : Nat :=
  let ix := get raw 76 1 (by decide)
  let Y := !(raw.getLsbD 74 || raw.getLsbD 72)
  4*ix + 2*(1-ix) + Y.toNat

/-- Actual incoming door source, separate from outer old-pair routing.
WAIT F/T holds raw, RESET ISSUE clears all file bytes, and dormant
comparisons/registers are not read unless that declaration uses them. -/
def source (raw : BitVec 96) (t : Token) : Patch 96 × Option Token :=
  let phase := get raw 81 2 (by decide)
  let op := get raw 78 3 (by decide)
  let reset := (resetSource,some E)
  if phase==0 || phase==3 || op==7 then reset
  else if phase==1 then
    let patch := if op==0 then resetSource else .empty 96
    let arg := if op==3 then 64 else if 4≤op then issuedDescriptor raw else 0
    (patch.compose (put 81 2 (by decide) 2),some { tag := 2, opcode := op, payload := arg })
  else if t.tag==1 || t.tag==2 then (.empty 96,none)
  else if t.tag != 3 || t.opcode != op || t.fault || t.outcome==1 then reset
  else
    match op with
    | 0 => (phaseOp 1 1,some E)
    | 1 => (phaseOp 1 2,some E)
    | 2 => if t.payload==1 then (phaseOp 1 3,some E) else reset
    | 3 => (((phaseOp 1 4).compose (put 72 6 (by decide) t.payload)).compose
      (put 68 4 (by decide) 0),some E)
    | 4 => (phaseOp 1 5,some E)
    | 5 => (phaseOp 1 6,some E)
    | _ => reset

theorem source_wait_holds (raw : BitVec 96) (t : Token)
    (hp : get raw 81 2 (by decide)=2) (hj : get raw 78 3 (by decide) <7)
    (hf : t.tag=1 ∨ t.tag=2) : source raw t = (.empty 96,none) := by
  have ho : (get raw 78 3 (by decide)==7)=false :=
    Bool.eq_false_iff.mpr (fun h => by
      have := beq_iff_eq.mp h
      omega)
  rcases hf with ht|ht <;> simp [source,hp,ho,ht]

/-- Issue COMMIT never uses an inherited applied bit. -/
theorem commit_issue_fresh (raw : BitVec 96)
    (hp : get raw 81 2 (by decide)=1) (hj : get raw 78 3 (by decide)=6) :
    (source raw E).2=some ⟨2,6,issuedDescriptor raw,0,0,false,false⟩ := by
  simp [source,hp,hj]

end L4.MISByteCodec
