import Leader.L4.BStarLongOutgoing
import Leader.L4.BStarLongPackets
import Leader.L4.Compiler.Literal

/-! Literal arithmetic row at one physical digit, and old source
file acceptance of one tour and its immediately following alias run.
The accepted instruction literal fixes the operands. No evaluation
of the entire held bank is substituted for a physical visit. -/
namespace L4.BStarLongArithmetic
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongCommand BStarLongRegisters BStarLongPackets
open BStarLongDoor BStarLongSignatures
open L4.Compiler.Native

def nodeOf (op : Nat) : Option Nat :=
  if op<13 then none else tourNodes[op-13]?

def get (i : Nat) : Option Code := literal[i]?
def num (x : BitVec LW) (j : Nat) := ((numeric j).read x).toNat
def source (x : BitVec LW) (j : Nat) := ((scalar j).read x).toNat

def writeNum (j n : Nat) : Patch LW := (numeric j).assign (BitVec.ofNat _ n)
def writeScalar (j n : Nat) : Patch LW := (scalar j).assign (BitVec.ofNat _ n)

def digitLoad (x : BitVec LW) (q : Fin 3) (f : Fin 9) (n : Nat) :
    Option Nat :=
  if q.val==1 then
    if h : n<3 then some (((bankDigit ⟨n,h⟩ f).read x).toNat) else none
  else
    let a := (readLane (if q.val==0 then 1 else 3) x).retained
    (a.nibble f).map BitVec.toNat

def litDigit (c : ConstId) (ends previousEnd : Bool) : Nat :=
  match c with
  | .zero => 0
  | .one => 1
  | .eight => 8
  | .p => if ends then 8 else 0
  | .max => 15
  | .bm1 => if ends || previousEnd then 0 else 15

def physicalDigit (g : LongGeometry) (x : BitVec LW) (i : Nat) (c : Code)
    (p : Payload) : Patch LW × Payload :=
  let n := p.argument.toNat
  let update := fun y => {p with argument:=BitVec.ofNat 34 y}
  let off := if g.axes.h6 then 0 else min 5 g.offset
  let ends := g.inside && g.last
  let wr := fun v => (writeNum i v,p)
  let bad : Payload := ⟨1,0,0,0,0⟩
  match c with
  | .load q f =>
    match digitLoad x q f n with
    | none => (.empty _,bad)
    | some k => wr k
  | .const v =>
    wr (match v with
        | .one | .eight => if off==0 then litDigit v ends g.successorEnd else 0
        | _ => litDigit v ends g.successorEnd)
  | .maskB j => wr (if ends || g.successorEnd then 0 else num x j)
  | .mux _ a b => wr (num x (if n%2==1 then a else b))
  | .add a b =>
    let z := num x a + num x b + n
    (writeNum i (z%16),update (z/16))
  | .sub a b =>
    let u := num x a; let v := num x b+n
    (writeNum i ((u+16-v)%16),update (if u<v then 1 else 0))
  | .shl3 a =>
    let z := 8*num x a+n
    (writeNum i (z%16),update (z/16))
  | .cmp a b =>
    let u := num x a; let v := num x b
    let eq := n/2==1 && u==v
    let lt := if u==v then n%2==1 else decide (u<v)
    (.empty _,update (2*eq.toNat+lt.toNat))
  | .scan5 a =>
    let u := num x a
    let q := if off==0 then n/16*16+u else if off==1 then n%16+16*(u%2) else n
    (.empty _,update q)
  | _ => (.empty _,p)

def visit (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload) :
    Patch LW × Payload :=
  if j.val != 1 || !g.inside || p.fault != 0 then (.empty _,p)
  else match nodeOf p.opcode.toNat with
  | none => (.empty _,p)
  | some i => match get i with
    | none => (.empty _,⟨1,0,0,0,0⟩)
    | some c => physicalDigit g x i c p

abbrev Pending := List (Nat × Nat)

def newest (old : BitVec LW) (xs : Pending) (i : Nat) : Nat :=
  ((xs.find? (fun w => w.1==i)).map Prod.snd).getD (source old i)

def nodeResult (old : BitVec LW) (n : Nat) : Code → Option Nat
  | .add _ _ | .sub _ _ | .shl3 _ | .cmp _ _ | .scan5 _ => some n
  | .not a => some ((source old a==0).toNat)
  | .and a b => some ((source old a==1 && source old b==1).toNat)
  | .or a b => some ((source old a==1 || source old b==1).toNat)
  | .bmux q a b => some (source old (if source old q==1 then a else b))
  | .phaseEq a j => some ((source old a==j).toNat)
  | _ => none

/-- These four operations are wires, not physical tour claims. Only this
one source-side transaction reads a result it has just assigned. -/
def aliasValue (old : BitVec LW) (xs : Pending) : Code → Option Nat
  | .header q i => some (((capturedHeader q i).read old).toNat)
  | .bconst b => some b.toNat
  | .cmpEq a => some (newest old xs a / 2)
  | .cmpLt a => some (newest old xs a % 2)
  | _ => none

def aliases (old : BitVec LW) : Nat → List Code → Pending → Pending
  | _,[],xs => xs
  | j,c::cs,xs =>
    match aliasValue old xs c with
    | none => xs
    | some v => aliases old (j+1) cs ((j,v)::xs)

def acceptFile (old : BitVec LW) (physical : Nat) (p : Payload) : Patch LW :=
  match nodeOf physical with
  | none => faultRestart
  | some i => match get i with
    | none => faultRestart
    | some c =>
      let n := p.argument.toNat
      let xs := (nodeResult old n c).toList.map (fun v => (i,v))
      let ys := aliases old (i+1) (literal.drop (i+1)) xs
      let ws := BStarLongOutgoing.fuse (ys.reverse.map fun (i,y) => writeScalar i y)
      if physical < 407 then ws.compose (schedule (physical+1))
      else
        let s := ((capturedSelector 1).read old).toNat
        if h : s<3 then
          let bit := newest old ys BStarLongSignatures.needIx == 1
          let d : BStarLongPublication.Descriptor :=
            ⟨⟨s,h⟩,⟨(s+1)%3,by omega⟩,⟨(s+2)%3,by omega⟩,bit⟩
          let header := (outHeaders0++outHeaders1).foldl (fun a j => a*2+newest old ys j) 0
          let q := ((sourceDescriptor.assign (BStarLongPublication.encode d)).compose
              (need.assign (BitVec.ofBool bit))).compose (candidateHeaders.assign (BitVec.ofNat 18 header))
          (ws.compose q).compose (schedule stageOp)
        else faultRestart

theorem padding_visit (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload)
    (h : g.inside=false) : visit g j x p=(.empty _,p) := by
  simp [visit,h]

set_option maxRecDepth 4096 in
theorem actual_table_lengths : tourNodes.length=395 ∧ literal.length=474 := by
  exact ⟨by decide,literal_length⟩

set_option maxRecDepth 4096 in
theorem mux_file_uses_bits :
    muxInputs.all (fun (op,i) => widthAt scalarWidths i==1 && arithKind op==some .mux)=true := by decide

#print axioms padding_visit
#print axioms actual_table_lengths
#print axioms mux_file_uses_bits
end L4.BStarLongArithmetic
