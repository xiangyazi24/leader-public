import Leader.L4.BStarLongClaims
import Leader.L4.BStarLongToken
import Leader.L4.BStarLongPublication
import Leader.L4.BStarLongSignatures

/-! Old-occurrence binding and command classification. Packet, grant and
arithmetic effects consume this classification before the selected
forward front is advanced. An occupied race does not become a reverse-D
offer, and a newly arrived front never observes the same label. -/
namespace L4.BStarLongCommand
open AllSizeProtocol BStarLongToken BStarLongClaims BStarLongSignatures

def admit := 4
def acquire := 5
def copyLoad := 8
def stageOp := 408
def sealOp := 409
def bitOp := 410
def commitOp := 411

def fault (reply : Bool) : Token :=
  let p : Payload := ⟨1,0,0,if reply then 2 else 0,0⟩
  if reply then .reply p else .forward p

def selTriple (n : Nat) : Bool :=
  n % 4 != 3 && n / 4 % 4 != 3 && n / 16 % 4 != 3

def low (n w : Nat) : Nat := n % 2^w
def cropped (p : Payload) (w : Nat) : Payload :=
  {p with argument := BitVec.ofNat 34 (low p.argument.toNat w)}

def arithKind (op : Nat) : Option Kind :=
  if op<13 then none else arithmetic[op-13]?

def descOK (n : Nat) : Bool :=
  (BStarLongPublication.decode (BitVec.ofNat 7 n)).isSome

/-- Width of the live payload, or none on a live malformed index or LD.
Ignored padding never changes validity. -/
def forwardWidth (op n : Nat) : Option Nat :=
  if op==admit || op==bitOp then some 1
  else if op==acquire then
    if selTriple (n/2^27) then some 34 else none
  else if op==copyLoad then if selTriple n then some 6 else none
  else if op==stageOp then if descOK (n/2^18) then some 25 else none
  else if op==sealOp then if descOK (n/2) then some 8 else none
  else if op==commitOp then
    match BStarLongPublication.decode (BitVec.ofNat 7 (n/4)) with
    | none => none
    | some d =>
      if n%4==d.b0.val || (d.need && n%4==d.b1.val) then some 9 else none
  else
    match arithKind op with
    | some .centerLoad => if n%4 != 3 then some 2 else none
    | some .mux | some .bitCarry => some 1
    | some .shiftCarry => some 3
    | some .cmp => some 2
    | some .scan => some 5
    | _ => some 0

def replyWidth (op outcome n : Nat) : Option Nat :=
  if outcome==1 then if op==acquire then some 0 else none
  else if outcome != 0 then none
  else if op==acquire then if selTriple (n/2^27) then some 33 else none
  else if op==admit || op==bitOp || op==sealOp then some 1
  else match arithKind op with
    | some .bitCarry => some 1
    | some .shiftCarry => some 3
    | some .cmp => some 2
    | some .scan => some 5
    | _ => some 0

def gate (op : Nat) (j : Fin 11) (g : LongGeometry) : Bool :=
  let off := if g.axes.h6 then 0 else min 5 g.offset
  j.val==1 && ((op==admit && off==2) || (op==bitOp && off==4))

def bind (g : LongGeometry) (j : Fin 11) : Token → Token
  | .empty => .empty
  | .trail => .trail
  | .forward p =>
    let op := p.opcode.toNat
    let r := p.race.toNat
    let raceOK := if gate op j g then decide (1≤r ∧ r≤5) else r==0
    if p.fault != 0 || decide (op≥413) || p.outcome != 0 || !raceOK then fault false
    else match forwardWidth op p.argument.toNat with
      | none => fault false
      | some w => .forward (cropped p w)
  | .reply p =>
    let op := p.opcode.toNat
    if p.fault != 0 || decide (op≥413) || p.race != 0 then fault true
    else match replyWidth op p.outcome.toNat p.argument.toNat with
      | none => fault true
      | some w => .reply (cropped p w)

def finish (p : Payload) : Token :=
  let op := p.opcode.toNat
  let n := p.argument.toNat
  if p.fault != 0 then fault true
  else if op==acquire then
    if n / 2^33 % 2 == 1 then .reply {p with race:=0,argument:=BitVec.ofNat 34 (low n 33)}
    else .reply {p with race:=0,outcome:=1,argument:=0}
  else match replyWidth op 0 n with
    | none => fault true
    | some w => .reply (cropped {p with race:=0,outcome:=0} w)

def arrive (g : LongGeometry) (j : Fin 11) (p : Payload) : Token :=
  if p.fault==0 && gate p.opcode.toNat j g then .forward {p with race:=1,argument:=0}
  else .forward p

def depart (g : LongGeometry) (j : Fin 11) (p : Payload) : Option Payload :=
  if p.fault==0 && gate p.opcode.toNat j g then
    let r := p.race.toNat
    if r<4 then none else some {p with race:=0,argument:=BitVec.ofNat 34 (r-4)}
  else some p

/-- Only an unoverwritten valid old gate token observes this endpoint.
At the old left endpoint the observation is Other-right; vice versa. -/
def observe (a : At (Fin 11)) (g : LongGeometry) (p : Payload) : Option Payload :=
  if p.fault==0 && gate p.opcode.toNat a.occurrence g then
    let r := p.race.toNat
    let this := if a.side==.left then 3 else 2
    if r==1 then some {p with race:=BitVec.ofNat 3 this}
    else if (r==2 || r==3) && r != this then some {p with race:=BitVec.ofNat 3 (r+2)}
    else none
  else none

inductive Offer where
  | hold
  | door (t : Token)
  | advance (p : Payload)
  | reverse (t : Token)
  | clear
  deriving DecidableEq, Repr

def classify (c : CommandClaim) (g : LongGeometry) (src dst : Token) : Offer :=
  if c.kind==.door then .door src
  else match src with
    | .forward p => match depart g c.source.occurrence p with
      | none => .hold
      | some p => .advance p
    | _ =>
      if c.kind==.terminal then
        if src==.trail then .clear else .hold
      else match dst with
        | .reply _ => .reverse dst
        | _ => if src==.trail && dst==.empty then .clear else .hold

def geometry (g : Pair LongGeometry) (side : Side) : LongGeometry :=
  if side==.left then g.1 else g.2

/-- Both K arguments are bound on the *same old pair*. Decisions at a
seam do not allow old-word terminal or link effects to feed its door. -/
def offersOn (g : Pair LongGeometry) (old : At (Fin 11) → Token) :
    List (CommandClaim × Offer) :=
  let atBound := fun a => bind (geometry g a.side) a.occurrence (old a)
  (orderedCommands g).map fun c =>
    (c,classify c (geometry g c.source.side) (atBound c.source)
      ((c.destination.map atBound).getD .empty))

theorem classified_claims (g : Pair LongGeometry) (old : At (Fin 11) → Token) :
    (offersOn g old).map Prod.fst=orderedCommands g := by
  simp [offersOn,List.map_map,Function.comp_def]

theorem classified_disjoint (g : Pair LongGeometry) (old : At (Fin 11) → Token) :
    (((offersOn g old).flatMap (fun x => x.1.slots)) ++ discarded g).Nodup := by
  rcases g with ⟨x,y⟩
  rw [←List.flatMap_map]
  rw [classified_claims]
  exact (geometry_exhaustive x y).1

private def fixtureGeo (off : Nat) : LongGeometry :=
  ⟨⟨false,false,false,false,false,false⟩,true,false,off,false⟩

private def p (op race outcome payload : Nat) : Payload :=
  ⟨0,BitVec.ofNat 9 op,BitVec.ofNat 3 race,BitVec.ofNat 2 outcome,BitVec.ofNat 34 payload⟩

set_option maxRecDepth 4096 in
theorem signature_pins :
    arithmetic.length=395 ∧
    forwardWidth 30 0=some 1 ∧ forwardWidth 37 3=none ∧
    forwardWidth 409 (2*(8+4))=some 8 ∧
    replyWidth 5 1 999=some 0 := by decide

theorem moving_gate_fixture :
    arrive (fixtureGeo 2) 1 (p admit 0 0 1)=.forward (p admit 1 0 0) ∧
    bind (fixtureGeo 1) 1 (.forward (p admit 1 0 0))=fault false ∧
    depart (fixtureGeo 2) 1 (p admit 3 0 0)=none ∧
    depart (fixtureGeo 2) 1 (p admit 5 0 0)=some (p admit 0 0 1) ∧
    observe (L 1) (fixtureGeo 2) (p admit 2 0 0)=some (p admit 4 0 0) ∧
    observe (L 1) (fixtureGeo 2) (p admit 3 0 0)=none := by decide

theorem terminal_fixture :
    finish (p acquire 0 0 0)=.reply (p acquire 0 1 0) ∧
    finish (p acquire 0 0 (2^33))=.reply (p acquire 0 0 0) ∧
    finish (p sealOp 0 0 (2*(8+4)+1))=.reply (p sealOp 0 0 1) := by decide

end L4.BStarLongCommand
