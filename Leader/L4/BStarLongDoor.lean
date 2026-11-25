import Leader.L4.BStarLongCommand
import Leader.L4.BStarLongRegisters

/-! Literal old-right source door, including captures, valid ISSUE, and
matching non-arithmetic replies. Arithmetic acceptance is an explicit
continuation; this module does not substitute a stuttering interpreter. -/
namespace L4.BStarLongDoor
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongCommand

def captures : Field LW 6 := ⟨2189,by decide⟩
def capturedHeaders : Field LW 27 := ⟨2162,by decide⟩
def candidateHeaders : Field LW 18 := ⟨2137,by decide⟩
def scalarFile : Field LW 369 := ⟨1764,by decide⟩

def ctrlPhase := LongDoorGuard.phaseField manifest
def ctrlOp := LongDoorGuard.opcodeField manifest
def srcFile := LongDoorGuard.fileField manifest
def clearFile := srcFile.assign 0

def schedule (op : Nat) : Patch LW :=
  ((ctrlPhase.assign 1).compose (ctrlOp.assign (BitVec.ofNat _ op))).compose
    (setToken 0 .empty)

def faultRestart : Patch LW := LongDoorGuard.repair manifest

def forward (op n : Nat) : Token :=
  .forward ⟨0,BitVec.ofNat 9 op,0,0,BitVec.ofNat 34 n⟩

def scalarMux (op : Nat) (x : BitVec LW) : Option Nat :=
  ((BStarLongSignatures.muxInputs.find? fun e => e.1==op).map fun e =>
   ((BStarLongRegisters.scalar e.2).read x).toNat)

/-- A legal ISSUE reads its named operands only. No active live read
can depend on a stale operation's dormant file, apart from its own args. -/
def initial (op : Nat) (x : BitVec LW) : Option Nat :=
  if op==acquire then some (2^33)
  else if op==copyLoad then
    let n := (captures.read x).toNat
    if selTriple n then some n else none
  else if op==stageOp || op==sealOp || op==commitOp then
    let d := (sourceDescriptor.read x).toNat
    match BStarLongPublication.decode (BitVec.ofNat 7 d) with
    | none => none
    | some a =>
      if op==stageOp then some (d*2^18+(candidateHeaders.read x).toNat)
      else if op==sealOp then some (2*d)
      else
        let b := (choice.read x).toNat
        if b==a.b0.val || (a.need && b==a.b1.val) then some (4*d+b) else none
  else match arithKind op with
    | some .centerLoad =>
      let n := ((capturedSelector 1).read x).toNat
      if n==3 then none else some n
    | some .mux => scalarMux op x
    | some .cmp => some 2
    | _ => some 0

def issued (op n : Nat) : Patch LW :=
  let q := (ctrlPhase.assign 2).compose (setToken 0 (forward op n))
  if op==1 then clearFile.compose q else q

def afterReply (op : Nat) (p : Payload) (x : BitVec LW) : Patch LW :=
  let n := p.argument.toNat
  if op==admit then schedule (if n%2==1 then acquire else 412)
  else if op==acquire then
    if p.outcome==1 then schedule 412
    else
      (schedule 6).compose ((captures.assign (BitVec.ofNat _ (n/2^27))).compose
        (capturedHeaders.assign (BitVec.ofNat _ n)))
  else if op==1 then
    (schedule 2).compose (((sourceDescriptor.assign 0).compose (choice.assign 0)).compose
      (candidateHeaders.assign 0))
  else if op==12 then
    (schedule 13).compose ((scalarFile.assign 0).compose (need.assign 0))
  else if op==sealOp || op==bitOp then
    match BStarLongPublication.decode (sourceDescriptor.read x) with
    | none => faultRestart
    | some d =>
      let b := n%2==1
      if op==sealOp then
        if b != d.need then faultRestart
        else if b then schedule bitOp
        else (schedule commitOp).compose (choice.assign (BitVec.ofNat 2 d.b0.val))
      else if !d.need then faultRestart
      else ((schedule commitOp).compose (delta.assign (BitVec.ofBool b))).compose
          (choice.assign (BitVec.ofNat 2 (if b then d.b1.val else d.b0.val)))
  else schedule (if op==commitOp || op==412 then 0 else op+1)

inductive Decision where
  | hold
  | write (q : Patch LW)
  | acceptTour (physicalOp : Nat) (reply : Payload)
  -- The tour writer installs scalar/descriptor live-outs and advances K0,
  -- or issues faultRestart if its operands do not validate.

/-- Only the immutable old right K0 binds the door. The input token is
the occurrence-bound variant (therefore all live reply fields are checked). -/
def oldDoor (x : BitVec LW) (k0 : Token) : Decision :=
  if !LongDoorGuard.valid manifest x then .write faultRestart
  else
    let phase := (ctrlPhase.read x).toNat
    let op := (ctrlOp.read x).toNat
    if phase==1 then
      match initial op x with
      | none => .write faultRestart
      | some n => .write (issued op n)
    else
      match k0 with
      | .trail | .forward _ => .hold
      | .reply p =>
        if p.fault != 0 || p.opcode.toNat != op then .write faultRestart
        else if arithKind op |>.isSome then .acceptTour op p
        else .write (afterReply op p x)
      | .empty => .write faultRestart

theorem invalid_owns_door (x : BitVec LW) (k0 : Token)
    (h : LongDoorGuard.valid manifest x=false) :
    oldDoor x k0=.write (LongDoorGuard.repair manifest) := by
  simp [oldDoor,h,faultRestart]

theorem wait_holds_forward (x : BitVec LW) (p : Payload)
    (hv : LongDoorGuard.valid manifest x=true) (hp : (ctrlPhase.read x).toNat=2) :
    oldDoor x (.forward p)=.hold := by
  simp [oldDoor,hv,hp]

theorem wait_holds_trail (x : BitVec LW)
    (hv : LongDoorGuard.valid manifest x=true) (hp : (ctrlPhase.read x).toNat=2) :
    oldDoor x .trail=.hold := by
  simp [oldDoor,hv,hp]

theorem wait_empty_repairs (x : BitVec LW)
    (hv : LongDoorGuard.valid manifest x=true) (hp : (ctrlPhase.read x).toNat=2) :
    oldDoor x .empty=.write faultRestart := by
  simp [oldDoor,hv,hp]

theorem seal_issues_zero (x : BitVec LW) (d : BStarLongPublication.Descriptor)
    (h : BStarLongPublication.decode (sourceDescriptor.read x)=some d) :
    initial sealOp x=some (2*(sourceDescriptor.read x).toNat) := by
  have hs : BitVec.ofNat 7 (sourceDescriptor.read x).toNat=sourceDescriptor.read x := by simp
  simp [initial,sealOp,acquire,copyLoad,stageOp,commitOp,hs,h]

#print axioms invalid_owns_door
#print axioms wait_holds_forward
#print axioms wait_holds_trail
#print axioms wait_empty_repairs
#print axioms seal_issues_zero
end L4.BStarLongDoor
