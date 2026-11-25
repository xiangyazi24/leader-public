import Leader.L4.Compiler.Literal

/-!
# Direct native clock and height specification

The input is the three held raw banks of the compiler. The row below is the
clock/height mathematical operation, not an evaluation of the instruction
list. Only the separate register readout uses the literal output indices.
-/

namespace L4.Compiler.Native
open Interp

/-- The eight fields common to each of a word's two snapshots. -/
structure Snapshot where
  x : Nat := 0
  d : Nat := 0
  z : Nat := 0
  proposal : Nat := 0
  anchor : Bool := false
  home : Bool := false
  role : Bool := false
  approve : Bool := false
deriving DecidableEq, Repr

/-- A decoded clock together with its previous and current snapshots. -/
structure NativeRecord where
  tick : Nat
  err : Bool
  prior : Snapshot
  curr : Snapshot
deriving DecidableEq, Repr

/-- One candidate bank, in the order used by the publication layer. -/
structure Output where
  digits : Fin 9 → Nat
  hdr : Fin 9 → Bool

def modulus (r : Nat) : Nat := 16 ^ r

def heightMod (r : Nat) : Nat := 16 ^ (r - 2)

/-- Clamp raw input words to the digit budget; heights, distances and
proposals then use the smaller height modulus in both snapshots. -/
def decodeBank (r : Nat) (bank : Bank) (side : Fin 3) : NativeRecord :=
  let raw := fun f => bank.digits side f % modulus r
  let bit := bank.hdr side
  let snap := fun (i : Nat) =>
    let f := fun j => raw (⟨(i+j)%9, Nat.mod_lt _ (by decide)⟩ : Fin 9)
    let q := fun j => bit (⟨(i+j)%9, Nat.mod_lt _ (by decide)⟩ : Fin 9)
    { x := f 0 % heightMod r, d := f 1 % heightMod r,
      z := f 2, proposal := f 3 % heightMod r,
      anchor := q 0, home := q 1, role := q 2, approve := q 3 : Snapshot }
  let err := bit 0
  let tick := raw 0
  ⟨if err && decide (modulus r / 2 ≤ tick) then 0 else tick, err, snap 1, snap 5⟩

/-- The five prioritized clock outcomes of the biased clock row. -/
inductive ClockAction where
  | reset
  | propagate (tick : Nat)
  | clear
  | inc (tick : Nat)
  | hold
deriving DecidableEq, Repr

def successor (m t : Nat) : Nat :=
  if t = m-1 then m/2 else t+1

/-- The independent four-guard clock row. -/
def nativeClock (m : Nat) (left center right : NativeRecord) : ClockAction :=
  let t := center.tick
  let p := m/2
  let lowerErr := fun y : NativeRecord => y.err && decide (y.tick < t)
  let upperGap := fun y : NativeRecord =>
    decide (t+2 ≤ y.tick) && !(decide (t=p) && decide (y.tick=m-1))
  let root := if center.err then !(lowerErr left || lowerErr right)
    else upperGap left || upperGap right
  let proposal := fun y : NativeRecord =>
    if y.err && decide (y.tick+1<p) && decide (y.tick+1<t) then y.tick+1 else t
  let least := min (proposal left) (proposal right)
  let near := fun y : NativeRecord => decide (y.tick ≤ t+1) && decide (t ≤ y.tick+1) &&
    (decide (y.tick ≤ t) || !y.err)
  let s := successor m t
  let atFront := fun y : NativeRecord => decide (y.tick=t) || decide (y.tick=s)
  if root && !(center.err && decide (t=0)) then .reset
  else if least<t then .propagate least
  else if center.err && near left && near right then .clear
  else if !center.err && atFront left && atFront right then .inc s
  else .hold

def neighborView (t : Nat) (y : NativeRecord) : Snapshot :=
  if y.tick=t then y.curr else y.prior

/-- One synchronous edit. Every RHS reads the old snapshot; in
particular phase 1 uses the old center distance, not the new one. -/
def phaseUpdate (B phase : Nat) (left center right : Snapshot) (delta : Bool) :
    Snapshot :=
  match phase with
  | 0 => { center with anchor := decide (center.x ≤ left.x) }
  | 1 =>
    let period := 8*center.d+8
    { center with
      d := if right.anchor then 1 else min (B-1) (right.d+1)
      z := if !center.anchor then 0
           else if center.z=0 then period else min period (center.z-1)
      home := center.anchor && (if center.z=0 then delta else center.home) }
  | 2 => { center with role := if center.anchor then center.home else left.role }
  | 3 =>
    -- Add B before subtraction, then reduce the proposal for both roles.
    let proposal := if center.role then
      if right.anchor then B-1 else right.x+B-1
      else if center.anchor then 0 else left.x+1
    { center with proposal := proposal % B }
  | 4 => { center with approve := center.anchor || decide (left.proposal < center.proposal) }
  | 5 => { center with x := if center.approve && right.approve then center.proposal else center.x }
  | _ => center

def pendingNeed (act : ClockAction) (center : NativeRecord) : Bool :=
  match act with
  | .inc _ => decide (center.tick%32=1) && center.curr.anchor && decide (center.curr.z=0)
  | _ => false

/-- Assemble the new clock and snapshots; only phase 1 can depend on delta. -/
def finishNative (B : Nat) (left center right : NativeRecord)
    (act : ClockAction) (delta : Bool) : NativeRecord :=
  match act with
  | .reset => ⟨0, true, {}, {}⟩
  | .propagate t => ⟨t, true, {}, {}⟩
  | .clear => ⟨center.tick, false, {}, {}⟩
  | .hold => center
  | .inc t =>
    let L := neighborView center.tick left
    let R := neighborView center.tick right
    ⟨t, false, center.curr, phaseUpdate B (center.tick%32) L center.curr R delta⟩

/-- Native register order: clock, four prior words, four current words;
error, four prior flags, four current flags. -/
def encodeOutput (y : NativeRecord) : Output :=
  let digits := [y.tick,y.prior.x,y.prior.d,y.prior.z,y.prior.proposal,
    y.curr.x,y.curr.d,y.curr.z,y.curr.proposal]
  let hdr := [y.err,y.prior.anchor,y.prior.home,y.prior.role,y.prior.approve,
    y.curr.anchor,y.curr.home,y.curr.role,y.curr.approve]
  ⟨fun i => digits.getD i.val 0, fun i => hdr.getD i.val false⟩

/-- Independent native mathematical row for both possible publication choices. -/
def nativeSpec (r : Nat) (bank : Bank) : Bool × (Bool → Output) :=
  let L := decodeBank r bank 0
  let C := decodeBank r bank 1
  let R := decodeBank r bank 2
  let act := nativeClock (modulus r) L C R
  (pendingNeed act C, fun delta => encodeOutput (finishNative (heightMod r) L C R act delta))

/-- Observe the emitted NEED register in a completed value file. -/
def readNeed (regs : List Value) : Bool :=
  (readReg regs needIx).asBool

/-- Observe the emitted nine words and nine bits of the chosen candidate. -/
def readOut (regs : List Value) (delta : Bool) : Output :=
  let ix := outIx delta
  ⟨fun i => (readReg regs (ix.1 i)).asWord,
   fun i => (readReg regs (ix.2 i)).asBool⟩

end L4.Compiler.Native
