import Leader.L4.BStarLongCommand
import Leader.L4.BStarLongPrep

/-! Long COPY binding. Commands, FENCE, LOAD captures, prep
arbitration and data moves use one immutable old pair. -/
namespace L4.BStarLongCommandData
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongPackets
open BStarLongToken BStarLongLayout BStarLongCommand

def prepOf : Nat → Option Prep
  | 0 => some .rstop
  | 1 => some .rclear
  | 6 => some .stop
  | 7 => some .clear
  | 8 => some .load
  | 9 => some .enable
  | 10 => some .inject
  | _ => none

def fenceSheet (g : LongGeometry) (j : Fin 11) : Option Sheet :=
  match j.val with
  | 6 => some .ls
  | 7 => if g.inside then some .ld else none
  | 9 => if g.inside then some .rs else none
  | 10 => some .rd
  | _ => none

inductive Fence where
  | advance | hold | fault
  deriving DecidableEq, Repr

def fence (x : Lane) (requireRetained : Bool) : Fence :=
  if !x.gate || x.error then .fault
  else if x.mobile != .empty then .hold
  else if requireRetained && !BStarLongPrep.validPayload x.retained then .fault
  else .advance

theorem fence_closed (x : Lane) (b : Bool) (h : x.gate=false) : fence x b=.fault := by
  simp [fence,h]

theorem fence_occupied (x : Lane) (b : Bool) (hg : x.gate=true) (he : x.error=false)
    (hm : x.mobile≠.empty) : fence x b=.hold := by simp [fence,hg,he,hm]

theorem fence_good (x : Lane) (b : Bool) (hg : x.gate=true) (he : x.error=false)
    (hm : x.mobile=.empty) (hr : b=false ∨ BStarLongPrep.validPayload x.retained=true) :
    fence x b=.advance := by
  rcases hr with h|h <;> simp [fence,hg,he,hm,h]

/-- COPY's six-bit capture in L,C,R high-to-low order. Spare index 3
is invalid here, never silently redirected to bank zero. -/
def captureIndex (p : Payload) (j : Fin 3) : Option (Fin 3) :=
  let k := p.argument.toNat / 4^(2-j.val) % 4
  if hk : k<3 then some ⟨k,hk⟩ else none

def oldBankPacket (raw : BitVec LW) (k : Fin 3) : Digit9 :=
  .data ((bankPart k 9 36 (by decide)).read raw)

def loadPayload (x : Pair (BitVec LW)) (a : At Sheet) (p : Payload) : Digit9 :=
  match captureIndex p (if a.occurrence==.ls then 0 else 2) with
  | some k => oldBankPacket (lane (a.side == .right) x) k
  | none => .bad

def fieldOffers (g : Pair LongGeometry) (x : Pair (BitVec LW)) (a : At (Fin 11)) (p : Payload) :
    List BStarLongPrep.Offer :=
  if p.fault != 0 then [] else
  match prepOf p.opcode.toNat with
  | none => []
  | some op => (prepClaims (geometry g a.side) a op).map fun c =>
      ⟨c,if op==.load then loadPayload x c.lane p else .empty⟩

def failedPayload : Payload := ⟨1,0,0,0,0⟩

theorem failedPayload_canonical : Token.forward failedPayload=fault false := rfl

def checkFence (g : Pair LongGeometry) (old : At Sheet → Lane)
    (a : At (Fin 11)) (p : Payload) : Fence :=
  if p.fault != 0 || p.opcode.toNat != 11 then .advance else
  match fenceSheet (geometry g a.side) a.occurrence with
  | none => .advance
  | some sh =>
    let s := At.mk a.side sh
    fence (old s) (retains g s)

def checkOffer (g : Pair LongGeometry) (old : At Sheet → Lane)
    (v : CommandClaim × BStarLongCommand.Offer) : BStarLongCommand.Offer :=
  match v.2 with
  | .advance p =>
    match checkFence g old v.1.source p with
    | .advance => .advance p
    | .hold => .hold
    | .fault => .advance failedPayload
  | t => t

def oldTokens (x : Pair (BitVec LW)) (a : At (Fin 11)) : Token :=
  BStarLongToken.atSite (lane (a.side == .right) x) a.occurrence

def gated (g : Pair LongGeometry) (x : Pair (BitVec LW)) :
    List (CommandClaim × BStarLongCommand.Offer) :=
  (offersOn g (oldTokens x)).map fun m => (m.1,checkOffer g (BStarLongPrep.view x) m)

def preparedBy (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (L : List (CommandClaim × BStarLongCommand.Offer)) : List BStarLongPrep.Offer :=
  L.flatMap fun m =>
    match m.2 with
    | .advance p => fieldOffers g x m.1.source p
    | _ => []

def cancel (faults : List (At (Fin 11))) (m : CommandClaim × BStarLongCommand.Offer) :
    CommandClaim × BStarLongCommand.Offer :=
  match m.2 with
  | .advance p => if m.1.source∈faults then (m.1,.advance failedPayload) else (m.1,.advance p)
  | _ => m

structure Round where
  offered : List (CommandClaim × BStarLongCommand.Offer)
  prep : List BStarLongPrep.Offer
  faults : List (At (Fin 11))
  writes : List (Write LW)

def round (g : Pair LongGeometry) (x : Pair (BitVec LW)) : Round :=
  let checked := gated g x
  let P := preparedBy g x checked
  let old := BStarLongPrep.view x
  let faults := BStarLongPrep.prepFaults old P
  ⟨checked.map (cancel faults),P,faults,BStarLongPrep.writes g old P⟩

def patch (g : Pair LongGeometry) (x : Pair (BitVec LW)) : Pair (Patch LW) :=
  BStarTrace.lower ((round g x).writes.map Write.patch)

theorem round_transfer (g : Pair LongGeometry) (x : Pair (BitVec LW)) :
    BStarLongPrep.view (patchPair (patch g x) x) =
      (BStarLongPrep.assignments g (BStarLongPrep.view x) (round g x).prep).foldl
        BStarLongPrep.update (BStarLongPrep.view x) :=
  BStarLongPrep.round_transfer g x (round g x).prep

theorem cancel_hit (F : List (At (Fin 11))) (c : CommandClaim) (p : Payload)
    (h : c.source∈F) : cancel F (c,.advance p)=(c,.advance failedPayload) := by
  simp [cancel,h]

private def inBody : LongGeometry :=
  ⟨⟨false,false,false,false,false,false⟩,true,false,2,false⟩

private def fixturePayload (op a : Nat) : Payload :=
  ⟨0,BitVec.ofNat 9 op,0,0,BitVec.ofNat 34 a⟩

/-- COPY consumes its L/R captured selectors (not the local selector).
Two LOADs here see the same old banks; no grant/door action is needed. -/
theorem copy_capture_fixture :
    let g := (inBody,inBody)
    let load := Token.forward (fixturePayload 8 33)
    let left := ((bankPart 2 9 36 (by decide)).assign 7).apply
      (((bankPart 1 9 36 (by decide)).assign 12).apply 0)
    let raw := ((setToken 2 load).apply ((setToken 0 load).apply left),(0 : BitVec LW))
    let out := patchPair (patch g raw) raw
    (BStarLongPrep.view out (L Sheet.ls)).frozen=.data 7 ∧
    (BStarLongPrep.view out (L Sheet.rs)).frozen=.data 12 ∧
    (round g raw).faults=[] ∧
    captureIndex (fixturePayload 8 49) 0=none := by
  decide +kernel

/-- A closed occupied lane faults before testing queue occupancy. Open
occupied FENCE holds on the selected command and emits no prep. -/
theorem fence_held_fixture :
    let g := (inBody,inBody)
    let packet := Leaf.mobile (.data 5)
    let sender := setToken 6 (.forward (fixturePayload 11 0))
    let closed := sender.apply ((packet.assign 0).apply 0)
    let opened := ((Leaf.gate true).assign 0).apply closed
    let check := fun raw : BitVec LW => (round g (raw,0)).offered
    (link (L 6) (R 6),BStarLongCommand.Offer.advance failedPayload)∈check closed ∧
    (link (L 6) (R 6),BStarLongCommand.Offer.hold)∈check opened ∧
    (round g (opened,0)).prep=[] := by
  decide +kernel

theorem claims_unchanged (g : Pair LongGeometry) (x : Pair (BitVec LW)) :
    (round g x).offered.map Prod.fst=orderedCommands g := by
  have fst_cancel (f : List (At (Fin 11))) (m : CommandClaim × BStarLongCommand.Offer) :
      (cancel f m).1=m.1 := by
    obtain ⟨c,o⟩ := m
    cases o <;> simp [cancel]
    split <;> rfl
  unfold round gated
  simp only [List.map_map,Function.comp_def,fst_cancel,classified_claims]

theorem held_on_fence (g : Pair LongGeometry) (old : At Sheet → Lane)
    (c : CommandClaim) (p : Payload) (h : checkFence g old c.source p=.hold) :
    checkOffer g old (c,.advance p)=.hold := by
  simp [checkOffer,h]

end L4.BStarLongCommandData
