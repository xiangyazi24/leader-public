import Leader.L4.BStarLongLayout
import Leader.L4.BStarLongClaims

/-! Total Digit9 and COPY lane codecs. Held storage is never repacked;
only a typed leaf assignment canonicalizes that leaf's raw image. -/
namespace L4.BStarLongPackets
open AllSizeProtocol BStarTrace BStarLongLayout

inductive Digit9 where
  | empty
  | data (nibbles : BitVec 36)
  | bad
  deriving DecidableEq, Repr

def Digit9.tag (x : BitVec 38) : BitVec 2 := x.extractLsb' 36 2

def Digit9.read (x : BitVec 38) : Digit9 :=
  if tag x=0 then .empty
  else if tag x=1 then .data (x.extractLsb' 0 36)
  else .bad

def Digit9.pack : Digit9 → BitVec 38
  | .empty => (0 : BitVec 2) ++ (0 : BitVec 36)
  | .data x => (1 : BitVec 2) ++ x
  | .bad => (2 : BitVec 2) ++ (0 : BitVec 36)

theorem Digit9.read_pack (v : Digit9) : read (pack v)=v := by
  cases v with
  | empty => decide
  | bad => decide
  | data x =>
    have H : tag ((1 : BitVec 2) ++ x)=1 := BitVec.extractLsb'_append_eq_left
    have X : ((1 : BitVec 2) ++ x).extractLsb' 0 36=x := BitVec.extractLsb'_append_eq_right
    simp only [read,pack,H,X,show (1 : BitVec 2)≠0 by decide,if_false,if_true]

theorem Digit9.read_bad2 (x : BitVec 38) (h : tag x=2) : read x=.bad := by
  simp [read,h]

theorem Digit9.read_bad3 (x : BitVec 38) (h : tag x=3) : read x=.bad := by
  simp [read,h]

/-- Payload digit order agrees with the high-to-low nine-nibble data lane. -/
def Digit9.nibble (v : Digit9) (i : Fin 9) : Option (BitVec 4) :=
  match v with
  | .data x => some (x.extractLsb' (4*(8-i.val)) 4)
  | _ => none

structure Lane where
  gate : Bool
  error : Bool
  mobile : Digit9
  frozen : Digit9
  retained : Digit9
  deriving DecidableEq, Repr

def readBit (f : Field LW 1) (x : BitVec LW) : Bool := (f.read x).getLsbD 0

def readLane (s : Fin 4) (x : BitVec LW) : Lane :=
  ⟨readBit (laneGate s) x,readBit (laneError s) x,
   Digit9.read ((laneMobile s).read x),Digit9.read ((laneFrozen s).read x),
   Digit9.read ((laneRetained s).read x)⟩

inductive Leaf where
  | gate (b : Bool)
  | error (b : Bool)
  | mobile (v : Digit9)
  | frozen (v : Digit9)
  | retained (v : Digit9)
  deriving DecidableEq, Repr

def Leaf.put : Leaf → Lane → Lane
  | .gate b,l => {l with gate:=b}
  | .error b,l => {l with error:=b}
  | .mobile p,l => {l with mobile:=p}
  | .frozen p,l => {l with frozen:=p}
  | .retained p,l => {l with retained:=p}

def Leaf.offset : Leaf → Nat
  | .gate _ => 115
  | .error _ => 114
  | .mobile _ => 76
  | .frozen _ => 38
  | .retained _ => 0

def Leaf.width : Leaf → Nat
  | .gate _ | .error _ => 1
  | _ => 38

theorem Leaf.fits (a : Leaf) : a.offset+a.width≤116 := by
  cases a <;> simp [Leaf.offset,Leaf.width]

def Leaf.bits : (a : Leaf) → BitVec a.width
  | .gate b | .error b => BitVec.ofBool b
  | .mobile p | .frozen p | .retained p => p.pack

def Leaf.assign (a : Leaf) (s : Fin 4) : Patch LW :=
  (lanePart s a.offset a.width a.fits).assign a.bits

theorem Leaf.mask (a : Leaf) (s : Fin 4) (i : Nat) :
    (a.assign s).mask.getLsbD i=true ↔
      laneBase s+a.offset≤i ∧ i<laneBase s+a.offset+a.width :=
  Field.inMask ..

theorem Leaf.hold_outside (a : Leaf) (s : Fin 4) (x : BitVec LW) (i : Nat)
    (h : i<laneBase s+a.offset ∨ laneBase s+a.offset+a.width≤i) :
    ((a.assign s).apply x).getLsbD i=x.getLsbD i :=
  Field.hold_outside _ _ _ _ h

private theorem read_written (s : Fin 4) (a : Leaf) (x : BitVec LW) :
    (lanePart s a.offset a.width a.fits).read ((a.assign s).apply x)=a.bits :=
  Field.read_assign ..

private theorem read_other (s : Fin 4) (a : Leaf) (x : BitVec LW) (base width : Nat)
    (fit : base+width≤116)
    (disj : base+width≤a.offset ∨ a.offset+a.width≤base) :
    (lanePart s base width fit).read ((a.assign s).apply x)=
      (lanePart s base width fit).read x :=
  Field.read_other_assign _ _ _ _
    (by change laneBase s+base+width≤laneBase s+a.offset ∨
        laneBase s+a.offset+a.width≤laneBase s+base; omega)

set_option linter.unusedSimpArgs false in
theorem readLane_assign (s : Fin 4) (a : Leaf) (x : BitVec LW) :
    readLane s ((a.assign s).apply x)=a.put (readLane s x) := by
  cases a with
  | gate v =>
    have gate := read_written s (Leaf.gate v) x
    have error := read_other s (Leaf.gate v) x 114 1 (by decide) (.inl (by simp [Leaf.offset,Leaf.width]))
    have mobile := read_other s (Leaf.gate v) x 76 38 (by decide) (.inl (by simp [Leaf.offset,Leaf.width]))
    have frozen := read_other s (Leaf.gate v) x 38 38 (by decide) (.inl (by simp [Leaf.offset,Leaf.width]))
    have retained := read_other s (Leaf.gate v) x 0 38 (by decide) (.inl (by simp [Leaf.offset,Leaf.width]))
    simp only [Leaf.offset,Leaf.width,Leaf.bits] at gate error mobile frozen retained
    simp only [readLane,Leaf.put,readBit,laneGate,laneError,laneMobile,laneFrozen,laneRetained,
      gate,error,mobile,frozen,retained,Digit9.read_pack,BitVec.getLsbD_ofBool,decide_true,Bool.true_and]
  | error v =>
    have gate := read_other s (Leaf.error v) x 115 1 (by decide) (.inr (by simp [Leaf.offset,Leaf.width]))
    have error := read_written s (Leaf.error v) x
    have mobile := read_other s (Leaf.error v) x 76 38 (by decide) (.inl (by simp [Leaf.offset,Leaf.width]))
    have frozen := read_other s (Leaf.error v) x 38 38 (by decide) (.inl (by simp [Leaf.offset,Leaf.width]))
    have retained := read_other s (Leaf.error v) x 0 38 (by decide) (.inl (by simp [Leaf.offset,Leaf.width]))
    simp only [Leaf.offset,Leaf.width,Leaf.bits] at gate error mobile frozen retained
    simp only [readLane,Leaf.put,readBit,laneGate,laneError,laneMobile,laneFrozen,laneRetained,
      gate,error,mobile,frozen,retained,Digit9.read_pack,BitVec.getLsbD_ofBool,decide_true,Bool.true_and]
  | mobile v =>
    have gate := read_other s (Leaf.mobile v) x 115 1 (by decide) (.inr (by simp [Leaf.offset,Leaf.width]))
    have error := read_other s (Leaf.mobile v) x 114 1 (by decide) (.inr (by simp [Leaf.offset,Leaf.width]))
    have mobile := read_written s (Leaf.mobile v) x
    have frozen := read_other s (Leaf.mobile v) x 38 38 (by decide) (.inl (by simp [Leaf.offset,Leaf.width]))
    have retained := read_other s (Leaf.mobile v) x 0 38 (by decide) (.inl (by simp [Leaf.offset,Leaf.width]))
    simp only [Leaf.offset,Leaf.width,Leaf.bits] at gate error mobile frozen retained
    simp only [readLane,Leaf.put,readBit,laneGate,laneError,laneMobile,laneFrozen,laneRetained,
      gate,error,mobile,frozen,retained,Digit9.read_pack,BitVec.getLsbD_ofBool,decide_true,Bool.true_and]
  | frozen v =>
    have gate := read_other s (Leaf.frozen v) x 115 1 (by decide) (.inr (by simp [Leaf.offset,Leaf.width]))
    have error := read_other s (Leaf.frozen v) x 114 1 (by decide) (.inr (by simp [Leaf.offset,Leaf.width]))
    have mobile := read_other s (Leaf.frozen v) x 76 38 (by decide) (.inr (by simp [Leaf.offset,Leaf.width]))
    have frozen := read_written s (Leaf.frozen v) x
    have retained := read_other s (Leaf.frozen v) x 0 38 (by decide) (.inl (by simp [Leaf.offset,Leaf.width]))
    simp only [Leaf.offset,Leaf.width,Leaf.bits] at gate error mobile frozen retained
    simp only [readLane,Leaf.put,readBit,laneGate,laneError,laneMobile,laneFrozen,laneRetained,
      gate,error,mobile,frozen,retained,Digit9.read_pack,BitVec.getLsbD_ofBool,decide_true,Bool.true_and]
  | retained v =>
    have gate := read_other s (Leaf.retained v) x 115 1 (by decide) (.inr (by simp [Leaf.offset,Leaf.width]))
    have error := read_other s (Leaf.retained v) x 114 1 (by decide) (.inr (by simp [Leaf.offset,Leaf.width]))
    have mobile := read_other s (Leaf.retained v) x 76 38 (by decide) (.inr (by simp [Leaf.offset,Leaf.width]))
    have frozen := read_other s (Leaf.retained v) x 38 38 (by decide) (.inr (by simp [Leaf.offset,Leaf.width]))
    have retained := read_written s (Leaf.retained v) x
    simp only [Leaf.offset,Leaf.width,Leaf.bits] at gate error mobile frozen retained
    simp only [readLane,Leaf.put,readBit,laneGate,laneError,laneMobile,laneFrozen,laneRetained,
      gate,error,mobile,frozen,retained,Digit9.read_pack,BitVec.getLsbD_ofBool,decide_true,Bool.true_and]

theorem readLane_other (s t : Fin 4) (ne : s≠t) (a : Leaf) (x : BitVec LW) :
    readLane s ((a.assign t).apply x)=readLane s x := by
  have preserve (base width : Nat) (fit : base+width≤116) :
      (lanePart s base width fit).read ((a.assign t).apply x)=(lanePart s base width fit).read x :=
    Field.read_other_assign _ _ _ _ (lanePart_spacing s t ne base width a.offset a.width fit a.fits)
  simp only [readLane,readBit,laneGate,laneError,laneMobile,laneFrozen,laneRetained,preserve]

/-- The complete raw packet (tag AND every payload bit) stays held if a
different leaf is written. In particular even BAD tag 3 is unchanged. -/
theorem raw_mobile_held (s : Fin 4) (a : Leaf) (x : BitVec LW)
    (ne : a.offset≠76) :
    (laneMobile s).read ((a.assign s).apply x)=(laneMobile s).read x := by
  apply read_other
  cases a <;> simp_all [Leaf.offset,Leaf.width]

#print axioms Digit9.read_pack
#print axioms readLane_assign
#print axioms readLane_other
#print axioms raw_mobile_held

theorem raw_frozen_held (s : Fin 4) (a : Leaf) (x : BitVec LW)
    (ne : a.offset≠38) :
    (laneFrozen s).read ((a.assign s).apply x)=(laneFrozen s).read x := by
  apply read_other
  cases a <;> simp_all [Leaf.offset,Leaf.width]

theorem raw_retained_held (s : Fin 4) (a : Leaf) (x : BitVec LW)
    (ne : a.offset≠0) :
    (laneRetained s).read ((a.assign s).apply x)=(laneRetained s).read x := by
  apply read_other
  cases a <;> simp_all [Leaf.offset,Leaf.width]

def Digit9.isBad : Digit9 → Bool
  | .bad => true
  | _ => false

/-- Typed statement-level writes; a selected disabled offer clears the
sender and reports error before examining occupied receiver space. -/
def endEffects (x : Lane) : List Leaf :=
  if x.mobile=.empty then [] else [.mobile .empty,.error true]

def hopEffects (x y : Lane) (retains : Bool) : Pair (List Leaf) :=
  if x.mobile=.empty then ([],[])
  else if !(x.gate && y.gate) then ([.mobile .empty,.error true],[])
  else if y.mobile≠.empty then ([],[])
  else
    let bad := x.mobile.isBad
    let out := [.mobile .empty,.error (x.error || bad)]
    (out, if retains then
      [.retained x.mobile,.mobile y.retained,.error (y.error || bad || y.retained.isBad)]
    else [.mobile x.mobile,.error (y.error || bad)])

def packedLeaves (s : Fin 4) (old : BitVec LW) (L : List Leaf) : BitVec LW :=
  L.foldl (fun x a => (a.assign s).apply x) old

def typedLeaves (old : Lane) (L : List Leaf) : Lane :=
  L.foldl (fun x a => a.put x) old

theorem leaf_fold (s : Fin 4) (x : BitVec LW) (L : List Leaf) :
    readLane s (packedLeaves s x L)=typedLeaves (readLane s x) L := by
  induction L generalizing x with
  | nil => rfl
  | cons a t ih =>
    change readLane s (packedLeaves s ((a.assign s).apply x) t)=
      typedLeaves (a.put (readLane s x)) t
    rw [ih,readLane_assign]

/-- Canonicalization is a write only. A closed or stale spare payload
that was not named by the effect never enters this list. -/
theorem hop_retained_bad (x y : Lane) (hx : x.mobile=.bad) (hg : (x.gate && y.gate)=true)
    (hy : y.mobile=.empty) :
    hopEffects x y true =
      ([.mobile .empty,.error true],
        [.retained .bad,.mobile y.retained,.error true]) := by
  obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp hg
  simp [hopEffects,hx,h₁,h₂,hy,Digit9.isBad]

theorem hop_empty (x y : Lane) (b : Bool) (h : x.mobile=.empty) :
    hopEffects x y b=([],[]) := by simp [hopEffects,h]

theorem hop_open_blocked (x y : Lane) (b : Bool) (h : (x.gate && y.gate)=true)
    (hy : y.mobile≠.empty) : hopEffects x y b=([],[]) := by
  by_cases H : x.mobile=.empty
  · simp [hopEffects,H]
  · obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp h
    simp [hopEffects,H,h₁,h₂,hy]

#print axioms leaf_fold
#print axioms raw_frozen_held
#print axioms raw_retained_held

open BStarLongClaims

def Sheet.index : BStarLongClaims.Sheet → Fin 4
  | .ls => 0
  | .ld => 1
  | .rs => 2
  | .rd => 3

def retains (g : Pair LongGeometry) (s : At Sheet) : Bool :=
  let x := match s.side with | .left => g.1 | .right => g.2
  x.inside && (s.occurrence == .ld || s.occurrence == .rd)

def writeAt (s : At Sheet) (a : Leaf) : Write LW :=
  ⟨s.side == .right,a.width,lanePart (Sheet.index s.occurrence) a.offset a.width a.fits,a.bits⟩

theorem writeAt_patch (s : At Sheet) (a : Leaf) :
    (writeAt s a).patch=(s.side == .right,a.assign (Sheet.index s.occurrence)) := rfl

/-- Emit every selected data statement from the same immutable old
pair. Newly received mobile values cannot circulate on this mark. -/
def dataEffects (g : Pair LongGeometry) (old : At Sheet → Lane)
    (claim : DataClaim) : List (At Sheet × Leaf) :=
  let sender := claim.source
  match claim.kind,claim.destination with
  | .ending,_ => (endEffects (old sender)).map (sender,·)
  | .hop,some receiver =>
    let (ls,rs) := hopEffects (old sender) (old receiver) (retains g receiver)
    ls.map (sender,·) ++ rs.map (receiver,·)
  | .hop,none => []

def dataWrites (g : Pair LongGeometry) (old : At Sheet → Lane)
    (reserved : List (At Sheet)) : List (Write LW) :=
  (orderedData g reserved).flatMap fun c => (dataEffects g old c).map (fun (s,a) => writeAt s a)

theorem end_occupied (x : Lane) (h : x.mobile≠.empty) :
    endEffects x=[.mobile .empty,.error true] := by
  simp [endEffects,h]

theorem hop_disabled (x y : Lane) (b : Bool) (hm : x.mobile≠.empty)
    (hg : (x.gate && y.gate)=false) :
    hopEffects x y b=([.mobile .empty,.error true],[]) := by
  simp [hopEffects,hm,hg]

#print axioms writeAt_patch
#print axioms hop_disabled
end L4.BStarLongPackets
