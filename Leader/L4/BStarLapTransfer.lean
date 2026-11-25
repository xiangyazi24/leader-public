import Leader.L4.AllSizeProtocol

/-! Guard states are decoded before decisions. Explicit
writes canonicalize their field, while unassigned raw spare bits are held.
A low-first byte packing is not the production layout. -/
namespace L4.BStarLapTransfer
open AllSizeProtocol

structure Raw where
  a : BitVec 3
  b : BitVec 3
  pc : BitVec 2
  deriving DecidableEq, Repr

structure Site where
  a : Nat
  b : Nat
  pc : Nat
  deriving DecidableEq, Repr

def get (x : BitVec 8) : Raw :=
  ⟨H5.aField.read x,H5.bField.read x,H5.pcField.read x⟩

def normal (max x : Nat) : Nat := if x≤max then x else 0

def decode (x : Raw) : Site :=
  ⟨normal 5 x.a.toNat,normal 5 x.b.toNat,normal 2 x.pc.toNat⟩

inductive Set where
  | a (v : Nat) | b (v : Nat) | pc (v : Nat)
  deriving DecidableEq, Repr

inductive Writes where
  | skip
  | one (s : Set)
  | thenDo (l r : Writes)
  deriving DecidableEq, Repr

infixl:70 " ⋙ " => Writes.thenDo
private abbrev A (v : Nat) := Writes.one (.a v)
private abbrev B (v : Nat) := Writes.one (.b v)
private abbrev PC (v : Nat) := Writes.one (.pc v)

def Set.patch : Set → Patch 8
  | .a n => H5.aField.assign (BitVec.ofNat 3 n)
  | .b n => H5.bField.assign (BitVec.ofNat 3 n)
  | .pc n => H5.pcField.assign (BitVec.ofNat 2 n)

def Writes.patch : Writes → Patch 8
  | .skip => .empty _
  | .one s => s.patch
  | .thenDo l r => l.patch.compose r.patch

def Set.raw (s : Set) (x : Raw) : Raw :=
  match s with
  | .a n => {x with a:=BitVec.ofNat 3 n}
  | .b n => {x with b:=BitVec.ofNat 3 n}
  | .pc n => {x with pc:=BitVec.ofNat 2 n}

def Writes.raw : Writes → Raw → Raw
  | .skip, x => x
  | .one s, x => s.raw x
  | .thenDo l r, x => r.raw (l.raw x)

theorem lower_set (s : Set) (x : BitVec 8) : get (s.patch.apply x)=s.raw (get x) := by
  cases s <;>
    (first | simp [get,Set.patch,Set.raw,Field.read_assign,
      Field.read_other_assign H5.aField H5.bField _ _ (by decide),
      Field.read_other_assign H5.aField H5.pcField _ _ (by decide),
      Field.read_other_assign H5.bField H5.aField _ _ (by decide),
      Field.read_other_assign H5.bField H5.pcField _ _ (by decide),
      Field.read_other_assign H5.pcField H5.aField _ _ (by decide),
      Field.read_other_assign H5.pcField H5.bField _ _ (by decide)])

theorem lower_run (s : Writes) (x : BitVec 8) : get (s.patch.apply x)=s.raw (get x) := by
  induction s generalizing x with
  | skip =>
    have h : (Patch.empty 8).apply x=x := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      exact Patch.hold _ _ _ (by simp [Patch.empty])
    exact congrArg get h
  | one s => exact lower_set s x
  | thenDo l r hl hr => rw [Writes.patch,Patch.compose_apply,hr,hl,Writes.raw]

def front (t : Nat) : Bool := t==2 || t==3
def back (t : Nat) : Bool := t==4 || t==5
def flag (hit : Bool) : Nat := if hit then 3 else 2
def touched (w : Nat → Writes) (t : Nat) (hit : Bool) : Writes :=
  if front t then w (flag hit) else .skip

def plan (u v : Site) (ra rb na nb : Bool) (before ordinary : Pair Bool) :
    Pair Writes × Bool :=
  let seed := rb && nb && (v.pc==2)
  let seenL := fun t : Nat => t==3 || before.1 || ordinary.1 || seed
  let seenR := fun t : Nat => t==3 || before.2 || ordinary.2
  let crossed := before.1 && !ordinary.1 && ordinary.2
  let seenHop := fun t : Nat => t==3 || before.2 || ordinary.1 || seed || crossed
  let l := touched A u.a (seenL u.a) ⋙ touched B u.b (seenL u.b)
  let r := touched A v.a (seenR v.a) ⋙ touched B v.b (seenR v.b)
  let out := fun t => if ra then B t else A t
  let q := if ra then u.b else u.a
  let p := v.a
  let routed :=
    if front p then (l ⋙ out (flag (seenHop p)),r ⋙ A 1)
    else if back q then (l ⋙ out 0,r ⋙ A q)
    else if p==1 && q==0 then (l,r ⋙ A 0)
    else (l,r)
  let l := routed.1
  let r := routed.2
  let l :=
    if ra then
      if u.pc==0 then l ⋙ A (flag (seenL 2)) ⋙ PC 1
      else if u.pc==1 && (back u.a || u.a==0) then
        l ⋙ A 0 ⋙ PC (if u.a==4 then 2 else 0)
      else l
    else l
  let r :=
    if rb then
      let r := if front v.b then r ⋙ B (if seenR v.b then 5 else 4)
               else if v.b==1 then r ⋙ B 0
               else r
      if v.pc==2 then r ⋙ PC 0 else r
    else r
  let discard := B 0 ⋙ PC 0
  ((if ra&&na then l else l ⋙ discard,
    if rb&&nb then r else r ⋙ discard), seed)

def oldPlan (old : Pair (BitVec 8)) (oldRef newRef : Pair RefView)
    (before ordinary : Pair Bool) :=
  plan (decode (get old.1)) (decode (get old.2))
    (H5.seesReference oldRef.1) (H5.seesReference oldRef.2)
    (H5.seesReference newRef.1) (H5.seesReference newRef.2) before ordinary

private theorem app_if {α β : Type} (f : α → β) (c : Prop) [Decidable c]
    (a b : α) : f (if c then a else b)=if c then f a else f b := by
  by_cases h:c <;> simp [h]

private theorem lower_if (c : Prop) [Decidable c] (a b : Writes) :
    (if c then a else b).patch=if c then a.patch else b.patch :=
  app_if Writes.patch c a b

private theorem first_if {α : Type} (c : Prop) [Decidable c] (a b : Pair α) :
    (if c then a else b).1=if c then a.1 else b.1 :=
  app_if Prod.fst c a b

private theorem second_if {α : Type} (c : Prop) [Decidable c] (a b : Pair α) :
    (if c then a else b).2=if c then a.2 else b.2 :=
  app_if Prod.snd c a b

theorem patch_transfer (old : Pair (BitVec 8)) (oldRef newRef : Pair RefView)
    (before ordinary : Pair Bool) :
    let p := oldPlan old oldRef newRef before ordinary
    H5.row old oldRef newRef before ordinary=⟨(p.1.1.patch,p.1.2.patch),(p.2,false)⟩ := by
  unfold H5.row oldPlan plan
  cases H5.seesReference oldRef.1 <;>
    simp only [Bool.false_eq_true,if_false,if_true,
      touched,lower_if,first_if,second_if,Writes.patch,Set.patch] <;> rfl

theorem raw_transfer (old : Pair (BitVec 8)) (oldRef newRef : Pair RefView)
    (before ordinary : Pair Bool) :
    let p := oldPlan old oldRef newRef before ordinary
    let r := H5.row old oldRef newRef before ordinary
    (get (r.slots.1.apply old.1),get (r.slots.2.apply old.2),r.seed)=
       (p.1.1.raw (get old.1),p.1.2.raw (get old.2),(p.2,false)) := by
  dsimp only
  rw [patch_transfer,lower_run,lower_run]

/-- Direct typed setter interpretation, with spare codes quotiented only at
the readout boundary. The tables themselves issue only canonical constants or
a decoded D0/D1, never an out-of-range code. -/
def Set.site (s : Set) (x : Site) : Site :=
  match s with
  | .a n => {x with a:=normal 5 (n%8)}
  | .b n => {x with b:=normal 5 (n%8)}
  | .pc n => {x with pc:=normal 2 (n%4)}

def Writes.site : Writes → Site → Site
  | .skip, x => x
  | .one s, x => s.site x
  | .thenDo l r, x => r.site (l.site x)

theorem decode_set (s : Set) (x : Raw) : decode (s.raw x)=s.site (decode x) := by
  cases s <;> rfl

theorem decode_run (s : Writes) (x : Raw) : decode (s.raw x)=s.site (decode x) := by
  induction s generalizing x with
  | skip => rfl
  | one s => exact decode_set s x
  | thenDo l r hl hr => rw [Writes.raw,hr,hl,Writes.site]

theorem decoded_transfer (old : Pair (BitVec 8)) (oldRef newRef : Pair RefView)
    (before ordinary : Pair Bool) :
    let p := oldPlan old oldRef newRef before ordinary
    let r := H5.row old oldRef newRef before ordinary
    (decode (get (r.slots.1.apply old.1)),decode (get (r.slots.2.apply old.2)),r.seed)=
       (p.1.1.site (decode (get old.1)),p.1.2.site (decode (get old.2)),(p.2,false)) := by
  dsimp only
  have h := congrArg (fun (x : Raw × Raw × Pair Bool) =>
    (decode x.1,decode x.2.1,x.2.2)) (raw_transfer old oldRef newRef before ordinary)
  simpa only [decode_run] using h

private def ref (b : Bool) : RefView := ⟨b,b⟩

/-- The F0 token hops right-to-left, opposite the old mark moving
left-to-right. Neither destination-old nor source-ordinary sees the mark;
the crossing nevertheless upgrades it to F1. -/
theorem opposite_hop_fixture :
    let x : Pair (BitVec 8) := (0,64)
    let r := H5.row x (ref false,ref false) (ref false,ref false) (true,false) (false,true)
    decode (get (r.slots.1.apply x.1)) = ⟨3,0,0⟩ ∧
      decode (get (r.slots.2.apply x.2)) = ⟨1,0,0⟩ ∧ r.seed=(false,false) := by decide

/-- Retaining a reference does not physically canonicalize its unused old
spare B field, even though the Python typed output decodes it as E. -/
theorem held_spare_fixture :
    let x : Pair (BitVec 8) := (28,0)
    let r := H5.row x (ref true,ref false) (ref true,ref false) (false,false) (false,false)
    (get (r.slots.1.apply x.1)).b=7 ∧
      (decode (get (r.slots.1.apply x.1))).b=0 := by decide

end L4.BStarLapTransfer

