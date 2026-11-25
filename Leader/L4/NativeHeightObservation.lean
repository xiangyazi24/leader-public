import Leader.L4.Compiler.NativeSpec

/-! Exact snapshot observation of the chosen native publication.  This
module makes no assumption about the physical event or the law of BIT. -/
namespace L4.NativeHeightObservation
open Compiler.Native

/-- The chosen output is already an encoded record; this observer
reads its fields without applying incident-input normalization. -/
def observe (out : Output) : NativeRecord :=
  ⟨out.digits 0,out.hdr 0,
    ⟨out.digits 1,out.digits 2,out.digits 3,out.digits 4,
     out.hdr 1,out.hdr 2,out.hdr 3,out.hdr 4⟩,
    ⟨out.digits 5,out.digits 6,out.digits 7,out.digits 8,
     out.hdr 5,out.hdr 6,out.hdr 7,out.hdr 8⟩⟩

@[simp] theorem observe_encode (x : NativeRecord) : observe (encodeOutput x)=x := by
  rcases x with ⟨t,e,⟨x,d,z,p,a,h,r,g⟩,⟨x',d',z',p',a',h',r',g'⟩⟩
  rfl

/-- Every field of the new height record is determined by the exact
old decoded triple and the actual chosen publication bit. -/
theorem publication (r : Nat) (bank : Bank) (δ : Bool) (out : Output)
    (write : out=(nativeSpec r bank).2 δ) :
    let l := decodeBank r bank 0
    let c := decodeBank r bank 1
    let z := decodeBank r bank 2
    match nativeClock (modulus r) l c z with
    | .reset => observe out=⟨0,true,{},{}⟩
    | .propagate t => observe out=⟨t,true,{},{}⟩
    | .clear => observe out=⟨c.tick,false,{},{}⟩
    | .hold => observe out=c
    | .inc t =>
      observe out=⟨t,false,c.curr,
        phaseUpdate (heightMod r) (c.tick%32) (neighborView c.tick l) c.curr
          (neighborView c.tick z) δ⟩ := by
  subst out
  simp only [nativeSpec,observe_encode]
  cases nativeClock (modulus r) (decodeBank r bank 0) (decodeBank r bank 1)
    (decodeBank r bank 2) <;> rfl

/-- A HOLD publication can physically rotate the selected bank. Its
identity here is only the identity of the decoded old centre record. -/
theorem publication_hold (r : Nat) (bank : Bank) (δ : Bool)
    (h : nativeClock (modulus r) (decodeBank r bank 0) (decodeBank r bank 1)
      (decodeBank r bank 2)=.hold) :
    observe ((nativeSpec r bank).2 δ)=decodeBank r bank 1 := by
  have H := publication r bank δ _ rfl
  dsimp only at H
  rwa [h] at H

/-- Read the selected output with the ordinary incident bank codec.
The premises state exactly which modular clamps must be no-ops. -/
def SnapshotInRange (r : Nat) (s : Snapshot) : Prop :=
  s.x<heightMod r ∧ s.d<heightMod r ∧ s.z<modulus r ∧ s.proposal<heightMod r

theorem exposure_roundtrip (r : Nat) (y : NativeRecord) (bank : Bank) (j : Fin 3)
    (digits : bank.digits j=(encodeOutput y).digits)
    (hdr : bank.hdr j=(encodeOutput y).hdr)
    (tick : y.tick<modulus r)
    (lowError : y.err=true → y.tick<modulus r/2)
    (prior : SnapshotInRange r y.prior)
    (curr : SnapshotInRange r y.curr) :
    decodeBank r bank j=y := by
  have factor : heightMod r≤modulus r := by
    unfold heightMod modulus
    exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  rcases y with ⟨t,e,⟨x,d,z,p,a,b,c,h⟩,⟨X,D,Z,P,A,B,C,H⟩⟩
  rcases prior with ⟨px,pd,pz,pp⟩
  rcases curr with ⟨cx,cd,cz,cp⟩
  unfold decodeBank
  rw [digits,hdr]
  change
    (⟨if e && decide (modulus r/2≤t%modulus r) then 0 else t%modulus r,e,
      ⟨x%modulus r%heightMod r,d%modulus r%heightMod r,z%modulus r,
       p%modulus r%heightMod r,a,b,c,h⟩,
      ⟨X%modulus r%heightMod r,D%modulus r%heightMod r,Z%modulus r,
       P%modulus r%heightMod r,A,B,C,H⟩⟩ : NativeRecord)=_
  rw [Nat.mod_eq_of_lt tick,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le px factor),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le pd factor),Nat.mod_eq_of_lt pz,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le pp factor),Nat.mod_eq_of_lt px,
    Nat.mod_eq_of_lt pd,Nat.mod_eq_of_lt pp,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le cx factor),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le cd factor),Nat.mod_eq_of_lt cz,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le cp factor),Nat.mod_eq_of_lt cx,
    Nat.mod_eq_of_lt cd,Nat.mod_eq_of_lt cp]
  cases e with
  | false => rfl
  | true => simp [show ¬ modulus r/2≤t from Nat.not_le.mpr (lowError rfl)]

end L4.NativeHeightObservation
