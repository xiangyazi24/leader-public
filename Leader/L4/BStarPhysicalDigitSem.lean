import Leader.L4.BStarLongArithmetic
import Leader.L4.Compiler.Digits

/-! Exact raw digit/accumulator refinement for old K1 arithmetic. The
target digit is decoded from the written packed word, not a shadow
arithmetic value. The step operations are the accepted compiler ones. -/
namespace L4.BStarPhysicalDigitSem
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongArithmetic BStarLongRegisters
open L4.Compiler.Digits

def WordSlot (j : Nat) : Prop := widthAt wordWidths j=4

theorem num_lt {j : Nat} (h : WordSlot j) (x : BitVec LW) : num x j<16 := by
  have H := ((numeric j).read x).isLt
  change widthAt wordWidths j=4 at h
  change num x j < 2 ^ widthAt wordWidths j at H
  have E : 2 ^ widthAt wordWidths j = 16 := congrArg (fun n : Nat => 2^n) h
  rw [E] at H
  exact H

def nib (x : BitVec LW) (j : Nat) (h : WordSlot j) : Nib := ⟨num x j,num_lt h x⟩

theorem num_write_of_lt {j v : Nat} (h : WordSlot j) (hv : v<16) (x : BitVec LW) :
    num ((writeNum j v).apply x) j=v := by
  unfold num writeNum
  rw [Field.read_assign,BitVec.toNat_ofNat,show widthAt wordWidths j=4 from h]
  exact Nat.mod_eq_of_lt hv

theorem num_other (i j v : Nat) (h : j≠i) (x : BitVec LW) :
    num ((writeNum i v).apply x) j=num x j := by
  unfold num writeNum
  rw [Field.read_other_assign _ _ _ _ (numeric_distinct _ _ h)]

/-- Small compiler accumulators are represented exactly in the physical
34-bit argument; every other token field is left untouched. -/
def withAcc (p : Payload) (v : Nat) : Payload :=
  {p with argument:=BitVec.ofNat 34 v}

theorem acc_read (p : Payload) (v : Nat) (h : v<2^34) :
    (withAcc p v).argument.toNat=v := by
  simp [withAcc,Nat.mod_eq_of_lt h]

theorem add_row (g : LongGeometry) (x : BitVec LW) (i a b : Nat) (p : Payload)
    (ha : WordSlot a) (hb : WordSlot b) (c : Fin 2) (hc : p.argument.toNat=c.val) :
    let v := addStep (nib x a ha) (nib x b hb) c
    physicalDigit g x i (.add a b) p=(writeNum i v.1.val,withAcc p v.2.val) := by
  simp only [physicalDigit,addStep,nib,hc,withAcc]

theorem sub_row (g : LongGeometry) (x : BitVec LW) (i a b : Nat) (p : Payload)
    (ha : WordSlot a) (hb : WordSlot b) (c : Fin 2) (hc : p.argument.toNat=c.val) :
    let v := subStep (nib x a ha) (nib x b hb) c
    physicalDigit g x i (.sub a b) p=(writeNum i v.1.val,withAcc p v.2.val) := by
  have l := num_lt ha x
  have m := num_lt hb x
  have q := c.isLt
  have E : (num x a + 16 - (num x b + c.val)) % 16 =
      (subStep (nib x a ha) (nib x b hb) c).1.val := by
    by_cases e : num x a < num x b+c.val
    · rw [Nat.mod_eq_of_lt (by omega)]
      have en : (nib x a ha).val < (nib x b hb).val+c.val := e
      simp only [subStep,if_pos en]
      change num x a + 16 - (num x b + c.val) = num x a + 16 - num x b - c.val
      omega
    · rw [show num x a+16-(num x b+c.val)=(num x a-(num x b+c.val))+16 by omega,
        Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
      have en : ¬(nib x a ha).val < (nib x b hb).val+c.val := e
      simp only [subStep,if_neg en]
      change num x a - (num x b + c.val) = num x a - num x b - c.val
      omega
  simp only [physicalDigit,nib,subStep,hc,withAcc] at *
  rw [E]
  rfl

theorem shift_row (g : LongGeometry) (x : BitVec LW) (i a : Nat) (p : Payload)
    (ha : WordSlot a) (c : Fin 8) (hc : p.argument.toNat=c.val) :
    let v := shl3Step (nib x a ha) c
    physicalDigit g x i (.shl3 a) p=(writeNum i v.1.val,withAcc p v.2.val) := by
  simp only [physicalDigit,shl3Step,nib,hc,withAcc]

def cmpPack (eq lt : Bool) : Nat := 2*eq.toNat+lt.toNat

theorem compare_row (g : LongGeometry) (x : BitVec LW) (i a b : Nat) (p : Payload)
    (ha : WordSlot a) (hb : WordSlot b) (eq lt : Bool)
    (h : p.argument.toNat=cmpPack eq lt) :
    let z := cmpStep eq lt (nib x a ha) (nib x b hb)
    physicalDigit g x i (.cmp a b) p=(.empty _,withAcc p (cmpPack z.1 z.2)) := by
  have e : (p.argument.toNat / 2 == 1)=eq := by rw [h]; cases eq <;> cases lt <;> decide
  have l : (p.argument.toNat % 2 == 1)=lt := by rw [h]; cases eq <;> cases lt <;> decide
  simp only [physicalDigit,cmpPack,cmpStep,nib,withAcc,e,l,beq_iff_eq]
  rfl

def off (g : LongGeometry) : Nat := if g.axes.h6 then 0 else min 5 g.offset

/-- Only the first two decisions of the clipped physical offset matter. -/
def ScanPosition (g : LongGeometry) (j : Nat) : Prop :=
  (off g=0 ↔ j=0) ∧ (off g=1 ↔ j=1)

set_option linter.unusedSimpArgs false in
theorem scan_row (g : LongGeometry) (x : BitVec LW) (i a j : Nat) (p : Payload)
    (ha : WordSlot a) (u : Fin 32) (hu : p.argument.toNat=u.val)
    (hpos : ScanPosition g j) (small : j≤1 → u.val<16) :
    physicalDigit g x i (.scan5 a) p =
      (.empty _,withAcc p (scan5Step j u (nib x a ha)).val) := by
  have n := num_lt ha x
  by_cases h0 : j=0
  · have he := hpos.1.mpr h0
    have hlt := small (by omega)
    simp [physicalDigit,scan5Step,nib,withAcc,h0,show (if g.axes.h6 then 0 else min 5 g.offset)=0 from he,
      hu,Nat.div_eq_of_lt hlt]
  · have hz : off g≠0 := h0 ∘ hpos.1.mp
    by_cases h1 : j=1
    · have he := hpos.2.mpr h1
      have hlt := small (by omega)
      have hv : u.val+16*(num x a%2)<32 := by omega
      simp [physicalDigit,scan5Step,nib,withAcc,hu,h0,h1,
        show (if g.axes.h6 then 0 else min 5 g.offset)≠0 from hz,
        show (if g.axes.h6 then 0 else min 5 g.offset)=1 from he,beq_iff_eq,
        Nat.mod_eq_of_lt hlt,Nat.mod_eq_of_lt hv,Prod.mk.injEq]
    · have ho : off g≠1 := h1 ∘ hpos.2.mp
      simp [physicalDigit,scan5Step,nib,withAcc,h0,h1,hu,show (if g.axes.h6 then 0 else min 5 g.offset)≠0 from hz,
        show (if g.axes.h6 then 0 else min 5 g.offset)≠1 from ho]

/-- Previous rows concern the exact handler; this lemma plugs them
into the literal old K1 visit, with padding and inherited faults
excluded by the physical premise. -/
theorem visit_row (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload)
    (i : Nat) (c : L4.Compiler.Native.Code)
    (h1 : j.val=1) (hi : g.inside=true) (hf : p.fault=0)
    (hop : nodeOf p.opcode.toNat=some i) (hc : get i=some c) :
    visit g j x p=physicalDigit g x i c p := by
  simp [visit,h1,hi,hf,hop,hc]

/-- Conditional on the actual physical offset/END readout, the cached
position supplies exactly the tests consumed by the compiler. -/
structure ConstantsPosition (g : LongGeometry) (r j : Nat) : Prop where
  scan : ScanPosition g j
  last : (g.inside && g.last)=decide (j+1=r)
  lastTwo : ((g.inside && g.last) || g.successorEnd)=decide (r≤j+2)

def constDigit (c : L4.Compiler.Native.ConstId) (pos : Position) : Nib :=
  match c with
  | .zero => 0
  | .one => constSmallStep 1 pos
  | .eight => constSmallStep 8 pos
  | .p => constPStep pos
  | .max => constMaxStep
  | .bm1 => constBM1Step pos

set_option linter.unusedSimpArgs false in
theorem const_row (g : LongGeometry) (x : BitVec LW) (i r j : Nat) (p : Payload)
    (c : L4.Compiler.Native.ConstId) (h : ConstantsPosition g r j) :
    physicalDigit g x i (.const c) p=
      (writeNum i (constDigit c (positionAt r j)).val,p) := by
  have hs : (off g==0)=decide (j=0) := by
    by_cases e : j=0
    · simp [e,h.scan.1.mpr e]
    · have ho : off g≠0 := e ∘ h.scan.1.mp
      simp [e,ho]
  have H : ((if g.axes.h6 then 0 else min 5 g.offset)==0)=decide (j=0) := hs
  cases c
  · rfl
  · simp only [physicalDigit,litDigit,constDigit,positionAt,constSmallStep,H]
    by_cases h0 : j=0 <;> simp [h0] <;> rfl
  · simp only [physicalDigit,litDigit,constDigit,positionAt,constPStep,h.last]
    by_cases hl : j+1=r <;> simp [hl] <;> rfl
  · simp only [physicalDigit,litDigit,constDigit,positionAt,constBM1Step,h.lastTwo]
    by_cases hB : r≤j+2 <;> simp [hB] <;> rfl
  · rfl
  · simp only [physicalDigit,litDigit,constDigit,positionAt,constSmallStep,H]
    by_cases h0 : j=0 <;> simp [h0] <;> rfl

theorem mask_row (g : LongGeometry) (x : BitVec LW) (i a r j : Nat) (p : Payload)
    (ha : WordSlot a) (h : ConstantsPosition g r j) :
    physicalDigit g x i (.maskB a) p=
      (writeNum i (maskStep (nib x a ha) (positionAt r j)).val,p) := by
  simp only [physicalDigit, h.lastTwo, maskStep,positionAt]
  by_cases hb : r≤j+2 <;> simp [hb,nib]

theorem mux_row (g : LongGeometry) (x : BitVec LW) (i u a b : Nat) (p : Payload)
    (ha : WordSlot a) (hb : WordSlot b) (q : Bool)
    (hq : (p.argument.toNat%2==1) = q) :
    physicalDigit g x i (.mux u a b) p =
      (writeNum i (muxStep q (nib x a ha) (nib x b hb)).val,p) := by
  simp only [physicalDigit,hq,muxStep]
  cases q <;> rfl

theorem load_center_row (g : LongGeometry) (x : BitVec LW) (i : Nat) (f : Fin 9)
    (p : Payload) (b : Fin 3) (h : p.argument.toNat=b.val) :
    physicalDigit g x i (.load 1 f) p=(writeNum i ((bankDigit b f).read x).toNat,p) := by
  simp [physicalDigit,digitLoad,h,b.isLt]

def wordCheck (i : Nat) : Bool := widthAt wordWidths i==4

/-- Exact widths of literal numeric sources and outputs; irrelevant
opcode kinds do not create an artificial numeric slot. -/
def typedSlots (i : Nat) : L4.Compiler.Native.Code → Bool
  | .load _ _ | .const _ => wordCheck i
  | .maskB a | .shl3 a => wordCheck i && wordCheck a
  | .add a b | .sub a b | .mux _ a b => wordCheck i && wordCheck a && wordCheck b
  | .cmp a b => wordCheck a && wordCheck b
  | .scan5 a => wordCheck a
  | _ => true

def checkedSlotAt (i : Nat) : Bool :=
  match get i with
  | none => false
  | some c => typedSlots i c

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem literal_typing_certificate :
    (List.range 474).all checkedSlotAt=true := by decide +kernel

theorem literal_typed (i : Nat) (c : L4.Compiler.Native.Code)
    (h : get i=some c) : typedSlots i c=true := by
  have hh := List.getElem?_eq_some_iff.mp h
  obtain ⟨hLen,_⟩ := hh
  have hi : i∈List.range 474 := by
    apply List.mem_range.mpr
    simpa only [L4.Compiler.Native.literal_length] using hLen
  have E := List.all_eq_true.mp literal_typing_certificate i hi
  simpa [checkedSlotAt,h] using E

#print axioms const_row
#print axioms mask_row
#print axioms mux_row
#print axioms load_center_row
#print axioms literal_typed
#print axioms num_write_of_lt
#print axioms add_row
#print axioms sub_row
#print axioms shift_row
#print axioms compare_row
#print axioms scan_row
#print axioms visit_row
end L4.BStarPhysicalDigitSem
