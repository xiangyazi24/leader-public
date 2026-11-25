import Leader.L4.ShortControllerMIS1

namespace L4.ShortReadResult
open AllSizeProtocol MISByteCodec PhysicalCustody
open ShortResetMIS1Ring (header)

def fileField : Field 96 6 := lane 72 6 (by decide)

theorem file_bit (x : BitVec 96) (i : Nat) (I : i<6) :
    x.getLsbD (72+i)=(fileField.read x).getLsbD i := by
  simp [fileField,lane,Field.read,I]

/-- A successful READ reply writes its exact six captured bits at the
literal owner door, independently of the responder's other lanes and
the initiator's old bytes. The K0 clear is made by that same mark. -/
theorem successful_read_store {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (eligible : header x (rightNeighbor e)=true)
    (phase : get (x (rightNeighbor e)).mis1 81 2 (by decide)=2)
    (cmd : get (x (rightNeighbor e)).mis1 78 3 (by decide)=3)
    (tag : (oldK true (x (rightNeighbor e)).mis1 0).tag=3)
    (op : (oldK true (x (rightNeighbor e)).mis1 0).opcode=3)
    (live : (oldK true (x (rightNeighbor e)).mis1 0).fault=false)
    (success : (oldK true (x (rightNeighbor e)).mis1 0).outcome=0) :
    let t := oldK true (x (rightNeighbor e)).mis1 0
    let y := (rawNext s x e (rightNeighbor e)).mis1
    (kField 0).read y=encode E ∧ fileField.read y=BitVec.ofNat 6 t.payload := by
  let old := (x (rightNeighbor e)).mis1
  let t := oldK true old 0
  let patch := ((phaseOp 1 4).compose (put 72 6 (by decide) t.payload)).compose
    (put 68 4 (by decide) 0)
  have p : get old 81 2 (by decide)=2 := phase
  have c : get old 78 3 (by decide)=3 := cmd
  have tg : t.tag=3 := tag
  have o : t.opcode=3 := op
  have l : t.fault=false := live
  have k : t.outcome=0 := success
  have sourceEq : source old t=(patch,some E) := by simp [source,p,c,tg,o,l,k,patch]
  obtain ⟨b,_,H⟩ := ShortControllerMIS1.source_door_raw x e sep eligible
  change ∀ {k : Nat} (f : Field 96 k), f.offset+k≤93 →
      f.read (rawNext s x e (rightNeighbor e)).mis1 =
        f.read (match (source old t).2 with
          | none => (source old t).1.apply b
          | some q => (putK 0 q).apply ((source old t).1.apply b)) at H
  rw [sourceEq] at H
  have clear := (H (kField 0) (by decide)).trans (ShortResetFlow.read_putK _ _ _)
  refine ⟨clear,?_⟩
  have W := H fileField (by decide)
  change fileField.read (rawNext s x e (rightNeighbor e)).mis1 =
    fileField.read ((putK 0 E).apply (patch.apply b)) at W
  rw [W]
  rw [show putK 0 E=(kField 0).assign (encode E) from rfl,
    Field.read_other_assign fileField (kField 0) _ _ (.inr (by decide))]
  unfold patch
  rw [Patch.compose_apply,Patch.compose_apply]
  change fileField.read ((lane 68 4 (by decide)).assign (0 : BitVec 4) |>.apply
    ((fileField.assign (BitVec.ofNat 6 t.payload)).apply ((phaseOp 1 4).apply b)))=_
  rw [Field.read_other_assign fileField (lane 68 4 (by decide)) _ _ (.inr (by decide)),
    Field.read_assign]

/-- In the physical source descriptor, bit zero is NOR of the two
captured neighbour values. Selector indices contribute only even terms. -/
theorem descriptor_result (x : BitVec 96) :
    (issuedDescriptor x % 2 == 1)= !(x.getLsbD 74 || x.getLsbD 72) := by
  unfold issuedDescriptor
  let a := get x 76 1 (by decide)
  have H : (a:Nat)≤1 := by
    have h := ((lane 76 1 (by decide)).read x).isLt
    change a<2 at h
    omega
  change ((4*a+2*(1-a)+(!(x.getLsbD 74 || x.getLsbD 72)).toNat)%2 == 1)=_
  have A : a=0 ∨ a=1 := by omega
  rcases A with B|B <;> rw [B] <;> cases (x.getLsbD 74 || x.getLsbD 72) <;> decide

/-- If the two recorded bits equal the protected live neighbour values
at use, the source's descriptor encodes their CURRENT NOR. -/
theorem descriptor_of_protected_reads (x : BitVec 96) (l r : Bool)
    (L : x.getLsbD 74=l) (R : x.getLsbD 72=r) :
    (issuedDescriptor x % 2 == 1)= !(l || r) := by
  rw [descriptor_result,L,R]

#print axioms successful_read_store
#print axioms descriptor_result
#print axioms descriptor_of_protected_reads

/-- The retained six-bit file from READ determines the next descriptor,
even if any number of other sites have taken physical marks. -/
theorem descriptor_of_retained_file (x : BitVec 96) (data : BitVec 6)
    (W : fileField.read x=data) :
    (issuedDescriptor x % 2 == 1)= !(data.getLsbD 2 || data.getLsbD 0) := by
  rw [descriptor_result,show x.getLsbD 74=(fileField.read x).getLsbD 2 from file_bit x 2 (by decide),
    show x.getLsbD 72=(fileField.read x).getLsbD 0 from file_bit x 0 (by decide),W]

theorem successful_read_descriptor {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (eligible : header x (rightNeighbor e)=true)
    (phase : get (x (rightNeighbor e)).mis1 81 2 (by decide)=2)
    (cmd : get (x (rightNeighbor e)).mis1 78 3 (by decide)=3)
    (tag : (oldK true (x (rightNeighbor e)).mis1 0).tag=3)
    (op : (oldK true (x (rightNeighbor e)).mis1 0).opcode=3)
    (live : (oldK true (x (rightNeighbor e)).mis1 0).fault=false)
    (success : (oldK true (x (rightNeighbor e)).mis1 0).outcome=0) :
    let data := BitVec.ofNat 6 (oldK true (x (rightNeighbor e)).mis1 0).payload
    let y := (rawNext s x e (rightNeighbor e)).mis1
    (issuedDescriptor y % 2 == 1)= !(data.getLsbD 2 || data.getLsbD 0) :=
  descriptor_of_retained_file _ _
    (successful_read_store x e sep eligible phase cmd tag op live success).2

#print axioms descriptor_of_retained_file
#print axioms successful_read_descriptor
end L4.ShortReadResult
