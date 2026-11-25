import Leader.L4.ShortReadReverseChart
import Leader.L4.ShortControllerEntrance

namespace L4.ShortReadReturnPC
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortReadReturnHop ShortControllerEntrance

private theorem read_covered {n m : Nat} (a : Field 96 n) (b : Field 96 m)
    (v : BitVec m) (x : BitVec 96)
    (lo : b.offset≤a.offset) (hi : a.offset+n≤b.offset+m) :
    a.read ((b.assign v).apply x)=a.read ((b.assign v).apply 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i ilt
  have H := (b.inMask v (a.offset+i)).mpr ⟨by omega,by omega⟩
  simp only [Field.read,BitVec.getLsbD_extractLsb',ilt,decide_true,Bool.true_and]
  rw [Patch.write _ _ _ H,Patch.write _ _ _ H]

/-- The literal WAIT3 door enters ISSUE4 for a canonical successful
reply and ISSUE0 for the wire denial. It does not latch a denial as
a successful file. This contract is local to the actual consumed reply. -/
theorem consume_pc {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true)
    (W : ShortReadReverseChart.Wait3 x (rightNeighbor e))
    (ok : Bool) (d : Fin 64)
    (D : (kField 0).read (x (rightNeighbor e)).mis1=encode (readReply ok d)) :
    pc (rawNext s x e (rightNeighbor e)).mis1=(if ok then 12 else 8) := by
  let old := (x (rightNeighbor e)).mis1
  have H := oldK_readReply true old 0 ok d D
  obtain ⟨b,_,A⟩ := ShortControllerMIS1.source_door_raw x e sep head
  have P := A (lane 78 5 (by decide)) (by decide)
  change (lane 78 5 (by decide)).read (rawNext s x e (rightNeighbor e)).mis1 =
    (lane 78 5 (by decide)).read (match (source old (oldK true old 0)).2 with
      | none => (source old (oldK true old 0)).1.apply b
      | some q => (putK 0 q).apply ((source old (oldK true old 0)).1.apply b)) at P
  let f := lane 78 5 (by decide)
  have p : get old 81 2 (by decide)=2 := W.1
  have o : get old 78 3 (by decide)=3 := W.2
  change pc (rawNext s x e (rightNeighbor e)).mis1=_
  unfold pc
  change (f.read (rawNext s x e (rightNeighbor e)).mis1).toNat=_
  rw [show f.read (rawNext s x e (rightNeighbor e)).mis1=_ from P,H]
  cases ok
  · have K : source old (readReply false d)=(resetSource,some E) := by simp [source,p,o,readReply]
    rw [K]
    change (f.read ((kField 0).assign (encode E) |>.apply (resetSource.apply b))).toNat=8
    rw [Field.read_other_assign f (kField 0) _ _ (.inr (by decide))]
    unfold resetSource put
    rw [read_covered _ _ _ _ (by decide) (by decide)]
    decide
  · have K : source old (readReply true d)=
        (((phaseOp 1 4).compose (put 72 6 (by decide) d.val)).compose
          (put 68 4 (by decide) 0),some E) := by simp [source,p,o,readReply]
    rw [K]
    change (f.read ((kField 0).assign (encode E) |>.apply
      ((((phaseOp 1 4).compose (put 72 6 (by decide) d.val)).compose
          (put 68 4 (by decide) 0)).apply b))).toNat=12
    rw [Field.read_other_assign f (kField 0) _ _ (.inr (by decide)),
      Patch.compose_apply,Patch.compose_apply]
    unfold put
    rw [Field.read_other_assign,Field.read_other_assign]
    · change (f.read ((f.assign (12 : BitVec 5)).apply b)).toNat=12
      rw [Field.read_assign]
      decide
    · exact .inr (by decide)
    · exact .inr (by decide)

#print axioms consume_pc
end L4.ShortReadReturnPC
