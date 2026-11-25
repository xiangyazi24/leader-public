import Leader.L4.BStarLongLayout
import Leader.L4.Compiler.BitField

/-! Link between the normative bit addressing used by the accepted
compiler field proofs and the executable BitVec patches of the joined map.
This imports BitField; it does not replicate the natural-number lemmas. -/
namespace L4.BStarLongFieldBridge
open AllSizeProtocol
open Compiler.BitField

theorem extract_same {W w : Nat} (f : Field W w) (x : BitVec W) :
    (f.read x).toNat=extract x.toNat f.offset w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_extract]
  simp [Field.read]

theorem patch_same {W w : Nat} (f : Field W w) (x : BitVec W) (v : BitVec w) :
    ((f.assign v).apply x).toNat=patch x.toNat f.offset w v.toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_patch]
  change ((f.assign v).apply x).getLsbD i = _
  by_cases h : f.offset≤i ∧ i<f.offset+w
  · rw [if_pos h,Patch.write _ _ _ ((Field.inMask f v i).mpr h)]
    have hi : i<W := Nat.lt_of_lt_of_le h.2 f.fits
    simp [Field.assign,hi,Nat.not_lt.mpr h.1]
    rfl
  · rw [if_neg h]
    exact Patch.hold _ _ _ (Bool.eq_false_iff.mpr (fun hh => h ((Field.inMask f v i).mp hh)))

/-- Once the packed setter is interpreted numerically, any imported
compiler disjoint-field read theorem applies to the joined row's byte. -/
theorem disjoint_read {W w z : Nat} (f : Field W w) (g : Field W z)
    (x : BitVec W) (v : BitVec w)
    (h : f.offset+w≤g.offset ∨ g.offset+z≤f.offset) :
    extract (((f.assign v).apply x).toNat) g.offset z=(g.read x).toNat := by
  rw [patch_same,extract_same,extract_patch_disjoint _ _ _ _ _ _ h]

#print axioms extract_same
#print axioms patch_same
#print axioms disjoint_read
end L4.BStarLongFieldBridge
