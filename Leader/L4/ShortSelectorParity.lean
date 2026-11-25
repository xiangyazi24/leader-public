import Leader.L4.MISByteCodec

namespace L4.ShortSelectorParity
open MISByteCodec AllSizeProtocol

theorem selector_toNat (v : BitVec 96) :
    get v 92 1 (by decide) = (v.getLsbD 92).toNat := by
  unfold MISByteCodec.get lane Field.read
  rw [BitVec.extractLsb'_toNat]
  rw [Nat.shiftRight_eq_div_pow]
  rw [BitVec.getLsbD]
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have B : v.toNat / 2^92 % 2 < 2 := Nat.mod_lt _ (by decide)
  change v.toNat / 2^92 % 2 = (decide (v.toNat / 2^92 % 2 = 1)).toNat
  by_cases H : v.toNat / 2^92 % 2 = 1
  · simp [H]
  · have Z : v.toNat / 2^92 % 2 = 0 := by omega
    simp [Z]

/-- The authenticated old seal supplies the bounded complementary descriptor. -/
theorem seal_descriptor (v : BitVec 96) (p : Nat) (H : readSeal v=some p) :
    p<8 ∧ descValid p=true := by
  unfold readSeal at H
  dsimp only at H
  split at H
  · rename_i V
    have E := Option.some.inj H
    subst p
    exact ⟨Nat.mod_lt _ (by decide), (Bool.and_eq_true_iff.mp V).2⟩
  · contradiction

theorem decoded_descriptor (g : Bool) (x : BitVec 19)
    (tag : (decode g x).tag=2) (op : 4≤(decode g x).opcode)
    (live : (decode g x).fault=false) :
    (decode g x).payload<8 ∧ descValid (decode g x).payload=true := by
  revert tag op live
  unfold decode
  dsimp only
  split
  · intro tag op live; contradiction
  split
  · intro tag op live; contradiction
  split
  · intro tag op live; contradiction
  split
  · by_cases G : (g && (x.extractLsb' 13 3).toNat==2)=true
    all_goals first | rw [if_pos G] | rw [if_neg G]
    all_goals split
    all_goals try (intro tag op live; contradiction)
    all_goals
      rename_i H
      intro tag op live
      let k := (x.extractLsb' 13 3).toNat
      let p := (x.extractLsb' 0 7).toNat
      change 4≤k at op
      have A : k≠3 := by omega
      have B : k≠2 := by omega
      have F : fPayloadSize k=3 := by simp [fPayloadSize,A,B,op]
      change p%2^fPayloadSize k<8 ∧ descValid (p%2^fPayloadSize k)=true
      rw [F]
      have V : descValid p=true := by
        by_cases V : descValid p=true
        · exact V
        · have W : descValid p=false := Bool.eq_false_iff.mpr V
          exact False.elim (H (by
            apply Bool.or_eq_true_iff.mpr
            right
            exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true op, by rw [show descValid (x.extractLsb' 0 7).toNat=false from W]; rfl⟩))
      have D4 : (p%8/4)%2 = (p/4)%2 := by omega
      have D2 : (p%8/2)%2 = (p/2)%2 := by omega
      refine ⟨Nat.mod_lt _ (by decide),?_⟩
      change descValid (p%8)=true
      simpa only [descValid,D4,D2] using V
  · rename_i H
    split <;> intro tag op live <;> exact False.elim (H (by change (x.extractLsb' 17 2).toNat=2 at tag; rw [tag]; decide))

/-- A guarded target selector is the complement of the old raw selector. -/
theorem seal_selector_complement (v : BitVec 96) (p : Nat)
    (sealH : readSeal v=some p) (old : get v 92 1 (by decide)=p/4) :
    ((p/2)%2==1) = !(v.getLsbD 92) := by
  obtain ⟨L,V⟩ := seal_descriptor v p sealH
  rw [selector_toNat] at old
  have h : (p/4)%2 ≠ (p/2)%2 := by simpa [descValid] using V
  have B : (p/2)%2<2 := Nat.mod_lt _ (by decide)
  cases F : v.getLsbD 92
  · rw [F] at old
    simp only [Bool.toNat_false] at old
    have S : (p/2)%2=1 := by omega
    simp [S]
  · rw [F] at old
    simp only [Bool.toNat_true] at old
    have S : (p/2)%2=0 := by omega
    simp [S]

end L4.ShortSelectorParity
