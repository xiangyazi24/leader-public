import Leader.L4.WidthJoinedProjection

namespace L4.WidthWaitExit
open AllSizeProtocol WidthByteRows WidthChecksum WidthOwnerController PhysicalCustody

private theorem clearDoor_phase {c : Nat} (x : BitVec (W c)) (op a : Nat)
    (O : op≤5) (A : a<4) : phase (c:=c) ((clearDoor c op a).apply x)=1 := by
  unfold clearDoor
  rw [Patch.compose_apply]
  unfold phase WidthByteRows.get tokenPatch
  rw [Field.read_other_assign _ _ _ _ (.inr (by simp [suffixField]))]
  let y := (control c 1 op a).apply x
  have E : ((suffixField c 7 7 (by decide)).read y).extractLsb' 5 2 =
      (suffixField c 7 2 (by decide)).read y := by
    apply BitVec.eq_of_getLsbD_eq
    intro j J
    change ((y.extractLsb' 16 7).extractLsb' 5 2).getLsbD j =
      (y.extractLsb' 21 2).getLsbD j
    have K : 5+j<7 := by omega
    simp only [BitVec.getLsbD_extractLsb',J,K,decide_true,Bool.true_and,←Nat.add_assoc]
  change ((suffixField c 7 2 (by decide)).read y).toNat=1
  rw [←E]
  have F : (suffixField c 7 7 (by decide)).read y=BitVec.ofNat 7 (32+4*op+a) :=
    Field.read_assign _ _ _
  rw [F]
  have H : 32+4*op+a<128 := by omega
  rw [BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt H,Nat.shiftRight_eq_div_pow]
  omega

private theorem reply_arg_cap (x : BitVec 16) (T : (decode x).tag=3) : (decode x).arg<4 := by
  rw [WidthTokenTransport.decode_tag] at T
  simp [decode,faultCode,T]
  split
  · decide
  · split
    · change _ % 4 < 4
      omega
    · split
      · change _ % 2 < 4
        omega
      · change _ % 1 < 4
        omega


theorem incoming_reply_or_empty_phase {c : Nat} (r : Nat) (h : Bool) (u v : BitVec (W c))
    (W : phase (c:=c) v=2)
    (B : (packet (c:=c) v).tag=0 ∨ (packet (c:=c) v).tag=3) :
    phase (c:=c) ((row (c:=c) r (h,true) (u,v)).2.apply v)=1 := by
  let t := packet (c:=c) v
  have norm : ∃ op a, op≤5 ∧ a<4 ∧ doorPatch (c:=c) v t=clearDoor c op a := by
    by_cases O : opcode (c:=c) v≤5
    · rcases B with E|D
      · exact ⟨0,0,by decide,by decide,wait_fault_or_empty v t W O (.inl E)⟩
      · by_cases F : t.fault=true
        · exact ⟨0,0,by decide,by decide,wait_fault_or_empty v t W O (.inr ⟨D,F⟩)⟩
        · by_cases T : t.op=opcode (c:=c) v
          · have J := wait_good_reply v t W O D T (Bool.eq_false_iff.mpr F)
            have cap : t.op≤5 := T ▸ O
            have V : t.op=0 ∨ t.op=1 ∨ t.op=2 ∨ t.op=3 ∨ t.op=4 ∨ t.op=5 := by omega
            rcases V with V|V|V|V|V|V
            · exact ⟨1,0,by decide,by decide,by simpa [V] using J⟩
            · refine ⟨if t.arg==1 then 2 else 5,0,?_,by decide,?_⟩
              · split <;> omega
              · simpa [V] using J
            · exact ⟨3,t.arg,by decide,reply_arg_cap _ D,by simpa [V] using J⟩
            · exact ⟨4,0,by decide,by decide,by simpa [V] using J⟩
            · exact ⟨1,0,by decide,by decide,by simpa [V] using J⟩
            · exact ⟨0,0,by decide,by decide,by simpa [V] using J⟩
          · change t.tag=3 at D
            refine ⟨0,0,by decide,by decide,?_⟩
            simp [doorPatch,show WidthByteRows.get (c:=c) v 7 2 (by decide)=2 from W,
              show ¬5<WidthByteRows.get (c:=c) v 9 3 (by decide) from Nat.not_lt.mpr O,
              D,show t.op≠WidthByteRows.get (c:=c) v 9 3 (by decide) from T,clearDoor]
    · refine ⟨0,0,by decide,by decide,?_⟩
      simp [doorPatch,show 5<WidthByteRows.get (c:=c) v 9 3 (by decide) from by
        exact Nat.lt_of_not_ge O,clearDoor]
  obtain ⟨op,a,O,A,Q⟩ := norm
  change doorPatch (c:=c) v (decode ((suffixField c 14 16 (by decide)).read v))=
    clearDoor c op a at Q
  unfold row
  simp only [Q,if_true,Patch.compose_apply]
  exact clearDoor_phase _ _ _ O A

#print axioms incoming_reply_or_empty_phase
end L4.WidthWaitExit
