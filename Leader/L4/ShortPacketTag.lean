import Leader.L4.ShortResetFlow

namespace L4.ShortPacketTag
open AllSizeProtocol MISByteCodec

/-- The decoder may normalize the payload or declare a fault, but it
never changes the two actual wire tag bits, even when the gate moves. -/
theorem inherited_decode_tag (g : Bool) (x : BitVec 19) :
    (decode g x).tag=(x.extractLsb' 17 2).toNat := by
  unfold decode
  dsimp only
  split
  · rename_i H
    exact (beq_iff_eq.mp H).symm
  split
  · rename_i H
    exact (beq_iff_eq.mp H).symm
  split
  · rfl
  split
  · split <;> split <;> rfl
  · split <;> rfl

/-- Wire encoding cannot overflow into a tag if the exact sum of the
payload/control fields stays below the 17 bits reserved for them. -/
def lowCode (t : Token) : Nat :=
  t.fault.toNat*2^16 + t.opcode*2^13 + t.race*2^10 +
    t.outcome*2^8 + t.applied.toNat*2^7 + t.payload

theorem inherited_encode_tag (t : Token) (g : Bool) (L : lowCode t<2^17)
    (H : t.tag<4) : (decode g (encode t)).tag=t.tag := by
  rw [inherited_decode_tag]
  change ((encode t).extractLsb' 17 2).toNat = t.tag
  rw [BitVec.extractLsb'_toNat, encode, BitVec.toNat_ofNat]
  simp only [Nat.shiftRight_eq_div_pow]
  unfold lowCode at L
  omega

private theorem modulus_payload (op p : Nat) : p % 2^fPayloadSize op<128 := by
  have B : fPayloadSize op≤7 := by
    unfold fPayloadSize
    split
    · decide
    split
    · decide
    split <;> decide
  exact Nat.lt_of_lt_of_le (Nat.mod_lt p (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by decide) B)

private theorem pred_ite {α : Type} (P : α→Prop) (c : Prop) [Decidable c]
    (x y : α) (A : P x) (B : P y) : P (if c then x else y) := by
  by_cases C : c
  · simpa only [if_pos C] using A
  · simpa only [if_neg C] using B

theorem decoded_forward_bounds (g : Bool) (x : BitVec 19)
    (F : (decode g x).tag=2) :
    (decode g x).opcode<8 ∧ (decode g x).race<8 ∧
      (decode g x).outcome=0 ∧ (decode g x).payload<128 := by
  rw [inherited_decode_tag] at F
  have O : (x.extractLsb' 13 3).toNat<8 := (x.extractLsb' 13 3).isLt
  have R : (x.extractLsb' 10 3).toNat<8 := (x.extractLsb' 10 3).isLt
  let P := fun t : Token=>t.opcode<8 ∧ t.race<8 ∧ t.outcome=0 ∧ t.payload<128
  change P (decode g x)
  have bad : P (faultToken 2) := by decide
  unfold decode
  dsimp only
  simp only [F, show ((2:Nat)==0)=false by decide,show ((2:Nat)==1)=false by decide,
    show ((2:Nat)==2)=true by decide,if_true]
  apply pred_ite P _ _ _ bad
  apply pred_ite P _ _ _ bad
  exact ⟨O,R,rfl,modulus_payload _ _⟩

theorem no_kind_change (g h : Bool) (x : BitVec 19) :
    (decode g x).tag=(decode h x).tag := by rw [inherited_decode_tag,inherited_decode_tag]

theorem forward_low_bound (t : Token) (op : t.opcode<8) (race : t.race<8)
    (outcome : t.outcome=0) (payload : t.payload<256) : lowCode t<2^17 := by
  have F : t.fault.toNat≤1 := by cases t.fault <;> decide
  have A : t.applied.toNat≤1 := by cases t.applied <;> decide
  unfold lowCode
  omega

#print axioms inherited_decode_tag
#print axioms inherited_encode_tag
#print axioms decoded_forward_bounds
#print axioms forward_low_bound

private theorem modulus_reply_payload (op p : Nat) : p % 2^dPayloadSize op<64 := by
  have B : dPayloadSize op≤6 := by
    unfold dPayloadSize
    split
    · decide
    split <;> decide
  exact Nat.lt_of_lt_of_le (Nat.mod_lt p (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by decide) B)

private theorem force_E (g : Bool) (x : BitVec 19)
    (H : (decode g x).tag=0) : decode g x=E := by
  rw [inherited_decode_tag] at H
  simp only [decode,H,beq_self_eq_true,if_true]

private theorem force_T (g : Bool) (x : BitVec 19)
    (H : (decode g x).tag=1) : decode g x=T := by
  rw [inherited_decode_tag] at H
  simp only [decode,H,show ((1:Nat)==0)=false by decide,beq_self_eq_true,if_true,Bool.false_eq_true,if_false]

private theorem decoded_reply_bound (g : Bool) (x : BitVec 19)
    (D : (decode g x).tag=3) :
    (decode g x).opcode<8 ∧ (decode g x).race=0 ∧
      (decode g x).outcome≤3 ∧ (decode g x).payload<64 := by
  rw [inherited_decode_tag] at D
  have O : (x.extractLsb' 13 3).toNat<8 := (x.extractLsb' 13 3).isLt
  have R : (x.extractLsb' 8 2).toNat<4 := (x.extractLsb' 8 2).isLt
  let P := fun t : Token=>t.opcode<8 ∧ t.race=0 ∧ t.outcome≤3 ∧ t.payload<64
  change P (decode g x)
  have bad : P (faultToken 3) := by dsimp [P]; decide
  unfold decode
  dsimp only
  simp only [D,show ((3:Nat)==0)=false by decide,show ((3:Nat)==1)=false by decide,
    show ((3:Nat)==2)=false by decide]
  apply pred_ite P _ _ _ bad
  apply pred_ite P _ _ _ bad
  refine ⟨O,rfl,by exact Nat.le_of_lt_succ R,?_⟩
  change (if (x.extractLsb' 8 2).toNat==1 then 0 else
    (x.extractLsb' 0 7).toNat%2^dPayloadSize (x.extractLsb' 13 3).toNat)<64
  split
  · decide
  · exact modulus_reply_payload _ _

/-- Re-encoding any previously decoded word preserves its kind at
every new gate. This includes junk normalized to a fault reply. -/
theorem encode_decoded_tag (g h : Bool) (x : BitVec 19) :
    (decode h (encode (decode g x))).tag=(decode g x).tag := by
  have B : (decode g x).tag<4 := by rw [inherited_decode_tag]; exact (x.extractLsb' 17 2).isLt
  apply inherited_encode_tag _ _ _ B
  have cases : (decode g x).tag=0 ∨ (decode g x).tag=1 ∨
      (decode g x).tag=2 ∨ (decode g x).tag=3 := by omega
  rcases cases with Z|Tt|F|D
  · rw [force_E g x Z]; decide
  · rw [force_T g x Tt]; decide
  · obtain ⟨O,R,A,P⟩ := decoded_forward_bounds g x F
    exact forward_low_bound _ O R A (by omega)
  · obtain ⟨O,R,A,P⟩ := decoded_reply_bound g x D
    let t := decode g x
    have C : t.fault.toNat≤1 := by cases t.fault <;> decide
    have I : t.applied.toNat≤1 := by cases t.applied <;> decide
    change lowCode t<2^17
    change t.opcode<8 at O
    change t.race=0 at R
    change t.outcome≤3 at A
    change t.payload<64 at P
    unfold lowCode
    omega

#print axioms encode_decoded_tag

/-- The live ADMIT branch of the wire decoder at an actual gate allows
only the five real races. Invalid race bytes decode as faults. -/
theorem gate_admit_shape (x : BitVec 19) (tag : (decode true x).tag=2)
    (op : (decode true x).opcode=2) (ok : (decode true x).fault=false) :
    1≤(decode true x).race ∧ (decode true x).race≤5 ∧
      (decode true x).payload≤1 ∧ (decode true x).outcome=0 ∧ (decode true x).applied=false := by
  rw [inherited_decode_tag] at tag
  let wireOp := (x.extractLsb' 13 3).toNat
  let wireRace := (x.extractLsb' 10 3).toNat
  unfold decode at op ok ⊢
  simp only [tag,show ((2:Nat)==0)=false by decide,show ((2:Nat)==1)=false by decide,
    show ((2:Nat)==2)=true by decide,if_true,Bool.true_and,Bool.false_eq_true,if_false] at op ok ⊢
  by_cases F : (x.getLsbD 16 || (wireOp==7))=true
  · change (if (x.getLsbD 16 || (wireOp==7))=true then faultToken 2 else _).fault=false at ok
    simp only [if_pos F] at ok
    contradiction
  · have G : ¬ (x.getLsbD 16 || ((x.extractLsb' 13 3).toNat==7))=true := F
    rw [if_neg G] at op ok ⊢
    let c : Bool := (x.extractLsb' 8 2).toNat != 0 ||
      (if wireOp==2 then wireRace<1 || 5<wireRace else wireRace != 0) ||
      (4≤wireOp && !descValid (x.extractLsb' 0 7).toNat)
    by_cases C : c=true
    · change (if c=true then faultToken 2 else _).fault=false at ok
      simp only [if_pos C] at ok
      contradiction
    · change (if c=true then faultToken 2 else _).opcode=2 at op
      rw [if_neg C] at op
      change wireOp=2 at op
      have E : ¬(wireRace<1 ∨ 5<wireRace) := by
        intro D
        apply C
        rcases D with D|D <;> simp [c,op,D]
      rw [if_neg C]
      refine ⟨by change 1≤wireRace; omega,by change wireRace≤5; omega,?_,rfl,?_⟩
      · change (x.extractLsb' 0 7).toNat % 2^fPayloadSize wireOp ≤ 1
        rw [op]
        change (x.extractLsb' 0 7).toNat % 2 ≤ 1
        omega
      · change (wireOp==6 && x.getLsbD 7)=false
        rw [op]
        rfl

/-- Changing only the live race to one of values 1–5 redecodes to
exactly that token at the same true gate. Applies to normalized junk too
after requiring the live codec shape, not to all raw encodings. -/
theorem admit_race_roundtrip (t : Token) (r : Nat)
    (tag : t.tag=2) (op : t.opcode=2) (ok : t.fault=false)
    (pl : t.payload≤1) (out : t.outcome=0) (app : t.applied=false)
    (lo : 1≤r) (hi : r≤5) :
    decode true (encode {t with race:=r})={t with race:=r} := by
  have p : t.payload=0 ∨ t.payload=1 := by omega
  have q : r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 := by omega
  rcases t with ⟨tt,oo,pp,rr,uu,ff,aa⟩
  dsimp only at *
  subst tt; subst oo; subst uu; subst ff; subst aa
  rcases p with E|E <;> subst pp <;>
    rcases q with E|E|E|E|E <;> subst r <;> decide

#print axioms gate_admit_shape
#print axioms admit_race_roundtrip

/-- Outside an actual gate, any nonzero stored race is rejected rather
than becoming live countdown debt. -/
theorem ungated_race_zero (x : BitVec 19) : (decode false x).race=0 := by
  unfold decode
  dsimp only
  simp only [Bool.false_and,Bool.false_eq_true,if_false]
  split
  · rfl
  split
  · rfl
  split
  · rfl
  split
  · let rr := (x.extractLsb' 10 3).toNat
    by_cases R : rr=0
    · apply pred_ite (fun t : Token=>t.race=0)
      · rfl
      · exact R
    · have V : (rr != 0)=true := by simp [R]
      have H : (((x.extractLsb' 8 2).toNat != 0 || rr != 0) ||
          (4≤(x.extractLsb' 13 3).toNat && !descValid (x.extractLsb' 0 7).toNat))=true := by
        simp [V]
      rw [if_pos H]
      rfl
  · apply pred_ite (fun t : Token=>t.race=0) <;> rfl

#print axioms ungated_race_zero
end L4.ShortPacketTag
