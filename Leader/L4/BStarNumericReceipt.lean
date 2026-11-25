import Leader.L4.BStarNumericHealthy
import Leader.L4.BStarNativeReceiptTape
import Leader.L4.BStarAcquireAckAncestry

/-! The exact numeric terminal codec and stable reply binding. -/
namespace L4.BStarNumericReceipt
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongSignatures BStarNumericCarry

def resultWidth (op : Nat) : Nat :=
  match arithKind op with
  | some .bitCarry => 1
  | some .shiftCarry => 3
  | some .cmp => 2
  | some .scan => 5
  | _ => 0

theorem reply_width {op : Nat} (L : 13≤op) (U : op<408) (n : Nat) :
    replyWidth op 0 n=some (resultWidth op) := by
  have A : op≠admit := by unfold admit; omega
  have B : op≠bitOp := by unfold bitOp; omega
  have C : op≠acquire := by unfold acquire; omega
  have D : op≠sealOp := by unfold sealOp; omega
  unfold replyWidth resultWidth
  simp [A,B,C,D]
  generalize arithKind op=t
  cases t with
  | none => rfl
  | some a => cases a <;> rfl

def output (p : Payload) : Payload :=
  cropped {p with race:=0,outcome:=0} (resultWidth p.opcode.toNat)

theorem finish_numeric (p : Payload) (P : Numeric p) : finish p=.reply (output p) := by
  have C : p.opcode.toNat≠acquire := by
    obtain ⟨_,L,_⟩ := P
    unfold acquire
    omega
  simp [finish,P.1,C,reply_width P.2.1 P.2.2,output]

theorem output_numeric (p : Payload) (P : Numeric p) : Numeric (output p) := P

theorem output_bind (g : LongGeometry) (j : Fin 11) (p : Payload) (P : Numeric p) :
    BStarLongCommand.bind g j (.reply (output p))=.reply (output p) := by
  let q := output p
  have Q : Numeric q := P
  have O : q.outcome=0 := rfl
  have R : q.race=0 := rfl
  have h : ¬q.opcode.toNat≥413 := by obtain ⟨_,_,U⟩ := Q; omega
  have e : cropped q (resultWidth q.opcode.toNat)=q := by
    have A : q.argument.toNat < 2^(resultWidth q.opcode.toNat) := by
      change (BitVec.ofNat 34 (p.argument.toNat % 2^(resultWidth p.opcode.toNat))).toNat < _
      rw [BitVec.toNat_ofNat]
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (Nat.two_pow_pos _))
    unfold cropped low
    rw [Nat.mod_eq_of_lt A,BitVec.ofNat_toNat]
    cases q
    rfl
  change BStarLongCommand.bind g j (.reply q)=.reply q
  simp [BStarLongCommand.bind,Q.1,h,O,R,reply_width Q.2.1 Q.2.2,e]

theorem finish_origin (p q : Payload) (F : finish p=.reply q) (N : Numeric q) :
    Numeric p ∧ p.opcode=q.opcode ∧ q=output p := by
  have origin : p.fault=0 ∧ p.opcode=q.opcode := by
    unfold finish at F
    dsimp only at F
    by_cases H : p.fault=0
    · simp only [H,bne_self_eq_false,Bool.false_eq_true,if_false] at F
      split at F
      · split at F <;> cases F <;> exact ⟨H,rfl⟩
      · split at F
        · cases F
          exact False.elim ((show (1 : BitVec 1) ≠ 0 by decide) N.1)
        · cases F
          exact ⟨H,rfl⟩
    · split at F
      · cases F
        exact False.elim ((show (1 : BitVec 1) ≠ 0 by decide) N.1)
      · rename_i E
        exact False.elim (E (bne_iff_ne.mpr H))
  have H : Numeric p := ⟨origin.1,by rw [origin.2]; exact N.2.1,by rw [origin.2]; exact N.2.2⟩
  exact ⟨H,origin.2,Token.reply.inj (F.symm.trans (finish_numeric p H))⟩

#print axioms output_bind
#print axioms finish_origin
end L4.BStarNumericReceipt
