import Leader.L4.BStarLongOutgoing

namespace L4.BStarBitNoAbort
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongCommand BStarLongOutgoing BStarLongPublication BStarLongDoor

/-- Exactly the byte predicates not checked by a BIT read or a source
ISSUE411. Geometric H6/K1, descriptor validity and candidate membership
are tracked separately. -/
def SealedCenter (d : Descriptor) (x : BitVec LW) : Prop :=
  ((grant 1).read x).getLsbD 0=true ∧ readSel x=d.old ∧
    readOptional (stage.read x)=some d ∧ readOptional (sealField.read x)=some d

theorem guard_iff (d : Descriptor) (valid : d.valid=true)
    (b : Fin 3) (ok : b=d.b0 ∨ (d.need=true ∧ b=d.b1)) (x : BitVec LW) :
    BStarLongPublication.guard true 1 x d b=true ↔ SealedCenter d x := by
  have A : (b==d.b0 || (d.need && b==d.b1))=true := by
    rcases ok with rfl|⟨N,rfl⟩ <;> simp_all
  simp only [BStarLongPublication.guard,typedGuard,valid,A,show ((1:Fin 11)==1)=true by decide,
    Bool.true_and,Bool.and_true,Bool.and_eq_true,beq_iff_eq,SealedCenter]
  exact and_assoc.trans and_assoc

theorem keep (d : Descriptor) (x y : BitVec LW)
    (G : (grant 1).read y=(grant 1).read x) (S : selector.read y=selector.read x)
    (T : stage.read y=stage.read x) (E : sealField.read y=sealField.read x)
    (old : SealedCenter d x) : SealedCenter d y := by
  simpa only [SealedCenter,G,readSel,S,T,E] using old

/-- Exact center seed at the literal SEAL handler. This only proves
the outgoing sub-row, not yet the packed selected-visit or custody
fold through the whole ring. -/
theorem seal_seed (g : LongGeometry) (x : BitVec LW) (p q : Payload) (d : Descriptor)
    (head : g.axes.h6=true) (op : p.opcode.toNat=sealOp) (F : p.fault=0)
    (D : BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2))=some d)
    (enc : readOptional (packOptional (some d))=some d)
    (success : (execute g 1 x p).carried=.forward q) (good : q.fault=0) :
    SealedCenter d ((execute g 1 x p).row.apply x) := by
  have rule : execute g 1 x p=
      if (actual x d && readOptional (stage.read x)==some d)=true then
        ⟨sealField.assign (packOptional (some d)),
          .forward {p with argument:=BitVec.ofNat 34 (2*(p.argument.toNat/2)+d.need.toNat)},none⟩
      else refuse := by
    simp [execute,op,head,F,sealOp,stageOp,D]
  rw [rule] at success ⊢
  split at success
  · rename_i auth
    rw [if_pos auth]
    simp only [actual,Bool.and_eq_true,beq_iff_eq] at auth
    refine ⟨?_,?_,?_,?_⟩
    · rw [Field.read_other_assign _ _ _ _ (by decide)]
      exact auth.1.1
    · unfold readSel
      rw [Field.read_other_assign _ _ _ _ (by decide)]
      exact auth.1.2
    · rw [Field.read_other_assign _ _ _ _ (by decide)]
      exact auth.2
    · rw [Field.read_assign]
      exact enc
  · change fault false=.forward q at success
    cases success
    contradiction

private def d0 : Descriptor := ⟨0,1,2,true⟩
private def missingSeal : BitVec LW :=
  ((stage.assign (packOptional (some d0))).apply (((grant 1).assign 1).apply 0))

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 4096 in
/-- Literal old center counterexample to inferring COMMIT authorization
from a decoded NEED descriptor, a live writer, selector and STAGE.
This is not claimed reachable after a genuine own successful SEAL. -/
theorem missing_seal_fixture :
    d0.valid=true ∧ BStarLongPublication.decode (encode d0)=some d0 ∧
    ((grant 1).read missingSeal).getLsbD 0=true ∧
    readSel missingSeal=d0.old ∧ readOptional (stage.read missingSeal)=some d0 ∧
    readOptional (sealField.read missingSeal)=none ∧
    (commit true 1 missingSeal d0 d0.b0).2=none ∧
    (commit true 1 missingSeal d0 d0.b1).2=none := by decide

end L4.BStarBitNoAbort
