import Leader.L4.BStarScalarFlightTrace

/-! Reconstructed receipt head interface: the Boolean case is exact
evaluation over the old scalar file, while arithmetic/word heads
carry the independently established pending representation. -/
namespace L4.BStarNativeScalarRecurrence
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongArithmetic BStarLongToken
open BStarAliasFold BStarAliasRoster BStarNativeReceiptInduction BStarScalarFits
open BStarPhysicalDigitSem
open L4.Compiler.Native L4.Compiler.Interp

inductive ScalarHead {width : Nat} (table : PrimTable width) (bank : Bank)
    (old : BitVec LW) (k : Nat) (regs : List Value) (c' : Code) (f : Payload) : Prop where
  | bool : HeadOK old regs c' → ScalarHead table bank old k regs c' f
  | cmp {a b : Nat} (C : c'=.cmp a b) (P : PrimSem table bank)
      (A : f.argument.toNat=cmpPack
        (decide (argW width (readArgs regs [a,b]) 0=argW width (readArgs regs [a,b]) 1))
        (decide (argW width (readArgs regs [a,b]) 0<argW width (readArgs regs [a,b]) 1))) :
      ScalarHead table bank old k regs c' f
  | ready : PayloadBound c' f.argument.toNat → MuxBound old c' →
      WellRep old (headPending old k f c')
        (regs++[evalInstr (toInstr table bank c') regs]) literalCmp →
      ScalarHead table bank old k regs c' f

theorem head_ready {width : Nat} (table : PrimTable width) (bank : Bank)
    (old : BitVec LW) (k : Nat) (regs : List Value) (c' : Code) (f : Payload)
    (G : get (start k)=some c') (L : regs.length=start k)
    (R : WellRep old [] regs literalCmp)
    (H : ScalarHead table bank old k regs c' f) :
    PayloadBound c' f.argument.toNat ∧ MuxBound old c' ∧
      WellRep old (headPending old k f c')
        (regs++[evalInstr (toInstr table bank c') regs]) literalCmp := by
  cases H with
  | ready P M E => exact ⟨P,M,E⟩
  | @cmp a b C sem A =>
    subst c'
    let u := argW width (readArgs regs [a,b]) 0
    let v := argW width (readArgs regs [a,b]) 1
    have aBound : f.argument.toNat<4 := by
      rw [A]
      by_cases E : u=v <;> by_cases J : u<v <;>
        simp [u,v,cmpPack,E,J] at *
    have eval : evalInstr (toInstr table bank (.cmp a b)) regs=.word (cmpCode u v) := by
      change Value.word (den table.cmp (readArgs regs [a,b]))=_
      rw [sem.cmp]
    refine ⟨aBound,True.intro,?_⟩
    rw [eval]
    simp only [headPending,nodeResult,Option.toList_some,List.map_cons,List.map_nil,A]
    rw [←L]
    exact extend_cmp old [] regs literalCmp u v R
  | bool H =>
    have P : PayloadBound c' f.argument.toNat := by cases H <;> exact True.intro
    have M : MuxBound old c' := by
      cases H with
      | mux q a b Q A B =>
        unfold OldBool at A B
        exact ⟨A ▸ Bool.toNat_lt _,B ▸ Bool.toNat_lt _⟩
      | _ => exact True.intro
    have C : ¬ literalCmp (start k) := by
      cases H <;> simp [literalCmp,G,BStarCmpReceipt.isCmp]
    obtain ⟨b,E,V⟩ := exact_boolean_head table bank old regs c' f.argument.toNat H
    refine ⟨P,M,?_⟩
    rw [V]
    simp only [headPending,E,Option.toList_some,List.map_cons,List.map_nil]
    exact L ▸ extend_rep old [] regs literalCmp b R (L.symm ▸ C)

#print axioms head_ready
end L4.BStarNativeScalarRecurrence
