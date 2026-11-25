import Leader.L4.BStarNativeReceiptInduction

namespace L4.BStarScalarFits
open AllSizeProtocol BStarTrace BStarLongLayout
open BStarLongArithmetic BStarLongRegisters BStarAliasRoster
open BStarAliasFold L4.Compiler.Native

/-- Minimum number of scalar bits required by the literal
receipt/alias interpretation, not the numeric digit field. -/
def minimum : Code → Nat
  | .header _ _ | .bconst _ | .cmpEq _ | .cmpLt _ | .not _ | .and _ _
  | .or _ _ | .bmux _ _ _ | .phaseEq _ _ | .add _ _ | .sub _ _ => 1
  | .cmp _ _ => 2
  | .shl3 _ => 3
  | .scan5 _ => 5
  | _ => 0

def sizesOK : List Code → List Nat → Bool
  | [],_ => true
  | _,[] => false
  | c::cs,w::ws => decide (minimum c ≤ w) && sizesOK cs ws

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem sizes : sizesOK literal scalarWidths=true := by
  decide +kernel

theorem width_of_ok (cs : List Code) (ws : List Nat) (i : Nat) (c : Code)
    (K : sizesOK cs ws=true) (G : cs[i]?=some c) : minimum c≤widthAt ws i := by
  induction cs generalizing ws i with
  | nil => simp at G
  | cons hd cs ih =>
    cases ws with
    | nil => simp [sizesOK] at K
    | cons w ws =>
      have H := Bool.and_eq_true_iff.mp K
      cases i with
      | zero =>
        simp at G
        subst c
        exact of_decide_eq_true H.1
      | succ i => exact ih ws i H.2 (by simpa using G)

theorem literal_width {i : Nat} {c : Code} (G : get i=some c) :
    minimum c≤widthAt scalarWidths i :=
  width_of_ok literal scalarWidths i c sizes G

def PayloadBound (c : Code) (n : Nat) : Prop :=
  match c with
  | .add _ _ | .sub _ _ => n<2
  | .cmp _ _ => n<4
  | .shl3 _ => n<8
  | .scan5 _ => n<32
  | _ => True

def MuxBound (old : BitVec LW) : Code → Prop
  | .bmux _ a b => source old a<2 ∧ source old b<2
  | _ => True

theorem result_fit (old : BitVec LW) (n i v : Nat) (c : Code)
    (G : get i=some c) (B : PayloadBound c n) (M : MuxBound old c)
    (V : nodeResult old n c=some v) : v<2^(widthAt scalarWidths i) := by
  have base := literal_width G
  apply Nat.lt_of_lt_of_le _ (Nat.pow_le_pow_right (by decide) base)
  cases c <;> simp [PayloadBound,MuxBound,nodeResult,minimum] at B M V ⊢
  all_goals try contradiction
  all_goals try (subst v; exact B)
  all_goals try (subst v; exact Bool.toNat_lt _)
  subst v
  split <;> first | exact M.1 | exact M.2

open L4.Compiler.Interp BStarNativeReceiptInduction

def Fits (xs : Pending) : Prop :=
  ∀ a∈xs, a.2<2^(widthAt scalarWidths a.1)

theorem alias_slot {bank : Bank} {x : BitVec LW} {j : Nat} {c : Code}
    (H : AliasOK bank x literalCmp j c) (G : get j=some c) : 1≤widthAt scalarWidths j := by
  have W := literal_width G
  cases H <;> exact W

theorem fit_aliases {r : Nat} (T : PrimTable r) (bank : Bank) (x : BitVec LW)
    (cs : List Code) (j : Nat) (regs : List Value) (xs : Pending)
    (S : Segment bank x literalCmp j cs) (L : regs.length=j)
    (R : WellRep x xs regs literalCmp) (F : Fits xs)
    (aligned : ∀ i c, cs[i]?=some c → get (j+i)=some c) :
    Fits (aliases x j cs xs) := by
  induction S generalizing regs xs with
  | nil => exact F
  | @cons j c cs head new tail ih =>
    have head' : AliasOK bank x literalCmp regs.length c := L ▸ head
    obtain ⟨b,E,_⟩ := exact_alias T bank x xs regs literalCmp c R head'
    simp only [aliases,E]
    have W := alias_slot head (by simpa using aligned 0 c rfl)
    have addFit : Fits ((j,b.toNat)::xs) := by
      intro a h
      rcases List.mem_cons.mp h with rfl|h
      · exact Nat.lt_of_lt_of_le (Bool.toNat_lt _) (Nat.pow_le_pow_right (by decide : 0<2) W)
      · exact F _ h
    have R' := extend_rep x xs regs literalCmp b R (L.symm ▸ new)
    rw [L] at R'
    exact ih (regs++[.boolean b]) _ (by simp [L]) R' addFit (fun i q H => by
      rw [show j+1+i=j+(i+1) by omega]
      exact aligned (i+1) q H)

theorem pending_fit (old : BitVec LW) (k : Nat) (p : BStarLongToken.Payload)
    {c : Code} (G : get (start k)=some c) (H : PayloadBound c p.argument.toNat)
    (M : MuxBound old c) :
    Fits (headPending old k p c) := by
  unfold headPending
  cases E : nodeResult old p.argument.toNat c with
  | none => simp [Fits]
  | some v =>
    intro a h
    have J : a=(start k,v) := List.mem_singleton.mp h
    subst a
    exact result_fit old p.argument.toNat _ _ c G H M E

/-- Automatically discharge the entire literal pending overlay's width
obligation from the real head accumulator bound and the old file's
typed comparisons/captured bits. No slot truncation is assumed away. -/
theorem receipt_fit {r : Nat} (T : PrimTable r) (bank : Bank) (old : BitVec LW)
    {k : Nat} (K : k<395) (p : BStarLongToken.Payload) {c : Code} (G : get (start k)=some c)
    (regs : List Value) (L : regs.length=start k+1)
    (R : WellRep old (headPending old k p c) regs literalCmp)
    (capture : ∀ q i, ((capturedHeader q i).read old).toNat=(bank.hdr q i).toNat)
    (H : PayloadBound c p.argument.toNat) (M : MuxBound old c) :
    Fits (aliases old (start k+1) (literal.drop (start k+1)) (headPending old k p c)) := by
  rw [aliases_take,maximal_suffix K]
  apply fit_aliases T bank old _ _ regs _ (roster_segment bank old K capture)
    L R (pending_fit old k p G H M)
  intro i d G'
  unfold suffix at G'
  rw [List.getElem?_take,List.getElem?_drop] at G'
  split at G'
  · exact G'
  · contradiction

#print axioms receipt_fit
#print axioms literal_width
#print axioms result_fit
end L4.BStarScalarFits
