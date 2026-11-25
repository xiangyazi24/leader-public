import Leader.L4.BStarNativePartialDispatcher
import Leader.L4.BStarNativeAllLoadsAccepted

namespace L4.BStarNativeLoadReady
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongWork BStarLongToken BStarLongDoor BStarLongCommand
open BStarGeneratedOwner BStarGeneratedBandScan BStarNativeReceiptTape BStarAcquireVisitOrder
open BStarNativePrefixInduction BStarNativePackedRep BStarNativeScalarRecurrence BStarScalarFits
open BStarNativeZeroHead BStarNativeLoadTours BStarNativeAllLoadsAccepted BStarLongArithmetic
open BStarLongSignatures BStarPhysicalDigitSem L4.Compiler.Native L4.Compiler.Interp L4.Compiler.Digits
open BStarNativeReceiptInduction BStarLongFixedRouting
open BStarAliasRoster BStarAliasFold
open BStarOwnerLaunchOrigin BStarPhysicalWordSem

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

theorem same_hit {base x : X} {addr : Nat → Pos n} {len : Nat} {mode : Mode}
    (K : (addr 0).2=0) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w l s la sa : List (Fin n)} {e f : Fin n} {op : Nat}
    (G : GeneratedOwner hp base addr len x .idle w mode)
    (band : CompilerBand hp x (addr 0).1 w)
    (WL : w=l++e::la) (WR : w=s++f::sa)
    (HL : Hit hp base addr len (run x l) e op)
    (HR : Hit hp base addr len (run x s) f op) :
    l=s ∧ e=f ∧ la=sa := by
  have noEarlier (l s la sa : List (Fin n)) (e f : Fin n)
      (WL : w=l++e::la) (WR : w=s++f::sa)
      (HL : Hit hp base addr len (run x l) e op)
      (HR : Hit hp base addr len (run x s) f op) : ¬l.length<s.length := by
    intro lt
    have L : (l++[e]) <+: w := ⟨la, by simpa [List.append_assoc] using WL.symm⟩
    have R : s <+: w := ⟨f::sa,WR.symm⟩
    obtain ⟨v,E⟩ := List.prefix_of_prefix_length_le L R (by simp; omega)
    let p := l++[e]
    have split : w=p++(v++f::sa) := by rw [WR,←E,List.append_assoc]
    obtain ⟨a,_,S⟩ := BStarGeneratedTapeCuts.split hp p (v++f::sa) (split ▸ G)
    obtain ⟨b,T,_⟩ := BStarGeneratedTapeCuts.split hp v (f::sa) S
    have V : CompilerBand hp (run x p) (addr 0).1 v := by
      intro u z J
      have H := band (p++u) (z++f::sa) (by rw [split,J]; simp only [List.append_assoc])
      simpa only [BStarResetSchedule.run_append] using H
    have M := end_monotone hp K sep T V
    rw [←BStarResetSchedule.run_append,show p++v=s from E] at M
    have A : run x p=step (run x l) e := by
      dsimp only [p]
      rw [BStarResetSchedule.run_append]
      rfl
    rw [A,HL.2.2.2.1,HR.2.2.1] at M
    omega
  have a := Nat.le_of_not_gt (noEarlier l s la sa e f WL WR HL HR)
  have b := Nat.le_of_not_gt (noEarlier s l sa la f e WR WL HR HL)
  have E := congrArg (List.take l.length) (WL.symm.trans WR)
  rw [List.take_append_of_le_length (Nat.le_refl l.length),List.take_length,
      List.take_append_of_le_length b,List.take_of_length_le a] at E
  subst s
  have eq : e::la=f::sa := List.append_cancel_left (WL.symm.trans WR)
  exact ⟨rfl,List.cons.inj eq⟩

private theorem scalar {width : Nat} (T : PrimTable width) (bank : Bank)
    (old : BitVec LW) (k : Nat) (f : Payload) (q : Fin 3) (d : Fin 9) (regs : List Value)
    (G : get (start k)=some (.load q d)) (L : regs.length=start k)
    (R : WellRep old [] regs literalCmp) : ScalarHead T bank old k regs (.load q d) f := by
  have U : ¬literalCmp (start k) := by simp [literalCmp,G,BStarCmpReceipt.isCmp]
  refine .ready True.intro True.intro ?_
  have W : ∃ m, evalInstr (toInstr T bank (.load q d)) regs=.word m := ⟨_,rfl⟩
  obtain ⟨m,W⟩ := W
  simp only [headPending,nodeResult,Option.toList_none,List.map_nil,W]
  intro i hi
  by_cases h : i<regs.length
  · have E := readReg_append_left regs [Value.word m] i h
    simpa only [BoolRep,CmpRep,E] using R i h
  · have eq : i=regs.length := by simp at hi; omega
    subst i
    have E : readReg (regs++[Value.word m]) regs.length=.word m := by simp [readReg]
    refine ⟨?_,?_⟩
    · intro b H
      rw [E] at H
      contradiction
    · intro C
      exact False.elim (U (L ▸ C))

theorem load_plan : ∀ k : Fin 395, ∀ q : Fin 3, ∀ f : Fin 9,
    get (start k.val)=some (.load q f) → 13+k.val=loadOp q f ∧ start k.val=loadNode q f := by
  decide +kernel

/-- The callback consumes the exact supplied compiler word and bank;
same-PC candidates cannot move the LOAD receipt to another cut. -/
theorem callback {base x : X} {addr : Nat→Pos n} {len : Nat} {mode : Mode}
    {width : Nat} (site : Fin width → Fin n)
    (K : (addr 0).2=0) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} (G : GeneratedOwner hp base addr len x .idle w mode)
    (band : CompilerBand hp x (addr 0).1 w)
    (table : PrimTable width) (bank : Bank) (sem : PrimSem table bank)
    (capture : ∀ u v,w=u++v → ∀ q d,
      ((capturedHeader q d).read (run x u (addr 0).1).long).toNat=(bank.hdr q d).toNat)
    (data : ∀ (q : Fin 3) (d : Fin 9), ∃ p a t, w=p++a::t ∧
      Hit hp base addr len (run x p) a (loadOp q d) ∧
      ∀ s : WordSlot (loadNode q d),
        wordAt (step (run x p) a) site (loadNode q d) s=bank.digits q d % 16^width) :
    ∀ (prior pre tail : List (Fin n)) (e : Fin n) (k : Nat), k<394 →
      w=prior++(pre++e::tail) →
      let st := run x prior
      let y := run st pre
      Found hp base addr len (13+k) st pre (.back 0) →
      Flat hp st (addr 0).1 pre →
      Hit hp base addr len y e (13+k) →
      PackedRep y (addr 0).1 site k (regsBefore table bank k) →
      ∀ c', get (start k)=some c' → BStarNativePartialDispatcher.Remaining c' →
      Ready hp table bank y (step y e) (addr 0).1 site k c' (regsBefore table bank k) := by
  intro prior pre tail e k hk W
  dsimp only
  intro _ _ H R c' code C
  cases C with
  | load q d =>
    obtain ⟨op,node⟩ := load_plan ⟨k,by omega⟩ q d code
    have cut : w=(prior++pre)++e::tail := by rw [W,List.append_assoc]
    have E : run x (prior++pre)=run (run x prior) pre := BStarResetSchedule.run_append step x prior pre
    obtain ⟨p,a,t,wa,ha,word⟩ := data q d
    have H' : Hit hp base addr len (run x (prior++pre)) e (loadOp q d) := by rw [←op,E]; exact H
    obtain ⟨eq,markEq,_⟩ := same_hit hp K sep G band wa cut ha H'
    rw [eq,E,markEq] at word
    refine ⟨code,fun q d=>by simpa only [E] using capture (prior++pre) (e::tail) cut q d,
      fun f _=>Or.inr (scalar table bank _ k f q d _ code R.length R.scalar), ?_, ?_⟩
    · intro _ _ _ contra
      cases contra
    · intro s
      change Value.word (den (table.load q d) [])=Value.word _
      rw [sem.load]
      have word' : ∀ a : WordSlot (start k), wordAt (step (run (run x prior) pre) e) site (start k) a = bank.digits q d % 16^width := node.symm ▸ word
      exact congrArg Value.word (word' s).symm

/-- Join the physical pointwise nibble statement to the packed-register
callback, without requiring a choice of WordSlot proof. -/
theorem word_from_nibbles {width : Nat} (y : X) (site : Fin width→Fin n)
    (i : Nat) (payload : Word width) (target : Nat)
    (D : ∀ j, num (y (site j)).long i=(payload j).val)
    (V : val payload=target) :
    ∀ s : WordSlot i, wordAt y site i s=target := by
  intro s
  have E : readWord (fun j => (y (site j)).long) i s=payload := by
    funext j
    exact Fin.ext (D j)
  unfold wordAt
  rw [E,V]

end L4.BStarNativeLoadReady
