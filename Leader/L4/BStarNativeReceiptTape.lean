import Leader.L4.BStarGeneratedTapeCuts
import Leader.L4.BStarOwnerLaunchOrigin

namespace L4.BStarNativeReceiptTape
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongLayout BStarLongDoor
open BStarLongCommand BStarH6WordChart BStarGeneratedOwner BStarGeneratedPCAncestry
open BStarAcquireVisitOrder BStarGeneratedTapeCuts BStarOwnerLaunchOrigin BStarLiteralPC

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "pc" => BStarGeneratedBandScan.pc

private theorem foreign_pc (x : X) (i e : Fin n)
    (h : oldH6 B x i=true) (away : e≠RearTrace.predecessor i) :
    pc (step x e) i=pc x i := by
  have R : rightNeighbor e≠i := fun E =>
    away ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor E))
  by_cases E : i=e
  · subst i
    let pair := (x e,x (rightNeighbor e))
    have h' : (oldHeaders B pair.1).h6=true := h
    have t := BStarResetWaitRing.joined_left k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair h'
    unfold BStarGeneratedBandScan.pc
    simp only [AllSizeS1Geometry.step,if_true]
    exact congrArg (fun y : BitVec 2 × BitVec 9 => y.2.toNat) t
  · unfold BStarGeneratedBandScan.pc
    simp only [AllSizeS1Geometry.step,if_neg E,if_neg (Ne.symm R)]

private theorem reject_pc {x : X} {addr : Nat → Pos n} {e : Fin n}
    (h : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e) (I : BStarClearanceSource.Issue (x (addr 0).1).long)
    (E : e=RearTrace.predecessor (addr 0).1)
    (bad : initial (pc x (addr 0).1) (x (addr 0).1).long=none) :
    pc (step x e) (addr 0).1=0 := by
  have R : rightNeighbor e=(addr 0).1 := E ▸ RearTrace.right_predecessor _
  let pair := (x e,x (rightNeighbor e))
  have hdr : (oldHeaders B pair.2).h6=true := by change oldH6 B x (rightNeighbor e)=true; rwa [R]
  have valid : LongDoorGuard.valid manifest pair.2.long=true := by
    change LongDoorGuard.valid manifest (x (rightNeighbor e)).long=true
    rw [R]; exact I.1
  have phase : (ctrlPhase.read pair.2.long).toNat=1 := by
    change (ctrlPhase.read (x (rightNeighbor e)).long).toNat=1
    rw [R]; exact I.2
  have A := BStarResetControllerEntry.exact_issue_any_token k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair hdr valid phase
  have bad' : initial (ctrlOp.read pair.2.long).toNat pair.2.long=none := by
    change initial (pc x (rightNeighbor e)) (x (rightNeighbor e)).long=none
    rwa [R]
  rw [bad'] at A
  have eq : step x e (addr 0).1=(largePair B pair).2 := by
    rw [←R]; simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true,pair]
  exact congrArg (fun t : _ × BitVec 9 => t.2.toNat) (eq ▸ A)

/-- One actual accepted arithmetic receipt, with its literal old
state, old payload, and control event. -/
def Hit (base : X) (addr : Nat → Pos n) (len : Nat)
    (x : X) (e : Fin n) (op : Nat) : Prop :=
  let i := (addr 0).1
  Current hp base addr len x (.busy op (.back 0)) ∧
    Event hp addr len x e (.busy op (.back 0)) .idle ∧
    pc x i=op ∧ pc (step x e) i=op+1 ∧
    e=RearTrace.predecessor i ∧
    ∃ f, bind (longGeometry B (x i)) 0 (atSite (x i).long 0)=.reply f ∧
      f.fault=0 ∧ f.opcode.toNat=op

/-- The one-step accepted native phase either holds PC (including
actual launch) or takes the exact authentic next consume. -/
theorem one_step {base x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    {a b : Mode}
    (K : (addr 0).2=0) (H : oldH6 B x (addr 0).1=true) (sep : e≠rightNeighbor e)
    (I : Current hp base addr len x a) (J : Current hp base addr len (step x e) b)
    (E : Event hp addr len x e a b)
    (new : pc (step x e) (addr 0).1≤408)
    (lo : 13≤pc (step x e) (addr 0).1) :
    pc (step x e) (addr 0).1=pc x (addr 0).1 ∨
      ∃ op, a=.busy op (.back 0) ∧ b=.idle ∧ Hit hp base addr len x e op := by
  cases E with
  | idle_hold away => exact .inl (foreign_pc hp x _ e H away)
  | arrived_hold op away => exact .inl (foreign_pc hp x _ e H away)
  | launch own L =>
    exact .inl (congrArg (fun t : _ × BitVec 9 => t.2.toNat) L.2.choose_spec.2)
  | transit op z d live S => exact .inl (J.1.2.2.2.trans I.1.2.2.2.symm)
  | bad_issue own bad =>
    have Z := reject_pc hp H sep I.1 own bad
    omega
  | consume op own clear =>
    have evt : Event hp addr len x e (.busy op (.back 0)) .idle := .consume op own clear
    have low : 7≤pc (step x e) (addr 0).1 := by omega
    obtain ⟨eq,f,R,F,O⟩ := consume_to_band hp K H sep I evt low new
    exact .inr ⟨op,rfl,rfl,I,evt,I.1.2.2.2,eq,own,f,R,F,O⟩

/-- This band is the one uninterrupted compiler attempt; it excludes
abort-to-zero and later recovery, but allows arbitrary foreign marks. -/
def CompilerBand (x : X) (i : Fin n) (w : List (Fin n)) : Prop :=
  ∀ u v,w=u++v →
    oldH6 B (run x u) i=true ∧ 13≤pc (run x u) i ∧ pc (run x u) i≤408

/-- No scheduled source PC jump anywhere in this exact subword. -/
def Flat (x : X) (root : Fin n) (w : List (Fin n)) : Prop :=
  ∀ u v,w=u++v → pc (run x u) root=pc x root

private theorem flat_cons {x : X} {i e : Fin n} {w : List (Fin n)}
    (same : pc (step x e) i=pc x i) (F : Flat hp (step x e) i w) :
    Flat hp x i (e::w) := by
  intro u v E
  cases u with
  | nil => rfl
  | cons q u =>
    obtain ⟨rfl,Q⟩ := List.cons.inj E
    exact (F u v Q).trans same

private theorem flat_nil (x : X) (i : Fin n) : Flat hp x i [] := by
  intro u v E
  obtain ⟨rfl,_⟩ := List.append_eq_nil_iff.mp E.symm
  rfl

theorem end_monotone {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b : Mode} {w : List (Fin n)} (K : (addr 0).2=0)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x a w b)
    (band : CompilerBand hp x (addr 0).1 w) :
    pc x (addr 0).1≤pc (run x w) (addr 0).1 := by
  induction T with
  | endpoint _ => exact Nat.le_refl _
  | @next x a e w b dest I E T ih =>
    have sub : CompilerBand hp (step x e) (addr 0).1 w := by
      intro u v Q
      exact band (e::u) v (congrArg (List.cons e) Q)
    have H := (band [] (e::w) rfl).1
    have L := (sub [] w rfl).2
    refine Nat.le_trans ?_ (ih sub)
    rcases one_step hp K H (sep e) I (at_start hp T) E L.2 L.1 with same|⟨_,_,_,hit⟩
    · exact Nat.le_of_eq same.symm
    · have A : pc x (addr 0).1=_ := hit.2.2.1
      have Z : pc (step x e) (addr 0).1=_ := hit.2.2.2.1
      omega

theorem flat_of_equal {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b : Mode} {w : List (Fin n)} (K : (addr 0).2=0)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x a w b)
    (band : CompilerBand hp x (addr 0).1 w)
    (same : pc (run x w) (addr 0).1=pc x (addr 0).1) : Flat hp x (addr 0).1 w := by
  intro u v E
  have T' : GeneratedOwner hp base addr len x a (u++v) b := E ▸ T
  obtain ⟨mid,L,R⟩ := BStarGeneratedTapeCuts.split hp u v T'
  have B₁ : CompilerBand hp x (addr 0).1 u := by
    intro pre tail W
    apply band pre (tail++v)
    rw [E,W,List.append_assoc]
  have B₂ : CompilerBand hp (run x u) (addr 0).1 v := by
    intro pre tail W
    have H := band (u++pre) tail (by rw [E,W,List.append_assoc])
    rw [BStarResetSchedule.run_append] at H
    exact H
  have W := end_monotone hp K sep L B₁
  have Z := end_monotone hp K sep R B₂
  have Q : run (run x u) v=run x w :=
    (BStarResetSchedule.run_append step x u v).symm.trans (congrArg (run x) E.symm)
  rw [Q,same] at Z
  exact Nat.le_antisymm Z W

theorem first_hit {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b : Mode} {w : List (Fin n)} (K : (addr 0).2=0)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x a w b)
    (band : CompilerBand hp x (addr 0).1 w)
    (rise : pc x (addr 0).1<pc (run x w) (addr 0).1) :
    ∃ pre e post, w=pre++e::post ∧ Flat hp x (addr 0).1 pre ∧
      GeneratedOwner hp base addr len x a pre (.busy (pc x (addr 0).1) (.back 0)) ∧
      Hit hp base addr len (run x pre) e (pc x (addr 0).1) ∧
      GeneratedOwner hp base addr len (step (run x pre) e) .idle post b ∧
      CompilerBand hp (step (run x pre) e) (addr 0).1 post := by
  induction T with
  | endpoint I =>
    simp only [BStarResetSchedule.run] at rise
    omega
  | @next x a e w b dest I E T ih =>
    have sub : CompilerBand hp (step x e) (addr 0).1 w := by
      intro u v Q
      exact band (e::u) v (congrArg (List.cons e) Q)
    have H := (band [] (e::w) rfl).1
    have L := (sub [] w rfl).2
    rcases one_step hp K H (sep e) I (at_start hp T) E L.2 L.1 with same|⟨op,A,C,hit⟩
    · have r : pc x (addr 0).1<pc (run (step x e) w) (addr 0).1 := rise
      have p : pc (step x e) (addr 0).1<pc (run (step x e) w) (addr 0).1 :=
        Nat.lt_of_le_of_lt (Nat.le_of_eq same) r
      obtain ⟨pre,m,post,W,Pflat,U,V,D,F⟩ := ih sub p
      have s : pc (step x e) (addr 0).1=pc x (addr 0).1 := same
      rw [s] at U V
      exact ⟨e::pre,m,post,congrArg (List.cons e) W,flat_cons hp s Pflat,.next I E U,V,D,F⟩
    · have P : pc x (addr 0).1=op := hit.2.2.1
      subst a
      subst b
      rw [P]
      exact ⟨[],e,w,rfl,flat_nil hp x _,.endpoint I,hit,T,sub⟩

/-- Chronological native receipts with exact word splitting. Each cons
ends the previous idle-to-idle stage at its actual sole consume, and
witnesses the real busy-only radial path from its physical launch. -/
inductive NativeTape (base : X) (addr : Nat → Pos n) (len : Nat) :
    X → Nat → List (Fin n) → Nat → Prop where
  | done {x w op}
      (E : GeneratedOwner hp base addr len x .idle w .idle)
      (P : pc (run x w) (addr 0).1=op) (flat : Flat hp x (addr 0).1 w) :
      NativeTape base addr len x op w 0
  | take {x : X} {op : Nat} {pre tail : List (Fin n)} {e : Fin n} {k : Nat}
      (ahead : GeneratedOwner hp base addr len x .idle pre (.busy op (.back 0)))
      (flat : Flat hp x (addr 0).1 pre)
      (launch : Found hp base addr len op x pre (.back 0))
      (receipt : Hit hp base addr len (run x pre) e op)
      (rest : NativeTape base addr len (step (run x pre) e) (op+1) tail k) :
      NativeTape base addr len x op (pre++e::tail) (k+1)

/-- Count and ordering are derived from the actual word, not imposed
through an externally enumerated list of candidate receipts. -/
theorem extract_count {base x : X} {addr : Nat → Pos n} {len : Nat}
    {w : List (Fin n)} (K : (addr 0).2=0)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x .idle w .idle)
    (band : CompilerBand hp x (addr 0).1 w)
    (count : pc (run x w) (addr 0).1=pc x (addr 0).1+k) :
    NativeTape hp base addr len x (pc x (addr 0).1) w k := by
  induction k generalizing x w with
  | zero =>
    have same : pc (run x w) (addr 0).1=pc x (addr 0).1 := by simpa using count
    exact .done T same (flat_of_equal hp K sep T band same)
  | succ k ih =>
    have up : pc x (addr 0).1<pc (run x w) (addr 0).1 := by omega
    obtain ⟨pre,e,tail,W,Pflat,H,receipt,R,L⟩ := first_hit hp K sep T band up
    have newPC : pc (step (run x pre) e) (addr 0).1=pc x (addr 0).1+1 := receipt.2.2.2.1
    have runEq : run x w=run (step (run x pre) e) tail := by
      rw [W,BStarResetSchedule.run_append]
      rfl
    have cnt : pc (run (step (run x pre) e) tail) (addr 0).1=
        pc (step (run x pre) e) (addr 0).1+k := by
      rw [←runEq,newPC]
      omega
    have rem := ih R L cnt
    rw [newPC] at rem
    rw [W]
    exact .take H Pflat (from_idle hp H) receipt rem

/-- Exactly 395 chronological compiler consumes, opcodes 13..407. -/
theorem native_395 {base x : X} {addr : Nat → Pos n} {len : Nat} {w : List (Fin n)}
    (K : (addr 0).2=0) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x .idle w .idle)
    (band : CompilerBand hp x (addr 0).1 w)
    (lo : pc x (addr 0).1=13) (hi : pc (run x w) (addr 0).1=408) :
    NativeTape hp base addr len x 13 w 395 := by
  have H := extract_count hp K sep T band (k:=395) (by omega)
  rwa [lo] at H

#print axioms native_395
#print axioms first_hit
#print axioms one_step
end L4.BStarNativeReceiptTape
