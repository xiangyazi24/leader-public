import Leader.L4.BStarGeneratedOwner
import Leader.L4.BStarLiteralPC

namespace L4.BStarGeneratedPCAncestry
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongDoor
open BStarGeneratedOwner BStarResetChartService BStarResetMarkAdapter BStarSeparatorControl
open BStarAcquireVisitOrder BStarLiteralPC BStarResetControllerEntry

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

set_option maxRecDepth 4096

/-- A GeneratedOwner consume really handles the old bound reply
at its own incoming seam; its PC is the literal old-data successor. -/
theorem consume_exact {base x : X} {addr : Nat → Pos n} {len op : Nat} {e : Fin n}
    (H : (addr 0).2=0) (hh : (oldHeaders B (x (addr 0).1)).h6=true)
    (distinct : e≠rightNeighbor e)
    (cur : Current hp base addr len x (.busy op (.back 0)))
    (event : Event hp addr len x e (.busy op (.back 0)) .idle) :
    let root := (addr 0).1
    let old := (x root).long
    let new := (AllSizeS1Geometry.step B x e root).long
    ∃ f, BStarLongCommand.bind (longGeometry B (x root)) 0 (atSite old 0)=.reply f ∧
      snapshot new=((.empty,1),BitVec.ofNat 9 (pcNext old f)) := by
  dsimp only
  have E : e=RearTrace.predecessor (addr 0).1 := by
    cases event <;> assumption
  have R : rightNeighbor e=(addr 0).1 := E ▸ RearTrace.right_predecessor (addr 0).1
  have W := cur.1
  obtain ⟨payload,P⟩ := cur.2.1.2.1
  change atSite (x (addr 0).1).long (addr 0).2=.reply payload at P
  rw [H] at P
  obtain ⟨f,F⟩ := bound_D (longGeometry B (x (addr 0).1)) 0 payload
  rw [←P] at F
  have S := joined_reply_PC k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) f
    (by rwa [R]) (by rw [R]; exact W.2.1) (by rw [R]; exact W.2.2.1) (by rwa [R])
  have V : AllSizeS1Geometry.step B x e (addr 0).1=(largePair B (x e,x (rightNeighbor e))).2 := by
    simp only [←R,AllSizeS1Geometry.step,if_neg (Ne.symm distinct),if_true]
  refine ⟨f,F,?_⟩
  rw [V]
  change snapshot (largePair B (x e,x (rightNeighbor e))).2.long =
    ((.empty,1),BitVec.ofNat 9 (pcNext (x (addr 0).1).long f))
  simpa only [Prod.snd,R] using S

theorem pcNext_bound (old : BitVec LW) (f : Payload) (V : LongDoorGuard.valid manifest old=true) :
    pcNext old f<413 := by
  have B' : (ctrlOp.read old).toNat<413 := by
    unfold LongDoorGuard.valid at V
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp V).2
  unfold pcNext
  dsimp only
  split
  · omega
  · split
    · rename_i ar
      have ar' := BStarArithmeticControllerReturn.arithmetic_range (ctrlOp.read old).toNat ar
      rcases BStarArithmeticControllerReturn.successor_order old (ctrlOp.read old).toNat ar'.2 with k|k <;> omega
    · rcases BStarResetControllerProgress.ordinary_progress old (ctrlOp.read old).toNat f B' with k|k
      · omega
      · exact k.2

theorem consume_pc {base x : X} {addr : Nat → Pos n} {len op : Nat} {e : Fin n}
    (H : (addr 0).2=0) (hh : (oldHeaders B (x (addr 0).1)).h6=true)
    (distinct : e≠rightNeighbor e)
    (cur : Current hp base addr len x (.busy op (.back 0)))
    (event : Event hp addr len x e (.busy op (.back 0)) .idle) :
    let root := (addr 0).1
    let old := (x root).long
    let new := (AllSizeS1Geometry.step B x e root).long
    ∃ f, BStarLongCommand.bind (longGeometry B (x root)) 0 (atSite old 0)=.reply f ∧
      (ctrlOp.read new).toNat=pcNext old f := by
  dsimp only
  obtain ⟨f,F,S⟩ := consume_exact hp H hh distinct cur event
  have T := congrArg (fun t : (Token × BitVec 2) × BitVec 9 => t.2.toNat) S
  change (ctrlOp.read (AllSizeS1Geometry.step B x e (addr 0).1).long).toNat =
    pcNext (x (addr 0).1).long f % 512 at T
  rw [Nat.mod_eq_of_lt (Nat.lt_trans (pcNext_bound _ _ cur.1.2.1) (by decide))] at T
  exact ⟨f,F,T⟩

theorem consume_to_stage {base x : X} {addr : Nat → Pos n} {len op : Nat} {e : Fin n}
    (H : (addr 0).2=0) (hh : (oldHeaders B (x (addr 0).1)).h6=true)
    (distinct : e≠rightNeighbor e)
    (cur : Current hp base addr len x (.busy op (.back 0)))
    (event : Event hp addr len x e (.busy op (.back 0)) .idle)
    (new : (ctrlOp.read (AllSizeS1Geometry.step B x e (addr 0).1).long).toNat=408) :
    op=407 ∧ ∃ f, BStarLongCommand.bind (longGeometry B (x (addr 0).1)) 0
      (atSite (x (addr 0).1).long 0)=.reply f ∧ f.fault=0 ∧ f.opcode.toNat=407 ∧
      ((BStarLongLayout.capturedSelector 1).read (x (addr 0).1).long).toNat<3 := by
  obtain ⟨f,F,N⟩ := consume_pc hp H hh distinct cur event
  obtain ⟨P,A,K,L⟩ := next_to_stage _ f (N.symm.trans new)
  exact ⟨cur.1.2.2.2.symm.trans P,f,F,A,K,L⟩

theorem consume_to_six {base x : X} {addr : Nat → Pos n} {len op : Nat} {e : Fin n}
    (H : (addr 0).2=0) (hh : (oldHeaders B (x (addr 0).1)).h6=true)
    (distinct : e≠rightNeighbor e)
    (cur : Current hp base addr len x (.busy op (.back 0)))
    (event : Event hp addr len x e (.busy op (.back 0)) .idle)
    (new : (ctrlOp.read (AllSizeS1Geometry.step B x e (addr 0).1).long).toNat=6) :
    op=5 ∧ ∃ f, BStarLongCommand.bind (longGeometry B (x (addr 0).1)) 0
      (atSite (x (addr 0).1).long 0)=.reply f ∧ f.fault=0 ∧ f.opcode.toNat=5 ∧
      f.outcome≠1 := by
  obtain ⟨f,F,N⟩ := consume_pc hp H hh distinct cur event
  obtain ⟨P,A,K,L⟩ := next_to_six _ f (N.symm.trans new)
  exact ⟨cur.1.2.2.2.symm.trans P,f,F,A,K,L⟩

theorem next_to_band (old : BitVec LW) (f : Payload)
    (L : 7≤pcNext old f) (U : pcNext old f≤408) :
    pcNext old f=(ctrlOp.read old).toNat+1 ∧
      f.fault=0 ∧ f.opcode.toNat=(ctrlOp.read old).toNat := by
  let op := (ctrlOp.read old).toNat
  have Bad : (f.fault != 0 || f.opcode.toNat != op)=false := by
    cases H : (f.fault != 0 || f.opcode.toNat != op)
    · rfl
    · have Z : pcNext old f=0 := by unfold pcNext; exact if_pos H
      omega
  have A := Bool.or_eq_false_iff.mp Bad
  refine ⟨?_,by simpa using A.1,by simpa using A.2⟩
  have G : pcNext old f=if (BStarLongCommand.arithKind op).isSome then
      BStarArithmeticControllerReturn.successor old op
      else BStarResetControllerProgress.nextOrdinary old op f := by
    unfold pcNext
    exact if_neg (Bool.eq_false_iff.mp Bad)
  by_cases E : (BStarLongCommand.arithKind op).isSome=true
  · rw [G,if_pos E] at L ⊢
    have R := BStarArithmeticControllerReturn.arithmetic_range op E
    rcases BStarArithmeticControllerReturn.successor_order old op R.2 with H|H
    · omega
    · exact H
  · rw [G,if_neg E] at L U ⊢
    generalize H : BStarResetControllerProgress.nextOrdinary old op f = a at L U ⊢
    unfold BStarResetControllerProgress.nextOrdinary at H
    repeat' first | split at H
    all_goals simp_all
    all_goals try omega
    all_goals split at H <;> (try split at H) <;> simp_all <;> omega

theorem consume_to_band {base x : X} {addr : Nat → Pos n} {len op : Nat} {e : Fin n}
    (H : (addr 0).2=0) (hh : (oldHeaders B (x (addr 0).1)).h6=true)
    (distinct : e≠rightNeighbor e)
    (cur : Current hp base addr len x (.busy op (.back 0)))
    (event : Event hp addr len x e (.busy op (.back 0)) .idle)
    (L : 7≤(ctrlOp.read (AllSizeS1Geometry.step B x e (addr 0).1).long).toNat)
    (U : (ctrlOp.read (AllSizeS1Geometry.step B x e (addr 0).1).long).toNat≤408) :
    (ctrlOp.read (AllSizeS1Geometry.step B x e (addr 0).1).long).toNat=op+1 ∧
      ∃ f, BStarLongCommand.bind (longGeometry B (x (addr 0).1)) 0
        (atSite (x (addr 0).1).long 0)=.reply f ∧ f.fault=0 ∧ f.opcode.toNat=op := by
  obtain ⟨f,F,N⟩ := consume_pc hp H hh distinct cur event
  rw [N] at L U ⊢
  obtain ⟨E,A,D⟩ := next_to_band _ f L U
  rw [cur.1.2.2.2] at E D
  exact ⟨E,f,F,A,D⟩

#print axioms consume_exact
#print axioms consume_to_stage
#print axioms consume_to_six
#print axioms consume_to_band
end L4.BStarGeneratedPCAncestry
