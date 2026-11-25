import Leader.L4.BStarSerialTourDebt
import Leader.L4.BStarCommitGeneratedTail

namespace L4.BStarSerialGeneratedEvent
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongDoor BStarH6WordChart
open BStarLongToken BStarLongWork BStarAcquireWaitControl BStarLongCommand
open BStarGeneratedOwner BStarAcquireVisitOrder BStarResetControllerEntry
open BStarSerialTourDebt

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
def pc (x : X) (i : Fin n) := (ctrlOp.read (x i).long).toNat
private theorem bad_issue_pc {x : X} {addr : Nat → Pos n} {e : Fin n}
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
  have A := exact_issue_any_token k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair hdr valid phase
  have bad' : initial (ctrlOp.read pair.2.long).toNat pair.2.long=none := by
    change initial (pc x (rightNeighbor e)) (x (rightNeighbor e)).long=none
    rwa [R]
  rw [bad'] at A
  have eq : step x e (addr 0).1=(largePair B pair).2 := by
    rw [←R]; simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true,pair]
  exact congrArg (fun t : _ × BitVec 9 => t.2.toNat) (eq ▸ A)

private theorem foreign_pc (x : X) (i e : Fin n)
    (h : oldH6 B x i=true) (ne : rightNeighbor e≠i) :
    pc (step x e) i=pc x i := by
  by_cases E : i=e
  · subst i
    let pair := (x e,x (rightNeighbor e))
    have h' : (oldHeaders B pair.1).h6=true := h
    have t := BStarResetWaitRing.joined_left k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair h'
    unfold pc
    simp only [AllSizeS1Geometry.step,if_true]
    have Q := congrArg (fun y : BitVec 2 × BitVec 9 => y.2.toNat) t
    exact Q
  · unfold pc
    simp only [AllSizeS1Geometry.step,if_neg E,if_neg (Ne.symm ne)]

/-- The literal initialization decoder never rejects a reset opcode. -/
theorem reset_initial (x : BitVec LW) (a : Nat) (h : a<3) : initial a x=some 0 := by
  have E : a=0 ∨ a=1 ∨ a=2 := by omega
  rcases E with rfl|rfl|rfl <;> rfl

/-- An actual generated event either retains its PC/debt, spends at least
one tour, or is the cycle-ending reset receipt. A rejected issue and a
non-ending consume belong only to the strict-spend branch. -/
theorem event_debt {base x : X} {addr : Nat → Pos n} {len : Nat}
    {e : Fin n} {a b : Mode}
    (root : (addr 0).2=0) (hdr : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e)
    (I : Current hp base addr len x a)
    (J : Current hp base addr len (step x e) b)
    (E : Event hp addr len x e a b)
    (reset : ∀ f,
      a=.busy (pc x (addr 0).1) (.back 0) → b=.idle →
      pc x (addr 0).1<3 →
      bind (longGeometry B (x (addr 0).1)) 0 (atSite (x (addr 0).1).long 0)=.reply f →
      f.fault=0 ∧ f.opcode.toNat=pc x (addr 0).1) :
    let old := pc x (addr 0).1
    let new := pc (step x e) (addr 0).1
    (old=2 ∧ new=3 ∧ a=.busy 2 (.back 0) ∧ b=.idle) ∨
      toursLeft new+1≤toursLeft old ∨
      (new=old ∧ ¬ (∃ op, a=.busy op (.back 0) ∧ b=.idle) ∧
       ¬ (a=.idle ∧ b=.idle ∧ e=RearTrace.predecessor (addr 0).1)) := by
  dsimp only
  cases E with
  | idle_hold away =>
    have ne : rightNeighbor e≠(addr 0).1 := by
      intro Q
      exact away ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor Q))
    exact .inr (.inr ⟨foreign_pc hp x (addr 0).1 e hdr ne, by simp, by simp [away]⟩)
  | bad_issue own bad =>
    have Z := bad_issue_pc hp hdr sep I.1 own bad
    have high : ¬ pc x (addr 0).1<3 := by
      intro low
      change initial (pc x (addr 0).1) (x (addr 0).1).long=none at bad
      have contra := (reset_initial (x (addr 0).1).long _ low).symm.trans bad
      cases contra
    have bound : pc x (addr 0).1<413 := by
      have V := I.1.1
      unfold LongDoorGuard.valid at V
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp V).2
    right; left
    rw [Z,toursLeft,toursLeft,if_pos (by decide : (0:Nat)<3),if_neg high]
    omega
  | launch _ L =>
    exact .inr (.inr ⟨congrArg (fun t : _ × BitVec 9 => t.2.toNat) L.2.choose_spec.2,
      by simp, by simp⟩)
  | transit op z d _ _ =>
    exact .inr (.inr ⟨J.1.2.2.2.trans I.1.2.2.2.symm,by simp,by simp⟩)
  | arrived_hold op _ =>
    exact .inr (.inr ⟨J.1.2.2.2.trans I.1.2.2.2.symm,by simp,by simp⟩)
  | consume op own clear =>
    have old : pc x (addr 0).1=op := I.1.2.2.2
    have H := consume_pays_or_release hp root hdr sep I (.consume op own clear)
      (fun f low F=>by
        have := reset f (by rw [old]) rfl (old.symm ▸ low) F
        rwa [old] at this)
    rw [←old] at H
    rcases H with ⟨O,N⟩|S
    · exact .inl ⟨O,N,by rw [←O,old],rfl⟩
    · exact .inr (.inl S)

#print axioms event_debt
end L4.BStarSerialGeneratedEvent
