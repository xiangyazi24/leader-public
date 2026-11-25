import Leader.L4.BStarAttemptCuts
import Leader.L4.BStarNativeReceiptTape
import Leader.L4.BStarGeneratedTapeCuts
import Leader.L4.BStarOwnerLaunchOrigin

namespace L4.BStarPhysicalPhase
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

/-- An actual generated mark either holds the old PC, restarts at zero,
or strictly raises the PC through the exact incoming consume. -/
theorem generated_pc_step {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b : Mode} (e : Fin n)
    (K : (addr 0).2=0) (H : oldH6 B x (addr 0).1=true) (sep : e≠rightNeighbor e)
    (I : Current hp base addr len x a) (J : Current hp base addr len (step x e) b)
    (E : Event hp addr len x e a b) :
    let i := (addr 0).1
    pc (step x e) i=pc x i ∨ pc (step x e) i=0 ∨
      (pc x i<pc (step x e) i ∧ e=RearTrace.predecessor i) := by
  dsimp only
  cases E with
  | idle_hold away => exact .inl (foreign_pc hp x _ e H away)
  | arrived_hold op away => exact .inl (foreign_pc hp x _ e H away)
  | launch own L =>
    exact .inl (congrArg (fun t : _ × BitVec 9 => t.2.toNat) L.2.choose_spec.2)
  | transit op z d live S => exact .inl (J.1.2.2.2.trans I.1.2.2.2.symm)
  | bad_issue own bad => exact .inr (.inl (reject_pc hp H sep I.1 own bad))
  | consume op own clear =>
    have E : Event hp addr len x e (.busy op (.back 0)) .idle := .consume op own clear
    obtain ⟨f,_,N⟩ := consume_pc hp K H sep I E
    have range : pc x (addr 0).1<413 := by
      have A := I.1.2.1
      unfold LongDoorGuard.valid at A
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp A).2
    change pc (step x e) (addr 0).1=pcNext (x (addr 0).1).long f at N
    rw [N]
    unfold pcNext
    dsimp only
    split
    · exact .inr (.inl rfl)
    · split
      · rename_i ar
        have ar' := BStarArithmeticControllerReturn.arithmetic_range _ ar
        rcases BStarArithmeticControllerReturn.successor_order _ _ ar'.2 with L|L
        · exact .inr (.inl L)
        · exact .inr (.inr ⟨by change pc x (addr 0).1 < _; change _ = pc x (addr 0).1+1 at L; omega,own⟩)
      · rcases BStarResetControllerProgress.ordinary_progress _ _ f range with L|L
        · exact .inr (.inl L)
        · exact .inr (.inr ⟨L.1,own⟩)

theorem literal_rrel_next (old : BitVec LW) (f : Payload)
    (P : (ctrlOp.read old).toNat=2) (N : pcNext old f=3) :
    f.fault=0 ∧ f.opcode.toNat=2 := by
  unfold pcNext at N
  dsimp only at N
  rw [P] at N
  by_cases F : f.fault=0
  · by_cases O : f.opcode.toNat=2
    · exact ⟨F,O⟩
    · simp [F,O] at N
  · have FF : f.fault ≠ (0#1) := F
    simp [FF] at N

/-- A real RREL stop is the healthy opcode-2 response on the exact
incoming mark; a transition to RSTOP/0 is no release certificate. -/
theorem rrel_stop {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b : Mode} (e : Fin n)
    (K : (addr 0).2=0) (H : oldH6 B x (addr 0).1=true) (sep : e≠rightNeighbor e)
    (I : Current hp base addr len x a) (J : Current hp base addr len (step x e) b)
    (E : Event hp addr len x e a b)
    (P : pc x (addr 0).1=2) (N : pc (step x e) (addr 0).1=3) :
    a=.busy 2 (.back 0) ∧ b=.idle ∧ BStarNativeReceiptTape.Hit hp base addr len x e 2 := by
  cases E with
  | idle_hold away => have eq := foreign_pc hp x _ e H away; omega
  | arrived_hold op away => have eq := foreign_pc hp x _ e H away; omega
  | launch own L =>
    have eq : pc (step x e) (addr 0).1=pc x (addr 0).1 :=
      congrArg (fun t : _ × BitVec 9 => t.2.toNat) L.2.choose_spec.2
    omega
  | transit op z d live S =>
    have eq : pc (step x e) (addr 0).1=pc x (addr 0).1 := J.1.2.2.2.trans I.1.2.2.2.symm
    omega
  | bad_issue own bad => have eq := reject_pc hp H sep I.1 own bad; omega
  | consume op own clear =>
    have eq : op=2 := I.1.2.2.2.symm.trans P
    subst op
    have evt : Event hp addr len x e (.busy 2 (.back 0)) .idle := .consume 2 own clear
    obtain ⟨f,R,M⟩ := consume_pc hp K H sep I evt
    have M' : pc (step x e) (addr 0).1=pcNext (x (addr 0).1).long f := M
    obtain ⟨F,O⟩ := literal_rrel_next _ f P (M'.symm.trans N)
    exact ⟨rfl,rfl,I,evt,P,N,own,f,R,F,O⟩

/-- A generated interval is within one attempt if no actual post-mark
cut has reset PC zero. A later attempt must be analyzed after RESET,
not included in the same monotone interval. -/
def PositiveTape (x : X) (i : Fin n) (w : List (Fin n)) : Prop :=
  ∀ u v,w=u++v → oldH6 B (run x u) i=true ∧ 0<pc (run x u) i

theorem attempt_pc_mono {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b : Mode} {w : List (Fin n)} (K : (addr 0).2=0)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x a w b)
    (A : PositiveTape hp x (addr 0).1 w) :
    pc x (addr 0).1≤pc (run x w) (addr 0).1 := by
  induction T with
  | endpoint _ => exact Nat.le_refl _
  | @next x a e w b dest I E T ih =>
    have sub : PositiveTape hp (step x e) (addr 0).1 w := by
      intro u v U
      exact A (e::u) v (congrArg (List.cons e) U)
    have H := (A [] (e::w) rfl).1
    have L := (sub [] w rfl).2
    refine Nat.le_trans ?_ (ih sub)
    rcases generated_pc_step hp e K H (sep e) I (at_start hp T) E with V|V|V
    · exact Nat.le_of_eq V.symm
    · change 0<pc (step x e) (addr 0).1 at L
      change pc (step x e) (addr 0).1=0 at V
      omega
    · exact Nat.le_of_lt V.1

/-- A fresh entrance into FENCE (PC 11) cannot occur after the first
one and before RESET, even if other owners take arbitrary marks. -/
theorem no_second_fence_entry {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b d : Mode} {w : List (Fin n)} (K : (addr 0).2=0)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x a w b)
    (A : PositiveTape hp x (addr 0).1 w)
    (first : pc x (addr 0).1=11)
    (e : Fin n)
    (E : Event hp addr len (run x w) e b d)
    (J : Current hp base addr len (step (run x w) e) d)
    (next : pc (step (run x w) e) (addr 0).1=11) :
    pc (run x w) (addr 0).1=11 := by
  have H := (A w [] (List.append_nil _).symm).1
  have M := attempt_pc_mono hp K sep T A
  rcases generated_pc_step hp e K H (sep e) (at_end hp T) J E with V|V|V <;> omega

theorem literal_dummy_to_reset (old : BitVec LW) (f : Payload)
    (P : (ctrlOp.read old).toNat=412) : pcNext old f=0 := by
  unfold pcNext
  dsimp only
  rw [P]
  split
  · rfl
  · rfl

/-- DUMMY completion enters zero by its own ACK, but cannot be the
opcode-2 RREL release cut. -/
theorem dummy_consume_not_release {base x : X} {addr : Nat → Pos n} {len : Nat}
    (e : Fin n) (K : (addr 0).2=0) (H : oldH6 B x (addr 0).1=true) (sep : e≠rightNeighbor e)
    (I : Current hp base addr len x (.busy 412 (.back 0)))
    (E : Event hp addr len x e (.busy 412 (.back 0)) .idle) :
    pc (step x e) (addr 0).1=0 ∧ ¬ BStarNativeReceiptTape.Hit hp base addr len x e 2 := by
  obtain ⟨f,_,N⟩ := consume_pc hp K H sep I E
  have P : pc x (addr 0).1=412 := I.1.2.2.2
  exact ⟨N.trans (literal_dummy_to_reset _ f P),fun H => by have F := H.2.2.1; omega⟩

end L4.BStarPhysicalPhase
