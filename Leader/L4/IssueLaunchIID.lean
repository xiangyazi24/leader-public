import Leader.L4.BStarClearanceSource
import Leader.L4.BStarResetWaitRing
import Leader.L4.ResetReturnIID

namespace L4.IssueLaunchIID
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongDoor
open BStarClearanceSource BStarResetControllerEntry BStarAcquireWaitControl
open BStarH6WordChart

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
private def op (w : BitVec LW) : Nat := (ctrlOp.read w).toNat

/-- The observation records a real selected launch at the root's
incoming mark. It does not authenticate an inherited byte match. -/
noncomputable def observe (root : Fin n) (z : X × Bool) (e : Fin n) : X × Bool := by
  classical
  exact (step z.1 e, z.2 || decide (e=RearTrace.predecessor root ∧
    Launch (z.1 root).long (step z.1 e root).long))

private theorem away_control (root e : Fin n) (x : X) (H : oldH6 B x root=true)
    (away : e≠RearTrace.predecessor root) :
    control (step x e root).long=control (x root).long := by
  have notRight : root≠rightNeighbor e := by
    intro E
    apply away
    rw [E,RearTrace.predecessor_right]
  by_cases left : root=e
  · subst root
    simpa only [AllSizeS1Geometry.step,if_true] using
      BStarResetWaitRing.joined_left k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) H
  · simp only [AllSizeS1Geometry.step,if_neg left,if_neg notRight]

private theorem door_issue_outcome (root : Fin n) (x : X)
    (head : oldH6 B x root=true) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (I : Issue (x root).long) :
    let e := RearTrace.predecessor root
    let y := step x e
    Launch (x root).long (y root).long ∨
      (op (x root).long≠0 ∧ Issue (y root).long ∧ op (y root).long=0) := by
  dsimp only
  let door := RearTrace.predecessor root
  have R : rightNeighbor door=root := RearTrace.right_predecessor root
  have Q := exact_issue_any_token k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x door,x (rightNeighbor door))
    (by rw [R]; exact head) (by rw [R]; exact I.1) (by rw [R]; exact I.2)
  have out : snapshot (step x door root).long =
      (match initial (op (x root).long) (x root).long with
       | none => ((.empty,1),0)
       | some a => ((forward (op (x root).long) a,2),ctrlOp.read (x root).long)) := by
    rw [show step x door root=(largePair B (x door,x (rightNeighbor door))).2 by
      simp only [AllSizeS1Geometry.step,←R,if_neg (Ne.symm (sep door)),if_true]]
    rw [R] at Q ⊢
    exact Q
  cases args : initial (op (x root).long) (x root).long with
  | none =>
    have old : op (x root).long≠0 := by
      intro E
      rw [E] at args
      exact Option.some_ne_none 0 (show some 0 = none from args)
    change snapshot (step x door root).long =
      (match initial (op (x root).long) (x root).long with
       | none => ((.empty,1),0)
       | some a => ((forward (op (x root).long) a,2),ctrlOp.read (x root).long)) at out
    rw [args] at out
    exact .inr ⟨old,issue_of_snapshot (by decide : 0<413) out,
      congrArg (fun v : (Token×BitVec 2)×BitVec 9=>v.2.toNat) out⟩
  | some a =>
    change snapshot (step x door root).long =
      (match initial (op (x root).long) (x root).long with
       | none => ((.empty,1),0)
       | some a => ((forward (op (x root).long) a,2),ctrlOp.read (x root).long)) at out
    rw [args] at out
    exact .inl ⟨I,a,args,out⟩

/-- From a legal ISSUE, other labels preserve phase and opcode.
At most two paid door marks produce a literal fresh ISSUE launch,
even when its initial operand is rejected on the first paid mark. -/
theorem issue_launch_expected (root : Fin n)
    (Q : X → Prop) (closed : ∀ z e,Q z→Q (step z e))
    (heads : ∀ z,Q z→oldH6 B z root=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (x : X) (qx : Q x) (issue : Issue (x root).long) :
    Height.IIDExpectedHittingTimeAtMost (observe hp root) (fun z=>z.2=true) (x,false)
      (n*(if op (x root).long=0 then 1 else 2)) := by
  classical
  let R := fun z : X => if op (z root).long=0 then 1 else 2
  let Stop := fun z : X×Bool=>z.2=true
  let Live := fun z : X×Bool => fun k=>Q z.1 ∧ Issue (z.1 root).long ∧ R z.1=k
  let door := RearTrace.predecessor root
  have pos (z : X×Bool) (k : Nat) (H : Live z k) : 0<k := by
    rw [←H.2.2]; unfold R; split <;> decide
  have service (z : X×Bool) (k : Nat) (H : Live z k) :
      ∃ d : Fin n, ∀ e : Fin n, Stop (observe hp root z e) ∨
        ∃ j, Live (observe hp root z e) j ∧ j≤k ∧ (e=d→j<k) := by
    obtain ⟨Qz,I,K⟩ := H
    refine ⟨door,fun e=>?_⟩
    by_cases paid : e=door
    · subst e
      obtain good|⟨nonzero,J,Z⟩ := door_issue_outcome hp root z.1 (heads _ Qz) sep I
      · left
        simp [Stop,observe,door,good]
      · right
        have rank1 : R (step z.1 door)=1 := if_pos Z
        have rank2 : k=2 := K.symm.trans (if_neg nonzero)
        exact ⟨1,⟨closed _ _ Qz,J,rank1⟩,by omega,fun _=>by omega⟩
    · have E := away_control hp root e z.1 (heads _ Qz) paid
      have P : (ctrlPhase.read (step z.1 e root).long).toNat=
          (ctrlPhase.read (z.1 root).long).toNat :=
        congrArg (fun u : BitVec 2×BitVec 9 => u.1.toNat) E
      have T : op (step z.1 e root).long=op (z.1 root).long :=
        congrArg (fun u : BitVec 2×BitVec 9 => u.2.toNat) E
      have J : Issue (step z.1 e root).long :=
        ⟨(BStarResetWaitRing.valid_of_control_eq _ _ E).trans I.1,P.trans I.2⟩
      have rankEq : R (step z.1 e)=k := by unfold R at K ⊢; rwa [T]
      exact .inr ⟨k,⟨closed _ _ Qz,J,rankEq⟩,Nat.le_refl _,fun F=>(paid F).elim⟩
  exact ResetReturnIID.iid_of_relational_rank (observe hp root) Stop Live pos service
    (x,false) (R x) (.inr ⟨qx,issue,rfl⟩)

#print axioms issue_launch_expected
end L4.IssueLaunchIID
