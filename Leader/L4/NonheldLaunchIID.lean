import Leader.L4.IssueLaunchIID

namespace L4.NonheldLaunchIID
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongDoor
open BStarClearanceSource BStarResetControllerEntry BStarAcquireWaitControl BStarH6WordChart
open IssueLaunchIID

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- Nonheld entry costs at most three door waits if foreign marks
cannot recreate a held owner before a legal ISSUE. The no-reentry
premise is deliberately explicit. -/
theorem expected_of_no_reentry (root : Fin n)
    (Q : X → Prop) (closed : ∀ z e,Q z→Q (step z e))
    (heads : ∀ z,Q z→oldH6 B z root=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (noRise : ∀ z e,Q z→e≠RearTrace.predecessor root→¬Held (z root).long →
      ¬Held (step z e root).long)
    (x : X) (qx : Q x) (NH : ¬Held (x root).long) :
    Height.IIDExpectedHittingTimeAtMost (observe hp root) (fun z=>z.2=true) (x,false) (3*n) := by
  classical
  let Stop := fun z : X×Bool => z.2=true
  let IssueState := fun z : X×Bool => Q z.1 ∧ Issue (z.1 root).long
  let Live := fun z : X×Bool => fun k : Nat => Q z.1 ∧ ¬Held (z.1 root).long ∧ k=1
  let door := RearTrace.predecessor root
  have first : Height.IIDExpectedHittingTimeAtMost (observe hp root)
      (fun z=>IssueState z ∨ Stop z) (x,false) n := by
    have H := ResetReturnIID.iid_of_relational_rank (observe hp root)
      (fun z=>IssueState z ∨ Stop z) Live
      (fun _ _ Z => Z.2.2.symm ▸ (by decide : 0<1)) (by
        intro z rold Z
        have q := Z.1
        refine ⟨door,fun e=>?_⟩
        by_cases paid : e=door
        · subst e
          rcases dirty_source hp z.1 root (heads _ q) sep Z.2.1 with L|⟨o,O,F⟩
          · left; right
            simp [Stop,observe,door,L]
          · left; left
            exact ⟨closed _ _ q,issue_of_snapshot O F⟩
        · right
          exact ⟨rold,⟨closed _ _ q,noRise _ _ q paid Z.2.1,Z.2.2⟩,
            Nat.le_refl _,fun eq=>(paid eq).elim⟩)
      (x,false) 1 (.inr ⟨qx,NH,rfl⟩)
    simpa only [Nat.mul_one] using H
  have second : ∀ z,IssueState z→ Height.IIDExpectedHittingTimeAtMost
      (observe hp root) Stop z (n*2) := by
    rintro ⟨y,b⟩ ⟨qy,J⟩
    cases b
    · have H := issue_launch_expected hp root Q closed heads sep y qy J
      intro T
      exact Nat.le_trans (H T) (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left n (by split <;> decide)))
    · intro T
      rw [Height.iidHitCost_of_target _ Stop _ (show Stop (y,true) from rfl)]
      exact Nat.zero_le _
  have out := Height.iid_stage_le (observe hp root) (Nat.zero_lt_of_lt root.isLt)
    (x,false) IssueState Stop n (n*2) first second
  have equal : n+n*2=3*n := by omega
  rw [equal] at out
  exact out

#print axioms expected_of_no_reentry
end L4.NonheldLaunchIID
