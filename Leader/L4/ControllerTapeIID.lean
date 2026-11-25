import Leader.L4.ResetReturnIID

namespace L4.ControllerTapeIID
open BStarResetSchedule ResetReturnIID

theorem sum_mono {n : Nat} {a b : Fin n → Nat} (H : ∀ e,a e≤b e) :
    (List.ofFn a).sum≤(List.ofFn b).sum := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    simp only [List.ofFn_succ,List.sum_cons]
    exact Nat.add_le_add (H 0) (ih (fun e=>H e.succ))

theorem expected_of_prefix {X : Type} {n : Nat} (step : X→Fin n→X)
    (x : X) (P : X→Prop) (A : List (Fin n)→Prop) (K : Nat)
    (witness : ∀ w,A w→∃ pre tail,w=pre++tail ∧ P (BStarResetSchedule.run step x pre))
    (h : Height.IIDExpectedHittingTimeAtMost appendTape A [] K) :
    Height.IIDExpectedHittingTimeAtMost step P x K := by
  classical
  let Past := fun w : List (Fin n)=>∀ pre tail, w=pre++tail→tail≠[]→¬P (BStarResetSchedule.run step x pre)
  have comp (t : Nat) (w : List (Fin n)) (H : Past w) :
      Height.iidHitCost step P t (BStarResetSchedule.run step x w) ≤ Height.iidHitCost appendTape A t w := by
    induction t generalizing w with
    | zero => exact Nat.zero_le _
    | succ t ih =>
      by_cases hit : P (BStarResetSchedule.run step x w)
      · rw [Height.iidHitCost_of_target _ _ _ hit]
        exact Nat.zero_le _
      · have N : ¬A w := by
          intro T
          obtain ⟨pre,tail,E,F⟩:=witness w T
          by_cases L : tail=[]
          · subst tail; rw [List.append_nil] at E; exact hit (E.symm ▸ F)
          · exact H pre tail E L F
        simp only [Height.iidHitCost,if_neg hit,if_neg N]
        apply Nat.add_le_add_left
        apply sum_mono
        intro e
        have T : Past (appendTape w e) := by
          intro pre tail E nonempty
          change w++[e]=pre++tail at E
          rcases List.append_eq_append_iff.mp E with ⟨extra,EP,ET⟩|⟨extra,EW,_⟩
          · have extra0 : extra=[] := by
              have L := congrArg List.length ET
              simp only [List.length_cons,List.length_nil,List.length_append] at L
              exact List.length_eq_zero_iff.mp (by have Ht := List.length_pos_iff.mpr nonempty; omega)
            subst extra
            rw [List.append_nil] at EP
            exact EP.symm ▸ hit
          · by_cases ex : extra=[]
            · subst extra; rw [List.append_nil] at EW; exact EW ▸ hit
            · exact H pre extra EW ex
        rw [←show BStarResetSchedule.run step x (appendTape w e)=step (BStarResetSchedule.run step x w) e from BStarResetSchedule.run_append _ _ _ _]
        exact ih _ T
  intro t
  apply Nat.le_trans (comp t [] ?_) (h t)
  intro pre tail E N
  have Z := congrArg List.length E
  have L := List.length_pos_iff.mpr N
  simp only [List.length_append,List.length_nil] at Z
  omega

theorem expected_after_prefix {n : Nat} (A : List (Fin n)→Prop)
    (P : List (Fin n)→Prop) (pre : List (Fin n)) (K : Nat)
    (cut : ∀ w,A w→P (pre++w))
    (H : Height.IIDExpectedHittingTimeAtMost appendTape A [] K) :
    Height.IIDExpectedHittingTimeAtMost appendTape P pre K := by
  classical
  have C (t : Nat) (w : List (Fin n)) :
      Height.iidHitCost appendTape P t (pre++w) ≤ Height.iidHitCost appendTape A t w := by
    induction t generalizing w with
    | zero => exact Nat.zero_le _
    | succ t ih =>
      by_cases hit : P (pre++w)
      · rw [Height.iidHitCost_of_target _ _ _ hit]
        exact Nat.zero_le _
      · have N : ¬A w := fun h=>hit (cut w h)
        simp only [Height.iidHitCost,if_neg hit,if_neg N]
        apply Nat.add_le_add_left
        apply sum_mono
        intro e
        rw [show appendTape (pre++w) e=pre++appendTape w e by simp only [appendTape,List.append_assoc]]
        exact ih _
  intro t
  simpa using Nat.le_trans (C t []) (H t)

#print axioms expected_of_prefix
#print axioms expected_after_prefix
end L4.ControllerTapeIID
