import Leader.L4.BStarClearanceOffsetMask
import Leader.L4.BStarResetSchedule

namespace L4.BStarClearanceSettled
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart
open BStarClearanceOffset

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => BStarClearanceOffset.X k₁ k₂ t₂ J₁ J₂ r c p c₁ n
local notation "step" => AllSizeS1Geometry.step B

theorem word_eq (x : X) (w : List (Fin n)) :
    BStarResetSchedule.run step x w=w.foldl step x := by
  induction w generalizing x with
  | nil => rfl
  | cons _ _ ih => exact ih _

/-- These are concrete offset preparation marks, not an abstract gate
assumption: take exactly five traversals of the physical mark alphabet.
No information about the old long offset is required. -/
theorem settle (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (he : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (closed : ∀ x e, Q x → Q (step x e))
    (same : ∀ x, Q x → ∀ i, oldH6 B x i=h i)
    (x : X) (I : Q x) :
    ∃ w : List (Fin n), w.length=5*n ∧
      Q (BStarResetSchedule.run step x w) ∧
      correct h hh 5 (BStarResetSchedule.run step x w) := by
  let w := List.finRange n
  have A := five_covers hp h hh he Q closed same
    (fun y e _ => BStarClearanceOffsetMask.leftFrame hp y e) x I w List.mem_finRange
  refine ⟨(List.replicate 5 w).flatten,by simp [w,List.replicate_succ]; omega,?_⟩
  rw [word_eq hp,List.foldl_flatten]
  exact A

theorem settled_step (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (he : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (closed : ∀ x e, Q x → Q (step x e))
    (same : ∀ x, Q x → ∀ i, oldH6 B x i=h i)
    (x : X) (e : Fin n) (I : Q x ∧ correct h hh 5 x) :
    Q (step x e) ∧ correct h hh 5 (step x e) :=
  ⟨closed x e I.1,stable hp h hh x e (he e) (same x I.1)
      (BStarClearanceOffsetMask.leftFrame hp x e) I.2⟩

end L4.BStarClearanceSettled
