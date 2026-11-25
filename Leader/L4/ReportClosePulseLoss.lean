import Leader.L4.ReportLossArithmetic
import Leader.L4.FourLossStickyClock
import Leader.L4.ReportPulseJointCount

namespace L4.ReportClosePulseLoss
open Height FourLossStickyClock ReportLossArithmetic

variable {n : Nat}

/-- After two fixed completions are pinned, union over the finite family
of gate/position choices. No probabilistic independence is used. -/
theorem loss_of_pinned_family
    (B J C m : Nat) (L : 2≤B) (Many : m≤C*n^2)
    (Small : 8*C≤2^(2*J))
    (joint : Fin m→List (Fin n)→Prop) (loss : List (Fin n)→Prop)
    (maps : ∀ w,loss w→∃ i,joint i w)
    (per : ∀ i,2^(2*J)*badCount (joint i) B≤n^(B-2)) :
    8*badCount loss B≤n^B := by
  let p := 2^(2*J)
  let F := fun i : Fin m=>badCount (joint i) B
  have P : 0<p := Nat.pow_pos (by decide)
  have U : badCount loss B≤(List.ofFn F).sum :=
    Nat.le_trans (badCount_mono maps B) (badCount_union joint B)
  have Sum : p*(List.ofFn F).sum≤m*n^(B-2) := by
    rw [←sum_ofFn_mul_left,←sum_ofFn_const]
    exact sum_ofFn_le _ _ per
  have E : n^(B-2)*n^2=n^B := by
    rw [←Nat.pow_add,show B-2+2=B by omega]
  apply Nat.le_of_mul_le_mul_left _ P
  calc
    p*(8*badCount loss B)=8*(p*badCount loss B) := by ac_rfl
    _ ≤ 8*(m*n^(B-2)) := Nat.mul_le_mul_left _
      (Nat.le_trans (Nat.mul_le_mul_left _ U) Sum)
    _ ≤ 8*((C*n^2)*n^(B-2)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ Many)
    _ = (8*C)*n^B := by rw [←E]; ac_rfl
    _ ≤ p*n^B := Nat.mul_le_mul_right _ Small

theorem close_from_two_pin_counts
    (rho : Nat) (B m : Nat) (L : 2≤B)
    (M : m≤(600*(AdviceBandRadiusBudget.trialH rho)^2*
      (AdviceBandRadiusBudget.trialU rho+1)*(hSize rho+1))*n^2)
    (joint : Fin m→List (Fin n)→Prop) (loss : List (Fin n)→Prop)
    (maps : ∀ w,loss w→∃ i,joint i w)
    (per : ∀ i,2^(2*AdviceBandRadiusBudget.trialJ rho)*badCount (joint i) B≤n^(B-2)) :
    8*badCount loss B≤n^B := by
  refine loss_of_pinned_family B _ _ m L M ?_ joint loss maps per
  rw [Nat.mul_comm 2,Nat.pow_mul]
  exact Nat.le_of_lt (close_loss_lt rho)

end L4.ReportClosePulseLoss
