import Leader.L4.BStarSteeredLikelihood

namespace L4.BStarResidualBudget
open Height Classical

/-- Arithmetic form of the paper's 420-tour / one-FENCE residual estimate.
The verification of the tour count and FENCE exclusion is a separate
protocol fact. Here L is the command length and H the longer mobile chain. -/
theorem residual_le {n W L H : Nat} (w : 0<W) (link : L≤11*W) (chain : H≤2*W) :
    n*(420*(4*L+10)+128*H) ≤ 2^15*n*W := by
  rw [Nat.mul_comm (2^15) n,Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  omega

/-- Given one capped ledger that charges all four releases and both target
cycles, the time failure at D of the two-interval experiment has mass
at most 3/16. A failure tape must have cost at least one full interval.
No independence of competitors, or of consecutive waits, is used. -/
theorem time_fraction {n W L H : Nat} (hn : 0<n) (hw : 0<W)
    (hL : L≤11*W) (hH : H≤2*W)
    (cost : List (Fin n) → Nat) (F : List (Fin n) → Prop)
    (spent : ∀ v, F v → 2^20*n*W ≤ cost v)
    (mean : let t := 2*(2^20*n*W)
      wordSum cost t ≤ 6*(n*(420*(4*L+10)+128*H))*n^t) :
    let t := 2*(2^20*n*W)
    16*wordSum (BStarRawBlockDrift.massInd F) t ≤ 3*n^t := by
  dsimp only at mean ⊢
  let D := 2^20*n*W
  let A := n*(420*(4*L+10)+128*H)
  let C := wordSum (BStarRawBlockDrift.massInd F) (2*D)
  have drop : D*C ≤ wordSum cost (2*D) := by
    rw [←wordSum_mul_left]
    apply wordSum_mono
    intro v
    by_cases Fv : F v
    · simpa [BStarRawBlockDrift.massInd,Fv] using spent v Fv
    · simp [BStarRawBlockDrift.massInd,Fv]
  have O : 16*(6*A) ≤ 3*D := by
    apply Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (residual_le hw hL hH)))
    change 16*(6*(2^15*n*W)) ≤ 3*(2^20*n*W)
    exact Nat.le_of_eq (by
      have P : (16:Nat)*(6*2^15)=3*2^20 := by decide
      calc
        _ = (16*(6*2^15))*(n*W) := by ac_rfl
        _ = (3*2^20)*(n*W) := by rw [P]
        _ = _ := by ac_rfl)
  apply Nat.le_of_mul_le_mul_left (c := D) _ (Nat.mul_pos (Nat.mul_pos (by decide) hn) hw)
  calc
    D*(16*C) = 16*(D*C) := by ac_rfl
    _ ≤ 16*(6*A*n^(2*D)) := Nat.mul_le_mul_left _ (Nat.le_trans drop mean)
    _ = (16*(6*A))*n^(2*D) := by ac_rfl
    _ ≤ (3*D)*n^(2*D) := Nat.mul_le_mul_right _ O
    _ = D*(3*n^(2*D)) := by ac_rfl

end L4.BStarResidualBudget
