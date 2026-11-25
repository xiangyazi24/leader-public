import Leader.L4.AdviceBandRadiusBudget
import Leader.L4.Height.G9DotCoefficient

namespace L4.AllSizeHeadline
set_option exponentiation.threshold 2976
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
open AllSizeProtocol PhysicalCustody AdviceBandRadiusBudget BStarTrace

def prodParams (s : Nat) :=
  production s (radiusTwo s) (ell (radiusTwo s+1)) (streak s)
    (streak (radiusTwo s)) (radWidth s) (s+11) 2 12

def width (s : Nat) : Nat := if s ≤ 5 then 48 else PackedCore.width (prodParams s)

abbrev State (s : Nat) := Fin (2^width s)

theorem ell_le_input (x : Nat) : ell x ≤ x :=
  (ell_le_iff _ _).2 (Nat.le_of_lt (Nat.lt_two_pow_self))

private theorem streak_bound {s k : Nat} (hk : k ≤ 2^s) :
    streak k ≤ (3*sigma+263)*(s+2) := by
  have hl : ell (k+2) ≤ s+2 := by
    have hp : 0 < 2^s := Nat.two_pow_pos s
    apply (ell_le_iff _ _).2
    rw [Nat.pow_add]
    omega
  have hx := ell_le_input (sigma+6*ell (k+2)+100)
  have h : streak k ≤ 3*sigma+18*(s+2)+245 := by
    unfold streak
    dsimp
    omega
  have ha : 18 ≤ 3*sigma+263 := by omega
  have hb : 1 ≤ s+2 := by omega
  calc
    _ ≤ 3*sigma+245+18*(s+2) := by omega
    _ ≤ (3*sigma+245)*(s+2)+18*(s+2) :=
      Nat.add_le_add_right (Nat.le_mul_of_pos_right _ (by omega)) _
    _ = _ := by rw [←Nat.add_mul]

theorem state_count (s : Nat) : 2^width s ≤ 2^2976*(s+2)^20 := by
  by_cases hs : s≤5
  · rw [width,if_pos hs]
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by decide : 48≤2976))
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)))
  · have hr : radiusTwo s ≤ 2^s := radius_le_power (by omega)
    have h := PackedCore.production_width (prodParams s) s (3*sigma+263)
      rfl (reportDigits_le s _ hr) rfl
      (streak_bound (Nat.le_of_lt (Nat.lt_two_pow_self))) (streak_bound hr)
    let C := 541+2*ell (3*sigma+263)+longWidth (prodParams s).alu
    have ex : C+20=2976 := by
      dsimp [C]
      rw [show (prodParams s).alu = manifest from rfl,
        (show longWidth manifest = 2367 from production_long_width)]
      decide
    have cap : 2^ell (s+2) ≤ 2*(s+2) := by
      have hh' : 2^(((s+2)-1).log2) ≤ (s+2)-1 :=
        (Nat.le_log2 (by omega)).mp (Nat.le_refl _)
      rw [ell, if_neg (by omega),Nat.pow_succ]
      have := Nat.mul_le_mul_right 2 hh'
      omega
    rw [width,if_neg hs]
    calc
      _ ≤ 2^(C+20*ell (s+2)) := Nat.pow_le_pow_right (by decide) h
      _ = 2^C*(2^ell (s+2))^20 :=
        by rw [Nat.pow_add,Nat.mul_comm 20 (ell (s+2)),Nat.pow_mul]
      _ ≤ 2^C*(2*(s+2))^20 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left cap 20)
      _ = 2^2976*(s+2)^20 := by rw [Nat.mul_pow,←Nat.mul_assoc,←Nat.pow_add,ex]
/-- Exact padded alphabet, including every spare code. No Mathlib
cardinality interface is needed: both coding inverses are part of this type. -/
def deployedStateCoding (s : Nat) :
    L4.ExactCoding (L4.Height.G9Wire.compactDeployment s).Site (State s) := by
  by_cases h : 6 ≤ s
  · have h' : ¬ s ≤ 5 := by omega
    rw [L4.Height.G9Wire.compactDeployment, if_pos h]
    change L4.ExactCoding (PackedCore (prodParams s)) (Fin (2^width s))
    rw [width, if_neg h']
    exact PackedCore.coding (prodParams s)
  · have h' : s ≤ 5 := by omega
    rw [L4.Height.G9Wire.compactDeployment, if_neg h]
    change L4.ExactCoding (Fin (2^48)) (Fin (2^width s))
    rw [width, if_pos h']
    exact L4.ExactCoding.id _

open L4.Height L4.Height.G9Wire L4.Height.G9Wire.PublicSpec

/-- The same advice-only deployed family has at most
`2^2976 * (s+2)^20` states and reaches a permanent physical winner
in expected time at most the named absolute coefficient times `n^2`. -/
theorem allSize_fast :
    (∀ s : Nat, ∃ card : Nat,
      Nonempty (L4.ExactCoding (compactDeployment s).Site (Fin card)) ∧
      card ≤ 2^2976*(s+2)^20) ∧
    (∀ n (hn : 4 ≤ n),
      (compactDeployment (ceilingLogTwo (ceilingLogTwo n))).Expected boundedEncode boundedDecode n hn
        L4.PhysicalCustodyProduction.K_custody
        (patrolAllowance L4.WindowCappedPublic.coefficient)) := by
  refine ⟨?_, G9Dot.compact_allSize_fast⟩
  intro s
  exact ⟨2^width s, ⟨deployedStateCoding s⟩, state_count s⟩

end L4.AllSizeHeadline

#print axioms L4.AllSizeHeadline.state_count
#print axioms L4.AllSizeHeadline.deployedStateCoding
#print axioms L4.AllSizeHeadline.allSize_fast
#check L4.AllSizeHeadline.allSize_fast
